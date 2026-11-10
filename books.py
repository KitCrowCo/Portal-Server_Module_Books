# modules/books/books.py
"""
Books - ebooks and comics kept on this server, indexed where they are. Several roots (folders), each read-only or writable; nothing is moved or copied to be indexed.
Metadata comes from inside the files: EPUB (title, authors, series, language, cover; DRM marked), CBZ / CBR / CB7 (ComicInfo.xml; otherwise the folder holding the comic is its series and the number in its name its place),
folders of page images (a chapter as Tachiyomi / Mihon and similar apps download it: the folder is the chapter, its parent folder the series), MOBI / AZW3 (title, author, DRM marked); TXT, PDF and the rest by file name.
Comics are grouped by series and read in the browser - page by page, or as one long scroll for webtoons (chosen per series) - with the place remembered per login and the next chapter one tap away at the end.
EPUB is read part by part in a frame showing the book's own pages (its scripts are blocked; portal colors or the book's own look; text size per login; the part and place are remembered), TXT as text, PDF in the browser's own viewer.
Upload keeps folders as they are: a chapter folder of page images (or a series folder of chapters) goes up as it is, in batches, and is never converted.
Actions: download (a folder of images as a CBZ); send to an e-reader on the network (CrossPoint firmware's /upload - a name already on the device is never overwritten); convert to EPUB or TXT with calibre's ebook-convert when it is
installed (whatever that calibre can read; DRM is marked for information only); upload into a writable root; delete from a writable root (asks first).
CBR and CB7 are read with bsdtar (libarchive, free software) when it is installed; nothing non-free is used.
Data at data/books/: settings.json (roots, e-readers), index/<root>.json (only new or changed files and folders are read again), covers/<id>.jpg (comic covers are made the first time they are shown),
positions.json (place per comic and reading mode per series, per login), tmp/ (a folder being downloaded as a CBZ).
Everything stays on this server; nothing is fetched from outside.
"""
import io, os, re, json, html, shutil, asyncio, hashlib, secrets, zipfile, posixpath, subprocess, mimetypes
import xml.etree.ElementTree as ET
from datetime import datetime
from pathlib import Path
from urllib.parse import unquote, quote
import httpx
from PIL import Image
from fastapi import APIRouter, Request, HTTPException
from fastapi.responses import HTMLResponse, FileResponse, Response
from starlette.background import BackgroundTask

MODULE_META = {"label": "Books", "icon": "&#x1F4DA;", "description": "Ebooks and comics on this server: browse, read comics, send to an e-reader, convert"}
router = APIRouter()
ENV = {}
UI = BI = IM = None
DATA = Path("./data/books")
EXTS = {".epub", ".kepub", ".cbz", ".cbr", ".cb7", ".mobi", ".azw", ".azw3", ".kfx", ".pdf", ".txt", ".fb2", ".djvu", ".xtc", ".xtch"}
COMIC = (".cbz", ".cbr", ".cb7", ".images")   # .images: a folder of page images, indexed as one comic
TEXT = (".epub", ".kepub", ".txt", ".pdf")   # read in the browser: EPUB by its chapters, TXT as text, PDF in the browser's own viewer
IMG = (".jpg", ".jpeg", ".png", ".webp", ".gif")
_EPUB_CSP = "default-src 'self' data:; script-src 'none'; object-src 'none'; frame-src 'none'; connect-src 'none'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; font-src 'self' data:"   # a book's own scripts never run
_MIME = {".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".png": "image/png", ".webp": "image/webp", ".gif": "image/gif"}
_FONT_OBFUSCATION = ("http://www.idpf.org/2008/embedding", "http://ns.adobe.com/pdf/enc#RC")   # font scrambling some EPUBs carry - not DRM
_CHAPTER = re.compile(r"(?:\bch(?:apter)?|\bep(?:isode)?|#)\.?\s*(\d+(?:\.\d+)?)", re.I)
_JOBS = {}    # background jobs by book id ("_scan" for indexing): {"state": running|done|error, "msg"}
_TASKS = set()
_SCAN_LOCK = asyncio.Lock()
_SCAN = {"n": 0}   # files and folders read so far by the running scan
_IDX = {}     # root -> (index file time, index): an index file is parsed again only when it changed
_BYID = {}    # {"key": index file times, "map": book id -> entry}
_SPINES = {}  # (epub path, mtime) -> its reading order: [{"href", "type", "label"}]

def init_module(env: dict):
    global UI, BI, IM
    ENV.update(env)
    UI, BI = env["templates"].env.globals.get("UI"), env["tools"]["built_ins"]
    for d in ("index", "covers", "library", "tmp"): (DATA / d).mkdir(parents=True, exist_ok=True)
    for f in (DATA / "tmp").iterdir(): f.unlink()   # downloads cut off by a restart
    IM = env["InterfaceManager"](nesting_level=1, db_path=f"""{env["data_dir"]}/im_registry.db""")
    IM.scripts.update({f"books_{k}": [fn] for k, fn in {"view": _h_view, "rescan": _h_rescan, "send": _h_send, "convert": _h_convert, "delete": _h_delete, "settings_save": _h_settings_save, "page": _h_page, "pos": _h_pos, "mode": _h_mode, "viewset": _h_viewset, "job": _h_job, "chapter": _h_chapter, "tpos": _h_tpos, "meta": _h_meta, "rate": _h_rate, "cover": _h_cover, "card": _h_card}.items()})

# --- Settings: roots and e-readers (one per line, "|" between fields - short enough to edit by hand) ---

def _settings() -> dict: return json.loads((DATA / "settings.json").read_text(encoding="utf-8")) if (DATA / "settings.json").exists() else {"roots": "Manga | ./data/_common/Manga | rw\nBooks | ./data/_common/Books | rw", "devices": ""}   # _common: the portal's shared, backed-up area
def _lines(text: str) -> list: return [[p.strip() for p in l.split("|")] for l in text.splitlines() if l.strip() and not l.strip().startswith("#")]

def roots() -> dict:
    """name -> {"name", "path", "writable"}. A root is used where it is; a read-only root is never written to (no upload, delete or conversion output)."""
    return {p[0]: {"name": p[0], "path": Path(p[1]).expanduser(), "writable": len(p) > 2 and p[2].lower() == "rw"} for p in _lines(_settings()["roots"]) if len(p) >= 2}

def devices() -> dict:
    """name -> {"name", "url", "folder"}: e-readers reachable over the network with CrossPoint's file transfer on (its Wi-Fi transfer screen shows the address)."""
    return {p[0]: {"name": p[0], "url": p[1].rstrip("/"), "folder": p[2] if len(p) > 2 and p[2] else "/"} for p in _lines(_settings()["devices"]) if len(p) >= 2}

def _root_path(root: dict, rel: str) -> Path:
    p = (root["path"] / rel).resolve()
    if not p.is_relative_to(root["path"].resolve()): raise HTTPException(400, "path outside the root")
    return p

# --- Comic pages: CBZ (zip), CBR / CB7 (bsdtar), folders of images ---

def _natural(s: str) -> list: return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", s)]

def _chapter_no(name: str) -> str:
    """The chapter number in a file or folder name: after Ch / Chapter / Ep / #, else the last number in it."""
    m = _CHAPTER.search(name) or re.search(r"(\d+(?:\.\d+)?)\D*$", name)
    return m.group(1) if m else ""

def _bsdtar() -> str:
    exe = shutil.which("bsdtar")
    if not exe: raise RuntimeError("CBR and CB7 are read with bsdtar (package libarchive-tools - free software), which is not installed on this server; or convert the file to CBZ")
    return exe

def _names(path: Path) -> list:
    """Every member of a comic archive, or the files of an image folder."""
    if path.is_dir(): return [f.name for f in path.iterdir() if f.is_file()]
    if path.suffix.lower() == ".cbz":
        with zipfile.ZipFile(path) as z: return z.namelist()
    return subprocess.run([_bsdtar(), "-tf", str(path)], capture_output=True, text=True, check=True).stdout.splitlines()

def _read(path: Path, name: str) -> bytes:
    if path.is_dir(): return (path / Path(name).name).read_bytes()
    if path.suffix.lower() == ".cbz":
        with zipfile.ZipFile(path) as z: return z.read(name)
    return subprocess.run([_bsdtar(), "-xOf", str(path), re.sub(r"([\[\]*?\\])", r"\\\1", name)], capture_output=True, check=True).stdout   # bsdtar reads member names as patterns

def _pages_of(names: list) -> list: return sorted((n for n in names if n.lower().endswith(IMG) and "__MACOSX" not in n and not posixpath.basename(n).startswith(".")), key=_natural)

# --- Reading metadata from the files ---

def _epub(path: Path) -> dict:
    with zipfile.ZipFile(path) as z:
        names = set(z.namelist())
        drm = "META-INF/rights.xml" in names or ("META-INF/encryption.xml" in names and any(a not in _FONT_OBFUSCATION for a in re.findall(r'Algorithm="([^"]+)"', z.read("META-INF/encryption.xml").decode("utf-8", "replace"))))
        opf_path = re.search(r'full-path="([^"]+)"', z.read("META-INF/container.xml").decode("utf-8", "replace")).group(1)
        opf = ET.fromstring(z.read(opf_path))
        ns = {"o": "http://www.idpf.org/2007/opf", "dc": "http://purl.org/dc/elements/1.1/"}
        md = opf.find("o:metadata", ns)
        metas = {m.get("name"): m.get("content", "") for m in md.findall("o:meta", ns) if m.get("name")}
        series = metas.get("calibre:series") or next((m.text or "" for m in md.findall("o:meta", ns) if m.get("property") == "belongs-to-collection"), "")
        items = {i.get("id"): i for i in opf.findall("o:manifest/o:item", ns)}
        cov = next((i for i in items.values() if "cover-image" in (i.get("properties") or "")), None) or items.get(metas.get("cover", ""))
        cover = z.read(posixpath.normpath(posixpath.join(posixpath.dirname(opf_path), unquote(cov.get("href"))))) if cov is not None and not drm else None
        return {"title": (md.findtext("dc:title", "", ns) or "").strip(), "authors": [e.text.strip() for e in md.findall("dc:creator", ns) if e.text], "language": md.findtext("dc:language", "", ns) or "",
                "series": series, "series_index": metas.get("calibre:series_index", ""), "drm": drm, "cover": cover}

def _epub_spine(path: Path) -> list:
    """The EPUB's reading order as paths inside the zip, with a label from its table of contents (EPUB 3 nav or EPUB 2 NCX) where one points at that file. Kept while the file is unchanged."""
    key = (str(path), path.stat().st_mtime_ns)
    if key in _SPINES: return _SPINES[key]
    with zipfile.ZipFile(path) as z:
        opf_path = re.search(r'full-path="([^"]+)"', z.read("META-INF/container.xml").decode("utf-8", "replace")).group(1)
        opf, base, ns = ET.fromstring(z.read(opf_path)), posixpath.dirname(opf_path), {"o": "http://www.idpf.org/2007/opf"}
        full = lambda href, rel=base: posixpath.normpath(posixpath.join(rel, unquote(href.split("#")[0])))
        items = {i.get("id"): i for i in opf.findall("o:manifest/o:item", ns)}
        labels = {}
        try:   # the table of contents only names the parts; a broken one leaves them numbered
            nav = next((i for i in items.values() if "nav" in (i.get("properties") or "").split()), None)
            ncx = items.get(opf.find("o:spine", ns).get("toc") or "") or next((i for i in items.values() if i.get("media-type") == "application/x-dtbncx+xml"), None)
            if nav is not None:
                navp = full(nav.get("href"))
                for a in ET.fromstring(z.read(navp)).iter("{http://www.w3.org/1999/xhtml}a"): labels.setdefault(full(a.get("href", ""), posixpath.dirname(navp)), " ".join("".join(a.itertext()).split()))
            elif ncx is not None:
                ncxp, n = full(ncx.get("href")), "{http://www.daisy.org/z3986/2005/ncx/}"
                for p in ET.fromstring(z.read(ncxp)).iter(f"{n}navPoint"): labels.setdefault(full(p.find(f"{n}content").get("src", ""), posixpath.dirname(ncxp)), " ".join((p.findtext(f"{n}navLabel/{n}text") or "").split()))
        except Exception: pass
        spine = [items[r.get("idref")] for r in opf.findall("o:spine/o:itemref", ns) if r.get("idref") in items]
        out = [{"href": full(i.get("href")), "type": i.get("media-type") or "application/xhtml+xml", "label": labels.get(full(i.get("href")), "")} for i in spine]
    _SPINES[key] = [{**s, "label": s["label"] or f"Part {k + 1}"} for k, s in enumerate(out)]
    return _SPINES[key]

def _comic(path: Path, base: Path) -> dict:
    """CBZ / CBR / CB7 or a folder of images. ComicInfo.xml when there is one; otherwise the folder holding the comic (below the root) is its series and the number in its name its place. The cover is made when first shown."""
    names = _names(path)
    ci_name = next((n for n in names if posixpath.basename(n).lower() == "comicinfo.xml"), None)
    ci = ET.fromstring(_read(path, ci_name)) if ci_name else None
    get = (lambda k: (ci.findtext(k) or "").strip()) if ci is not None else (lambda k: "")
    name = path.name if path.is_dir() else path.stem
    return {"title": get("Title") or name, "authors": [a.strip() for a in get("Writer").split(",") if a.strip()], "language": get("LanguageISO"), "series": get("Series") or (path.parent.name if path.parent != base else ""),
            "series_index": get("Number") or _chapter_no(name), "drm": False, "pages": len(_pages_of(names)), "rtl": get("Manga").lower() == "yesandrighttoleft"}   # ComicInfo's Manga field gives the reading direction

def _mobi(path: Path) -> dict:
    """MOBI / AZW3: title and author from the EXTH header, DRM from record 0's encryption field. KFX (Kindle's newer format) is marked: Kindle-only."""
    with path.open("rb") as f: head = f.read(262144)
    if head[:4] == b"\xeaDRM" or head[:4] == b"CONT": return {"title": "", "authors": [], "drm": True, "kindle_only": True}
    rec0 = int.from_bytes(head[78:82], "big")
    out = {"title": head[:32].split(b"\0")[0].decode("latin-1").replace("_", " "), "authors": [], "language": "", "drm": int.from_bytes(head[rec0 + 12:rec0 + 14], "big") != 0}
    if head[rec0 + 16:rec0 + 20] != b"MOBI": return out
    mlen = int.from_bytes(head[rec0 + 20:rec0 + 24], "big")
    if int.from_bytes(head[rec0 + 128:rec0 + 132], "big") & 0x40 and head[rec0 + 16 + mlen:rec0 + 20 + mlen] == b"EXTH":
        pos, count = rec0 + 16 + mlen + 12, int.from_bytes(head[rec0 + 24 + mlen:rec0 + 28 + mlen], "big")
        for _ in range(count):
            t, n = int.from_bytes(head[pos:pos + 4], "big"), int.from_bytes(head[pos + 4:pos + 8], "big")
            val = head[pos + 8:pos + n].decode("utf-8", "replace")
            if t == 100: out["authors"].append(val)
            elif t == 503: out["title"] = val
            elif t == 524: out["language"] = val
            pos += n
    return out

def _read_meta(path: Path, base: Path) -> dict:
    """Metadata for one file or image folder; one that cannot be read keeps its name and shows why (one damaged book does not stop the index)."""
    ext = ".images" if path.is_dir() else path.suffix.lower()
    try:
        m = _epub(path) if ext in (".epub", ".kepub") else _comic(path, base) if ext in COMIC else _mobi(path) if ext in (".mobi", ".azw", ".azw3", ".kfx") else {}
    except Exception as e: m = {"error": f"{type(e).__name__}: {e}"[:200]}
    return {"title": m.get("title") or (path.name if path.is_dir() else path.stem).replace("_", " "), "authors": m.get("authors", []), "language": m.get("language", ""), "series": m.get("series", ""), "series_index": m.get("series_index", ""),
            "drm": m.get("drm", False), "kindle_only": m.get("kindle_only", False), "pages": m.get("pages", 0), "rtl": m.get("rtl", False), "error": m.get("error", ""), "cover": m.get("cover")}

# --- Index (per root; only new or changed files and folders are read again) ---

def _bid(root: str, rel: str) -> str: return hashlib.sha1(f"{root}\n{rel}".encode()).hexdigest()[:16]
def _index_path(root: str) -> Path: return DATA / "index" / f"""{re.sub(r"[^A-Za-z0-9_-]", "_", root)}.json"""

def index(root: str) -> dict:
    p = _index_path(root)
    if not p.exists(): return {}
    t = p.stat().st_mtime_ns
    if _IDX.get(root, (None,))[0] != t: _IDX[root] = (t, json.loads(p.read_text(encoding="utf-8")))
    return _IDX[root][1]

def _write_json(p: Path, data):
    """Written beside the file, then put in its place in one step: a reader never sees a half-written index (the scan writes from a worker thread while pages are being drawn)."""
    tmp = p.with_name(f"{p.name}.{secrets.token_hex(3)}.tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
    os.replace(tmp, p)

def _write_index(root: str, idx: dict): _write_json(_index_path(root), idx)

def _save_cover(bid: str, data: bytes):
    with Image.open(io.BytesIO(data)) as im:
        im = im.convert("RGB")
        im.thumbnail((240, 360))
        im.save(DATA / "covers" / f"{bid}.jpg", "JPEG", quality=80)

def _comic_cover(b: dict, page: int = 0):
    path = book_path(b)
    pages = _pages_of(_names(path))
    if not pages: raise FileNotFoundError("no pages")
    _save_cover(f"""{b["id"]}{f"_p{page}" if page else ""}""", _read(path, pages[min(page, len(pages) - 1)]))

def _scan_root(root: dict) -> int:
    """Walks one root; returns how many files and folders were (re)read. A folder of page images (two or more, no book files beside them, not the root itself) is one comic.
    A file keeps its entry while its size and time are the same; an image folder while its time and page count are. Runs in a worker thread."""
    old, new, n, base = index(root["name"]), {}, 0, root["path"]
    for d, dirs, files in os.walk(base) if base.is_dir() else []:
        dirs[:] = sorted(x for x in dirs if not x.startswith("."))
        dp, files = Path(d), [f for f in files if not f.startswith(".")]
        imgs = [f for f in files if f.lower().endswith(IMG)]
        found = [(dp / f, (dp / f).stat()) for f in sorted(files) if Path(f).suffix.lower() in EXTS]
        found = [(p, st, [st.st_mtime, st.st_size]) for p, st in found]
        if len(imgs) >= 2 and not found and "metadata.opf" not in files and dp != base: found.append((dp, dp.stat(), [dp.stat().st_mtime, len(imgs)]))
        for path, st, key in found:
            rel = path.relative_to(base).as_posix()
            prev = old.get(rel)
            if prev and prev.get("key") == key: new[rel] = prev; continue
            bid, m = _bid(root["name"], rel), _read_meta(path, base)
            cover = m.pop("cover")
            (DATA / "covers" / f"{bid}.jpg").unlink(missing_ok=True)
            if cover:
                try: _save_cover(bid, cover)
                except Exception: pass   # an unreadable cover image: the card shows the title instead
            new[rel] = {**m, "id": bid, "root": root["name"], "rel": rel, "ext": ".images" if path.is_dir() else path.suffix.lower(), "size": sum((path / f).stat().st_size for f in imgs) if path.is_dir() else st.st_size,
                        "mtime": st.st_mtime, "key": key, "added": prev["added"] if prev else datetime.now().isoformat(timespec="seconds")}
            n += 1
            _SCAN["n"] += 1
    for rel in old.keys() - new.keys(): (DATA / "covers" / f"""{old[rel]["id"]}.jpg""").unlink(missing_ok=True)
    _write_index(root["name"], new)
    return n

async def rescan(only: str = "") -> int:
    async with _SCAN_LOCK:
        _SCAN["n"] = 0
        return sum([await asyncio.to_thread(_scan_root, r) for name, r in roots().items() if not only or name == only])

def _scan_job():
    """Indexing in the background (a large library takes a while the first time); the side bar shows its progress."""
    if _JOBS.get("_scan", {}).get("state") != "running": _spawn("_scan", _scan_all(), "Indexing...")

async def _scan_all() -> str: return f"{await rescan()} file(s) and folder(s) read"

def books(root: str = "", q: str = "", fmt: str = "") -> list:
    ql = q.lower()
    out = [b for name in roots() if not root or name == root for b in index(name).values()]
    out = [b for b in out if (not ql or ql in f"""{b["title"]} {" ".join(b["authors"])} {b["series"]} {b["rel"]}""".lower() or any(ql in t.lower() for t in _tags_of(b))) and (not fmt or b["ext"] == fmt)]   # tags: the book's own and its series'

    return sorted(out, key=lambda b: (b["series"].lower() or b["title"].lower(), _natural(str(b["series_index"])), _natural(b["title"])))

def _by_id() -> dict:
    idx = {n: index(n) for n in roots()}
    key = tuple(_IDX.get(n, (0,))[0] for n in idx)
    if _BYID.get("key") != key: _BYID.update(key=key, map={b["id"]: b for i in idx.values() for b in i.values()})
    return _BYID["map"]

def book(bid: str) -> dict:
    b = _by_id().get(bid)
    if not b: raise HTTPException(404, "book not found - rescan?")
    return b

def book_path(b: dict) -> Path: return _root_path(roots()[b["root"]], b["rel"])

def _drop_entry(b: dict):
    idx = dict(index(b["root"]))
    idx.pop(b["rel"], None)
    _write_index(b["root"], idx)

def _free(folder: Path, name: str) -> Path:
    p, n = folder / name, 2
    while p.exists(): p, n = folder / f"{Path(name).stem}-{n}{Path(name).suffix}", n + 1
    return p

def _zip_folder(folder: Path, dest: Path):
    with zipfile.ZipFile(dest, "w", zipfile.ZIP_STORED) as z:   # page images are compressed already
        for n in _pages_of(_names(folder)) + [x for x in _names(folder) if x.lower() == "comicinfo.xml"]: z.write(folder / n, n)

# --- Series and reading progress (per login) ---

def _positions() -> dict: return json.loads((DATA / "positions.json").read_text(encoding="utf-8")) if (DATA / "positions.json").exists() else {}
def _write_positions(pos: dict): _write_json(DATA / "positions.json", pos)
def _pos(user: str) -> dict: return _positions().get(user, {})

def _save_pos(user: str, b: dict, page: int):
    """The place in a comic; reaching its last page also marks it read, and that mark stays when it is read again from the start."""
    pos = _positions()
    mine = pos.setdefault(user, {})
    mine[b["id"]] = page = max(0, min(page, b["pages"] - 1))
    if page == b["pages"] - 1: mine.setdefault("_read", {})[b["id"]] = 1
    _write_positions(pos)

def _save_tpos(user: str, b: dict, part: int, frac: float, parts: int):
    """The place in a book read as text: the part (chapter) and how far down it is scrolled; the end of the last part marks it read."""
    pos = _positions()
    mine = pos.setdefault(user, {})
    mine[b["id"]], mine.setdefault("_frac", {})[b["id"]] = part, max(0.0, min(frac, 1.0))
    if part >= parts - 1 and frac >= 0.97: mine.setdefault("_read", {})[b["id"]] = 1
    _write_positions(pos)

def _series_key(b: dict) -> str: return f"""{b["root"]}|{b["series"]}""" if b["series"] else b["id"]
def _series_items(root: str, series: str) -> list: return [b for b in books(root) if b["series"] == series]
def _done(b: dict, pos: dict) -> bool: return b["id"] in pos.get("_read", {}) or (b["pages"] > 0 and pos.get(b["id"], -1) >= b["pages"] - 1)

def _groups(bs: list) -> list:
    """Books in sort order, one group per series (a book without a series is a group of its own)."""
    g = {}
    for b in bs: g.setdefault(_series_key(b), []).append(b)
    return list(g.values())

def _resume(items: list, pos: dict) -> tuple:
    """Where a series is picked up: the last item with a saved place (the item after it once that one is finished), else the first item. -> (item, page)"""
    last = max((i for i, b in enumerate(items) if b["id"] in pos), default=None)
    if last is None: return items[0], 0
    if _done(items[last], pos) and last + 1 < len(items): return items[last + 1], pos.get(items[last + 1]["id"], 0)
    return items[last], pos[items[last]["id"]]

def _next_in_series(b: dict) -> dict:
    if not b["series"]: return None
    items = _series_items(b["root"], b["series"])
    i = next(i for i, x in enumerate(items) if x["id"] == b["id"])
    return items[i + 1] if i + 1 < len(items) else None

def _mode(user: str, b: dict) -> str:
    """Reading mode: the series' own, else the login's setting for new series (pages / scroll), else the one last chosen anywhere, else pages."""
    m, new = _pos(user).get("_mode", {}), _view_opts(user)["new_mode"]
    return m.get(_series_key(b)) or (new if new != "last" else m.get("", "pages"))

def _dir(user: str, b: dict) -> str:
    """Page-turning direction: the series' own choice, else right to left when its ComicInfo.xml says so (entries indexed before this field existed have none), else left to right."""
    return _pos(user).get("_dir", {}).get(_series_key(b)) or ("rtl" if b.get("rtl") else "ltr")

def _view_opts(user: str) -> dict:
    """How pages are shown, per login: fit (pages mode: the whole page in view, or the full width) and w (scroll mode: page width in % of the reader, 0 = full width up to 900 px)."""
    return {"fit": "height", "w": 0, "new_mode": "last", "fs": 100, "look": "portal", "card": "m", **_pos(user).get("_view", {})}

def _readable(b: dict) -> bool: return b["ext"] in TEXT or (b["ext"] in COMIC and b["pages"] > 0)

def _progress(b: dict, pos: dict) -> str:
    if _done(b, pos): return "&#x2713; read"
    if b["ext"] in TEXT: return f"""part {pos[b["id"]] + 1}""" if b["id"] in pos and b["ext"] in (".epub", ".kepub") else b["ext"][1:]
    if b["ext"] not in COMIC or not b["pages"]: return b["ext"][1:]
    return f"""page {pos[b["id"]] + 1} / {b["pages"]}""" if b["id"] in pos else f"""{b["pages"]} p"""

# --- Tags, notes, ratings and chosen covers: kept beside the books, in .portal-books.json in the folder that holds them (a series' own folder), so they travel with the folder ---
# A read-only root is never written to: its file is kept under data/books/meta/<root>/<folder>/ instead. Tags and notes are shared by everyone who reads the library; ratings are per login (each person's own).

_MEMO = {}   # metadata file -> (mtime, parsed)
_SIDE = ".portal-books.json"

def _meta_file(b: dict) -> Path:
    r = roots()[b["root"]]
    folder = book_path(b).parent
    return folder / _SIDE if r["writable"] else DATA / "meta" / re.sub(r"[^A-Za-z0-9_-]", "_", b["root"]) / folder.relative_to(r["path"].resolve()) / "meta.json"

def _meta_all(p: Path) -> dict:
    if not p.exists(): return {}
    t = p.stat().st_mtime_ns
    if _MEMO.get(p, (None,))[0] != t: _MEMO[p] = (t, json.loads(p.read_text(encoding="utf-8")))
    return _MEMO[p][1]

def _mkey(b: dict, series: bool) -> str: return f"""series:{b["series"]}""" if series else Path(b["rel"]).name
def meta(b: dict, series: bool = False) -> dict:
    """{"tags": [...], "notes": "...", "rating": {login: 1-5}, "cover": {"bid", "page"} (series)} of one book, or (series=True, b = its first item) of its series."""
    return {"tags": [], "notes": "", "rating": {}, **_meta_all(_meta_file(b)).get(_mkey(b, series), {})}

def _meta_set(b: dict, series: bool, **kw):
    p = _meta_file(b)
    data = {**_meta_all(p), _mkey(b, series): {**meta(b, series), **kw}}
    p.parent.mkdir(parents=True, exist_ok=True)
    _write_json(p, data)

def _tags_of(b: dict) -> list: return meta(b)["tags"] + (meta(_series_items(b["root"], b["series"])[0], True)["tags"] if b["series"] else [])
def _stars(n: int) -> str: return "&#x2605;" * n + "&#x2606;" * (5 - n) if n else ""

# --- Send and convert (background; the detail view polls the job) ---

def _spawn(bid: str, coro, label: str):
    _JOBS[bid] = {"state": "running", "msg": label}   # set before the task starts, so the reply shows this job (and polls), not the last one
    async def run():
        try: _JOBS[bid] = {"state": "done", "msg": await coro}
        except Exception as e: _JOBS[bid] = {"state": "error", "msg": f"{type(e).__name__}: {e}"[:400]}
    t = asyncio.create_task(run())
    _TASKS.add(t)
    t.add_done_callback(_TASKS.discard)

async def send(b: dict, dev: dict) -> str:
    """Uploads a book to an e-reader running CrossPoint's file transfer. The device replaces a file of the same name, so the folder is listed first and a free name is used."""
    path, folder = book_path(b), dev["folder"]
    async with httpx.AsyncClient(timeout=httpx.Timeout(connect=5.0, read=300.0, write=300.0, pool=5.0)) as c:
        r = await c.get(f"""{dev["url"]}/api/files""", params={"path": folder})
        r.raise_for_status()
        listed = r.json()
        taken = {str(i.get("name", "")) for i in (listed if isinstance(listed, list) else listed.get("files", listed.get("entries", []))) if isinstance(i, dict)}
        name, n = path.name, 2
        while name in taken: name, n = f"{path.stem}-{n}{path.suffix}", n + 1
        r = await c.post(f"""{dev["url"]}/upload""", params={"path": folder}, files={"file": (name, path.read_bytes())})
        r.raise_for_status()
    return f"""Sent to {dev["name"]} as {folder.rstrip("/")}/{name}"""

async def convert(b: dict, fmt: str) -> str:
    """calibre's ebook-convert into the book's own root when it is writable, else the first writable root; never over an existing file."""
    exe = shutil.which("ebook-convert")
    if not exe: raise RuntimeError("calibre's ebook-convert is not installed on this server")
    src, rs = book_path(b), roots()
    dest_root = rs[b["root"]] if rs[b["root"]]["writable"] else next((r for r in rs.values() if r["writable"]), None)
    if not dest_root: raise RuntimeError("no writable root to put the converted file in (Settings: add one ending in | rw)")
    dest = _free((dest_root["path"] / b["rel"]).parent if dest_root is rs[b["root"]] else dest_root["path"], f"{src.stem}.{fmt}")
    dest.parent.mkdir(parents=True, exist_ok=True)
    proc = await asyncio.create_subprocess_exec(exe, str(src), str(dest), stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT)
    out, _ = await asyncio.wait_for(proc.communicate(), timeout=1800)
    if proc.returncode != 0: raise RuntimeError(out.decode("utf-8", "replace")[-400:])
    await rescan(dest_root["name"])
    return f"""Converted: {dest_root["name"]}/{dest.relative_to(dest_root["path"]).as_posix()}"""

# --- HTML ---

def _esc(s) -> str: return html.escape(str(s or ""))
def _post(action: str, **extra) -> str: return f"""hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals="{_esc(json.dumps({"type": f"books_{action}", "lvl": 1, **extra}))}\""""   # escaped: series names carry quotes and ampersands
def _size(n: int) -> str: return f"{n / 1048576:.1f} MB" if n > 1048576 else f"{n // 1024} KB"

def _cover_src(b: dict, m: dict) -> str: return f"""/module/books/cover/{m["cover"]["bid"]}?page={int(m["cover"]["page"])}""" if m.get("cover") else f"""/module/books/cover/{b["id"]}"""
def _badges(m: dict, user: str) -> str: return f"""<div class="bk-badges">{f'<span class="bk-stars">{_stars(m["rating"].get(user, 0))}</span>' if m["rating"].get(user) else ""}{"".join(f'<span class="bk-tag">{_esc(t)}</span>' for t in m["tags"][:3])}</div>""" if m["tags"] or m["rating"].get(user) else ""

def _card(b: dict, user: str) -> str:
    m = meta(b)
    badge = " &#x1F512;" if b["drm"] else ""
    return f"""<div class="bk-card" {_post("view", view="book", bid=b["id"])} title="{_esc(b["rel"])}"><div class="bk-cover"><span class="bk-ph">{_esc(b["title"][:40])}</span><img src="{_cover_src(b, m)}" loading="lazy" alt="" onerror="this.remove()"></div>
               <div class="bk-title">{_esc(b["title"])}{badge}</div><div class="status-label">{_esc(", ".join(b["authors"])[:60])}{" &#xB7; " + b["ext"][1:] if b["ext"] else ""}</div>{_badges(m, user)}</div>"""

def _series_card(items: list, pos: dict, user: str) -> str:
    b, m = items[0], meta(items[0], True)
    line = f"""{sum(1 for x in items if _done(x, pos))} / {len(items)} read""" if b["ext"] in COMIC else f"{len(items)} books"
    return f"""<div class="bk-card" {_post("view", view="series", root=b["root"], series=b["series"])} title="{_esc(b["series"])}"><div class="bk-cover"><span class="bk-ph">{_esc(b["series"][:40])}</span><img src="{_cover_src(b, m)}" loading="lazy" alt="" onerror="this.remove()"><span class="bk-count">{len(items)}</span></div>
               <div class="bk-title">{_esc(b["series"])}</div><div class="status-label">{line}</div>{_badges(m, user)}</div>"""

def _meta_form(b: dict, series: bool, user: str) -> str:
    """Your rating (tap a star; the same star again clears it), tags (comma-separated) and notes - for one book, or for its whole series."""
    m, what = meta(b, series), "series" if series else "book"
    stars = "".join(f"""<button class="bk-star{" bk-on" if m["rating"].get(user, 0) >= n else ""}" title="{n} of 5" {_post("rate", bid=b["id"], series=int(series), n=0 if m["rating"].get(user) == n else n)}>{"&#x2605;" if m["rating"].get(user, 0) >= n else "&#x2606;"}</button>""" for n in range(1, 6))
    others = ", ".join(f"{u} {r}/5" for u, r in m["rating"].items() if u != user)
    return f"""<form class="node-form bk-meta" {_post("meta", bid=b["id"], series=int(series))} hx-include="this">
                   <div class="row"><span class="status-label">Your rating</span>{stars}{f'<span class="status-label">{_esc(others)}</span>' if others else ""}</div>
                   <input name="tags" class="module-select" value="{_esc(", ".join(m["tags"]))}" placeholder="Tags for this {what}, comma-separated (romance, finished, reread...)">
                   <textarea name="notes" class="cm-input" rows="3" placeholder="Notes on this {what}">{_esc(m["notes"])}</textarea>
                   <div class="row"><button type="submit" class="ui-btn">Save</button><span id="bk-meta-msg-{int(series)}" class="status-label"></span></div></form>"""

def _grid_html(v: dict, user: str) -> str:
    bs = books(v.get("root", ""), v.get("q", ""), v.get("fmt", ""))
    gs, pos, limit = _groups(bs), _pos(user), int(v.get("limit") or 120)
    cards = "".join(_series_card(g, pos, user) if g[0]["series"] and (len(g) > 1 or g[0]["ext"] in COMIC) else _card(g[0], user) for g in gs[:limit])
    more = f"""<div style="grid-column:1/-1;text-align:center"><button class="ui-btn" {_post("view", **{**v, "limit": limit + 120})}>More ({len(gs) - limit})</button></div>""" if len(gs) > limit else ""
    empty = """<div class="list-empty" style="grid-column:1/-1">No books here yet. Add a root in Settings (it is indexed where it is), or upload into a writable root, then Rescan.</div>"""
    return f"""<div class="row"><span class="form-title">{_esc(v.get("root") or "All books")}</span><span class="status-label">{len(bs)} item(s){" matching " + _esc(v["q"]) if v.get("q") else ""}</span></div>
               <div class="bk-grid" style="--bk-card:{ {"s": "6rem", "m": "7.5rem", "l": "10.5rem"}.get(_view_opts(user)["card"], "7.5rem") }">{cards or empty}{more}</div>"""

def _series_html(v: dict, user: str) -> str:
    items, pos = _series_items(v.get("root", ""), v.get("series", "")), _pos(user)
    if not items: return _grid_html({"view": "grid"}, user)
    nxt, page = _resume(items, pos)
    go = f"""<button class="ui-btn" {_post("view", view="read", bid=nxt["id"])}>&#x25B6; {"Continue" if nxt["id"] in pos or nxt is not items[0] else "Start"}: {_esc(nxt["title"])}{f" ({'part' if nxt['ext'] in TEXT else 'page'} {page + 1})" if page else ""}</button>""" if _readable(nxt) else ""
    rows = "".join(f"""<div class="list-row row"><span class="status-label bk-num">{_esc(b["series_index"])}</span><span class="grow bk-link" {_post("view", view="read", bid=b["id"], **({"start": "0"} if _done(b, pos) else {})) if _readable(b) else _post("view", view="book", bid=b["id"])}>{_esc(b["title"])}</span><span class="status-label">{_progress(b, pos)}</span><button class="cm-qbtn" title="Details" {_post("view", view="book", bid=b["id"])}>&#x2139;</button></div>""" for b in items)
    return f"""<div class="row"><button class="ui-btn" {_post("view", view="grid", root=v.get("root", ""))}>&#x2190; Back</button><span class="form-title grow">{_esc(v["series"])}</span><span class="status-label">{len(items)} item(s) &#xB7; {_esc(v.get("root", ""))}</span></div>
               <div class="row" style="align-items:flex-start;gap:.8rem"><div class="bk-cover bk-cover-lg"><span class="bk-ph">{_esc(v["series"][:60])}</span><img src="{_cover_src(items[0], meta(items[0], True))}" alt="" onerror="this.remove()"></div><div class="grow"><div class="row">{go}</div>{_meta_form(items[0], True, user)}</div></div>{rows}"""

def _job_html(bid: str) -> str:
    j = _JOBS.get(bid)
    if not j: return ""
    poll = f"""<div {_post("job", bid=bid)} hx-trigger="load delay:3s"></div>""" if j["state"] == "running" else ""
    color = {"running": "var(--text_muted)", "done": "var(--accent)", "error": "#ff5f5f"}[j["state"]]
    msg = f"""Indexing - {_SCAN["n"]} read so far""" if bid == "_scan" and j["state"] == "running" else j["msg"]
    return f"""<div style="color:{color};font-size:.75rem">{"&#x25CC; " if j["state"] == "running" else ""}{_esc(msg)}</div>{poll}"""

def _book_html(b: dict, user: str) -> str:
    root, devs, calibre, folder = roots()[b["root"]], devices(), shutil.which("ebook-convert"), b["ext"] == ".images"
    lock_note = f"""<div class="info-bar">&#x1F512; Marked as DRM-protected{" (Kindle KFX)" if b["kindle_only"] else ""} by a format check. Send and Convert work as for any file; whether the reader or your calibre can open it is up to them.</div>""" if b["drm"] or b["kindle_only"] else ""   # information only - Books does not decide what you may do with your own files
    send = "".join(f"""<button class="ui-btn" {_post("send", bid=b["id"], device=d)}>&#x2192; {_esc(d)}</button>""" for d in devs) if not folder else ""
    send_row = f"""<div class="row"><span class="status-label">Send to:</span>{send}</div>""" if send else ("" if folder else """<div class="status-label">Send to an e-reader: add one in Settings (CrossPoint firmware, file transfer on).</div>""")
    conv = "".join(f"""<button class="ui-btn" {_post("convert", bid=b["id"], fmt=f)}>To {f.upper()}</button>""" for f in ("epub", "txt") if b["ext"] != f".{f}") if calibre and b["ext"] not in COMIC else ""
    conv_row = f"""<div class="row"><span class="status-label">Convert (calibre):</span>{conv}</div>""" if conv else ""
    read = f"""<button class="ui-btn" {_post("view", view="read", bid=b["id"])}>&#x1F4D6; Read</button>""" if _readable(b) else ""
    read_note = "" if _readable(b) or folder or b["ext"] in COMIC else f"""<div class="status-label">{b["ext"][1:].upper()} is not read in the browser{" - Convert to EPUB below, then read the EPUB" if calibre else " - with calibre installed it can be converted to EPUB and read here"}.</div>"""
    series = f"""<button class="ui-btn" {_post("view", view="series", root=b["root"], series=b["series"])}>Series</button>""" if b["series"] else ""
    what = f"""the folder {_esc(b["rel"])} and its {b["pages"]} page images""" if folder else _esc(b["rel"])
    delete = f"""<button class="ui-btn" style="color:#ff5f5f" {_post("delete", bid=b["id"])} hx-confirm="Delete {what} from {_esc(b["root"])}? It is removed from disk; this cannot be undone.">Delete</button>""" if root["writable"] else ""
    rows = "".join(f"""<tr><td class="status-label">{k}</td><td>{_esc(v)}</td></tr>""" for k, v in (("Authors", ", ".join(b["authors"])), ("Series", f"""{b["series"]} {b["series_index"]}""".strip()), ("Language", b["language"]), ("Format", "Folder of images" if folder else b["ext"][1:].upper()),
               ("Pages", b["pages"] or ""), ("Size", _size(b["size"])), ("File", f"""{b["root"]}/{b["rel"]}"""), ("Added", b["added"].replace("T", " ")), ("Problem", b["error"])) if v)
    return f"""<div class="row"><button class="ui-btn" {_post("view", view="grid")}>&#x2190; Back</button><span class="form-title grow">{_esc(b["title"])}</span></div>{lock_note}
               <div class="row" style="align-items:flex-start;gap:1rem"><div class="bk-cover bk-cover-lg"><span class="bk-ph">{_esc(b["title"][:60])}</span><img src="{_cover_src(b, meta(b))}" alt="" onerror="this.remove()"></div>
               <div class="grow"><table class="data-table">{rows}</table>
               <div class="row" style="margin-top:.4rem">{read}{series}<a class="ui-btn" href="/module/books/file/{b["id"]}" download>&#x2B07; Download{" (CBZ)" if folder else ""}</a>{delete}</div>{read_note}{send_row}{conv_row}<div id="bk-job">{_job_html(b["id"])}</div>{_meta_form(b, False, user)}</div></div>"""

_PAGES_JS = """<script>(function(){ var r = document.getElementById('bk-reader'); if (!r || r.dataset.ready) return; r.dataset.ready = 1;
    function go(d){ var p = parseInt(r.dataset.page) + d, n = parseInt(r.dataset.pages);
        if (p >= n && r.dataset.next) return htmx.ajax('POST', '/im/in', {values: {type: 'books_page', lvl: 1, bid: r.dataset.next, page: 0}, swap: 'none'});   // past the last page: the next chapter
        if (p < 0 || p >= n) return;
        htmx.ajax('POST', '/im/in', {values: {type: 'books_page', lvl: 1, bid: r.dataset.bid, page: p}, swap: 'none'}); }
    var fwd = r.dataset.dir === 'rtl' ? -1 : 1;   // right to left (manga): the left side and the left arrow go forward
    r.addEventListener('pointerup', function(e){ if (e.target.closest('button, details')) return; var b = r.getBoundingClientRect(), x = (e.clientX - b.left) / b.width; if (x < .33) go(-fwd); else if (x > .67) go(fwd); });   /* thirds of the reader, not of the window (a side bar may be open) */
    document.addEventListener('keydown', function k(e){ if (!document.body.contains(r)) return document.removeEventListener('keydown', k); if (e.key === ' ') go(1); if (e.key === 'ArrowRight') go(fwd); if (e.key === 'ArrowLeft') go(-fwd); }); })();</script>"""

_SCROLL_JS = """<script>(function(){ var r = document.getElementById('bk-reader'); if (!r || r.dataset.ready) return; r.dataset.ready = 1;
    var n = parseInt(r.dataset.pages), last = -1, t = null;
    function save(p){ if (last === n - 1 || p === last) return; last = p; clearTimeout(t);   // once the end is reached it stays the place (the chapter counts as read)
        t = setTimeout(function(){ htmx.ajax('POST', '/im/in', {values: {type: 'books_pos', lvl: 1, bid: r.dataset.bid, page: p}, swap: 'none'}); }, p === n - 1 ? 0 : 1200); }
    var io = new IntersectionObserver(function(es){ es.forEach(function(e){ if (e.isIntersecting) save(parseInt(e.target.dataset.n)); }); }, {rootMargin: '0px 0px -60% 0px'});   // the page crossing the top 40% of the screen is the one being read
    r.querySelectorAll('.bk-scroll img').forEach(function(i){ io.observe(i); });
    var end = r.querySelector('.bk-end'); if (end) new IntersectionObserver(function(es){ if (es[0].isIntersecting) save(n - 1); }).observe(end); })();</script>"""

def _view_menu(b: dict, mode: str, d: str, vo: dict, page: int = 0) -> str:
    """The reader's view options: scroll mode - page width; pages mode - fit and page-turning direction. Kept per login (direction per series)."""
    if mode == "scroll":
        w = int(vo["w"] or 0)
        opts = f"""<span class="status-label">Width</span><button class="ui-btn" {_post("viewset", bid=b["id"], key="w", val=max(30, (w or 100) - 10))}>&#x2212;</button><span class="status-label">{f"{w}%" if w else "auto"}</span><button class="ui-btn" {_post("viewset", bid=b["id"], key="w", val=min(100, (w or 90) + 10))}>+</button><button class="ui-btn" {_post("viewset", bid=b["id"], key="w", val=0)} title="Full width, up to 900 px">Auto</button>"""
    else:
        fit = "".join(f"""<button class="ui-btn{" bk-on" if vo["fit"] == f else ""}" {_post("viewset", bid=b["id"], key="fit", val=f)}>{label}</button>""" for f, label in (("height", "Whole page"), ("width", "Full width")))
        way = "".join(f"""<button class="ui-btn{" bk-on" if d == k else ""}" {_post("viewset", bid=b["id"], key="dir", val=k)} title="{tip}">{label}</button>""" for k, label, tip in (("ltr", "Left to right", "Tap right or press &#x2192; for the next page"), ("rtl", "Right to left", "Manga: tap left or press &#x2190; for the next page")))
        opts = f"""<span class="status-label">Fit</span>{fit}<span class="status-label">Pages turn</span>{way}"""
    opts += f"""<button class="ui-btn" {_post("cover", bid=b["id"], page=page)} title="{"The page in view (scroll mode: the page you are at)" if mode == "scroll" else "This page"} becomes the cover card">&#x1F5BC; Use page {page + 1} as cover</button><span id="bk-cover-msg" class="status-label"></span>"""
    opts += """<span class="status-label">New series open in</span>""" + "".join(f"""<button class="ui-btn{" bk-on" if vo["new_mode"] == k else ""}" {_post("viewset", bid=b["id"], key="new_mode", val=k)}>{label}</button>""" for k, label in (("scroll", "Scroll"), ("pages", "Pages"), ("last", "Last used")))
    return f"""<details class="bk-opts"><summary class="ui-btn" title="View: {"page width" if mode == "scroll" else "fit and direction"}">&#x2699;</summary><div class="row bk-opts-row">{opts}</div></details>"""

def _reader_html(b: dict, user: str, start: int = None) -> str:
    """Comic reader. Pages: one page at a time - tap the left or right third, or the arrow keys (direction per series: right to left for manga). Scroll: the pages one under another (webtoons); the page in view is remembered.
    The place is kept per login, the mode and direction per series, the view (fit, width) per login; past the last page (or at the end of the scroll) the next item of the series opens. start opens at that page instead of the saved place."""
    if b["ext"] in TEXT: return _text_reader_html(b, user, start)
    n, mode, nxt, d, vo = b["pages"], _mode(user, b), _next_in_series(b), _dir(user, b), _view_opts(user)
    page = max(0, min(_pos(user).get(b["id"], 0) if start is None else start, n - 1))
    back = _post("view", view="series", root=b["root"], series=b["series"]) if b["series"] else _post("view", view="book", bid=b["id"])
    nxt_btn = f"""<button class="ui-btn" {_post("page", bid=nxt["id"], page=0)}>Next: {_esc(nxt["title"])} &#x2192;</button>""" if nxt else """<span class="status-label">End of the series</span>"""
    head = f"""<div class="row bk-head"><button class="ui-btn" {back}>&#x2190; Back</button><span class="status-label grow">{_esc(b["title"])}{"" if mode == "scroll" else f" - page {page + 1} of {n}"}</span>{_view_menu(b, mode, d, vo, page)}<button class="ui-btn" {_post("mode", bid=b["id"], mode="pages" if mode == "scroll" else "scroll")} title="Reading mode for this series">{"&#x2194; Pages" if mode == "scroll" else "&#x2195; Scroll"}</button></div>"""
    if mode == "scroll":
        imgs = "".join(f"""<img src="/module/books/page/{b["id"]}/{i}" data-n="{i}" loading="lazy" alt="page {i + 1}" onload="this.dataset.loaded=1">""" for i in range(page, n))
        earlier = f"""<button class="ui-btn" {_post("view", view="read", bid=b["id"], start="0")}>&#x2191; Pages 1-{page}</button>""" if page else ""
        width = f""" style="--bk-w:{int(vo["w"])}%;--bk-max:none\"""" if vo["w"] else ""
        return f"""<div id="bk-reader" class="bk-reader" data-bid="{b["id"]}" data-pages="{n}">{head}{earlier}<div class="bk-scroll"{width}>{imgs}</div><div class="row bk-end">{nxt_btn}</div>{_SCROLL_JS}</div>"""
    prefetch = f"""<img src="/module/books/page/{b["id"]}/{page + 1}" alt="" hidden>""" if page + 1 < n else ""
    end = f"""<div class="row bk-end">{nxt_btn}</div>""" if page == n - 1 else ""
    return f"""<div id="bk-reader" class="bk-reader{" bk-fit-width" if vo["fit"] == "width" else ""}" data-bid="{b["id"]}" data-page="{page}" data-pages="{n}" data-dir="{d}" data-next="{nxt["id"] if nxt else ""}">{head}<img src="/module/books/page/{b["id"]}/{page}" alt="page {page + 1}">{end}{prefetch}{_PAGES_JS}</div>"""

_TEXT_JS = """<script>(function(){ var r = document.getElementById('bk-reader'), f = document.getElementById('bk-frame'); if (!r || !f || r.dataset.ready) return; r.dataset.ready = 1;
    var t = null;
    function look(d){ var s = getComputedStyle(document.body), st = d.createElement('style');   // portal colors and text size inside the book's page (same origin; the page's own scripts are blocked by its CSP)
        st.textContent = (r.dataset.look === 'book' ? '' : 'html,body{background:' + s.backgroundColor + ' !important;color:' + s.color + ' !important;} a{color:inherit !important;} ') + 'html{font-size:' + r.dataset.fs + '% !important;} body{line-height:1.55;max-width:44em;margin:0 auto !important;padding:1rem !important;overflow-wrap:break-word;} img,svg{max-width:100%;height:auto;} pre{white-space:pre-wrap !important;font-family:inherit;}';
        (d.head || d.documentElement).appendChild(st); }
    function init(){ var w = f.contentWindow, d = f.contentDocument; if (!d || !d.documentElement || w.location.href === 'about:blank' || d.bkReady) return; d.bkReady = 1;
        look(d);
        var h = function(){ return Math.max(1, d.documentElement.scrollHeight - w.innerHeight); };
        setTimeout(function(){ w.scrollTo(0, parseFloat(r.dataset.frac || 0) * h()); }, 50);   // after the styles above have laid the page out
        w.addEventListener('scroll', function(){ clearTimeout(t); t = setTimeout(function(){ htmx.ajax('POST', '/im/in', {values: {type: 'books_tpos', lvl: 1, bid: r.dataset.bid, ch: r.dataset.ch, n: r.dataset.n, frac: (w.scrollY / h()).toFixed(4)}, swap: 'none'}); }, 800); });
        d.addEventListener('keydown', function(e){ if (e.key === 'ArrowRight' && w.scrollY >= h() - 2 && r.dataset.next) htmx.ajax('POST', '/im/in', {values: JSON.parse(r.dataset.next), swap: 'none'}); }); }
    f.addEventListener('load', init);
    if (f.contentDocument && f.contentDocument.readyState === 'complete') init(); })();   /* a cached part can finish loading before this script runs */</script>"""

def _text_reader_html(b: dict, user: str, start: int = None) -> str:
    """A book read as text. EPUB: one part (chapter) at a time in a frame showing the book's own pages, where scripts never run; TXT as one part; PDF in the browser's own viewer.
    The part and how far down it is scrolled are kept per login; the text takes the portal's colors (or the book's own look) and a text size, both per login."""
    vo, pos, path = _view_opts(user), _pos(user), book_path(b)
    back = _post("view", view="series", root=b["root"], series=b["series"]) if b["series"] else _post("view", view="book", bid=b["id"])
    if b["ext"] == ".pdf": return f"""<div id="bk-reader" class="bk-reader"><div class="row bk-head"><button class="ui-btn" {back}>&#x2190; Back</button><span class="status-label grow">{_esc(b["title"])} - the browser's PDF viewer (the place is not kept; phone browsers may download it instead)</span></div><iframe id="bk-frame" class="bk-frame" src="/module/books/file/{b["id"]}?inline=1"></iframe></div>"""
    epub = b["ext"] in (".epub", ".kepub")
    parts = _epub_spine(path) if epub else [{"href": "", "label": "Text"}]
    if not parts: return f"""<div class="row"><button class="ui-btn" {back}>&#x2190; Back</button><span class="status-label">This EPUB lists no parts to read.</span></div>"""
    saved = pos.get(b["id"], 0)
    ch = max(0, min(saved if start is None else start, len(parts) - 1))
    frac = pos.get("_frac", {}).get(b["id"], 0) if ch == saved else 0
    nxt = _next_in_series(b) if ch == len(parts) - 1 else None
    nxt_vals = {"type": "books_chapter", "lvl": 1, "bid": b["id"], "ch": ch + 1} if ch + 1 < len(parts) else {"type": "books_view", "lvl": 1, "view": "read", "bid": nxt["id"]} if nxt else None
    src = f"""/module/books/epub/{b["id"]}/{quote(parts[ch]["href"])}""" if epub else f"""/module/books/text/{b["id"]}"""
    opts = "".join(f"""<option value="{k}"{" selected" if k == ch else ""}>{k + 1}. {_esc(p["label"][:60])}</option>""" for k, p in enumerate(parts))
    nav = f"""<button class="ui-btn" {_post("chapter", bid=b["id"], ch=ch - 1)} {"disabled" if ch == 0 else ""} title="Previous part">&#x2039;</button><select name="ch" class="module-select bk-parts" {_post("chapter", bid=b["id"])} hx-trigger="change">{opts}</select><button class="ui-btn" {_post("chapter", bid=b["id"], ch=ch + 1)} {"disabled" if ch + 1 >= len(parts) else ""} title="Next part">&#x203A;</button>""" if len(parts) > 1 else ""
    size = f"""<span class="status-label">Text</span><button class="ui-btn" {_post("viewset", bid=b["id"], key="fs", val=int(vo["fs"]) - 10)}>A&#x2212;</button><span class="status-label">{int(vo["fs"])}%</span><button class="ui-btn" {_post("viewset", bid=b["id"], key="fs", val=int(vo["fs"]) + 10)}>A+</button>"""
    looks = "".join(f"""<button class="ui-btn{" bk-on" if vo["look"] == k else ""}" {_post("viewset", bid=b["id"], key="look", val=k)}>{label}</button>""" for k, label in (("portal", "Portal colors"), ("book", "Book's own look")))
    menu = f"""<details class="bk-opts"><summary class="ui-btn" title="Text size and colors">&#x2699;</summary><div class="row bk-opts-row">{size}{looks}</div></details>"""
    drm = """<div class="info-bar">&#x1F512; Marked as DRM-protected: its text may not show here.</div>""" if b["drm"] else ""
    end = f"""<div class="row bk-end"><button class="ui-btn" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{json.dumps(nxt_vals)}'>{"Next part" if nxt_vals["type"] == "books_chapter" else "Next: " + _esc(nxt["title"])} &#x2192;</button></div>""" if nxt_vals else """<div class="row bk-end"><span class="status-label">The end</span></div>"""
    return f"""<div id="bk-reader" class="bk-reader bk-text" data-bid="{b["id"]}" data-ch="{ch}" data-n="{len(parts)}" data-frac="{frac}" data-fs="{int(vo["fs"])}" data-look="{vo["look"]}" data-next='{_esc(json.dumps(nxt_vals)) if nxt_vals else ""}'>
               <div class="row bk-head"><button class="ui-btn" {back}>&#x2190; Back</button><span class="status-label grow">{_esc(b["title"])}</span>{nav}{menu}</div>{drm}<iframe id="bk-frame" class="bk-frame" src="{src}"></iframe>{end}{_TEXT_JS}</div>"""

def _settings_html(msg: str = "") -> str:
    s, calibre, bsdtar = _settings(), shutil.which("ebook-convert"), shutil.which("bsdtar")
    note = f"""calibre's ebook-convert: {"found at " + _esc(calibre) if calibre else "not installed - conversion is off. calibre is free software (GPL-3); its command-line converter does not contact the internet (the desktop app's update check is not involved)."}
               bsdtar (CBR / CB7): {"found at " + _esc(bsdtar) if bsdtar else "not installed - CBR and CB7 are listed but cannot be opened (apt install libarchive-tools; free software, no network use)."}"""
    return f"""<div class="row"><button class="ui-btn" {_post("view", view="grid")}>&#x2190; Back</button><span class="form-title">Books settings</span><span class="status-label">{msg}</span></div>
               <form class="node-form" {_post("settings_save")}>
                   <label class="status-label">Roots - one per line: name | folder on this server | rw (writable) or ro (read-only). A root is indexed where it is; nothing is moved. A folder of page images is one comic (chapter), its parent folder the series.</label>
                   <textarea name="roots" class="cm-input mono" rows="5">{_esc(s["roots"])}</textarea>
                   <label class="status-label">E-readers - one per line: name | http://address shown on its Wi-Fi transfer screen | folder on the device (default /). For CrossPoint firmware.</label>
                   <textarea name="devices" class="cm-input mono" rows="3" placeholder="Reader | http://192.168.1.50 | /Books">{_esc(s["devices"])}</textarea>
                   <div class="row"><span class="status-label grow pre-wrap">{note}</span><button type="submit" class="ui-btn">Save</button></div></form>"""

_UPLOAD_JS = """<script>window.BK_upload = window.BK_upload || async function(inp){   // in batches, so a series of a few thousand page images goes up without one huge request; each file keeps its folder path
    var f = inp.closest('form'), msg = document.getElementById('bk-upload-msg'), files = Array.from(inp.files), done = {saved: 0, same: 0, renamed: 0, skipped: 0}, notes = [];
    for (var i = 0; i < files.length;) { var fd = new FormData(), paths = [], size = 0;
        fd.append('root', f.root.value); fd.append('into', f.into.value);
        while (i < files.length && paths.length < 40 && (size < 64e6 || !paths.length)) { fd.append('files', files[i]); paths.push(files[i].webkitRelativePath || files[i].name); size += files[i].size; i++; }
        fd.append('paths', JSON.stringify(paths)); fd.append('final', i >= files.length ? '1' : '');
        msg.textContent = 'Uploading ' + i + ' / ' + files.length + ' ...';
        var r = await fetch('/module/books/upload', {method: 'POST', body: fd});
        if (!r.ok) { msg.innerHTML = '<span style="color:#ff5f5f">Stopped at ' + (i - paths.length) + ' / ' + files.length + ': ' + r.status + ' ' + (await r.text()).slice(0, 200) + '</span>'; inp.value = ''; return; }
        var j = await r.json(); for (var k in done) done[k] += j[k]; notes = notes.concat(j.notes); }
    inp.value = '';
    var text = '&#x2713; ' + done.saved + ' added' + (done.same ? ', ' + done.same + ' already there' : '') + (done.renamed ? ', ' + done.renamed + ' kept beside a different file of the same name (-2)' : '') + (done.skipped ? ', ' + done.skipped + ' skipped' : '') + (notes.length ? '<br>' + notes.slice(0, 5).map(function(n){ return n.replace(/</g, '&lt;'); }).join('<br>') : ''), root = f.root.value;
    htmx.ajax('POST', '/im/in', {values: {type: 'books_view', lvl: 1, view: 'grid', root: root}, swap: 'none'}).then(function(){ var m = document.getElementById('bk-upload-msg'), s = document.querySelector('#bk-upload select[name=root]'); if (m) m.innerHTML = text; if (s) s.value = root; }); window.BK_upmsg = text; };   // the side bar is drawn again with the root's list; the result stays in it
if (!window.BK_upkeep) { window.BK_upkeep = 1; document.body.addEventListener('htmx:afterSettle', function(){ var m = document.getElementById('bk-upload-msg'); if (m && !m.innerHTML && window.BK_upmsg) m.innerHTML = window.BK_upmsg; }); }   /* the side bar is redrawn again when indexing ends */</script>"""

def _side_html(v: dict, user: str) -> str:
    """The library bar along the top (collapsible; closed at first on phones): search, roots, formats, card size, rescan, settings, and Add (upload) as a drop-down."""
    rs = roots()
    on = ' style="background:var(--accent);color:var(--bg)"'
    root_rows = f"""<button class="chip"{on if not v.get("root") else ""} {_post("view", view="grid")}>All</button>""" + "".join(f"""<button class="chip"{on if v.get("root") == n else ""} {_post("view", view="grid", root=n)} title="{"writable" if r["writable"] else "read-only"}">{_esc(n)} {len(index(n))}</button>""" for n, r in rs.items())
    sizes = "".join(f"""<button class="chip"{on if _view_opts(user)["card"] == k else ""} {_post("card", size=k)} title="Card size">{k.upper()}</button>""" for k in ("s", "m", "l"))
    fmts = sorted({b["ext"] for n in rs for b in index(n).values()})
    chips = "".join(f"""<button class="chip"{' style="background:var(--accent);color:var(--bg)"' if v.get("fmt") == f else ""} {_post("view", view="grid", root=v.get("root", ""), q=v.get("q", ""), fmt="" if v.get("fmt") == f else f)}>{f[1:]}</button>""" for f in fmts)
    upload_opts = "".join(f"""<option value="{_esc(n)}"{" selected" if v.get("root") == n else ""}>{_esc(n)}</option>""" for n, r in rs.items() if r["writable"])   # the root being looked at
    upload = f"""<form id="bk-upload" class="node-form" onsubmit="return false"><div class="row"><select name="root" class="module-select grow">{upload_opts}</select></div>
                   <input name="into" class="module-select" placeholder="Into folder (optional), e.g. My Series" title="A folder below the root; made when new. Chapters of a series: put the series name here and pick the chapter folders.">
                   <div class="row"><label class="ui-btn" title="Chapter folders of page images (or a series folder holding them) - kept exactly as they are">&#x1F4C1; Folder<input type="file" webkitdirectory multiple hidden onchange="BK_upload(this)"></label><label class="ui-btn" title="Book files (EPUB, CBZ, PDF ...), or page images when Into folder names the chapter">&#x1F4C4; Files<input type="file" multiple hidden accept="{",".join(sorted(EXTS | set(IMG)))}" onchange="BK_upload(this)"></label></div><div id="bk-upload-msg" class="status-label"></div></form>{_UPLOAD_JS}""" if upload_opts else """<div class="status-label">Adding books needs a writable root (Settings: a root line ending in | rw).</div>"""
    scanning = _job_html("_scan") if _JOBS.get("_scan", {}).get("state") == "running" else ""
    return f"""<div class="row bk-bar"><form {_post("view", view="grid", root=v.get("root", ""), fmt=v.get("fmt", ""))}><input name="q" value="{_esc(v.get("q", ""))}" class="module-select bk-q" placeholder="Title, author, series, tag"></form>{root_rows}<span class="bk-sep"></span>{chips}<span class="bk-sep"></span>{sizes}<span class="grow"></span>
                   <button class="ui-btn" {_post("rescan")} title="Reads new and changed files and folders in every root">&#x21BB;</button><button class="ui-btn" {_post("view", view="settings")} title="Settings">&#x2699;</button>
                   <details class="bk-add"><summary class="ui-btn">+ Add</summary><div class="bk-add-pop">{upload}</div></details></div><div id="bk-scan-msg">{scanning}</div>"""

async def _view(request) -> dict: return await ENV["get_state"](request, scope="user", namespace="books", key="view") or {"view": "grid"}

def _main_html(request, v: dict) -> str:
    user, b = request.state.user.username, _by_id().get(v.get("bid", ""))
    if v.get("view") == "settings": return _settings_html() if request.state.user.role == "admin" else _grid_html(v, user)
    if v.get("view") in ("book", "read") and not b: return _grid_html({"view": "grid"}, user)   # the book is gone since (moved, deleted, its root removed)
    if v.get("view") == "book": return _book_html(b, user)
    if v.get("view") == "series": return _series_html(v, user)
    if v.get("view") == "read": return _reader_html(b, user, int(v["start"]) if v.get("start") else None)
    return _grid_html(v, user)

async def _show(request, imr, v: dict, main: str = None):
    await ENV["set_state"](request, v, scope="user", namespace="books", key="view")
    imr.oob(main if main is not None else _main_html(request, v), "bk-main")
    return imr.oob(_side_html(v, request.state.user.username), "bk-side")

# --- Intent handlers ---

async def _h_view(request, payload, imr): return await _show(request, imr, {k: payload[k] for k in ("view", "root", "q", "fmt", "bid", "limit", "series", "start") if payload.get(k)})

async def _h_rescan(request, payload, imr):
    _scan_job()
    return imr.oob(_job_html("_scan"), "bk-scan-msg")

async def _h_send(request, payload, imr):
    b, dev = book(payload["bid"]), devices()[payload["device"]]
    _spawn(b["id"], send(b, dev), f"""Sending to {dev["name"]}...""")
    return imr.oob(_job_html(b["id"]), "bk-job")

async def _h_convert(request, payload, imr):
    b = book(payload["bid"])
    _spawn(b["id"], convert(b, payload["fmt"]), f"""Converting to {payload["fmt"].upper()} (calibre)...""")
    return imr.oob(_job_html(b["id"]), "bk-job")

async def _h_job(request, payload, imr):
    """Poll target of a running job; when indexing ends, the open view is shown again with what was found."""
    if payload["bid"] != "_scan": return imr.oob(_job_html(payload["bid"]), "bk-job")
    if _JOBS["_scan"]["state"] != "running": await _show(request, imr, await _view(request))
    return imr.oob(_job_html("_scan"), "bk-scan-msg")

async def _h_delete(request, payload, imr):
    b = book(payload["bid"])
    if not roots()[b["root"]]["writable"]: raise HTTPException(403, "read-only root")
    shutil.rmtree(book_path(b)) if b["ext"] == ".images" else book_path(b).unlink()
    (DATA / "covers" / f"""{b["id"]}.jpg""").unlink(missing_ok=True)
    _drop_entry(b)
    return await _show(request, imr, {"view": "grid", "root": b["root"]})

async def _h_settings_save(request, payload, imr):
    if request.state.user.role != "admin": return imr
    (DATA / "settings.json").write_text(json.dumps({"roots": payload.get("roots", ""), "devices": payload.get("devices", "")}, indent=1), encoding="utf-8")
    for r in roots().values():
        if r["writable"]: r["path"].mkdir(parents=True, exist_ok=True)
    _scan_job()
    return await _show(request, imr, {"view": "settings"}, _settings_html("saved - indexing in the background"))

async def _h_page(request, payload, imr):
    """A comic page turned, or the next chapter opened: remembered for this login, then shown."""
    b, user = book(payload["bid"]), request.state.user.username
    _save_pos(user, b, int(payload["page"]))
    await ENV["set_state"](request, {"view": "read", "bid": b["id"]}, scope="user", namespace="books", key="view")
    return imr.oob(_reader_html(b, user), "bk-main")

async def _h_pos(request, payload, imr):
    """Scroll reading: the page in view is stored; nothing is redrawn."""
    _save_pos(request.state.user.username, book(payload["bid"]), int(payload["page"]))
    return imr

async def _h_viewset(request, payload, imr):
    """A view option from the reader's menu: dir (this series), fit or w (this login); the reader is shown again at the same place."""
    b, user, key, val = book(payload["bid"]), request.state.user.username, payload["key"], str(payload.get("val", ""))
    pos = _positions()
    mine = pos.setdefault(user, {})
    if key == "dir": mine.setdefault("_dir", {})[_series_key(b)] = "rtl" if val == "rtl" else "ltr"
    elif key == "fit": mine.setdefault("_view", {})["fit"] = "width" if val == "width" else "height"
    elif key == "new_mode": mine.setdefault("_view", {})["new_mode"] = val if val in ("scroll", "pages") else "last"
    elif key == "w": mine.setdefault("_view", {})["w"] = max(30, min(100, int(val))) if int(val or 0) else 0
    elif key == "fs": mine.setdefault("_view", {})["fs"] = max(60, min(200, int(val)))
    elif key == "look": mine.setdefault("_view", {})["look"] = "book" if val == "book" else "portal"
    elif key == "card": mine.setdefault("_view", {})["card"] = val if val in ("s", "m", "l") else "m"
    _write_positions(pos)
    return imr.oob(_reader_html(b, user), "bk-main")

async def _h_chapter(request, payload, imr):
    """Another part of a book read as text: shown from its top, and remembered."""
    b, user = book(payload["bid"]), request.state.user.username
    n = len(_epub_spine(book_path(b))) if b["ext"] in (".epub", ".kepub") else 1
    _save_tpos(user, b, max(0, min(int(payload["ch"]), n - 1)), 0.0, n)
    await ENV["set_state"](request, {"view": "read", "bid": b["id"]}, scope="user", namespace="books", key="view")
    return imr.oob(_reader_html(b, user), "bk-main")

async def _h_tpos(request, payload, imr):
    """Scrolling in a book read as text: the part and the place in it are stored; nothing is redrawn."""
    _save_tpos(request.state.user.username, book(payload["bid"]), int(payload["ch"]), float(payload["frac"]), int(payload["n"]))
    return imr

async def _h_meta(request, payload, imr):
    """Tags and notes of a book or (series=1) its series, kept in the folder's .portal-books.json."""
    b, series = book(payload["bid"]), str(payload.get("series")) == "1"
    _meta_set(b, series, tags=[t.strip() for t in str(payload.get("tags", "")).split(",") if t.strip()], notes=str(payload.get("notes", "")).strip())
    return imr.oob("&#x2713; saved", f"""bk-meta-msg-{int(series)}""")

async def _h_rate(request, payload, imr):
    """This login's rating of a book or its series (0 clears it); the view is drawn again."""
    b, series, user, n = book(payload["bid"]), str(payload.get("series")) == "1", request.state.user.username, max(0, min(5, int(payload.get("n") or 0)))
    rating = {k: v for k, v in meta(b, series)["rating"].items() if k != user}
    _meta_set(b, series, rating={**rating, **({user: n} if n else {})})
    return await _show(request, imr, await _view(request))

async def _h_cover(request, payload, imr):
    """A comic page chosen as its series' cover (or the book's own, when it has no series)."""
    b, page = book(payload["bid"]), int(payload.get("page") or 0)
    first = _series_items(b["root"], b["series"])[0] if b["series"] else b
    _meta_set(first, bool(b["series"]), cover={"bid": b["id"], "page": page})
    return imr.oob(f"""&#x2713; page {page + 1} is the {"series'" if b["series"] else "book's"} cover""", "bk-cover-msg")

async def _h_card(request, payload, imr):
    user = request.state.user.username
    pos = _positions()
    pos.setdefault(user, {}).setdefault("_view", {})["card"] = payload.get("size") if payload.get("size") in ("s", "m", "l") else "m"
    _write_positions(pos)
    return await _show(request, imr, await _view(request))

async def _h_mode(request, payload, imr):
    """Pages / scroll for this series - and the default for series not yet set."""
    b, user = book(payload["bid"]), request.state.user.username
    pos = _positions()
    modes = pos.setdefault(user, {}).setdefault("_mode", {})
    modes[_series_key(b)] = modes[""] = "scroll" if payload.get("mode") == "scroll" else "pages"
    _write_positions(pos)
    return imr.oob(_reader_html(b, user), "bk-main")

# --- Routes ---

@router.get("/")
async def root(request: Request):
    v = await _view(request)
    if not any(index(n) for n in roots()): _scan_job()
    bar = UI.toolbar(side="top", content=f"""<div id="bk-side" class="bk-top">{_side_html(v, request.state.user.username)}</div>""", size="3.2rem", overlay=False, start_open=True, id="bk-topbar", nesting_level=1, phone_closed=True)   # phones: the reader first; the bar opens from its arrow
    theme = await ENV["resolve_theme"](request, module_ns="books")
    return ENV["templates"].TemplateResponse(name="base.html", request=request, context={"request": request, "user": request.state.user, "nesting_level": 1, "shell_id": IM.branch_id, "toolbars": {"top": bar}, "content": f"""<div id="bk-main" class="scroll-pane">{_main_html(request, v)}</div>""", "extra_css": CSS, "theme": theme, "theme_resolved": True})
    #return ENV["templates"].TemplateResponse(name="base.html", request=request, context={"request": request, "user": request.state.user, "nesting_level": 1, "shell_id": IM.branch_id, "toolbars": {"top": bar}, "content": f"""<div id="bk-main" class="scroll-pane">{_main_html(request, v)}</div>""", "extra_css": CSS, "PWA": True, "manifest_path": '<link rel="manifest" href="/module/books/manifest.json">'})

# --- PWA launcher (install Books as its own full-screen app, separate from the Portal PWA) ---

_BOOKS_MANIFEST = {"name": "Books", "short_name": "Books", "scope": "/module/books/", "start_url": "/module/books/", "display": "fullscreen", "orientation": "portrait-primary", "background_color": "#020408", "theme_color": "#020408", "icons": [{"src": "/static/icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any maskable"}, {"src": "/static/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"}]}

@router.get("/manifest.json")
async def books_manifest(): return Response(json.dumps(_BOOKS_MANIFEST), media_type="application/manifest+json")

@router.get("/cover/{bid}")
async def cover(bid: str, page: int = 0):
    """A comic's cover (its first page, or the page chosen as cover) is made the first time it is asked for, so indexing a large library stays quick."""
    p = DATA / "covers" / f"""{re.sub(r"[^0-9a-f]", "", bid)}{f"_p{page}" if page else ""}.jpg"""
    if not p.exists():
        b = _by_id().get(bid)
        if not b or b["ext"] not in COMIC or not b["pages"]: raise HTTPException(404)
        try: await asyncio.to_thread(_comic_cover, b, page)
        except Exception: raise HTTPException(404)   # an unreadable page: the card shows the title
    return FileResponse(p, media_type="image/jpeg", headers={"Cache-Control": "private, max-age=86400"})

@router.get("/file/{bid}")
async def download(bid: str, inline: int = 0):
    """The file itself (inline=1: shown by the browser, as the PDF reader uses it); a folder of images as a CBZ made for this download (removed once sent)."""
    b = book(bid)
    path = book_path(b)
    if not path.is_dir(): return FileResponse(path, filename=path.name, content_disposition_type="inline" if inline else "attachment")
    tmp = DATA / "tmp" / f"{bid}-{secrets.token_hex(4)}.cbz"
    await asyncio.to_thread(_zip_folder, path, tmp)
    return FileResponse(tmp, filename=f"{path.name}.cbz", background=BackgroundTask(tmp.unlink, missing_ok=True))

@router.get("/page/{bid}/{n}")
async def page(bid: str, n: int):
    b = book(bid)
    if b["ext"] not in COMIC: raise HTTPException(400, "not a comic")
    path = book_path(b)
    pages = _pages_of(await asyncio.to_thread(_names, path))
    if not 0 <= n < len(pages): raise HTTPException(404)
    mime, cache = _MIME[Path(pages[n]).suffix.lower()], {"Cache-Control": "private, max-age=3600"}
    if path.is_dir(): return FileResponse(path / pages[n], media_type=mime, headers=cache)
    return Response(await asyncio.to_thread(_read, path, pages[n]), media_type=mime, headers=cache)

@router.get("/epub/{bid}/{inner:path}")
async def epub_part(bid: str, inner: str):
    """A file inside an EPUB (a part's page, its styles, images, fonts), for the reader's frame. The book's scripts are blocked (Content-Security-Policy)."""
    b = book(bid)
    if b["ext"] not in (".epub", ".kepub"): raise HTTPException(400, "not an EPUB")
    path, name = book_path(b), posixpath.normpath(inner)
    def read():
        with zipfile.ZipFile(path) as z: return z.read(name)
    try: data = await asyncio.to_thread(read)
    except KeyError: raise HTTPException(404)
    mime = next((s["type"] for s in _epub_spine(path) if s["href"] == name), None) or mimetypes.guess_type(name)[0] or "application/octet-stream"
    return Response(data, media_type=mime, headers={"Content-Security-Policy": _EPUB_CSP, "Cache-Control": "private, max-age=3600"})

@router.get("/text/{bid}")
async def text_file(bid: str):
    """A TXT book as one page for the reader's frame (UTF-8, else Windows-1252)."""
    b = book(bid)
    if b["ext"] != ".txt": raise HTTPException(400, "not a TXT file")
    raw = await asyncio.to_thread(book_path(b).read_bytes)
    try: t = raw.decode("utf-8")
    except UnicodeDecodeError: t = raw.decode("cp1252", "replace")
    return HTMLResponse(f"""<!doctype html><html><head><meta charset="utf-8"><title>{_esc(b["title"])}</title></head><body><pre>{html.escape(t)}</pre></body></html>""", headers={"Content-Security-Policy": _EPUB_CSP})

def _upload_rel(into: str, rel: str) -> str:
    """Where an uploaded file goes below the root: its folder path as the browser sent it (a folder upload keeps the folders), below the optional Into folder. "" when it may not be stored."""
    parts = [x for x in f"{into}/{rel}".replace("\\", "/").split("/") if x.strip() and x != "."]
    if not parts or any(x == ".." or x.startswith(".") or x == "__MACOSX" for x in parts): return ""
    name = parts[-1].lower()
    if not (Path(name).suffix in EXTS or name.endswith(IMG) or name == "comicinfo.xml"): return ""
    return "/".join(parts)

@router.post("/upload")
async def upload(request: Request):
    """One batch of an upload into a writable root. Folders are kept as they are (a chapter folder of page images stays one); nothing is converted.
    A file already there with the same size is left alone (an upload repeated after a break); a different file of the same name is kept beside it as -2. The last batch indexes the root again."""
    form = await request.form(max_files=200, max_fields=50)
    r = roots().get(form.get("root", ""))
    if not r or not r["writable"]: raise HTTPException(400, "pick a writable root")
    out, into = {"saved": 0, "same": 0, "renamed": 0, "skipped": 0, "notes": []}, str(form.get("into", "")).strip()
    for f, rel in zip(form.getlist("files"), json.loads(form.get("paths", "[]"))):
        rel = _upload_rel(into, rel)
        if not rel or (rel.lower().endswith(IMG) and "/" not in rel):
            out["skipped"] += 1
            out["notes"].append(f"{f.filename}: " + ("page images need a folder - pick the chapter folder, or name it in Into folder" if rel else "not a book, comic page or ComicInfo.xml"))
            continue
        dest, data = _root_path(r, rel), await f.read()
        dest.parent.mkdir(parents=True, exist_ok=True)
        if dest.exists() and dest.stat().st_size == len(data): out["same"] += 1; continue
        if dest.exists(): dest, out["renamed"] = _free(dest.parent, dest.name), out["renamed"] + 1
        dest.write_bytes(data)
        out["saved"] += 1
    if form.get("final"): _scan_job()
    return out

CSS = """
.bk-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(var(--bk-card, 7.5rem),1fr));gap:.6rem;align-items:start;}
.bk-top{height:100%;overflow-y:auto;padding:.25rem .5rem;box-sizing:border-box;}
.bk-bar{flex-wrap:wrap;gap:.3rem;align-items:center;}
.bk-q{width:14rem;margin:0;}
.bk-sep{width:1px;align-self:stretch;background:var(--border);margin:0 .15rem;}
.bk-add{position:relative;}
.bk-add > summary{list-style:none;}
.bk-add-pop{position:absolute;right:0;top:110%;z-index:20;width:min(20rem,90vw);background:var(--bg_panel, var(--bg));border:var(--border-thick) solid var(--border);border-radius:var(--radius);padding:.4rem;}
.bk-badges{display:flex;flex-wrap:wrap;gap:.2rem;align-items:center;}
.bk-stars{color:#ffcc00;font-size:.7rem;letter-spacing:.05rem;}
.bk-tag{font-size:.6rem;padding:0 .3rem;border-radius:1rem;border:var(--border-thick) solid var(--border);color:var(--text_muted);}
.bk-star{background:none;border:none;color:#ffcc00;font-size:1.1rem;cursor:pointer;padding:0 .05rem;}
.bk-meta{margin-top:.5rem;}
.bk-card{cursor:pointer;display:flex;flex-direction:column;gap:.15rem;min-width:0;}
.bk-card:hover .bk-cover{border-color:var(--accent);}
.bk-cover{position:relative;aspect-ratio:2/3;border:var(--border-thick) solid var(--border);border-radius:var(--radius);overflow:hidden;background:var(--glass);display:flex;align-items:center;justify-content:center;}
.bk-cover img{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;}
.bk-cover-lg{width:11rem;flex-shrink:0;}
.bk-count{position:absolute;top:.25rem;right:.25rem;z-index:1;background:var(--accent);color:var(--bg);border-radius:1rem;padding:0 .35rem;font-size:.65rem;font-weight:700;}
.bk-ph{padding:.4rem;font-size:.7rem;text-align:center;color:var(--text_muted);overflow-wrap:anywhere;}
.bk-title{font-size:.78rem;font-weight:600;overflow:hidden;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;}
.bk-num{min-width:2.5rem;}
.bk-link{cursor:pointer;}
.bk-link:hover{color:var(--accent);}
.bk-reader{display:flex;flex-direction:column;align-items:center;gap:.3rem;user-select:none;}
.bk-head{width:100%;}
.bk-reader > img{max-width:100%;max-height:calc(100vh - 7rem);object-fit:contain;}
.bk-reader.bk-fit-width > img{width:100%;max-height:none;}
.bk-scroll{display:flex;flex-direction:column;align-items:center;width:100%;}
.bk-scroll img{display:block;width:var(--bk-w, 100%);max-width:var(--bk-max, 900px);height:auto;}
.bk-opts{position:relative;}
.bk-opts > summary{list-style:none;}
.bk-opts-row{position:absolute;right:0;top:100%;z-index:5;background:var(--bg);border:var(--border-thick) solid var(--border);border-radius:var(--radius);padding:.3rem;flex-wrap:wrap;width:max-content;max-width:90vw;}
.bk-on{border-color:var(--accent);color:var(--accent);}
.bk-scroll img:not([data-loaded]){min-height:60vh;}
.bk-end{justify-content:center;padding:1rem 0;}
.bk-frame{width:100%;height:calc(100vh - 8rem);border:none;background:transparent;}
.bk-parts{width:auto;max-width:14rem;}
"""
