from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import Counter, defaultdict

GT = chr(62)                       # ">"
QUOT = chr(34) + chr(39)           # comillas " y '  (para regex sin romper el shell)
BOM = chr(0xFEFF) if False else "\ufeff"  # len 1, para deteccion de BOM

ASSET_EXT = (
    ".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".ogg", ".mp3", ".wav",
    ".flac", ".m4a", ".mp4", ".webm", ".woff", ".ttf", ".otf", ".eot",
    ".json", ".js", ".css", ".html", ".htm", ".ico", ".xml", ".bin", ".txt",
    ".cur", ".glb", ".gltf", ".wasm", ".webmanifest", ".manifest", ".map",
    ".jsm", ".br", ".gz", ".zzz", ".woff2",
)


def default_root() -> str:
    return os.path.dirname(os.path.abspath(__file__))


def parse_args(argv):
    ap = argparse.ArgumentParser(description="Detecta/corrige deps rotas de los juegos")
    ap.add_argument("--root", default=default_root())
    ap.add_argument("--apply", action="store_true", help="Aplica las correcciones seguras")
    ap.add_argument("--apply-ambiguous", action="store_true",
                    help="Con --apply, resuelve las ambiguas usando el primer candidato")
    ap.add_argument("--games", default="", help="Solo estos juegos (comas)")
    ap.add_argument("--json", default="", help="Guarda informe JSON en esa ruta")
    ap.add_argument("--ignore", default="", help="Regex separadas por coma de refs a ignorar")
    ap.add_argument("--max-missing", type=int, default=60)
    ap.add_argument("--full-missing", action="store_true")
    ap.add_argument("--js-base", choices=("root", "file", "auto"), default="auto",
                    help="Base para resolver strings en JS (auto = root salvo import())")
    return ap.parse_args(argv)


# ---------------------------------------------------------------- indexado ---
class Index:
    def __init__(self, root):
        self.root = root
        self.files = {}       # lower(abs) -> abs real
        self.dirs = {}        # lower(abs) -> abs real
        self.basenames = {}   # lower(name) -> [abs real]
        self.games = set()    # nombres de juego (primer nivel)

    def build(self):
        stack = [self.root]
        while stack:
            d = stack.pop()
            try:
                names = os.listdir(d)
            except OSError:
                continue
            for n in names:
                if n == ".git":
                    continue
                p = os.path.join(d, n)
                try:
                    isdir = os.path.isdir(p)
                except OSError:
                    isdir = False
                if isdir:
                    self.dirs.setdefault(p.lower(), p)
                    stack.append(p)
                else:
                    self.files[p.lower()] = p
                    self.basenames.setdefault(os.path.basename(p).lower(), []).append(p)
        self.games = {self.game_of(p) for p in self.files.values()}
        return self

    def game_of(self, path):
        rel = os.path.relpath(path, self.root)
        return rel.split(os.sep)[0]

    def game_root(self, path):
        return os.path.join(self.root, self.game_of(path))


# ------------------------------------------------------------ lectura/escritura ---
def read_bytes(path):
    try:
        with open(path, "rb") as fh:
            return fh.read(50_000_000)
    except OSError:
        return None


def decode(raw: bytes):
    for enc, bom in (("utf-8-sig", True), ("utf-8", False), ("cp1252", False)):
        try:
            txt = raw.decode(enc)
            return txt, (enc == "utf-8-sig"), "utf-8"
        except UnicodeDecodeError:
            continue
    return raw.decode("utf-8", errors="replace"), False, "utf-8"


def encode(txt, had_bom):
    data = txt.encode("utf-8")
    if had_bom:
        data = "\ufeff".encode("utf-8") + data
    return data


# ------------------------------------------------------------------- escaneo ---
class Scanner:
    def __init__(self, idx, args):
        self.idx = idx
        self.args = args
        self.counts = Counter()
        self.by_file = defaultdict(list)      # fref -> [(start, end, newtext)]
        self.fixes = []                        # (status, game, fref, ref, newref)
        self.ambiguous = []
        self.missing = Counter()               # ref -> n
        self.missing_info = {}                 # ref -> (game, base)
        self.absolut = []
        self.external = []
        self.dynamic = 0
        self.ignored = []
        self.game_filter = {g.strip() for g in args.games.split(",") if g.strip()} if args.games else None
        self.ignore_pats = [re.compile(p) for p in args.ignore.split(",") if p.strip()]

        self.tag_re = re.compile(r"<[a-zA-Z][^<" + GT + r"]{0,600}" + GT, re.S)
        self.attr_re = re.compile(
            r"(?:src|href|poster|data-src|data-script-src|data-html-src)\s*=\s*([" + QUOT + r"])(.*?)\1", re.I)
        self.comment_re = re.compile(r"<!--.*?--" + GT, re.S)
        self.css_url_re = re.compile(
            r"url(\s*([" + QUOT + r"]?)([^)" + QUOT + r"\s]+)\1\s*)", re.I)
        self.css_import_re = re.compile(
            r"@import\s+(?:url(\s*)?([" + QUOT + r"]?)([^;)" + QUOT + r"\s]+)\1\s*;?", re.I)
        self.js_import_re = re.compile(r"import\s*(\s*([" + QUOT + r"])([^" + QUOT + r"]+)\1")
        self.js_rel_re = re.compile(
            r"([" + QUOT + r"])((?:.{1,2}[/\])[^" + QUOT + r"]+?.[a-zA-Z0-9]{2,7})\1")

    # ---------------- resolucion de una referencia ----------------
    def _skip(self, ref):
        if not ref:
            return "empty"
        if re.match(r"^(https?:|//|data:|#|mailto:|javascript:|blob:|about:|tel:|ftp:|file:)", ref.lower()):
            return "remote"
        if re.match(r"^[a-z]:", ref.lower()):
            return "absdrive"
        if ref.startswith("/"):
            return "absolute"
        if re.search(r"[\\+$}{|*`,]|^%", ref):
            return "dynamic"
        return None

    def _resolve_base(self, fref, js_base_kind):
        if js_base_kind == "css":
            return os.path.dirname(fref)
        if js_base_kind == "js-import":
            return os.path.dirname(fref)
        if js_base_kind == "js-str":
            if self.args.js_base == "file":
                return os.path.dirname(fref)
            return self.idx.game_root(fref)
        return os.path.dirname(fref)

    def _find_candidates(self, base_name, game):
        out = [c for c in self.idx.basenames.get(base_name, [])
               if self.idx.game_of(c) == game]
        return out

    def handle(self, fref, ref, base, kind, game, mstart, mend):
        ref = ref.strip()
        skip = self._skip(ref)
        if skip:
            if skip == "absolute":
                self.absolut.append((game, os.path.relpath(fref, self.idx.root), ref))
            elif skip == "dynamic":
                self.dynamic += 1
            return
        if self.ignore_pats and any(p.search(ref) for p in self.ignore_pats):
            self.ignored.append((game, ref))
            return
        clean = ref.split("#")[0].split("?")[0].strip()
        if not clean or clean in (".", ".."):
            return
        t = os.path.normpath(os.path.join(base, clean))
        lt = t.lower()
        if not lt.startswith(self.idx.root.lower()):
            self.external.append((game, os.path.relpath(fref, self.idx.root), ref))
            return
        try:
            if os.path.isdir(t):
                rd = self.idx.dirs.get(lt)
                if rd is not None and rd != t:
                    newref = os.path.relpath(rd, base).replace(os.sep, "/")
                    self._add_fix("caseD", fref, ref, newref, kind, game, mstart, mend, base)
                return
        except OSError:
            pass
        rp = self.idx.files.get(lt)
        if rp is not None:
            if rp != t:
                newref = os.path.relpath(rp, base).replace(os.sep, "/")
                self._add_fix("case", fref, ref, newref, kind, game, mstart, mend, base)
            return
        # no existe: buscar por nombre dentro del mismo juego
        cand = self._find_candidates(os.path.basename(t).lower(), game)
        if len(cand) == 1:
            newref = os.path.relpath(cand[0], base).replace(os.sep, "/")
            self._add_fix("basename", fref, ref, newref, kind, game, mstart, mend, base)
        elif len(cand) > 1:
            self.ambiguous.append({
                "game": game, "file": os.path.relpath(fref, self.idx.root),
                "ref": ref, "cands": [os.path.relpath(c, self.idx.root) for c in cand[:5]],
            })
            if self.args.apply_ambiguous and self.args.apply:
                newref = os.path.relpath(cand[0], base).replace(os.sep, "/")
                self._add_fix("basename", fref, ref, newref, kind, game, mstart, mend, base)
        else:
            self.counts["missing"] += 1
            self.missing[ref] += 1
            self.missing_info.setdefault(ref, (game, os.path.relpath(base, self.idx.root)))

    def _add_fix(self, status, fref, ref, newref, kind, game, mstart, mend, base):
        if ref.startswith("./") and not newref.startswith("../"):
            newref = "./" + newref
        elif ref.startswith("../") and newref.startswith("./"):
            newref = newref[2:]
        self.counts[status] += 1
        self.fixes.append((status, game, os.path.relpath(fref, self.idx.root), ref, newref, kind))
        self.by_file[fref].append((mstart, mend, newref))

    # --------------------------- pases ---------------------------
    def run(self):
        root = self.idx.root
        for p, lf in sorted(self.idx.files.items()):
            lf = lf.lower()
            if lf.endswith((".html", ".htm")):
                self._scan_html(self.idx.files[p])
            elif lf.endswith(".css"):
                self._scan_css(self.idx.files[p])
            elif lf.endswith(".js"):
                self._scan_js(self.idx.files[p])

    def _scan_html(self, path):
        game = self.idx.game_of(path)
        if self.game_filter and game not in self.game_filter:
            return
        raw = read_bytes(path)
        if raw is None:
            return
        txt, _, _ = decode(raw)
        masked = self.comment_re.sub(lambda m: " " * (m.end() - m.start()), txt)
        base = os.path.dirname(path)
        for mt in self.tag_re.finditer(masked):
            tag = mt.group(0)
            for ma in self.attr_re.finditer(tag + GT):
                q, ref = ma.group(1), ma.group(2)
                # desplazamiento real dentro del fichero
                off = mt.start(0) + ma.start(1)
                self.handle(path, ref, base, "html", game, off, off + len(ref))

    def _scan_css(self, path):
        game = self.idx.game_of(path)
        if self.game_filter and game not in self.game_filter:
            return
        raw = read_bytes(path)
        if raw is None:
            return
        txt, _, _ = decode(raw)
        base = os.path.dirname(path)
        for mu in self.css_url_re.finditer(txt):
            q, ref = mu.group(1), mu.group(2)
            self.handle(path, ref, base, "css", game, mu.start(2), mu.end(2))
        for mi in self.css_import_re.finditer(txt):
            q, ref = mi.group(1), mi.group(2)
            self.handle(path, ref, base, "css", game, mi.start(2), mi.end(2))

    def _scan_js(self, path):
        game = self.idx.game_of(path)
        if self.game_filter and game not in self.game_filter:
            return
        raw = read_bytes(path)
        if raw is None:
            return
        txt, _, _ = decode(raw)
        import_spans = []
        for mi in self.js_import_re.finditer(txt):
            ref = mi.group(2)
            base = os.path.dirname(path)
            self.handle(path, ref, base, "js-import", game, mi.start(2), mi.end(2))
            import_spans.append((mi.start(0), mi.end(0)))
        base_str = self.idx.game_root(path)
        seen = set()
        for mj in self.js_rel_re.finditer(txt):
            if any(s <= mj.start(0) < e for s, e in import_spans):
                continue
            ref = mj.group(2)
            low = ref.lower()
            if low in seen:
                continue
            seen.add(low)
            # auto: probamos los dos bases y usamos el primero que exista
            bases = [self._resolve_base(path, "js-str")]
            if self.args.js_base == "auto":
                other = os.path.dirname(path)
                if other not in bases:
                    bases.append(other)
            handled = False
            for b in bases:
                # si existe, ok y paramos
                t = os.path.normpath(os.path.join(b, ref.split("#")[0].split("?")[0].strip()))
                lt = t.lower()
                if lt in self.idx.files or (lt in self.idx.dirs):
                    handled = True
                    break
            if handled:
                self.counts["ok"] += 1
                continue
            self.handle(path, ref, bases[0], "js-str", game, mj.start(2), mj.end(2))

    # --------------------------- aplicacion ---------------------------
    def apply(self):
        changed = 0
        for fref, repls in sorted(self.by_file.items()):
            raw = read_bytes(fref)
            if raw is None:
                continue
            txt, had_bom, enc = decode(raw)
            new_txt = txt
            for start, end, newtext in sorted(repls, reverse=True):
                if 0 <= start <= end <= len(new_txt) and new_txt[start:end] == txt[start:end]:
                    pass
                new_txt = new_txt[:start] + newtext + new_txt[end:]
            if new_txt != txt:
                with open(fref, "wb") as fh:
                    fh.write(encode(new_txt, had_bom))
                changed += 1
        return changed


# ------------------------------------------------------------- informe final ---
def main(argv=None):
    args = parse_args(argv)
    root = os.path.abspath(args.root)
    if not os.path.isdir(root):
        print("La raiz no existe:", root)
        return 2
    idx = Index(root).build()
    sc = Scanner(idx, args)
    sc.run()

    print("Juegos escaneados:", len(idx.games))
    print("COUNTS:", dict(sc.counts))
    print()

    if sc.fixes:
        print("=== CORRECCIONES PROPUESTAS (" + str(len(sc.fixes)) + ") ===")
        for status, game, f, ref, new, kind in sc.fixes:
            mark = " [OK puedo-] " if False else " "
            print("  " + status + " | " + game + " | " + f + " | " + ref + "  =>  " + new + mark)
        print()
    if sc.ambiguous:
        print("=== AMBIGUAS (" + str(len(sc.ambiguous)) + ") ===")
        for a in sc.ambiguous:
            print("  " + a["game"] + " | " + a["file"] + " | " + a["ref"] + " | cands: " + ", ".join(a["cands"]))
        print()
    if sc.absolut:
        print("=== RUTAS ABSOLUTAS (" + str(len(sc.absolut)) + ") ===")
        for game, f, ref in sc.absolut[:25]:
            print("  " + game + " | " + f + " | " + ref)
        print()
    if sc.external:
        print("=== EXTERNAS (fuera del repo) (" + str(len(sc.external)) + ") ===")
        for game, f, ref in sc.external[:20]:
            print("  " + game + " | " + f + " | " + ref)
        print()

    miss_total = sum(sc.missing.values())
    print("=== FALTANTES (sin candidato) total " + str(miss_total) + " / unicas " + str(len(sc.missing)) + " ===")
    maxn = 10 ** 9 if args.full_missing else args.max_missing
    for i, (ref, n) in enumerate(sc.missing.most_common(maxn)):
        game, base = sc.missing_info[ref]
        print("  " + str(n) + "x  " + ref + "   (ej: " + game + ", base " + base + ")")
        if i >= maxn - 1:
            print("  ... (hay mas; usa --full-missing para verlas todas)")
    print()

    if args.json:
        report = {
            "counts": dict(sc.counts),
            "fixes": [dict(status=s[0], game=s[1], file=s[2], ref=s[3], newref=s[4]) for s in sc.fixes],
            "ambiguous": sc.ambiguous,
            "absolute": sc.absolut,
            "external": sc.external,
            "missing": [{"ref": r, "n": n} for r, n in sc.missing.most_common()],
        }
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump(report, fh, ensure_ascii=False, indent=2)
        print("Informe guardado en:", args.json)

    if args.apply:
        n = sc.apply()
        print("Aplicadas correcciones en", n, "ficheros.")
        print("Recomendacion: vuelve a ejecutar el script para verificar que quedan 0 corregibles.")
        print("Revisa con:  git diff --stat   y   git diff")
    else:
        if sc.fixes:
            print("Hay " + str(len(sc.fixes)) + " correcciones seguras pendientes.")
            print("Ejecuta con --apply para aplicarlas (primero revisa el diff de arriba).")
    return 0


if __name__ == "__main__":
    sys.exit(main())

##
