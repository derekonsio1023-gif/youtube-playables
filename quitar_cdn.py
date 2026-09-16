#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""quitar_cdn.py - Quita la dependencia del CDN externo de los juegos del repo.

Todos los juegos de este repo cargan sus recursos a traves de un CDN externo
(jsDelivr -> GitHub), porque cada HTML lleva:

    <base href="https://cdn.jsdelivr.net/gh/bubbls/youtube-playables@<ref>/<juego>/">

Con esa etiqueta <base> TODAS las rutas relativas del juego (imagenes, .js,
.ogg, .json, bundle de Unity, etc.) se piden al CDN y no a los ficheros locales.
Ademas los shims `ytgame.js` / `gamesnacks.js` tambien se cargan del CDN.

Esta herramienta:

  1. Detecta todas las referencias a `cdn.jsdelivr.net/gh/<owner>/<repo>@<ref>/<ruta>`
     (y `raw.githubusercontent.com/<owner>/<repo>/<ref>/<ruta>`) en los ficheros
     de texto del repo (.html, .htm, .js, .json, .css, .mjs, .xml, .map...).
  2. Reescribe cada referencia a su equivalente LOCAL:
       - <base href=".../<juego>/">  ->  <base href="./">
       - <script src=".../ytgame.js">     ->  ytgame.js       (copia local del shim)
       - <script src=".../gamesnacks.js"> ->  gamesnacks.js   (copia local del shim)
       - cualquier otra ruta del repo     ->  ruta relativa local
  3. Verifica estaticamente que todos los recursos relativos de cada HTML/CSS
     existen en local (para saber si el juego funcionara sin el CDN).
  4. Con --descargar, se trae del CDN los recursos que falten y los guarda en su
     sitio, dejando el juego 100% autocontenido.

Uso tipico (informe -> aplicar -> verificar):

    python quitar_cdn.py
    python quitar_cdn.py --apply
    python quitar_cdn.py --apply --descargar
    python quitar_cdn.py                      # debe salir 0 pendientes

Opciones utiles:
    --games a,b,c      solo esos juegos
    --json informe.json
    --shim-relativo    en vez de copiar el shim, enlazar ../ytgame.js
    --no-verificar     no comprobar que los recursos locales existan
    --externas         listar tambien el resto de dependencias externas (info)
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
import urllib.request
from collections import Counter, defaultdict
from urllib.parse import unquote, quote, urlsplit

# --------------------------------------------------------------- constantes ---
BOM = "\ufeff"

# Rutas relativas al repo que son ficheros "shim" (se copian a cada juego).
SHIMS = ("ytgame.js", "gamesnacks.js")

TEXT_EXT = (
    ".html", ".htm", ".js", ".mjs", ".cjs", ".json", ".json5", ".css",
    ".xml", ".map", ".webmanifest", ".manifest", ".txt", ".tsv", ".csv",
    ".svg", ".webc", ".vue", ".svelte",
)

# Extensiones que se consideran recursos que deben existir en local.
ASSET_EXT = (
    ".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp", ".ico", ".svg",
    ".ogg", ".mp3", ".wav", ".m4a", ".mp4", ".webm", ".flac",
    ".js", ".mjs", ".css", ".json", ".html", ".htm", ".txt", ".xml",
    ".bin", ".bundle", ".unityweb", ".wasm", ".data", ".zip", ".glb",
    ".gltf", ".fbx", ".atlas", ".cconb", ".basis", ".woff", ".woff2",
    ".ttf", ".otf", ".eot", ".encrypted", ".cur", ".csv", ".webmanifest",
)

# Ficheros que nunca se tocan (los propios informes/utillidades).
SKIP_NAMES = {"quitar_cdn.py"}

CDN_RE = re.compile(
    r"""(?P<url>(?:https?:)?//cdn\.jsdelivr\.net/gh/""" 
    r"""(?P<owner>[^/@\s"'<>]+)/(?P<repo>[^/@\s"'<>]+)"""
    r"""@(?P<ref>[^/\s"'<>]+)/(?P<path>[^\s"'<>),]*))""",
    re.I,
)
RAW_RE = re.compile(
    r"""(?P<url>(?:https?:)?//raw\.githubusercontent\.com/"""
    r"""(?P<owner>[^/@\s"'<>]+)/(?P<repo>[^/@\s"'<>]+)"""
    r"""/(?P<ref>[^/\s"'<>]+)/(?P<path>[^\s"'<>),]*))""",
    re.I,
)
BASE_HREF_RE = re.compile(r"""(<base\b[^>]*?href\s*=\s*)(["'])([^"']*)(\2)""", re.I)

# Referencias relativas dentro de HTML/CSS (para la verificacion).
ATTR_REF_RE = re.compile(
    r"""\b(?:src|href|data-src|data-href|poster|action|background)\s*=\s*([\"'])([^\"'>]+)\1""",
    re.I,
)
CSS_URL_RE = re.compile(r"""url\(\s*([\"']?)([^\"')]+)\1\s*\)""", re.I)
JS_REF_RE = re.compile(
    r"""[\"']([^\"'\s]+\.(?:""" + "|".join(e.lstrip(".") for e in ASSET_EXT) + r"""))[\"']""",
    re.I,
)


# ------------------------------------------------------------ lectura/escritura
def read_text(path):
    """Devuelve (texto, tenia_bom)."""
    with open(path, "rb") as fh:
        raw = fh.read()
    had_bom = raw.startswith(b"\xef\xbb\xbf")
    if had_bom:
        raw = raw[3:]
    try:
        return raw.decode("utf-8"), had_bom
    except UnicodeDecodeError:
        return raw.decode("utf-8", "replace"), had_bom


def write_text(path, text, had_bom):
    data = (BOM + text) if had_bom else text
    with open(path, "wb") as fh:
        fh.write(data.encode("utf-8"))


# ------------------------------------------------------------------ indexado ---
def norm_slug(name):
    """Normaliza un slug de URL para poder compararlo con los nombres locales."""
    n = unquote(name).lower()
    n = re.sub(r"[-_.+]+", " ", n)
    n = re.sub(r"\s+", " ", n).strip()
    return n


def compact(name):
    return re.sub(r"[^a-z0-9]", "", norm_slug(name))


class Index:
    """Indice del repo: juegos (primer nivel) y ficheros."""

    def __init__(self, root):
        self.root = root
        self.games = {}       # nombre real del dir -> ruta absoluta
        self.aliases = {}     # nombre normalizado -> nombre real
        self.files = {}       # ruta relativa en minusculas -> ruta relativa real
        self.slug_dirs = {}   # slug normalizado del CDN -> dir local del juego
        self.build()

    def build(self):
        try:
            entries = sorted(os.listdir(self.root))
        except OSError:
            entries = []
        for name in entries:
            p = os.path.join(self.root, name)
            if not os.path.isdir(p) or name.startswith((".", "_")):
                continue
            self.games[name] = p
            self.aliases.setdefault(norm_slug(name), name)
        for dirpath, dirnames, filenames in os.walk(self.root, onerror=lambda e: None):
            dirnames[:] = [d for d in dirnames
                           if d != ".git" and len(os.path.join(dirpath, d)) < 240]
            for fn in filenames:
                rel = os.path.relpath(os.path.join(dirpath, fn), self.root).replace(os.sep, "/")
                self.files.setdefault(rel.lower(), rel)
        self._index_slug_dirs()
        return self

    def _index_slug_dirs(self):
        """Deduce slug del CDN -> carpeta local leyendo los <base href> de cada HTML.

        Asi funciona aunque la carpeta local se llame distinto al slug del CDN
        (p.ej. 'slice%20it%20all' -> 'slice-it-all') y aunque el juego no este
        en el primer nivel del arbol.
        """
        for rel in list(self.files.values()):
            if not rel.lower().endswith((".html", ".htm")):
                continue
            p = os.path.join(self.root, rel.replace("/", os.sep))
            try:
                if os.path.getsize(p) > 8_000_000:
                    continue
                with open(p, "rb") as fh:
                    data = fh.read()
            except OSError:
                continue
            if b"<base" not in data.lower():
                continue
            text = data.decode("utf-8", "ignore")
            for m in BASE_HREF_RE.finditer(text):
                val = m.group(3)
                m2 = CDN_RE.search(val) or RAW_RE.search(val)
                if not m2:
                    continue
                ref, path = m2.group("ref"), m2.group("path")
                if ref.lower() == "refs":
                    bits = path.split("/", 2)
                    if len(bits) == 3 and bits[0] in ("heads", "tags"):
                        path = bits[2]
                slug = path.strip("/")
                if not slug or "/" in slug:
                    continue
                d = os.path.dirname(rel)
                self.slug_dirs.setdefault(norm_slug(slug), d if d else ".")
        return self

    # -- resolucion de slugs -------------------------------------------------
    def game_dir(self, slug):
        """Devuelve la carpeta local del juego para un slug de URL (o None).

        Primero usa el mapa deducido de los <base href> (evidencia real) y
        despues la similitud de nombres con los directorios de primer nivel.
        """
        n = norm_slug(slug)
        if n in self.slug_dirs:
            return self.slug_dirs[n]
        key = compact(slug)
        if key:
            for k, d in self.slug_dirs.items():
                if compact(k) == key:
                    return d
        real = self.aliases.get(n)
        if real:
            return real
        if not key:
            return None
        for normname, realname in self.aliases.items():
            if compact(normname) == key:
                return realname
        return None

    @staticmethod
    def _join(prefix, rest):
        if prefix in (None, "", "."):
            return rest
        return prefix + "/" + rest

    def is_shim(self, path):
        pure = path.partition("?")[0].strip("/")
        return "/" not in pure and pure.lower() in {s.lower() for s in SHIMS}

    def exists(self, rel):
        """Existe la ruta relativa al repo (insensible a mayusculas)?"""
        if not rel:
            return False
        rel_fs = unquote(rel).replace("/", os.sep)
        if os.path.exists(os.path.join(self.root, rel_fs)):
            return True
        return rel_fs.lower() in self.files

    def resolve(self, path):
        """Ruta URL del CDN -> ruta local relativa al repo, o None.

        Acepta rutas codificadas (%20) y con ?query.
        """
        pure = path.partition("?")[0].strip("/")
        if not pure:
            return None
        if self.is_shim(pure):
            return pure if self.exists(pure) else None
        parts = pure.split("/")
        real_game = self.game_dir(parts[0])
        if real_game is not None:
            if len(parts) == 1:
                return real_game      # la referencia apunta a la carpeta del juego
            cand = self._join(real_game, "/".join(parts[1:]))
            if self.exists(cand):
                return cand
        if self.exists(pure):
            return pure
        return None

    def local_path_for_download(self, path):
        """Ruta local donde guardar un recurso que falta (aunque aun no exista)."""
        pure = path.partition("?")[0].strip("/")
        if not pure:
            return None
        if self.is_shim(pure):
            return pure
        parts = pure.split("/")
        real_game = self.game_dir(parts[0])
        if real_game and len(parts) > 1:
            return real_game + "/" + "/".join(parts[1:])
        return pure

    def rel_url(self, local_rel, base_dir_abs):
        """Ruta relativa (con / y con %XX) desde base_dir_abs hasta local_rel."""
        target = os.path.join(self.root, unquote(local_rel).replace("/", os.sep))
        rel = os.path.relpath(target, base_dir_abs).replace(os.sep, "/")
        rel = quote(rel)
        if not rel.startswith("."):
            rel = "./" + rel
        return rel


# ------------------------------------------------------------------ scanner ---
class Scanner:
    def __init__(self, idx, args):
        self.idx = idx
        self.args = args
        self.root = idx.root
        self.edits = []            # dicts por edicion
        self.copies = []           # (origen_rel, destino_rel)
        self.downloads = []        # (destino_rel, url)
        self.unresolved = []       # (rel, url, path)
        self.externas = defaultdict(Counter)
        self.docs = []             # html/css para verificar
        self.writes = []           # (ruta_abs, texto_nuevo, tenia_bom)
        self.counts = Counter()
        self.missing_attr = defaultdict(list)   # game -> [(rel, ref)]
        self.missing_js = defaultdict(list)

    # -- utilidades ----------------------------------------------------------
    def _solo_juego(self, rel):
        if not self.args.games:
            return True
        return rel.split("/")[0] in self.args.juegos

    def _ref_dir_abs(self, rel):
        return os.path.dirname(os.path.join(self.root, rel.replace("/", os.sep)))

    def _kind(self, path, game):
        pure = path.partition("?")[0].strip("/")
        if self.idx.is_shim(pure):
            return "shim"
        if game and (compact(pure) == compact(game)):
            return "base"
        return "recurso"

    @staticmethod
    def _split_ref_path(ref, path):
        """Normaliza el ref/path de URLs raw.githubusercontent.com/.../refs/heads/x/..."""
        if ref.lower() == "refs":
            bits = path.split("/", 2)
            if len(bits) == 3 and bits[0] in ("heads", "tags"):
                return "refs/" + bits[0] + "/" + bits[1], bits[2]
        return ref, path

    # -- analisis de un fichero ---------------------------------------------
    def _compute(self, rel, text):
        """Devuelve (nuevo_texto, hubo_cambios)."""
        game = rel.split("/")[0] if "/" in rel else None
        ref_dir_abs = self._ref_dir_abs(rel)

        def repl(m):
            url = m.group("url")
            _ref, path = self._split_ref_path(m.group("ref"), m.group("path"))
            kind = self._kind(path, game)
            local = self.idx.resolve(path)
            if local is None:
                dest = self.idx.local_path_for_download(path)
                self.unresolved.append((rel, url, path))
                self.counts["sin_resolver"] += 1
                if self.args.descargar and dest and "." in os.path.basename(dest):
                    self.downloads.append((dest, url))
                return url
            if kind == "shim" and self.args.copiar_shims and game:
                dest_rel = game + "/" + os.path.basename(local)
                self.copies.append((local, dest_rel))
                new = self.idx.rel_url(dest_rel, ref_dir_abs)
            else:
                new = self.idx.rel_url(local, ref_dir_abs)
            self.edits.append(dict(file=rel, game=game or "(raiz)", old=url, new=new,
                                   kind=kind, target=local))
            self.counts[kind] += 1
            return new

        new_text = CDN_RE.sub(repl, text)
        new_text = RAW_RE.sub(repl, new_text)
        return new_text, new_text != text

    def scan(self):
        for dirpath, dirnames, filenames in os.walk(self.root, onerror=lambda e: None):
            dirnames[:] = [d for d in dirnames
                           if d != ".git" and len(os.path.join(dirpath, d)) < 240]
            for fn in sorted(filenames):
                if fn in SKIP_NAMES or fn.startswith("_scan") or fn.startswith("_git"):
                    continue
                rel0 = os.path.join(dirpath, fn)
                if os.path.dirname(rel0) == self.root and fn.startswith("_"):
                    continue  # informes/ficheros temporales en la raiz
                ext = os.path.splitext(fn)[1].lower()
                if ext not in TEXT_EXT:
                    continue
                p = os.path.join(dirpath, fn)
                rel = os.path.relpath(p, self.root).replace(os.sep, "/")
                if not self._solo_juego(rel):
                    continue
                try:
                    if os.path.getsize(p) > 8_000_000:
                        continue
                    text, had_bom = read_text(p)
                except OSError:
                    continue
                low = text.lower()
                if self.args.externas:
                    self._scan_externas(rel, text)
                base = None
                if "jsdelivr" in low or "raw.githubusercontent" in low:
                    new_text, changed = self._compute(rel, text)
                    if changed:
                        self.counts["ficheros_modificados"] += 1
                        base = self._base_url(text)
                        self.writes.append((p, new_text, had_bom))
                        if ext in (".html", ".htm", ".css"):
                            self.docs.append(dict(rel=rel, text=new_text, had_bom=had_bom,
                                                  base=base, game=rel.split("/")[0], file=p))
                    continue
                if ext in (".html", ".htm"):
                    self.docs.append(dict(rel=rel, text=text, had_bom=had_bom,
                                          base=base, game=rel.split("/")[0], file=p))

    @staticmethod
    def _base_url(text):
        m = BASE_HREF_RE.search(text)
        if m and ("jsdelivr" in m.group(3).lower() or "githubusercontent" in m.group(3).lower()):
            return m.group(3)
        return None

    def _scan_externas(self, rel, text):
        game = rel.split("/")[0]
        for _, ref in ATTR_REF_RE.findall(text):
            if ref.lower().startswith(("http://", "https://", "//")):
                try:
                    host = urlsplit(ref).netloc.lower()
                except ValueError:
                    continue
                if host and "jsdelivr" not in host:
                    self.externas[game][host] += 1

    # -- verificacion estatica de recursos locales ---------------------------
    @staticmethod
    def _es_absoluto(ref):
        r = ref.strip()
        if r.startswith(("//", "/", "#")):
            return True
        return bool(re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", r))

    @staticmethod
    def _limpia(ref):
        return unquote(ref.partition("?")[0].partition("#")[0].strip())

    def verify(self):
        """Comprueba que los recursos relativos de cada HTML/CSS existen en local."""
        for doc in self.docs:
            dir_abs = self._ref_dir_abs(doc["rel"])
            atributos = [r for _, r in ATTR_REF_RE.findall(doc["text"])]
            if doc["rel"].lower().endswith(".css"):
                atributos += [r for _, r in CSS_URL_RE.findall(doc["text"])]
            vistos = set()
            for ref in atributos:
                self._comprueba(doc, dir_abs, ref, vistos, tipo="attr")
            for m in JS_REF_RE.finditer(doc["text"]):
                ref = m.group(1)
                if ref in vistos or "/" not in ref:
                    continue
                if not ref.startswith(("assets", "html5games", "Build", "StreamingAssets",
                                       "TemplateData", "vendor", "fastLib", "./", "../")):
                    continue
                self._comprueba(doc, dir_abs, ref, vistos, tipo="js")

    def _comprueba(self, doc, dir_abs, ref, vistos, tipo):
        ref = ref.strip()
        if not ref or ref in vistos:
            return
        vistos.add(ref)
        if self._es_absoluto(ref):
            return
        limpia = self._limpia(ref)
        if not limpia:
            return
        if os.path.basename(limpia).lower() in {s.lower() for s in SHIMS}:
            return  # los shims se copian en la fase de aplicacion
        destino = os.path.normpath(os.path.join(dir_abs, limpia.replace("/", os.sep)))
        if os.path.exists(destino):
            return
        entrada = (doc["rel"], ref)
        if tipo == "attr":
            self.missing_attr[doc["game"]].append(entrada)
        else:
            self.missing_js[doc["game"]].append(entrada)
        if doc["base"] and self.args.descargar:
            local_rel = os.path.relpath(destino, self.root).replace(os.sep, "/")
            if not local_rel.startswith(".."):
                self.downloads.append((local_rel, doc["base"] + quote(ref)))

    # -- aplicacion ----------------------------------------------------------
    def _descargar(self, dest_rel, url):
        dest = os.path.join(self.root, unquote(dest_rel).replace("/", os.sep))
        if os.path.exists(dest):
            return "ya existe"
        req = urllib.request.Request(url, headers={"User-Agent": "quitar_cdn/1.0"})
        try:
            with urllib.request.urlopen(req, timeout=45) as resp:
                data = resp.read()
        except Exception as exc:  # noqa: BLE001
            return "error: " + str(exc)
        if not data:
            return "error: respuesta vacia"
        os.makedirs(os.path.dirname(dest) or self.root, exist_ok=True)
        with open(dest, "wb") as fh:
            fh.write(data)
        return "ok"

    def apply(self):
        copiados = 0
        for src_rel, dest_rel in self.copies:
            src = os.path.join(self.root, src_rel.replace("/", os.sep))
            dest = os.path.join(self.root, dest_rel.replace("/", os.sep))
            if not os.path.isfile(src):
                continue
            if os.path.isfile(dest):
                if (os.path.getsize(src) == os.path.getsize(dest)
                        and open(src, "rb").read() == open(dest, "rb").read()):
                    continue
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            shutil.copyfile(src, dest)
            copiados += 1

        escritos = 0
        for path, text, had_bom in self.writes:
            write_text(path, text, had_bom)
            escritos += 1

        descargas = Counter()
        for dest_rel, url in self.downloads:
            descargas[self._descargar(dest_rel, url)] += 1
        return copiados, escritos, descargas

# ------------------------------------------------------------------ informe ---
def parse_args(argv):
    ap = argparse.ArgumentParser(
        description="Quita la dependencia del CDN externo (jsDelivr/GitHub) de los juegos.")
    ap.add_argument("--root", default=os.path.dirname(os.path.abspath(__file__)),
                    help="Raiz del repo (por defecto, la carpeta del script)")
    ap.add_argument("--apply", action="store_true", help="Aplica los cambios (si no, solo informa)")
    ap.add_argument("--descargar", action="store_true",
                    help="Con --apply, descarga del CDN los recursos que falten")
    ap.add_argument("--games", default="", help="Solo estos juegos, separados por comas")
    ap.add_argument("--json", default="", help="Guarda el informe JSON en esa ruta")
    ap.add_argument("--externas", action="store_true",
                    help="Informa tambien del resto de hosts externos por juego")
    ap.add_argument("--no-verificar", action="store_true",
                    help="No comprobar que los recursos locales existan")
    ap.add_argument("--shim-relativo", action="store_true",
                    help="Enlazar ../ytgame.js en vez de copiar el shim en cada juego")
    ap.add_argument("--max-lineas", type=int, default=40,
                    help="Maximo de lineas por seccion del informe")
    args = ap.parse_args(argv)
    args.juegos = {g.strip() for g in args.games.split(",") if g.strip()}
    args.copiar_shims = not args.shim_relativo
    return args


def avisos(idx):
    """Avisos utiles: juegos sin index.html, juegos sin HTML."""
    sin_index, sin_html = [], []
    for game in sorted(idx.games):
        htmls = [f for f in idx.files.values()
                 if f.startswith(game + "/") and f.lower().endswith((".html", ".htm"))]
        if not htmls:
            sin_html.append(game)
        elif not any(os.path.basename(h).lower() == "index.html" for h in htmls):
            sin_index.append((game, sorted(os.path.basename(h) for h in htmls)))
    return sin_index, sin_html


def informe_base(idx, sc, args):
    add = []
    add.append("=" * 78)
    add.append("INFORME: dependencia del CDN externo (jsDelivr/GitHub) de los juegos")
    add.append("Raiz: " + idx.root)
    add.append("Juegos (primer nivel): " + str(len(idx.games)))
    add.append("=" * 78)
    add.append("Ediciones por tipo: " + json.dumps(dict(sc.counts), ensure_ascii=False))
    add.append("Ficheros a reescribir: " + str(len(sc.writes)))
    add.append("Shims a copiar: " + str(len(set(sc.copies))))
    add.append("Referencias sin resolver en local: " + str(len(sc.unresolved)))
    add.append("")

    por_juego = defaultdict(Counter)
    for e in sc.edits:
        por_juego[e["game"]][e["kind"]] += 1
    add.append("--- EDICIONES POR JUEGO (base / shim / recurso) ---")
    for game in sorted(por_juego):
        c = por_juego[game]
        add.append("  %-28s base=%-3d shim=%-3d recurso=%-4d"
                   % (game, c["base"], c["shim"], c["recurso"]))
    add.append("")

    if sc.unresolved:
        add.append("--- REFERENCIAS AL CDN SIN EQUIVALENTE LOCAL (%d) ---" % len(sc.unresolved))
        for rel, url, path in sc.unresolved[:args.max_lineas]:
            add.append("  %s -> %s" % (rel, url))
        add.append("")
    return add
def informe_extra(add, idx, sc, args):
    if sc.missing_attr:
        total = sum(len(v) for v in sc.missing_attr.values())
        add.append("--- RECURSOS RELATIVOS QUE NO EXISTEN EN LOCAL: atributos (%d) ---" % total)
        for game in sorted(sc.missing_attr):
            lst = sc.missing_attr[game]
            add.append("  %s: %d" % (game, len(lst)))
            for rel, ref in lst[:6]:
                add.append("      %s -> %s" % (rel, ref))
        add.append("")

    if sc.missing_js:
        total = sum(len(v) for v in sc.missing_js.values())
        add.append("--- POSIBLES RECURSOS FALTANTES: cadenas JS (%d) ---" % total)
        for game in sorted(sc.missing_js):
            lst = sc.missing_js[game]
            add.append("  %s: %d" % (game, len(lst)))
            for rel, ref in lst[:6]:
                add.append("      %s -> %s" % (rel, ref))
        add.append("")

    if args.externas and sc.externas:
        add.append("--- OTROS HOSTS EXTERNOS REFERENCIADOS (info, no se tocan) ---")
        for game in sorted(sc.externas):
            hosts = ", ".join("%s x%d" % (h, n) for h, n in sc.externas[game].most_common(6))
            if hosts:
                add.append("  %-28s %s" % (game, hosts))
        add.append("")

    sin_index, sin_html = avisos(idx)
    if sin_index or sin_html:
        add.append("--- AVISOS ---")
        for game, htmls in sin_index:
            add.append("  %s: no tiene index.html (ficheros: %s)" % (game, ", ".join(htmls)))
        for game in sin_html:
            add.append("  %s: no tiene ningun HTML" % game)
        add.append("")
def main(argv=None):
    args = parse_args(argv)
    root = os.path.abspath(args.root)
    if not os.path.isdir(root):
        print("La raiz no existe:", root)
        return 2

    idx = Index(root)
    sc = Scanner(idx, args)
    print("Analizando " + str(len(idx.games)) + " juegos...")
    sc.scan()
    if not args.no_verificar:
        sc.verify()

    add = informe_base(idx, sc, args)
    informe_extra(add, idx, sc, args)
    print("\n".join(add))

    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump({
                "counts": dict(sc.counts),
                "edits": sc.edits,
                "unresolved": [dict(file=r, url=u, path=p) for r, u, p in sc.unresolved],
                "copies": [dict(src=s, dest=d) for s, d in sorted(set(sc.copies))],
                "downloads": [dict(dest=d, url=u) for d, u in sc.downloads],
                "missing_attr": {g: v for g, v in sc.missing_attr.items()},
                "missing_js": {g: v for g, v in sc.missing_js.items()},
            }, fh, ensure_ascii=False, indent=2)
        print("Informe guardado en:", args.json)

    if args.apply:
        copiados, escritos, descargas = sc.apply()
        print()
        print("APLICADO: %d shim(s) copiado(s), %d fichero(s) reescrito(s)."
              % (copiados, escritos))
        if descargas:
            print("Descargas: " + ", ".join("%s=%d" % (k, v) for k, v in descargas.items()))
        print("Revisa con: git diff --stat    y     git diff")
        print("Los shims copiados son ficheros NUEVOS: recuerda 'git add' antes de hacer commit.")
        print("Vuelve a ejecutar sin --apply: debe quedar 0 referencias sin resolver.")
    else:
        if sc.writes or sc.copies:
            print()
            print("Hay cambios pendientes. Ejecuta con --apply para aplicarlos.")
    return 0


if __name__ == "__main__":
    sys.exit(main())