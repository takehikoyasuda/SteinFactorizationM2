#!/bin/sh
# Turn an installPackage html directory into a self-contained site.
#
# Macaulay2 writes those pages for a local installation: the stylesheet, the
# KaTeX scripts that render the mathematics, and every link to a core Macaulay2
# node are absolute paths into the M2 prefix.  Served from anywhere else they
# 404, leaving the pages unstyled with the mathematics as raw TeX.  This copies
# the style assets in beside the pages, repoints those paths at the copy, and
# sends the core-documentation links to macaulay2.com, which serves the same
# file names.
#
# Usage: make-site.sh <html-dir> <out-dir> <package> <repo-url>
set -eu
HTML="$1"; OUT="$2"; PKG="$3"; REPO="$4"

PREFIX=$(M2 --no-readline -q -e 'print prefixDirectory; exit 0' < /dev/null | tail -1)
STYLE="${PREFIX}share/Macaulay2/Style"
[ -d "$STYLE" ] || { echo "no Style directory at $STYLE" >&2; exit 1; }

rm -rf "$OUT"; mkdir -p "$OUT"
cp -R "$HTML"/. "$OUT"/
mkdir -p "$OUT/Style"
cp -R "$STYLE"/. "$OUT/Style"/

CORE="https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/"
BANNER="<div style=\"margin:0 0 1.5em;padding:.75em 1em;border:1px solid #c9c9c9;background:#fbf7e8;font-family:sans-serif;font-size:90%;line-height:1.5\">This is the manual of <b>${PKG}</b>, a third-party research package. It is <b>not part of the Macaulay2 distribution</b> and has not been reviewed by it; the pages merely use Macaulay2's own documentation format. Source and installation instructions: <a href=\"${REPO}\">${REPO}</a>.</div>"

for f in "$OUT"/*.html; do
  python3 - "$f" "$PREFIX" "$CORE" "$BANNER" <<'PY'
import sys, re, io
path, prefix, core, banner = sys.argv[1:5]
s = io.open(path, encoding="utf-8").read()
s = s.replace(prefix + "share/doc/Macaulay2/", core)
s = s.replace(prefix + "share/Macaulay2/Style/", "Style/")
s = re.sub(r"(<body[^>]*>)", lambda m: m.group(1) + banner, s, count=1)
io.open(path, "w", encoding="utf-8").write(s)
PY
done

echo "site: $OUT"
echo "remaining absolute prefix references: $(grep -o "$PREFIX" "$OUT"/*.html | wc -l | tr -d ' ')"
