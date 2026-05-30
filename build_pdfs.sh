#!/usr/bin/env bash
#
# build_pdfs.sh — regenerate the QIQT-H publication PDFs from the
# markdown sources.
#
# Outputs go to build/ (gitignored). Run from the repo root:
#     bash build_pdfs.sh
#
# Requires pandoc + a LaTeX engine (xelatex preferred for Unicode:
# the docs use ψ, Φ, λ, ℓ_P, ≥, ⊗, etc.). Install on Windows e.g.
#     winget install JohnMacFarlane.Pandoc ; winget install MiKTeX.MiKTeX
# or on Debian/Ubuntu
#     sudo apt-get install pandoc texlive-xetex texlive-latex-extra
#
# The four published documents:
DOCS=(
  "QIQT_Foundations_Paper"
  "QIQT_Position_Paper"
  "QIQT_Math"
  "TUTORIAL"
)

set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build

# Pick a LaTeX engine: xelatex (best Unicode), else lualatex, else pdflatex.
ENGINE=""
for e in xelatex lualatex pdflatex; do
  if command -v "$e" >/dev/null 2>&1; then ENGINE="$e"; break; fi
done
if ! command -v pandoc >/dev/null 2>&1; then
  echo "ERROR: pandoc not found on PATH." >&2; exit 1
fi
if [ -z "$ENGINE" ]; then
  echo "ERROR: no LaTeX engine (xelatex/lualatex/pdflatex) found on PATH." >&2; exit 1
fi
echo "[build_pdfs] pandoc + $ENGINE"

# Unicode fonts only help (and are only accepted) under xelatex/lualatex.
# Override with FONT=... if "DejaVu Serif" is not installed; leave empty to
# use the engine default.
FONT="${FONT-DejaVu Serif}"
FONT_OPTS=()
if [ "$ENGINE" != "pdflatex" ] && [ -n "$FONT" ]; then
  FONT_OPTS=(-V "mainfont=$FONT")
fi

for d in "${DOCS[@]}"; do
  if [ ! -f "$d.md" ]; then echo "[build_pdfs] skip (missing): $d.md"; continue; fi
  echo "[build_pdfs] $d.md -> build/$d.pdf"
  pandoc "$d.md" \
    --from=markdown+tex_math_dollars+yaml_metadata_block \
    --pdf-engine="$ENGINE" \
    --toc --number-sections \
    -V geometry:margin=1in \
    "${FONT_OPTS[@]}" \
    -o "build/$d.pdf" \
    || echo "[build_pdfs] WARNING: $d failed (often a missing-font or unsupported-glyph issue under $ENGINE; try FONT= or install texlive-xetex)."
done

echo "[build_pdfs] done. PDFs in build/ (gitignored)."
echo "[build_pdfs] note: build/ is gitignored; PDFs are not part of 'git push'."
echo "[build_pdfs] upload destinations: PhilSci-Archive (records 29766, 29767)"
echo "[build_pdfs]                       Zenodo (10.5281/zenodo.20422040, 20422107)."
