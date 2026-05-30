"""Escape '|' pipes inside inline $...$ math on markdown TABLE rows.

scripts/build_pdf.py splits table rows on raw '|', shredding any inline
'$...$' that uses '|' (bra-kets, |x|, conditionals) and leaving unbalanced
'$' -> pdflatex "Missing $ inserted". Replace in-math pipes on table rows
with '\vert ' (identical rendering). Idempotent and surgical.
Usage: python scripts/fix_table_pipe_math.py [file.md ...]"""
from __future__ import annotations
import re, sys
from pathlib import Path
REPO = Path(__file__).resolve().parent.parent
DEFAULT = [REPO/"QIQT_Math.md", REPO/"QIQT_Foundations_Paper.md",
           REPO/"QIQT_Position_Paper.md", REPO/"TUTORIAL.md"]
INLINE = re.compile(r"\$[^$\n]*\$")
def fix_line(line):
    if not line.lstrip().startswith("|"):
        return line, 0
    n = 0
    def repl(m):
        nonlocal n
        s = m.group(0)
        if "|" not in s: return s
        n += s.count("|")
        return s.replace("|", r"\vert ")
    return INLINE.sub(repl, line), n
def main():
    targets = [Path(a) for a in sys.argv[1:]] or DEFAULT
    total = 0
    for f in targets:
        if not f.exists():
            print(f"skip(missing): {f}"); continue
        lines = f.read_text(encoding="utf-8").split("\n")
        out, changed = [], 0
        for ln in lines:
            nl, k = fix_line(ln); out.append(nl); changed += k
        if changed:
            f.write_text("\n".join(out), encoding="utf-8")
        print(f"{f.name}: {changed} pipe(s) fixed"); total += changed
    print(f"TOTAL: {total}")
    return 0
if __name__ == "__main__":
    sys.exit(main())
