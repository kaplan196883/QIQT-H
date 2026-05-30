"""Fix '**bold**' markup that breaks markdown TABLE rows.

scripts/build_pdf.py converts tables BEFORE emphasis: it first splits a
'|'-row into cells joined by ' & ', then runs '**x**' -> \\textbf{x} on the
whole line with the regex  \\*\\*([^*\\n]+?)\\*\\*  (which FORBIDS a single
'*' between the '**' pair). So a cell whose bold contains an italic
(e.g. '**No second *dynamical* ontology ... incomplete') leaves a dangling
'**' that the regex cannot consume; the next dangling '**' (a later cell)
then pairs ACROSS the ' & ' separator, yielding '\\textbf{ & }' fragments
and a runaway tabularx group -> pdflatex "Forbidden control sequence
\\check@nocorr@ / Missing $ inserted".

Precise fix: on table rows only, for each cell, simulate the converter's
own '**...**' regex; if any '**' remains unconsumed in that cell, strip the
leftover '**' from it (dropping only the broken bold, preserving single-'*'
italics and well-formed in-cell bold). After this no dangling '**' can
cross a cell boundary. Idempotent and surgical.
Usage: python scripts/fix_table_bold_span.py [file.md ...]"""
from __future__ import annotations
import re, sys
from pathlib import Path
REPO = Path(__file__).resolve().parent.parent
DEFAULT = [REPO/"QIQT_Math.md", REPO/"QIQT_Foundations_Paper.md",
           REPO/"QIQT_Position_Paper.md", REPO/"TUTORIAL.md"]
# Same pattern build_pdf.py uses for bold.
BOLD = re.compile(r"\*\*([^*\n]+?)\*\*")


def fix_cell(cell: str) -> tuple[str, int]:
    # Remove the bold spans the converter WOULD consume, then see what '**'
    # is left over (these are the ones that break across cells).
    consumed = BOLD.sub("", cell)
    if "**" not in consumed:
        return cell, 0           # all '**' pair cleanly within the cell
    n = cell.count("**")
    return cell.replace("**", ""), n


def fix_line(line: str) -> tuple[str, int]:
    if not line.lstrip().startswith("|"):
        return line, 0
    cells = line.split("|")
    total = 0
    for i, c in enumerate(cells):
        nc, k = fix_cell(c)
        cells[i] = nc
        total += k
    return "|".join(cells), total


def main() -> int:
    targets = [Path(a) for a in sys.argv[1:]] or DEFAULT
    grand = 0
    for f in targets:
        if not f.exists():
            print(f"skip(missing): {f}"); continue
        lines = f.read_text(encoding="utf-8").split("\n")
        out, changed = [], 0
        for ln in lines:
            nl, k = fix_line(ln); out.append(nl); changed += k
        if changed:
            f.write_text("\n".join(out), encoding="utf-8")
        print(f"{f.name}: stripped {changed} dangling '**' marker(s)")
        grand += changed
    print(f"TOTAL: {grand}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
