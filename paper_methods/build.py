"""
Markdown -> arXiv LaTeX builder for the cs.AI methods paper.

Single source of truth:  paper_cs_ai/MANUSCRIPT.md  (+ YAML frontmatter)
Generated deliverable:    paper_arxiv_cs_ai/main.tex  ->  main.pdf

This is a dedicated converter (not the generic scripts/build_pdf.py): it emits a
self-contained arXiv article with a TikZ figure, booktabs tables with captions,
numbered \\cite / thebibliography, and the framed "what we claim" box. The markdown
is authored to a small set of conventions, documented in the project README and in
the cs.AI paper itself (the paper is, fittingly, produced by the pipeline it describes):

  * `## `  -> \\section,  `### ` -> \\subsection,  `#### ` -> \\subsubsection.
    A leading manual number ("3", "3.5", "4.2") is stripped; LaTeX renumbers.
    Keep the manual numbers sequential so literal cross-refs ("§3.5") stay correct.
    A heading titled exactly "Acknowledgements" becomes \\section* (unnumbered).
  * Citations: `[40]`, `[32, 33, 34]` -> \\cite{r40}, \\cite{r32,r33,r34}.
    The `## References` section's `[n] ...` lines become \\bibitem{rn} ... .
  * Raw LaTeX: a fenced block ```{=latex} ... ``` is emitted verbatim (the figure).
  * Tables: a paragraph `**Table N. caption**` immediately above a pipe table is
    rendered as a floating, captioned booktabs/tabularx table.
  * Blockquote (`>`): rendered as a framed minipage (the claim box).
  * `$$...$$` -> display math; `$...$` and ```lean fences pass through; `---` dividers
    are dropped; `§` -> \\S.

Usage:
    python paper_cs_ai/build.py            # convert + compile (latexmk/pdflatex)
    python paper_cs_ai/build.py --no-pdf   # convert only
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "paper_methods" / "MANUSCRIPT.md"
OUT_DIR = REPO / "paper_methods_out"
OUT_TEX = OUT_DIR / "main.tex"

# ---------------------------------------------------------------------------
# Preamble.  Mirrors the hand-authored main.tex preamble (11pt, A4, microtype,
# booktabs, TikZ, hyperref) and adds tabularx + a broad newunicodechar map so
# raw unicode in the markdown (≤, ⟹, ∇, →, ⟨⟩, greek, §) renders.
# Markers __TITLE__/__AUTHOR__/__DATE__/__ABSTRACT__/__KEYWORDS__ are substituted.
# ---------------------------------------------------------------------------
PREAMBLE = r"""\documentclass[11pt]{article}

% --- Encoding and fonts ---
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{lmodern}

% --- Layout ---
\usepackage[a4paper,margin=1in]{geometry}
\usepackage{microtype}
\setlength{\parskip}{0.4em}
\setlength{\parindent}{0pt}

% --- Math, tables, graphics ---
\usepackage{amsmath,amssymb}
\usepackage{booktabs}
\usepackage{array}
\usepackage{tabularx}
\newcolumntype{Y}{>{\raggedright\arraybackslash}X}
\usepackage{alltt}
\usepackage{tikz}
\usetikzlibrary{arrows.meta,positioning}

% --- Links ---
\usepackage[hidelinks]{hyperref}

% --- Raw-unicode coverage (markdown source uses literal unicode in prose/tables) ---
\usepackage{newunicodechar}
\newunicodechar{−}{$-$}\newunicodechar{×}{$\times$}\newunicodechar{÷}{$\div$}
\newunicodechar{±}{$\pm$}\newunicodechar{≈}{$\approx$}\newunicodechar{≠}{$\neq$}
\newunicodechar{≤}{$\leq$}\newunicodechar{≥}{$\geq$}\newunicodechar{∈}{$\in$}
\newunicodechar{∞}{$\infty$}\newunicodechar{→}{$\to$}\newunicodechar{↦}{$\mapsto$}
\newunicodechar{⊗}{$\otimes$}\newunicodechar{⊕}{$\oplus$}\newunicodechar{∂}{$\partial$}
\newunicodechar{∇}{$\nabla$}\newunicodechar{∑}{$\sum$}\newunicodechar{∫}{$\int$}
\newunicodechar{√}{$\sqrt{}$}\newunicodechar{α}{$\alpha$}\newunicodechar{β}{$\beta$}
\newunicodechar{γ}{$\gamma$}\newunicodechar{δ}{$\delta$}\newunicodechar{ε}{$\varepsilon$}
\newunicodechar{η}{$\eta$}\newunicodechar{θ}{$\theta$}\newunicodechar{λ}{$\lambda$}
\newunicodechar{μ}{$\mu$}\newunicodechar{ν}{$\nu$}\newunicodechar{ξ}{$\xi$}
\newunicodechar{π}{$\pi$}\newunicodechar{ρ}{$\rho$}\newunicodechar{σ}{$\sigma$}
\newunicodechar{τ}{$\tau$}\newunicodechar{φ}{$\varphi$}\newunicodechar{χ}{$\chi$}
\newunicodechar{ψ}{$\psi$}\newunicodechar{ω}{$\omega$}\newunicodechar{Γ}{$\Gamma$}
\newunicodechar{Δ}{$\Delta$}\newunicodechar{Λ}{$\Lambda$}\newunicodechar{Σ}{$\Sigma$}
\newunicodechar{Φ}{$\Phi$}\newunicodechar{Ψ}{$\Psi$}\newunicodechar{Ω}{$\Omega$}
\newunicodechar{ℏ}{$\hbar$}\newunicodechar{ℓ}{$\ell$}\newunicodechar{ℝ}{$\mathbb{R}$}
\newunicodechar{ℂ}{$\mathbb{C}$}\newunicodechar{ℕ}{$\mathbb{N}$}\newunicodechar{ℤ}{$\mathbb{Z}$}
\newunicodechar{…}{\ldots}\newunicodechar{—}{---}\newunicodechar{–}{--}
\newunicodechar{‘}{`}\newunicodechar{’}{'}\newunicodechar{“}{``}\newunicodechar{”}{''}
\newunicodechar{·}{$\cdot$}\newunicodechar{↔}{$\leftrightarrow$}\newunicodechar{⟹}{$\Longrightarrow$}
\newunicodechar{⟸}{$\Longleftarrow$}\newunicodechar{⟺}{$\Longleftrightarrow$}
\newunicodechar{←}{$\leftarrow$}\newunicodechar{⇒}{$\Rightarrow$}\newunicodechar{⇐}{$\Leftarrow$}
\newunicodechar{⇔}{$\Leftrightarrow$}\newunicodechar{≡}{$\equiv$}\newunicodechar{≅}{$\cong$}
\newunicodechar{≃}{$\simeq$}\newunicodechar{∝}{$\propto$}\newunicodechar{∀}{$\forall$}
\newunicodechar{∃}{$\exists$}\newunicodechar{∅}{$\emptyset$}\newunicodechar{¬}{$\neg$}
\newunicodechar{∧}{$\wedge$}\newunicodechar{∨}{$\vee$}\newunicodechar{⊥}{$\perp$}
\newunicodechar{∥}{$\parallel$}\newunicodechar{∘}{$\circ$}\newunicodechar{•}{$\bullet$}
\newunicodechar{⊆}{$\subseteq$}\newunicodechar{⊂}{$\subset$}\newunicodechar{⊇}{$\supseteq$}
\newunicodechar{⊃}{$\supset$}\newunicodechar{∩}{$\cap$}\newunicodechar{∪}{$\cup$}
\newunicodechar{∖}{$\setminus$}\newunicodechar{⟨}{$\langle$}\newunicodechar{⟩}{$\rangle$}
\newunicodechar{†}{$\dagger$}\newunicodechar{′}{$'$}\newunicodechar{⊤}{$\top$}
\newunicodechar{⊨}{$\models$}\newunicodechar{⊢}{$\vdash$}\newunicodechar{∎}{$\blacksquare$}
\newunicodechar{☆}{$\star$}\newunicodechar{★}{$\star$}\newunicodechar{§}{\S}
\newunicodechar{²}{\textsuperscript{2}}\newunicodechar{³}{\textsuperscript{3}}
\newunicodechar{¹}{\textsuperscript{1}}\newunicodechar{₀}{\textsubscript{0}}
\newunicodechar{₁}{\textsubscript{1}}\newunicodechar{₂}{\textsubscript{2}}
\newunicodechar{₃}{\textsubscript{3}}\newunicodechar{ₙ}{\textsubscript{n}}
\newunicodechar{✓}{\checkmark}\newunicodechar{µ}{$\mu$}

\title{__TITLE__}
\author{__AUTHOR__}
\date{__DATE__}

\begin{document}
\maketitle

\begin{abstract}
\noindent
__ABSTRACT__

\medskip
\noindent\textbf{Keywords:} __KEYWORDS__
\end{abstract}
"""

POSTAMBLE = "\n\\end{document}\n"


# ---------------------------------------------------------------------------
# Frontmatter / abstract extraction
# ---------------------------------------------------------------------------
def parse_frontmatter(md: str) -> tuple[dict, str]:
    if not md.startswith("---\n") and not md.startswith("---\r\n"):
        return {}, md
    m = re.search(r"\n---\s*\n", md[4:])
    if not m:
        return {}, md
    fm_text, body = md[4:4 + m.start()], md[4 + m.end():]
    meta: dict[str, str] = {}
    for line in fm_text.split("\n"):
        km = re.match(r'^(\w+):\s*(.*)$', line)
        if km:
            val = km.group(2).strip()
            if val.startswith('"') and val.endswith('"'):
                val = val[1:-1]
            meta[km.group(1)] = val
    return meta, body


def extract_abstract(md: str) -> tuple[str, str, str]:
    """Return (abstract_text, keywords_text, body_without_abstract)."""
    m = re.search(r"^##\s+Abstract\s*\n(.*?)(?=\n##\s|\n#\s|\Z)", md,
                  re.DOTALL | re.MULTILINE)
    if not m:
        return "", "", md
    block = re.sub(r"\n\s*---+\s*$", "", m.group(1).strip()).strip()
    body = md[:m.start()] + md[m.end():]
    body = re.sub(r"^\s*\n---+\s*\n", "\n", body, count=1)
    kw = re.search(r"\n\s*\*\*Keywords:?\*\*\s*(.*)$", block, re.DOTALL)
    if kw:
        keywords = kw.group(1).strip()
        block = block[:kw.start()].strip()
    else:
        keywords = ""
    return block, keywords, body


def split_references(body: str) -> tuple[str, str]:
    """Peel off the `## References` section; return (body, references_block)."""
    m = re.search(r"^##\s+References\s*\n(.*?)(?=\n##\s|\n#\s|\Z)", body,
                  re.DOTALL | re.MULTILINE)
    if not m:
        return body, ""
    refs = m.group(1).strip()
    body = body[:m.start()] + body[m.end():]
    return body, refs


# ---------------------------------------------------------------------------
# Verbatim protection (raw-latex, code, math, inline code)
# ---------------------------------------------------------------------------
def _protect(pattern: str, text: str, store: list[str], flags=0) -> str:
    def repl(m: re.Match) -> str:
        store.append(m.group(1))
        return f"@@TOK{len(store)-1}@@"
    return re.sub(pattern, repl, text, flags=flags)


def _convert_headings(md: str) -> tuple[str, list[str]]:
    blocks: list[str] = []
    out: list[str] = []
    skipped_h1 = False
    for ln in md.split("\n"):
        m = re.match(r"^(#{1,6})\s+(.*)$", ln)
        if not m:
            out.append(ln)
            continue
        level = len(m.group(1))
        title = m.group(2).strip().rstrip("#").strip()
        if level == 1 and not skipped_h1:
            skipped_h1 = True
            continue
        title = re.sub(r"^\d+[A-Za-z]?(?:\.\d+[a-z]?)*\.?\s+", "", title)
        sec = level - 1  # ## -> section
        if title == "Acknowledgements":
            latex = r"\section*{" + title + "}"
        elif sec <= 1:
            latex = r"\section{" + title + "}"
        elif sec == 2:
            latex = r"\subsection{" + title + "}"
        else:
            latex = r"\subsubsection{" + title + "}"
        blocks.append(latex)
        out.append(f"@@HEAD{len(blocks)-1}@@")
    return "\n".join(out), blocks


def _escape_prose(text: str) -> str:
    for a, b in (("\\", r"\textbackslash{}"), ("&", r"\&"), ("%", r"\%"),
                 ("#", r"\#"), ("_", r"\_"), ("{", r"\{"), ("}", r"\}"),
                 ("~", r"\textasciitilde{}"), ("^", r"\textasciicircum{}")):
        text = text.replace(a, b)
    return text


def _convert_emphasis(text: str) -> str:
    # bold may wrap across a line break (a bold lead-in on a list item), so the
    # body class allows newlines; non-greedy stops at the nearest closing **.
    text = re.sub(r"\*\*([^*]+?)\*\*", lambda m: r"\textbf{" + m.group(1) + "}", text)
    text = re.sub(r"(?<![*\w])\*([^*\n]+?)\*(?![*\w])",
                  lambda m: r"\emph{" + m.group(1) + "}", text)
    return text


def _convert_links(text: str) -> str:
    return re.sub(r"\[([^\]]+)\]\(([^)]+)\)",
                  lambda m: r"\href{" + m.group(2) + "}{" + m.group(1) + "}", text)


def _convert_blockquotes(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    i, n = 0, len(lines)
    while i < n:
        if lines[i].lstrip().startswith(">"):
            buf: list[str] = []
            while i < n and lines[i].lstrip().startswith(">"):
                buf.append(lines[i].lstrip()[1:].lstrip())
                i += 1
            out.append(r"\begin{center}\fbox{\begin{minipage}{0.93\linewidth}")
            out.append("\n".join(buf))
            out.append(r"\end{minipage}}\end{center}")
        else:
            out.append(lines[i]); i += 1
    return "\n".join(out)


_BULLET = re.compile(r"^(\s*)[-*+]\s+(.*)$")
_NUM = re.compile(r"^(\s*)\d+\.\s+(.*)$")


def _item_match(s: str):
    """Return (env, content) if the line starts a list item, else None."""
    m = _BULLET.match(s)
    if m:
        return ("itemize", m.group(2))
    m = _NUM.match(s)
    if m:
        return ("enumerate", m.group(2))
    return None


def _convert_lists(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    i, n = 0, len(lines)
    while i < n:
        m = _item_match(lines[i])
        if not m:
            out.append(lines[i]); i += 1
            continue
        env = m[0]
        out.append(r"\begin{" + env + "}")
        while i < n:
            m = _item_match(lines[i])
            if not m:
                break
            content = m[1]
            i += 1
            # fold continuation lines (indented/non-blank, not a new item) into this item
            while i < n and lines[i].strip() != "" and not _item_match(lines[i]):
                content += " " + lines[i].strip()
                i += 1
            out.append(r"  \item " + content)
            # a blank line continues the same list only if another item follows
            if i < n and lines[i].strip() == "":
                j = i
                while j < n and lines[j].strip() == "":
                    j += 1
                if j < n and _item_match(lines[j]):
                    i = j
                else:
                    break
        out.append(r"\end{" + env + "}")
    return "\n".join(out)


def _drop_hr(text: str) -> str:
    return "\n".join("" if re.match(r"^---+\s*$", ln.strip()) else ln
                     for ln in text.split("\n"))


def _split_row(line: str) -> list[str]:
    s = line.strip()
    if s.startswith("|"): s = s[1:]
    if s.endswith("|"): s = s[:-1]
    return [c.strip() for c in s.split("|")]


def _convert_tables(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    i, n = 0, len(lines)
    while i < n:
        line = lines[i].strip()
        is_table = (line.startswith("|") and i + 1 < n and
                    re.match(r"^\|?[\s:|-]+\|?$", lines[i + 1].strip()) and
                    "|" in lines[i + 1])
        if not is_table:
            out.append(lines[i]); i += 1; continue

        # caption: a preceding **Table N. ...** line already in `out`
        caption = ""
        j = len(out) - 1
        while j >= 0 and out[j].strip() == "":
            j -= 1
        if j >= 0:
            cm = re.match(r"^\*\*(Table[^*]+?)\*\*\s*$", out[j].strip())
            if cm:
                # drop the leading "Table N." — LaTeX supplies its own label/number
                caption = re.sub(r"^Table\s+\d+[.:]\s*", "", cm.group(1).strip())
                del out[j:]

        header = _split_row(lines[i])
        ncols = len(header)
        i += 2
        body: list[list[str]] = []
        while i < n and lines[i].strip().startswith("|"):
            row = _split_row(lines[i])
            row = (row + [""] * ncols)[:ncols]
            body.append(row)
            i += 1

        if ncols == 2:
            colspec = r"@{}>{\raggedright\arraybackslash}p{0.60\linewidth}Y@{}"
        else:
            colspec = "@{}" + "Y" * ncols + "@{}"
        out.append(r"\begin{table}[ht]")
        out.append(r"\centering")
        if caption:
            out.append(r"\caption{" + caption + "}")
        out.append(r"\begin{tabularx}{\linewidth}{" + colspec + "}")
        out.append(r"\toprule")
        out.append(" & ".join(r"\textbf{" + c + "}" for c in header) + r" \\")
        out.append(r"\midrule")
        for row in body:
            out.append(" & ".join(row) + r" \\")
        out.append(r"\bottomrule")
        out.append(r"\end{tabularx}")
        out.append(r"\end{table}")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Inline fragment conversion (abstract, keywords, caption text, bib entries)
# ---------------------------------------------------------------------------
def convert_inline(md: str) -> str:
    math: list[str] = []
    inline: list[str] = []
    md = re.sub(r"(?<!\$)\$(?!\$)([^\$\n]+?)\$(?!\$)",
                lambda m: (math.append("$" + m.group(1) + "$"),
                           f"@@MATH{len(math)-1}@@")[1], md)
    md = _protect(r"`([^`\n]+)`", md, inline)
    md = _escape_prose(md)
    md = _convert_links(md)
    md = _convert_emphasis(md)
    md = re.sub(r"@@MATH(\d+)@@", lambda m: math[int(m.group(1))], md)
    md = re.sub(r"@@TOK(\d+)@@",
                lambda m: r"\texttt{" + _escape_verb(inline[int(m.group(1))]) + "}", md)
    return md


def _escape_verb(s: str) -> str:
    s = s.replace("\\", r"\textbackslash{}")
    for a, b in (("&", r"\&"), ("%", r"\%"), ("$", r"\$"), ("#", r"\#"),
                 ("_", r"\_"), ("{", r"\{"), ("}", r"\}"),
                 ("~", r"\textasciitilde{}"), ("^", r"\textasciicircum{}")):
        s = s.replace(a, b)
    return s


def convert_references(refs: str) -> str:
    if not refs.strip():
        return ""
    items = []
    for m in re.finditer(r"\[(\d+)\]\s*(.*?)(?=\n\s*\[\d+\]|\Z)", refs, re.DOTALL):
        num = m.group(1)
        entry = re.sub(r"\s+", " ", m.group(2).strip())
        items.append(r"\bibitem{r" + num + "} " + convert_inline(entry))
    if not items:
        return ""
    return ("\n\\begin{thebibliography}{99}\n\n"
            + "\n".join(items) + "\n\n\\end{thebibliography}\n")


# ---------------------------------------------------------------------------
# convert_body needs prefixed tokens; reimplement protection cleanly here.
# ---------------------------------------------------------------------------
def _build_body(md: str) -> str:
    store: dict[str, list[str]] = {"RAW": [], "CODE": [], "INLINE": []}

    def prot(tag, pattern, flags=0):
        nonlocal md
        def repl(m):
            store[tag].append(m.group(1))
            return f"@@{tag}{len(store[tag])-1}@@"
        md = re.sub(pattern, repl, md, flags=flags)

    prot("RAW", r"```\{=latex\}\n(.*?)```", re.DOTALL)
    prot("CODE", r"```[a-zA-Z]*\n(.*?)```", re.DOTALL)

    math: list[str] = []
    md = re.sub(r"\$\$(.*?)\$\$",
                lambda m: (math.append(m.group(1)), f"@@DISP{len(math)-1}@@")[1],
                md, flags=re.DOTALL)
    inlinemath: list[str] = []
    md = re.sub(r"(?<!\$)\$(?!\$)([^\$\n]+?)\$(?!\$)",
                lambda m: (inlinemath.append("$" + m.group(1) + "$"),
                           f"@@IMATH{len(inlinemath)-1}@@")[1], md)
    prot("INLINE", r"`([^`\n]+)`")

    md, headings = _convert_headings(md)

    # Escape prose FIRST; every converter below emits LaTeX control sequences
    # that must not be re-escaped. Protected spans are alnum tokens and survive.
    md = _escape_prose(md)

    # citations operate on escaped text ([ and ] are not escaped); links have
    # non-digit anchor text so the digit-only citation regex never eats them.
    md = re.sub(r"\[(\d+(?:\s*,\s*\d+)*)\]",
                lambda m: r"\cite{" + ",".join("r" + x.strip()
                          for x in m.group(1).split(",")) + "}", md)

    # Lists BEFORE tables: while pipe-table rows still begin with "|", list
    # detection won't mis-read a cell that starts with "+ "/"- " as a bullet.
    md = _convert_blockquotes(md)
    md = _convert_lists(md)
    md = _convert_tables(md)
    md = _drop_hr(md)
    md = _convert_links(md)
    md = _convert_emphasis(md)

    md = re.sub(r"@@HEAD(\d+)@@", lambda m: headings[int(m.group(1))], md)
    md = re.sub(r"@@DISP(\d+)@@",
                lambda m: "\n\\[\n" + math[int(m.group(1))].strip() + "\n\\]\n", md)
    md = re.sub(r"@@IMATH(\d+)@@", lambda m: inlinemath[int(m.group(1))], md)
    md = re.sub(r"@@RAW(\d+)@@", lambda m: store["RAW"][int(m.group(1))], md)
    # alltt (not verbatim): keeps \ { } active so newunicodechar substitutions fire,
    # letting Lean's unicode (∀ ∑ → η Λ …) render in code blocks. Code fences must
    # therefore avoid literal \ { } and any unicode not covered by the preamble map.
    md = re.sub(r"@@CODE(\d+)@@",
                lambda m: "\n{\\footnotesize\\begin{alltt}\n" + store["CODE"][int(m.group(1))].rstrip("\n")
                          + "\n\\end{alltt}}\n", md)
    md = re.sub(r"@@INLINE(\d+)@@",
                lambda m: r"\texttt{" + _escape_verb(store["INLINE"][int(m.group(1))]) + "}", md)
    return re.sub(r"\n{3,}", "\n\n", md)


def build() -> str:
    md = SRC.read_text(encoding="utf-8").replace("﻿", "")
    meta, body = parse_frontmatter(md)
    abstract_md, keywords_md, body = extract_abstract(body)
    body, refs_md = split_references(body)

    title = meta.get("title", SRC.stem)
    if ": " in title:  # mimic the two-line title of the original
        head, tail = title.split(": ", 1)
        title = head + ":\\\\\n" + tail
    author = meta.get("author", "")
    date = meta.get("date", "")

    preamble = (PREAMBLE
                .replace("__TITLE__", title)
                .replace("__AUTHOR__", author)
                .replace("__DATE__", date)
                .replace("__ABSTRACT__", convert_inline(abstract_md))
                .replace("__KEYWORDS__", convert_inline(keywords_md)))

    tex = preamble + "\n" + _build_body(body) + convert_references(refs_md) + POSTAMBLE
    OUT_DIR.mkdir(exist_ok=True)
    OUT_TEX.write_text(tex, encoding="utf-8")
    print(f"wrote {OUT_TEX.relative_to(REPO)} ({len(tex)} chars)")
    return tex


def compile_pdf() -> bool:
    for tool in (["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                 ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"]):
        try:
            r = subprocess.run(tool, cwd=str(OUT_DIR), capture_output=True, text=True)
        except FileNotFoundError:
            continue
        if tool[0] == "pdflatex":  # second pass for refs/toc
            subprocess.run(tool, cwd=str(OUT_DIR), capture_output=True, text=True)
        ok = (OUT_DIR / "main.pdf").exists() and r.returncode == 0
        print(f"{tool[0]}: {'OK' if ok else 'FAILED (exit %d)' % r.returncode}")
        if not ok:
            print("\n".join(r.stdout.split("\n")[-40:]))
        return ok
    print("no LaTeX engine found")
    return False


if __name__ == "__main__":
    build()
    if "--no-pdf" not in sys.argv:
        sys.exit(0 if compile_pdf() else 1)
