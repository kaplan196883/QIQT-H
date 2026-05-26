"""
TUTORIAL.md -> LaTeX -> PDF builder for QIQT-H.

Modeled after Wings/scripts/build_paper_tex.py, kept simpler because
TUTORIAL.md has no figures, no bibliography, and no theorem environments
that need special treatment.

Pipeline:
  1. Read TUTORIAL.md.
  2. Extract title (first H1).
  3. Walk section tree (#, ##, ###, ####).
  4. Translate inline patterns: bold, italic, code, links.
  5. Translate lists (- and 1.) and blockquotes.
  6. Translate markdown tables to tabular environments.
  7. Pass math expressions ($...$ and $$...$$) through unchanged.
  8. Substitute Unicode characters that pdflatex can't handle.
  9. Write build/qiqt_tutorial.tex.
 10. Run pdflatex twice (for ToC + cross-refs).

Usage:
    python scripts/build_tutorial_pdf.py
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "TUTORIAL.md"
OUT_DIR = REPO / "build"
OUT_TEX = OUT_DIR / "qiqt_tutorial.tex"
OUT_PDF = OUT_DIR / "qiqt_tutorial.pdf"


# ---------------------------------------------------------------------------
# Preamble — self-contained, arxiv-preprint-like
# ---------------------------------------------------------------------------

PREAMBLE = r"""\documentclass[11pt,a4paper]{article}

\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{textcomp}
\usepackage{lmodern}

\usepackage[a4paper,margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}

\usepackage{xcolor}
\usepackage{hyperref}
\hypersetup{
  colorlinks=true,
  linkcolor=blue!60!black,
  citecolor=blue!60!black,
  urlcolor=blue!60!black,
  breaklinks=true,
}

\usepackage{tabularx}
\usepackage{array}
\newcolumntype{Y}{>{\raggedright\arraybackslash}X}
\usepackage{booktabs}

\usepackage{enumitem}
\setlist[itemize]{leftmargin=*,topsep=2pt,partopsep=0pt,parsep=2pt,itemsep=2pt}
\setlist[enumerate]{leftmargin=*,topsep=2pt,partopsep=0pt,parsep=2pt,itemsep=2pt}

\usepackage{etoolbox}
\setlength{\emergencystretch}{3em}
\tolerance=1000

\usepackage{mdframed}
\definecolor{quotebg}{gray}{0.965}
\definecolor{quoterule}{gray}{0.55}
\mdfdefinestyle{quotestyle}{%
  backgroundcolor=quotebg,
  linecolor=quoterule,
  linewidth=0pt,
  leftline=true,
  innerleftmargin=10pt,
  innerrightmargin=6pt,
  innertopmargin=4pt,
  innerbottommargin=4pt,
  skipabove=4pt,
  skipbelow=4pt
}
\newenvironment{qiqtquote}{\begin{mdframed}[style=quotestyle]}{\end{mdframed}}

\definecolor{codebg}{gray}{0.96}
\mdfdefinestyle{codestyle}{%
  backgroundcolor=codebg,
  linecolor=quoterule,
  linewidth=0pt,
  leftline=true,
  innerleftmargin=8pt,
  innerrightmargin=4pt,
  innertopmargin=4pt,
  innerbottommargin=4pt,
  skipabove=4pt,
  skipbelow=4pt
}
\newenvironment{qiqtcode}{\begingroup\footnotesize\ttfamily\begin{mdframed}[style=codestyle]}{\end{mdframed}\endgroup}

% Unicode characters used in TUTORIAL.md
\usepackage{newunicodechar}
\newunicodechar{−}{$-$}
\newunicodechar{×}{$\times$}
\newunicodechar{÷}{$\div$}
\newunicodechar{±}{$\pm$}
\newunicodechar{≈}{$\approx$}
\newunicodechar{≠}{$\neq$}
\newunicodechar{≤}{$\leq$}
\newunicodechar{≥}{$\geq$}
\newunicodechar{∈}{$\in$}
\newunicodechar{∉}{$\notin$}
\newunicodechar{∞}{$\infty$}
\newunicodechar{→}{$\to$}
\newunicodechar{↦}{$\mapsto$}
\newunicodechar{⊗}{$\otimes$}
\newunicodechar{⊕}{$\oplus$}
\newunicodechar{⊂}{$\subset$}
\newunicodechar{⊆}{$\subseteq$}
\newunicodechar{∩}{$\cap$}
\newunicodechar{∪}{$\cup$}
\newunicodechar{∂}{$\partial$}
\newunicodechar{∇}{$\nabla$}
\newunicodechar{∑}{$\sum$}
\newunicodechar{∫}{$\int$}
\newunicodechar{√}{$\sqrt{}$}
\newunicodechar{α}{$\alpha$}
\newunicodechar{β}{$\beta$}
\newunicodechar{γ}{$\gamma$}
\newunicodechar{δ}{$\delta$}
\newunicodechar{ε}{$\varepsilon$}
\newunicodechar{ζ}{$\zeta$}
\newunicodechar{η}{$\eta$}
\newunicodechar{θ}{$\theta$}
\newunicodechar{λ}{$\lambda$}
\newunicodechar{μ}{$\mu$}
\newunicodechar{ν}{$\nu$}
\newunicodechar{ξ}{$\xi$}
\newunicodechar{π}{$\pi$}
\newunicodechar{ρ}{$\rho$}
\newunicodechar{σ}{$\sigma$}
\newunicodechar{τ}{$\tau$}
\newunicodechar{φ}{$\varphi$}
\newunicodechar{χ}{$\chi$}
\newunicodechar{ψ}{$\psi$}
\newunicodechar{ω}{$\omega$}
\newunicodechar{Γ}{$\Gamma$}
\newunicodechar{Δ}{$\Delta$}
\newunicodechar{Θ}{$\Theta$}
\newunicodechar{Λ}{$\Lambda$}
\newunicodechar{Π}{$\Pi$}
\newunicodechar{Σ}{$\Sigma$}
\newunicodechar{Φ}{$\Phi$}
\newunicodechar{Ψ}{$\Psi$}
\newunicodechar{Ω}{$\Omega$}
\newunicodechar{ℏ}{$\hbar$}
\newunicodechar{ℓ}{$\ell$}
\newunicodechar{ℝ}{$\mathbb{R}$}
\newunicodechar{ℂ}{$\mathbb{C}$}
\newunicodechar{ℕ}{$\mathbb{N}$}
\newunicodechar{ℤ}{$\mathbb{Z}$}
\newunicodechar{ℍ}{$\mathbb{H}$}
\newunicodechar{ℰ}{$\mathcal{E}$}
\newunicodechar{✓}{\checkmark}
\newunicodechar{✗}{$\times$}
\newunicodechar{…}{\ldots}
\newunicodechar{—}{---}
\newunicodechar{–}{--}
\newunicodechar{‘}{`}
\newunicodechar{’}{'}
\newunicodechar{“}{``}
\newunicodechar{”}{''}
\newunicodechar{·}{$\cdot$}
\newunicodechar{∼}{$\sim$}
\newunicodechar{ν}{$\nu$}
\newunicodechar{‐}{-}
\newunicodechar{‑}{-}

\title{A Tutorial on QIQT-H}
\author{Paweł Kapłański}
\date{May 26, 2026}

\begin{document}
\maketitle

\begin{abstract}
\noindent How holographic finite-information constraints can — in principle —
address the measurement problem of quantum mechanics, without adding collapses,
worlds as separate substances, or hidden trajectories. This tutorial walks
through the entire QIQT-H framework piece by piece, building every advanced
concept from undergraduate quantum mechanics. The framework is presented as a
research program, not a completed theory; its borrowed mathematical machinery
(Witten/CPW Type II crossed-product algebras) and its central new physical
postulate (the Branch-Summed Holographic Bound as superselection rule) are
clearly distinguished, and its open problems are honestly flagged.
\end{abstract}

\tableofcontents
\newpage
"""

POSTAMBLE = r"""
\end{document}
"""


# ---------------------------------------------------------------------------
# Math protection (pass-through)
# ---------------------------------------------------------------------------

def _protect_math(text: str) -> tuple[str, list[str]]:
    """Replace $$...$$ and $...$ blocks with placeholders; return blocks for
    later restoration. Order matters: protect $$ first, then $."""
    blocks: list[str] = []

    def _repl_display(m: re.Match) -> str:
        blocks.append(m.group(0))
        return f"@@MATHBLOCK{len(blocks)-1}@@"

    # $$...$$ display math (possibly multiline)
    text = re.sub(r"\$\$.*?\$\$", _repl_display, text, flags=re.DOTALL)
    # $...$ inline math (single-line only, non-greedy, avoid matching $$ remnants)
    text = re.sub(r"(?<!\$)\$(?!\$)([^\$\n]+?)\$(?!\$)",
                  lambda m: (blocks.append(m.group(0)), f"@@MATHBLOCK{len(blocks)-1}@@")[1],
                  text)
    return text, blocks


def _restore_math(text: str, blocks: list[str]) -> str:
    def _convert_block(s: str) -> str:
        # $$X$$ -> \[X\] ; $X$ -> $X$ (keep)
        if s.startswith("$$") and s.endswith("$$"):
            inner = s[2:-2].strip()
            return "\n\\[\n" + inner + "\n\\]\n"
        # leave $...$ alone
        return s

    def _restore(m: re.Match) -> str:
        idx = int(m.group(1))
        return _convert_block(blocks[idx])

    return re.sub(r"@@MATHBLOCK(\d+)@@", _restore, text)


# ---------------------------------------------------------------------------
# Code-block protection (fenced ``` blocks)
# ---------------------------------------------------------------------------

def _protect_code(text: str) -> tuple[str, list[str]]:
    blocks: list[str] = []

    def _repl(m: re.Match) -> str:
        blocks.append(m.group(1))
        return f"@@CODEBLOCK{len(blocks)-1}@@"

    text = re.sub(r"```[a-zA-Z]*\n(.*?)```", _repl, text, flags=re.DOTALL)
    return text, blocks


def _restore_code(text: str, blocks: list[str]) -> str:
    def _restore(m: re.Match) -> str:
        idx = int(m.group(1))
        body = blocks[idx].rstrip("\n")
        return "\n\\begin{qiqtcode}\n" + body + "\n\\end{qiqtcode}\n"
    return re.sub(r"@@CODEBLOCK(\d+)@@", _restore, text)


# ---------------------------------------------------------------------------
# Inline code (`...`) — protect from escaping, then wrap in \texttt
# ---------------------------------------------------------------------------

def _protect_inline_code(text: str) -> tuple[str, list[str]]:
    blocks: list[str] = []

    def _repl(m: re.Match) -> str:
        blocks.append(m.group(1))
        return f"@@INLINECODE{len(blocks)-1}@@"
    text = re.sub(r"`([^`\n]+)`", _repl, text)
    return text, blocks


def _restore_inline_code(text: str, blocks: list[str]) -> str:
    def _restore(m: re.Match) -> str:
        idx = int(m.group(1))
        body = blocks[idx]
        body = body.replace("\\", r"\textbackslash{}")
        body = (body.replace("&", r"\&").replace("%", r"\%")
                .replace("$", r"\$").replace("#", r"\#")
                .replace("_", r"\_").replace("{", r"\{").replace("}", r"\}")
                .replace("~", r"\textasciitilde{}").replace("^", r"\textasciicircum{}"))
        return r"\texttt{" + body + r"}"
    return re.sub(r"@@INLINECODE(\d+)@@", _restore, text)


# ---------------------------------------------------------------------------
# Escape special characters in prose (avoid breaking math/code placeholders)
# ---------------------------------------------------------------------------

def _escape_prose(text: str) -> str:
    """Escape LaTeX-special characters in prose. Placeholders are safe
    because they only contain @, digits, and uppercase letters."""
    # Order matters: backslash first, then others
    text = text.replace("\\", r"\textbackslash{}")
    text = text.replace("&", r"\&")
    text = text.replace("%", r"\%")
    text = text.replace("#", r"\#")
    text = text.replace("_", r"\_")
    text = text.replace("{", r"\{")
    text = text.replace("}", r"\}")
    text = text.replace("~", r"\textasciitilde{}")
    text = text.replace("^", r"\textasciicircum{}")
    return text


# ---------------------------------------------------------------------------
# Headings
# ---------------------------------------------------------------------------

def _convert_headings(text: str) -> tuple[str, list[str]]:
    """Convert markdown headings to placeholder tokens so that the escape
    pass doesn't mangle the LaTeX backslashes and braces. The placeholders
    are restored at the end of the pipeline.

    # -> \section ; ## -> \subsection ; ### -> \subsubsection ; #### -> \paragraph
    """
    blocks: list[str] = []
    lines = text.split("\n")
    out: list[str] = []
    for ln in lines:
        m = re.match(r"^(#{1,6})\s+(.*)$", ln)
        if m:
            level = len(m.group(1))
            title = m.group(2).strip().rstrip("#").strip()
            if level == 1 and title == "A Tutorial on QIQT-H":
                continue
            # Strip leading "N.", "N.N", "N.N.N" numbering — LaTeX adds its own.
            title = re.sub(r"^\d+(?:\.\d+)*\.?\s+", "", title)
            if level == 1:
                latex = r"\section{" + title + r"}"
            elif level == 2:
                latex = r"\subsection{" + title + r"}"
            elif level == 3:
                latex = r"\subsubsection{" + title + r"}"
            else:
                latex = r"\paragraph{" + title + r"}"
            blocks.append(latex)
            out.append(f"@@HEADING{len(blocks)-1}@@")
        else:
            out.append(ln)
    return "\n".join(out), blocks


def _restore_headings(text: str, blocks: list[str]) -> str:
    def _restore(m: re.Match) -> str:
        return blocks[int(m.group(1))]
    return re.sub(r"@@HEADING(\d+)@@", _restore, text)


# ---------------------------------------------------------------------------
# Inline emphasis: **bold** and *italic*
# ---------------------------------------------------------------------------

def _convert_emphasis(text: str) -> str:
    # **bold** -> \textbf{bold}
    text = re.sub(r"\*\*([^*\n]+?)\*\*",
                  lambda m: r"\textbf{" + m.group(1) + r"}", text)
    # *italic* -> \emph{italic}  (avoid touching * inside words)
    text = re.sub(r"(?<![*\w])\*([^*\n]+?)\*(?![*\w])",
                  lambda m: r"\emph{" + m.group(1) + r"}", text)
    return text


# ---------------------------------------------------------------------------
# Links: [text](url) -> \href{url}{text}
# ---------------------------------------------------------------------------

def _convert_links(text: str) -> str:
    def _repl(m: re.Match) -> str:
        link_text = m.group(1)
        url = m.group(2)
        return r"\href{" + url + "}{" + link_text + "}"
    return re.sub(r"\[([^\]]+)\]\(([^)]+)\)", _repl, text)


# ---------------------------------------------------------------------------
# Blockquotes: contiguous "> ..." lines -> qiqtquote env
# ---------------------------------------------------------------------------

def _convert_blockquotes(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    i = 0
    n = len(lines)
    while i < n:
        if lines[i].lstrip().startswith(">"):
            block_lines: list[str] = []
            while i < n and lines[i].lstrip().startswith(">"):
                stripped = lines[i].lstrip()[1:].lstrip()
                block_lines.append(stripped)
                i += 1
            out.append(r"\begin{qiqtquote}")
            out.append("\n".join(block_lines))
            out.append(r"\end{qiqtquote}")
        else:
            out.append(lines[i])
            i += 1
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Lists: bullet (-, *) and numbered (1., 2., ...)
# Single-level only for now (tutorial uses mostly single-level lists).
# ---------------------------------------------------------------------------

_BULLET_RE = re.compile(r"^(\s*)[-*+]\s+(.*)$")
_NUMBER_RE = re.compile(r"^(\s*)\d+\.\s+(.*)$")


def _convert_lists(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    i = 0
    n = len(lines)

    def _is_bullet(line: str) -> bool:
        return bool(_BULLET_RE.match(line))

    def _is_number(line: str) -> bool:
        return bool(_NUMBER_RE.match(line))

    while i < n:
        line = lines[i]
        if _is_bullet(line):
            out.append(r"\begin{itemize}")
            while i < n and (_is_bullet(lines[i]) or
                             (lines[i].strip() == "" and i + 1 < n and _is_bullet(lines[i + 1]))):
                if lines[i].strip() == "":
                    i += 1
                    continue
                m = _BULLET_RE.match(lines[i])
                item_text = m.group(2)
                out.append(r"  \item " + item_text)
                i += 1
            out.append(r"\end{itemize}")
        elif _is_number(line):
            out.append(r"\begin{enumerate}")
            while i < n and (_is_number(lines[i]) or
                             (lines[i].strip() == "" and i + 1 < n and _is_number(lines[i + 1]))):
                if lines[i].strip() == "":
                    i += 1
                    continue
                m = _NUMBER_RE.match(lines[i])
                item_text = m.group(2)
                out.append(r"  \item " + item_text)
                i += 1
            out.append(r"\end{enumerate}")
        else:
            out.append(line)
            i += 1

    return "\n".join(out)


# ---------------------------------------------------------------------------
# Tables: GitHub-flavored markdown tables -> tabularx
# ---------------------------------------------------------------------------

def _split_table_row(line: str) -> list[str]:
    s = line.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|"):
        s = s[:-1]
    return [c.strip() for c in s.split("|")]


def _convert_tables(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i].strip()
        # Detect a table start: a row, then a separator line.
        if (line.startswith("|") and i + 1 < n and
                re.match(r"^\|?[\s:|-]+\|?$", lines[i + 1].strip()) and
                "|" in lines[i + 1]):
            header = _split_table_row(lines[i])
            ncols = len(header)
            i += 2  # skip header and separator
            body: list[list[str]] = []
            while i < n and lines[i].strip().startswith("|"):
                row = _split_table_row(lines[i])
                # Pad/trim to ncols
                if len(row) < ncols:
                    row = row + [""] * (ncols - len(row))
                elif len(row) > ncols:
                    row = row[:ncols]
                body.append(row)
                i += 1

            col_spec = "|" + "|".join(["Y"] * ncols) + "|"
            out.append(r"\begin{center}")
            out.append(r"\small")
            out.append(r"\begin{tabularx}{\linewidth}{" + col_spec + "}")
            out.append(r"\hline")
            out.append(" & ".join([r"\textbf{" + c + "}" for c in header]) + r" \\")
            out.append(r"\hline")
            for row in body:
                out.append(" & ".join(row) + r" \\")
                out.append(r"\hline")
            out.append(r"\end{tabularx}")
            out.append(r"\end{center}")
        else:
            out.append(lines[i])
            i += 1
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Horizontal rules: --- -> \medskip\hrule\medskip
# ---------------------------------------------------------------------------

def _convert_hr(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    for ln in lines:
        if re.match(r"^---+\s*$", ln.strip()):
            out.append(r"\medskip\hrule\medskip")
        else:
            out.append(ln)
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Convert YAML / metadata front-matter and italic intro (first *...* block)
# ---------------------------------------------------------------------------

def _strip_italic_intro(text: str) -> str:
    """Strip the italic abstract line right under the title since we already
    have an \\abstract block in the preamble."""
    # The intro line is just *italic text* on a single line right after title
    # We handle this in the preamble's \begin{abstract}.
    # Just remove the first standalone italic block that appears at the top.
    pattern = re.compile(r"\A\*([^*\n]+(?:\n[^*\n]+)*)\*", re.MULTILINE)
    return pattern.sub("", text, count=1)


# ---------------------------------------------------------------------------
# Paragraph wrapping: convert single newlines to spaces within a paragraph
# (LaTeX doesn't need the markdown newline structure)
# Actually, leave them — LaTeX handles them fine. Just collapse multiple
# blank lines to single \par equivalents.
# ---------------------------------------------------------------------------

def _normalize_blank_lines(text: str) -> str:
    return re.sub(r"\n{3,}", "\n\n", text)


# ---------------------------------------------------------------------------
# Main conversion
# ---------------------------------------------------------------------------

def convert_md_to_tex(md: str) -> str:
    # 1. Strip the title H1 (we handle title in preamble)
    # 2. Strip the italic intro line
    md = _strip_italic_intro(md)

    # 3. Protect code blocks first (their content is verbatim, no further conversion)
    md, code_blocks = _protect_code(md)

    # 4. Protect math (pass-through unchanged into LaTeX)
    md, math_blocks = _protect_math(md)

    # 5. Protect inline code (`...`)
    md, inline_code_blocks = _protect_inline_code(md)

    # 6. Convert headings to placeholders FIRST — they use `#` markers which
    #    are in the escape list, AND their LaTeX output contains \ and {}
    #    that must not be re-escaped.
    md, heading_blocks = _convert_headings(md)

    # 7. ESCAPE prose specials. Structural placeholders (HEADING, MATH,
    #    CODE, INLINECODE) only contain @, digits, uppercase letters — safe
    #    to leave alone during escape.
    md = _escape_prose(md)

    # 8. Convert remaining structural elements. These produce LaTeX output;
    #    nothing else escapes after this point.
    md = _convert_tables(md)
    md = _convert_hr(md)
    md = _convert_blockquotes(md)
    md = _convert_lists(md)

    # 9. Convert inline elements
    md = _convert_links(md)
    md = _convert_emphasis(md)

    # 10. Restore protected content. Headings FIRST — heading titles may
    #     contain @@MATHBLOCK###@@ / @@INLINECODE###@@ tokens that were
    #     captured into heading_blocks at protection time; restoring the
    #     headings first puts those tokens back into the document so the
    #     subsequent math / inline-code passes can resolve them.
    md = _restore_headings(md, heading_blocks)
    md = _restore_inline_code(md, inline_code_blocks)
    md = _restore_math(md, math_blocks)
    md = _restore_code(md, code_blocks)

    # 10. Normalize blank lines
    md = _normalize_blank_lines(md)

    return md


def main() -> int:
    if not SRC.exists():
        print(f"ERROR: {SRC} not found.")
        return 1

    OUT_DIR.mkdir(exist_ok=True)

    print(f"[1/3] Reading {SRC.relative_to(REPO)}")
    md = SRC.read_text(encoding="utf-8")
    print(f"      {len(md)} chars, {md.count(chr(10)) + 1} lines")

    print("[2/3] Converting markdown to LaTeX")
    body = convert_md_to_tex(md)
    tex = PREAMBLE + body + POSTAMBLE

    OUT_TEX.write_text(tex, encoding="utf-8")
    print(f"      wrote {OUT_TEX.relative_to(REPO)} ({len(tex)} chars)")

    print("[3/3] Running pdflatex (twice for ToC)")
    for pass_num in (1, 2):
        result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
             "-output-directory", str(OUT_DIR), str(OUT_TEX)],
            capture_output=True,
            text=True,
            cwd=str(OUT_DIR),
        )
        if result.returncode != 0:
            print(f"      pdflatex pass {pass_num} FAILED (exit {result.returncode})")
            # Print last 50 lines of stdout for diagnosis
            tail = "\n".join(result.stdout.split("\n")[-50:])
            print(tail)
            return 1
        print(f"      pdflatex pass {pass_num} OK")

    if OUT_PDF.exists():
        pdf_size = OUT_PDF.stat().st_size
        print(f"\nSUCCESS: {OUT_PDF.relative_to(REPO)} ({pdf_size / 1024:.1f} KB)")
    else:
        print(f"\nERROR: {OUT_PDF.relative_to(REPO)} not produced")
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
