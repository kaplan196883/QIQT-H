"""
Generic markdown -> LaTeX -> PDF builder for QIQT-H documents.

Modeled after build_tutorial_pdf.py but generalized: reads YAML frontmatter
(title/author/date) when present, auto-detects "## Abstract" + "**Keywords:**"
blocks at the top, and emits one PDF per input markdown file.

Usage:
    python scripts/build_pdf.py                 # builds all DOCS
    python scripts/build_pdf.py TUTORIAL.md     # builds just one
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
OUT_DIR = REPO / "build"

DOCS = [
    REPO / "TUTORIAL.md",
    REPO / "QIQT_Position_Paper.md",
    REPO / "QIQT_Math.md",
    REPO / "QIQT_Foundations_Paper.md",
]

# Per-document fallback metadata for files without YAML frontmatter.
DEFAULTS = {
    "TUTORIAL.md": {
        "title": "A Tutorial on QIQT-H",
        "author": r"Paweł Kapłański",
        "date": "May 27, 2026",
        "abstract": (
            r"How holographic finite-information constraints can --- in principle --- "
            r"address the measurement problem of quantum mechanics, without adding collapses, "
            r"worlds as separate substances, or hidden trajectories. This tutorial walks "
            r"through the entire QIQT-H framework piece by piece, building every advanced "
            r"concept from undergraduate quantum mechanics. The framework is presented as a "
            r"research program, not a completed theory; its borrowed mathematical machinery "
            r"(Witten/CPW Type II crossed-product algebras) and its central new physical "
            r"postulate (the Branch-Summed Holographic Bound as superselection rule) are "
            r"clearly distinguished, and its open problems are honestly flagged."
        ),
        "keywords": "",
    },
}


# ---------------------------------------------------------------------------
# Preamble — substituted with __TITLE__ / __AUTHOR__ / __DATE__ / __ABSTRACT__
# / __KEYWORDS__. Using markers (not .format) to avoid escaping LaTeX braces.
# ---------------------------------------------------------------------------

PREAMBLE_TEMPLATE = r"""\documentclass[11pt,a4paper]{article}

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
\newunicodechar{‐}{-}
\newunicodechar{‑}{-}

% --- QIQTH extended symbol coverage (arrows/relations/logic/brackets) ---
\newunicodechar{↔}{$\leftrightarrow$}
\newunicodechar{⟷}{$\longleftrightarrow$}
\newunicodechar{⟶}{$\longrightarrow$}
\newunicodechar{⟵}{$\longleftarrow$}
\newunicodechar{←}{$\leftarrow$}
\newunicodechar{⇒}{$\Rightarrow$}
\newunicodechar{⇐}{$\Leftarrow$}
\newunicodechar{⇔}{$\Leftrightarrow$}
\newunicodechar{⇏}{$\nRightarrow$}
\newunicodechar{⇎}{$\nLeftrightarrow$}
\newunicodechar{⇌}{$\rightleftharpoons$}
\newunicodechar{↑}{$\uparrow$}
\newunicodechar{↓}{$\downarrow$}
\newunicodechar{↕}{$\updownarrow$}
\newunicodechar{↪}{$\hookrightarrow$}
\newunicodechar{≡}{$\equiv$}
\newunicodechar{≢}{$\not\equiv$}
\newunicodechar{≅}{$\cong$}
\newunicodechar{≃}{$\simeq$}
\newunicodechar{≲}{$\lesssim$}
\newunicodechar{≳}{$\gtrsim$}
\newunicodechar{≪}{$\ll$}
\newunicodechar{≫}{$\gg$}
\newunicodechar{∝}{$\propto$}
\newunicodechar{≔}{$:=$}
\newunicodechar{∀}{$\forall$}
\newunicodechar{∃}{$\exists$}
\newunicodechar{∄}{$\nexists$}
\newunicodechar{∅}{$\emptyset$}
\newunicodechar{¬}{$\neg$}
\newunicodechar{∧}{$\wedge$}
\newunicodechar{∨}{$\vee$}
\newunicodechar{⊙}{$\odot$}
\newunicodechar{⊥}{$\perp$}
\newunicodechar{∥}{$\parallel$}
\newunicodechar{‖}{$\Vert$}
\newunicodechar{∘}{$\circ$}
\newunicodechar{∙}{$\bullet$}
\newunicodechar{•}{$\bullet$}
\newunicodechar{∗}{$\ast$}
\newunicodechar{⊇}{$\supseteq$}
\newunicodechar{⊃}{$\supset$}
\newunicodechar{∖}{$\setminus$}
\newunicodechar{⟨}{$\langle$}
\newunicodechar{⟩}{$\rangle$}
\newunicodechar{†}{$\dagger$}
\newunicodechar{‡}{$\ddagger$}
\newunicodechar{′}{$'$}
\newunicodechar{″}{$''$}
\newunicodechar{⟂}{$\perp$}
\newunicodechar{⊤}{$\top$}
\newunicodechar{⊨}{$\models$}
\newunicodechar{⊢}{$\vdash$}
\newunicodechar{∎}{$\blacksquare$}
\newunicodechar{□}{$\square$}
\newunicodechar{△}{$\triangle$}
\newunicodechar{Ξ}{$\Xi$}
\newunicodechar{Υ}{$\Upsilon$}
\newunicodechar{ϕ}{$\phi$}
\newunicodechar{ϵ}{$\epsilon$}
\newunicodechar{ϑ}{$\vartheta$}
\newunicodechar{∓}{$\mp$}
\newunicodechar{°}{\textdegree}
\newunicodechar{µ}{$\mu$}
\newunicodechar{²}{\textsuperscript{2}}
\newunicodechar{³}{\textsuperscript{3}}
\newunicodechar{¹}{\textsuperscript{1}}
\newunicodechar{⁰}{\textsuperscript{0}}
\newunicodechar{₀}{\textsubscript{0}}
\newunicodechar{₁}{\textsubscript{1}}
\newunicodechar{₂}{\textsubscript{2}}
\newunicodechar{₃}{\textsubscript{3}}
\newunicodechar{ₙ}{\textsubscript{n}}

\title{__TITLE__}
\author{__AUTHOR__}
\date{__DATE__}

\begin{document}
\maketitle

\begin{abstract}
\noindent __ABSTRACT__
__KEYWORDS__
\end{abstract}

\tableofcontents
\newpage
"""

POSTAMBLE = r"""
\end{document}
"""


# ---------------------------------------------------------------------------
# YAML frontmatter parsing (minimal, regex-based — no PyYAML dependency)
# ---------------------------------------------------------------------------

def parse_frontmatter(md: str) -> tuple[dict, str]:
    if not md.startswith("---\n") and not md.startswith("---\r\n"):
        return {}, md
    # Find closing --- on its own line
    m = re.search(r"\n---\s*\n", md[4:])
    if not m:
        return {}, md
    fm_text = md[4:4 + m.start()]
    body = md[4 + m.end():]
    meta: dict[str, str] = {}
    for line in fm_text.split("\n"):
        km = re.match(r'^(\w+):\s*(.*)$', line)
        if km:
            key = km.group(1)
            val = km.group(2).strip()
            # Strip surrounding quotes
            if val.startswith('"') and val.endswith('"'):
                val = val[1:-1]
            meta[key] = val
    return meta, body


def extract_abstract(md: str) -> tuple[str, str, str]:
    """Find '## Abstract' section, then the following '**Keywords:** ...' line,
    return (abstract_body, keywords_line_text, body_with_those_removed)."""
    abs_match = re.search(
        r"^##\s+Abstract\s*\n(.*?)(?=\n##\s|\n#\s|\Z)",
        md, re.DOTALL | re.MULTILINE,
    )
    if not abs_match:
        return "", "", md
    abstract_block = abs_match.group(1).strip()
    # Drop a trailing horizontal rule that belongs to the section break, not
    # the abstract itself (otherwise '---' renders as an em-dash in LaTeX).
    abstract_block = re.sub(r"\n\s*---+\s*$", "", abstract_block).strip()
    body = md[:abs_match.start()] + md[abs_match.end():]

    # Inside abstract_block, peel off a trailing "**Keywords:** ..." line.
    kw_match = re.search(r"\n\s*\*\*Keywords:?\*\*\s*(.*)$",
                         abstract_block, re.DOTALL)
    if kw_match:
        keywords = kw_match.group(1).strip()
        abstract_block = abstract_block[:kw_match.start()].strip()
    else:
        keywords = ""

    # Strip a leading horizontal rule sitting right under the abstract.
    body = re.sub(r"^\s*\n---+\s*\n", "\n", body, count=1)

    return abstract_block, keywords, body


# ---------------------------------------------------------------------------
# Math / code / inline-code protection (verbatim pass-through)
# ---------------------------------------------------------------------------

def _protect_math(text: str) -> tuple[str, list[str]]:
    blocks: list[str] = []

    def _repl_display(m: re.Match) -> str:
        blocks.append(m.group(0))
        return f"@@MATHBLOCK{len(blocks)-1}@@"

    text = re.sub(r"\$\$.*?\$\$", _repl_display, text, flags=re.DOTALL)
    text = re.sub(
        r"(?<!\$)\$(?!\$)([^\$\n]+?)\$(?!\$)",
        lambda m: (blocks.append(m.group(0)), f"@@MATHBLOCK{len(blocks)-1}@@")[1],
        text,
    )
    return text, blocks


def _restore_math(text: str, blocks: list[str]) -> str:
    def _convert(s: str) -> str:
        if s.startswith("$$") and s.endswith("$$"):
            inner = s[2:-2].strip()
            return "\n\\[\n" + inner + "\n\\]\n"
        return s

    return re.sub(
        r"@@MATHBLOCK(\d+)@@",
        lambda m: _convert(blocks[int(m.group(1))]),
        text,
    )


def _protect_code(text: str) -> tuple[str, list[str]]:
    blocks: list[str] = []

    def _repl(m: re.Match) -> str:
        blocks.append(m.group(1))
        return f"@@CODEBLOCK{len(blocks)-1}@@"

    text = re.sub(r"```[a-zA-Z]*\n(.*?)```", _repl, text, flags=re.DOTALL)
    return text, blocks


def _restore_code(text: str, blocks: list[str]) -> str:
    def _restore(m: re.Match) -> str:
        body = blocks[int(m.group(1))].rstrip("\n")
        return "\n\\begin{qiqtcode}\n" + body + "\n\\end{qiqtcode}\n"
    return re.sub(r"@@CODEBLOCK(\d+)@@", _restore, text)


def _protect_inline_code(text: str) -> tuple[str, list[str]]:
    blocks: list[str] = []

    def _repl(m: re.Match) -> str:
        blocks.append(m.group(1))
        return f"@@INLINECODE{len(blocks)-1}@@"
    text = re.sub(r"`([^`\n]+)`", _repl, text)
    return text, blocks


def _restore_inline_code(text: str, blocks: list[str]) -> str:
    def _restore(m: re.Match) -> str:
        body = blocks[int(m.group(1))]
        body = body.replace("\\", r"\textbackslash{}")
        body = (body.replace("&", r"\&").replace("%", r"\%")
                .replace("$", r"\$").replace("#", r"\#")
                .replace("_", r"\_").replace("{", r"\{").replace("}", r"\}")
                .replace("~", r"\textasciitilde{}").replace("^", r"\textasciicircum{}"))
        return r"\texttt{" + body + r"}"
    return re.sub(r"@@INLINECODE(\d+)@@", _restore, text)


# ---------------------------------------------------------------------------
# Prose escaping (placeholders are safe; only @, digits, uppercase letters)
# ---------------------------------------------------------------------------

def _escape_prose(text: str) -> str:
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
# Structural converters
# ---------------------------------------------------------------------------

def _detect_heading_offset(text: str) -> int:
    """If the only H1 in the doc is the title (i.e. the body uses ## for top
    sections, paper convention), return -1 so ## maps to \\section. Otherwise
    return 0 (tutorial convention: # for sections)."""
    h1_count = sum(1 for ln in text.split("\n") if re.match(r"^#\s+", ln))
    return -1 if h1_count <= 1 else 0


def _convert_headings(text: str, skip_h1_title: str | None) -> tuple[str, list[str]]:
    blocks: list[str] = []
    lines = text.split("\n")
    out: list[str] = []
    skipped_first_h1 = False
    offset = _detect_heading_offset(text)
    for ln in lines:
        m = re.match(r"^(#{1,6})\s+(.*)$", ln)
        if m:
            raw_level = len(m.group(1))
            title = m.group(2).strip().rstrip("#").strip()
            # Skip the document's H1 title (we render it via \maketitle)
            if raw_level == 1 and not skipped_first_h1:
                skipped_first_h1 = True
                continue
            if raw_level == 1 and skip_h1_title and title == skip_h1_title:
                continue
            # Strip leading numbering: "N", "NA", "N.N", "N.Na", "NA.Nb", etc.
            # — LaTeX provides its own numbering.
            title = re.sub(r"^\d+[A-Za-z]?(?:\.\d+[a-z]?)*\.?\s+", "", title)
            level = max(1, raw_level + offset)
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
    return re.sub(r"@@HEADING(\d+)@@", lambda m: blocks[int(m.group(1))], text)


def _convert_emphasis(text: str) -> str:
    text = re.sub(r"\*\*([^*\n]+?)\*\*",
                  lambda m: r"\textbf{" + m.group(1) + r"}", text)
    text = re.sub(r"(?<![*\w])\*([^*\n]+?)\*(?![*\w])",
                  lambda m: r"\emph{" + m.group(1) + r"}", text)
    return text


def _convert_links(text: str) -> str:
    def _repl(m: re.Match) -> str:
        return r"\href{" + m.group(2) + "}{" + m.group(1) + "}"
    return re.sub(r"\[([^\]]+)\]\(([^)]+)\)", _repl, text)


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


_BULLET_RE = re.compile(r"^(\s*)[-*+]\s+(.*)$")
_NUMBER_RE = re.compile(r"^(\s*)\d+\.\s+(.*)$")


def _convert_lists(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    i = 0
    n = len(lines)

    def _is_b(ln: str) -> bool: return bool(_BULLET_RE.match(ln))
    def _is_n(ln: str) -> bool: return bool(_NUMBER_RE.match(ln))

    while i < n:
        line = lines[i]
        if _is_b(line):
            out.append(r"\begin{itemize}")
            while i < n and (_is_b(lines[i]) or
                             (lines[i].strip() == "" and i + 1 < n and _is_b(lines[i + 1]))):
                if lines[i].strip() == "":
                    i += 1
                    continue
                m = _BULLET_RE.match(lines[i])
                out.append(r"  \item " + m.group(2))
                i += 1
            out.append(r"\end{itemize}")
        elif _is_n(line):
            out.append(r"\begin{enumerate}")
            while i < n and (_is_n(lines[i]) or
                             (lines[i].strip() == "" and i + 1 < n and _is_n(lines[i + 1]))):
                if lines[i].strip() == "":
                    i += 1
                    continue
                m = _NUMBER_RE.match(lines[i])
                out.append(r"  \item " + m.group(2))
                i += 1
            out.append(r"\end{enumerate}")
        else:
            out.append(line)
            i += 1

    return "\n".join(out)


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
        if (line.startswith("|") and i + 1 < n and
                re.match(r"^\|?[\s:|-]+\|?$", lines[i + 1].strip()) and
                "|" in lines[i + 1]):
            header = _split_table_row(lines[i])
            ncols = len(header)
            i += 2
            body: list[list[str]] = []
            while i < n and lines[i].strip().startswith("|"):
                row = _split_table_row(lines[i])
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


def _convert_hr(text: str) -> str:
    out: list[str] = []
    for ln in text.split("\n"):
        if re.match(r"^---+\s*$", ln.strip()):
            out.append(r"\medskip\hrule\medskip")
        else:
            out.append(ln)
    return "\n".join(out)


def _strip_italic_intro(text: str) -> str:
    """Strip a leading standalone *...* italic block (used by TUTORIAL.md)."""
    pattern = re.compile(r"\A\*([^*\n]+(?:\n[^*\n]+)*)\*", re.MULTILINE)
    return pattern.sub("", text, count=1)


def _normalize_blank_lines(text: str) -> str:
    return re.sub(r"\n{3,}", "\n\n", text)


# ---------------------------------------------------------------------------
# Convert one document body (after frontmatter / abstract extraction)
# ---------------------------------------------------------------------------

def convert_body(md: str, h1_title: str | None) -> str:
    md = _strip_italic_intro(md)

    md, code_blocks = _protect_code(md)
    md, math_blocks = _protect_math(md)
    md, inline_code_blocks = _protect_inline_code(md)
    md, heading_blocks = _convert_headings(md, skip_h1_title=h1_title)

    md = _escape_prose(md)

    md = _convert_tables(md)
    md = _convert_hr(md)
    md = _convert_blockquotes(md)
    md = _convert_lists(md)

    md = _convert_links(md)
    md = _convert_emphasis(md)

    md = _restore_headings(md, heading_blocks)
    md = _restore_inline_code(md, inline_code_blocks)
    md = _restore_math(md, math_blocks)
    md = _restore_code(md, code_blocks)

    md = _normalize_blank_lines(md)
    return md


# ---------------------------------------------------------------------------
# Convert an inline-text fragment (abstract, keywords) — same pipeline minus
# structural converters that don't apply.
# ---------------------------------------------------------------------------

def convert_inline_fragment(md: str) -> str:
    md, code_blocks = _protect_code(md)
    md, math_blocks = _protect_math(md)
    md, inline_code_blocks = _protect_inline_code(md)
    md = _escape_prose(md)
    md = _convert_links(md)
    md = _convert_emphasis(md)
    md = _restore_inline_code(md, inline_code_blocks)
    md = _restore_math(md, math_blocks)
    md = _restore_code(md, code_blocks)
    return md


# ---------------------------------------------------------------------------
# Build one document
# ---------------------------------------------------------------------------

def build_one(src: Path) -> bool:
    print(f"\n=== {src.name} ===")
    md = src.read_text(encoding="utf-8").replace("﻿", "")
    print(f"  read {len(md)} chars, {md.count(chr(10)) + 1} lines")

    meta, body = parse_frontmatter(md)
    abstract_md, keywords_md, body = extract_abstract(body)

    defaults = DEFAULTS.get(src.name, {})
    title = meta.get("title") or defaults.get("title", src.stem)
    author = meta.get("author") or defaults.get("author", "")
    date = meta.get("date") or defaults.get("date", "")
    if not abstract_md:
        abstract_md = defaults.get("abstract", "")
    if not keywords_md:
        keywords_md = defaults.get("keywords", "")

    # Find the H1 title in the body so _convert_headings can skip it too
    h1_match = re.search(r"^#\s+(.*)$", body, re.MULTILINE)
    h1_title = h1_match.group(1).strip() if h1_match else None

    body_tex = convert_body(body, h1_title=h1_title)
    abstract_tex = convert_inline_fragment(abstract_md) if abstract_md else ""
    keywords_tex = ""
    if keywords_md:
        kw = convert_inline_fragment(keywords_md)
        keywords_tex = "\n\n\\medskip\n\\noindent\\textbf{Keywords:} " + kw

    preamble = (PREAMBLE_TEMPLATE
                .replace("__TITLE__", title)
                .replace("__AUTHOR__", author)
                .replace("__DATE__", date)
                .replace("__ABSTRACT__", abstract_tex)
                .replace("__KEYWORDS__", keywords_tex))

    tex = preamble + body_tex + POSTAMBLE

    OUT_DIR.mkdir(exist_ok=True)
    out_tex = OUT_DIR / (src.stem + ".tex")
    out_pdf = OUT_DIR / (src.stem + ".pdf")
    out_tex.write_text(tex, encoding="utf-8")
    print(f"  wrote {out_tex.relative_to(REPO)} ({len(tex)} chars)")

    for pass_num in (1, 2):
        result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
             "-output-directory", str(OUT_DIR), str(out_tex)],
            capture_output=True, text=True, cwd=str(OUT_DIR),
        )
        if result.returncode != 0:
            print(f"  pdflatex pass {pass_num} FAILED (exit {result.returncode})")
            tail = "\n".join(result.stdout.split("\n")[-60:])
            print(tail)
            return False
        print(f"  pdflatex pass {pass_num} OK")

    if out_pdf.exists():
        sz = out_pdf.stat().st_size
        print(f"  SUCCESS: {out_pdf.relative_to(REPO)} ({sz/1024:.1f} KB)")
        return True
    print(f"  ERROR: {out_pdf.relative_to(REPO)} not produced")
    return False


def main() -> int:
    if len(sys.argv) > 1:
        targets = [REPO / a for a in sys.argv[1:]]
    else:
        targets = DOCS

    results: list[tuple[Path, bool]] = []
    for src in targets:
        if not src.exists():
            print(f"ERROR: {src} not found, skipping")
            results.append((src, False))
            continue
        ok = build_one(src)
        results.append((src, ok))

    print("\n=== Summary ===")
    for src, ok in results:
        mark = "OK " if ok else "FAIL"
        print(f"  [{mark}] {src.name}")

    return 0 if all(ok for _, ok in results) else 1


if __name__ == "__main__":
    sys.exit(main())
