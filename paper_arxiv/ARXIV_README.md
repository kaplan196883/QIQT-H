# arXiv submission package

Self-contained LaTeX source for the methodology paper. Compiles to a 16-page PDF with no
external dependencies beyond a standard TeXLive (the same one arXiv runs).

## Files
- `main.tex` — the complete paper (article class; inline `thebibliography`; TikZ figure; two
  `booktabs` tables). Pure ASCII. This is the only file you upload.
- `arxiv-submission.tar.gz` — `main.tex` packaged for upload.
- `main.pdf` — local compile result (do **not** upload the PDF; arXiv compiles from source).

## How it was built / verified
```
cd paper_arxiv
latexmk -pdf main.tex      # runs pdflatex enough times to resolve \ref and \cite
```
Result: exit 0, 16 pages, 0 LaTeX warnings, 0 undefined citations/references, 0 bad overfull
boxes. Packages used (all standard on arXiv): inputenc, fontenc, lmodern, geometry, microtype,
amsmath, amssymb, booktabs, array, tikz (+arrows.meta, positioning), hyperref.

## Uploading to arXiv
1. **Source, not PDF.** Upload `arxiv-submission.tar.gz` (or `main.tex` directly). arXiv runs
   AutoTeX (pdflatex/latexmk) on the source. No `.bbl` is required because the bibliography is
   an inline `thebibliography` environment, and there is no `.bib`.
2. **Categories.** Primary `cs.AI`; cross-list `quant-ph` and `math.LO`. (The author is endorsed
   for `cs.AI`; cross-lists need no separate endorsement once the primary is accepted. See
   `../PUBLICATION_STRATEGY.md`.)
3. **Title / authors / abstract.** Taken from `main.tex`. The abstract is 1920 characters,
   exactly arXiv's metadata limit; if the web form rejects it, delete the clause
   `, with no \texttt{sorry},` to gain margin (also drop it from the metadata abstract).
4. **Comments field.** Suggested: `16 pages, 1 figure, 2 tables. Reproducible artifact (Lean 4 /
   Mathlib development, axiom audit, verified blueprint) at https://github.com/kaplan196883/QIQT-H, commit 4720763.`
5. **License.** Choose one (arXiv's default non-exclusive licence, or CC BY 4.0).
6. **AI-assistance disclosure.** Already in the Acknowledgements and Section 3 (Claude Code as
   formalizer, GPT-5.5-Pro as reviewer, under the author's direction). This is required by arXiv
   and is the subject of the paper.

## Remaining pre-submission items (optional, non-blocking)
- All 45 references were verified to exist via web search (2026-06-12); arXiv IDs and venues are filled in. References [42] (companion foundations paper) and [43] (project repository) are the author's own work.
- Consider mirroring the exact commit on Zenodo for a DOI (no endorsement needed).
- Paper size is A4 (`\usepackage[a4paper,margin=1in]{geometry}`).
