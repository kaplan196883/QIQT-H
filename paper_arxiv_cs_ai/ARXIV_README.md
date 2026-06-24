# arXiv submission package

Self-contained LaTeX source for the methodology paper. Compiles to a 22-page PDF with no
external dependencies beyond a standard TeXLive (the same one arXiv runs).

## Source of truth and pipeline
`main.tex` is **generated**, not hand-edited. The single source is the Markdown manuscript
`../paper_cs_ai/MANUSCRIPT.md` (+ YAML frontmatter); a dedicated converter emits this `main.tex`:
```
python paper_cs_ai/build.py            # MANUSCRIPT.md -> paper_arxiv_cs_ai/main.tex, then compiles
python paper_cs_ai/build.py --no-pdf   # convert only
```
Edit the Markdown, re-run the script, commit both. The converter handles the figure (a `{=latex}`
raw block), captioned `booktabs`/`tabularx` tables, numbered `\cite`/`thebibliography`, and the
framed claim box; its conventions are documented at the top of `build.py`. Single-sourcing keeps the
cross-references consistent (they previously drifted when `main.tex` and the manuscript were edited
in parallel).

## Files
- `main.tex` — the complete generated paper (article class; inline `thebibliography`; TikZ figure;
  three `booktabs` tables). This is the only file you upload.
- `arxiv-submission.tar.gz` — `main.tex` packaged for upload.
- `main.pdf` — local compile result (do **not** upload the PDF; arXiv compiles from source).

## Verified
Result: exit 0, 22 pages, 0 LaTeX warnings, 0 undefined citations/references, 0 bad overfull
boxes. Packages used (all standard on arXiv): inputenc, fontenc, lmodern, geometry, microtype,
amsmath, amssymb, booktabs, array, tabularx, tikz (+arrows.meta, positioning), newunicodechar,
hyperref.

## Uploading to arXiv
1. **Source, not PDF.** Upload `arxiv-submission.tar.gz` (or `main.tex` directly). arXiv runs
   AutoTeX (pdflatex/latexmk) on the source. No `.bbl` is required because the bibliography is
   an inline `thebibliography` environment, and there is no `.bib`.
2. **Categories.** Primary `cs.AI`; cross-list `quant-ph` and `math.LO`. (The author is endorsed
   for `cs.AI`; cross-lists need no separate endorsement once the primary is accepted. See
   `../PUBLICATION_STRATEGY.md`.)
3. **Title / authors / abstract.** Title and authors from `main.tex`. The PDF abstract is ~2,300
   chars (no LaTeX limit); the arXiv web-form metadata abstract is capped at 1920, so paste the
   **condensed** metadata abstract from `../paper_cs_ai/SUBMISSION_METADATA.md` (1,724 chars) into
   that field rather than the full PDF abstract.
4. **Comments field.** Suggested: `22 pages, 1 figure, 3 tables. Reproducible artifact (Lean 4 /
   Mathlib development, axiom audit, verified blueprint) at https://github.com/kaplan196883/QIQT-H.`
5. **License.** Choose one (arXiv's default non-exclusive licence, or CC BY 4.0).
6. **AI-assistance disclosure.** Already in the Acknowledgements and Section 3 (Claude Code as
   formalizer, GPT-5.5-Pro as reviewer, under the author's direction). This is required by arXiv
   and is the subject of the paper.

## Remaining pre-submission items (optional, non-blocking)
- All 49 references were verified to exist via web search; arXiv IDs and venues are filled in. References [42] (companion foundations paper) and [43] (project repository) are the author's own work.
- Consider mirroring the exact commit on Zenodo for a DOI (no endorsement needed).
- Paper size is A4 (`\usepackage[a4paper,margin=1in]{geometry}`).
