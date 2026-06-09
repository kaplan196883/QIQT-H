# QIQT-H Blueprint

A human-readable, mathematician-facing rendering of the machine-checked QIQT-H
formalization, built with [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint)
(LaTeX statements + a verified dependency graph linking each statement to its Lean
declaration) and, separately, [`doc-gen4`](https://github.com/leanprover/doc-gen4)
(browsable API reference).

This gives the "both" deliverable:

* **arXiv-bound LaTeX** — `blueprint/src/content.tex` holds the math statements; they
  compile to a PDF and convert cleanly into paper sections.
* **Browsable web artifact** — a website with a clickable dependency DAG showing the
  layered A / B / C / Phase-B structure, plus per-statement links to the Lean source.

## What's here

```
blueprint/
  src/
    content.tex        <- THE math (statements, proofs-as-sketches, \uses edges)
    web.tex            <- plasTeX master for the web build
    print.tex          <- xelatex master for the pdf build
    plastex.cfg        <- web build config (renderer, dep-graph plugin, ...)
    latexmkrc          <- pdf build config (uses xelatex)
    extra_styles.css   <- web CSS tweaks
    macros/            <- common.tex (shared), print.tex, web.tex
  lean_decls           <- AUTO-GENERATED list of \lean{...} names (by the web build)
  web/                 <- AUTO-GENERATED website (gitignored)
  print/               <- AUTO-GENERATED pdf (gitignored)
```

Only `src/` (and this README) is version-controlled; `web/`, `print/`, and the
build droppings are gitignored. `lean_decls` is regenerated on every web build.

## Building

Because this Lean project lives in a subdirectory (`lean/mathlib`) of the QIQT-H
git repo, the `leanblueprint` CLI (which expects the lakefile at the git root) does
not drive it directly. Use the wrapper script instead:

```bash
# from lean/mathlib
bash scripts/build_blueprint.sh all     # web + pdf + declaration check
bash scripts/build_blueprint.sh web     # just the website
bash scripts/build_blueprint.sh pdf     # just the pdf
bash scripts/build_blueprint.sh check   # just verify \lean{...} names exist
```

Outputs:
* Website: `blueprint/web/index.html` (graph at `blueprint/web/dep_graph_document.html`)
* PDF: `blueprint/print/print.pdf`

The script sets the PATH for the three toolchains (Graphviz, the plasTeX conda env,
MiKTeX); edit the paths at the top of the script if your install locations differ.

## The integrity guarantee

`build_blueprint.sh check` runs `lake exe checkdecls blueprint/lean_decls`, which
fails if any `\lean{Foo}` in the blueprint names a declaration that does not exist
in the compiled Lean. This is what keeps the readable document honest: a green
("Lean") tag cannot drift from the actual proof. Run it in CI before publishing.

## API reference (doc-gen4)

The lakefile has a dev-only `doc-gen4` requirement so ordinary `lake build` stays
light. To generate the browsable API docs:

```bash
# from lean/mathlib   (first time only: fetch the dependency)
lake -R -Kenv=dev update doc-gen4
lake -R -Kenv=dev build QIQTH:docs
```

This builds documentation for the QIQTH library (and its Mathlib dependencies — a
large, multi-GB, long-running build). Output lands under `.lake/build/doc/`. Point
the blueprint's `\dochome` (in `web.tex`) at where you host these docs so the
dependency-graph nodes link through to the API.

## Adding more theorems

The current `content.tex` is a representative cross-section (one flagship result per
layer). To add a result:

1. Write a `\begin{theorem}...\end{theorem}` (or `definition`/`lemma`) in
   `content.tex` with a `\label{...}`.
2. Add `\lean{Fully.Qualified.Name}` (and `\leanok` if the statement is formalized;
   `\leanok` inside the proof if the proof is, too).
3. Add `\uses{label1, label2}` to wire dependency-graph edges to results it relies on.
4. Rebuild and run the declaration check.
