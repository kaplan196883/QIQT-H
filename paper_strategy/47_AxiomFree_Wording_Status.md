# "Axiom-free" wording — status + canonical phrasing

GPT-5.5-pro (2026-06-12) flagged: do not call the Lean work "axiom-free" **unqualified** in external/
paper-facing text, because `propext`, `Classical.choice`, `Quot.sound` ARE the standard foundational axioms
of classical Lean/Mathlib. A referee in formal methods will object to a bare "axiom-free" claim.

## Status — already handled where it matters

- **Foundations paper (`build/QIQT_Foundations_Paper.tex`):** ALREADY safe. The first occurrence (line ~1614)
  defines the term inline: *"…is now **axiom-free** (every theorem … depends only on Lean's standard axioms
  `propext`, `Classical.choice`, `Quot.sound`, verified by `AxiomAudit.lean`)."* The later uses (≈1868, 1871,
  1877) sit in the same section and are covered by that definition. **No edit required.**
- **New artifacts (this session):** `44_Formalization_Scope_Note.md`, `45_Theorem_Paper_Index.md`,
  `46_Formalization_Paper_Outline.md` all use the qualified phrasing. **OK.**

## Action only if these become arXiv-facing

The ancillary notes use bare "axiom-free" and should get a one-line qualification **if published as-is**:
`ARXIV_NOTE_WeylBit.md` (lines ~76, 235, 296, 501, 509), `AXIOM_CONTRACTS.md`, `CORE_THEOREM_REFS.md`,
`FINITE_BORN_REPRESENTATION.md`. (Internal corpus docs / commit messages: leave as-is — there "axiom-free"
unambiguously means "no project/interface axioms," and the audit discipline is corpus-internal.)

## Canonical replacement phrasing (use anywhere external)

Prose:
> "machine-checked in Lean 4/Mathlib with no `sorry` and no axioms beyond the standard classical foundations
> (`propext`, `Classical.choice`, `Quot.sound`)."

Ready-to-paste LaTeX footnote (attach to the first external use of "axiom-free" in any new document):
```latex
\footnote{Throughout, ``axiom-free'' is shorthand for: the development carries no \texttt{sorry} and, as
reported by Lean's \texttt{\#print axioms}, every cited theorem depends only on the standard classical
foundations of Lean/Mathlib (\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound})---i.e.\ it
introduces no project-specific or interface axioms beyond those.}
```

## Conclusion

The wording concern is **already satisfied** in the foundations paper and in all new packaging artifacts.
No blocking edit is required for submission; the canonical phrasing above is the reference for any future
external text.
