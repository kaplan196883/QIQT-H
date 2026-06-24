# arXiv Submission Metadata (MANUSCRIPT.md)

**Title.** Trustworthy AI for Foundational Science: An Audited Human-AI Loop that
Machine-Checks a Conditional Derivation of the Einstein Field Equations from a Finite-Information Bound

**Author.** Paweł Kapłański

**Primary category.** cs.AI  ·  **Cross-list.** quant-ph, math.LO

**ACM/MSC (optional).** I.2.3 (Deduction and Theorem Proving); 68V15 (Theorem proving);
03B35 (Mechanization of proofs).

**Comments field (suggested).** "24 pages, 1 figure, 5 tables. Reproducible artifact:
Lean 4 / Mathlib development, axiom audit, track-state tool, and link-checked blueprint at https://github.com/kaplan196883/QIQT-H, commit 83dc08e (toolchain leanprover/lean4:v4.30.0).
AI assistance (the subject of the paper) disclosed in §3."

**Note.** The paper's LaTeX abstract is ~2,300 chars (no LaTeX limit). The arXiv *web-form metadata*
abstract is capped at 1920 chars, so use the condensed version below for that field (it preserves
the honesty qualifiers; the full abstract stays in the PDF).

**Abstract (de-wrapped; condensed to within arXiv's 1920-char metadata limit).**
AI now produces scientific reasoning faster than it can be vetted, and most of it is not machine-checked: a proof that compiles can still rest on a vacuous or over-strong axiom. We present an audited human-AI formalization loop and apply it to a demanding target. A coding agent (Claude Code) formalizes a researcher's own framework in Lean 4 / Mathlib, self-correcting against the compiler; an independent model (GPT-5.5-Pro) adversarially reviews the design; a human directs scope; and a soundness audit records each result's axioms, holds the project-axiom budget at zero, and, via a hypothesis ledger and a goal-directed track-state report, extends the audit from declared axioms to local hypotheses. Running the loop, we obtained a machine-checked, project-axiom-free Lean theorem (only Lean's standard axioms; no project-specific axiom) deriving, conditionally, the Einstein field equations aT=G+Lg from a finite-information (Bekenstein-type) capacity bound by a Jacobson-style equation of state: the thermodynamic first law is itself derived from the framework, while Bisognano-Wichmann modular flux and Raychaudhuri focusing enter as explicitly labelled hypotheses. We are explicit about scope: the audit certifies no project axiom and labelled premises, and a machine-checked witness shows the premise set jointly satisfiable (non-vacuous) - but not that the cited inputs or the capacity postulate are true. The same development carries a no-collapse measurement core (axiom count 57 to 0; 192 modules, no sorry). The contribution is an auditable, goal-directed architecture for AI-assisted formalization, reported as a single-team case study and conjectured to transfer; we make the negative claim deliberately - this is not "AI proved general relativity."

**Endorsement.** Submit under cs.AI (author endorsed); cross-lists do not require separate
endorsement once the primary is accepted. See `../PUBLICATION_STRATEGY.md` §1, §7.

**AI-assistance disclosure (required).** State plainly (already in §3 + Acknowledgements): Claude
Code as formalizer, GPT-5.5-Pro as independent reviewer, under author direction; this is the
paper's subject, not incidental tooling.

**Pre-submission LOW fixes (from Final_Evaluation_Report.md).** verify abstract char count;
fill arXiv IDs/authors for refs [3], [14]; replace the ASCII Fig. 1 with a TikZ vector; optional
expansion of §2/§5 toward the outline length.

**Permanence.** Mirror the exact commit on Zenodo for a DOI (no endorsement needed), per
`PUBLICATION_STRATEGY.md` §1.
