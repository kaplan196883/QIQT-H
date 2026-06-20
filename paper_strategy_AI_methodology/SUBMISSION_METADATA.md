# arXiv Submission Metadata (MANUSCRIPT.md)

**Title.** Trustworthy AI for Foundational Science: A Closed, Audited Human-AI Loop for
Machine-Checked Theory Formalization

**Author.** Paweł Kapłański

**Primary category.** cs.AI  ·  **Cross-list.** quant-ph, math.LO

**ACM/MSC (optional).** I.2.3 (Deduction and Theorem Proving); 68V15 (Theorem proving);
03B35 (Mechanization of proofs).

**Comments field (suggested).** "N pages, 1 figure, 2 tables. Reproducible artifact:
Lean 4 / Mathlib development, axiom audit, and verified blueprint at https://github.com/kaplan196883/QIQT-H, commit 5727bcd.
AI assistance (the subject of the paper) disclosed in §3."

**Abstract (de-wrapped; 1920 chars, at arXiv's 1920 limit — if the uploader rejects, drop the
clause "with no sorry," to gain margin; matches MANUSCRIPT.md).**
Artificial intelligence now proposes hypotheses and even solves open problems, yet most of what it produces is not machine-checked, so plausible but wrong results threaten to outpace our capacity to vet them. Proof assistants offer machine-checkable truth, and agentic systems can now autoformalize and prove mathematics in Lean. A green build is not enough, however: a proof that compiles can still rest on a vacuous or over-strong axiom. We present a methodology that closes this gap. A coding agent (Claude Code) is repurposed to formalize a researcher's own new foundational physics framework in Lean 4 / Mathlib, self-correcting against the compiler; a second, independent model (GPT-5.5-Pro) adversarially reviews the conceptual design; a human directs scope and adjudicates; and a soundness audit records which named axioms each result depends on, ratcheting a tracked budget down and publishing an honest proved/conditional/cited boundary. A verified blueprint links every human-readable statement to its kernel-checked proof. Applied to a collapse-free, finite-information account of quantum measurement, the loop drove the deductive core from fifty-seven project-specific axioms to zero, with no sorry, across 192 modules and roughly 2,010 theorems. We report two episodes in which the independent reviewer caught a false axiom and an inconsistent one that the axiom counter could not see, motivating a third soundness instrument. We are explicit about scope: verification certifies that the framework's conditional mathematics is correct and free of hidden axioms, not its physical postulates, which remain open. The contribution is a transferable architecture for trustworthy AI-assisted formalization, not a new physical result.

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
