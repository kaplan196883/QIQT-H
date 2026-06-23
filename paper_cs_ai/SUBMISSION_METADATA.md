# arXiv Submission Metadata (MANUSCRIPT.md)

**Title.** Trustworthy AI for Foundational Science: An Audited Human-AI Loop that
Machine-Checks the Einstein Field Equations from a Finite-Information Bound

**Author.** Paweł Kapłański

**Primary category.** cs.AI  ·  **Cross-list.** quant-ph, math.LO

**ACM/MSC (optional).** I.2.3 (Deduction and Theorem Proving); 68V15 (Theorem proving);
03B35 (Mechanization of proofs).

**Comments field (suggested).** "N pages, 1 figure, 2 tables. Reproducible artifact:
Lean 4 / Mathlib development, axiom audit, and verified blueprint at https://github.com/kaplan196883/QIQT-H, commit 5727bcd.
AI assistance (the subject of the paper) disclosed in §3."

**Abstract (de-wrapped; ~1900 chars, within arXiv's 1920 limit; matches main.tex).**
Artificial intelligence now proposes hypotheses and even solves open problems, yet most of what it produces is not machine-checked, so plausible but wrong results threaten to outpace our capacity to vet them. Proof assistants give machine-checkable truth, but a green build is not enough: a proof that compiles can still rest on a vacuous or over-strong axiom. We present a methodology that closes this gap and apply it to a deep result. A coding agent (Claude Code) is repurposed to formalize a researcher's own framework in Lean 4 / Mathlib, self-correcting against the compiler; an independent model (GPT-5.5-Pro) adversarially reviews the design; a human directs scope; and a soundness audit records which named axioms each result depends on, holding the budget at zero. Running this loop, we obtained a machine-checked, axiom-free Lean derivation of the Einstein field equations $aT_{\mu\nu}=G_{\mu\nu}+\Lambda g_{\mu\nu}$ from a finite-information (Bekenstein-type) capacity bound: a Jacobson-style equation of state in which the thermodynamic input is itself derived from the framework, with only the Bisognano-Wichmann wedge-modular flux and Raychaudhuri focusing cited as explicit hypotheses, and all the differential geometry (Bianchi, $\nabla^\mu G_{\mu\nu}=0$, the null-cone-to-tensor step, constant $\Lambda$) machine-checked. The same development carries an axiom-free no-collapse measurement core; in total 192 modules, roughly 2,010 theorems, 0 project-specific axioms, no sorry. We are explicit about scope: verification certifies that the derivation is correct and rests on no hidden axiom, with its physics inputs labelled as explicit hypotheses; it does not by itself establish those cited inputs or the framework's physical postulates. The contribution is a transferable, auditable architecture for AI-assisted formalization, demonstrated on a hard physics target.

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
