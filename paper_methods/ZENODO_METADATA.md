# Zenodo deposit metadata — methods paper

Use these fields when creating the Zenodo deposit at <https://zenodo.org/uploads/new>.
Upload `paper_methods_out/main.pdf` as the file. Zenodo mints a versioned DOI and a
concept (all-versions) DOI; cite the concept DOI on qiqt.org.

---

**Upload type:** Publication → Preprint

**Title:**
An Audited Human-AI Loop for Trustworthy Lean Formalization: Axiom-Budget Auditing, a Goal-Directed State Report, and a Conditional General-Relativity Case Study

**Authors / Creators:**
- Kapłański, Paweł — Cognitum (affiliation) — ORCID: <add if available>

**Description (HTML/plain):**

AI can now write mathematics and code faster than humans can vet it, and in a proof assistant a
proof that merely compiles is not enough: the load-bearing content can hide in a declared axiom, and
"it builds, with no sorry" cannot distinguish a sound development from one resting on a false,
vacuous, or over-strong assumption. This paper presents a human-directed, two-model formalization
loop built around that gap. A coding agent (Claude Code) writes Lean 4 / Mathlib and self-corrects
against the compiler; an independent model (GPT-5.5-Pro) adversarially reviews the design rather than
the syntax; and a human controls scope and premises. The soundness contribution is the audit that
wraps the loop: a continuously-enforced axiom budget that classifies every result as
proved/conditional/cited and can only ratchet down; a vacuity lint and a hypothesis ledger /
redundancy probe that extend the audit from declared axioms to a theorem's local hypotheses; a
goal-directed track-state report that turns the audit into the loop's steering signal; and a
link-checked blueprint from prose to kernel-checked declarations. A small controlled instrument
ablation shows that the structural instruments catch structural faults while only the independent
reviewer diagnoses the semantic ones (a false-but-well-typed axiom, a circular hypothesis). As a
demanding case study, the loop is driven to a machine-checked, project-axiom-free Lean theorem that
derives, conditionally, the Einstein field equations from a finite-information capacity bound by a
Jacobson-style equation of state, with the cited physics inputs carried as explicit, labelled
hypotheses and a machine-checked witness that the premise set is jointly satisfiable. The case study
stresses the workflow, not physics: verification certifies the conditional mathematics and the
absence of any hidden axiom; it does not establish the cited inputs or the framework's physical
postulates, which remain open.

**Keywords:**
interactive theorem proving; Lean; Mathlib; autoformalization; LLM-assisted formalization; soundness
auditing; axiom budget; vacuity checking; LLM-as-judge; human-AI collaboration; verification;
reproducible blueprints; machine-checked general relativity

**License:** Creative Commons Attribution 4.0 International (CC-BY-4.0)

**Language:** English

**Related identifiers:**
- `isSupplementedBy` — URL: https://github.com/kaplan196883/QIQT-H (the Lean development)
- `isDocumentedBy` — URL: https://qiqt.org (project site)
- `isPartOf` — (concept DOI of the QIQT-H foundations paper deposit, once minted)

**Notes:**
Preprint. The Lean 4 / Mathlib development reported on is public and every theorem is audited with
`#print axioms`; the development carries no `sorry`. AI assistance (Claude Code as formalizer,
GPT-5.5-Pro as independent reviewer) is the subject of the paper and is described in full in §3.
