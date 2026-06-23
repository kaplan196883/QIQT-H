# Optimized Detailed Outline ⭐ (review-ready)

**Title (working):** *Trustworthy AI for Foundational Science: A Closed, Audited Human–AI
Loop for Machine-Checked Theory Formalization*

**Alt titles:**
- *Auditable Formalization: Machine-Checked, Axiom-Audited AI Formalization of a New Physics Theory*
- *Compiles Is Not Enough: Soundness Auditing for AI-Assisted Formal Science*

**Venue:** arXiv **cs.AI** (primary) · cross-list **quant-ph**, **math.LO** · ~9,000 words · **45–55 refs**
**Predicted reviewer score:** 31/35 (post-optimization A–E applied)
**Companion:** hand this to **academic-paper-composer** to write the full paper.

**One-sentence thesis (Issue D):** *For AI to contribute trustworthily to foundational
science, "the proof compiles" must be replaced by "here is exactly which named axioms the
result depends on" — and we show a human-directed, two-model loop that delivers this, by
formalizing a new collapse-free quantum-measurement theory end-to-end with a continuously
audited, ratcheting axiom budget.*

---

## Abstract (~230 words)
Cover, in order: (1) the verification crisis — AI now generates scientific hypotheses and
even solves open problems, but mostly without machine-checking, so plausible-but-wrong
results threaten to flood science [cite Need-for-Verification]; (2) the missing filter —
machine-checking plus *soundness auditing* (which axioms a result truly rests on); (3) the
method — a closed human-directed loop: a coding agent that formalizes and self-corrects
against the Lean compiler, an *independent* adversarial AI reviewer that attacks the
conceptual design, a human who directs scope and adjudicates, an *axiom budget* that records
and ratchets down every named dependency, and a *verified blueprint* that makes the result
legible to domain experts; (4) the demonstration — end-to-end formalization of a researcher's
own new collapse-free quantum-measurement theory in Lean 4 / Mathlib; (5) the honest result —
a green build, an explicit proved/conditional/cited boundary, and documented cases where the
reviewer caught soundness problems the formalizer missed. Lead the abstract with trust/
verification, not the physics.

---

## 1. Introduction (~1,400 words)

### 1.1 The verification crisis in AI-for-science (~450)
- AI scientists and discovery agents now produce hypotheses, papers, even solutions to open
  problems [The AI Scientist-v2 2504.08066; AI Co-Scientist; Brenner et al. 2603.04735].
- But most outputs are *not machine-checked*; LLMs hallucinate plausible-but-wrong reasoning
  [Self-Consistency Hallucination 2504.09440]. Verification is the field's central risk
  [Need-for-Verification 2509.01398].
- Formal methods (Lean/Mathlib) offer machine-checkable truth [Formal Math Reasoning: A New
  Frontier 2412.16075] — but a green build is not enough (next).

### 1.2 Machine-checking + auditing as the missing filter (~400)
- The deeper risk: a proof that *compiles* but rests on a vacuous or over-strong **axiom**.
  "Compiles" ≠ "sound theory." → need an explicit audit of the axiom base.
- **[BOXED claim/non-claim — Issue D]** *We claim:* a transferable loop + audit that makes
  the proved/conditional/cited boundary explicit and shrinking. *We do not claim:* that AI
  discovered new physics, nor that the case-study theory is empirically established.
- State the **one-sentence thesis** here.

### 1.3 Contributions (bulleted — Issue E) (~350)
- A **closed, audited human–AI formalization loop** (formalizer + compiler self-correction +
  independent adversarial reviewer + human direction).
- An **axiom-budget discipline**: a first-class soundness instrument (proved/conditional/
  cited; budget only ratchets down) — the trust mechanism.
- The first **end-to-end formalization of a researcher's own new foundational theory** (vs
  benchmarks/known results), in the **foundations-of-QM** domain.
- A **verified blueprint** bridging machine proof and domain-expert-legible math.
- A reproducible **artifact**: public repo, axiom audit, blueprint (concise + expanded).

### 1.4 Roadmap (~200)

---

## 2. Related Work (~1,000 words; trimmed — Issue E)

### 2.1 Agentic autoformalization & theorem proving (~280)
- Autoformalization [Wu 2205.12615; Draft-Sketch-Prove 2210.12283; Survey 2505.23486].
- Agentic provers + self-correction [Ax-Prover 2510.12787; LeanMarathon 2606.05400; MA-LoT;
  Goedel-Prover-V2; Repair-from-Compiler-Feedback 2602.02990].
- **Contrast:** they prove *externally-given* theorems; we formalize a *new* theory.

### 2.2 AI-for-science & autonomous discovery: the verification gap (~260)
- [AI Scientist-v2; AI Co-Scientist; Agentic Researcher 2603.15914; Brenner et al. 2603.04735].
- **Contrast:** discovery without machine-checking; we are machine-checked + audited.

### 2.3 LLM-as-judge / adversarial review (~230)
- [When AIs Judge AIs 2508.02994; Multi-Agent Debate Judges 2510.12697; Meta-Judges 2504.17087].
- **Contrast:** judging in the abstract; we embed an adversarial reviewer in a verifier-backed
  formalization loop.

### 2.4 Formalizing physics in Lean (~230)
- [Formalization of QFT 2603.15770; Quantum Stein's Lemma 2510.08672; PhysProver 2601.15737;
  PhysLean; Tooby-Smith 2026; Chemical Physics 2210.12150].
- **Contrast:** settled mathematical physics; we target a *contested foundational* proposal.

---

## 3. Method: A Closed, Audited Human–AI Formalization Loop (~2,600 words)

### 3.1 Architecture overview [FIGURE 1 — the loop] (~380)
- Diagram: Human → scope; Formalizer (coding agent) ⇄ Lean compiler (self-correction);
  Formalizer → artifact → Adversarial Reviewer (independent model) → critiques → back to
  Human/Formalizer; Axiom Auditor reads the build; Blueprint renders the result.

### 3.2 The formalizer: coding agent + compiler self-correction (~430)
- A coding agent (Claude Code) repurposed to emit Lean/Mathlib, not software; every error
  from `lake build` is a signal it must fix; "ship green increments" discipline.

### 3.3 The adversarial reviewer: an independent model critiquing design (~430)
- A *different* model (GPT-5.5 Pro) reviews after each significant step — not for compile
  errors (the compiler owns those) but for *conceptual* faults: vacuous hypotheses,
  over-strong axioms, hidden circularity, overclaiming. Why heterogeneity matters.

### 3.4 Human direction: scope, adjudication, premise control (~330)
- The human sets targets, adjudicates reviewer disputes, controls which premises are allowed
  as axioms vs must be proved. The irreducible human role.

### 3.5 Soundness instrumentation: the axiom budget & proved/conditional/cited audit (~470)
- `#print axioms` per headline theorem; a tracked **budget** that may only decrease; the
  proved (standard-axioms-only) / conditional (named interface axioms) / cited (external)
  taxonomy. The audit as a *published artifact*, not a side note.

### 3.6 The verified blueprint bridge (~300)
- leanblueprint: LaTeX statements mechanically linked (`\lean`/`\leanok`) to kernel-checked
  declarations; a dependency graph; checkdecls prevents drift; concise + expanded editions
  [contrast LeanArchitect 2601.22554].

### 3.7 Protocol & reproducibility [NEW — Issue A] (~260)
- Explicit round definition (formalize → self-correct to green → reviewer pass → human
  adjudication → audit update). Role boundaries table. How the axiom audit is captured and
  ratcheted. **Artifact/metrics table** (modules, theorems, axiom count over time, build
  status). Public repo + exact commit + blueprint URL.

---

## 4. Case Study: Formalizing a Collapse-Free Quantum Measurement Theory (~2,000 words)

> **Concrete source for all numbers/cases in this section:** `B_axiom_discharge_timeline.md`
> (trajectory, metrics, two reviewer-caught case studies) + `VERIFICATION_STATUS_UPDATE.md`.
> All figures verified against the repo on 2026-06-12.

### 4.1 The target theory (QIQT-H), AI-audience framing (~360)
- One neutral paragraph: a ψ-monist (weak/dynamical sense), exactly-unitary account where a
  finite-information (holographic) capacity bound + decoherence make multi-record macrostates
  non-instantiable, a non-dynamical selector λ fixes which record is actual, and Born is an
  across-run frequency. Framed as **the formalization target, not advocated** — the paper's
  contribution is the *method*, not the physics.

### 4.2 What was formalized: the layered core + artifact metrics (~520)
- The layered core: no-collapse mechanism (CoreNoCollapse/CapacityModel/SBSBridge/
  CollisionalGamma); Born as a conditional representation theorem + necessity countermodels
  (EffectGleason, BornJoin, the negative audits); covariant σ-additive typicality measure;
  normal state on B(H); free-field boost-invariant instance; continuum Fock/Spectral/Entropy
  tower (in progress).
- **Hard artifact metrics (the table reviewers want):** **122 modules · ~1,347
  theorems/lemmas · 795 `#print axioms` directives · 0 project axioms · 0 `sorry` · 1 benign
  vacuity-lint site · green build.** Quantify, don't assert.

### 4.3 The audit in action: proved / conditional / cited (~520)
- **The ratchet (the figure):** project axiom total **57 → 40 → 37 → 35 → 33 → 32 → 31 → 29 →
  21 → 17 → 8 → 7 → 6 → 0** (per `B.2`), with the honest note that some passes *added* an
  interface axiom (new conditional structure) before discharging it. Landmarks: ArakiInterface
  11→0 (incl. Donald's identity + Holevo `χ ≤ H(p)` via operator-monotone log), EntropyBridge
  6→0, Goldstein–Struyve Schur classification proved, DPI/Klein/Tsirelson discharged.
- **The three-layer honesty boundary (must appear verbatim-in-spirit):**
  (i) *axiom-free* — the conditional/structural deductive core; (ii) *open physics postulates*
  — (FQ), Macroscopic Definiteness, Canonical-IC/Born, Lorentz covariance, on which axiom-free
  Lean bears nothing; (iii) *formalization frontier* — the continuum Type II/Fock tower.
- **Framing guard (carry into §5.3):** "axiom-free in Lean certifies the *mathematics is
  conditional-correct and hidden-axiom-free*, **not** that AI proved new physics."

### 4.4 What the reviewer caught: evidence of the loop's value [Issue B] (~600)
Two concrete, kernel-checkable episodes (full detail in `B.3`/`B.4`):
- **Case 1 — a *false* axiom (GleasonSelector).** The formalizer encoded effect-Gleason as an
  interface axiom; the independent reviewer's *third* pass flagged it **false** (positivity
  omitted; a $\mathbb{C}^2$ weight $E_{00}+E_{01}$ meets the premises, isn't Born). Retired and
  replaced by *proved* content (`positive_ray_certain_forces_born`) — the fix made the result
  **stronger** (Born from positivity). Lesson: an independent vantage catches a capable agent's
  plausible-but-false premise.
- **Case 2 — an *inconsistent* axiom the budget check structurally could not see
  (MarginalLocality).** A `…locality…(h_alg : True)` axiom was logically inconsistent (a `True`
  antecedent ⇒ a false universal); counting axioms + scanning `sorry` cannot detect this.
  Converted to an explicit hypothesis; a dedicated **vacuity lint** added as a *third*
  soundness instrument (now 1 benign hit). Lesson: "compiles + axiom-count = 0" is necessary,
  **not sufficient** — soundness needs vacuity/inconsistency auditing too. This episode *is*
  the paper's trust thesis in miniature.
- Tie both to the **measurable trajectory ending at 0** as the empirical payload: the loop did
  not merely produce a green build — it produced an *audited, shrinking-to-zero* conditional
  base, with documented saves.

---

## 5. Discussion, Limitations, Threats to Validity (~900 words)

### 5.1 What generalizes: the transferable pattern (~300)
- The loop + audit is domain-agnostic; applies to any AI formalization where soundness, not
  just compilation, matters.

### 5.2 Failure modes & the human's irreducible role (~300)
- Where the formalizer stalls; where the reviewer is wrong/over-cautious; the human as
  premise-gatekeeper; cost.

### 5.3 Threats to validity (~300)
- Single case study (one theory, one team); model-specific (Claude/GPT versions);
  audit completeness (axioms named ≠ axioms justified); the theory's own open physics premise
  is not closed by formalization. State all plainly.

---

## 6. Conclusion (~400 words)
- Restate: trustworthy AI-for-science needs auditable machine-checking; the closed loop +
  axiom budget is a concrete, reproducible instrument; demonstrated on a hard foundational
  target. Future work: multi-team replication, automating the audit, richer reviewer protocols.

---

## References (~45–55) — ensure all six themes [Issue C]
Autoformalization (Wu, DSP, Survey, CRAMF, Aria) · Agentic proving (Ax-Prover, LeanMarathon,
MA-LoT, Goedel-Prover-V2, Repair-from-Feedback, Prover Agent, MPS-Prover) · AI-for-science
(AI Scientist v1/v2, AI Co-Scientist, Agentic Researcher, AgentRxiv, Brenner et al., "Why
LLMs Aren't Scientists Yet", surveys) · LLM-as-judge (When AIs Judge AIs, Debate Judges,
Meta-Judges, Judging with Many Minds, Auditing Reasoning Trees) · Verification/trust (Need-
for-Verification, Self-Consistency Hallucination, Tool Receipts, New Frontier) · Physics-in-
Lean (QFT formalization, Quantum Stein's Lemma, PhysProver, PhysLean, Tooby-Smith, Chemical
Physics) · Foundations background for the case study (Zurek decoherence/SBS; Bekenstein/Bousso
holographic bounds; CPW/Witten Type II; Srikanth; Goldstein–Struyve typicality; Busch POVM
Gleason; the project's own repo + WRITEUP).

---

## Quality Gate 3 check
- ✓ Reviewer score ≥28/35 (predicted 31/35 with A–E)
- ✓ All HIGH-severity issues resolved (Issue A → §3.7 + metrics table)
- ✓ Word allocations sum to target (~9,000)
- ✓ Platform conformity ≥70% (systems-paper structure, contributions list, architecture
  figure, reproducibility artifact, numeric citations — matches sample-paper norms)
