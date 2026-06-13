# QIQT-H — Publication & Promotion Strategy

A comprehensive recommendation document for releasing **QIQT-H (Quantized Information
Quantum Theory — Holographic)** as a human–AI research project. Distilled from the
2026-06-11 brainstorming transcript (`refs/Archive category suggestion.md`) and
reconciled with the *actual* state of the formalization so nothing here overclaims.

> **One-line positioning.** A ψ-monist, collapse-free account of quantum measurement in
> which a finite-information (holographic) capacity bound — together with decoherence —
> makes multi-record macroscopic states non-instantiable, so a single outcome obtains
> under exactly unitary dynamics; the deductive core is **machine-checked in Lean 4 /
> Mathlib**, produced through a closed human–AI formalization loop.

---

## 0. The honesty baseline (read this first)

Every promotional claim below must stay inside this line. The repo supports exactly:

- **Machine-checked, axiom-free (only `propext`, `Classical.choice`, `Quot.sound`):**
  the single-record *mechanism* as a conditional theorem (`CoreNoCollapse`,
  `CapacityModel`, `SBSBridge`, `CollisionalGamma`); the covariant σ-additive typicality
  measure μ∞ over histories (Layer C: `KolmogorovFiniteFiber`, `StateNetMeasure`); a
  genuine normal state on B(H) (`NormalState`) closing the loop end-to-end
  (`BHTypicalityMeasure`); a free-field, boost-invariant instance
  (`FreeFieldTypicality`); no-signaling for arbitrary entangled states
  (`NoSignalingGeneral`); Bell/CHSH with an explicit singlet reaching 2√2.
- **Machine-checked but conditional** on a small, explicitly enumerated set of *named
  interface axioms* (standard operator-algebra / probability facts), all listed in
  `lean/mathlib/QIQTH/AxiomAudit.lean`: the Born rule as a representation/typicality
  theorem (Layer B), with companion countermodels proving each premise is necessary.
- **Cited, not proved (honest boundary):** that specific local QFT algebras are
  type III₁ (Buchholz–Wichmann); the field-theoretic origin of the per-collision
  distinguishability premise; an *unconditional* Born derivation (the shared open
  problem of all interpretations); all empirical/physical claims.

**Do not** say "we proved quantum collapse is unnecessary" without the qualifier
"*conditional on a named, audited finite-information premise, with the mechanism — not
the premise's field-theoretic origin — machine-checked.*" The strength of the project is
precisely this disciplined separation of proved / conditional / cited.

---

## 1. arXiv: category, cross-list, endorsement

**Recommendation: submit with primary `cs.LO` or `cs.AI`, cross-list `quant-ph`
(and `math-ph`).** Rationale:

| Option | Pro | Con |
|---|---|---|
| **Primary `cs.AI`** (you are endorsed) | No endorsement hurdle; fits the "AI-driven formalization" story; broad reach | Reviewers may expect ML; the content is formal methods + physics, not learning |
| **Primary `cs.LO`** (Logic in CS) | Best technical fit for a Lean/Mathlib formalization; serious-formal-methods audience; you may already qualify via the AI endorsement domain | Confirm your endorsement covers `cs.LO`; smaller buzz than `cs.AI` |
| **Primary `quant-ph`** | Correct physics home | **You have no endorsement here** — blocked until you secure one |

- **Endorsement reality:** arXiv requires a per-category endorsement for a first
  submission to that category. You are endorsed in **AI**. Lead there; do **not** wait on
  a quant-ph endorser to publish.
- **Cross-list** `quant-ph` and `math-ph` so the physics/foundations community sees it.
  Cross-listing does not need separate endorsement once the primary is accepted.
- **AI-content policy caveat (important).** arXiv has tightened handling of LLM-generated
  submissions, especially in CS. Mitigate by foregrounding the **reproducible formal
  artifact**: the Lean repo + the blueprint with a verified dependency graph is concrete,
  checkable evidence — the opposite of "AI slop." Disclose AI assistance plainly in the
  acknowledgements/methods; that disclosure is an asset here, not a liability.
- **Dual-track virality:** release in the AI category first for cross-disciplinary
  curiosity; once it has traction, pursue a quant-ph endorser / a foundations venue. This
  is the transcript's instinct and it is sound.

**Secondary deposit for a DOI + permanence:** mirror on **Zenodo** (mints a DOI, archives
the exact Lean commit) and optionally **OSF**. No endorsement needed; gives a citable
artifact immediately and de-risks the arXiv timeline.

---

## 2. Title options

Pick one; A/B the subtitle.

1. **"Single Outcomes from Finite Information: A Machine-Checked, Collapse-Free Account of
   Quantum Measurement"** — leads with the result, signals the formal verification.
2. **"One Wave Function, One World: A Human–AI Formalization of Finite-Information Quantum
   Mechanics in Lean 4"** — leads with the collaboration angle (AI audience).
3. **"Collapse as a Theorem, Not a Postulate: Finite-Information Constraints, Decoherence,
   and a Verified Typicality Measure"** — leads with the foundations claim.

For a **cs.AI primary**, prefer #2 (methodology forward). For **cs.LO / quant-ph**,
prefer #1 or #3 (result forward).

---

## 3. Abstract (two framings)

**(A) AI-community framing — for a `cs.AI` primary.**

> We present a human–AI research program that uses interactive theorem proving to attack a
> foundational problem in physics: the quantum measurement problem. A coding assistant
> (Claude / Claude Code) was repurposed not to write software but to produce a Lean 4 /
> Mathlib formalization of each axiom and theorem of a finite-information quantum theory
> (QIQT-H), inside a closed self-verification loop in which every proof error was
> corrected by the assistant; a second model (GPT-5.5 Pro) served as adversarial reviewer
> after each significant step, with its feedback consumed back into the loop. The result
> is a machine-checked deductive core — a single-outcome *mechanism* from a finite
> (holographic) information capacity plus decoherence, a covariant σ-additive typicality
> measure over measurement histories, no-signaling for arbitrary entangled states, and the
> Born rule as a conditional representation theorem — with every dependency either reduced
> to Lean's three standard axioms or named in an explicit axiom audit. We report the
> methodology, the verified results and their honest boundaries (which premises are proved,
> which are conditional, which are cited), and argue that AI-driven formalization is a
> practical instrument for foundational science, not only for software.

**(B) Physics/foundations framing — for the `quant-ph` cross-list / a foundations venue.**

> We formalize, in Lean 4 / Mathlib, a ψ-monist and exactly-unitary account of quantum
> measurement in which no collapse postulate is invoked. A finite-information capacity
> bound of holographic origin renders macroscopic multi-record regional states
> non-instantiable; together with environmental decoherence this yields a single actual
> record per run, while the Born weights emerge as an across-run frequency pattern rather
> than a fundamental per-run probability. We machine-check: the single-record mechanism as
> a conditional theorem; a Lorentz-covariant, σ-additive typicality measure on the space
> of histories (correlated, state-agnostic), instantiated on a free-field net with a
> genuine boost symmetry; operational no-signaling for arbitrary entangled states; and the
> Born rule as a representation theorem whose premises we prove necessary by explicit
> countermodels. We delineate precisely what is proved, what is conditional on named
> operator-algebra interface axioms, and what is cited (e.g. type III₁-ness of local
> algebras, and an unconditional Born derivation, which remains open).

---

## 4. Paper outline (section by section)

1. **Introduction** — the measurement problem; the interpretation zoo (Copenhagen, MWI,
   Bohm); the thesis: *no collapse needed* — unitary evolution + decoherence + a finite
   (Bekenstein/holographic) information bound. State up front that the deductive core is
   machine-checked and that AI did the formalization.
2. **The QIQT-H framework** — ψ-monism; the finite coherent-information axiom (FQ);
   `d_eff(ρ) = 1/Tr(ρ²) ≤ 2^{Q_R}`; the holographic grounding of `Q_R` (area law / Wald).
3. **The single-outcome mechanism (machine-checked, conditional theorem)** — capacity
   exclusion (`CoreNoCollapse`/`CapacityModel`), record broadcasting / SBS (`SBSBridge`),
   the derived per-collision distinguishability (`CollisionalGamma`). State the one
   remaining open physical input (field-theoretic origin of the premise).
4. **Born as a conditional theorem** — Layer B; the representation/typicality result;
   the necessity countermodels; what an *unconditional* Born would require.
5. **A covariant typicality measure** — Layer C; the Kolmogorov/Carathéodory extension to
   μ∞; no-signaling; state-agnostic construction; the free-field boost-invariant instance.
6. **Methodology: a closed human–AI formalization loop** — Claude Code as formalizer with
   self-correction; GPT-5.5 Pro as reviewer; the axiom-budget discipline; the blueprint +
   doc-gen4 as the reproducible, human-readable artifact. (This is the AI-audience payload.)
7. **Scope, boundaries, and open problems** — the proved/conditional/cited table;
   unconditional Born; continuum type III₁; empirical (FQ) calibration via `I_0`.
8. **Relation to prior work** — Srikanth (finite fine-graining), Zurek (decoherence/SBS),
   CPW/Witten (Type II algebras), Bekenstein/Bousso (holographic bounds), Palmer (RaQM),
   Goldstein–Struyve (typicality). Position honestly as a *synthesis* with a new verified core.
9. **Reproducibility** — repo, exact commit, build instructions, the blueprint URL,
   the axiom audit; AI-assistance disclosure.

Keep §3–5 tight and let the **blueprint** carry the formal detail (link it).

---

## 5. The reproducible-artifact asset (your strongest differentiator)

What makes this credible rather than hype is that the math is *checkable*:

- **Lean repo:** `github.com/kaplan196883/QIQT-H` — green build, axiom audit.
- **Blueprint (math-readable):** LaTeX statements + a verified dependency graph linking
  each statement to its Lean proof; concise and expanded editions; pdf + web. Host it on
  **GitHub Pages** so it has a public URL the paper can cite.
- **doc-gen4 API docs:** browsable per-declaration source.
- **`WRITEUP.md`:** the honest, layered master summary.

Action: stand up GitHub Pages for the blueprint (and optionally the docs) and put the URL
in the abstract's comments field. A reviewer who can click from a theorem statement to a
kernel-checked proof is the antidote to "AI-generated" skepticism.

---

## 6. Promotion plan (dual-track, low-effort first)

**Immediate (this week):**
- Zenodo deposit of the repo (DOI) — instant citable artifact, no gatekeeper.
- One-page project site (GitHub Pages) linking: paper PDF, blueprint, repo, WRITEUP.
- arXiv submission, primary `cs.AI` (or `cs.LO`), cross-list `quant-ph`, `math-ph`.

**Launch (week of arXiv posting):**
- A blog post (Medium / personal site) titled for the AI audience: *"I used a coding agent
  to formalize a new theory of quantum measurement — and a second AI to review it."* Lead
  with the loop, the self-correction, the axiom discipline; link the blueprint.
- Short threads on X and LinkedIn; tag formal-methods (Lean/Mathlib community is active and
  receptive), quantum-foundations, and AI-for-science audiences. The Lean community in
  particular will amplify a serious Mathlib-rooted formalization.

**Follow-up:**
- Submit a talk to a quantum-foundations or AI-for-science workshop.
- Pursue a `quant-ph` endorser once there's visible traction (see §7).

---

## 7. Endorsement & outreach checklist

- [ ] Confirm which arXiv categories your existing endorsement covers (cs.AI; check cs.LO).
- [ ] Prepare a 3-sentence outreach blurb: what it is, why it's checkable (blueprint link),
      what you're asking (endorsement or feedback) — honest about proved-vs-conditional.
- [ ] For a `quant-ph` endorser: target authors in **quantum foundations / typicality /
      algebraic QFT** (the natural reader), not celebrities. A clickable verified blueprint
      is your differentiator; lead with it.
- [ ] Institutional fits to approach via *official channels* (not personal emails):
      Perimeter Institute (foundations), MIT CQE, Santa Fe Institute (complex systems),
      and AI-for-science groups at DeepMind / OpenAI / Anthropic. Engage by citing/
      discussing their public work, not cold-contacting executives.
- [ ] Disclose AI assistance in the paper; this is required and, framed as the methodology,
      is the headline rather than a footnote.

---

## 8. Risks and how to de-risk

| Risk | Mitigation |
|---|---|
| **Overclaiming** ("collapse disproved") | Use the proved/conditional/cited table everywhere; the audit is the proof of discipline. |
| **"AI slop" perception** | Lead with the reproducible Lean artifact + verified blueprint; disclose AI honestly as *method*. |
| **Endorsement block in quant-ph** | Publish via cs.AI/cs.LO first; cross-list; pursue endorser after traction. |
| **Physics community pushback on the (FQ) premise** | Be explicit that the *mechanism* is verified and the *premise's field-theoretic origin* is the open input; invite scrutiny of exactly that. |
| **Empirical untestability** | **Own it honestly (2026-06-13, GPT-5.5 assessment):** the finite-capacity postulate is kinematic and `Q_R ~ A/4ℓ_P²` is far too large (~10⁶⁶ bits/cm²) to deviate from QM at accessible scales — absent an *added* dynamical law with a small (currently free-parameter) effective capacity `Q^eff`, the framework is **empirically equivalent to standard QM**, i.e. an interpretation. Do NOT advertise the `I_0`/neutrino signature as a derived falsifiable prediction; present it as a *conditional dynamical extension* whose `Q^eff` is the open requirement. Honesty here is the credibility play. |

---

## 9. Bottom line

You have something most foundations proposals do not: a **machine-checked deductive core
with an honest, audited boundary**, produced by a **novel closed human–AI loop**. Lead with
that pairing. Publish in AI (where you're endorsed) with a quant-ph cross-list, make the
verified blueprint public so the claims are clickable, and let the reproducible artifact —
not adjectives — carry the credibility. The science is positioned as a serious speculative
program; the methodology is positioned as a genuine first.
