# THE TOMITA OPERATOR (T0_1–T0_6): S₀ on the orbit domain

**Status:** ACTIVE (2026-07-08). **FABLE-5-CONSULT-VERIFIED (self-consult, high reasoning; all
held APIs + Mathlib names verified — including the DECISIVE DISCOVERY: Mathlib's `LinearPMap` IS
σ-semilinear at this pin, so `E →ₛₗ.[starRingEnd ℂ] F` typechecks with full algebraic API; what
Mathlib lacks is the closure/adjoint THEORY for σ ≠ id).** **Goal:** the Tomita operator S₀ of
the tower limit state, constructed on its classical orbit domain, with: exact computation on the
pure-component core, the right-multiplication adjoint = the FINITE σ₋ᵢ (computed, not
analytically continued), the adjoint-domain pairing family, and closability in the graph-limit
sense. File: `QIQTH/TowerGNS/Tomita.lean`.

## Binding verdict (never violate)

- **A1 — Packaging:** `towerTomita₀ : TowerGNS →ₛₗ.[starRingEnd ℂ] TowerGNS` (the semilinear
  LinearPMap) with `domain := towerTomitaDom` — the ℂ-submodule with CARRIER
  `{v | ∃ T ∈ towerLimitVN, v = T Ω}` (a submodule OUTRIGHT — towerLimitVN closed under +/•/0;
  no span needed). toFun by Classical.choose; well-definedness TRIVIAL by separation (T ↦ TΩ is
  INJECTIVE on towerLimitVN = towerLimitVN_eq_of_apply_cyclicVec); map_add'/map_smul' by
  injectivity + star_smul (StarModule instance verified). REJECTED: ℝ-linear PMap (the R3
  instance hazard on the Completion; designated thin path ONLY if a closure object is ever
  demanded — do not open now); the graph route (id-only in Mathlib).
- **A2 — The right-multiplication adjoint (THE STRONGEST THEOREM — include):**
  `adjoint (towerRightMulCLM C₀ a) = towerRightMulCLM C₀ ((rightConj (rightConj a))ᴴ)` — via
  THE ENGINE SQUARED: ι(a)·ρ_K = ρ_K·ι(rightConj² a) (two E1 applications + sqrtGibbs_mul_self +
  mul_assoc — NO S_K⁻¹ at stage K); the stage pairing gnsInner K (x·ιb) y = gnsInner K x (y·ιa)
  with b := (rightConj² a)ᴴ (cornerEmbed_star + trace_mul_cycle); raw double induction mirrors
  rawInner_leftMulRaw_conjTranspose; eq_adjoint_iff mirrors towerRepCLM_star. BRIDGE (optional,
  include if cheap): (rightConj² a)ᴴ = modAut (gibbsDensity) aᴴ — THE FINITE σ₋ᵢ, linking to the
  held modAut of towerState_kms_boundary.
- **A3 — Closability: the SEQUENCE/GRAPH-LIMIT form, independent of A2:** for T : ℕ → CLM with
  ∀ n, T n ∈ towerLimitVN, (T n Ω) → 0 ∧ (star (T n) Ω) → v ⟹ v = 0. Proof chain (orientation-
  verified): ⟪R_aΩ, (star Tₙ)Ω⟫ = ⟪Tₙ(R_aΩ), Ω⟫ (adjoint_inner_right) = ⟪R_a(TₙΩ), Ω⟫
  (towerRightMul_comm_limitVN) = ⟪TₙΩ, (adjoint R_a)Ω⟫ → 0; LHS → ⟪R_aΩ, v⟫
  (Filter.Tendsto.inner); so ⟪↑(of C a), v⟫ = 0 (towerRightMul_cyclicVec); span_induction +
  **Dense.eq_zero_of_inner_right** (VERIFIED: dense set in the FIRST slot) on
  dense_span_towerRep_cyclicVec. Uses only the ABSTRACT adjoint of R_a. Bank this EARLY (before
  the heavy T0_4).
- **A4 — The adjoint-domain pairing (needs A2):** ∀ T ∈ towerLimitVN, ∀ C₀ a:
  ⟪(star T)Ω, ↑(of C₀ a)⟫ = ⟪↑(of C₀ ((rightConj² a)ᴴ)), TΩ⟫ — the classical
  ⟪T*Ω, T′Ω⟫ = ⟪T′*Ω, TΩ⟫ with T′ = R_a. Do NOT package F₀ as a second choice-based operator —
  the pairing family carries the full content (note: every coerced pre-vector IS R_cΩ for a
  single collapsed c, via towerGerm + additivity).
- **A5 — CUTS (binding):** the closure S̄₀ as an OBJECT (no σ-closure infra; the ℝ-PMap thin path
  stays closed); polar decomposition/Δ/J; KMS-at-the-limit; type. Names: `towerTomitaDom`,
  `towerTomita₀`. Banner in every docstring: "constructed on the orbit domain; conjugate-linear
  partial operator; closable in the sequence sense; the closure, Δ, J, KMS-at-the-limit, and
  type are NOT constructed or claimed."
- **Choice hygiene (binding):** EXACTLY ONE spec lemma `towerTomita₀_apply : S₀ ⟨TΩ, _⟩ =
  (star T) Ω` proved once from separation; everything downstream routes through it; NEVER
  `unfold towerTomita₀`.

## Increments

- [x] **T0_1 — `QIQTH/TowerGNS/Tomita.lean`: the domain** ✅ DONE — `towerTomitaDom` (submodule
  outright); Ω ∈ D, ↑(of C a) ∈ D, T Ω ∈ D; **Dense D** (Submodule.span_le from S8's
  dense_span_limitVN_orbit_cyclicVec). Risk NEGLIGIBLE.
- [x] **T0_2 — the operator** ✅ DONE — `towerTomita₀` (semilinear PMap; toFun by choose); THE ONE SPEC
  LEMMA `towerTomita₀_apply`; map_add'/map_smul' (injectivity + star_smul); **S₀ Ω = Ω**;
  **`towerTomita₀_of`** (S₀ ↑(of C a) = ↑(of C aᴴ) — map_star of towerRep +
  towerRep_cyclicVec_of); S₀ v ∈ D; INVOLUTION S₀(S₀ v) = v. Risk LOW-MEDIUM (choice hygiene,
  subtype coercions; no completion induction anywhere).
- [x] **T0_3 — CLOSABILITY (bank early)** ✅ DONE — the A3 sequence theorem + the S₀-phrased corollary.
  Risk LOW.
- [x] **T0_4 — the right-multiplication adjoint** ✅ DONE — `cornerEmbed_mul_gibbsDensity` (the engine
  squared, own lemma BEFORE the induction); stage `gnsInner_rightMul_adjoint`; raw
  `rawInner_rightMulRaw_adjoint`; CAPSTONE **`towerRightMulCLM_adjoint`** (state with the
  EXPLICIT candidate via (eq_adjoint_iff R_b R_a).mpr — the towerRepCLM_star shape); the
  optional modAut bridge. Risk MEDIUM (deep-stage bookkeeping; exact mirror of two green
  proofs).
- [x] **T0_5 — the adjoint-domain pairing capstone** ✅ DONE — the A4 family. Risk LOW.
- [ ] **T0_6 — checkpoint** — the HAVE/HAVE-NOT sentences VERBATIM (below) into
  TowerGNS/Checkpoint.lean (Tomita stanza) + inventory; AxiomAudit pins; plan → COMPLETE;
  delete the loop; stop.

## Checkpoint sentences (verbatim at T0_6)

HAVE: "The Tomita operator S₀ of the tower limit state is constructed on its classical orbit
domain {TΩ : T ∈ towerLimitVN}: it is well-defined (Ω is separating), conjugate-linear,
involutive, and densely defined; its action on the dense core of pure components is computed
exactly (S₀ ↑(of C a) = ↑(of C aᴴ)); the commutant-side right multiplications R_a admit the
exact adjoint R_a† = R_{ρ aᴴ ρ⁻¹} (the finite-stage σ₋ᵢ, computed — not analytically
continued), witnessing the pairing ⟪T*Ω, R_aΩ⟫ = ⟪R_a†Ω, TΩ⟫ on a dense family; consequently
S₀ is closable in the graph-limit sense (TₙΩ → 0 and Tₙ*Ω → v force v = 0)."

HAVE NOT: "The closure S̄ is not constructed as an object, and no polar decomposition, no
modular operator Δ, no modular conjugation J, no KMS condition of the limit state, and no von
Neumann type classification is constructed or claimed; Mathlib's LinearPMap closure and adjoint
theories cover only ℂ-linear (identity ring-hom) partial maps, and a conjugate-linear closure
theory is not built here."

## Top-4 failure modes (mitigations binding)

1. Completion-synonym instance mismatch in the PMap bundle → all working lemmas at CLM/inner
   level; PMap fields delegate to a pre-proved plain function in application position; T0_4 raw
   layer copies LeftMul.lean line-for-line.
2. Classical.choose leakage → the ONE spec lemma; never unfold.
3. Orientation errors (adjoint_inner_left/right; first-slot conj-linearity;
   Dense.eq_zero_of_inner_right's dense-first-slot; the S₀/F₀ pairing) → canonical "pure
   component in the stated slot" form per theorem; the two orbit adapters as named rewrites.
4. T0_4 eq_adjoint_iff stall → explicit candidate on the adjoint side; the engine-squared corner
   identity as its own lemma BEFORE the raw induction (three-rewrite of/of case).

## Discipline (every increment)

`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.TowerGNS.Tomita` green; #print axioms std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit on
main + trailer `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log AND
LEAN_RESULTS_INVENTORY.md. NO sorry; NEVER claim S̄/Δ/J/KMS-at-limit/a type; NEVER unfold
towerTomita₀; NEVER claim an increment too hard (attempt, iterate; checkpoint only after a
genuine failed attempt with the error shown); check sibling jobs before each increment; explicit
git paths only. Subagent authoring (fable) permitted, discipline in the main loop. Consults:
Agent tool (fable) high reasoning or mcp__OpenAI__ask gpt-5.5-pro (never expose keys).

## Progress log

- **2026-07-08** — Campaign scoped; consult verified (decisive discovery: LinearPMap is
  σ-semilinear at the pin — the conjugate-linear PMap typechecks with full algebraic API; only
  the closure/adjoint THEORY is id-only, hence the sequence-form closability + the object-cut).
  The adjoint-of-R_a theorem confirmed provable via the engine squared — the finite σ₋ᵢ computed,
  not analytically continued. Loop armed.

- **2026-07-08** — **T0_1+T0_2+T0_3 LANDED** (`QIQTH/TowerGNS/Tomita.lean`, axiom-free std-3,
  budget 0; fable subagent, one iteration issue): `towerTomitaDom` (submodule outright, DENSE
  via S8); **`towerTomita₀ : TowerGNS →ₛₗ.[starRingEnd ℂ] TowerGNS`** — THE SEMILINEAR PMAP
  TYPECHECKED AS PREDICTED; the ONE spec lemma `towerTomita₀_apply` (choice contained in
  tomitaWitness); **S₀Ω = Ω**; **`towerTomita₀_of`** (S₀ ↑(of C a) = ↑(of C aᴴ) — the computed
  core); INVOLUTION (both forms); **`towerTomita₀_closable`** — the A3 sequence theorem BANKED
  EARLY (+ the S₀ corollary). Lean note: subtype-mk type annotations differ syntactically
  between ↥(S₀.domain) and ↥(towerTomitaDom) — defeq but rw-opaque; route through
  towerTomita₀_congr / exact, never rw the spec lemma directly (recorded for T0_4/T0_5).
  NEXT → T0_4 (the σ₋ᵢ adjoint).

- **2026-07-08** — **T0_4+T0_5 LANDED, GREEN FIRST BUILD** (Tomita.lean extended, axiom-free
  std-3, budget 0; fable subagent, zero proof failures): the engine squared
  `cornerEmbed_mul_gibbsDensity`; the stage/raw adjoint pairings (verbatim mirror of the
  Representation.lean skeleton); CAPSTONE **`towerRightMulCLM_adjoint`** — adjoint R_a =
  R_{(rightConj² a)ᴴ}; the modAut BRIDGE INCLUDED **`rightConj_sq_conjTranspose_eq_modAut`** —
  (rightConj² a)ᴴ = modAut ρ aᴴ: THE ADJOINT PARAMETER IS THE FINITE σ₋ᵢ IMAGE, COMPUTED (the ⅟
  plumbing cooperated via invOf_eq_right_inv); T0_5 **`tomita_adjoint_pairing`** — the classical
  ⟪T*Ω, R_aΩ⟫ = ⟪R_a†Ω, TΩ⟫ on the dense family, one rw chain, all orientations first-try.
  NEXT → T0_6 (checkpoint; delete loop; stop).
