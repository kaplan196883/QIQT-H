# THE TOWER (T1–T7): the first machine-checked contact with the Type III₁ wall

**Status:** COMPLETE (2026-07-03) — T1–T8 ALL LANDED, axiom-free std-3, budget 0. **FABLE-5-CONSULT-VERIFIED (self-consult, high reasoning)** (binding
verdict below). **Goal:** phase A of the continuum-definition attack via the ITPFI/Araki–Woods
route — the code tower with its Gibbs product states IS Araki–Woods input data. Centerpiece: **the
Araki–Woods III₁ criterion for the code's Gibbs tower as a machine-checked ARITHMETIC theorem about
eigenvalue-list data** (`gibbsTower_awFingerprint_III₁`), plus the σ-additive infinite-mode Gibbs
measure (DY4 consistency → the held Kolmogorov extension), non-atomicity, the Powers guard, and the
finite operator refinement tower. Files under `lean/mathlib/QIQTH/Tower/`.

## Binding verdict (from the consult — never violate)
- **Formalize a NAMED WITNESS PREDICATE, never the verbatim AW r∞ definition** (the
  weight-threshold constant differs across sources — misquoting poisons the citation; the
  amplification lemma buys nothing interpretable). Definitions ADDITIVE in κ (log-eigenvalue
  differences — the kappaOf language), NOT multiplicative in ratios: `IsTailModularExponent Λ κ`
  (∃ δ > 0, ∀ ε > 0, ∀ N, ∃ k ≥ N, ∃ i j, δ ≤ Λ k i ∧ δ ≤ Λ k j ∧ |log Λki − log Λkj − κ| ≤ ε)
  and `AWFingerprintIII1 Λ` (the additive subgroup closure of the tail exponents is DENSE in ℝ).
- **The two clauses are load-bearing (counterexamples to record in comments):** (1) drifting
  frequencies βω_k = s + 1/k: the algebraic ratio group is dense but the factor is III_{e^{−s}} —
  the TAIL quantifier (beyond every N) is essential; (2) vanishing weights λ_k = (1−ε_k, ε_k),
  Σε_k < ∞: nontrivial ratios everywhere, but the factor is type I∞ — the uniform δ is essential.
- **The two-frequency criterion IS correct and sufficient:** two values s ≠ t of βω_k, each
  occurring infinitely often, s/t irrational, uniform bounds 0 < a ≤ βω_k ≤ b, D_k ≥ 2 ⟹
  AWFingerprintIII1. Route: the (1,0) pair in each factor gives the EXACT exponent (the Z cancels
  — never approximate); ℤs + ℤt dense via `AddSubgroup.dense_or_cyclic` (cyclic ⟹ s/t ∈ ℚ).
- **The three cited operator facts — VERBATIM in the T3 docstring, never proved:** (α) a ratio
  witnessed in infinitely many disjoint factors with weight uniformly ≥ δ lies in r∞ (Araki–Woods
  1968, sufficiency/amplification); (β) r∞ is closed and r∞ ∩ (0,∞) is a closed multiplicative
  subgroup (Araki–Woods 1968); (γ) r∞ = [0,∞) defines the III₁ class for ITPFI and r∞ = the Connes
  S-invariant for ITPFI (Araki–Woods 1968; Connes 1973). None proved; no vN algebra constructed.
- **Uniform bounds (elementary, exact):** λ_k(0) = 1/Z > 1 − e^{−a} (via Z(1−q) = 1 − q^D < 1);
  λ_k(1) = e^{−βω_k}/Z > e^{−b}(1 − e^{−a}) =: δ₀; λ_k(1)/λ_k(0) = e^{−βω_k} EXACTLY.
- **The state limit (T5) is near-immediate:** DY4's marginal consistency = exactly Mathlib's
  `IsProjectiveMeasureFamily` direction (no off-by-one); the small gap is the ADAPTER from weight
  sums to `Measure.map` equalities (Measure.ext on singletons, finite additivity; `PMF.toMeasure`
  or weighted Dirac sums); cross-check vs `Measure.infinitePi` via the held uniqueness.
- **The quantum reading of the limit is FALSE, not deferred:** under βω_k ≤ b the limit measure is
  NON-ATOMIC (singleton weights → 0), so no diagState/diagonal density exists (and ℓ² of the
  configuration space is nonseparable). T6 proves non-atomicity as a guard; the GNS/ITPFI quantum
  limit is Phase-B/cited. The vacuum-atom dichotomy Σe^{−βω_k} < ∞ mirrors the AW type-I boundary
  — cited, not proved.
- **Naming discipline:** theorem `gibbsTower_awFingerprint_III₁`, never `typeIII_one_*`; "III₁"
  appears only in predicate names and cited docstrings. The single most likely failure mode is the
  T3 docstring writing "hence the code algebra is a III₁ factor" — FORBIDDEN outside a citation
  sentence naming Araki–Woods 1968 + Connes 1973 and stating the algebra is not constructed.
- **CUT:** infinite tensor products/GNS-of-tower/weak closures/hyperfiniteness; any theorem whose
  STATEMENT mentions a vN algebra type; the verbatim AW r∞ definition + amplification; converse
  classification (constant spectrum ⟹ algebra is III_λ — only the fingerprint FAILURE is proved);
  any quantum state limit; Connes S-invariant/flow of weights/σ-weak machinery; inductive limits;
  any continuum-completion or QG-progress claim beyond "first machine-checked contact with the
  III₁ fingerprint".

## Increments (T7 is first to drop if budget tightens)
- [x] **T1 — AW data + fingerprint definitions + κ-bridge** ✅ DONE (`QIQTH/Tower/AWFingerprint.lean`):
  `gibbsEigen` lists (positivity, normalization); the uniform bounds (λ₀ > 1−e^{−a},
  λ₁ > e^{−b}(1−e^{−a}), the EXACT ratio λ₁/λ₀ = e^{−x}); `IsTailModularExponent` +
  `AWFingerprintIII1` (additive, in κ); the bridges `kappaOf (gibbsEigen D x) i j = x·(j−i)` and
  `exp (kappaOf p i j) = p i / p j`.
- [x] **T2 — Kronecker density** ✅ DONE (`QIQTH/Tower/KroneckerDensity.lean`): `Irrational (s/t) →
  Dense (AddSubgroup.closure {s, t})` via `AddSubgroup.dense_or_cyclic` (cyclic ⟹ s = ma, t = na
  ⟹ s/t ∈ ℚ). Classical arithmetic, no operator content.
- [x] **T3 — THE CENTERPIECE: `gibbsTower_awFingerprint_III₁`** ✅ DONE: two frequencies i.o. with
  irrational ratio + uniform bounds + D_k ≥ 2 ⟹ AWFingerprintIII1; PLUS the hypothesis-free
  concrete corollary with βω ∈ {1, √2} via `irrational_sqrt_two` (the vacuity guard). The (α)(β)(γ)
  citation block VERBATIM in the docstring.
- [x] **T4 — the Powers guard** ✅ DONE: constant frequency s ⟹ every tail exponent ∈ sℤ ⟹ the closure is
  cyclic/closed ⟹ ¬AWFingerprintIII1 (the fingerprint of Powers III_{e^{−s}} — cited). The
  separation theorem: the predicate is neither vacuous nor universal.
- [x] **T5 — the state limit** ✅ DONE (`QIQTH/Tower/GibbsLimit.lean`): the adapter (DY4 weight sums →
  Measure.map equalities); `gibbsLimitMeasure := kolmogorovMeasure` with `IsProjectiveLimit` +
  uniqueness; identification with `Measure.infinitePi` of the single-mode Boltzmann measures.
- [x] **T6 — non-atomicity** ✅ DONE: under βω_k ≤ b every singleton has measure zero (cylinder squeeze,
  `tendsto_measure_iInter`) — certifying the classical measure as the correct limit object and
  that no diagonal quantum density exists (the vacuum-atom dichotomy cited).
- [x] **T7 (optional) — the finite operator tower** ✅ DONE: `cornerEmbed` for C ⊆ C′ — unital ⋆-hom,
  mode-operator compatibility, state compatibility φ_{C′}∘ι = φ_C, and MODULAR-FLOW EQUIVARIANCE
  σ_t^{C′}∘ι = ι∘σ_t^C via the kappaOf eigen-law. The honest finite shadow of the ITPFI tower;
  family of finite-dimensional maps only.
- [x] **T8 — checkpoint** ✅ DONE: the campaign checkpoint sentences (from the consult, per-increment
  versions logged as each lands): HAVE: "the machine-checked arithmetic content of the Araki–Woods
  III₁ criterion for the code's Gibbs tower, including a hypothesis-free concrete instance, the
  Powers-guard separation, the σ-additive infinite-mode Gibbs measure with its non-atomicity, and
  the state-compatible modular-equivariant finite refinement tower; the inference to an actual III₁
  factor is cited (Araki–Woods 1968; Connes 1973), never proved." HAVE NOT: "the ITPFI von Neumann
  algebra, its ratio set, its type, any inductive limit or weak closure, any quantum state on the
  infinite system, or any continuum-limit completion — none are constructed or classified here."
  VERBATIM in the module docstring + inventory; delete the loop; paper/website sync on request.

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.Tower.<mod>` green; `#print axioms` std-3;
budget 0; AxiomAudit pins; wire `QIQTH.lean`; ONE commit +
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push schannel; update this checklist +
`LEAN_RESULTS_INVENTORY.md`. HONESTY: the naming discipline above; the cut list; NEVER claim QG
solved, a wall crossed, or the continuum limit done — this is the wall's FINGERPRINT, measured.
NEVER claim an increment too hard — attempt, iterate, checkpoint only after a genuine failed
attempt with the error shown. Check sibling jobs before each increment. Consults: the Agent tool
(fable, general-purpose) at high reasoning, or `mcp__OpenAI__ask` gpt-5.5-pro (never expose keys).

## Progress log
- **2026-07-03** — plan created from the Fable-5 self-consult (additive-κ witness predicate, never
  verbatim r∞; the two load-bearing clauses with counterexamples; the two-frequency criterion
  verified correct; the (α)(β)(γ) citation discipline; diagState-on-limit ruled FALSE not deferred;
  the operator inductive limit cut, one finite tower increment allowed; ordering T1→T8). NEXT → T1.

- **2026-07-03** — **T1 LANDED** (`QIQTH/Tower/AWFingerprint.lean`, axiom-free std-3, budget 0,
  no sorry): gibbsEigen (positive, normalized); Zgeom_lt_inv_one_sub (Z(1−q) = 1−q^D < 1 via
  geom_sum_mul); the uniform weight bounds gibbsEigen_zero_bound (λ₀ > 1−e^{−a}) +
  gibbsEigen_one_bound (λ₁ > e^{−b}(1−e^{−a})); gibbsEigen_ratio (the EXACT λ₁/λ₀ = e^{−x} — the
  Z cancels); IsTailModularExponent + AWFingerprintIII1 (the named witness predicates, additive in
  κ, load-bearing clauses documented with counterexamples); the κ-bridge kappaOf_gibbsEigen
  (= x(j−i)) + exp_kappaOf (= the eigenvalue ratio). Checkpoint (T1): HAVE the finite eigenvalue
  data with uniform bounds, the arithmetic AW fingerprint predicates, and the exact bridge from
  the corner modular exponents to the ratio data; HAVE NOT any von Neumann algebra, ratio set of
  an algebra, or type classification — arithmetic about eigenvalue lists only. NEXT → T2
  (Kronecker density).

- **2026-07-03** — **T2 LANDED** (`QIQTH/Tower/KroneckerDensity.lean`, axiom-free std-3,
  budget 0): dense_closure_pair — the additive subgroup of ℝ generated by two reals with
  IRRATIONAL ratio is dense (AddSubgroup.dense_or_cyclic; in the cyclic case s = m•a, t = n•a
  force s/t = m/n ∈ ℚ — contradiction; the t ≠ 0/n ≠ 0/a ≠ 0 degeneracies handled via the
  irrationality itself). Checkpoint (T2): HAVE density in ℝ of the additive subgroup generated by
  two frequencies with irrational ratio, fully in Mathlib-native subgroup language; HAVE NOT any
  connection to operator algebras — classical Kronecker arithmetic and nothing else.
  NEXT → T3 (the centerpiece).

- **2026-07-03** — **T3 LANDED — THE CENTERPIECE** (`QIQTH/Tower/Centerpiece.lean`, axiom-free
  std-3, budget 0, GREEN FIRST TRY): isTailModularExponent_of_frequently (a frequency occurring
  i.o. contributes its EXACT negated value — the (1,0) pair, the Z cancels, accuracy 0);
  **gibbsTower_awFingerprint_III₁** — THE ARAKI–WOODS III₁ FINGERPRINT OF THE CODE'S GIBBS TOWER
  (two frequencies i.o., irrational ratio, uniform bounds, D_k ≥ 2 ⟹ AWFingerprintIII1 — T1's
  exact exponents feeding T2's Kronecker density through closure monotonicity + Dense.mono);
  the (α)(β)(γ) citation block VERBATIM in the docstring (the operator reading cited, never
  proved); **gibbsTower_awFingerprint_III₁_sqrtTwo** — the HYPOTHESIS-FREE alternating {√2, 1}
  qubit instance via irrational_sqrt_two (the vacuity guard). Checkpoint (T3): HAVE the
  machine-checked arithmetic content of the Araki–Woods III₁ criterion for the code's Gibbs
  tower, including a hypothesis-free concrete instance; the inference to an actual III₁ factor is
  cited (Araki–Woods 1968; Connes 1973), never proved. HAVE NOT the ITPFI von Neumann algebra,
  its ratio set, or its type — none are constructed or classified here. NEXT → T4 (the Powers
  guard).

- **2026-07-03** — **T4 LANDED** (`QIQTH/Tower/PowersGuard.lean`, axiom-free std-3, budget 0):
  tail_exponent_constant_mem (every tail exponent of a constant-frequency tower ∈ sℤ — the
  fractional-part gap min(f, 1−f) gives the positive minimum distance defeating every accuracy);
  CAPSTONE gibbsTower_constant_not_fingerprint — the constant tower FAILS the fingerprint (sℤ is
  not dense: s/2 keeps distance s/2 from every multiple). Checkpoint (T4): HAVE the separation
  theorem — the fingerprint holds for two-frequency irrational towers and provably fails for
  single-frequency towers, so the predicate is not vacuous and not universal; HAVE NOT any claim
  that the single-frequency algebra is III_λ or is not III₁ — only the arithmetic fingerprint
  failure is proved (Powers 1967 cited). NEXT → T5 (the state limit).

- **2026-07-03** — **T5 LANDED** (`QIQTH/Tower/GibbsLimit.lean`, axiom-free std-3, budget 0, GREEN
  FIRST TRY): boltzMeasure (the single-mode Boltzmann probability measure; singleton = ofReal
  gibbsEigen); **gibbsLimitMeasure := Measure.infinitePi** — THE σ-ADDITIVE INFINITE-MODE GIBBS
  MEASURE on occupation configurations, via the held product/Kolmogorov machinery, with
  IsProjectiveLimit + uniqueness + the probability instance; pMode_eq_gibbsEigen (the DY bridge —
  DS2's partition identity closes the parametrizations); CAPSTONE gibbsLimit_marginal_singleton —
  the finite marginals ARE the code's own DY Gibbs weights. Checkpoint (T5): HAVE the σ-additive
  infinite-mode Gibbs measure on occupation configurations, as the unique projective limit of the
  DY marginals through the held Kolmogorov extension, identified with the Mathlib infinite
  product; HAVE NOT any quantum state on an infinite system — the classical (diagonal) limit
  object only. NEXT → T6 (non-atomicity).

- **2026-07-03** — **T6 LANDED** (`QIQTH/Tower/NonAtomic.lean`, axiom-free std-3, budget 0):
  one_add_le_Zgeom (1+q ≤ Z for D ≥ 2); **gibbsEigen_le_ceiling** — the uniform eigenvalue
  ceiling 1/(1+e^{−b}) < 1 under 0 ≤ x ≤ b; CAPSTONE **gibbsLimitMeasure_singleton_eq_zero** —
  THE CYLINDER SQUEEZE: every singleton configuration is null (depth-N cylinder mass ≤ c^N → 0,
  via the T5 projective-limit identity + Measure.pi_pi + ENNReal.tendsto_pow_atTop_nhds_zero);
  bundled **gibbsLimitMeasure_noAtoms** (Mathlib NoAtoms). So NO diagonal-density ("diagState")
  reading of the T5 limit exists — the quantum reading of the limit measure is FALSE (binding
  verdict), not deferred. The vacuum-atom dichotomy (Σe^{−x_k} < ∞ ⟹ vacuum atom; Kakutani-type)
  is CITED in the docstring, never proved — the uniform bound is load-bearing. NEXT → T7
  (cornerEmbed, optional — drop first if budget tightens) then T8 (checkpoint).

- **2026-07-03** — **T7 LANDED** (`QIQTH/Tower/CornerEmbed.lean`, axiom-free std-3, budget 0):
  **cornerEmbed** (C ⊆ C′: act on the C-modes, identity on the complement; via
  sameOffSub/updOn/restrictMicro combinatorics) is a UNITAL ⋆-HOMOMORPHISM
  (cornerEmbed_one/_mul/_star/_add/_smul — the multiplicativity by the updOn fiber collapse of
  the intermediate index sum), MODE-COMPATIBLE (cornerEmbed_modeOp — C-mode operators go to the
  SAME upstairs mode operators), STATE-COMPATIBLE (cornerEmbed_stateOf — φ_{C′}∘ι = φ_C, the
  operator form of DY4's marginal via Finset.sum_fiberwise + marginal_gibbsWeight), and
  MODULAR-FLOW EQUIVARIANT (CAPSTONE **cornerEmbed_sigmaDiag** — σ_s^{C′}∘ι = ι∘σ_s^C, through
  the kappaOf eigen-law **kappaOf_gibbsWeight_of_sameOffSub**: the Gibbs log-weight difference
  of configurations agreeing off C is computed inside C — energy_sub_of_sameOffSub, the
  partition functions cancel). A FAMILY OF FINITE-DIMENSIONAL MAPS only — no inductive limit,
  weak closure, vN algebra or type claim (binding verdict); the ITPFI tower DATA exhibited,
  its classification cited at T3 (Araki–Woods 1968), never performed. NEXT → T8 (checkpoint:
  the campaign HAVE/HAVE-NOT sentences verbatim; delete the loop; stop).

- **2026-07-03** — **T8 LANDED — CAMPAIGN COMPLETE (8/8)** (`QIQTH/Tower/Checkpoint.lean`,
  checkpoint marker module, budget 0). The HAVE/HAVE-NOT sentences VERBATIM in the module
  docstring and the inventory. HAVE: "the machine-checked arithmetic content of the Araki–Woods
  III₁ criterion for the code's Gibbs tower, including a hypothesis-free concrete instance, the
  Powers-guard separation, the σ-additive infinite-mode Gibbs measure with its non-atomicity,
  and the state-compatible modular-equivariant finite refinement tower; the inference to an
  actual III₁ factor is cited (Araki–Woods 1968; Connes 1973), never proved." HAVE NOT: "the
  ITPFI von Neumann algebra, its ratio set, its type, any inductive limit or weak closure, any
  quantum state on the infinite system, or any continuum-limit completion — none are constructed
  or classified here." Loop 25f89281 deleted. Paper/website sync on request.
