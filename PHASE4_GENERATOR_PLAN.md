# The Wall, Phase 4 — the clock energy `X` (the area edge operator `A_edge`) via the generator of `λ_t`

**Status:** PLAN (not started). **Track:** GR / continuum (campaign Phase 4 of `P4_WALL_CAMPAIGN_PLAN.md`).
**Goal:** extract the **clock energy** `X` — the (unbounded, self-adjoint) generator of the clock translation
group `λ_t = clockTransl t` (Phase 2) — and identify it as the **area edge operator** `A_edge := X` (up to the
`1/4ℓ_P²` normalization, the cited UV datum).  This is the operator whose expectation the trace (Phase 5) turns
into the area term of the generalized entropy.

## 0. HONEST FRONTIER WARNING (read first)
Phase 4 is the **genuine research frontier** — most of it cannot be built without operator-algebra
infrastructure Mathlib does not have.  Specifically: **Stone's theorem** (a strongly-continuous one-parameter
unitary group `↔` a self-adjoint generator with `U_t = e^{itX}`) is **absent from Mathlib**, and it is the only
route to `X` as a self-adjoint operator.  Mathlib *does* have unbounded densely-defined operators with adjoints
(`LinearPMap` + `IsSelfAdjoint`, in `Analysis/InnerProductSpace/LinearPMap.lean`), so the *target type* exists —
but the group→generator step (Stone) does not.  **Expect this phase to deliver the tractable down-payment (4.1)
and then honestly checkpoint at the Stone wall (4.2).**  No `1/4` is ever claimed.  Axiom-free.

## 1. What Mathlib has vs lacks
- **Has:** `LinearPMap` (densely-defined unbounded maps `E →ₗ.[𝕜] F`), `LinearPMap.adjoint`, `IsSelfAdjoint`
  for them (`Analysis/InnerProductSpace/LinearPMap.lean`); the bounded clock group `λ_t` (Phase 2, strongly
  continuous, isometric, group law); `clockTransl_coeFn` (`(λ_t ξ)(s) = ξ(s+t)`); calculus (`HasDerivAt`),
  Bochner `L²(ℝ;H)`.
- **Lacks (the wall):** **Stone's theorem**, the infinitesimal-generator API, unbounded-self-adjoint spectral
  theorem, `e^{itX}` for unbounded `X`.  (Same continuum-TT frontier flagged throughout; cf. `K = −log Δ` in
  JLMS Stage 1, also gated on this.)

## 2. Sub-steps — `QIQTH/CrossedProductGenerator.lean`

### 4.1 — the clock-energy at the FORM / strong-derivative level  *(the tractable down-payment)*
Avoid the unbounded operator; work with the **clock energy expectation** on smooth vectors.
- For `ξ` with a strong `L²`-derivative of the flow (`HasDerivAt (fun t => clockTransl t ξ) (Xξ) 0`), define the
  clock-energy form `⟨ξ, X ξ⟩ := -i · ⟪ξ, (d/dt λ_t ξ)|₀⟫` (the generator's expectation, the modular/clock energy).
- The reality/sign structure: for a unitary group `d/dt⟪ξ,λ_t ξ⟫|₀ = i⟪ξ, Xξ⟩` is purely imaginary (the modular
  energy is real) — mirrors the JLMS-Stage-1 sign lemmas (`kFn` sign).
- Concretely on `L²(ℝ;H)`: `(d/dt λ_t ξ)|₀ = ξ'` (the `L²` derivative), so `X = −i d/ds` (momentum) — the clock
  energy density.  Deliver the form for `ξ` in a dense smooth domain; this is the *expectation* of `A_edge`.
**Risk: high** (the `L²(ℝ;H)` strong derivative + dense smooth domain is real analysis friction; may itself need
sub-breaking or hit a Bochner-calculus gap — checkpoint honestly if so).

### 4.2 — Stone's theorem: `X` self-adjoint, `λ_t = e^{itX}`  *(FRONTIER — Mathlib gap)*
Build/cite Stone's theorem to promote the form/generator (4.1) to a **self-adjoint `LinearPMap`** `X` with
`clockTransl t = exp(it X)`.  **This is the multi-week–multi-month Mathlib-grade build** (closed densely-defined
operators, Cayley transform, the unbounded spectral theorem).  Honest expectation: **record as the cited frontier**
unless a tractable special-case route (translation-on-`L²(ℝ)` via Fourier/Plancherel — `X` = multiplication by
frequency) turns out lighter; if so, pursue that.

### 4.3 — `A_edge := X` (the area edge operator)  *(gated on 4.2)*
Define `A_edge := X` (the clock energy = the area edge operator, up to the carried `1/4ℓ_P²` normalization),
and the dressed modular generator `K̃ = K + X`.  Gated on 4.2 (and on `K` as an operator, JLMS Stage 1's own
frontier).  The geometric identification `⟨A_edge⟩ = A(∂R)` and the `1/4` stay the cited UV datum — NOT claimed.

## 3. Honest deliverable
Realistically: the **clock-energy expectation/form** (4.1) — the down-payment on `A_edge` — with **Stone's
theorem (4.2) and the self-adjoint operator `X` recorded as the cited frontier** (Mathlib gap).  This is the
phase where the campaign meets the genuine operator-algebra wall; the value is the form-level handle on the
clock energy plus a precise, honest map of exactly what infrastructure is missing.

## 4. Verification (per sub-step)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.CrossedProductGenerator` green; `#print axioms` = standard 3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per
sub-step with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; refresh.

## Progress log
- (none yet — Sub-step 4.1 next; honest checkpoint at the Stone wall expected at 4.2)
