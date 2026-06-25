# The Wall, Phase 2 — the translation (clock) unitary group `λ_t` on `L²(ℝ;H)`

**Status:** PLAN (not started). **Track:** GR / continuum (campaign Phase 2 of `P4_WALL_CAMPAIGN_PLAN.md`).
**Goal:** build the **clock translation group** `λ_t : L²(ℝ;H) →L[ℂ] L²(ℝ;H)` — the `L²(ℝ)` clock factor of the
crossed product `M ⋊_σ ℝ`, and (with `modUnitary`) the *second* half of the covariant representation (Phase 3).
This bundles Mathlib's `Lp.compMeasurePreserving` translation action into a **continuous ℂ-linear unitary group**.

## 0. Scope (stated up front)
Bounded operators only.  `λ_t` is the unitary GROUP; its (unbounded) generator `X` = the **clock energy**
(`= c·A_edge`) is **Phase 4** (Stone's theorem) — *not* this phase.  No `1/4` coefficient, no trace.  Axiom-free.

## 1. The Mathlib API (verified)
On `Lp E p μ` (here `E = H`, `p = 2`, `μ = volume` on `ℝ`):
- `Lp.compMeasurePreserving (f) (hf : MeasurePreserving f μ μ) : Lp E p μ →+ Lp E p μ` — precomposition
  `ξ ↦ ξ ∘ f`, an **AddMonoidHom** (`coeFn_compMeasurePreserving : compMeasurePreserving f hf g =ᵐ g ∘ f`).
- `Lp.norm_compMeasurePreserving` + `Lp.isometry_compMeasurePreserving [Fact (1 ≤ p)] hf` — it's an **isometry**.
- `Lp.compMeasurePreserving_id : compMeasurePreserving id .id = AddMonoidHom.id`.
- `Lp.compMeasurePreserving_comp : compMeasurePreserving (f ∘ f') (hf.comp hf')
   = (compMeasurePreserving f' hf').comp (compMeasurePreserving f hf)` — the **group law** (contravariant;
   harmless: translations on `ℝ` commute, so the resulting unitary group is fine).
- translation `(· + t) : ℝ → ℝ` is measure-preserving for `volume` (`measurePreserving_add_right` / Haar
  left-invariance of `volume`).
There is **no** ready CLM / `LinearIsometryEquiv` form — Phase 2 supplies the bundling.

## 2. Sub-steps (each axiom-free, green-building, one commit) — `QIQTH/CrossedProductTranslation.lean`

### 2.1 — `clockTransl t : L²(ℝ;H) →L[ℂ] L²(ℝ;H)` (the bundling)
Define `clockTransl t` from `Lp.compMeasurePreserving (· + t) (htmp t)` (`htmp t : MeasurePreserving (· + t)
volume volume`).  Bundle the `AddMonoidHom` to a ℂ-linear CLM:
- **ℂ-linearity** `clockTransl t (c • ξ) = c • clockTransl t ξ` — via `coeFn` (`compMeasurePreserving g =ᵐ g∘f`
  + `Lp.coeFn_smul`, both `=ᵐ c • (ξ∘(·+t))`), assembling a `LinearMap` (`map_add'` from the AddMonoidHom,
  `map_smul'` from this).
- **continuity / norm** from `Lp.isometry_compMeasurePreserving` (isometry ⟹ Lipschitz-1) — bundle via
  `LinearMap.mkContinuous … 1 (norm bound)` or `LinearIsometry.toContinuousLinearMap`.
- `clockTransl_coeFn : clockTransl t ξ =ᵐ fun s => ξ (s + t)` and `‖clockTransl t ξ‖ = ‖ξ‖`.
**Risk: medium** (the `AddMonoidHom`→`CLM` bundling + the `map_smul` `coeFn` argument).

### 2.2 — the one-parameter group law
- `clockTransl_zero : clockTransl 0 = 1` (`compMeasurePreserving_id` + `(· + 0) = id`).
- `clockTransl_add : clockTransl (s + t) = clockTransl s ∘L clockTransl t` (from `compMeasurePreserving_comp`
  with `(· + s) ∘ (· + t) = (· + (s + t))`, using `add_comm`/`add_assoc`; translations commute).
**Risk: low** (the API gives it; just thread the measure-preserving composition).

### 2.3 — unitarity
- `clockTransl_isometry`/`norm` (from 2.1).
- `clockTransl_unitary : clockTransl t ∈ unitary (…)` — equivalently `adjoint (clockTransl t) = clockTransl (-t)`
  and `clockTransl t ∘L clockTransl (-t) = 1` (from the group law `clockTransl_add` at `t + (-t) = 0`).  The
  inverse is `clockTransl (-t)`, so `λ_t` is a **unitary** (isometry + surjective).
**Risk: low–medium** (the adjoint = inverse step may meet the same `Lp`/`RCLike` adjoint-instance diamond seen in
Phase 1's `*`; if so, deliver `λ_t ∘L λ_{-t} = 1 = λ_{-t} ∘L λ_t` (two-sided inverse ⟹ unitary for an isometry)
without the explicit `adjoint`, and record the diamond — not a math gap).

## 3. Honest deliverable
The clock translation **unitary group** `λ_t` on `L²(ℝ;H)` — bounded, with `λ_0 = 1`, `λ_{s+t} = λ_s λ_t`,
isometric, invertible (`λ_{-t}`).  This is the `L²(ℝ)` clock factor; together with `matterRep` (Phase 1) it is
the data for Phase 3's covariance `λ_t π(a) λ_{-t} = π(σ_t a)`.  The clock ENERGY `X` (generator) is Phase 4.

## 4. Verification (per sub-step)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.CrossedProductTranslation` green; `#print axioms` = standard 3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per
sub-step with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; refresh.

## Progress log
- **Sub-step 2.1 ✅** (`QIQTH/CrossedProductTranslation.lean`) — `clockTransl t : L²(ℝ;H) →L[ℂ] L²(ℝ;H)`,
  `(λ_t ξ)(s) = ξ(s+t)`, built from Mathlib's **`Lp.compMeasurePreservingₗᵢ ℂ`** (a ready ℂ-linear isometry —
  no hand-rolled `map_smul`), with `clockTransl_apply`, `clockTransl_coeFn` (`λ_t ξ =ᵐ fun s => ξ(s+t)`), and
  `clockTransl_norm` (isometry `‖λ_t ξ‖ = ‖ξ‖`). `measurePreserving_addRight_volume` (translation is volume-MP).
  Axiom-free (std 3); wired into AxiomAudit; budget 0. *(The `compMeasurePreservingₗᵢ` form sidestepped the
  AddMonoidHom→CLM bundling entirely — Phase 2.1 was a clean one-shot.)*
- **NEXT: Sub-step 2.2** — the group law `clockTransl 0 = 1`, `clockTransl (s+t) = clockTransl s ∘L clockTransl t`
  (via `Lp.compMeasurePreserving_comp`/`_id`; the dependent measure-preserving proofs + the function
  decomposition `(·+(s+t)) = (·+t)∘(·+s)` need care, or the `coeFn` + `ae_eq_comp` route). Then 2.3 (unitarity).
