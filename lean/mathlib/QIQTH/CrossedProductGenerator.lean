/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Wall, Phase 4.1 — strong continuity of the clock group `λ_t`

Toward the clock energy `X` = the generator of `λ_t = clockTransl t` (see `PHASE4_GENERATOR_PLAN.md`), the first
(tractable) step is **strong continuity**: `t ↦ λ_t ξ` is continuous in `L²(ℝ;H)` for each `ξ`.  With the group
law + isometry (Phase 2), this completes "`λ_t` is a **strongly-continuous one-parameter unitary group**" — the
exact hypothesis of **Stone's theorem**, which would then yield `X` (the next, frontier step).

Built from Mathlib's `Lp.ContinuousAt.compMeasurePreservingLp` (continuity of `L^p`-composition with a
continuously-varying measure-preserving map) — the varying map being translation `(· + t)`, continuous into
`C(ℝ,ℝ)` as the curry of continuous addition.  Bounded operators only; Stone (`X` as a self-adjoint operator)
is the cited frontier.  Axiom-free.
-/
import QIQTH.CrossedProductTranslation
import QIQTH.Spectral.Stone
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space

namespace QIQTH.StandardSubspaceModular

open MeasureTheory QIQTH.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Translation `t ↦ (· + t)` as a continuous family `ℝ → C(ℝ,ℝ)` (the curry of continuous addition). -/
noncomputable def translMap : C(ℝ, C(ℝ, ℝ)) :=
  ContinuousMap.curry ⟨fun p : ℝ × ℝ => p.2 + p.1, by fun_prop⟩

@[simp] theorem translMap_apply (t x : ℝ) : translMap t x = x + t := rfl

/-- **★ Phase 4.1 — strong continuity of the clock group.**  `t ↦ λ_t ξ` is continuous in `L²(ℝ;H)`.  With the
    group law (`clockTransl_add`) and isometry (`clockTransl_norm`), `λ_t` is a strongly-continuous one-parameter
    unitary group — Stone's theorem hypothesis (the generator `X` is the next, frontier, step). -/
theorem clockTransl_stronglyContinuous (ξ : Lp H 2 (volume : Measure ℝ)) :
    Continuous (fun t => clockTransl t ξ) := by
  have hg : Continuous (fun t : ℝ => translMap t) := translMap.continuous
  refine continuous_iff_continuousAt.2 fun t => ?_
  have key : ContinuousAt
      (fun t => Lp.compMeasurePreserving (translMap t) (measurePreserving_addRight_volume t) ξ) t :=
    ContinuousAt.compMeasurePreservingLp continuousAt_const hg.continuousAt
      (fun t => measurePreserving_addRight_volume t) (by simp)
  exact key

/-! ### Phase 4.3 (operator) — the clock energy `X` as a symmetric unbounded operator

Applying the **general Stone scaffolding** (`QIQTH/Spectral/Stone.lean`) to the strongly-continuous unitary
group `λ_t = clockTransl t`: its three Stone hypotheses are now all in hand — the group law
(`clockTransl_add`), `λ_0 = 1` (`clockTransl_zero`), and inner-product preservation
(`clockTransl_inner`, below, from `λ_t` being a ℂ-linear isometry). This realizes the **clock energy**
`X := stoneGen clockTransl = −i d/dt λ_t` as a genuine *symmetric* unbounded operator (`LinearPMap`) with the
Cayley estimates, hence `X ± i` injective. `X` (its closure) is the operator the campaign calls `A_edge`.

Essential self-adjointness of `X` — needed before Stone returns `λ_t = exp(itX)` and before the dual-weight
trace — requires the Gårding density of the smooth domain (`Range(X ± i)` dense), the carried analytic
frontier (Phase 3.3); it is NOT claimed here. The 1/4 ratio is derived (`SakharovRatio`); the value of `G` /
the edge normalization `⟨A_edge⟩ = A/4ℓ_P²` is never claimed. -/

/-- **★ `λ_t` preserves the inner product:** `⟪λ_t a, λ_t b⟫ = ⟪a, b⟫` (it is a ℂ-linear isometry). This is
    the third Stone hypothesis (`hUinner`) for `clockTransl` — the genuinely *unitary* statement of the clock
    group (diamond-free, unlike the `star`/adjoint form): with `clockTransl_add` (group law) and
    `clockTransl_zero` (`λ_0 = 1`), the three hypotheses of the general Stone generator are now all in hand. -/
theorem clockTransl_inner (t : ℝ) (a b : Lp H 2 (volume : Measure ℝ)) :
    (inner ℂ (clockTransl t a) (clockTransl t b) : ℂ) = inner ℂ a b :=
  (Lp.compMeasurePreservingₗᵢ ℂ (· + t) (measurePreserving_addRight_volume t)).inner_map_map a b

/-! ### Phase 4.3 (operator) — the clock energy `X` as a symmetric unbounded operator

With `clockTransl_add` (group law), `clockTransl_zero` (`λ_0 = 1`), and `clockTransl_inner` (unitarity) all in
hand, the strongly-continuous unitary group `λ_t` satisfies the three hypotheses of the **general Stone
generator** (`QIQTH/Spectral/Stone.lean`). The clock energy `X := stoneGen clockTransl = −i d/dt λ_t` is the
(densely-definable) generator; here we land it as a genuine **symmetric** unbounded operator (`LinearPMap`),
and `X ± i` injective via the Cayley estimates. Its closure is the campaign's `A_edge`.

**The `Lp`-elaboration wall (now cracked for these statements):** forming `stoneGen clockTransl` at the concrete
`Lp H 2 volume` type makes the elaborator `whnf`-unfold the `LinearPMap.domain` projection through the heavy
`Lp`/`InnerProductSpace` instance tower → `isDefEq`/`whnf` divergence (the Phase-1.1/1.3 friction). Fixed by
`attribute [local irreducible] stoneGen stoneDomain` (so the projection is not unfolded) + pinning the ambient
space `(H := Lp H 2 volume)` explicitly. Essential self-adjointness of `X` — needed before Stone returns
`λ_t = exp(itX)` — still requires `Range(X ± i)` dense (Gårding density), the carried analytic frontier (NOT
claimed). The 1/4 ratio is derived (`SakharovRatio`); `⟨A_edge⟩ = A/4ℓ_P²` (value of `G`) is never claimed. -/

attribute [local irreducible] QIQTH.Spectral.stoneGen QIQTH.Spectral.stoneDomain

/-- **★ Phase 4.3 — the clock energy `X`** = the (densely-definable) generator `−i d/dt λ_t` of the clock
    translation group, as a `LinearPMap` on `L²(ℝ;H)`. Its closure is the campaign's `A_edge`. -/
noncomputable def clockEnergy :
    (Lp H 2 (volume : Measure ℝ)) →ₗ.[ℂ] (Lp H 2 (volume : Measure ℝ)) :=
  stoneGen clockTransl

/-- **★ The clock energy is symmetric** — `X = stoneGen clockTransl` is a formal adjoint of itself in
    Mathlib's `LinearPMap` framework (`X ⊆ X†` once its domain is dense), the concrete instantiation of the
    general `stoneGen_isFormalAdjoint_self` for the clock group. -/
theorem clockEnergy_isFormalAdjoint_self :
    (stoneGen (clockTransl (H := H))).IsFormalAdjoint (stoneGen clockTransl) :=
  stoneGen_isFormalAdjoint_self (H := Lp H 2 (volume : Measure ℝ)) clockTransl
    clockTransl_add clockTransl_zero clockTransl_inner

/-- **★ The Cayley estimate for the clock energy** — `‖(X + i) x‖² = ‖X x‖² + ‖x‖²` on the smooth domain. -/
theorem clockEnergy_norm_add_smul_I_sq (x : (stoneGen (clockTransl (H := H))).domain) :
    ‖stoneGen (clockTransl (H := H)) x + Complex.I • (x : Lp H 2 (volume : Measure ℝ))‖ ^ 2
      = ‖stoneGen (clockTransl (H := H)) x‖ ^ 2 + ‖(x : Lp H 2 (volume : Measure ℝ))‖ ^ 2 :=
  stoneGen_norm_add_smul_I_sq_dom (H := Lp H 2 (volume : Measure ℝ)) (clockTransl (H := H))
    clockTransl_add clockTransl_zero clockTransl_inner x

/-- **★ `X + i` is bounded below** — `‖x‖ ≤ ‖(X + i) x‖`, so `X + i` is injective on the smooth domain (half
    the deficiency-index data; essential self-adjointness needs `Range(X ± i)` dense, the carried frontier). -/
theorem clockEnergy_norm_le_norm_add_smul_I (x : (stoneGen (clockTransl (H := H))).domain) :
    ‖(x : Lp H 2 (volume : Measure ℝ))‖
      ≤ ‖stoneGen (clockTransl (H := H)) x + Complex.I • (x : Lp H 2 (volume : Measure ℝ))‖ :=
  stoneGen_norm_le_norm_add_smul_I_dom (H := Lp H 2 (volume : Measure ℝ)) (clockTransl (H := H))
    clockTransl_add clockTransl_zero clockTransl_inner x

end QIQTH.StandardSubspaceModular
