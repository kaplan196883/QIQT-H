/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The momentum operator `P` as a symmetric unbounded operator (Stone generator of `τ_t`)

Applying the **general Stone generator** (`QIQTH/Spectral/Stone.lean`) to the translation group
`τ_t = translationLp t` on `L²(ℝ)` (the C₀ unitary group `e^{itP}`, `(τ_t f)(x) = f(x+t)`): its three Stone
hypotheses — the group law (`translationLp_add`), `τ_0 = 1` (`translationLp_zero`), and inner-product
preservation (`τ_t` a ℂ-linear isometry) — are all in hand. So the **momentum operator**
`P := stoneGen translationCLM = −i d/dt τ_t = −i d/dx` is a genuine *symmetric* unbounded operator
(`LinearPMap`) with the Cayley estimates, hence `P ± i` injective.

This is the second of the three C₀ groups the wall-campaign instantiates (the clock energy `X = A_edge` is the
first, `QIQTH/CrossedProductGenerator.lean`; the modular `Δ^{it}` is the third). Essential self-adjointness of
`P` (`Range(P ± i)` dense / Gårding density) is the carried analytic frontier — NOT claimed here. Axiom-free.

The `Lp`-elaboration friction (the `whnf`/`isDefEq` divergence on the `(stoneGen _).domain` projection through
the heavy `Lp`/`InnerProductSpace` instance tower) is handled by the same pattern as the clock energy:
`attribute [local irreducible] stoneGen stoneDomain` + explicit ambient `(H := Lp ℂ 2 volume)`.
-/
import QIQTH.Spectral.TranslationFlow
import QIQTH.Spectral.Stone
import QIQTH.Spectral.Garding
import QIQTH.Spectral.StoneExp
import Mathlib.MeasureTheory.Function.L2Space

namespace QIQTH.Spectral.Multiplication

open MeasureTheory QIQTH.Spectral

/-- `L²(ℝ)` is nontrivial (the indicator of `[0,1]` is a nonzero element) — needed for the continuous functional
    calculus instance on the Cayley unitary when instantiating the spectral generator identity. -/
noncomputable instance instNontrivialLp2 : Nontrivial (Lp ℂ 2 (volume : Measure ℝ)) := by
  have hμ : (volume : Measure ℝ) (Set.Icc 0 1) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  refine nontrivial_of_ne (indicatorConstLp 2 measurableSet_Icc hμ (1 : ℂ)) 0 ?_
  rw [← norm_ne_zero_iff, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one, Real.one_rpow,
    norm_one, mul_one]
  norm_num

/-- The translation operator `τ_t` on `L²(ℝ)` as a bounded ℂ-linear operator (the CLM form of the isometry
    `translationLp`) — the `U : ℝ → (H →L[ℂ] H)` input the general Stone generator consumes. -/
noncomputable def translationCLM (t : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (translationLp t).toContinuousLinearMap

@[simp] theorem translationCLM_apply (t : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    translationCLM t g = translationLp t g := rfl

/-- `τ_0 = 1`. -/
theorem translationCLM_zero :
    (translationCLM 0 : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) = 1 := by
  refine ContinuousLinearMap.ext fun g => ?_
  rw [translationCLM_apply, ContinuousLinearMap.one_apply, translationLp_zero]

/-- **The one-parameter group law** `τ_{s+t} = τ_s ∘L τ_t`. -/
theorem translationCLM_add (s t : ℝ) :
    (translationCLM (s + t) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
      = translationCLM s ∘L translationCLM t := by
  refine ContinuousLinearMap.ext fun g => ?_
  rw [ContinuousLinearMap.comp_apply, translationCLM_apply, translationCLM_apply, translationCLM_apply]
  exact (translationLp_add s t g).symm

/-- Inner-product preservation: `⟪τ_t a, τ_t b⟫ = ⟪a, b⟫` (`τ_t` a ℂ-linear isometry). The third Stone
    hypothesis (`hUinner`) for the translation group. -/
theorem translationCLM_inner (t : ℝ) (a b : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ (translationCLM t a) (translationCLM t b) : ℂ) = inner ℂ a b :=
  (translationLp t).inner_map_map a b

/-- `‖τ_t y‖ ≤ ‖y‖` — the contraction (in fact isometry) bound (`hUbd`) for the translation group. -/
theorem translationCLM_norm_le (t : ℝ) (y : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖translationCLM t y‖ ≤ ‖y‖ :=
  le_of_eq (by rw [translationCLM_apply]; exact norm_translationLp t y)

/-- `t ↦ τ_t y` is continuous — strong continuity (`hSC`) for the translation group. -/
theorem translationCLM_continuous (y : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous (fun t => translationCLM t y) := by
  simp only [translationCLM_apply]; exact continuous_translationLp y

attribute [local irreducible] QIQTH.Spectral.stoneGen QIQTH.Spectral.stoneDomain

/-- **★ The momentum operator `P`** = the (densely-definable) generator `−i d/dt τ_t = −i d/dx` of the
    translation group, as a `LinearPMap` on `L²(ℝ)`. -/
noncomputable def momentumOp :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  stoneGen translationCLM

/-- **★ The momentum operator is symmetric** — `P` is a formal adjoint of itself in Mathlib's `LinearPMap`
    framework (`P ⊆ P†` once its domain is dense). -/
theorem momentumOp_isFormalAdjoint_self :
    (stoneGen translationCLM).IsFormalAdjoint (stoneGen translationCLM) :=
  stoneGen_isFormalAdjoint_self (H := Lp ℂ 2 (volume : Measure ℝ)) translationCLM
    translationCLM_add translationCLM_zero translationCLM_inner

/-- **★ The Cayley estimate for the momentum operator** — `‖(P + i) x‖² = ‖P x‖² + ‖x‖²` on the smooth domain. -/
theorem momentumOp_norm_add_smul_I_sq (x : (stoneGen translationCLM).domain) :
    ‖stoneGen translationCLM x + Complex.I • (x : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2
      = ‖stoneGen translationCLM x‖ ^ 2 + ‖(x : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2 :=
  stoneGen_norm_add_smul_I_sq_dom (H := Lp ℂ 2 (volume : Measure ℝ)) translationCLM
    translationCLM_add translationCLM_zero translationCLM_inner x

/-- **★ `P + i` is bounded below** — `‖x‖ ≤ ‖(P + i) x‖`, so `P + i` is injective on the smooth domain (half
    the deficiency-index data; essential self-adjointness needs `Range(P ± i)` dense, the carried frontier). -/
theorem momentumOp_norm_le_norm_add_smul_I (x : (stoneGen translationCLM).domain) :
    ‖(x : Lp ℂ 2 (volume : Measure ℝ))‖
      ≤ ‖stoneGen translationCLM x + Complex.I • (x : Lp ℂ 2 (volume : Measure ℝ))‖ :=
  stoneGen_norm_le_norm_add_smul_I_dom (H := Lp ℂ 2 (volume : Measure ℝ)) translationCLM
    translationCLM_add translationCLM_zero translationCLM_inner x

/-- **★★★ The momentum operator `P` is self-adjoint:** `IsSelfAdjoint (stoneGen translationCLM)`. The generic
    `stoneGen_isSelfAdjoint` instantiated for the translation group `τ_t = e^{itP}` (group law, `τ_0 = 1`,
    unitarity `translationCLM_inner`, the isometry `norm_translationLp`, strong continuity
    `continuous_translationLp`). So `P = −i d/dx` is a genuine self-adjoint unbounded operator. -/
theorem momentumOp_isSelfAdjoint : IsSelfAdjoint (stoneGen translationCLM) :=
  stoneGen_isSelfAdjoint (H := Lp ℂ 2 (volume : Measure ℝ)) translationCLM
    translationCLM_add translationCLM_zero translationCLM_inner
    translationCLM_norm_le translationCLM_continuous

/- **CHECKPOINT — instantiating the direct generator identity `stoneGen_cfc_h_mul` for `translationCLM`** (so that
   `P (cfc(h·ψ) V z) = cfc(i(1+ω)/2·ψ) V z`, the explicit spectral form of `P = −i d/dx`) is blocked on the documented
   `Lp` elaboration friction: the `cfc`-on-the-`Lp`-Cayley-unitary subtype `⟨cfc φ V z, cfc_h_mul_mem_stoneDomain …⟩`
   produces a `↑↑(cayleyUnitary …)` double-coercion that does not unify with the membership proof's form through the
   heavy `Lp`/`InnerProductSpace` instance tower (the same `whnf`/`isDefEq` divergence the `[local irreducible]`
   pattern handles for `stoneGen`/`stoneDomain`, but here it reaches into `cfc`/`cayleyUnitary`).  The named hypotheses
   `translationCLM_norm_le`/`translationCLM_continuous` and the `Nontrivial L²` instance above are the prerequisites,
   now in place; the instantiation itself is the carried (purely-plumbing) gap — the abstract identity
   `QIQTH.Spectral.stoneGen_cfc_h_mul` is proven and axiom-free. -/

end QIQTH.Spectral.Multiplication
