import Mathlib
import QIQTH.SecondVariationSupply
import QIQTH.DoubledFamilyLink
import QIQTH.DoubledVariationField
import QIQTH.JacobiDoubledFamily
import QIQTH.BoundedGeometry
import QIQTH.BoundedGeometryConfine

/-!
# (F3a) Lipschitz-in-basepoint bound for `fderiv (geodesicField)` along geodesic base curves

This file supplies the **`hAd`-shaped** binder of
`QIQTH.ExpMap.expMap_common_nondeg_radius_of_doubled_supply`
(`JacobiDoubledFamily.lean`): the Lipschitz-in-`q` control of the base-geodesic
`A`-operator `fderiv (geodesicField)` evaluated along two geodesic phase flows.

The engine is the composition of two standard estimates, both already available in the
substrate:

* the **two-point geodesic Grönwall bound** `geodesic_twopoint_gronwall`
  (`ExpMap.lean`, via Mathlib `dist_le_of_trajectories_ODE_of_mem`): two integral curves of the
  autonomous geodesic field that stay in a common set `S` on which the field is `K`-Lipschitz obey
  `dist (Y₁ τ) (Y₂ τ) ≤ dist (Y₁ 0) (Y₂ 0) · e^{K τ}`;

* the **mean-value Lipschitz bound** for `fderiv (geodesicField)` on the same compact convex `S`
  (`lipschitzOnWith_of_nnnorm_fderiv_le`, fed by `geodesicField_fderiv_bddOn_compact` and the
  continuity of `fderiv²(geodesicField)`).

Composing gives, on `[0,1]`,
`‖fderiv(gf)(Y₁ τ) − fderiv(gf)(Y₂ τ)‖ ≤ Lg · e^{Kg} · dist (Y₁ 0) (Y₂ 0)` —
exactly the `hAd` shape with `D₀ = Lg · e^{Kg}` once `Y₁ 0 = (q,v)`, `Y₂ 0 = (q',v)` are the two
base points (so `dist (Y₁ 0) (Y₂ 0) = dist q q'`).

Everything here is PROVED, no `sorry`; the two `LipschitzOnWith` producers are unconditional given a
compact convex phase set `S`, and the composition takes only genuine geodesic-ODE data.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

variable {n : ℕ}

/-- **`geodesicField` is Lipschitz on any compact convex phase set.**  Its Fréchet derivative is
    bounded on the compact `S` (`geodesicField_fderiv_bddOn_compact`), and the mean-value theorem on
    the convex `S` (`lipschitzOnWith_of_nnnorm_fderiv_le`) turns that bound into a Lipschitz modulus. -/
theorem geodesicField_lipschitzOnWith_of_isCompact_convex
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hS : IsCompact S) (hSc : Convex ℝ S) :
    ∃ Kg : ℝ≥0, LipschitzOnWith Kg (geodesicField g gi) S := by
  obtain ⟨Kb, hKb0, hbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hS
  refine ⟨⟨Kb, hKb0⟩, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => ((contDiff_geodesicField g gi hC).differentiable (by simp)).differentiableAt)
    (fun x hx => ?_) hSc
  exact_mod_cast hbd x hx

/-- **`fderiv (geodesicField)` is Lipschitz on any compact convex phase set.**  `geodesicField` is
    `C^∞`, so `fderiv (geodesicField)` is `C^∞` too, hence `fderiv² (geodesicField)` is continuous and
    bounded on the compact `S`; the mean-value theorem on the convex `S` converts that into a
    Lipschitz modulus for `fderiv (geodesicField)`. -/
theorem fderiv_geodesicField_lipschitzOnWith_of_isCompact_convex
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hS : IsCompact S) (hSc : Convex ℝ S) :
    ∃ Lg : ℝ≥0, LipschitzOnWith Lg (fderiv ℝ (geodesicField g gi)) S := by
  have hDf : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).fderiv_right le_top
  -- Bound the (real-valued, continuous) operator norm of `fderiv²(geodesicField)` on the compact `S`.
  have hcont : Continuous (fun x => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖) :=
    (hDf.continuous_fderiv (by simp)).norm
  obtain ⟨C, hCb⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (hDf.differentiable (by simp)).differentiableAt) (fun x hx => ?_) hSc
  have h : ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ max C 0 :=
    ((Real.le_norm_self _).trans (hCb x hx)).trans (le_max_left _ _)
  exact_mod_cast h

/-- **(F3a) — the `hAd`-shaped two-point Lipschitz bound for the base-geodesic `A`-operator.**

    If `Y₁, Y₂` are two integral curves of the autonomous geodesic field on `[0,1]` that both stay in
    a set `S` on which `geodesicField` is `Kg`-Lipschitz and `fderiv (geodesicField)` is
    `Lg`-Lipschitz, then along the whole interval
    `‖fderiv(gf)(Y₁ τ) − fderiv(gf)(Y₂ τ)‖ ≤ Lg · e^{Kg} · dist (Y₁ 0) (Y₂ 0)`.

    Proof: two-point geodesic Grönwall (`geodesic_twopoint_gronwall`) bounds the phase distance
    `dist (Y₁ τ) (Y₂ τ) ≤ dist (Y₁ 0) (Y₂ 0) · e^{Kg τ}`, and the `Lg`-Lipschitz control of
    `fderiv (geodesicField)` on `S` (`LipschitzOnWith.dist_le_mul`) turns that into the stated
    operator-norm bound (using `e^{Kg τ} ≤ e^{Kg}` since `τ ≤ 1`, `Kg ≥ 0`).

    This is exactly the `hAd` binder of `expMap_common_nondeg_radius_of_doubled_supply` with
    `D₀ := Lg · e^{Kg}` and `Ybase q v · := Y₁`, `Ybase q' v · := Y₂` (whence
    `dist (Y₁ 0) (Y₂ 0) = dist q q'` when the base points differ only in the phase basepoint slot). -/
theorem fderiv_geodesicField_twopoint_dist_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    {S : Set (Point n × Point n)} {Kg Lg : ℝ≥0}
    (hLip : LipschitzOnWith Kg (geodesicField g gi) S)
    (hLip2 : LipschitzOnWith Lg (fderiv ℝ (geodesicField g gi)) S)
    {Y₁ Y₂ : ℝ → Point n × Point n}
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t)
    (hS1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₁ t ∈ S)
    (hS2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₂ t ∈ S) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y₁ τ) - fderiv ℝ (geodesicField g gi) (Y₂ τ)‖
        ≤ (Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0) := by
  intro τ hτ
  -- Two-point geodesic Grönwall: phase distance controlled by the initial distance.
  have hg : dist (Y₁ τ) (Y₂ τ) ≤ dist (Y₁ 0) (Y₂ 0) * Real.exp ((Kg : ℝ) * τ) :=
    geodesic_twopoint_gronwall g gi hLip h1 h2 hS1 hS2 τ hτ
  -- `Lg`-Lipschitz control of `fderiv (geodesicField)` on `S`.
  have hlip2τ :
      ‖fderiv ℝ (geodesicField g gi) (Y₁ τ) - fderiv ℝ (geodesicField g gi) (Y₂ τ)‖
        ≤ (Lg : ℝ) * dist (Y₁ τ) (Y₂ τ) := by
    have h := hLip2.dist_le_mul (Y₁ τ) (hS1 τ hτ) (Y₂ τ) (hS2 τ hτ)
    rwa [dist_eq_norm] at h
  refine hlip2τ.trans ?_
  -- `e^{Kg τ} ≤ e^{Kg}` since `Kg τ ≤ Kg` (τ ≤ 1, Kg ≥ 0).
  have hexp : Real.exp ((Kg : ℝ) * τ) ≤ Real.exp Kg := by
    apply Real.exp_le_exp.mpr
    have : (Kg : ℝ) * τ ≤ (Kg : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hτ.2 (NNReal.coe_nonneg Kg)
    simpa using this
  calc (Lg : ℝ) * dist (Y₁ τ) (Y₂ τ)
      ≤ (Lg : ℝ) * (dist (Y₁ 0) (Y₂ 0) * Real.exp ((Kg : ℝ) * τ)) :=
        mul_le_mul_of_nonneg_left hg (NNReal.coe_nonneg Lg)
    _ ≤ (Lg : ℝ) * (dist (Y₁ 0) (Y₂ 0) * Real.exp Kg) := by
        apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg Lg)
        exact mul_le_mul_of_nonneg_left hexp dist_nonneg
    _ = (Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0) := by ring

end QIQTH.ExpMap
