/-
  GeodesicJointFDerivLipschitz — Lipschitz-in-base-point of the JOINT geodesic-flow Fréchet derivative
  map `ξ₀ ↦ L(ξ₀)` (plan `tranquil-stargazing-fox.md`, Task B).

  MOTIVATION.
  `GeodesicJointFDerivAtPoint.geodesicFlow_joint_hasFDerivAt_exists_atPoint` (Task A) produces, for each
  base point `ξ₀`, the joint first-order Fréchet derivative `L(ξ₀)` of the geodesic flow endpoint
  `fun ξ => W ξ t`, characterised by `L(ξ₀) ξ = V_{ξ₀} ξ t` where `V_{ξ₀} ξ` is the Jacobi field along the
  reference geodesic `W ξ₀` seeded at `ξ`.  The neighborhood-quality `ContDiffOn ℝ 1` upgrade (Task C)
  needs this derivative map to vary CONTINUOUSLY — indeed LIPSCHITZ — in the base point `ξ₀`.  This file
  supplies exactly that operator-norm Lipschitz bound, by combining two already-banked two-point Grönwall
  engines with no new geometric input.

  METHOD — the two-level Grönwall combination the plan sketched, entirely from banked engines.
  For two base points with reference geodesics `Y₁ = W ξ₀`, `Y₂ = W ξ₀'`, the difference of the two
  derivative maps applied to a common seed `ξ` is the two-point difference of two Jacobi fields with the
  SAME seed along the two different reference curves:
    `(L(ξ₀) − L(ξ₀')) ξ = V₁ ξ t − V₂ ξ t`.
  Bounding it needs the coefficient-field separation `‖DF(Y₁ τ) − DF(Y₂ τ)‖`, which the banked
  `SecondVariationLipschitz.fderiv_geodesicField_twopoint_dist_bound` supplies as
  `Lg·e^{Kg}·dist(Y₁ 0, Y₂ 0)` via a TWO-LEVEL Grönwall (base-curve Grönwall
  `geodesic_twopoint_gronwall` on the two reference geodesics, then the mean-value Lipschitz control of
  `fderiv (geodesicField)` on the compact convex phase set).  Feeding that separation into the banked
  Jacobi two-point difference bound `BasepointJetModulus.jacobi_twopoint_diff_bound`, together with a
  single-field Jacobi growth bound `‖V₂ ξ τ‖ ≤ ‖ξ‖·e^{Kbd}` (a homogeneous linear Grönwall, `jacobi_field_norm_bound` below), gives the per-seed pointwise bound
    `‖(L(ξ₀) − L(ξ₀')) ξ‖ ≤ Lg·e^{Kg}·e^{Kbd}·e^{Kbd}·dist(Y₁ 0, Y₂ 0)·‖ξ‖`,
  which `ContinuousLinearMap.opNorm_le_bound` turns into the operator-norm Lipschitz bound.

  WHAT LANDS HERE (axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `jacobi_field_norm_bound` — the homogeneous single-field Grönwall growth bound
    `‖J τ‖ ≤ ‖J 0‖·e^{K}` for a linear ODE `J' = A·J` with `‖A τ‖ ≤ K` on `[0,1]`.

  * `geodesicFlow_joint_fderiv_lipschitz_in_basepoint` — the abstract operator-norm Lipschitz bound
    `‖L₁ − L₂‖ ≤ Lg·e^{Kg}·e^{Kbd}·e^{Kbd}·dist(Y₁ 0, Y₂ 0)` for the two Task-A derivative maps `L₁, L₂`
    based at the two reference geodesics `Y₁, Y₂` (with Jacobi families `V₁, V₂` seeded at `ξ`).

  * `geodesicFlow_joint_fderiv_lipschitz_in_basepoint_compact` — the concrete-facing corollary that
    DISCHARGES the two Lipschitz moduli `Kg, Lg` and the coefficient bound `Kbd` from `IsCompact S`,
    `Convex ℝ S`, and the smoothness `hC` of the Christoffel symbols (via
    `geodesicField_lipschitzOnWith_of_isCompact_convex`, `fderiv_geodesicField_lipschitzOnWith_of_isCompact_convex`, and `geodesicField_fderiv_bddOn_compact`), leaving only the geodesic/Jacobi
    ODE data (exactly Task A's supplied data) as hypotheses.  Delivers `∃ C ≥ 0, ‖L₁ − L₂‖ ≤ C·dist(Y₁ 0, Y₂ 0)`.

  HONEST CHECKPOINT (binding).  This is the operator-norm Lipschitz dependence of the JOINT first-order
  derivative map on the base point — the missing continuity ingredient for the Task-C `ContDiffOn ℝ 1`
  upgrade.  The base points, reference geodesics `Y₁, Y₂`, Jacobi families `V₁, V₂`, and derivative CLMs
  `L₁, L₂` are supplied as hypotheses at exactly the same abstraction level as Task A (they are Task A's
  own supplied data at two nearby base points).  It does NOT itself wire `Y₁/Y₂/V₁/V₂` to the concrete
  `uniformFlowExp` (that is Task C's job — feed `uniformFlowTube`'s spec lemmas plus the concrete Jacobi
  families here), NOT upgrade to `ContDiffOn`/`ContDiffAt`, NOT build the second-order jet, and does NOT
  by itself discharge `hCConv`.
-/
import Mathlib
import QIQTH.BasepointJetModulus
import QIQTH.SecondVariationLipschitz
import QIQTH.BoundedGeometry
import QIQTH.GeodesicJointFDerivAtPoint

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 400000

variable {n : ℕ}

/-- **Homogeneous single-field Grönwall growth bound.**  For a solution `J` of a linear ODE
    `J' = A·J` on `[0,1]` whose coefficient is bounded `‖A τ‖ ≤ K` (`K ≥ 0`), the norm grows at most
    exponentially: `‖J τ‖ ≤ ‖J 0‖·e^{K}` for all `τ ∈ [0,1]`.  Mathlib's homogeneous Grönwall
    (`norm_le_gronwallBound_of_norm_deriv_right_le` with `ε = 0`, `δ = ‖J 0‖`) then `gronwallBound δ K 0 τ
    = δ·e^{K τ} ≤ δ·e^{K}` (since `K τ ≤ K`).  This is the linear-in-seed Jacobi-field bound consumed by
    the two-point difference estimate below. -/
theorem jacobi_field_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → (E →L[ℝ] E)} {J : ℝ → E} {K : ℝ} (hK0 : 0 ≤ K)
    (hJ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt J (A τ (J τ)) τ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖A τ‖ ≤ K) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ ‖J 0‖ * Real.exp K := by
  have hcont : ContinuousOn J (Set.Icc 0 1) :=
    fun s hs => (hJ s hs).continuousAt.continuousWithinAt
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := J) (f' := fun s => A s (J s)) (δ := ‖J 0‖) (K := K) (ε := 0) (a := 0) (b := 1)
    hcont
    (fun x hx => (hJ x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
    le_rfl
    (fun x hx => by
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      calc ‖A x (J x)‖ ≤ ‖A x‖ * ‖J x‖ := (A x).le_opNorm _
        _ ≤ K * ‖J x‖ := mul_le_mul_of_nonneg_right (hKb x hx') (norm_nonneg _)
        _ = K * ‖J x‖ + 0 := by ring)
  intro τ hτ
  refine (hmain τ hτ).trans ?_
  rw [sub_zero]
  have heq : gronwallBound ‖J 0‖ K 0 τ = ‖J 0‖ * Real.exp (K * τ) := by
    simp only [gronwallBound]
    split_ifs with h
    · subst h; simp
    · rw [zero_div, zero_mul, add_zero]
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_of_le_one_right hK0 hτ.2)) (norm_nonneg _)

/-- **Lipschitz-in-base-point of the joint geodesic-flow Fréchet derivative map (abstract).**
    Let `Y₁, Y₂` be two reference geodesics (integral curves of the geodesic field on `[0,1]`) staying in
    a phase set `S` on which `geodesicField` is `Kg`-Lipschitz and `fderiv (geodesicField)` is
    `Lg`-Lipschitz, with the coefficient bound `‖fderiv(gf)(Yᵢ τ)‖ ≤ Kbd` along both.  Let `V₁, V₂` be the
    two Jacobi families along `Y₁, Y₂` respectively (`Vᵢ' = DF(Yᵢ)·Vᵢ`, `Vᵢ ξ 0 = ξ`), and `L₁, L₂` the
    Task-A endpoint derivative CLMs (`Lᵢ ξ = Vᵢ ξ t`).  Then
      `‖L₁ − L₂‖ ≤ Lg·e^{Kg}·e^{Kbd}·e^{Kbd}·dist(Y₁ 0, Y₂ 0)`.

    PROOF — the two-level Grönwall combination:
    `fderiv_geodesicField_twopoint_dist_bound` gives the coefficient-field separation
    `‖DF(Y₁ τ) − DF(Y₂ τ)‖ ≤ Lg·e^{Kg}·dist(Y₁ 0, Y₂ 0)` (base-curve Grönwall + mean-value Lipschitz);
    `jacobi_twopoint_diff_bound` (fed that separation, the coefficient bound `Kbd` along `Y₁`, and the
    single-field growth bound `‖V₂ ξ τ‖ ≤ ‖ξ‖·e^{Kbd}` from `jacobi_field_norm_bound`) gives the per-seed
    bound `‖V₁ ξ t − V₂ ξ t‖ ≤ Lg·e^{Kg}·dist·(‖ξ‖·e^{Kbd})·e^{Kbd}`; `opNorm_le_bound` concludes. -/
theorem geodesicFlow_joint_fderiv_lipschitz_in_basepoint
    (g gi : Point n → Fin n → Fin n → ℝ)
    {S : Set (Point n × Point n)} {Kg Lg : ℝ≥0}
    (hLip : LipschitzOnWith Kg (geodesicField g gi) S)
    (hLip2 : LipschitzOnWith Lg (fderiv ℝ (geodesicField g gi)) S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {Y₁ Y₂ : ℝ → Point n × Point n}
    (h1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (geodesicField g gi (Y₁ τ)) τ)
    (h2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (geodesicField g gi (Y₂ τ)) τ)
    (hS1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y₁ τ ∈ S)
    (hS2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y₂ τ ∈ S)
    {Kbd : ℝ} (hKbd0 : 0 ≤ Kbd)
    (hKb1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y₁ τ)‖ ≤ Kbd)
    (hKb2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y₂ τ)‖ ≤ Kbd)
    {V₁ V₂ : Point n × Point n → ℝ → Point n × Point n}
    (hV1ode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V₁ ξ) (fderiv ℝ (geodesicField g gi) (Y₁ τ) (V₁ ξ τ)) τ)
    (hV2ode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V₂ ξ) (fderiv ℝ (geodesicField g gi) (Y₂ τ) (V₂ ξ τ)) τ)
    (hV10 : ∀ ξ : Point n × Point n, V₁ ξ 0 = ξ)
    (hV20 : ∀ ξ : Point n × Point n, V₂ ξ 0 = ξ)
    {L₁ L₂ : (Point n × Point n) →L[ℝ] Point n × Point n}
    (hL1eq : ∀ ξ : Point n × Point n, L₁ ξ = V₁ ξ t)
    (hL2eq : ∀ ξ : Point n × Point n, L₂ ξ = V₂ ξ t) :
    ‖L₁ - L₂‖ ≤ (Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd * dist (Y₁ 0) (Y₂ 0) := by
  -- coefficient-field separation via the banked two-level Grönwall.
  have hD0 := fderiv_geodesicField_twopoint_dist_bound g gi hLip hLip2 h1 h2 hS1 hS2
  -- single-field growth bound for the second Jacobi family (linear in the seed).
  have hJb2 : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖V₂ ξ τ‖ ≤ ‖ξ‖ * Real.exp Kbd := by
    intro ξ τ hτ
    have hb := jacobi_field_norm_bound hKbd0 (hV2ode ξ) hKb2 τ hτ
    rwa [hV20 ξ] at hb
  -- per-seed two-point Jacobi difference, packaged as an operator bound.
  have hper : ∀ ξ : Point n × Point n, ‖(L₁ - L₂) ξ‖ ≤
      ((Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd * dist (Y₁ 0) (Y₂ 0)) * ‖ξ‖ := by
    intro ξ
    rw [ContinuousLinearMap.sub_apply, hL1eq ξ, hL2eq ξ]
    have h0 : V₁ ξ 0 = V₂ ξ 0 := by rw [hV10 ξ, hV20 ξ]
    have hdiff := jacobi_twopoint_diff_bound g gi hKbd0
      (Y₁ := Y₁) (Y₂ := Y₂) (J₁ := V₁ ξ) (J₂ := V₂ ξ)
      (K := (Kbd : ℝ)) (Dcoef := (Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0))
      (Jb := ‖ξ‖ * Real.exp Kbd)
      (hV1ode ξ) (hV2ode ξ) h0 hKb1 hD0 (fun τ hτ => hJb2 ξ τ hτ) t ht
    calc ‖V₁ ξ t - V₂ ξ t‖
        ≤ ((Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0)) * (‖ξ‖ * Real.exp Kbd) * Real.exp Kbd :=
          hdiff
      _ = ((Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd * dist (Y₁ 0) (Y₂ 0)) * ‖ξ‖ := by
          ring
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ hper
  have hLgnn : (0 : ℝ) ≤ (Lg : ℝ) := NNReal.coe_nonneg Lg
  have hdnn : (0 : ℝ) ≤ dist (Y₁ 0) (Y₂ 0) := dist_nonneg
  positivity

/-- **Lipschitz-in-base-point of the joint geodesic-flow Fréchet derivative map (concrete-facing).**
    The compact-set corollary of `geodesicFlow_joint_fderiv_lipschitz_in_basepoint`: given `IsCompact S`,
    `Convex ℝ S`, and the Christoffel smoothness `hC`, the two Lipschitz moduli `Kg, Lg` and the
    coefficient bound `Kbd` are all PRODUCED from compactness (`geodesicField_lipschitzOnWith_of_isCompact_convex`, `fderiv_geodesicField_lipschitzOnWith_of_isCompact_convex`,
    `geodesicField_fderiv_bddOn_compact`).  Leaves only the geodesic/Jacobi ODE data (Task A's supplied
    data at the two base points) as hypotheses, and delivers a single Lipschitz constant `C ≥ 0`:
      `‖L₁ − L₂‖ ≤ C·dist(Y₁ 0, Y₂ 0)`. -/
theorem geodesicFlow_joint_fderiv_lipschitz_in_basepoint_compact
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hScomp : IsCompact S) (hSconv : Convex ℝ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {Y₁ Y₂ : ℝ → Point n × Point n}
    (h1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (geodesicField g gi (Y₁ τ)) τ)
    (h2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (geodesicField g gi (Y₂ τ)) τ)
    (hS1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y₁ τ ∈ S)
    (hS2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y₂ τ ∈ S)
    {V₁ V₂ : Point n × Point n → ℝ → Point n × Point n}
    (hV1ode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V₁ ξ) (fderiv ℝ (geodesicField g gi) (Y₁ τ) (V₁ ξ τ)) τ)
    (hV2ode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V₂ ξ) (fderiv ℝ (geodesicField g gi) (Y₂ τ) (V₂ ξ τ)) τ)
    (hV10 : ∀ ξ : Point n × Point n, V₁ ξ 0 = ξ)
    (hV20 : ∀ ξ : Point n × Point n, V₂ ξ 0 = ξ)
    {L₁ L₂ : (Point n × Point n) →L[ℝ] Point n × Point n}
    (hL1eq : ∀ ξ : Point n × Point n, L₁ ξ = V₁ ξ t)
    (hL2eq : ∀ ξ : Point n × Point n, L₂ ξ = V₂ ξ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖L₁ - L₂‖ ≤ C * dist (Y₁ 0) (Y₂ 0) := by
  obtain ⟨Kbd, hKbd0, hbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScomp
  obtain ⟨Kg, hLip⟩ := geodesicField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  obtain ⟨Lg, hLip2⟩ := fderiv_geodesicField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  refine ⟨(Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd, ?_, ?_⟩
  · have hLgnn : (0 : ℝ) ≤ (Lg : ℝ) := NNReal.coe_nonneg Lg
    positivity
  · exact geodesicFlow_joint_fderiv_lipschitz_in_basepoint g gi hLip hLip2 ht h1 h2 hS1 hS2
      hKbd0 (fun τ hτ => hbd _ (hS1 τ hτ)) (fun τ hτ => hbd _ (hS2 τ hτ))
      hV1ode hV2ode hV10 hV20 hL1eq hL2eq

end QIQTH.ExpMap
