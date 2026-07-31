/-
  AutonomousSmoothDep — first-order smooth dependence on the initial condition for a GENERAL
  autonomous C²-field on a normed space, via the repo's Grönwall residual machinery.

  This is the ABSTRACT engine that `QIQTH.ExpMap.geodesicVariation_exists` (and its unconditional
  form `geodesicVariation_exists_uncond`) is a special case of.  The J-b/J-c/J-27 findings established
  that the geodesic variation machinery is largely FIELD-AGNOSTIC: the C¹-dependence-on-IC argument
  uses only that the field is C¹/C² with a uniform quadratic Taylor remainder along the perturbed
  tube, NOT anything special about `geodesicField`.  This file extracts that content verbatim, with
  the concrete field `geodesicField g gi` replaced by an abstract `Φ : E → E` on a normed space `E`.

  MISSION (J4-35, the `(h3a)` foundation).  The (J) gate for compact-uniform local `a₁ = R/6` is
  isolated to the Fréchet-differentiability of the geodesic Jacobi SOLUTION OPERATOR w.r.t. its base
  initial condition.  Per the GPT-5.5 consult, this needs first-order SMOOTH DEPENDENCE for the
  DOUBLED tangent field `G(Y,V) = (F(Y), DF(Y)·V)` (F = geodesicField), one abstraction up from the
  existing specialization.  The reusable generalization built here applies directly to `G`.

  WHAT LANDS HERE (all axiom-clean, no `sorry`; only genuine field-regularity carried as honest
  hypotheses):

  * `autonomous_linVariation_residual_deriv` — the residual ODE `R' = DΦ(Y₁)·R + N`, `N` the
    first-order Taylor remainder of `Φ`, for the residual `R = (Y₂ − Y₁) − J` of two integral curves
    of `Φ` and any solution `J` of the linearized ODE.  Pure `HasDerivAt` algebra; abstract mirror of
    `expJet_linVariation_residual_deriv`.

  * `autonomousField_variation_residual_bound` — UNCONDITIONAL (given the ODEs and the norm bounds):
    if `‖DΦ(Y₁ t)‖ ≤ K` and `‖Φ(Y₂ t) − Φ(Y₁ t) − DΦ(Y₁ t)(Y₂ t − Y₁ t)‖ ≤ C` on `[0,1]`, then
    `‖Y₂ t − Y₁ t − J t‖ ≤ C·exp K`.  Abstract mirror of `geodesicVariation_residual_bound`.

  * `autonomousField_variation_exists` — the IC-derivative EXISTS and equals a supplied linearized-ODE
    solution `V`, i.e. `HasDerivAt (fun s => Y s t) (V t) 0`, under the UNIFORM QUADRATIC field
    remainder `‖Φ(Y s ·) − Φ(Y 0 ·) − DΦ(Y 0 ·)(Y s · − Y 0 ·)‖ ≤ Cn·s²`.  Abstract mirror of
    `geodesicVariation_exists`; this is the (h3a) foundation.

  * `autonomous_twopoint_gronwall` — the two-point flow-Lipschitz bound for `Φ`; abstract mirror of
    `geodesic_twopoint_gronwall`.

  * `autonomousField_hNb_discharge` / `autonomousField_variation_exists_uncond` — discharge the carried
    quadratic remainder from the field's C² bound (`decay_order_two_remainder_convex`, already fully
    abstract) + the two-point Grönwall, giving IC-derivative existence carrying only genuine field
    regularity: `Φ` differentiable and `DΦ` differentiable on a convex `S`, `‖∂²Φ‖ ≤ M₂`, `Φ` Lipschitz
    on `S`, `‖DΦ(Y 0 τ)‖ ≤ K`, tube containment `Y s τ ∈ S`, and the supplied linearized solution `V`.

  These are FAITHFUL GENERALIZATIONS of PROVEN theorems: no hypothesis equals the conclusion, and the
  only inputs carried are genuine autonomous-field regularity (the same data the geodesic versions
  ultimately reduce to).  Nothing here builds the second-order Jacobi equation, Raychaudhuri, or the
  heat-kernel coefficient `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GeodesicSmoothDep

namespace QIQTH.AutonomousDep

open Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The residual ODE for an abstract autonomous field.**  Let `Y₁ Y₂` be integral curves of
    `Φ : E → E` (`Y' = Φ ∘ Y`) and `J` any solution of the linearized ODE `J' = DΦ(Y₁)·J` along `Y₁`.
    Then the residual `R = (Y₂ − Y₁) − J` solves `R' = DΦ(Y₁)·R + N`, where
    `N = Φ(Y₂) − Φ(Y₁) − DΦ(Y₁)(Y₂ − Y₁)` is the first-order Taylor remainder of `Φ`.

    Pure `HasDerivAt` algebra: `(h2.sub h1).sub hJ` gives `R' = Φ(Y₂) − Φ(Y₁) − DΦ(Y₁)(J)`, which
    rearranges (by linearity of `DΦ(Y₁)`) into the inhomogeneous linear form.  Abstract mirror of
    `QIQTH.ExpMap.expJet_linVariation_residual_deriv`. -/
theorem autonomous_linVariation_residual_deriv (Φ : E → E)
    {Y₁ Y₂ J : ℝ → E} {t : ℝ}
    (h1 : HasDerivAt Y₁ (Φ (Y₁ t)) t)
    (h2 : HasDerivAt Y₂ (Φ (Y₂ t)) t)
    (hJ : HasDerivAt J (fderiv ℝ Φ (Y₁ t) (J t)) t) :
    HasDerivAt (fun τ => Y₂ τ - Y₁ τ - J τ)
      (fderiv ℝ Φ (Y₁ t) (Y₂ t - Y₁ t - J t)
        + (Φ (Y₂ t) - Φ (Y₁ t) - fderiv ℝ Φ (Y₁ t) (Y₂ t - Y₁ t))) t := by
  have hbase : HasDerivAt (fun τ => Y₂ τ - Y₁ τ - J τ)
      (Φ (Y₂ t) - Φ (Y₁ t) - fderiv ℝ Φ (Y₁ t) (J t)) t := (h2.sub h1).sub hJ
  have key : fderiv ℝ Φ (Y₁ t) (Y₂ t - Y₁ t - J t)
        + (Φ (Y₂ t) - Φ (Y₁ t) - fderiv ℝ Φ (Y₁ t) (Y₂ t - Y₁ t))
      = Φ (Y₂ t) - Φ (Y₁ t) - fderiv ℝ Φ (Y₁ t) (J t) := by
    rw [map_sub]; abel
  rw [key]; exact hbase

/-- **The residual Grönwall for an abstract autonomous field — UNCONDITIONAL given the ODEs and the
    norm bounds.**  For two integral curves `Y₁ Y₂` of `Φ` on `[0,1]` and any solution `J` of the
    linearized ODE along `Y₁` with residual vanishing at `0`, if the Jacobi coefficient is bounded
    `‖DΦ(Y₁ t)‖ ≤ K` and the first-order Taylor remainder is bounded
    `‖Φ(Y₂ t) − Φ(Y₁ t) − DΦ(Y₁ t)(Y₂ t − Y₁ t)‖ ≤ C` on `[0,1]`, then
    `‖Y₂ t − Y₁ t − J t‖ ≤ C·exp K` for all `t ∈ [0,1]`.

    Abstract mirror of `QIQTH.ExpMap.geodesicVariation_residual_bound`: `R` solves
    `R' = DΦ(Y₁)·R + N` (`autonomous_linVariation_residual_deriv`), so `‖R'‖ ≤ K‖R‖ + C`; Mathlib's
    inhomogeneous Grönwall with `R 0 = 0` gives `‖R t‖ ≤ gronwallBound 0 K C t ≤ C·exp K`. -/
theorem autonomousField_variation_residual_bound (Φ : E → E)
    {Y₁ Y₂ J : ℝ → E} {K C : ℝ} (hK0 : 0 ≤ K) (hC0 : 0 ≤ C)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (Φ (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (Φ (Y₂ t)) t)
    (hJ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt J (fderiv ℝ Φ (Y₁ t) (J t)) t)
    (h0 : Y₂ 0 - Y₁ 0 - J 0 = 0)
    (hKb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ Φ (Y₁ t)‖ ≤ K)
    (hNb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ (Y₂ t) - Φ (Y₁ t) - fderiv ℝ Φ (Y₁ t) (Y₂ t - Y₁ t)‖ ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Y₂ t - Y₁ t - J t‖ ≤ C * Real.exp K := by
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ => Y₂ τ - Y₁ τ - J τ)
        (fderiv ℝ Φ (Y₁ t) (Y₂ t - Y₁ t - J t)
          + (Φ (Y₂ t) - Φ (Y₁ t) - fderiv ℝ Φ (Y₁ t) (Y₂ t - Y₁ t))) t :=
    fun t ht => autonomous_linVariation_residual_deriv Φ (h1 t ht) (h2 t ht) (hJ t ht)
  have hcont : ContinuousOn (fun τ => Y₂ τ - Y₁ τ - J τ) (Set.Icc 0 1) :=
    fun t ht => ((key t ht).continuousAt).continuousWithinAt
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun τ => Y₂ τ - Y₁ τ - J τ)
    (f' := fun t => fderiv ℝ Φ (Y₁ t) (Y₂ t - Y₁ t - J t)
      + (Φ (Y₂ t) - Φ (Y₁ t) - fderiv ℝ Φ (Y₁ t) (Y₂ t - Y₁ t)))
    (δ := 0) (K := K) (ε := C) (a := 0) (b := 1)
    hcont
    (fun x hx => (key x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (by show ‖Y₂ 0 - Y₁ 0 - J 0‖ ≤ 0; rw [h0]; simp)
    (by
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      show ‖fderiv ℝ Φ (Y₁ x) (Y₂ x - Y₁ x - J x)
          + (Φ (Y₂ x) - Φ (Y₁ x) - fderiv ℝ Φ (Y₁ x) (Y₂ x - Y₁ x))‖
        ≤ K * ‖Y₂ x - Y₁ x - J x‖ + C
      refine (norm_add_le _ _).trans (add_le_add ?_ (hNb x hx'))
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hKb x hx') (norm_nonneg _))
  intro t ht
  refine (hmain t ht).trans ?_
  rw [sub_zero]
  exact QIQTH.ExpMap.gronwallBound_zero_le_exp K C t hK0 hC0 ht.1 ht.2

/-- **The IC-derivative EXISTS for an abstract autonomous field.**  Let `Y : ℝ → ℝ → E` be a
    one-parameter family of integral curves of `Φ` (`s` = variation parameter, second argument =
    time), with base IC perturbed linearly `Y s 0 − Y 0 0 = s·p`.  Let `V` solve the linearized ODE
    `V' = DΦ(Y 0)·V` along the base curve with `V 0 = p`.  If `‖DΦ(Y 0 τ)‖ ≤ K` and the field obeys the
    UNIFORM QUADRATIC Taylor remainder `‖Φ(Y s ·) − Φ(Y 0 ·) − DΦ(Y 0 ·)(Y s · − Y 0 ·)‖ ≤ Cn·s²` on
    `[0,1]`, then the IC-derivative of the flow at time `t` EXISTS and equals `V t`:
    `HasDerivAt (fun s => Y s t) (V t) 0`.

    Abstract mirror of `QIQTH.ExpMap.geodesicVariation_exists` (`(0,w)` ↦ `p`).  For each `s`,
    `J := s·V` is a linearized solution with `J 0 = s·p = Y s 0 − Y 0 0`, so the residual bound (with
    `C = Cn·s²`) gives `‖Y s t − Y 0 t − s·V t‖ ≤ Cn·s²·exp K = O(s²) = o(s)`, the little-o
    characterisation of the derivative.  `V` is supplied as a linearized-ODE solution (non-circular:
    the conclusion that this solution IS the IC-derivative is a genuinely different statement). -/
theorem autonomousField_variation_exists (Φ : E → E)
    {Y : ℝ → ℝ → E} {V : ℝ → E} {p : E}
    {K Cn : ℝ} (hK0 : 0 ≤ K) (hCn0 : 0 ≤ Cn) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Y s) (Φ (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt V (fderiv ℝ Φ (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = p)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • p)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ Φ (Y 0 τ)‖ ≤ K)
    (hNb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ (Y s τ) - Φ (Y 0 τ) - fderiv ℝ Φ (Y 0 τ) (Y s τ - Y 0 τ)‖ ≤ Cn * s ^ 2) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  have hbnd : ∀ s : ℝ, ‖Y s t - Y 0 t - s • V t‖ ≤ Cn * s ^ 2 * Real.exp K := by
    intro s
    have hJ : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun σ => s • V σ)
          (fderiv ℝ Φ (Y 0 τ) ((fun σ => s • V σ) τ)) τ := by
      intro τ hτ
      have hcs := (hVode τ hτ).const_smul s
      have he : s • fderiv ℝ Φ (Y 0 τ) (V τ) = fderiv ℝ Φ (Y 0 τ) (s • V τ) :=
        (map_smul (fderiv ℝ Φ (Y 0 τ)) s (V τ)).symm
      rw [he] at hcs
      exact hcs
    have h0 : Y s 0 - Y 0 0 - (fun σ => s • V σ) 0 = 0 := by
      simp only
      rw [hIC s, hV0]; abel
    have := autonomousField_variation_residual_bound Φ hK0
      (mul_nonneg hCn0 (sq_nonneg s)) (hYode 0) (hYode s) hJ h0 hKb (hNb s) t ht
    simpa using this
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set M : ℝ := Cn * Real.exp K with hMdef
  have hM0 : 0 ≤ M := mul_nonneg hCn0 (Real.exp_pos K).le
  rw [Metric.eventually_nhds_iff]
  refine ⟨c / (M + 1), by positivity, fun s hs => ?_⟩
  rw [dist_eq_norm, sub_zero] at hs
  have hrw : Cn * s ^ 2 * Real.exp K = M * ‖s‖ ^ 2 := by
    rw [hMdef]; rw [Real.norm_eq_abs, sq_abs]; ring
  have hkey : ‖Y s t - Y 0 t - s • V t‖ ≤ M * ‖s‖ ^ 2 := hrw ▸ hbnd s
  have hMs : M * ‖s‖ ≤ c := by
    have hlt : ‖s‖ * (M + 1) < c := (lt_div_iff₀ (by positivity)).mp hs
    nlinarith [norm_nonneg s, hM0]
  calc ‖Y s t - Y 0 t - s • V t‖
      ≤ M * ‖s‖ ^ 2 := hkey
    _ = (M * ‖s‖) * ‖s‖ := by ring
    _ ≤ c * ‖s‖ := mul_le_mul_of_nonneg_right hMs (norm_nonneg _)

/-- **Two-point flow-Lipschitz bound for an abstract autonomous field.**  If `Φ` is `K`-Lipschitz on
    `S` and `Y₁ Y₂` are integral curves of `Φ` on `[0,1]` staying in `S`, then
    `dist (Y₁ t) (Y₂ t) ≤ dist (Y₁ 0) (Y₂ 0)·exp(K t)`.  Abstract mirror of
    `QIQTH.ExpMap.geodesic_twopoint_gronwall` (direct application of Mathlib's
    `dist_le_of_trajectories_ODE_of_mem`). -/
theorem autonomous_twopoint_gronwall (Φ : E → E)
    {Y₁ Y₂ : ℝ → E} {S : Set E} {K : NNReal}
    (hLip : LipschitzOnWith K Φ S)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (Φ (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (Φ (Y₂ t)) t)
    (hS1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₁ t ∈ S)
    (hS2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₂ t ∈ S) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist (Y₁ t) (Y₂ t) ≤ dist (Y₁ 0) (Y₂ 0) * Real.exp (K * t) := by
  intro t ht
  have hmain := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ => Φ) (s := fun _ => S) (K := K)
    (f := Y₁) (g := Y₂) (a := 0) (b := 1) (δ := dist (Y₁ 0) (Y₂ 0))
    (fun t _ => hLip)
    (fun t ht => (h1 t ht).continuousAt.continuousWithinAt)
    (fun t ht => (h1 t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hS1 t (Set.Ico_subset_Icc_self ht))
    (fun t ht => (h2 t ht).continuousAt.continuousWithinAt)
    (fun t ht => (h2 t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hS2 t (Set.Ico_subset_Icc_self ht))
    le_rfl t ht
  simpa using hmain

/-- **Discharge of the carried quadratic remainder from the field's C² bound.**  Feeds the general
    convex-set second-order Taylor remainder (`QIQTH.ExpMap.decay_order_two_remainder_convex`, already
    fully abstract) and the two-point flow-Lipschitz bound (`autonomous_twopoint_gronwall`) into the
    `hNb` shape of `autonomousField_variation_exists`.

    Inputs (all genuine field regularity): `S` convex; `Φ` differentiable and `DΦ` differentiable on
    `S`; `‖∂²Φ‖ ≤ M₂` on `S`; `Φ` Lipschitz on `S`; the ODE `hYode`; the linear IC perturbation `hIC`;
    tube containment `hmem`.  Output: the uniform quadratic remainder with
    `Cn = M₂·(‖p‖·e^{K₀})²`. -/
theorem autonomousField_hNb_discharge (Φ : E → E)
    {Y : ℝ → ℝ → E} {p : E} {S : Set E}
    {M₂ : ℝ} {K₀ : NNReal} (hconv : Convex ℝ S)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ Φ x)
    (hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ Φ) x)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ Φ) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ Φ S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Y s) (Φ (Y s τ)) τ)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • p)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ (Y s τ) - Φ (Y 0 τ) - fderiv ℝ Φ (Y 0 τ) (Y s τ - Y 0 τ)‖
        ≤ (M₂ * (‖p‖ * Real.exp K₀) ^ 2) * s ^ 2 := by
  intro s τ hτ
  have htp := autonomous_twopoint_gronwall Φ hLip (hYode s) (hYode 0) (hmem s) (hmem 0) τ hτ
  have hd0 : dist (Y s 0) (Y 0 0) = |s| * ‖p‖ := by
    rw [dist_eq_norm, hIC s, norm_smul, Real.norm_eq_abs]
  have hexp : Real.exp ((K₀ : ℝ) * τ) ≤ Real.exp K₀ := by
    apply Real.exp_le_exp.mpr
    calc (K₀ : ℝ) * τ ≤ (K₀ : ℝ) * 1 := mul_le_mul_of_nonneg_left hτ.2 (NNReal.coe_nonneg K₀)
      _ = (K₀ : ℝ) := mul_one _
  have hLnn : 0 ≤ |s| * ‖p‖ * Real.exp K₀ := by positivity
  have hL : ‖Y s τ - Y 0 τ‖ ≤ |s| * ‖p‖ * Real.exp K₀ := by
    rw [← dist_eq_norm]
    calc dist (Y s τ) (Y 0 τ)
        ≤ dist (Y s 0) (Y 0 0) * Real.exp ((K₀ : ℝ) * τ) := htp
      _ = |s| * ‖p‖ * Real.exp ((K₀ : ℝ) * τ) := by rw [hd0]
      _ ≤ |s| * ‖p‖ * Real.exp K₀ := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hrem := QIQTH.ExpMap.decay_order_two_remainder_convex Φ M₂ hconv
    (fun x hx => hdiff x hx) (fun x hx => hdiff2 x hx) hbound2 (hmem s τ hτ) (hmem 0 τ hτ)
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ Φ) (Y 0 τ))) (hbound2 (Y 0 τ) (hmem 0 τ hτ))
  refine hrem.trans ?_
  have hsq : ‖Y s τ - Y 0 τ‖ ^ 2 ≤ (|s| * ‖p‖ * Real.exp K₀) ^ 2 := by
    have := mul_le_mul hL hL (norm_nonneg _) hLnn
    simpa [pow_two] using this
  calc M₂ * ‖Y s τ - Y 0 τ‖ ^ 2
      ≤ M₂ * (|s| * ‖p‖ * Real.exp K₀) ^ 2 := mul_le_mul_of_nonneg_left hsq hnn
    _ = M₂ * (‖p‖ * Real.exp K₀) ^ 2 * s ^ 2 := by
        have hrw : (|s| * ‖p‖ * Real.exp K₀) ^ 2 = s ^ 2 * (‖p‖ * Real.exp K₀) ^ 2 := by
          rw [mul_assoc, mul_pow, sq_abs]
        rw [hrw]; ring

/-- **The IC-derivative exists for an abstract autonomous field, with the quadratic remainder
    DISCHARGED.**  Plugging `autonomousField_hNb_discharge` into `autonomousField_variation_exists`
    gives `HasDerivAt (fun s => Y s t) (V t) 0`, carrying only genuine field regularity: `S` convex,
    `Φ` and `DΦ` differentiable on `S`, `‖∂²Φ‖ ≤ M₂` on `S`, `Φ` Lipschitz on `S`, `‖DΦ(Y 0 τ)‖ ≤ K`,
    tube containment, and the supplied linearized solution `V`.  Abstract mirror of
    `QIQTH.ExpMap.geodesicVariation_exists_uncond`, with `Cn = M₂·(‖p‖·e^{K₀})²`. -/
theorem autonomousField_variation_exists_uncond (Φ : E → E)
    {Y : ℝ → ℝ → E} {V : ℝ → E} {p : E}
    {S : Set E} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ Φ x)
    (hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ Φ) x)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ Φ) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ Φ S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Y s) (Φ (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt V (fderiv ℝ Φ (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = p)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • p)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ Φ (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ Φ) (Y 0 t))) (hbound2 (Y 0 t) (hmem 0 t ht))
  have hCn0 : 0 ≤ M₂ * (‖p‖ * Real.exp K₀) ^ 2 := mul_nonneg hnn (sq_nonneg _)
  exact autonomousField_variation_exists Φ hK0 hCn0 ht hYode hVode hV0 hIC hKb
    (autonomousField_hNb_discharge Φ hconv hdiff hdiff2 hbound2 hLip hYode hIC hmem)

end QIQTH.AutonomousDep
