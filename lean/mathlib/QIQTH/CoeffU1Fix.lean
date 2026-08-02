/-
  CoeffU1Fix — J4-108: the SOUND replacement of the (generically-false) `hCoeffU1` firewall of the
  `N = 1` van-Vleck capstone (J4-106) by a DISCHARGED `O(r)` coefficient bound at the shifted profile.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## The obstruction (J4-107 finding, Sol-confirmed).

  `hCoeffU1` — the `O(r²)` bound `|totalRadialO1_coeff g̃_q g̃⁻¹_q Θ u' v| ≤ C·rncRadialSq v` at the
  SHIFTED van-Vleck profile `u' = fun j => u (j+1)` — is **GENERICALLY FALSE**, because `∂_e w₁(0) ≠ 0`
  for the van-Vleck `u₁` (the transport ODE forces `2∂_e u₁(0) = ∂_e(T u₀)(0) ≠ 0`), so the
  `radialDeriv(w₁)` summand carries a nonvanishing `O(r)` linear part.  The `uniformCoeff_bound` route
  (J4-87), which needs `∂w₁(0)=0`, cannot discharge it.

  ## The sound route (this file).

  (L1)  `rncRadial_mul_gaussDdim_le_width` — the ODD-power absorption `r·G_c ≤ C·√τ·G_d` (`c<d`), via the
        width-ratio identity + the scalar `u·exp(−βu²) ≤ √(1/(2β))` (from `x·e^{−x} ≤ 1!` on the square).
  (L2)  `uniformCoeffLinear_bound` — the `O(r)` uniform coefficient bound (`uniformCoeff_bound`'s proof
        MINUS the flatness step: the `radialDeriv` term is bounded by the `C¹` sup directly, the other two
        summands are `O(r²) ⊆ O(r)` on the ball).  NO `hw0flat` needed.
  (L3a) `uniformResidualLinear_gaussian_bound_tau_narrow` — the `N = 0` narrow residual bound with an
        `O(r)` coefficient: `|R₀| ≤ (C₀ + C₁·(1/√τ))·G_{3/2}` (the `T1` term gains a `1/√τ` from L1).
  (L3)  `uniformResidualN1_narrow_mixed_restricted` — the `(0,t]`-restricted `N = 1` mixed residual bound:
        the `τ·R₀[u']` branch, via L3a, produces `(C₀'·τ + C₁'·√τ)·G`, folded on `(0,t]` (√τ ≤ 1+t) into
        the affine `(B₀ + B₁·τ)·G` shape.

  No `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WidthMarginEngine
import QIQTH.UniformCoeffBound
import QIQTH.OrderOneTower
import QIQTH.OrderOneGeometry
import QIQTH.CoeffBoundsN1

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### L1 — the odd-power (√τ) width-parametric absorption `r·G_c ≤ C·√τ·G_d`. -/

/-- **★ J4-108 (L1) — THE ODD-POWER WIDTH ABSORPTION.**  For `1 ≤ c < d` (here `0 < c < d`), `τ > 0`,
        `rncRadial v · gaussDdim (c·τ) v
           ≤ √(d/c)ⁿ · √(2cd/(d−c)) · √τ · gaussDdim (d·τ) v`.
    The `m = 1/2` companion of `rncRadialSq_pow_mul_gaussDdim_le_width` (A1): the width gap deposits
    `exp(−r²β/τ)` (`β = (d−c)/(4cd)`), and the scalar bound `(r·exp(−r²β/τ))² = (τ/(2β))·(y·e^{−y}) ≤
    τ/(2β)` (`y = 2r²β/τ`, `y·e^{−y} ≤ 1! = 1`) gives `r·exp(−r²β/τ) ≤ √(τ/(2β)) = √(2cd/(d−c))·√τ`. -/
theorem rncRadial_mul_gaussDdim_le_width {c d : ℝ} (hc : 0 < c) (hcd : c < d)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    rncRadial v * gaussDdim (c * τ) v
      ≤ Real.sqrt (d / c) ^ n * Real.sqrt (2 * c * d / (d - c))
          * Real.sqrt τ * gaussDdim (d * τ) v := by
  have hd : 0 < d := lt_trans hc hcd
  have hdc : 0 < d - c := by linarith
  rw [gaussDdim_width_ratio hc hd hτ v]
  set G := gaussDdim (d * τ) v with hG
  have hG0 : 0 ≤ G := gaussDdim_nonneg _ _
  set r := rncRadial v with hr
  have hr0 : 0 ≤ r := rncRadial_nonneg v
  set r2 := rncRadialSq v with hr2
  have hr20 : 0 ≤ r2 := rncRadialSq_nonneg v
  have hr2eq : r2 = r ^ 2 := by rw [hr, hr2, rncRadial_sq]
  set β := (d - c) / (4 * c * d) with hβ
  have hβ0 : 0 < β := div_pos hdc (by positivity)
  set A := r * Real.exp (-(r2 * β / τ)) with hA
  have hA0 : 0 ≤ A := mul_nonneg hr0 (Real.exp_pos _).le
  -- `A² = r2 · exp(−2r2β/τ)`.
  have hA2 : A ^ 2 = r2 * Real.exp (-(2 * r2 * β / τ)) := by
    rw [hA, mul_pow, ← hr2eq]
    congr 1
    rw [sq, ← Real.exp_add]; congr 1; ring
  set y := 2 * r2 * β / τ with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hr2y : r2 = y * τ / (2 * β) := by rw [hy]; field_simp
  have hA2' : A ^ 2 = (τ / (2 * β)) * (y * Real.exp (-y)) := by
    rw [hA2, hr2y]; ring
  have hyexp : y * Real.exp (-y) ≤ 1 := by
    have h := pow_mul_exp_neg_le_factorial hy0 1
    simpa using h
  have hA2le : A ^ 2 ≤ τ / (2 * β) := by
    rw [hA2']
    calc (τ / (2 * β)) * (y * Real.exp (-y))
        ≤ (τ / (2 * β)) * 1 := mul_le_mul_of_nonneg_left hyexp (by positivity)
      _ = τ / (2 * β) := mul_one _
  have hAle : A ≤ Real.sqrt (τ / (2 * β)) := by
    rw [← Real.sqrt_sq hA0]; exact Real.sqrt_le_sqrt hA2le
  have hsqrteq : Real.sqrt (τ / (2 * β)) = Real.sqrt τ * Real.sqrt (2 * c * d / (d - c)) := by
    rw [show τ / (2 * β) = τ * (2 * c * d / (d - c)) by rw [hβ]; field_simp; ring,
        Real.sqrt_mul hτ.le]
  calc r * (Real.sqrt (d / c) ^ n * Real.exp (-(r2 * β / τ)) * G)
      = Real.sqrt (d / c) ^ n * G * A := by rw [hA]; ring
    _ ≤ Real.sqrt (d / c) ^ n * G * (Real.sqrt τ * Real.sqrt (2 * c * d / (d - c))) :=
        mul_le_mul_of_nonneg_left (hAle.trans_eq hsqrteq) (mul_nonneg (by positivity) hG0)
    _ = Real.sqrt (d / c) ^ n * Real.sqrt (2 * c * d / (d - c)) * Real.sqrt τ * G := by ring

/-- L1 specialized to `(c,d) = (1, 3/2)`:  `r·G ≤ √(3/2)ⁿ·√6·√τ·G_{3/2}`. -/
theorem rncRadial_mul_gaussDdim_le_narrow {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    rncRadial v * gaussDdim τ v
      ≤ Real.sqrt (3 / 2) ^ n * Real.sqrt 6 * Real.sqrt τ * gaussDdim (3 / 2 * τ) v := by
  have h := rncRadial_mul_gaussDdim_le_width (c := 1) (d := 3 / 2) (by norm_num) (by norm_num) hτ v
  have e1 : (2 * (1 : ℝ) * (3 / 2) / (3 / 2 - 1)) = 6 := by norm_num
  have e2 : ((3 / 2) / (1 : ℝ)) = 3 / 2 := by norm_num
  rw [e1, e2, one_mul] at h
  exact h

/-! ### L2 — the `O(r)` uniform coefficient bound (`uniformCoeff_bound` MINUS flatness). -/

/-- **★ J4-108 (L2) — THE UNIFORM `O(r)` COEFFICIENT BOUND, NO FLATNESS.**  For ANY smooth folded
    leading coefficient `w₀ = foldedCoeff Θ u 0` (no `∂w₀(0)=0` assumed),
      `∃ ρ_c > 0, ∃ C_c ≥ 0, ∀ q ∈ K, ∀ v, ‖v‖ < ρ_c →
         |totalRadialO1_coeff g̃_q g̃⁻¹_q Θ u v| ≤ C_c · rncRadial v`.
    Identical to `uniformCoeff_bound` (J4-87) EXCEPT the flatness-dependent step is removed: the
    `radialDeriv(w₀) = Σ vᵢ ∂ᵢw₀` summand is bounded by the `C¹` sup `|∂ᵢw₀| ≤ Kw` DIRECTLY (giving the
    honest `O(r)` linear part `n·Kw·r`), and the two `O(r²)` summands (`coeffAF·w₀`, `coeffDevF`) are
    demoted to `O(r)` on the ball via `r² ≤ (√n·ρ_c)·r`.  This is the coefficient input the shifted
    van-Vleck profile `u'` supplies (its `∂w₁(0) ≠ 0` makes the `O(r²)` bound false).  NOT `a₁ = R/6`. -/
theorem uniformCoeffLinear_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0)) :
    ∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c : ℝ, 0 ≤ C_c ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c * rncRadial v := by
  classical
  obtain ⟨r_d, hr_d0, Md, hMd0, hdev⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform g gi hC hK hg hgnd hgsymm hinvF hframeK
  obtain ⟨r_e, hr_e0, Kg, hKg0, hGIb⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound g gi hg hC hK hgnd
  obtain ⟨r_Γ, hr_Γ0, KdΓ, hKdΓ0, hChb⟩ :=
    uniformFlowChristoffel_linear_decay g gi hg hC hK hgnd hgsymm hinvF hframeK
  set ρ_c : ℝ := min r_d (min r_e r_Γ) with hρ_c_def
  have hρ_c0 : 0 < ρ_c := lt_min hr_d0 (lt_min hr_e0 hr_Γ0)
  -- heat-side sups (NO flatness): `W = sup|w₀|`, `Kw = sup|∂w₀|` on the closed ball.
  obtain ⟨W, hW0, hWbd⟩ : ∃ W : ℝ, 0 ≤ W ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_c, |foldedCoeff Θ u 0 v| ≤ W := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_c).exists_bound_of_continuousOn
        hw0smooth.continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  obtain ⟨Kw, hKw0, hpdw⟩ : ∃ Kw : ℝ, 0 ≤ Kw ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_c, ∀ i : Fin n,
        |pd (foldedCoeff Θ u 0) i v| ≤ Kw := by
    have hcont : Continuous (fun w => ∑ i, |pd (foldedCoeff Θ u 0) i w|) :=
      continuous_finsetSum _
        (fun i _ => (contDiff_pd (foldedCoeff Θ u 0) hw0smooth i).continuous.abs)
    obtain ⟨C, hC'⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_c).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun v hvmem i => ?_⟩
    have hsum := hC' v hvmem
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at hsum
    calc |pd (foldedCoeff Θ u 0) i v|
        ≤ ∑ i', |pd (foldedCoeff Θ u 0) i' v| :=
          Finset.single_le_sum (f := fun i' => |pd (foldedCoeff Θ u 0) i' v|)
            (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ C := hsum
      _ ≤ max C 0 := le_max_left _ _
  set Caf : ℝ := (1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ with hCaf_def
  have hCaf0 : 0 ≤ Caf := by
    rw [hCaf_def]; positivity
  set Rmax : ℝ := Real.sqrt (n : ℝ) * ρ_c with hRmax_def
  have hRmax0 : 0 ≤ Rmax := by rw [hRmax_def]; positivity
  refine ⟨ρ_c, hρ_c0,
    Caf * W * Rmax + (n : ℝ) * Kw + (n : ℝ) ^ 2 * Md * Kw * ((n : ℝ) * ρ_c ^ 2), ?_, ?_⟩
  · positivity
  intro q hq v hv
  have hvd : ‖v‖ < r_d := lt_of_lt_of_le hv (min_le_left _ _)
  have hve : ‖v‖ < r_e := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvΓ : ‖v‖ < r_Γ := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_c := by
    rw [mem_closedBall_zero_iff]; exact hv.le
  have hvle : ‖v‖ ≤ ρ_c := hv.le
  unfold totalRadialO1_coeff radialDeriv
  set Gm : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetric g gi hC hK q with hGmdef
  set Gi : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetricInv g gi hC hK q with hGidef
  set w0 : Point n → ℝ := foldedCoeff Θ u 0 with hw0def
  have hGI : ∀ i j : Fin n, |Gi v i j| ≤ Kg := fun i j => hGIb q hq v hve i j
  have hdevv : ∀ i j : Fin n, |Gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v :=
    fun i j => hdev q hq v hvd i j
  have hΓv : ∀ k i j : Fin n, |christoffel Gm Gi k i j v| ≤ KdΓ * ‖v‖ :=
    fun k i j => hChb q hq v hvΓ k i j
  have hpdwv : ∀ i : Fin n, |pd w0 i v| ≤ Kw := hpdw v hvball
  have hWv : |w0 v| ≤ W := hWbd v hvball
  have hvi : ∀ i : Fin n, |v i| ≤ rncRadial v := fun i => abs_coord_le_rncRadial v i
  have hvnorm : ‖v‖ ≤ rncRadial v := norm_le_rncRadial v
  -- `r² = rncRadialSq v` bounds.
  have hrsq_bnd : rncRadialSq v ≤ (n : ℝ) * ρ_c ^ 2 := by
    have hsq : ∀ i : Fin n, (v i) ^ 2 ≤ ρ_c ^ 2 := by
      intro i
      have h1 : |v i| ≤ ρ_c := le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i) hvle
      nlinarith [sq_abs (v i), abs_nonneg (v i)]
    calc rncRadialSq v = ∑ i, (v i) ^ 2 := rfl
      _ ≤ ∑ _i : Fin n, ρ_c ^ 2 := Finset.sum_le_sum fun i _ => hsq i
      _ = (n : ℝ) * ρ_c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hRle : rncRadial v ≤ Rmax := by
    rw [rncRadial, hRmax_def]
    calc Real.sqrt (rncRadialSq v) ≤ Real.sqrt ((n : ℝ) * ρ_c ^ 2) := Real.sqrt_le_sqrt hrsq_bnd
      _ = Real.sqrt (n : ℝ) * ρ_c := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hρ_c0.le]
  have hrsq_r : rncRadialSq v ≤ Rmax * rncRadial v := by
    calc rncRadialSq v = rncRadial v * rncRadial v := by rw [← rncRadial_sq]; ring
      _ ≤ Rmax * rncRadial v := mul_le_mul_of_nonneg_right hRle (rncRadial_nonneg v)
  have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    have h := abs_add_le x (-y); rwa [← sub_eq_add_neg, abs_neg] at h
  -- (A1) diagonal-trace part.
  have hA1 : |(1 / 2) * (∑ i, (Gi v i i - 1))| ≤ (1 / 2) * (n : ℝ) * Md * rncRadialSq v := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, (Gi v i i - 1)| ≤ (n : ℝ) * Md * rncRadialSq v := by
      calc |∑ i, (Gi v i i - 1)| ≤ ∑ i, |Gi v i i - 1| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, Md * rncRadialSq v := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h := hdevv i i; simpa using h
        _ = (n : ℝ) * Md * rncRadialSq v := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc (1 / 2 : ℝ) * |∑ i, (Gi v i i - 1)|
        ≤ (1 / 2) * ((n : ℝ) * Md * rncRadialSq v) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (1 / 2) * (n : ℝ) * Md * rncRadialSq v := by ring
  -- (A2) Christoffel-contraction part.
  have hA2 : |(1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
      ≤ (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
        ≤ (n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖) := by
      calc |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
          ≤ ∑ i, ∑ j, ∑ k, |Gi v i j * christoffel Gm Gi k i j v * v k| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, Kg * (KdΓ * ‖v‖) * ‖v‖ := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul, abs_mul]
            refine mul_le_mul (mul_le_mul (hGI i j) (hΓv k i j) (abs_nonneg _) hKg0) ?_
              (abs_nonneg _) (mul_nonneg hKg0 (mul_nonneg hKdΓ0 (norm_nonneg _)))
            rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v k
        _ = (n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc (1 / 2 : ℝ) * |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
        ≤ (1 / 2) * ((n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ (1 / 2) * ((n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by positivity) hKg0) hKdΓ0)
          have h := norm_le_rncRadial v
          calc ‖v‖ * ‖v‖ ≤ rncRadial v * rncRadial v :=
                mul_le_mul h h (norm_nonneg _) (rncRadial_nonneg _)
            _ = rncRadialSq v := by rw [← rncRadial_sq]; ring
      _ = (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := by ring
  -- (TA) `coeffAF · w₀`, bounded `≤ Caf·W·Rmax·rncRadial v`.
  have hTA : |((1 / 2) * (∑ i, (Gi v i i - 1))
        - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)) * w0 v|
      ≤ Caf * W * Rmax * rncRadial v := by
    rw [abs_mul]
    have hAF : |(1 / 2) * (∑ i, (Gi v i i - 1))
          - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
        ≤ Caf * rncRadialSq v := by
      rw [hCaf_def]
      calc |(1 / 2) * (∑ i, (Gi v i i - 1))
              - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
          ≤ |(1 / 2) * (∑ i, (Gi v i i - 1))|
              + |(1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)| :=
            habs_sub _ _
        _ ≤ (1 / 2) * (n : ℝ) * Md * rncRadialSq v
              + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := add_le_add hA1 hA2
        _ = ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * rncRadialSq v := by ring
    calc |(1 / 2) * (∑ i, (Gi v i i - 1))
            - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)| * |w0 v|
        ≤ (Caf * rncRadialSq v) * W := mul_le_mul hAF hWv (abs_nonneg _)
          (mul_nonneg hCaf0 (rncRadialSq_nonneg v))
      _ ≤ (Caf * (Rmax * rncRadial v)) * W :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrsq_r hCaf0) hW0
      _ = Caf * W * Rmax * rncRadial v := by ring
  -- (TB) `radialDeriv(w₀) = Σ vᵢ ∂ᵢw₀`, the honest `O(r)` part.
  have hTB : |∑ i, v i * pd w0 i v| ≤ (n : ℝ) * Kw * rncRadial v := by
    calc |∑ i, v i * pd w0 i v| ≤ ∑ i, |v i * pd w0 i v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, rncRadial v * Kw := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hvi i) (hpdwv i) (abs_nonneg _) (rncRadial_nonneg v)
      _ = (n : ℝ) * Kw * rncRadial v := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- (TC) `coeffDevF`, `O(r³) ⊆ O(r)`.
  have hTC : |(1 / 2) * (∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd w0 j v + v j * pd w0 i v))|
      ≤ (n : ℝ) ^ 2 * Md * Kw * ((n : ℝ) * ρ_c ^ 2) * rncRadial v := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd w0 j v + v j * pd w0 i v)|
        ≤ (n : ℝ) ^ 2 * Md * Kw * 2 * rncRadialSq v * rncRadial v := by
      calc |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
              * (v i * pd w0 j v + v j * pd w0 i v)|
          ≤ ∑ i, ∑ j, (Md * rncRadialSq v) * (2 * (rncRadial v * Kw)) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul]
            refine mul_le_mul (hdevv i j) ?_ (abs_nonneg _)
              (mul_nonneg hMd0 (rncRadialSq_nonneg v))
            calc |v i * pd w0 j v + v j * pd w0 i v|
                ≤ |v i * pd w0 j v| + |v j * pd w0 i v| := abs_add_le _ _
              _ ≤ rncRadial v * Kw + rncRadial v * Kw := by
                  refine add_le_add ?_ ?_
                  · rw [abs_mul]
                    exact mul_le_mul (hvi i) (hpdwv j) (abs_nonneg _) (rncRadial_nonneg v)
                  · rw [abs_mul]
                    exact mul_le_mul (hvi j) (hpdwv i) (abs_nonneg _) (rncRadial_nonneg v)
              _ = 2 * (rncRadial v * Kw) := by ring
        _ = (n : ℝ) ^ 2 * Md * Kw * 2 * rncRadialSq v * rncRadial v := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc (1 / 2 : ℝ) * |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
            * (v i * pd w0 j v + v j * pd w0 i v)|
        ≤ (1 / 2) * ((n : ℝ) ^ 2 * Md * Kw * 2 * rncRadialSq v * rncRadial v) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = ((n : ℝ) ^ 2 * Md * Kw * rncRadial v) * rncRadialSq v := by ring
      _ ≤ ((n : ℝ) ^ 2 * Md * Kw * rncRadial v) * ((n : ℝ) * ρ_c ^ 2) :=
          mul_le_mul_of_nonneg_left hrsq_bnd
            (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMd0) hKw0) (rncRadial_nonneg v))
      _ = (n : ℝ) ^ 2 * Md * Kw * ((n : ℝ) * ρ_c ^ 2) * rncRadial v := by ring
  -- assemble.
  refine le_trans (abs_add_le _ _)
    (le_trans (add_le_add (abs_add_le _ _) (le_refl _))
      (le_trans (add_le_add (add_le_add hTA hTB) hTC) ?_))
  apply le_of_eq; ring

/-! ### L3a — the `N = 0` narrow residual bound with an `O(r)` coefficient. -/

/-- **★ J4-108 (L3a) — THE `N = 0` NARROW RESIDUAL BOUND, `O(r)` COEFFICIENT.**  The exact analogue of
    `WidthMarginEngine.uniformResidual_gaussian_bound_tau_narrow` but consuming an `O(r)` (LINEAR)
    coefficient bound `hCoeffLin` instead of the `O(r²)` one, and producing the correspondingly weakened
        `|parametrixResidualN 0 g̃_q g̃⁻¹_q Θ u τ v| ≤ (C₀ + C₁·(√τ/τ))·gaussDdim (3/2·τ) v`,   ∀ τ > 0.
    The `T1` term `(1/τ)·G·coeff` gains a `√τ/τ` from L1's odd-power absorption (`r·G ≤ √(3/2)ⁿ·√6·√τ·
    G_{3/2}`), replacing the bounded `C·G` of the `O(r²)` route; the `T2` (quadratic) and `T3` (Laplacian)
    terms are UNCHANGED (flatness-independent).  `C₀ = √(3/2)ⁿ·(72n²MW+L)`, `C₁ = C_c·√(3/2)ⁿ·√6`.  This
    is the shifted-profile branch's honest bound.  NOT `a₁ = R/6`. -/
theorem uniformResidualLinear_gaussian_bound_tau_narrow (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (ρ_c C_c : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c)
    (hCoeffLin : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c * rncRadial v) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
          ≤ (C₀ + C₁ * (Real.sqrt τ / τ)) * gaussDdim (3 / 2 * τ) v := by
  classical
  obtain ⟨rM, hrM0, M, hM0, hdevU⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform g gi hC hK hg hgnd hgsymm hinvF hframeK
  obtain ⟨rL, hrL0, L, hL0, hLapU⟩ :=
    uniformFlowLaplaceBeltrami_w0_near_uniform g gi hg hC hK hgnd Θ u hw0smooth
  set ρ_u : ℝ := min rM (min rL ρ_c) with hρ_u_def
  have hρ_u0 : 0 < ρ_u := lt_min hrM0 (lt_min hrL0 hρ_c)
  obtain ⟨W, hW0, hWbd⟩ : ∃ W : ℝ, 0 ≤ W ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_u, |foldedCoeff Θ u 0 v| ≤ W := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_u).exists_bound_of_continuousOn
        hw0smooth.continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  refine ⟨ρ_u, hρ_u0, Real.sqrt (3 / 2) ^ n * (72 * (n : ℝ) ^ 2 * M * W + L),
    C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6), by positivity, by positivity, ?_⟩
  intro τ hτ q hq v hv
  have hvM : ‖v‖ < rM := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL : ‖v‖ < rL := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvc : ‖v‖ < ρ_c := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hw0at : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := hw0smooth.contDiffAt.of_le le_top
  rw [parametrixResidual_N0_O1_isolated_C2 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw0at]
  set Gn : ℝ := gaussDdim (3 / 2 * τ) v with hGndef
  have hGnn0 : 0 ≤ Gn := gaussDdim_nonneg _ v
  have hGτ0 : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  set T1 : ℝ := (1 / τ) * gaussDdim τ v
      * totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v with hT1def
  set T2 : ℝ := (1 / τ ^ 2) * gaussDdim τ v
      * ((-1 / 4) * (∑ i, ∑ j, (uniformFlowPullbackMetricInv g gi hC hK q v i j
          - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
      * foldedCoeff Θ u 0 v with hT2def
  set T3 : ℝ := gaussDdim τ v * laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v with hT3def
  have hT1bd : |T1|
      ≤ (C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * (Real.sqrt τ / τ) * Gn := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)]
    have hdivmul : (1 / τ) * Real.sqrt τ = Real.sqrt τ / τ := by rw [one_div, inv_mul_eq_div]
    calc (1 / τ) * gaussDdim τ v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / τ) * gaussDdim τ v * (C_c * rncRadial v) :=
          mul_le_mul_of_nonneg_left (hCoeffLin q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)
      _ = C_c * (1 / τ) * (rncRadial v * gaussDdim τ v) := by ring
      _ ≤ C_c * (1 / τ) * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6 * Real.sqrt τ * Gn) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_c0 (one_div_nonneg.mpr hτ.le))
          rw [hGndef]; exact rncRadial_mul_gaussDdim_le_narrow hτ v
      _ = (C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * ((1 / τ) * Real.sqrt τ) * Gn := by ring
      _ = (C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * (Real.sqrt τ / τ) * Gn := by
          rw [hdivmul]
  have hT2bd : |T2| ≤ Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * Gn := by
    rw [hT2def, hGndef]
    exact residualQuadratic_pointwise_narrow (uniformFlowPullbackMetricInv g gi hC hK q) Θ u hτ M W
      hM0 hW0 v (hdevU q hq v hvM) (hWbd v hvball)
  have hT3bd : |T3| ≤ Real.sqrt (3 / 2) ^ n * L * Gn := by
    rw [hT3def, abs_mul, abs_of_nonneg hGτ0]
    calc gaussDdim τ v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim τ v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGτ0
      _ ≤ (Real.sqrt (3 / 2) ^ n * Gn) * L := by
          rw [hGndef]
          exact mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdim_narrow hτ v) hL0
      _ = Real.sqrt (3 / 2) ^ n * L * Gn := by ring
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ (C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * (Real.sqrt τ / τ) * Gn
          + Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * Gn
          + Real.sqrt (3 / 2) ^ n * L * Gn :=
        add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ = (Real.sqrt (3 / 2) ^ n * (72 * (n : ℝ) ^ 2 * M * W + L)
          + (C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * (Real.sqrt τ / τ)) * Gn := by ring

/-! ### L3 — the `N = 1` mixed residual bound with an `O(r)` shifted coefficient (the CORE). -/

/-- **★★ J4-108 (L3) — THE `N = 1` MIXED RESIDUAL BOUND, `O(r)` SHIFTED COEFFICIENT.**  The sound
    replacement of `OrderOneTower.uniformResidualN1_narrow_mixed`: the `O(r²)` coefficient input at the
    shifted profile (`hCoeffU1`, GENERICALLY FALSE) is replaced by the DISCHARGEABLE `O(r)` input
    `hCoeffLin1`, WITHOUT weakening the conclusion shape:
        `|parametrixResidualN 1 g̃_q g̃⁻¹_q Θ u τ v| ≤ (B₀ + B₁·τ)·gaussDdim (3/2·τ) v`,   ∀ τ > 0.
    ROUTE: the J4-103 split `R₁ = R₀[u] + H₀[u'] + τ·R₀[u']`; `R₀[u]` via the `O(r²)` narrow engine
    (`hCoeffU0`, constant `Cu`); `R₀[u']` via L3a (`hCoeffLin1`, `≤ (Cs₀ + Cs₁·√τ/τ)·G`); `H₀[u'] =
    gauss·w₁` dominated by `W₁·√(3/2)ⁿ·G`.  The `τ·R₀[u']` branch gives `(Cs₀·τ + Cs₁·√τ)·G`; the KEY is
    `√τ ≤ 1+τ` for **all** `τ ≥ 0` (⟺ `0 ≤ 1+τ+τ²`), so `Cs₁·√τ ≤ Cs₁ + Cs₁·τ` folds into the affine
    constants `B₀ := Cu + W₁√(3/2)ⁿ + Cs₁`, `B₁ := Cs₀ + Cs₁` — NO ceiling restriction needed.  Hence the
    output is SHAPE-IDENTICAL to `uniformResidualN1_narrow_mixed`, drop-in for the whole downstream chain.
    Genuine inputs: `hw`, `hCoeffU0` (`O(r²)` at `u`), `hCoeffLin1` (`O(r)` at `u'`).  NOT `a₁ = R/6`. -/
theorem uniformResidualN1_narrow_mixed_lin (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v)
    (hCoeffLin1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ B₀ B₁ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
          ≤ (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := by
  obtain ⟨ρ₀, hρ₀0, Cu, hCu0, hbnd0⟩ :=
    uniformResidual_gaussian_bound_tau_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ u (hw 0) ρ_c C_c0 hρ_c hC_c0 hCoeffU0
  obtain ⟨ρ₁, hρ₁0, Cs₀, Cs₁, hCs00, hCs10, hbnd1⟩ :=
    uniformResidualLinear_gaussian_bound_tau_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ (fun j => u (j + 1)) (hw 1) ρ_c C_c1 hρ_c hC_c1 hCoeffLin1
  set ρ_u : ℝ := min ρ₀ ρ₁ with hρ_u_def
  have hρ_u0 : 0 < ρ_u := lt_min hρ₀0 hρ₁0
  obtain ⟨W₁, hW₁0, hW₁bd⟩ : ∃ W₁ : ℝ, 0 ≤ W₁ ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_u, |foldedCoeff Θ u 1 v| ≤ W₁ := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_u).exists_bound_of_continuousOn
        (hw 1).continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  refine ⟨ρ_u, hρ_u0, Cu + W₁ * Real.sqrt (3 / 2) ^ n + Cs₁, Cs₀ + Cs₁,
    by positivity, by positivity, ?_⟩
  intro τ hτ q hq v hv
  have hv0 : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv1 : ‖v‖ < ρ₁ := lt_of_lt_of_le hv (min_le_right _ _)
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  rw [parametrixResidual_one_split (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw]
  set G : ℝ := gaussDdim (3 / 2 * τ) v with hGdef
  have hG0 : 0 ≤ G := gaussDdim_nonneg _ v
  set R0 : ℝ := parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v with hR0def
  set Mid : ℝ := heatParametrix 0 Θ (fun j => u (j + 1)) τ v with hMiddef
  set R0' : ℝ := parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) τ v with hR0'def
  have hb0 : |R0| ≤ Cu * G := hbnd0 τ hτ q hq v hv0
  have hb1 : |R0'| ≤ (Cs₀ + Cs₁ * (Real.sqrt τ / τ)) * G := hbnd1 τ hτ q hq v hv1
  have hmid : |Mid| ≤ (W₁ * Real.sqrt (3 / 2) ^ n) * G := by
    have hfold : Mid = gaussDdim τ v * foldedCoeff Θ (fun j => u (j + 1)) 0 v := by
      rw [hMiddef, heatParametrix_folded, Finset.sum_range_one, pow_zero, mul_one]
    rw [hfold, abs_mul, abs_of_nonneg (gaussDdim_nonneg τ v)]
    have hv' : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W₁ := hW₁bd v hvball
    calc gaussDdim τ v * |foldedCoeff Θ (fun j => u (j + 1)) 0 v|
        ≤ gaussDdim τ v * W₁ := mul_le_mul_of_nonneg_left hv' (gaussDdim_nonneg τ v)
      _ = W₁ * gaussDdim τ v := by ring
      _ ≤ W₁ * (Real.sqrt (3 / 2) ^ n * G) := by
          rw [hGdef]; exact mul_le_mul_of_nonneg_left (gaussDdim_le_gaussDdim_narrow hτ v) hW₁0
      _ = (W₁ * Real.sqrt (3 / 2) ^ n) * G := by ring
  -- `τ·R₀[u']` branch: `√τ ≤ 1+τ` for ALL `τ ≥ 0` folds the `√τ` tail into the affine shape.
  have hττ : τ * (Real.sqrt τ / τ) = Real.sqrt τ := by field_simp
  have hsqle : Real.sqrt τ ≤ 1 + τ := by
    rw [show (1 : ℝ) + τ = Real.sqrt ((1 + τ) ^ 2) from (Real.sqrt_sq (by linarith [hτ.le])).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hτ.le])
  have hb1τ : τ * |R0'| ≤ (Cs₀ * τ + Cs₁ * (1 + τ)) * G := by
    calc τ * |R0'|
        ≤ τ * ((Cs₀ + Cs₁ * (Real.sqrt τ / τ)) * G) := mul_le_mul_of_nonneg_left hb1 hτ.le
      _ = (Cs₀ * τ + Cs₁ * (τ * (Real.sqrt τ / τ))) * G := by ring
      _ = (Cs₀ * τ + Cs₁ * Real.sqrt τ) * G := by rw [hττ]
      _ ≤ (Cs₀ * τ + Cs₁ * (1 + τ)) * G := by
          apply mul_le_mul_of_nonneg_right _ hG0
          have := mul_le_mul_of_nonneg_left hsqle hCs10
          linarith
  calc |R0 + Mid + τ * R0'|
      ≤ |R0 + Mid| + |τ * R0'| := abs_add_le _ _
    _ ≤ (|R0| + |Mid|) + |τ * R0'| := add_le_add (abs_add_le _ _) le_rfl
    _ = (|R0| + |Mid|) + τ * |R0'| := by rw [abs_mul, abs_of_pos hτ]
    _ ≤ (Cu * G + (W₁ * Real.sqrt (3 / 2) ^ n) * G) + (Cs₀ * τ + Cs₁ * (1 + τ)) * G :=
        add_le_add (add_le_add hb0 hmid) hb1τ
    _ = ((Cu + W₁ * Real.sqrt (3 / 2) ^ n + Cs₁) + (Cs₀ + Cs₁) * τ) * G := by ring

/-! ### L4 — re-running the J4-106 chain with the `O(r)` shifted coefficient (the PAYOFF). -/

/-- **★ J4-108 (L4) — THE `N = 1` CUTOFF-RESIDUAL MIXED BOUND, `O(r)` SHIFTED COEFFICIENT.**  The exact
    `_lin` analogue of `OrderOneGeometry.cutoffResidualN1_uniformFlow_narrow_mixed_below`: identical
    proof, but the near-packet residual is supplied by L3 (`uniformResidualN1_narrow_mixed_lin`, consuming
    the `O(r)` `hCoeffLin1`) instead of the `O(r²)` `uniformResidualN1_narrow_mixed`.  Same MIXED output
    `(B₀ + B₁·τ)·gaussDdim (3/2·τ) v`.  NOT `a₁ = R/6`. -/
theorem cutoffResidualN1_uniformFlow_narrow_mixed_below_lin (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v)
    (hCoeffLin1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v)
    (ρc : ℝ) (hρc : 0 < ρc) :
    ∃ a b B₀ B₁ : ℝ, 0 < a ∧ a < b ∧ b < ρc ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n,
        |radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v|
          ≤ (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := by
  classical
  obtain ⟨ρ_u, hρ_u0, Bᵣ0, Bᵣ1, hBᵣ0, hBᵣ1, hResU1⟩ :=
    uniformResidualN1_narrow_mixed_lin g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1
  obtain ⟨rKg, hrKg0, Kg, hKg0, hGIann⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound_annulus g gi hg hC hK hgnd
  obtain ⟨rKc2, hrKc20, hLapAnn⟩ :=
    uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound g gi hg hC hK hgnd
  set bN : ℝ := ρ_u / 2 with hbN_def
  have hbN0 : 0 < bN := by rw [hbN_def]; linarith
  set rmin : ℝ := min rKg rKc2 with hrmin_def
  have hrmin0 : 0 < rmin := lt_min hrKg0 hrKc20
  set b : ℝ := min (min bN (rmin / 2)) (ρc / 2) with hb_def
  have hb0 : 0 < b := lt_min (lt_min hbN0 (by linarith)) (by linarith)
  have hb_nonneg : (0 : ℝ) ≤ b := le_of_lt hb0
  set a : ℝ := b / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  have hb_lt_ρc : b < ρc := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hb_le_bN : b ≤ bN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hb_lt_rmin : b < rmin :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  have hb_lt_rKg : b < rKg := lt_of_lt_of_le hb_lt_rmin (min_le_left _ _)
  have hb_lt_rKc2 : b < rKc2 := lt_of_lt_of_le hb_lt_rmin (min_le_right _ _)
  have hGIannK := hGIann a b hb_nonneg hb_lt_rKg
  obtain ⟨Kc2, hKc20, hLapChiU⟩ := hLapAnn a b hb_nonneg hb_lt_rKc2
  obtain ⟨Kc1, hKc10, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  obtain ⟨Kcof0, hKcof00, hHann0U⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b (foldedCoeff Θ u 0) (hw 0).continuous
  obtain ⟨Kcof1, hKcof10, hHann1U⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b (foldedCoeff Θ u 1) (hw 1).continuous
  obtain ⟨Kder0, hKder00, hDHann0U⟩ :=
    parametrixCofactor_deriv_annulus_narrow_tauUniform a b ha0 hb0 (foldedCoeff Θ u 0)
      (hw 0).continuous (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) (hw 0) i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) (hw 0) j).continuous)
  obtain ⟨Kder1, hKder10, hDHann1U⟩ :=
    parametrixCofactor_deriv_annulus_narrow_tauUniform a b ha0 hb0 (foldedCoeff Θ u 1)
      (hw 1).continuous (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 1) (hw 1) i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 1) (hw 1) j).continuous)
  set S32 : ℝ := Real.sqrt (3 / 2) ^ n with hS32_def
  have hS320 : 0 ≤ S32 := by positivity
  set B₀ : ℝ := Bᵣ0 + Kcof0 * S32 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder0 with hB0_def
  set B₁ : ℝ := Bᵣ1 + Kcof1 * S32 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder1 with hB1_def
  have hB0nn : 0 ≤ B₀ := by rw [hB0_def]; positivity
  have hB1nn : 0 ≤ B₁ := by rw [hB1_def]; positivity
  refine ⟨a, b, B₀, B₁, ha0, hab, hb_lt_ρc, hB0nn, hB1nn, ?_⟩
  intro τ hτ q hq v
  have hH1eq : (heatParametrix 1 Θ u τ : Point n → ℝ)
      = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y
          + τ * (gaussDdim τ y * foldedCoeff Θ u 1 y) := by
    funext y
    rw [heatParametrix_one_split Θ u τ y]
    have e0 : heatParametrix 0 Θ u τ y = gaussDdim τ y * foldedCoeff Θ u 0 y := by
      rw [heatParametrix_folded]; simp
    have e1 : heatParametrix 0 Θ (fun j => u (j + 1)) τ y
        = gaussDdim τ y * foldedCoeff Θ u 1 y := by
      rw [heatParametrix_folded]; simp [foldedCoeff_shift]
    rw [e0, e1]
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 1 Θ u τ) w :=
    fun w => (heatParametrix_contDiff_space 1 Θ u τ hw).contDiffAt.of_le le_top
  have hb_le_ρu2 : b ≤ ρ_u / 2 := hb_le_bN
  have hEnear_q : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
      |deriv (fun s => heatParametrix 1 Θ u s w) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 1 Θ u τ) w|
        ≤ (Bᵣ0 + Bᵣ1 * τ) * gaussDdim (3 / 2 * τ) w := by
    intro w hw2
    have hnw : ‖w‖ < ρ_u := by
      have h1 : ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
      have hb2 : rncRadialSq w ≤ (ρ_u / 2) ^ 2 := by
        refine le_trans hw2 ?_
        have := mul_le_mul hb_le_ρu2 hb_le_ρu2 hb_nonneg (by linarith)
        simpa [pow_two] using this
      have h2 : rncRadial w ≤ ρ_u / 2 := by
        rw [rncRadial]
        calc Real.sqrt (rncRadialSq w)
            ≤ Real.sqrt ((ρ_u / 2) ^ 2) := Real.sqrt_le_sqrt hb2
          _ = ρ_u / 2 := by rw [Real.sqrt_sq (by linarith)]
      linarith
    have hs := hResU1 τ hτ q hq w hnw
    simpa only [parametrixResidualN] using hs
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 1 Θ u τ w| ≤ ((Kcof0 + τ * Kcof1) * S32) * gaussDdim (3 / 2 * τ) w := by
    intro w h1 h2
    have hsplit : heatParametrix 1 Θ u τ w
        = gaussDdim τ w * foldedCoeff Θ u 0 w + τ * (gaussDdim τ w * foldedCoeff Θ u 1 w) := by
      rw [hH1eq]
    rw [hsplit]
    have hb0v := hHann0U τ hτ w h1 h2
    have hb1v := hHann1U τ hτ w h1 h2
    have hnarrow := gaussDdim_le_gaussDdim_narrow hτ w
    have hKsum : (0 : ℝ) ≤ Kcof0 + τ * Kcof1 := by positivity
    calc |gaussDdim τ w * foldedCoeff Θ u 0 w + τ * (gaussDdim τ w * foldedCoeff Θ u 1 w)|
        ≤ |gaussDdim τ w * foldedCoeff Θ u 0 w| + |τ * (gaussDdim τ w * foldedCoeff Θ u 1 w)| :=
          abs_add_le _ _
      _ = |gaussDdim τ w * foldedCoeff Θ u 0 w| + τ * |gaussDdim τ w * foldedCoeff Θ u 1 w| := by
          rw [abs_mul τ (gaussDdim τ w * foldedCoeff Θ u 1 w), abs_of_pos hτ]
      _ ≤ Kcof0 * gaussDdim τ w + τ * (Kcof1 * gaussDdim τ w) :=
          add_le_add hb0v (mul_le_mul_of_nonneg_left hb1v hτ.le)
      _ = (Kcof0 + τ * Kcof1) * gaussDdim τ w := by ring
      _ ≤ (Kcof0 + τ * Kcof1) * (S32 * gaussDdim (3 / 2 * τ) w) :=
          mul_le_mul_of_nonneg_left hnarrow hKsum
      _ = ((Kcof0 + τ * Kcof1) * S32) * gaussDdim (3 / 2 * τ) w := by rw [hS32_def]; ring
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 1 Θ u τ) j w| ≤ (Kder0 + τ * Kder1) * gaussDdim (3 / 2 * τ) w := by
    intro w j h1 h2
    have hpdA : PdiffAt (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w :=
      PdiffAt_of_contDiff _ ((gaussDdim_contDiff τ).mul (hw 0)) j w
    have hpdB : PdiffAt (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w :=
      PdiffAt_of_contDiff _ ((gaussDdim_contDiff τ).mul (hw 1)) j w
    have hpdτB : PdiffAt (fun y => τ * (gaussDdim τ y * foldedCoeff Θ u 1 y)) j w :=
      PdiffAt_of_contDiff _ (contDiff_const.mul ((gaussDdim_contDiff τ).mul (hw 1))) j w
    have hpdsplit : pd (heatParametrix 1 Θ u τ) j w
        = pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w
          + τ * pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w := by
      rw [hH1eq, pd_add _ _ j w hpdA hpdτB,
        pd_const_mul τ (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w hpdB]
    rw [hpdsplit]
    have hd0 := hDHann0U τ hτ w j h1 h2
    have hd1 := hDHann1U τ hτ w j h1 h2
    calc |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w
            + τ * pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w|
        ≤ |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w|
            + |τ * pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w| := abs_add_le _ _
      _ = |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w|
            + τ * |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w| := by
          rw [abs_mul τ (pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w), abs_of_pos hτ]
      _ ≤ Kder0 * gaussDdim (3 / 2 * τ) w + τ * (Kder1 * gaussDdim (3 / 2 * τ) w) :=
          add_le_add hd0 (mul_le_mul_of_nonneg_left hd1 hτ.le)
      _ = (Kder0 + τ * Kder1) * gaussDdim (3 / 2 * τ) w := by ring
  have hgisymm_q : ∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
      = uniformFlowPullbackMetricInv g gi hC hK q w j i :=
    fun w i j => uniformFlowPullbackMetricInv_symm_global g gi hC hK hgsymm q w i j
  have hgibd_q : ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg :=
    fun w i j h1 h2 => hGIannK q hq w h1 h2 i j
  have hCnn : (0 : ℝ) ≤ Bᵣ0 + Bᵣ1 * τ := by positivity
  have hKcofnn : (0 : ℝ) ≤ (Kcof0 + τ * Kcof1) * S32 := by positivity
  have hKdernn : (0 : ℝ) ≤ Kder0 + τ * Kder1 := by positivity
  have hres := (cutoffResidual_narrow_tauUniform_engine
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    (heatParametrix 1 Θ u τ) (fun x => deriv (fun s => heatParametrix 1 Θ u s x) τ)
    a b τ ha0 hab hτ hH2 hgisymm_q
    (Bᵣ0 + Bᵣ1 * τ) hCnn hEnear_q
    ((Kcof0 + τ * Kcof1) * S32) hKcofnn hHann
    (Kder0 + τ * Kder1) hKdernn hDHann
    Kg Kc1 Kc2 hKg0 hKc10 hKc20 hgibd_q hDchi (hLapChiU q hq)).2 v
  calc |radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v|
      ≤ ((Bᵣ0 + Bᵣ1 * τ) + ((Kcof0 + τ * Kcof1) * S32) * Kc2
          + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * (Kder0 + τ * Kder1)) * gaussDdim (3 / 2 * τ) v := hres
    _ = (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := by rw [hB0_def, hB1_def]; ring

/-- **★★★ J4-108 (L4) — `gatedWitnessN1_hEboundW_le_lin`.**  The `_lin` analogue of
    `OrderOneGeometry.gatedWitnessN1_hEboundW_le` (via its `_gen`): identical proof, but the (A) cutoff
    residual is supplied by `cutoffResidualN1_uniformFlow_narrow_mixed_below_lin` (`O(r)` `hCoeffLin1`)
    instead of the `O(r²)` `hCoeffU1`.  The cover builder `gatedWitnessN1_hEboundW_le_of_good` and the
    (B) transport identity / chart transfer are reused verbatim (residual-abstract).  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_lin (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v)
    (hCoeffLin1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      ∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  obtain ⟨r₁, hr₁pos, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hC hK
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set Sc : ℝ := Real.sqrt (2 / (3 / 2)) ^ n with hSc_def
  have hSc0 : 0 ≤ Sc := by positivity
  set ρc : ℝ := min (min rN δ₀) r₁ with hρcdef
  have hρc : 0 < ρc := lt_min (lt_min hrNpos hδ₀) hr₁pos
  have hρc_rN : ρc ≤ rN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρc_δ₀ : ρc ≤ δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρc_r₁ : ρc ≤ r₁ := min_le_right _ _
  obtain ⟨a, b, B₀, B₁, ha, hab, hbρc, hB0, hB1, hAbound⟩ :=
    cutoffResidualN1_uniformFlow_narrow_mixed_below_lin g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1 ρc hρc
  set B₀' : ℝ := B₀ * Sc with hB0'_def
  set B₁' : ℝ := B₁ * Sc with hB1'_def
  have hB0'0 : 0 ≤ B₀' := by rw [hB0'_def]; positivity
  have hB1'0 : 0 ≤ B₁' := by rw [hB1'_def]; positivity
  refine ⟨a, b, max B₀' B₁', ha, hab, le_trans hB0'0 (le_max_left _ _), ?_⟩
  apply gatedWitnessN1_hEboundW_le_of_good g gi hC hK Θ u a b B₀' B₁' ha hab hB0'0 hB1'0 W
  intro q hq
  obtain ⟨hchartGerm, hchartOC⟩ := hchart q hq
  set c : ℝ := (b + ρc) / 2 with hcdef
  have hbc : b < c := by rw [hcdef]; linarith
  have hcρc : c < ρc := by rw [hcdef]; linarith
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hc_rN : c < rN := lt_of_lt_of_le hcρc hρc_rN
  have hc_δ₀ : c < δ₀ := lt_of_lt_of_le hcρc hρc_δ₀
  have hc_r₁ : c < r₁ := lt_of_lt_of_le hcρc hρc_r₁
  refine ⟨c, hbc, ?_, ?_, ?_, ?_⟩
  · intro τ hτ v hv
    have hvN : ‖v‖ < rN := lt_trans hv hc_rN
    have hvδ₀ : ‖v‖ < δ₀ := lt_trans hv hc_δ₀
    have hvr₁ : ‖v‖ < r₁ := lt_trans hv hc_r₁
    obtain ⟨hgerm, hWc2⟩ := hchartGerm v hvδ₀
    have hg1 : ∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v) :=
      fun a' b' => (hg a' b').contDiffAt.of_le le_top
    have hU : IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) :=
      hgnd (uniformFlowExp g gi hC hK q v)
    have hGGi : ∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
        * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0 :=
      fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc
    have hGiG : ∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
        * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0 :=
      metricInv_left_of_right
        (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')
        (fun a' b' => gi (uniformFlowExp g gi hC hK q v) a' b')
        (hgnd (uniformFlowExp g gi hC hK q v))
        (fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc)
    have hf : ContDiffAt ℝ 2
        (fun x => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ x q)
        (uniformFlowExp g gi hC hK q v) := by
      have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 1 Θ u τ y)
          (W q (uniformFlowExp g gi hC hK q v)) := by
        apply ContDiffAt.mul
        · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
        · exact (heatParametrix_contDiff_space 1 Θ u τ hw).contDiffAt.of_le le_top
      exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
    have hpt : W q (uniformFlowExp g gi hC hK q v) = v := by
      simpa using hgerm.eq_of_nhds
    have hprofilegerm :
        (fun z => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ
            (uniformFlowExp g gi hC hK q z) q)
          =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) := by
      filter_upwards [hgerm] with z hz
      have hz' : W q (uniformFlowExp g gi hC hK q z) = z := hz
      simp only [globalCutoffParametrixWitnessN, hz']
    have hlap : laplaceBeltrami g gi
          (fun p => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ p q)
          (uniformFlowExp g gi hC hK q v)
        = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q)
            (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
      have hn := hnat
        (fun x => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ x q)
        q hq v hvN hg1 hf hU hGGi hGiG
      rw [← hn]
      exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
        (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
        _ _ v hprofilegerm
    have htransport :
        heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (W)) τ
            (uniformFlowExp g gi hC hK q v) q
          = radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
      simp only [heatOp]
      have hterm1fun :
          (fun s => globalCutoffParametrixWitnessN 1 Θ u a b (W) s
              (uniformFlowExp g gi hC hK q v) q)
            = (fun s => radialCutoff a b v * heatParametrix 1 Θ u s v) := by
        funext s
        simp only [globalCutoffParametrixWitnessN, hpt]
      rw [hterm1fun, deriv_const_mul_field, hlap]
    rw [htransport]
    have hnarrow := hAbound τ hτ q hq v
    have htransfer :
        gaussDdim (3 / 2 * τ) v
          ≤ Real.sqrt (2 / (3 / 2)) ^ n
              * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) :=
      gaussDdim_le_gaussDdim_chart (c := 3 / 2) (d := 2) (by norm_num) (by norm_num) hτ
        (hdisp q hq v hvr₁)
    have hBτ0 : (0 : ℝ) ≤ B₀ + B₁ * τ := by positivity
    calc |radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
              - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                  (uniformFlowPullbackMetricInv g gi hC hK q)
                  (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v|
        ≤ (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := hnarrow
      _ ≤ (B₀ + B₁ * τ) * (Sc * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
          rw [hSc_def]; exact mul_le_mul_of_nonneg_left htransfer hBτ0
      _ = (B₀' + B₁' * τ) * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by
          rw [hB0'_def, hB1'_def]; ring
  · intro v hv
    have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
    simpa using (hchartGerm v hvδ₀).1.eq_of_nhds
  · intro v hv
    have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
    exact (hchartGerm v hvδ₀).2.continuousAt
  · exact hchartOC c hc0 hc_δ₀

/-- **★★★★ J4-108 (L4) CAPSTONE — `gatedWitnessN1_hEboundW_le_vanVleck_final`.**  The `N = 1` van-Vleck
    gated-witness restricted `hEboundW_le` with BOTH firewalled coefficient inputs DISCHARGED: `hCoeffU0`
    via `hCoeffU0_vanVleck` (J4-107 K1), and the (generically-false) `hCoeffU1` REPLACED by the sound
    `O(r)` bound `uniformCoeffLinear_bound` (L2) at the shifted van-Vleck profile, threaded through the
    `_lin` chain (L3/L4).  The remaining hypotheses are ONLY: the geometric data
    (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`), the all-`k` van-Vleck folded smoothness `hw`, and
    the genuine ambient RNC gauge inputs `hdg0` (`∂g(0)=0`) and `hg0` (`g(0)=δ`) — NO coefficient
    hypotheses remain.  This is J4-106's capstone with the `hCoeffU1` wall removed.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_vanVleck_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      ∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck g gi hg hC hK hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck g) g gi) (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound g gi hg hC hK hgnd hgsymm hinvF hframeK (vanVleck g)
      (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) (hw 1)
  set ρ_c : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρ_c := lt_min hρ0 hρ1
  refine gatedWitnessN1_hEboundW_le_lin g gi hg hC hK hgnd hgsymm hinvF hframeK
    (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw
    ρ_c C0 C1 hρc0 hC0 hC1 ?_ ?_
  · intro q hq v hv
    exact hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _))
  · intro q hq v hv
    exact hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _))

end QIQTH.HeatResidualBound
