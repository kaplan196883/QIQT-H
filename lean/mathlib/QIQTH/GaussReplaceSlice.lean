/-
  GaussReplaceSlice — J4-137: the `hRemE1` discharge — the `T_E1` Gaussian-replacement slice bound,
  the LAST integration grind of the sliver-2 chart program.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS BRICK IS.  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and
  proves NOTHING about `R/6`.  `RemainderIntegration.witness_sliver2_complete` carries the entangled
  Gaussian-replacement half of the Hessian-slice remainder as a single honest hypothesis
      `hRemE1 : ∀ s ∈ Ioo (u−ε) u,
         |∫ z, (G_{u−s}(Y z) − G_{u−s}(z))·polyChart(z)·(A₀ (u−s) z · F s z 0)|
          ≤ C_E1·(u−s)^{−1/2}`,
  where `polyChart(z) = ⟨Y z,P z⟩²/(4τ²) − (⟨P z,P z⟩+⟨Y z,Q z⟩)/(2τ)` (`τ := u−s`) is the CHART
  Hessian coefficient and `G_{u−s}(Y z) − G_{u−s}(z)` the Gaussian-replacement (argument-substitution)
  difference.  This file DISCHARGES `hRemE1` by PURE MOMENT INTEGRATION.

  ROUTE (mirrors `RemainderIntegration.tE2_slice_bound` / `InnerSliceBounds.hInner1_discharge`):
    • (R1) the two-term Gaussian-replacement bound — from the ℓ²-coercivity `hco` and the quadratic
      displacement `hYdisp` (`‖Y z + z‖ ≤ C_W‖z‖²`),
        `|G_τ(Y z) − G_τ(z)| ≤ (2n·C_W‖z‖³ + n·C_W²‖z‖⁴)/(4τ)·(√2)ⁿ·G_{2τ}(z)`
      (a generalisation `gaussDdim_replace_bound_gen` of the banked `gaussDdim_replace_bound`, fed the
      ℓ²-difference algebra `rncRadialSq_diff_bound`);
    • (R2) the crude chart-coefficient cap — via `abs_inner_le`/`normY_le`/`normP_le`,
        `|polyChart(z)| ≤ n²(‖z‖+C_W‖z‖²)²(1+C_P‖z‖)²/(4τ²)
                          + (n(1+C_P‖z‖)²+n(‖z‖+C_W‖z‖²)C_Q)/(2τ)`;
    • (R3) the slice discharge — the product `R1×R2×M₀×C_F` expands into monomials `‖z‖^k·G_{2τ}`
      (`k = 5..10` over `16τ³`, `k = 3..6` over `8τ²`); the width-`2τ` moment envelope
      `pow_norm_mul_gauss_integral (κ=2)` (fed `oneD_absMoment3..10`) turns each `∫ ‖z‖^k G_{2τ}` into
      `n·c_k·(√2)^k·(√τ)^k`; the `w = √τ` fold (`τ ≤ τ₀`) collapses every term to `≤ C·(√τ)^{−1}`.
    • (R4) `hRemE1_discharge` (the EXACT `hRemE1` shape of `witness_sliver2_complete`) and
      `witness_sliver2_grand` = `witness_sliver2_complete` with `hRemE1` DISCHARGED in-line.

  WHAT LANDS (this file):
    • `oneD_absMoment10`     — the 1-D 10th absolute moment (`hk_even_moment_le 5`).
    • `gaussDdim_replace_bound_gen` — the abstract-error kernel-replacement bound.
    • `rncRadialSq_diff_bound` — ★ the two-term ℓ² near-isometry error `|r²_{Yz}−r²_z| ≤ 2nC_W‖z‖³+nC_W²‖z‖⁴`.
    • `gaussReplace_E1_bound`  — ★ (R1) the pointwise Gaussian-replacement bound.
    • `polyChart_abs_bound`    — ★ (R2) the pointwise chart-coefficient cap.
    • `tE1_slice_bound`        — ★★ (R3) the `T_E1` per-slice integral discharge `|∫ T_E1| ≤ C_E1·τ^{−1/2}`.
    • `hRemE1_discharge`       — ★★★ (R4) the EXACT `hRemE1` shape, an `∃ C_E1 ≥ 0` producing it.
    • `witness_sliver2_grand`  — ★★★ (R4) `witness_sliver2_complete` with `hRemE1` GONE.

  ⚠ HONEST FIREWALL — the carry list (each a genuine fact, NONE the conclusion, none vacuous; the model
    `Y = −id`, `P = eᵢ`, `Q = 0`, `A₀` bounded, `F` a width-2 Gaussian bump satisfies EVERY hypothesis,
    for which `T_E1 ≡ 0` since `G_τ(−z) = G_τ(z)`):
      • `hco` — the ℓ²-coercivity `½·r²_z ≤ r²_{Y z}`; `hYdisp` — `‖Y z + z‖ ≤ C_W‖z‖²`;
        `hJ3` — `‖P z − eᵢ‖ ≤ C_P‖z‖`; `hJ3Q` — `‖Q z‖ ≤ C_Q` (the geometric inputs).
      • `hA0bdd` — `|A₀ τ z| ≤ M₀`; `hFdom` — the width-2 `F`-domination.
    No `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.RemainderIntegration

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ★ R0 — the 1-D 10th absolute moment (completing the S4a tower to `k = 10`).
    ############################################################################### -/

/-- **(S4a, k = 10) the tenth absolute moment.**  `∫ y, G_t(y)·|y|^10 ≤ 3932160√2·(√t)^10`
    (even block `hk_even_moment_le 5`; `|y|¹⁰ = (y²)⁵`, `(√t)¹⁰ = t⁵`, `8⁵·5! = 3932160`). -/
theorem oneD_absMoment10 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 10 ≤ 3932160 * Real.sqrt 2 * (Real.sqrt t) ^ 10 := by
  have hconv : ∀ y : ℝ, heatKernel1D t y * |y| ^ 10 = heatKernel1D t y * (y ^ 2) ^ 5 :=
    fun y => by congr 1; rw [← sq_abs y]; ring
  rw [integral_congr_ae (ae_of_all _ hconv)]
  have h10 : (Real.sqrt t) ^ 10 = t ^ 5 := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul, Real.sq_sqrt ht.le]
  rw [h10]
  have hfac : (Nat.factorial 5 : ℝ) = 120 := by norm_num
  have heq : (8 : ℝ) ^ 5 * (Nat.factorial 5 : ℝ) * Real.sqrt 2 * t ^ 5
      = 3932160 * Real.sqrt 2 * t ^ 5 := by rw [hfac]; ring
  linarith [hk_even_moment_le 5 t ht, heq]

/-! ###############################################################################
    ★ R1 — the two-term Gaussian-replacement bound (kernel replacement, quartic error).
    ############################################################################### -/

/-- **THE ABSTRACT-ERROR KERNEL-REPLACEMENT BOUND.**  A generalisation of `gaussDdim_replace_bound`
    with the ℓ²-error bounded by an arbitrary nonneg `Eb` (not necessarily `L'‖z‖³`): from the coercivity
    `hmin : ½·r²_z ≤ r²_{Wz}` and the error `herr : |r²_{Wz}−r²_z| ≤ Eb`, for `τ > 0`,
      `|G_τ(W z) − G_τ(z)| ≤ (Eb/4τ)·(√2)ⁿ·G_{2τ}(z)`.  Same route: `Gk` expansion, `exp_neg_div_sub_le`,
    `min ≥ ½r²_z`, and `Gk_scaled (s=½)`. -/
theorem gaussDdim_replace_bound_gen (τ : ℝ) (hτ : 0 < τ) (W : Point n → Point n) (z : Point n)
    (Eb : ℝ) (_hEb : 0 ≤ Eb)
    (herr : |rncRadialSq (W z) - rncRadialSq z| ≤ Eb)
    (hmin : (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (W z)) :
    |gaussDdim τ (W z) - gaussDdim τ z|
      ≤ Eb / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
  have hpnn : (0 : ℝ) ≤ rncRadialSq z := rncRadialSq_nonneg z
  rw [gaussDdim_eq_Gk τ (W z), gaussDdim_eq_Gk τ z]
  set p := rncRadialSq z with hpdef
  set q := rncRadialSq (W z) with hqdef
  have hGksub : Gk n τ q - Gk n τ p
      = (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n
          * (Real.exp (-q / (4 * τ)) - Real.exp (-p / (4 * τ))) := by
    unfold Gk; ring
  rw [hGksub, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n)]
  have hS5a := exp_neg_div_sub_le q p τ hτ
  have hmin' : (1 / 2 : ℝ) * p ≤ min q p := le_min hmin (by linarith [hpnn])
  have hexple : Real.exp (-(min q p) / (4 * τ)) ≤ Real.exp (-((1 / 2) * p) / (4 * τ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith [hmin']) (by positivity)
  have hs2 : (Real.sqrt (1 / 2))⁻¹ = Real.sqrt 2 := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ from by norm_num, Real.sqrt_inv, inv_inv]
  have hhalf : (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.exp (-((1 / 2) * p) / (4 * τ))
      = (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
    have hkey : Gk n τ ((1 / 2) * p) = (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
      rw [hpdef, Gk_scaled (1 / 2) τ (by norm_num) hτ z, hs2,
          show τ / (1 / 2) = 2 * τ from by ring]
    rw [← hkey]; rfl
  have hXnn : (0 : ℝ) ≤ (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
    mul_nonneg (by positivity) (gaussDdim_nonneg _ _)
  calc (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n
          * |Real.exp (-q / (4 * τ)) - Real.exp (-p / (4 * τ))|
      ≤ (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n
          * ((|q - p| / (4 * τ)) * Real.exp (-(min q p) / (4 * τ))) :=
        mul_le_mul_of_nonneg_left hS5a (by positivity)
    _ = (|q - p| / (4 * τ))
          * ((Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.exp (-(min q p) / (4 * τ))) := by ring
    _ ≤ (|q - p| / (4 * τ))
          * ((Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.exp (-((1 / 2) * p) / (4 * τ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hexple (by positivity)
    _ = (|q - p| / (4 * τ)) * ((Real.sqrt 2) ^ n * gaussDdim (2 * τ) z) := by rw [hhalf]
    _ ≤ (Eb / (4 * τ)) * ((Real.sqrt 2) ^ n * gaussDdim (2 * τ) z) := by
        apply mul_le_mul_of_nonneg_right _ hXnn
        exact (div_le_div_iff_of_pos_right (by positivity)).mpr herr
    _ = Eb / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by ring

/-- The ℓ²-square is `≤ n·(sup-norm)²`: `rncRadialSq v ≤ n·‖v‖²` (each `(vᵢ)² = |vᵢ|² ≤ ‖v‖²`). -/
theorem rncRadialSq_le_nsq (v : Point n) : rncRadialSq v ≤ (n : ℝ) * ‖v‖ ^ 2 := by
  unfold rncRadialSq
  calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h : |v i| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
        calc (v i) ^ 2 = |v i| ^ 2 := (sq_abs _).symm
          _ ≤ ‖v‖ ^ 2 := by nlinarith [abs_nonneg (v i), norm_nonneg v]
    _ = (n : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The coordinatewise identity `r²_{Yz} − r²_z = r²_{Yz+z} − 2·∑ (Yz+z)ₖ·zₖ` (from
    `(Yzₖ)²−(zₖ)² = (Yzₖ+zₖ)²−2(Yzₖ+zₖ)zₖ`, summed). -/
theorem rncRadialSq_sub_expand (Y : Point n → Point n) (z : Point n) :
    rncRadialSq (Y z) - rncRadialSq z
      = rncRadialSq (Y z + z) - 2 * ∑ i, (Y z i + z i) * (z i) := by
  simp only [rncRadialSq, Pi.add_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **★ THE TWO-TERM ℓ² NEAR-ISOMETRY ERROR.**  From the quadratic displacement `hYd`
    (`‖Y z + z‖ ≤ C_W‖z‖²`), the ℓ² radial coordinate changes by at most a quartic:
      `|r²_{Y z} − r²_z| ≤ 2n·C_W‖z‖³ + n·C_W²‖z‖⁴`.
    Route: the expansion `r²_{Yz}−r²_z = r²_{Yz+z} − 2⟨Y z+z, z⟩`, then `r²_{Yz+z} ≤ n‖Yz+z‖² ≤ nC_W²‖z‖⁴`
    (`rncRadialSq_le_nsq`) and `|⟨Yz+z,z⟩| ≤ n‖Yz+z‖‖z‖ ≤ nC_W‖z‖³` (`abs_inner_le`). -/
theorem rncRadialSq_diff_bound (Y : Point n → Point n) (z : Point n) (C_W : ℝ) (_hC_W : 0 ≤ C_W)
    (hYd : ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2) :
    |rncRadialSq (Y z) - rncRadialSq z| ≤ 2 * (n : ℝ) * C_W * ‖z‖ ^ 3 + (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4 := by
  rw [rncRadialSq_sub_expand]
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have h1 : rncRadialSq (Y z + z) ≤ (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4 := by
    calc rncRadialSq (Y z + z) ≤ (n : ℝ) * ‖Y z + z‖ ^ 2 := rncRadialSq_le_nsq _
      _ ≤ (n : ℝ) * (C_W * ‖z‖ ^ 2) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hcast
          exact pow_le_pow_left₀ (norm_nonneg _) hYd 2
      _ = (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4 := by ring
  have h2 : |∑ i, (Y z i + z i) * (z i)| ≤ (n : ℝ) * C_W * ‖z‖ ^ 3 := by
    have hstep : (n : ℝ) * ‖Y z + z‖ * ‖z‖ ≤ (n : ℝ) * (C_W * ‖z‖ ^ 2) * ‖z‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left hYd hcast
    calc |∑ i, (Y z i + z i) * (z i)| ≤ (n : ℝ) * ‖Y z + z‖ * ‖z‖ := abs_inner_le (Y z + z) z
      _ ≤ (n : ℝ) * (C_W * ‖z‖ ^ 2) * ‖z‖ := hstep
      _ = (n : ℝ) * C_W * ‖z‖ ^ 3 := by ring
  have hrnn : 0 ≤ rncRadialSq (Y z + z) := rncRadialSq_nonneg _
  have habs : |rncRadialSq (Y z + z) - 2 * ∑ i, (Y z i + z i) * (z i)|
      ≤ |rncRadialSq (Y z + z)| + |2 * ∑ i, (Y z i + z i) * (z i)| := by
    have := abs_add_le (rncRadialSq (Y z + z)) (-(2 * ∑ i, (Y z i + z i) * (z i)))
    rwa [← sub_eq_add_neg, abs_neg] at this
  calc |rncRadialSq (Y z + z) - 2 * ∑ i, (Y z i + z i) * (z i)|
      ≤ |rncRadialSq (Y z + z)| + |2 * ∑ i, (Y z i + z i) * (z i)| := habs
    _ = rncRadialSq (Y z + z) + 2 * |∑ i, (Y z i + z i) * (z i)| := by
        rw [abs_of_nonneg hrnn, abs_mul, abs_two]
    _ ≤ (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4 + 2 * ((n : ℝ) * C_W * ‖z‖ ^ 3) := by
        exact add_le_add h1 (by linarith [h2])
    _ = 2 * (n : ℝ) * C_W * ‖z‖ ^ 3 + (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4 := by ring

/-- **★ R1 — THE POINTWISE GAUSSIAN-REPLACEMENT BOUND.**  Under the ℓ²-coercivity `hco` and the
    quadratic displacement `hYd`, the argument-substitution difference obeys
      `|G_τ(Y z) − G_τ(z)| ≤ (2n·C_W‖z‖³ + n·C_W²‖z‖⁴)/(4τ)·(√2)ⁿ·G_{2τ}(z)`.
    (`gaussDdim_replace_bound_gen` with the two-term error `rncRadialSq_diff_bound`.)  NOT `a₁ = R/6`. -/
theorem gaussReplace_E1_bound (τ : ℝ) (hτ : 0 < τ) (Y : Point n → Point n) (z : Point n)
    (C_W : ℝ) (hC_W : 0 ≤ C_W) (hYd : ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hco : (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z)) :
    |gaussDdim τ (Y z) - gaussDdim τ z|
      ≤ (2 * (n : ℝ) * C_W * ‖z‖ ^ 3 + (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4) / (4 * τ)
          * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
  gaussDdim_replace_bound_gen τ hτ Y z _
    (by positivity) (rncRadialSq_diff_bound Y z C_W hC_W hYd) hco

/-! ###############################################################################
    ★ R2 — the crude chart-coefficient cap.
    ############################################################################### -/

/-- **★ R2 — THE POINTWISE CHART-COEFFICIENT CAP.**  The chart Hessian coefficient `polyChart` is
    bounded pointwise, via `abs_inner_le`/`normY_le`/`normP_le` fed the geometric inputs, by an
    explicit polynomial over `τ²`/`τ`:
      `|⟨Y z,P z⟩²/(4τ²) − (⟨P z,P z⟩+⟨Y z,Q z⟩)/(2τ)|`
        `≤ n²(‖z‖+C_W‖z‖²)²(1+C_P‖z‖)²/(4τ²) + (n(1+C_P‖z‖)²+n(‖z‖+C_W‖z‖²)C_Q)/(2τ)`.  NOT `a₁ = R/6`. -/
theorem polyChart_abs_bound (Y P Q : Point n → Point n) (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (C_W C_P C_Q : ℝ) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (_hC_Q : 0 ≤ C_Q)
    (hYd : ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2) (hJ : ‖P z - unitVec i‖ ≤ C_P * ‖z‖) (hQ : ‖Q z‖ ≤ C_Q) :
    |(∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
        - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)|
      ≤ (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 / (4 * τ ^ 2)
        + ((n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q) / (2 * τ) := by
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hYn : ‖Y z‖ ≤ C_W * ‖z‖ ^ 2 + ‖z‖ := normY_le (Y z) z (C_W * ‖z‖ ^ 2) hYd
  have hYn' : ‖Y z‖ ≤ ‖z‖ + C_W * ‖z‖ ^ 2 := by linarith [hYn]
  have hPn : ‖P z‖ ≤ 1 + C_P * ‖z‖ := normP_le (P z) i C_P ‖z‖ hJ
  -- the three inner-product caps.
  have hip : |∑ k, Y z k * P z k| ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * (1 + C_P * ‖z‖) := by
    calc |∑ k, Y z k * P z k| ≤ (n : ℝ) * ‖Y z‖ * ‖P z‖ := abs_inner_le (Y z) (P z)
      _ ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * (1 + C_P * ‖z‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hYn' hcast) hPn (norm_nonneg _)
            (mul_nonneg hcast (by positivity))
  have hPP : |∑ k, P z k * P z k| ≤ (n : ℝ) * (1 + C_P * ‖z‖) ^ 2 := by
    calc |∑ k, P z k * P z k| ≤ (n : ℝ) * ‖P z‖ * ‖P z‖ := abs_inner_le (P z) (P z)
      _ ≤ (n : ℝ) * (1 + C_P * ‖z‖) * (1 + C_P * ‖z‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hPn hcast) hPn (norm_nonneg _)
            (mul_nonneg hcast (by positivity))
      _ = (n : ℝ) * (1 + C_P * ‖z‖) ^ 2 := by ring
  have hYQ : |∑ k, Y z k * Q z k| ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q := by
    calc |∑ k, Y z k * Q z k| ≤ (n : ℝ) * ‖Y z‖ * ‖Q z‖ := abs_inner_le (Y z) (Q z)
      _ ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q :=
          mul_le_mul (mul_le_mul_of_nonneg_left hYn' hcast) hQ (norm_nonneg _)
            (mul_nonneg hcast (by positivity))
  -- numerator caps.
  have hXcap : (∑ k, Y z k * P z k) ^ 2
      ≤ (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 := by
    calc (∑ k, Y z k * P z k) ^ 2 = |∑ k, Y z k * P z k| ^ 2 := (sq_abs _).symm
      _ ≤ ((n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * (1 + C_P * ‖z‖)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hip 2
      _ = (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 := by ring
  have hYb : |(∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)|
      ≤ (n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q :=
    (abs_add_le _ _).trans (add_le_add hPP hYQ)
  have hXcap' : |(∑ k, Y z k * P z k) ^ 2|
      ≤ (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 := by
    rwa [abs_of_nonneg (sq_nonneg _)]
  have h4 : (0 : ℝ) < 4 * τ ^ 2 := by positivity
  have h2p : (0 : ℝ) < 2 * τ := by linarith
  have habs2 : |(∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
        - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)|
      ≤ |(∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)|
        + |((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)| := by
    have := abs_add_le ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2))
      (-(((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)))
    rwa [← sub_eq_add_neg, abs_neg] at this
  calc |(∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
          - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)|
      ≤ |(∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)|
        + |((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)| := habs2
    _ = |(∑ k, Y z k * P z k) ^ 2| / (4 * τ ^ 2)
        + |(∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)| / (2 * τ) := by
        rw [abs_div, abs_div, abs_of_pos h4, abs_of_pos h2p]
    _ ≤ (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 / (4 * τ ^ 2)
        + ((n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q) / (2 * τ) :=
        add_le_add ((div_le_div_iff_of_pos_right h4).mpr hXcap')
          ((div_le_div_iff_of_pos_right h2p).mpr hYb)

/-! ###############################################################################
    ★★ R3 — the T_E1 per-slice integral discharge (moment integration).
    ############################################################################### -/

/-- **★★ THE T_E1 SLICE DISCHARGE.**  The Gaussian-replacement remainder integrand
    `T_E1 z = (G_τ(Y z) − G_τ(z))·polyChart(z)·(A₀ τ z · F s z 0)` (τ = u−s) has the `τ^{−1/2}`
    rate: there is an `s`-uniform constant `C_E1 ≥ 0` with
      `∀ s ∈ Ioo (u−ε) u,  |∫ z, T_E1 z| ≤ C_E1·(u−s)^{−1/2}`.
    Route: `gaussReplace_E1_bound` (R1) × `polyChart_abs_bound` (R2) × the amplitude/F caps give the
    pointwise domination by `K·Σ_{k=3}^{10} c_k·‖z‖^k·G_{2τ}`; the width-`2τ` moment envelope
    `pow_norm_mul_gauss_integral (κ=2)` (fed `oneD_absMoment3..10`) evaluates each moment; the
    `w = √τ` fold (`τ ≤ τ₀`) collapses everything to `≤ C_E1·(√τ)^{−1}` (leading terms: the `(5,3)`
    and `(3,2)` monomials, exactly `τ^{−1/2}`).  This IS the carried `hRemE1` of
    `witness_sliver2_complete`, now proven.  NOT `a₁ = R/6`. -/
theorem tE1_slice_bound
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₀ C_L T a u ε τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (_hε0 : 0 ≤ ε) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∃ C_E1 : ℝ, 0 ≤ C_E1 ∧ ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z 0)|
        ≤ C_E1 * (u - s) ^ (-(1 : ℝ) / 2) := by
  set K : ℝ := (Real.sqrt 2) ^ n * (M₀ * (C_L * gaussDdim a (0 : Point n))) with hKdef
  have hga : (0 : ℝ) ≤ gaussDdim a (0 : Point n) := gaussDdim_nonneg' a 0
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  refine ⟨K * (((n : ℝ) ^ 3 * C_W / 8 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5)
        + (n : ℝ) ^ 2 * C_W / 4 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3))
      + (C_W * (n : ℝ) ^ 3 * (5 * C_W + 4 * C_P) / 16
            * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6)
          + C_W * (n : ℝ) ^ 2 * (C_W + 4 * C_P + 2 * C_Q) / 8
            * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4)) * Real.sqrt τ₀
      + (C_W * (n : ℝ) ^ 3 * (2 * C_W ^ 2 + 5 * C_W * C_P + C_P ^ 2) / 8
            * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7)
          + C_W * (n : ℝ) ^ 2 * (2 * C_W * C_P + 3 * C_W * C_Q + 2 * C_P ^ 2) / 8
            * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5)) * Real.sqrt τ₀ ^ 2
      + (C_W ^ 2 * (n : ℝ) ^ 3 * (C_W ^ 2 + 8 * C_W * C_P + 5 * C_P ^ 2) / 16
            * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8)
          + C_W ^ 2 * (n : ℝ) ^ 2 * (C_W * C_Q + C_P ^ 2) / 8
            * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6)) * Real.sqrt τ₀ ^ 3
      + (C_W ^ 3 * (n : ℝ) ^ 3 * C_P * (C_W + 2 * C_P) / 8
            * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9)) * Real.sqrt τ₀ ^ 4
      + (C_W ^ 4 * (n : ℝ) ^ 3 * C_P ^ 2 / 16
            * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10)) * Real.sqrt τ₀ ^ 5),
    ?_, ?_⟩
  · exact mul_nonneg hKnn (by positivity)
  intro s hsmem
  have hτpos : 0 < u - s := by linarith [hsmem.2]
  have hlo : u - ε > a / 2 := by linarith
  have hspos : 0 < s := by linarith [hsmem.1, hlo]
  have hsT : s ≤ T := by linarith [hsmem.2, huT]
  have hsa2 : a / 2 ≤ s := by linarith [hsmem.1, hlo]
  have hττ₀ : u - s ≤ τ₀ := by linarith [hsmem.1, hετ₀]
  set τ : ℝ := u - s with hτ_def
  have hτne : τ ≠ 0 := hτpos.ne'
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  -- F-cap.
  set C_F : ℝ := C_L * gaussDdim a (0 : Point n) with hCF_def
  have hCFnn : 0 ≤ C_F := by rw [hCF_def]; exact mul_nonneg hC_L hga
  have hFcap : ∀ z : Point n, |F s z 0| ≤ C_F :=
    fun z => B_le_MB F C_L T a hC_L hFdom ha s hsa2 hsT z
  -- the eight τ-coefficients of the product polynomial (E·polyChart-cap, collected by degree).
  set c3 : ℝ := (n : ℝ) ^ 2 * C_W / (4 * τ ^ 2) with hc3
  set c4 : ℝ := C_W * (n : ℝ) ^ 2 * (C_W + 4 * C_P + 2 * C_Q) / (8 * τ ^ 2) with hc4
  set c5 : ℝ := (n : ℝ) ^ 3 * C_W / (8 * τ ^ 3)
      + C_W * (n : ℝ) ^ 2 * (2 * C_W * C_P + 3 * C_W * C_Q + 2 * C_P ^ 2) / (8 * τ ^ 2) with hc5
  set c6 : ℝ := C_W * (n : ℝ) ^ 3 * (5 * C_W + 4 * C_P) / (16 * τ ^ 3)
      + C_W ^ 2 * (n : ℝ) ^ 2 * (C_W * C_Q + C_P ^ 2) / (8 * τ ^ 2) with hc6
  set c7 : ℝ := C_W * (n : ℝ) ^ 3 * (2 * C_W ^ 2 + 5 * C_W * C_P + C_P ^ 2) / (8 * τ ^ 3) with hc7
  set c8 : ℝ := C_W ^ 2 * (n : ℝ) ^ 3 * (C_W ^ 2 + 8 * C_W * C_P + 5 * C_P ^ 2) / (16 * τ ^ 3) with hc8
  set c9 : ℝ := C_W ^ 3 * (n : ℝ) ^ 3 * C_P * (C_W + 2 * C_P) / (8 * τ ^ 3) with hc9
  set c10 : ℝ := C_W ^ 4 * (n : ℝ) ^ 3 * C_P ^ 2 / (16 * τ ^ 3) with hc10
  have hc3nn : 0 ≤ c3 := by rw [hc3]; positivity
  have hc4nn : 0 ≤ c4 := by rw [hc4]; positivity
  have hc5nn : 0 ≤ c5 := by rw [hc5]; positivity
  have hc6nn : 0 ≤ c6 := by rw [hc6]; positivity
  have hc7nn : 0 ≤ c7 := by rw [hc7]; positivity
  have hc8nn : 0 ≤ c8 := by rw [hc8]; positivity
  have hc9nn : 0 ≤ c9 := by rw [hc9]; positivity
  have hc10nn : 0 ≤ c10 := by rw [hc10]; positivity
  -- pointwise domination by the dominating (poly × width-2τ Gaussian) function.
  have hpt : ∀ z : Point n,
      ‖(gaussDdim τ (Y z) - gaussDdim τ z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
          * (A0 τ z * F s z 0)‖
        ≤ K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z)
            + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z)
            + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z)
            + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z)) := by
    intro z
    have hG2nn : 0 ≤ gaussDdim (2 * τ) z := gaussDdim_nonneg' (2 * τ) z
    have hGd := gaussReplace_E1_bound τ hτpos Y z C_W hC_W (hYdisp z) (hco z)
    have hpc := polyChart_abs_bound Y P Q i τ hτpos z C_W C_P C_Q hC_W hC_P hC_Q
      (hYdisp z) (hJ3 z) (hJ3Q z)
    have hAF : |A0 τ z * F s z 0| ≤ M₀ * C_F := by
      rw [abs_mul]; exact mul_le_mul (hA0bdd τ z) (hFcap z) (abs_nonneg _) hM₀
    have hEnn : (0 : ℝ) ≤ (2 * (n : ℝ) * C_W * ‖z‖ ^ 3 + (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4) / (4 * τ)
        * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity)) hG2nn
    have hPCnn : (0 : ℝ)
        ≤ (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 / (4 * τ ^ 2)
          + ((n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q) / (2 * τ) := by
      positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |gaussDdim τ (Y z) - gaussDdim τ z|
            * |(∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)|
            * |A0 τ z * F s z 0|
        ≤ ((2 * (n : ℝ) * C_W * ‖z‖ ^ 3 + (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4) / (4 * τ)
              * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z)
            * ((n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 / (4 * τ ^ 2)
              + ((n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q) / (2 * τ))
            * (M₀ * C_F) :=
          mul_le_mul (mul_le_mul hGd hpc (abs_nonneg _) hEnn) hAF (abs_nonneg _)
            (mul_nonneg hEnn hPCnn)
      _ = K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z)
            + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z)
            + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z)
            + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z)) := by
          rw [hKdef, hCF_def, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10]
          field_simp
          ring
  -- integrability of each monomial × Gaussian and of the dominating function.
  have hi3 := (normPow_gauss_integrable 3 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c3
  have hi4 := (normPow_gauss_integrable 4 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c4
  have hi5 := (normPow_gauss_integrable 5 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c5
  have hi6 := (normPow_gauss_integrable 6 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c6
  have hi7 := (normPow_gauss_integrable 7 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c7
  have hi8 := (normPow_gauss_integrable 8 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c8
  have hi9 := (normPow_gauss_integrable 9 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c9
  have hi10 := (normPow_gauss_integrable 10 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c10
  have hdom_int : Integrable (fun z : Point n =>
      K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z)
        + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z)
        + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z)
        + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z))) volume :=
    (((((((hi3.add hi4).add hi5).add hi6).add hi7).add hi8).add hi9).add hi10).const_mul K
  -- the width-2τ moment values (κ = 2).
  have hm3 : ∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3 :=
    pow_norm_mul_gauss_integral 3 (by norm_num) 2 (by norm_num) τ hτpos (64 * Real.sqrt 2 + 1)
      (by positivity) (oneD_absMoment3 (2 * τ) h2τ)
  have hm4 : ∫ z : Point n, ‖z‖ ^ 4 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4 * (Real.sqrt τ) ^ 4 :=
    pow_norm_mul_gauss_integral 4 (by norm_num) 2 (by norm_num) τ hτpos (128 * Real.sqrt 2)
      (by positivity) (oneD_absMoment4 (2 * τ) h2τ)
  have hm5 : ∫ z : Point n, ‖z‖ ^ 5 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * (Real.sqrt τ) ^ 5 :=
    pow_norm_mul_gauss_integral 5 (by norm_num) 2 (by norm_num) τ hτpos (1600 * Real.sqrt 2)
      (by positivity) (oneD_absMoment5 (2 * τ) h2τ)
  have hm6 : ∫ z : Point n, ‖z‖ ^ 6 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6 * (Real.sqrt τ) ^ 6 :=
    pow_norm_mul_gauss_integral 6 (by norm_num) 2 (by norm_num) τ hτpos (3072 * Real.sqrt 2)
      (by positivity) (oneD_absMoment6 (2 * τ) h2τ)
  have hm7 : ∫ z : Point n, ‖z‖ ^ 7 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7 * (Real.sqrt τ) ^ 7 :=
    pow_norm_mul_gauss_integral 7 (by norm_num) 2 (by norm_num) τ hτpos (50688 * Real.sqrt 2)
      (by positivity) (oneD_absMoment7 (2 * τ) h2τ)
  have hm8 : ∫ z : Point n, ‖z‖ ^ 8 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8 * (Real.sqrt τ) ^ 8 :=
    pow_norm_mul_gauss_integral 8 (by norm_num) 2 (by norm_num) τ hτpos (98304 * Real.sqrt 2)
      (by positivity) (oneD_absMoment8 (2 * τ) h2τ)
  have hm9 : ∫ z : Point n, ‖z‖ ^ 9 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9 * (Real.sqrt τ) ^ 9 :=
    pow_norm_mul_gauss_integral 9 (by norm_num) 2 (by norm_num) τ hτpos (2015232 * Real.sqrt 2)
      (by positivity) (oneD_absMoment9 (2 * τ) h2τ)
  have hm10 : ∫ z : Point n, ‖z‖ ^ 10 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10 * (Real.sqrt τ) ^ 10 :=
    pow_norm_mul_gauss_integral 10 (by norm_num) 2 (by norm_num) τ hτpos (3932160 * Real.sqrt 2)
      (by positivity) (oneD_absMoment10 (2 * τ) h2τ)
  -- the integral of the dominating function.
  have e1 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) := integral_add hi3 hi4
  have e2 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) := integral_add (hi3.add hi4) hi5
  have e3 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) :=
    integral_add ((hi3.add hi4).add hi5) hi6
  have e4 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) :=
    integral_add (((hi3.add hi4).add hi5).add hi6) hi7
  have e5 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
        + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) :=
    integral_add ((((hi3.add hi4).add hi5).add hi6).add hi7) hi8
  have e6 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
        + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
          + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) :=
    integral_add (((((hi3.add hi4).add hi5).add hi6).add hi7).add hi8) hi9
  have e7 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
        + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z)
        + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
          + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z) :=
    integral_add ((((((hi3.add hi4).add hi5).add hi6).add hi7).add hi8).add hi9) hi10
  have hDval : ∫ z : Point n, K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
        + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z)
        + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z))
      = K * (c3 * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (∫ z : Point n, ‖z‖ ^ 4 * gaussDdim (2 * τ) z)
          + c5 * (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (∫ z : Point n, ‖z‖ ^ 6 * gaussDdim (2 * τ) z)
          + c7 * (∫ z : Point n, ‖z‖ ^ 7 * gaussDdim (2 * τ) z)
          + c8 * (∫ z : Point n, ‖z‖ ^ 8 * gaussDdim (2 * τ) z)
          + c9 * (∫ z : Point n, ‖z‖ ^ 9 * gaussDdim (2 * τ) z)
          + c10 * (∫ z : Point n, ‖z‖ ^ 10 * gaussDdim (2 * τ) z)) := by
    rw [integral_const_mul, e7, e6, e5, e4, e3, e2, e1, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul]
  -- main inequality: |∫ T_E1| ≤ (moment upper bounds).
  have hmain : |∫ z, (gaussDdim τ (Y z) - gaussDdim τ z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
          * (A0 τ z * F s z 0)|
      ≤ K * (c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
          + c4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4 * (Real.sqrt τ) ^ 4)
          + c5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * (Real.sqrt τ) ^ 5)
          + c6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6 * (Real.sqrt τ) ^ 6)
          + c7 * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7 * (Real.sqrt τ) ^ 7)
          + c8 * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8 * (Real.sqrt τ) ^ 8)
          + c9 * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9 * (Real.sqrt τ) ^ 9)
          + c10 * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10 * (Real.sqrt τ) ^ 10)) := by
    calc |∫ z, (gaussDdim τ (Y z) - gaussDdim τ z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
            * (A0 τ z * F s z 0)|
        = ‖∫ z, (gaussDdim τ (Y z) - gaussDdim τ z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
            * (A0 τ z * F s z 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖(gaussDdim τ (Y z) - gaussDdim τ z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
            * (A0 τ z * F s z 0)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z)
            + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z)
            + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z)
            + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z)) :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hdom_int (ae_of_all _ hpt)
      _ = K * (c3 * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)
            + c4 * (∫ z : Point n, ‖z‖ ^ 4 * gaussDdim (2 * τ) z)
            + c5 * (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim (2 * τ) z)
            + c6 * (∫ z : Point n, ‖z‖ ^ 6 * gaussDdim (2 * τ) z)
            + c7 * (∫ z : Point n, ‖z‖ ^ 7 * gaussDdim (2 * τ) z)
            + c8 * (∫ z : Point n, ‖z‖ ^ 8 * gaussDdim (2 * τ) z)
            + c9 * (∫ z : Point n, ‖z‖ ^ 9 * gaussDdim (2 * τ) z)
            + c10 * (∫ z : Point n, ‖z‖ ^ 10 * gaussDdim (2 * τ) z)) := hDval
      _ ≤ K * (c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
            + c4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4 * (Real.sqrt τ) ^ 4)
            + c5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * (Real.sqrt τ) ^ 5)
            + c6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6 * (Real.sqrt τ) ^ 6)
            + c7 * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7 * (Real.sqrt τ) ^ 7)
            + c8 * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8 * (Real.sqrt τ) ^ 8)
            + c9 * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9 * (Real.sqrt τ) ^ 9)
            + c10 * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10 * (Real.sqrt τ) ^ 10)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKnn
          exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left hm3 hc3nn) (mul_le_mul_of_nonneg_left hm4 hc4nn))
            (mul_le_mul_of_nonneg_left hm5 hc5nn)) (mul_le_mul_of_nonneg_left hm6 hc6nn))
            (mul_le_mul_of_nonneg_left hm7 hc7nn)) (mul_le_mul_of_nonneg_left hm8 hc8nn))
            (mul_le_mul_of_nonneg_left hm9 hc9nn)) (mul_le_mul_of_nonneg_left hm10 hc10nn)
  refine le_trans hmain ?_
  -- the τ^{−1/2} fold: substitute `w = √τ`, cap `w ≤ √τ₀`.
  rw [← inv_sqrt_eq_rpow τ hτpos]
  have hwpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτpos
  have hwne : Real.sqrt τ ≠ 0 := hwpos.ne'
  have hwsq : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτpos.le
  have hwle : Real.sqrt τ ≤ Real.sqrt τ₀ := Real.sqrt_le_sqrt hττ₀
  set w : ℝ := Real.sqrt τ with hwdef
  -- linearise: pull out `w⁻¹`.
  have hlin : K * (c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 3)
          + c4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4 * w ^ 4)
          + c5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * w ^ 5)
          + c6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6 * w ^ 6)
          + c7 * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7 * w ^ 7)
          + c8 * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8 * w ^ 8)
          + c9 * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9 * w ^ 9)
          + c10 * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10 * w ^ 10))
      = w⁻¹ * (K * (((n : ℝ) ^ 3 * C_W / 8 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5)
            + (n : ℝ) ^ 2 * C_W / 4 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3))
          + (C_W * (n : ℝ) ^ 3 * (5 * C_W + 4 * C_P) / 16
                * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6)
              + C_W * (n : ℝ) ^ 2 * (C_W + 4 * C_P + 2 * C_Q) / 8
                * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4)) * w
          + (C_W * (n : ℝ) ^ 3 * (2 * C_W ^ 2 + 5 * C_W * C_P + C_P ^ 2) / 8
                * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7)
              + C_W * (n : ℝ) ^ 2 * (2 * C_W * C_P + 3 * C_W * C_Q + 2 * C_P ^ 2) / 8
                * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5)) * w ^ 2
          + (C_W ^ 2 * (n : ℝ) ^ 3 * (C_W ^ 2 + 8 * C_W * C_P + 5 * C_P ^ 2) / 16
                * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8)
              + C_W ^ 2 * (n : ℝ) ^ 2 * (C_W * C_Q + C_P ^ 2) / 8
                * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6)) * w ^ 3
          + (C_W ^ 3 * (n : ℝ) ^ 3 * C_P * (C_W + 2 * C_P) / 8
                * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9)) * w ^ 4
          + (C_W ^ 4 * (n : ℝ) ^ 3 * C_P ^ 2 / 16
                * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10)) * w ^ 5)) := by
    rw [hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ← hwsq]
    field_simp
    try ring
  rw [hlin]
  have hwinv_nn : (0 : ℝ) ≤ w⁻¹ := inv_nonneg.mpr hwpos.le
  rw [mul_comm _ w⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ hwinv_nn
  refine mul_le_mul_of_nonneg_left ?_ hKnn
  gcongr

/-! ###############################################################################
    ★★★ R4 — the EXACT `hRemE1` shape + the grand composite (E1 GONE).
    ############################################################################### -/

/-- **★★★ THE `hRemE1` DISCHARGE.**  The EXACT carried Gaussian-replacement hypothesis of
    `hRem_discharge`/`witness_sliver2_complete`, now a theorem: an `s`-uniform `C_E1 ≥ 0` with
      `∀ s ∈ Ioo (u−ε) u,  |∫ z, T_E1 z| ≤ C_E1·(u−s)^{−1/2}`.
    (A restatement of `tE1_slice_bound`.)  NOT `a₁ = R/6`. -/
theorem hRemE1_discharge
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₀ C_L T a u ε τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∃ C_E1 : ℝ, 0 ≤ C_E1 ∧ ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z 0)|
        ≤ C_E1 * (u - s) ^ (-(1 : ℝ) / 2) :=
  tE1_slice_bound Y P Q A0 F i M₀ C_L T a u ε τ₀ C_W C_P C_Q
    hM₀ hC_L hC_W hC_P hC_Q ha hau huT hε0 hεa hετ₀ hco hYdisp hJ3 hJ3Q hA0bdd hFdom

/-- **★★★ `witness_sliver2_grand`.**  The composite `witness_sliver2_complete` with its carried
    Gaussian-replacement half `hRemE1` DISCHARGED in-line by `tE1_slice_bound` — BOTH integration
    halves of the entangled Hessian-slice remainder are now proven.  For an `s`-uniform `C_R ≥ 0`
    (existential, absorbing both proven halves), the terminal concrete formal-Hessian sliver obeys
      `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ ((15/2·n·L + C_R) + C₁)·2√ε + C₂·ε`.
    Remaining carries: `hNormalForm`, the geometric inputs `hco`/`hYdisp`/`hJ3`/`hJ3Q`, the amplitude
    bounds, `hFdom`, `hqLip`, and the split-algebra integrabilities `hIntT1/2/3`/`hInt1`/`hInt2`
    (no measurability of `Y`/`P`/`Q` is carried, so the integrabilities stay labelled).
    NOT `a₁ = R/6`. -/
theorem witness_sliver2_grand
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (Y P Q : Point n → Point n) (A0 A1 A2 : ℝ → Point n → ℝ)
    (i : Fin n) (L M₀ M₁ M₂ C_L T a τ₀ C_W C_P C_Q : ℝ)
    (hL : 0 ≤ L) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hC_L : 0 ≤ C_L)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (u ε : ℝ) (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hA1bdd : ∀ τ, ∀ z : Point n, |A1 τ z| ≤ M₁)
    (hA2bdd : ∀ τ, ∀ z : Point n, |A2 τ z| ≤ M₂)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hNormalForm : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
        D2H τ z = sTerm0 Y P Q A0 τ z + sTerm1 Y P A1 τ z + sTerm2 Y A2 τ z)
    (hIntT1 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z 0)) volume)
    (hIntT2 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z 0)) volume)
    (hIntT3 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (A0 (u - s) z * F s z 0)) volume)
    (hqLip : ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n, |A0 (u - s) z * F s z 0 - A0 (u - s) w * F s w 0| ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z 0) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * F s z 0| ≤ M)
    (hInt1 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm1 Y P A1 (u - s) z * F s z 0) volume)
    (hInt2 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm2 Y A2 (u - s) z * F s z 0) volume) :
    ∃ C_R : ℝ, 0 ≤ C_R ∧
      |∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z 0|
        ≤ ((15 / 2 * (n : ℝ) * L + C_R)
            + ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
                * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
                  + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
                  + ((n : ℝ) * C_W * C_P)
                    * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀))))
            * (2 * Real.sqrt ε)
          + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n)) * ε := by
  obtain ⟨C_E1, hC_E1nn, hE1⟩ := tE1_slice_bound Y P Q A0 F i M₀ C_L T a u ε τ₀ C_W C_P C_Q
    hM₀ hC_L hC_W hC_P hC_Q ha hau huT hε0 hεa hετ₀ hco hYdisp hJ3 hJ3Q hA0bdd hFdom
  exact witness_sliver2_complete D2H F Y P Q A0 A1 A2 i L M₀ M₁ M₂ C_L T a τ₀ C_W C_P C_Q C_E1
    hL hM₀ hM₁ hM₂ hC_L hC_W hC_P hC_Q hC_E1nn u ε ha hau huT hε0 hεu hεa hετ₀
    hco hYdisp hJ3 hJ3Q hA0bdd hA1bdd hA2bdd hFdom hNormalForm hE1 hIntT1 hIntT2 hIntT3
    hqLip hInt1 hInt2

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.oneD_absMoment10
#print axioms QIQTH.HeatResidualBound.gaussDdim_replace_bound_gen
#print axioms QIQTH.HeatResidualBound.rncRadialSq_diff_bound
#print axioms QIQTH.HeatResidualBound.gaussReplace_E1_bound
#print axioms QIQTH.HeatResidualBound.polyChart_abs_bound
#print axioms QIQTH.HeatResidualBound.tE1_slice_bound
#print axioms QIQTH.HeatResidualBound.hRemE1_discharge
#print axioms QIQTH.HeatResidualBound.witness_sliver2_grand
