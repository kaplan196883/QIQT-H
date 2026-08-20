/-
  GaussTauTraceCancellationLocalized — the SET-RESTRICTED (localized-domain) `∂_τ`-TRACE
  moment-cancellation Lipschitz bound: the flat cancellation `gaussian_hessian_cancel_trace`
  (full space ℝⁿ) transported to an integral over any measurable superset `Ω ⊇ ball 0 r`, at the
  cost of an EXPONENTIALLY-SUPPRESSED Gaussian tail remainder.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick — the "domain-bridge" companion of `gaussian_hessian_cancel_trace`
  identified by the gpt-5.6-sol strategic audit as the highest-leverage next unit for breaking the
  recurring "chart change-of-variables" wall of the `hCross`/`hGpow`/`hOn` census carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS BRICK (the chart-CoV audit finding).  After the banked EXACT change of variables
  `ChartIFTPackage.chart_gaussian_change_variables_concrete` (J4-270) transports the chart-composed
  census integrand `∫_{z∈ball 0 ρ} (∑ᵢ((W₀z)ᵢ²/4τ² − 1/2τ))·gaussDdim τ (W₀z)·A(z)` into the FLAT
  coordinate `∫_{w∈Ω} (∑ᵢ(wᵢ²/4τ² − 1/2τ))·gaussDdim τ w·q(w)` (with `q(w)=A(Vw)/|det f'(Vw)|`,
  `Ω = W₀''(ball 0 ρ) ∈ 𝓝 0`), the ONLY remaining gap to the τ^{−1/2} moment-cancellation bound is:
    (i) the domain is `Ω` (a neighbourhood of `0`), NOT all of ℝⁿ — the flat cancellation lives on ℝⁿ;
    (ii) `q` need only be bounded on `Ω` and Lipschitz — it is NOT globally defined off `Ω`.
  This file discharges (i): the difference `∫_ℝⁿ − ∫_Ω = ∫_{Ωᶜ}` is Gaussian-tail suppressed because
  `Ωᶜ ⊆ (ball 0 r)ᶜ = {‖z‖ ≥ r}` sits at distance `≥ r > 0` from the Gaussian peak `w = 0`, so it is
  `O(e^{−r²/8τ}·τ^{−1})`, which is `o(τ^{−1/2})`.  Thus the τ^{−1/2} cancellation SURVIVES restriction
  to `Ω`, up to a super-polynomially small (in `1/τ`) remainder.

  ## WHAT LANDS.
    • `hessCoord_abs_weighted_tail_le` — the per-coordinate ABSOLUTE weighted Gaussian tail moment:
        `∫_{z∈T} |((zᵢ)²−2τ)/(4τ²)·gaussDdim τ z·q(z)| ≤ M·(√2)ⁿ·e^{−r²/8τ}·(2n+1)/(2τ)`,
      for any measurable `T ⊆ {r ≤ ‖z‖}` and any measurable `q` bounded by `M`.  (Reuses the
      `OffCollarTailMoment` dominator `G` = `√2ⁿe^{−r²/8τ}` × doubled-time Gaussian pair, with the
      strict `<` in the banked `gaussDdim_tail_le_scaled` relaxed to `≤` — identical `nlinarith` core.)
    • `gaussian_hessian_cancel_trace_on_superset` — ★★ THE SET-RESTRICTED TRACE CANCELLATION BOUND.
        For `τ>0`, `r>0`, `q` `L`-Lipschitz + bounded (`|q|≤M`) + measurable, and ANY measurable
        `Ω ⊇ ball 0 r`,
          `|∫_{z∈Ω} (∑ᵢ((zᵢ)²/4τ² − 1/2τ))·gaussDdim τ z·q(z)|`
              `≤ L·(15/2·n²)/√τ  +  n·M·(√2)ⁿ·e^{−r²/8τ}·(2n+1)/(2τ)` .
      Route: `∫_ℝⁿ = ∫_Ω + ∫_{Ωᶜ}` (`integral_add_compl`), `|∫_ℝⁿ| ≤ L·(15/2·n²)/√τ`
      (`gaussian_hessian_cancel_trace`), and `|∫_{Ωᶜ}| ≤ ∫_{Ωᶜ}|·| ≤ ∑ᵢ (per-coord abs tail)` via the
      first lemma with `T = Ωᶜ ⊆ {r ≤ ‖z‖}`.
    • `gaussian_hessian_cancel_trace_on_superset_hyp_satisfiable` — non-vacuity EXHIBITED at the genuine
      NONCONSTANT weight `q z := cos(dist z 0)` on a PROPER superset `Ω = ball 0 5 ⊋ ball 0 1`.

  ⚠  STILL NOT `a₁ = R/6`.  Sol's second relaxation (ii) — dropping GLOBAL Lipschitz to Lipschitz on
  the inner ball only, so the transformed chart weight `q(w)=A(Vw)/|det f'(Vw)|` (defined only on `Ω`)
  can be fed WITHOUT a global extension — is left as the explicit follow-on.  The concrete chart wiring
  (transformed-weight boundedness + inner-ball Lipschitz from the banked near-identity Jacobian and
  resolvent Lipschitz) is NOT done here.  No `sorry`, no new axioms, no `:= True`, no vacuous
  hypothesis, none equal to the conclusion, no existing file edited.
-/
import Mathlib
import QIQTH.GaussTauTraceCancellation
import QIQTH.OffCollarTailMoment

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ `hessCoord_abs_weighted_tail_le` — the per-coordinate ABSOLUTE weighted Gaussian tail moment.**
    For any measurable `T ⊆ {z | r ≤ ‖z‖}` and any measurable `q` with `|q| ≤ M`,
        `∫_{z∈T} |((zᵢ)²−2τ)/(4τ²)·gaussDdim τ z·q(z)| ≤ M·(√2)ⁿ·e^{−r²/8τ}·(2n+1)/(2τ)`.
    Reuses the `OffCollarTailMoment` dominator with the strict `<` relaxed to `≤`.  NOT `a₁ = R/6`. -/
theorem hessCoord_abs_weighted_tail_le
    (τ r : ℝ) (hτ : 0 < τ) (hr : 0 ≤ r) (i : Fin n)
    (q : Point n → ℝ) (hqmeas : AEStronglyMeasurable q volume)
    (M : ℝ) (hM : ∀ z, |q z| ≤ M)
    (T : Set (Point n)) (hT : MeasurableSet T) (hTsub : T ⊆ {z : Point n | r ≤ ‖z‖}) :
    (∫ z in T, |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * q z|)
      ≤ M * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ))) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hτ0 : τ ≠ 0 := hτ.ne'
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  -- ≤-variant of `gaussDdim_tail_le_scaled` (identical core; strict `<` relaxed to `≤`).
  have tail_le : ∀ z : Point n, r ≤ ‖z‖ →
      gaussDdim τ z ≤ Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ)) * gaussDdim (2 * τ) z := by
    intro z hz
    have hRsq : r ^ 2 ≤ rncRadialSq z := by
      have h1 : r ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hz, hr, norm_nonneg z]
      exact le_trans h1 (norm_sq_le_rncRadialSq z)
    have hexp_le : Real.exp (-(rncRadialSq z) / (8 * τ)) ≤ Real.exp (-(r ^ 2) / (8 * τ)) := by
      apply Real.exp_le_exp.mpr
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith [hRsq]) (by positivity)
    rw [gaussDdim_eq_wide_mul hτ z, gaussDdimWide_eq_scaled_gaussDdim hτ z]
    have hg2 : 0 ≤ gaussDdim (2 * τ) z := gaussDdim_nonneg (2 * τ) z
    calc Real.exp (-(rncRadialSq z) / (8 * τ)) * (Real.sqrt 2 ^ n * gaussDdim (2 * τ) z)
        ≤ Real.exp (-(r ^ 2) / (8 * τ)) * (Real.sqrt 2 ^ n * gaussDdim (2 * τ) z) :=
          mul_le_mul_of_nonneg_right hexp_le (by positivity)
      _ = Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ)) * gaussDdim (2 * τ) z := by ring
  -- the OffCollar dominator `G` and its integral.
  set C : ℝ := Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ)) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  set G : Point n → ℝ :=
    fun z => C * (1 / (4 * τ ^ 2) * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
                    + 1 / (2 * τ) * gaussDdim (2 * τ) z) with hGdef
  have hmom2 : ∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z ≤ 4 * (n : ℝ) * τ := by
    have h := normPow_gauss_tau (n := n) 2 (by norm_num) 2 (by norm_num) (2 * τ) h2τ
      (oneD_absMoment2 (2 * τ) h2τ)
    have hsq : (n : ℝ) * 2 * (Real.sqrt (2 * τ)) ^ 2 = 4 * (n : ℝ) * τ := by
      rw [Real.sq_sqrt h2τ.le]; ring
    linarith [h, hsq]
  have hI2 : Integrable (fun z : Point n => ‖z‖ ^ 2 * gaussDdim (2 * τ) z) volume :=
    normPow_gauss_integrable 2 (by norm_num) (2 * τ) h2τ
  have hI0 : Integrable (fun z : Point n => gaussDdim (2 * τ) z) volume :=
    gaussDdim_integrable (2 * τ) h2τ
  have hGint : Integrable G volume := by
    rw [hGdef]
    exact ((hI2.const_mul (1 / (4 * τ ^ 2))).add (hI0.const_mul (1 / (2 * τ)))).const_mul C
  have hGnn : ∀ z, 0 ≤ G z := by
    intro z
    rw [hGdef]
    have hg2 : 0 ≤ gaussDdim (2 * τ) z := gaussDdim_nonneg (2 * τ) z
    refine mul_nonneg hCnn (add_nonneg ?_ ?_)
    · exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) hg2)
    · exact mul_nonneg (by positivity) hg2
  have hInt_G : ∫ z, G z ≤ C * ((2 * (n : ℝ) + 1) / (2 * τ)) := by
    have hEq : ∫ z, G z
        = C * (1 / (4 * τ ^ 2) * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z)
                + 1 / (2 * τ) * (∫ z : Point n, gaussDdim (2 * τ) z)) := by
      rw [hGdef, integral_const_mul]
      congr 1
      rw [integral_add (hI2.const_mul _) (hI0.const_mul _), integral_const_mul, integral_const_mul]
    calc ∫ z, G z
        = C * (1 / (4 * τ ^ 2) * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z) + 1 / (2 * τ) * 1) := by
          rw [hEq, gaussDdim_integral_eq_one (2 * τ) h2τ]
      _ ≤ C * (1 / (4 * τ ^ 2) * (4 * (n : ℝ) * τ) + 1 / (2 * τ) * 1) := by
          apply mul_le_mul_of_nonneg_left _ hCnn
          gcongr
      _ = C * ((2 * (n : ℝ) + 1) / (2 * τ)) := by field_simp
  -- pointwise domination of the abs weighted integrand on `T` by `M · G`.
  have hpt : ∀ z ∈ T, |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * q z| ≤ M * G z := by
    intro z hz
    have hznorm : r ≤ ‖z‖ := hTsub hz
    have hg1 : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
    have hzi_norm : |z i| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z i
    have hzi_sq : (z i) ^ 2 ≤ ‖z‖ ^ 2 := by
      nlinarith [hzi_norm, abs_nonneg (z i), sq_abs (z i), norm_nonneg z]
    have habs : |(z i) ^ 2 - 2 * τ| ≤ ‖z‖ ^ 2 + 2 * τ := by
      rw [abs_le]; constructor <;> nlinarith [hzi_sq, hτ, sq_nonneg (z i), norm_nonneg z]
    have hweight : |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 4 * τ ^ 2 by positivity)]
      gcongr
    have habs_eq : |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * q z|
        = |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |q z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hg1]
    have hnum_nn : (0 : ℝ) ≤ ‖z‖ ^ 2 + 2 * τ := add_nonneg (sq_nonneg _) (by linarith)
    have hfrac_nn : (0 : ℝ) ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := div_nonneg hnum_nn (by positivity)
    have hg2 : 0 ≤ gaussDdim (2 * τ) z := gaussDdim_nonneg (2 * τ) z
    have hXnn : (0 : ℝ) ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) * (C * gaussDdim (2 * τ) z) :=
      mul_nonneg hfrac_nn (mul_nonneg hCnn hg2)
    have hinner : |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z
        ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) * (C * gaussDdim (2 * τ) z) :=
      mul_le_mul hweight (tail_le z hznorm) hg1 hfrac_nn
    have hstep : |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |q z|
        ≤ ((‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) * (C * gaussDdim (2 * τ) z)) * M :=
      mul_le_mul hinner (hM z) (abs_nonneg _) hXnn
    have hEq : (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) * (C * gaussDdim (2 * τ) z) * M = M * G z := by
      simp only [hGdef]; field_simp; ring
    rw [habs_eq]
    exact hstep.trans_eq hEq
  -- integrability of the abs weighted integrand.
  have hInt_abs : Integrable
      (fun z : Point n => |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * q z|) volume :=
    (hess_coord_gaussDdim_q_integrable τ hτ i q hqmeas M hM).abs
  calc (∫ z in T, |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * q z|)
      ≤ ∫ z in T, M * G z :=
        setIntegral_mono_on hInt_abs.integrableOn (hGint.const_mul M).integrableOn hT hpt
    _ = M * ∫ z in T, G z := integral_const_mul _ _
    _ ≤ M * ∫ z, G z := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        exact setIntegral_le_integral hGint (ae_of_all _ hGnn)
    _ ≤ M * (C * ((2 * (n : ℝ) + 1) / (2 * τ))) := mul_le_mul_of_nonneg_left hInt_G hM0
    _ = M * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ))) := by
        rw [hCdef]

/-- **★★ `gaussian_hessian_cancel_trace_on_superset` — THE SET-RESTRICTED TRACE CANCELLATION BOUND.**
    For `τ>0`, `r>0`, `q` `L`-Lipschitz + bounded (`|q|≤M`) + measurable, and ANY measurable
    `Ω ⊇ ball 0 r`,
      `|∫_{z∈Ω} (∑ᵢ((zᵢ)²/4τ² − 1/2τ))·gaussDdim τ z·q(z)|`
          `≤ L·(15/2·n²)/√τ  +  n·M·(√2)ⁿ·e^{−r²/8τ}·(2n+1)/(2τ)` .
    The full-space cancellation (`gaussian_hessian_cancel_trace`) supplies the `τ^{−1/2}` main term; the
    domain restriction `Ω ⊆ ℝⁿ` costs only the exponentially-suppressed Gaussian tail over `Ωᶜ ⊆
    {‖z‖ ≥ r}` (`hessCoord_abs_weighted_tail_le` summed over the `n` coordinates).  NOT `a₁ = R/6`. -/
theorem gaussian_hessian_cancel_trace_on_superset
    (τ r : ℝ) (hτ : 0 < τ) (hr : 0 < r) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) (M : ℝ) (hM : ∀ z, |q z| ≤ M)
    (Ω : Set (Point n)) (hΩ : MeasurableSet Ω) (hball : Metric.ball (0 : Point n) r ⊆ Ω) :
    |∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q z|
      ≤ L * (15 / 2 * (n : ℝ) ^ 2) / Real.sqrt τ
        + (n : ℝ) * (M * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ))
            * ((2 * (n : ℝ) + 1) / (2 * τ)))) := by
  -- per-coordinate summands.
  set g : Fin n → Point n → ℝ :=
    fun i z => ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * q z with hgdef
  have hint : ∀ i : Fin n, Integrable (g i) volume := by
    intro i; rw [hgdef]
    exact hess_coord_gaussDdim_q_integrable τ hτ i q hqmeas M hM
  -- pointwise: the trace integrand equals `∑ᵢ g i`.
  have hpt : ∀ z : Point n,
      (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q z = ∑ i, g i z := by
    intro z
    rw [hgdef, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hc : (z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ) = ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) := by
      field_simp; ring
    rw [hc]
  set F : Point n → ℝ :=
    fun z => (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q z with hFdef
  have hFeq : F = fun z => ∑ i, g i z := by funext z; rw [hFdef]; exact hpt z
  have hFint : Integrable F volume := by
    rw [hFeq]; exact integrable_finsetSum _ (fun i _ => hint i)
  -- split `∫_ℝⁿ = ∫_Ω + ∫_{Ωᶜ}`.
  have hsplit : (∫ z in Ω, F z) + (∫ z in Ωᶜ, F z) = ∫ z, F z :=
    integral_add_compl hΩ hFint
  have hΩint : (∫ z in Ω, F z) = (∫ z, F z) - (∫ z in Ωᶜ, F z) := by linarith [hsplit]
  -- main term: full-space cancellation.
  have hmain : |∫ z, F z| ≤ L * (15 / 2 * (n : ℝ) ^ 2) / Real.sqrt τ := by
    rw [hFdef]
    exact gaussian_hessian_cancel_trace τ hτ q L hL hq hqmeas ⟨M, hM⟩
  -- tail term: `Ωᶜ ⊆ {r ≤ ‖z‖}`, then abs-triangle + per-coord tail.
  have hcompl_sub : Ωᶜ ⊆ {z : Point n | r ≤ ‖z‖} := by
    intro z hz
    simp only [Set.mem_setOf_eq]
    by_contra h
    push_neg at h
    exact hz (hball (mem_ball_zero_iff.mpr h))
  have hcomplmeas : MeasurableSet Ωᶜ := hΩ.compl
  have htail : |∫ z in Ωᶜ, F z|
      ≤ (n : ℝ) * (M * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ))
          * ((2 * (n : ℝ) + 1) / (2 * τ)))) := by
    calc |∫ z in Ωᶜ, F z|
        ≤ ∫ z in Ωᶜ, |F z| := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := volume.restrict Ωᶜ) (f := F)
      _ ≤ ∫ z in Ωᶜ, ∑ i, |g i z| := by
          refine setIntegral_mono_on ?_ ?_ hcomplmeas (fun z _ => ?_)
          · exact (hFint.abs).integrableOn
          · exact (integrable_finsetSum _ (fun i _ => (hint i).abs)).integrableOn
          · rw [hFeq]; exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, ∫ z in Ωᶜ, |g i z| := by
          rw [integral_finsetSum _ (fun i _ => ((hint i).abs).integrableOn)]
      _ ≤ ∑ _i : Fin n,
            M * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ))
              * ((2 * (n : ℝ) + 1) / (2 * τ))) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [hgdef]
          exact hessCoord_abs_weighted_tail_le τ r hτ hr.le i q hqmeas M hM Ωᶜ hcomplmeas hcompl_sub
      _ = (n : ℝ) * (M * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ))
            * ((2 * (n : ℝ) + 1) / (2 * τ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- combine.
  calc |∫ z in Ω, F z|
      = |(∫ z, F z) - (∫ z in Ωᶜ, F z)| := by rw [hΩint]
    _ ≤ |∫ z, F z| + |∫ z in Ωᶜ, F z| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ L * (15 / 2 * (n : ℝ) ^ 2) / Real.sqrt τ
          + (n : ℝ) * (M * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ))
              * ((2 * (n : ℝ) + 1) / (2 * τ)))) := add_le_add hmain htail

/-- **Non-vacuity witness.**  The hypothesis bundle is jointly satisfiable at the genuine NONCONSTANT
    bounded Lipschitz weight `q z := cos(dist z 0)` (`|q|≤1`, `L=1`) on a PROPER superset
    `Ω = ball 0 5 ⊋ ball 0 1` (`r = 1`).  So the bound fires on a real weight and a real, non-trivial
    superset, not an empty/degenerate bundle.  NOT `a₁ = R/6`. -/
theorem gaussian_hessian_cancel_trace_on_superset_hyp_satisfiable :
    ∃ (r : ℝ) (q : Point n → ℝ) (L M : ℝ) (Ω : Set (Point n)),
      0 < r ∧ 0 ≤ L ∧ (∀ z w, |q z - q w| ≤ L * dist z w) ∧
        AEStronglyMeasurable q (volume : Measure (Point n)) ∧ (∀ z, |q z| ≤ M) ∧
        MeasurableSet Ω ∧ Metric.ball (0 : Point n) r ⊆ Ω := by
  refine ⟨1, fun z => Real.cos (dist z (0 : Point n)), 1, 1, Metric.ball (0 : Point n) 5,
    one_pos, zero_le_one, ?_, ?_, ?_, measurableSet_ball, ?_⟩
  · intro z w
    show |Real.cos (dist z (0 : Point n)) - Real.cos (dist w (0 : Point n))| ≤ 1 * dist z w
    rw [one_mul]
    exact (Real.abs_cos_sub_cos_le _ _).trans (abs_dist_sub_le z w (0 : Point n))
  · exact (Real.continuous_cos.comp (continuous_id.dist continuous_const)).aestronglyMeasurable
  · intro z; exact Real.abs_cos_le_one _
  · exact Metric.ball_subset_ball (by norm_num)

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms hessCoord_abs_weighted_tail_le
#print axioms gaussian_hessian_cancel_trace_on_superset
#print axioms gaussian_hessian_cancel_trace_on_superset_hyp_satisfiable
end AxiomChecks
