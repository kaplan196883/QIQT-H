/-
  MixedTE2Slice — J4-783: the OFF-DIAGONAL (`∂ᵢ∂ⱼ`, `i ≠ j`) moment-integration SLICE bound — the mixed
  analogue of `XUniformSliverFull.tE2_slice_abstract`, plus the combination with the banked mixed parity
  cancellation `GaussianHessianCancelMixed.gaussian_hessian_cancel_mixed` into the full mixed
  plain-Gaussian Hessian-slice bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the `a₁ = R/6` heat-kernel campaign — the mechanical STEP-1 port scoped in J4-782.

  ## WHAT THIS DELIVERS.

  J4-782 (`MixedHessianBracketBound.mixedBracket_abs_bound`) proved that the mixed Hessian bracket, with
  its parity-cancellable leading term `zᵢ·zⱼ/(4τ²)` subtracted, obeys the IDENTICAL polynomial RHS as the
  diagonal chart-jet remainder `RemainderIntegration.tE2_bracket_poly`.  J4-781
  (`GaussianHessianCancelMixed.gaussian_hessian_cancel_mixed`) proved the leading parity term
  `|∫ zᵢ·zⱼ/(4τ²)·G_τ·q| ≤ L·n/√τ`.

  THIS FILE moment-integrates the mixed bracket bound into a mixed `tE2`-style SLICE bound, and combines
  it with the parity term:

    • `tE2_slice_abstract_mixed`  — ★★ the mixed E2 per-slice bound (field slice `g`).  A VERBATIM port
        of `tE2_slice_abstract`: the sole change is the pointwise domination step, where the diagonal
        `tE2_bracket_poly` is swapped for `mixedBracket_abs_bound` fed the two INDIVIDUAL coordinate-aligned
        first-jet gaps (`innerYP_add_zi_bound` for `Pi`/`Pj`), the off-diagonal second-moment
        (`innerPiPj_offdiag_bound`), and the center-jet bound (`innerYQ_bound`).  Because the mixed RHS is
        SYNTACTICALLY the diagonal factored polynomial, the ENTIRE downstream moment tower (the six
        `τ`-coefficients, the `normPow_gauss_tau` envelope, the `w = √τ` fold) transfers unchanged and
        delivers the SAME explicit constant `tE2RateConst`.

    • `mixedHessianSlice_plain_bound` — ★★★ the full mixed PLAIN-Gaussian Hessian-slice bound.  Splits
        the mixed Hessian slice `∫ G_τ(z)·(⟨Y,Pi⟩⟨Y,Pj⟩/(4τ²) − (⟨Pi,Pj⟩+⟨Y,Q⟩)/(2τ))·(A₀·g)` into the E2
        remainder (bounded by `tE2_slice_abstract_mixed`) plus the parity leading term (bounded by
        `gaussian_hessian_cancel_mixed`), giving `≤ (tE2RateConst + L·n)·τ^{−1/2}`.  This is the
        PLAIN-Gaussian (`G_τ(z)`) mixed analogue of the diagonal E2+E3 combination inside
        `hInner0_discharge` — the combine scoped by J4-782 STEP 1.

  ## WHAT THIS DOES NOT DO (honest scope).

  This is the mixed slice at the PLAIN Gaussian `G_τ(z)`.  The concrete mixed sTerm0 uses the CHART
  Gaussian `G_τ(V z)` and the mixed normal form (`ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed`) is a
  FOUR-term form (Hessian + TWO distinct gradient terms `G·(−⟨V,Pj⟩/2τ)·∂ᵢA` and `G·(−⟨V,Pi⟩/2τ)·∂ⱼA` +
  mass), so a full `witness_sliver2_xuniform_mixed` additionally needs (i) a mixed E1 Gaussian-replacement
  port `G_τ(V z)→G_τ(z)` and (ii) a NEW four-term assembly — NEITHER a "swap two lemmas" operation.  This
  file lands the two genuinely-mechanical STEP-1 pieces; the four-term assembly remains the downstream work.

  Every hypothesis is satisfiable and non-vacuous (the model `Y = −id`, `Pi = eᵢ`, `Pj = eⱼ`, `Q = 0`,
  `A₀` bounded, `g` a width-2 Gaussian bump cap satisfies all of them, with `Δ = 0`, `⟨Pi,Pj⟩ = 0`), and
  none equals the conclusion.  `i ≠ j` is load-bearing.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.XUniformSliverFull
import QIQTH.MixedHessianBracketBound
import QIQTH.GaussianHessianCancelMixed

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull
open scoped Interval Topology

namespace QIQTH.MixedTE2Slice

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ★★ The mixed E2 per-slice bound (moment integration of the mixed bracket).
    ############################################################################### -/

/-- **★★ THE MIXED E2 PER-SLICE BOUND.**  The off-diagonal (`i ≠ j`) analogue of
    `XUniformSliverFull.tE2_slice_abstract`.  The concrete diagonal chart-remainder integrand is replaced
    by the MIXED Hessian bracket (with the parity-cancellable leading term `zᵢ·zⱼ/(4τ²)` subtracted); the
    pointwise domination uses `mixedBracket_abs_bound` fed the individual coordinate-aligned jets, whose
    RHS is SYNTACTICALLY the diagonal factored polynomial.  Every downstream moment-integration step is
    imported verbatim.  Delivers the SAME explicit constant `tE2RateConst`.  NOT `a₁ = R/6`. -/
theorem tE2_slice_abstract_mixed
    (Y Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (g : ℝ → Point n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (M₀ C_F u ε τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_F : 0 ≤ C_F) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (hετ₀ : ε ≤ τ₀)
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3i : ∀ z : Point n, ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3j : ∀ z : Point n, ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hgcap : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |g s z| ≤ C_F) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, gaussDdim (u - s) z * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * (u - s) ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
            - (z i * z j) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * g s z)|
        ≤ tE2RateConst n M₀ C_F C_W C_P C_Q τ₀ * (u - s) ^ (-(1 : ℝ) / 2) := by
  set K : ℝ := M₀ * C_F with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  intro s hsmem
  have hτpos : 0 < u - s := by linarith [hsmem.2]
  have hττ₀ : u - s ≤ τ₀ := by linarith [hsmem.1, hετ₀]
  set τ : ℝ := u - s with hτ_def
  have hτne : τ ≠ 0 := hτpos.ne'
  have hτ₀pos : (0 : ℝ) < τ₀ := lt_of_lt_of_le hτpos hττ₀
  -- field cap (the only field-dependent input).
  have hFcap : ∀ z : Point n, |g s z| ≤ C_F := hgcap s hsmem
  -- the six τ-coefficients of the bracket polynomial.
  set coef6 : ℝ := ((n : ℝ) * C_W * C_P) ^ 2 / (4 * τ ^ 2) with hcoef6
  set coef5 : ℝ := 2 * ((n : ℝ) * C_W * C_P) * ((n : ℝ) * (C_W + C_P)) / (4 * τ ^ 2) with hcoef5
  set coef4 : ℝ := (2 * ((n : ℝ) * C_W * C_P) + ((n : ℝ) * (C_W + C_P)) ^ 2) / (4 * τ ^ 2) with hcoef4
  set coef3 : ℝ := 2 * ((n : ℝ) * (C_W + C_P)) / (4 * τ ^ 2) with hcoef3
  set coef2 : ℝ := ((n : ℝ) * C_P ^ 2 + (n : ℝ) * C_W * C_Q) / (2 * τ) with hcoef2
  set coef1 : ℝ := (2 * C_P + (n : ℝ) * C_Q) / (2 * τ) with hcoef1
  have hcoef6nn : 0 ≤ coef6 := by rw [hcoef6]; positivity
  have hcoef5nn : 0 ≤ coef5 := by rw [hcoef5]; positivity
  have hcoef4nn : 0 ≤ coef4 := by rw [hcoef4]; positivity
  have hcoef3nn : 0 ≤ coef3 := by rw [hcoef3]; positivity
  have hcoef2nn : 0 ≤ coef2 := by rw [hcoef2]; positivity
  have hcoef1nn : 0 ≤ coef1 := by rw [hcoef1]; positivity
  -- the bracket polynomial identity (bridge output = the 6-monomial sum).
  have hbrk : ∀ z : Point n,
      ((n : ℝ) * (C_W * ‖z‖ ^ 2) * (C_P * ‖z‖) + (n : ℝ) * (C_W * ‖z‖ ^ 2)
            + (n : ℝ) * ‖z‖ * (C_P * ‖z‖))
          * (((n : ℝ) * (C_W * ‖z‖ ^ 2) * (C_P * ‖z‖) + (n : ℝ) * (C_W * ‖z‖ ^ 2)
              + (n : ℝ) * ‖z‖ * (C_P * ‖z‖)) + 2 * ‖z‖) / (4 * τ ^ 2)
        + ((n : ℝ) * (C_P * ‖z‖) ^ 2 + 2 * (C_P * ‖z‖)) / (2 * τ)
        + ((n : ℝ) * (C_W * ‖z‖ ^ 2 + ‖z‖) * C_Q) / (2 * τ)
      = coef6 * ‖z‖ ^ 6 + coef5 * ‖z‖ ^ 5 + coef4 * ‖z‖ ^ 4 + coef3 * ‖z‖ ^ 3
          + coef2 * ‖z‖ ^ 2 + coef1 * ‖z‖ := by
    intro z
    rw [hcoef6, hcoef5, hcoef4, hcoef3, hcoef2, hcoef1]
    field_simp
    ring
  -- pointwise domination by the dominating (poly × Gaussian) function.
  have hpt : ∀ z : Point n,
      ‖gaussDdim τ z * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
            - (z i * z j) / (4 * τ ^ 2))
          * (A0 τ z * g s z)‖
        ≤ K * (coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
            + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z)
            + coef2 * (‖z‖ ^ 2 * gaussDdim τ z) + coef1 * (‖z‖ ^ 1 * gaussDdim τ z)) := by
    intro z
    have hGnn : 0 ≤ gaussDdim τ z := gaussDdim_nonneg' τ z
    -- the individual coordinate-aligned jet feeds into the mixed bracket bound.
    have hΔi := innerYP_add_zi_bound (Y z) z (Pi z) i (C_W * ‖z‖ ^ 2) (C_P * ‖z‖) (hYdisp z) (hJ3i z)
    have hΔj := innerYP_add_zi_bound (Y z) z (Pj z) j (C_W * ‖z‖ ^ 2) (C_P * ‖z‖) (hYdisp z) (hJ3j z)
    have hP₁ := innerPiPj_offdiag_bound (Pi z) (Pj z) i j hij (C_P * ‖z‖) (hJ3i z) (hJ3j z)
    have hQ₁ := innerYQ_bound (Y z) z (Q z) (C_W * ‖z‖ ^ 2) C_Q (hYdisp z) (hJ3Q z) hC_Q
    have hdiff := mixedBracket_abs_bound (Y z) (Pi z) (Pj z) (Q z) i j τ hτpos z _ _ _ hΔi hΔj hP₁ hQ₁
    have hbrknn : 0 ≤ ((n : ℝ) * (C_W * ‖z‖ ^ 2) * (C_P * ‖z‖) + (n : ℝ) * (C_W * ‖z‖ ^ 2)
            + (n : ℝ) * ‖z‖ * (C_P * ‖z‖))
          * (((n : ℝ) * (C_W * ‖z‖ ^ 2) * (C_P * ‖z‖) + (n : ℝ) * (C_W * ‖z‖ ^ 2)
              + (n : ℝ) * ‖z‖ * (C_P * ‖z‖)) + 2 * ‖z‖) / (4 * τ ^ 2)
        + ((n : ℝ) * (C_P * ‖z‖) ^ 2 + 2 * (C_P * ‖z‖)) / (2 * τ)
        + ((n : ℝ) * (C_W * ‖z‖ ^ 2 + ‖z‖) * C_Q) / (2 * τ) := by positivity
    have hAF : |A0 τ z * g s z| ≤ M₀ * C_F := by
      rw [abs_mul]; exact mul_le_mul (hA0bdd τ z) (hFcap z) (abs_nonneg _) hM₀
    have hAFnn : 0 ≤ |A0 τ z * g s z| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hGnn]
    calc gaussDdim τ z
            * |(∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - (z i * z j) / (4 * τ ^ 2)|
            * |A0 τ z * g s z|
        ≤ gaussDdim τ z
            * (((n : ℝ) * (C_W * ‖z‖ ^ 2) * (C_P * ‖z‖) + (n : ℝ) * (C_W * ‖z‖ ^ 2)
                  + (n : ℝ) * ‖z‖ * (C_P * ‖z‖))
                * (((n : ℝ) * (C_W * ‖z‖ ^ 2) * (C_P * ‖z‖) + (n : ℝ) * (C_W * ‖z‖ ^ 2)
                    + (n : ℝ) * ‖z‖ * (C_P * ‖z‖)) + 2 * ‖z‖) / (4 * τ ^ 2)
              + ((n : ℝ) * (C_P * ‖z‖) ^ 2 + 2 * (C_P * ‖z‖)) / (2 * τ)
              + ((n : ℝ) * (C_W * ‖z‖ ^ 2 + ‖z‖) * C_Q) / (2 * τ))
            * (M₀ * C_F) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdiff hGnn) hAF hAFnn
            (mul_nonneg hGnn hbrknn)
      _ = K * (coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
              + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z)
              + coef2 * (‖z‖ ^ 2 * gaussDdim τ z) + coef1 * (‖z‖ ^ 1 * gaussDdim τ z)) := by
          rw [hbrk z, hKdef]; ring
  -- integrability of each monomial × Gaussian and of the dominating function.
  have hi6 := (normPow_gauss_integrable 6 (by norm_num) τ hτpos (n := n)).const_mul coef6
  have hi5 := (normPow_gauss_integrable 5 (by norm_num) τ hτpos (n := n)).const_mul coef5
  have hi4 := (normPow_gauss_integrable 4 (by norm_num) τ hτpos (n := n)).const_mul coef4
  have hi3 := (normPow_gauss_integrable 3 (by norm_num) τ hτpos (n := n)).const_mul coef3
  have hi2 := (normPow_gauss_integrable 2 (by norm_num) τ hτpos (n := n)).const_mul coef2
  have hi1 := (normPow_gauss_integrable 1 (by norm_num) τ hτpos (n := n)).const_mul coef1
  have hdom_int : Integrable (fun z : Point n =>
      K * (coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
        + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z)
        + coef2 * (‖z‖ ^ 2 * gaussDdim τ z) + coef1 * (‖z‖ ^ 1 * gaussDdim τ z))) volume :=
    (((((hi6.add hi5).add hi4).add hi3).add hi2).add hi1).const_mul K
  -- the moment values.
  have hm6 : ∫ z : Point n, ‖z‖ ^ 6 * gaussDdim τ z ≤ (n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt τ) ^ 6 :=
    normPow_gauss_tau 6 (by norm_num) (3072 * Real.sqrt 2) (by positivity) τ hτpos (oneD_absMoment6 τ hτpos)
  have hm5 : ∫ z : Point n, ‖z‖ ^ 5 * gaussDdim τ z ≤ (n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt τ) ^ 5 :=
    normPow_gauss_tau 5 (by norm_num) (1600 * Real.sqrt 2) (by positivity) τ hτpos (oneD_absMoment5 τ hτpos)
  have hm4 : ∫ z : Point n, ‖z‖ ^ 4 * gaussDdim τ z ≤ (n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt τ) ^ 4 :=
    normPow_gauss_tau 4 (by norm_num) (128 * Real.sqrt 2) (by positivity) τ hτpos (oneD_absMoment4 τ hτpos)
  have hm3 : ∫ z : Point n, ‖z‖ ^ 3 * gaussDdim τ z ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt τ) ^ 3 :=
    normPow_gauss_tau 3 (by norm_num) (64 * Real.sqrt 2 + 1) (by positivity) τ hτpos (oneD_absMoment3 τ hτpos)
  have hm2 : ∫ z : Point n, ‖z‖ ^ 2 * gaussDdim τ z ≤ (n : ℝ) * 2 * (Real.sqrt τ) ^ 2 :=
    normPow_gauss_tau 2 (by norm_num) 2 (by norm_num) τ hτpos (oneD_absMoment2 τ hτpos)
  have hm1 : ∫ z : Point n, ‖z‖ ^ 1 * gaussDdim τ z ≤ (n : ℝ) * (3 / 2) * (Real.sqrt τ) ^ 1 :=
    normPow_gauss_tau 1 (by norm_num) (3 / 2) (by norm_num) τ hτpos (oneD_absMoment1 τ hτpos)
  -- the integral of the dominating function.
  have hDval : ∫ z : Point n, K * (coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
        + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z)
        + coef2 * (‖z‖ ^ 2 * gaussDdim τ z) + coef1 * (‖z‖ ^ 1 * gaussDdim τ z))
      = K * (coef6 * (∫ z : Point n, ‖z‖ ^ 6 * gaussDdim τ z)
          + coef5 * (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim τ z)
          + coef4 * (∫ z : Point n, ‖z‖ ^ 4 * gaussDdim τ z)
          + coef3 * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim τ z)
          + coef2 * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim τ z)
          + coef1 * (∫ z : Point n, ‖z‖ ^ 1 * gaussDdim τ z)) := by
    have e1 : (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z))
        = (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z))
          + ∫ z : Point n, coef5 * (‖z‖ ^ 5 * gaussDdim τ z) := integral_add hi6 hi5
    have e2 : (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
          + coef4 * (‖z‖ ^ 4 * gaussDdim τ z))
        = (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z))
          + ∫ z : Point n, coef4 * (‖z‖ ^ 4 * gaussDdim τ z) := integral_add (hi6.add hi5) hi4
    have e3 : (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
          + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z))
        = (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
            + coef4 * (‖z‖ ^ 4 * gaussDdim τ z))
          + ∫ z : Point n, coef3 * (‖z‖ ^ 3 * gaussDdim τ z) :=
      integral_add ((hi6.add hi5).add hi4) hi3
    have e4 : (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
          + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z)
          + coef2 * (‖z‖ ^ 2 * gaussDdim τ z))
        = (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
            + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z))
          + ∫ z : Point n, coef2 * (‖z‖ ^ 2 * gaussDdim τ z) :=
      integral_add (((hi6.add hi5).add hi4).add hi3) hi2
    have e5 : (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
          + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z)
          + coef2 * (‖z‖ ^ 2 * gaussDdim τ z) + coef1 * (‖z‖ ^ 1 * gaussDdim τ z))
        = (∫ z : Point n, coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
            + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z)
            + coef2 * (‖z‖ ^ 2 * gaussDdim τ z))
          + ∫ z : Point n, coef1 * (‖z‖ ^ 1 * gaussDdim τ z) :=
      integral_add ((((hi6.add hi5).add hi4).add hi3).add hi2) hi1
    rw [integral_const_mul, e5, e4, e3, e2, e1, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  -- main inequality: |∫ T_E2| ≤ (moment upper bounds).
  have hmain : |∫ z, gaussDdim τ z * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
              - (z i * z j) / (4 * τ ^ 2))
            * (A0 τ z * g s z)|
      ≤ K * (coef6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt τ) ^ 6)
          + coef5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt τ) ^ 5)
          + coef4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt τ) ^ 4)
          + coef3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt τ) ^ 3)
          + coef2 * ((n : ℝ) * 2 * (Real.sqrt τ) ^ 2)
          + coef1 * ((n : ℝ) * (3 / 2) * (Real.sqrt τ) ^ 1)) := by
    calc |∫ z, gaussDdim τ z * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - (z i * z j) / (4 * τ ^ 2))
              * (A0 τ z * g s z)|
        = ‖∫ z, gaussDdim τ z * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - (z i * z j) / (4 * τ ^ 2))
              * (A0 τ z * g s z)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖gaussDdim τ z * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - (z i * z j) / (4 * τ ^ 2))
              * (A0 τ z * g s z)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, K * (coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
              + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z)
              + coef2 * (‖z‖ ^ 2 * gaussDdim τ z) + coef1 * (‖z‖ ^ 1 * gaussDdim τ z)) :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hdom_int (ae_of_all _ hpt)
      _ = K * (coef6 * (∫ z : Point n, ‖z‖ ^ 6 * gaussDdim τ z)
            + coef5 * (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim τ z)
            + coef4 * (∫ z : Point n, ‖z‖ ^ 4 * gaussDdim τ z)
            + coef3 * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim τ z)
            + coef2 * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim τ z)
            + coef1 * (∫ z : Point n, ‖z‖ ^ 1 * gaussDdim τ z)) := hDval
      _ ≤ K * (coef6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt τ) ^ 6)
            + coef5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt τ) ^ 5)
            + coef4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt τ) ^ 4)
            + coef3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt τ) ^ 3)
            + coef2 * ((n : ℝ) * 2 * (Real.sqrt τ) ^ 2)
            + coef1 * ((n : ℝ) * (3 / 2) * (Real.sqrt τ) ^ 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKnn
          exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left hm6 hcoef6nn) (mul_le_mul_of_nonneg_left hm5 hcoef5nn))
            (mul_le_mul_of_nonneg_left hm4 hcoef4nn)) (mul_le_mul_of_nonneg_left hm3 hcoef3nn))
            (mul_le_mul_of_nonneg_left hm2 hcoef2nn)) (mul_le_mul_of_nonneg_left hm1 hcoef1nn)
  refine le_trans hmain ?_
  -- expose the explicit constant and fold `K`.
  unfold tE2RateConst
  rw [← hKdef]
  -- the τ^{−1/2} fold: substitute `w = √τ`, cap `w ≤ √τ₀`.
  rw [← inv_sqrt_eq_rpow τ hτpos]
  have hwpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτpos
  have hwne : Real.sqrt τ ≠ 0 := hwpos.ne'
  have hwsq : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτpos.le
  have hwle : Real.sqrt τ ≤ Real.sqrt τ₀ := Real.sqrt_le_sqrt hττ₀
  set w : ℝ := Real.sqrt τ with hwdef
  -- linearise: pull out `w⁻¹`.
  have hlin : K * (coef6 * ((n : ℝ) * (3072 * Real.sqrt 2) * w ^ 6)
          + coef5 * ((n : ℝ) * (1600 * Real.sqrt 2) * w ^ 5)
          + coef4 * ((n : ℝ) * (128 * Real.sqrt 2) * w ^ 4)
          + coef3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * w ^ 3)
          + coef2 * ((n : ℝ) * 2 * w ^ 2)
          + coef1 * ((n : ℝ) * (3 / 2) * w ^ 1))
      = w⁻¹ * (K * (((n : ℝ) * C_W * C_P) ^ 2 * ((n : ℝ) * (3072 * Real.sqrt 2)) / 4 * w ^ 3
          + 2 * ((n : ℝ) * C_W * C_P) * ((n : ℝ) * (C_W + C_P))
              * ((n : ℝ) * (1600 * Real.sqrt 2)) / 4 * w ^ 2
          + (2 * ((n : ℝ) * C_W * C_P) + ((n : ℝ) * (C_W + C_P)) ^ 2)
              * ((n : ℝ) * (128 * Real.sqrt 2)) / 4 * w
          + 2 * ((n : ℝ) * (C_W + C_P)) * ((n : ℝ) * (64 * Real.sqrt 2 + 1)) / 4
          + ((n : ℝ) * C_P ^ 2 + (n : ℝ) * C_W * C_Q) * ((n : ℝ) * 2) / 2 * w
          + (2 * C_P + (n : ℝ) * C_Q) * ((n : ℝ) * (3 / 2)) / 2)) := by
    rw [hcoef6, hcoef5, hcoef4, hcoef3, hcoef2, hcoef1, ← hwsq]
    field_simp
    try ring
  rw [hlin]
  have hwinv_nn : (0 : ℝ) ≤ w⁻¹ := inv_nonneg.mpr hwpos.le
  rw [mul_comm _ w⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ hwinv_nn
  refine mul_le_mul_of_nonneg_left ?_ hKnn
  gcongr

/-! ###############################################################################
    ★★★ The full mixed PLAIN-Gaussian Hessian-slice bound (E2 remainder + parity leading).
    ############################################################################### -/

/-- **★★★ THE FULL MIXED PLAIN-GAUSSIAN HESSIAN-SLICE BOUND.**  Combines `tE2_slice_abstract_mixed` (the
    E2 remainder) with `gaussian_hessian_cancel_mixed` (the parity leading term) into the mixed Hessian
    slice at the PLAIN Gaussian `G_τ(z)`:
      `|∫ z, G_τ(z)·(⟨Y,Pi⟩⟨Y,Pj⟩/(4τ²) − (⟨Pi,Pj⟩+⟨Y,Q⟩)/(2τ))·(A₀·g)| ≤ (tE2RateConst + L·n)·τ^{−1/2}`.
    Route: the add-and-subtract split `fullbracket = (fullbracket − zᵢzⱼ/(4τ²)) + zᵢzⱼ/(4τ²)`; the
    remainder integral is bounded by `tE2_slice_abstract_mixed`, and the leading parity integral
    `∫ zᵢzⱼ/(4τ²)·G_τ·(A₀·g)` by `gaussian_hessian_cancel_mixed` (whose `L·n/√τ` is `L·n·τ^{−1/2}` via
    `inv_sqrt_eq_rpow`).  The mixed analogue of the diagonal E2+E3 combination.  NOT `a₁ = R/6`. -/
theorem mixedHessianSlice_plain_bound
    (Y Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (g : ℝ → Point n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (L M₀ C_F u ε τ₀ C_W C_P C_Q : ℝ)
    (hL : 0 ≤ L) (hM₀ : 0 ≤ M₀) (hC_F : 0 ≤ C_F) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (hετ₀ : ε ≤ τ₀)
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3i : ∀ z : Point n, ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3j : ∀ z : Point n, ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hgcap : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |g s z| ≤ C_F)
    (hqLip : ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n, |A0 (u - s) z * g s z - A0 (u - s) w * g s w| ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * g s z) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * g s z| ≤ M)
    (hIntRem : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * (u - s) ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - (z i * z j) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * g s z)) volume) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, gaussDdim (u - s) z
          * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * g s z)|
        ≤ (tE2RateConst n M₀ C_F C_W C_P C_Q τ₀ + L * (n : ℝ)) * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hE2 := tE2_slice_abstract_mixed Y Pi Pj Q A0 g i j hij M₀ C_F u ε τ₀ C_W C_P C_Q
    hM₀ hC_F hC_W hC_P hC_Q hετ₀ hYdisp hJ3i hJ3j hJ3Q hA0bdd hgcap
  intro s hs
  have hτpos : 0 < u - s := by linarith [hs.2]
  set τ : ℝ := u - s with hτ_def
  obtain ⟨hLip, hmeas, hbdd⟩ := hqLip s hs
  -- the parity leading term (bounded by the banked mixed cancellation).
  have hlead : |∫ z, (z i * z j) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * g s z)|
      ≤ L * (n : ℝ) / Real.sqrt τ :=
    gaussian_hessian_cancel_mixed τ hτpos i j hij (fun z => A0 τ z * g s z) L hL hLip hmeas hbdd
  -- leading-term integrability (from the bounded, measurable field slice).
  have hIntLead : Integrable
      (fun z => (z i * z j) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * g s z)) volume := by
    obtain ⟨M, hM⟩ := hbdd
    exact (coordMulHess_gaussDdim_integrable τ hτpos i j hij).mul_bdd hmeas
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hM z))
  -- the add-and-subtract split of the full mixed Hessian slice.
  have hsplit : (∫ z, gaussDdim τ z
          * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
          * (A0 τ z * g s z))
      = (∫ z, gaussDdim τ z
            * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - (z i * z j) / (4 * τ ^ 2))
            * (A0 τ z * g s z))
        + ∫ z, (z i * z j) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * g s z) := by
    rw [← integral_add (hIntRem s hs) hIntLead]
    refine integral_congr_ae (ae_of_all _ (fun z => ?_)); ring
  rw [hsplit]
  -- combine the two bounds.
  have hτ2 : τ ^ (-(1 : ℝ) / 2) = (Real.sqrt τ)⁻¹ := (inv_sqrt_eq_rpow τ hτpos).symm
  calc |(∫ z, gaussDdim τ z
            * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - (z i * z j) / (4 * τ ^ 2))
            * (A0 τ z * g s z))
          + ∫ z, (z i * z j) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * g s z)|
      ≤ |∫ z, gaussDdim τ z
            * ((∑ k, Y z k * Pi z k) * (∑ k, Y z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - (z i * z j) / (4 * τ ^ 2))
            * (A0 τ z * g s z)|
          + |∫ z, (z i * z j) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * g s z)| := abs_add_le _ _
    _ ≤ tE2RateConst n M₀ C_F C_W C_P C_Q τ₀ * τ ^ (-(1 : ℝ) / 2) + L * (n : ℝ) / Real.sqrt τ :=
        add_le_add (hE2 s hs) hlead
    _ = (tE2RateConst n M₀ C_F C_W C_P C_Q τ₀ + L * (n : ℝ)) * τ ^ (-(1 : ℝ) / 2) := by
        rw [hτ2]; ring

end QIQTH.MixedTE2Slice

section AxiomChecks
open QIQTH.MixedTE2Slice
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms tE2_slice_abstract_mixed
#print axioms mixedHessianSlice_plain_bound
end AxiomChecks
