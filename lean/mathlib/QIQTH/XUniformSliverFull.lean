/-
  XUniformSliverFull — J4-202: the x-UNIFORM upgrade of the REMAINING halves of the full sliver
  composite (E2 bridge-difference + the T1/T2 leading slices), and the x-uniform s-integrated `√ε`
  composite bound at every field point in the ball.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the `a₁ = R/6` heat-kernel campaign.  J4-201 (`XUniformSliver`) lifted the E1 (Gaussian-replacement)
  sliver bound off the pinned centre `0` to a bound UNIFORM over the field point `x` (`tE1_slice_xuniform`,
  `sliver_rate_hsbound`), on the ROUTE-A observation that the sole field-dependent link of the sliver
  chain is the F-cap, and that cap (`BoundaryAssembly.B_le_MB` / `F_le_const_xuniform`) is ALREADY
  x-uniform with the SAME constant.  THIS brick applies the identical route-A pinning map to the REMAINING
  per-slice halves of `RemainderIntegration.witness_sliver2_complete`:
    • the E2 bridge-difference slice (`RemainderIntegration.tE2_slice_bound`, `F s z 0`-pinned);
    • the T1 gradient slice (`InnerSliceBounds.hInner1_discharge`, `F s z 0`-pinned);
    • the T2 mass slice (`InnerSliceBounds.hInner2_discharge`, `F s z 0`-pinned).
  No new singular-convolution analysis: every moment integration is imported from the banked bricks, not
  reproved.  NO `sorry`.  NO new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE COMPOSITE DECOMPOSITION (asked by the ledger).

  `RemainderIntegration.witness_sliver2_complete` bounds the concrete formal-Hessian sliver
      `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ ((15/2·n·L + C_R) + C₁)·2√ε + C₂·ε`
  by routing through `HessianSliceBound.witness_sliver2_final → SliverAssembly.witness_sliver2_assembly`,
  which splits the inner integrand via `hNormalForm : D2H = sTerm0 + sTerm1 + sTerm2` into three per-slice
  bounds:
    • `hInner0` (`sTerm0`, the Hessian slice), discharged by `hInner0_discharge` = the plain-Hermite
      cancellation (`15/2·n·L`) + the entangled REMAINDER `hRem`.  `hRem` in turn (`hRem_discharge`)
      splits `sTerm0·F − T_E3 = T_E1 + T_E2` into
        – the E1 half `|∫ T_E1| ≤ C_E1·(u−s)^{−1/2}` (`GaussReplaceSlice.tE1_slice_bound`), and
        – the E2 half `|∫ T_E2| ≤ C_E2·(u−s)^{−1/2}` (`RemainderIntegration.tE2_slice_bound`);
    • `hInner1` (`sTerm1`, the gradient slice), discharged by `hInner1_discharge` (`C₁·(u−s)^{−1/2}`);
    • `hInner2` (`sTerm2`, the mass slice), discharged by `hInner2_discharge` (`C₂`, `O(1)`).
  So the composite's per-slice sources are exactly {E1, E2} (inside `sTerm0`'s remainder) ∪ {T1, T2}.
  J4-201 delivered the E1 half x-uniform.  THIS brick delivers the E2, T1, T2 halves x-uniform, each by
  the SAME route-A pinning (their only field-dependent link is the peak F-cap `|F s z x| ≤ C_L·G_a(0)`,
  which is x-uniform by `F_le_const_xuniform`), then re-assembles the full x-uniform composite via the
  SHIFT trick on `SliverAssembly.witness_sliver2_assembly` (which is F-generic — the field point enters
  only through the per-slice hypotheses, never opened by the assembly proof).

  ## WHAT LANDS (this file, ns `QIQTH.XUniformSliverFull`).
    • `tE2RateConst`          — the explicit, x-FREE per-slice E2 constant (the banked witness).
    • `tE2RateConst_nonneg`   — its nonnegativity.
    • `tE2_slice_abstract`    — ★★ the abstract constant-cap E2 per-slice bound (field slice `g`).
    • `tE2_slice_xuniform`    — ★★ the E2 per-slice bound at a GENERAL field point `x`, SAME constant.
    • `hInner1_xuniform`      — ★★ the T1 gradient slice at a GENERAL field point `x`, SAME constant.
    • `hInner2_xuniform`      — ★★ the T2 mass slice at a GENERAL field point `x`, SAME constant.
    • `witness_sliver2_xuniform` — ★★★ the s-integrated `√ε` composite bound at EVERY field point `x`
        (the x-uniform version of `witness_sliver2_complete`; E1/E2/T1/T2 discharged in-line, only the
        Hessian-cancellation Lipschitz carry `hqLip` and the per-slice integrabilities remain per-x).

  Every hypothesis is satisfiable and non-vacuous (the model `Y = −id`, `P = eᵢ`, `Q = 0`, `A_j` bounded,
  `F` a width-2 Gaussian bump satisfies all of them — the SAME model as the pinned bricks), and none
  equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.XUniformSliver
import QIQTH.InnerSliceBounds
import QIQTH.HessianSliceBound
import QIQTH.DeltaFamilyBoundary
import QIQTH.HD1ConcreteWiring

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver
open scoped Interval Topology

namespace QIQTH.XUniformSliverFull

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ★ The explicit, x-free per-slice E2 constant.
    ############################################################################### -/

/-- **THE EXPLICIT, x-FREE PER-SLICE E2 CONSTANT.**  The banked `tE2_slice_bound` witness, written with
    the abstract field cap `C_F` in place of `C_L·gaussDdim a 0` (so `K := M₀·C_F`).  It does NOT mention
    the field point, so it serves as the SINGLE x-uniform constant of the E2 per-slice bound. -/
noncomputable def tE2RateConst (n : ℕ) (M₀ C_F C_W C_P C_Q τ₀ : ℝ) : ℝ :=
  (M₀ * C_F) * (((n : ℝ) * C_W * C_P) ^ 2 * ((n : ℝ) * (3072 * Real.sqrt 2)) / 4 * Real.sqrt τ₀ ^ 3
      + 2 * ((n : ℝ) * C_W * C_P) * ((n : ℝ) * (C_W + C_P))
          * ((n : ℝ) * (1600 * Real.sqrt 2)) / 4 * Real.sqrt τ₀ ^ 2
      + (2 * ((n : ℝ) * C_W * C_P) + ((n : ℝ) * (C_W + C_P)) ^ 2)
          * ((n : ℝ) * (128 * Real.sqrt 2)) / 4 * Real.sqrt τ₀
      + 2 * ((n : ℝ) * (C_W + C_P)) * ((n : ℝ) * (64 * Real.sqrt 2 + 1)) / 4
      + ((n : ℝ) * C_P ^ 2 + (n : ℝ) * C_W * C_Q) * ((n : ℝ) * 2) / 2 * Real.sqrt τ₀
      + (2 * C_P + (n : ℝ) * C_Q) * ((n : ℝ) * (3 / 2)) / 2)

/-- The per-slice E2 constant is nonnegative. -/
theorem tE2RateConst_nonneg (M₀ C_F C_W C_P C_Q τ₀ : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_F : 0 ≤ C_F) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q) :
    0 ≤ tE2RateConst n M₀ C_F C_W C_P C_Q τ₀ := by
  unfold tE2RateConst
  have h1 : (0 : ℝ) ≤ M₀ * C_F := mul_nonneg hM₀ hC_F
  positivity

/-! ###############################################################################
    ★★ The abstract constant-cap E2 per-slice bound (field slice `g`).
    ############################################################################### -/

/-- **★★ THE ABSTRACT E2 PER-SLICE BOUND.**  `RemainderIntegration.tE2_slice_bound` with the concrete
    Gaussian-dominated field slice `F s z 0` replaced by an ABSTRACT field slice `g s z` carrying ONLY the
    constant cap `|g s z| ≤ C_F`.  Every other link (`tE2_bracket_poly`, the width-τ moment envelope, the
    `w = √τ` fold) is field-free and imported verbatim.  Delivers the EXPLICIT single constant
    `tE2RateConst`.  NOT `a₁ = R/6`. -/
theorem tE2_slice_abstract
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (g : ℝ → Point n → ℝ)
    (i : Fin n) (M₀ C_F u ε τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_F : 0 ≤ C_F) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (hετ₀ : ε ≤ τ₀)
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hgcap : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |g s z| ≤ C_F) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, gaussDdim (u - s) z * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
            - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
            - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
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
      ‖gaussDdim τ z * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
            - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
            - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2))
          * (A0 τ z * g s z)‖
        ≤ K * (coef6 * (‖z‖ ^ 6 * gaussDdim τ z) + coef5 * (‖z‖ ^ 5 * gaussDdim τ z)
            + coef4 * (‖z‖ ^ 4 * gaussDdim τ z) + coef3 * (‖z‖ ^ 3 * gaussDdim τ z)
            + coef2 * (‖z‖ ^ 2 * gaussDdim τ z) + coef1 * (‖z‖ ^ 1 * gaussDdim τ z)) := by
    intro z
    have hGnn : 0 ≤ gaussDdim τ z := gaussDdim_nonneg' τ z
    have hdiff := tE2_bracket_poly Y P Q i τ hτpos z C_W C_P C_Q hC_Q (hYdisp z) (hJ3 z) (hJ3Q z)
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
            * |(∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2)|
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
  have hmain : |∫ z, gaussDdim τ z * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
              - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2))
            * (A0 τ z * g s z)|
      ≤ K * (coef6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt τ) ^ 6)
          + coef5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt τ) ^ 5)
          + coef4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt τ) ^ 4)
          + coef3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt τ) ^ 3)
          + coef2 * ((n : ℝ) * 2 * (Real.sqrt τ) ^ 2)
          + coef1 * ((n : ℝ) * (3 / 2) * (Real.sqrt τ) ^ 1)) := by
    calc |∫ z, gaussDdim τ z * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2))
              * (A0 τ z * g s z)|
        = ‖∫ z, gaussDdim τ z * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2))
              * (A0 τ z * g s z)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖gaussDdim τ z * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2))
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
    ★★ The x-uniform E2 per-slice bound (field point ranging).
    ############################################################################### -/

/-- **★★ THE x-UNIFORM E2 PER-SLICE BOUND.**  `RemainderIntegration.tE2_slice_bound` at a GENERAL field
    point `x`, with the SAME explicit `x`-free constant `tE2RateConst` (evaluated at `C_F = C_L·G_a(0)`).
    Instance of `tE2_slice_abstract` with the field slice `g s z := F s z x`, whose constant cap
    `|F s z x| ≤ C_L·gaussDdim a 0` is discharged by `F_le_const_xuniform` (route A).  NOT `a₁ = R/6`. -/
theorem tE2_slice_xuniform
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₀ C_L T a u ε τ₀ C_W C_P C_Q : ℝ) (x : Point n)
    (hM₀ : 0 ≤ M₀) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, gaussDdim (u - s) z * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
            - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
            - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z x)|
        ≤ tE2RateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀
            * (u - s) ^ (-(1 : ℝ) / 2) := by
  refine tE2_slice_abstract Y P Q A0 (fun s z => F s z x) i M₀ (C_L * gaussDdim a (0 : Point n))
    u ε τ₀ C_W C_P C_Q hM₀ (mul_nonneg hC_L (gaussDdim_nonneg' a 0)) hC_W hC_P hC_Q hετ₀
    hYdisp hJ3 hJ3Q hA0bdd ?_
  intro s hsmem z
  have hlo : a / 2 < s := by linarith [hsmem.1]
  have hsT : s ≤ T := by linarith [hsmem.2]
  exact F_le_const_xuniform F C_L T a hC_L hFdom ha s hlo.le hsT x z

/-! ###############################################################################
    ★★ The x-uniform T1 (gradient) and T2 (mass) per-slice bounds.
    ############################################################################### -/

/-- **★★ THE x-UNIFORM T1 GRADIENT SLICE.**  `InnerSliceBounds.hInner1_discharge` at a GENERAL field
    point `x`, with the SAME explicit `x`-free constant.  The only field-dependent link is the peak
    F-cap `|F s z x| ≤ C_L·gaussDdim a 0` (route A, `F_le_const_xuniform`, replacing `B_le_MB`); every
    other link (`gaussDdim_halfcoer_le`, the cubic `|⟨Y z,P z⟩|` bound, the `G_{2τ}`-moments) is
    field-free and imported verbatim.  NOT `a₁ = R/6`. -/
theorem hInner1_xuniform
    (Y P : Point n → Point n) (A1 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₁ C_L T a u ε τ₀ C_W C_P : ℝ) (x : Point n)
    (hM₁ : 0 ≤ M₁) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (_hε0 : 0 ≤ ε) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hA1bdd : ∀ τ, ∀ z : Point n, |A1 τ z| ≤ M₁)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, sTerm1 Y P A1 (u - s) z * F s z x|
        ≤ ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
            * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
              + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
              + ((n : ℝ) * C_W * C_P)
                * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀)))
          * (u - s) ^ (-(1 : ℝ) / 2) := by
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
  have hτ0 : (0 : ℝ) < τ₀ := lt_of_lt_of_le hτpos hττ₀
  -- constants
  set C_F : ℝ := C_L * gaussDdim a (0 : Point n) with hCF_def
  have hCFnn : 0 ≤ C_F := by rw [hCF_def]; exact mul_nonneg hC_L (gaussDdim_nonneg' _ _)
  -- F cap (route A: x-uniform peak bound)
  have hFcap : ∀ z : Point n, |F s z x| ≤ C_F :=
    fun z => F_le_const_xuniform F C_L T a hC_L hFdom ha s hsa2 hsT x z
  set K : ℝ := (Real.sqrt 2) ^ n * M₁ * C_F with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  set P₁ : ℝ := (n : ℝ) with hP₁_def
  set P₂ : ℝ := (n : ℝ) * (C_W + C_P) with hP₂_def
  set P₃ : ℝ := (n : ℝ) * C_W * C_P with hP₃_def
  have hP₁nn : 0 ≤ P₁ := by rw [hP₁_def]; positivity
  have hP₂nn : 0 ≤ P₂ := by rw [hP₂_def]; positivity
  have hP₃nn : 0 ≤ P₃ := by rw [hP₃_def]; positivity
  -- the cubic polynomial bound on |⟨Y z, P z⟩|
  have hpoly : ∀ z : Point n,
      |∑ k, Y z k * P z k| ≤ P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3 := by
    intro z
    have hYn : ‖Y z‖ ≤ C_W * ‖z‖ ^ 2 + ‖z‖ := normY_le (Y z) z (C_W * ‖z‖ ^ 2) (hYdisp z)
    have hPn : ‖P z‖ ≤ 1 + C_P * ‖z‖ := normP_le (P z) i C_P ‖z‖ (hJ3 z)
    have hYnn : 0 ≤ ‖Y z‖ := norm_nonneg _
    have hcast : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    calc |∑ k, Y z k * P z k|
        ≤ (n : ℝ) * ‖Y z‖ * ‖P z‖ := abs_inner_le (Y z) (P z)
      _ ≤ (n : ℝ) * (C_W * ‖z‖ ^ 2 + ‖z‖) * (1 + C_P * ‖z‖) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hYn hcast) hPn (norm_nonneg _)
            (mul_nonneg hcast (le_trans hYnn hYn))
      _ = P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3 := by
          rw [hP₁_def, hP₂_def, hP₃_def]; ring
  -- pointwise domination by the moment dominating function
  have hpt : ∀ z : Point n, ‖sTerm1 Y P A1 τ z * F s z x‖
      ≤ K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
          + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
          + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) := by
    intro z
    have hG2nn : 0 ≤ gaussDdim (2 * τ) z := gaussDdim_nonneg' (2 * τ) z
    have hGle : gaussDdim τ (Y z) ≤ (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
      gaussDdim_halfcoer_le τ hτpos (Y z) z (hco z)
    have hpolyz : |∑ k, Y z k * P z k| ≤ P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3 := hpoly z
    have hpolynn : 0 ≤ P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3 := le_trans (abs_nonneg _) hpolyz
    have habs : ‖sTerm1 Y P A1 τ z * F s z x‖
        = gaussDdim τ (Y z) * |∑ k, Y z k * P z k| * |A1 τ z| * |F s z x| / τ := by
      rw [Real.norm_eq_abs, sTerm1, abs_mul, abs_mul, abs_mul, abs_mul, abs_div, abs_neg, abs_two,
          abs_of_nonneg (gaussDdim_nonneg' τ (Y z)),
          abs_of_pos (show (0 : ℝ) < 2 * τ by linarith)]
      field_simp
    rw [habs, div_eq_mul_inv]
    have hnum : gaussDdim τ (Y z) * |∑ k, Y z k * P z k| * |A1 τ z| * |F s z x|
        ≤ ((Real.sqrt 2) ^ n * gaussDdim (2 * τ) z)
            * (P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3) * M₁ * C_F :=
      mul_le_mul
        (mul_le_mul
          (mul_le_mul hGle hpolyz (abs_nonneg _) (mul_nonneg (by positivity) hG2nn))
          (hA1bdd τ z) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by positivity) hG2nn) hpolynn))
        (hFcap z) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hG2nn) hpolynn) hM₁)
    have hfin : gaussDdim τ (Y z) * |∑ k, Y z k * P z k| * |A1 τ z| * |F s z x|
        ≤ K * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z) + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
            + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) :=
      le_trans hnum (le_of_eq (by rw [hKdef]; ring))
    calc gaussDdim τ (Y z) * |∑ k, Y z k * P z k| * |A1 τ z| * |F s z x| * τ⁻¹
        ≤ (K * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z) + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
            + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))) * τ⁻¹ :=
          mul_le_mul_of_nonneg_right hfin (by positivity)
      _ = K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
            + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
            + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) := by rw [one_div]; ring
  -- dominating function integrability
  have hbase_int : Integrable (fun z : Point n =>
      P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z) + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
        + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) volume :=
    (((normPow_gauss_integrable 1 (by norm_num) (2 * τ) h2τ).const_mul P₁).add
      ((normPow_gauss_integrable 2 (by norm_num) (2 * τ) h2τ).const_mul P₂)).add
      ((normPow_gauss_integrable 3 (by norm_num) (2 * τ) h2τ).const_mul P₃)
  have hdom_int : Integrable (fun z : Point n =>
      K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
        + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
        + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))) volume :=
    hbase_int.const_mul _
  -- the moment values
  have hm1 : ∫ z : Point n, ‖z‖ ^ 1 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1 :=
    pow_norm_mul_gauss_integral 1 (by norm_num) 2 (by norm_num) τ hτpos (3 / 2) (by norm_num)
      (oneD_absMoment1 (2 * τ) h2τ)
  have hm2 : ∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2 :=
    pow_norm_mul_gauss_integral 2 (by norm_num) 2 (by norm_num) τ hτpos 2 (by norm_num)
      (oneD_absMoment2 (2 * τ) h2τ)
  have hm3 : ∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3 :=
    pow_norm_mul_gauss_integral 3 (by norm_num) 2 (by norm_num) τ hτpos (64 * Real.sqrt 2 + 1)
      (by positivity) (oneD_absMoment3 (2 * τ) h2τ)
  -- integral of the dominating function
  have hI1 := (normPow_gauss_integrable 1 (by norm_num) (2 * τ) h2τ (n := n)).const_mul P₁
  have hI2 := (normPow_gauss_integrable 2 (by norm_num) (2 * τ) h2τ (n := n)).const_mul P₂
  have hI3 := (normPow_gauss_integrable 3 (by norm_num) (2 * τ) h2τ (n := n)).const_mul P₃
  have e1 : (∫ z : Point n, P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
        + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z) := integral_add hI1 hI2
  have e2 : (∫ z : Point n, (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
          + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)) + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
          + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) := integral_add (hI1.add hI2) hI3
  have hDval : ∫ z : Point n, K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
        + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z) + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))
      = K * (1 / τ) * (P₁ * (∫ z : Point n, ‖z‖ ^ 1 * gaussDdim (2 * τ) z)
          + P₂ * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z)
          + P₃ * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)) := by
    rw [integral_const_mul, e2, e1, integral_const_mul, integral_const_mul, integral_const_mul]
  -- the analytic core: everything ≤ C₁ · (√τ)⁻¹
  have hwpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτpos
  have hwne : Real.sqrt τ ≠ 0 := hwpos.ne'
  have hwsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτpos.le
  have hww₀ : Real.sqrt τ ≤ Real.sqrt τ₀ := Real.sqrt_le_sqrt hττ₀
  have hmain : |∫ z, sTerm1 Y P A1 τ z * F s z x|
      ≤ K * (1 / τ) * (P₁ * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
          + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
          + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)) := by
    calc |∫ z, sTerm1 Y P A1 τ z * F s z x|
        = ‖∫ z, sTerm1 Y P A1 τ z * F s z x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖sTerm1 Y P A1 τ z * F s z x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
              + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z) + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hdom_int (ae_of_all _ hpt)
      _ = K * (1 / τ) * (P₁ * (∫ z : Point n, ‖z‖ ^ 1 * gaussDdim (2 * τ) z)
            + P₂ * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z)
            + P₃ * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)) := hDval
      _ ≤ K * (1 / τ) * (P₁ * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
            + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
            + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKnn (by positivity))
          exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hm1 hP₁nn)
            (mul_le_mul_of_nonneg_left hm2 hP₂nn)) (mul_le_mul_of_nonneg_left hm3 hP₃nn)
  refine le_trans hmain ?_
  rw [← inv_sqrt_eq_rpow τ hτpos]
  have hsq : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτpos.le
  set w : ℝ := Real.sqrt τ with hwdef
  rw [← hsq]
  have hlin : K * (1 / (w * w)) * (P₁ * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * w ^ 1)
        + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w ^ 2)
        + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 3))
      = K * w⁻¹ * (P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
          + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w)
          + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 2)) := by
    field_simp
    try ring
  rw [hlin]
  have hwle : w ≤ Real.sqrt τ₀ := hww₀
  have hw2le : w ^ 2 ≤ τ₀ := by rw [hwsq]; exact hττ₀
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hbracket :
      P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
        + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w)
        + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 2)
      ≤ P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
        + P₂ * ((4 * (n : ℝ)) * Real.sqrt τ₀)
        + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) := by
    have ht2 : P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w) ≤ P₂ * ((4 * (n : ℝ)) * Real.sqrt τ₀) := by
      apply mul_le_mul_of_nonneg_left _ hP₂nn
      rw [hsqrt2sq]
      calc (n : ℝ) * 2 * 2 * w = (4 * (n : ℝ)) * w := by ring
        _ ≤ (4 * (n : ℝ)) * Real.sqrt τ₀ := mul_le_mul_of_nonneg_left hwle (by positivity)
    have ht3 : P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 2)
        ≤ P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) := by
      apply mul_le_mul_of_nonneg_left _ hP₃nn
      apply mul_le_mul_of_nonneg_left hw2le (by positivity)
    linarith [ht2, ht3]
  have hKwnn : 0 ≤ K * w⁻¹ := mul_nonneg hKnn (inv_nonneg.mpr hwpos.le)
  calc K * w⁻¹ * (P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
          + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w)
          + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 2))
      ≤ K * w⁻¹ * (P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
          + P₂ * ((4 * (n : ℝ)) * Real.sqrt τ₀)
          + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀)) :=
        mul_le_mul_of_nonneg_left hbracket hKwnn
    _ = ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
            * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
              + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
              + ((n : ℝ) * C_W * C_P)
                * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀))) * w⁻¹ := by
        rw [hKdef, hCF_def, hP₁_def, hP₂_def, hP₃_def]; ring

/-- **★★ THE x-UNIFORM T2 MASS SLICE.**  `InnerSliceBounds.hInner2_discharge` at a GENERAL field point
    `x`, with the SAME `O(1)` constant `(√2)ⁿ·M₂·C_L·gaussDdim a 0`.  Route A via the x-uniform peak cap
    `|F s z x| ≤ C_L·gaussDdim a 0` (`F_le_const_xuniform`): `|sTerm2·F| ≤ (√2)ⁿ M₂ C_F·G_{2τ}(z)`
    pointwise (`gaussDdim_halfcoer_le`), and `∫ G_{2τ} = 1` (`gaussDdim_integral_eq_one`) — no
    convolution/shift needed.  NOT `a₁ = R/6`. -/
theorem hInner2_xuniform
    (Y : Point n → Point n) (A2 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (M₂ C_L T a u ε : ℝ) (x : Point n)
    (hM₂ : 0 ≤ M₂) (hC_L : 0 ≤ C_L)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (_hε0 : 0 ≤ ε) (hεa : ε < a / 2)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hA2bdd : ∀ τ, ∀ z : Point n, |A2 τ z| ≤ M₂)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, sTerm2 Y A2 (u - s) z * F s z x|
        ≤ (Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n) := by
  intro s hsmem
  have hτpos : 0 < u - s := by linarith [hsmem.2]
  have hlo : u - ε > a / 2 := by linarith
  have hspos : 0 < s := by linarith [hsmem.1, hlo]
  have hsT : s ≤ T := by linarith [hsmem.2, huT]
  have hsa2 : a / 2 ≤ s := by linarith [hsmem.1, hlo]
  set τ : ℝ := u - s with hτ_def
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  have hga : (0 : ℝ) ≤ gaussDdim a (0 : Point n) := gaussDdim_nonneg' a 0
  set C_F : ℝ := C_L * gaussDdim a (0 : Point n) with hCF_def
  have hFcap : ∀ z : Point n, |F s z x| ≤ C_F :=
    fun z => F_le_const_xuniform F C_L T a hC_L hFdom ha s hsa2 hsT x z
  set K : ℝ := (Real.sqrt 2) ^ n * M₂ * C_L with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  -- pointwise domination
  have hpt : ∀ z : Point n, ‖sTerm2 Y A2 τ z * F s z x‖
      ≤ (K * gaussDdim a (0 : Point n)) * gaussDdim (2 * τ) z := by
    intro z
    rw [Real.norm_eq_abs, sTerm2, abs_mul, abs_mul, abs_of_nonneg (gaussDdim_nonneg' τ (Y z))]
    have hG : gaussDdim τ (Y z) ≤ (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
      gaussDdim_halfcoer_le τ hτpos (Y z) z (hco z)
    calc gaussDdim τ (Y z) * |A2 τ z| * |F s z x|
        ≤ ((Real.sqrt 2) ^ n * gaussDdim (2 * τ) z) * M₂ * C_F := by
          refine mul_le_mul (mul_le_mul hG (hA2bdd τ z) (abs_nonneg _)
            (mul_nonneg (by positivity) (gaussDdim_nonneg' _ _))) (hFcap z) (abs_nonneg _)
            (mul_nonneg (mul_nonneg (by positivity) (gaussDdim_nonneg' _ _)) hM₂)
      _ = (K * gaussDdim a (0 : Point n)) * gaussDdim (2 * τ) z := by rw [hKdef, hCF_def]; ring
  have hdomint : Integrable
      (fun z : Point n => (K * gaussDdim a (0 : Point n)) * gaussDdim (2 * τ) z) volume :=
    (gaussDdim_integrable (2 * τ) h2τ).const_mul _
  calc |∫ z, sTerm2 Y A2 τ z * F s z x|
      = ‖∫ z, sTerm2 Y A2 τ z * F s z x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, ‖sTerm2 Y A2 τ z * F s z x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, (K * gaussDdim a (0 : Point n)) * gaussDdim (2 * τ) z :=
        integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hdomint (ae_of_all _ hpt)
    _ = (K * gaussDdim a (0 : Point n)) * ∫ z, gaussDdim (2 * τ) z := integral_const_mul _ _
    _ = (K * gaussDdim a (0 : Point n)) * 1 := by rw [gaussDdim_integral_eq_one (2 * τ) h2τ]
    _ = (Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n) := by rw [hKdef]; ring

/-! ###############################################################################
    ★★ The x-uniform remainder `hRem` (E1 + E2 discharged in-line at field point `x`).
    ############################################################################### -/

/-- **★★ THE x-UNIFORM `hRem`.**  The exact entangled-remainder shape of `hInner0_discharge` at a GENERAL
    field point `x`, produced from BOTH halves PROVEN x-uniform: the E1 half `tE1_slice_xuniform`
    (`≤ sliverRateConst·(u−s)^{−1/2}`) and the E2 half `tE2_slice_xuniform`
    (`≤ tE2RateConst·(u−s)^{−1/2}`), via the add-and-subtract identity
    `sTerm0·F − T_E3 = T_E1 + T_E2`.  Unlike `RemainderIntegration.hRem_discharge` (which CARRIES the E1
    half `hRemE1`), here the E1 half is discharged from `hFdom` by route A.  NOT `a₁ = R/6`. -/
theorem hRem_xuniform
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₀ C_L T a u ε τ₀ C_W C_P C_Q : ℝ) (x : Point n)
    (hM₀ : 0 ≤ M₀) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hIntT1 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z x)) volume)
    (hIntT2 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z x)) volume)
    (hIntT3 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (A0 (u - s) z * F s z x)) volume) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |(∫ z, sTerm0 Y P Q A0 (u - s) z * F s z x)
          - (∫ z, ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
              * (A0 (u - s) z * F s z x))|
        ≤ (sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀
            + tE2RateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀)
          * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hE1 := tE1_slice_xuniform Y P Q A0 F i M₀ C_L T a u ε τ₀ C_W C_P C_Q x
    hM₀ hC_L hC_W hC_P hC_Q ha hau huT hεa hετ₀ hco hYdisp hJ3 hJ3Q hA0bdd hFdom
  have hE2 := tE2_slice_xuniform Y P Q A0 F i M₀ C_L T a u ε τ₀ C_W C_P C_Q x
    hM₀ hC_L hC_W hC_P hC_Q ha hau huT hεa hετ₀ hYdisp hJ3 hJ3Q hA0bdd hFdom
  intro s hs
  have hInt0 : Integrable (fun z => sTerm0 Y P Q A0 (u - s) z * F s z x) volume := by
    have heq : (fun z : Point n => sTerm0 Y P Q A0 (u - s) z * F s z x)
        = fun z => (((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
              * (A0 (u - s) z * F s z x)
            + (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
                * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                    - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
                * (A0 (u - s) z * F s z x))
          + gaussDdim (u - s) z
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                  - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
              * (A0 (u - s) z * F s z x) := by
      funext z; simp only [sTerm0]; ring
    rw [heq]
    exact ((hIntT3 s hs).add (hIntT1 s hs)).add (hIntT2 s hs)
  have hid2 : ∀ z : Point n, sTerm0 Y P Q A0 (u - s) z * F s z x
        - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (A0 (u - s) z * F s z x)
      = (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z x)
        + gaussDdim (u - s) z
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z x) := by
    intro z; simp only [sTerm0]; ring
  have hrem : (∫ z, sTerm0 Y P Q A0 (u - s) z * F s z x)
        - (∫ z, ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (A0 (u - s) z * F s z x))
      = (∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
              * (A0 (u - s) z * F s z x))
        + ∫ z, gaussDdim (u - s) z
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z x) := by
    rw [← integral_sub hInt0 (hIntT3 s hs), integral_congr_ae (ae_of_all _ hid2),
        integral_add (hIntT1 s hs) (hIntT2 s hs)]
  rw [hrem]
  calc |(∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
              * (A0 (u - s) z * F s z x))
          + ∫ z, gaussDdim (u - s) z
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                  - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
              * (A0 (u - s) z * F s z x)|
      ≤ |∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
              * (A0 (u - s) z * F s z x)|
          + |∫ z, gaussDdim (u - s) z
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                  - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
              * (A0 (u - s) z * F s z x)| := abs_add_le _ _
    _ ≤ sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀ * (u - s) ^ (-(1 : ℝ) / 2)
          + tE2RateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀ * (u - s) ^ (-(1 : ℝ) / 2) :=
        add_le_add (hE1 s hs) (hE2 s hs)
    _ = (sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀
          + tE2RateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀)
        * (u - s) ^ (-(1 : ℝ) / 2) := by ring

/-! ###############################################################################
    ★★★ The full x-uniform composite `√ε` bound at EVERY field point.
    ############################################################################### -/

/-- **★★★ `witness_sliver2_xuniform`.**  The x-UNIFORM version of
    `RemainderIntegration.witness_sliver2_complete`: for EVERY field point `x`, the terminal concrete
    formal-Hessian sliver obeys the same `√ε` bound with the SAME (now EXPLICIT) constants.  Re-assembled
    from the four x-uniform per-slice halves — E1 (`tE1_slice_xuniform`) + E2 (`tE2_slice_xuniform`)
    inside the Hessian remainder (`hRem_xuniform` → `hInner0_discharge`), the T1 gradient
    (`hInner1_xuniform`) and the T2 mass (`hInner2_xuniform`) — fed to the F-generic
    `SliverAssembly.witness_sliver2_assembly` at the field slice `fun s z _ => F s z x` (the assembly
    never opens the field, so this is the ONLY step where the field point moves).  The E1/E2/T1/T2 halves
    are discharged in-line from `hFdom`; only the Hermite-cancellation Lipschitz data `hqLip` and the
    per-slice integrabilities remain per-`x` carries (satisfiable by the width-2 Gaussian model).  This
    is exactly the DIST-form control the `hsliver` slot of `HD1SliverRoute.hD1_bulk_sliver_reduction`
    consumes over the field ball.  NOT `a₁ = R/6`. -/
theorem witness_sliver2_xuniform
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
    (hqLip : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n, |A0 (u - s) z * F s z x - A0 (u - s) w * F s w x| ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z x) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * F s z x| ≤ M)
    (hIntT1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z x)) volume)
    (hIntT2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z x)) volume)
    (hIntT3 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (A0 (u - s) z * F s z x)) volume)
    (hInt1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm1 Y P A1 (u - s) z * F s z x) volume)
    (hInt2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm2 Y A2 (u - s) z * F s z x) volume) :
    ∀ x : Point n,
      |∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z x|
        ≤ ((15 / 2 * (n : ℝ) * L
              + (sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀
                  + tE2RateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀))
            + ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
                * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
                  + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
                  + ((n : ℝ) * C_W * C_P)
                    * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀))))
            * (2 * Real.sqrt ε)
          + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n)) * ε := by
  have hga : (0 : ℝ) ≤ gaussDdim a (0 : Point n) := gaussDdim_nonneg' a 0
  have hτ₀0 : (0 : ℝ) ≤ τ₀ := le_trans hε0 hετ₀
  -- constant nonnegativities.
  have hCRnn : (0 : ℝ) ≤ sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀
      + tE2RateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀ :=
    add_nonneg (sliverRateConst_nonneg _ _ _ _ _ _ hM₀ (mul_nonneg hC_L hga) hC_W hC_P hC_Q)
      (tE2RateConst_nonneg _ _ _ _ _ _ hM₀ (mul_nonneg hC_L hga) hC_W hC_P hC_Q)
  have hC₀ : (0 : ℝ) ≤ 15 / 2 * (n : ℝ) * L
      + (sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀
          + tE2RateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀) :=
    add_nonneg (mul_nonneg (by positivity) hL) hCRnn
  have hbrkt : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
        + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
        + ((n : ℝ) * C_W * C_P)
          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) := by
    have ht2 : (0 : ℝ) ≤ ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
    have ht3 : (0 : ℝ) ≤ ((n : ℝ) * C_W * C_P)
        * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC_W) hC_P)
        (mul_nonneg (by positivity) hτ₀0)
    have ht1 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2) := by positivity
    linarith
  have hC₁ : (0 : ℝ) ≤ (Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
        * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
          + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
          + ((n : ℝ) * C_W * C_P)
            * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hM₁) (mul_nonneg hC_L hga)) hbrkt
  have hC₂ : (0 : ℝ) ≤ (Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hM₂) hC_L) hga
  intro x
  -- the three x-uniform per-slice discharges at the field slice `fun s z _ => F s z x`.
  have hI0 := hInner0_discharge Y P Q A0 (fun s z _ => F s z x) i L
    (sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀
      + tE2RateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀)
    u ε hL hCRnn (hqLip x)
    (hRem_xuniform Y P Q A0 F i M₀ C_L T a u ε τ₀ C_W C_P C_Q x
      hM₀ hC_L hC_W hC_P hC_Q ha hau huT hεa hετ₀ hco hYdisp hJ3 hJ3Q hA0bdd hFdom
      (hIntT1 x) (hIntT2 x) (hIntT3 x))
  have hI1 := hInner1_xuniform Y P A1 F i M₁ C_L T a u ε τ₀ C_W C_P x
    hM₁ hC_L hC_W hC_P ha hau huT hε0 hεa hετ₀ hco hYdisp hJ3 hA1bdd hFdom
  have hI2 := hInner2_xuniform Y A2 F M₂ C_L T a u ε x
    hM₂ hC_L ha hau huT hε0 hεa hco hA2bdd hFdom
  -- integrability of `sTerm0·F s z x` (add-and-subtract identity).
  have hInt0 : ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z => sTerm0 Y P Q A0 (u - s) z * F s z x) volume := by
    intro s hs
    have heq : (fun z : Point n => sTerm0 Y P Q A0 (u - s) z * F s z x)
        = fun z => (((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
              * (A0 (u - s) z * F s z x)
            + (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
                * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                    - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
                * (A0 (u - s) z * F s z x))
          + gaussDdim (u - s) z
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                  - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
              * (A0 (u - s) z * F s z x) := by
      funext z; simp only [sTerm0]; ring
    rw [heq]
    exact ((hIntT3 x s hs).add (hIntT1 x s hs)).add (hIntT2 x s hs)
  exact witness_sliver2_assembly D2H (fun s z _ => F s z x) Y P Q A0 A1 A2
    _ _ _ τ₀ hC₀ hC₁ hC₂ u ε hε0 hεu hετ₀ hNormalForm hI0 hI1 hI2
    hInt0 (hInt1 x) (hInt2 x)

/-! ###############################################################################
    ★★★ The interface-level `hD1` closure from the unified carries.
    ############################################################################### -/

/-- **★★★ `hD1_from_data`.**  THE full `hD1 : ContDiffAt ℝ 1 D 0` closure at the interface level,
    assembled from the two J4-199/J4-200 skeletons:
      • `HD1SliverRoute.hD1_bulk_sliver_reduction` — the uniform-limit-of-derivatives theorem, applied at
        EVERY field point `x ∈ sSet` (the x-uniformity is what makes `hsliver` hold across the whole ball;
        it is supplied by `witness_sliver2_xuniform`'s DIST-form sliver bound, whose vanishing `hb` is
        `HD1ConcreteWiring.sliver_bound_tendsto_zero`) — giving `HasFDerivAt gfull (gderiv x) x` for each
        `x ∈ sSet`;
      • `HD1ConcreteWiring.hD1_reduction` — turning that nbhd derivative family together with the
        derivative-field continuity `hcont` (`gderiv_continuousAt` over `sSet`) into `ContDiffAt ℝ 1`.
    The unified carry list is exactly {bulk derivatives `hbulkderiv` (← `gcoef_bulk_hasFDerivAt`), bulk
    pointwise convergence `hbulk_tendsto` (← `bulk_tendsto_of_primitive`), the x-uniform sliver
    dist-bound `hsliver` (← `witness_sliver2_xuniform`), its vanishing `hb`, and the derivative-field
    continuity `hcont` (← `gderiv_continuousAt`)} — the L1-chain geometric data plus the sliver-chain
    carries, nothing more.  Scalar (per-gcoef-component) `gfull`; the CLM-valued lift is componentwise.
    NOT `a₁ = R/6`. -/
theorem hD1_from_data
    {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {l : Filter ι} [l.NeBot]
    {sSet : Set H} (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : H))
    (fbulk : ι → H → ℝ) (fderivBulk : ι → H → (H →L[ℝ] ℝ))
    (gfull : H → ℝ) (gderiv : H → (H →L[ℝ] ℝ))
    (b : ι → ℝ) (hb : Filter.Tendsto b l (𝓝 0))
    (hbulkderiv : ∀ i, ∀ x ∈ sSet, HasFDerivAt (fbulk i) (fderivBulk i x) x)
    (hbulk_tendsto : ∀ x ∈ sSet, Filter.Tendsto (fun i => fbulk i x) l (𝓝 (gfull x)))
    (hsliver : ∀ i, ∀ x ∈ sSet, dist (fderivBulk i x) (gderiv x) ≤ b i)
    (hcont : ContinuousOn gderiv sSet) :
    ContDiffAt ℝ 1 gfull (0 : H) := by
  refine QIQTH.HD1ConcreteWiring.hD1_reduction gfull gderiv hsnhds ?_ hcont
  intro x hx
  exact QIQTH.HD1SliverRoute.hD1_bulk_sliver_reduction hsOpen hx
    fbulk fderivBulk gfull gderiv b hb hbulkderiv hbulk_tendsto hsliver

end QIQTH.XUniformSliverFull

section AxiomChecks
open QIQTH.XUniformSliverFull
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms tE2RateConst_nonneg
#print axioms tE2_slice_abstract
#print axioms tE2_slice_xuniform
#print axioms hInner1_xuniform
#print axioms hInner2_xuniform
#print axioms hRem_xuniform
#print axioms witness_sliver2_xuniform
#print axioms hD1_from_data
end AxiomChecks
