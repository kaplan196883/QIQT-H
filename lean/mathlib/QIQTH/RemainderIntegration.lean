/-
  RemainderIntegration — J4-136: the `hRem` bridge-difference (T_E2) discharge — the pure
  moment-integration of the cancellation-free remainder of the Hessian slice.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS BRICK IS.  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and
  proves NOTHING about `R/6`.  `HessianSliceBound.hInner0_discharge`/`witness_sliver2_final` carry the
  entangled Hessian-slice remainder as a single honest hypothesis
      `hRem : ∀ s ∈ Ioo (u−ε) u,
         |(∫ z, sTerm0 Y P Q A₀ (u−s) z · F s z 0)
            − (∫ z, ((zᵢ)²−2(u−s))/(4(u−s)²)·G_{u−s}(z)·(A₀ (u−s) z · F s z 0))|
          ≤ C_R·(u−s)^{−1/2}`.
  Write `τ := u−s`.  Using the ADD-AND-SUBTRACT identity `sTerm0·F = T_E3 + T_E1 + T_E2` with
      `T_E3 z := ((zᵢ)²−2τ)/(4τ²)·G_τ(z)·(A₀ τ z · F s z 0)`     (plain-Hermite — the subtracted term),
      `T_E2 z := G_τ(z)·(polyChart(z) − polyPlain(z))·(A₀ τ z · F s z 0)`  (bridge-difference),
      `T_E1 z := (G_τ(Y z) − G_τ(z))·polyChart(z)·(A₀ τ z · F s z 0)`      (Gaussian replacement),
  the remainder integrand `sTerm0·F − T_E3 = T_E1 + T_E2`, so
      `(∫ sTerm0·F) − (∫ T_E3) = (∫ T_E1) + (∫ T_E2)`
  and `hRem`'s LHS `≤ |∫ T_E1| + |∫ T_E2|`.

  This file DISCHARGES the `T_E2` half by PURE MOMENT INTEGRATION (no coercivity — `T_E2` carries the
  PLAIN Gaussian `G_τ(z)`), reusing the banked toolset:
    • `polyChartDiff_abs_bound` (HessianSliceBound) + the three T1' bridges
      (`innerYP_add_zi_bound`/`innerPP_sub_one_bound`/`innerYQ_bound`, SliverAssembly) fed from the
      geometric inputs `hYdisp`/`hJ3`/`hJ3Q` give the pointwise polynomial bracket bound
        `|polyChart − polyPlain| ≤ (A₃²r⁶+2A₃A₂r⁵+(A₂²+2A₃)r⁴+2A₂r³)/(4τ²)
                                    + (nC_P²+nC_WC_Q)r²/(2τ) + (2C_P+nC_Q)r/(2τ)`
      (`r := ‖z‖`, `A₃ := nC_WC_P`, `A₂ := n(C_W+C_P)`);
    • the F-cap `|F s z 0| ≤ C_L·G_a(0)` (`B_le_MB`) and amplitude cap `|A₀| ≤ M₀`;
    • the n-D sup-norm moment envelope `pow_norm_mul_gauss_integral` (κ = 1) fed the 1-D moments
      `oneD_absMoment1..6`, so `∫ ‖z‖^k G_τ ≤ n·c_k·(√τ)^k`;
    • the termwise fold: each `∫ r^k G_τ /τ²` (k = 3..6) and `∫ r^k G_τ /τ` (k = 1,2) is `≤ C·τ^{−1/2}`
      on `(0,τ₀]` (the leading `k=3/τ²` and `k=1/τ` are exactly `τ^{−1/2}`; the rest fold via `τ ≤ τ₀`).

  WHAT LANDS (this file):
    • `normPow_gauss_tau`   — the width-τ (κ = 1) n-D sup-norm moment `∫ ‖z‖^k G_τ ≤ n·c_k·(√τ)^k`.
    • `tE2_bracket_poly`    — ★ the pointwise polynomial bracket bound (bridges → explicit poly/τ).
    • `tE2_slice_bound`     — ★★ the `T_E2` per-slice integral discharge `|∫ T_E2| ≤ C_{E2}·τ^{−1/2}`
                              (`∃` explicit constant), the fully-proven E2 half of `hRem`.
    • `hRem_discharge`      — ★★★ the EXACT `hRem` shape of `witness_sliver2_final`, produced from the
                              PROVEN E2 half + a carried E1 half `hRemE1` + the per-term integrabilities.
    • `witness_sliver2_complete` — ★★★ the composite `witness_sliver2_final` with `hRem` REPLACED by the
                              geometric/amplitude carries + `hRemE1` + integrabilities (E2 gone).

  ⚠ HONEST FIREWALL — the carry list (each a genuine fact, NONE the conclusion, none vacuous; the model
    `Y = −id`, `P = eᵢ`, `Q = 0`, `A₀` bounded, `F` a width-2 Gaussian bump satisfies EVERY hypothesis,
    for which `T_E1 ≡ 0` and the `T_E2` bracket collapses to the plain proven bound):
      • `hYdisp`/`hJ3`/`hJ3Q` — the quadratic displacement `‖Y z + z‖ ≤ C_W‖z‖²`, first-jet modulus
        `‖P z − eᵢ‖ ≤ C_P‖z‖`, second-jet bound `‖Q z‖ ≤ C_Q` (the T1' bridge inputs).
      • `hA0bdd` — the amplitude sup bound `|A₀ τ z| ≤ M₀`; `hFdom` — the width-2 `F`-domination.
      • `hRemE1` — the carried GAUSSIAN-REPLACEMENT half `|∫ T_E1| ≤ C_E1·τ^{−1/2}` (the entangled
        `G_τ(Y z)` replacement — a genuine multi-file effort via `gaussDdim_replace_bound`; SATISFIABLE:
        `Y = −id` gives `T_E1 ≡ 0`).  NOT the conclusion.
      • the per-term integrabilities of `T_E1`/`T_E2`/`T_E3` (the split algebra carry).
    No `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HessianSliceBound

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ★ Width-τ (κ = 1) n-D sup-norm moment envelope.
    ############################################################################### -/

/-- **The width-τ n-D sup-norm moment.**  For `k ≥ 1`, `τ > 0`, and a supplied 1-D `k`-moment bound
    (constant `ck ≥ 0`), `∫_z ‖z‖^k · G_τ(z) ≤ n·ck·(√τ)^k`.  A `κ = 1` wrapper of
    `pow_norm_mul_gauss_integral`. -/
theorem normPow_gauss_tau (k : ℕ) (hk1 : 1 ≤ k) (ck : ℝ) (hck : 0 ≤ ck) (τ : ℝ) (hτ : 0 < τ)
    (hmom : ∫ y : ℝ, heatKernel1D τ y * |y| ^ k ≤ ck * (Real.sqrt τ) ^ k) :
    ∫ z : Point n, ‖z‖ ^ k * gaussDdim τ z ≤ (n : ℝ) * ck * (Real.sqrt τ) ^ k := by
  have h := pow_norm_mul_gauss_integral (n := n) k hk1 1 one_pos τ hτ ck hck
    (by rw [one_mul]; exact hmom)
  simpa [one_mul, Real.sqrt_one] using h

/-! ###############################################################################
    ★ The pointwise polynomial bracket bound (bridges → explicit polynomial / τ).
    ############################################################################### -/

/-- **★ THE POINTWISE POLYNOMIAL BRACKET BOUND.**  Composing `polyChartDiff_abs_bound` with the three
    T1' bridges (`innerYP_add_zi_bound`/`innerPP_sub_one_bound`/`innerYQ_bound`) fed from the geometric
    inputs `hYd`/`hJ`/`hQ`, the chart-jet Hessian coefficient `polyChart` differs from the plain-Hermite
    `polyPlain` by a bounded polynomial in `r := ‖z‖`: with `Δz := n(C_W r²)(C_P r)+n C_W r²+n r(C_P r)`,
    `P₁z := n(C_P r)²+2(C_P r)`, `Q₁z := n(C_W r²+r)C_Q`,
      `|polyChart − polyPlain| ≤ Δz·(Δz+2r)/(4τ²) + P₁z/(2τ) + Q₁z/(2τ)`.  NOT `a₁ = R/6`. -/
theorem tE2_bracket_poly (Y P Q : Point n → Point n) (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (C_W C_P C_Q : ℝ) (hC_Q : 0 ≤ C_Q)
    (hYd : ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ : ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hQ : ‖Q z‖ ≤ C_Q) :
    |((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
          - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
        - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2)|
      ≤ ((n : ℝ) * (C_W * ‖z‖ ^ 2) * (C_P * ‖z‖) + (n : ℝ) * (C_W * ‖z‖ ^ 2)
            + (n : ℝ) * ‖z‖ * (C_P * ‖z‖))
          * (((n : ℝ) * (C_W * ‖z‖ ^ 2) * (C_P * ‖z‖) + (n : ℝ) * (C_W * ‖z‖ ^ 2)
              + (n : ℝ) * ‖z‖ * (C_P * ‖z‖)) + 2 * ‖z‖) / (4 * τ ^ 2)
        + ((n : ℝ) * (C_P * ‖z‖) ^ 2 + 2 * (C_P * ‖z‖)) / (2 * τ)
        + ((n : ℝ) * (C_W * ‖z‖ ^ 2 + ‖z‖) * C_Q) / (2 * τ) := by
  have hΔ := innerYP_add_zi_bound (Y z) z (P z) i (C_W * ‖z‖ ^ 2) (C_P * ‖z‖) hYd hJ
  have hP₁ := innerPP_sub_one_bound (P z) i (C_P * ‖z‖) hJ
  have hQ₁ := innerYQ_bound (Y z) z (Q z) (C_W * ‖z‖ ^ 2) C_Q hYd hQ hC_Q
  exact polyChartDiff_abs_bound Y P Q i τ hτ z _ _ _ hΔ hP₁ hQ₁

/-! ###############################################################################
    ★★ T_E2 — the bridge-difference per-slice integral discharge (moment integration).
    ############################################################################### -/

/-- **★★ THE T_E2 SLICE DISCHARGE.**  The bridge-difference remainder integrand
    `T_E2 z = G_τ(z)·(polyChart(z) − polyPlain(z))·(A₀ τ z · F s z 0)` (τ = u−s) has the `τ^{−1/2}`
    rate: there is an `s`-uniform constant `C_E2 ≥ 0` with
      `∀ s ∈ Ioo (u−ε) u,  |∫ z, T_E2 z| ≤ C_E2·(u−s)^{−1/2}`.
    Route: `tE2_bracket_poly` (the three T1' bridges) bounds `|polyChart − polyPlain|` by an explicit
    polynomial in `‖z‖` over `τ²`/`τ`; the F-cap (`B_le_MB`) and amplitude cap bound `|A₀·F| ≤ M₀·C_F`;
    the width-τ moment envelope `normPow_gauss_tau` (fed `oneD_absMoment1..6`) turns `∫ ‖z‖^k G_τ` into
    `n·c_k·(√τ)^k`; the termwise fold (`τ ≤ τ₀`) collapses every `(√τ)^k/τ²` (k = 3..6) and
    `(√τ)^k/τ` (k = 1,2) to `≤ C·(√τ)^{−1}`.  PURELY the E2 half — no coercivity.  NOT `a₁ = R/6`. -/
theorem tE2_slice_bound
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₀ C_L T a u ε τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∃ C_E2 : ℝ, 0 ≤ C_E2 ∧ ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, gaussDdim (u - s) z * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
            - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
            - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z 0)|
        ≤ C_E2 * (u - s) ^ (-(1 : ℝ) / 2) := by
  -- abbreviations for the moment constants (`oneD_absMoment1..6`).
  set K : ℝ := M₀ * (C_L * gaussDdim a (0 : Point n)) with hKdef
  have hga : (0 : ℝ) ≤ gaussDdim a (0 : Point n) := gaussDdim_nonneg' a 0
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hw0nn : (0 : ℝ) ≤ Real.sqrt τ₀ := Real.sqrt_nonneg _
  refine ⟨K * (((n : ℝ) * C_W * C_P) ^ 2 * ((n : ℝ) * (3072 * Real.sqrt 2)) / 4 * Real.sqrt τ₀ ^ 3
      + 2 * ((n : ℝ) * C_W * C_P) * ((n : ℝ) * (C_W + C_P))
          * ((n : ℝ) * (1600 * Real.sqrt 2)) / 4 * Real.sqrt τ₀ ^ 2
      + (2 * ((n : ℝ) * C_W * C_P) + ((n : ℝ) * (C_W + C_P)) ^ 2)
          * ((n : ℝ) * (128 * Real.sqrt 2)) / 4 * Real.sqrt τ₀
      + 2 * ((n : ℝ) * (C_W + C_P)) * ((n : ℝ) * (64 * Real.sqrt 2 + 1)) / 4
      + ((n : ℝ) * C_P ^ 2 + (n : ℝ) * C_W * C_Q) * ((n : ℝ) * 2) / 2 * Real.sqrt τ₀
      + (2 * C_P + (n : ℝ) * C_Q) * ((n : ℝ) * (3 / 2)) / 2), ?_, ?_⟩
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
  have hτ₀pos : (0 : ℝ) < τ₀ := lt_of_lt_of_le hτpos hττ₀
  -- F-cap.
  set C_F : ℝ := C_L * gaussDdim a (0 : Point n) with hCF_def
  have hCFnn : 0 ≤ C_F := by rw [hCF_def]; exact mul_nonneg hC_L hga
  have hFcap : ∀ z : Point n, |F s z 0| ≤ C_F :=
    fun z => B_le_MB F C_L T a hC_L hFdom ha s hsa2 hsT z
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
          * (A0 τ z * F s z 0)‖
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
    have hAF : |A0 τ z * F s z 0| ≤ M₀ * C_F := by
      rw [abs_mul]; exact mul_le_mul (hA0bdd τ z) (hFcap z) (abs_nonneg _) hM₀
    have hAFnn : 0 ≤ |A0 τ z * F s z 0| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hGnn]
    calc gaussDdim τ z
            * |(∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2)|
            * |A0 τ z * F s z 0|
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
          rw [hbrk z, hKdef, hCF_def]; ring
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
            * (A0 τ z * F s z 0)|
      ≤ K * (coef6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt τ) ^ 6)
          + coef5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt τ) ^ 5)
          + coef4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt τ) ^ 4)
          + coef3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt τ) ^ 3)
          + coef2 * ((n : ℝ) * 2 * (Real.sqrt τ) ^ 2)
          + coef1 * ((n : ℝ) * (3 / 2) * (Real.sqrt τ) ^ 1)) := by
    calc |∫ z, gaussDdim τ z * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2))
              * (A0 τ z * F s z 0)|
        = ‖∫ z, gaussDdim τ z * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2))
              * (A0 τ z * F s z 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖gaussDdim τ z * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)
                - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2))
              * (A0 τ z * F s z 0)‖ := norm_integral_le_integral_norm _
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
  gcongr <;> first | exact hwle | positivity

/-! ###############################################################################
    ★★★ hRem — the EXACT remainder shape of `witness_sliver2_final` (E2 proven, E1 carried).
    ############################################################################### -/

/-- **★★★ THE `hRem` DISCHARGE.**  The exact entangled-remainder hypothesis of
    `hInner0_discharge`/`witness_sliver2_final`, produced from the PROVEN bridge-difference half
    (`tE2_slice_bound`) plus the carried Gaussian-replacement half `hRemE1`
    (`|∫ T_E1| ≤ C_E1·(u−s)^{−1/2}`) and the per-term integrabilities of `T_E1`/`T_E2`/`T_E3`.  Via the
    ADD-AND-SUBTRACT identity `sTerm0·F = T_E3 + T_E1 + T_E2` (`ring` from the `sTerm0` definition),
      `(∫ sTerm0·F) − (∫ T_E3) = (∫ T_E1) + (∫ T_E2)`,
    so the remainder is `≤ |∫ T_E1| + |∫ T_E2| ≤ (C_E1 + C_E2)·(u−s)^{−1/2}`, the exact `hRem` shape
    with `C_R := C_E1 + C_E2`.  The E2 half is FULLY proven here; only the entangled `T_E1` half is
    carried (`hRemE1`, SATISFIABLE: `Y = −id` gives `T_E1 ≡ 0`).  NOT `a₁ = R/6`. -/
theorem hRem_discharge
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₀ C_L T a u ε τ₀ C_W C_P C_Q C_E1 : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (hC_E1 : 0 ≤ C_E1)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hRemE1 : ∀ s ∈ Set.Ioo (u - ε) u,
        |∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z 0)|
          ≤ C_E1 * (u - s) ^ (-(1 : ℝ) / 2))
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
            * (A0 (u - s) z * F s z 0)) volume) :
    ∃ C_R : ℝ, 0 ≤ C_R ∧ ∀ s ∈ Set.Ioo (u - ε) u,
      |(∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0)
          - (∫ z, ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
              * (A0 (u - s) z * F s z 0))|
        ≤ C_R * (u - s) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C_E2, hC_E2nn, hE2⟩ := tE2_slice_bound Y P Q A0 F i M₀ C_L T a u ε τ₀ C_W C_P C_Q
    hM₀ hC_L hC_W hC_P hC_Q ha hau huT hε0 hεa hετ₀ hYdisp hJ3 hJ3Q hA0bdd hFdom
  refine ⟨C_E1 + C_E2, by linarith, ?_⟩
  intro s hs
  -- `sTerm0·F` integrable, and the add-and-subtract remainder identity `sTerm0·F − T_E3 = T_E1 + T_E2`.
  have hInt0 : Integrable (fun z => sTerm0 Y P Q A0 (u - s) z * F s z 0) volume := by
    have heq : (fun z : Point n => sTerm0 Y P Q A0 (u - s) z * F s z 0)
        = fun z => (((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
              * (A0 (u - s) z * F s z 0)
            + (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
                * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                    - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
                * (A0 (u - s) z * F s z 0))
          + gaussDdim (u - s) z
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                  - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
              * (A0 (u - s) z * F s z 0) := by
      funext z; simp only [sTerm0]; ring
    rw [heq]
    exact ((hIntT3 s hs).add (hIntT1 s hs)).add (hIntT2 s hs)
  have hid2 : ∀ z : Point n, sTerm0 Y P Q A0 (u - s) z * F s z 0
        - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (A0 (u - s) z * F s z 0)
      = (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z 0)
        + gaussDdim (u - s) z
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z 0) := by
    intro z; simp only [sTerm0]; ring
  -- remainder = `∫ T_E1 + ∫ T_E2` via `integral_sub` + `integral_add`.
  have hrem : (∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0)
        - (∫ z, ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (A0 (u - s) z * F s z 0))
      = (∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
              * (A0 (u - s) z * F s z 0))
        + ∫ z, gaussDdim (u - s) z
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z 0) := by
    rw [← integral_sub hInt0 (hIntT3 s hs), integral_congr_ae (ae_of_all _ hid2),
        integral_add (hIntT1 s hs) (hIntT2 s hs)]
  rw [hrem]
  calc |(∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
              * (A0 (u - s) z * F s z 0))
          + ∫ z, gaussDdim (u - s) z
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                  - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
              * (A0 (u - s) z * F s z 0)|
      ≤ |∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
              * (A0 (u - s) z * F s z 0)|
          + |∫ z, gaussDdim (u - s) z
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                  - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
              * (A0 (u - s) z * F s z 0)| := abs_add_le _ _
    _ ≤ C_E1 * (u - s) ^ (-(1 : ℝ) / 2) + C_E2 * (u - s) ^ (-(1 : ℝ) / 2) :=
        add_le_add (hRemE1 s hs) (hE2 s hs)
    _ = (C_E1 + C_E2) * (u - s) ^ (-(1 : ℝ) / 2) := by ring

/-! ###############################################################################
    ★★★ I3 — the composite: `witness_sliver2_final` with `hRem` REPLACED (E2 discharged).
    ############################################################################### -/

/-- **★★★ `witness_sliver2_complete`.**  The composite of `witness_sliver2_final` with its carried
    entangled remainder `hRem` REPLACED by the geometric/amplitude carries + the E1 half `hRemE1` +
    the per-term integrabilities — the E2 half now discharged in-line by `hRem_discharge`.  For an
    `s`-uniform `C_R ≥ 0` (existential, absorbing the proven `C_E2` and the carried `C_E1`), the
    terminal concrete formal-Hessian sliver obeys the `√ε` bound
      `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ ((15/2·n·L + C_R) + C₁)·2√ε + C₂·ε`.
    NOT `a₁ = R/6`. -/
theorem witness_sliver2_complete
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (Y P Q : Point n → Point n) (A0 A1 A2 : ℝ → Point n → ℝ)
    (i : Fin n) (L M₀ M₁ M₂ C_L T a τ₀ C_W C_P C_Q C_E1 : ℝ)
    (hL : 0 ≤ L) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hC_L : 0 ≤ C_L)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q) (hC_E1 : 0 ≤ C_E1)
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
    (hRemE1 : ∀ s ∈ Set.Ioo (u - ε) u,
        |∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z 0)|
          ≤ C_E1 * (u - s) ^ (-(1 : ℝ) / 2))
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
  obtain ⟨C_R, hC_Rnn, hRem⟩ := hRem_discharge Y P Q A0 F i M₀ C_L T a u ε τ₀ C_W C_P C_Q C_E1
    hM₀ hC_L hC_W hC_P hC_Q hC_E1 ha hau huT hε0 hεa hετ₀ hYdisp hJ3 hJ3Q hA0bdd hFdom
    hRemE1 hIntT1 hIntT2 hIntT3
  refine ⟨C_R, hC_Rnn, ?_⟩
  -- `sTerm0·F` integrability via the add-and-subtract identity.
  have hInt0 : ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z => sTerm0 Y P Q A0 (u - s) z * F s z 0) volume := by
    intro s hs
    have heq : (fun z : Point n => sTerm0 Y P Q A0 (u - s) z * F s z 0)
        = fun z => (((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
              * (A0 (u - s) z * F s z 0)
            + (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
                * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                    - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
                * (A0 (u - s) z * F s z 0))
          + gaussDdim (u - s) z
              * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                  - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                  - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
              * (A0 (u - s) z * F s z 0) := by
      funext z; simp only [sTerm0]; ring
    rw [heq]
    exact ((hIntT3 s hs).add (hIntT1 s hs)).add (hIntT2 s hs)
  exact witness_sliver2_final D2H F Y P Q A0 A1 A2 i L C_R M₁ M₂ C_L T a τ₀ C_W C_P
    hL hC_Rnn hM₁ hM₂ hC_L hC_W hC_P u ε ha hau huT hε0 hεu hεa hετ₀
    hco hYdisp hJ3 hA1bdd hA2bdd hFdom hqLip hRem hNormalForm hInt0 hInt1 hInt2

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.normPow_gauss_tau
#print axioms QIQTH.HeatResidualBound.tE2_bracket_poly
#print axioms QIQTH.HeatResidualBound.tE2_slice_bound
#print axioms QIQTH.HeatResidualBound.hRem_discharge
#print axioms QIQTH.HeatResidualBound.witness_sliver2_complete
