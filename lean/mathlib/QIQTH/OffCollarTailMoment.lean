/-
  OffCollarTailMoment — J4-546: making the leg-1 HI-leg `hOffCollarTail` a CONCRETE, exponentially
  suppressed Gaussian-tail moment integral (the sharp `poly·e^{−c²/8}` refinement deferred by
  `SliverTailMatched.tailMoment_bound`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It supplies
  ONE analytic brick: the SHARP off-collar Gaussian-tail moment bound that `SliverTailMatched` (J4-354)
  explicitly DEFERRED ("The sharp `poly(c)·e^{−κc²}` refinement is deferred (not needed downstream)").
  No `sorry`/`admit` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to the conclusion, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT — the bare off-collar tail moment `T_τ = tailMoment i τ R := ∫_{‖z‖>R} H_{τ,i}`,
  `H_{τ,i}(z) = (z_i²−2τ)/(4τ²)·G_τ(z)` (`SliverTailMatched.hessGaussFactor`).  `tailMoment_bound`
  banks only the CRUDE `|T_τ| ≤ τ⁻¹` (which drops the tail decay entirely, giving the log-divergent
  `a(c)/τ` diagnosed in Sol #13).  THIS file replaces that with the honest exponentially-small-in-`c²`
  estimate that J4-546 targets.

  ## WHAT LANDS.
    • `gaussDdim_tail_le_scaled` — the pointwise n-D Gaussian tail domination on `‖z‖ > R`:
          `G_τ(z) ≤ (√2)ⁿ · exp(−R²/(8τ)) · G_{2τ}(z)`,
      built from the banked width-split `gaussDdim_eq_wide_mul` (`G_τ = e^{−r²/8τ}·G_wide`) +
      `gaussDdimWide_eq_scaled_gaussDdim` (`G_wide = (√2)ⁿ·G_{2τ}`), with the tail hypothesis
      `R² ≤ ‖z‖² ≤ rncRadialSq z` (`norm_sq_le_rncRadialSq`) feeding `e^{−r²/8τ} ≤ e^{−R²/8τ}`.
    • `tailMoment_expSuppressed_bound` — ★★★ the CONCRETE off-collar tail moment bound:
          `|tailMoment i τ R| ≤ (√2)ⁿ · exp(−R²/(8τ)) · (2n+1)/(2τ)`.
      Route: `|T_τ| ≤ ∫_{‖z‖>R} ‖H‖`; on the tail `‖H‖ = |(z_i²−2τ)/(4τ²)|·G_τ ≤
      (‖z‖²+2τ)/(4τ²)·[(√2)ⁿe^{−R²/8τ}G_{2τ}]`; extend to full space and integrate — the `G_{2τ}`
      second moment `∫‖z‖²G_{2τ} ≤ 4nτ` (`normPow_gauss_tau`, `oneD_absMoment2`) + mass one give the
      closed form `(2n+1)/(2τ)`.
    • `tailMoment_collar_expSuppressed` — ★ the √ε-collar specialisation `R = c·√τ`, where the exponent
      COLLAPSES to a `τ`-independent constant:
          `|tailMoment i τ (c√τ)| ≤ (√2)ⁿ · exp(−c²/8) · (2n+1)/(2τ)`.
      THIS is the concrete `hOffCollarTail`: a genuine Gaussian-tail moment integral, exponentially small
      in `c²` relative to the naive `τ⁻¹` of `tailMoment_bound`.

  ## HONEST SCOPING (blunt — Sol #J4-546).  This SHARPENS `tailMoment_bound` but is NOT the operational
  closure of the HI-leg term-1.  For FIXED `c`, `e^{−c²/8}·τ⁻¹` is still `O(τ⁻¹)` (worse than the target
  `O(τ^{−1/2})` of `hinner_window`); the exponential becomes operational ONLY under a GROWING collar
  `c = c(τ) → ∞` (balancing `e^{−c²/8}` against `√τ`).  The genuine `O(τ^{−1/2})` closure of term-1 is
  the MATCHED-PAIR estimate `SliverTailMatched.sliver_term1_on_collar_matched`
  (`‖∫_{collar}H·q + q(0)·T_τ‖ ≤ L·(15/2·n)/√τ`), where `T_τ` stays PAIRED with the on-collar integral
  and cancels EXACTLY via `collarMoment_eq_neg_tail`.  This file makes the bare `T_τ` a concrete
  exp-suppressed integral; the matched pairing is what actually keeps it controlled.

  ⚠  `a₁ = R/6` remains CONDITIONAL and effectively FLAT-ONLY.  Closing/sharpening the off-collar tail
  does NOT derive the coefficient — the on-collar `hjets` bundle, the capped leg-2 `hLapFull`, the
  convergence trio, and the Seeley–DeWitt geometric wiring ALL remain.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SliverTailMatched
import QIQTH.AnnulusGaussianBound
import QIQTH.ParametrixResidualBaseKernel
import QIQTH.RemainderIntegration
import QIQTH.GaussianMomentEnvelope
import QIQTH.InverseChartDisplacement
import QIQTH.DeltaFamilyBoundary

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.OffCollarTailMoment

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the pointwise n-D Gaussian tail domination on `‖z‖ > R`.
    ############################################################################### -/

/-- **`gaussDdim_tail_le_scaled`.**  THE POINTWISE n-D GAUSSIAN TAIL DOMINATION.  On the off-collar
    region `‖z‖ > R` (Pi sup-norm), the heat kernel is dominated by the DOUBLED-time kernel times an
    exponentially small factor:
        `G_τ(z) ≤ (√2)ⁿ · exp(−R²/(8τ)) · G_{2τ}(z)`.
    Route (all banked): the width-split `gaussDdim_eq_wide_mul` (`G_τ = e^{−r²/8τ}·G_wide`, `r² =
    rncRadialSq z`) + `gaussDdimWide_eq_scaled_gaussDdim` (`G_wide = (√2)ⁿ·G_{2τ}`), and the tail
    hypothesis `R² ≤ ‖z‖² ≤ rncRadialSq z` (`norm_sq_le_rncRadialSq`) makes `e^{−r²/8τ} ≤ e^{−R²/8τ}`.
    ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_tail_le_scaled (τ R : ℝ) (hτ : 0 < τ) (hR : 0 ≤ R) (z : Point n)
    (hz : R < ‖z‖) :
    gaussDdim τ z ≤ Real.sqrt 2 ^ n * Real.exp (-(R ^ 2) / (8 * τ)) * gaussDdim (2 * τ) z := by
  have hRsq : R ^ 2 ≤ rncRadialSq z := by
    have h1 : R ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hz, hR, norm_nonneg z]
    exact le_trans h1 (norm_sq_le_rncRadialSq z)
  have hexp_le : Real.exp (-(rncRadialSq z) / (8 * τ)) ≤ Real.exp (-(R ^ 2) / (8 * τ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith [hRsq]) (by positivity)
  rw [gaussDdim_eq_wide_mul hτ z, gaussDdimWide_eq_scaled_gaussDdim hτ z]
  have hg2 : 0 ≤ gaussDdim (2 * τ) z := gaussDdim_nonneg (2 * τ) z
  calc Real.exp (-(rncRadialSq z) / (8 * τ)) * (Real.sqrt 2 ^ n * gaussDdim (2 * τ) z)
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2 ^ n * gaussDdim (2 * τ) z) :=
        mul_le_mul_of_nonneg_right hexp_le (by positivity)
    _ = Real.sqrt 2 ^ n * Real.exp (-(R ^ 2) / (8 * τ)) * gaussDdim (2 * τ) z := by ring

/-! ###############################################################################
    ### §2 — the concrete exponentially suppressed off-collar tail moment bound.
    ############################################################################### -/

/-- **★★★ `tailMoment_expSuppressed_bound`.**  THE CONCRETE OFF-COLLAR TAIL MOMENT BOUND.  For `0 ≤ R`,
        `|tailMoment i τ R| ≤ (√2)ⁿ · exp(−R²/(8τ)) · (2n+1)/(2τ)`.
    Sharpens the crude `tailMoment_bound : |T_τ| ≤ τ⁻¹` with the honest Gaussian tail-decay factor.
    Route: `|T_τ| ≤ ∫_{‖z‖>R}‖H‖`; on the tail `‖H‖ = |(z_i²−2τ)/(4τ²)|·G_τ ≤
    (‖z‖²+2τ)/(4τ²)·[(√2)ⁿe^{−R²/8τ}G_{2τ}]` (weight bound × `gaussDdim_tail_le_scaled`); extend to
    full space and integrate via `∫‖z‖²G_{2τ} ≤ 4nτ` (`normPow_gauss_tau`/`oneD_absMoment2`) and
    `∫G_{2τ} = 1`.  ⚠ NOT `a₁ = R/6`. -/
theorem tailMoment_expSuppressed_bound (τ R : ℝ) (hτ : 0 < τ) (hR : 0 ≤ R) (i : Fin n) :
    |SliverTailMatched.tailMoment i τ R|
      ≤ Real.sqrt 2 ^ n * Real.exp (-(R ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ)) := by
  have hτ0 : τ ≠ 0 := hτ.ne'
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  -- the doubled-time second moment `∫ ‖z‖²·G_{2τ} ≤ 4nτ`.
  have hmom2 : ∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z ≤ 4 * (n : ℝ) * τ := by
    have h := normPow_gauss_tau (n := n) 2 (by norm_num) 2 (by norm_num) (2 * τ) h2τ
      (oneD_absMoment2 (2 * τ) h2τ)
    have hsq : (n : ℝ) * 2 * (Real.sqrt (2 * τ)) ^ 2 = 4 * (n : ℝ) * τ := by
      rw [Real.sq_sqrt h2τ.le]; ring
    linarith [h, hsq]
  set C : ℝ := Real.sqrt 2 ^ n * Real.exp (-(R ^ 2) / (8 * τ)) with hCdef
  set G : Point n → ℝ :=
    fun z => C * (1 / (4 * τ ^ 2) * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
                    + 1 / (2 * τ) * gaussDdim (2 * τ) z) with hGdef
  have hI2 : Integrable (fun z : Point n => ‖z‖ ^ 2 * gaussDdim (2 * τ) z) volume :=
    normPow_gauss_integrable 2 (by norm_num) (2 * τ) h2τ
  have hI0 : Integrable (fun z : Point n => gaussDdim (2 * τ) z) volume :=
    gaussDdim_integrable (2 * τ) h2τ
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
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
  -- the pointwise domination of the tail integrand `‖H‖ ≤ G` on `‖z‖ > R`.
  have hpt : ∀ z ∈ (SliverTailMatched.collar R)ᶜ,
      ‖SliverTailMatched.hessGaussFactor i τ z‖ ≤ G z := by
    intro z hz
    have hznorm : R < ‖z‖ := by
      rw [Set.mem_compl_iff, SliverTailMatched.collar, Set.mem_setOf_eq, not_le] at hz
      exact hz
    have hg1 : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
    have hnorm_eq : ‖SliverTailMatched.hessGaussFactor i τ z‖
        = |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z := by
      rw [SliverTailMatched.hessGaussFactor, Real.norm_eq_abs, abs_mul, abs_of_nonneg hg1]
    have hzi_norm : |z i| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z i
    have hzi_sq : (z i) ^ 2 ≤ ‖z‖ ^ 2 := by
      nlinarith [hzi_norm, abs_nonneg (z i), sq_abs (z i), norm_nonneg z]
    have habs : |(z i) ^ 2 - 2 * τ| ≤ ‖z‖ ^ 2 + 2 * τ := by
      rw [abs_le]; constructor <;> nlinarith [hzi_sq, hτ, sq_nonneg (z i), norm_nonneg z]
    have hweight : |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 4 * τ ^ 2 by positivity)]
      gcongr
    have htail : gaussDdim τ z
        ≤ Real.sqrt 2 ^ n * Real.exp (-(R ^ 2) / (8 * τ)) * gaussDdim (2 * τ) z :=
      gaussDdim_tail_le_scaled τ R hτ hR z hznorm
    rw [hnorm_eq]
    calc |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z
        ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2)
            * (Real.sqrt 2 ^ n * Real.exp (-(R ^ 2) / (8 * τ)) * gaussDdim (2 * τ) z) :=
          mul_le_mul hweight htail hg1 (by positivity)
      _ = G z := by rw [hGdef, hCdef]; field_simp; ring
  -- the integral of the dominator in closed form.
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
  calc |SliverTailMatched.tailMoment i τ R|
      = ‖∫ z in (SliverTailMatched.collar R)ᶜ, SliverTailMatched.hessGaussFactor i τ z‖ := by
        simp only [SliverTailMatched.tailMoment, Real.norm_eq_abs]
    _ ≤ ∫ z in (SliverTailMatched.collar R)ᶜ, ‖SliverTailMatched.hessGaussFactor i τ z‖ :=
        norm_integral_le_integral_norm
          (f := fun z : Point n => SliverTailMatched.hessGaussFactor i τ z)
    _ ≤ ∫ z in (SliverTailMatched.collar R)ᶜ, G z :=
        setIntegral_mono_on
          ((SliverTailMatched.hessGaussFactor_integrable τ hτ i).norm.integrableOn)
          hGint.integrableOn ((SliverTailMatched.collar_measurableSet R).compl) hpt
    _ ≤ ∫ z, G z := setIntegral_le_integral hGint (ae_of_all _ hGnn)
    _ ≤ C * ((2 * (n : ℝ) + 1) / (2 * τ)) := hInt_G

/-! ###############################################################################
    ### §3 — the √ε-collar specialisation (`R = c·√τ`): the concrete `hOffCollarTail`.
    ############################################################################### -/

/-- **★ `tailMoment_collar_expSuppressed`.**  THE √ε-COLLAR SPECIALISATION — the concrete
    `hOffCollarTail`.  With the sliver collar radius `R = c·√τ` (`0 ≤ c`), the exponent collapses to a
    `τ`-independent constant `exp(−c²/8)`:
        `|tailMoment i τ (c√τ)| ≤ (√2)ⁿ · exp(−c²/8) · (2n+1)/(2τ)`.
    This is the corrected off-collar Gaussian-tail moment integral, exponentially small in `c²` relative
    to the naive `τ⁻¹` (`tailMoment_bound`).  ⚠ Still `O(τ⁻¹)` for FIXED `c`; the exponential is
    operational only under a growing collar `c = c(τ)` — the genuine `O(τ^{−1/2})` term-1 closure is the
    matched pair `SliverTailMatched.sliver_term1_on_collar_matched`.  ⚠ NOT `a₁ = R/6`. -/
theorem tailMoment_collar_expSuppressed (τ c : ℝ) (hτ : 0 < τ) (hc : 0 ≤ c) (i : Fin n) :
    |SliverTailMatched.tailMoment i τ (c * Real.sqrt τ)|
      ≤ Real.sqrt 2 ^ n * Real.exp (-(c ^ 2) / 8) * ((2 * (n : ℝ) + 1) / (2 * τ)) := by
  have hR : 0 ≤ c * Real.sqrt τ := mul_nonneg hc (Real.sqrt_nonneg _)
  have h := tailMoment_expSuppressed_bound τ (c * Real.sqrt τ) hτ hR i
  have hEq : -((c * Real.sqrt τ) ^ 2) / (8 * τ) = -(c ^ 2) / 8 := by
    rw [mul_pow, Real.sq_sqrt hτ.le]
    field_simp
  rw [hEq] at h
  exact h

end QIQTH.OffCollarTailMoment

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.OffCollarTailMoment.gaussDdim_tail_le_scaled
#print axioms QIQTH.OffCollarTailMoment.tailMoment_expSuppressed_bound
#print axioms QIQTH.OffCollarTailMoment.tailMoment_collar_expSuppressed
