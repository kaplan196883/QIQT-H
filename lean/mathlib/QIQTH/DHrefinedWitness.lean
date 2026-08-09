/-
  DHrefinedWitness — J4-452: the CENTERING/SHAPE GATE on the census `hDHrefined` atom, and its
  CORRECTED (two-term) re-grounding of the a₁ = R/6 census `hProfRate`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ★★★ THE MANDATORY SATISFIABILITY GATE (run BEFORE any lemma; the verdict is BINDING).

  THE J4-451 census consumes `hDHrefined` in the SINGLE-COORDINATE, ONE-TERM, 0-CENTERED shape
    `|witnessFieldDeriv i (u−s) x z| ≤ CA/(2(u−s))·(|z_i|·gaussDdim (wA(u−s)) z)`   a.e. `z`.

  AUDIT OF THE ACTUAL WITNESS SLOPE (E1/E2 + the J4-443 chain rule).  The on-gate first-derivative
  formula (`HeatResidualBound.witnessFieldDeriv_gate_abs_le`) is
    `|dH i τ p z| ≤ G_τ(W z p)·(Bs·Ba + Bd)`,   `Bs = |−(∑ₖ (W z p)ₖ·Pvalₖ)/(2τ)|`,
  i.e. the parametrix slope is the FULL CONTRACTION `sc = −⟨W z p, ∂ᵢW⟩/(2τ)` (`Pval = ∂ᵢW`, the
  chart FIELD-jet), NOT a single coordinate.  By Cauchy–Schwarz `|sc| ≤ ‖W z p‖·L/(2τ)` (`L` the
  chart-Jacobian column bound), so the slope term is `‖W z p‖·(bounded)/(2τ)·G_τ(W z p)` — a FULL-NORM
  `‖W z p‖`-MOMENT, which the near-isometry (coercivity `½‖z‖² ≤ ‖W z p‖²` + Lipschitz upper) maps to a
  FULL-NORM `‖z‖`-moment `‖z‖·G_σ(z)`.  The `Bd = |∂ᵢA|` term contributes a pure GAUSSIAN MASS
  `Bd·G_σ(z)` (no `1/(2τ)`, no moment).

  ── THE GATE VERDICT (two-term SHAPE CORRECTION, satisfiable; the single-coordinate shape is NOT).
    (1)  UNSATISFIABLE AS STATED.  The demanded `|z_i|` (single coordinate) CANNOT be produced from the
         honest slope: the contraction gives the FULL norm `‖z‖`, and `‖z‖ ≤ |z_i|` is FALSE.  So the
         J4-451 one-term single-coordinate `hDHrefined` is not the honest envelope of the witness slope.
    (2)  THE CORRECTED SATISFIABLE SHAPE `hDHrefined₂` (two-term, full-norm + mass, single width):
           `|dH i (u−s) x z| ≤ (CA/(2(u−s))·‖z‖ + CB)·gaussDdim (wA(u−s)) z`   a.e. `z`.
         BOTH terms are honest: the `‖z‖`-moment is the contracted parametrix slope through the
         near-isometry; the `CB` mass is the amplitude-derivative term `Bd`.  This IS at the exact
         `witnessFieldDeriv_gate_envelope`/`hgauss_env` honesty tier (a chart + Gaussian geometry fact,
         near-isometry-satisfiable), one refinement up (moment envelope instead of bare envelope).
    (3)  THE RATE SURVIVES (the mass-term scaling settled — NO `τ^{−1}` blow-up).  Under the weighted
         two-Gaussian pairing:
           · MOMENT term:  `‖z‖ ≤ ∑ⱼ|zⱼ|` (banked `norm_pow_le_sum_abs_pow`), so
             `∫ ‖z‖·G_a·G_b ≤ ∑ⱼ ∫|zⱼ|·G_a·G_b ≤ n·G_{a+b}(0)·(3/2)√h` (the banked centered
             `pairing_moment_zero` summed over coordinates), `√h ≤ √(wA·τ)` ⟹ the `Q·τ^{−1/2}` rate
             (with `Q` inflated by `n`).  m-FREE.
           · MASS term:  `∫ G_a·G_b = G_{a+b}(0)` (banked `gaussDdim_pairing_integral`), bounded
             `s`-uniformly by `K := G_{min(wA,wF)·u}(0)` (antitone).  Its contribution is `τ⁰` BOUNDED
             (NO `1/(2τ)` singularity — the mass term has no `τ`-power), and `τ⁰ = √τ·τ^{−1/2} ≤
             √u·τ^{−1/2}`, so it is absorbed into `Q·τ^{−1/2}`.  The feared `Q'·τ^{−1}` blow-up does
             NOT occur: the mass coefficient `CB` carries NO `1/(2τ)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (this file, ns `QIQTH.DHrefinedWitness`).
    • `normPairing_moment`      — ★ the FULL-NORM centered pairing moment
        `∫ ‖z‖·(G_a·G_b) ≤ n·G_{a+b}(0)·(3/2)√(ab/(a+b))` (`‖z‖ ≤ ∑|zⱼ|` + banked `pairing_moment_zero`).
    • `profRate_inner_bound₂`   — ★★ THE CORRECTED ABSTRACT LEVER: the two-term envelope
        `|dH z| ≤ (CA/(2τ)·‖z‖ + CB)·G_{wA τ}(z)` + the Levi Gaussian envelope ⟹ `|∫ dH·Lev| ≤ Q·τ^{−1/2}`.
    • `profRate_integral₂`      — ★★ the EXACT census `hProfRate` shape, re-grounded on the CORRECTED
        `{hDHrefined₂, hFdomEvery, hProdMeas}` (identical conclusion to `profRate_integral`).
    • `hGint_regrounded₂`       — ★★ the census `hGint`, `hProfRate` re-grounded on `hDHrefined₂`.
    • `perUCensus_phase9`       — ★★★ the fired per-`u` census, `hProfRate` re-grounded on `hDHrefined₂`.

  ⚠  HONESTY FIREWALL.  Every theorem re-threads BANKED Gaussian pairing/moment machinery + the
  CORRECTED two-term (satisfiable) field-derivative envelope + the standing Levi envelope into the exact
  census `hProfRate`/`hGint` shapes.  NONE proves `a₁ = R/6`.  Each carried hypothesis is genuine,
  satisfiable, non-vacuous, strictly lower-level than the conclusion, and never the conclusion.  No
  `sorry` (header prose excepted), no `:= True`, no new axioms, no existing file edited.  `a₁ = R/6`
  remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack AND on the surviving
  enumerated carries.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.WeightedPairingHelper
import QIQTH.GaussianMomentEnvelope

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.WeightedPairingHelper QIQTH.CConvV2GaussianPairing QIQTH.ResidueBound
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.DHrefinedWitness

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `normPairing_moment` — the full-norm centered two-Gaussian pairing moment.
    ############################################################################### -/

/-- **★ `normPairing_moment` — THE FULL-NORM CENTERED PAIRING MOMENT.**  For `a, b > 0`,
      `∫ z, ‖z‖·(G_a(z)·G_b(z)) ≤ n·(G_{a+b}(0)·(3/2)·√(ab/(a+b)))`.
    Route: `‖z‖ ≤ ∑ⱼ|zⱼ|` (banked `norm_pow_le_sum_abs_pow` at `k=1`), so
    `∫ ‖z‖·(G_a·G_b) ≤ ∑ⱼ ∫|zⱼ|·(G_a·G_b) ≤ ∑ⱼ G_{a+b}(0)·(3/2)√h` (the banked centered corollary
    `pairing_moment_zero`), then the constant sum over the `n` coordinates.  ⚠ NOT `a₁ = R/6`. -/
theorem normPairing_moment (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ z : Point n, ‖z‖ * (gaussDdim a z * gaussDdim b z))
      ≤ (n : ℝ) * (gaussDdim (a + b) (0 : Point n) * (3 / 2 * Real.sqrt (a * b / (a + b)))) := by
  have hh : 0 < a * b / (a + b) := by positivity
  -- each coordinate moment integrand is integrable (via the product-to-single factorization)
  have hIntj : ∀ j : Fin n,
      Integrable (fun z : Point n => |z j| * (gaussDdim a z * gaussDdim b z)) volume := by
    intro j
    have hpt : (fun z : Point n => |z j| * (gaussDdim a z * gaussDdim b z))
        = fun z => gaussDdim (a + b) (0 : Point n) * (|z j| * gaussDdim (a * b / (a + b)) z) := by
      funext z; rw [gaussDdim_sq_pairing a b ha hb z]; ring
    rw [hpt]
    have hb1 : Integrable (fun z : Point n => |z j| * gaussDdim (a * b / (a + b)) z) volume := by
      have := QIQTH.HeatResidualBound.coordAbsPow_gauss_integrable (a * b / (a + b)) hh j 1
      simpa using this
    exact hb1.const_mul _
  have hInt : Integrable
      (fun z : Point n => ∑ j : Fin n, |z j| * (gaussDdim a z * gaussDdim b z)) volume :=
    integrable_finsetSum _ (fun j _ => hIntj j)
  -- pointwise ‖z‖·(G_a·G_b) ≤ ∑ⱼ |zⱼ|·(G_a·G_b)
  have hmono : (∫ z : Point n, ‖z‖ * (gaussDdim a z * gaussDdim b z))
      ≤ ∫ z : Point n, ∑ j : Fin n, |z j| * (gaussDdim a z * gaussDdim b z) := by
    refine integral_mono_of_nonneg (ae_of_all _ (fun z => ?_)) hInt (ae_of_all _ (fun z => ?_))
    · exact mul_nonneg (norm_nonneg _)
        (mul_nonneg (gaussDdim_nonneg _ _) (gaussDdim_nonneg _ _))
    · have hG : 0 ≤ gaussDdim a z * gaussDdim b z :=
        mul_nonneg (gaussDdim_nonneg _ _) (gaussDdim_nonneg _ _)
      have hns : ‖z‖ ≤ ∑ j, |z j| := by
        have := QIQTH.HeatResidualBound.norm_pow_le_sum_abs_pow 1 (le_refl 1) z
        simpa using this
      calc ‖z‖ * (gaussDdim a z * gaussDdim b z)
          ≤ (∑ j, |z j|) * (gaussDdim a z * gaussDdim b z) :=
            mul_le_mul_of_nonneg_right hns hG
        _ = ∑ j, |z j| * (gaussDdim a z * gaussDdim b z) := by rw [Finset.sum_mul]
  -- ∫ ∑ = ∑ ∫, then each ≤ pairing_moment_zero, then constant sum
  have hsum : (∫ z : Point n, ∑ j : Fin n, |z j| * (gaussDdim a z * gaussDdim b z))
      = ∑ j : Fin n, ∫ z : Point n, |z j| * (gaussDdim a z * gaussDdim b z) :=
    integral_finsetSum _ (fun j _ => hIntj j)
  calc (∫ z : Point n, ‖z‖ * (gaussDdim a z * gaussDdim b z))
      ≤ ∫ z : Point n, ∑ j : Fin n, |z j| * (gaussDdim a z * gaussDdim b z) := hmono
    _ = ∑ j : Fin n, ∫ z : Point n, |z j| * (gaussDdim a z * gaussDdim b z) := hsum
    _ ≤ ∑ _j : Fin n, gaussDdim (a + b) (0 : Point n) * (3 / 2 * Real.sqrt (a * b / (a + b))) :=
        Finset.sum_le_sum (fun j _ => pairing_moment_zero j a b ha hb)
    _ = (n : ℝ) * (gaussDdim (a + b) (0 : Point n) * (3 / 2 * Real.sqrt (a * b / (a + b)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ###############################################################################
    ### ★★ `profRate_inner_bound₂` — the CORRECTED two-term lever ⟹ `Q·τ^{−1/2}`.
    ############################################################################### -/

/-- **★★ `profRate_inner_bound₂` — THE CORRECTED ABSTRACT LEVER (the satisfiable two-term envelope).**
    For `τ = u − s`, `0 < s < u`, widths `wA, wF > 0`, amplitudes `CA, CB, CF ≥ 0`, two integrands
    `dH Lev : Point n → ℝ` with product `AEStronglyMeasurable` (`hmeas`), the a.e. TWO-TERM CENTERED
    envelope `|dH z| ≤ (CA/(2τ)·‖z‖ + CB)·G_{wA·τ}(z)` (`hdH` — the honest witness-slope shape:
    full-norm moment + amplitude-derivative mass) and the pointwise CENTERED Levi Gaussian envelope
    `|Lev z| ≤ CF·G_{wF·s}(z)` (`hLev`), the absolute product integral obeys
      `|∫z dH·Lev| ≤ ((3·n·CA·CF·G_{min(wA,wF)·u}(0)·√wA/4) + CB·CF·G_{min(wA,wF)·u}(0)·√u)·τ^{−1/2}`.
    Route: dominate `‖dH·Lev‖` by `CF·(CA/(2τ)‖z‖ + CB)·G_{wA τ}·G_{wF s}`, split into the FULL-NORM
    MOMENT (`normPairing_moment`, `≤ n·G_{a+b}(0)·(3/2)√h`) and the MASS (`gaussDdim_pairing_integral`,
    `= G_{a+b}(0)`), bound `G_{a+b}(0) ≤ G_{min·u}(0)` (antitone) and `√h ≤ √(wA τ)`, and count
    `τ⁻¹·√τ = τ^{−1/2}` (moment), `1 ≤ √u·τ^{−1/2}` (mass).  m-FREE.  ⚠ NOT `a₁ = R/6`. -/
theorem profRate_inner_bound₂ (i : Fin n) (u s wA CA CB wF CF : ℝ)
    (hs0 : 0 < s) (hsu : s < u) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (dH Lev : Point n → ℝ)
    (hmeas : AEStronglyMeasurable (fun z => dH z * Lev z) volume)
    (hdH : ∀ᵐ z ∂(volume : Measure (Point n)),
      |dH z| ≤ (CA / (2 * (u - s)) * ‖z‖ + CB) * gaussDdim (wA * (u - s)) z)
    (hLev : ∀ z : Point n, |Lev z| ≤ CF * gaussDdim (wF * s) z) :
    |∫ z, dH z * Lev z|
      ≤ ((3 * ((n : ℝ) * (CA * CF)) * gaussDdim (min wA wF * u) (0 : Point n) * Real.sqrt wA / 4)
          + CB * CF * gaussDdim (min wA wF * u) (0 : Point n) * Real.sqrt u)
          * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hτ : 0 < u - s := by linarith
  have hu : 0 < u := by linarith
  set τ : ℝ := u - s with hτ_def
  set a : ℝ := wA * τ with ha_def
  set bb : ℝ := wF * s with hbb_def
  have ha : 0 < a := mul_pos hwA hτ
  have hbb : 0 < bb := mul_pos hwF hs0
  have hab : 0 < a + bb := by linarith
  have hh : 0 < a * bb / (a + bb) := by positivity
  set K : ℝ := gaussDdim (min wA wF * u) (0 : Point n) with hK_def
  have hKnn : 0 ≤ K := gaussDdim_nonneg _ _
  have hτs : (0 : ℝ) < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  -- the two-piece dominator
  set D : Point n → ℝ := fun z =>
    CF * CA / (2 * τ) * (‖z‖ * (gaussDdim a z * gaussDdim bb z))
      + CF * CB * (gaussDdim a z * gaussDdim bb z) with hD_def
  -- a.e. domination ‖dH·Lev‖ ≤ D
  have hdom : ∀ᵐ z ∂(volume : Measure (Point n)), ‖dH z * Lev z‖ ≤ D z := by
    filter_upwards [hdH] with z h1
    have h2 := hLev z
    have hB1nn : 0 ≤ (CA / (2 * τ) * ‖z‖ + CB) * gaussDdim a z := le_trans (abs_nonneg _) h1
    rw [Real.norm_eq_abs, abs_mul]
    calc |dH z| * |Lev z|
        ≤ ((CA / (2 * τ) * ‖z‖ + CB) * gaussDdim a z) * (CF * gaussDdim bb z) :=
          mul_le_mul h1 h2 (abs_nonneg _) hB1nn
      _ = D z := by simp only [hD_def]; ring
  -- the two pieces are integrable
  have hIntNorm : Integrable (fun z : Point n => ‖z‖ * (gaussDdim a z * gaussDdim bb z)) volume := by
    have hpt : (fun z : Point n => ‖z‖ * (gaussDdim a z * gaussDdim bb z))
        = fun z => gaussDdim (a + bb) (0 : Point n) * (‖z‖ * gaussDdim (a * bb / (a + bb)) z) := by
      funext z; rw [gaussDdim_sq_pairing a bb ha hbb z]; ring
    rw [hpt]
    have hb1 : Integrable (fun z : Point n => ‖z‖ * gaussDdim (a * bb / (a + bb)) z) volume := by
      have := QIQTH.HeatResidualBound.normPow_gauss_integrable (n := n) 1 (le_refl 1)
        (a * bb / (a + bb)) hh
      simpa using this
    exact hb1.const_mul _
  have hIntMass : Integrable (fun z : Point n => gaussDdim a z * gaussDdim bb z) volume := by
    have hpt : (fun z : Point n => gaussDdim a z * gaussDdim bb z)
        = fun z => gaussDdim (a + bb) (0 : Point n) * gaussDdim (a * bb / (a + bb)) z := by
      funext z; rw [gaussDdim_sq_pairing a bb ha hbb z]
    rw [hpt]
    exact (QIQTH.HeatResidualBound.gaussDdim_integrable (a * bb / (a + bb)) hh).const_mul _
  have hDint : Integrable D volume := by
    simp only [hD_def]
    exact (hIntNorm.const_mul _).add (hIntMass.const_mul _)
  have hfint : Integrable (fun z : Point n => dH z * Lev z) volume := hDint.mono' hmeas hdom
  -- G_{a+bb}(0) ≤ K, and √h ≤ √wA·√τ
  have hGle : gaussDdim (a + bb) (0 : Point n) ≤ K := by
    rw [hK_def]
    refine gaussDdim_zero_antitone (min wA wF * u) (a + bb) ?_ ?_
    · exact mul_pos (lt_min hwA hwF) hu
    · have h1 : min wA wF * τ ≤ a := by
        rw [ha_def]; exact mul_le_mul_of_nonneg_right (min_le_left _ _) hτ.le
      have h2 : min wA wF * s ≤ bb := by
        rw [hbb_def]; exact mul_le_mul_of_nonneg_right (min_le_right _ _) hs0.le
      have hus : u = τ + s := by rw [hτ_def]; ring
      nlinarith [h1, h2]
  have hsqrt : Real.sqrt (a * bb / (a + bb)) ≤ Real.sqrt wA * Real.sqrt τ := by
    have hha : a * bb / (a + bb) ≤ a := by
      rw [div_le_iff₀ hab]; nlinarith [ha, hbb]
    calc Real.sqrt (a * bb / (a + bb)) ≤ Real.sqrt a := Real.sqrt_le_sqrt hha
      _ = Real.sqrt wA * Real.sqrt τ := by rw [ha_def, Real.sqrt_mul hwA.le]
  -- the moment-term bound: CF·CA/(2τ)·∫‖z‖(G_a·G_bb) ≤ (3·n·CA·CF·K·√wA/4)·τ^{−1/2}
  have hmomterm :
      CF * CA / (2 * τ) * (∫ z : Point n, ‖z‖ * (gaussDdim a z * gaussDdim bb z))
        ≤ (3 * ((n : ℝ) * (CA * CF)) * K * Real.sqrt wA / 4) * τ ^ (-(1 : ℝ) / 2) := by
    have hc0 : 0 ≤ CF * CA / (2 * τ) := by positivity
    have hstep :
        (n : ℝ) * (gaussDdim (a + bb) (0 : Point n) * (3 / 2 * Real.sqrt (a * bb / (a + bb))))
          ≤ (n : ℝ) * (K * (3 / 2 * (Real.sqrt wA * Real.sqrt τ))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      apply mul_le_mul hGle _ _ hKnn
      · exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    calc CF * CA / (2 * τ) * (∫ z : Point n, ‖z‖ * (gaussDdim a z * gaussDdim bb z))
        ≤ CF * CA / (2 * τ)
            * ((n : ℝ) * (gaussDdim (a + bb) (0 : Point n)
                * (3 / 2 * Real.sqrt (a * bb / (a + bb))))) :=
          mul_le_mul_of_nonneg_left (normPairing_moment a bb ha hbb) hc0
      _ ≤ CF * CA / (2 * τ) * ((n : ℝ) * (K * (3 / 2 * (Real.sqrt wA * Real.sqrt τ)))) :=
          mul_le_mul_of_nonneg_left hstep hc0
      _ = (3 * ((n : ℝ) * (CA * CF)) * K * Real.sqrt wA / 4) * τ ^ (-(1 : ℝ) / 2) := by
          rw [← QIQTH.HeatResidualBound.inv_sqrt_eq_rpow τ hτ]
          have h2τ : (2 : ℝ) * τ = 2 * (Real.sqrt τ * Real.sqrt τ) := by
            rw [Real.mul_self_sqrt hτ.le]
          rw [h2τ]; field_simp; ring
  -- the mass-term bound: CF·CB·∫(G_a·G_bb) = CF·CB·G_{a+bb}(0) ≤ (CB·CF·K·√u)·τ^{−1/2}
  have hmassterm :
      CF * CB * (∫ z : Point n, gaussDdim a z * gaussDdim bb z)
        ≤ (CB * CF * K * Real.sqrt u) * τ ^ (-(1 : ℝ) / 2) := by
    rw [gaussDdim_pairing_integral a bb ha hbb]
    have h1 : CF * CB * gaussDdim (a + bb) (0 : Point n) ≤ CF * CB * K :=
      mul_le_mul_of_nonneg_left hGle (by positivity)
    have hCBCFK : (0 : ℝ) ≤ CB * CF * K := mul_nonneg (mul_nonneg hCB hCF) hKnn
    have hsu' : Real.sqrt τ ≤ Real.sqrt u := Real.sqrt_le_sqrt (by linarith)
    rw [← QIQTH.HeatResidualBound.inv_sqrt_eq_rpow τ hτ]
    have hkey : CF * CB * K * Real.sqrt τ ≤ CB * CF * K * Real.sqrt u := by
      have := mul_le_mul_of_nonneg_left hsu' hCBCFK
      nlinarith [this]
    have hcancel : CF * CB * K = CF * CB * K * Real.sqrt τ * (Real.sqrt τ)⁻¹ := by
      rw [mul_assoc (CF * CB * K), mul_inv_cancel₀ hτs.ne', mul_one]
    have h2 : CF * CB * K ≤ (CB * CF * K * Real.sqrt u) * (Real.sqrt τ)⁻¹ := by
      rw [hcancel]
      exact mul_le_mul_of_nonneg_right hkey (by positivity)
    linarith [h1, h2]
  -- assemble ∫ D ≤ target
  have hQ : (∫ z, D z) ≤
      ((3 * ((n : ℝ) * (CA * CF)) * K * Real.sqrt wA / 4)
        + CB * CF * K * Real.sqrt u) * τ ^ (-(1 : ℝ) / 2) := by
    have hsplit : (∫ z, D z)
        = CF * CA / (2 * τ) * (∫ z : Point n, ‖z‖ * (gaussDdim a z * gaussDdim bb z))
          + CF * CB * (∫ z : Point n, gaussDdim a z * gaussDdim bb z) := by
      simp only [hD_def]
      rw [integral_add (hIntNorm.const_mul _) (hIntMass.const_mul _),
          integral_const_mul, integral_const_mul]
    have hexpand :
        ((3 * ((n : ℝ) * (CA * CF)) * K * Real.sqrt wA / 4) + CB * CF * K * Real.sqrt u)
            * τ ^ (-(1 : ℝ) / 2)
          = (3 * ((n : ℝ) * (CA * CF)) * K * Real.sqrt wA / 4) * τ ^ (-(1 : ℝ) / 2)
            + (CB * CF * K * Real.sqrt u) * τ ^ (-(1 : ℝ) / 2) := by ring
    rw [hsplit, hexpand]
    exact add_le_add hmomterm hmassterm
  -- fire the banked dominated-integral bound
  exact QIQTH.GpowClosure.abs_integral_le_of_dom (fun z => dH z * Lev z) D
    (((3 * ((n : ℝ) * (CA * CF)) * K * Real.sqrt wA / 4)
        + CB * CF * K * Real.sqrt u) * τ ^ (-(1 : ℝ) / 2))
    hfint hDint hdom hQ

/-! ###############################################################################
    ### ★★ `profRate_integral₂` — the EXACT census hProfRate shape, CORRECTED re-grounding.
    ############################################################################### -/

/-- **★★ `profRate_integral₂` — THE `hProfRate` CARRY, CORRECTED re-grounding (J4-452).**  The EXACT
    `hProfRate` binder consumed by `ProfFacWitness.hGint_grounded` / `perUCensus_phase4` (identical shape
    to `ProfRateTheorem.profRate_theorem`'s conclusion): per `(u,i,x)`, a `Q ≥ 0` with the moment-gained
    inner rate `|∫z witnessFieldDeriv i (u−s) x z · leviSeries s z 0| ≤ Q·(u−s)^{−1/2}` on `0 < s < u`.
    Supplied from the CORRECTED (satisfiable) two-term field-derivative envelope `hDHrefined₂`
    (full-norm moment + amplitude-derivative mass — see THE GATE) and the every-ceiling Levi Gaussian
    envelope `hFdomEvery` (Tc := u), plus product measurability `hProdMeas`, fed through
    `profRate_inner_bound₂`.  The J4-451 single-coordinate `hDHrefined` (unsatisfiable from the witness
    slope) is REPLACED by `hDHrefined₂`.  `Q := 3·n·CA·CF·G_{min(wA,wF)·u}(0)·√wA/4 +
    CB·CF·G_{min(wA,wF)·u}(0)·√u`.  m-FREE.  ⚠ NOT `a₁ = R/6`. -/
theorem profRate_integral₂ (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hDHrefined₂ : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA CB : ℝ,
        0 < wA ∧ 0 ≤ CA ∧ 0 ≤ CB ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ (CA / (2 * (u - s)) * ‖z‖ + CB) * gaussDdim (wA * (u - s)) z)
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ Q : ℝ, 0 ≤ Q ∧
        ∀ s, 0 < s → s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ Q * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro u hu i x
  obtain ⟨wA, CA, CB, hwA, hCA, hCB, hdH⟩ := hDHrefined₂ u hu i x
  obtain ⟨wF, CF, hwF, hCF, hLev⟩ := hFdomEvery u
  have hKnn : 0 ≤ gaussDdim (min wA wF * u) (0 : Point n) := gaussDdim_nonneg _ _
  refine ⟨(3 * ((n : ℝ) * (CA * CF)) * gaussDdim (min wA wF * u) (0 : Point n) * Real.sqrt wA / 4)
      + CB * CF * gaussDdim (min wA wF * u) (0 : Point n) * Real.sqrt u, ?_, ?_⟩
  · refine add_nonneg ?_ ?_
    · apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 4)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hCA hCF))) hKnn) (Real.sqrt_nonneg _)
    · exact mul_nonneg (mul_nonneg (mul_nonneg hCB hCF) hKnn) (Real.sqrt_nonneg _)
  · intro s hs0 hsu
    exact profRate_inner_bound₂ i u s wA CA CB wF CF hs0 hsu hwA hCA hCB hwF hCF _ _
      (hProdMeas u hu i x s hs0 hsu) (hdH s hs0 hsu) (fun z => hLev s hs0 hsu.le z)

/-! ###############################################################################
    ### ★★ `hGint_regrounded₂` — the census hGint, hProfRate CORRECTED re-grounding.
    ############################################################################### -/

/-- **★★ `hGint_regrounded₂` — THE CENSUS `hGint`, `hProfRate` CORRECTED re-grounding (J4-452).**  The
    EXACT `hGint` conclusion of `ProfFacWitness.hGint_grounded`, with `hProfRate` supplied by
    `profRate_integral₂` on the CORRECTED satisfiable carry `hDHrefined₂` (two-term envelope) instead of
    the J4-451 unsatisfiable single-coordinate `hDHrefined`.  Every OTHER carry is threaded exactly as
    `hGint_grounded`.  ⚠ NOT `a₁ = R/6`. -/
theorem hGint_regrounded₂ (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hDHrefined₂ : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA CB : ℝ,
        0 < wA ∧ 0 ≤ CA ∧ 0 ≤ CB ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ (CA / (2 * (u - s)) * ‖z‖ + CB) * gaussDdim (wA * (u - s)) z)
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u :=
  QIQTH.ProfFacWitness.hGint_grounded g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery
    hGintMeas hWFDjoint hLeviJoint
    (profRate_integral₂ g gi hC hK S a b U hDHrefined₂ hFdomEvery hProdMeas)

/-! ###############################################################################
    ### ★★★ `perUCensus_phase9` — the fired per-`u` census, hProfRate CORRECTED re-grounding.
    ############################################################################### -/

/-- **★★★ `perUCensus_phase9`.**  `ProfFacWitness.perUCensus_phase4` with `hProfRate` supplied by
    `profRate_integral₂` — the J4-452 CORRECTED (two-term, satisfiable) re-grounding on `hDHrefined₂`
    (the J4-451 single-coordinate `hDHrefined`, unsatisfiable from the witness slope, is REPLACED).
    Every OTHER census field is threaded exactly as `perUCensus_phase4`.  Pure composition; each carry
    satisfiable, non-vacuous, strictly lower-level than the conclusion, none equal to `a₁ = R/6`.
    ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase9 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hDHrefined₂ : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA CB : ℝ,
        0 < wA ∧ 0 ≤ CA ∧ 0 ≤ CB ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ (CA / (2 * (u - s)) * ‖z‖ + CB) * gaussDdim (wA * (u - s)) z)
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n)))
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hQ1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        ∃ V ∈ 𝓝 (0 : Point n),
          ∀ y ∈ V, pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
              (u - epsSeq m) x 0) i y
            = QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m y) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.ProfFacWitness.perUCensus_phase4 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hFzero hWFDdomCapped hFdomEvery hGintMeas hWFDjoint hLeviJoint
    (profRate_integral₂ g gi hC hK S a b U hDHrefined₂ hFdomEvery hProdMeas)
    hbulkderiv hsliver hcont hQ1

end QIQTH.DHrefinedWitness

/-! ## THE `hDHrefined` GATE + RE-GROUNDING LEDGER (J4-452).

  ── ★★★ THE GATE VERDICT (binding; the single-coordinate shape is RETRACTED).
    The J4-451 census consumed `hDHrefined` in the SINGLE-COORDINATE, ONE-TERM, 0-CENTERED shape
      `|dH i (u−s) x z| ≤ CA/(2(u−s))·(|z_i|·G_{wA(u−s)}(z))`.
    The ACTUAL witness slope (E1 `witnessFieldDeriv_gate_abs_le`) is the FULL CONTRACTION
      `Bs = |−(∑ₖ (W z p)ₖ·(∂ᵢW)ₖ)/(2τ)| = |−⟨W z p, ∂ᵢW⟩/(2τ)| ≤ ‖W z p‖·L/(2τ)`   (Cauchy–Schwarz),
    which the near-isometry (coercivity + Lipschitz upper) maps to a FULL-NORM `‖z‖`-moment, NOT a
    single coordinate.  The amplitude-derivative term `Bd = |∂ᵢA|` is a pure GAUSSIAN MASS.  Hence:
      • the demanded `|z_i|` shape is UNSATISFIABLE (`‖z‖ ≤ |z_i|` is FALSE);
      • the CORRECTED satisfiable shape is TWO-TERM (full-norm moment + mass, single width):
          `hDHrefined₂ :  |dH i (u−s) x z| ≤ (CA/(2(u−s))·‖z‖ + CB)·G_{wA(u−s)}(z)`.

  ── THE MASS-TERM SCALING (the make-or-break, settled — NO `τ^{−1}` blow-up).
    The moment term pairs (via `‖z‖ ≤ ∑ⱼ|zⱼ|` + banked `pairing_moment_zero`) to `n·G_{a+b}(0)·(3/2)√h`
    with `√h ≤ √(wA τ)`, giving `Q·τ^{−1/2}` (Q inflated by `n`).  The mass term pairs (via banked
    `gaussDdim_pairing_integral`) to `CB·CF·G_{a+b}(0) ≤ CB·CF·K`, `K := G_{min(wA,wF)·u}(0)` bounded
    `s`-uniformly (antitone).  Crucially the mass coefficient carries NO `1/(2τ)`, so its contribution
    is `τ⁰` BOUNDED, and `τ⁰ = √τ·τ^{−1/2} ≤ √u·τ^{−1/2}` — absorbed into `Q·τ^{−1/2}`.  The feared
    `Q'·τ^{−1}` singularity does NOT arise (it would only if the mass had a `1/(2τ)` factor; it does not).

  ── AFTER J4-452, the census `hProfRate` rests (via `profRate_integral₂`) on the CORRECTED carries
    `{hDHrefined₂, hFdomEvery, hProdMeas}` (the J4-451 unsatisfiable single-coordinate `hDHrefined` is
    REPLACED by the two-term `hDHrefined₂`).  `hGint_regrounded₂` / `perUCensus_phase9` reproduce the
    EXACT `hGint_grounded` / `perUCensus_phase4` conclusions with this corrected supplier; every other
    carry is threaded identically.

  ── THE INTEGRAL-LEVEL ENGINE (fully PROVED here, no new carry).
    • `normPairing_moment` — `∫ ‖z‖·(G_a·G_b) ≤ n·G_{a+b}(0)·(3/2)√(ab/(a+b))` (`‖z‖ ≤ ∑|zⱼ|` +
      banked `pairing_moment_zero` summed over coordinates).  PROVED, std-3.
    • `profRate_inner_bound₂` — the corrected two-term lever ⟹ `Q·τ^{−1/2}` (moment via
      `normPairing_moment`, mass via `gaussDdim_pairing_integral`, `G_{a+b}(0) ≤ K` antitone,
      `√h ≤ √(wA τ)`, count `τ⁻¹√τ = τ^{−1/2}` and `τ⁰ ≤ √u·τ^{−1/2}`).  PROVED, std-3.
    • `profRate_integral₂` / `hGint_regrounded₂` / `perUCensus_phase9` — the exact census shapes,
      re-grounded on `hDHrefined₂`.

  ── DONT-UNDERCREDIT FINDINGS.
    • The full-norm moment infrastructure was ALREADY banked (`GaussianMomentEnvelope`):
      `norm_pow_le_sum_abs_pow` (`‖z‖^k ≤ ∑|zⱼ|^k`), `normPow_gauss_integrable`,
      `coordAbsPow_gauss_integrable`.  `normPairing_moment` needed only their assembly with the banked
      centered `pairing_moment_zero` — no new moment analysis.
    • The mass pairing `∫ G_a·G_b = G_{a+b}(0)` was banked (`CConvV2GaussianPairing.gaussDdim_pairing_integral`),
      the antitone peak bound `gaussDdim_zero_antitone`, the dominated-integral assembly
      `GpowClosure.abs_integral_le_of_dom`, and the `τ⁻¹√τ = τ^{−1/2}` count `inv_sqrt_eq_rpow` — the
      lever is a re-assembly of banked pieces at the corrected (two-term) envelope.
    • The `s`-uniform lower bound `a+b = wA(u−s)+wF·s ≥ min(wA,wF)·u` (via `nlinarith`) is what makes
      BOTH `G_{a+b}(0)` peaks (moment and mass) bounded `s`-uniformly — the same mechanism that carries
      the J4-451 single-coordinate lever, now applied to the honest full-norm + mass envelope.

  ⚠  J4-452 = the census `hProfRate` GATE-CORRECTED: the J4-451 single-coordinate `hDHrefined`
  (unsatisfiable from the witness slope) is retracted in favour of the two-term full-norm+mass
  `hDHrefined₂`, and the `Q·τ^{−1/2}` rate re-established with the mass term proven `τ⁰`-bounded (NO
  `τ^{−1}` blow-up).  This brick does NOT prove `a₁ = R/6` and makes NO claim of unconditionality.
  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack AND on the
  surviving enumerated carries.
-/

section AxiomChecks
open QIQTH.DHrefinedWitness
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms normPairing_moment
#print axioms profRate_inner_bound₂
#print axioms profRate_integral₂
#print axioms hGint_regrounded₂
#print axioms perUCensus_phase9
end AxiomChecks
