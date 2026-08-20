/-
  HZMassCappedWindowClosed — J4-886: the ELEMENTARY closure of the `hzmass` matched-power slot on the
  CAPPED window, discharging the FINDING-C `(t−s)⁻¹`-rate wall of `HZMassLeviBaseEnvelope` (J4-883).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick discharges the matched-power
  `hpow` slot of the J4-882 width-`2s` split reduction (`HZMassLeviBaseEnvelope.hzmass_of_peak_BF_gaussian2s_BL`)
  by the ELEMENTARY observation that the `hzmass` window `Set.uIoc 0 (t − εₘ)` is CAPPED away from `s = t`
  (`t − s ≥ εₘ > 0` on the WHOLE window), so the divergent `s → t` limit FINDING C feared is OUT OF SCOPE.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE CORRECTIVE FINDING (the audit that reopened `hzmass`).

  `HZMassLeviBaseEnvelope.FINDING C` (J4-883) concluded that the matched power `Ppk·CB ≤ C·(t−s)⁻¹`
  FAILS for `n ≥ 3`, because `Ppk s · CB s ≍ (t−s)^{−n/2}` and the target requires `(t−s)^{1−n/2} ≤ C`
  UNIFORMLY as `s → t` — which diverges for `n ≥ 3`.

  ⚠ THAT ANALYSIS EXAMINED THE WRONG LIMIT.  The `hzmass` field of `MixedDirectionsFieldHessianEnvelope`
  is quantified over `s ∈ Set.uIoc 0 (t − epsSeq m)` with `epsSeq m := 1/(m+1) > 0`
  (`HeatResidualBound.epsSeq`, `ConvApproximants`).  The window is CAPPED AWAY from `s = t`:
      `s ≤ t − εₘ  ⟹  t − s ≥ εₘ > 0`   on the WHOLE window,
  so `t − s` NEVER approaches `0`.  The `(t−s)^{1−n/2} → ∞ as s → t` divergence is therefore NEVER
  reached.  For FIXED `m` the product `Ppk s · CB s` is UNIFORMLY BOUNDED on the capped window by some
  finite `M` (an `m`-dependent constant, e.g. `M := gaussDdim (εₘ) 0 · P · C_L` via peak-width
  monotonicity — see `gaussDdimPeak_antitone_width`), and the matched power closes at `C := M · t`.

  ## THE ELEMENTARY MONOTONE BOUND (the load-bearing step, `hpow_capped`).

  On the capped window `0 < s ≤ t − εₘ` (with `t − εₘ > 0`, hence `t > 0`):
    • `t − s ≥ εₘ > 0`         (`s ≤ t − εₘ`);
    • `t − s ≤ t`              (`s ≥ 0`);
    • `t · (t − s)⁻¹ ≥ 1`      (`t ≥ t − s > 0`, monotone reciprocal — the EXACT `(t−s)^{−1}` case,
                                verified by the numeric sanity check below).
  Hence for `M ≥ 0` and any `Ppk s · CB s ≤ M`:
      `Ppk s · CB s ≤ M = M · 1 ≤ M · (t · (t − s)⁻¹) = (M · t) · (t − s)⁻¹`.
  This is a MONOTONE-RECIPROCAL inequality on the compact-in-`(t−s)` window — the elementary content the
  corrective audit identified (for the physical `n = 4`, `Ppk·CB ≍ (t−s)^{−1}·(t−s)^{−1}` and the
  `(t−s)^{−1}` blow-up is capped by `εₘ⁻¹`, i.e. `(t−s)^{−1} ≤ εₘ⁻¹`, a trivial monotone reciprocal).

  ### NUMERIC SANITY CHECK (direction of the monotone bound, `n = 4`, `m = 1`).
  `epsSeq 1 = 1/2`, so on the window `t − s ∈ [1/2, t)`.  The exponent in `Ppk·CB ≍ (t−s)^{−n/2} =
  (t−s)^{−2}` and target `(t−s)^{−1}` leaves the residual factor `(t−s)^{−(n/2−1)} = (t−s)^{−1}`, which,
  as a DECREASING function of `t−s > 0`, is MAXIMIZED at the LEFT endpoint `t − s = εₘ = 1/2`, giving
  `(t−s)^{−1} ≤ (1/2)^{−1} = 2 = εₘ⁻¹`.  Smallest `t−s ⟹ largest (t−s)⁻¹`: the bound direction is
  CONFIRMED (`x ↦ x⁻¹` is antitone on `x > 0`, so the sup over the window is at the cap `εₘ`).

  ## WHAT LANDS (ns `QIQTH.HZMassCappedWindowClosed`).
    • `hpow_capped` — ★★ the elementary monotone-reciprocal discharge of the matched-power slot:
      `Ppk·CB ≤ M ⟹ Ppk·CB ≤ (M·t)·(t−s)⁻¹` on the capped window.
    • `hzmass_capped_window_closed` — ★★★ the FULL `hzmass` closure on the capped window: feeds
      `hpow_capped` into the J4-882 width-`2s` split, reducing `hzmass` to a UNIFORM window bound
      `Ppk·CB ≤ M` (the residual `(t−s)⁻¹`-rate wall of FINDING C ELIMINATED).
    • `gaussDdimPeak_antitone_width` — ★ the peak-width monotonicity `gaussDdim w₂ 0 ≤ gaussDdim w₁ 0`
      for `0 < w₁ ≤ w₂`, exhibiting the concrete `m`-dependent `M` for the FINDING-C peak shape.
    • `hzmass_capped_window_gaussPeak` — ★★ the CONCRETE-shape closure: for `Ppk s := gaussDdim (t−s) 0
      · P` and `CB s := C_L` (the exact FINDING-C shape), the uniform bound `M := gaussDdim εₘ 0 · P · C_L`
      is supplied by peak-width monotonicity, so `hzmass` closes with a fully explicit `m`-dependent `C`.
    • `hzmass_capped_window_nonvacuous` — the antecedents are jointly inhabited (zero envelopes, `M = 0`).
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HZMassLeviBaseEnvelope

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.FlatHeatEquation QIQTH.ResidueBound
open QIQTH.RadialDistance
open scoped Topology BigOperators

namespace QIQTH.HZMassCappedWindowClosed

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §0 — the capped-window facts.
    ############################################################################### -/

/-- **§0 — capped window ⟹ `t > 0`.**  `t − εₘ > 0` and `εₘ > 0` give `t = (t − εₘ) + εₘ > 0`. -/
theorem t_pos_of_epspos {t : ℝ} {m : ℕ} (hepspos : 0 < t - epsSeq m) : 0 < t := by
  have := epsSeq_pos m
  linarith

/-- **§0 — membership ⟹ `t − s ≥ εₘ`.**  On the capped window (`t − εₘ > 0`, so
    `uIoc 0 (t − εₘ) = Ioc 0 (t − εₘ)`), membership gives `0 < s ≤ t − εₘ`, hence `t − s ≥ εₘ`. -/
theorem window_gap {t : ℝ} {m : ℕ} (hepspos : 0 < t - epsSeq m)
    {s : ℝ} (hs : s ∈ Set.uIoc 0 (t - epsSeq m)) : 0 < s ∧ epsSeq m ≤ t - s := by
  rw [Set.uIoc_of_le (le_of_lt hepspos)] at hs
  exact ⟨hs.1, by linarith [hs.2]⟩

/-! ###############################################################################
    ### §1 — the elementary monotone-reciprocal discharge of the matched power.
    ############################################################################### -/

/-- **★★ §1 — `hpow_capped`.**  THE ELEMENTARY LOAD-BEARING STEP.  On the capped window, a UNIFORM
    bound `Ppk s · CB s ≤ M` (`M ≥ 0`) discharges the matched-power slot at `C := M · t`:
      `Ppk s · CB s ≤ M ≤ (M · t) · (t − s)⁻¹`,
    because `t · (t − s)⁻¹ ≥ 1` (since `0 < t − s ≤ t`, a MONOTONE-RECIPROCAL inequality — the sup of
    `(t−s)⁻¹` on the window is at the cap `εₘ`, NOT at `s = t` which is OUT OF SCOPE).  NOT `a₁ = R/6`. -/
theorem hpow_capped (t : ℝ) (m : ℕ) (M : ℝ) (Ppk CB : ℝ → ℝ)
    (hMnn : 0 ≤ M) (hepspos : 0 < t - epsSeq m)
    (hPCbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → Ppk s * CB s ≤ M) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Ppk s * CB s ≤ (M * t) * (t - s)⁻¹ := by
  have htpos : 0 < t := t_pos_of_epspos hepspos
  filter_upwards [hPCbound] with s hpc hs
  obtain ⟨hspos, hgap⟩ := window_gap hepspos hs
  have hts : 0 < t - s := lt_of_lt_of_le (epsSeq_pos m) hgap
  have htle : t - s ≤ t := by linarith
  -- `t · (t − s)⁻¹ ≥ (t − s) · (t − s)⁻¹ = 1`.
  have hge1 : (1 : ℝ) ≤ t * (t - s)⁻¹ := by
    have hinvpos : 0 < (t - s)⁻¹ := inv_pos.mpr hts
    calc (1 : ℝ) = (t - s) * (t - s)⁻¹ := by
            rw [mul_inv_cancel₀ (ne_of_gt hts)]
      _ ≤ t * (t - s)⁻¹ := by exact mul_le_mul_of_nonneg_right htle (le_of_lt hinvpos)
  -- `M ≤ M · (t · (t − s)⁻¹) = (M · t) · (t − s)⁻¹`.
  have hMle : M ≤ (M * t) * (t - s)⁻¹ := by
    have : M * 1 ≤ M * (t * (t - s)⁻¹) := mul_le_mul_of_nonneg_left hge1 hMnn
    rw [mul_one] at this
    linarith [this, (by ring : M * (t * (t - s)⁻¹) = (M * t) * (t - s)⁻¹)]
  exact le_trans (hpc hs) hMle

/-! ###############################################################################
    ### §2 — the FULL `hzmass` closure on the capped window.
    ############################################################################### -/

/-- **★★★ §2 — `hzmass_capped_window_closed`.**  THE FULL `hzmass` closure on the capped window.
    Feeding the elementary `hpow_capped` into the J4-882 width-`2s` split reduction
    `HZMassLeviBaseEnvelope.hzmass_of_peak_BF_gaussian2s_BL`, the deep `z`-mass bound
    `∫z BL·BF ≤ C·(t−s)⁻¹` closes at `C := M · t`, given ONLY a UNIFORM window bound `Ppk s · CB s ≤ M`
    on the matched product (`M ≥ 0`) — the FINDING-C `(t−s)⁻¹`-rate wall (which examined the out-of-scope
    `s → t` limit) is ELIMINATED.  The remaining inputs are the honest split ingredients:
      • `hint`     — per-slice product integrability (the `hbint` field content);
      • `hBFpeak`  — the `z`-UNIFORM field-Hessian PEAK `BF s z ≤ Ppk s` (J4-868);
      • `hBLnn`    — Levi nonnegativity;
      • `hBLgauss` — the CONCRETE width-`2s` Levi Gaussian envelope `BL s z ≤ CB s · gaussDdim (2s) z`
                     (J4-883 §A, `leviBase_gaussDdim2s_envelope`);
      • `hPpknn`   — peak nonnegativity.
    NOT `a₁ = R/6`. -/
theorem hzmass_capped_window_closed
    (t : ℝ) (m : ℕ) (M : ℝ) (BL BF : ℝ → Point n → ℝ) (Ppk CB : ℝ → ℝ)
    (hMnn : 0 ≤ M) (hepspos : 0 < t - epsSeq m)
    (hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (hBFpeak : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BF s z ≤ Ppk s)
    (hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, 0 ≤ BL s z)
    (hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BL s z ≤ CB s * gaussDdim (2 * s) z)
    (hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        0 ≤ Ppk s)
    (hPCbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → Ppk s * CB s ≤ M) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, BL s z * BF s z) ≤ (M * t) * (t - s)⁻¹ := by
  have htpos : 0 < t := t_pos_of_epspos hepspos
  -- the split's window facts.
  have hspos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < s := by
    refine ae_of_all _ (fun s hs => (window_gap hepspos hs).1)
  have hpos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < t - s := by
    refine ae_of_all _ (fun s hs => ?_)
    exact lt_of_lt_of_le (epsSeq_pos m) (window_gap hepspos hs).2
  -- the elementary matched power at `C := M · t`.
  have hpow := hpow_capped t m M Ppk CB hMnn hepspos hPCbound
  exact QIQTH.HZMassLeviBaseEnvelope.hzmass_of_peak_BF_gaussian2s_BL
    (n := n) t m (M * t) BL BF Ppk CB
    (mul_nonneg hMnn (le_of_lt htpos)) hspos hpos hint hBFpeak hBLnn hBLgauss hPpknn hpow

/-! ###############################################################################
    ### §3 — peak-width monotonicity ⟹ the concrete `m`-dependent `M` for FINDING C's shape.
    ############################################################################### -/

/-- **★ §3 — `gaussDdimPeak_antitone_width`.**  The Gaussian PEAK `gaussDdim w 0 = (√(4πw))⁻ⁿ` is
    ANTITONE in the width `w`: for `0 < w₁ ≤ w₂`,
      `gaussDdim w₂ 0 ≤ gaussDdim w₁ 0`.
    (`√` monotone ⟹ `√(4πw₂) ≥ √(4πw₁) > 0` ⟹ `(√(4πw₂))⁻¹ ≤ (√(4πw₁))⁻¹` ⟹ `n`-th powers preserve.)
    This exhibits the concrete `m`-dependent uniform bound `gaussDdim (t−s) 0 ≤ gaussDdim εₘ 0` on the
    capped window (`t − s ≥ εₘ`), closing FINDING C's peak shape.  NOT `a₁ = R/6`. -/
theorem gaussDdimPeak_antitone_width {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hle : w₁ ≤ w₂) :
    gaussDdim w₂ (0 : Point n) ≤ gaussDdim w₁ (0 : Point n) := by
  have hw₂ : 0 < w₂ := lt_of_lt_of_le hw₁ hle
  have hr0 : (rncRadialSq (0 : Point n)) = 0 := by
    simp [rncRadialSq]
  -- normal form `gaussDdim w 0 = (√(4πw))⁻ⁿ`.
  have hform : ∀ w : ℝ, gaussDdim w (0 : Point n) = ((Real.sqrt (4 * Real.pi * w))⁻¹) ^ n := by
    intro w
    rw [gaussDdim_eq_exp, hr0]
    simp
  rw [hform w₁, hform w₂]
  -- the arguments of `√` are ordered and positive.
  have hpi : (0 : ℝ) < 4 * Real.pi := by positivity
  have harg₁ : (0 : ℝ) < 4 * Real.pi * w₁ := by positivity
  have hargle : 4 * Real.pi * w₁ ≤ 4 * Real.pi * w₂ :=
    mul_le_mul_of_nonneg_left hle (le_of_lt hpi)
  have hsqrtle : Real.sqrt (4 * Real.pi * w₁) ≤ Real.sqrt (4 * Real.pi * w₂) :=
    Real.sqrt_le_sqrt hargle
  have hsqrtpos : (0 : ℝ) < Real.sqrt (4 * Real.pi * w₁) := Real.sqrt_pos.mpr harg₁
  gcongr

/-- **★★ §3 — `hzmass_capped_window_gaussPeak`.**  THE CONCRETE-SHAPE `hzmass` closure.  For the exact
    FINDING-C peak shape `Ppk s := gaussDdim (t−s) 0 · P` (field-Hessian `z`-uniform peak, `P ≥ 0`) and
    `CB s := C_L` (the CONSTANT whole-gate Levi coefficient, `C_L ≥ 0`), the uniform window bound is
    supplied by peak-width monotonicity: on `t − s ≥ εₘ`,
      `Ppk s · CB s = gaussDdim (t−s) 0 · P · C_L ≤ gaussDdim εₘ 0 · P · C_L =: M`.
    Hence `hzmass` closes with the fully explicit `m`-dependent constant `C := M · t = gaussDdim εₘ 0 ·
    P · C_L · t`.  This is FINDING C's own `Ppk·CB ≍ (t−s)^{−n/2}` product, CAPPED at `εₘ` — the honest
    resolution of the reopened wall.  NOT `a₁ = R/6`. -/
theorem hzmass_capped_window_gaussPeak
    (t : ℝ) (m : ℕ) (P C_L : ℝ) (BL BF : ℝ → Point n → ℝ)
    (hP : 0 ≤ P) (hCL : 0 ≤ C_L) (hepspos : 0 < t - epsSeq m)
    (hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (hBFpeak : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BF s z ≤ gaussDdim (t - s) (0 : Point n) * P)
    (hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, 0 ≤ BL s z)
    (hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BL s z ≤ C_L * gaussDdim (2 * s) z) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, BL s z * BF s z)
          ≤ ((gaussDdim (epsSeq m) (0 : Point n) * P * C_L) * t) * (t - s)⁻¹ := by
  set M : ℝ := gaussDdim (epsSeq m) (0 : Point n) * P * C_L with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (gaussDdim_nonneg _ _) hP) hCL
  have hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      0 ≤ gaussDdim (t - s) (0 : Point n) * P :=
    ae_of_all _ (fun s _ => mul_nonneg (gaussDdim_nonneg _ _) hP)
  -- the uniform window bound `Ppk·CB ≤ M` via peak-width monotonicity.
  have hPCbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      (gaussDdim (t - s) (0 : Point n) * P) * C_L ≤ M := by
    refine ae_of_all _ (fun s hs => ?_)
    obtain ⟨_, hgap⟩ := window_gap hepspos hs
    have hpeakle : gaussDdim (t - s) (0 : Point n) ≤ gaussDdim (epsSeq m) (0 : Point n) :=
      gaussDdimPeak_antitone_width (epsSeq_pos m) hgap
    rw [hMdef]
    -- `(gaussDdim (t−s) 0 · P) · C_L ≤ (gaussDdim εₘ 0 · P) · C_L`.
    have h1 : gaussDdim (t - s) (0 : Point n) * P ≤ gaussDdim (epsSeq m) (0 : Point n) * P :=
      mul_le_mul_of_nonneg_right hpeakle hP
    calc (gaussDdim (t - s) (0 : Point n) * P) * C_L
        ≤ (gaussDdim (epsSeq m) (0 : Point n) * P) * C_L :=
          mul_le_mul_of_nonneg_right h1 hCL
      _ = gaussDdim (epsSeq m) (0 : Point n) * P * C_L := by ring
  exact hzmass_capped_window_closed t m M BL BF
    (fun s => gaussDdim (t - s) (0 : Point n) * P) (fun _ => C_L)
    hMnn hepspos hint hBFpeak hBLnn hBLgauss hPpknn hPCbound

/-! ###############################################################################
    ### §4 — NON-VACUITY.
    ############################################################################### -/

/-- **Non-vacuity of the capped-window closure.**  The genuinely-chosen antecedents are jointly
    inhabited at the zero envelopes `BL ≡ 0`, `BF ≡ 0`, `Ppk ≡ 0`, `CB ≡ 0`, `M := 0`: the product is
    integrable (`0`), `BF ≤ 0`, `0 ≤ BL`, `BL ≤ 0·gaussDdim = 0`, `0 ≤ Ppk`, and `Ppk·CB = 0 ≤ 0 = M`,
    yielding `∫z 0 = 0 ≤ (0·t)·(t−s)⁻¹`.  The window fact `hepspos` is a property of `(t,m)` (carried,
    not asserted false).  No J4-548/847-style unsatisfiable antecedent. -/
theorem hzmass_capped_window_nonvacuous {n : ℕ} (t : ℝ) (m : ℕ) (hepspos : 0 < t - epsSeq m) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ _z : Point n, (0 : ℝ) * 0) ≤ ((0 : ℝ) * t) * (t - s)⁻¹ := by
  have hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z : Point n =>
        (fun _ _ => (0 : ℝ)) s z * (fun _ _ => (0 : ℝ)) s z) volume := by
    refine ae_of_all _ (fun s _ => ?_)
    simp only [mul_zero]
    exact integrable_zero _ _ _
  have hBFpeak : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, (fun _ _ => (0 : ℝ)) s z ≤ (fun _ => (0 : ℝ)) s :=
    ae_of_all _ (fun s _ z => le_refl 0)
  have hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, 0 ≤ (fun _ _ => (0 : ℝ)) s z :=
    ae_of_all _ (fun s _ z => le_refl 0)
  have hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, (fun _ _ => (0 : ℝ)) s z
        ≤ (fun _ => (0 : ℝ)) s * gaussDdim (2 * s) z := by
    refine ae_of_all _ (fun s _ z => ?_)
    simp
  have hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      0 ≤ (fun _ => (0 : ℝ)) s :=
    ae_of_all _ (fun s _ => le_refl 0)
  have hPCbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      (fun _ => (0 : ℝ)) s * (fun _ => (0 : ℝ)) s ≤ (0 : ℝ) :=
    ae_of_all _ (fun s _ => by simp)
  exact hzmass_capped_window_closed (n := n) t m 0
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    (le_refl 0) hepspos hint hBFpeak hBLnn hBLgauss hPpknn hPCbound

end QIQTH.HZMassCappedWindowClosed

section AxiomChecks
open QIQTH.HZMassCappedWindowClosed
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms hpow_capped
#print axioms hzmass_capped_window_closed
#print axioms gaussDdimPeak_antitone_width
#print axioms hzmass_capped_window_gaussPeak
#print axioms hzmass_capped_window_nonvacuous
end AxiomChecks
