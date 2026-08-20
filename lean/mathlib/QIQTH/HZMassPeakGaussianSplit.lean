/-
  HZMassPeakGaussianSplit — J4-881: the STRATEGIC REDIRECT of the deep `hzmass` `z`-mass wall of
  `MixedDirectionsFieldHessianEnvelope`, answering the question "can the J4-879/880 near-isometry
  CANCELLATION technique discharge `hzmass`?".

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick REDUCES the deep §C `hzmass`
  `z`-mass wall (`∫z BL·BF ≤ C·(t−s)⁻¹`) to a SPLIT envelope hypothesis that is compatible with — indeed
  DEMANDED by — the J4-868 no-go, and records the precise finding that the J4-879/880 near-isometry
  cancellation route is inapplicable to `hzmass`.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## FINDING 1 — the J4-879/880 near-isometry CANCELLATION route is INAPPLICABLE to `hzmass`.

  The J4-879/880 near carry controls a WEIGHTED DIFFERENCE of two near-equal Gaussians,
      `∫ s in (t−ε)..t, ∫_{ball 0 R} ‖v‖^k · |G_τ(T_{x₀} v) − G_τ(v)| dv ds`,
  integrated over a SMALL FIELD-chart ball `ball 0 R` (near-diagonal) and a TIME SLIVER `(t−ε, t]`.  Its
  superpolynomial gain `ε^{(k+3)/2−p}` comes from the near-isometry CANCELLATION `G_τ(T_{x₀}v) ≈ G_τ(v)`,
  and the enabling reversal link (`gaussDdim_reversal_link`, J4-880) is a GERM `=ᶠ[𝓝 x₀]` — valid only for
  `v` near the diagonal.

  `hzmass` is a STRUCTURALLY DIFFERENT object:
    • its integrand `BL s z · BF s z` is a PRODUCT of nonnegative MAGNITUDES (`BF = ⨆ₓ ‖fderiv …‖ ≥ 0`,
      `BL ≥ |leviSeries …| ≥ 0`) — NOT a difference of two near-equal Gaussians, so there is no pair to
      subtract and no cancellation to exploit;
    • it integrates over the FULL BASE variable `z` (supported on the whole compact `K`, J4-867), at
      FIXED time `s` — NOT over a small near-diagonal field ball, and with NO time sliver;
    • its target `C·(t−s)⁻¹` is a TIME singularity, needing `BF`'s peak absorbed by a BASE-`z` mass —
      decay in the BASE variable, whereas the cancellation supplies decay only in the FIELD chart
      coordinate.
  A difference-cancellation bound can never upper-bound a magnitude-mass integral, the germ `=ᶠ[𝓝 x₀]`
  can never control a global base integral over `K`, and `T_{x₀}` acts on the field chart at fixed base
  `x₀` — it says nothing about base-`z` mass.  So the cancellation route is GENUINELY DISTINCT from
  J4-868's naive-peak route (different mechanism), and it is ALSO inapplicable, for INDEPENDENT reasons.
  This is NOT a disguised re-run of J4-868's no-go.

  ## FINDING 2 — the PRODUCTIVE route: keep `BF`'s peak, put the Gaussian on `BL`.

  J4-868 proved `BF` has NO `z`-decay: its only `z`-uniform bound is the PEAK `gaussDdim (t−s) 0` (a
  `z`-CONSTANT).  J4-867 reduced `hzmass` to a POINTWISE Gaussian-in-`z` envelope on the PRODUCT
  `BL·BF ≤ C·(t−s)⁻¹·gaussDdim (t−s) z`.  The ONLY way to reconcile these is: the `z`-Gaussian is carried
  ENTIRELY by the LEVI BASE factor `BL` (`|leviSeries (heatOp …) s z 0| ≤ BL s z`, a genuine heat-parametrix
  off-diagonal base density), while `BF` contributes ONLY its `z`-uniform PEAK.

  `hzmass_of_peak_BF_gaussian_BL` PROVES exactly this reduction: from
    • `hBFpeak` — `BF s z ≤ Ppk s`      (`z`-UNIFORM peak; the ONLY bound J4-868 allows for `BF`),
    • `hBLgauss` — `BL s z ≤ CB s · gaussDdim (t−s) z`   (BASE-Gaussian envelope on the Levi factor),
    • `hpow`    — `Ppk s · CB s ≤ C · (t−s)⁻¹`           (the matched time-power bookkeeping),
    • nonnegativity + product integrability,
  the product bound `BL·BF ≤ C·(t−s)⁻¹·gaussDdim (t−s) z` follows pointwise, and the J4-867 mass-one
  reduction (`gaussDdim` integrates to `1`) closes `hzmass`.  This isolates the SOLE genuine remaining
  wall as a BASE-Gaussian envelope for the LEVI factor `BL` (a standard parametrix estimate), NOT a
  field-Hessian `z`-decay (impossible, J4-868) and NOT a near-isometry cancellation (inapplicable,
  FINDING 1).

  ## WHAT LANDS (ns `QIQTH.HZMassPeakGaussianSplit`).
    • `hzmass_of_peak_BF_gaussian_BL` — ★★★ the split reduction of `hzmass` to {peak `BF`, Gaussian `BL`,
      matched power}, via the J4-867 mass-one reduction.
    • `hzmass_peak_gaussian_split_nonvacuous` — the split antecedents are jointly inhabited (zero
      envelopes), no J4-548/847-style unsatisfiable hypothesis.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HZMassIntegrabilityAttempt

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.FlatHeatEquation
open QIQTH.ChartJetXUniformBound
open scoped Topology BigOperators

namespace QIQTH.HZMassPeakGaussianSplit

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### THE PEAK-`BF` / GAUSSIAN-`BL` SPLIT REDUCTION of `hzmass`.
    ############################################################################### -/

/-- **★★★ `hzmass_of_peak_BF_gaussian_BL`.**  THE STRATEGIC REDIRECT of `hzmass`.  The deep `z`-mass
    bound `∫z BL·BF ≤ C·(t−s)⁻¹` follows from a SPLIT envelope in which the `z`-Gaussian is carried
    ENTIRELY by the LEVI base factor `BL`, and the field-Hessian factor `BF` contributes ONLY its
    `z`-UNIFORM PEAK — the ONLY bound J4-868 permits for `BF`.  Precisely, given, a.e. `s` in the
    window:
      • `hBFpeak`  — `BF s z ≤ Ppk s` for all `z`  (the `z`-CONSTANT peak from J4-868);
      • `hBLnn`    — `0 ≤ BL s z` for all `z`;
      • `hBLgauss` — `BL s z ≤ CB s · gaussDdim (t−s) z` for all `z`  (BASE-Gaussian envelope on the
                     Levi factor — the honest remaining parametrix estimate);
      • `hPpknn`   — `0 ≤ Ppk s`;
      • `hpow`     — `Ppk s · CB s ≤ C · (t−s)⁻¹`  (matched time-power bookkeeping),
      • plus window positivity `hpos` and product integrability `hint`,
    the pointwise product bound `BL s z · BF s z ≤ C·(t−s)⁻¹·gaussDdim (t−s) z` holds (multiply
    `BF ≤ Ppk` by `BL ≥ 0`, then `BL ≤ CB·gaussDdim` by `Ppk ≥ 0`, then `Ppk·CB ≤ C(t−s)⁻¹` by
    `gaussDdim ≥ 0`), and `HZMassIntegrabilityAttempt.hzmass_of_gaussian_product_envelope` (mass-one)
    closes `hzmass`.  This is the productive route: NOT a field-Hessian `z`-decay (impossible, J4-868)
    and NOT a near-isometry cancellation (inapplicable, FINDING 1).  NOT `a₁ = R/6`. -/
theorem hzmass_of_peak_BF_gaussian_BL
    (t : ℝ) (m : ℕ) (C : ℝ) (BL BF : ℝ → Point n → ℝ) (Ppk CB : ℝ → ℝ)
    (hCnn : 0 ≤ C)
    (hpos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < t - s)
    (hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (hBFpeak : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BF s z ≤ Ppk s)
    (hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, 0 ≤ BL s z)
    (hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BL s z ≤ CB s * gaussDdim (t - s) z)
    (hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        0 ≤ Ppk s)
    (hpow : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Ppk s * CB s ≤ C * (t - s)⁻¹) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, BL s z * BF s z) ≤ C * (t - s)⁻¹ := by
  -- assemble the J4-867 pointwise Gaussian PRODUCT envelope `henv` from the split.
  have henv : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, BL s z * BF s z ≤ C * (t - s)⁻¹ * gaussDdim (t - s) z := by
    filter_upwards [hBFpeak, hBLnn, hBLgauss, hPpknn, hpow]
      with s hpk hbn hbg hpn hpw hs
    intro z
    have hpks := hpk hs z
    have hbns := hbn hs z
    have hbgs := hbg hs z
    have hpns := hpn hs
    have hpws := hpw hs
    have hgnn : (0 : ℝ) ≤ gaussDdim (t - s) z := gaussDdim_nonneg' (t - s) z
    -- `BL·BF ≤ BL·Ppk` (BF ≤ Ppk, BL ≥ 0).
    have step1 : BL s z * BF s z ≤ BL s z * Ppk s :=
      mul_le_mul_of_nonneg_left hpks hbns
    -- `BL·Ppk ≤ (CB·gaussDdim)·Ppk` (BL ≤ CB·gaussDdim, Ppk ≥ 0).
    have step2 : BL s z * Ppk s ≤ (CB s * gaussDdim (t - s) z) * Ppk s :=
      mul_le_mul_of_nonneg_right hbgs hpns
    -- `(CB·gaussDdim)·Ppk = (Ppk·CB)·gaussDdim ≤ (C·(t−s)⁻¹)·gaussDdim` (matched power, gaussDdim ≥ 0).
    have step3 : (CB s * gaussDdim (t - s) z) * Ppk s
        ≤ C * (t - s)⁻¹ * gaussDdim (t - s) z := by
      have hrw : (CB s * gaussDdim (t - s) z) * Ppk s
          = (Ppk s * CB s) * gaussDdim (t - s) z := by ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_right hpws hgnn
    calc BL s z * BF s z
        ≤ BL s z * Ppk s := step1
      _ ≤ (CB s * gaussDdim (t - s) z) * Ppk s := step2
      _ ≤ C * (t - s)⁻¹ * gaussDdim (t - s) z := step3
  exact QIQTH.HZMassIntegrabilityAttempt.hzmass_of_gaussian_product_envelope
    t m C BL BF hCnn hpos hint henv

/-! ###############################################################################
    ### NON-VACUITY.
    ############################################################################### -/

/-- **Non-vacuity of the split reduction.**  The GENUINELY-CHOSEN antecedents are jointly inhabited at
    the zero envelopes `BL ≡ 0`, `BF ≡ 0`, `Ppk ≡ 0`, `CB ≡ 0`: the product is integrable (`0`),
    `BF ≤ 0`, `0 ≤ BL`, `BL ≤ 0·gaussDdim = 0`, `0 ≤ Ppk`, and `Ppk·CB = 0 ≤ C·(t−s)⁻¹` on the positive
    window (`C ≥ 0`, `(t−s)⁻¹ > 0`), yielding `∫z 0 = 0 ≤ C·(t−s)⁻¹`.  Window positivity `hpos` is a
    property of `(t,m)` (carried, not asserted false).  No J4-548/847-style unsatisfiable antecedent. -/
theorem hzmass_peak_gaussian_split_nonvacuous {n : ℕ} (t : ℝ) (m : ℕ) (C : ℝ) (hCnn : 0 ≤ C)
    (hpos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < t - s) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ _z : Point n, (0 : ℝ) * 0) ≤ C * (t - s)⁻¹ := by
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
        ≤ (fun _ => (0 : ℝ)) s * gaussDdim (t - s) z := by
    refine ae_of_all _ (fun s _ z => ?_)
    simp
  have hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      0 ≤ (fun _ => (0 : ℝ)) s :=
    ae_of_all _ (fun s _ => le_refl 0)
  have hpow : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      (fun _ => (0 : ℝ)) s * (fun _ => (0 : ℝ)) s ≤ C * (t - s)⁻¹ := by
    filter_upwards [hpos] with s hposs hs
    have hts : 0 < t - s := hposs hs
    have : (0 : ℝ) ≤ C * (t - s)⁻¹ := mul_nonneg hCnn (le_of_lt (inv_pos.mpr hts))
    simpa using this
  have h := hzmass_of_peak_BF_gaussian_BL (n := n) t m C
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    hCnn hpos hint hBFpeak hBLnn hBLgauss hPpknn hpow
  filter_upwards [h] with s hs hsU
  exact hs hsU

end QIQTH.HZMassPeakGaussianSplit

section AxiomChecks
open QIQTH.HZMassPeakGaussianSplit
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms hzmass_of_peak_BF_gaussian_BL
#print axioms hzmass_peak_gaussian_split_nonvacuous
end AxiomChecks
