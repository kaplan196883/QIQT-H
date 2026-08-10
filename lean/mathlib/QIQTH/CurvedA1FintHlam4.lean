/-
  CurvedA1FintHlam4 — J4-574: DISCHARGING the `hlam4 : 4 ≤ lam` width-compatibility scalar
  owed by J4-572 (`CurvedA1FintHFarSource`), via a WIDENED gate variant `curvedGate4`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This file removes the ONE remaining SCALAR residual
  `hlam4 : 4 ≤ (curvedGate κ hChr hK).lam` owed by the far-field annulus source
  `CurvedA1FintHFarSource.curved_hFint_hFar_at_gate` (which widens the banked width-`4τ` star bound
  up to the gate width `lam·τ`, needing `4 ≤ lam`).

  ── THE VERDICT (route b — `lam` is a FREE existential choice).  The gate `lam` is pinned by
  `InverseChartNormalJets.chart_width_gate` to `(η, lam) = (1−c, 1/c + 1)` from the near-isometry
  coarse constant `c > 0`, and is constrained ONLY by `1 < lam` and `1/lam < 1 − η`.  BOTH constraints
  are RELAXED by enlarging `lam` (`1/lam` shrinks).  So `lam` may be re-chosen ARBITRARILY LARGE — in
  particular `≥ 4`.  `4 ≤ (curvedGate …).lam` is NOT true for the concrete `of_geometry` gate (`lam` can
  be `< 4` when `c` is large), so shipping it for `curvedGate` would be a FALSE bound; but the WIDENED
  gate `curvedGate4` with `lam := max 4 (curvedGate …).lam` is a fully admissible `FixedFlowGateData`
  (all constraints survive, `r, a, b, η` UNCHANGED) whose `lam ≥ 4` is GENUINELY TRUE.

  ── WHAT IS PROVED (axiom-free, no `sorry`).
    •  `curvedGate4` — the widened gate variant (only `lam` enlarged to `max 4 (curvedGate …).lam`;
       `r, a, b, η` and the proved width gate are inherited VERBATIM from `curvedGate`).
    •  `curvedGate4_r`, `curvedGate4_lam` — the definitional field identities (`.r` unchanged;
       `.lam = max 4 (curvedGate …).lam`).
    •  `curved_hlam4_at_gate4 : 4 ≤ (curvedGate4 κ hChr hK).lam` — THE DISCHARGE (genuinely true).
    •  `curved_hFint_hFar_general` — the far-field annulus envelope over an ARBITRARY width `(r, lam)`
       with `4 ≤ lam` (the general form of J4-572's `curved_hFint_hFar_at_gate`, verbatim proof).
    •  `curved_hFint_hFar_at_gate4` — J4-572's far-field envelope over `curvedGate4`, with the `hlam4`
       hypothesis REMOVED (discharged internally by `curved_hlam4_at_gate4`).
    •  `curved_hFint_hlam4_curved_satisfiable` — the CURVED (not-secretly-flat) gate.

  ── WHAT REMAINS.  Discharging `hlam4` does NOT make `a₁ = R/6` unconditional.  To thread the widened
  gate all the way through the mainline `hcrude` census, `curved_hFint_hcrude_at_gate` (and the far
  source above it) would swap `curvedGate → curvedGate4` — a MECHANICAL substitution, since `r, a, b, η`
  are unchanged and `lam` only enlarges (`poly_absorb`, `hgate`, the ordered radii all survive).  The
  `hdata`-family, `hFirstEnv`, `hsrc`, `hOffCollarTail`, the convergence trio, and `hInnerCont` all
  remain owed.  NOT `a₁ = R/6`.
-/
import QIQTH.CurvedA1FintHFarSource

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.InverseChartNormalJets QIQTH.WideWitnessAmplitude
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCHeatOpDom2 QIQTH.WidthAdapters QIQTH.CurvedA1FintAdomSource
open QIQTH.CConvV2WitnessStar QIQTH.CurvedA1FintHcrudeSource QIQTH.CurvedA1FintHFarSource
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1FintHlam4

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### (A) — THE WIDENED GATE VARIANT `curvedGate4` (`lam ≥ 4`, all else inherited).
    ############################################################################### -/

/-- **★★★ J4-574 — `curvedGate4`.**  The width-widened gate variant of `curvedGate`.  Inherits the
    ordered radial-cutoff radii `0 < a < b < r`, the tolerance `η < 1`, and the PROVED inverse-chart
    width gate VERBATIM from `curvedGate κ hChr hKset`; the ONLY change is the dilation
    `lam := max 4 (curvedGate …).lam`, which stays admissible because enlarging `lam` only RELAXES the
    two `FixedFlowGateData` width constraints `1 < lam`, `1/lam < 1 − η`.  So `curvedGate4` is a genuine
    `FixedFlowGateData` with `4 ≤ lam`.  NOT `a₁ = R/6`. -/
noncomputable def curvedGate4 (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) :
    FixedFlowGateData (curvedRNCMetric κ) (curvedRNCInv κ) hChr hKset :=
  let D := curvedGate κ hChr hKset
  { a := D.a
    b := D.b
    r := D.r
    eta := D.eta
    lam := max 4 D.lam
    ha := D.ha
    hab := D.hab
    hbr := D.hbr
    heta := D.heta
    hlam := lt_of_lt_of_le (by norm_num) (le_max_left 4 D.lam)
    hgap := by
      have h0 : 0 < D.lam := lt_trans zero_lt_one D.hlam
      have hle : (1 : ℝ) / max 4 D.lam ≤ 1 / D.lam :=
        one_div_le_one_div_of_le h0 (le_max_right 4 D.lam)
      linarith [D.hgap]
    hgate := D.hgate }

/-- `curvedGate4` keeps the gate radius `r` of `curvedGate` unchanged (definitional). -/
@[simp] theorem curvedGate4_r (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) :
    (curvedGate4 κ hChr hKset).r = (curvedGate κ hChr hKset).r := rfl

/-- `curvedGate4`'s dilation is `max 4 (curvedGate …).lam` (definitional). -/
@[simp] theorem curvedGate4_lam (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) :
    (curvedGate4 κ hChr hKset).lam = max 4 (curvedGate κ hChr hKset).lam := rfl

/-- **★★★ J4-574 — `curved_hlam4_at_gate4`.**  THE DISCHARGE of the J4-572 width-compatibility scalar
    `hlam4`: the widened gate `curvedGate4` has dilation `≥ 4` GENUINELY (`lam := max 4 …`).  NOT
    `a₁ = R/6`. -/
theorem curved_hlam4_at_gate4 (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) :
    4 ≤ (curvedGate4 κ hChr hKset).lam := by
  rw [curvedGate4_lam]; exact le_max_left 4 _

/-! ###############################################################################
    ### (B) — THE FAR-FIELD ANNULUS ENVELOPE over an ARBITRARY width `(r, lam)`, `4 ≤ lam`.
    ############################################################################### -/

/-- **★★★ J4-574 — `curved_hFint_hFar_general`.**  The far-field annulus first-derivative envelope of
    J4-572 (`CurvedA1FintHFarSource.curved_hFint_hFar_at_gate`) generalised to an ARBITRARY gate-width
    pair `(r, lam)` with `4 ≤ lam` (verbatim proof: banked star-wide width-`4τ` bound
    `witnessFieldDeriv_starWide_onGate` + the free pure-Gaussian width upgrade
    `gaussDdim_le_gaussDdim_chart`, `4 ≤ lam`).  This is the general form that `curvedGate4` instantiates
    with `hlam4` DISCHARGED.  ⚠ The `(√τ)⁻¹` prefactor is kept VERBATIM.  NOT `a₁ = R/6`. -/
theorem curved_hFint_hFar_general (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T L Ba Bd : ℝ)
    (r lam : ℝ) (hlam4 : 4 ≤ lam)
    (hL : 0 ≤ L) (hBa0 : 0 ≤ Ba) (hBd0 : 0 ≤ Bd)
    (hSopen : ∀ z ∈ K, IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z))
    (hgate0 : ∀ z ∈ K, (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z)
    (hdata : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
      ∃ Pval : Fin n → ℝ,
        (∀ k, HasDerivAt
          (fun r : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
              (Function.update (0 : Point n) i r) k) (Pval k) ((0 : Point n) i))
        ∧ (∀ k, |Pval k| ≤ L)
        ∧ PdiffAt (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
        ∧ |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba
        ∧ |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd
        ∧ (1 / 2 : ℝ) * rncRadialSq z
            ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)) :
    ∃ Cfar : ℝ, 0 ≤ Cfar ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n, z ∈ K →
        ¬ (‖z‖ < r) →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Cfar * (Real.sqrt τ)⁻¹ * gaussDdim (lam * τ) z := by
  have hlam0 : 0 < lam := by linarith
  -- the `s`-uniform star-wide constant (width `4τ`, prefactor `τ^{−1/2}`).
  set Cstar : ℝ :=
    Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba + (2 : ℝ) ^ n * Bd * Real.sqrt T
    with hCstardef
  have hCstar_nn : 0 ≤ Cstar := by
    have h0 : 0 ≤ Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba :=
      mul_nonneg (mul_nonneg
        (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) (by norm_num)) (by positivity)) hBa0
    have h1 : 0 ≤ (2 : ℝ) ^ n * Bd * Real.sqrt T :=
      mul_nonneg (mul_nonneg (by positivity) hBd0) (Real.sqrt_nonneg _)
    rw [hCstardef]; linarith
  -- the free pure-Gaussian width-upgrade normalizer `√(lam/4)ⁿ`.
  set Cw : ℝ := Real.sqrt (lam / 4) ^ n with hCwdef
  have hCw_nn : 0 ≤ Cw := by rw [hCwdef]; positivity
  refine ⟨Cstar * Cw, mul_nonneg hCstar_nn hCw_nn, ?_⟩
  intro i τ hτ hτT z hzK _hann
  -- the per-point banked star-wide data on the annulus (field point `0 ∈ gate`, global near-isometry).
  obtain ⟨Pval, hJetV, hJac, hAmp1, hBa, hBd, hmin⟩ := hdata i τ hτ hτT z hzK
  -- the banked `(⋆)`-WIDE on-gate first-derivative bound at width `4τ`.
  have hstar := witnessFieldDeriv_starWide_onGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i T τ hτ hτT z hzK
    (hSopen z hzK) (0 : Point n) (hgate0 z hzK) Pval hJetV hAmp1 L Ba Bd hL hJac hBa hBd hmin
  -- convert the rpow prefactor `τ^{−1/2}` into `(√τ)⁻¹`, folding `Cstar`.
  rw [← hCstardef, ← sqrtInv_eq_rpow τ hτ.le] at hstar
  -- the free width upgrade `gaussDdim (4τ) z ≤ Cw · gaussDdim (lam·τ) z`  (`4 ≤ lam`).
  have hnn : 0 ≤ rncRadialSq z := rncRadialSq_nonneg z
  have hwid : gaussDdim (4 * τ) z ≤ Cw * gaussDdim (lam * τ) z := by
    have h := gaussDdim_le_gaussDdim_chart (n := n) (c := 4) (d := lam)
      (by norm_num) hlam0 hτ (v := z) (w := z)
      (by have := mul_le_mul_of_nonneg_right hlam4 hnn; linarith)
    simpa only [hCwdef] using h
  -- combine: keep the `(√τ)⁻¹` prefactor verbatim, widen the Gaussian.
  have hst : 0 ≤ (Real.sqrt τ)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg τ)
  have hCst_st : 0 ≤ Cstar * (Real.sqrt τ)⁻¹ := mul_nonneg hCstar_nn hst
  calc |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
      ≤ Cstar * (Real.sqrt τ)⁻¹ * gaussDdim (4 * τ) z := hstar
    _ ≤ Cstar * (Real.sqrt τ)⁻¹ * (Cw * gaussDdim (lam * τ) z) :=
        mul_le_mul_of_nonneg_left hwid hCst_st
    _ = Cstar * Cw * (Real.sqrt τ)⁻¹ * gaussDdim (lam * τ) z := by ring

/-! ###############################################################################
    ### (C) — THE J4-572 FAR-FIELD ENVELOPE over `curvedGate4`, `hlam4` REMOVED.
    ############################################################################### -/

/-- **★★★ J4-574 — `curved_hFint_hFar_at_gate4`.**  J4-572's far-field annulus first-derivative envelope
    `hFar` at the WIDENED gate `curvedGate4`, with the `hlam4 : 4 ≤ lam` hypothesis DISCHARGED internally
    by `curved_hlam4_at_gate4` — the concrete demonstration that widening the gate REMOVES the last
    scalar residual owed by `curved_hFint_hFar_at_gate`.  NOT `a₁ = R/6`. -/
theorem curved_hFint_hFar_at_gate4 (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T L Ba Bd : ℝ)
    (hL : 0 ≤ L) (hBa0 : 0 ≤ Ba) (hBd0 : 0 ≤ Bd)
    (hSopen : ∀ z ∈ K, IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z))
    (hgate0 : ∀ z ∈ K, (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z)
    (hdata : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
      ∃ Pval : Fin n → ℝ,
        (∀ k, HasDerivAt
          (fun r : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
              (Function.update (0 : Point n) i r) k) (Pval k) ((0 : Point n) i))
        ∧ (∀ k, |Pval k| ≤ L)
        ∧ PdiffAt (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
        ∧ |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba
        ∧ |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd
        ∧ (1 / 2 : ℝ) * rncRadialSq z
            ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)) :
    ∃ Cfar : ℝ, 0 ≤ Cfar ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n, z ∈ K →
        ¬ (‖z‖ < (curvedGate4 κ hChr hK).r) →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Cfar * (Real.sqrt τ)⁻¹ * gaussDdim ((curvedGate4 κ hChr hK).lam * τ) z :=
  curved_hFint_hFar_general κ hChr hK a b c T L Ba Bd
    (curvedGate4 κ hChr hK).r (curvedGate4 κ hChr hK).lam
    (curved_hlam4_at_gate4 κ hChr hK) hL hBa0 hBd0 hSopen hgate0 hdata

/-! ###############################################################################
    ### (D) — the CURVED (not-secretly-flat) satisfiability GATE.
    ############################################################################### -/

/-- **★ J4-574 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the discharged `hlam4`
    (via `curvedGate4`) is landed at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.  The
    widened dilation `lam ≥ 4` is genuinely TRUE (`max 4 …`), NOT a false bound on the concrete gate.
    NOT `a₁ = R/6`. -/
theorem curved_hFint_hlam4_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintHlam4

section AxiomChecks
open QIQTH.CurvedA1FintHlam4
#print axioms curvedGate4
#print axioms curved_hlam4_at_gate4
#print axioms curved_hFint_hFar_general
#print axioms curved_hFint_hFar_at_gate4
#print axioms curved_hFint_hlam4_curved_satisfiable
end AxiomChecks
