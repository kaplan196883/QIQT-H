/-
  CurvedA1ClassBMeas — J4-559.  Close the thinnest genuinely-closable MEASURABILITY census member of
  the fully-wired curved a₁ two-jet capstone `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`
  at the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges ONE mechanical MEASURABILITY census binder —
  the frozen/moving witness-slice AEStronglyMeasurability `hWmeas` — for `g^K` from a banked,
  geometry-only supplier.  It does NOT make `a₁ = R/6` unconditional: the geometric residuals
  `hsrc`/`hOffCollarTail`, the convergence trio, and the rest of the measurability/gate census
  (`hmeasLo`/`hmeasHi`/`hmeas2Lo`, the W2 diff-under-∫ family `hFmeas`/`hFint`/`hF'meas`, Section-G
  `hMeasFII`/`hFmeas_d`, …) all remain owed.

  ## What is closed

  `curved_hWmeas_at_gate` — the EXACT shape of the capstone binder
    `hWmeas : ∀ τ, AEStronglyMeasurable (z ↦ vanVleckGatedWitness g^K … (constGate … c) a b τ 0 z) volume`
  produced, for `g^K = curvedRNCMetric κ` (`κ < 0`), by the banked curved-witness measurability supplier
  `CurvedRNCWitnessMeas.curvedRNC_hWmeas` (J4-527/528), which routes the curved smoothness bundle
  {`curvedRNCMetric_contDiff`, `curvedRNCInv_contDiff`, `curvedRNCMetric_hgpos`} through the generic
  banked reduction `WitnessMeasDeriv.vanVleckGatedWitness_slice_aestronglyMeasurable`.  The two strictly
  lighter, CURVATURE-INDEPENDENT carries {`hSm` (gate-set preimage measurable), `hVmap` (base-chart
  pullback z-ae-measurability)} are carried honestly — they are geometric bookkeeping slots, not the
  `a₁` coefficient and not gate-smallness.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  The member is a genuine `AEStronglyMeasurable` fact about the curved witness slice, discharged from a
  banked supplier — NOT the capstone's conclusion, and NOT vacuous.  It holds at the genuinely-curved
  `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`, `curvedRNCMetric_ricci_trace_diag_ne`); the two carries
  {`hSm`, `hVmap`} are satisfiable for the geometric const-radius gate and its base chart (see the
  satisfiability gate of `CurvedRNCWitnessMeas`).  It does not touch, and is unaffected by, the `R/6`
  coefficient.  No `sorry`, no new axioms, no `:= True`, no hypothesis = conclusion, no existing file
  edited.  NOT `a₁ = R/6`. -/
import QIQTH.CurvedRNCWitnessMeas

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.GateChartMeasurability QIQTH.WitnessMeasDeriv
open QIQTH.CurvedRNCWitnessMeas
open scoped ContDiff

namespace QIQTH.CurvedA1ClassBMeas

variable {n : ℕ}

/-- **★ J4-559 — `curved_hWmeas_at_gate`.**  The MEASURABILITY census binder `hWmeas` of
    `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the genuinely-curved witness
    `g^K = curvedRNCMetric κ` (`κ < 0`): the frozen/moving witness slice
    `z ↦ vanVleckGatedWitness g^K … (constGate … c) a b τ 0 z` is `AEStronglyMeasurable` for every `τ`.
    Discharged from the banked curved-witness measurability supplier
    `CurvedRNCWitnessMeas.curvedRNC_hWmeas`, which feeds the curved smoothness bundle through the
    generic banked reduction `WitnessMeasDeriv.vanVleckGatedWitness_slice_aestronglyMeasurable`.  The two
    strictly lighter curvature-independent carries {`hSm`, `hVmap`} are carried honestly.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hWmeas_at_gate (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b : ℝ)
    (hSm : MeasurableSet {z : Point n |
      (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z})
    (hVmap : ∀ p : Point n, AEStronglyMeasurable
      (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z p)
      (volume : Measure (Point n))) :
    ∀ (τ : ℝ), AEStronglyMeasurable
      (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z)
      (volume : Measure (Point n)) :=
  curvedRNC_hWmeas κ hκ hChr hK c a b hSm hVmap

end QIQTH.CurvedA1ClassBMeas

section AxiomChecks
open QIQTH.CurvedA1ClassBMeas
#print axioms curved_hWmeas_at_gate
end AxiomChecks
