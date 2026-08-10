/-
  CurvedRNCWitnessMeas — J4-527: the type-(iii) measurability binders `hWmeas` / `hWslice` of the
  curved-signature capstone, INSTANTIATED for the genuinely curved witness `g^K = curvedRNCMetric K`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about the coefficient.  The two
  binders discharged here —

      hWmeas / hWslice : ∀ τ, AEStronglyMeasurable
          (fun z => vanVleckGatedWitness g gi hChr hK (constGate …) a b τ 0 z) volume

  — are CURVATURE-INDEPENDENT bookkeeping.  Closing them does NOT derive `a₁`.  The remaining wall to
  a non-vacuous derived curved `a₁` is the curved heat-kernel Gaussian dominations (heatOp / Levi),
  which are entirely untouched here.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`), for `g := curvedRNCMetric K`, `gi := curvedRNCInv K`,
     `K < 0` (`Ric(0) = (n−1)Kδ ≠ 0`, genuinely curved — NOT secretly flat):

    • `curvedRNC_hIn_from_geometry` — ★ the inner order-1 parametrix slice
        `z ↦ globalCutoffParametrixWitnessN 1 (vanVleck g^K) (transportCoeff …) a b (uniformInverseChart …) τ 0 z`
        is `AEStronglyMeasurable`, discharged END-TO-END from the curved smoothness bundle
        {`curvedRNCMetric_contDiff`, `curvedRNCInv_contDiff`, `curvedRNCMetric_hgpos`}.  The parametrix
        chain `hu → hw → parametrix → continuity` is closed at the `∞` level (never `ω`) via
        `HuInftyRebase.vanVleck_witnessInner_continuous_ofGeom`, then composed with the base-chart
        pullback (`Continuous.comp_aestronglyMeasurable`).  The ONLY residual carry is `hVmap`
        (base-chart pullback z-ae-measurability), a curvature-independent geometric bookkeeping slot.

    • `curvedRNC_hWmeas` — ★★ the EXACT `hWmeas` binder of
        `A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary` for `g^K`, obtained by
        feeding `curvedRNC_hIn_from_geometry` and `compactGate_measurableSet hK` (from bound
        compactness) through the generic banked reduction
        `WitnessMeasDeriv.vanVleckGatedWitness_slice_aestronglyMeasurable`.  Reduced to the two strictly
        lighter curvature-independent carries {`hSm` (gate-set preimage measurable), `hVmap`}.

    • `curvedRNC_hWslice` — the `hWslice` binder, identical in statement to `hWmeas`; the same
        discharge serves both.  NOT `a₁ = R/6`.

  ── SATISFIABILITY GATE.  The hypotheses are jointly satisfiable at a GENUINELY CURVED witness:
     take any `K < 0`, any compact `Kset ∋ 0`, any window `a < b`, radius `c`.  Then `g^K` has
     `Ric(0) = (n−1)Kδ ≠ 0` (`CurvedRNCGaussWitness.curvedRNCMetric_ricci_trace_diag_ne`), so nothing
     collapses to flat; `curvedRNCMetric_hgpos K (le_of_lt hK)` supplies `det g^K > 0` (the curved
     det-positivity, where `K ≤ 0` posdef genuinely enters); `hSm` / `hVmap` hold for the geometric
     const-radius gate and its base chart.  None of the discharged/carried facts is vacuous, and none
     is the `a₁` conclusion.
-/
import Mathlib
import QIQTH.CurvedRNCPosDef
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.A1R6CoreAtGate
import QIQTH.DataPileWitnessAudit
import QIQTH.GateChartMeasurability
import QIQTH.HuInftyRebase

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.GateChartMeasurability QIQTH.WitnessMeasDeriv QIQTH.HuInftyRebase
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.HeatParametrixAnsatz
open scoped BigOperators

namespace QIQTH.CurvedRNCWitnessMeas

variable {n : ℕ}

/-- **★ `curvedRNC_hIn_from_geometry`.**  For the genuinely curved witness `g^K = curvedRNCMetric K`
    (`K < 0`), the inner order-1 parametrix slice
      `z ↦ globalCutoffParametrixWitnessN 1 (vanVleck g^K) (transportCoeff …) a b (uniformInverseChart …) τ 0 z`
    is `AEStronglyMeasurable`, discharged end-to-end from the curved smoothness bundle.  The parametrix
    continuity is closed at the `∞` level (never `ω`) by
    `HuInftyRebase.vanVleck_witnessInner_continuous_ofGeom`, fed the curved
    {`curvedRNCMetric_contDiff`, `curvedRNCInv_contDiff`, `curvedRNCMetric_hgpos`}; the slice is that
    continuous spatial function composed with the base-chart pullback, so
    `Continuous.comp_aestronglyMeasurable` closes it.  The only residual carry is `hVmap` (base-chart
    pullback z-ae-measurability), curvature-independent.  NOT `a₁ = R/6`. -/
theorem curvedRNC_hIn_from_geometry (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (a b : ℝ)
    (hVmap : ∀ p : Point n, AEStronglyMeasurable
      (fun z => uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z p)
      (volume : Measure (Point n))) :
    ∀ (τ : ℝ), AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck (curvedRNCMetric K))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K) (curvedRNCInv K)))
        a b (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset) τ (0 : Point n) z)
      (volume : Measure (Point n)) := by
  intro τ
  have hcont : Continuous (fun w : Point n => radialCutoff a b w
      * heatParametrix 1 (vanVleck (curvedRNCMetric K))
          (transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K) (curvedRNCInv K))) τ w) :=
    vanVleck_witnessInner_continuous_ofGeom (curvedRNCMetric K) (curvedRNCInv K)
      (fun a b => curvedRNCMetric_contDiff K a b)
      (fun a b => curvedRNCInv_contDiff K (le_of_lt hK) a b)
      (curvedRNCMetric_hgpos K (le_of_lt hK)) a b τ
  exact hcont.comp_aestronglyMeasurable (hVmap 0)

/-- **★★ `curvedRNC_hWmeas`.**  The EXACT `hWmeas` binder of
    `A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary` for the curved witness
    `g^K = curvedRNCMetric K` (`K < 0`): `∀ τ, AEStronglyMeasurable (z ↦ H_G τ 0 z) volume`.  Obtained
    by feeding `curvedRNC_hIn_from_geometry` and `compactGate_measurableSet hK` (bound compactness)
    through the generic banked reduction
    `WitnessMeasDeriv.vanVleckGatedWitness_slice_aestronglyMeasurable`.  Reduced to the two strictly
    lighter, curvature-independent carries {`hSm`, `hVmap`}.  NOT `a₁ = R/6`. -/
theorem curvedRNC_hWmeas (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (c a b : ℝ)
    (hSm : MeasurableSet {z : Point n |
      (0 : Point n) ∈ constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c z})
    (hVmap : ∀ p : Point n, AEStronglyMeasurable
      (fun z => uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z p)
      (volume : Measure (Point n))) :
    ∀ (τ : ℝ), AEStronglyMeasurable
      (fun z => vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
        (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n) z)
      (volume : Measure (Point n)) :=
  fun τ => vanVleckGatedWitness_slice_aestronglyMeasurable
    (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
    (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n)
    (compactGate_measurableSet hKset) hSm
    (curvedRNC_hIn_from_geometry K hK hChr hKset a b hVmap τ)

/-- **`curvedRNC_hWslice`.**  The `hWslice` binder of `a1_R6_from_labelled_curved_boundary` for the
    curved witness `g^K` — identical in statement to `hWmeas`; the same discharge serves both.
    NOT `a₁ = R/6`. -/
theorem curvedRNC_hWslice (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (c a b : ℝ)
    (hSm : MeasurableSet {z : Point n |
      (0 : Point n) ∈ constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c z})
    (hVmap : ∀ p : Point n, AEStronglyMeasurable
      (fun z => uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z p)
      (volume : Measure (Point n))) :
    ∀ (τ : ℝ), AEStronglyMeasurable
      (fun z => vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
        (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n) z)
      (volume : Measure (Point n)) :=
  curvedRNC_hWmeas K hK hChr hKset c a b hSm hVmap

end QIQTH.CurvedRNCWitnessMeas

section AxiomChecks
open QIQTH.CurvedRNCWitnessMeas
#print axioms curvedRNC_hIn_from_geometry
#print axioms curvedRNC_hWmeas
#print axioms curvedRNC_hWslice
end AxiomChecks
