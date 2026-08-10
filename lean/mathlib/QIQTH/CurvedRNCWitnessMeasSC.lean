/-
  CurvedRNCWitnessMeasSC — J4-528: the SELF-CONTAINED curved witness measurability capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about the coefficient.  The
  binder discharged here is the CURVATURE-INDEPENDENT measurability bookkeeping `hWmeas` / `hWslice`
  of the curved-signature capstone, for the genuinely curved witness `g^K = curvedRNCMetric K`
  (`K < 0`).  Closing it does NOT derive `a₁`.  The remaining wall to a non-vacuous derived curved
  `a₁` is the curved heat-kernel Gaussian dominations (heatOp / Levi), entirely untouched here.

  ── J4-527 (`CurvedRNCWitnessMeas`) reduced the capstone `hWmeas` for `g^K` to exactly TWO residual
     carries: `hSm` (the gate-set preimage `{z | 0 ∈ constGate … c z}` measurable) and `hVmap`
     (FULL-`volume` AE-measurability of the base-chart pullback `z ↦ uniformInverseChart … z p`, ∀p).

  ── J4-528 (THIS FILE) DISCHARGES `hSm` INTERNALLY and STRICTLY LIGHTENS `hVmap`, leaving ONE carry:

    • `hSm` — DISCHARGED (no longer a hypothesis) for gate radii `c` below the uniform reach `δ₀`,
      via the banked Lusin–Souslin K-restricted gate graph
      (`ConcreteGateInstantiation.hKSmeas_concrete` ⟹ `B2MeasurabilityDissolution.hSmeasSet_Krestricted`).
      KEY: the gated witness `vanVleckGatedWitness` only ever tests the gate INSIDE `K`
      (`gatedKernel` gates on `z ∈ K`), so the FULL-volume witness slice needs only
      `MeasurableSet (K ∩ {z | 0 ∈ S z}) = MeasurableSet {z | z ∈ K ∧ 0 ∈ S z}` — the banked
      K-restricted graph — NOT the raw off-`K` set.  The `∞`-continuity route (`vanVleck_witnessInner…
      _ofGeom`) supplies the restricted inner slice, then the K-guard indicator lever
      (`gatedKernel_slice_aemeas_ofRestricted_Kguard`) delivers full `volume`.

    • `hw` (foldedCoeff smoothness) — DISCHARGED INTERNALLY from the curved smoothness bundle via the
      `∞` rebase inside `HuInftyRebase.vanVleck_witnessInner_continuous_ofGeom` (`⊤`/analytic is NOT
      available for `g^K`; the whole chain lives at `∞`).

    • `hVmapK` — the ONE remaining carry, STRICTLY LIGHTER than J4-527's `hVmap`: it is the
      `volume.restrict Kset` AE-measurability of the base-chart pullback at the SINGLE field point
      `p = 0` (vs J4-527's full-`volume`, ∀-`p`).  This is exactly the honest geometric residue the
      flat program carries (`FoldedCoeffChartMeas.hVmapMeasK_zero_of_geom` / the injectivity-radius
      disjunction): the chart's origin right-inverse over `K` is genuine curved geometry, not
      bookkeeping, so it is not discharged here.

  ── SATISFIABILITY GATE.  Non-vacuous at a GENUINELY CURVED witness: take any `K < 0`, any compact
     `Kset ∋ 0`, window `a < b`, radius `0 < c < δ₀`.  Then `g^K` has `Ric(0) = (n−1)Kδ ≠ 0`
     (`CurvedRNCGaussWitness.curvedRNCMetric_ricci_trace_diag_ne`), so nothing collapses to flat;
     `curvedRNCMetric_hgpos K (le_of_lt hK)` supplies `det g^K > 0` (the curved det-positivity where
     `K ≤ 0` posdef genuinely enters); `hVmapK` holds for the concrete origin chart over `Kset`.
     None of the discharged/carried facts is vacuous, and none is the `a₁` conclusion.
-/
import Mathlib
import QIQTH.CurvedRNCWitnessMeas
import QIQTH.FoldedCoeffChartMeas
import QIQTH.B2MeasurabilityDissolution
import QIQTH.ConcreteGateInstantiation

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.GateChartMeasurability QIQTH.WitnessMeasDeriv QIQTH.HuInftyRebase
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.HeatParametrixAnsatz
open scoped BigOperators

namespace QIQTH.CurvedRNCWitnessMeasSC

variable {n : ℕ}

/-- **★ `gatedKernel_slice_aemeas_ofRestricted_Kguard` — the K-GUARD restricted indicator lever.**
    The full-`volume` gated slice `z ↦ gatedKernel K S H τ p z` is `AEStronglyMeasurable` from the
    K-RESTRICTED gate-graph measurability `MeasurableSet {z | z ∈ K ∧ p ∈ S z}` (equivalently
    `MeasurableSet (K ∩ {z | p ∈ S z})`) plus the inner slice on `volume.restrict K`.  The gate always
    guards on `z ∈ K`, so the indicator support is `K ∩ {z | p ∈ S z}` and the RAW off-`K` gate slice
    is NEVER needed.  The K-guard variant of `FoldedCoeffChartMeas.gatedKernel_slice_aestronglyMeasurable_of_restricted`
    (which carries the raw `{z | p ∈ S z}`).  Reusable, parametric in `H`.  NOT `a₁ = R/6`. -/
theorem gatedKernel_slice_aemeas_ofRestricted_Kguard (K : Set (Point n))
    (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p : Point n)
    (hKSm : MeasurableSet {z : Point n | z ∈ K ∧ p ∈ S z})
    (hHmK : AEStronglyMeasurable (fun z => H τ p z) ((volume : Measure (Point n)).restrict K)) :
    AEStronglyMeasurable (fun z => gatedKernel K S H τ p z) (volume : Measure (Point n)) := by
  classical
  have hKinter : MeasurableSet (K ∩ {z : Point n | p ∈ S z}) := hKSm
  have hrw : (fun z => gatedKernel K S H τ p z)
      = (K ∩ {z : Point n | p ∈ S z}).indicator (fun z => H τ p z) := by
    funext z
    rw [Set.indicator_apply]
    by_cases hzK : z ∈ K
    · by_cases hzS : p ∈ S z
      · rw [gatedKernel_apply_of_mem K S H τ hzK hzS,
          if_pos (show z ∈ K ∩ {z : Point n | p ∈ S z} from ⟨hzK, hzS⟩)]
      · rw [gatedKernel_apply_of_notMem K S H τ p z (Or.inr hzS),
          if_neg (show z ∉ K ∩ {z : Point n | p ∈ S z} from fun h => hzS h.2)]
    · rw [gatedKernel_apply_of_notMem K S H τ p z (Or.inl hzK),
        if_neg (show z ∉ K ∩ {z : Point n | p ∈ S z} from fun h => hzK h.1)]
  rw [hrw, aestronglyMeasurable_indicator_iff hKinter]
  exact hHmK.mono_measure (Measure.restrict_mono_set volume Set.inter_subset_left)

/-- **★★ `curvedRNC_hWmeas_sc` — the SELF-CONTAINED curved witness `hWmeas`.**  For the genuinely
    curved witness `g^K = curvedRNCMetric K` (`K < 0`): there is a uniform reach `δ₀ > 0` such that for
    every gate radius `0 < c < δ₀` and every `τ`, the base witness slice
    `z ↦ vanVleckGatedWitness g^K gi^K hChr hKset (constGate … c) a b τ 0 z` is `AEStronglyMeasurable`
    for full `volume`, from the SINGLE curvature-independent carry `hVmapK`
    (`volume.restrict Kset` AE-measurability of the origin base-chart pullback).  `hSm` (the gate-set
    preimage) is DISCHARGED internally via the banked K-restricted Lusin–Souslin gate graph; `hw`
    (foldedCoeff smoothness) is DISCHARGED internally via the `∞` rebase.  NOT `a₁ = R/6`. -/
theorem curvedRNC_hWmeas_sc (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (a b : ℝ)
    (hVmapK : AEStronglyMeasurable
      (fun z => uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z (0 : Point n))
      ((volume : Measure (Point n)).restrict Kset)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ (τ : ℝ),
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
          (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n) z)
        (volume : Measure (Point n)) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ :=
    QIQTH.ConcreteGateInstantiation.hKSmeas_concrete (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ τ
  -- `hSm` DISCHARGED: the banked K-restricted gate graph at `p = 0`.
  have hgraph : MeasurableSet {w : ℝ × Point n × Point n |
      w.2.2 ∈ Kset ∧ w.2.1 ∈ constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c w.2.2} := by
    simpa only [constGate] using hspec c hc0 hcδ
  have hKSm : MeasurableSet {z : Point n |
      z ∈ Kset ∧ (0 : Point n) ∈ constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c z} :=
    QIQTH.B2MeasurabilityDissolution.hSmeasSet_Krestricted hgraph (0 : Point n)
  -- restrict-`K` inner slice from the `∞`-continuity + the single restrict-`K` carry `hVmapK`.
  have hInK : AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck (curvedRNCMetric K))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K) (curvedRNCInv K)))
        a b (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset) τ (0 : Point n) z)
      ((volume : Measure (Point n)).restrict Kset) := by
    have hcont : Continuous (fun w : Point n => radialCutoff a b w
        * heatParametrix 1 (vanVleck (curvedRNCMetric K))
            (transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K) (curvedRNCInv K))) τ w) :=
      vanVleck_witnessInner_continuous_ofGeom (curvedRNCMetric K) (curvedRNCInv K)
        (fun a b => curvedRNCMetric_contDiff K a b)
        (fun a b => curvedRNCInv_contDiff K (le_of_lt hK) a b)
        (curvedRNCMetric_hgpos K (le_of_lt hK)) a b τ
    exact hcont.comp_aestronglyMeasurable hVmapK
  -- assemble via the K-guard indicator lever.
  unfold vanVleckGatedWitness
  exact gatedKernel_slice_aemeas_ofRestricted_Kguard Kset
    (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) _ τ (0 : Point n) hKSm hInK

/-- **`curvedRNC_hWslice_sc` — the SELF-CONTAINED curved witness `hWslice`.**  Identical statement to
    `curvedRNC_hWmeas_sc`; the same discharge serves both.  NOT `a₁ = R/6`. -/
theorem curvedRNC_hWslice_sc (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (a b : ℝ)
    (hVmapK : AEStronglyMeasurable
      (fun z => uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z (0 : Point n))
      ((volume : Measure (Point n)).restrict Kset)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ (τ : ℝ),
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
          (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n) z)
        (volume : Measure (Point n)) :=
  curvedRNC_hWmeas_sc K hK hChr hKset a b hVmapK

end QIQTH.CurvedRNCWitnessMeasSC

section AxiomChecks
open QIQTH.CurvedRNCWitnessMeasSC
#print axioms gatedKernel_slice_aemeas_ofRestricted_Kguard
#print axioms curvedRNC_hWmeas_sc
#print axioms curvedRNC_hWslice_sc
end AxiomChecks
