/-
  GateChartMeasurability — J4-166: discharge of the `hKm` carry and reduction of the `hIn` carry
  that `QIQTH.WitnessMeasDeriv.hKmeas_concrete` (J4-165) consumes for the concrete `N = 1` gated
  van-Vleck witness derivative kernel `witnessFieldDeriv`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It takes the four
  carries `{hKm, hSm, hIn, hGateDiff}` that `hKmeas_concrete` leaves standing, DISCHARGES `hKm`
  (`MeasurableSet K` from the compactness of the base gate that is already bound throughout), and
  REDUCES `hIn` (z-ae-measurability of the inner order-1 parametrix slice) to strictly lighter,
  satisfiable, non-vacuous carries via a continuity/composition lever.  Never the conclusion.

  ── THE INNER-SLICE STRUCTURE (J4-165 finding, verified here).  Definitionally
      `globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p q
         = radialCutoff a b (Vmap q p) * heatParametrix 1 Θ u τ (Vmap q p)`,
  so the outer integration variable `z (= q)` enters the inner slice ONLY through the chart pullback
  `Vmap z p = uniformInverseChart g gi hC hK z p`.  Hence the inner slice is the COMPOSITION of the
  fixed spatial function `w ↦ radialCutoff a b w · heatParametrix 1 Θ u τ w` (CONTINUOUS — smooth
  cutoff times smooth parametrix, `radialCutoff_contDiff` × `heatParametrix_contDiff_space`, for
  EVERY `τ`, no `τ > 0` restriction needed) with the chart pullback `z ↦ Vmap z p`.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`).

    ● `compactGate_measurableSet` — `hKm` DISCHARGED.  `MeasurableSet K` from `IsCompact K`
      (`IsCompact.measurableSet`, `Point n` is `T2`).  The base gate `K` is bound as `IsCompact K`
      through the entire witness chain, so this is an unconditional discharge — `hKm` disappears.

    ● `witnessInner_continuous` — ★ THE INNER-SLICE SPATIAL CONTINUITY.  For every `τ` (no sign
      restriction), `w ↦ radialCutoff a b w · heatParametrix 1 Θ u τ w` is `Continuous`, from the
      unconditional smoothness of `radialCutoff` and the `hw`-conditional smoothness of the order-1
      parametrix (`heatParametrix_contDiff_space`, valid for all `t`).

    ● `hIn_composed_aestronglyMeasurable` — ★ THE COMPOSITION LEVER (generic in `Θ, u, Vmap`).  From
      {`hw` : coefficient smoothness, `hVmap` : z-ae-measurability of the chart pullback `z ↦ Vmap z p`}
      the inner slice `z ↦ globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p z` is
      `AEStronglyMeasurable` — `Continuous.comp_aestronglyMeasurable` of the continuous spatial function
      with the ae-measurable chart pullback.  Reusable, parametric.

    ● `hIn_concrete_of_chart_measurable` / `hIn_concrete_of_chart_continuous` — the exact `hIn` slot
      of `hKmeas_concrete` (concrete `Θ = vanVleck g`, `u = transportCoeff …`,
      `Vmap = uniformInverseChart g gi hC hK`), reduced to {`hw`, `hVmapMeas`} (resp. {`hw`, `hVmapCont`}
      with the continuity ⟹ ae-measurability step).

    ● CAPSTONE — `hKmeas_concrete_v2`.  The EXACT `hKmeas` slot for `witnessFieldDeriv`, with `hKm`
      DISCHARGED (via `compactGate_measurableSet hK`) and `hIn` REPLACED by {`hw`, `hVmapMeas`}.  Reduced
      to the strictly lighter carries {`hSm`, `hw`, `hVmapMeas`, `hGateDiff`}.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hSm`     — measurability of the field-gate preimage `{z | p ∈ S z}` (geometric; untouched here).
    • `hw`      — `∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)`, the STANDARD coefficient-smoothness carry
                  threaded through the entire parametrix chain (satisfiable from `hC`; a genuine
                  regularity input, strictly lighter than the derivative measurability it feeds).
    • `hVmapMeas` — `∀ p, AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p) volume`,
                  z-ae-measurability of the base-chart pullback.  Satisfiable: the chart pullback's
                  z-continuity is proved at `p = 0` on subsets (`GeodesicGronwall`,
                  `FlowJointRegularity`), and measurability is strictly weaker; a genuine geometric
                  regularity carry, not the conclusion.
    • `hGateDiff` — the a.e.-z on-gate `C¹` family (harder; untouched here).

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WitnessMeasDeriv

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.WitnessDerivDomination QIQTH.G2CarryDischarge QIQTH.WitnessMeasDeriv
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.GateChartMeasurability

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### `hKm` — DISCHARGED from the bound compactness of the base gate.
    ############################################################################### -/

/-- **`compactGate_measurableSet` — `hKm` DISCHARGED.**  The base gate `K` is bound as `IsCompact K`
    throughout the witness chain; since `Point n` is `T2`, `IsCompact.measurableSet` gives
    `MeasurableSet K` unconditionally.  NOT `a₁ = R/6`. -/
theorem compactGate_measurableSet {K : Set (Point n)} (hK : IsCompact K) : MeasurableSet K :=
  hK.measurableSet

/-! ###############################################################################
    ### `hIn` — the inner-slice spatial continuity + the composition lever.
    ############################################################################### -/

/-- **★ `witnessInner_continuous` — THE INNER-SLICE SPATIAL CONTINUITY.**  For every time `τ` (no
    sign restriction), the fixed spatial function `w ↦ radialCutoff a b w · heatParametrix 1 Θ u τ w`
    is `Continuous`, being the product of the unconditionally smooth radial cutoff
    (`radialCutoff_contDiff`) and the `hw`-conditionally smooth order-1 parametrix at fixed time
    (`heatParametrix_contDiff_space`, valid for ALL `t`).  NOT `a₁ = R/6`. -/
theorem witnessInner_continuous (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    Continuous (fun w : Point n => radialCutoff a b w * heatParametrix 1 Θ u τ w) :=
  (radialCutoff_contDiff a b).continuous.mul
    (heatParametrix_contDiff_space 1 Θ u τ hw).continuous

/-- **★ `hIn_composed_aestronglyMeasurable` — THE COMPOSITION LEVER (generic in `Θ, u, Vmap`).**
    The inner order-1 parametrix slice `z ↦ globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p z`
    is `AEStronglyMeasurable` from {`hw` : coefficient smoothness, `hVmap` : z-ae-measurability of the
    chart pullback `z ↦ Vmap z p`}.  The slice is definitionally the COMPOSITION of the continuous
    spatial function `w ↦ radialCutoff a b w · heatParametrix 1 Θ u τ w` (`witnessInner_continuous`)
    with the ae-measurable pullback, so `Continuous.comp_aestronglyMeasurable` closes it.  Reusable,
    parametric.  NOT `a₁ = R/6`. -/
theorem hIn_composed_aestronglyMeasurable (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (Vmap : Point n → Point n → Point n) (τ : ℝ) (p : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hVmap : AEStronglyMeasurable (fun z => Vmap z p) (volume : Measure (Point n))) :
    AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p z) (volume : Measure (Point n)) := by
  have hcont : Continuous (fun w : Point n => radialCutoff a b w * heatParametrix 1 Θ u τ w) :=
    witnessInner_continuous Θ u a b τ hw
  have hrw : (fun z => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p z)
      = (fun z => (fun w : Point n => radialCutoff a b w * heatParametrix 1 Θ u τ w) (Vmap z p)) := by
    funext z; rfl
  rw [hrw]
  exact hcont.comp_aestronglyMeasurable hVmap

/-- **`hIn_concrete_of_chart_measurable`** — the EXACT `hIn` slot of `hKmeas_concrete` for the concrete
    `Θ = vanVleck g`, `u = transportCoeff (transportOp (vanVleck g) g gi)`,
    `Vmap = uniformInverseChart g gi hC hK`, reduced to {`hw`, `hVmapMeas`} (z-ae-measurability of the
    base-chart pullback for every field point `p`).  Instantiates the generic composition lever.
    NOT `a₁ = R/6`. -/
theorem hIn_concrete_of_chart_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (hw : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hVmapMeas : ∀ p : Point n,
      AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p) (volume : Measure (Point n))) :
    ∀ (τ : ℝ) (p : Point n), AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p z)
      (volume : Measure (Point n)) :=
  fun τ p => hIn_composed_aestronglyMeasurable (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p hw
    (hVmapMeas p)

/-- **`hIn_concrete_of_chart_continuous`** — the same `hIn` slot from the STRONGER, often more directly
    available carry `hVmapCont` (z-CONTINUITY of the base-chart pullback), routed through
    `Continuous.aestronglyMeasurable`.  Shows continuity ⟹ the measurability the composition needs.
    NOT `a₁ = R/6`. -/
theorem hIn_concrete_of_chart_continuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (hw : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hVmapCont : ∀ p : Point n, Continuous (fun z => uniformInverseChart g gi hC hK z p)) :
    ∀ (τ : ℝ) (p : Point n), AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p z)
      (volume : Measure (Point n)) :=
  hIn_concrete_of_chart_measurable g gi hC hK a b hw
    (fun p => (hVmapCont p).aestronglyMeasurable)

/-! ###############################################################################
    ### CAPSTONE — `hKmeas_concrete_v2` (hKm discharged, hIn reduced to {hw, hVmapMeas}).
    ############################################################################### -/

/-- **★★ `hKmeas_concrete_v2`.**  The EXACT `hKmeas` slot of `g2_bundle_assembled` for the concrete
    witness first-derivative kernel `witnessFieldDeriv`, with the two `WitnessMeasDeriv.hKmeas_concrete`
    carries `hKm` and `hIn` REMOVED: `hKm` is discharged from the bound compactness `hK`
    (`compactGate_measurableSet`), and `hIn` is reduced to {`hw`, `hVmapMeas`} via the composition
    lever (`hIn_concrete_of_chart_measurable`).  Reduced to the strictly lighter carries
    {`hSm`, `hw`, `hVmapMeas`, `hGateDiff`} — each satisfiable, non-vacuous, none the conclusion.
    NOT `a₁ = R/6`. -/
theorem hKmeas_concrete_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hSm : ∀ p : Point n, MeasurableSet {z : Point n | p ∈ S z})
    (hw : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hVmapMeas : ∀ p : Point n,
      AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p) (volume : Measure (Point n)))
    (hGateDiff : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z)
        (volume : Measure (Point n)) :=
  hKmeas_concrete g gi hC hK S a b t u
    (compactGate_measurableSet hK) hSm
    (hIn_concrete_of_chart_measurable g gi hC hK a b hw hVmapMeas)
    hGateDiff

end QIQTH.GateChartMeasurability

section AxiomChecks
open QIQTH.GateChartMeasurability
#print axioms compactGate_measurableSet
#print axioms witnessInner_continuous
#print axioms hIn_composed_aestronglyMeasurable
#print axioms hIn_concrete_of_chart_measurable
#print axioms hIn_concrete_of_chart_continuous
#print axioms hKmeas_concrete_v2
end AxiomChecks
