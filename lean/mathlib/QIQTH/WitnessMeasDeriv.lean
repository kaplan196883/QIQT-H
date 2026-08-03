/-
  WitnessMeasDeriv — J4-165: discharge / reduction of the two lighter carries `hWmeas` and `hWdiff`
  that `QIQTH.G2CarryDischarge.hKmeas_from_witness` (J4-163) consumes for the concrete `N = 1`
  gated van-Vleck witness `H_G := vanVleckGatedWitness`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It takes the two
  carries `hWmeas` (z-ae-measurability of the WITNESS field-slices) and `hWdiff` (field-slice
  differentiability of the witness to the derivative kernel) that `hKmeas_from_witness` leaves
  standing, and discharges / reduces each to strictly lighter, satisfiable, non-vacuous carries.
  Never the conclusion.

  ── SLOT CONVENTION.  In `H_G τ p q` the FIELD point is `p`, the BASE point is `q`.  `hWmeas` /
  `hWdiff` are about z-ae-measurability / field-slice differentiability where `z` is the BASE slot
  `q` (the outer integration variable).  The gate is `q ∈ K` (base) ∧ `p ∈ S q` (field), so in the
  z (= base) variable the witness has the indicator shape
      `z ↦ if z ∈ K then (if p ∈ S z then H_inner τ p z else 0) else 0`
  (`p` fixed on the slice), and off the base gate (`z ∉ K`) the whole witness vanishes in EVERY
  field slot.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`).

    ● PART A — `hWmeas` (z-measurability), FULLY REDUCED to three strictly lighter carries.
      • `gatedKernel_slice_aestronglyMeasurable` — ★ THE GENERAL GATED-INDICATOR MEASURABILITY LEVER
          (reusable, parametric in the base kernel `H`).  For a fixed time `τ` and field point `p`,
          if `K` is measurable, the field-gate preimage `{z | p ∈ S z}` is measurable, and the inner
          kernel slice `z ↦ H τ p z` is `AEStronglyMeasurable`, then the gated slice
          `z ↦ gatedKernel K S H τ p z` is `AEStronglyMeasurable`.  Route: the gated slice equals
          `(K ∩ {z | p ∈ S z}).indicator (z ↦ H τ p z)`, then `AEStronglyMeasurable.indicator`.
      • `vanVleckGatedWitness_slice_aestronglyMeasurable` — the concrete wrapper: the witness slice
          `z ↦ H_G τ p z` is `AEStronglyMeasurable` from {`K` measurable, `{z | p ∈ S z}` measurable,
          inner parametrix slice z-ae-measurable}.
      • `hWmeas_from_carries` — the EXACT `hWmeas` slot of `hKmeas_from_witness`, reduced to the three
          carries {`hKm` : `MeasurableSet K`, `hSm` : `∀ p, MeasurableSet {z | p ∈ S z}`, `hIn` :
          z-ae-measurability of the inner order-1 parametrix slice for every `(τ, p)`}.  Each strictly
          lighter than the gated derivative-kernel measurability they eventually produce.

    ● PART B — `hWdiff` (field-slice differentiability), off-gate leg DISCHARGED, on-gate reduced.
      • `hWdiff_offGate` — ★ THE OFF-GATE LEG, FULLY PROVED.  Off the base gate (`z ∉ K`) the witness
          field-slice `w ↦ H_G τ (update x i w) z` is the CONSTANT `0`, so `HasDerivAt … 0`, and
          `witnessFieldDeriv … x z = 0` there (`witnessFieldDeriv_offGate_eq_zero`); hence the exact
          `HasDerivAt (slice) (witnessFieldDeriv …)` holds with derivative `0`.  Unconditional.
      • `hWdiff_onGate` — the on-gate leg reduced to the on-gate `C¹` carry `PdiffAt (x' ↦ H_G τ x' z)
          i x` (field-slot partial-differentiability of the witness); since `witnessFieldDeriv` is by
          definition `pd` = `deriv` of that very slice, `DifferentiableAt.hasDerivAt` closes it.
      • `hWdiff_from_gateDiff` — the EXACT `hWdiff` slot, reduced (via the a.e.-z gate dichotomy) to
          the on-gate `C¹` family `hGateDiff` (a.e. z, `z ∈ K → PdiffAt …`); off the gate the proved
          off-gate leg discharges it.

    ● CAPSTONE — `hKmeas_concrete`.  Feeding `hWmeas_from_carries` and `hWdiff_from_gateDiff` through
      `hKmeas_from_witness`, the EXACT `hKmeas` slot of `g2_bundle_assembled` for the concrete witness
      derivative kernel `witnessFieldDeriv`, reduced to the four strictly lighter carries
      {`hKm`, `hSm`, `hIn`, `hGateDiff`} — each satisfiable, non-vacuous, none the conclusion.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hKm` — `MeasurableSet K`.  The concrete `K` is a compact base-gate set (`IsCompact.measurableSet`
      / `IsClosed.measurableSet` once its concrete form is exposed); a genuine measurability input.
    • `hSm` — measurability of the field-gate preimage `{z | p ∈ S z}`.  The concrete `S q` is the
      chart-image ball `φ_q '' (inner ball)`; measurability of its `z`-preimage is a genuine geometric
      measurability input (chart continuity in the base slot).
    • `hIn` — z-ae-measurability of the inner smooth order-1 parametrix slice
      `z ↦ radialCutoff · heatParametrix 1 (Θ ∘ W z p)` (z enters through `W z p =
      uniformInverseChart g gi hC hK z p`).  Satisfiable from z-continuity of the base-chart pullback
      (`Continuous.aestronglyMeasurable`); a lighter regularity carry than the derivative measurability.
    • `hGateDiff` — the a.e.-z on-gate `C¹` family `z ∈ K → PdiffAt (x' ↦ H_G τ x' z) i x`; grounded
      in the germ-`C²` witness family (`witnessFieldDeriv_gate_eq` establishes exactly this
      differentiability at the field point from the carried chart jet + amplitude data).

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.G2CarryDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.WitnessDerivDomination QIQTH.G2CarryDischarge
open scoped Interval Topology BigOperators

namespace QIQTH.WitnessMeasDeriv

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART A — `hWmeas` : the gated-indicator z-measurability lever + reductions.
    ############################################################################### -/

/-- **★ `gatedKernel_slice_aestronglyMeasurable` — THE GENERAL GATED-INDICATOR MEASURABILITY LEVER.**
    For a base kernel `H : ℝ → Point n → Point n → ℝ`, a fixed time `τ`, and a fixed field point `p`,
    if `K` is measurable, the field-gate preimage `{z | p ∈ S z}` is measurable, and the inner slice
    `z ↦ H τ p z` is `AEStronglyMeasurable`, then the gated slice `z ↦ gatedKernel K S H τ p z` is
    `AEStronglyMeasurable`.  Route: the gated slice equals `(K ∩ {z | p ∈ S z}).indicator (z ↦ H τ p z)`
    (banked `gatedKernel_apply_of_mem`/`_of_notMem` case-split), then `AEStronglyMeasurable.indicator`.
    Reusable, parametric in `H`.  NOT `a₁ = R/6`. -/
theorem gatedKernel_slice_aestronglyMeasurable (K : Set (Point n)) (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p : Point n) (ν : Measure (Point n))
    (hKm : MeasurableSet K) (hSm : MeasurableSet {z : Point n | p ∈ S z})
    (hHm : AEStronglyMeasurable (fun z => H τ p z) ν) :
    AEStronglyMeasurable (fun z => gatedKernel K S H τ p z) ν := by
  classical
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
  rw [hrw]
  exact hHm.indicator (hKm.inter hSm)

/-- **`vanVleckGatedWitness_slice_aestronglyMeasurable`** — the concrete wrapper of the lever for the
    `N = 1` gated van-Vleck witness `H_G`.  The witness base-slice `z ↦ H_G τ p z` is
    `AEStronglyMeasurable` from {`K` measurable, `{z | p ∈ S z}` measurable, inner order-1 parametrix
    slice z-ae-measurable}.  NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitness_slice_aestronglyMeasurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (p : Point n)
    (hKm : MeasurableSet K) (hSm : MeasurableSet {z : Point n | p ∈ S z})
    (hIn : AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p z)
      (volume : Measure (Point n))) :
    AEStronglyMeasurable
      (fun z => vanVleckGatedWitness g gi hC hK S a b τ p z) (volume : Measure (Point n)) := by
  unfold vanVleckGatedWitness
  exact gatedKernel_slice_aestronglyMeasurable K S _ τ p volume hKm hSm hIn

/-- **`hWmeas_from_carries`** — the EXACT `hWmeas` slot of `hKmeas_from_witness`, reduced to three
    strictly lighter carries: `hKm` (`MeasurableSet K`), `hSm` (`∀ p, MeasurableSet {z | p ∈ S z}`),
    and `hIn` (z-ae-measurability of the inner order-1 parametrix slice for every `(τ, p)`).  Since
    the reduced hWmeas holds for EVERY `x`/`s`, the `∀ᵐ s`/`∀ᶠ x` quantifiers collapse to
    `ae_of_all`/`Eventually.of_forall`.  NOT `a₁ = R/6`. -/
theorem hWmeas_from_carries (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hKm : MeasurableSet K)
    (hSm : ∀ p : Point n, MeasurableSet {z : Point n | p ∈ S z})
    (hIn : ∀ (τ : ℝ) (p : Point n), AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p z)
      (volume : Measure (Point n))) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z)
        (volume : Measure (Point n)) := by
  intro x₀ _hx₀ i
  refine ae_of_all volume (fun s => ?_)
  intro _hmem
  refine Filter.Eventually.of_forall (fun x => ?_)
  intro w
  exact vanVleckGatedWitness_slice_aestronglyMeasurable g gi hC hK S a b (t - s)
    (Function.update x i w) hKm (hSm _) (hIn (t - s) (Function.update x i w))

/-! ###############################################################################
    ### PART B — `hWdiff` : off-gate leg (proved) + on-gate reduction + dichotomy.
    ############################################################################### -/

/-- **★ `hWdiff_offGate` — THE OFF-GATE LEG, FULLY PROVED.**  Off the base gate (`z ∉ K`) the witness
    field-slice `w ↦ H_G τ (update x i w) z` is the CONSTANT `0`, so it has derivative `0`; and the
    concrete first-derivative kernel `witnessFieldDeriv … x z = 0` there
    (`witnessFieldDeriv_offGate_eq_zero`).  Hence the exact
    `HasDerivAt (slice) (witnessFieldDeriv …) (x i)` holds with derivative `0`.  Unconditional. -/
theorem hWdiff_offGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (x z : Point n) (hz : z ∉ K) :
    HasDerivAt (fun w => vanVleckGatedWitness g gi hC hK S a b τ (Function.update x i w) z)
      (witnessFieldDeriv g gi hC hK S a b i τ x z) (x i) := by
  have hzero : (fun w : ℝ => vanVleckGatedWitness g gi hC hK S a b τ (Function.update x i w) z)
      = (fun _ : ℝ => (0 : ℝ)) := by
    funext w
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ (Function.update x i w) z (Or.inl hz)
  rw [hzero, witnessFieldDeriv_offGate_eq_zero g gi hC hK S a b i τ x z hz]
  exact hasDerivAt_const (x i) (0 : ℝ)

/-- **`hWdiff_onGate`** — the on-gate leg, reduced to the on-gate `C¹` carry.  `witnessFieldDeriv` is
    BY DEFINITION `pd (x' ↦ H_G τ x' z) i x = deriv (w ↦ H_G τ (update x i w) z) (x i)`, so from the
    field-slot partial-differentiability of the witness (`PdiffAt (x' ↦ H_G τ x' z) i x`,
    definitionally `DifferentiableAt` of the very slice) `DifferentiableAt.hasDerivAt` closes it.
    NOT `a₁ = R/6`. -/
theorem hWdiff_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (x z : Point n)
    (hpdiff : PdiffAt (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x) :
    HasDerivAt (fun w => vanVleckGatedWitness g gi hC hK S a b τ (Function.update x i w) z)
      (witnessFieldDeriv g gi hC hK S a b i τ x z) (x i) := by
  have hd : DifferentiableAt ℝ
      (fun w : ℝ => vanVleckGatedWitness g gi hC hK S a b τ (Function.update x i w) z) (x i) :=
    hpdiff
  exact hd.hasDerivAt

/-- **`hWdiff_from_gateDiff`** — the EXACT `hWdiff` slot of `hKmeas_from_witness`, reduced via the
    a.e.-z gate DICHOTOMY to the on-gate `C¹` family carry `hGateDiff` (a.e. z, `z ∈ K → PdiffAt (x' ↦
    H_G (t−s) x' z) i x`).  For a.e. z: if `z ∈ K` the on-gate leg `hWdiff_onGate` applies with the
    carried `PdiffAt`; if `z ∉ K` the proved off-gate leg `hWdiff_offGate` applies unconditionally.
    NOT `a₁ = R/6`. -/
theorem hWdiff_from_gateDiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hGateDiff : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ z ∂(volume : Measure (Point n)),
        HasDerivAt (fun w => vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z)
          (witnessFieldDeriv g gi hC hK S a b i (t - s) x z) (x i) := by
  intro x₀ hx₀ i
  filter_upwards [hGateDiff x₀ hx₀ i] with s hs hmem
  filter_upwards [hs hmem] with x hx
  filter_upwards [hx] with z hz
  by_cases hzK : z ∈ K
  · exact hWdiff_onGate g gi hC hK S a b i (t - s) x z (hz hzK)
  · exact hWdiff_offGate g gi hC hK S a b i (t - s) x z hzK

/-! ###############################################################################
    ### CAPSTONE — `hKmeas_concrete` (feed both reductions through `hKmeas_from_witness`).
    ############################################################################### -/

/-- **★★ `hKmeas_concrete`.**  The EXACT `hKmeas` slot of `g2_bundle_assembled` for the concrete
    witness first-derivative kernel `witnessFieldDeriv`, obtained by feeding `hWmeas_from_carries`
    and `hWdiff_from_gateDiff` through `G2CarryDischarge.hKmeas_from_witness`.  Reduced to the FOUR
    strictly lighter carries {`hKm` : `MeasurableSet K`, `hSm` : field-gate preimage measurable,
    `hIn` : inner parametrix slice z-ae-measurable, `hGateDiff` : on-gate `C¹` family} — each
    satisfiable, non-vacuous, none the conclusion.  NOT `a₁ = R/6`. -/
theorem hKmeas_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hKm : MeasurableSet K)
    (hSm : ∀ p : Point n, MeasurableSet {z : Point n | p ∈ S z})
    (hIn : ∀ (τ : ℝ) (p : Point n), AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p z)
      (volume : Measure (Point n)))
    (hGateDiff : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z)
        (volume : Measure (Point n)) :=
  hKmeas_from_witness g gi hC hK S a b t u
    (hWmeas_from_carries g gi hC hK S a b t u hKm hSm hIn)
    (hWdiff_from_gateDiff g gi hC hK S a b t u hGateDiff)

end QIQTH.WitnessMeasDeriv

section AxiomChecks
open QIQTH.WitnessMeasDeriv
#print axioms gatedKernel_slice_aestronglyMeasurable
#print axioms vanVleckGatedWitness_slice_aestronglyMeasurable
#print axioms hWmeas_from_carries
#print axioms hWdiff_offGate
#print axioms hWdiff_onGate
#print axioms hWdiff_from_gateDiff
#print axioms hKmeas_concrete
end AxiomChecks
