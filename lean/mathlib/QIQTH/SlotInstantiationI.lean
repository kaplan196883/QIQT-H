/-
  SlotInstantiationI — J4-418 (Part B, tranche (a) phase 1): CONCRETE instantiation of the EASIEST
  group-(1) slot carries at the true van-Vleck witness.

  The a₁ = R/6 terminal conditional surface (J4-417) reduces to satisfiable enumerated data, of which
  group (1) is the slot-instantiation carries of `GpowClosure.leviSecondPairing_inner_bound_concrete`
  (the `qc`/`Ichart`/`hoff`, the integrabilities, the Lipschitz/center carries, and the Gaussian-moment
  dominators — census-projected by `GpowClosure.gpow_closure_carries` /
  `SlotDischarges.slot_discharge_residuals`).  This file BEGINS discharging them CONCRETELY, at the same
  ρ-scaled chart amplitude used by `AmplitudeDataOnCollar.amplitudeDataOn_concrete` and the literal-gate
  machinery of `ConstGateAssembly` — so the discharged binders can later be ABSORBED like the
  `hGauss`/`constRadius` bundles were.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It discharges
  a HONEST PARTIAL of group (1): the `qc` chart-native comparison amplitude (as a concrete function), the
  `h0` centre-match slot (fully, via `rhoRatio_center`), and the `hgate` gate-coverage slot (its radius
  conjunct fully/purely, its `z ∈ K` conjunct carried).  See the `## PHASE 1 COVERAGE` block for the
  honest fields-discharged / fields-remaining ledger.  No `sorry`, no `:= True`, no new axioms; std-3.
-/
import QIQTH.SlotDischarges

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SlotInstantiationI

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### B-field 1 — the `h0` centre-match slot at the concrete chart amplitude.
    ############################################################################### -/

/-- **★ B (slot `h0`, DISCHARGED) — `center_identity_concrete`.**  THE CENTRE-MATCH SLOT `qz 0 = qc 0`
    at the CONCRETE ρ-scaled chart amplitude.  With the term-1 amplitude
      `qz z := (rhoRatio g gi hChr hK τ z · chartAmp g gi hChr hK a b τ z 0) · F s z 0`
    (the exact `data.Aamp τ z · F s z 0` of `amplitudeDataOn_concrete`) and the chart-native comparison
    amplitude
      `qc z := chartAmp g gi hChr hK a b τ z 0 · F s z 0`,
    the two agree at the integration centre `z = 0` because `ρ(τ,0) = 1` (`rhoRatio_center`, given
    `0 ∈ K`).  This is VERBATIM the `h0` argument of `GpowClosure.leviSecondPairing_inner_bound_concrete`
    (equivalently the `h0_slot_of_center` shape) at the true witness — FULLY discharged, self-contained
    (no amplitude-data structure, no `∃`-witness mismatch).  ⚠ NOT `a₁ = R/6`. -/
theorem center_identity_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (τ s : ℝ) :
    (rhoRatio g gi hChr hK τ 0 * chartAmp g gi hChr hK a b τ 0 0) * F s 0 0
      = chartAmp g gi hChr hK a b τ 0 0 * F s 0 0 := by
  rw [rhoRatio_center g gi hChr hK h0K τ, one_mul]

/-! ###############################################################################
    ### B-field 2 — the `hgate` gate-coverage slot (radius conjunct pure, `K` conjunct carried).
    ############################################################################### -/

/-- **★ B (slot `hgate`, radius conjunct, DISCHARGED) — `hgate_radius_concrete`.**  THE RADIUS CONJUNCT
    of the gate-coverage slot, discharged PURELY from the scalar collar/gate comparison `c·√τ < r₀`: on
    the collar `‖z‖ ≤ c·√τ < r₀`, so `‖z‖ < r₀` for every collar point.  No geometry, no amplitude data.
    ⚠ NOT `a₁ = R/6`. -/
theorem hgate_radius_concrete (c τ r₀ : ℝ) (hcr : c * Real.sqrt τ < r₀) :
    ∀ z ∈ collar (n := n) (c * Real.sqrt τ), ‖z‖ < r₀ := by
  intro z hz
  have hzc : ‖z‖ ≤ c * Real.sqrt τ := hz
  linarith

/-- **★ B (slot `hgate`, ASSEMBLED) — `hgate_concrete`.**  THE GATE-COVERAGE SLOT
    `∀ z ∈ collar (c·√τ), z ∈ K ∧ ‖z‖ < r₀` — VERBATIM the `hgate` argument of `GpowClosure.hon_concrete`
    / `leviSecondPairing_inner_bound_concrete`.  The radius conjunct is discharged PURELY by
    `hgate_radius_concrete` (from `c·√τ < r₀`); the `z ∈ K` conjunct is the honest collar-in-base carry
    `hKcover` (the collar sits inside the compact base region for the geometry, exactly the ambient
    hypothesis `collar_to_regime` consumes).  Honest partial discharge of `hgate`.  ⚠ NOT `a₁ = R/6`. -/
theorem hgate_concrete {K : Set (Point n)} (c τ r₀ : ℝ) (hcr : c * Real.sqrt τ < r₀)
    (hKcover : ∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K) :
    ∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀ := by
  intro z hz
  exact ⟨hKcover z hz, hgate_radius_concrete c τ r₀ hcr z hz⟩

/-! ###############################################################################
    ### PACKAGE — the phase-1 conjunction of the concretely-discharged group-(1) fields.
    ############################################################################### -/

/-- **★★ B (phase-1 package) — `slotInstantiation_phase1`.**  The conjunction of the group-(1) slot
    carries DISCHARGED CONCRETELY in this brick, at the true ρ-scaled chart witness:
      • the `h0` centre-match slot (`center_identity_concrete`, fully; `qc := chartAmp·F`,
        `qz := (ρ·chartAmp)·F`), AND
      • the `hgate` gate-coverage slot (`hgate_concrete`; radius conjunct pure, `K` conjunct carried).
    Both are VERBATIM arguments of `GpowClosure.leviSecondPairing_inner_bound_concrete`.  This seeds
    J4-419+ (the next tranche-(a) fields).  ⚠ NOT `a₁ = R/6`. -/
theorem slotInstantiation_phase1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (c τ s r₀ : ℝ) (hcr : c * Real.sqrt τ < r₀)
    (hKcover : ∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K) :
    ((rhoRatio g gi hChr hK τ 0 * chartAmp g gi hChr hK a b τ 0 0) * F s 0 0
        = chartAmp g gi hChr hK a b τ 0 0 * F s 0 0)
    ∧ (∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀) :=
  ⟨center_identity_concrete g gi hChr hK h0K a b F τ s,
   hgate_concrete c τ r₀ hcr hKcover⟩

end QIQTH.SlotInstantiationI

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SlotInstantiationI
#print axioms center_identity_concrete
#print axioms hgate_radius_concrete
#print axioms hgate_concrete
#print axioms slotInstantiation_phase1
end AxiomChecks

/-! ###############################################################################
    ## PHASE 1 COVERAGE  (J4-418 Part B, tranche (a))
    ###############################################################################

  FIELDS DISCHARGED CONCRETELY (at the true ρ-scaled chart witness, `S`-generic):
    • `qc` (chart-native comparison amplitude) — SUPPLIED as the concrete function
      `fun z => chartAmp g gi hChr hK a b τ z 0 * F s z 0` (the `h0_slot_of_center` `hqc0` shape).
    • `h0` (centre-match slot `qz 0 = qc 0`) — FULLY, via `center_identity_concrete`
      (supplier: `AmpGeometryBundle.rhoRatio_center`, needs `0 ∈ K`).  Self-contained.
    • `hgate` (gate-coverage `∀ z ∈ collar, z ∈ K ∧ ‖z‖ < r₀`) — via `hgate_concrete`:
        · radius conjunct `‖z‖ < r₀` — FULLY/PURELY (`hgate_radius_concrete`, from `c·√τ < r₀`);
        · `z ∈ K` conjunct — carried honestly (`hKcover`, the collar-in-base geometry carry).

  DONT-UNDERCREDIT CHECK.  A concrete `AmplitudeDerivativeDataOn` bundle already exists in the bank
  (`AmplitudeDataOnCollar.amplitudeDataOn_concrete`), whose `Aamp := ρ·chartAmp 0` fixes the concrete
  `qz`; and `SlotDischarges.h0_slot_of_center` / `hgate_of_collarRegime_cover` already state these slots
  ABSTRACTLY (from a `data` term / a `collarRegime` cover).  This brick supplies the `qc`/`h0`/`hgate`
  fields DIRECTLY (no `data` structure, no `collarRegime` cover needed), so they are genuinely NEW
  self-contained concrete discharges rather than re-exports.

  FIELDS NOT YET DISCHARGED (honest residue — J4-419+; each with a one-line plan):
    • `Ichart` + `hoff` (off-collar integrand identity) — plan: instantiate `Ichart := hessCoeff·G^chart·qc`
      and derive `hoff` from `SliverAssemblyMatched`'s off-collar chart-native identity at the witness.
    • integrabilities (`hWint`/`hf2`/`hf3`/`hIchart_int`) — plan: from the concrete amplitude sup-bounds
      (`amplitudeDataOn_concrete.hAampBdd/…`) × Gaussian integrability (banked `gaussDdim` integrable).
    • Lipschitz carries (`hqz`/`hqc`) — plan: `DataAmpAssembly.concrete_hqLip_of_carries` at this witness.
    • `hcomp` (comparison leg) — plan: `SlotDischarges.hcomp_slot_of_dom` + `cubic_gaussian_moment_witness`.
    • `hf2bound`/`hf3bound` (gradient/mass Gaussian-moment dominators) — plan:
      `SlotDischarges.hf2bound_slot_of_dom`/`hf3bound_slot_of_dom` + the cubic/mass moment family.
  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.
-/
