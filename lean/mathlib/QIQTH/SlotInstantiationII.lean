/-
  SlotInstantiationII — J4-419 (Part B, tranche (a) phase 2): CONCRETE discharge of the `Ichart`
  witness + the `hoff` off-collar integrand identity, continuing `SlotInstantiationI` (phase 1).

  This file supplies the OFF-COLLAR half of the group-(1) slot carries of
  `GpowClosure.leviSecondPairing_inner_bound_concrete` (census-projected by
  `GpowClosure.gpow_closure_carries`, `hslots` field): the chart-native off-collar integrand `Ichart`
  (as a CONCRETE function) and the `hoff` slot `Wpair = Ichart + f₂ + f₃` on `(collar (c√τ))ᶜ`.

  ★ THE DESIGN-INTENDED WITNESS.  `GpowBridge.leviSecondPairing_eq_matchedAssembly` names its
  auxiliary integrand `f₁ := Wpair − f₂ − f₃`, which "equals `H·qz` on the collar and `Ichart` off it"
  (GpowBridge §A2, line 116).  So the CANONICAL off-collar `Ichart` is exactly the residual
      `Ichart z := witnessSecondXDeriv·F − f₂ − f₃`
  (`f₂ = z_i/(2τ)·G_τ·A1amp·F`, `f₃ = G_τ·A2amp·F`).  With this residual, the `hoff` identity
  `Wpair = Ichart + f₂ + f₃` holds POINTWISE-EVERYWHERE (in particular off the collar) by pure `ring`,
  so it is discharged FULLY and self-containedly — an id-transport-normal-form carry.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It discharges
  a HONEST PARTIAL of group (1): the `Ichart` witness (as a concrete function), the `hoff` slot (FULLY,
  by `ring`), the `hoff` SATISFIABILITY certificate (`∃ Ichart, hoff`), and — reduced to the three
  remaining full-space integrability carries `hWint`/`hf2`/`hf3` — the `hIchart_int` off-collar
  integrability slot.  The geometric CONTENT (that this residual has the chart-native `hessCoeff·G^chart·qc`
  form, needed for `hcomp`) is UNCHANGED and remains the honest residue.  No `sorry`, no `:= True`, no new
  axioms; std-3.  See the `## PHASE 2 COVERAGE` block for the honest ledger.
-/
import QIQTH.SlotInstantiationI

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open QIQTH.SlotInstantiationI
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SlotInstantiationII

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### B-field 3 — the chart-native off-collar integrand `Ichart` (the design residual).
    ############################################################################### -/

/-- **★ B (slot `Ichart`, WITNESS) — `IchartResidual`.**  THE OFF-COLLAR INTEGRAND, as the CANONICAL
    residual `Wpair − f₂ − f₃`:
      `IchartResidual z := witnessSecondXDeriv·F s z 0
                            − z_i/(2τ)·gaussDdim τ z·A1amp τ z·F s z 0
                            − gaussDdim τ z·A2amp τ z·F s z 0`.
    This is EXACTLY the auxiliary `f₁ := Wpair − f₂ − f₃` of
    `GpowBridge.leviSecondPairing_eq_matchedAssembly` restricted to the off-collar set (where it plays
    the `Ichart` role).  It is the concrete function instantiating the abstract `Ichart : Point n → ℝ`
    slot of `GpowClosure.leviSecondPairing_inner_bound_concrete`.  ⚠ NOT `a₁ = R/6`. -/
noncomputable def IchartResidual (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (z : Point n) : ℝ :=
  witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0
    - z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0
    - gaussDdim τ z * data.A2amp τ z * F s z 0

/-! ###############################################################################
    ### B-field 4 — the `hoff` off-collar integrand identity at the residual witness.
    ############################################################################### -/

/-- **★★ B (slot `hoff`, DISCHARGED) — `hoff_concrete`.**  THE OFF-COLLAR INTEGRAND IDENTITY
      `witnessSecondXDeriv·F s z 0 = Ichart z + f₂ z + f₃ z`   on `(collar (c√τ))ᶜ`,
    VERBATIM the `hoff` argument of `GpowClosure.leviSecondPairing_inner_bound_concrete` (its exact
    binder shape), with `Ichart := IchartResidual`.  Since `IchartResidual = Wpair − f₂ − f₃`, the
    identity holds POINTWISE-EVERYWHERE by `ring` (the off-collar restriction is not even needed) — a
    FULL, self-contained discharge in id-transport normal form.  ⚠ NOT `a₁ = R/6`. -/
theorem hoff_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) :
    ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
        witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0
          = IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
            + z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0
            + gaussDdim τ z * data.A2amp τ z * F s z 0 := by
  intro z _
  unfold IchartResidual
  ring

/-- **★ B (slot `hoff`, SATISFIABILITY) — `hoff_slot_inhabited`.**  THE CENSUS-LEVEL DISCHARGE of the
    abstract `hoff` slot: there EXISTS an `Ichart : Point n → ℝ` making the off-collar integrand
    identity hold — exactly the (existentially-quantified) satisfiability the `gpow_closure_carries`
    `hslots` field asserts for `hoff`.  Witnessed by `IchartResidual` (via `hoff_concrete`).  This is
    the id-transport certificate that the abstract `Ichart`/`hoff` slot pair of
    `leviSecondPairing_inner_bound_concrete` is inhabitable at the true witness.  ⚠ NOT `a₁ = R/6`. -/
theorem hoff_slot_inhabited (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) :
    ∃ Ichart : Point n → ℝ, ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
        witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0
          = Ichart z + z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0
            + gaussDdim τ z * data.A2amp τ z * F s z 0 :=
  ⟨IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s,
   hoff_concrete g gi hC hK S a b F i T τ₀ r₀ c data τ s⟩

/-! ###############################################################################
    ### B-field 5 — the off-collar integrability of `Ichart` (reduced to `hWint`/`hf2`/`hf3`).
    ############################################################################### -/

/-- **★ B (slot `hIchart_int`, DISCHARGED-MODULO) — `hIchart_int_concrete`.**  THE OFF-COLLAR
    INTEGRABILITY SLOT `IntegrableOn Ichart (collar (c√τ))ᶜ`, at the residual witness, REDUCED to the
    three full-space integrability carries `hWint` (`witnessSecondXDeriv·F`), `hf2` (gradient) and
    `hf3` (mass): since `IchartResidual = Wpair − f₂ − f₃`, it is integrable over ALL of space
    (`Integrable.sub` twice), hence `IntegrableOn` any set (`Integrable.integrableOn`).  This is the
    exact `hIchart_int` slot of `GpowClosure.leviSecondPairing_inner_bound_concrete`, discharged modulo
    the three (independent, still-carried) integrability inputs.  ⚠ NOT `a₁ = R/6`. -/
theorem hIchart_int_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ)
    (hWint : Integrable
      (fun z => witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0) volume)
    (hf2 : Integrable
      (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume)
    (hf3 : Integrable (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume) :
    IntegrableOn (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s)
        (collar (c * Real.sqrt τ))ᶜ volume := by
  have hInt : Integrable (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s) volume := by
    unfold IchartResidual
    exact (hWint.sub hf2).sub hf3
  exact hInt.integrableOn

/-! ###############################################################################
    ### PACKAGE — the phase-2 conjunction (phase-1 ∧ the off-collar `Ichart`/`hoff`/int slots).
    ############################################################################### -/

/-- **★★ B (phase-2 package) — `slotInstantiation_phase2`.**  The conjunction of the group-(1) slot
    carries discharged through phase 2, at the true ρ-scaled chart witness (built on
    `slotInstantiation_phase1`):
      • the `h0` centre-match slot (phase 1, `center_identity_concrete`), AND
      • the `hgate` gate-coverage slot (phase 1, `hgate_concrete`), AND
      • the `hoff` off-collar integrand identity (`hoff_concrete`, FULLY, at `Ichart := IchartResidual`), AND
      • the `hIchart_int` off-collar integrability (`hIchart_int_concrete`, reduced to `hWint`/`hf2`/`hf3`).
    All four are VERBATIM arguments of `GpowClosure.leviSecondPairing_inner_bound_concrete` at the same
    concrete witness.  This seeds J4-420+ (the Lipschitz carries `hqz`/`hqc`, `hcomp`, `hf2bound`,
    `hf3bound`).  ⚠ NOT `a₁ = R/6`. -/
theorem slotInstantiation_phase2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hChr hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hcr : c * Real.sqrt τ < r₀)
    (hKcover : ∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K)
    (hWint : Integrable
      (fun z => witnessSecondXDeriv g gi hChr hK S a b i τ z * F s z 0) volume)
    (hf2 : Integrable
      (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume)
    (hf3 : Integrable (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume) :
    ((rhoRatio g gi hChr hK τ 0 * chartAmp g gi hChr hK a b τ 0 0) * F s 0 0
        = chartAmp g gi hChr hK a b τ 0 0 * F s 0 0)
    ∧ (∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀)
    ∧ (∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
        witnessSecondXDeriv g gi hChr hK S a b i τ z * F s z 0
          = IchartResidual g gi hChr hK S a b F i T τ₀ r₀ c data τ s z
            + z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0
            + gaussDdim τ z * data.A2amp τ z * F s z 0)
    ∧ IntegrableOn (IchartResidual g gi hChr hK S a b F i T τ₀ r₀ c data τ s)
        (collar (c * Real.sqrt τ))ᶜ volume := by
  obtain ⟨hc, hg⟩ := slotInstantiation_phase1 g gi hChr hK h0K a b F c τ s r₀ hcr hKcover
  exact ⟨hc, hg,
    hoff_concrete g gi hChr hK S a b F i T τ₀ r₀ c data τ s,
    hIchart_int_concrete g gi hChr hK S a b F i T τ₀ r₀ c data τ s hWint hf2 hf3⟩

end QIQTH.SlotInstantiationII

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SlotInstantiationII
#print axioms hoff_concrete
#print axioms hoff_slot_inhabited
#print axioms hIchart_int_concrete
#print axioms slotInstantiation_phase2
end AxiomChecks

/-! ###############################################################################
    ## PHASE 2 COVERAGE  (J4-419, Part B, tranche (a))
    ###############################################################################

  FIELDS DISCHARGED CONCRETELY (at the true ρ-scaled chart witness, `S`-generic; building on phase 1):
    • `Ichart` (off-collar integrand) — SUPPLIED as the concrete function `IchartResidual`
      (`= Wpair − f₂ − f₃`, the design-intended auxiliary `f₁` of
      `GpowBridge.leviSecondPairing_eq_matchedAssembly` off the collar).
    • `hoff` (off-collar identity `Wpair = Ichart + f₂ + f₃`) — FULLY, via `hoff_concrete`
      (pure `ring`; holds pointwise-everywhere, so a fortiori on `(collar (c√τ))ᶜ`).  Its census-level
      SATISFIABILITY is `hoff_slot_inhabited` (`∃ Ichart, hoff`), the abstract-slot inhabitant.
    • `hIchart_int` (off-collar integrability of `Ichart`) — via `hIchart_int_concrete`, REDUCED to the
      three still-carried full-space integrability inputs `hWint`/`hf2`/`hf3` (`Integrable.sub` ×2 →
      `Integrable.integrableOn`).
    • (carried through from phase 1) `h0` (`center_identity_concrete`, fully) and `hgate`
      (`hgate_concrete`; radius conjunct pure, `z ∈ K` conjunct via `hKcover`).

  DONT-UNDERCREDIT CHECK.  Grepped the bank for existing `Ichart`/`hoff` constructions:
    · `GpowClosure.leviSecondPairing_inner_bound_concrete` / `GpowBridge.leviSecondPairing_inner_bound`
      take `Ichart`/`hoff` as ABSTRACT parameters — they never CONSTRUCT a concrete `Ichart` nor prove
      `hoff`.  `SliverAssemblyMatched`/`SliverOffCollarMatched` also thread an abstract `Ichart` and only
      prove BOUNDS on `Ichart − hessGaussFactor·qc` (the `hcomp` leg), never the raw `hoff` equality.
    · `AmplitudeDerivativeDataOn.hD2Hexpand` is the exact 3-term identity but is CONDITIONED on
      `Regime = collarRegime` (i.e. ON the collar `‖z‖ ≤ c√τ`); it does NOT hold on `(collar (c√τ))ᶜ`,
      so it CANNOT supply `hoff` (which lives off the collar).  The residual definition is therefore the
      genuinely-new, honest, off-collar `hoff` discharge — not a re-export.

  FIELDS NOT YET DISCHARGED (honest residue — J4-420+; each with a one-line plan):
    • `hqz`/`hqc` (Lipschitz carries) — plan: `DataAmpAssembly.concrete_hqLip_of_carries` at this witness
      (the `data.hqLip` field gives `hqz`; `hqc` for the chart-native `qc`).
    • `hcomp` (comparison leg) — plan: `SlotDischarges.hcomp_slot_of_dom` /
      `SliverAssemblyMatched.comparison_leg_of_dom` + `cubic_gaussian_moment_witness` (this is where the
      chart-native geometric CONTENT of `IchartResidual` re-enters: bound `∫‖Ichart − H·qc‖`).
    • `hf2bound`/`hf3bound` (gradient/mass Gaussian-moment dominators) — plan:
      `SlotDischarges.hf2bound_slot_of_dom`/`hf3bound_slot_of_dom` + the cubic/mass moment family.
    • `hWint`/`hf2`/`hf3` (full-space integrabilities) — still carried; feed both `hIchart_int` (here) and
      the `leviSecondPairing_inner_bound_concrete` split.
  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.
-/
