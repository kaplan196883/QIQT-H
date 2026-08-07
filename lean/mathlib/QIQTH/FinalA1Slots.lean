/-
  FinalA1Slots — J4-409: Sol #18 final-assembly brick #2, THE SEMANTIC-DATA-TO-SLOTS BUNDLE.
  `FinalA1SlotsAtConstGate` + `finalA1Slots_from_data` (+ the firing lemma `.fire`): a `Prop` bundle,
  stated at the ONE literal constant-radius gate `G₀ := constGate g gi hChr hK c`, of EXACTLY what the
  a₁ two-jet core `A1R6CoreAtGate.wide_a1_R6_core_AT_CONSTRADIUS` consumes BEYOND the J4-408 base bundle
  `ConstGateAssembly.ConstGateAssemblyData` — namely the three per-gate analytic slots
  (`hDuhamel`/`hDConv`/`hCConv`) plus the geometry-gauge `htr` at the concrete Ricci.  ONE brick of the
  `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠⚠⚠ HONESTY FIREWALL — THIS FILE IS **NOT** `a₁ = R/6`. ⚠⚠⚠
  Nothing here proves anything new about `R/6`.  `FinalA1SlotsAtConstGate` is a CARRIER structure and
  `finalA1Slots_from_data` is a CONDITIONAL bundling: its three slot fields are the already-banked
  per-gate analytic slots (grouped as the ONE semantic package `A1R6SlotAdapters.A1R6GateSlots`, itself
  fed by the Duhamel census, the W1-free census, and the L2/F-pile — see `a1_R6_slots_AT_GATE`), and its
  `htr` field is `A1R6SlotAdapters.htr_adapter` re-exported at the concrete Ricci `ricci g gi · · 0`,
  which STILL rests on the labelled gauge input `hGauss`.  The firing lemma `.fire` merely APPLIES the
  banked core `wide_a1_R6_core_AT_CONSTRADIUS` to {a J4-408 base bundle, this bundle, the base geometry}
  and re-exports the core's CONDITIONAL two-jet.  Every hypothesis is satisfiable and NONE of them is the
  conclusion; no `sorry`, no `admit`, no `:= True`, no new axiom.  `a₁ = R/6` stays CONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SEMANTIC-CARRY GROUPS (Sol #18 — group as packages, never re-list raw census fields).
    • the three slots  ← the ONE semantic package `A1R6GateSlots g gi hChr hK c a b t`
                         (its own producer `a1_R6_slots_AT_GATE` bundles: the Duhamel census carry, the
                         W1-free census carry, and the L2/F-pile firings — so we do NOT re-list them);
    • the gauge `htr`  ← `htr_adapter` from the single labelled gauge carry `hGauss` (+ base geometry).

  ## THE J4-410 HANDOFF (the one-line public capstone this brick sets up).
  `.fire` already discharges the two-jet from {`ConstGateAssemblyData`, `FinalA1SlotsAtConstGate`, base
  geometry}.  J4-410 is then the one-line public wrap: assemble both bundles from semantic data
  (`constGate_assembly_data_from_data` + `finalA1Slots_from_data`) and hand them to `.fire`.  The public
  signature will expose exactly: the base geometry/gauge binders, the `ConstGateAssemblyData` carries,
  the `A1R6GateSlots` slot package, and the `hGauss` gauge carry — with the a₁ two-jet at
  `Ric := fun cc d => ricci g gi cc d 0` as conclusion.  ⚠ STILL CONDITIONAL — NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.A1R6CoreAtGate
import QIQTH.A1R6SlotAdapters
import QIQTH.ConstGateAssembly

open MeasureTheory Finset Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.HeatKernelA1 QIQTH.ExpMap
open QIQTH.A1R6CoreAtGate QIQTH.A1R6SlotAdapters QIQTH.ConstGateAssembly
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.FinalA1Slots

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (S1) THE BUNDLE — the core's slot + gauge antecedents at the literal gate.
    ############################################################################### -/

/-- **★★★ J4-409 (S1) — `FinalA1SlotsAtConstGate`.**  The `Prop` bundle of EXACTLY what the a₁ two-jet
    core `wide_a1_R6_core_AT_CONSTRADIUS` consumes BEYOND the J4-408 base bundle `ConstGateAssemblyData`,
    all at the ONE literal constant-radius gate `G₀ := constGate g gi hChr hK c` with cutoffs `(a,b)` and
    time `t`:
      • `hDuhamel`/`hDConv`/`hCConv` — the three per-gate analytic slots, VERBATIM the core's slot
        antecedents (equivalently the fields of `A1R6SlotAdapters.A1R6GateSlots`);
      • `htr` — the geometry-gauge identity at the CONCRETE Ricci `ricci g gi · · 0`, VERBATIM the shape
        `A1R6SlotAdapters.htr_adapter` supplies (which the core consumes at `Ric := ricci g gi · · 0`).
    A carrier structure only — every field is a CONDITIONAL analytic/geometric fact; ⚠ NOT `a₁ = R/6`. -/
structure FinalA1SlotsAtConstGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b t : ℝ) : Prop where
  /-- the `hDuhamel` slot at the literal gate (verbatim the core's antecedent). -/
  hDuhamel : heatOp g gi (fun u p q =>
        heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
          u p q) t 0 0
      = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) t 0 0
        + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
            t 0 0
  /-- the `hDConv` slot at the literal gate (verbatim the core's antecedent). -/
  hDConv : DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
        u 0 0) t
  /-- the `hCConv` slot at the literal gate (verbatim the core's antecedent). -/
  hCConv : ContDiffAt ℝ 2
      (fun p => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
        t p 0)
      (0 : Point n)
  /-- the geometry-gauge identity at the concrete Ricci `ricci g gi · · 0` (verbatim `htr_adapter`). -/
  htr : ∀ cc d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) cc 0)
      = -(2 / 3) * ricci g gi cc d 0

/-! ###############################################################################
    ### (S2) THE PER-FIELD BUILDERS (split into private lemmas, one banked call each).
    ############################################################################### -/

/-- **(field builder) `finalSlots_hDuhamel`.**  The `hDuhamel` field, from the ONE semantic slot package
    `A1R6GateSlots` (a projection — `A1R6GateSlots` is itself fed by the Duhamel census carry via
    `a1_R6_slots_AT_GATE`).  ⚠ NOT `a₁ = R/6`. -/
private theorem finalSlots_hDuhamel (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b t : ℝ)
    (slots : A1R6GateSlots g gi hChr hK c a b t) :
    heatOp g gi (fun u p q =>
        heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
          u p q) t 0 0
      = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) t 0 0
        + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
            t 0 0 :=
  slots.hDuhamel

/-- **(field builder) `finalSlots_hDConv`.**  The `hDConv` field, from the ONE semantic slot package
    `A1R6GateSlots` (a projection — fed by the W1-free census carry via `a1_R6_slots_AT_GATE`).
    ⚠ NOT `a₁ = R/6`. -/
private theorem finalSlots_hDConv (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b t : ℝ)
    (slots : A1R6GateSlots g gi hChr hK c a b t) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
        u 0 0) t :=
  slots.hDConv

/-- **(field builder) `finalSlots_hCConv`.**  The `hCConv` field, from the ONE semantic slot package
    `A1R6GateSlots` (a projection — fed by the L2/F-pile firings via `a1_R6_slots_AT_GATE`).
    ⚠ NOT `a₁ = R/6`. -/
private theorem finalSlots_hCConv (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b t : ℝ)
    (slots : A1R6GateSlots g gi hChr hK c a b t) :
    ContDiffAt ℝ 2
      (fun p => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
        t p 0)
      (0 : Point n) :=
  slots.hCConv

/-- **(field builder) `finalSlots_htr`.**  The `htr` field at the concrete Ricci `ricci g gi · · 0`,
    from the single labelled gauge carry `hGauss` (+ base geometry), via ONE banked call to
    `A1R6SlotAdapters.htr_adapter`.  The whole R3 Ricci-source coefficient still rests on `hGauss`.
    ⚠ NOT `a₁ = R/6`. -/
private theorem finalSlots_htr (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i)) :
    ∀ cc d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) cc 0)
      = -(2 / 3) * ricci g gi cc d 0 :=
  htr_adapter g gi hg hgsymm hgiC hgi0 hdg0 hGauss

/-- **★★★ J4-409 (S2) — `finalA1Slots_from_data`.**  Assembles the `FinalA1SlotsAtConstGate` bundle at
    the literal constant-radius gate `G₀ := constGate g gi hChr hK c` from the SEMANTIC packages: the ONE
    slot package `A1R6GateSlots` (which internally carries the Duhamel/W1-free/L2 censuses via
    `a1_R6_slots_AT_GATE`) closes the three slot fields as projections, and the single labelled gauge
    carry `hGauss` (+ base geometry) closes `htr` via `htr_adapter`.  No raw census field is re-listed;
    each field is closed by ONE banked call.  Every hypothesis is satisfiable; NONE is the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem finalA1Slots_from_data (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b t : ℝ)
    -- ── the three slots: the ONE semantic slot package (Duhamel + W1-free + L2 censuses bundled):
    (slots : A1R6GateSlots g gi hChr hK c a b t)
    -- ── the gauge `htr`: the single labelled gauge carry `hGauss` + base geometry:
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i)) :
    FinalA1SlotsAtConstGate g gi hChr hK c a b t where
  hDuhamel := finalSlots_hDuhamel g gi hChr hK c a b t slots
  hDConv := finalSlots_hDConv g gi hChr hK c a b t slots
  hCConv := finalSlots_hCConv g gi hChr hK c a b t slots
  htr := finalSlots_htr g gi hg hgsymm hgiC hgi0 hdg0 hGauss

/-! ###############################################################################
    ### (S3) THE FIRING LEMMA — apply the banked core to both bundles ⟹ the a₁ two-jet.
    ############################################################################### -/

/-- **★★★★ J4-409 (S3) — `FinalA1SlotsAtConstGate.fire`.**  Fires the a₁ two-jet at the literal
    constant-radius gate by applying the banked core `A1R6CoreAtGate.wide_a1_R6_core_AT_CONSTRADIUS`
    (at `Ric := fun cc d => ricci g gi cc d 0`) to {the J4-408 base bundle `ConstGateAssemblyData`
    (its `hpkgBound`/`hmemS0`/`hopenS0`/`hS1` fields), this bundle (its three slots + `htr`), and the
    base geometry/gauge binders}.  The `hEdom`/`hEz` fields of the base bundle are unused (the core
    re-derives non-positive-time vanishing internally).  A THIN apply-wrapper — leaves J4-410 as the
    one-line public wrap that assembles both bundles from semantic data.  ⚠ CONDITIONAL — NOT
    `a₁ = R/6`. -/
theorem FinalA1SlotsAtConstGate.fire (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    (base : ConstGateAssemblyData g gi hChr hK c a b C)
    (self : FinalA1SlotsAtConstGate g gi hChr hK c a b t) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) :=
  wide_a1_R6_core_AT_CONSTRADIUS g gi (fun cc d => ricci g gi cc d 0) t ht hn hChr hK hK0
    hg hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    self.htr base.hpkgBound base.hmemS0 base.hopenS0 base.hS1
    self.hDuhamel self.hDConv self.hCConv

end QIQTH.FinalA1Slots

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.FinalA1Slots
#print axioms finalA1Slots_from_data
#print axioms FinalA1SlotsAtConstGate.fire
end AxiomChecks
