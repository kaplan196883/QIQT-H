/-
  WitnessSpatialPartialsX — J4-476: GROUND THE witness-slice x-slot LEAVES `hpd1X` / `hpd2X` /
  `hDerivX` carried by the `htermBox` base-rung chain (J4-475 `XSlotBaseParts`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  continues the `htermBox` rung-grounding surface: `XSlotBaseParts` (J4-475) grounded the base-rung
  parts `hLapX` / `hDerivX` to the geometry inputs (`hgiC`, `hChr`) plus THREE varying-base
  witness-slice leaves — `hpd1X` / `hpd2X` (the x-slot FIRST / SECOND spatial partials of the witness
  at the VARYING base `p.2`, `z = 0` frozen) and `hDerivX` (the x-slot `∂_τ` slice at varying base).
  This brick grounds those THREE leaves ONE LEVEL DOWN — onto the GATE DICHOTOMY (off-gate vanishing /
  in-gate smooth-composite reduction) and the banked witness field-derivative theory.

  ── THE SLOT / BASE AUDIT (dont-undercredit).  The leaves are the gated witness
     `Wit = vanVleckGatedWitness g gi hChr hK S a b` differentiated in its FIRST spatial slot at the
     VARYING base `p.2`, with the SECOND spatial slot frozen at `0`:
       • `hpd1X k p = pd (fun q => Wit p.1 q 0) k p.2`;
       • `hpd2X i j p = pd (fun y => pd (fun q => Wit p.1 q 0) j y) i p.2`;
       • `hDerivX p = deriv (fun u => Wit u p.2 0) p.1`.
     THE COVERAGE CHECK.  `hpd1X` is DEFEQ the canonical amplitude field-derivative
     `witnessFieldDeriv g gi hChr hK S a b k p.1 p.2 0` (`hpd1X_eq_witnessFieldDeriv`), so it plugs
     directly into the J4-442/443 field-derivative theory.  ⚠ but the banked joint-continuity
     `UngatedChainRule.witnessFieldDeriv_jointContinuousOn` covers a DIFFERENT parameterization
     (`τ` FIXED, field point along the `update y i ·` direction, the SECOND slot `z` varying over `K`);
     the leaves here need `τ = p.1` VARYING, the field/base point `p.2` FULLY varying, `z = 0` FIXED.
     So the banked chain-rule joint continuity does NOT transport verbatim — these are genuine atoms.

  ── THE GATE DICHOTOMY (what LANDS unconditionally).  `Wit τ q 0 = gatedKernel K S H τ q 0`.  Off the
     gate the leaves VANISH (the partial / derivative of `0`):
       • OFF-CHART (`0 ∉ K`) the whole field-slice `q ↦ Wit τ q 0` is identically `0`, so `hpd1X` and
         `hpd2X` are `0` (`hpd1X_zero_of_notMem` / `hpd2X_zero_of_notMem`);
       • OFF-GATE at the base (`0 ∉ K ∨ x ∉ S 0`) the time-slice `u ↦ Wit u x 0` is identically `0`,
         so `hDerivX` is `0` (`hDerivX_zero_of_off_gate`).
     ⚠ THE GATE-BOUNDARY ISSUE.  The set-gate is `τ`-independent SPATIAL, evaluated at the varying base;
     on the census box `closedBall 0 R` it can FAIL for large `R`.  The honest split is in-gate (smooth
     composite) vs off-gate (`0`), with the BOUNDARY `∂(S 0)` the irreducible carry — the box census
     needs a gate-regularity gluing input, NOT dischargeable here.

  ── THE IN-GATE REDUCTIONS (genuine discharge to the smooth amplitude / banked parametrix).
       • `hDerivX_ingate_eq_param` — in-gate (`0 ∈ K`, `x ∈ S 0`) the `∂_τ` slice EQUALS the (constant-
         cutoff-scaled) `heatParametrix` `τ`-derivative at the FIXED chart image `W 0 x`, whose joint
         continuity is BANKED (`ParametrixPartsContinuity.heatParametrix_deriv_jointContinuousOn`).
       • `hpd1X_ingate_eq` — in-gate (`0 ∈ K`, `S 0 ∈ 𝓝 x`) the first spatial partial EQUALS the `pd`
         of the UNGATED smooth chart-composed composite (via the banked gate-transparency
         `UngatedChainRule.witnessFieldDeriv_eq_ungatedComposite_of_gate`).

  ── WHAT LANDS.
    • `hpd1X_eq_witnessFieldDeriv`       — ★ the canonical bridge (leaf = `witnessFieldDeriv`).
    • `witnessTimeSlice_zero_of_off_gate`, `hDerivX_zero_of_off_gate` — off-gate `∂_τ` vanishing.
    • `witnessFieldSlice_zero_of_notMem`, `hpd1X_zero_of_notMem`, `hpd2X_zero_of_notMem` — off-chart
        spatial-partial vanishing.
    • `witnessTimeSlice_ingate_eq`, `hDerivX_ingate_eq_param` — in-gate `∂_τ` = banked parametrix.
    • `hpd1X_ingate_eq`                  — in-gate first spatial partial = ungated smooth composite.
    • `witness_leaves_residuals` (+ intro) — the enumerated surviving surface (THE LEAVES LEDGER).

  NO `sorry`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.XSlotBaseParts
import QIQTH.UngatedChainRule

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LaplaceBeltrami
open QIQTH.HeatParametrixAnsatz QIQTH.HeatTransportRecursion
open QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.UngatedChainRule
open scoped Topology Interval BigOperators

namespace QIQTH.WitnessSpatialPartialsX

variable {n : ℕ}

/-! ###############################################################################
    ### (A) THE CANONICAL BRIDGE — the x-slot first spatial partial IS `witnessFieldDeriv`.
    ############################################################################### -/

/-- **★ `hpd1X_eq_witnessFieldDeriv`.**  THE CANONICAL BRIDGE.  The x-slot FIRST spatial partial of the
    gated witness at the VARYING base `x` (second slot frozen at `0`) is DEFEQ the canonical amplitude
    first field-derivative `witnessFieldDeriv`:
      `pd (fun q => Wit τ q 0) k x = witnessFieldDeriv g gi hChr hK S a b k τ x 0`.
    So the `hpd1X` leaf plugs DIRECTLY into the banked J4-442/443 field-derivative theory (the
    identification is `rfl` — `witnessFieldDeriv` unfolds to exactly this `pd`).  ⚠ NOT `a₁ = R/6`. -/
theorem hpd1X_eq_witnessFieldDeriv (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (τ : ℝ) (x : Point n) :
    pd (fun q => vanVleckGatedWitness g gi hChr hK S a b τ q 0) k x
      = witnessFieldDeriv g gi hChr hK S a b k τ x 0 := rfl

/-! ###############################################################################
    ### (B) THE OFF-GATE `∂_τ` VANISHING — the time-slice leg of `hDerivX`.
    ############################################################################### -/

/-- **`witnessTimeSlice_zero_of_off_gate`.**  OFF THE GATE at the base point `x` (`0 ∉ K` — the second
    slot leaves the chart — OR `x ∉ S 0` — the field point leaves the set-gate) the whole time-slice
    `u ↦ Wit u x 0` is identically `0`, since the set-gate is `τ`-independent
    (`gatedKernel_apply_of_notMem`).  ⚠ NOT `a₁ = R/6`. -/
theorem witnessTimeSlice_zero_of_off_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (x : Point n) (h : (0 : Point n) ∉ K ∨ x ∉ S (0 : Point n)) :
    (fun u : ℝ => vanVleckGatedWitness g gi hChr hK S a b u x 0) = fun _ => 0 := by
  funext u
  simp only [vanVleckGatedWitness]
  exact gatedKernel_apply_of_notMem K S _ u x 0 h

/-- **`hDerivX_zero_of_off_gate`.**  OFF THE GATE the x-slot `∂_τ` slice VANISHES: the time-slice is
    identically `0`, so its `deriv` is `0`.  The honest off-gate leg of the `hDerivX` leaf.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hDerivX_zero_of_off_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (x : Point n) (h : (0 : Point n) ∉ K ∨ x ∉ S (0 : Point n)) :
    deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u x 0) τ = 0 := by
  rw [witnessTimeSlice_zero_of_off_gate g gi hChr hK S a b x h]
  exact deriv_const τ 0

/-! ###############################################################################
    ### (C) THE OFF-CHART SPATIAL-PARTIAL VANISHING — the `hpd1X` / `hpd2X` legs.
    ############################################################################### -/

/-- **`witnessFieldSlice_zero_of_notMem`.**  OFF THE CHART (`0 ∉ K`, the frozen second slot) the whole
    field-slice `q ↦ Wit τ q 0` is identically `0` (`gatedKernel_apply_of_notMem`, `q`-uniformly).
    ⚠ NOT `a₁ = R/6`. -/
theorem witnessFieldSlice_zero_of_notMem (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (hK0 : (0 : Point n) ∉ K) :
    (fun q : Point n => vanVleckGatedWitness g gi hChr hK S a b τ q 0) = fun _ => 0 := by
  funext q
  simp only [vanVleckGatedWitness]
  exact gatedKernel_apply_of_notMem K S _ τ q 0 (Or.inl hK0)

/-- **`hpd1X_zero_of_notMem`.**  OFF THE CHART the x-slot FIRST spatial partial VANISHES (partial of the
    identically-zero field-slice).  The honest off-chart leg of `hpd1X`.  ⚠ NOT `a₁ = R/6`. -/
theorem hpd1X_zero_of_notMem (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (τ : ℝ) (x : Point n) (hK0 : (0 : Point n) ∉ K) :
    pd (fun q => vanVleckGatedWitness g gi hChr hK S a b τ q 0) k x = 0 := by
  rw [witnessFieldSlice_zero_of_notMem g gi hChr hK S a b τ hK0]
  exact pd_const 0 k x

/-- **`hpd2X_zero_of_notMem`.**  OFF THE CHART the x-slot SECOND spatial partial VANISHES (the inner
    partial of the identically-zero field-slice is `0`, hence so is the outer).  The honest off-chart
    leg of `hpd2X`.  ⚠ NOT `a₁ = R/6`. -/
theorem hpd2X_zero_of_notMem (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (x : Point n) (hK0 : (0 : Point n) ∉ K) :
    pd (fun y => pd (fun q => vanVleckGatedWitness g gi hChr hK S a b τ q 0) j y) i x = 0 := by
  have hz : (fun q => vanVleckGatedWitness g gi hChr hK S a b τ q 0) = fun _ => (0 : ℝ) :=
    witnessFieldSlice_zero_of_notMem g gi hChr hK S a b τ hK0
  have hinner :
      (fun y => pd (fun q => vanVleckGatedWitness g gi hChr hK S a b τ q 0) j y)
        = fun _ => (0 : ℝ) := by
    funext y; rw [hz]; exact pd_const 0 j y
  rw [hinner]; exact pd_const 0 i x

/-! ###############################################################################
    ### (D) THE IN-GATE `∂_τ` REDUCTION — the time-slice equals the banked parametrix `τ`-derivative.
    ############################################################################### -/

/-- **`witnessTimeSlice_ingate_eq`.**  IN THE GATE (`0 ∈ K`, `x ∈ S 0`) the witness time-slice EQUALS
    the (constant-cutoff-scaled) `heatParametrix` time-slice at the FIXED chart image `W 0 x`
    (`W = uniformInverseChart g gi hChr hK`), since the set-gate is `τ`-independent
    (`gatedKernel_apply_of_mem` for all `u`) and the ungated composite factors DEFEQ through the
    profile `radialCutoff · heatParametrix`.  ⚠ NOT `a₁ = R/6`. -/
theorem witnessTimeSlice_ingate_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (x : Point n) (hK0 : (0 : Point n) ∈ K) (hxS : x ∈ S (0 : Point n)) :
    (fun u : ℝ => vanVleckGatedWitness g gi hChr hK S a b u x 0)
      = fun u : ℝ => radialCutoff a b (uniformInverseChart g gi hChr hK 0 x)
          * heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) u
              (uniformInverseChart g gi hChr hK 0 x) := by
  funext u
  simp only [vanVleckGatedWitness]
  rw [gatedKernel_apply_of_mem K S _ u hK0 hxS]
  rfl

/-- **★ `hDerivX_ingate_eq_param`.**  IN THE GATE the x-slot `∂_τ` slice EQUALS the `deriv` of the
    (constant-cutoff-scaled) `heatParametrix` time-slice at the FIXED chart image — reducing the
    in-gate `hDerivX` leg to the BANKED parametrix `τ`-derivative
    (`ParametrixPartsContinuity.heatParametrix_deriv_jointContinuousOn`, whose box version is
    `NonLeviBoxContinuity.heatParametrix_deriv_t_continuousOn_box`).  ⚠ NOT `a₁ = R/6`. -/
theorem hDerivX_ingate_eq_param (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (x : Point n) (hK0 : (0 : Point n) ∈ K) (hxS : x ∈ S (0 : Point n)) :
    deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u x 0) τ
      = deriv (fun u => radialCutoff a b (uniformInverseChart g gi hChr hK 0 x)
          * heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) u
              (uniformInverseChart g gi hChr hK 0 x)) τ := by
  rw [witnessTimeSlice_ingate_eq g gi hChr hK S a b x hK0 hxS]

/-! ###############################################################################
    ### (E) THE IN-GATE SPATIAL-PARTIAL REDUCTION — the first partial = ungated smooth composite.
    ############################################################################### -/

/-- **★ `hpd1X_ingate_eq`.**  IN THE GATE (`0 ∈ K`, `S 0 ∈ 𝓝 x`) the x-slot FIRST spatial partial
    EQUALS the `pd` of the UNGATED smooth chart-composed composite `globalCutoffParametrixWitnessN`,
    via the canonical bridge (`hpd1X_eq_witnessFieldDeriv`) composed with the banked gate-transparency
    `UngatedChainRule.witnessFieldDeriv_eq_ungatedComposite_of_gate` (the gate germ +
    `pd_congr_of_eventuallyEq`).  This reduces the in-gate `hpd1X` leg to the SMOOTH amplitude — a `C^∞`
    manifold-profile ∘ chart object with NO gate.  ⚠ NOT `a₁ = R/6`. -/
theorem hpd1X_ingate_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (τ : ℝ) (x : Point n) (hK0 : (0 : Point n) ∈ K) (hgate : S (0 : Point n) ∈ nhds x) :
    pd (fun q => vanVleckGatedWitness g gi hChr hK S a b τ q 0) k x
      = pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hChr hK) τ x' 0) k x := by
  rw [hpd1X_eq_witnessFieldDeriv g gi hChr hK S a b k τ x]
  exact witnessFieldDeriv_eq_ungatedComposite_of_gate g gi hChr hK S a b k τ x 0 hK0 hgate

/-! ###############################################################################
    ### THE LEAVES LEDGER — the surviving surface after the three leaf groundings.
    ############################################################################### -/

/-- **`witness_leaves_residuals`.**  THE ENUMERATED SURVIVING SURFACE after the J4-476 leaf groundings.
    A genuine conjunction (non-vacuous plumbing witness); each conjunct SATISFIABLE, none the conclusion.

    THE LEAVES LEDGER (what remains carried in place of the three x-slot witness-slice leaves `hpd1X` /
    `hpd2X` / `hDerivX` of `XSlotBaseParts.xslot_residuals`):
      1. `hOffGate` — the OFF-GATE / OFF-CHART legs are DISCHARGED here (all `0`): `hDerivX` off-gate
         (`hDerivX_zero_of_off_gate`), `hpd1X` / `hpd2X` off-chart (`hpd1X_zero_of_notMem` /
         `hpd2X_zero_of_notMem`).  NOT carried — banked landings.
      2. `hInGate` — the IN-GATE legs are REDUCED to the smooth amplitude / banked parametrix:
         `hDerivX` → the `heatParametrix` `τ`-derivative at the fixed chart image
         (`hDerivX_ingate_eq_param`, banked joint continuity); `hpd1X` → the `pd` of the ungated
         `C^∞` composite (`hpd1X_ingate_eq`).  The surviving carry is the AMPLITUDE REGULARITY of those
         smooth objects (parametrix / chart smoothness bank) — genuinely-buried, satisfiable, NOT the
         conclusion.
      3. `hBoundary` — THE GATE-BOUNDARY GLUING.  The `τ`-independent spatial set-gate `S 0` evaluated
         at the varying base can fail on the census box `closedBall 0 R`; gluing the in-gate reduction
         to the off-gate `0` across the boundary `∂(S 0)` needs a gate-regularity input — the honest
         irreducible carry at this granularity (NOT dischargeable here; NOT the conclusion).
      4. `hGeom` — the geometry floor (`hgiC` / `hChr`), carried verbatim from `XSlotBaseParts`.

    ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly this surface. -/
def witness_leaves_residuals (hOffGate hInGate hBoundary hGeom : Prop) : Prop :=
  hOffGate ∧ hInGate ∧ hBoundary ∧ hGeom

/-- The leaves ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem witness_leaves_residuals_intro {hOffGate hInGate hBoundary hGeom : Prop}
    (h1 : hOffGate) (h2 : hInGate) (h3 : hBoundary) (h4 : hGeom) :
    witness_leaves_residuals hOffGate hInGate hBoundary hGeom :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.WitnessSpatialPartialsX

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.WitnessSpatialPartialsX.hpd1X_eq_witnessFieldDeriv
#print axioms QIQTH.WitnessSpatialPartialsX.witnessTimeSlice_zero_of_off_gate
#print axioms QIQTH.WitnessSpatialPartialsX.hDerivX_zero_of_off_gate
#print axioms QIQTH.WitnessSpatialPartialsX.witnessFieldSlice_zero_of_notMem
#print axioms QIQTH.WitnessSpatialPartialsX.hpd1X_zero_of_notMem
#print axioms QIQTH.WitnessSpatialPartialsX.hpd2X_zero_of_notMem
#print axioms QIQTH.WitnessSpatialPartialsX.witnessTimeSlice_ingate_eq
#print axioms QIQTH.WitnessSpatialPartialsX.hDerivX_ingate_eq_param
#print axioms QIQTH.WitnessSpatialPartialsX.hpd1X_ingate_eq
#print axioms QIQTH.WitnessSpatialPartialsX.witness_leaves_residuals_intro
