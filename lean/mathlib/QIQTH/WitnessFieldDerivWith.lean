/-
  WitnessFieldDerivWith — J4-1157: Phase 2, Task A of the chart-parametric rebuild campaign
  (dispatch 2 of the newly-authorized full rebuild; per `gpt-5.6-sol`'s 33rd consult, 2026-08-24).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  genericizes `EngineInstantiation.witnessFieldDeriv` / `witnessFieldDeriv2` — the FIRST/SECOND
  concrete field-derivative kernels of the gated van-Vleck witness — over an ABSTRACT chart argument
  `W : Point n → Point n → Point n`, threading through Phase 1's `vanVleckGatedWitnessWith`
  (`VanVleckGatedWitnessWith.lean`, J4-1156) instead of the concrete `uniformInverseChart`-hardwired
  `vanVleckGatedWitness`.  Instantiates the generic pair twice: once at the OLD chart (bridged back to
  the existing `witnessFieldDeriv`/`witnessFieldDeriv2` via `rfl`-level compatibility theorems) and
  once at the NEW, jointly-measurable chart `uniformInverseChart'` (J4-1147).  This is Phase 2 Task A
  of `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md`: pure definitional threading, mirroring the
  Phase 1 shape exactly (`witnessFieldDeriv`/`witnessFieldDeriv2` call `vanVleckGatedWitness` DIRECTLY,
  with no other chart-dependence in their own bodies — confirmed by direct read,
  `EngineInstantiation.lean:103-119`). No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypotheses, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `witnessFieldDerivWith` — the chart-generic sibling of `witnessFieldDeriv`: the SAME
      `pd (x' ↦ vanVleckGatedWitnessWith … W τ x' z) i p` body, with the witness built from the
      GENERIC `vanVleckGatedWitnessWith` (Phase 1) instead of the concrete `vanVleckGatedWitness`.

    * `witnessFieldDerivWith_uniformInverseChart` — ★ THE COMPATIBILITY BRIDGE: instantiating the
      generic definition at `W := uniformInverseChart g gi hC hK` recovers the EXISTING
      `witnessFieldDeriv` literally (`rfl`).

    * `witnessFieldDeriv'` — the NEW-chart instantiation: `witnessFieldDerivWith` at
      `W := uniformInverseChart' g gi hC hK c`.

    * `witnessFieldDeriv2With` — the chart-generic sibling of `witnessFieldDeriv2`: the SAME
      `pd (x ↦ pd (x' ↦ vanVleckGatedWitnessWith … W τ x' z) i x) i p` body, generic in `W`.

    * `witnessFieldDeriv2With_uniformInverseChart` — ★ the analogous `rfl` compatibility bridge for the
      SECOND field-derivative kernel: `witnessFieldDeriv2With … (uniformInverseChart …) =
      witnessFieldDeriv2 …`.

    * `witnessFieldDeriv2'` — the NEW-chart instantiation: `witnessFieldDeriv2With` at
      `W := uniformInverseChart' g gi hC hK c`.

  ## WHAT THIS DOES NOT DO.
  This file does NOT prove any relationship between the primed kernels and the old ones beyond what the
  generic definitions trivially give — it does NOT claim global equality (false in general; the two
  charts agree only on a bounded tube image). It does NOT build the first genuine mathematical diamond
  connecting a primed witness derivative to `chartFieldAmp'`/`chartFieldAmpWith` (canary
  **C1 — FirstDerivativeDiamond**, target dispatch 5-7 per the plan) — that is the on-gate-formula
  analogue of `witnessFieldDeriv_gate_eq`/`witnessFieldDeriv_gate_abs_le` for the primed kernels, still
  ahead. This dispatch supplies only the definitional layer those theorems will be stated over. It does
  not touch the measurability/audit chain (Phase 4).

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.EngineInstantiation
import QIQTH.VanVleckGatedWitnessWith

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel
open QIQTH.ThetaMeasurableEmbedding
open scoped Interval Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ###############################################################################
    ### THE CHART-GENERIC SIBLINGS — `witnessFieldDerivWith` / `witnessFieldDeriv2With`.
    ############################################################################### -/

/-- **`witnessFieldDerivWith` — the chart-generic sibling of `witnessFieldDeriv`.**  Literally the
    same body, with the underlying gated witness built from `vanVleckGatedWitnessWith` (abstract chart
    `W`) instead of the concrete `vanVleckGatedWitness`. Pure data — no chart-property hypotheses
    attached. NOT `a₁ = R/6`. -/
noncomputable def witnessFieldDerivWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (W : Point n → Point n → Point n) : ℝ :=
  pd (fun x' : Point n => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z) i p

/-- **`witnessFieldDeriv2With` — the chart-generic sibling of `witnessFieldDeriv2`.**  Literally the
    same body, with the underlying gated witness built from `vanVleckGatedWitnessWith` (abstract chart
    `W`) instead of the concrete `vanVleckGatedWitness`. NOT `a₁ = R/6`. -/
noncomputable def witnessFieldDeriv2With (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (W : Point n → Point n → Point n) : ℝ :=
  pd (fun x : Point n =>
      pd (fun x' : Point n => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z) i x) i p

/-! ###############################################################################
    ### ★ THE COMPATIBILITY BRIDGES — old-chart instantiation recovers the old kernels verbatim.
    ############################################################################### -/

/-- **★ `witnessFieldDerivWith_uniformInverseChart` — the compatibility bridge.**  Instantiating the
    generic `witnessFieldDerivWith` at the OLD concrete chart `uniformInverseChart g gi hC hK` recovers
    the EXISTING `witnessFieldDeriv` literally.  Pure `rfl`.  NOT `a₁ = R/6`. -/
theorem witnessFieldDerivWith_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) :
    witnessFieldDerivWith g gi hC hK S a b i τ p z (uniformInverseChart g gi hC hK)
      = witnessFieldDeriv g gi hC hK S a b i τ p z := rfl

/-- **★ `witnessFieldDeriv2With_uniformInverseChart` — the compatibility bridge.**  Instantiating the
    generic `witnessFieldDeriv2With` at the OLD concrete chart `uniformInverseChart g gi hC hK`
    recovers the EXISTING `witnessFieldDeriv2` literally.  Pure `rfl`.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2With_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) :
    witnessFieldDeriv2With g gi hC hK S a b i τ p z (uniformInverseChart g gi hC hK)
      = witnessFieldDeriv2 g gi hC hK S a b i τ p z := rfl

/-! ###############################################################################
    ### THE NEW-CHART INSTANTIATIONS — `witnessFieldDeriv'` / `witnessFieldDeriv2'`.
    ############################################################################### -/

/-- **`witnessFieldDeriv'` — the NEW-chart instantiation.**  `witnessFieldDerivWith` at
    `W := uniformInverseChart' g gi hC hK c` (the derived-jointly-measurable chart, J4-1147/1148/1149),
    for a fixed tube radius `c`.  NOT globally equal to `witnessFieldDeriv`.  NOT `a₁ = R/6`. -/
noncomputable def witnessFieldDeriv' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (c : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) : ℝ :=
  witnessFieldDerivWith g gi hC hK S a b i τ p z (uniformInverseChart' g gi hC hK c)

/-- **`witnessFieldDeriv2'` — the NEW-chart instantiation.**  `witnessFieldDeriv2With` at
    `W := uniformInverseChart' g gi hC hK c`.  NOT globally equal to `witnessFieldDeriv2`.  NOT
    `a₁ = R/6`. -/
noncomputable def witnessFieldDeriv2' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (c : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) : ℝ :=
  witnessFieldDeriv2With g gi hC hK S a b i τ p z (uniformInverseChart' g gi hC hK c)

end QIQTH.HeatResidualBound

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms witnessFieldDerivWith
#print axioms witnessFieldDeriv2With
#print axioms witnessFieldDerivWith_uniformInverseChart
#print axioms witnessFieldDeriv2With_uniformInverseChart
#print axioms witnessFieldDeriv'
#print axioms witnessFieldDeriv2'
end AxiomChecks
