/-
  HbintFullyClosedCurved — the FULL discharge of the interior tube-cover `hbint` integrability leg at
  the genuinely-curved witness: the two ELEMENTARY residual carries of J4-983
  (`HbintRequant.hbint_bLtR0_closed_curved`) — the `BL`-continuity carry and the compact-`K` sup-bound
  carry — are DISCHARGED unconditionally, because the compact set is the SINGLETON `K = {0}`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the J4-983 residual).  `HbintRequant.hbint_bLtR0_closed_curved` (κ<0, 1≤n) produces gate
  parameters `0 < a < b < c` at the concrete flow-ball gate with the `b < r₀` opacity obstruction and
  the null-frontier carry BOTH already discharged (`K = {0}` ⟹ `volume (frontier K) = 0`), leaving the
  implication conclusion gated on exactly TWO elementary carries over the singleton `K = {0}`:
    • `hBLK`  : `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ContinuousOn (BL s) {0}`               (BL-continuity)
    • `hbnd`  : `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ∃ C, ∀ z ∈ {0}, ‖BL s z · (⨆ …)‖ ≤ C`  (compact-K sup-bound)
  BOTH are UNCONDITIONALLY TRUE on a singleton:
    • continuity on a singleton is automatic (`continuousOn_singleton`);
    • a function is bounded on a singleton by its value there (take `C := ‖BL s 0 · (⨆ …)‖`).
  Discharging them delivers the FULLY UNCONDITIONAL integrability of the interior tube-cover leg at the
  curved witness — no residual carries at all for this `hbint` route.

  ⚠ HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  the LAST elementary carries of ONE `hCConv` sub-leg (the J4-907 interior tube-cover `hbint` route),
  turning `hbint_bLtR0_closed_curved`'s gated conclusion into an UNCONDITIONAL integrability at the
  genuinely-curved witness.  It does NOT touch `hzmass` or the other `hCConv` legs, and does NOT bear on
  `hDuhamel`/`hDConv`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on {hDuhamel, hDConv, hCConv}.  No
  existing file is edited.
-/
import Mathlib
import QIQTH.HbintRequant

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.PullbackMetric
open QIQTH.HbintRequant
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.HbintFullyClosedCurved

variable {n : ℕ}

/-- A real-valued function is bounded on a singleton by its value there.  Used to discharge the
    compact-`K` sup-bound carry unconditionally at `K = {0}`. -/
theorem singleton_exists_bound {α : Type*} (h : α → ℝ) (a : α) :
    ∃ C : ℝ, ∀ z ∈ ({a} : Set α), h z ≤ C :=
  ⟨h a, fun z hz => le_of_eq (by rw [Set.mem_singleton_iff.mp hz])⟩

/-- **★★★ `hbint_fully_closed_curved`.**  THE FULL CLOSURE of the interior tube-cover `hbint`
    integrability leg at the genuinely-curved witness `g^κ = curvedRNCMetric κ` (`κ < 0`, `1 ≤ n`,
    `K = {0}`).  Off `HbintRequant.hbint_bLtR0_closed_curved` (which already discharges the `b < r₀`
    opacity obstruction and the null-frontier carry): its remaining TWO elementary carries — the
    `BL`-continuity carry `hBLK` and the compact-`K` sup-bound carry `hbnd` — are dischargeable
    UNCONDITIONALLY because `K = {0}` is a singleton (`continuousOn_singleton`; bound by the value at
    `0`).  The conclusion is therefore the FULLY UNCONDITIONAL integrability of the tube-cover leg at
    concrete gate parameters `0 < a < b < c`.

    NON-VACUOUS: inherits the satisfiable curved bundle of `hbint_bLtR0_closed_curved` (whose curved
    hypotheses are exactly the satisfiable curved bundle of `curvedRNC_heatOp_dom_pkg_prescribed`); the
    two discharged carries are theorems of singleton topology, adding no hypotheses.  NOT `a₁ = R/6` —
    this closes only the last carries of ONE `hCConv` sub-leg; `a₁ = R/6` remains CONDITIONAL on
    {hDuhamel, hDConv, hCConv}. -/
theorem hbint_fully_closed_curved (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z *
          (⨆ x : Point n,
            ‖fderiv ℝ (fun y => witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
              (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
                '' Metric.ball (0 : Point n) c) a b i (t - s) y z) x‖)) volume) := by
  obtain ⟨a, b, c, ha, hab, hbc, hcond⟩ :=
    hbint_bLtR0_closed_curved κ hκ hn hChr hw i t m BL
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  -- the two elementary carries, discharged unconditionally on the singleton `K = {0}`.
  refine hcond ?_ ?_
  · -- `hBLK`: continuity on a singleton is automatic.
    exact ae_of_all volume (fun s _ => continuousOn_singleton (BL s) 0)
  · -- `hbnd`: a function is bounded on a singleton by its value there.
    exact ae_of_all volume (fun s _ => singleton_exists_bound _ 0)

end QIQTH.HbintFullyClosedCurved

/-! ## Axiom check — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HbintFullyClosedCurved
#print axioms hbint_fully_closed_curved
end AxiomChecks
