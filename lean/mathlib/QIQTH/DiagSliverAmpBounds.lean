/-
  DiagSliverAmpBounds — J4-810: concrete discharge of the THREE amplitude sup-bound hypotheses
  (`hA0bdd`, `hA1bdd`, `hA2bdd`) of `XUniformSliverFull.witness_sliver2_xuniform` at the CONCRETE gated
  chart amplitudes fed into `DiagNormalFormFull.witnessDiag_hNormalForm_full` (J4-809).  The diagonal twin
  of `MixedSliverAmpBounds.witnessMixed_amplitude_sup_bounds` (J4-793).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the exact
  diagonal (`j := i`) specialisation of J4-793: the diagonal sliver rate
  `XUniformSliverFull.witness_sliver2_xuniform` carries THREE global amplitude sup bounds
  `∀ τ, ∀ ζ, |A_ τ ζ| ≤ M_`, at the **`S`-GATED** chart amplitudes that
  `DiagNormalFormFull.witnessDiag_hNormalForm_full` feeds it:
    • `A0 := gateAmp S z₀ (fun τ ζ => chartFieldAmp … z₀ ζ)`                        — bound `M₀`;
    • `A1 := gateAmp S z₀ (fun τ ζ => pd (chartFieldAmp … z₀) i ζ)`                 — bound `M₁`;
    • `A2 := gateAmp S z₀ (fun τ ζ => pd (fun y => pd (chartFieldAmp …) i y) i ζ)`  — bound `M₂`.
  These are exactly conjuncts 1, 2 and 4 of J4-793's four at `j := i` (the mixed `A2 = ∂ⱼ∂ᵢ chartFieldAmp`
  collapses to the diagonal `∂ᵢ∂ᵢ chartFieldAmp`, and the mixed `A1i = ∂ᵢ` is the diagonal `A1`).

  ## THE KEY LOCALIZATION (verbatim from J4-793).  `gateAmp` converts the LOCAL amplitude suppliers
  (`AmplitudeFamilyDischarge.amp_bound_*`, which bound `chartFieldAmp` only on the gate) into the GLOBAL
  bound the sliver demands: off the gate the gated amplitude is identically `0` (`≤ M` for `M ≥ 0`), so a
  global uniform bound reduces to an ON-GATE bound.  `MixedSliverAmpBounds.gateAmp_abs_le_onGate` (which is
  index-free) formalizes this reduction and is reused verbatim.

  Every hypothesis is satisfiable and non-vacuous (`A ≡ 0`, `M = 0` gives both sides `0`), and none equals
  the conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverAmpBounds
import QIQTH.DiagNormalFormFull

open QIQTH.Curvature QIQTH.HeatResidualBound
open QIQTH.MixedNormalFormFull QIQTH.MixedSliverAmpBounds

namespace QIQTH.DiagSliverAmpBounds

variable {n : ℕ}

/-- **★★ J4-810 — `witnessDiag_amplitude_sup_bounds` — THE THREE DIAGONAL SLIVER AMPLITUDE HYPOTHESES
    DISCHARGED.**  Supplies EXACTLY the three amplitude sup-bound hypotheses `hA0bdd`/`hA1bdd`/`hA2bdd` of
    `XUniformSliverFull.witness_sliver2_xuniform`, at the CONCRETE gated chart amplitudes fed into
    `DiagNormalFormFull.witnessDiag_hNormalForm_full`.  Each is reduced (via the index-free
    `MixedSliverAmpBounds.gateAmp_abs_le_onGate`) to an ON-GATE base bound — the natural output of the
    local continuity suppliers (`AmplitudeFamilyDischarge.amp_bound_*`) over the (bounded) gate.  The
    diagonal (`j := i`) specialisation of `MixedSliverAmpBounds.witnessMixed_amplitude_sup_bounds`.
    NOT `a₁ = R/6`. -/
theorem witnessDiag_amplitude_sup_bounds
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b : ℝ) (i : Fin n) (z₀ : Point n)
    (M₀ M₁ M₂ : ℝ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hg0 : ∀ τ, ∀ w ∈ S z₀, |chartFieldAmp g gi hC hK a b τ z₀ w| ≤ M₀)
    (hg1 : ∀ τ, ∀ w ∈ S z₀, |pd (chartFieldAmp g gi hC hK a b τ z₀) i w| ≤ M₁)
    (hg2 : ∀ τ, ∀ w ∈ S z₀,
      |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) i w| ≤ M₂) :
    (∀ τ, ∀ ζ : Point n,
        |gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') τ ζ| ≤ M₀)
    ∧ (∀ τ, ∀ ζ : Point n,
        |gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
            pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ') τ ζ| ≤ M₁)
    ∧ (∀ τ, ∀ ζ : Point n,
        |gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
            pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ') τ ζ| ≤ M₂) :=
  ⟨gateAmp_abs_le_onGate S z₀ _ M₀ hM₀ hg0,
   gateAmp_abs_le_onGate S z₀ _ M₁ hM₁ hg1,
   gateAmp_abs_le_onGate S z₀ _ M₂ hM₂ hg2⟩

end QIQTH.DiagSliverAmpBounds

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.DiagSliverAmpBounds
#print axioms witnessDiag_amplitude_sup_bounds
end AxiomChecks
