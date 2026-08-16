/-
  MixedSliverAmpBounds — J4-793: concrete discharge of the FOUR amplitude sup-bound hypotheses
  (`hA0bdd`, `hA1ibdd`, `hA1jbdd`, `hA2bdd`) of `MixedSliverXUniform.witness_sliver2_xuniform_mixed`
  at the CONCRETE gated chart amplitudes fed into `MixedNormalFormFull.witnessMixed_hNormalForm_full`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is one of the
  concrete "chart-surface hypothesis verification" steps (J4-788 sub-task 2): the sliver rate theorem
  `witness_sliver2_xuniform_mixed` carries four GLOBAL amplitude sup bounds `∀ τ, ∀ ζ, |A_ τ ζ| ≤ M_`.
  In the concrete mixed normal form (`witnessMixed_hNormalForm_full`) the amplitudes are the **`S`-GATED**
  chart amplitudes `gateAmp S z₀ (…)`, i.e. `Set.indicator (S z₀)`-restricted versions of `chartFieldAmp`
  and its field partials.

  ## THE KEY LOCALIZATION.  The gate `gateAmp` is exactly what converts the LOCAL amplitude suppliers
  (`AmplitudeFamilyDischarge.amp_bound_*`, which bound `chartFieldAmp` only on a ball / on the gate) into
  the GLOBAL bound the sliver demands: off the gate the gated amplitude is identically `0` (`≤ M` for any
  `M ≥ 0`), so a global uniform bound reduces to a bound ON THE GATE ONLY.  `gateAmp_abs_le_onGate`
  formalizes this reduction; `witnessMixed_amplitude_sup_bounds` packages the four sliver amplitude
  hypotheses at the concrete gated `chartFieldAmp`/partials, reducing them to the four on-gate base
  bounds (which are the natural output of the local continuity suppliers over a bounded gate).

  Every hypothesis is satisfiable and non-vacuous (`A ≡ 0`, `M = 0` gives both sides `0`; any bounded
  amplitude on the gate is a genuine witness), and none equals the conclusion.  No `sorry`, no new
  axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedNormalFormFull
import QIQTH.NormalFormDischarge

open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.MixedNormalFormFull

namespace QIQTH.MixedSliverAmpBounds

variable {n : ℕ}

/-- **★ `gateAmp_abs_le_onGate` — THE GATE-LOCALIZATION OF A SUP BOUND.**  If an amplitude `A` is
    bounded by `M ≥ 0` **only on the gate** `S z₀`, then its `S`-gated version `gateAmp S z₀ A` is
    bounded by `M` **globally** (at every field point `ζ` and every time `τ`).  Off the gate the gated
    amplitude is identically `0`; on the gate it equals `A`.  This is the exact reduction that turns the
    LOCAL amplitude suppliers into the GLOBAL sup bound `witness_sliver2_xuniform_mixed` demands.
    NOT `a₁ = R/6`. -/
theorem gateAmp_abs_le_onGate (S : Point n → Set (Point n)) (z₀ : Point n)
    (A : ℝ → Point n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ τ, ∀ w ∈ S z₀, |A τ w| ≤ M) :
    ∀ τ, ∀ ζ : Point n, |gateAmp S z₀ A τ ζ| ≤ M := by
  intro τ ζ
  by_cases hζ : ζ ∈ S z₀
  · rw [gateAmp_of_mem S z₀ A τ hζ]; exact hbdd τ ζ hζ
  · rw [gateAmp_of_notMem S z₀ A τ hζ]; simpa using hM

/-- **★★ J4-793 — `witnessMixed_amplitude_sup_bounds` — THE FOUR SLIVER AMPLITUDE HYPOTHESES DISCHARGED.**
    Supplies EXACTLY the four amplitude sup-bound hypotheses `hA0bdd`/`hA1ibdd`/`hA1jbdd`/`hA2bdd` of
    `MixedSliverXUniform.witness_sliver2_xuniform_mixed`, at the CONCRETE gated chart amplitudes fed into
    `MixedNormalFormFull.witnessMixed_hNormalForm_full`:
      • `A0  := gateAmp S z₀ (fun τ ζ => chartFieldAmp … z₀ ζ)`               — bound `M₀`;
      • `A1i := gateAmp S z₀ (fun τ ζ => pd (chartFieldAmp … z₀) i ζ)`         — bound `M₁i`;
      • `A1j := gateAmp S z₀ (fun τ ζ => pd (chartFieldAmp … z₀) j ζ)`         — bound `M₁j`;
      • `A2  := gateAmp S z₀ (fun τ ζ => pd (fun y => pd (chartFieldAmp …) i y) j ζ)` — bound `M₂`.
    Each is reduced (via `gateAmp_abs_le_onGate`) to an ON-GATE base bound — the natural output of the
    local continuity suppliers (`AmplitudeFamilyDischarge.amp_bound_*`) over the (bounded) gate.
    NOT `a₁ = R/6`. -/
theorem witnessMixed_amplitude_sup_bounds
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b : ℝ) (i j : Fin n) (z₀ : Point n)
    (M₀ M₁i M₁j M₂ : ℝ) (hM₀ : 0 ≤ M₀) (hM₁i : 0 ≤ M₁i) (hM₁j : 0 ≤ M₁j) (hM₂ : 0 ≤ M₂)
    (hg0 : ∀ τ, ∀ w ∈ S z₀, |chartFieldAmp g gi hC hK a b τ z₀ w| ≤ M₀)
    (hg1i : ∀ τ, ∀ w ∈ S z₀, |pd (chartFieldAmp g gi hC hK a b τ z₀) i w| ≤ M₁i)
    (hg1j : ∀ τ, ∀ w ∈ S z₀, |pd (chartFieldAmp g gi hC hK a b τ z₀) j w| ≤ M₁j)
    (hg2 : ∀ τ, ∀ w ∈ S z₀,
      |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) j w| ≤ M₂) :
    (∀ τ, ∀ ζ : Point n,
        |gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') τ ζ| ≤ M₀)
    ∧ (∀ τ, ∀ ζ : Point n,
        |gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
            pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ') τ ζ| ≤ M₁i)
    ∧ (∀ τ, ∀ ζ : Point n,
        |gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
            pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ') τ ζ| ≤ M₁j)
    ∧ (∀ τ, ∀ ζ : Point n,
        |gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
            pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ') τ ζ| ≤ M₂) :=
  ⟨gateAmp_abs_le_onGate S z₀ _ M₀ hM₀ hg0,
   gateAmp_abs_le_onGate S z₀ _ M₁i hM₁i hg1i,
   gateAmp_abs_le_onGate S z₀ _ M₁j hM₁j hg1j,
   gateAmp_abs_le_onGate S z₀ _ M₂ hM₂ hg2⟩

end QIQTH.MixedSliverAmpBounds

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverAmpBounds
#print axioms gateAmp_abs_le_onGate
#print axioms witnessMixed_amplitude_sup_bounds
end AxiomChecks
