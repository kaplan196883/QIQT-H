/-
  DiagNormalFormFull — the FULL `∀ζ` DIAGONAL (`∂ᵢ∂ᵢ`, same-index) `hNormalForm` for the concrete
  gated van-Vleck witness, assembling the ON-gate `sTerm`-form match (`DiagNormalFormOnGate`, J4-795
  TASK A) with the OFF-gate reconciliation.  The diagonal twin of
  `MixedNormalFormFull.witnessMixed_hNormalForm_full` (J4-792).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the exact
  diagonal analogue of J4-792's off-gate reconciliation: the on-gate match
  `DiagNormalFormOnGate.witnessDiag_gate_eq_sTerm` establishes the three-term `sTerm` normal form ONLY on
  the open gate (`ζ ∈ S z₀`).  The closed diagonal sliver rate
  `XUniformSliverFull.witness_sliver2_xuniform` consumes its `hNormalForm` hypothesis POINTWISE at EVERY
  field point `ζ` (the `∫ z` integration variable), i.e. as an UNCONDITIONAL `∀ τ ∈ Ioo 0 τ₀, ∀ ζ`
  equality.  So the on-gate match alone does NOT supply it; this file closes the `∀ζ` gap.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE RECONCILIATION (identical mechanism to the mixed J4-792, one index instead of two).  Off the gate
  (`ζ ∉ S z₀`) the concrete witness partial is `0` (the witness is hard-gated: `gatedKernel` kills the
  field slot outside `S z₀`), derived from the off-gate value germ `hOffNhd` via the mixed germ lemma
  `MixedNormalFormFull.pd_pd_mixed_eq_zero_of_eventuallyZero` specialised to `j := i` (the diagonal
  orientation `∂ᵢ∂ᵢ`).  But `sTerm0` carries a NONZERO Gaussian `gaussDdim τ (V ζ)`, so for the raw chart
  amplitude `chartFieldAmp` the three-term sum would NOT vanish off-gate — a mismatch.  The fix, exactly
  as in J4-792: the amplitude fields fed into the `sTerm` decomposition must be the **`S`-GATED** versions
  (`MixedNormalFormFull.gateAmp`, vanishing off `S z₀`).  With the `Set.indicator`-gated amplitudes,
  off-gate ALL THREE amplitudes are `0`, so every `sTerm` collapses to `gaussDdim · … · 0 = 0`, matching
  the (also-`0`) witness partial.  On-gate the indicator is transparent (`Set.indicator_of_mem`), so the
  gated amplitude EQUALS `chartFieldAmp` and its field partials, and the three-term sum is exactly the
  J4-795 on-gate match.  Strictly SIMPLER than the mixed case (three terms, one gradient, one index — no
  cross-jet asymmetry).

  Every hypothesis is a genuine per-point chart/amplitude jet (`HasDerivAt`/`PdiffAt`, the same class as
  `witnessDiag_gate_eq_sTerm`) or the off-gate germ `hOffNhd` (the chart-surface residue, satisfiable e.g.
  when `S z₀ = Set.univ` or the witness `≡ 0`); all are satisfiable and non-vacuous, and NONE is the
  conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DiagNormalFormOnGate
import QIQTH.MixedNormalFormFull

open Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.DiagNormalFormOnGate QIQTH.MixedNormalFormFull

namespace QIQTH.DiagNormalFormFull

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ `witnessDiag_hNormalForm_full` — THE FULL `∀ζ` DIAGONAL `hNormalForm`.**  For the concrete gated
    van-Vleck witness at a fixed base `z₀ ∈ K`, the diagonal `∂ᵢ∂ᵢ` second field partial equals the
    THREE-term diagonal normal form at EVERY field point `ζ` and EVERY `τ ∈ Ioo 0 τ₀` — the EXACT
    unconditional `hNormalForm` shape that `XUniformSliverFull.witness_sliver2_xuniform` consumes, with the
    concrete chart `V := uniformInverseChart … z₀`, carried jets `P/Q`, and the **`S`-GATED** amplitude
    fields (`gateAmp S z₀` of `chartFieldAmp` and its `i`/diagonal-`i` field partials).
    ON gate (`ζ ∈ S z₀`): the gated amplitudes are transparent, and the equality IS the J4-795 on-gate
    match `witnessDiag_gate_eq_sTerm`.  OFF gate (`ζ ∉ S z₀`): the witness partial vanishes
    (`pd_pd_mixed_eq_zero_of_eventuallyZero` at `j := i` from the off-gate germ `hOffNhd`) and every gated
    amplitude vanishes (`gateAmp_of_notMem`), so both sides are `0`.  Carries the geometric off-gate germ
    `hOffNhd` (the chart-surface residue) and the per-point chart/amplitude jets — all satisfiable, none
    the conclusion.  The diagonal twin of `MixedNormalFormFull.witnessMixed_hNormalForm_full`.
    NOT `a₁ = R/6`. -/
theorem witnessDiag_hNormalForm_full (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ₀ : ℝ) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (P Q : Point n → Point n)
    (hJetV : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y i s) k) (P y k) (y i))
    (hJetQ : ∀ ζ : Point n, ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update ζ i s) k) (Q ζ k) (ζ i))
    (hAmpDi : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ y : Point n,
      PdiffAt (chartFieldAmp g gi hC hK a b τ z₀) i y)
    (hAmpD2 : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ ∈ S z₀,
      PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) i ζ)
    (hOffNhd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n, ζ ∉ S z₀ →
      ∀ᶠ w in 𝓝 ζ, vanVleckGatedWitness g gi hC hK S a b τ w z₀ = 0) :
    ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n,
      pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) i ζ
        = sTerm0 (uniformInverseChart g gi hC hK z₀) P Q
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ')) τ ζ
          + sTerm1 (uniformInverseChart g gi hC hK z₀) P
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) τ ζ
          + sTerm2 (uniformInverseChart g gi hC hK z₀)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ')) τ ζ := by
  intro τ hτIoo ζ
  have hτ : 0 < τ := hτIoo.1
  by_cases hζS : ζ ∈ S z₀
  · -- ON the gate: the gated amplitudes are transparent; use the J4-795 on-gate match.
    rw [witnessDiag_gate_eq_sTerm g gi hC hK S a b i τ hτ z₀ hz₀ hSopen ζ hζS P Q
        hJetV (hJetQ ζ) (hAmpDi τ hτIoo) (hAmpD2 τ hτIoo ζ hζS)]
    simp only [sTerm0, sTerm1, sTerm2, gateAmp, Set.indicator_of_mem hζS]
  · -- OFF the gate: witness partial is 0 (from `hOffNhd`); every gated amplitude is 0.
    rw [pd_pd_mixed_eq_zero_of_eventuallyZero
        (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i i ζ (hOffNhd τ hτIoo ζ hζS)]
    simp only [sTerm0, sTerm1, sTerm2, gateAmp, Set.indicator_of_notMem hζS,
      mul_zero, add_zero]

end QIQTH.DiagNormalFormFull

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.DiagNormalFormFull
#print axioms witnessDiag_hNormalForm_full
end AxiomChecks
