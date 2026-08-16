/-
  MixedNormalFormOnGate — J4-790: the ON-GATE `mTerm`-form match for the concrete van-Vleck witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  per-base-point relabeling that turns the on-gate mixed Leibniz–Gaussian second field partial of the
  concrete gated van-Vleck witness (`ChartJetHessianMixed.witnessMixed_gate_eq`, already banked, and
  independently sympy-verified in `docs/qg_roadmap/SYMBOLIC_VERIFICATION_MIXED_SLIVER.md`) into the exact
  FOUR-term `mTerm0 + mTerm1 + mTerm1 + sTerm2` decomposition that the closed mixed sliver rate
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed`'s `hNormalForm` hypothesis is stated in.  It is the
  "on-gate mTerm-form match" — link 2 of J4-788's precisely-scoped chain to `hCConv`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MATCH (the point).  `KPrimeMixedPdBridge.kPrime_apply_single_eq_mixedPd` (J4-788) identifies the
  abstract CLM-derivative kernel's `j`-th component with the CONCRETE mixed second field partial in the
  `∂ⱼ∂ᵢ` orientation
      `pd (fun y => pd (fun x' => vanVleckGatedWitness … τ x' z) i y) j x`.
  This file proves that this concrete `∂ⱼ∂ᵢ` partial, ON the open gate (base `z ∈ K`, field point
  `x ∈ S z`, `0 < τ`), equals
      `mTerm0 V Pi Pj Q A0 τ x  +  mTerm1 V Pj (∂ᵢA) τ x  +  mTerm1 V Pi (∂ⱼA) τ x  +  sTerm2 V (∂ⱼ∂ᵢA) τ x`
  with the CONCRETE chart objects based at `z`, evaluated at the field point `x`:
      `V := uniformInverseChart g gi hC hK z` (the field-slot inverse chart based at `z`),
      `Pi`/`Pj` the `i`/`j`-line first jet FIELDS of `V`, `Q` the mixed second jet field
      (`Q x = ∂ⱼ(Pi ·) x`), and `A0 := chartFieldAmp … z`, `∂ᵢA`/`∂ⱼA`/`∂ⱼ∂ᵢA` its field partials.
  This is EXACTLY the `hNormalForm` shape of `witness_sliver2_xuniform_mixed`
  (`mTerm0 V Pi Pj Q A0 + mTerm1 V Pj A1i + mTerm1 V Pi A1j + sTerm2 V A2`), with the natural labeling
  `A1i = ∂ᵢA`, `A1j = ∂ⱼA`, `A2 = ∂ⱼ∂ᵢA`.

  ## HOW.  A pure rewrite: `witnessMixed_gate_eq` (applied with its formal `i`/`j` swapped, to realise the
  `∂ⱼ∂ᵢ` LHS) supplies the on-gate closed form in the abstract `gaussComp_amp_pd_pd_mixed` shape; unfolding
  the `mTerm0`/`mTerm1`/`sTerm2` definitions and a single `∑ Pi·Pj = ∑ Pj·Pi` symmetry (the mixed second
  moment is a PRODUCT of two first-moment factors, so the only content is commutativity of the cross-jet
  contraction) closes it by `ring`.  No new theory — this is the tedious-but-sound relabeling J4-788
  scoped, de-risked by the sympy cross-check (residual exactly `0`).

  Every hypothesis is a genuine first/second `x`-jet `HasDerivAt` or `PdiffAt` (the same class as
  `witnessMixed_gate_eq` / `NormalFormDischarge.hNormalForm_concrete`), satisfiable (the width-2 Gaussian
  chart model `Pi = eᵢ`, `Pj = eⱼ`, `Q = 0` is a genuinely-nonzero witness), and NONE is the conclusion.
  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetHessianMixed
import QIQTH.MixedSliverAssembly

open Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.ChartJetHessianMixed QIQTH.MixedSliverAssembly

namespace QIQTH.MixedNormalFormOnGate

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ J4-790 — `witnessMixed_gate_eq_mTerm` — THE ON-GATE `mTerm`-FORM MATCH.**  On the open gate
    (base `z ∈ K`, field point `x ∈ S z`, `0 < τ`), the concrete `∂ⱼ∂ᵢ` mixed second field partial of the
    gated van-Vleck witness (the orientation produced by `KPrimeMixedPdBridge.kPrime_apply_single_eq_mixedPd`)
    equals the FOUR-term mixed normal form in the EXACT `hNormalForm` shape of
    `MixedSliverXUniform.witness_sliver2_xuniform_mixed`:
      `pd (fun y => pd (fun x' => vanVleckGatedWitness … τ x' z) i y) j x`
        `= mTerm0 V Pi Pj Q A0 τ x + mTerm1 V Pj (∂ᵢA) τ x + mTerm1 V Pi (∂ⱼA) τ x + sTerm2 V (∂ⱼ∂ᵢA) τ x`,
    `V := uniformInverseChart g gi hC hK z`, `A0/∂ᵢA/∂ⱼA/∂ⱼ∂ᵢA := chartFieldAmp … z` and its field
    partials.  Route: `witnessMixed_gate_eq` (formal `i`/`j` swapped) + `mTerm0/mTerm1/sTerm2` unfold +
    the cross-jet contraction symmetry `∑ Pi·Pj = ∑ Pj·Pi` + `ring`.  NOT `a₁ = R/6`. -/
theorem witnessMixed_gate_eq_mTerm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (x : Point n) (hx : x ∈ S z)
    (Pi Pj Q : Point n → Point n)
    (hJetPi : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update y i s) k) (Pi y k) (y i))
    (hJetPj : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update y j s) k) (Pj y k) (y j))
    (hJetQ : ∀ k, HasDerivAt
      (fun s : ℝ => Pi (Function.update x j s) k) (Q x k) (x j))
    (hAmpDi : ∀ y, PdiffAt (chartFieldAmp g gi hC hK a b τ z) i y)
    (hAmpDj : PdiffAt (chartFieldAmp g gi hC hK a b τ z) j x)
    (hAmpD2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) j x) :
    pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y) j x
      = mTerm0 (uniformInverseChart g gi hC hK z) Pi Pj Q
            (fun (τ' : ℝ) (ζ : Point n) => chartFieldAmp g gi hC hK a b τ' z ζ) τ x
        + mTerm1 (uniformInverseChart g gi hC hK z) Pj
            (fun (τ' : ℝ) (ζ : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z) i ζ) τ x
        + mTerm1 (uniformInverseChart g gi hC hK z) Pi
            (fun (τ' : ℝ) (ζ : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z) j ζ) τ x
        + sTerm2 (uniformInverseChart g gi hC hK z)
            (fun (τ' : ℝ) (ζ : Point n) =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z) i y) j ζ) τ x := by
  -- The on-gate closed form in the abstract `gaussComp_amp_pd_pd_mixed` shape, `∂ⱼ∂ᵢ` orientation
  -- (`witnessMixed_gate_eq` with its formal `i`/`j` swapped).
  rw [witnessMixed_gate_eq g gi hC hK S a b j i τ hτ z hz hSopen x hx Pj Pi (Q x)
      hJetPj hJetPi hJetQ hAmpDi hAmpDj hAmpD2]
  simp only [mTerm0, mTerm1, sTerm2]
  -- the only content: the cross-jet contraction is symmetric.
  have hcross : (∑ k, Pi x k * Pj x k) = ∑ k, Pj x k * Pi x k :=
    Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [hcross]
  ring

end QIQTH.MixedNormalFormOnGate

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedNormalFormOnGate
#print axioms witnessMixed_gate_eq_mTerm
end AxiomChecks
