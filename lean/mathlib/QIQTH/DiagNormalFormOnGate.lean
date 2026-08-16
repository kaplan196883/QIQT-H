/-
  DiagNormalFormOnGate — the DIAGONAL (`∂ᵢ∂ᵢ`, same-index) `sTerm`-form on-gate match for the concrete
  van-Vleck witness.  The diagonal counterpart of `MixedNormalFormOnGate.witnessMixed_gate_eq_mTerm`
  (J4-790).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  per-base-point relabeling that turns the on-gate DIAGONAL Leibniz–Gaussian second field partial of the
  concrete gated van-Vleck witness (`SecondDerivEnvelope.witnessFieldDeriv2_gate_eq`, already banked)
  into the exact THREE-term `sTerm0 + sTerm1 + sTerm2` decomposition that the closed diagonal sliver rate
  `XUniformSliverFull.witness_sliver2_xuniform`'s `hNormalForm` hypothesis is stated in.  It is the
  "diagonal `sTerm`-form gate identity wired at the `kPrime` `D2H` level" flagged as the remaining
  diagonal-leg need at the end of J4-791/792 — the exact diagonal analogue of the mixed J4-790.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MATCH (the point).  `KPrimeDiagPdBridge.kPrime_apply_single_eq_diagPd` (J4-791) identifies the
  abstract CLM-derivative kernel's `i`-th (diagonal) basis component with the CONCRETE diagonal second
  field partial in the `∂ᵢ∂ᵢ` orientation
      `pd (fun y => pd (fun x' => vanVleckGatedWitness … τ x' z) i y) i x`.
  This file proves that this concrete `∂ᵢ∂ᵢ` partial, ON the open gate (base `z ∈ K`, field point
  `p ∈ S z`, `0 < τ`), equals
      `sTerm0 V P Q A0 τ p  +  sTerm1 V P (∂ᵢA) τ p  +  sTerm2 V (∂ᵢ∂ᵢA) τ p`
  with the CONCRETE chart objects based at `z`, evaluated at the field point `p`:
      `V := uniformInverseChart g gi hC hK z`, `P` the `i`-line first jet FIELD of `V`, `Q` its
      diagonal second jet field (`Q p = ∂ᵢ(P ·) p`), and `A0 := chartFieldAmp … z`, `∂ᵢA`/`∂ᵢ∂ᵢA` its
      field partials.  This is EXACTLY the `hNormalForm` shape of `witness_sliver2_xuniform`.

  ## HOW.  A pure rewrite: `witnessFieldDeriv2_gate_eq` supplies the on-gate closed form in the raw
  `gaussComp_amp_pd_pd` shape (`witnessFieldDeriv2 … = pd (pd witness i) i` definitionally); unfolding the
  `sTerm0`/`sTerm1`/`sTerm2` definitions and reconciling the ONE syntactic difference (`∑ P²` vs
  `∑ P·P`, `pow_two`) closes it.  The diagonal case is strictly SIMPLER than the mixed J4-790 (no
  cross-jet symmetry needed — the two gradient contributions already pre-merged into the single `2·(…)`
  `sTerm1`).  Sympy-cross-checked (residual exactly `0`).

  Every hypothesis is a genuine first/second `x`-jet `HasDerivAt` or `PdiffAt` (the same class as
  `witnessFieldDeriv2_gate_eq`), satisfiable (the width-2 Gaussian chart model `P = eᵢ`, `Q = 0` is a
  genuinely-nonzero witness), and NONE is the conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SecondDerivEnvelope
import QIQTH.SliverAssembly

open Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.SecondDerivEnvelope

namespace QIQTH.DiagNormalFormOnGate

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ `witnessDiag_gate_eq_sTerm` — THE ON-GATE DIAGONAL `sTerm`-FORM MATCH.**  On the open gate
    (base `z ∈ K`, field point `p ∈ S z`, `0 < τ`), the concrete `∂ᵢ∂ᵢ` diagonal second field partial of
    the gated van-Vleck witness (the orientation produced by
    `KPrimeDiagPdBridge.kPrime_apply_single_eq_diagPd`) equals the THREE-term diagonal normal form in the
    EXACT `hNormalForm` shape of `XUniformSliverFull.witness_sliver2_xuniform`:
      `pd (fun y => pd (fun x' => vanVleckGatedWitness … τ x' z) i y) i p`
        `= sTerm0 V P Q A0 τ p + sTerm1 V P (∂ᵢA) τ p + sTerm2 V (∂ᵢ∂ᵢA) τ p`,
    `V := uniformInverseChart g gi hC hK z`, `A0/∂ᵢA/∂ᵢ∂ᵢA := chartFieldAmp … z` and its field partials.
    Route: `witnessFieldDeriv2_gate_eq` + `sTerm0/sTerm1/sTerm2` unfold + the `∑ P² = ∑ P·P` reconciliation.
    The diagonal analogue of `MixedNormalFormOnGate.witnessMixed_gate_eq_mTerm` (J4-790).  NOT `a₁ = R/6`. -/
theorem witnessDiag_gate_eq_sTerm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (P Q : Point n → Point n)
    (hJetV : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hJetP : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update p i s) k) (Q p k) (p i))
    (hAmp1 : ∀ x, PdiffAt (chartFieldAmp g gi hC hK a b τ z) i x)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i p) :
    pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y) i p
      = sTerm0 (uniformInverseChart g gi hC hK z) P Q
            (fun (τ' : ℝ) (ζ : Point n) => chartFieldAmp g gi hC hK a b τ' z ζ) τ p
        + sTerm1 (uniformInverseChart g gi hC hK z) P
            (fun (τ' : ℝ) (ζ : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z) i ζ) τ p
        + sTerm2 (uniformInverseChart g gi hC hK z)
            (fun (τ' : ℝ) (ζ : Point n) =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z) i y) i ζ) τ p := by
  -- `pd (pd witness i) i p = witnessFieldDeriv2 … i τ p z` definitionally.
  show witnessFieldDeriv2 g gi hC hK S a b i τ p z = _
  rw [witnessFieldDeriv2_gate_eq g gi hC hK S a b i τ hτ z hz hSopen p hp P (Q p) hJetV hJetP
      hAmp1 hAmp2]
  simp only [sTerm0, sTerm1, sTerm2]
  -- the only syntactic difference: `∑ P p k ^ 2` (gate_eq) vs `∑ P p k * P p k` (sTerm0).
  have hsq : (∑ k, P p k ^ 2) = ∑ k, P p k * P p k :=
    Finset.sum_congr rfl (fun k _ => by rw [pow_two])
  rw [hsq]

end QIQTH.DiagNormalFormOnGate

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.DiagNormalFormOnGate
#print axioms witnessDiag_gate_eq_sTerm
end AxiomChecks
