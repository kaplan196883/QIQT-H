/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# P4-derivation Stage 1 (operator level) — the modular Hamiltonian K as a genuine unbounded operator

`ModularHamiltonian.lean` delivered the spectral function `kFn(r) = log(r/(2−r))` of `K = −log Δ` and the
spectral-level generator identity `Δ^{it} = e^{−itK}` (`modChar_eq_exp_neg_kFn`), but flagged the *unbounded
operator* `K = kFn(R)` itself as the cited Tomita–Takesaki frontier ("needs unbounded-self-adjoint-operator
infrastructure Mathlib does not yet have").

That infrastructure is now built (`QIQTH/Spectral/UnboundedFC.lean`): the unbounded functional calculus
`∫ f dE` on a PVM.  Since `R = rvdRC S` is bounded self-adjoint, `E_R := PVM_of_selfAdjoint R` is a genuine
PVM and `rvdSpecMeasure S ξ = E_R.scalarMeasure ξ` *by definition*.  So the modular Hamiltonian is the
honest operator
```
   K = modK S := ∫ kFn dE_R    (= E_R.fcOp (kFn ∘ val)),
```
ℂ-linear and symmetric (from `fcOp`'s general properties), and **its expectation is the modular entropy**:
`⟨ξ, K ξ⟩ = ∫ kFn dμ_ξ = cgpEntropy S ξ` — the JLMS first law `⟨K⟩ = S` at the genuine **operator** level,
upgrading the spectral-level `cgpEntropy_eq_integral_kFn`.  Axiom-free.

Honest scope: `Δ^{it} = e^{−itK}` as an *operator* identity (the FC exponential law) is the remaining frontier;
this file delivers `K` as an operator and the operator-level first law.  Free-field / RvD standard-subspace
setting only.
-/
import QIQTH.ModularHamiltonian
import QIQTH.Spectral.UnboundedFC

namespace QIQTH.StandardSubspaceModular

open MeasureTheory QIQTH.SpectralTheorem QIQTH.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectrum-restricted modular symbol `kFn ∘ val` is measurable. -/
theorem kFn_val_measurable (S : StandardSubspace H) :
    Measurable (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val) :=
  kFn_measurable.comp measurable_subtype_coe

/-- **The modular Hamiltonian `K = −log Δ` as a genuine (unbounded) operator** `K = ∫ kFn dE_R`, via the
    unbounded functional calculus on `E_R = PVM_of_selfAdjoint (rvdRC S)`. -/
noncomputable def modK (S : StandardSubspace H) (ξ : H) : H :=
  (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcOp (kFn_val_measurable S) ξ

/-- **The operator-level first law `⟨K⟩ = S`:** the modular Hamiltonian's expectation in `ξ` is the modular
    (CGP) entropy, `⟨ξ, K ξ⟩ = cgpEntropy S ξ`.  Upgrades the spectral-level `cgpEntropy_eq_integral_kFn` to the
    genuine operator `K = modK S` (built by the unbounded functional calculus).  `hdom` = finite modular
    energy (`ξ` in `D(K)`); `hspec` = the separating/cyclic spectral condition. -/
theorem modK_inner_self (S : StandardSubspace H) (ξ : H)
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2) :
    inner ℂ ξ (modK S ξ) = ((cgpEntropy S ξ : ℝ) : ℂ) := by
  rw [modK, (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcOp_inner_self
      (kFn_val_measurable S) hdom, cgpEntropy_eq_integral_kFn S ξ hspec]
  simp only [rvdSpecMeasure]

end QIQTH.StandardSubspaceModular
