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

/-- **`K` is symmetric** (`K = K†` on its domain): `⟨K ξ, η⟩ = ⟨ξ, K η⟩` — the reality/self-adjointness of the
    modular Hamiltonian, inherited from `fcOp_symmetric`. -/
theorem modK_symmetric (S : StandardSubspace H) {ξ η : H}
    (hξ : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hη : η ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val)) :
    inner ℂ (modK S ξ) η = inner ℂ ξ (modK S η) :=
  (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcOp_symmetric (kFn_val_measurable S) hξ hη

/-- **`K` is additive** on its domain. -/
theorem modK_add (S : StandardSubspace H) {ξ η : H}
    (hξ : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hη : η ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hξη : ξ + η ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val)) :
    modK S (ξ + η) = modK S ξ + modK S η :=
  (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcOp_add (kFn_val_measurable S) hξ hη hξη

/-- **`K` is `ℂ`-homogeneous** on its domain. -/
theorem modK_smul (S : StandardSubspace H) (c : ℂ) {ξ : H}
    (hξ : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hcξ : c • ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val)) :
    modK S (c • ξ) = c • modK S ξ :=
  (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcOp_smul (kFn_val_measurable S) c hξ hcξ

/-- **The modular flow generator — the operator `Δ^{it} = e^{−itK}` pinned to the genuine modular Hamiltonian
    `K = modK`.**  The strongly-continuous one-parameter unitary flow `t ↦ boundedFC(e^{it·kFn}(R)) ξ` —
    which on the spectrum `(0,2)` is `modChar(−t) = Δ^{−it}` (by `modChar_eq_exp_neg_kFn`) — has Stone generator
    `i·modK = iK`:
    `d/dt (Δ^{−it} ξ)|₀ = i·K ξ`,  i.e.  `Δ^{it} = e^{−itK}` at the **operator** level.
    This is a direct specialization of the general PVM Stone reconstruction
    `hasDerivAt_boundedFC_expSymbol` to `E_R = PVM_of_selfAdjoint (rvdRC S)` with symbol `kFn ∘ val`
    (so `K = ∫ kFn dE_R = modK`).  Discharges the operator-level half of the documented Tomita–Takesaki
    `Δ^{it}=e^{−itK}` frontier for the RvD free-field modular Hamiltonian.  Axiom-free. -/
theorem hasDerivAt_modFlow (S : StandardSubspace H) {ξ : H}
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val)) :
    HasDerivAt
      (fun t : ℝ => (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC
        (QIQTH.Spectral.ProjectionValuedMeasure.measurable_expSymbol (kFn_val_measurable S) t)
        zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_le t) ξ)
      (Complex.I • modK S ξ) 0 :=
  (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).hasDerivAt_boundedFC_expSymbol
    (kFn_val_measurable S) hdom

/-- **Strong continuity of the modular flow** (the Stone hypothesis for `Δ^{it}`): for `ξ` in the domain of
    `K = modK`, the modular flow `t ↦ boundedFC(e^{it·kFn}(R)) ξ` (= `Δ^{−it} ξ` on the spectrum) is continuous
    at every `t₀`.  A direct specialization of `continuousAt_boundedFC_expSymbol'`; together with the group law
    and unitarity, this is the full `C₀`-unitary-group structure of the modular flow.  Axiom-free. -/
theorem continuousAt_modFlow (S : StandardSubspace H) {ξ : H}
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val)) (t₀ : ℝ) :
    ContinuousAt
      (fun t : ℝ => (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC
        (QIQTH.Spectral.ProjectionValuedMeasure.measurable_expSymbol (kFn_val_measurable S) t)
        zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_le t) ξ) t₀ :=
  (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).continuousAt_boundedFC_expSymbol'
    (kFn_val_measurable S) hdom t₀

/-- **The modular flow is unitary (norm-preserving):** `‖boundedFC(e^{it·kFn}(R)) ξ‖ = ‖ξ‖`, i.e. `Δ^{it}` is
    an isometry on every vector (a specialization of `norm_boundedFC_expSymbol`).  With the group law + generator
    + strong continuity, this completes the modular flow as a genuine `C₀` one-parameter **unitary** group.
    Axiom-free. -/
theorem norm_modFlow (S : StandardSubspace H) (t : ℝ) (ξ : H) :
    ‖(PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC
        (QIQTH.Spectral.ProjectionValuedMeasure.measurable_expSymbol (kFn_val_measurable S) t)
        zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_le t) ξ‖ = ‖ξ‖ :=
  (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).norm_boundedFC_expSymbol
    (kFn_val_measurable S) t ξ

/-- **The infinitesimal JLMS first law `d/dt⟨Δ^{it}⟩|₀ = i·S`:** the derivative at `t = 0` of the modular flow's
    diagonal matrix element `⟪ξ, Δ^{−it} ξ⟫ = ⟪ξ, boundedFC(e^{it·kFn}(R)) ξ⟫` is `i·S`, where `S = cgpEntropy S ξ`
    is the modular (CGP) entropy.  Combines the modular flow generator (`hasDerivAt_inner_boundedFC_expSymbol`)
    with the operator first law `⟨K⟩ = S` (`modK_inner_self`): `d/dt⟨ξ,Δ^{it}ξ⟩|₀ = i·⟨ξ,Kξ⟩ = i·S`.  This ties the
    `C₀` modular-flow Stone package directly to the entanglement entropy.  Axiom-free. -/
theorem hasDerivAt_modFlow_inner (S : StandardSubspace H) {ξ : H}
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2) :
    HasDerivAt
      (fun t : ℝ => inner ℂ ξ ((PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC
        (QIQTH.Spectral.ProjectionValuedMeasure.measurable_expSymbol (kFn_val_measurable S) t)
        zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_le t) ξ))
      (Complex.I * ((cgpEntropy S ξ : ℝ) : ℂ)) 0 := by
  have h := (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).hasDerivAt_inner_boundedFC_expSymbol
    (kFn_val_measurable S) hdom ξ
  have hval : inner ℂ ξ (Complex.I • (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcOp
        (kFn_val_measurable S) ξ) = Complex.I * ((cgpEntropy S ξ : ℝ) : ℂ) := by
    rw [inner_smul_right]
    congr 1
    exact modK_inner_self S ξ hdom hspec
  rwa [hval] at h

end QIQTH.StandardSubspaceModular
