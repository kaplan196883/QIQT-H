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

/-- **The real-valued (physical) first law `d/dt Im⟪ξ, Δ^{−it} ξ⟫|₀ = S`.**  Since the modular correlator's
    derivative `i·S` is purely imaginary, the entropy `S = cgpEntropy S ξ` is precisely the `t`-derivative of the
    **imaginary part** of `⟪ξ, Δ^{−it} ξ⟫` — a real observable.  This is the operator first law in its physical,
    real-valued form (the real part of the correlator is stationary at `t = 0`; the imaginary part carries `S`).
    Axiom-free. -/
theorem hasDerivAt_modFlow_inner_im (S : StandardSubspace H) {ξ : H}
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2) :
    HasDerivAt
      (fun t : ℝ => (inner ℂ ξ ((PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC
        (QIQTH.Spectral.ProjectionValuedMeasure.measurable_expSymbol (kFn_val_measurable S) t)
        zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_le t) ξ) : ℂ).im)
      (cgpEntropy S ξ) 0 := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_modFlow_inner S hdom hspec)
  simpa [Complex.mul_im] using h

/-- **The modular flow in the canonical `Δ^{it}=e^{−itK}` direction (generator `−iK`).**  The flow
    `t ↦ boundedFC(e^{it·(−kFn)}(R)) ξ` — which on the spectrum `(0,2)` is exactly `modChar(t) = Δ^{it}`
    (by `modChar_eq_exp_neg_kFn`, `e^{it·(−kFn r)} = e^{−(i·t·kFn r)} = modChar t r`) — has Stone generator
    `−i·modK = −iK`:  `d/dt(Δ^{it} ξ)|₀ = −i·K ξ`,  i.e. `Δ^{it}=e^{−itK}` literally.  Uses the symbol-linearity
    `fcOp_neg` (`∫(−kFn) dE = −modK`) on top of the general capstone.  Axiom-free. -/
theorem hasDerivAt_modChar (S : StandardSubspace H) {ξ : H}
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val)) :
    HasDerivAt
      (fun t : ℝ => (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC
        (QIQTH.Spectral.ProjectionValuedMeasure.measurable_expSymbol (kFn_val_measurable S).neg t)
        zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_le t) ξ)
      (-(Complex.I • modK S ξ)) 0 := by
  have hdom' : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => -kFn ω.val) := by
    rw [ProjectionValuedMeasure.mem_fcDomain, ProjectionValuedMeasure.fcEnergy_neg]
    exact ((PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).mem_fcDomain).mp hdom
  have h := (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).hasDerivAt_boundedFC_expSymbol
    (kFn_val_measurable S).neg hdom'
  have hval : Complex.I • (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcOp
      (kFn_val_measurable S).neg ξ
      = -(Complex.I • (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcOp
        (kFn_val_measurable S) ξ) := by
    rw [(PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcOp_neg (kFn_val_measurable S) hdom,
      smul_neg]
  rwa [hval] at h

/-- **The crossed-product modular unitary `modUnitary S t = Δ^{it}` is the FC of the `(−kFn)`-exponential.**
    `modUnitary` is `borelFC(modChar t) = (PVM_R).boundedFC(modSpecFun S t)`, and `modSpecFun S t ω = modChar t ω.val
    = e^{it·(−kFn ω.val)}` (by `modChar_eq_exp_neg_kFn` on the spectrum `(0,2)`; both equal `1` off it).  Identifies
    the crossed-product's `Δ^{it}` with the operator whose Stone generator is the modular Hamiltonian. -/
theorem modUnitary_eq (S : StandardSubspace H) (t : ℝ) :
    modUnitary S t = (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC
      (QIQTH.Spectral.ProjectionValuedMeasure.measurable_expSymbol (kFn_val_measurable S).neg t)
      zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_le t) := by
  have hsym : modSpecFun S t
      = fun ω : spectrum ℝ (rvdRC S) => Complex.exp (Complex.I * (t : ℂ) * ((-kFn ω.val : ℝ) : ℂ)) := by
    funext ω
    simp only [modSpecFun]
    by_cases hω : ω.val ∈ Set.Ioo (0 : ℝ) 2
    · rw [modChar_eq_exp_neg_kFn t hω]; congr 1; push_cast; ring
    · rw [modChar, Set.piecewise_eq_of_notMem _ _ _ hω]
      simp only [kFn, Set.piecewise_eq_of_notMem _ _ _ hω, neg_zero, Complex.ofReal_zero,
        mul_zero, Complex.exp_zero]
  rw [modUnitary, borelFC]
  exact (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC_congr _ _ _ _ _ _ hsym

/-- **The Stone generator of the crossed-product modular unitary:** `d/dt(modUnitary S t · ξ)|₀ = −i·K ξ`.
    The crossed-product's modular flow `Δ^{it} = modUnitary S t` (on which the modular automorphism
    `σ_t(a) = Δ^{it} a Δ^{−it}` and hence the crossed product `M ⋊_σ ℝ` are built) has Stone generator `−i·modK`.
    This **connects the unbounded-FC modular Hamiltonian `K = modK` to the crossed-product machinery** —
    `modUnitary_eq` identifies `Δ^{it}` with the `(−kFn)`-exponential FC, whose generator is `hasDerivAt_modChar`.
    Axiom-free. -/
theorem hasDerivAt_modUnitary (S : StandardSubspace H) {ξ : H}
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val)) :
    HasDerivAt (fun t : ℝ => modUnitary S t ξ) (-(Complex.I • modK S ξ)) 0 := by
  have heq : (fun t : ℝ => modUnitary S t ξ)
      = fun t : ℝ => (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC
        (QIQTH.Spectral.ProjectionValuedMeasure.measurable_expSymbol (kFn_val_measurable S).neg t)
        zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_le t) ξ := by
    funext t; rw [modUnitary_eq S t]
  rw [heq]
  exact hasDerivAt_modChar S hdom

/-- **Strong continuity of the crossed-product modular unitary `Δ^{it} = modUnitary S t`** (the last piece of its
    `C₀`-structure): for `ξ` in the domain of `K = modK`, `t ↦ modUnitary S t ξ` is continuous at every `t₀`.
    With the group law (`modUnitary_add`), unitarity (`modUnitary_unitary`) and the Stone generator `−iK`
    (`hasDerivAt_modUnitary`), the crossed-product's `Δ^{it}` is now a full `C₀` one-parameter unitary group with
    a *known* generator — exactly the Stone-theorem package the Wall/crossed product is built on.  Axiom-free. -/
theorem continuousAt_modUnitary (S : StandardSubspace H) {ξ : H}
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val)) (t₀ : ℝ) :
    ContinuousAt (fun t : ℝ => modUnitary S t ξ) t₀ := by
  have hdom' : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => -kFn ω.val) := by
    rw [ProjectionValuedMeasure.mem_fcDomain, ProjectionValuedMeasure.fcEnergy_neg]
    exact ((PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).mem_fcDomain).mp hdom
  have heq : (fun t : ℝ => modUnitary S t ξ)
      = fun t : ℝ => (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC
        (QIQTH.Spectral.ProjectionValuedMeasure.measurable_expSymbol (kFn_val_measurable S).neg t)
        zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_le t) ξ := by
    funext t; rw [modUnitary_eq S t]
  rw [heq]
  exact (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).continuousAt_boundedFC_expSymbol'
    (kFn_val_measurable S).neg hdom' t₀

end QIQTH.StandardSubspaceModular
