/-
  Phase C — the RELATIVE MODULAR OPERATOR of a coherent state, and its Connes cocycle.

  For a coherent state `Ψ = W(f)Ω` relative to the vacuum `Ω`, over the standard-subspace algebra `M`
  (with `f` such that `W(f) ∈ M`), the relative modular operator is the Weyl-conjugate of the vacuum
  modular operator (Araki; the standard computation `Δ_{uΩ|Ω} = u Δ_Ω u⋆` for `u = W(f) ∈ M`):

      Δ_{W(f)Ω | Ω}^{it}  =  W(f) · Γ(Δ^{it}) · W(f)⋆     (with `W(f)⋆ = W(−f)`).

  This is `relModFlowH` — a bounded operator on the Fock Hilbert space, built entirely from the
  second-quantized vacuum modular flow `Γ(Δ^{it})` (`SecondQuantModularFlow`) and the Weyl operators
  (`WeylOp`).  No unbounded GNS / relative-modular construction is needed: the coherent-state structure
  makes the relative modular operator a bounded Weyl conjugate.

  Headline result — **the Connes cocycle of a coherent state is a product of Weyl operators:**

      (D ω_{W(f)Ω} : D ω_Ω)_t  =  Δ_{W(f)Ω|Ω}^{it} · Δ_Ω^{-it}  =  W(f) · W(−Δ^{it} f).

  This is the Araki/Connes formula for the cocycle of a coherent (quasi-free) excitation — it follows
  immediately from the Tomita covariance `Γ(Δ^{it}) W(−f) = W(−Δ^{it}f) Γ(Δ^{it})` (`secondQuantModFlowH_weylH`)
  and the group law of `Γ(Δ^{it})`.  Axiom-free.

  HONEST SCOPE: this is the relative modular flow / Connes cocycle for COHERENT states (the case where the
  relative modular operator is a bounded Weyl conjugate).  The full Araki relative entropy
  `S(ω_{W(f)Ω} ‖ ω_Ω) = −⟨Ω, log Δ_{Ω|W(f)Ω} Ω⟩` then reduces (Casini–Grillo–Pontello) to the one-particle
  `cgpEntropy` of `f`, already proved `≥ 0` in `ModularRelativeEntropy`.  General two-state relative modular
  operators (arbitrary normal states) remain the unbounded-GNS frontier.
-/

import QIQTH.Fock.SecondQuantModularFlow
import QIQTH.ModularRelativeEntropy

namespace QIQTH.Fock

open QIQTH.StandardSubspaceModular
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`W(f) W(−f) = id`** on the Fock Hilbert space (the unitarity inverse `W(f)⋆ = W(−f)`, lifted from
    the pre-level `weylPre_neg_cancel`). -/
theorem weylH_neg_cancel (f : H) (x : Fock H) : weylH f (weylH (-f) x) = x := by
  have hfun : (⇑(weylₗᵢ f)) ∘ (⇑(weylₗᵢ (-f))) = id := by
    funext φ
    show weylPre f (weylPre (-f) φ) = φ
    have h := weylPre_neg_cancel (-f) φ
    rwa [neg_neg] at h
  rw [weylH, weylH, ← Function.comp_apply (f := UniformSpace.Completion.map (weylₗᵢ f)),
      UniformSpace.Completion.map_comp (weylₗᵢ f).isometry.uniformContinuous
        (weylₗᵢ (-f)).isometry.uniformContinuous, hfun]
  exact congrFun UniformSpace.Completion.map_id x

/-- **The relative modular flow** `Δ_{W(f)Ω | Ω}^{it} = W(f) Γ(Δ^{it}) W(f)⋆` of the coherent state
    `W(f)Ω` relative to the vacuum — a bounded Weyl conjugate of the vacuum modular flow. -/
noncomputable def relModFlowH (S : StandardSubspace H) (t : ℝ) (f : H) : Fock H → Fock H :=
  fun x => weylH f (secondQuantModFlowH S t (weylH (-f) x))

/-- **`Δ_{rel}^{i·0} = id`** — the relative modular flow at `t = 0` is the identity. -/
theorem relModFlowH_zero (S : StandardSubspace H) (f : H) (x : Fock H) :
    relModFlowH S 0 f x = x := by
  rw [relModFlowH, secondQuantModFlowH_zero, weylH_neg_cancel]

/-- **★ THE CONNES COCYCLE OF A COHERENT STATE IS A PRODUCT OF WEYL OPERATORS:**
        `(D ω_{W(f)Ω} : D ω_Ω)_t  =  Δ_{W(f)Ω|Ω}^{it} · Δ_Ω^{-it}  =  W(f) · W(−Δ^{it} f)`.
    The defining cocycle of the relative modular flow against the vacuum modular flow collapses, by the
    Tomita covariance `Γ(Δ^{it}) W(−f) = W(−Δ^{it}f) Γ(Δ^{it})` and the group law `Γ(Δ^{it})Γ(Δ^{-it}) = 1`,
    to a product of two Weyl unitaries — the Araki/Connes formula for the cocycle of a coherent excitation. -/
theorem connesCocycle_eq (S : StandardSubspace H) (t : ℝ) (f : H) (x : Fock H) :
    relModFlowH S t f (secondQuantModFlowH S (-t) x)
      = weylH f (weylH (-(modUnitary S t f)) x) := by
  rw [relModFlowH, secondQuantModFlowH_weylH, map_neg]
  congr 2
  rw [secondQuantModFlowH_add, add_neg_cancel, secondQuantModFlowH_zero]

/-! ### The relative modular flow is a one-parameter group, and the Connes-cocycle chain rule -/

/-- **`W(−f) W(f) = id`** on the Fock Hilbert space. -/
theorem weylH_neg_cancel' (f : H) (x : Fock H) : weylH (-f) (weylH f x) = x := by
  have h := weylH_neg_cancel (-f) x
  rwa [neg_neg] at h

/-- **The relative modular flow is a one-parameter group:** `Δ_rel^{is} ∘ Δ_rel^{it} = Δ_rel^{i(s+t)}`.
    With `relModFlowH_zero` (`Δ_rel^{i·0} = id`), this makes `relModFlowH` a genuine one-parameter modular
    flow — the conjugate `W(f) Γ(Δ^{i·}) W(f)⋆` of the vacuum modular flow (the inner `W(f)⋆ W(f)` cancels). -/
theorem relModFlowH_add (S : StandardSubspace H) (s t : ℝ) (f : H) (x : Fock H) :
    relModFlowH S s f (relModFlowH S t f x) = relModFlowH S (s + t) f x := by
  rw [relModFlowH, relModFlowH, relModFlowH, weylH_neg_cancel', secondQuantModFlowH_add]

/-- **The Connes cocycle** `u_t = (D ω_{W(f)Ω} : D ω_Ω)_t = W(f) W(−Δ^{it} f)` in closed Weyl-product form
    (`= connesCocycle_eq`). -/
noncomputable def connesCocycleH (S : StandardSubspace H) (t : ℝ) (f : H) : Fock H → Fock H :=
  fun x => weylH f (weylH (-(modUnitary S t f)) x)

/-- **`u_0 = id`** — the Connes cocycle at `t = 0` is the identity. -/
theorem connesCocycleH_zero (S : StandardSubspace H) (f : H) (x : Fock H) :
    connesCocycleH S 0 f x = x := by
  rw [connesCocycleH, modUnitary_zero, ContinuousLinearMap.one_apply, weylH_neg_cancel]

/-- **★ THE CONNES-COCYCLE CHAIN RULE** `u_{s+t} = u_s · σ_s(u_t)`, where `σ_s = Ad(Γ(Δ^{is}))` is the
    vacuum modular automorphism — the defining identity of a genuine Connes cocycle (Connes' Radon–Nikodym
    theorem).  Here it is a clean algebraic consequence of the Tomita covariance and the group law: the
    middle `W(Δ^{is}f)⋆ W(Δ^{is}f)` cancels and `Δ^{is}Δ^{it}f = Δ^{i(s+t)}f`. -/
theorem connesCocycleH_chain (S : StandardSubspace H) (s t : ℝ) (f : H) (x : Fock H) :
    connesCocycleH S (s + t) f x
      = connesCocycleH S s f
          (secondQuantModFlowH S s (connesCocycleH S t f (secondQuantModFlowH S (-s) x))) := by
  simp only [connesCocycleH]
  rw [secondQuantModFlowH_weylH, secondQuantModFlowH_weylH, secondQuantModFlowH_add,
      add_neg_cancel, secondQuantModFlowH_zero, map_neg, ← ContinuousLinearMap.mul_apply,
      ← modUnitary_add, weylH_neg_cancel']

/-! ### The vacuum characteristic function — the generating function of the relative entropy

  The relative entropy `S(ω_{W(f)Ω} ‖ ω_Ω)` of the coherent state is encoded in the bounded vacuum matrix
  element of the relative modular flow.  This is the genuine bridge to the one-particle `cgpEntropy`: the
  `t`-derivative of the characteristic function at `t = 0` is `i · cgpEntropy(f)`. -/

/-- **★ THE VACUUM CHARACTERISTIC FUNCTION of the relative modular flow:**
        `⟨Ω, Δ_{W(f)Ω|Ω}^{it} Ω⟩ = exp( ⟨f, Δ^{it} f⟩ − ⟨f, f⟩ )`.
    A bounded, exact, computable generating function for the coherent-state relative entropy: since
    `⟨f, Δ^{it}f⟩ − ⟨f,f⟩ = ∫ (u_t(r) − 1) dμ^R_f` and `d/dt|₀ u_t(r) = i·log((2−r)/r) = i·entropyDensity(r)`,
    its derivative is `i·d/dt|₀ ⟨Ω,Δ_rel^{it}Ω⟩ = −∫ entropyDensity dμ^R_f = cgpEntropy(f)` — the one-particle
    relative entropy proved `≥ 0` in `ModularRelativeEntropy`.  Proof: push `relModFlowH` to the pre-Fock
    level (`map_coe`), where the coherent vector is `weylCoeff(−f,0)·weylCoeff(f,−Δ^{it}f)·e(f−Δ^{it}f)`, then
    evaluate `⟨Ω, ·⟩ = fockInner` and collapse the Weyl coefficients. -/
theorem relModFlow_vacuum_char (S : StandardSubspace H) (t : ℝ) (f : H) :
    inner ℂ (Fock.vacuum : Fock H) (relModFlowH S t f Fock.vacuum)
      = Complex.exp (⟪f, modUnitary S t f⟫_ℂ - ⟪f, f⟫_ℂ) := by
  have hexp : ∀ a b : H, inner ℂ (FockPre.expVec a : FockPre H) (FockPre.expVec b)
      = Complex.exp ⟪a, b⟫_ℂ := fun a b => FockPre.inner_expVec a b
  have h1 : relModFlowH S t f Fock.vacuum
      = ((weylPre f (secondQuantModFlow S t (weylPre (-f) (FockPre.expVec 0))) : FockPre H) : Fock H) := by
    simp only [relModFlowH, Fock.vacuum, Fock.expVec, weylH, secondQuantModFlowH]
    rw [UniformSpace.Completion.map_coe (weylₗᵢ (-f)).isometry.uniformContinuous,
        UniformSpace.Completion.map_coe (secondQuantModFlowₗᵢ S t).isometry.uniformContinuous,
        UniformSpace.Completion.map_coe (weylₗᵢ f).isometry.uniformContinuous]
    simp only [weylₗᵢ, secondQuantModFlowₗᵢ, LinearMap.coe_isometryOfInner]
  rw [h1, Fock.vacuum, Fock.expVec, UniformSpace.Completion.inner_coe,
      weylPre_expVec, zero_add, map_smul, secondQuantModFlow_expVec, map_neg, map_smul,
      weylPre_expVec, inner_smul_right, inner_smul_right, hexp, inner_zero_left, Complex.exp_zero,
      mul_one]
  unfold Weyl.weylCoeff
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_neg_left, inner_neg_right, inner_zero_right]
  ring

open MeasureTheory in
/-- **★★★ THE ENTROPY REDUCTION** `S(ω_{W(f)Ω} ‖ ω_Ω) = cgpEntropy(f)`, as a derivative theorem.
    In the regular regime (`σ(R) ⊆ [a,2−a]`), the vacuum matrix element of the relative modular flow has
    `t`-derivative `−i·cgpEntropy(f)` at `0`:
        `d/dt|₀ ⟨Ω, Δ_{W(f)Ω|Ω}^{it} Ω⟩ = −i·cgpEntropy(f)`,
    so the coherent-state Araki relative entropy `S = i·d/dt|₀ ⟨Ω, Δ_rel^{it} Ω⟩ = cgpEntropy(f)` — the
    one-particle CGP relative entropy, already proved `≥ 0` (`cgpEntropy_nonneg`).  This CLOSES the loop:
    the Fock-level relative entropy of a coherent excitation IS the one-particle entropy.  Chain rule on the
    characteristic function (`relModFlow_vacuum_char`) + differentiation of the matrix element
    (`hasDerivAt_inner_modUnitary`) + `∫ entropyDensity dμ = −cgpEntropy`. -/
theorem hasDerivAt_relModFlow_vacuum (S : StandardSubspace H) (f : H) {a : ℝ} (ha : 0 < a) (ha2 : a < 2)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : ℝ) ∧ (ω : ℝ) ≤ 2 - a) :
    HasDerivAt (fun t => inner ℂ (Fock.vacuum : Fock H) (relModFlowH S t f Fock.vacuum))
      (-Complex.I * (cgpEntropy S f : ℂ)) 0 := by
  have hd := hasDerivAt_inner_modUnitary S f ha ha2 hspec
  have hcgp : (∫ ω, (entropyDensity ((ω : spectrum ℝ (rvdRC S)) : ℝ) : ℂ) ∂(rvdSpecMeasure S f))
      = -(cgpEntropy S f : ℂ) := by
    rw [cgpEntropy, integral_complex_ofReal]; push_cast; ring
  rw [hcgp] at hd
  have hd2 : HasDerivAt (fun t => inner ℂ f (modUnitary S t f) - inner ℂ f f)
      (Complex.I * -(cgpEntropy S f : ℂ)) 0 := hd.sub_const _
  simp only [relModFlow_vacuum_char]
  have heq : -Complex.I * (cgpEntropy S f : ℂ)
      = Complex.exp (inner ℂ f (modUnitary S 0 f) - inner ℂ f f) * (Complex.I * -(cgpEntropy S f : ℂ)) := by
    rw [modUnitary_zero, ContinuousLinearMap.one_apply, sub_self, Complex.exp_zero, one_mul]; ring
  rw [heq]
  exact hd2.cexp

end QIQTH.Fock
