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

namespace QIQTH.Fock

open QIQTH.StandardSubspaceModular

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

end QIQTH.Fock
