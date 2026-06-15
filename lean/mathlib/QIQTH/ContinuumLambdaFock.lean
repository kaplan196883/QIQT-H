/-
  ContinuumLambdaFock — Stage 4 capstone (foundation): the second-quantized
  free-field modular flow Γ(Δ^{it}) at the Fock level.

  The continuum λ-law (Stages 1–3) lives at the one-particle / standard-subspace
  level (the bounded RvD `modUnitary = Δ^{it}`).  The genuine FREE-FIELD flow is
  its second quantization `Γ(Δ^{it}) = secondQuantModFlowH`, already built on the
  Fock Hilbert space (`Fock/SecondQuantModularFlow.lean`).  This file records the
  Fock-level facts the λ-persistence story needs:

    * `secondQuantModFlowH_leftInv` / `_rightInv` / `_bijective` — the flow is a
      bijection with inverse the `(-t)`-flow; together with its isometry
      (`secondQuantModFlowH_isometry`) it is a SURJECTIVE ISOMETRY — the
      vector-level unitarity of `Γ(Δ^{it})`.  This is the foundation for
      repackaging `Γ(Δ^{it})` as a unitary `Fock H →L[ℂ] Fock H` (the step that
      would let `ContinuumLambda`'s `Ad(Δ^{it})` persistence machinery be replayed
      verbatim at the field level).
    * `secondQuantModFlowH_weyl_fixed` — **Γ-level persistence**: a Weyl record
      `W(u)` built on a one-particle mode `u` that is FIXED by the modular flow
      (`Δ^{it}u = u`) commutes with the second-quantized flow `Γ(Δ^{it})`.  The
      field-level statement that records on modular-invariant modes persist under
      the genuine free-field modular dynamics.

  Honest scope: `secondQuantModFlowH` is currently a `Fock H → Fock H` function
  (`Completion.map`), NOT yet a bounded operator with adjoint; the full
  `Ad(Γ(Δ^{it}))`-on-`B(Fock)` persistence (the finite/one-particle pattern of
  `LambdaPointer`/`ContinuumLambda`) awaits that repackaging, for which the
  bijective-isometry facts below are exactly the input.  Axiom-free.
-/

import QIQTH.Fock.SecondQuantModularFlow

namespace QIQTH.Fock

open QIQTH.StandardSubspaceModular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- ── Vector-level unitarity of Γ(Δ^{it}): inverse = the (-t)-flow ───────────-/

/-- `Γ(Δ^{-it}) ∘ Γ(Δ^{it}) = id`. -/
theorem secondQuantModFlowH_leftInv (S : StandardSubspace H) (t : ℝ) (x : Fock H) :
    secondQuantModFlowH S (-t) (secondQuantModFlowH S t x) = x := by
  rw [secondQuantModFlowH_add, neg_add_cancel, secondQuantModFlowH_zero]

/-- `Γ(Δ^{it}) ∘ Γ(Δ^{-it}) = id`. -/
theorem secondQuantModFlowH_rightInv (S : StandardSubspace H) (t : ℝ) (x : Fock H) :
    secondQuantModFlowH S t (secondQuantModFlowH S (-t) x) = x := by
  rw [secondQuantModFlowH_add, add_neg_cancel, secondQuantModFlowH_zero]

/-- **The free-field modular flow is a bijection**, with inverse the `(-t)`-flow.
    Together with `secondQuantModFlowH_isometry` it is a surjective isometry —
    the vector-level unitarity of `Γ(Δ^{it})`. -/
theorem secondQuantModFlowH_bijective (S : StandardSubspace H) (t : ℝ) :
    Function.Bijective (secondQuantModFlowH S t) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨secondQuantModFlowH S (-t),
     secondQuantModFlowH_leftInv S t, secondQuantModFlowH_rightInv S t⟩

/- ── Γ-level persistence: modular-fixed Weyl records commute with the flow ──-/

/-- **Γ-level persistence.**  If a one-particle mode `u` is fixed by the modular
    flow (`Δ^{it}u = u`), the second-quantized Weyl record `W(u)` commutes with
    the free-field modular flow `Γ(Δ^{it})`:
    `Γ(Δ^{it}) W(u) x = W(u) Γ(Δ^{it}) x`.  Records built on modular-invariant
    modes persist under the genuine free-field modular dynamics. -/
theorem secondQuantModFlowH_weyl_fixed (S : StandardSubspace H) (t : ℝ) (u : H)
    (hu : modUnitary S t u = u) (x : Fock H) :
    secondQuantModFlowH S t (weylH u x) = weylH u (secondQuantModFlowH S t x) := by
  rw [secondQuantModFlowH_weylH, hu]

/-- **Audit conclusion (Stage 4 capstone foundation).**  The free-field modular
    flow `Γ(Δ^{it})` is a bijective isometry (vector-level unitarity, inverse =
    the `(-t)`-flow), and Weyl records on modular-fixed modes commute with it.
    NO project axioms.  The full `Ad(Γ)`-on-`B(Fock)` persistence awaits
    repackaging `Γ(Δ^{it})` as a unitary `Fock H →L[ℂ] Fock H`, enabled by these
    facts. -/
theorem continuumLambdaFock_audit : True := trivial

end QIQTH.Fock
