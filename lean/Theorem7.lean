/-
  QIQT-H Theorem 7 — No-signaling from AQFT microcausality + locality

  ------------------------------------------------------------------
  Abstract algebraic formalization. No Mathlib dependency.
  Verify with:  lean Theorem7.lean
  ------------------------------------------------------------------

  Original statement (informal, from QIQT_Foundations_Paper §7.7
  and QIQT_Math §9B):

      For two spacelike-separated diamonds D_A, D_B in an AQFT net,
      let Alice perform a POVM {E^x_a} ⊂ Â(D_A) and Bob an instrument
      {Ψ^y_b} on Â(D_B) with non-selective completion Ψ^y = Σ_b Ψ^y_b.
      Then the QIQT-H prediction
              P(a | x, y) := ω(Ψ^{y*}(E^x_a))
      is independent of y, i.e. Alice's marginal does not depend on
      Bob's setting:
              P(a | x, y₁) = P(a | x, y₂).

  Two physical inputs feed the proof:

    (M)  Microcausality.  [Â(D_A), Â(D_B)] = 0  whenever D_A, D_B
         are spacelike separated.
    (L)  Locality of the non-selective channel.  Bob's non-selective
         Heisenberg channel Ψ^{y*} acts as the identity on Â(D_A).
         For a unitary-dilation instrument Ψ^{y*}(X) = U_y^* X U_y
         with U_y ∈ Â(D_B), (L) follows from (M) directly.

  Here we axiomatize (L) — which is the algebraic content that the
  proof actually consumes — and derive no-signaling in two lines.
  The reduction (M) ⇒ (L) for unitary-dilation instruments is a
  one-liner [Â(D_A), Â(D_B)] = 0 ⇒ U_y^* X U_y = X for X ∈ Â(D_A);
  see the comment block at the end of the file for the four-line
  derivation and a note on the Mathlib prerequisites it would need.
-/

namespace QIQTH
namespace Theorem7

/-- Abstract setup for the QIQT-H no-signaling theorem.
    All operator-algebraic machinery is encoded as a `Prop`-valued
    membership predicate `inA` (= "lives in Alice's subalgebra"). -/
structure Setup where
  /-- Carrier of the observable algebra. -/
  Obs : Type
  /-- Value type of the state (e.g. ℝ, ℂ; we need only equality). -/
  Val : Type
  /-- The state ω : Obs → Val. -/
  ω : Obs → Val
  /-- Alice's setting (input) labels. -/
  AliceSetting : Type
  /-- Alice's outcome labels. -/
  AliceOutcome : Type
  /-- Bob's setting (input) labels. -/
  BobSetting : Type
  /-- Alice's POVM effects, indexed by setting `x` and outcome `a`. -/
  E : AliceSetting → AliceOutcome → Obs
  /-- Bob's non-selective Heisenberg channel, one per Bob setting. -/
  Ψ : BobSetting → Obs → Obs
  /-- "Lives in Alice's local subalgebra Â(D_A)". -/
  inA : Obs → Prop
  /-- Effects are local to Alice. -/
  alice_effect_inA : ∀ (x : AliceSetting) (a : AliceOutcome), inA (E x a)
  /-- LOCALITY of Bob's non-selective channel:
      it pointwise fixes Alice's subalgebra.
      (Algebraic translation of AQFT microcausality for non-selective
      Bob instruments — see header.) -/
  locality : ∀ (y : BobSetting) (X : Obs), inA X → Ψ y X = X

namespace Setup
variable (S : Setup)

/-- The QIQT-H joint-experiment prediction (Heisenberg picture). -/
def P (x : S.AliceSetting) (a : S.AliceOutcome) (y : S.BobSetting) : S.Val :=
  S.ω (S.Ψ y (S.E x a))

/-- The "Alice alone" prediction — what Alice would compute if Bob were absent. -/
def PAlice (x : S.AliceSetting) (a : S.AliceOutcome) : S.Val :=
  S.ω (S.E x a)

/-- **QIQT-H Theorem 7 (no-signaling).**
    Alice's marginal coincides with the Alice-alone prediction;
    in particular it does not depend on Bob's setting `y`. -/
theorem no_signaling
    (x : S.AliceSetting) (a : S.AliceOutcome) (y : S.BobSetting) :
    S.P x a y = S.PAlice x a := by
  show S.ω (S.Ψ y (S.E x a)) = S.ω (S.E x a)
  rw [S.locality y (S.E x a) (S.alice_effect_inA x a)]

/-- Two Bob-settings yield identical Alice-marginals. -/
theorem alice_marginal_independent_of_bob
    (x : S.AliceSetting) (a : S.AliceOutcome) (y₁ y₂ : S.BobSetting) :
    S.P x a y₁ = S.P x a y₂ := by
  rw [S.no_signaling x a y₁, S.no_signaling x a y₂]

end Setup

/-
  --------------------------------------------------------------------
  Why we axiomatize `locality` rather than derive it from microcausality
  --------------------------------------------------------------------

  In the unitary-dilation form of a non-selective instrument we have
      Ψ^{y*}(X) = U_y^* X U_y     with     U_y ∈ Â(D_B).
  Microcausality says elements of Â(D_A) and Â(D_B) commute. So for
  any X ∈ Â(D_A):

      U_y^* X U_y
        = U_y^* (X U_y)            -- associativity
        = U_y^* (U_y X)            -- microcausality:  X U_y = U_y X
        = (U_y^* U_y) X            -- associativity
        = X                        -- unitarity:  U_y^* U_y = 1.

  This is a four-line algebraic proof — *given* the prerequisites:
  unital *-algebra structure on `Obs`, the relation U_y^* U_y = 1,
  and Â(D_A), Â(D_B) realized as subalgebras (not just `Prop`-valued
  membership predicates) with a real commutator law.

  Mathlib has `StarAlgebra` / `StarSubalgebra`, so the unital *-algebra
  layer is available; what's missing is the von-Neumann–algebra
  refinement (Type-classification, commutants, instruments) needed to
  *state* microcausality as `commutes : ∀ X ∈ A, Y ∈ B, X * Y = Y * X`
  in a way that hooks into the AQFT net structure. A future revision
  of this file could carry out the four-line proof inside Mathlib's
  `StarRing` once that machinery lands.
-/

end Theorem7
end QIQTH
