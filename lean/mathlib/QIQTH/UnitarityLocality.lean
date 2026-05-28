/-
  Closing the microcausality ⇒ locality gap in QIQT-H Theorem 7.

  In Theorem7.lean we axiomatize the `locality` field of `Setup`:
      Ψ y X = X        for X ∈ A_A.

  This file *derives* that axiom for the special (but standard) case
  where Bob's non-selective channel is given by conjugation by a
  unitary U_y ∈ A_B:
      Ψ y X := U_y^* X U_y.

  Inputs are the AQFT premises:
    · `commute_A_B`:  ∀ a ∈ A_A, ∀ b ∈ A_B,  a * b = b * a   (microcausality)
    · `hU_inB`:       U_y ∈ A_B                                (Bob-local unitary)
    · `hUnitary`:     U_y^* * U_y = 1                          (unitarity)
  Output (for any X ∈ A_A):
      U_y^* * X * U_y = X.
-/

import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Defs

namespace QIQTH
namespace UnitarityLocality

variable {R : Type*} [Ring R] [StarRing R]

/-- Microcausality between two subsets A_A, A_B ⊂ R: every pair of
    elements commutes.  In AQFT, this is the elementary algebraic
    content of [Â(D_A), Â(D_B)] = 0 for spacelike-separated diamonds. -/
def Microcausality (A_A A_B : Set R) : Prop :=
  ∀ a ∈ A_A, ∀ b ∈ A_B, a * b = b * a

/-- **Locality of conjugation by a Bob-local unitary.**

    Given microcausality between Alice's and Bob's local algebras,
    a unitary U ∈ A_B, and any X ∈ A_A, conjugation by U fixes X.

    This discharges the `locality` axiom of `Theorem7.Setup` in the
    common case where Bob's non-selective channel has unitary
    dilation Ψ(X) = U* X U.  -/
theorem locality_of_conjugation
    {A_A A_B : Set R} (hMicro : Microcausality A_A A_B)
    {U : R} (hU_inB : U ∈ A_B) (hUnitary : star U * U = 1)
    {X : R} (hX_inA : X ∈ A_A) :
    star U * X * U = X := by
  calc star U * X * U
      = star U * (X * U)   := by rw [mul_assoc]
    _ = star U * (U * X)   := by rw [hMicro X hX_inA U hU_inB]
    _ = (star U * U) * X   := by rw [← mul_assoc]
    _ = 1 * X              := by rw [hUnitary]
    _ = X                  := by rw [one_mul]

/-- Same statement packaged as "the conjugation map is the identity
    on A_A".  This is the form that plugs straight into the `locality`
    field of `Theorem7.Setup`. -/
theorem conj_identity_on_A
    {A_A A_B : Set R} (hMicro : Microcausality A_A A_B)
    {U : R} (hU_inB : U ∈ A_B) (hUnitary : star U * U = 1) :
    ∀ X ∈ A_A, (fun Y => star U * Y * U) X = X := by
  intro X hX
  exact locality_of_conjugation hMicro hU_inB hUnitary hX

end UnitarityLocality
end QIQTH
