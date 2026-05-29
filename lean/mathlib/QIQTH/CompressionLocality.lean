/-
  Compression-Locality Obstruction — projection can break commutativity.

  GPT-5.5-pro audit observation:

      Ambient commutativity `[A, B] = 0` does NOT imply restricted
      commutativity `[PAP, PBP] = 0` for a projection P (P² = P).
      The leakage identity:

          [PAP, PBP]  =  PB(1−P)AP  −  PA(1−P)BP.

      A non-local projection can manufacture apparent nonlocality
      from a locally commuting ambient theory.

  Why this matters for QIQT-H:

      Theorem 7's no-signaling rests on AQFT microcausality
      `[Â(D_A), Â(D_B)] = 0` for spacelike-separated diamonds.
      If the FQ-restricted dynamics introduces a projection `P` onto
      H_phys that does NOT respect spacelike separation, then the
      restricted observables may fail to commute even though the
      ambient ones do — breaking the locality input to Theorem 7.

      To preserve locality, the FQ projection must be local /
      isotonic / tensor-compatible: it must commute with the
      microcausality structure.  This is an implicit additional
      constraint on the framework's notion of "physical Hamiltonian
      restricted to H_phys".

  This module formalises the algebraic identity (purely ring-theoretic,
  no Mathlib operator-algebra needed) and isolates the constraint.
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NoncommRing

namespace QIQTH
namespace CompressionLocality

variable {R : Type*} [Ring R]

/-- The **compressed-commutator leakage identity**.

    For a projection P (P² = P) and any A, B in a (possibly
    non-commutative) ring R with [A, B] = 0:

        (PAP)(PBP) − (PBP)(PAP)
          = PB·(1−P)·AP − PA·(1−P)·BP. -/
theorem compressed_commutator_with_commute
    (P A B : R) (hP : P * P = P) (hAB : A * B = B * A) :
    (P * A * P) * (P * B * P) - (P * B * P) * (P * A * P)
      = P * B * (1 - P) * A * P - P * A * (1 - P) * B * P := by
  -- Collapse P² on both LHS products.
  have h_left : (P * A * P) * (P * B * P) = P * A * P * B * P := by
    have e : (P * A * P) * (P * B * P) = P * A * (P * P) * B * P := by noncomm_ring
    rw [e, hP]
  have h_right : (P * B * P) * (P * A * P) = P * B * P * A * P := by
    have e : (P * B * P) * (P * A * P) = P * B * (P * P) * A * P := by noncomm_ring
    rw [e, hP]
  rw [h_left, h_right]
  -- Expand RHS using distributivity of (1 - P).
  have h_rhs_expand :
      P * B * (1 - P) * A * P - P * A * (1 - P) * B * P
      = P * B * A * P - P * B * P * A * P
        - (P * A * B * P - P * A * P * B * P) := by
    noncomm_ring
  rw [h_rhs_expand]
  -- Use [A,B] = 0 (i.e. AB = BA) to swap PBAP ↔ PABP.
  have h_swap : P * B * A * P = P * A * B * P := by
    have e1 : P * B * A * P = P * (B * A) * P := by noncomm_ring
    have e2 : P * A * B * P = P * (A * B) * P := by noncomm_ring
    rw [e1, e2, hAB]
  rw [h_swap]
  noncomm_ring

/-- **Audit corollary.**  When does compression preserve commutativity?

    The leakage identity shows that `[PAP, PBP] = 0` holds when the
    projection commutes with both A and B (the "local projection"
    case).  This isolates the constraint on a (FQ)-projection P that
    preserves the no-signaling chain of Theorem 7: the projection
    must commute with the local algebras' observables. -/
theorem compressed_commutator_zero_of_commuting_projection
    (P A B : R) (hP : P * P = P)
    (hAB : A * B = B * A)
    (hPA : P * A = A * P) (hPB : P * B = B * P) :
    (P * A * P) * (P * B * P) - (P * B * P) * (P * A * P) = 0 := by
  -- Under PA=AP and P²=P, the compression PAP collapses to AP. Similarly PBP = BP.
  have h_PAP : P * A * P = A * P := by
    calc P * A * P = (P * A) * P := by noncomm_ring
      _ = (A * P) * P := by rw [hPA]
      _ = A * (P * P) := by noncomm_ring
      _ = A * P := by rw [hP]
  have h_PBP : P * B * P = B * P := by
    calc P * B * P = (P * B) * P := by noncomm_ring
      _ = (B * P) * P := by rw [hPB]
      _ = B * (P * P) := by noncomm_ring
      _ = B * P := by rw [hP]
  rw [h_PAP, h_PBP]
  -- Goal: (A * P) * (B * P) - (B * P) * (A * P) = 0
  -- Pull P into the middle of A·B via the local-commuting projection, then [A,B]=0 closes.
  calc (A * P) * (B * P) - (B * P) * (A * P)
      = A * (P * B) * P - B * (P * A) * P := by noncomm_ring
    _ = A * (B * P) * P - B * (A * P) * P := by rw [hPB, hPA]
    _ = A * B * (P * P) - B * A * (P * P) := by noncomm_ring
    _ = A * B * P - B * A * P := by rw [hP]
    _ = (A * B) * P - (B * A) * P := by noncomm_ring
    _ = (B * A) * P - (B * A) * P := by rw [hAB]
    _ = 0 := sub_self _

end CompressionLocality
end QIQTH
