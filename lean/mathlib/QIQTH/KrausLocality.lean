/-
  Kraus / Lüders locality — generalization of `UnitarityLocality`.

  The unitary-dilation locality lemma covers Bob's reversible local
  operations.  This file extends to arbitrary finite-outcome Kraus
  channels: if every Kraus operator V_i ∈ Â(D_B) and the completeness
  relation Σ V_i^* V_i = 1 holds, then the non-selective Heisenberg
  channel

      Ψ(X) := Σ_i V_i^* X V_i

  fixes every Alice observable X ∈ Â(D_A).  The unitary case is the
  one-Kraus-operator special case; projective/Lüders measurement
  (V_i = P_i with Σ P_i = 1, P_i² = P_i, P_i^* = P_i) is another
  special case.
-/

import QIQTH.UnitarityLocality
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace QIQTH
namespace KrausLocality

open UnitarityLocality

variable {R : Type*} [Ring R] [StarRing R]

/-- **Kraus-channel locality.**  Given microcausality between A_A
    and A_B, a finite family of Kraus operators V : ι → R with each
    V i ∈ A_B and Σ_i V_i^* V_i = 1, the non-selective Heisenberg
    channel Σ_i V_i^* X V_i fixes any X ∈ A_A.

    Strategy: each summand V_i^* X V_i = X by the same
    microcausality + commutation argument as the unitary case
    (note: Σ V_i^* V_i = 1 is *not* needed term-by-term, only for
    the completeness check; the term-by-term identity uses only
    `V_i X = X V_i`).  Hence the sum equals Σ_i V_i^* V_i X =
    (Σ V_i^* V_i) X = 1·X = X. -/
theorem kraus_channel_aliceFixing
    {ι : Type*} (s : Finset ι)
    {A_A A_B : Set R} (hMicro : Microcausality A_A A_B)
    (V : ι → R) (hV_inB : ∀ i ∈ s, V i ∈ A_B)
    (hComplete : ∑ i ∈ s, star (V i) * V i = 1)
    (X : R) (hX_inA : X ∈ A_A) :
    ∑ i ∈ s, star (V i) * X * V i = X := by
  -- Rewrite each summand using microcausality: X * V i = V i * X.
  -- So V_i^* X V_i = V_i^* (X V_i) = V_i^* (V_i X) = (V_i^* V_i) X.
  have step : ∀ i ∈ s, star (V i) * X * V i = star (V i) * V i * X := by
    intro i hi
    calc star (V i) * X * V i
        = star (V i) * (X * V i) := by rw [mul_assoc]
      _ = star (V i) * (V i * X) := by rw [hMicro X hX_inA (V i) (hV_inB i hi)]
      _ = star (V i) * V i * X   := by rw [← mul_assoc]
  -- Hence Σ_i V_i^* X V_i = Σ_i (V_i^* V_i) X = (Σ V_i^* V_i) X = 1·X = X.
  calc ∑ i ∈ s, star (V i) * X * V i
      = ∑ i ∈ s, star (V i) * V i * X     := Finset.sum_congr rfl step
    _ = (∑ i ∈ s, star (V i) * V i) * X   := by rw [Finset.sum_mul]
    _ = 1 * X                              := by rw [hComplete]
    _ = X                                  := one_mul X

/-- **Projective / Lüders measurement is Alice-fixing.**
    Specialization of `kraus_channel_aliceFixing` to V_i = P_i with
    Σ P_i = 1 (no idempotence/self-adjointness needed for this
    statement, since the proof goes through `Σ P_i^* P_i = 1`
    which we take as a hypothesis). -/
theorem projective_aliceFixing
    {ι : Type*} (s : Finset ι)
    {A_A A_B : Set R} (hMicro : Microcausality A_A A_B)
    (P : ι → R) (hP_inB : ∀ i ∈ s, P i ∈ A_B)
    (hCompleteness : ∑ i ∈ s, star (P i) * P i = 1)
    (X : R) (hX_inA : X ∈ A_A) :
    ∑ i ∈ s, star (P i) * X * P i = X :=
  kraus_channel_aliceFixing s hMicro P hP_inB hCompleteness X hX_inA

/-- **Unitary case is the singleton Kraus channel.**  Specialization
    showing `UnitarityLocality.locality_of_conjugation` is the
    one-operator instance of `kraus_channel_aliceFixing`. -/
example
    {A_A A_B : Set R} (hMicro : Microcausality A_A A_B)
    {U : R} (hU_inB : U ∈ A_B) (hUnitary : star U * U = 1)
    {X : R} (hX_inA : X ∈ A_A) :
    star U * X * U = X := by
  -- Apply the Kraus lemma with the singleton family {⟨⟩ ↦ U}.
  have := kraus_channel_aliceFixing
    (ι := Unit) {()} hMicro (fun _ => U)
    (by intro i _; exact hU_inB)
    (by simp [hUnitary]) X hX_inA
  simpa using this

end KrausLocality
end QIQTH
