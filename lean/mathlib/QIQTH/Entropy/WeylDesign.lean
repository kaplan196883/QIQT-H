import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Matrix.PosDef

/-!
# Character orthogonality — the engine of the discrete-Weyl 1-design

Toward **partial-trace data processing** (the route `D(Tr₂ρ ‖ Tr₂σ) ≤ D(ρ‖σ)` of Carlen §5.7): the
complete depolarization of a tensor factor is realized as an average of conjugations by the **discrete
Weyl (clock–shift) unitaries**, a unitary 1-design. The arithmetic engine behind every 1-design identity
is **character orthogonality** for the `m`-th roots of unity:

  `Σ_{b=0}^{m-1} ω^{b·c} = m · [c ≡ 0]`,   `ω` a primitive `m`-th root of unity.

This file proves that orthogonality (the off-diagonal `c ≢ 0` vanishing, plus the diagonal `c ≡ 0`
evaluation) from Mathlib's `geom_sum_eq` and `IsPrimitiveRoot`. It is the reusable number-theoretic core
that the clock-twirl (`Σ_b Z^b M Z^{-b} = diag M`) and hence the full Weyl 1-design will consume.
Axiom-free.
-/

namespace QIQTH.Entropy

open Finset

variable {m : ℕ} [NeZero m]

/-- **Character orthogonality, off-diagonal case.** For a primitive `m`-th root of unity `ω` and a
nonzero residue `c : Fin m`, the character sum `Σ_{b<m} ω^{b·c}` vanishes. (`ω^c` is an `m`-th root of
unity `≠ 1`, so the geometric sum telescopes to `(ω^{cm}-1)/(ω^c-1) = 0`.) -/
theorem weyl_char_sum_eq_zero {ω : ℂ} (hω : IsPrimitiveRoot ω m) (c : Fin m) (hc : c ≠ 0) :
    ∑ b : Fin m, ω ^ (b.val * c.val) = 0 := by
  have hcval : c.val ≠ 0 := fun h => hc (Fin.ext h)
  -- `z = ω^c` is an `m`-th root of unity, and `z ≠ 1`.
  set z : ℂ := ω ^ c.val with hz
  have hzm : z ^ m = 1 := by rw [hz, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hz1 : z ≠ 1 := by
    rw [hz]; intro h
    have hdvd : m ∣ c.val := (hω.pow_eq_one_iff_dvd c.val).mp h
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hcval) hdvd) (not_le.mpr c.isLt)
  -- rewrite the character sum as a geometric sum and evaluate
  have hsum : ∑ b : Fin m, ω ^ (b.val * c.val) = ∑ b : Fin m, z ^ b.val :=
    Finset.sum_congr rfl (fun b _ => by rw [hz, ← pow_mul, mul_comm])
  rw [hsum, Fin.sum_univ_eq_sum_range (fun i => z ^ i) m, geom_sum_eq hz1 m, hzm, sub_self,
    zero_div]

/-- **Character orthogonality, full statement.** `Σ_{b<m} ω^{b·c} = m·[c=0]`: it is `m` on the diagonal
`c = 0` (every term is `1`) and `0` off-diagonal (`weyl_char_sum_eq_zero`). This is the orthogonality
relation that makes the clock twirl a projection onto the diagonal. -/
theorem weyl_char_sum {ω : ℂ} (hω : IsPrimitiveRoot ω m) (c : Fin m) :
    ∑ b : Fin m, ω ^ (b.val * c.val) = if c = 0 then (m : ℂ) else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [if_neg hc, weyl_char_sum_eq_zero hω c hc]

/-! ## The clock and shift Weyl unitaries -/

open Matrix

/-- **The clock operator** `Z = diag(1, ω, ω², …, ω^{m−1})` on `ℂ^m`. -/
noncomputable def clock (ω : ℂ) (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  diagonal (fun j => ω ^ j.val)

/-- **The shift operator** `X : |j⟩ ↦ |j+1 mod m⟩`, the cyclic permutation matrix. -/
noncomputable def shift (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  (finRotate m).permMatrix ℂ

/-- The clock operator is **unitary** (a diagonal of unit-modulus roots of unity). -/
theorem clock_mem_unitary {ω : ℂ} (hω : IsPrimitiveRoot ω m) :
    clock ω m ∈ unitary (Matrix (Fin m) (Fin m) ℂ) := by
  have hnsq : Complex.normSq ω = 1 := by
    rw [Complex.normSq_eq_norm_sq, hω.norm'_eq_one (NeZero.ne m), one_pow]
  have hdiag : ∀ j : Fin m, star (ω ^ j.val) * ω ^ j.val = 1 := by
    intro j
    rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, map_pow, hnsq, one_pow,
      Complex.ofReal_one]
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩ <;>
  · rw [clock, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    refine congrArg _ (funext fun j => ?_)
    first
      | exact hdiag j
      | (rw [mul_comm]; exact hdiag j)

/-- The shift operator is **unitary** (a permutation matrix). -/
theorem shift_mem_unitary : shift m ∈ unitary (Matrix (Fin m) (Fin m) ℂ) := by
  rw [Unitary.mem_iff, shift, star_eq_conjTranspose, conjTranspose_permMatrix]
  refine ⟨?_, ?_⟩ <;> simp [← permMatrix_mul, permMatrix_one]

end QIQTH.Entropy
