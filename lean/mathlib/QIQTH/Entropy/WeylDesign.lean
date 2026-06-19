import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Fin

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

end QIQTH.Entropy
