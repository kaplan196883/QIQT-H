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

/-- **Geometric sum of an `m`-th root of unity `≠ 1` vanishes**: `Σ_{b<m} w^b = 0`. The arithmetic
heart of every character-orthogonality relation: `geom_sum_eq` telescopes the sum to `(w^m−1)/(w−1)`,
and `w^m = 1` kills the numerator. -/
theorem geom_sum_root_eq_zero {w : ℂ} (hwm : w ^ m = 1) (hw1 : w ≠ 1) :
    ∑ b : Fin m, w ^ b.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => w ^ i) m, geom_sum_eq hw1 m, hwm, sub_self, zero_div]

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

/-- **Clock character orthogonality** — the entrywise engine of the clock (dephasing) twirl:
`Σ_b ω^{j·b}·conj(ω^{k·b}) = m·[j=k]`. Each summand factors as `w^b` with `w = ω^j·conj(ω^k)`, an
`m`-th root of unity that is `1` iff `j = k` (primitive-root injectivity). On the diagonal the sum is
`m`; off-diagonal it vanishes (`geom_sum_root_eq_zero`). This is exactly the relation that makes the
clock twirl `(1/m)Σ_b Z^b M (Z^b)⋆` project `M` onto its diagonal. -/
theorem clock_char_orthogonality {ω : ℂ} (hω : IsPrimitiveRoot ω m) (j k : Fin m) :
    ∑ b : Fin m, ω ^ (j.val * b.val) * (starRingEnd ℂ) (ω ^ (k.val * b.val))
      = if j = k then (m : ℂ) else 0 := by
  have hnsq : Complex.normSq ω = 1 := by
    rw [Complex.normSq_eq_norm_sq, hω.norm'_eq_one (NeZero.ne m), one_pow]
  -- each summand is `w^b` for `w = ω^j · conj(ω^k)`
  set w : ℂ := ω ^ j.val * (starRingEnd ℂ) (ω ^ k.val) with hwdef
  have hfac : ∀ b : Fin m,
      ω ^ (j.val * b.val) * (starRingEnd ℂ) (ω ^ (k.val * b.val)) = w ^ b.val := by
    intro b
    rw [hwdef, mul_pow, ← pow_mul, ← map_pow, ← pow_mul]
  simp_rw [hfac]
  by_cases hjk : j = k
  · subst hjk
    have hw1 : w = 1 := by
      rw [hwdef, mul_comm, ← Complex.normSq_eq_conj_mul_self, map_pow, hnsq, one_pow,
        Complex.ofReal_one]
    simp [hw1]
  · rw [if_neg hjk]
    refine geom_sum_root_eq_zero ?_ ?_
    · -- `w^m = 1`
      rw [hwdef, mul_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm j.val m, mul_comm k.val m,
        pow_mul, pow_mul]
      simp only [hω.pow_eq_one, one_pow, map_one, mul_one]
    · -- `w ≠ 1`: else `ω^j = ω^k`, forcing `j = k` by primitive-root injectivity
      intro hw1
      apply hjk
      apply Fin.ext
      apply hω.pow_inj j.isLt k.isLt
      have hk1 : (starRingEnd ℂ) (ω ^ k.val) * ω ^ k.val = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self, map_pow, hnsq, one_pow, Complex.ofReal_one]
      calc ω ^ j.val
          = ω ^ j.val * ((starRingEnd ℂ) (ω ^ k.val) * ω ^ k.val) := by rw [hk1, mul_one]
        _ = w * ω ^ k.val := by rw [hwdef]; ring
        _ = ω ^ k.val := by rw [hw1, one_mul]

end QIQTH.Entropy
