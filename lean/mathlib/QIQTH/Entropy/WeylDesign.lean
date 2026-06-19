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

/-- **Permutation conjugation of a diagonal is the relabeled diagonal**: `P_σ · diag d · P_σ⋆ =
diag(d ∘ σ)`. Conjugating a diagonal matrix by a permutation matrix permutes its diagonal entries —
the structural fact behind the shift twirl (the shift `X = P_{finRotate}` conjugation keeps a diagonal
diagonal, just cyclically relabeled). Proved by reading the conjugation as a double `submatrix`
relabeling (`toMatrix_toPEquiv_mul` / `mul_toMatrix_toPEquiv`) of `diag d`. -/
theorem perm_conj_diagonal (σ : Equiv.Perm (Fin m)) (d : Fin m → ℂ) :
    σ.permMatrix ℂ * diagonal d * (σ.permMatrix ℂ)ᴴ = diagonal (fun i => d (σ i)) := by
  rw [conjTranspose_permMatrix]
  simp only [Equiv.Perm.permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
    Function.comp_id, Function.id_comp,
    show ((σ⁻¹ : Equiv.Perm (Fin m)).symm) = σ from Equiv.symm_symm σ, submatrix_diagonal_equiv]
  rfl

/-- **Orbit sum over the cyclic shift.** Since `finRotate m` is an `m`-cycle, the powers
`σ⁰j, σ¹j, …, σ^{m-1}j` enumerate every index exactly once, so summing any `d` along the orbit of `j`
equals the full sum: `Σ_{a<m} d(σ^a j) = Σ_p d_p`. The orbit-covering fact behind the shift twirl. -/
theorem shift_orbit_sum (j : Fin m) (d : Fin m → ℂ) :
    ∑ a : Fin m, d ((finRotate m ^ a.val) j) = ∑ p, d p := by
  have hinj : Function.Injective (fun a : Fin m => (finRotate m ^ a.val) j) := by
    intro a b hab
    simp only at hab
    by_cases hm2 : 2 ≤ m
    · have hcyc := isCycle_finRotate_of_le hm2
      have hsupp : (finRotate m) j ≠ j := by
        rw [← Equiv.Perm.mem_support, support_finRotate_of_le hm2]; exact Finset.mem_univ j
      have hpow : finRotate m ^ a.val = finRotate m ^ b.val :=
        hcyc.pow_eq_pow_iff.mpr ⟨j, hsupp, hab⟩
      have hord : orderOf (finRotate m) = m := by
        rw [hcyc.orderOf, support_finRotate_of_le hm2, Finset.card_univ, Fintype.card_fin]
      exact Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr (hord.symm ▸ a.isLt))
        (Set.mem_Iio.mpr (hord.symm ▸ b.isLt)) hpow)
    · have hm1 : m = 1 := by
        have := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m); omega
      subst hm1; exact Subsingleton.elim a b
  exact Fintype.sum_bijective _ (Finite.injective_iff_bijective.mp hinj)
    (fun a => d ((finRotate m ^ a.val) j)) d (fun _ => rfl)

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

/-- The `k`-th power of the clock is the diagonal of `k`-fold characters: `Z^k = diag(ω^{i·k})`. -/
theorem clock_pow {ω : ℂ} (k : ℕ) :
    (clock ω m) ^ k = diagonal (fun i : Fin m => ω ^ (i.val * k)) := by
  rw [clock, diagonal_pow]
  refine congrArg _ (funext fun i => ?_)
  rw [Pi.pow_apply, ← pow_mul]

/-- **The clock twirl is the dephasing channel.** Averaging `M` over conjugation by all clock powers
projects `M` onto its diagonal: `(1/m) Σ_b Z^b M (Z^b)⋆ = diag(M)`. This is a **mixed-unitary channel**
(uniform weights `1/m` over the clock unitaries `Z^b`), and it kills every off-diagonal entry by clock
character orthogonality — the first half of the Weyl twirl (the shift twirl then mixes the diagonal to
maximally mixed, completing the depolarization `ρ ↦ (Tr₂ρ)⊗(I/m)`). -/
theorem clock_twirl {ω : ℂ} (hω : IsPrimitiveRoot ω m) (M : Matrix (Fin m) (Fin m) ℂ) :
    ∑ b : Fin m, (m : ℂ)⁻¹ • ((clock ω m) ^ b.val * M * ((clock ω m) ^ b.val)ᴴ)
      = diagonal (fun j => M j j) := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  ext j k
  rw [Matrix.sum_apply, diagonal_apply]
  -- each conjugated entry is `ω^{j·b}·M_{jk}·conj(ω^{k·b})`
  have hentry : ∀ b : Fin m,
      ((m : ℂ)⁻¹ • ((clock ω m) ^ b.val * M * ((clock ω m) ^ b.val)ᴴ)) j k
        = (m : ℂ)⁻¹ * (M j k * (ω ^ (j.val * b.val) * (starRingEnd ℂ) (ω ^ (k.val * b.val)))) := by
    intro b
    rw [Matrix.smul_apply]
    simp only [clock_pow]
    rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, smul_eq_mul]
    simp only [Pi.star_apply, starRingEnd_apply]
    ring
  simp_rw [hentry]
  rw [← Finset.mul_sum, ← Finset.mul_sum, clock_char_orthogonality hω j k]
  by_cases hjk : j = k
  · subst hjk; rw [if_pos rfl, if_pos rfl]; field_simp
  · rw [if_neg hjk, if_neg hjk, mul_zero, mul_zero]

/-- **The shift twirl mixes a diagonal to the maximally-mixed state.** Averaging a diagonal `diag d`
over conjugation by all cyclic-shift powers gives the uniform diagonal: `(1/m) Σ_a X^a (diag d) (X^a)⋆
= ((Σ_j d_j)/m) · I`. Each conjugation relabels the diagonal cyclically (`perm_conj_diagonal`), and
summing over the full cycle replaces every diagonal entry by the orbit sum `Σ_p d_p`
(`shift_orbit_sum`). Composing this with the clock twirl (dephasing) gives the complete depolarization
`M ↦ (Tr M/m)·I` — the full discrete-Weyl 1-design, a mixed-unitary channel. -/
theorem shift_twirl (d : Fin m → ℂ) :
    ∑ a : Fin m, (m : ℂ)⁻¹ • (((finRotate m) ^ a.val).permMatrix ℂ * diagonal d
        * (((finRotate m) ^ a.val).permMatrix ℂ)ᴴ)
      = ((m : ℂ)⁻¹ * ∑ p, d p) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  simp_rw [perm_conj_diagonal]
  ext i k
  rw [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp_rw [Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  by_cases hik : i = k
  · subst hik
    simp only [if_true, mul_one]
    rw [← Finset.mul_sum, shift_orbit_sum]
  · simp [hik]

/-- **The complete depolarizing channel as the Weyl twirl** (clock dephasing ∘ shift mixing). Averaging
`M` over conjugation by every Weyl unitary `W_{a,b} = X^a Z^b` — first dephasing by the clock
(`Σ_b Z^b M (Z^b)⋆ /m = diag M`), then mixing the resulting diagonal by the shift
(`Σ_a X^a (diag M) (X^a)⋆ /m = (Tr M/m)·I`) — maps `M` to the maximally-mixed `(Tr M/m)·I`. This is the
full discrete-Weyl 1-design (a mixed-unitary channel), the single-factor depolarization underlying the
factor-2 twirl `ρ ↦ (Tr₂ρ)⊗(I/m)` of the partial-trace DPI. -/
theorem weyl_depolarization {ω : ℂ} (hω : IsPrimitiveRoot ω m) (M : Matrix (Fin m) (Fin m) ℂ) :
    ∑ a : Fin m, (m : ℂ)⁻¹ • (((finRotate m) ^ a.val).permMatrix ℂ
        * (∑ b : Fin m, (m : ℂ)⁻¹ • ((clock ω m) ^ b.val * M * ((clock ω m) ^ b.val)ᴴ))
        * (((finRotate m) ^ a.val).permMatrix ℂ)ᴴ)
      = ((m : ℂ)⁻¹ * M.trace) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  simp_rw [clock_twirl hω]
  rw [shift_twirl]
  rfl

end QIQTH.Entropy
