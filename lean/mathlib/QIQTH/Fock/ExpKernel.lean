/-
  F2 (keystone) — the exponential kernel `K(f,g) = exp⟪f,g⟫` is positive semidefinite.

  This is the one hard analytic lemma of the Fock/CCR foundation (`FOCK_CCR_FOUNDATION_PLAN.md`,
  Phase F2; Parthasarathy §15 "Positive definite kernels", §19 "The Fock Spaces").  On it the entire
  symmetric (bosonic) Fock space is built: Mathlib's `RKHS.OfKernel` turns a positive-semidefinite
  kernel into a Hilbert space (Moore–Aronszajn), whose kernel functions are the **exponential vectors**
  `e(f)` with `⟪e(f), e(g)⟫ = exp⟪f,g⟫`.

  ## The proof
  We prove `exp⟪f,g⟫` PSD (for any finite family) from:
    • `Matrix.posSemidef_gram` — the Gram kernel `G(f,g)=⟪f,g⟫` is PSD;
    • the **Schur product theorem** `Matrix.PosSemidef.hadamard` — the entrywise product of PSD matrices
      is PSD, hence every entrywise power `G^{∘k}` (`hPow`) is PSD;
    • `exp⟪f,g⟫ = ∑ₖ ⟪f,g⟫ᵏ/k!` with `1/k! ≥ 0`, so the quadratic form `xᴴ·exp(G)·x` is a convergent
      sum of nonnegative terms `(k!)⁻¹·(xᴴ·G^{∘k}·x)`.

  This is the full mathematical content of positive-definiteness of the exponential kernel.  (The
  general infinite-index version that `RKHS.OfKernel` consumes is the finitely-supported restriction of
  this; that lift is the next increment.)  Axiom-free.
-/
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace QIQTH.Fock.ExpKernel

open Matrix Complex
open scoped ComplexOrder Matrix InnerProductSpace ComplexConjugate

variable {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### The complex exponential as its power series -/

/-- `exp z = ∑ₖ (k!)⁻¹ zᵏ`. -/
theorem exp_eq_tsum (z : ℂ) : Complex.exp z = ∑' k : ℕ, (k.factorial : ℂ)⁻¹ * z ^ k := by
  rw [Complex.exp_eq_exp_ℂ]
  simp only [NormedSpace.exp_eq_tsum ℂ, smul_eq_mul]

/-- The exponential series is summable. -/
theorem summable_exp_term (z : ℂ) : Summable fun k : ℕ => (k.factorial : ℂ)⁻¹ * z ^ k := by
  have := NormedSpace.expSeries_div_summable (𝔸 := ℂ) z
  simpa only [div_eq_inv_mul] using this

/-! ### Entrywise (Hadamard) powers of a matrix -/

/-- The entrywise (Hadamard) `k`-th power of a matrix: `(hPow M k) i j = (M i j)^k`. -/
def hPow (M : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => Matrix.of fun _ _ => 1
  | (k + 1) => M ⊙ hPow M k

@[simp] theorem hPow_apply (M : Matrix ι ι ℂ) (k : ℕ) (i j : ι) :
    hPow M k i j = (M i j) ^ k := by
  induction k with
  | zero => simp [hPow]
  | succ k ih => simp [hPow, Matrix.hadamard_apply, ih, pow_succ, mul_comm]

/-- The all-ones matrix is positive semidefinite (it is the Gram matrix of constant vectors). -/
theorem posSemidef_one [Finite ι] : (Matrix.of (fun _ _ => (1 : ℂ)) : Matrix ι ι ℂ).PosSemidef := by
  have h : (Matrix.of (fun _ _ => (1 : ℂ)) : Matrix ι ι ℂ) = gram ℂ (fun _ : ι => (1 : ℂ)) := by
    ext i j; simp [gram_apply]
  rw [h]; exact posSemidef_gram ℂ _

/-- Every entrywise power of a positive-semidefinite matrix is positive semidefinite
    (Schur product theorem, iterated). -/
theorem hPow_posSemidef [Finite ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (k : ℕ) :
    (hPow M k).PosSemidef := by
  induction k with
  | zero => exact posSemidef_one
  | succ k ih => exact hM.hadamard ih

/-! ### The exponential kernel -/

/-- The **exponential kernel** of a family `f : ι → H`: `expKernel f i j = exp⟪f i, f j⟫`. -/
noncomputable def expKernel (f : ι → H) : Matrix ι ι ℂ :=
  Matrix.of fun i j => Complex.exp ⟪f i, f j⟫_ℂ

@[simp] theorem expKernel_apply (f : ι → H) (i j : ι) :
    expKernel f i j = Complex.exp ⟪f i, f j⟫_ℂ := rfl

/-- The exponential kernel is Hermitian. -/
theorem expKernel_isHermitian (f : ι → H) : (expKernel f).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, expKernel_apply, RCLike.star_def]
  rw [← Complex.exp_conj, inner_conj_symm]

/-- The exponential kernel entry is the exponential series of the Gram entry. -/
theorem expKernel_eq_tsum (f : ι → H) (i j : ι) :
    expKernel f i j = ∑' k : ℕ, (k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j := by
  simp only [expKernel_apply, hPow_apply, gram_apply]
  exact exp_eq_tsum _

/-- A summable series of nonnegative complex numbers has nonnegative sum.  (`tsum_nonneg` itself
    needs `IsOrderedAddMonoid`, which `ℂ` lacks, so we reduce to the real and imaginary parts.) -/
theorem complex_tsum_nonneg {c : ℕ → ℂ} (hc : Summable c) (h : ∀ k, 0 ≤ c k) :
    0 ≤ ∑' k, c k := by
  have hre : ∀ k, 0 ≤ (c k).re := fun k => (Complex.nonneg_iff.mp (h k)).1
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · rw [Complex.re_tsum hc]; exact tsum_nonneg hre
  · rw [Complex.im_tsum hc]
    have him : ∀ k, (c k).im = 0 := fun k => ((Complex.nonneg_iff.mp (h k)).2).symm
    simp [him]

/-! ### The keystone: positive semidefiniteness -/

/-- **Keystone.** The exponential kernel `K(f,g) = exp⟪f,g⟫` is positive semidefinite.  This is the
    positive-definite-kernel hypothesis that turns the exponential vectors into an inner-product space,
    i.e. builds the symmetric (bosonic) Fock space. -/
theorem expKernel_posSemidef [Fintype ι] (f : ι → H) : (expKernel f).PosSemidef := by
  -- The quadratic form as an explicit double sum.
  have key : ∀ (M : Matrix ι ι ℂ) (x : ι → ℂ),
      star x ⬝ᵥ M *ᵥ x = ∑ i, ∑ j, conj (x i) * M i j * x j := by
    intro M x
    simp only [dotProduct, mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, mul_assoc]
  refine PosSemidef.of_dotProduct_mulVec_nonneg (expKernel_isHermitian f) (fun x => ?_)
  -- Per-`(i,j)` summability of the exponential series scaled by `conj (x i) * · * x j`.
  have hg : ∀ i j, Summable (fun k : ℕ =>
      conj (x i) * ((k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j) * x j) := by
    intro i j
    have hs : Summable (fun k : ℕ => (k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j) := by
      simpa only [hPow_apply, gram_apply] using summable_exp_term (⟪f i, f j⟫_ℂ)
    exact (hs.mul_left (conj (x i))).mul_right (x j)
  -- The quadratic form of the exp-kernel is the series of quadratic forms of the Hadamard powers.
  have hEq : star x ⬝ᵥ (expKernel f) *ᵥ x
      = ∑' k : ℕ, (k.factorial : ℂ)⁻¹ * (star x ⬝ᵥ hPow (gram ℂ f) k *ᵥ x) := by
    rw [key]
    have hentry : ∀ i j, conj (x i) * expKernel f i j * x j
        = ∑' k : ℕ, conj (x i) * ((k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j) * x j := by
      intro i j
      calc conj (x i) * expKernel f i j * x j
          = conj (x i) * (∑' k : ℕ, (k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j) * x j := by
            rw [expKernel_eq_tsum f i j]
        _ = (∑' k : ℕ, conj (x i) * ((k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j)) * x j := by
            rw [tsum_mul_left]
        _ = ∑' k : ℕ, conj (x i) * ((k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j) * x j := by
            rw [tsum_mul_right]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hentry i j))]
    have hinner : ∀ i, ∑ j, (∑' k : ℕ, conj (x i) * ((k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j) * x j)
        = ∑' k : ℕ, ∑ j, conj (x i) * ((k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j) * x j := by
      intro i; rw [← Summable.tsum_finsetSum (fun j _ => hg i j)]
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    rw [← Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ => hg i j)]
    apply tsum_congr; intro k
    rw [key, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- summability of the series of quadratic forms
  have hc : Summable (fun k : ℕ => (k.factorial : ℂ)⁻¹ * (star x ⬝ᵥ hPow (gram ℂ f) k *ᵥ x)) := by
    have hrw : (fun k : ℕ => (k.factorial : ℂ)⁻¹ * (star x ⬝ᵥ hPow (gram ℂ f) k *ᵥ x))
        = (fun k : ℕ => ∑ i, ∑ j, conj (x i) * ((k.factorial : ℂ)⁻¹ * hPow (gram ℂ f) k i j) * x j) := by
      funext k
      rw [key, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hrw]
    exact summable_sum (fun i _ => summable_sum fun j _ => hg i j)
  rw [hEq]
  refine complex_tsum_nonneg hc (fun k => ?_)
  have hk : (0 : ℂ) ≤ (k.factorial : ℂ)⁻¹ := by
    rw [inv_nonneg]; exact_mod_cast (Nat.cast_nonneg k.factorial : (0:ℝ) ≤ _)
  exact mul_nonneg hk ((hPow_posSemidef (posSemidef_gram ℂ f) k).dotProduct_mulVec_nonneg x)

/-- The Hermitian quadratic form of a matrix, unfolded as a double sum. -/
theorem dotProduct_mulVec_eq [Fintype ι] (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    star x ⬝ᵥ M *ᵥ x = ∑ i, ∑ j, conj (x i) * M i j * x j := by
  simp only [dotProduct, mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, mul_assoc]

/-- **Infinite-index keystone.** The exponential kernel `K(f,g) = exp⟪f,g⟫` is positive semidefinite
    for an *arbitrary* (possibly infinite-dimensional) family.  This is the form consumed by the
    exponential-vector inner product / `RKHS.OfKernel`: `Matrix.PosSemidef` quantifies over
    finitely-supported test vectors, so it reduces to the finite keystone on each support. -/
theorem expKernel_posSemidef' (f : ι → H) : (expKernel f).PosSemidef := by
  classical
  refine ⟨expKernel_isHermitian f, fun x => ?_⟩
  have hpos := (expKernel_posSemidef (fun i : x.support => f i)).dotProduct_mulVec_nonneg
                  (fun i : x.support => x i)
  rw [dotProduct_mulVec_eq] at hpos
  have heq : (x.sum fun i xi => x.sum fun j xj => star xi * expKernel f i j * xj)
      = ∑ i : x.support, ∑ j : x.support,
          conj (x ↑i) * expKernel (fun i : x.support => f ↑i) i j * x ↑j := by
    show (∑ i ∈ x.support, ∑ j ∈ x.support, star (x i) * expKernel f i j * x j) = _
    rw [← Finset.sum_coe_sort x.support]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_coe_sort x.support]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [expKernel_apply, RCLike.star_def]
  rw [heq]; exact hpos

end QIQTH.Fock.ExpKernel
