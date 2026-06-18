/-
  SpectralSum — eigenvalue-perturbation infrastructure (fixed-basis core).

  Toward discharging `hev` (eigenvalues differentiable) for the entanglement first law: the obstacle
  is that `IsHermitian.eigenvalues` is the SORTED spectral data, with no Mathlib lemma relating it to an
  externally-given diagonal. This file builds the bridge for the DIAGONAL fixed-basis case, where the
  connection is made through the CHARACTERISTIC POLYNOMIAL (similarity/sorting-invariant): a symmetric
  sum over eigenvalues equals the same sum over the diagonal, because both have the same charpoly.

  Core: `sum_eq_of_prod_X_sub_C_eq` — if ∏(X−aᵢ) = ∏(X−bᵢ) over ℂ then ∑f(aᵢ)=∑f(bᵢ) (the eigenvalue
  MULTISET is determined by the charpoly; sorting/ordering drops out under the symmetric sum).
-/
import QIQTH.QuantumRelativeEntropy

open Polynomial Finset
open scoped ComplexOrder

namespace QIQTH.SpectralSum

/-- **Symmetric sums are determined by the characteristic product.** If two real index-vectors `a, b`
    have the same monic product `∏ᵢ (X − aᵢ) = ∏ᵢ (X − bᵢ)` over `ℂ`, then `∑ᵢ f(aᵢ) = ∑ᵢ f(bᵢ)` for
    any `f`. (The roots multiset is `{aᵢ} = {bᵢ}`; a symmetric sum is multiset-determined, so the
    sorting/ordering of eigenvalues is irrelevant.) -/
theorem sum_eq_of_prod_X_sub_C_eq {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (a b : ι → ℝ) (f : ℝ → M)
    (h : ∏ i, (X - C ((a i : ℂ))) = ∏ i, (X - C ((b i : ℂ)))) :
    ∑ i, f (a i) = ∑ i, f (b i) := by
  classical
  -- the ℂ-valued multisets of a- and b-images coincide (roots of the equal products)
  have hroots : (univ.val.map (fun i => (a i : ℂ))) = (univ.val.map (fun i => (b i : ℂ))) := by
    have ha : (∏ i, (X - C ((a i : ℂ))))
        = ((univ.val.map (fun i => (a i : ℂ))).map (fun c => X - C c)).prod := by
      rw [Multiset.map_map, Finset.prod]; rfl
    have hb : (∏ i, (X - C ((b i : ℂ))))
        = ((univ.val.map (fun i => (b i : ℂ))).map (fun c => X - C c)).prod := by
      rw [Multiset.map_map, Finset.prod]; rfl
    have h' := h
    rw [ha, hb] at h'
    have hr := congrArg Polynomial.roots h'
    rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  -- ℝ-valued multisets coincide (ofReal injective)
  have hreal : (univ.val.map a) = (univ.val.map b) := by
    have : (univ.val.map a).map (Complex.ofReal) = (univ.val.map b).map (Complex.ofReal) := by
      rw [Multiset.map_map, Multiset.map_map]; exact hroots
    exact Multiset.map_injective Complex.ofReal_injective this
  -- the symmetric sum is then equal
  have lhs : ∑ i, f (a i) = ((univ.val.map a).map f).sum := by
    rw [Multiset.map_map, Finset.sum]; rfl
  have rhs : ∑ i, f (b i) = ((univ.val.map b).map f).sum := by
    rw [Multiset.map_map, Finset.sum]; rfl
  rw [lhs, rhs, hreal]

open QIQTH.QuantumEntropy in
/-- **Von Neumann entropy of a DIAGONAL density = Shannon entropy of the diagonal.** For a diagonal
    density `diagonal (dᵢ)`, the spectral eigenvalues are a permutation of the diagonal `d` (equal
    characteristic polynomials, `charpoly_diagonal` vs `IsHermitian.charpoly_eq`), so
    `S(diagonal d) = ∑ᵢ negMulLog(dᵢ)`. The fixed-basis (U = I) case, with the eigenvalue ORDERING
    eliminated through the symmetric sum. -/
theorem vonNeumannEntropy_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ)
    (h : IsDensity (Matrix.diagonal (fun i => (d i : ℂ)))) :
    vonNeumannEntropy h = ∑ i, Real.negMulLog (d i) := by
  have hH := h.posSemidef.1
  have heq := hH.charpoly_eq.symm.trans (Matrix.charpoly_diagonal (fun i => (d i : ℂ)))
  have key := sum_eq_of_prod_X_sub_C_eq hH.eigenvalues d Real.negMulLog heq
  simpa [vonNeumannEntropy, IsDensity.eigenvalues] using key

open QIQTH.QuantumEntropy in
/-- **Von Neumann entropy is basis-independent: `S(U diag(p) U†) = ∑ᵢ negMulLog(pᵢ)`** for any unitary
    `U` (`star U · U = 1`). The eigenvalues of `U diag(p) U†` are a permutation of `p` because
    conjugation preserves the characteristic polynomial: `charpoly(U·diag·U†) = charpoly((U†·U)·diag) =
    charpoly(diag)` (cyclic `charpoly_mul_comm`). This closes the GENERAL fixed-basis case — any fixed
    eigenbasis, not just the diagonal one. -/
theorem vonNeumannEntropy_unitaryConj {n : Type*} [Fintype n] [DecidableEq n] (p : n → ℝ)
    (U : Matrix n n ℂ) (hU : star U * U = 1)
    (h : IsDensity (U * Matrix.diagonal (fun i => (p i : ℂ)) * star U)) :
    vonNeumannEntropy h = ∑ i, Real.negMulLog (p i) := by
  have hH := h.posSemidef.1
  have hcp : (U * Matrix.diagonal (fun i => (p i : ℂ)) * star U).charpoly
      = ∏ i, (X - C ((p i : ℂ))) := by
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, hU, one_mul, Matrix.charpoly_diagonal]
  have heq := hH.charpoly_eq.symm.trans hcp
  have key := sum_eq_of_prod_X_sub_C_eq hH.eigenvalues p Real.negMulLog heq
  simpa [vonNeumannEntropy, IsDensity.eigenvalues] using key

end QIQTH.SpectralSum
