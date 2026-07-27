import Mathlib

/-!
# M4a — the analytic Jacobi formula `d/dτ log det W = tr(W⁻¹ W')`

This file lands the **abstract analytic toolkit** behind the van-Vleck / Raychaudhuri radial
expansion.  For a differentiable matrix curve `W : ℝ → Matrix (Fin n) (Fin n) ℝ`:

* `matrix_det_contDiff` — `Matrix.det` is `C^∞` (it is a polynomial in the entries).
* `hasDerivAt_matrix_det` — **Jacobi's formula**
  `d/dτ det(W τ) = tr(adjugate(W τ) · W' τ)`.
* `hasDerivAt_log_det_matrix` — when `W τ` is invertible,
  `d/dτ log det(W τ) = tr((W τ)⁻¹ · W' τ)`.
  This is the regularized expansion `θ = tr(W⁻¹ W')` that is the abstract core of the
  van-Vleck / Raychaudhuri radial ODE.

## What this is NOT

This is the **abstract analytic layer only**.  It does **not**:

* identify `W` with the geodesic Jacobi field / the differential `D exp_p` of the exponential
  map (phase M2b), so it says nothing yet about the *geometric* van-Vleck determinant;
* build the **uniform-in-direction van-Vleck radial ODE** `(r ∂_r) log √det g̃ = …` that cancels
  the off-diagonal `O(1/t)` term (M4-full);
* establish `a₁ = R/6` for the true heat kernel (M6).

Those remain the documented Mathlib-absent geometric walls; here we only supply the exact
differential-calculus identity for `det` of an arbitrary smooth matrix curve.
-/

namespace QIQTH.JacobiFormula

open Matrix Finset
open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

/-- **`Matrix.det` is `C^∞`.**  The determinant is a finite sum (over permutations) of signed
finite products of matrix entries; each entry evaluation `A ↦ A i j` is `C^∞`, and finite
sums/products of `C^∞` functions are `C^∞`.  (Mathlib has `Continuous.matrix_det` but not the
smooth/analytic version.) -/
theorem matrix_det_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
  have hrw : (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
      = fun A => ∑ σ : Equiv.Perm (Fin n),
          (Equiv.Perm.sign σ : ℝ) * ∏ i, A (σ i) i :=
    funext fun A => Matrix.det_apply' A
  rw [hrw]
  apply ContDiff.sum
  intro σ _
  refine contDiff_const.mul ?_
  apply contDiff_prod
  intro i _
  exact contDiff_apply_apply ℝ ℝ (σ i) i

/-! ### The algebraic cofactor collection -/

/-- **Cofactor collection, Lemma C.**  For any two square matrices,
`∑ k, det(A with row k replaced by row k of B) = tr(adjugate A · B)`.  This is the algebraic heart
of Jacobi's formula (the multilinear/row-derivative sum re-collected into `adjugate`), proved via
Cramer's rule. -/
theorem sum_det_updateRow_eq_trace (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∑ k, (A.updateRow k (B k)).det = (A.adjugate * B).trace := by
  have hcol : ∀ k, (A.updateRow k (B k)).det = ∑ j, A.adjugate j k * B k j := by
    intro k
    have h1 : (A.updateRow k (B k)).det = ((A.adjugate)ᵀ *ᵥ B k) k := by
      rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
        ← Matrix.adjugate_transpose]
    rw [h1]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  simp only [hcol, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]

/-! ### The analytic derivative in permutation-sum form -/

/-- **Entrywise/permutation form of Jacobi's formula.**  `d/dτ det(W τ)` computed term-by-term
from `det = ∑_σ sign σ · ∏_i` and the product rule. -/
theorem hasDerivAt_det_perm (W W' : ℝ → Matrix (Fin n) (Fin n) ℝ) {τ : ℝ}
    (hW : HasDerivAt W (W' τ) τ) :
    HasDerivAt (fun s => (W s).det)
      (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) *
        ∑ k, (∏ j ∈ univ.erase k, (W τ) (σ j) j) * (W' τ) (σ k) k) τ := by
  have hentry : ∀ (a b : Fin n), HasDerivAt (fun s => (W s) a b) ((W' τ) a b) τ := by
    intro a b
    exact (hasDerivAt_pi.mp ((hasDerivAt_pi.mp hW) a)) b
  have hrw : (fun s => (W s).det)
      = fun s => ∑ σ : Equiv.Perm (Fin n),
          (Equiv.Perm.sign σ : ℝ) * ∏ i, (W s) (σ i) i :=
    funext fun s => Matrix.det_apply' (W s)
  rw [hrw]
  apply HasDerivAt.fun_sum
  intro σ _
  have hprod : HasDerivAt (fun s => ∏ i, (W s) (σ i) i)
      (∑ k, (∏ j ∈ univ.erase k, (W τ) (σ j) j) * (W' τ) (σ k) k) τ := by
    have hfun : (fun s => ∏ i, (W s) (σ i) i)
        = ∏ i : Fin n, (fun s => (W s) (σ i) i) := by
      funext s; simp only [Finset.prod_apply]
    rw [hfun]
    have h := HasDerivAt.finsetProd (u := (univ : Finset (Fin n)))
      (f := fun i s => (W s) (σ i) i) (f' := fun i => (W' τ) (σ i) i)
      (fun i _ => hentry (σ i) i)
    simpa only [smul_eq_mul] using h
  exact hprod.const_mul (Equiv.Perm.sign σ : ℝ)

/-- **Lemma B: the permutation form equals the cofactor-collection form.**  Re-indexing the
term-by-term derivative `∑_σ sign σ · ∑_k (∏_{j≠k} A(σ j) j) · B(σ k) k` as a sum of determinants
with one updated row, `∑_k det(A.updateRow k (B k))`. -/
theorem perm_eq_sum_det_updateRow (A B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) *
        ∑ k, (∏ j ∈ univ.erase k, A (σ j) j) * B (σ k) k)
      = ∑ k, (A.updateRow k (B k)).det := by
  -- expand each determinant of an updated row
  have key : ∀ (σ : Equiv.Perm (Fin n)) (k : Fin n),
      ∏ i, (A.updateRow k (B k)) (σ i) i
        = B k (σ.symm k) * ∏ i ∈ univ.erase (σ.symm k), A (σ i) i := by
    intro σ k
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ (σ.symm k))]
    congr 1
    · rw [Equiv.apply_symm_apply, Matrix.updateRow_self]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [Matrix.updateRow_ne]
      intro hik
      exact (Finset.mem_erase.mp hi).1 (by rw [← hik, Equiv.symm_apply_apply])
  calc
    (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) *
          ∑ k, (∏ j ∈ univ.erase k, A (σ j) j) * B (σ k) k)
        = ∑ σ : Equiv.Perm (Fin n), ∑ k,
            (Equiv.Perm.sign σ : ℝ) *
              (B k (σ.symm k) * ∏ i ∈ univ.erase (σ.symm k), A (σ i) i) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.mul_sum]
          rw [← Equiv.sum_comp σ (fun k => (Equiv.Perm.sign σ : ℝ) *
            (B k (σ.symm k) * ∏ i ∈ univ.erase (σ.symm k), A (σ i) i))]
          apply Finset.sum_congr rfl
          intro m _
          simp only [Equiv.symm_apply_apply]
          ring
    _ = ∑ k, ∑ σ : Equiv.Perm (Fin n),
            (Equiv.Perm.sign σ : ℝ) *
              (B k (σ.symm k) * ∏ i ∈ univ.erase (σ.symm k), A (σ i) i) := by
          rw [Finset.sum_comm]
    _ = ∑ k, (A.updateRow k (B k)).det := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Matrix.det_apply']
          apply Finset.sum_congr rfl
          intro σ _
          rw [key σ k]

/-! ### Jacobi's formula and its logarithmic form -/

/-- **Jacobi's formula.**  For a differentiable matrix curve `W`,
`d/dτ det(W τ) = tr(adjugate(W τ) · W' τ)`. -/
theorem hasDerivAt_matrix_det (W W' : ℝ → Matrix (Fin n) (Fin n) ℝ) {τ : ℝ}
    (hW : HasDerivAt W (W' τ) τ) :
    HasDerivAt (fun s => (W s).det) ((W τ).adjugate * W' τ).trace τ := by
  have h := hasDerivAt_det_perm W W' hW
  rwa [perm_eq_sum_det_updateRow (W τ) (W' τ),
    sum_det_updateRow_eq_trace (W τ) (W' τ)] at h

/-- **Logarithmic Jacobi formula = the van-Vleck/Raychaudhuri expansion core.**  When `W τ` is
invertible, `d/dτ log det(W τ) = tr((W τ)⁻¹ · W' τ)`.  This is the regularized `θ = tr(W⁻¹ W')`. -/
theorem hasDerivAt_log_det_matrix (W W' : ℝ → Matrix (Fin n) (Fin n) ℝ) {τ : ℝ}
    (hW : HasDerivAt W (W' τ) τ) (hu : IsUnit (W τ).det) :
    HasDerivAt (fun s => Real.log (W s).det) (((W τ)⁻¹ * W' τ).trace) τ := by
  have hdet := hasDerivAt_matrix_det W W' hW
  have hlog := hdet.log hu.ne_zero
  convert hlog using 1
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    div_eq_inv_mul]

end QIQTH.JacobiFormula
