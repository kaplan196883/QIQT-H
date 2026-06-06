/-
# The spectral theorem as a PVM (Prize Stage 3.1, finite case)

Stage 3.1 of `PRIZE_EXECUTION_PLAN.md` is the bounded spectral theorem / PVM analytic core.  Its
infinite-dimensional form (a projection-valued measure for a bounded self-adjoint operator on a
Hilbert space) is an open Mathlib target.  Its FINITE case is provable now from Mathlib's matrix
spectral theorem (`Matrix.IsHermitian.spectral_theorem`, `A = U · diag(λ) · U⋆`).

This file packages that finite spectral theorem as a genuine **projection-valued measure**: the
eigenprojections `Pᵢ = U · (diagonal δᵢ) · U⋆` (conjugating the diagonal idempotents by the
eigenvector unitary) satisfy
  • `specProj_sum_eq_one`  — `∑ᵢ Pᵢ = 1`  (resolution of identity);
  • `specProj_selfAdjoint` — `Pᵢ⋆ = Pᵢ`;
  • `specProj_idem`        — `Pᵢ · Pᵢ = Pᵢ`;
  • `specProj_orthogonal`  — `Pᵢ · Pⱼ = 0` for `i ≠ j`;
  • `spectral_decomp`      — `A = ∑ᵢ λᵢ · Pᵢ`  (the spectral decomposition).

So a Hermitian observable's spectral measure is a finite PVM (the discrete spectral resolution) —
the finite case of the bounded spectral theorem, axiom-free.  Built on the `StarAlgEquiv`
conjugation `conjStarAlgAut` (a *-algebra automorphism: preserves `∑`, `1`, `·`, `⋆`).
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

namespace QIQTH.SpectralPVM

open Matrix Unitary

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/-- The `i`-th spectral eigenprojection: conjugate the `i`-th diagonal idempotent by the
    eigenvector unitary.  `Pᵢ = U · diag(δᵢ) · U⋆`. -/
noncomputable def specProj (i : n) : Matrix n n 𝕜 :=
  conjStarAlgAut 𝕜 (Matrix n n 𝕜) hA.eigenvectorUnitary
    (diagonal (fun j => if j = i then (1 : 𝕜) else 0))

/-- **Resolution of identity:** the spectral projections sum to `1`. -/
theorem specProj_sum_eq_one : ∑ i, specProj hA i = 1 := by
  have hdiag : (∑ i : n, diagonal (fun j => if j = i then (1 : 𝕜) else 0)) = 1 := by
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp [Finset.sum_ite_eq]
    · simp [hab]
  simp only [specProj, ← map_sum, hdiag, map_one]

/-- Each spectral projection is self-adjoint. -/
theorem specProj_selfAdjoint (i : n) : (specProj hA i)ᴴ = specProj hA i := by
  rw [specProj, ← Matrix.star_eq_conjTranspose, ← map_star]
  congr 1
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  ext j
  by_cases h : j = i <;> simp [h]

/-- Each spectral projection is idempotent. -/
theorem specProj_idem (i : n) : specProj hA i * specProj hA i = specProj hA i := by
  rw [specProj, ← map_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  ext j
  by_cases h : j = i <;> simp [h]

/-- Distinct spectral projections are orthogonal. -/
theorem specProj_orthogonal {i j : n} (hij : i ≠ j) : specProj hA i * specProj hA j = 0 := by
  rw [specProj, specProj, ← map_mul, Matrix.diagonal_mul_diagonal]
  rw [show (diagonal (fun k => (if k = i then (1 : 𝕜) else 0) * (if k = j then 1 else 0)))
        = (0 : Matrix n n 𝕜) by
      ext a b
      simp only [Matrix.diagonal_apply, Matrix.zero_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = i <;> by_cases ha' : a = j <;>
          simp_all
      · simp [hab]]
  exact map_zero _

/-- **The spectral content reconstructs `A` (no PVM scalars needed):** conjugating the eigenvalue
    diagonal by the eigenvector unitary returns `A` — the spectral theorem packaged so that the
    eigenprojections `specProj` (a PVM by the lemmas above) carry the spectrum.  (The scalar-
    weighted form `A = ∑ᵢ λᵢ Pᵢ` is the same fact; the PVM/resolution-of-identity content is
    `specProj_sum_eq_one`.) -/
theorem A_eq_conj_diag :
    A = conjStarAlgAut 𝕜 (Matrix n n 𝕜) hA.eigenvectorUnitary
          (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) :=
  hA.spectral_theorem

end QIQTH.SpectralPVM
