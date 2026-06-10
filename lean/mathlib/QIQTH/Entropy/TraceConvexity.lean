/-
  Phase 1 of the DPI / Lieb program (Carlen §2): the trace-convexity toolkit.

  We follow Carlen, "Trace Inequalities and Quantum Entropy" §2.  The foundation is **Peierls'
  inequality** (Carlen Thm 2.9): for a Hermitian matrix and a convex `f`, the sum of `f` over the
  diagonal entries (in any orthonormal basis) is at most the trace of `f` applied to the matrix.

  The diagonal entries of a Hermitian matrix are a *doubly-stochastic average* of its eigenvalues
  (`Bⱼⱼ = ∑ₖ ‖Vⱼₖ‖² λₖ`, `V` the eigenvector unitary), so Peierls is Jensen's inequality applied
  termwise plus the column-stochasticity of `‖Vⱼₖ‖²` — exactly the structure used in our proof of
  Klein's inequality (`QuantumEntropy.relEntropy_nonneg`).  This module reuses that machinery
  (`spectral_UDU`, `row_sum_normSq`, `col_sum_normSq`).

  Downstream (later in this phase): convexity of the trace function `A ↦ Tr f(A)` (Thm 2.10), the
  general operator Klein inequality (Thm 2.11), Peierls–Bogoliubov (Thm 2.12).
-/
import QIQTH.QuantumRelativeEntropy
import Mathlib.Analysis.Convex.Jensen

namespace QIQTH.Entropy

open Matrix QuantumEntropy
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The diagonal entries of a Hermitian matrix are a doubly-stochastic average of its
    eigenvalues**: `Re Bⱼⱼ = ∑ₖ ‖Vⱼₖ‖² λₖ`, where `V` is the eigenvector unitary and `λ` the
    eigenvalues.  (The imaginary part of a Hermitian diagonal entry is zero.) -/
lemma diag_re_eq_overlap_sum {B : Matrix n n ℂ} (hB : B.IsHermitian) (j : n) :
    (B j j).re
      = ∑ k, Complex.normSq ((hB.eigenvectorUnitary : Matrix n n ℂ) j k) * hB.eigenvalues k := by
  conv_lhs => rw [spectral_UDU hB]
  rw [Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply,
    show (hB.eigenvectorUnitary : Matrix n n ℂ) j k * ((hB.eigenvalues k : ℝ) : ℂ)
        * star ((hB.eigenvectorUnitary : Matrix n n ℂ) j k)
      = ((hB.eigenvalues k : ℝ) : ℂ) * ((hB.eigenvectorUnitary : Matrix n n ℂ) j k
          * star ((hB.eigenvectorUnitary : Matrix n n ℂ) j k)) from by ring,
    show star ((hB.eigenvectorUnitary : Matrix n n ℂ) j k)
        = (starRingEnd ℂ) ((hB.eigenvectorUnitary : Matrix n n ℂ) j k) from rfl,
    Complex.mul_conj, Complex.re_ofReal_mul, Complex.ofReal_re]
  ring

/-- The overlap weights `‖Vⱼₖ‖²` of the eigenvector unitary are **column-stochastic**:
    `∑ⱼ ‖Vⱼₖ‖² = 1` (from `V⋆V = 1`). -/
lemma eigenvectorUnitary_col_sum {B : Matrix n n ℂ} (hB : B.IsHermitian) (k : n) :
    ∑ j, Complex.normSq ((hB.eigenvectorUnitary : Matrix n n ℂ) j k) = 1 :=
  col_sum_normSq _ (Unitary.coe_star_mul_self _) k

/-- The overlap weights are **row-stochastic**: `∑ₖ ‖Vⱼₖ‖² = 1` (from `VV⋆ = 1`). -/
lemma eigenvectorUnitary_row_sum {B : Matrix n n ℂ} (hB : B.IsHermitian) (j : n) :
    ∑ k, Complex.normSq ((hB.eigenvectorUnitary : Matrix n n ℂ) j k) = 1 :=
  row_sum_normSq _ (Unitary.coe_mul_star_self _) j

/-- **Peierls' inequality (Carlen Thm 2.9).**  For a Hermitian matrix `B` and a convex `f : ℝ → ℝ`,
    the sum of `f` over the (real) diagonal entries is at most `∑ᵢ f(λᵢ) = Tr f(B)`:
    `∑ⱼ f(Re Bⱼⱼ) ≤ ∑ᵢ f(λᵢ)`.

    Proof: each `Re Bⱼⱼ = ∑ₖ ‖Vⱼₖ‖² λₖ` is a convex combination of eigenvalues (row-stochastic),
    so `f(Re Bⱼⱼ) ≤ ∑ₖ ‖Vⱼₖ‖² f(λₖ)` by Jensen; summing over `j` and using column-stochasticity
    collapses `∑ⱼ ‖Vⱼₖ‖² = 1`. -/
theorem peierls_inequality {B : Matrix n n ℂ} (hB : B.IsHermitian) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) :
    ∑ j, f ((B j j).re) ≤ ∑ i, f (hB.eigenvalues i) := by
  have hrow := eigenvectorUnitary_row_sum hB
  have hjensen : ∀ j, f ((B j j).re)
      ≤ ∑ k, Complex.normSq ((hB.eigenvectorUnitary : Matrix n n ℂ) j k) * f (hB.eigenvalues k) := by
    intro j
    rw [diag_re_eq_overlap_sum hB j]
    have := hf.map_sum_le (t := Finset.univ)
      (w := fun k => Complex.normSq ((hB.eigenvectorUnitary : Matrix n n ℂ) j k))
      (p := hB.eigenvalues)
      (fun k _ => Complex.normSq_nonneg _) (hrow j) (fun k _ => Set.mem_univ _)
    simpa only [smul_eq_mul] using this
  calc ∑ j, f ((B j j).re)
      ≤ ∑ j, ∑ k, Complex.normSq ((hB.eigenvectorUnitary : Matrix n n ℂ) j k) * f (hB.eigenvalues k) :=
        Finset.sum_le_sum fun j _ => hjensen j
    _ = ∑ k, (∑ j, Complex.normSq ((hB.eigenvectorUnitary : Matrix n n ℂ) j k)) * f (hB.eigenvalues k) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
    _ = ∑ k, f (hB.eigenvalues k) := by
        exact Finset.sum_congr rfl fun k _ => by rw [eigenvectorUnitary_col_sum hB k, one_mul]

/-! ### Unitary-conjugation invariance of eigenvalue sums (foundation for 2.10–2.12 and DPI)

Conjugate Hermitian matrices `A` and `V⋆AV` (V unitary) are similar, hence have the same characteristic
polynomial (`charpoly_units_conj'`) and therefore the same eigenvalue multiset
(`roots_charpoly_eq_eigenvalues`).  So `∑ᵢ f(λᵢ)` is invariant under unitary conjugation — equivalently
`Tr(cfc f (V⋆AV)) = Tr(cfc f A)`. -/

/-- **Eigenvalue sums are unitary-conjugation invariant**: for Hermitian `A`, unitary `V`
    (`star V * V = 1`, `V * star V = 1`), and the Hermitian conjugate `V⋆AV`,
    `∑ᵢ f((V⋆AV).λᵢ) = ∑ᵢ f(A.λᵢ)`.  Via equal characteristic polynomials ⇒ equal eigenvalue multisets. -/
theorem eigenvalues_sum_conj_invariant {A V : Matrix n n ℂ} (hA : A.IsHermitian)
    (hVl : star V * V = 1) (hVr : V * star V = 1)
    (h2 : (star V * A * V).IsHermitian) (f : ℝ → ℝ) :
    ∑ i, f (h2.eigenvalues i) = ∑ i, f (hA.eigenvalues i) := by
  classical
  have hchar : (star V * A * V).charpoly = A.charpoly := by
    rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hVr, mul_one]
  have hroots : Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ h2.eigenvalues) Finset.univ.val
      = Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues) Finset.univ.val := by
    rw [← h2.roots_charpoly_eq_eigenvalues, ← hA.roots_charpoly_eq_eigenvalues, hchar]
  have heig : Multiset.map h2.eigenvalues Finset.univ.val
      = Multiset.map hA.eigenvalues Finset.univ.val := by
    refine Multiset.map_injective (RCLike.ofReal_injective (K := ℂ)) ?_
    simpa only [Multiset.map_map] using hroots
  have key : Multiset.map (f ∘ h2.eigenvalues) Finset.univ.val
      = Multiset.map (f ∘ hA.eigenvalues) Finset.univ.val := by
    rw [← Multiset.map_map, ← Multiset.map_map, heig]
  calc ∑ i, f (h2.eigenvalues i)
      = (Multiset.map (f ∘ h2.eigenvalues) Finset.univ.val).sum := rfl
    _ = (Multiset.map (f ∘ hA.eigenvalues) Finset.univ.val).sum := by rw [key]
    _ = ∑ i, f (hA.eigenvalues i) := rfl

end QIQTH.Entropy
