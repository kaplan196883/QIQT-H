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

/-- Unitary conjugation `A ↦ V⋆AV` preserves the Hermitian property. -/
lemma isHermitian_conj {A V : Matrix n n ℂ} (hA : A.IsHermitian) :
    (star V * A * V).IsHermitian := by
  show (star V * A * V)ᴴ = star V * A * V
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

/-! ### Convexity of trace functions (Carlen Thm 2.10) -/

/-- **Convexity of the trace function (Carlen Thm 2.10), midpoint form.**  For Hermitian `A, B` and a
    convex `f`, with `M = (A+B)/2`:  `∑ᵢ f(λᵢ(M)) ≤ (∑ᵢ f(λᵢ(A)) + ∑ᵢ f(λᵢ(B)))/2`  (i.e.
    `Tr f((A+B)/2) ≤ (Tr f(A) + Tr f(B))/2`).

    Proof: in the eigenbasis `V` of `M`, the diagonal of `M` is `λ(M)`, and `M = (A'+B')/2` with
    `A' = V⋆AV`, `B' = V⋆BV`; so `λᵢ(M) = (Re A'ᵢᵢ + Re B'ᵢᵢ)/2`.  Midpoint convexity of `f` termwise,
    then Peierls on `A', B'` (`∑ f(Re A'ᵢᵢ) ≤ ∑ f(λ(A'))`) and conjugation invariance
    (`∑ f(λ(A')) = ∑ f(λ(A))`). -/
theorem trace_function_midpoint_convex {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hM : ((2 : ℂ)⁻¹ • (A + B)).IsHermitian) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ∑ i, f (hM.eigenvalues i)
      ≤ (∑ i, f (hA.eigenvalues i) + ∑ i, f (hB.eigenvalues i)) / 2 := by
  set V := (hM.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  have hVl : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVr : V * star V = 1 := Unitary.coe_mul_star_self _
  have hA' : (star V * A * V).IsHermitian := isHermitian_conj hA
  have hB' : (star V * B * V).IsHermitian := isHermitian_conj hB
  -- the diagonal of M (in its eigenbasis) is its eigenvalues, and equals (A'+B')/2 entrywise
  have hMconj : star V * ((2 : ℂ)⁻¹ • (A + B)) * V
      = diagonal (fun i => (hM.eigenvalues i : ℂ)) := by
    conv_lhs => rw [spectral_UDU hM]
    rw [show star V * (V * diagonal (fun i => (hM.eigenvalues i : ℂ)) * star V) * V
        = (star V * V) * diagonal (fun i => (hM.eigenvalues i : ℂ)) * (star V * V)
        from by simp only [Matrix.mul_assoc], hVl, Matrix.one_mul, Matrix.mul_one]
  have hhalf : ∀ w : ℂ, ((2 : ℂ)⁻¹ * w).re = w.re / 2 := fun w => by
    have h2 : (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [h2, Complex.re_ofReal_mul]; ring
  have hsplit : star V * ((2 : ℂ)⁻¹ • (A + B)) * V
      = (2 : ℂ)⁻¹ • (star V * A * V) + (2 : ℂ)⁻¹ • (star V * B * V) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, smul_add]
  have hdiag : ∀ i, (hM.eigenvalues i : ℝ)
      = ((star V * A * V) i i).re / 2 + ((star V * B * V) i i).re / 2 := by
    intro i
    have hC : (hM.eigenvalues i : ℂ)
        = (2 : ℂ)⁻¹ * ((star V * A * V) i i + (star V * B * V) i i) := by
      have hen := Matrix.diagonal_apply_eq (fun i => (hM.eigenvalues i : ℂ)) i
      rw [← hen, ← hMconj, hsplit, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
        smul_eq_mul, smul_eq_mul, ← mul_add]
    have hre := congrArg Complex.re hC
    rw [Complex.ofReal_re, hhalf, Complex.add_re] at hre
    rw [hre]; ring
  -- midpoint convexity of f, termwise
  have hmid : ∀ i, f (hM.eigenvalues i)
      ≤ f (((star V * A * V) i i).re) / 2 + f (((star V * B * V) i i).re) / 2 := by
    intro i
    rw [hdiag i]
    have hcvx := hf.2 (Set.mem_univ ((star V * A * V) i i).re)
      (Set.mem_univ ((star V * B * V) i i).re)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 + 1/2 = 1)
    simp only [smul_eq_mul] at hcvx
    rw [show (1/2 * ((star V * A * V) i i).re + 1/2 * ((star V * B * V) i i).re)
        = ((star V * A * V) i i).re / 2 + ((star V * B * V) i i).re / 2 from by ring] at hcvx
    linarith [hcvx]
  -- assemble
  calc ∑ i, f (hM.eigenvalues i)
      ≤ ∑ i, (f (((star V * A * V) i i).re) / 2 + f (((star V * B * V) i i).re) / 2) :=
        Finset.sum_le_sum fun i _ => hmid i
    _ = (∑ i, f (((star V * A * V) i i).re)) / 2 + (∑ i, f (((star V * B * V) i i).re)) / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    _ ≤ (∑ i, f (hA.eigenvalues i)) / 2 + (∑ i, f (hB.eigenvalues i)) / 2 := by
        have hPA : ∑ i, f (((star V * A * V) i i).re) ≤ ∑ i, f (hA.eigenvalues i) :=
          (peierls_inequality hA' hf).trans_eq (eigenvalues_sum_conj_invariant hA hVl hVr hA' f)
        have hPB : ∑ i, f (((star V * B * V) i i).re) ≤ ∑ i, f (hB.eigenvalues i) :=
          (peierls_inequality hB' hf).trans_eq (eigenvalues_sum_conj_invariant hB hVl hVr hB' f)
        gcongr
    _ = (∑ i, f (hA.eigenvalues i) + ∑ i, f (hB.eigenvalues i)) / 2 := by ring

end QIQTH.Entropy
