/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Hilbert–Schmidt operators and the basis-independent HS norm

Hilbert–Schmidt operators + the BASIS-INDEPENDENT HS norm (`hsNormSqE`,
`hsNormSqE_basis_indep`), on a complex Hilbert space with a `HilbertBasis`. **T1** of the
trace-class API (**L5** of the heat-kernel full-infrastructure plan) — pure functional analysis,
no manifold/PDE. This is FOUNDATION for `Tr e^{−tΔ} = Σ e^{−λt}` but does NOT itself build the
heat kernel or discharge `a₁ = R/6` (L1/L3 manifold analysis stay the wall). NOT the conjecture,
NOT QG. No axioms, no `sorry`.

## Main results

* `hsNormSqE b T` : the extended-real HS norm-squared `∑' i, ‖T (b i)‖ₑ²`; always defined.
* `hsNormSqE_adjoint`   : `hsNormSqE b T = hsNormSqE b Tᴴ` (same-basis adjoint invariance).
* `hsNormSqE_basis_indep` : `hsNormSqE b T = hsNormSqE c T` — **the HS norm-squared is
  orthonormal-basis independent**. This is what makes Hilbert–Schmidt operators well defined.
* `IsHilbertSchmidt T`  : `T` is Hilbert–Schmidt (basis-independent, `isHilbertSchmidt_iff`).
* `isHilbertSchmidt_adjoint` : HS operators are closed under adjoint.
* `hsNormSqE_comp_le` / `IsHilbertSchmidt.comp_left` : the two-sided ideal bound
  `hsNormSqE b (S ∘ T) ≤ ‖S‖ₑ² · hsNormSqE b T`.

## Implementation notes

The core swaps are done in `ℝ≥0∞` (`ENNReal.tsum_comm` is unconditional there), so no summability
side conditions are needed for the basis-independence theorem. The bridge to `ℝ` is via Parseval
(`parsevalE`), transported from the real Parseval identity supplied by `HilbertBasis.repr` +
`lp.norm_rpow_eq_tsum`.
-/

open scoped ENNReal NNReal ComplexInnerProductSpace

namespace QIQTH.TraceClass

variable {ι κ : Type*} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- `(‖y‖₊ : ℝ≥0∞)²` written as an `ENNReal.ofReal` of the real norm-square. -/
private lemma enorm_sq_ofReal (y : H) :
    (‖y‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg y), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

omit [CompleteSpace H] in
/-- Symmetry of the extended inner-product norm: `‖⟪x, y⟫‖ₑ = ‖⟪y, x⟫‖ₑ`. -/
private lemma enorm_inner_symm (x y : H) :
    (‖(inner ℂ x y : ℂ)‖₊ : ℝ≥0∞) = (‖(inner ℂ y x : ℂ)‖₊ : ℝ≥0∞) := by
  congr 1
  rw [← NNReal.coe_inj]
  simpa using norm_inner_symm (𝕜 := ℂ) x y

omit [CompleteSpace H] in
/-- **Parseval, `ℝ≥0∞` form.** For a Hilbert basis `b`, the squared enorm of any vector is the
sum of the squared enorms of its `b`-coefficients. -/
theorem parsevalE (b : HilbertBasis ι ℂ H) (x : H) :
    (‖x‖₊ : ℝ≥0∞) ^ 2 = ∑' i, (‖(inner ℂ (b i) x : ℂ)‖₊ : ℝ≥0∞) ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  -- The real Parseval identity, summability, and value, from `b.repr` (an isometry to `ℓ²`).
  have hsummable : Summable (fun i => ‖(inner ℂ (b i) x : ℂ)‖ ^ 2) := by
    have h := (lp.memℓp (b.repr x)).summable hp
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply] using h
  have hval : ∑' i, ‖(inner ℂ (b i) x : ℂ)‖ ^ 2 = ‖x‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum hp (b.repr x)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply,
      LinearIsometryEquiv.norm_map] at h
    exact h.symm
  -- Transport to `ℝ≥0∞`.
  have key := ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsummable
  rw [hval] at key
  rw [enorm_sq_ofReal, key]
  exact tsum_congr fun i => (enorm_sq_ofReal _).symm

/-- The extended-real Hilbert–Schmidt norm-squared of `T` relative to a Hilbert basis `b`:
`∑' i, ‖T (b i)‖ₑ²`. Always defined (may be `⊤`). -/
noncomputable def hsNormSqE (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, (‖T (b i)‖₊ : ℝ≥0∞) ^ 2

/-- **Cross-basis adjoint identity.** For any two Hilbert bases `b`, `c`,
`hsNormSqE b T = hsNormSqE c Tᴴ`. This single lemma yields both same-basis adjoint invariance
(`c := b`) and basis independence. -/
theorem hsNormSqE_cross (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) : hsNormSqE b T = hsNormSqE c (ContinuousLinearMap.adjoint T) := by
  unfold hsNormSqE
  calc ∑' i, (‖T (b i)‖₊ : ℝ≥0∞) ^ 2
      = ∑' i, ∑' j, (‖(inner ℂ (c j) (T (b i)) : ℂ)‖₊ : ℝ≥0∞) ^ 2 :=
        tsum_congr fun i => parsevalE c (T (b i))
    _ = ∑' j, ∑' i, (‖(inner ℂ (c j) (T (b i)) : ℂ)‖₊ : ℝ≥0∞) ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i,
          (‖(inner ℂ (b i) (ContinuousLinearMap.adjoint T (c j)) : ℂ)‖₊ : ℝ≥0∞) ^ 2 := by
        refine tsum_congr fun j => tsum_congr fun i => ?_
        rw [← ContinuousLinearMap.adjoint_inner_left,
          enorm_inner_symm (ContinuousLinearMap.adjoint T (c j)) (b i)]
    _ = ∑' j, (‖(ContinuousLinearMap.adjoint T) (c j)‖₊ : ℝ≥0∞) ^ 2 :=
        tsum_congr fun j => (parsevalE b (ContinuousLinearMap.adjoint T (c j))).symm

/-- **Same-basis adjoint invariance.** `hsNormSqE b T = hsNormSqE b Tᴴ`. -/
theorem hsNormSqE_adjoint (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    hsNormSqE b T = hsNormSqE b (ContinuousLinearMap.adjoint T) :=
  hsNormSqE_cross b b T

/-- **The headline: the HS norm-squared is orthonormal-basis independent.**
`hsNormSqE b T = hsNormSqE c T` for any two Hilbert bases `b`, `c`. -/
theorem hsNormSqE_basis_indep (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) : hsNormSqE b T = hsNormSqE c T := by
  rw [hsNormSqE_cross b c T, ← hsNormSqE_adjoint c T]

/-- `T` is a **Hilbert–Schmidt operator**: its HS norm-squared is finite. Stated basis-freely as
"there exists a Hilbert basis making the sum finite"; by `hsNormSqE_basis_indep` this then holds
for *every* Hilbert basis (`isHilbertSchmidt_iff`). -/
def IsHilbertSchmidt (T : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (b : HilbertBasis w ℂ H), hsNormSqE b T ≠ ⊤

/-- The Hilbert–Schmidt predicate is testable against *any* Hilbert basis. -/
theorem isHilbertSchmidt_iff (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    IsHilbertSchmidt T ↔ hsNormSqE b T ≠ ⊤ := by
  constructor
  · rintro ⟨w, b', h⟩
    rwa [hsNormSqE_basis_indep b b' T]
  · intro h
    obtain ⟨w, b', -⟩ := exists_hilbertBasis ℂ H
    exact ⟨w, b', by rwa [hsNormSqE_basis_indep b' b T]⟩

/-- **Hilbert–Schmidt operators are closed under adjoint.** -/
theorem isHilbertSchmidt_adjoint (T : H →L[ℂ] H) :
    IsHilbertSchmidt T ↔ IsHilbertSchmidt (ContinuousLinearMap.adjoint T) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  rw [isHilbertSchmidt_iff b, isHilbertSchmidt_iff b, hsNormSqE_adjoint b T]

/-- The real Hilbert–Schmidt norm-squared (`⊤ ↦ 0`; use for HS operators). -/
noncomputable def hsNormSq (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℝ :=
  (hsNormSqE b T).toReal

omit [CompleteSpace H] in
/-- **Two-sided ideal bound.** `hsNormSqE b (S ∘ T) ≤ ‖S‖ₑ² · hsNormSqE b T`. -/
theorem hsNormSqE_comp_le (b : HilbertBasis ι ℂ H) (S T : H →L[ℂ] H) :
    hsNormSqE b (S.comp T) ≤ (‖S‖₊ : ℝ≥0∞) ^ 2 * hsNormSqE b T := by
  unfold hsNormSqE
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [ContinuousLinearMap.comp_apply]
  have hle : (‖S (T (b i))‖₊ : ℝ≥0∞) ≤ (‖S‖₊ : ℝ≥0∞) * (‖T (b i)‖₊ : ℝ≥0∞) := by
    exact_mod_cast S.le_opNNNorm (T (b i))
  calc (‖S (T (b i))‖₊ : ℝ≥0∞) ^ 2
      ≤ ((‖S‖₊ : ℝ≥0∞) * (‖T (b i)‖₊ : ℝ≥0∞)) ^ 2 := by gcongr
    _ = (‖S‖₊ : ℝ≥0∞) ^ 2 * (‖T (b i)‖₊ : ℝ≥0∞) ^ 2 := by rw [mul_pow]

/-- The Hilbert–Schmidt operators form a two-sided ideal: `S ∘ T` is HS whenever `T` is. -/
theorem IsHilbertSchmidt.comp_left {T : H →L[ℂ] H} (S : H →L[ℂ] H)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S.comp T) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  rw [isHilbertSchmidt_iff b] at hT ⊢
  refine ne_top_of_le_ne_top ?_ (hsNormSqE_comp_le b S T)
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hT

end QIQTH.TraceClass
