/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.TraceClass.HilbertSchmidt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The Hilbert–Schmidt inner product, trace-class operators, and the basis-independent trace

The Hilbert–Schmidt inner product `⟨S, T⟩_HS = ∑' i, ⟪S (b i), T (b i)⟫`, trace-class operators
`T = A⋆B` with `A, B` Hilbert–Schmidt, and the **basis-independent trace** `Tr T = ∑' i, ⟪b i,
T (b i)⟫`. **T2** of the trace-class API (**L5** of the heat-kernel full-infrastructure plan) — pure
functional analysis, no manifold/PDE. This is FOUNDATION for `Tr e^{−tΔ} = Σ e^{−λt}` but does NOT
itself build the heat kernel or discharge the general `a₁ = R/6` (L1/L3 manifold analysis stay the
wall). NOT the conjecture, NOT QG. No axioms, no `sorry`.

## Main results

* `hsInner b S T` : the HS inner product `∑' i, ⟪S (b i), T (b i)⟫`.
* `hsInner_summable` : the defining series is summable for HS operators.
* `hsInner_basis_indep` : **the HS inner product is orthonormal-basis independent** (proved by
  polarization into four basis-independent HS norm-squares, reusing `hsNormSqE_basis_indep`).
* `IsTraceClass T` : `T = A⋆B` with `A, B` Hilbert–Schmidt; `IsTraceClass.isHilbertSchmidt`.
* `traceE b T` : the trace `∑' i, ⟪b i, T (b i)⟫`.
* `traceE_eq_hsInner` : `Tr (A⋆B) = ⟨A, B⟩_HS`.
* `traceE_basis_indep` : **the trace is orthonormal-basis independent** — the whole point.
* `traceE_add`, `traceE_smul`, `traceE_adjoint` : linearity and conjugation of the trace.

## Implementation notes

Basis independence of the *complex* HS inner product is obtained by **polarization**:
`4⟨S, T⟩_HS = ∑_{k} iᵏ ‖S + iᵏ T‖²_HS`, each `‖·‖²_HS` being basis-independent by T1's
`hsNormSqE_basis_indep`. This reduces the ℂ-valued statement to T1's `ℝ≥0∞`-valued result plus finite
algebra, avoiding a ℂ-valued double-sum Tonelli argument.
-/

open scoped ENNReal NNReal ComplexInnerProductSpace

namespace QIQTH.TraceClass

variable {ι κ : Type*} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- `(‖y‖₊ : ℝ≥0∞)²` written as an `ENNReal.ofReal` of the real norm-square. -/
private lemma enorm_sq_ofReal' (y : H) :
    (‖y‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg y), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

/-- **Hilbert–Schmidt ⇔ real square-summability of the coefficients.** `T` is Hilbert–Schmidt iff
the real sequence `i ↦ ‖T (b i)‖²` is summable, for any given Hilbert basis `b`. -/
theorem isHilbertSchmidt_iff_summable (b : HilbertBasis ι ℂ H) (X : H →L[ℂ] H) :
    IsHilbertSchmidt X ↔ Summable (fun i => ‖X (b i)‖ ^ 2) := by
  rw [isHilbertSchmidt_iff b]
  unfold hsNormSqE
  simp_rw [← ENNReal.coe_pow]
  rw [ENNReal.tsum_coe_ne_top_iff_summable_coe]
  apply summable_congr
  intro i
  simp only [NNReal.coe_pow, coe_nnnorm]

/-- For a Hilbert–Schmidt operator the coefficient squares are summable. -/
theorem IsHilbertSchmidt.summable_normSq {X : H →L[ℂ] H} (hX : IsHilbertSchmidt X)
    (b : HilbertBasis ι ℂ H) : Summable (fun i => ‖X (b i)‖ ^ 2) :=
  (isHilbertSchmidt_iff_summable b X).mp hX

/-- The real HS norm-squared of a Hilbert–Schmidt operator is the (convergent) sum of the squared
coefficient norms. -/
theorem hsNormSq_eq_tsum (b : HilbertBasis ι ℂ H) {X : H →L[ℂ] H} (hX : IsHilbertSchmidt X) :
    hsNormSq b X = ∑' i, ‖X (b i)‖ ^ 2 := by
  have hsum := hX.summable_normSq b
  unfold hsNormSq hsNormSqE
  simp_rw [enorm_sq_ofReal']
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsum,
    ENNReal.toReal_ofReal (tsum_nonneg fun i => sq_nonneg _)]

/-- The real HS norm-squared is orthonormal-basis independent (from T1's `hsNormSqE_basis_indep`). -/
theorem hsNormSq_basis_indep (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    (X : H →L[ℂ] H) : hsNormSq b X = hsNormSq c X := by
  unfold hsNormSq
  rw [hsNormSqE_basis_indep b c X]

/-! ### Vector-space closure of the Hilbert–Schmidt operators -/

/-- Hilbert–Schmidt operators are closed under addition. -/
theorem IsHilbertSchmidt.add {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S + T) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  rw [isHilbertSchmidt_iff_summable b] at hS hT ⊢
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
    ((hS.mul_left 2).add (hT.mul_left 2))
  simp only [ContinuousLinearMap.add_apply]
  nlinarith [norm_add_le (S (b i)) (T (b i)), norm_nonneg (S (b i)), norm_nonneg (T (b i)),
    norm_nonneg (S (b i) + T (b i)), sq_nonneg (‖S (b i)‖ - ‖T (b i)‖)]

/-- Hilbert–Schmidt operators are closed under scalar multiplication. -/
theorem IsHilbertSchmidt.smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (c • T) := by
  have h : c • T = (c • ContinuousLinearMap.id ℂ H).comp T := by ext x; simp
  rw [h]; exact hT.comp_left _

/-- Hilbert–Schmidt operators are closed under negation. -/
theorem IsHilbertSchmidt.neg {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (-T) := by
  have h : (-T) = ((-1 : ℂ) • T) := by rw [neg_one_smul]
  rw [h]; exact hT.smul (-1)

/-- Hilbert–Schmidt operators are closed under subtraction. -/
theorem IsHilbertSchmidt.sub {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S - T) := by
  rw [sub_eq_add_neg]; exact hS.add hT.neg

/-! ### The Hilbert–Schmidt inner product -/

/-- The **Hilbert–Schmidt inner product** of two operators relative to a Hilbert basis `b`:
`∑' i, ⟪S (b i), T (b i)⟫`. -/
noncomputable def hsInner (b : HilbertBasis ι ℂ H) (S T : H →L[ℂ] H) : ℂ :=
  ∑' i, (inner ℂ (S (b i)) (T (b i)) : ℂ)

/-- The defining series of the HS inner product is summable for Hilbert–Schmidt operators. The
majorant is `½(‖S (b i)‖² + ‖T (b i)‖²)`, using `‖⟪x, y⟫‖ ≤ ‖x‖‖y‖ ≤ ½(‖x‖² + ‖y‖²)`. -/
theorem hsInner_summable {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    (b : HilbertBasis ι ℂ H) : Summable (fun i => (inner ℂ (S (b i)) (T (b i)) : ℂ)) := by
  refine Summable.of_norm_bounded (g := fun i => (‖S (b i)‖ ^ 2 + ‖T (b i)‖ ^ 2) / 2)
    (((hS.summable_normSq b).add (hT.summable_normSq b)).div_const 2) (fun i => ?_)
  nlinarith [norm_inner_le_norm (𝕜 := ℂ) (S (b i)) (T (b i)),
    two_mul_le_add_sq ‖S (b i)‖ ‖T (b i)‖,
    norm_nonneg (inner ℂ (S (b i)) (T (b i)) : ℂ)]

/-- **Polarization of the HS inner product** into the four basis-independent HS norm-squares. -/
theorem hsInner_eq_polarization {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) (b : HilbertBasis ι ℂ H) :
    hsInner b S T
      = ((hsNormSq b (S + T) : ℂ) - (hsNormSq b (S - T) : ℂ)
          + ((hsNormSq b (S - Complex.I • T) : ℂ) - (hsNormSq b (S + Complex.I • T) : ℂ))
            * Complex.I) / 4 := by
  have hST := hS.add hT
  have hSmT := hS.sub hT
  have hSiT := hS.sub (hT.smul Complex.I)
  have hSpiT := hS.add (hT.smul Complex.I)
  have c1 : Summable (fun i => ((‖(S + T) (b i)‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr (hST.summable_normSq b)
  have c2 : Summable (fun i => ((‖(S - T) (b i)‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr (hSmT.summable_normSq b)
  have c3 : Summable (fun i => ((‖(S - Complex.I • T) (b i)‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr (hSiT.summable_normSq b)
  have c4 : Summable (fun i => ((‖(S + Complex.I • T) (b i)‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr (hSpiT.summable_normSq b)
  have hpol : ∀ i, (inner ℂ (S (b i)) (T (b i)) : ℂ)
      = (((‖(S + T) (b i)‖ ^ 2 : ℝ) : ℂ) - ((‖(S - T) (b i)‖ ^ 2 : ℝ) : ℂ)
          + (((‖(S - Complex.I • T) (b i)‖ ^ 2 : ℝ) : ℂ)
              - ((‖(S + Complex.I • T) (b i)‖ ^ 2 : ℝ) : ℂ)) * Complex.I) / 4 := by
    intro i
    rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (S (b i)) (T (b i))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, RCLike.I_to_complex, RCLike.ofReal_eq_complex_ofReal]
    push_cast
    ring
  unfold hsInner
  rw [tsum_congr hpol, tsum_div_const]
  congr 1
  rw [Summable.tsum_add (c1.sub c2) ((c3.sub c4).mul_right Complex.I),
    Summable.tsum_sub c1 c2, tsum_mul_right, Summable.tsum_sub c3 c4,
    ← Complex.ofReal_tsum, ← Complex.ofReal_tsum, ← Complex.ofReal_tsum, ← Complex.ofReal_tsum,
    ← hsNormSq_eq_tsum b hST, ← hsNormSq_eq_tsum b hSmT,
    ← hsNormSq_eq_tsum b hSiT, ← hsNormSq_eq_tsum b hSpiT]

/-- **The Hilbert–Schmidt inner product is orthonormal-basis independent.** Proved by polarization
into four basis-independent HS norm-squares. -/
theorem hsInner_basis_indep {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H) : hsInner b S T = hsInner c S T := by
  rw [hsInner_eq_polarization hS hT b, hsInner_eq_polarization hS hT c,
    hsNormSq_basis_indep b c (S + T), hsNormSq_basis_indep b c (S - T),
    hsNormSq_basis_indep b c (S - Complex.I • T), hsNormSq_basis_indep b c (S + Complex.I • T)]

/-! ### Trace-class operators and the trace -/

/-- `T` is **trace-class** if it factors as `T = A⋆B` with `A`, `B` Hilbert–Schmidt. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ (A B : H →L[ℂ] H), IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧
    T = (ContinuousLinearMap.adjoint A).comp B

/-- **Trace-class operators are Hilbert–Schmidt.** (`A⋆B` is HS since `A⋆` is bounded and `B` is HS,
by the two-sided ideal property.) -/
theorem IsTraceClass.isHilbertSchmidt {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsHilbertSchmidt T := by
  obtain ⟨A, B, _, hB, rfl⟩ := hT
  exact hB.comp_left (ContinuousLinearMap.adjoint A)

/-- The **trace** of `T` relative to a Hilbert basis `b`: `∑' i, ⟪b i, T (b i)⟫`. -/
noncomputable def traceE (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℂ :=
  ∑' i, (inner ℂ (b i) (T (b i)) : ℂ)

/-- **The trace of `A⋆B` equals the HS inner product `⟨A, B⟩_HS`.** Termwise:
`⟪b i, A⋆B (b i)⟫ = ⟪A (b i), B (b i)⟫`. -/
theorem traceE_eq_hsInner (b : HilbertBasis ι ℂ H) {A B : H →L[ℂ] H}
    (_hA : IsHilbertSchmidt A) (_hB : IsHilbertSchmidt B) :
    traceE b ((ContinuousLinearMap.adjoint A).comp B) = hsInner b A B := by
  unfold traceE hsInner
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

/-- **The trace is orthonormal-basis independent** — the whole point of trace-class theory. Reduces
to `traceE_eq_hsInner` plus `hsInner_basis_indep`. -/
theorem traceE_basis_indep {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H) : traceE b T = traceE c T := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  rw [traceE_eq_hsInner b hA hB, traceE_eq_hsInner c hA hB]
  exact hsInner_basis_indep hA hB b c

/-! ### Linearity and conjugation of the trace (fixed basis) -/

/-- The defining series of the trace is summable for a trace-class operator. -/
theorem IsTraceClass.summable (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    Summable (fun i => (inner ℂ (b i) (T (b i)) : ℂ)) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  refine (hsInner_summable hA hB b).congr (fun i => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

/-- The trace is additive (on trace-class operators, fixed basis). -/
theorem traceE_add (b : HilbertBasis ι ℂ H) {S T : H →L[ℂ] H} (hS : IsTraceClass S)
    (hT : IsTraceClass T) : traceE b (S + T) = traceE b S + traceE b T := by
  unfold traceE
  simp_rw [ContinuousLinearMap.add_apply, inner_add_right]
  rw [Summable.tsum_add (hS.summable b) (hT.summable b)]

omit [CompleteSpace H] in
/-- The trace is homogeneous (fixed basis). -/
theorem traceE_smul (b : HilbertBasis ι ℂ H) (c : ℂ) (T : H →L[ℂ] H) :
    traceE b (c • T) = c * traceE b T := by
  unfold traceE
  simp_rw [ContinuousLinearMap.smul_apply, inner_smul_right]
  rw [tsum_mul_left]

/-- The trace conjugates under the adjoint: `Tr T⋆ = conj (Tr T)`. -/
theorem traceE_adjoint (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    traceE b (ContinuousLinearMap.adjoint T) = starRingEnd ℂ (traceE b T) := by
  unfold traceE
  rw [Complex.conj_tsum]
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

end QIQTH.TraceClass
