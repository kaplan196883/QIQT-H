/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.TraceClass.Trace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The trace-class ideal property and cyclicity `Tr (A B) = Tr (B A)`

The two-sided **ideal** property of the trace-class operators (`A` trace-class, `B` bounded ⟹
`A ∘ B` and `B ∘ A` trace-class) and the **cyclicity** of the trace `Tr (A B) = Tr (B A)`. **T3** of
the trace-class API (**L5** of the heat-kernel full-infrastructure plan) — pure functional analysis,
no manifold/PDE. This completes the trace's algebraic laws and is FOUNDATION for `Tr e^{−tΔ}`, but it
does NOT itself build the heat kernel or discharge the general `a₁ = R/6` (L1/L3 manifold analysis
stay the wall). NOT the conjecture, NOT QG. No axioms, no `sorry`.

## Main results

* `matrixElt_summable_sq` : the matrix entries `S_{ij} = ⟪b i, S (b j)⟫` are square-summable over
  `ι × ι` (with total mass `‖S‖²_HS`) for a Hilbert–Schmidt operator `S`.
* `traceE_comp_eq_tsum_matrixElt` : `Tr (S ∘ T) = ∑'_{i,k} S_{ik} T_{ki}` — the matrix-element
  double-sum form of the trace of a product of Hilbert–Schmidt operators.
* `traceE_comp_comm_hs` : **cyclicity for Hilbert–Schmidt operators**, `Tr (S ∘ T) = Tr (T ∘ S)`.
* `IsHilbertSchmidt.comp_right` : the right two-sided ideal bound (`D` HS, `B` bounded ⟹ `D ∘ B` HS).
* `IsTraceClass.comp_right_bounded` / `IsTraceClass.comp_left_bounded` : the trace-class operators
  form a two-sided ideal in the bounded operators.
* `traceE_comp_comm` : **general cyclicity**, `Tr (A ∘ B) = Tr (B ∘ A)` for `A` trace-class and
  `B` bounded. Basis-independent by `traceE_basis_indep` since both sides are trace-class.

## Implementation notes

The load-bearing core is the matrix-element double-sum (`traceE_comp_eq_tsum_matrixElt`) plus the
`(i,k) ↔ (k,i)` relabel (`traceE_comp_comm_hs`). The per-term Parseval insertion reuses Mathlib's
`HilbertBasis.tsum_inner_mul_inner`; absolute summability over `ι × ι` is Cauchy–Schwarz
(`two_mul_le_add_sq`) against the square-summable matrix entries; the interchange of the double sum
is `Summable.tsum_prod` and the relabel is `Equiv.prodComm`. The general cyclicity reduces to the
Hilbert–Schmidt case via the factorization `A = C⋆ ∘ D` and the ideal bounds (`adjoint_comp`).
-/

open scoped ENNReal NNReal ComplexInnerProductSpace

namespace QIQTH.TraceClass

variable {ι κ : Type*} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Real Parseval per vector (extracted from T1's `parsevalE` proof) -/

omit [CompleteSpace H] in
/-- The `b`-coefficients of a vector are square-summable. -/
theorem inner_sq_summable (b : HilbertBasis ι ℂ H) (x : H) :
    Summable (fun i => ‖(inner ℂ (b i) x : ℂ)‖ ^ 2) := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := (lp.memℓp (b.repr x)).summable hp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply] using h

omit [CompleteSpace H] in
/-- **Real Parseval.** The squared norm of a vector is the sum of the squared `b`-coefficients. -/
theorem inner_sq_tsum (b : HilbertBasis ι ℂ H) (x : H) :
    ∑' i, ‖(inner ℂ (b i) x : ℂ)‖ ^ 2 = ‖x‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp (b.repr x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply,
    LinearIsometryEquiv.norm_map] at h
  exact h.symm

/-! ### Square-summability of the matrix entries -/

/-- **The matrix entries `S_{ij} = ⟪b i, S (b j)⟫` are square-summable over `ι × ι`.** Summing over
the row index first collapses (Parseval) to `∑' j, ‖S (b j)‖²`, which is `‖S‖²_HS < ∞`. -/
theorem matrixElt_summable_sq (b : HilbertBasis ι ℂ H) {S : H →L[ℂ] H} (hS : IsHilbertSchmidt S) :
    Summable (fun p : ι × ι => ‖(inner ℂ (b p.1) (S (b p.2)) : ℂ)‖ ^ 2) := by
  rw [← (Equiv.prodComm ι ι).summable_iff]
  refine (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    ⟨fun x => inner_sq_summable b (S (b x)), ?_⟩
  exact (hS.summable_normSq b).congr (fun x => (inner_sq_tsum b (S (b x))).symm)

/-! ### The matrix-element form of the trace of a product -/

/-- Per-diagonal-term Parseval insertion: `⟪b i, S (T (b i))⟫ = ∑' k, ⟪b i, S (b k)⟫ ⟪b k, T (b i)⟫`,
via `⟪b i, S (T (b i))⟫ = ⟪S⋆ (b i), T (b i)⟫` and `HilbertBasis.tsum_inner_mul_inner`. -/
private theorem traceE_comp_term (S T : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (i : ι) :
    (inner ℂ (b i) (S (T (b i))) : ℂ)
      = ∑' k, (inner ℂ (b i) (S (b k)) : ℂ) * (inner ℂ (b k) (T (b i)) : ℂ) := by
  have h := b.tsum_inner_mul_inner (ContinuousLinearMap.adjoint S (b i)) (T (b i))
  rw [ContinuousLinearMap.adjoint_inner_left] at h
  rw [← h]
  refine tsum_congr fun k => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- **The trace of a product of Hilbert–Schmidt operators as a matrix-element double sum:**
`Tr (S ∘ T) = ∑'_{(i,k)} ⟪b i, S (b k)⟫ ⟪b k, T (b i)⟫`. Absolute summability over `ι × ι` is
Cauchy–Schwarz (`‖S_{ik} T_{ki}‖ ≤ ½(‖S_{ik}‖² + ‖T_{ki}‖²)`) against `matrixElt_summable_sq`. -/
theorem traceE_comp_eq_tsum_matrixElt (b : HilbertBasis ι ℂ H) {S T : H →L[ℂ] H}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    traceE b (S.comp T)
      = ∑' p : ι × ι, (inner ℂ (b p.1) (S (b p.2)) : ℂ) * (inner ℂ (b p.2) (T (b p.1)) : ℂ) := by
  have Asum := matrixElt_summable_sq b hS
  have Bsum : Summable (fun p : ι × ι => ‖(inner ℂ (b p.2) (T (b p.1)) : ℂ)‖ ^ 2) :=
    (Equiv.prodComm ι ι).summable_iff.mpr (matrixElt_summable_sq b hT)
  have hg : Summable (fun p : ι × ι =>
      (inner ℂ (b p.1) (S (b p.2)) : ℂ) * (inner ℂ (b p.2) (T (b p.1)) : ℂ)) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((Asum.add Bsum).div_const 2)
    rw [norm_mul]
    nlinarith [two_mul_le_add_sq ‖(inner ℂ (b p.1) (S (b p.2)) : ℂ)‖
        ‖(inner ℂ (b p.2) (T (b p.1)) : ℂ)‖,
      norm_nonneg (inner ℂ (b p.1) (S (b p.2)) : ℂ),
      norm_nonneg (inner ℂ (b p.2) (T (b p.1)) : ℂ)]
  rw [hg.tsum_prod]
  unfold traceE
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.comp_apply]
  exact traceE_comp_term S T b i

/-! ### Cyclicity for Hilbert–Schmidt operators -/

/-- **Cyclicity of the trace for Hilbert–Schmidt operators:** `Tr (S ∘ T) = Tr (T ∘ S)`. The two
matrix-element double sums are related by the `(i,k) ↔ (k,i)` relabel `Equiv.prodComm`. -/
theorem traceE_comp_comm_hs (b : HilbertBasis ι ℂ H) {S T : H →L[ℂ] H}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    traceE b (S.comp T) = traceE b (T.comp S) := by
  rw [traceE_comp_eq_tsum_matrixElt b hS hT, traceE_comp_eq_tsum_matrixElt b hT hS,
    ← (Equiv.prodComm ι ι).tsum_eq
      (fun p : ι × ι => (inner ℂ (b p.1) (S (b p.2)) : ℂ) * (inner ℂ (b p.2) (T (b p.1)) : ℂ))]
  refine tsum_congr fun p => ?_
  rw [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]

/-! ### The trace-class two-sided ideal -/

/-- **Right two-sided ideal bound for Hilbert–Schmidt operators.** `D ∘ B` is HS whenever `D` is HS
and `B` is bounded (via `(D ∘ B)⋆ = B⋆ ∘ D⋆` and the left ideal bound). -/
theorem IsHilbertSchmidt.comp_right {D : H →L[ℂ] H} (hD : IsHilbertSchmidt D) (B : H →L[ℂ] H) :
    IsHilbertSchmidt (D.comp B) := by
  rw [isHilbertSchmidt_adjoint, ContinuousLinearMap.adjoint_comp]
  exact ((isHilbertSchmidt_adjoint D).mp hD).comp_left (ContinuousLinearMap.adjoint B)

/-- **The trace-class operators are a right ideal:** `A ∘ B` is trace-class for `A` trace-class and
`B` bounded (`A = C⋆ ∘ D`, so `A ∘ B = C⋆ ∘ (D ∘ B)` with `D ∘ B` HS). -/
theorem IsTraceClass.comp_right_bounded {A : H →L[ℂ] H} (hA : IsTraceClass A) (B : H →L[ℂ] H) :
    IsTraceClass (A.comp B) := by
  obtain ⟨C, D, hC, hD, rfl⟩ := hA
  refine ⟨C, D.comp B, hC, hD.comp_right B, ?_⟩
  rw [ContinuousLinearMap.comp_assoc]

/-- **The trace-class operators are a left ideal:** `B ∘ A` is trace-class for `A` trace-class and
`B` bounded (`A = C⋆ ∘ D`, so `B ∘ A = (C ∘ B⋆)⋆ ∘ D` with `C ∘ B⋆` HS). -/
theorem IsTraceClass.comp_left_bounded {A : H →L[ℂ] H} (hA : IsTraceClass A) (B : H →L[ℂ] H) :
    IsTraceClass (B.comp A) := by
  obtain ⟨C, D, hC, hD, rfl⟩ := hA
  refine ⟨C.comp (ContinuousLinearMap.adjoint B), D, hC.comp_right _, hD, ?_⟩
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

/-! ### General cyclicity -/

/-- **Cyclicity of the trace** `Tr (A ∘ B) = Tr (B ∘ A)` for `A` trace-class and `B` bounded. Reduces
to the Hilbert–Schmidt case via `A = C⋆ ∘ D`: both sides equal `Tr (D ∘ (B ∘ C⋆))`. Both traces are
of trace-class operators (ideal property), hence this identity is basis-independent. -/
theorem traceE_comp_comm (b : HilbertBasis ι ℂ H) {A : H →L[ℂ] H} (hA : IsTraceClass A)
    (B : H →L[ℂ] H) : traceE b (A.comp B) = traceE b (B.comp A) := by
  obtain ⟨C, D, hC, hD, rfl⟩ := hA
  have hCadj : IsHilbertSchmidt (ContinuousLinearMap.adjoint C) := (isHilbertSchmidt_adjoint C).mp hC
  have hDB : IsHilbertSchmidt (D.comp B) := hD.comp_right B
  have hBC : IsHilbertSchmidt (B.comp (ContinuousLinearMap.adjoint C)) := hCadj.comp_left B
  calc traceE b (((ContinuousLinearMap.adjoint C).comp D).comp B)
      = traceE b ((ContinuousLinearMap.adjoint C).comp (D.comp B)) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = traceE b ((D.comp B).comp (ContinuousLinearMap.adjoint C)) :=
        traceE_comp_comm_hs b hCadj hDB
    _ = traceE b (D.comp (B.comp (ContinuousLinearMap.adjoint C))) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = traceE b ((B.comp (ContinuousLinearMap.adjoint C)).comp D) :=
        traceE_comp_comm_hs b hD hBC
    _ = traceE b (B.comp ((ContinuousLinearMap.adjoint C).comp D)) := by
        rw [ContinuousLinearMap.comp_assoc]

end QIQTH.TraceClass
