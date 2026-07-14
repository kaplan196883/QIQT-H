/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.TraceClass.CompactSpectral
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Hilbert–Schmidt ⟹ compact, and the unconditional trace-class trace formula

Every **Hilbert–Schmidt** operator `T` on a complex Hilbert space is **compact**: `T` is the
operator-norm limit of its finite-rank truncations `F S x = ∑_{i ∈ S} ⟪bᵢ, x⟫ • T bᵢ`. Each `F S`
is finite-rank (its range lies in the finite-dimensional span of `{T bᵢ : i ∈ S}`), hence compact;
and `‖T - F S‖ ≤ √(∑_{i ∉ S} ‖T bᵢ‖²) → 0` because `∑ᵢ ‖T bᵢ‖² < ∞`. The key estimate is a
Cauchy–Schwarz bound on the ℓ²-tail, using Parseval `∑ᵢ ‖⟪bᵢ, x⟫‖² = ‖x‖²`.

Since **trace-class ⊆ Hilbert–Schmidt** (`IsTraceClass.isHilbertSchmidt`), trace-class operators
are compact too. Combined with the compact self-adjoint spectral theorem
(`compactSelfAdjoint_traceE_eq_tsum_eigenvalues`), this gives the McKean–Singer trace identity for a
**trace-class self-adjoint** operator with **no carried spectral or compactness hypothesis**: its
trace is the sum of its eigenvalues.

## Main results

* `IsHilbertSchmidt.isCompactOperator` : every Hilbert–Schmidt operator is compact.
* `IsTraceClass.isCompactOperator` : every trace-class operator is compact.
* `traceClass_selfAdjoint_traceE_eq_tsum_eigenvalues` : a trace-class self-adjoint operator has an
  eigen-`HilbertBasis` with real eigenvalues `μ` and `traceE b T = ∑' i, μ i` — hypothesis-free.

## Honest firewall

This is **pure functional analysis** completing the standard inclusion
`trace-class ⊆ Hilbert–Schmidt ⊆ compact`. It does **not** touch the manifold input (that the
resolvent of the Laplacian is compact — Rellich–Kondrachov — which remains the wall), does **not**
build the manifold heat kernel, and does **not** discharge the general `a₁ = R/6`. NOT the
conjecture, NOT QG. No axioms, no `sorry`.
-/

open scoped ComplexInnerProductSpace ENNReal NNReal
open ContinuousLinearMap Filter Topology

namespace QIQTH.TraceClass

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Cauchy–Schwarz for `tsum`s of nonnegative real sequences.** If `f² ` and `g²` are summable
then `∑' i, f i · g i ≤ √(∑' i, f i²) · √(∑' i, g i²)`. Proved from the finset Cauchy–Schwarz
inequality by passing partial sums to the limit via `Real.tsum_le_of_sum_le`. -/
private lemma tsum_mul_le_sqrt {ι : Type*} {f g : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf2 : Summable (fun i => f i ^ 2)) (hg2 : Summable (fun i => g i ^ 2)) :
    ∑' i, f i * g i ≤ Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) := by
  rw [← Real.sqrt_mul (tsum_nonneg fun i => sq_nonneg _)]
  refine Real.tsum_le_of_sum_le (fun i => mul_nonneg (hf i) (hg i)) (fun s => ?_)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hfle : ∑ i ∈ s, f i ^ 2 ≤ ∑' i, f i ^ 2 :=
    Summable.sum_le_tsum s (fun i _ => sq_nonneg _) hf2
  have hgle : ∑ i ∈ s, g i ^ 2 ≤ ∑' i, g i ^ 2 :=
    Summable.sum_le_tsum s (fun i _ => sq_nonneg _) hg2
  have hsq : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * (∑' i, g i ^ 2) :=
    le_trans hcs (mul_le_mul hfle hgle (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (tsum_nonneg fun i => sq_nonneg _))
  have hs0 : 0 ≤ ∑ i ∈ s, f i * g i := Finset.sum_nonneg fun i _ => mul_nonneg (hf i) (hg i)
  calc ∑ i ∈ s, f i * g i = Real.sqrt ((∑ i ∈ s, f i * g i) ^ 2) := (Real.sqrt_sq hs0).symm
    _ ≤ Real.sqrt ((∑' i, f i ^ 2) * (∑' i, g i ^ 2)) := Real.sqrt_le_sqrt hsq

/-- **Every Hilbert–Schmidt operator is compact.** `T` is the operator-norm limit of its
finite-rank truncations `F S x = ∑_{i ∈ S} ⟪bᵢ, x⟫ • T bᵢ` (`S : Finset` of basis indices): each
`F S` is finite-rank hence compact, and `‖T - F S‖ ≤ √(∑_{i ∉ S} ‖T bᵢ‖²) → 0`. -/
theorem IsHilbertSchmidt.isCompactOperator {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  have hsum : Summable (fun i => ‖T (b i)‖ ^ 2) := (isHilbertSchmidt_iff_summable b T).mp hT
  -- The finite-rank truncations.
  set F : Finset w → (H →L[ℂ] H) :=
    fun S => ∑ i ∈ S, (innerSL ℂ (b i)).smulRight (T (b i)) with hFdef
  -- (a) Each truncation is compact: its range is a finite-dimensional (locally compact) subspace.
  have hFcompact : ∀ S, IsCompactOperator (F S) := by
    intro S
    set V : Submodule ℂ H :=
      Submodule.span ℂ ((S.image (fun i => T (b i)) : Finset H) : Set H) with hV
    have hmem : ∀ x, F S x ∈ V := by
      intro x
      rw [hFdef, ContinuousLinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i hi => ?_
      rw [ContinuousLinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi)))
    set G : H →L[ℂ] V := (F S).codRestrict V hmem with hG
    have hGc : IsCompactOperator G := isCompactOperator_of_locallyCompactSpace_dom G
    have hcomp : IsCompactOperator (⇑V.subtypeL ∘ ⇑G) := hGc.clm_comp V.subtypeL
    have hfun : ⇑V.subtypeL ∘ ⇑G = ⇑(F S) := by funext x; rfl
    rwa [hfun] at hcomp
  -- (b) The truncations converge to `T` in operator norm.
  have hTend : Tendsto F atTop (𝓝 T) := by
    have htail0 :
        Tendsto (fun S : Finset w => ∑' a : {x // x ∉ S}, ‖T (b a)‖ ^ 2) atTop (𝓝 0) :=
      tendsto_tsum_compl_atTop_zero (fun i => ‖T (b i)‖ ^ 2)
    -- Pointwise tail bound `‖(T - F S) x‖ ≤ √(tail S) · ‖x‖`.
    have hbound : ∀ S x, ‖(T - F S) x‖ ≤ Real.sqrt (∑' a : {x // x ∉ S}, ‖T (b a)‖ ^ 2) * ‖x‖ := by
      intro S x
      have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      have hParsSum : Summable (fun i => ‖b.repr x i‖ ^ 2) := by
        have h := (lp.memℓp (b.repr x)).summable hp
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
      have hParsVal : ∑' i, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
        have h := lp.norm_rpow_eq_tsum hp (b.repr x)
        simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] at h
        exact h.symm
      set g : w → H := fun i => b.repr x i • T (b i) with hg
      have hgabs : Summable (fun i => ‖g i‖) := by
        have hb : ∀ i, ‖g i‖ ≤ ‖b.repr x i‖ ^ 2 + ‖T (b i)‖ ^ 2 := by
          intro i
          rw [hg, norm_smul]
          nlinarith [sq_nonneg (‖b.repr x i‖ - ‖T (b i)‖), norm_nonneg (b.repr x i),
            norm_nonneg (T (b i))]
        exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) hb (hParsSum.add hsum)
      have hgsum : Summable g := hgabs.of_norm
      have hTx : HasSum g (T x) := by
        have h := (b.hasSum_repr x).mapL T
        simpa only [hg, ContinuousLinearMap.map_smul] using h
      have hFSx : F S x = ∑ i ∈ S, g i := by
        simp only [hFdef, hg, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
          innerSL_apply_apply, HilbertBasis.repr_apply_apply]
      have hcompl : (T - F S) x = ∑' a : {x // x ∉ S}, g a := by
        rw [ContinuousLinearMap.sub_apply, hFSx, ← hTx.tsum_eq]
        have hs : (∑ i ∈ S, g i) + ∑' a : {x // x ∉ S}, g a = ∑' i, g i :=
          hgsum.sum_add_tsum_compl
        rw [← hs, add_sub_cancel_left]
      rw [hcompl]
      have hgcompl_abs : Summable (fun a : {x // x ∉ S} => ‖g a‖) := hgabs.subtype _
      calc ‖∑' a : {x // x ∉ S}, g a‖
          ≤ ∑' a : {x // x ∉ S}, ‖g a‖ := norm_tsum_le_tsum_norm hgcompl_abs
        _ = ∑' a : {x // x ∉ S}, ‖b.repr x a‖ * ‖T (b a)‖ := by
            refine tsum_congr fun a => ?_
            rw [hg, norm_smul]
        _ ≤ Real.sqrt (∑' a : {x // x ∉ S}, ‖b.repr x a‖ ^ 2)
              * Real.sqrt (∑' a : {x // x ∉ S}, ‖T (b a)‖ ^ 2) :=
            tsum_mul_le_sqrt (fun a => norm_nonneg _) (fun a => norm_nonneg _)
              (hParsSum.subtype _) (hsum.subtype _)
        _ ≤ ‖x‖ * Real.sqrt (∑' a : {x // x ∉ S}, ‖T (b a)‖ ^ 2) := by
            gcongr
            rw [show ‖x‖ = Real.sqrt (‖x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm, ← hParsVal]
            exact Real.sqrt_le_sqrt
              (tsum_comp_le_tsum_of_inj hParsSum (fun i => sq_nonneg _) Subtype.val_injective)
        _ = Real.sqrt (∑' a : {x // x ∉ S}, ‖T (b a)‖ ^ 2) * ‖x‖ := by ring
    -- Turn the pointwise bound into an operator-norm bound and squeeze.
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hopbound : ∀ S, ‖F S - T‖ ≤ Real.sqrt (∑' a : {x // x ∉ S}, ‖T (b a)‖ ^ 2) := by
      intro S
      rw [show F S - T = -(T - F S) from by abel, norm_neg]
      exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun x => hbound S x)
    refine squeeze_zero (fun S => norm_nonneg _) hopbound ?_
    have hcomp := (Real.continuous_sqrt.tendsto 0).comp htail0
    simpa using hcomp
  exact isCompactOperator_of_tendsto hTend (Eventually.of_forall hFcompact)

/-- **Every trace-class operator is compact** (via `trace-class ⊆ Hilbert–Schmidt`). -/
theorem IsTraceClass.isCompactOperator {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsCompactOperator T :=
  hT.isHilbertSchmidt.isCompactOperator

/-- **Trace = sum of eigenvalues for a trace-class self-adjoint operator, unconditionally.**
Combining `IsTraceClass.isCompactOperator` with the compact self-adjoint spectral theorem
`compactSelfAdjoint_traceE_eq_tsum_eigenvalues`: a trace-class self-adjoint `T` has an eigen-Hilbert
basis `b` with real eigenvalues `μ` and `traceE b T = ∑' i, μ i` — with **no** carried spectral or
compactness hypothesis. -/
theorem traceClass_selfAdjoint_traceE_eq_tsum_eigenvalues {T : H →L[ℂ] H}
    (htc : IsTraceClass T) (hsa : IsSelfAdjoint T) :
    ∃ (κ : Type u) (b : HilbertBasis κ ℂ H) (μ : κ → ℝ),
      (∀ i, T (b i) = ((μ i : ℝ) : ℂ) • b i) ∧ traceE b T = ∑' i, ((μ i : ℝ) : ℂ) :=
  compactSelfAdjoint_traceE_eq_tsum_eigenvalues htc.isCompactOperator hsa

end QIQTH.TraceClass
