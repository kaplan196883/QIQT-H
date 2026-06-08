/-
  Phase-B Part A, general trace-class step A1 — the operator ABSOLUTE VALUE `|T| = √(T⋆ T)`
  (Simon, *Trace Ideals*, §1.1), the foundation of the general (non-diagonal) trace-class theory.

  For a bounded operator `T : H →L[ℂ] H`, `T⋆ T` is self-adjoint with NONNEGATIVE ℝ-spectrum
  (`spectrum_star_mul_self_nonneg`, true in any C\*-algebra — crucially WITHOUT needing the missing
  `StarOrderedRing (B(H))` instance).  So the continuous functional calculus applies and we set
  `|T| := cfc Real.sqrt (T⋆ T)`.  We prove the three §1.1 properties:

    • `absOp_isSelfAdjoint` : `|T|` is self-adjoint;
    • `absOp_mul_self`      : `|T| · |T| = T⋆ T`  (`√x·√x = x` on the nonneg spectrum);
    • `norm_absOp_apply`    : `‖|T| x‖ = ‖T x‖`   (the defining isometry property,
                              `‖|T|x‖² = ⟨x, |T|² x⟩ = ⟨x, T⋆T x⟩ = ‖Tx‖²`).

  This is the first brick of the general Part-A program (trace-class → trace → `Tr(AB)=Tr(BA)` →
  Lidskii), which would extend the diagonal normal state (`NormalState`) to all density operators.
  Axiom-free.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace QIQTH.AbsoluteValue

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **absolute value** `|T| = √(T⋆ T)` of a bounded operator (Simon §1.1), via the continuous
    functional calculus on the positive operator `T⋆ T`. -/
noncomputable def absOp (T : H →L[ℂ] H) : H →L[ℂ] H := cfc Real.sqrt (star T * T)

/-- `|T|` is self-adjoint. -/
theorem absOp_isSelfAdjoint (T : H →L[ℂ] H) : IsSelfAdjoint (absOp T) :=
  cfc_predicate Real.sqrt (star T * T)

/-- **`|T| · |T| = T⋆ T`** — since `√x · √x = x` on the nonnegative spectrum of `T⋆ T`. -/
theorem absOp_mul_self (T : H →L[ℂ] H) : absOp T * absOp T = star T * T := by
  have hcongr : (spectrum ℝ (star T * T)).EqOn (fun x => Real.sqrt x * Real.sqrt x) id :=
    fun x hx => Real.mul_self_sqrt (spectrum_star_mul_self_nonneg x hx)
  unfold absOp
  rw [← cfc_mul Real.sqrt Real.sqrt (star T * T), cfc_congr hcongr, cfc_id ℝ (star T * T)]

/-- **`‖|T| x‖ = ‖T x‖`** — the defining isometry property of the absolute value. -/
theorem norm_absOp_apply (T : H →L[ℂ] H) (x : H) : ‖absOp T x‖ = ‖T x‖ := by
  have hsa : ContinuousLinearMap.adjoint (absOp T) = absOp T := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact absOp_isSelfAdjoint T
  have key : inner ℂ (absOp T x) (absOp T x) = inner ℂ (T x) (T x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right (absOp T) x (absOp T x), hsa,
      ← ContinuousLinearMap.mul_apply, absOp_mul_self, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]

end QIQTH.AbsoluteValue
