/-
  Phase-B Part A, first brick: a genuine infinite-dimensional NORMAL STATE on `B(H)`.

  Building the full predual / trace-class theory of `B(H)` is a large project (Mathlib has none of it).
  This module delivers the concrete object the prize actually needs — a *normal state* `ω` on `B(H)` —
  for the tractable DIAGONAL case: a diagonal density operator `ρ = ∑ₙ pₙ |eₙ⟩⟨eₙ|` (w.r.t. a Hilbert
  basis `b`, weights `p ≥ 0`, `∑ p = 1`) gives the normal state

      ω(x) = Tr(ρ x) = ∑ₙ pₙ ⟨eₙ, x eₙ⟩        (`diagState`).

  This needs no general Schatten machinery: convergence is by comparison with `∑ pₙ = 1` (each
  `|Re⟨eₙ, x eₙ⟩| ≤ ‖x‖`).  We prove it is a positive, normalized, additive `ℝ`-functional
  (`diagStateHom`, `diagState_nonneg`, `diagState_one`) — i.e. a state — exactly the
  `ω : A →+ ℝ` that `StateNetMeasure.EffectStateNet` consumes, now on the infinite-dimensional `B(H)`.

  This is the diagonal special case of Part-A's normal-state goal (A3); the general trace-class predual
  (A1/A2) would extend it.  Axiom-free.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Tactic

namespace QIQTH.NormalState

open scoped ComplexInnerProductSpace

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normal state of a diagonal density operator `ρ = ∑ₙ pₙ |bₙ⟩⟨bₙ|`:
    `ω(x) = ∑ₙ pₙ · Re⟨bₙ, x bₙ⟩`. -/
noncomputable def diagState (b : HilbertBasis ι ℂ H) (p : ι → ℝ) (x : H →L[ℂ] H) : ℝ :=
  ∑' i, p i * RCLike.re (inner ℂ (b i) (x (b i)))

variable {b : HilbertBasis ι ℂ H} {p : ι → ℝ}

/-- `|Re⟨bᵢ, x bᵢ⟩| ≤ ‖x‖` for a unit basis vector. -/
private theorem abs_re_inner_le (hb : Orthonormal ℂ b) (x : H →L[ℂ] H) (i : ι) :
    |RCLike.re (inner ℂ (b i) (x (b i)))| ≤ ‖x‖ := by
  calc |RCLike.re (inner ℂ (b i) (x (b i)))|
      ≤ ‖inner ℂ (b i) (x (b i))‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖b i‖ * ‖x (b i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b i‖ * (‖x‖ * ‖b i‖) := by gcongr; exact x.le_opNorm (b i)
    _ = ‖x‖ := by rw [hb.norm_eq_one i]; ring

/-- **Convergence**: the diagonal-state series is summable (comparison with `∑ pᵢ = 1`). -/
theorem summable_diagState (hb : Orthonormal ℂ b) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    (x : H →L[ℂ] H) : Summable (fun i => p i * RCLike.re (inner ℂ (b i) (x (b i)))) := by
  apply Summable.of_norm_bounded (g := fun i => p i * ‖x‖) (hsum.mul_right ‖x‖)
  intro i
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hp i)]
  exact mul_le_mul_of_nonneg_left (abs_re_inner_le hb x i) (hp i)

@[simp] theorem diagState_zero (b : HilbertBasis ι ℂ H) (p : ι → ℝ) :
    diagState b p 0 = 0 := by simp [diagState]

/-- The diagonal state is additive. -/
theorem diagState_add (hb : Orthonormal ℂ b) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    (x y : H →L[ℂ] H) : diagState b p (x + y) = diagState b p x + diagState b p y := by
  unfold diagState
  rw [← Summable.tsum_add (summable_diagState hb hp hsum x) (summable_diagState hb hp hsum y)]
  refine tsum_congr fun i => ?_
  simp [ContinuousLinearMap.add_apply, inner_add_right, map_add, mul_add]

/-- The diagonal state of a density operator, bundled as an additive `ℝ`-functional on `B(H)` — the
    `ω : A →+ ℝ` that `EffectStateNet` consumes (here `A = H →L[ℂ] H`). -/
noncomputable def diagStateHom (hb : Orthonormal ℂ b) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) :
    (H →L[ℂ] H) →+ ℝ where
  toFun := diagState b p
  map_zero' := diagState_zero b p
  map_add' := diagState_add hb hp hsum

/-- **Positivity**: the state is nonnegative on positive operators (`0 ≤ ω(x)` for `x ≥ 0`). -/
theorem diagState_nonneg (hp : ∀ i, 0 ≤ p i) (x : H →L[ℂ] H) (hx : x.IsPositive) :
    0 ≤ diagState b p x :=
  tsum_nonneg fun i => mul_nonneg (hp i) (hx.re_inner_nonneg_right (b i))

/-- **Normalization**: `ω(1) = ∑ pᵢ` (`= 1` for a density operator).  So `diagStateHom` of a probability
    weight is a genuine state. -/
theorem diagState_one (hb : Orthonormal ℂ b) :
    diagState b p (1 : H →L[ℂ] H) = ∑' i, p i := by
  unfold diagState
  refine tsum_congr fun i => ?_
  have h1 : RCLike.re (inner ℂ (b i) ((1 : H →L[ℂ] H) (b i))) = 1 := by
    rw [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq, hb.norm_eq_one i, one_pow]
  rw [h1, mul_one]

end QIQTH.NormalState
