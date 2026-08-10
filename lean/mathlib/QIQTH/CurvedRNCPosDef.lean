import QIQTH.CurvedRNCGaugeBundle
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# J4-526 — positive-definiteness / `det > 0` for the curved RNC witness `g^K` (`hgpos`)

This file discharges the remaining geometric-gauge member `hgpos` of the curved-signature capstone
`A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary`, whose binder is literally

```
(hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
```

with `g := CurvedRNCGaussWitness.curvedRNCMetric K`.

## The mathematics

`g^K(x) = δ − (K/3)(‖x‖²δ − x⊗x) = α(x)·I + (K/3)·x xᵀ`, with `α(x) = 1 − (K/3)‖x‖²`.  Its quadratic
form on a vector `w` is

```
wᵀ g^K(x) w = ‖w‖² + (K/3)(⟨x,w⟩² − ‖x‖²‖w‖²)   (curvedRNCMetric_quadForm)
```

For `K ≤ 0` the bracket `⟨x,w⟩² − ‖x‖²‖w‖² ≤ 0` (Cauchy–Schwarz) and `K/3 ≤ 0`, so their product is
`≥ 0` and hence `wᵀ g^K w ≥ ‖w‖² > 0` for `w ≠ 0`.  Thus `g^K(x)` is positive-definite
(`curvedRNCMetric_posDef`), and `Matrix.PosDef.det_pos` gives `det g^K(x) > 0`
(`curvedRNCMetric_det_pos`) — exactly `hgpos`.

## Scope / satisfiability

`K < 0` is genuinely curved (`Ric(0) = (n−1)Kδ ≠ 0`, see `curvedRNCMetric_ricci_trace_diag_ne`) and
lies in the `K ≤ 0` range here, so this positivity is **not** secretly flat.  This is a geometric
completion of the gauge half; it is **NOT** a proof of `a₁ = R/6` — the curved heat-kernel Gaussian
dominations remain the sole analytic wall.
-/

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness
open scoped BigOperators Matrix

namespace QIQTH.CurvedRNCPosDef

variable {n : ℕ}

/-- **The quadratic form of `g^K` at `v` on a vector `w`.**
    `wᵀ g^K(v) w = ‖w‖² + (K/3)(⟨v,w⟩² − ‖v‖²‖w‖²)`. -/
theorem curvedRNCMetric_quadForm (K : ℝ) (v w : Point n) :
    star w ⬝ᵥ (curvedRNCMetric K v *ᵥ w)
      = rncRadialSq w
        + (K / 3) * ((∑ i, v i * w i) ^ 2 - rncRadialSq v * rncRadialSq w) := by
  classical
  -- the inner matrix-vector row, summed over the column index `j`
  have hMrow : ∀ i : Fin n, (∑ j, curvedRNCMetric K v i j * w j)
      = w i - (K / 3) * rncRadialSq v * w i + (K / 3) * v i * (∑ j, v j * w j) := by
    intro i
    have e1 : ∀ j : Fin n, curvedRNCMetric K v i j * w j
        = (if i = j then w j else 0)
          - ((K / 3) * rncRadialSq v) * (if i = j then w j else 0)
          + ((K / 3) * v i) * (v j * w j) := by
      intro j
      by_cases h : i = j
      · simp only [curvedRNCMetric, h, if_true]; ring
      · simp only [curvedRNCMetric, if_neg h]; ring
    rw [Finset.sum_congr rfl (fun j _ => e1 j),
        Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    have hA : (∑ j, (if i = j then w j else 0)) = w i := by
      rw [Finset.sum_ite_eq]; simp
    rw [hA]
  -- expand the two dot products and the mat-vec (all definitional; `star = id` on ℝ is `rfl`)
  have hunf : star w ⬝ᵥ (curvedRNCMetric K v *ᵥ w)
      = ∑ i, w i * (∑ j, curvedRNCMetric K v i j * w j) := rfl
  rw [hunf]
  -- substitute the row identity (explicit target ⇒ no metavariable)
  have hrow2 : (∑ i, w i * (∑ j, curvedRNCMetric K v i j * w j))
      = ∑ i, w i * (w i - (K / 3) * rncRadialSq v * w i
          + (K / 3) * v i * (∑ j, v j * w j)) :=
    Finset.sum_congr rfl (fun i _ => by rw [hMrow i])
  rw [hrow2]
  -- expand each summand into three monomials, then distribute the sum
  have step1 : ∀ i : Fin n,
      w i * (w i - (K / 3) * rncRadialSq v * w i + (K / 3) * v i * (∑ j, v j * w j))
        = (w i) ^ 2 - (K / 3 * rncRadialSq v) * (w i) ^ 2
          + (K / 3 * (∑ j, v j * w j)) * (v i * w i) :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => step1 i),
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, rncRadialSq]
  ring

/-- `g^K(v)` is symmetric hence (real-)Hermitian. -/
theorem curvedRNCMetric_isHermitian (K : ℝ) (v : Point n) :
    Matrix.IsHermitian (curvedRNCMetric K v) := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact curvedRNCMetric_symm K v j i

/-- **`g^K(v)` is positive-definite for `K ≤ 0`.**  Via `wᵀ g^K w = ‖w‖² + (K/3)(⟨v,w⟩² − ‖v‖²‖w‖²)`
    and Cauchy–Schwarz. -/
theorem curvedRNCMetric_posDef (K : ℝ) (hK : K ≤ 0) (v : Point n) :
    Matrix.PosDef (curvedRNCMetric K v) := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (curvedRNCMetric_isHermitian K v) ?_
  intro w hw
  rw [curvedRNCMetric_quadForm K v w]
  have hcs : (∑ i, v i * w i) ^ 2 ≤ rncRadialSq v * rncRadialSq w := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => v i) (fun i => w i)
    simpa only [rncRadialSq] using h
  have hwpos : 0 < rncRadialSq w := rncRadialSq_pos hw
  have hK3 : K / 3 ≤ 0 := by linarith
  have hprod : 0 ≤ (K / 3) * ((∑ i, v i * w i) ^ 2 - rncRadialSq v * rncRadialSq w) := by
    nlinarith [mul_nonneg (neg_nonneg.mpr hK3) (sub_nonneg.mpr hcs)]
  linarith

/-- **`hgpos` for `g^K`.**  `det g^K(v) > 0` for every `v` when `K ≤ 0` — the exact shape of the
    capstone binder `∀ v : Point n, 0 < Matrix.det (g v)`. -/
theorem curvedRNCMetric_det_pos (K : ℝ) (hK : K ≤ 0) (v : Point n) :
    0 < Matrix.det (curvedRNCMetric K v) :=
  Matrix.PosDef.det_pos (curvedRNCMetric_posDef K hK v)

/-- The `hgpos` member packaged over all `v`, ready to feed the capstone antecedent. -/
theorem curvedRNCMetric_hgpos (K : ℝ) (hK : K ≤ 0) :
    ∀ v : Point n, 0 < Matrix.det (curvedRNCMetric K v) :=
  fun v => curvedRNCMetric_det_pos K hK v

#print axioms curvedRNCMetric_quadForm
#print axioms curvedRNCMetric_posDef
#print axioms curvedRNCMetric_hgpos

end QIQTH.CurvedRNCPosDef
