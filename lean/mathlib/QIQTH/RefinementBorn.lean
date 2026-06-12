/-
RefinementBorn.lean — the exact extra premise behind the Born *weights*.

QIQT-H records (finite capacity ⇒ definite, redundantly-broadcast pointer values) give a
Boolean pointer algebra and a probability rule, but they do NOT fix the Born EXPONENT.
This file isolates exactly what does.

NEGATIVE (records ⇏ Born): the α=2 record measure  μ₂(k) = w_k² / Σ_j w_j²  is a genuine
probability (normalized), yet already disagrees with Born on the weights (1/3, 2/3).
A rule satisfying every "record fact" (definiteness, redundancy agreement, support,
certainty, label symmetry, product independence) can therefore be non-Born.

POSITIVE (refinement additivity ⇒ Born): writing a rule as p_k = f(w_k) / Σ_j f(w_j),
if `f` is ADDITIVE then p = Born on (rational) weights. Refinement / coarse-graining
indifference — splitting an outcome of weight x+y into sub-records of weights x,y leaves
the coarse probability fixed — is exactly the additivity f(x+y)=f(x)+f(y); and (·)² is
not additive, so the α≠1 family is excluded precisely by refinement additivity. The record
structure does not supply that premise (GPT-5.5-pro cross-check, 2026-06-13).
See `paper_strategy/49_Born_Status.md` §5.

HONEST SCOPE: finite-dimensional; no `sorry`, no project axioms. This pins down the missing
premise. Whether finite capacity / H2 MOTIVATES refinement additivity is the genuine open
physics question — it is NOT settled here.
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

open scoped BigOperators

namespace QIQTH.RefinementBorn

variable {n : ℕ}

/-- A probability rule built from a function `f` of the Hilbert weights:
`p_k = f(w_k) / Σ_j f(w_j)`.  Born is the case `f = id`; the α=2 record measure is `f = (·²)`. -/
noncomputable def fMeasure (f : ℝ → ℝ) (w : Fin n → ℝ) (k : Fin n) : ℝ :=
  f (w k) / ∑ j, f (w j)

/-- The α = 2 record measure `μ₂(k) = w_k² / Σ_j w_j²`. -/
noncomputable def alphaSqMeasure (w : Fin n → ℝ) (k : Fin n) : ℝ :=
  fMeasure (fun t => t ^ 2) w k

/-- `μ₂` is a genuine probability: it sums to `1` whenever the denominator is nonzero. -/
theorem alphaSqMeasure_sum (w : Fin n → ℝ) (h : ∑ j, (w j) ^ 2 ≠ 0) :
    ∑ k, alphaSqMeasure w k = 1 := by
  unfold alphaSqMeasure fMeasure
  rw [← Finset.sum_div]
  exact div_self h

/-- The α=2 record measure on the weights `(1/3, 2/3)` returns `1/5` for the first outcome. -/
theorem alphaSq_value :
    alphaSqMeasure (![1/3, 2/3] : Fin 2 → ℝ) 0 = 1/5 := by
  simp only [alphaSqMeasure, fMeasure, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **Records ⇏ Born — the load-bearing negative result.** The Born weight of the first
outcome is `1/3`, but the α=2 record measure returns `1/5 ≠ 1/3`. So a probability rule
satisfying all the record facts can disagree with Born; the record structure alone does not
fix the exponent. -/
theorem alphaSq_ne_born :
    alphaSqMeasure (![1/3, 2/3] : Fin 2 → ℝ) 0 ≠ (1/3 : ℝ) := by
  rw [alphaSq_value]; norm_num

/-- `(·)²` is not additive — the precise premise the α=2 rule violates. -/
theorem sq_not_additive : ∃ x y : ℝ, (x + y) ^ 2 ≠ x ^ 2 + y ^ 2 := by
  exact ⟨1, 1, by norm_num⟩

/-- **Refinement additivity ⇒ Born.** If the rule's function `f` is additive (`f : ℝ →+ ℝ`,
with `f 1 ≠ 0`) — which is exactly refinement / coarse-graining indifference — then on any
rational weights summing to `1` the rule *is* the Born rule `p_k = w_k`. Together with
`sq_not_additive`/`alphaSq_ne_born` this shows additivity is the exponent-fixing premise. -/
theorem additive_fMeasure_eq_born (f : ℝ →+ ℝ) (h1 : f 1 ≠ 0)
    {q : Fin n → ℚ} (hsum : ∑ j, (q j : ℝ) = 1) (k : Fin n) :
    fMeasure f (fun j => (q j : ℝ)) k = (q k : ℝ) := by
  have hlin : ∀ r : ℚ, f (r : ℝ) = (r : ℝ) * f 1 := by
    intro r
    have h := map_ratCast_smul f ℝ ℝ r (1 : ℝ)
    simpa [Rat.smul_def, mul_one] using h
  unfold fMeasure
  have hden : ∑ j, f ((q j : ℝ)) = f 1 := by
    simp_rw [hlin]
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [hden, hlin, mul_div_assoc, div_self h1, mul_one]

end QIQTH.RefinementBorn
