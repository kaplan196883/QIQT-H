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

/-- The coarse α=2 probability of the weight-`2/3` outcome on `(1/3, 2/3)` is `4/5`. -/
theorem alphaSq_coarse_one :
    alphaSqMeasure (![1/3, 2/3] : Fin 2 → ℝ) 1 = 4/5 := by
  simp only [alphaSqMeasure, fMeasure, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- On the uniform triple `(1/3,1/3,1/3)` (the refinement of the `2/3` outcome into two equal
`1/3` sub-records) the α=2 measure is uniform: each fine outcome has probability `1/3`. -/
theorem alphaSq_fine (k : Fin 3) :
    alphaSqMeasure (fun _ => (1/3 : ℝ)) k = 1/3 := by
  simp only [alphaSqMeasure, fMeasure, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **α=2 violates refinement indifference — the precise mechanism.** Refining the weight-`2/3`
outcome of `(1/3, 2/3)` into two equal `1/3` sub-records gives the uniform triple `(1/3,1/3,1/3)`.
Refinement indifference would require the coarse probability of that outcome to equal the sum of
the two fine probabilities; but the coarse α=2 value is `4/5` while the fine sum is `2/3`, and
`4/5 ≠ 2/3`. So α=2 is refinement-inconsistent — it fails exactly the additivity premise that
`additive_fMeasure_eq_born` shows fixes Born. -/
theorem alphaSq_refinement_violation :
    alphaSqMeasure (![1/3, 2/3] : Fin 2 → ℝ) 1
      ≠ alphaSqMeasure (fun _ => (1/3 : ℝ)) (1 : Fin 3)
        + alphaSqMeasure (fun _ => (1/3 : ℝ)) (2 : Fin 3) := by
  rw [alphaSq_coarse_one, alphaSq_fine 1, alphaSq_fine 2]
  norm_num

/-! ### No-signaling under refinement ⇒ Born (route 4, per GPT-5.5-pro 2026-06-13)

The cleanest physical form of the missing premise: **chance is invariant under refining a record**.
Refining a coarse outcome of weight `x+y` (against the rest, of total weight `z`) into two sub-records
of weights `x,y` must leave the coarse outcome's probability unchanged — equal to the sum of the two
fine probabilities. If a *spacelike-separated* choice to refine could change a local coarse frequency,
that would be operational **signaling**; so this is no-signaling under remote refinement, not an ad-hoc
postulate. For the rule `p ∝ f(weight)` it reads `f(x+y)/(f(x+y)+f z) = (f x + f y)/(f x + f y + f z)`. -/

/-- No-signaling under refinement (binary-split form) for the rule `p_k ∝ f(w_k)`: the coarse
probability of a merged outcome of weight `x+y` against remainder `z` equals the sum of the two fine
probabilities. -/
def RefinementNatural (f : ℝ → ℝ) : Prop :=
  ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z →
    f (x + y) / (f (x + y) + f z) = (f x + f y) / (f x + f y + f z)

/-- **No-signaling under refinement ⇒ additivity of `f`.** If the `f`-rule is refinement-natural and
`f` is positive on positive weights, then `f(x+y) = f x + f y`. Composed with
`additive_fMeasure_eq_born` (additivity ⇒ Born), this is the route-4 chain
*no-signaling ⇒ refinement additivity ⇒ Born*. -/
theorem refinementNatural_additive (f : ℝ → ℝ) (hf : ∀ t, 0 < t → 0 < f t)
    (hnat : RefinementNatural f) {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    f (x + y) = f x + f y := by
  have ha : 0 < f (x + y) := hf _ (by linarith)
  have hb1 : 0 < f x := hf _ hx
  have hb2 : 0 < f y := hf _ hy
  have hc : 0 < f z := hf _ hz
  have h := hnat x y z hx hy hz
  rw [div_eq_div_iff (ne_of_gt (by linarith)) (ne_of_gt (by linarith))] at h
  have key : f (x + y) * f z = (f x + f y) * f z := by linear_combination h
  exact mul_right_cancel₀ (ne_of_gt hc) key

/-- **The Born rule (f = id) IS refinement-natural** — the easy direction. This is the abstract
counterpart of the existing physical microcausality results (`NoSignalingGeneral.bipartite_no_signaling`,
`FreeFieldNet.bornNet_no_signaling`): the Born/trace functional is no-signaling *because it is linear*.
Together with `refinementNatural_additive` (the converse: no-signaling ⇒ additive ⇒ Born) this is the iff —
among rules `p ∝ f`, **refinement-natural ⟺ Born**. (The existing theorems give only this easy direction;
the converse — no-signaling forcing Born — is the genuinely load-bearing route-4 content here.) -/
theorem id_refinementNatural : RefinementNatural id := by
  intro x y z _ _ _; simp only [id_eq]

/-- **The α=2 record rule is NOT refinement-natural** — i.e. it signals under refinement. (If it were,
`refinementNatural_additive` would force `(·)²` to be additive, contradicting `sq_not_additive` at
`x=y=1`.) So the `α`-family is exactly excluded by the no-signaling premise. -/
theorem sq_not_refinementNatural : ¬ RefinementNatural (fun t => t ^ 2) := by
  intro hnat
  have h := refinementNatural_additive (fun t => t ^ 2) (fun t ht => pow_pos ht 2) hnat
    (x := 1) (y := 1) (z := 1) one_pos one_pos one_pos
  norm_num at h

end QIQTH.RefinementBorn
