/-
  Finite Born-typicality — a NON-VACUOUS replacement for the placeholder
  `BornTypicality.LLN_typicality_axiom` (whose conclusion was `∃ N, True`).

  Self-contained finite probability (no measure-theory infrastructure): the
  sample space is `Ω = Fin N → Fin m` (N i.i.d. trials, m outcomes) with the
  product weight `w p ω = ∏ t, p (ω t)` of a probability vector `p`.  We prove,
  axiom-free:

    • `w_nonneg`         the weight is nonnegative;
    • `sum_w_eq_one`     it is a genuine probability distribution (∑ = 1);
    • `expectation_count`  E[#{t : ω t = k}] = N · p k   (empirical counts are
                           UNBIASED estimators of the Born weight p k).

  For the QIQT-H reading, `p k = tr(ρ E_k)` (Born weights of a finite POVM):
  the canonical product measure assigns those weights as the expected
  frequencies.  We also prove the full CONCENTRATION direction:

    • `marginal2`/`expectation_count_sq`/`variance_count`  the binomial variance
                         `E[(count − N·p k)²] = N·p k·(1 − p k)`;
    • `markov_le`/`chebyshev_count`  finite Markov / Chebyshev on the squared deviation;
    • `chebyshev_freq`   the CLEAN typicality bound: the weight of `|freq − p k| ≥ ε`
                         is `≤ p k·(1 − p k) / (N·ε²)`.

  So `P(|freq − p k| ≥ ε) → 0` as `N → ∞`: empirical frequencies are typically the
  Born weights.  This is the genuine finite content that the vacuous
  `BornTypicality.LLN_typicality_axiom` (`∃ N, True`) only gestured at.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace QIQTH
namespace BornTypicalityFinite

open Finset

variable {m N : ℕ}

/-- Product weight of a sample path `ω : Fin N → Fin m` under a probability
    vector `p : Fin m → ℝ`. -/
def w (p : Fin m → ℝ) (ω : Fin N → Fin m) : ℝ := ∏ t, p (ω t)

/-- Empirical count of outcome `k` along `ω` (as a real number). -/
def count (k : Fin m) (ω : Fin N → Fin m) : ℝ := ∑ t, if ω t = k then (1 : ℝ) else 0

/-- The product weight is nonnegative. -/
theorem w_nonneg (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (ω : Fin N → Fin m) :
    0 ≤ w p ω :=
  Finset.prod_nonneg (fun t _ => hp (ω t))

/-- **The product weight is a probability distribution:** `∑_ω w p ω = 1`. -/
theorem sum_w_eq_one (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) :
    ∑ ω : Fin N → Fin m, w p ω = 1 := by
  calc ∑ ω : Fin N → Fin m, w p ω
      = ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => (univ : Finset (Fin m))), ∏ t, p (ω t) := by
        unfold w; rw [Fintype.piFinset_univ]
    _ = ∏ _t : Fin N, ∑ j, p j :=
        (Finset.prod_univ_sum (fun _ : Fin N => (univ : Finset (Fin m))) (fun _ j => p j)).symm
    _ = 1 := by simp [hp1]

/-- **Single-trial marginal:** summing the product weight against the indicator
    `[ω s = k]` recovers the Born weight `p k` (the `s`-th coordinate is
    distributed as `p`, the others sum out to `1`). -/
theorem marginal (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) (k : Fin m) (s : Fin N) :
    ∑ ω : Fin N → Fin m, (∏ t, p (ω t)) * (if ω s = k then (1 : ℝ) else 0) = p k := by
  have key : ∀ ω : Fin N → Fin m,
      (∏ t, p (ω t)) * (if ω s = k then (1 : ℝ) else 0)
        = ∏ t, p (ω t) * (if t = s then (if ω t = k then (1 : ℝ) else 0) else 1) := by
    intro ω
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ s, if_pos (mem_univ s)]
  simp_rw [key]
  calc ∑ ω : Fin N → Fin m,
          ∏ t, p (ω t) * (if t = s then (if ω t = k then (1 : ℝ) else 0) else 1)
      = ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => (univ : Finset (Fin m))),
          ∏ t, p (ω t) * (if t = s then (if ω t = k then (1 : ℝ) else 0) else 1) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ t : Fin N, ∑ j, p j * (if t = s then (if j = k then (1 : ℝ) else 0) else 1) :=
        (Finset.prod_univ_sum _
          (fun t j => p j * (if t = s then (if j = k then (1 : ℝ) else 0) else 1))).symm
    _ = ∏ t : Fin N, (if t = s then p k else 1) := by
        refine Finset.prod_congr rfl (fun t _ => ?_)
        by_cases ht : t = s
        · simp only [ht, if_true]
          simp_rw [mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq' univ k (fun j => p j), if_pos (mem_univ k)]
        · simp only [ht, if_false, mul_one]; exact hp1
    _ = p k := by rw [Finset.prod_ite_eq' univ s (fun _ => p k), if_pos (mem_univ s)]

/-- **Two-coordinate marginal:** `∑_ω w(ω)·[ω s = k]·[ω s' = k] = p k` if `s = s'`
    (idempotent indicator) and `p k · p k` if `s ≠ s'` (independence of distinct
    trials).  This is the covariance structure behind the variance. -/
theorem marginal2 (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) (k : Fin m) (s s' : Fin N) :
    ∑ ω : Fin N → Fin m,
        (∏ t, p (ω t)) * (if ω s = k then (1 : ℝ) else 0) * (if ω s' = k then (1 : ℝ) else 0)
      = if s = s' then p k else p k * p k := by
  by_cases hss : s = s'
  · subst hss
    rw [if_pos rfl]
    have hidem : ∀ ω : Fin N → Fin m,
        (∏ t, p (ω t)) * (if ω s = k then (1 : ℝ) else 0) * (if ω s = k then (1 : ℝ) else 0)
          = (∏ t, p (ω t)) * (if ω s = k then (1 : ℝ) else 0) := by
      intro ω; rw [mul_assoc]; congr 1; by_cases h : ω s = k <;> simp [h]
    simp_rw [hidem]; exact marginal p hp1 k s
  · rw [if_neg hss]
    have key : ∀ ω : Fin N → Fin m,
        (∏ t, p (ω t)) * (if ω s = k then (1 : ℝ) else 0) * (if ω s' = k then (1 : ℝ) else 0)
          = ∏ t, p (ω t) * (if t = s then (if ω t = k then (1 : ℝ) else 0) else 1)
                  * (if t = s' then (if ω t = k then (1 : ℝ) else 0) else 1) := by
      intro ω
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_ite_eq' univ s, if_pos (mem_univ s),
        Finset.prod_ite_eq' univ s', if_pos (mem_univ s')]
    simp_rw [key]
    calc ∑ ω : Fin N → Fin m, ∏ t, p (ω t) * (if t = s then (if ω t = k then (1 : ℝ) else 0) else 1)
              * (if t = s' then (if ω t = k then (1 : ℝ) else 0) else 1)
        = ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => (univ : Finset (Fin m))),
            ∏ t, p (ω t) * (if t = s then (if ω t = k then (1 : ℝ) else 0) else 1)
              * (if t = s' then (if ω t = k then (1 : ℝ) else 0) else 1) := by
          rw [Fintype.piFinset_univ]
      _ = ∏ t : Fin N, ∑ j, p j * (if t = s then (if j = k then (1 : ℝ) else 0) else 1)
              * (if t = s' then (if j = k then (1 : ℝ) else 0) else 1) :=
          (Finset.prod_univ_sum _ (fun t j => p j
            * (if t = s then (if j = k then (1 : ℝ) else 0) else 1)
            * (if t = s' then (if j = k then (1 : ℝ) else 0) else 1))).symm
      _ = ∏ t : Fin N, ((if t = s then p k else 1) * (if t = s' then p k else 1)) := by
          refine Finset.prod_congr rfl (fun t _ => ?_)
          by_cases hts : t = s
          · have hts2 : ¬ t = s' := fun h => hss (hts ▸ h)
            simp [if_pos hts, if_neg hts2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
          · by_cases hts2 : t = s'
            · simp [if_neg hts, if_pos hts2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
            · simp only [if_neg hts, if_neg hts2, mul_one]; exact hp1
      _ = p k * p k := by
          rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ s, if_pos (mem_univ s),
            Finset.prod_ite_eq' univ s', if_pos (mem_univ s')]

/-- **Empirical counts are unbiased estimators of the Born weight:**
    `E[#{t : ω t = k}] = N · p k`.  (Linearity of expectation over the `N`
    i.i.d. trials, each `marginal` giving `p k`.) -/
theorem expectation_count (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) (k : Fin m) :
    ∑ ω : Fin N → Fin m, w p ω * count k ω = (N : ℝ) * p k := by
  simp only [w, count, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [marginal p hp1 k]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Second moment of the empirical count:** `E[count² ] = ∑_{s,s'} two-coordinate
    marginal` — the double sum of `marginal2`. -/
theorem expectation_count_sq (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) (k : Fin m) :
    ∑ ω : Fin N → Fin m, w p ω * (count k ω) ^ 2
      = ∑ s : Fin N, ∑ s' : Fin N, (if s = s' then p k else p k * p k) := by
  have expand : ∀ ω : Fin N → Fin m, w p ω * (count k ω) ^ 2
      = ∑ s : Fin N, ∑ s' : Fin N,
          (∏ t, p (ω t)) * (if ω s = k then (1 : ℝ) else 0) * (if ω s' = k then (1 : ℝ) else 0) := by
    intro ω
    rw [sq, count, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    simp only [w]; ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  exact marginal2 p hp1 k s s'

/-- **Finite Markov inequality** for the product measure: for a nonnegative
    observable `g` and threshold `c > 0`, the weight of `{g ≥ c}` is at most
    `E[g] / c`. -/
theorem markov_le (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i)
    (g : (Fin N → Fin m) → ℝ) (hg : ∀ ω, 0 ≤ g ω) {c : ℝ} (hc : 0 < c) :
    (∑ ω ∈ univ.filter (fun ω => c ≤ g ω), w p ω) ≤ (∑ ω, w p ω * g ω) / c := by
  rw [le_div_iff₀ hc]
  calc (∑ ω ∈ univ.filter (fun ω => c ≤ g ω), w p ω) * c
      = ∑ ω ∈ univ.filter (fun ω => c ≤ g ω), w p ω * c := by rw [Finset.sum_mul]
    _ ≤ ∑ ω ∈ univ.filter (fun ω => c ≤ g ω), w p ω * g ω := by
        refine Finset.sum_le_sum (fun ω hω => ?_)
        rw [Finset.mem_filter] at hω
        exact mul_le_mul_of_nonneg_left hω.2 (w_nonneg p hp ω)
    _ ≤ ∑ ω, w p ω * g ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => mul_nonneg (w_nonneg p hp ω) (hg ω))

/-- **Chebyshev concentration for empirical counts.**  The weight of the
    deviation event `(count − N·p k)² ≥ (N·ε)²` (equivalently `|freq − p k| ≥ ε`)
    is bounded by the second moment over `(N·ε)²`.  Combined with
    `expectation_count` (`E[count] = N·p k`), the second-moment numerator is the
    variance `N·p k·(1−p k)`, giving the standard `p(1−p)/(Nε²)` typicality bound
    once that variance is computed. -/
theorem chebyshev_count (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (k : Fin m)
    {ε : ℝ} (hε : 0 < ε) (hN : 0 < N) :
    (∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter
          (fun ω => ((N : ℝ) * ε) ^ 2 ≤ (count k ω - (N : ℝ) * p k) ^ 2), w p ω)
      ≤ (∑ ω : Fin N → Fin m, w p ω * (count k ω - (N : ℝ) * p k) ^ 2) / ((N : ℝ) * ε) ^ 2 := by
  -- (Markov inequality on the squared deviation, inlined to keep `N` concrete.)
  rw [le_div_iff₀ (pow_pos (mul_pos (by exact_mod_cast hN) hε) 2), Finset.sum_mul]
  refine (Finset.sum_le_sum fun ω hω => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω _ _ => mul_nonneg (w_nonneg p hp ω) (sq_nonneg _)))
  rw [Finset.mem_filter] at hω
  exact mul_le_mul_of_nonneg_left hω.2 (w_nonneg p hp ω)

/-- **Variance of the empirical count:** `E[(count − N·p k)²] = N · p k · (1 − p k)`
    (binomial variance — diagonal terms `N·p` minus the `N²p²` from the mean,
    plus the off-diagonal `N(N−1)p²`). -/
theorem variance_count (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) (k : Fin m) :
    ∑ ω : Fin N → Fin m, w p ω * (count k ω - (N : ℝ) * p k) ^ 2
      = (N : ℝ) * p k * (1 - p k) := by
  -- evaluate the double sum of `marginal2`
  have hds : (∑ s : Fin N, ∑ s' : Fin N, (if s = s' then p k else p k * p k))
      = (N : ℝ) * ((N : ℝ) * (p k * p k) + (p k - p k * p k)) := by
    have hinner : ∀ s : Fin N, (∑ s' : Fin N, (if s = s' then p k else p k * p k))
        = (N : ℝ) * (p k * p k) + (p k - p k * p k) := by
      intro s
      have hrw : ∀ s' : Fin N, (if s = s' then p k else p k * p k)
          = p k * p k + (if s = s' then (p k - p k * p k) else 0) := by
        intro s'; by_cases h : s = s' <;> simp [h]
      simp_rw [hrw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.sum_ite_eq univ s (fun _ => p k - p k * p k), if_pos (mem_univ s)]
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- expand the squared deviation and substitute the three moments
  have hpt : ∀ ω : Fin N → Fin m, w p ω * (count k ω - (N : ℝ) * p k) ^ 2
      = w p ω * (count k ω) ^ 2 - 2 * ((N : ℝ) * p k) * (w p ω * count k ω)
          + ((N : ℝ) * p k) ^ 2 * w p ω := fun ω => by ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    expectation_count p hp1 k, sum_w_eq_one p hp1, expectation_count_sq p hp1 k, hds]
  ring

/-- **Clean Chebyshev typicality bound:** the weight of `|freq − p k| ≥ ε` is at most
    `p k (1 − p k) / (N ε²)`.  This is the finite, quantitative form of "empirical
    frequencies are typically the Born weights" — replacing the vacuous
    `LLN_typicality_axiom` placeholder. -/
theorem chebyshev_freq (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (k : Fin m) {ε : ℝ} (hε : 0 < ε) (hN : 0 < N) :
    (∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter
          (fun ω => ((N : ℝ) * ε) ^ 2 ≤ (count k ω - (N : ℝ) * p k) ^ 2), w p ω)
      ≤ p k * (1 - p k) / ((N : ℝ) * ε ^ 2) := by
  refine (chebyshev_count p hp k hε hN).trans (le_of_eq ?_)
  rw [variance_count p hp1 k]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [mul_pow]; field_simp

/-- **Union bound over outcomes.**  The weight of the event "SOME outcome's empirical
    frequency is `ε`-far from its Born weight `p k`" is at most the sum of the
    per-outcome Chebyshev bounds, `(∑ₖ p k(1−p k)) / (N ε²)`.  (Standard union bound:
    the bad set is `⋃ₖ Bₖ`, and `w(⋃ Bₖ) ≤ ∑ w(Bₖ)` since the weights are nonnegative.) -/
theorem chebyshev_freq_union (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    {ε : ℝ} (hε : 0 < ε) (hN : 0 < N) :
    (∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter
        (fun ω => ∃ k, ((N : ℝ) * ε) ^ 2 ≤ (count k ω - (N : ℝ) * p k) ^ 2), w p ω)
      ≤ (∑ k, p k * (1 - p k)) / ((N : ℝ) * ε ^ 2) := by
  classical
  set P : Fin m → (Fin N → Fin m) → Prop :=
    fun k ω => ((N : ℝ) * ε) ^ 2 ≤ (count k ω - (N : ℝ) * p k) ^ 2 with hP
  have hunion :
      (∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter (fun ω => ∃ k, P k ω), w p ω)
        ≤ ∑ k : Fin m, ∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter (fun ω => P k ω), w p ω := by
    have hcomm :
        (∑ k : Fin m, ∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter (fun ω => P k ω), w p ω)
          = ∑ ω : Fin N → Fin m, ∑ k : Fin m, (if P k ω then w p ω else 0) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    rw [hcomm]
    calc (∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter (fun ω => ∃ k, P k ω), w p ω)
        ≤ ∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter (fun ω => ∃ k, P k ω),
            ∑ k : Fin m, (if P k ω then w p ω else 0) := by
          refine Finset.sum_le_sum (fun ω hω => ?_)
          rw [Finset.mem_filter] at hω
          obtain ⟨k0, hk0⟩ := hω.2
          conv_lhs => rw [show w p ω = (if P k0 ω then w p ω else 0) from (if_pos hk0).symm]
          exact Finset.single_le_sum (f := fun k => if P k ω then w p ω else 0)
            (fun k _ => by by_cases h : P k ω <;> simp [h, w_nonneg p hp ω]) (mem_univ k0)
      _ ≤ ∑ ω : Fin N → Fin m, ∑ k : Fin m, (if P k ω then w p ω else 0) :=
          Finset.sum_le_univ_sum_of_nonneg
            (fun ω => Finset.sum_nonneg
              (fun k _ => by by_cases h : P k ω <;> simp [h, w_nonneg p hp ω]))
  refine hunion.trans ?_
  rw [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [← div_eq_mul_inv]
  exact chebyshev_freq p hp hp1 k hε hN

/-- **Global union typicality bound.**  Since `∑ₖ p k(1−p k) = 1 − ∑ₖ p k² ≤ 1`, the
    probability that ANY outcome's frequency deviates by `ε` is `≤ 1/(N ε²) → 0`.
    Joint typicality: with high weight, ALL empirical frequencies match the Born
    weights simultaneously. -/
theorem chebyshev_freq_union_le (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    {ε : ℝ} (hε : 0 < ε) (hN : 0 < N) :
    (∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter
        (fun ω => ∃ k, ((N : ℝ) * ε) ^ 2 ≤ (count k ω - (N : ℝ) * p k) ^ 2), w p ω)
      ≤ 1 / ((N : ℝ) * ε ^ 2) := by
  refine (chebyshev_freq_union p hp hp1 hε hN).trans ?_
  have hsum : (∑ k, p k * (1 - p k)) ≤ 1 := by
    have heq : (∑ k, p k * (1 - p k)) = 1 - ∑ k, p k ^ 2 := by
      simp_rw [mul_one_sub, sq]; rw [Finset.sum_sub_distrib, hp1]
    rw [heq]
    exact sub_le_self 1 (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hden : 0 < (N : ℝ) * ε ^ 2 := mul_pos (by exact_mod_cast hN) (pow_pos hε 2)
  exact (div_le_div_iff_of_pos_right hden).mpr hsum

/-- **Product preparation ⇒ trial independence.**  For the product weight `w q` (the law of
    `N` i.i.d. trials), the weight of a full history `h` equals the product of the single-trial
    marginals: `w q {h} = ∏ₜ (weight of "trial t reads hₜ")`.  This is the trial-independence
    property `BornJoin.indep`, DERIVED purely from the product structure of `w q` — it is
    exactly the statement that the world-measure is a PRODUCT (independent preparation of `N`
    copies).  Independence cannot be derived from less: a product measure is genuinely required
    (no-signaling alone permits correlations), so product preparation is the irreducible,
    motivated physical input behind `indep`. -/
theorem w_history_factorizes (q : Fin m → ℝ) (hq1 : ∑ i, q i = 1) (h : Fin N → Fin m) :
    (∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter (fun ω => ω = h), w q ω)
      = ∏ t : Fin N, (∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter (fun ω => ω t = h t), w q ω) := by
  rw [Finset.filter_eq', if_pos (mem_univ h), Finset.sum_singleton]
  have hmarg : ∀ t : Fin N,
      (∑ ω ∈ (univ : Finset (Fin N → Fin m)).filter (fun ω => ω t = h t), w q ω) = q (h t) := by
    intro t
    rw [Finset.sum_filter, ← marginal q hq1 (h t) t]
    exact Finset.sum_congr rfl (fun ω _ => by by_cases hc : ω t = h t <;> simp [hc, w])
  rw [Finset.prod_congr rfl (fun t _ => hmarg t)]
  rfl

/-- **Permutation-equivariance of the product Born measure.**  Relabeling the trials/modes by
    any permutation `σ` leaves the product weight invariant: `w p (ω ∘ σ) = w p ω`.  This is the
    finite, exchange-symmetric content behind "the Born typicality measure is covariant under
    relabeling the records" — the `(Φ,λ)`-program's mode-permutation ("finite Lorentz") symmetry
    of the i.i.d. product measure.  (Reindexing a product by a bijection.) -/
theorem w_perm_invariant (p : Fin m → ℝ) (σ : Equiv.Perm (Fin N)) (ω : Fin N → Fin m) :
    w p (ω ∘ σ) = w p ω :=
  Equiv.prod_comp σ (fun t => p (ω t))

end BornTypicalityFinite
end QIQTH
