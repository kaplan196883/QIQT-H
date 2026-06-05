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
  frequencies.  We also prove the CONCENTRATION direction:

    • `markov_le`        finite Markov inequality for the product measure;
    • `chebyshev_count`  Chebyshev: the weight of the deviation event
                         `(count − N·p k)² ≥ (N·ε)²` (i.e. `|freq − p k| ≥ ε`)
                         is `≤ E[(count − N·p k)²] / (N·ε)²`.

  With `expectation_count` (`E[count] = N·p k`), the second-moment numerator is
  the variance; computing it to `N·p k·(1 − p k)` (needs the two-coordinate
  marginal) yields the standard `p(1−p)/(Nε²)` typicality bound — the last
  remaining step.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Complex.Basic

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

/-- **Empirical counts are unbiased estimators of the Born weight:**
    `E[#{t : ω t = k}] = N · p k`.  (Linearity of expectation over the `N`
    i.i.d. trials, each `marginal` giving `p k`.) -/
theorem expectation_count (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) (k : Fin m) :
    ∑ ω : Fin N → Fin m, w p ω * count k ω = (N : ℝ) * p k := by
  simp only [w, count, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [marginal p hp1 k]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

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

end BornTypicalityFinite
end QIQTH
