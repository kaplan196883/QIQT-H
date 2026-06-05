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
  frequencies.  (The Chebyshev concentration bound — `P(|freq − p| ≥ ε) ≤
  p(1−p)/(Nε²)` — is the next step; it needs the second moment.)
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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

end BornTypicalityFinite
end QIQTH
