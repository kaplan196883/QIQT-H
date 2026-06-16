/-
  FiniteIndexLambda — the finite-information λ that SURVIVES: a finite INDEX over a
  finite record-history space, with the EXACT Born law.  The machine-checked
  DIVIDING LINE between finiteness that is Born-transparent and finiteness that is
  fatal.

  Background.  Putting finiteness in λ's PROBABILITY LAW (the retracted
  `FiniteInfoLambda` grid — a uniform-N-cell inverse-CDF that ROUNDS the weights)
  fails: it is ordering-dependent and breaks the program's own envariance and
  operational no-signaling.  Putting finiteness in the ACTUALITY DOMAIN survives:

    λ is a finite INDEX `α ∈ {0,…,M−1}` into a finite set of distinguishable
    record-histories, and its law is the EXACT Born weight `Pr(λ=α) = pₐ` — a real,
    computed from Φ, NOT rounded.  The "finite encoding" of λ is then just the finite
    CARDINALITY of the index space (`M ≤ 2^B`, i.e. `log₂ M` bits — bounded by the
    horizon entropy via the mutual-information identity `H(λ)=I(λ;R) ≤ H(R) ≤ S`,
    with no new beable, since λ adds no distinctions beyond the records it indexes).

  This module machine-checks the DIVIDING LINE.  The finite-index law (= the exact
  Born `p`) preserves marginals and equal weights BY DEFINITION (`indexWeight`); the
  GRID provably breaks both:

    * `grid_breaks_envariance` — equal-weight records get UNEQUAL grid weights:
      `p = (1/3,1/3,1/3)`, `N=2` gives grid `(1/2,1/2,0)`.  (Contradicts the
      machine-checked Zurek envariance the Born reduction rests on.)
    * `grid_breaks_no_signaling` — rounding a JOINT distribution makes a remote
      marginal depend on the correlation: two joint Born distributions with the SAME
      Born marginal for one party get DIFFERENT grid marginals (an order-`1/N` signal).

  So finiteness in the law is fatal; finiteness in the index is Born-transparent,
  hence envariance/no-signaling-safe, and reduces to the EXACT Born measure — with
  Born holding as finite-SAMPLE typicality (`BornConcentration.born_chebyshev_*`).
  Honest limit: being Born-transparent, it is operationally equivalent to Everett;
  the distinction is ontological (one actual finite history vs. all finite branches).

  Axiom-free.
-/

import QIQTH.FiniteInfoLambda
import QIQTH.BornConcentration

namespace QIQTH.FiniteIndexLambda

open QIQTH.FiniteInfoLambda QIQTH.SelectionEvent

/- ── 1. The finite-index law IS the exact Born law (Born-transparent) ───────-/

/-- The finite-index selector's law: `λ=α` with the EXACT Born weight `pₐ`
    (no rounding). -/
def indexWeight (p : ℕ → ℝ) (α : ℕ) : ℝ := p α

/-- **No-signaling-transparent.**  The finite-index law preserves marginals
    exactly: the marginal over any record set is the exact Born marginal (because
    the law IS `p`). -/
theorem indexWeight_marginal (p : ℕ → ℝ) (S : Finset ℕ) :
    ∑ i ∈ S, indexWeight p i = ∑ i ∈ S, p i := rfl

/-- **Envariance-transparent.**  Equal-weight records get equal index weights
    (because the law IS `p`). -/
theorem indexWeight_envariant (p : ℕ → ℝ) {α β : ℕ} (h : p α = p β) :
    indexWeight p α = indexWeight p β := h

/- ── 2. A helper for computing the grid weight from the two cell boundaries ─-/

/-- `gridWeight p N α = (⌈N·lo_{α+1}⌉ − ⌈N·loₐ⌉)/N`, computed from the two
    cumulative boundary values and their ceilings. -/
theorem gridWeight_two (p : ℕ → ℝ) (N α : ℕ) (a b : ℝ) (ca cb : ℤ)
    (hb : lo p α = b) (ha : lo p (α + 1) = a)
    (hcb : ⌈(N : ℝ) * b⌉ = cb) (hca : ⌈(N : ℝ) * a⌉ = ca) :
    gridWeight p N α = ((ca - cb : ℤ) : ℝ) / N := by
  unfold gridWeight gridCount cumCeil
  rw [ha, hb, hca, hcb]

/- ── 3. The grid breaks ENVARIANCE (machine-checked counterexample) ─────────-/

/-- **The grid breaks envariance.**  For the uniform Born distribution
    `(1/3, 1/3, 1/3)` at resolution `N = 2`, records `0` and `2` have EQUAL Born
    weight but UNEQUAL grid weights (`1/2` vs `0`).  This contradicts the
    machine-checked Zurek envariance (equal amplitudes ⇒ equiprobable) that the
    Born reduction rests on — so finiteness in the probability LAW is fatal. -/
theorem grid_breaks_envariance :
    ∃ (p : ℕ → ℝ),
      (∑ i ∈ Finset.range 3, p i = 1) ∧ p 0 = p 2 ∧
      gridWeight p 2 0 ≠ gridWeight p 2 2 := by
  refine ⟨fun j => if j = 0 then 1 / 3 else if j = 1 then 1 / 3 else if j = 2 then 1 / 3 else 0,
          ?_, ?_, ?_⟩
  · norm_num [Finset.sum_range_succ]
  · norm_num
  · have g0 := gridWeight_two (fun j => if j = 0 then (1:ℝ)/3 else if j = 1 then 1/3 else if j = 2 then 1/3 else 0)
      2 0 (1/3) 0 1 0
      (by norm_num [lo]) (by norm_num [lo, Finset.sum_range_one])
      (by rw [mul_zero, Int.ceil_zero])
      (by rw [show ((2:ℕ):ℝ)*(1/3) = 2/3 by norm_num, Int.ceil_eq_iff] <;> norm_num)
    have g2 := gridWeight_two (fun j => if j = 0 then (1:ℝ)/3 else if j = 1 then 1/3 else if j = 2 then 1/3 else 0)
      2 2 1 (2/3) 2 2
      (by norm_num [lo, Finset.sum_range_succ]) (by norm_num [lo, Finset.sum_range_succ])
      (by rw [show ((2:ℕ):ℝ)*(2/3) = 4/3 by norm_num, Int.ceil_eq_iff] <;> norm_num)
      (by rw [show ((2:ℕ):ℝ)*(1:ℝ) = 2 by norm_num, Int.ceil_eq_iff] <;> norm_num)
    rw [g0, g2]; norm_num

/- ── 4. The grid breaks NO-SIGNALING (machine-checked counterexample) ───────-/

/-- **The grid breaks no-signaling.**  Records `(00,01,10,11)` with one party's
    bit `= 0` on `{00,10}` (indices `0,2`).  Two joint Born distributions —
    correlated `(1/2,0,0,1/2)` and anticorrelated `(0,1/2,1/2,0)` — have the SAME
    Born marginal `1/2` for that party, yet the grid (`N=3`) gives DIFFERENT
    marginals `2/3` vs `1/3`: an order-`1/N` SIGNAL.  Operational no-signaling is a
    machine-checked QIQT-H result, so finiteness in the probability LAW is fatal. -/
theorem grid_breaks_no_signaling :
    ∃ (p q : ℕ → ℝ),
      (∑ i ∈ Finset.range 4, p i = 1) ∧ (∑ i ∈ Finset.range 4, q i = 1) ∧
      p 0 + p 2 = q 0 + q 2 ∧
      gridWeight p 3 0 + gridWeight p 3 2 ≠ gridWeight q 3 0 + gridWeight q 3 2 := by
  refine ⟨fun j => if j = 0 then 1 / 2 else if j = 3 then 1 / 2 else 0,
          fun j => if j = 1 then 1 / 2 else if j = 2 then 1 / 2 else 0,
          ?_, ?_, ?_, ?_⟩
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]
  · norm_num
  · have gp0 := gridWeight_two (fun j => if j = 0 then (1:ℝ)/2 else if j = 3 then 1/2 else 0)
      3 0 (1/2) 0 2 0
      (by norm_num [lo]) (by norm_num [lo, Finset.sum_range_one])
      (by rw [mul_zero, Int.ceil_zero])
      (by rw [show ((3:ℕ):ℝ)*(1/2) = 3/2 by norm_num, Int.ceil_eq_iff] <;> norm_num)
    have gp2 := gridWeight_two (fun j => if j = 0 then (1:ℝ)/2 else if j = 3 then 1/2 else 0)
      3 2 (1/2) (1/2) 2 2
      (by norm_num [lo, Finset.sum_range_succ]) (by norm_num [lo, Finset.sum_range_succ])
      (by rw [show ((3:ℕ):ℝ)*(1/2) = 3/2 by norm_num, Int.ceil_eq_iff] <;> norm_num)
      (by rw [show ((3:ℕ):ℝ)*(1/2) = 3/2 by norm_num, Int.ceil_eq_iff] <;> norm_num)
    have gq0 := gridWeight_two (fun j => if j = 1 then (1:ℝ)/2 else if j = 2 then 1/2 else 0)
      3 0 0 0 0 0
      (by norm_num [lo]) (by norm_num [lo, Finset.sum_range_one])
      (by rw [mul_zero, Int.ceil_zero]) (by rw [mul_zero, Int.ceil_zero])
    have gq2 := gridWeight_two (fun j => if j = 1 then (1:ℝ)/2 else if j = 2 then 1/2 else 0)
      3 2 1 (1/2) 3 2
      (by norm_num [lo, Finset.sum_range_succ]) (by norm_num [lo, Finset.sum_range_succ])
      (by rw [show ((3:ℕ):ℝ)*(1/2) = 3/2 by norm_num, Int.ceil_eq_iff] <;> norm_num)
      (by rw [show ((3:ℕ):ℝ)*(1:ℝ) = 3 by norm_num, Int.ceil_eq_iff] <;> norm_num)
    rw [gp0, gp2, gq0, gq2]; norm_num

/-- **Audit conclusion.**  The machine-checked dividing line for finite-information
    λ.  The finite-INDEX law is the exact Born `p` (`indexWeight`): it preserves
    marginals (`indexWeight_marginal`, no-signaling-transparent) and equal weights
    (`indexWeight_envariant`, envariance-transparent), and is bounded only by the
    finite CARDINALITY of the record-history space (the holographic budget).  The
    GRID law (finiteness in the probability values) provably BREAKS envariance
    (`grid_breaks_envariance`) and no-signaling (`grid_breaks_no_signaling`).  So
    finite information must live in the actuality DOMAIN (a finite index), never in
    the law; Born then holds as finite-SAMPLE typicality
    (`QIQTH.BornConcentration.born_chebyshev_single_trial`).  Born-transparent ⇒
    operationally equivalent to Everett; the distinction is ontological.  NO axioms. -/
theorem audit_conclusion : True := trivial

end QIQTH.FiniteIndexLambda
