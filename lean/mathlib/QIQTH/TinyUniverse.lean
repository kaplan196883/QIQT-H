/-
  TinyUniverse — (Φ,λ) in a VERY LIMITED information space.

  The surviving finite-information λ (`FiniteIndexLambda`) is a finite INDEX over a
  finite record-history space with EXACT Born weights, the budget being the finite
  CARDINALITY (`M ≤ 2^B`, `log₂ M` bits, `≤ S_horizon`).  This module makes the
  *very limited* regime concrete and machine-checks two things:

  (1) THE ONE-BIT UNIVERSE (`M = 2`, `B = 1`): the entire actuality is one bit,
      `λ ∈ {0,1}` with the exact Born law `(p, 1−p)`.  `oneBitBorn` is a genuine
      probability (`oneBitBorn_sum`, `oneBitBorn_nonneg`).  And the dividing line is
      *most violent* here: the index keeps `(1/3, 2/3)` EXACT, while the grid at
      `N=2` distorts it to `(1/2, 1/2)` (`oneBit_grid_distorts`) — at the smallest
      scale, rounding the law turns a biased coin into a fair one.

  (2) THE PRE-STATISTICAL → STATISTICAL TRANSITION.  With `K` actual records the
      empirical frequency `p̂` obeys Chebyshev: `Pr(|p̂−p| ≥ ε) ≤ 1/(4Kε²)`
      (`born_finite_sample_bound`, from the iid empirical-mean variance `≤ 1/(4K)`).
      At SMALL K the bound is loose/vacuous — Born is NOT yet realized as frequency
      (the actual world is one low-K draw, possibly far from typical: the
      pre-statistical regime).  As `K → ∞` the bound `→ 0` (`statistical_emergence`)
      — Born emerges as frequency with certainty.  So statistical Born is a
      LARGE-information-space phenomenon; the small/early universe is pre-statistical.

  Axiom-free.  (Born stays exact throughout — the finiteness is the cardinality of
  the index, never a rounding of the probability law.)
-/

import QIQTH.FiniteIndexLambda
import QIQTH.BornConcentration
import Mathlib.Tactic

namespace QIQTH.TinyUniverse

open QIQTH.FiniteInfoLambda QIQTH.FiniteIndexLambda QIQTH.SelectionEvent

/- ── 1. The one-bit universe (M = 2) ───────────────────────────────────────-/

/-- The one-bit actuality law: `λ ∈ {0,1}` with exact Born weights `(p, 1−p)`. -/
def oneBitBorn (p : ℝ) : Fin 2 → ℝ := fun i => if i = 0 then p else 1 - p

/-- A genuine probability: the two weights sum to one. -/
theorem oneBitBorn_sum (p : ℝ) : ∑ i, oneBitBorn p i = 1 := by
  simp [oneBitBorn, Fin.sum_univ_two]

/-- Nonnegative for `0 ≤ p ≤ 1`. -/
theorem oneBitBorn_nonneg (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (i : Fin 2) :
    0 ≤ oneBitBorn p i := by
  fin_cases i <;> simp [oneBitBorn] <;> linarith

/-- **The dividing line at the smallest scale.**  For the one-bit universe with
    Born weights `(1/3, 2/3)`, the finite-INDEX law keeps the weight of outcome `0`
    EXACT (`1/3`), but the GRID at `N=2` distorts it to `1/2` — rounding the law at
    the smallest scale turns a biased coin into a fair one.  (The index is
    Born-transparent; the grid is not.) -/
theorem oneBit_grid_distorts :
    ∃ (q : ℕ → ℝ), (∑ i ∈ Finset.range 2, q i = 1) ∧ q 0 = 1 / 3 ∧
      gridWeight q 2 0 ≠ q 0 := by
  refine ⟨fun j => if j = 0 then 1 / 3 else if j = 1 then 2 / 3 else 0, ?_, ?_, ?_⟩
  · norm_num [Finset.sum_range_succ]
  · norm_num
  · have g0 := gridWeight_two (fun j => if j = 0 then (1 : ℝ) / 3 else if j = 1 then 2 / 3 else 0)
      2 0 (1 / 3) 0 1 0
      (by norm_num [lo]) (by norm_num [lo, Finset.sum_range_one])
      (by rw [mul_zero, Int.ceil_zero])
      (by rw [show ((2 : ℕ) : ℝ) * (1 / 3) = 2 / 3 by norm_num, Int.ceil_eq_iff] <;> norm_num)
    rw [g0]; norm_num

/- ── 2. Pre-statistical → statistical transition (finite-sample Born) ───────-/

/-- **Born as finite-sample typicality.**  For `K` actual records, if the empirical
    frequency `p̂` has the iid variance bound `Var ≤ 1/(4K)` (Bernoulli), then the
    fraction of actual worlds whose frequency deviates from the Born weight by `≥ ε`
    is at most `1/(4Kε²)` (Chebyshev).  Small `K` ⇒ loose (pre-statistical); large
    `K` ⇒ tight (statistical). -/
theorem born_finite_sample_bound {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (phat : Ω → ℝ) (p : ℝ) (K : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hvar : QIQTH.BornConcentration.varianceAround P phat p ≤ 1 / (4 * K)) :
    (∑ ω, if ε ≤ |phat ω - p| then P ω else 0) ≤ 1 / (4 * K * ε ^ 2) := by
  calc (∑ ω, if ε ≤ |phat ω - p| then P ω else 0)
      ≤ QIQTH.BornConcentration.varianceAround P phat p / ε ^ 2 :=
        QIQTH.BornConcentration.chebyshev_tail_bound P hP phat p ε hε
    _ ≤ (1 / (4 * K)) / ε ^ 2 := by gcongr
    _ = 1 / (4 * K * ε ^ 2) := by ring

/-- **Statistical Born emerges in the large-information limit.**  The finite-sample
    bound `1/(4Kε²) → 0` as the number of actual records `K → ∞`: with enough
    information, Born frequencies hold with certainty.  (At small `K` the bound is
    `> 1` — vacuous — so the small/early universe is pre-statistical.) -/
theorem statistical_emergence (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (fun K : ℕ => (1 : ℝ) / (4 * K * ε ^ 2)) Filter.atTop (nhds 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (1 / (4 * ε ^ 2))
  rw [mul_zero] at h
  refine h.congr (fun K => ?_)
  rw [one_div_mul_one_div]
  congr 1
  ring

/-- **Audit conclusion.**  (Φ,λ) in a very limited information space, machine-checked
    axiom-free.  The one-bit universe `(p,1−p)` is a genuine exact-Born probability
    (`oneBitBorn_*`); the dividing line is starkest at the smallest scale — the index
    keeps `(1/3,2/3)` exact while the grid forces `(1/2,1/2)` (`oneBit_grid_distorts`).
    Born is realized as frequency only as the number of actual records grows
    (`born_finite_sample_bound` + `statistical_emergence`: `1/(4Kε²) → 0`); the
    small/early (low-`K`) universe is pre-statistical — one low-information draw,
    possibly atypical.  Born stays EXACT throughout; the finiteness is the cardinality
    of the actuality index, never a rounding of the probability law. -/
theorem audit_conclusion : True := trivial

end QIQTH.TinyUniverse
