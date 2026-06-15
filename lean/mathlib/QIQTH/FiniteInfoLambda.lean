/-
  FiniteInfoLambda — a finite-information actuality selector λ, worked out.

  The honest finding (this session) was that λ does NOT require finite information:
  the inverse-CDF selector of `SelectionEvent` uses a continuum seed `s∈[0,1)` (an
  infinite-information real) and works on infinite-dimensional spaces.  This module
  works out the alternative the program is *named* for: **force λ to be finite**.

  MODEL.  Bound the selector's resolving power to a finite number `N` of equal
  actuality cells — `N ≤ e^{Q_R}`, i.e. `log₂ N` bits, capped by the regional
  holographic capacity (the principled "forcing": λ is physically instantiated in
  a region that holds `≤ Q_R` information, so it cannot resolve more finely).  The
  finite-information seed is then `j ∈ {0,…,N-1}` (seed value `j/N`), and record α
  is selected iff its Born cell `[loₐ, loₐ+pₐ)` contains `j/N` — i.e. the count is

      gridCount(α) = #{ j<N : loₐ ≤ j/N < loₐ+pₐ } = ⌈N·lo_{α+1}⌉ − ⌈N·loₐ⌉,

  and the realized (finite-information) weight is `gridWeight(α) = gridCount(α)/N`.

  WHAT IS DERIVED (machine-checked, axiom-free):
    * `gridCount_sum` / `gridWeight_sum` — every actuality seed selects exactly one
      record: `Σ gridCount = N`, so `Σ gridWeight = 1` (a genuine probability over a
      FINITE, uniform seed measure — no infinite-information seed).
    * `gridWeight_near_born` — **Born up to the resolution**: `|gridWeight − pₐ| < 1/N`.
      Finite λ reproduces Born to precision `1/N ≈ e^{−Q_R}`; the deviation is a
      calculable, capacity-controlled signature (testable for a small effective N).
    * `gridWeight_tendsto_born` — exact Born is the `N→∞` (infinite-capacity) limit.
    * `resolution_floor` — a **minimum actualizable weight**: a record with `pₐ` below
      the resolution gets ZERO cells (never actualized), unlike Everett where every
      branch is real.  This is the genuine ontological/empirical difference: finite λ
      has a smallest grain of actuality.

  Postulated (NOT derived): (FQ) the region holds ≤ Q_R info; λ instantiated within
  the region, so `N ≤ e^{Q_R}`; the uniform measure on the N seeds (typicality).
-/

import QIQTH.SelectionEvent
import Mathlib.Tactic

namespace QIQTH.FiniteInfoLambda

open QIQTH.SelectionEvent

/-- `⌈N · (cumulative Born weight below record k)⌉` — the cumulative actuality-cell
    boundary at record `k`. -/
noncomputable def cumCeil (p : ℕ → ℝ) (N : ℕ) (k : ℕ) : ℤ := ⌈(N : ℝ) * lo p k⌉

/-- The number of finite-information actuality seeds (`N` cells) that select record
    `α` — the count of grid points `j/N` in record `α`'s Born interval. -/
noncomputable def gridCount (p : ℕ → ℝ) (N : ℕ) (α : ℕ) : ℤ := cumCeil p N (α + 1) - cumCeil p N α

/-- The realized **finite-information weight** of record `α`: `gridCount(α)/N`. -/
noncomputable def gridWeight (p : ℕ → ℝ) (N : ℕ) (α : ℕ) : ℝ :=
  (gridCount p N α : ℝ) / N

/- ── 1. Every seed selects exactly one record (a genuine finite probability) ─-/

/-- **`Σ gridCount = N`** — the actuality cells partition the `N` seeds: every seed
    selects exactly one record (telescoping the cumulative ceilings). -/
theorem gridCount_sum (p : ℕ → ℝ) (N : ℕ) {n : ℕ}
    (hsum : ∑ i ∈ Finset.range n, p i = 1) :
    ∑ α ∈ Finset.range n, gridCount p N α = (N : ℤ) := by
  have htel : ∑ α ∈ Finset.range n, gridCount p N α = cumCeil p N n - cumCeil p N 0 := by
    simp only [gridCount]
    exact Finset.sum_range_sub (cumCeil p N) n
  rw [htel]
  have hn : cumCeil p N n = (N : ℤ) := by
    unfold cumCeil
    have hl : lo p n = 1 := hsum
    rw [hl, mul_one, Int.ceil_natCast]
  have h0 : cumCeil p N 0 = 0 := by
    unfold cumCeil
    have hl : lo p 0 = 0 := by simp [lo]
    rw [hl, mul_zero, Int.ceil_zero]
  rw [hn, h0, sub_zero]

/-- **The finite-information weights are a probability**: `Σ gridWeight = 1`. -/
theorem gridWeight_sum (p : ℕ → ℝ) (N : ℕ) (hN : 0 < N) {n : ℕ}
    (hsum : ∑ i ∈ Finset.range n, p i = 1) :
    ∑ α ∈ Finset.range n, gridWeight p N α = 1 := by
  have hne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold gridWeight
  rw [← Finset.sum_div, ← Int.cast_sum, gridCount_sum p N hsum, Int.cast_natCast,
      div_self hne]

/- ── 2. Born up to the resolution `1/N` ────────────────────────────────────-/

/-- The integer cell-count is within `1` of `N·pₐ`. -/
theorem gridCount_near_born (p : ℕ → ℝ) (N α : ℕ) :
    |(gridCount p N α : ℝ) - (N : ℝ) * p α| < 1 := by
  have hlo : (N : ℝ) * lo p (α + 1) - (N : ℝ) * lo p α = (N : ℝ) * p α := by
    rw [lo_succ]; ring
  unfold gridCount cumCeil
  push_cast
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · have h1 := Int.le_ceil ((N : ℝ) * lo p (α + 1))
    have h2 := Int.ceil_lt_add_one ((N : ℝ) * lo p α)
    linarith
  · have h1 := Int.ceil_lt_add_one ((N : ℝ) * lo p (α + 1))
    have h2 := Int.le_ceil ((N : ℝ) * lo p α)
    linarith

/-- **Born up to the resolution**: the realized finite-information weight is within
    `1/N` of the Born weight.  Finite λ reproduces Born to precision `1/N`. -/
theorem gridWeight_near_born (p : ℕ → ℝ) (N α : ℕ) (hN : 0 < N) :
    |gridWeight p N α - p α| < 1 / N := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hne : (N : ℝ) ≠ 0 := hNR.ne'
  have hb := gridCount_near_born p N α
  have key : gridWeight p N α - p α = ((gridCount p N α : ℝ) - (N : ℝ) * p α) / N := by
    unfold gridWeight
    field_simp
  rw [key, abs_div, abs_of_pos hNR]
  have hpos : (0 : ℝ) < 1 - |(gridCount p N α : ℝ) - (N : ℝ) * p α| := by linarith
  have hsplit : (1 : ℝ) / N - |(gridCount p N α : ℝ) - (N : ℝ) * p α| / N
      = (1 - |(gridCount p N α : ℝ) - (N : ℝ) * p α|) / N := by ring
  have hd : (0 : ℝ) < (1 - |(gridCount p N α : ℝ) - (N : ℝ) * p α|) / N := div_pos hpos hNR
  linarith [hsplit, hd]

/-- **Exact Born is the infinite-capacity limit**: as the resolution `N → ∞`, the
    finite-information weight tends to the Born weight. -/
theorem gridWeight_tendsto_born (p : ℕ → ℝ) (α : ℕ) :
    Filter.Tendsto (fun N => gridWeight p N α) Filter.atTop (nhds (p α)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  refine ⟨M + 1, fun N hN => ?_⟩
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN0
  have hb : |gridWeight p N α - p α| < 1 / N := gridWeight_near_born p N α hN0
  have hMR : (M : ℝ) < N := by exact_mod_cast (by omega : M < N)
  have h1N : (1 : ℝ) / N < ε := by
    have hlt : (1 : ℝ) / ε < N := lt_trans hM hMR
    have hεN : (1 : ℝ) < N * ε := by
      have h := mul_lt_mul_of_pos_right hlt hε
      rwa [one_div_mul_cancel hε.ne'] at h
    have hsplit : ε - 1 / N = (N * ε - 1) / N := by field_simp
    have hd : (0 : ℝ) < (N * ε - 1) / N := div_pos (by linarith) hNR
    linarith [hsplit, hd]
  rw [Real.dist_eq]
  linarith [hb, h1N]

/- ── 3. The resolution floor: a minimum actualizable weight ─────────────────-/

/-- **A minimum actualizable weight.**  There is a Born distribution and a finite
    resolution `N` at which a positive-weight record gets ZERO actuality cells — it
    is *below the resolution* and is never actualized.  (Here `p = (3/4, 1/4)` at
    `N = 2`: the weight-`1/4` record falls below the one-bit resolution `1/2`.)  This
    is the structural difference from Everett, where every branch is real. -/
theorem resolution_floor :
    ∃ (p : ℕ → ℝ) (N α : ℕ),
      (∑ i ∈ Finset.range 2, p i = 1) ∧ 0 < p α ∧ gridCount p N α = 0 := by
  refine ⟨fun j => if j = 0 then 3 / 4 else if j = 1 then 1 / 4 else 0, 2, 1, ?_, ?_, ?_⟩
  · simp [Finset.sum_range_succ]; norm_num
  · norm_num
  · have e2 : lo (fun j => if j = 0 then (3 : ℝ) / 4 else if j = 1 then 1 / 4 else 0) 2 = 1 := by
      simp [lo, Finset.sum_range_succ]; norm_num
    have e1 : lo (fun j => if j = 0 then (3 : ℝ) / 4 else if j = 1 then 1 / 4 else 0) 1 = 3 / 4 := by
      simp [lo, Finset.sum_range_one]
    simp only [gridCount, cumCeil, e2, e1, mul_one]
    rw [Int.ceil_natCast, show ((2 : ℕ) : ℝ) * (3 / 4) = 3 / 2 by norm_num,
        show (⌈(3 / 2 : ℝ)⌉ : ℤ) = 2 by rw [Int.ceil_eq_iff] <;> norm_num]
    norm_num

/-- **Audit conclusion.**  A finite-information actuality selector, worked out and
    machine-checked (axiom-free).  DERIVED: every seed selects exactly one record
    (`gridCount_sum`); the weights are a genuine probability over a FINITE seed
    measure (`gridWeight_sum`); Born holds up to the resolution `1/N`
    (`gridWeight_near_born`), exact in the `N→∞` limit (`gridWeight_tendsto_born`);
    and there is a minimum actualizable weight (`resolution_floor`) — a smallest
    grain of actuality that Everett lacks.  POSTULATED: (FQ), λ's instantiation
    within the region (so `N ≤ e^{Q_R}`), and the uniform seed measure. -/
theorem audit_conclusion : True := trivial

end QIQTH.FiniteInfoLambda
