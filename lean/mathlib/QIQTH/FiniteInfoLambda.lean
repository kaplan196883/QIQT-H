/-
  FiniteInfoLambda — a particular finite inverse-CDF sampler.  (Correct arithmetic;
  its physical INTERPRETATION as "finite-information λ" did NOT survive red-team.)

  STATUS / CAVEAT (2026-06-16, after a GPT-5.5-pro red-team, verified by direct
  computation).  The theorems below are correct, but they certify ONE arbitrary
  finite sampler — a deterministic uniform-`N`-cell inverse-CDF grid in a fixed
  record ORDERING — NOT a physical consequence of "finite information".  The
  conceptual payoffs first claimed for this module are RETRACTED:

    • "Finite information ⇒ this grid" is FALSE.  A finite-VALUED selector
      `λ ∈ {1,…,M}` with the exact Born law `μ(α)=pₐ` carries only `log M ≤ Q_R`
      realized bits and reproduces Born EXACTLY (no deviation, no floor).  The
      deviation is an artifact of the extra "uniform-seed + deterministic-CDF"
      assumption, not of finiteness.  (Dithering the grid restores exact Born in
      expectation.)
    • The "minimum actualizable weight / grain of actuality" is NOT a physical
      threshold — it is ORDERING-dependent.  Same Born `(3/4,1/4)`, `N=2`: ordering
      `(3/4,1/4) → (1,0)` excludes the `1/4` record; ordering `(1/4,3/4) → (1/2,1/2)`
      does not.  The only honest content is "nonzero gridWeight is a multiple of
      `1/N`" — a property of the SELECTOR measure, not a Born threshold.
    • The grid CONTRADICTS two of QIQT-H's own machine-checked results: it breaks
      **envariance** (equal-weight records get unequal grid weights, e.g.
      `(1/3,1/3,1/3), N=2 → (1/2,1/2,0)`), and it breaks **operational
      no-signaling** (rounding joint records makes a remote marginal depend on the
      correlation, an order-`1/N` signal).  So the grid is NOT viable as physics.
    • "Finite-λ forces contextuality" is FALSE (contextuality is forced by
      Kochen–Specker/Bell, not by a bit budget); the forcing argument
      (`λ` instantiated in `R` ⇒ bounded by `Q_R`) is incoherent for a
      non-dynamical λ.  See `paper_strategy/49_Finite_Information_Lambda.md`.

  WHAT THE THEOREMS ACTUALLY SAY (correct, axiom-free), about THIS sampler only:
  with `gridCount(α) = ⌈N·lo_{α+1}⌉ − ⌈N·loₐ⌉` and `gridWeight = gridCount/N`,
    * `gridCount_sum`/`gridWeight_sum` — the `N` cells partition the seeds; the grid
      weights are a probability on the lattice `k/N`;
    * `gridWeight_near_born` — `|gridWeight − pₐ| < 1/N` (lattice rounding error);
    * `gridWeight_tendsto_born` — `gridWeight → pₐ` as `N→∞`;
    * `resolution_floor` — for SOME ordering and `N`, a positive-weight record gets
      `0` cells (ordering-dependent; NOT a physical Born threshold — see caveat).
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

/-- **Lattice rounding error**: the grid weight is within `1/N` of the Born weight,
    `|gridWeight − pₐ| < 1/N`.  (This is the rounding error of the `k/N` lattice, not
    a physical "Born deviation" — see the module caveat.) -/
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

/-- **An ordering-dependent zero (NOT a physical threshold).**  For SOME record
    ordering and resolution `N`, a positive-weight record gets ZERO grid cells (here
    `p = (3/4, 1/4)`, `N = 2`).  CAVEAT (see module header): this is *not* a "minimum
    actualizable Born weight" — it is an artifact of the grid + the chosen ordering.
    The same Born distribution in the order `(1/4, 3/4)` gives `(1/2, 1/2)`, with the
    `1/4` record *not* excluded.  The only honest content is that nonzero grid weights
    are multiples of `1/N`. -/
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

/-- **Audit conclusion.**  Correct, axiom-free arithmetic for ONE finite inverse-CDF
    sampler: the `N` cells partition the seeds (`gridCount_sum`), the grid weights are
    a probability on the `k/N` lattice (`gridWeight_sum`) within `1/N` of Born
    (`gridWeight_near_born`), exact as `N→∞` (`gridWeight_tendsto_born`), with an
    ordering-dependent zero (`resolution_floor`).  Its INTERPRETATION as a physical
    "finite-information λ" is RETRACTED (see module header): finite *value-space* λ
    reproduces Born exactly with no deviation; this particular grid is an artifact and
    moreover breaks QIQT-H's own envariance and no-signaling.  Not viable as physics. -/
theorem audit_conclusion : True := trivial

end QIQTH.FiniteInfoLambda
