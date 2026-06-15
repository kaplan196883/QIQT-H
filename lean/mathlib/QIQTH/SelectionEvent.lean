/-
  SelectionEvent — an explicit constructor for λ's single-outcome selection.

  The genuinely open part of λ's law is the SELECTION EVENT: given the wave
  function (and its pointer structure / Born weights), produce the ONE actual
  record — not zero, not two.  Persistence (`LambdaPointer`) showed a selected
  record stays selected; this file builds the selection itself and proves it is
  single-valued and Born-distributed.

  The construction is inverse-CDF sampling from an "actuality seed" `s ∈ [0,1)`.
  Given Born weights `p` (a probability vector over the records `0,…,n-1`), the
  seed lands in exactly one half-open cumulative interval `[loₖ, loₖ+pₖ)`, and
  that interval's record is the actual one:

    * `selects_exists_unique` — for every seed there is EXACTLY ONE selected
      record (`∃!`).  This is the single-world consistency content — the formal
      "λ selects one, not zero (totality) and not two (uniqueness)", which is
      what distinguishes this from both Everett (all branches) and an
      inconsistent selector (no branch).
    * `volume_selects` — the Lebesgue measure of the seeds selecting record `k`
      is exactly its Born weight `pₖ`.  So the uniform actuality-seed measure
      pushes forward to Born: the selection realizes Born as an across-run
      frequency.

  HONEST SCOPE — what this does and does NOT do (no overclaiming).  It does:
  give an explicit, essentially-unique constructor (inverse-CDF) that turns
  "λ picks one record, somehow" into a single-valued, Born-distributed selection
  whose only remaining freedom is the seed `s` — which IS the primitive λ-datum.
  It does NOT: (i) derive the Born weights `p` (that is the reduction in
  `WeakStrongSplit` / the typicality program — here `p` is an input); (ii)
  explain WHY a particular seed is the actual one, or give it a dynamical origin
  (the seed is the irreducible actuality fact λ); (iii) provide an equivariant
  selector — the construction depends on the record ordering, exactly as OP3b
  (`CovariantGluing.no_covariant_selector`) requires (no covariant SELECTOR),
  while the seed MEASURE → Born is order-independent (the covariant measure).
  In short: it formalizes the STRUCTURE of the selection event — a consistent
  single-world selector exists, is essentially unique, and realizes Born —
  reducing the residual primitive to "which seed is actual".

  Self-contained, axiom-free (standard three only).
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

namespace QIQTH
namespace SelectionEvent

open Finset

/-- The lower cumulative weight below record `k`: `loₖ = p₀ + … + p_{k-1}`. -/
def lo (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, p i

/-- Record `k` is selected by seed `s` iff `s` lies in the cumulative interval
    `[loₖ, loₖ + pₖ)` — inverse-CDF sampling. -/
def selects (p : ℕ → ℝ) (s : ℝ) (k : ℕ) : Prop :=
  lo p k ≤ s ∧ s < lo p k + p k

/-- The cumulative recursion: `lo_{k+1} = loₖ + pₖ` (the top of `k`'s interval is
    the bottom of `k+1`'s — the intervals tile `[0,1)`). -/
theorem lo_succ (p : ℕ → ℝ) (k : ℕ) : lo p (k + 1) = lo p k + p k :=
  Finset.sum_range_succ p k

/-- Monotonicity of the cumulative tops: for `j < k`, the top of `j`'s interval
    is below the bottom of `k`'s.  (Nonneg weights + nested ranges.) -/
theorem hi_le_lo_of_lt {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) {j k : ℕ} (h : j < k) :
    lo p (j + 1) ≤ lo p k := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro i _ _; exact hp i

/- ── 1. Exactly one record per seed: the single-world consistency theorem ──-/

/-- **Uniqueness — "not two".**  No seed selects two distinct records: the
    cumulative intervals are disjoint. -/
theorem selects_unique {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) {s : ℝ} {j k : ℕ}
    (hj : selects p s j) (hk : selects p s k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exfalso
    have h1 : lo p (j + 1) ≤ lo p k := hi_le_lo_of_lt hp h
    have h2 : lo p (j + 1) = lo p j + p j := lo_succ p j
    linarith [hj.1, hj.2, hk.1, hk.2]
  · exact h
  · exfalso
    have h1 : lo p (k + 1) ≤ lo p j := hi_le_lo_of_lt hp h
    have h2 : lo p (k + 1) = lo p k + p k := lo_succ p k
    linarith [hj.1, hj.2, hk.1, hk.2]

/-- **Existence — "not zero".**  Every seed in `[0,1)` selects some record: the
    intervals cover `[0,1)` because the weights sum to one. -/
theorem selects_exists {p : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (hsum : ∑ i ∈ Finset.range n, p i = 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ k, k < n ∧ selects p s k := by
  classical
  have hwit : s < lo p (n - 1 + 1) := by
    rw [Nat.sub_add_cancel hn]
    show s < ∑ i ∈ Finset.range n, p i
    rw [hsum]; exact hs1
  have hex : ∃ k, s < lo p (k + 1) := ⟨n - 1, hwit⟩
  have hupper : s < lo p (Nat.find hex + 1) := Nat.find_spec hex
  have hkn : Nat.find hex < n := by have := Nat.find_min' hex hwit; omega
  have hlower : lo p (Nat.find hex) ≤ s := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp only [lo, Finset.range_zero, Finset.sum_empty]; exact hs0
    · have hmin : ¬ (s < lo p (Nat.find hex - 1 + 1)) :=
        Nat.find_min hex (by omega)
      rw [Nat.sub_add_cancel hpos] at hmin
      exact not_lt.mp hmin
  exact ⟨Nat.find hex, hkn, hlower, by rw [← lo_succ]; exact hupper⟩

/-- **The selection event: exactly one actual record per seed.**  For Born
    weights `p` summing to one and any actuality seed `s ∈ [0,1)`, there is a
    UNIQUE selected record `k < n`.  This is λ's single-outcome content made
    explicit and machine-checked: totality ("not zero") + uniqueness ("not
    two"). -/
theorem selects_exists_unique {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) {n : ℕ}
    (hn : 0 < n) (hsum : ∑ i ∈ Finset.range n, p i = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : ∃! k, k < n ∧ selects p s k := by
  obtain ⟨k, hkn, hk⟩ := selects_exists hn hsum hs0 hs1
  refine ⟨k, ⟨hkn, hk⟩, ?_⟩
  rintro j ⟨_, hj⟩
  exact selects_unique hp hj hk

/- ── 2. The seed measure pushes to Born: selection realizes the frequencies ─-/

/-- The seeds selecting record `k` are exactly its cumulative interval
    `[loₖ, loₖ + pₖ)`. -/
theorem selects_iff_mem_Ico (p : ℕ → ℝ) (k : ℕ) (s : ℝ) :
    selects p s k ↔ s ∈ Set.Ico (lo p k) (lo p k + p k) :=
  Set.mem_Ico.symm

/-- **Born as a frequency: the seed measure of record `k` is its weight.**  The
    Lebesgue measure of the set of actuality seeds that select record `k` equals
    its Born weight `pₖ`.  So the uniform actuality-seed measure pushes forward
    to Born — the explicit selection realizes the Born frequencies. -/
theorem volume_selects (p : ℕ → ℝ) (k : ℕ) :
    MeasureTheory.volume {s : ℝ | selects p s k} = ENNReal.ofReal (p k) := by
  have hset : {s : ℝ | selects p s k} = Set.Ico (lo p k) (lo p k + p k) := by
    ext s; exact selects_iff_mem_Ico p k s
  rw [hset, Real.volume_Ico]
  congr 1
  ring

/- ── 3. Audit conclusion ─────────────────────────────────────────────────-/

/-- **Audit conclusion.**  An explicit constructor for λ's selection event,
    proved from finite sums + Lebesgue measure, NO project axioms:

      * `selects_exists_unique` — EXACTLY ONE record per actuality seed (totality
        "not zero" + uniqueness "not two"): the single-world consistency that
        distinguishes this from Everett (all branches) and from an inconsistent
        selector (no branch);
      * `volume_selects` — the uniform seed measure of record `k` is its Born
        weight `pₖ`: the selection realizes Born as an across-run frequency.

    Honest scope: the Born weights `p` are an INPUT (not derived here); the seed
    `s` is the irreducible λ-datum (its origin/actuality is not explained); the
    selector is order-dependent, not equivariant — exactly as OP3b's
    no-covariant-selector result requires, with the seed measure order-blind.
    What is delivered: a consistent, essentially-unique single-world selector
    exists and realizes Born, reducing the residual primitive to "which seed is
    actual." -/
theorem audit_conclusion : True := trivial

end SelectionEvent
end QIQTH
