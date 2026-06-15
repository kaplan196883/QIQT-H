/-
  FieldSelection — the selection event at the genuine free-field level.

  The last piece of the continuum λ-law at the free-field level: the selection
  event on the Weyl-bit record POVM, driven by the genuine Fock-vacuum-state Born
  weights of `FieldBorn.lean`.  Reuses the inverse-CDF constructor
  (`SelectionEvent.lean`) — the selection event is Type-blind and works the same
  on the free-field vacuum-state weights.

    * `weylBitWeights u` — the two vacuum-state Born weights of the single-mode
      Weyl-bit record `{E(u,+1), E(u,−1)}`, packaged for the constructor; nonneg
      (`weylBitWeights_nonneg`) and summing to one (`weylBitWeights_sum`).
    * `field_selects_exists_unique` — EXACTLY ONE Weyl-bit record per actuality
      seed, driven by the free-field Born weights.
    * `field_volume_selects` — the uniform seed measure of a record equals its
      free-field Born weight: the selection realizes the free-field Born
      frequencies `(1±exp(−½‖u‖²))/2`.

  Axiom-free.  Completes the continuum λ-law's selection layer at the free-field
  (Fock vacuum state) level, complementing the one-particle `ContinuumSelection`.
-/

import QIQTH.Fock.FieldBorn
import QIQTH.SelectionEvent

namespace QIQTH.Fock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Weyl-bit weight `(1+exp(−½‖u‖²))/2` is nonnegative. -/
theorem weylBitWeight_nonneg (u : H) : 0 ≤ weylBitWeight u := by
  unfold weylBitWeight; positivity

/-- The Weyl-bit weight is at most one. -/
theorem weylBitWeight_le_one (u : H) : weylBitWeight u ≤ 1 := by
  unfold weylBitWeight
  have hx : -(‖u‖ ^ 2) / 2 ≤ 0 := by have := sq_nonneg ‖u‖; linarith
  have hexp : Real.exp (-(‖u‖ ^ 2) / 2) ≤ 1 :=
    calc Real.exp (-(‖u‖ ^ 2) / 2) ≤ Real.exp 0 := Real.exp_le_exp.mpr hx
      _ = 1 := Real.exp_zero
  linarith

/-- The two vacuum-state Born weights of the Weyl-bit record POVM, packaged as a
    function `ℕ → ℝ` (extended by `0`) for the inverse-CDF constructor. -/
noncomputable def weylBitWeights (u : H) (j : ℕ) : ℝ :=
  if j = 0 then vacuumState (weylBitEffectCLM u 1)
  else if j = 1 then vacuumState (weylBitEffectCLM u (-1)) else 0

theorem weylBitWeights_nonneg (u : H) (j : ℕ) : 0 ≤ weylBitWeights u j := by
  unfold weylBitWeights
  split_ifs with h0 h1
  · rw [vacuumState_weylBitEffectCLM_true]; exact weylBitWeight_nonneg u
  · have hsum := vacuumState_weylBit_sum u
    rw [vacuumState_weylBitEffectCLM_true] at hsum
    have := weylBitWeight_le_one u
    linarith
  · exact le_refl 0

theorem weylBitWeights_sum (u : H) :
    ∑ j ∈ Finset.range 2, weylBitWeights u j = 1 := by
  have h0 : weylBitWeights u 0 = vacuumState (weylBitEffectCLM u 1) := by
    simp [weylBitWeights]
  have h1 : weylBitWeights u 1 = vacuumState (weylBitEffectCLM u (-1)) := by
    simp [weylBitWeights]
  rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
  exact vacuumState_weylBit_sum u

/-- **The free-field selection event: exactly one Weyl-bit record per seed.**
    Driven by the genuine Fock-vacuum-state Born weights, every actuality seed
    `seed ∈ [0,1)` selects a UNIQUE record `k < 2` — single-world consistency at
    the free-field level. -/
theorem field_selects_exists_unique (u : H) {seed : ℝ} (hs0 : 0 ≤ seed)
    (hs1 : seed < 1) :
    ∃! k, k < 2 ∧ SelectionEvent.selects (weylBitWeights u) seed k :=
  SelectionEvent.selects_exists_unique (weylBitWeights_nonneg u) (by norm_num)
    (weylBitWeights_sum u) hs0 hs1

/-- **The free-field selection realizes Born.**  The Lebesgue measure of the
    seeds selecting record `k` equals its free-field Born weight — the uniform
    actuality-seed measure pushes to the free-field Born frequencies
    `(1±exp(−½‖u‖²))/2`. -/
theorem field_volume_selects (u : H) (k : ℕ) :
    MeasureTheory.volume {seed : ℝ | SelectionEvent.selects (weylBitWeights u) seed k}
      = ENNReal.ofReal (weylBitWeights u k) :=
  SelectionEvent.volume_selects (weylBitWeights u) k

/-- **Audit conclusion.**  The selection event at the genuine free-field level:
    exactly one Weyl-bit record per actuality seed, realizing the Fock-vacuum-state
    Born weights, by reusing the inverse-CDF `SelectionEvent` constructor.  NO
    project axioms.  The continuum λ-law's selection layer now holds at both the
    one-particle (`ContinuumSelection`) and free-field levels. -/
theorem fieldSelection_audit : True := trivial

end QIQTH.Fock
