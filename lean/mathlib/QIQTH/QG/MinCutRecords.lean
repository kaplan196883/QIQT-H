/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# I7 (Lean core) — min-cut bounds the distinguishable-record capacity (RT-from-QEC, finite form)

Phase D of the QG campaign (`QG_CAMPAIGN_PLAN.md`), Tier-2 §2.2 ("the capacity-is-area law, derived FROM the
substrate"). In a finite holographic code / random-tensor-network, a boundary region's distinguishable-record
capacity is bounded by the **min-cut "area"**, not its volume. This is the structural claim a HaPPY/RTN substrate
exhibits; here is its finite Lean core, complementing Track C's `entropy_le_cut`.

A region whose cut / bond space has dimension `card dCut` can carry at most `card dCut` perfectly
**distinguishable records** (orthogonal states distinguishable by a measurement confined to the cut/boundary):
no more than `dim` mutually orthogonal states exist. So if `N` records fit (`N ≤ card dCut`) and the bond
dimension fits the cut area (`log(card dCut) ≤ cut w S` — the tensor-network/holographic bond bound), then the
record information is bounded by the min-cut area:

    log N ≤ cut w S.

This is the area (not volume) law for the *distinguishable-record* capacity, as a theorem about the code's cut,
built on Track C's `cut` (B2). The matching *physics* claim "this min-cut is the geometric area `A/4ℓ_P²`" stays
the carried UV datum; the value of `G` / the `1/4` is never asserted. Axiom-free
(standard `propext`/`Classical.choice`/`Quot.sound`).
-/
import QIQTH.EmergentSpacetime

namespace QIQTH.QG

open QIQTH.EmergentSpacetime

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **★ I7 — min-cut bounds the distinguishable-record capacity.** If `N` mutually distinguishable records fit
in the cut/bond space (`N ≤ card dCut`) and the bond dimension fits the cut area
(`log(card dCut) ≤ cut w S`), then the record information obeys the **min-cut area bound** `log N ≤ cut w S`.
The finite, area-law (not volume-law) statement of the distinguishable-record capacity across a cut. -/
theorem mincut_bounds_distinguishable_records {dCut : Type*} [Fintype dCut]
    (w : V → V → ℝ) (S : Finset V) {N : ℕ} (hN : 0 < N) (hrec : N ≤ Fintype.card dCut)
    (hbond : Real.log (Fintype.card dCut) ≤ cut w S) :
    Real.log N ≤ cut w S :=
  le_trans (Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast hrec)) hbond

/-- **The record COUNT form:** at most `exp(cut w S)` distinguishable records fit across the cut — the
exponential of the min-cut area bounds the number of records (`N ≤ card dCut ≤ exp(cut w S)`). -/
theorem record_count_le_exp_cut {dCut : Type*} [Fintype dCut]
    (w : V → V → ℝ) (S : Finset V) {N : ℕ} (hN : 0 < N) (hrec : N ≤ Fintype.card dCut)
    (hbond : Real.log (Fintype.card dCut) ≤ cut w S) :
    (N : ℝ) ≤ Real.exp (cut w S) := by
  have h := mincut_bounds_distinguishable_records w S hN hrec hbond
  calc (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log (by exact_mod_cast hN)).symm
    _ ≤ Real.exp (cut w S) := Real.exp_le_exp.2 h

end QIQTH.QG
