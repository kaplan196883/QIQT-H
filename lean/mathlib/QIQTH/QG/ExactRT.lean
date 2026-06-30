/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# I6 — exact finite RT: the optimality-certificate (hard) half of max-flow = min-cut

Phase C of the QG campaign (`QG_CAMPAIGN_PLAN.md`), Tier-3 §3.2 ("RT as a substrate theorem"). Track C
(`EmergentSpacetime.lean`) proved the **easy** half of max-flow/min-cut — `flow_weak_duality`: every `s`-`t`
flow value is `≤` every separating cut's capacity. The **exact RT equality** `max-flow = min-cut` is the hard
half; Mathlib has **no** max-flow theorem.

This file delivers the **optimality-certificate** reduction: a *saturating witness* — a flow `f` and a separating
cut `C` with `flowValue f s = cutCapacity cap C` — **certifies** the equality. Given such a witness:
`f` maximizes the flow (no flow exceeds it), `C` minimizes the cut (no separating cut is cheaper), and their
common value is simultaneously the max flow and the min cut — i.e. **exact RT holds**. So exact RT is *reduced*
to producing a saturating witness; the witness existence (the Ford–Fulkerson augmenting-path construction /
Menger's theorem) is the cited Mathlib-gap frontier — a genuine multi-week formalization, honestly checkpointed
here, not faked. We also prove the **min-cut is attained** (finitely many cuts), so "min-cut" is well-defined.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).
-/
import QIQTH.EmergentSpacetime

namespace QIQTH.QG

open QIQTH.EmergentSpacetime

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **saturating flow is maximal**: if `f` saturates the separating cut `C`
(`flowValue f s = cutCapacity cap C`), then no `s`-`t` flow `f'` exceeds it (weak duality against `C`). -/
theorem saturating_flow_isMax {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) {C : Finset V} (hs : s ∈ C) (ht : t ∉ C)
    (hsat : flowValue f s = cutCapacity cap C)
    {f' : V → V → ℝ} (hf' : IsSTFlow cap s t f') :
    flowValue f' s ≤ flowValue f s := by
  rw [hsat]; exact flow_weak_duality hf' hs ht

/-- A **saturated cut is minimal**: if `f` saturates `C`, then no separating cut `C'` is cheaper than `C`
(weak duality of `f` against `C'`). -/
theorem saturated_cut_isMin {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) {C : Finset V} (hs : s ∈ C) (ht : t ∉ C)
    (hsat : flowValue f s = cutCapacity cap C)
    {C' : Finset V} (hs' : s ∈ C') (ht' : t ∉ C') :
    cutCapacity cap C ≤ cutCapacity cap C' := by
  rw [← hsat]; exact flow_weak_duality hf hs' ht'

/-- **★ I6 — exact RT from an optimality certificate.** A saturating witness (`flowValue f s =
cutCapacity cap C`) certifies `max-flow = min-cut`: `f` maximizes the flow value over all `s`-`t` flows AND
`C` minimizes the capacity over all separating cuts. Their common value `flowValue f s = cutCapacity cap C`
is therefore simultaneously the maximum flow and the minimum cut — the exact Ryu–Takayanagi equality, REDUCED
to the existence of a saturating witness (the easy/optimality-certificate half). -/
theorem exact_rt_of_saturating {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) {C : Finset V} (hs : s ∈ C) (ht : t ∉ C)
    (hsat : flowValue f s = cutCapacity cap C) :
    (∀ f', IsSTFlow cap s t f' → flowValue f' s ≤ flowValue f s) ∧
    (∀ C', s ∈ C' → t ∉ C' → cutCapacity cap C ≤ cutCapacity cap C') :=
  ⟨fun _ hf' => saturating_flow_isMax hf hs ht hsat hf',
   fun _ hs' ht' => saturated_cut_isMin hf hs ht hsat hs' ht'⟩

/-- **The min-cut is attained.** Over a finite vertex type there are finitely many separating cuts and at
least one (`{s}`, since `s ≠ t`), so the minimum separating-cut capacity is achieved by some cut. (This makes
"min-cut" — the RHS of exact RT — a well-defined attained quantity, not just an infimum.) -/
theorem minCut_attained (cap : V → V → ℝ) {s t : V} (hst : s ≠ t) :
    ∃ C : Finset V, (s ∈ C ∧ t ∉ C) ∧
      ∀ C' : Finset V, s ∈ C' → t ∉ C' → cutCapacity cap C ≤ cutCapacity cap C' := by
  classical
  have hne : (Finset.univ.filter (fun C : Finset V => s ∈ C ∧ t ∉ C)).Nonempty :=
    ⟨{s}, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      Finset.mem_singleton_self s, fun h => hst.symm (Finset.mem_singleton.1 h)⟩⟩
  obtain ⟨C, hCmem, hCmin⟩ := Finset.exists_min_image _ (cutCapacity cap) hne
  rw [Finset.mem_filter] at hCmem
  refine ⟨C, hCmem.2, fun C' hs' ht' => hCmin C' ?_⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hs', ht'⟩

end QIQTH.QG
