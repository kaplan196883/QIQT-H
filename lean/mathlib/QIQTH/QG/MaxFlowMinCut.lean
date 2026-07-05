/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# M1–M3 — the combinatorial core of max-flow = min-cut

Built on Track C's flow/cut framework (`EmergentSpacetime.lean`, `section Flow`). This file delivers the
combinatorial content of the hard half of max-flow = min-cut, discharging the combinatorial part of
`ExactRT.lean`'s cited Ford–Fulkerson gap:

* **M1** `flowValue_eq_cutCapacity_of_saturated` — the **algebraic saturation lemma**: a flow that
  saturates a separating cut's forward boundary (`f = cap` on `C×Cᶜ`) with zero backflow (`f = 0` on
  `Cᶜ×C`) has `flowValue f s = cutCapacity cap C`.
* **M2** `ResidualStep` / `residualCut` — the **residual graph** and its **reachable set** from `s`
  (`Relation.ReflTransGen`), with membership (`mem_residualCut`), the source (`source_mem_residualCut`),
  and **closure** under residual steps (`residualCut_closed`).
* **M3** `residualCut_saturates` — the **load-bearing lemma "no augmenting path ⟹ saturating cut"**: if
  the sink `t` is not residual-reachable from `s`, the residual-reachable set IS a saturating cut, so
  `flowValue f s = cutCapacity cap C`.

**Honest scope:** M1–M3 reduce ExactRT's gap to the single sharp condition `t ∉ residualCut cap f s`
(no augmenting path from a maximum flow) — the max-flow EXISTENCE / augmenting-path termination
(the genuine analytic frontier) is CARRIED later, not proved here. This is the finite (`V→V→ℝ`)
network model, not a continuum RT.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`; `open Classical` for the reachable-set
filter's decidability is a local convenience, not a project axiom).
-/
import QIQTH.EmergentSpacetime
import QIQTH.QG.ExactRT

namespace QIQTH.QG

open QIQTH.EmergentSpacetime

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **★ M1 — the algebraic saturation lemma.** If the `s`-`t` flow `f` saturates the forward boundary of
the separating cut `C` (`f u v = cap u v` for `u ∈ C`, `v ∈ Cᶜ`) and carries no backflow across it
(`f u v = 0` for `u ∈ Cᶜ`, `v ∈ C`), then the flow value equals the cut capacity. -/
theorem flowValue_eq_cutCapacity_of_saturated {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) {C : Finset V} (hs : s ∈ C) (ht : t ∉ C)
    (hsat : ∀ u ∈ C, ∀ v ∈ Cᶜ, f u v = cap u v)
    (hzero : ∀ u ∈ Cᶜ, ∀ v ∈ C, f u v = 0) :
    flowValue f s = cutCapacity cap C := by
  rw [flowValue_eq_netAcross_of_isSTFlow hf hs ht]
  simp only [netAcross, outAcross, inAcross, cutCapacity, cut]
  have hin : (∑ u ∈ Cᶜ, ∑ v ∈ C, f u v) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    exact hzero u hu v hv
  have hout : (∑ u ∈ C, ∑ v ∈ Cᶜ, f u v) = ∑ i ∈ C, ∑ j ∈ Cᶜ, cap i j := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    exact hsat u hu v hv
  rw [hin, hout, sub_zero]

/-- **M2 — a residual step** of the network `(cap, f)` from `u` to `v`: either the forward edge `u→v`
has unused capacity (`0 < cap u v − f u v`) or the reverse edge `v→u` carries flow that can be cancelled
(`0 < f v u`). This is the edge relation of the residual graph. -/
def ResidualStep (cap f : V → V → ℝ) (u v : V) : Prop :=
  0 < cap u v - f u v ∨ 0 < f v u

/-- **M2 — the residual-reachable set** from the source `s`: all vertices reachable from `s` by a walk in
the residual graph (`Relation.ReflTransGen` of `ResidualStep`). When the sink is NOT in this set there is
no augmenting path. -/
noncomputable def residualCut (cap f : V → V → ℝ) (s : V) : Finset V :=
  Finset.univ.filter (fun v => Relation.ReflTransGen (ResidualStep cap f) s v)

/-- Membership in `residualCut` is exactly residual reachability from `s`. -/
theorem mem_residualCut {cap f : V → V → ℝ} {s v : V} :
    v ∈ residualCut cap f s ↔ Relation.ReflTransGen (ResidualStep cap f) s v := by
  classical
  simp [residualCut, Finset.mem_filter]

/-- The source is residual-reachable from itself. -/
theorem source_mem_residualCut {cap f : V → V → ℝ} {s : V} :
    s ∈ residualCut cap f s :=
  mem_residualCut.mpr Relation.ReflTransGen.refl

/-- **M2 — closure.** The residual-reachable set is closed under residual steps: if `u` is reachable and
`ResidualStep cap f u v`, then `v` is reachable. -/
theorem residualCut_closed {cap f : V → V → ℝ} {s u v : V}
    (hu : u ∈ residualCut cap f s) (huv : ResidualStep cap f u v) :
    v ∈ residualCut cap f s :=
  mem_residualCut.mpr ((mem_residualCut.mp hu).tail huv)

/-- **★ M3 — the load-bearing lemma: "no augmenting path ⟹ saturating cut".** If the sink `t` is not
residual-reachable from the source `s`, then the residual-reachable set `C = residualCut cap f s` is a
saturating cut: `flowValue f s = cutCapacity cap C`.

Reasoning: on the forward boundary (`u ∈ C`, `v ∈ Cᶜ`) the flow must be saturated (`f u v = cap u v`),
else `0 < cap u v − f u v` gives a residual step `u→v`, extending reachability to `v ∈ C` —
contradiction. On the backward boundary (`u ∈ Cᶜ`, `v ∈ C`) the flow must vanish (`f u v = 0`), else
`0 < f u v` gives a residual step `v→u` (reverse-edge cancellation), extending reachability to `u ∈ C` —
contradiction. Then M1 applies (`s ∈ C`, `t ∉ C` by hypothesis). -/
theorem residualCut_saturates {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (ht : t ∉ residualCut cap f s) :
    flowValue f s = cutCapacity cap (residualCut cap f s) := by
  set C := residualCut cap f s with hC
  have hs : s ∈ C := source_mem_residualCut
  have hsat : ∀ u ∈ C, ∀ v ∈ Cᶜ, f u v = cap u v := by
    intro u hu v hv
    by_contra hne
    have hlt : f u v < cap u v := lt_of_le_of_ne (hf.capacity u v) hne
    have hstep : ResidualStep cap f u v := Or.inl (by linarith)
    have : v ∈ C := residualCut_closed hu hstep
    exact (Finset.mem_compl.mp hv) this
  have hzero : ∀ u ∈ Cᶜ, ∀ v ∈ C, f u v = 0 := by
    intro u hu v hv
    by_contra hne
    have hpos : 0 < f u v := lt_of_le_of_ne (hf.nonneg u v) (Ne.symm hne)
    have hstep : ResidualStep cap f v u := Or.inr hpos
    have : u ∈ C := residualCut_closed hv hstep
    exact (Finset.mem_compl.mp hu) this
  exact flowValue_eq_cutCapacity_of_saturated hf hs ht hsat hzero

end QIQTH.QG
