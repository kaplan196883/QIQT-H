/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# M1–M5 — the combinatorial core of max-flow = min-cut

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
* **M4** `IsMaxSTFlow` / `exact_rt_of_maxFlow` — **maximality** of an `s`-`t` flow and the **honest
  reduction**: a maximum flow has no augmenting path (`t ∉ residualCut`), CARRYING the single
  Ford–Fulkerson analytic input `haug` (an augmenting path yields a strictly larger flow).
* **M5** `exact_rt_maxFlow_mincut` — the **capstone**: max-flow = min-cut on the tower's flow/cut
  framework — `flowValue f s = cutCapacity cap (residualCut cap f s)` for a maximum flow, CONDITIONAL
  ONLY on the carried augmentation-existence `haug`.

**Honest scope:** M1–M3 reduce ExactRT's gap to the single sharp condition `t ∉ residualCut cap f s`
(no augmenting path from a maximum flow); M4–M5 derive that condition and the capstone
max-flow = min-cut from maximality, CARRYING the Ford–Fulkerson analytic content (`haug`: an
augmenting path augments the flow value) as a named hypothesis — NOT proved here. The augmenting-flow
construction (define `g` by modifying `f` by `ε` along a residual walk, re-prove `IsSTFlow`) and
max-flow EXISTENCE are the genuine analytic frontier. This is the finite (`V→V→ℝ`) network model,
not a continuum RT.

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

/-- **M4 — maximality of an `s`-`t` flow.** `f` is a maximum `s`-`t` flow if it is a flow whose value
dominates that of every other `s`-`t` flow `g`. -/
def IsMaxSTFlow (cap : V → V → ℝ) (s t : V) (f : V → V → ℝ) : Prop :=
  IsSTFlow cap s t f ∧ ∀ g, IsSTFlow cap s t g → flowValue g s ≤ flowValue f s

/-- **★ M4 (Attempt A) — the honest reduction: a maximum flow has no augmenting path.** If `f` is a
maximum `s`-`t` flow, then the sink `t` is not residual-reachable from `s` (`t ∉ residualCut`).

This isolates the genuine Ford–Fulkerson analytic content as the CARRIED hypothesis `haug`: *if* the
sink is residual-reachable (an augmenting path exists) *then* one can build a strictly larger flow `g`.
Given `haug`, maximality forbids that: `haug ht` yields `g` with `flowValue f s < flowValue g s`, while
`hmax.2 g hg` gives `flowValue g s ≤ flowValue f s` — contradiction. The augmenting-flow CONSTRUCTION
(modify `f` by `ε > 0` along the residual walk, re-prove `IsSTFlow`) is the frontier, not derived here. -/
theorem exact_rt_of_maxFlow {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hmax : IsMaxSTFlow cap s t f) (hst : s ≠ t)
    (haug : t ∈ residualCut cap f s →
      ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s) :
    t ∉ residualCut cap f s := by
  intro ht
  obtain ⟨g, hg, hlt⟩ := haug ht
  have hle : flowValue g s ≤ flowValue f s := hmax.2 g hg
  linarith

/-- **★★ M5 — the capstone: max-flow = min-cut on the tower's flow/cut framework.** For a maximum
`s`-`t` flow `f`, the flow value equals the capacity of the residual-reachable cut:
`flowValue f s = cutCapacity cap (residualCut cap f s)`.

Combining M4's `exact_rt_of_maxFlow` (no augmenting path from a maximum flow) with M3's
`residualCut_saturates` (no augmenting path ⟹ the residual-reachable set is a saturating cut). This is
the hard half of max-flow = min-cut, CONDITIONAL ONLY on the carried augmentation-existence `haug` —
the single Ford–Fulkerson analytic input. With M3 + `ExactRT`'s `exact_rt_of_saturating` this
discharges the combinatorial content of ExactRT's cited Ford–Fulkerson gap.

**Carried (the frontier):** `haug` — that a residual (augmenting) path yields a strictly larger flow;
its proof needs the augmenting-flow construction (define `g = f ± ε` along a residual `ReflTransGen`
walk, re-prove conservation/capacity/nonneg) plus max-flow EXISTENCE (compactness / Ford–Fulkerson
termination). **Derived (machine-checked here):** everything else — that maximality + `haug` gives no
augmenting path, and that no augmenting path gives `flowValue = cutCapacity`. -/
theorem exact_rt_maxFlow_mincut {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hmax : IsMaxSTFlow cap s t f) (hst : s ≠ t)
    (haug : t ∈ residualCut cap f s →
      ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s) :
    flowValue f s = cutCapacity cap (residualCut cap f s) :=
  residualCut_saturates hmax.1 (exact_rt_of_maxFlow hmax hst haug)

/-- **M4 (Attempt B) — a concrete single-edge augmentation (mechanism witness).** If the direct source→sink
edge `s→t` carries forward slack (`f s t < cap s t`), then adding `ε = cap s t − f s t > 0` on that edge
yields a valid `s`-`t` flow of strictly larger value. This is the simplest instance of the augmenting-flow
construction underlying the carried `haug`: augmenting along the one-edge residual path `s → t` bumps
`flowValue` by `ε`. Conservation is untouched (the modified edge touches only `s` and `t`, both excluded
from conservation); capacity holds since `g s t = cap s t`; nonnegativity since we add `ε ≥ 0`. -/
theorem singleEdge_augment_forward {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (hst : s ≠ t) (hslack : f s t < cap s t) :
    ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s := by
  classical
  set ε := cap s t - f s t with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  refine ⟨fun u v => f u v + (if u = s ∧ v = t then ε else 0), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- nonneg
    intro u v
    have := hf.nonneg u v
    split <;> linarith
  · -- capacity
    intro u v
    by_cases h : u = s ∧ v = t
    · obtain ⟨hu, hv⟩ := h
      subst hu; subst hv
      simp only [and_self, if_true]
      rw [hε]; linarith
    · simp only [h, if_false, add_zero]
      exact hf.capacity u v
  · -- conserve
    intro v hvs hvt
    unfold vertexExcess
    have h1 : (∑ w, (f v w + (if v = s ∧ w = t then ε else 0))) = ∑ w, f v w := by
      rw [Finset.sum_add_distrib]
      have hz : (∑ w, (if v = s ∧ w = t then ε else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro w _
        rw [if_neg]
        rintro ⟨rfl, _⟩; exact hvs rfl
      rw [hz, add_zero]
    have h2 : (∑ w, (f w v + (if w = s ∧ v = t then ε else 0))) = ∑ w, f w v := by
      rw [Finset.sum_add_distrib]
      have hz : (∑ w, (if w = s ∧ v = t then ε else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro w _
        rw [if_neg]
        rintro ⟨_, rfl⟩; exact hvt rfl
      rw [hz, add_zero]
    rw [h1, h2]
    exact hf.conserve v hvs hvt
  · -- value strictly increases
    unfold flowValue vertexExcess
    have h1 : (∑ w, (f s w + (if s = s ∧ w = t then ε else 0))) = (∑ w, f s w) + ε := by
      rw [Finset.sum_add_distrib]
      congr 1
      have hcong : (∑ w, (if s = s ∧ w = t then ε else 0)) = ∑ w, (if w = t then ε else 0) := by
        apply Finset.sum_congr rfl
        intro w _
        simp
      rw [hcong, Finset.sum_ite_eq']
      simp
    have h2 : (∑ w, (f w s + (if w = s ∧ s = t then ε else 0))) = ∑ w, f w s := by
      rw [Finset.sum_add_distrib]
      have hz : (∑ w, (if w = s ∧ s = t then ε else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro w _
        rw [if_neg]
        rintro ⟨_, rfl⟩; exact hst rfl
      rw [hz, add_zero]
    rw [h1, h2]
    linarith

end QIQTH.QG
