/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# M1–M12 — the finite max-flow = min-cut theorem (unconditional)

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
* **M6** `singleEdge_augment_forward` / `twoEdge_augment_forward` — **derived instances of the carried
  `haug`**: the augmenting-flow construction proved concretely for a one-edge (`s→t`) and a two-edge
  (`s→w→t`) forward residual path. `twoEdge_augment_forward` is the first case exhibiting the crux of
  the general construction — **conservation preserved at an interior vertex** (`w` gets `+ε` in and
  `+ε` out) — so it derives, machine-checked, a genuine sub-case of `haug` beyond the single edge.
* **M7** `ForwardAugPath` / `forwardAugPath_augments` — **the general forward simple-path augmentation.**
  A `ForwardAugPath` packages a forward augmenting path as a degree-structured directed edge set `P`
  (interior out-degree = in-degree; source +1 out; sink +1 in; forward slack on every edge) — no
  `List`/`ReflTransGen` walk. Given a uniform positive slack margin `ε`, `g = f + ε·𝟙[P]` is re-proved a
  valid `s`-`t` flow of strictly larger value, the conservation crux discharged by the clean Finset
  identity `∑ v, (if P u v then ε else 0) = ε·(filter (P u ·) univ).card` plus the degree conditions.
  This lifts M6's hand-built 1- and 2-edge cases to the augmentation MECHANISM for **any** forward
  simple path of arbitrary length.
* **M8** `ForwardResidualStep` / `SimpleForwardPath` / `SimpleForwardPath.toForwardAugPath` /
  `forwardAugPath_augments'` / `augment_of_simpleForwardPath` — **the degree-structure extraction.** M7
  presupposed the degree-structured `ForwardAugPath`; M8 DERIVES that degree structure from a *simple*
  (de-duplicated) forward path, carried as an injective `Fin (n+1)`-indexed vertex sequence with forward
  slack on every step (`SimpleForwardPath`). By exact fibre counting — `card {v | edge u v} = card {i |
  source i = u}` and "the card of an injective fibre is `0`/`1`" (`card_filter_fiber_of_injective`) — the
  interior in/out balance (`hDeg`), source `+1`-out (`hs`) and sink `+1`-in (`ht`) fall out of
  injectivity of `p`. `forwardAugPath_augments'` then **eliminates the uniform slack margin `ε`** (its
  min over the finite nonempty path-edge set is positive), and `augment_of_simpleForwardPath` composes:
  a simple forward residual path `s ⇝ t` alone yields a strictly larger flow (`s ≠ t` itself derived
  from injectivity). What stays CARRIED is only the **directed dedup** — that a residual `ReflTransGen`
  walk produces a `SimpleForwardPath` (the directed analogue of `SimpleGraph.Walk.bypass`; Mathlib's
  `bypass`/`toPath` are undirected — `fromRel` symmetrises, giving `r u v ∨ r v u`, not the forward
  direction). This splits M7's carried extraction (a) into a DERIVED degree-structure part and the lone
  carried directed-dedup part.
* **M9** `exists_isChain_list` / `dedup_aux` / `exists_nodup_isChain_list` /
  `simpleForwardPath_of_reachable` — **the directed dedup** (the genuine hard graph-theory core, no
  Mathlib support). A forward residual `Relation.ReflTransGen (ForwardResidualStep cap f)` walk `s ⇝ t`
  is materialised as an `IsChain` `List` (`exists_isChain_list`), de-duplicated into a `Nodup` chain list
  by the **splice-shortens** induction (`dedup_aux`: strong induction on a length bound; a repeat at
  indices `a < b` is removed via `take (a+1) ++ drop (b+1)`, strictly shorter, the rejoin edge holding
  because `w[a] = w[b]` and `r w[b] w[b+1]` is an original step), and finally converted to a
  `SimpleForwardPath` (`simpleForwardPath_of_reachable`: `List` → injective `Fin (n+1) → V` via
  `w.get ∘ Fin.cast`). This is the directed analogue of `SimpleGraph.Walk.bypass`, unavailable off the
  shelf (Mathlib's `bypass`/`fromRel` are undirected). **This DISCHARGES M8's lone carried piece (a′)**:
  composed with `augment_of_simpleForwardPath`, forward residual reachability `s ⇝ t` alone yields a
  strictly larger flow.
* **M10** `ResidualAugPath` / `residualAugPath_augments` — **the mixed-direction augmentation.** A
  `ResidualAugPath` packages a general residual augmenting path as TWO typed directed-edge relations —
  forward residual edges `Pf` (slack `cap − f`) and backward residual edges `Pb` (cancel real flow) —
  with the COMBINED residual degree structure (`#Pf-out + #Pb-out = #Pf-in + #Pb-in` at interior
  vertices; source `+1`, sink `−1`). The augmented flow
  `g u v := f u v + (if Pf u v then ε) − (if Pb v u then ε)` adds `ε` on forward edges and cancels `ε`
  on the real edge that a backward residual edge reverses. `residualAugPath_augments` re-proves the full
  `IsSTFlow` (nonneg uses `ε ≤ f` on cancelled edges, capacity uses `f + ε ≤ cap` on forward edges,
  conservation via the combined degree structure — the key sign bookkeeping that an OUTGOING residual
  step contributes `+ε` and an INCOMING one `−ε` REGARDLESS of forward/backward type) and raises the
  value by `ε` at the source. This generalizes M7's forward-only `forwardAugPath_augments` to the mixed
  forward/backward residual paths of general Ford–Fulkerson — discharging carry (b) at the
  degree-structured level (the mixed walk→degree-structure extraction, the M8/M9 analogue for the
  full `ResidualStep`, remains carried).

**Honest scope:** M1–M3 reduce ExactRT's gap to the single sharp condition `t ∉ residualCut cap f s`
(no augmenting path from a maximum flow); M4–M5 derive that condition and the capstone
max-flow = min-cut from maximality, CARRYING the Ford–Fulkerson analytic content (`haug`: an
augmenting path augments the flow value) as a named hypothesis — NOT proved here. **M6–M7 discharge the
forward augmentation concretely**: M6 the one- and two-edge instances, M7 the *general* forward simple
path presented as a degree-structured edge set with a uniform slack margin (full `IsSTFlow` re-proof,
interior-vertex conservation via the degree structure, value up by `ε`). **M8 extracts the degree
structure**: from a *simple* forward path (injective vertex sequence) it DERIVES the `ForwardAugPath`
degree conditions by fibre counting and eliminates `ε`, so a simple forward path augments the flow
outright. What remains CARRIED is: (a′) the **directed dedup** — that a residual `ReflTransGen` walk
produces a *simple* forward path / `SimpleForwardPath` (repeated-vertex removal preserving endpoints and
per-step forward slack; the directed analogue of `SimpleGraph.Walk.bypass`, unavailable off the shelf
since Mathlib's undirected `bypass`/`fromRel` only yield `r u v ∨ r v u`); (b) mixed forward/backward
(residual reverse-edge) paths; and (c) max-flow EXISTENCE (compactness / Ford–Fulkerson termination). M7
removed the length obstruction and M8 the degree-extraction obstruction for forward paths, narrowing
carry (a) to the single directed-dedup step — **which M9 now discharges**
(`simpleForwardPath_of_reachable`: a forward residual `ReflTransGen` walk is materialised as an `IsChain`
list, de-duplicated by the splice-shortens induction, and converted to a `SimpleForwardPath`). So for the
FORWARD case the entire pipeline reachability ⟹ strictly larger flow is now derived; the residual carry is
only (b) mixed forward/backward paths and (c) max-flow EXISTENCE. **M11 discharges (b)**: the mixed
`SimpleResidualPath` (Step 1, M9's dedup reused verbatim on `ResidualStep`), the deterministic
forward/backward tagging into a `ResidualAugPath` (Step 2, `toResidualAugPath` — disjoint-union card split
onto M8's fibre counts), and the mixed-margin `ε` feeding M10 (`residualReachable_augments`), so GENERAL
residual reachability `s ⇝ t` alone yields a strictly larger flow — the full Ford–Fulkerson `haug`. That
`haug`, carried through M4/M5, is then DISCHARGED in `exact_rt_maxFlow_mincut_unconditional` (via
`mem_residualCut`), leaving max-flow = min-cut conditional ONLY on (c) max-flow EXISTENCE (`IsMaxSTFlow`).
**M12 discharges (c)** — the last carry: the `s`-`t` flow set is nonempty (zero flow), closed (finite
intersection of the closed nonneg/capacity/conservation conditions) and bounded (`0 ≤ f ≤ cap`) in the
finite-dimensional `V→V→ℝ`, hence compact (Heine–Borel, `Metric.isCompact_of_isClosed_isBounded`), and
`flowValue · s` is continuous, so it attains a maximum (`IsCompact.exists_isMaxOn`) — an `IsMaxSTFlow`
(`exists_maxSTFlow`). Feeding it into `exact_rt_maxFlow_mincut_unconditional` gives the UNCONDITIONAL
capstone `maxFlow_min_cut`: for any nonnegative `cap` with `s ≠ t` there is an `s`-`t` flow with
`flowValue f s = cutCapacity cap (residualCut cap f s)`, carrying ONLY `cap`-nonnegativity. Every M1–M12
ingredient is machine-checked. This is the finite (`V→V→ℝ`) network model, not a continuum RT.

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

/-- **★ M6 (Attempt B) — a concrete two-edge (forward · forward) augmentation.** If an interior vertex
`w` (distinct from `s` and `t`) has forward residual slack on both `s→w` (`f s w < cap s w`) and `w→t`
(`f w t < cap w t`), then pushing `ε = min (cap s w − f s w) (cap w t − f w t) > 0` along the two-edge
residual path `s → w → t` yields a valid `s`-`t` flow of strictly larger value.

This is the genuine two-edge composition of the augmenting-flow construction underlying the carried
`haug`, extending `singleEdge_augment_forward` from one edge to two. The crux beyond the single-edge
case is **conservation at the intermediate vertex `w`**: `w` receives `+ε` in (from `s→w`) and emits
`+ε` out (to `w→t`), so its vertex excess is unchanged — the mechanism by which an augmenting *path*
(not just a single edge) preserves conservation at every interior vertex it traverses. Capacity holds
because `ε ≤ cap s w − f s w` and `ε ≤ cap w t − f w t`; nonnegativity because `ε ≥ 0`; and the value
rises by `ε` (the `s→w` edge adds `ε` to the source's out-flow, its in-flow is untouched). -/
theorem twoEdge_augment_forward {cap : V → V → ℝ} {s w t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (hsw' : s ≠ w) (hwt' : w ≠ t) (hst : s ≠ t)
    (hsw : f s w < cap s w) (hwt : f w t < cap w t) :
    ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s := by
  classical
  set ε := min (cap s w - f s w) (cap w t - f w t) with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by linarith) (by linarith)
  have hεsw : ε ≤ cap s w - f s w := min_le_left _ _
  have hεwt : ε ≤ cap w t - f w t := min_le_right _ _
  have he0 : (0:ℝ) ≤ ε := le_of_lt hεpos
  refine ⟨fun u v => f u v + (if u = s ∧ v = w then ε else 0) + (if u = w ∧ v = t then ε else 0),
    ⟨?_, ?_, ?_⟩, ?_⟩
  · -- nonneg
    intro u v
    have h0 := hf.nonneg u v
    split <;> split <;> linarith
  · -- capacity
    intro u v
    by_cases h1 : u = s ∧ v = w
    · obtain ⟨rfl, rfl⟩ := h1
      rw [if_pos ⟨rfl, rfl⟩, if_neg (fun h => hsw' h.1)]
      linarith
    · by_cases h2 : u = w ∧ v = t
      · obtain ⟨rfl, rfl⟩ := h2
        rw [if_neg h1, if_pos ⟨rfl, rfl⟩]
        linarith
      · rw [if_neg h1, if_neg h2, add_zero, add_zero]
        exact hf.capacity u v
  · -- conserve
    intro v hvs hvt
    unfold vertexExcess
    by_cases hvw : v = w
    · -- the intermediate vertex: +ε in and +ε out cancel
      have hout : (∑ x, (f v x + (if v = s ∧ x = w then ε else 0) + (if v = w ∧ x = t then ε else 0)))
          = (∑ x, f v x) + ε := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have e1 : (∑ x, (if v = s ∧ x = w then ε else 0)) = 0 := by
          apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨h, _⟩; exact hvs h
        have e2 : (∑ x, (if v = w ∧ x = t then ε else 0)) = ε := by
          have hcong : ∀ x, (if v = w ∧ x = t then ε else 0) = (if x = t then ε else 0) :=
            fun x => by simp [hvw]
          rw [Finset.sum_congr rfl (fun x _ => hcong x), Finset.sum_ite_eq']; simp
        rw [e1, e2, add_zero]
      have hin : (∑ x, (f x v + (if x = s ∧ v = w then ε else 0) + (if x = w ∧ v = t then ε else 0)))
          = (∑ x, f x v) + ε := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have e3 : (∑ x, (if x = s ∧ v = w then ε else 0)) = ε := by
          have hcong : ∀ x, (if x = s ∧ v = w then ε else 0) = (if x = s then ε else 0) :=
            fun x => by simp [hvw]
          rw [Finset.sum_congr rfl (fun x _ => hcong x), Finset.sum_ite_eq']; simp
        have e4 : (∑ x, (if x = w ∧ v = t then ε else 0)) = 0 := by
          apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨_, h⟩; exact hvt h
        rw [e3, e4, add_zero]
      rw [hout, hin]
      have := hf.conserve v hvs hvt
      unfold vertexExcess at this
      linarith
    · -- any other interior vertex: all four modifications vanish
      have hout : (∑ x, (f v x + (if v = s ∧ x = w then ε else 0) + (if v = w ∧ x = t then ε else 0)))
          = (∑ x, f v x) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have e1 : (∑ x, (if v = s ∧ x = w then ε else 0)) = 0 := by
          apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨h, _⟩; exact hvs h
        have e2 : (∑ x, (if v = w ∧ x = t then ε else 0)) = 0 := by
          apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨h, _⟩; exact hvw h
        rw [e1, e2, add_zero, add_zero]
      have hin : (∑ x, (f x v + (if x = s ∧ v = w then ε else 0) + (if x = w ∧ v = t then ε else 0)))
          = (∑ x, f x v) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have e3 : (∑ x, (if x = s ∧ v = w then ε else 0)) = 0 := by
          apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨_, h⟩; exact hvw h
        have e4 : (∑ x, (if x = w ∧ v = t then ε else 0)) = 0 := by
          apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨_, h⟩; exact hvt h
        rw [e3, e4, add_zero, add_zero]
      rw [hout, hin]
      have := hf.conserve v hvs hvt
      unfold vertexExcess at this
      linarith
  · -- value strictly increases by ε
    unfold flowValue vertexExcess
    have hout : (∑ x, (f s x + (if s = s ∧ x = w then ε else 0) + (if s = w ∧ x = t then ε else 0)))
        = (∑ x, f s x) + ε := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have e1 : (∑ x, (if s = s ∧ x = w then ε else 0)) = ε := by
        have hcong : ∀ x, (if s = s ∧ x = w then ε else 0) = (if x = w then ε else 0) :=
          fun x => by simp
        rw [Finset.sum_congr rfl (fun x _ => hcong x), Finset.sum_ite_eq']; simp
      have e2 : (∑ x, (if s = w ∧ x = t then ε else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨h, _⟩; exact hsw' h
      rw [e1, e2, add_zero]
    have hin : (∑ x, (f x s + (if x = s ∧ s = w then ε else 0) + (if x = w ∧ s = t then ε else 0)))
        = (∑ x, f x s) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have e3 : (∑ x, (if x = s ∧ s = w then ε else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨_, h⟩; exact hsw' h
      have e4 : (∑ x, (if x = w ∧ s = t then ε else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨_, h⟩; exact hst h
      rw [e3, e4, add_zero, add_zero]
    rw [hout, hin]
    linarith

/-- **M7 — a forward simple augmenting `s`-`t` path, as a degree-structured directed edge set.**
`P` is the directed-edge relation of a simple forward augmenting path; its *degree structure* is that of a
simple `s`-`t` path: every interior vertex has out-degree equal to in-degree (`hDeg`), the source has one
more out-edge than in-edge (`hs`), the sink one more in-edge than out-edge (`ht`), and every path edge
carries forward residual slack (`hslack`). This packages exactly the combinatorial data an augmenting
forward path contributes, WITHOUT committing to a `List`/`ReflTransGen` walk representation — the
degree conditions are all the conservation argument needs. -/
structure ForwardAugPath (cap : V → V → ℝ) (s t : V) (f : V → V → ℝ) where
  /-- The directed edges of the path. -/
  P : V → V → Prop
  /-- Interior vertices: out-degree = in-degree. -/
  hDeg : ∀ u, u ≠ s → u ≠ t →
    (Finset.univ.filter (fun v => P u v)).card = (Finset.univ.filter (fun v => P v u)).card
  /-- The source has exactly one more out-edge than in-edge. -/
  hs : (Finset.univ.filter (fun v => P s v)).card = (Finset.univ.filter (fun v => P v s)).card + 1
  /-- The sink has exactly one more in-edge than out-edge. -/
  ht : (Finset.univ.filter (fun v => P t v)).card + 1 = (Finset.univ.filter (fun v => P v t)).card
  /-- Every path edge has forward residual slack. -/
  hslack : ∀ u v, P u v → f u v < cap u v

/-- **★★ M7 — the general forward simple-path augmentation.** Given a forward simple augmenting path
`Q : ForwardAugPath cap s t f` (a degree-structured directed edge set) and a uniform positive slack
margin `ε` (`f u v + ε ≤ cap u v` on every path edge), the flow
`g u v := f u v + (if Q.P u v then ε else 0)` is a valid `s`-`t` flow of strictly larger value.

This DERIVES the augmentation MECHANISM for an arbitrary forward simple path — the full
conservation-via-degree-structure argument — not just the one- and two-edge special cases of M6. The
crux is the clean Finset computation
`∑ v, (if Q.P u v then ε else 0) = ε · (filter (Q.P u ·) univ).card`, turning `vertexExcess g u =
vertexExcess f u + ε·(outDeg u − inDeg u)`; interior vertices then conserve by `hDeg` (out = in), and
the value rises by `ε·1` at the source by `hs`.

**Carried (frontier, NOT here):** that residual reachability (`ReflTransGen`) actually PRODUCES such a
`ForwardAugPath` (the walk→simple-forward-path extraction with this degree structure), mixed
forward/backward (residual reverse-edge) paths, and max-flow EXISTENCE. **Derived here:** the entire
augmentation given a forward simple path presented as a degree-structured edge set with a uniform slack
margin — the general-length generalization of M6's hand-built 1- and 2-edge cases. -/
theorem forwardAugPath_augments {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (Q : ForwardAugPath cap s t f) (hst : s ≠ t)
    (ε : ℝ) (hε : 0 < ε) (hεcap : ∀ u v, Q.P u v → f u v + ε ≤ cap u v) :
    ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s := by
  classical
  -- the load-bearing helper: `∑ v, (if R v then ε else 0) = ε · card{v | R v}`.
  have hsum : ∀ (R : V → Prop),
      (∑ v, (if R v then ε else 0)) = ε * ((Finset.univ.filter R).card : ℝ) := by
    intro R
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have he0 : (0:ℝ) ≤ ε := le_of_lt hε
  refine ⟨fun u v => f u v + (if Q.P u v then ε else 0), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- nonneg
    intro u v
    have := hf.nonneg u v
    split <;> linarith
  · -- capacity
    intro u v
    by_cases h : Q.P u v
    · rw [if_pos h]; exact hεcap u v h
    · rw [if_neg h, add_zero]; exact hf.capacity u v
  · -- conserve at an interior vertex: degree structure cancels the ε-terms
    intro u hus hut
    unfold vertexExcess
    have hout : (∑ v, (f u v + if Q.P u v then ε else 0))
        = (∑ v, f u v) + ε * ((Finset.univ.filter (fun v => Q.P u v)).card : ℝ) := by
      rw [Finset.sum_add_distrib, hsum (fun v => Q.P u v)]
    have hin : (∑ v, (f v u + if Q.P v u then ε else 0))
        = (∑ v, f v u) + ε * ((Finset.univ.filter (fun v => Q.P v u)).card : ℝ) := by
      rw [Finset.sum_add_distrib, hsum (fun v => Q.P v u)]
    rw [hout, hin, Q.hDeg u hus hut]
    have hconv := hf.conserve u hus hut
    unfold vertexExcess at hconv
    linarith
  · -- value strictly increases by ε at the source (hs: outDeg s = inDeg s + 1)
    unfold flowValue vertexExcess
    have hout : (∑ v, (f s v + if Q.P s v then ε else 0))
        = (∑ v, f s v) + ε * ((Finset.univ.filter (fun v => Q.P s v)).card : ℝ) := by
      rw [Finset.sum_add_distrib, hsum (fun v => Q.P s v)]
    have hin : (∑ v, (f v s + if Q.P v s then ε else 0))
        = (∑ v, f v s) + ε * ((Finset.univ.filter (fun v => Q.P v s)).card : ℝ) := by
      rw [Finset.sum_add_distrib, hsum (fun v => Q.P v s)]
    rw [hout, hin, Q.hs]
    push_cast
    linarith

/-! ### M8 — the extraction: a simple forward path yields a `ForwardAugPath`

M7 proved the augmentation MECHANISM given a `ForwardAugPath` (a degree-structured directed edge set).
M8 discharges the *extraction* of that degree structure: from a **simple** (de-duplicated) forward
residual path — carried here as an injective `Fin`-indexed vertex sequence with forward slack on every
step (`SimpleForwardPath`) — we DERIVE the full `ForwardAugPath` degree structure (interior in/out
balance, source `+1` out, sink `+1` in) by exact fibre counting. We then eliminate the uniform slack
margin `ε` (`forwardAugPath_augments'`) and compose (`augment_of_simpleForwardPath`), so a simple
forward path alone augments the flow.

**Derived here (machine-checked):** the entire degree-structure extraction (nodup/injective vertex
sequence ⟹ the `hDeg`/`hs`/`ht` degree conditions), via `card {v | edge u v} = card {i | source i = u}`
and "card of an injective fibre is `0`/`1`". Plus the internal derivation of `ε` (min forward slack over
the finite path-edge set is positive).

**Still carried (the one remaining piece of M7's carry (a)):** the *directed dedup* — that a residual
`Relation.ReflTransGen (ForwardResidualStep cap f)` walk produces a `SimpleForwardPath` (removing
repeated vertices from a directed walk while preserving endpoints and per-step forward slack). This is
the directed analogue of `SimpleGraph.Walk.bypass`; Mathlib's `bypass`/`toPath` live on *undirected*
`SimpleGraph` (`fromRel` symmetrises, so a walk edge only gives `r u v ∨ r v u`, not the forward
direction we need), so the directed dedup is not available off the shelf. -/

/-- **M8 — a forward residual step:** the forward edge `u→v` has unused capacity. Unlike the mixed
`ResidualStep` (M2), this is forward-only — the natural edge relation for a forward augmenting path. -/
def ForwardResidualStep (cap f : V → V → ℝ) (u v : V) : Prop :=
  f u v < cap u v

/-- **M8 — a simple forward augmenting path**, carried as an *injective* `Fin (n+1)`-indexed vertex
sequence `p` from `s` (`p 0`) to `t` (`p (last n)`), `n ≥ 1`, with a forward residual step on every
consecutive pair. Injectivity encodes that the path is simple (no repeated vertex) — this is the
de-duplicated data from which the degree structure of a `ForwardAugPath` is extracted. -/
structure SimpleForwardPath (cap : V → V → ℝ) (s t : V) (f : V → V → ℝ) where
  /-- Number of edges (so `n+1` vertices); at least one edge. -/
  n : ℕ
  /-- The path has at least one edge. -/
  hn : 1 ≤ n
  /-- The vertex sequence. -/
  p : Fin (n + 1) → V
  /-- Simplicity: the vertex sequence has no repeats. -/
  hp_inj : Function.Injective p
  /-- The first vertex is the source. -/
  hp0 : p 0 = s
  /-- The last vertex is the sink. -/
  hplast : p (Fin.last n) = t
  /-- Every consecutive pair is a forward residual step (forward slack). -/
  hstep : ∀ i : Fin n, ForwardResidualStep cap f (p i.castSucc) (p i.succ)

/-- The directed edge relation of a `SimpleForwardPath`: `u→v` is an edge iff some consecutive pair of
the vertex sequence is `(u, v)`. -/
def SimpleForwardPath.edge {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (SP : SimpleForwardPath cap s t f) (u v : V) : Prop :=
  ∃ i : Fin SP.n, SP.p i.castSucc = u ∧ SP.p i.succ = v

/-- **M8 helper — the card of an injective fibre is `0` or `1`.** For an injective `q : Fin n → W`, the
number of indices mapping to `u` is `1` if `u` is hit and `0` otherwise. This is the arithmetic heart of
the degree extraction: a simple path visits each vertex once, so each vertex has at most one out-edge and
one in-edge. -/
theorem card_filter_fiber_of_injective {n : ℕ} {W : Type*} [DecidableEq W]
    (q : Fin n → W) (hq : Function.Injective q) (u : W) :
    (Finset.univ.filter (fun i => q i = u)).card = if (∃ i, q i = u) then 1 else 0 := by
  classical
  by_cases h : ∃ i, q i = u
  · obtain ⟨i0, hi0⟩ := h
    rw [if_pos ⟨i0, hi0⟩, Finset.card_eq_one]
    refine ⟨i0, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hi => hq (hi.trans hi0.symm), fun hi => hi ▸ hi0⟩
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ hi => h ⟨i, hi⟩

/-- **★★ M8 — the degree-structure extraction.** A `SimpleForwardPath` yields a `ForwardAugPath`: the
degree conditions (`hDeg`/`hs`/`ht`) are DERIVED from injectivity of the vertex sequence by exact fibre
counting, and forward slack (`hslack`) is exactly the per-step hypothesis. This discharges the
walk→degree-structure part of M7's carried extraction; only the directed dedup (residual walk →
`SimpleForwardPath`) remains carried. -/
def SimpleForwardPath.toForwardAugPath {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (SP : SimpleForwardPath cap s t f) : ForwardAugPath cap s t f := by
  classical
  haveI : NeZero SP.n := ⟨by have := SP.hn; omega⟩
  have hcs_inj : Function.Injective (fun i : Fin SP.n => SP.p i.castSucc) :=
    SP.hp_inj.comp (Fin.castSucc_injective SP.n)
  have hsucc_inj : Function.Injective (fun i : Fin SP.n => SP.p i.succ) :=
    SP.hp_inj.comp (Fin.succ_injective SP.n)
  -- out-degree of `u` = number of edge-sources equal to `u`
  have outdeg_eq : ∀ u, (Finset.univ.filter (fun v => SP.edge u v)).card
      = if (∃ i : Fin SP.n, SP.p i.castSucc = u) then 1 else 0 := by
    intro u
    have himg : Finset.univ.filter (fun v => SP.edge u v)
        = (Finset.univ.filter (fun i : Fin SP.n => SP.p i.castSucc = u)).image
            (fun i : Fin SP.n => SP.p i.succ) := by
      ext v
      simp only [SimpleForwardPath.edge, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]
    rw [himg, Finset.card_image_of_injective _ hsucc_inj,
      card_filter_fiber_of_injective _ hcs_inj u]
  -- in-degree of `u` = number of edge-targets equal to `u`
  have indeg_eq : ∀ u, (Finset.univ.filter (fun v => SP.edge v u)).card
      = if (∃ i : Fin SP.n, SP.p i.succ = u) then 1 else 0 := by
    intro u
    have himg : Finset.univ.filter (fun v => SP.edge v u)
        = (Finset.univ.filter (fun i : Fin SP.n => SP.p i.succ = u)).image
            (fun i : Fin SP.n => SP.p i.castSucc) := by
      ext v
      simp only [SimpleForwardPath.edge, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · rintro ⟨i, h1, h2⟩; exact ⟨i, h2, h1⟩
      · rintro ⟨i, h1, h2⟩; exact ⟨i, h2, h1⟩
    rw [himg, Finset.card_image_of_injective _ hcs_inj,
      card_filter_fiber_of_injective _ hsucc_inj u]
  exact {
    P := SP.edge
    hDeg := by
      intro u hus hut
      rw [outdeg_eq u, indeg_eq u]
      have hiff : (∃ i : Fin SP.n, SP.p i.castSucc = u) ↔ (∃ i : Fin SP.n, SP.p i.succ = u) := by
        have cs : (∃ i : Fin SP.n, SP.p i.castSucc = u)
            ↔ (∃ j : Fin (SP.n + 1), j ≠ Fin.last SP.n ∧ SP.p j = u) := by
          constructor
          · rintro ⟨i, rfl⟩; exact ⟨i.castSucc, Fin.castSucc_ne_last i, rfl⟩
          · rintro ⟨j, hj, rfl⟩; exact ⟨j.castPred hj, by rw [Fin.castSucc_castPred]⟩
        have sc : (∃ i : Fin SP.n, SP.p i.succ = u)
            ↔ (∃ j : Fin (SP.n + 1), j ≠ 0 ∧ SP.p j = u) := by
          constructor
          · rintro ⟨i, rfl⟩; exact ⟨i.succ, Fin.succ_ne_zero i, rfl⟩
          · rintro ⟨j, hj, rfl⟩; exact ⟨j.pred hj, by rw [Fin.succ_pred]⟩
        rw [cs, sc]
        constructor
        · rintro ⟨j, _, rfl⟩
          exact ⟨j, fun hj0 => hus (by rw [hj0, SP.hp0]), rfl⟩
        · rintro ⟨j, _, rfl⟩
          exact ⟨j, fun hjl => hut (by rw [hjl, SP.hplast]), rfl⟩
      simp only [hiff]
    hs := by
      have hex : ∃ i : Fin SP.n, SP.p i.castSucc = s := ⟨0, by rw [Fin.castSucc_zero', SP.hp0]⟩
      have hnex : ¬ ∃ i : Fin SP.n, SP.p i.succ = s := by
        rintro ⟨i, hi⟩; exact Fin.succ_ne_zero i (SP.hp_inj (hi.trans SP.hp0.symm))
      rw [outdeg_eq s, indeg_eq s, if_pos hex, if_neg hnex]
    ht := by
      have hnex : ¬ ∃ i : Fin SP.n, SP.p i.castSucc = t := by
        rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i (SP.hp_inj (hi.trans SP.hplast.symm))
      have hex : ∃ i : Fin SP.n, SP.p i.succ = t := by
        have hidx : (⟨SP.n - 1, by have := SP.hn; omega⟩ : Fin SP.n).succ = Fin.last SP.n := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_last]
          have := SP.hn; omega
        exact ⟨⟨SP.n - 1, by have := SP.hn; omega⟩, by rw [hidx]; exact SP.hplast⟩
      rw [outdeg_eq t, indeg_eq t, if_neg hnex, if_pos hex]
    hslack := by
      rintro u v ⟨i, rfl, rfl⟩
      exact SP.hstep i
  }

/-- **★ M8 — the general forward augmentation with `ε` eliminated.** Given only a `ForwardAugPath`
(no externally supplied slack margin), the flow augments: the min forward slack over the finite,
nonempty path-edge set is a positive `ε` satisfying `f + ε ≤ cap` on every edge, feeding
`forwardAugPath_augments`. This removes the uniform-margin hypothesis of M7. -/
theorem forwardAugPath_augments' {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (Q : ForwardAugPath cap s t f) (hst : s ≠ t) :
    ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s := by
  classical
  -- the source has an out-edge (by `Q.hs`), so the path-edge set is nonempty
  have hsrc : (Finset.univ.filter (fun v => Q.P s v)).Nonempty := by
    rw [← Finset.card_pos]; have := Q.hs; omega
  obtain ⟨v0, hv0⟩ := hsrc
  rw [Finset.mem_filter] at hv0
  set E : Finset (V × V) := Finset.univ.filter (fun p : V × V => Q.P p.1 p.2) with hE
  have hEne : E.Nonempty :=
    ⟨(s, v0), by rw [hE, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hv0.2⟩⟩
  set ε : ℝ := E.inf' hEne (fun p => cap p.1 p.2 - f p.1 p.2) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef, Finset.lt_inf'_iff]
    intro p hp
    rw [hE, Finset.mem_filter] at hp
    have := Q.hslack p.1 p.2 hp.2
    linarith
  have hεcap : ∀ u w, Q.P u w → f u w + ε ≤ cap u w := by
    intro u w huw
    have hmem : (u, w) ∈ E := by rw [hE, Finset.mem_filter]; exact ⟨Finset.mem_univ _, huw⟩
    have hle : ε ≤ cap u w - f u w := Finset.inf'_le (fun p => cap p.1 p.2 - f p.1 p.2) hmem
    linarith
  exact forwardAugPath_augments hf Q hst ε hεpos hεcap

/-- **★★ M8 — the extraction capstone: a simple forward path augments the flow.** Composing the degree
extraction (`SimpleForwardPath.toForwardAugPath`) with the `ε`-eliminated augmentation
(`forwardAugPath_augments'`): from a simple forward residual path `s ⇝ t` alone, one builds a strictly
larger `s`-`t` flow. `s ≠ t` is itself derived from injectivity (`p 0 = s ≠ t = p (last n)`). This is the
walk→augmentation pipeline modulo only the directed dedup (residual walk → `SimpleForwardPath`). -/
theorem augment_of_simpleForwardPath {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (SP : SimpleForwardPath cap s t f) :
    ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s := by
  have hst : s ≠ t := by
    intro h
    have h0 : (0 : Fin (SP.n + 1)) = Fin.last SP.n :=
      SP.hp_inj (SP.hp0.trans (h.trans SP.hplast.symm))
    have := SP.hn
    rw [Fin.ext_iff, Fin.val_zero, Fin.val_last] at h0
    omega
  exact forwardAugPath_augments' hf SP.toForwardAugPath hst

/-! ### M9 — the directed dedup: residual reachability yields a `SimpleForwardPath`

M8 left CARRIED exactly one piece: the *directed dedup* — that a residual
`Relation.ReflTransGen (ForwardResidualStep cap f)` walk `s ⇝ t` produces a **simple** forward path
(`SimpleForwardPath`), i.e. an injective vertex sequence. M9 DISCHARGES it, the genuine hard graph-theory
core (no Mathlib support: `SimpleGraph.Walk.bypass`/`toPath` are *undirected*, `fromRel` symmetrises).

The construction is the "shortest forward walk is simple" argument, done constructively:

* **`exists_isChain_list`** — `ReflTransGen r s t` yields a `List V` `w` with `w.IsChain r`,
  `w.head? = some s`, `w.getLast? = some t` (built by `head_induction_on`, prepending each residual edge).
* **`dedup_aux` / `exists_nodup_isChain_list`** — the **splice-shortens** crux: by strong induction on a
  length bound, any such chain list is replaced by a `Nodup` one. If `w` is not `Nodup`, injectivity of
  `w.get` fails, giving indices `a < b` with `w[a] = w[b]`; the splice `w.take (a+1) ++ w.drop (b+1)`
  is a strictly shorter chain list with the same endpoints (the rejoin edge `w[a] = w[b] → w[b+1]` is a
  step of the original chain), and the induction hypothesis simplifies it.
* **`simpleForwardPath_of_reachable`** — the **capstone**: convert the `Nodup` chain list to a
  `SimpleForwardPath` (`List` → injective `Fin (n+1) → V` via `w.get ∘ Fin.cast`; `Nodup ⟹ injective`,
  `IsChain ⟹ hstep`, `head?`/`getLast? ⟹ hp0`/`hplast`; `s ≠ t` forces length `≥ 2` so `n ≥ 1`).

Composed with M8's `augment_of_simpleForwardPath`, forward residual reachability `s ⇝ t` alone now yields
a strictly larger flow — the forward augmenting path `haug` is fully derived from reachability. What stays
CARRIED for the full Ford–Fulkerson `haug` is only (b) mixed forward/backward (residual reverse-edge)
paths and (c) max-flow EXISTENCE; the forward directed-dedup carry (a′) is discharged. -/

section DirectedDedup
open List
set_option linter.unusedSectionVars false

/-- **M9 (Step 1).** A `Relation.ReflTransGen r` chain `s ⇝ t` is witnessed by a `List V` that
`IsChain r`, starts at `s` (`head?`) and ends at `t` (`getLast?`). Built by induction on the chain,
prepending the source of each residual step. -/
theorem exists_isChain_list {W : Type*} {r : W → W → Prop} {s t : W}
    (h : Relation.ReflTransGen r s t) :
    ∃ w : List W, w.IsChain r ∧ w.head? = some s ∧ w.getLast? = some t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[t], isChain_singleton t, rfl, rfl⟩
  | @head a c h' hct ih =>
    obtain ⟨w, hchain, hhead, hlast⟩ := ih
    have hwne : w ≠ [] := by intro hw; rw [hw] at hhead; simp at hhead
    refine ⟨a :: w, ?_, rfl, ?_⟩
    · rw [isChain_cons]; refine ⟨?_, hchain⟩
      intro y hy; rw [hhead] at hy
      simp only [Option.mem_def, Option.some.injEq] at hy; subst hy; exact h'
    · rw [getLast?_cons_of_ne_nil hwne]; exact hlast

/-- **M9 (Step 2) — the splice-shortens crux.** By strong induction on a length bound `N`, every
`IsChain r` list from `s` to `t` is replaced by a `Nodup` one with the same endpoints. If the list is
not `Nodup`, `w.get` is not injective, giving indices `a < b` with `w[a] = w[b]`; the splice
`w.take (a+1) ++ w.drop (b+1)` is a strictly shorter `IsChain r` list from `s` to `t` — the rejoin edge
holds because `w[a] = w[b]` and `r w[b] w[b+1]` is a step of the original chain — so the induction
hypothesis applies. -/
theorem dedup_aux {W : Type*} {r : W → W → Prop} {s t : W} :
    ∀ (N : ℕ) (w : List W), w.length ≤ N → w.IsChain r → w.head? = some s →
      w.getLast? = some t →
      ∃ w' : List W, w'.IsChain r ∧ w'.head? = some s ∧ w'.getLast? = some t ∧ w'.Nodup := by
  intro N
  induction N with
  | zero =>
    intro w hlen _ hh _
    rcases w with _ | ⟨x, xs⟩
    · simp at hh
    · simp at hlen
  | succ N ih =>
    intro w hlen hc hh hl
    by_cases hnd : w.Nodup
    · exact ⟨w, hc, hh, hl, hnd⟩
    · rw [List.nodup_iff_injective_get, Function.not_injective_iff] at hnd
      obtain ⟨i, j, hEq, hne⟩ := hnd
      have hvne : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
      obtain ⟨a, b, hab, ha, hb, hwEq?⟩ :
          ∃ a b : ℕ, a < b ∧ a < w.length ∧ b < w.length ∧ w[a]? = w[b]? := by
        rcases lt_or_gt_of_ne hvne with h | h
        · exact ⟨i, j, h, i.2, j.2, by
            rw [getElem?_eq_getElem i.2, getElem?_eq_getElem j.2]
            simpa [List.get_eq_getElem] using hEq⟩
        · exact ⟨j, i, h, j.2, i.2, by
            rw [getElem?_eq_getElem j.2, getElem?_eq_getElem i.2]
            simpa [List.get_eq_getElem] using hEq.symm⟩
      have hwEq : w[a] = w[b] := by
        rw [getElem?_eq_getElem ha, getElem?_eq_getElem hb] at hwEq?
        simpa using hwEq?
      set w' := w.take (a+1) ++ w.drop (b+1) with hw'
      have hlen' : w'.length ≤ N := by
        have h1 : (w.take (a+1)).length = a + 1 := by rw [length_take]; omega
        have h2 : (w.drop (b+1)).length = w.length - (b+1) := length_drop
        rw [hw', length_append, h1, h2]; omega
      have htne : w.take (a+1) ≠ [] := by
        rw [Ne, take_eq_nil_iff]
        rintro (h | h)
        · omega
        · rw [h] at ha; simp at ha
      have hlastTake : (w.take (a+1)).getLast? = some w[a] := by
        rw [getLast?_take, if_neg (Nat.add_one_ne_zero a)]
        simp only [Nat.add_sub_cancel]; rw [getElem?_eq_getElem ha]; simp
      have hcTake : (w.take (a+1)).IsChain r := by
        have : (w.take (a+1) ++ w.drop (a+1)).IsChain r := by rw [take_append_drop]; exact hc
        exact (isChain_append.mp this).1
      have hcDrop : (w.drop (b+1)).IsChain r := by
        have : (w.take (b+1) ++ w.drop (b+1)).IsChain r := by rw [take_append_drop]; exact hc
        exact (isChain_append.mp this).2.1
      have hjun : ∀ x ∈ (w.take (a+1)).getLast?, ∀ y ∈ (w.drop (b+1)).head?, r x y := by
        intro x hx y hy
        rw [hlastTake] at hx
        simp only [Option.mem_def, Option.some.injEq] at hx; subst hx
        rw [head?_drop, Option.mem_def, List.getElem?_eq_some_iff] at hy
        obtain ⟨hb1, hyEq⟩ := hy; subst hyEq
        have hstep : r w[b] w[b+1] := isChain_iff_getElem.mp hc b hb1
        rw [hwEq]; exact hstep
      have hc' : w'.IsChain r := by rw [hw']; exact IsChain.append hcTake hcDrop hjun
      have hh' : w'.head? = some s := by
        rw [hw', head?_append, head?_take, if_neg (Nat.add_one_ne_zero a), hh]; simp
      have hl' : w'.getLast? = some t := by
        rw [hw', getLast?_append, getLast?_drop, hlastTake]
        by_cases hcase : w.length ≤ b + 1
        · rw [if_pos hcase, Option.none_or]
          have hbeq : b = w.length - 1 := by omega
          have hval : w[b] = t := by
            have e1 : w[b]? = some t := by rw [hbeq, ← getLast?_eq_getElem?]; exact hl
            rw [getElem?_eq_getElem hb] at e1; simpa using e1
          rw [hwEq, hval]
        · rw [if_neg hcase, hl]; simp
      exact ih w' hlen' hc' hh' hl'

/-- **M9 (Step 2, packaged).** Residual reachability `s ⇝ t` is witnessed by a `Nodup` `IsChain r` list
from `s` to `t`. -/
theorem exists_nodup_isChain_list {W : Type*} {r : W → W → Prop} {s t : W}
    (h : Relation.ReflTransGen r s t) :
    ∃ w : List W, w.IsChain r ∧ w.head? = some s ∧ w.getLast? = some t ∧ w.Nodup := by
  obtain ⟨w, hc, hh, hl⟩ := exists_isChain_list h
  exact dedup_aux w.length w le_rfl hc hh hl

/-- **★★ M9 — the directed dedup capstone.** Forward residual reachability `s ⇝ t`
(`Relation.ReflTransGen (ForwardResidualStep cap f) s t`) with `s ≠ t` yields a `SimpleForwardPath`: a
`Nodup` forward-chain `List` witnessing reachability is converted to the injective `Fin (n+1)`-indexed
vertex sequence (`w.get ∘ Fin.cast`; `Nodup ⟹ injective`, `IsChain ⟹ hstep`, endpoints ⟹ `hp0`/`hplast`;
`s ≠ t` forces length `≥ 2`, hence `n ≥ 1`). This DISCHARGES M8's lone carried piece — the directed
analogue of `SimpleGraph.Walk.bypass`, unavailable off the shelf. Composed with
`augment_of_simpleForwardPath`, forward reachability alone augments the flow. -/
theorem simpleForwardPath_of_reachable {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (hst : s ≠ t)
    (hreach : Relation.ReflTransGen (ForwardResidualStep cap f) s t) :
    Nonempty (SimpleForwardPath cap s t f) := by
  obtain ⟨w, hc, hh, hl, hnd⟩ := exists_nodup_isChain_list hreach
  have hwne : w ≠ [] := by rintro rfl; simp at hh
  have hlen1 : 1 ≤ w.length := List.length_pos_iff_ne_nil.mpr hwne
  have h0 : w[0]'(by omega) = s := by
    have e : w[0]? = some s := by rw [← head?_eq_getElem?]; exact hh
    rw [getElem?_eq_getElem (by omega)] at e; simpa using e
  have hL : w[w.length - 1]'(by omega) = t := by
    have e : w[w.length - 1]? = some t := by rw [← getLast?_eq_getElem?]; exact hl
    rw [getElem?_eq_getElem (by omega)] at e; simpa using e
  have hlen2 : 2 ≤ w.length := by
    rcases Nat.lt_or_ge w.length 2 with h | h
    · exfalso; apply hst
      have hone : w.length = 1 := by omega
      have e0 : w[0]? = some s := by rw [← head?_eq_getElem?]; exact hh
      have eL : w[0]? = some t := by
        have := hl; rw [getLast?_eq_getElem?, hone] at this; simpa using this
      rw [e0] at eL; exact Option.some.injEq _ _ |>.mp eL
    · exact h
  have hN' : w.length - 1 + 1 = w.length := by omega
  refine ⟨{
    n := w.length - 1
    hn := by omega
    p := fun i => w.get (Fin.cast hN' i)
    hp_inj := by
      intro x y hxy
      simp only [List.get_eq_getElem] at hxy
      exact Fin.cast_injective hN'
        ((List.nodup_iff_injective_get.mp hnd) (by simpa [List.get_eq_getElem] using hxy))
    hp0 := by
      simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_zero]; exact h0
    hplast := by
      simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_last]; exact hL
    hstep := by
      intro i
      have hi1 : (i : ℕ) + 1 < w.length := by have := i.2; omega
      have hstep := isChain_iff_getElem.mp hc i.val hi1
      show ForwardResidualStep cap f (w.get (Fin.cast hN' i.castSucc)) (w.get (Fin.cast hN' i.succ))
      simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_castSucc, Fin.val_succ]
      exact hstep
  }⟩

/-- **★ M9 CAPSTONE — the forward augmenting-path lemma, DERIVED.** Forward residual
reachability from `s` to `t` (with `s ≠ t`) yields a strictly larger flow — the forward case
of Ford–Fulkerson's `haug`, now fully machine-checked (no carried augmentation): the directed
dedup (`simpleForwardPath_of_reachable`) produces a simple forward path, and its augmentation
(`augment_of_simpleForwardPath`) strictly increases the flow value. Only mixed
forward/backward residual paths and max-flow existence remain carried. -/
theorem forwardReachable_augments {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (hst : s ≠ t)
    (hreach : Relation.ReflTransGen (ForwardResidualStep cap f) s t) :
    ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s := by
  obtain ⟨SP⟩ := simpleForwardPath_of_reachable hf hst hreach
  exact augment_of_simpleForwardPath hf SP

end DirectedDedup

/-! ### M10 — the mixed-direction augmentation (general Ford–Fulkerson residual path)

M7 handled a FORWARD-only degree-structured path. M10 handles the general residual augmenting path,
which carries a per-step DIRECTION: a step out of a vertex is either a *forward* residual edge (unused
capacity, `cap − f`) or a *backward* residual edge (cancelling real flow, `f` on the reverse edge). We
package the path as two typed directed-edge relations `Pf` (forward) and `Pb` (backward), with the
COMBINED residual degree structure. The augmented flow is
`g u v := f u v + (if Pf u v then ε) − (if Pb v u then ε)`: a forward edge `u→v` adds `ε` to `f u v`;
a backward residual edge `Pb v u` (which reverses the real edge `u→v`) subtracts `ε` from `f u v`.

The conservation crux is the sign bookkeeping: at any vertex `w`,
`vertexExcess g w = vertexExcess f w + ε·[(Pf-out + Pb-out) − (Pf-in + Pb-in)]`, using the
`∑ (if R then ε) = ε·card` helper FOUR times. The Pb terms land on the *opposite* out/in slot of the
excess (a `Pb w v` edge, cancelling real `v→w`, reduces `f v w` — an INCOMING quantity to `w` — hence
appears in `w`'s in-sum with a minus, i.e. contributes `+ε` to out-minus-in), so an OUTGOING residual
step contributes `+ε` and an INCOMING one `−ε` REGARDLESS of type. The combined degree structure
(`hDeg`) makes the bracket vanish at interior vertices; `hs` makes it `+1` at the source. -/

/-- **M10 — a mixed residual augmenting `s`-`t` path**, as two typed directed-edge relations. `Pf` are
forward residual edges `u→v` (forward slack `cap u v − f u v`); `Pb` are backward residual edges `u→v`
(they cancel the real edge `v→u`, whose flow `f v u > 0`). The *combined residual degree* — counting
`Pf`- and `Pb`-edges together — is that of a simple `s`-`t` path: interior out = in (`hDeg`), source
`+1` out (`hs`), sink `+1` in (`ht`). `hfslack`/`hbpos` record residual admissibility. This is the
mixed-direction generalization of `ForwardAugPath` (which is the `Pb = ∅` special case). -/
structure ResidualAugPath (cap : V → V → ℝ) (s t : V) (f : V → V → ℝ) where
  /-- Forward residual edges (unused capacity). -/
  Pf : V → V → Prop
  /-- Backward residual edges (cancel real flow on the reverse edge). -/
  Pb : V → V → Prop
  /-- Interior vertices: combined (forward + backward) out-degree = in-degree. -/
  hDeg : ∀ w, w ≠ s → w ≠ t →
    (Finset.univ.filter (fun v => Pf w v)).card + (Finset.univ.filter (fun v => Pb w v)).card
      = (Finset.univ.filter (fun u => Pf u w)).card + (Finset.univ.filter (fun u => Pb u w)).card
  /-- The source has one more combined out-edge than in-edge. -/
  hs : (Finset.univ.filter (fun v => Pf s v)).card + (Finset.univ.filter (fun v => Pb s v)).card
      = (Finset.univ.filter (fun u => Pf u s)).card + (Finset.univ.filter (fun u => Pb u s)).card + 1
  /-- The sink has one more combined in-edge than out-edge. -/
  ht : (Finset.univ.filter (fun v => Pf t v)).card + (Finset.univ.filter (fun v => Pb t v)).card + 1
      = (Finset.univ.filter (fun u => Pf u t)).card + (Finset.univ.filter (fun u => Pb u t)).card
  /-- Every forward edge has forward residual slack. -/
  hfslack : ∀ u v, Pf u v → f u v < cap u v
  /-- Every backward edge cancels a positively-loaded real edge. -/
  hbpos : ∀ u v, Pb u v → 0 < f v u

/-- **★★ M10 — the general mixed-direction augmentation.** Given a mixed residual augmenting path
`Q : ResidualAugPath cap s t f` and a uniform positive margin `ε` with `f u v + ε ≤ cap u v` on every
forward edge (`hfcap`) and `ε ≤ f v u` on every backward edge (`hbε`, so cancellation stays
nonnegative), the flow `g u v := f u v + (if Q.Pf u v then ε) − (if Q.Pb v u then ε)` is a valid `s`-`t`
flow of strictly larger value.

This is the augmentation MECHANISM for an ARBITRARY residual path with forward AND backward edges — the
augmentation half of general Ford–Fulkerson, generalizing M7's forward-only `forwardAugPath_augments`
(the `Q.Pb = ∅` case). Nonnegativity uses `hbε` (a cancelled edge keeps `f u v ≥ ε`); capacity uses
`hfcap` (forward edges) and the fact that backward cancellation only decreases `f`; conservation uses
the combined degree structure `hDeg` with the four-fold `∑ (if R then ε) = ε·card` identity, the Pb
terms flipping which out/in slot they hit so an outgoing step is always `+ε` and an incoming step `−ε`;
the value rises by `ε` at the source by `hs`. -/
theorem residualAugPath_augments {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (Q : ResidualAugPath cap s t f) (hst : s ≠ t)
    (ε : ℝ) (hε : 0 < ε) (hfcap : ∀ u v, Q.Pf u v → f u v + ε ≤ cap u v)
    (hbε : ∀ u v, Q.Pb u v → ε ≤ f v u) :
    ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s := by
  classical
  -- the load-bearing helper: `∑ v, (if R v then ε else 0) = ε · card{v | R v}`.
  have hsum : ∀ (R : V → Prop),
      (∑ v, (if R v then ε else 0)) = ε * ((Finset.univ.filter R).card : ℝ) := by
    intro R
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine ⟨fun u v => f u v + (if Q.Pf u v then ε else 0) - (if Q.Pb v u then ε else 0),
    ⟨?_, ?_, ?_⟩, ?_⟩
  · -- nonneg
    intro u v
    show 0 ≤ f u v + (if Q.Pf u v then ε else 0) - (if Q.Pb v u then ε else 0)
    have h0 := hf.nonneg u v
    by_cases hpb : Q.Pb v u
    · have hb := hbε v u hpb          -- ε ≤ f u v
      split_ifs <;> linarith
    · split_ifs <;> linarith
  · -- capacity
    intro u v
    show f u v + (if Q.Pf u v then ε else 0) - (if Q.Pb v u then ε else 0) ≤ cap u v
    have hc := hf.capacity u v
    have hεle : (0:ℝ) ≤ ε := le_of_lt hε
    by_cases hpf : Q.Pf u v
    · have hcap := hfcap u v hpf       -- f u v + ε ≤ cap u v
      split_ifs <;> linarith
    · split_ifs <;> linarith
  · -- conserve at an interior vertex: the combined degree structure cancels the ε-terms
    intro w hws hwt
    unfold vertexExcess
    have hout : (∑ v, (f w v + (if Q.Pf w v then ε else 0) - (if Q.Pb v w then ε else 0)))
        = (∑ v, f w v) + ε * ((Finset.univ.filter (fun v => Q.Pf w v)).card : ℝ)
          - ε * ((Finset.univ.filter (fun v => Q.Pb v w)).card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum (fun v => Q.Pf w v),
        hsum (fun v => Q.Pb v w)]
    have hin : (∑ v, (f v w + (if Q.Pf v w then ε else 0) - (if Q.Pb w v then ε else 0)))
        = (∑ v, f v w) + ε * ((Finset.univ.filter (fun v => Q.Pf v w)).card : ℝ)
          - ε * ((Finset.univ.filter (fun v => Q.Pb w v)).card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum (fun v => Q.Pf v w),
        hsum (fun v => Q.Pb w v)]
    rw [hout, hin]
    have hconv := hf.conserve w hws hwt
    unfold vertexExcess at hconv
    have hdeg : ((Finset.univ.filter (fun v => Q.Pf w v)).card : ℝ)
          + ((Finset.univ.filter (fun v => Q.Pb w v)).card : ℝ)
        = ((Finset.univ.filter (fun u => Q.Pf u w)).card : ℝ)
          + ((Finset.univ.filter (fun u => Q.Pb u w)).card : ℝ) := by
      exact_mod_cast Q.hDeg w hws hwt
    linear_combination hconv + ε * hdeg
  · -- value strictly increases by ε at the source (hs: combined out = in + 1)
    unfold flowValue vertexExcess
    have hout : (∑ v, (f s v + (if Q.Pf s v then ε else 0) - (if Q.Pb v s then ε else 0)))
        = (∑ v, f s v) + ε * ((Finset.univ.filter (fun v => Q.Pf s v)).card : ℝ)
          - ε * ((Finset.univ.filter (fun v => Q.Pb v s)).card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum (fun v => Q.Pf s v),
        hsum (fun v => Q.Pb v s)]
    have hin : (∑ v, (f v s + (if Q.Pf v s then ε else 0) - (if Q.Pb s v then ε else 0)))
        = (∑ v, f v s) + ε * ((Finset.univ.filter (fun v => Q.Pf v s)).card : ℝ)
          - ε * ((Finset.univ.filter (fun v => Q.Pb s v)).card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum (fun v => Q.Pf v s),
        hsum (fun v => Q.Pb s v)]
    rw [hout, hin]
    have hscard : ((Finset.univ.filter (fun v => Q.Pf s v)).card : ℝ)
          + ((Finset.univ.filter (fun v => Q.Pb s v)).card : ℝ)
        = ((Finset.univ.filter (fun u => Q.Pf u s)).card : ℝ)
          + ((Finset.univ.filter (fun u => Q.Pb u s)).card : ℝ) + 1 := by
      exact_mod_cast Q.hs
    have hval : ((∑ v, f s v) + ε * ((Finset.univ.filter (fun v => Q.Pf s v)).card : ℝ)
          - ε * ((Finset.univ.filter (fun v => Q.Pb v s)).card : ℝ))
        - ((∑ v, f v s) + ε * ((Finset.univ.filter (fun v => Q.Pf v s)).card : ℝ)
          - ε * ((Finset.univ.filter (fun v => Q.Pb s v)).card : ℝ))
        = ((∑ v, f s v) - (∑ v, f v s)) + ε := by
      linear_combination ε * hscard
    rw [hval]
    linarith

/-! ### M11 — the mixed extraction and the general Ford–Fulkerson `haug`, DERIVED

M10 built the augmentation MECHANISM given a degree-structured `ResidualAugPath` (typed forward `Pf` /
backward `Pb` edge relations with the combined residual degree structure). M11 discharges the *extraction*
of that structure from a general residual reachability walk, mirroring M8/M9's forward pipeline for the
full mixed `ResidualStep`:

* **Step 1** `SimpleResidualPath` / `simpleResidualPath_of_reachable` — a *simple* (de-duplicated) residual
  path, an injective `Fin (n+1)`-indexed vertex sequence with a `ResidualStep` on every consecutive pair,
  materialised from `Relation.ReflTransGen (ResidualStep cap f) s t` by REUSING M9's generic directed dedup
  (`exists_nodup_isChain_list` is generic in the step relation `r`, so it applies verbatim to
  `r := ResidualStep cap f`). This is M9's `simpleForwardPath_of_reachable` with `ForwardResidualStep`
  replaced by `ResidualStep`.
* **Step 2** `SimpleResidualPath.toResidualAugPath` — **the tagging.** Each path edge `u→v` is TAGGED
  deterministically: `Pf u v` if it has forward slack (`0 < cap u v − f u v`), else `Pb u v` (the residual
  step then forces `0 < f v u`). `Pf` and `Pb` are disjoint and their union is the path-edge set, so the
  combined out and in degree splits as `#Pf + #Pb = #edge` (`card_union_of_disjoint`), and the edge degree is
  exactly M8's fibre count (`card_edge_out`/`card_edge_in`, the same injective-fibre computation). The
  `ResidualAugPath` degree conditions (`hDeg`/`hs`/`ht`) thus reduce to M8's simple-path edge degrees;
  `hfslack`/`hbpos` come from the tag.
* **Step 3 + 4** `residualReachable_augments` — **the general haug, DERIVED.** ε is the min over the finite
  nonempty combined edge set of the per-edge margin (forward slack on `Pf` edges, backflow `f v u` on `Pb`
  edges), positive by `hfslack`/`hbpos`; it feeds `residualAugPath_augments` (M10). So residual
  reachability `s ⇝ t` ALONE yields a strictly larger flow — the FULL Ford–Fulkerson augmenting-path
  input, no longer carried, no forward/backward restriction.
* **Step 5** `exact_rt_maxFlow_mincut_unconditional` — **the haug discharged in the capstone.** Since
  `t ∈ residualCut ↔ ReflTransGen (ResidualStep cap f) s t` (`mem_residualCut`),
  `residualReachable_augments` PROVES the `haug` that M4/M5 carried. So max-flow = min-cut now holds for
  any maximum flow with `s ≠ t` with NO carried augmentation hypothesis — conditional ONLY on max-flow
  EXISTENCE (`IsMaxSTFlow`), the single remaining carry.
-/

/-- **M11 (Step 1) — a simple mixed residual augmenting path**, the `ResidualStep` analogue of
`SimpleForwardPath`: an *injective* `Fin (n+1)`-indexed vertex sequence from `s` to `t`, `n ≥ 1`, with a
(mixed forward/backward) `ResidualStep` on every consecutive pair. -/
structure SimpleResidualPath (cap : V → V → ℝ) (s t : V) (f : V → V → ℝ) where
  /-- Number of edges (so `n+1` vertices); at least one edge. -/
  n : ℕ
  /-- The path has at least one edge. -/
  hn : 1 ≤ n
  /-- The vertex sequence. -/
  p : Fin (n + 1) → V
  /-- Simplicity: the vertex sequence has no repeats. -/
  hp_inj : Function.Injective p
  /-- The first vertex is the source. -/
  hp0 : p 0 = s
  /-- The last vertex is the sink. -/
  hplast : p (Fin.last n) = t
  /-- Every consecutive pair is a residual step. -/
  hstep : ∀ i : Fin n, ResidualStep cap f (p i.castSucc) (p i.succ)

/-- The directed edge relation of a `SimpleResidualPath`: `u→v` is an edge iff some consecutive pair of the
vertex sequence is `(u, v)`. -/
def SimpleResidualPath.edge {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (SP : SimpleResidualPath cap s t f) (u v : V) : Prop :=
  ∃ i : Fin SP.n, SP.p i.castSucc = u ∧ SP.p i.succ = v

/-- **M11 — the forward tag.** A path edge `u→v` with forward residual slack. -/
def SimpleResidualPath.Pf {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (SP : SimpleResidualPath cap s t f) (u v : V) : Prop :=
  SP.edge u v ∧ 0 < cap u v - f u v

/-- **M11 — the backward tag.** A path edge `u→v` WITHOUT forward slack (so, being a residual step, its
reverse real edge `v→u` carries flow to cancel). -/
def SimpleResidualPath.Pb {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (SP : SimpleResidualPath cap s t f) (u v : V) : Prop :=
  SP.edge u v ∧ ¬ (0 < cap u v - f u v)

/-- **M11 — edge out-degree = injective fibre count** (the M8 computation for the residual edge). -/
theorem SimpleResidualPath.card_edge_out {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (SP : SimpleResidualPath cap s t f) (u : V) :
    (Finset.univ.filter (fun v => SP.edge u v)).card
      = if (∃ i : Fin SP.n, SP.p i.castSucc = u) then 1 else 0 := by
  classical
  have hcs_inj : Function.Injective (fun i : Fin SP.n => SP.p i.castSucc) :=
    SP.hp_inj.comp (Fin.castSucc_injective SP.n)
  have hsucc_inj : Function.Injective (fun i : Fin SP.n => SP.p i.succ) :=
    SP.hp_inj.comp (Fin.succ_injective SP.n)
  have himg : Finset.univ.filter (fun v => SP.edge u v)
      = (Finset.univ.filter (fun i : Fin SP.n => SP.p i.castSucc = u)).image
          (fun i : Fin SP.n => SP.p i.succ) := by
    ext v
    simp only [SimpleResidualPath.edge, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
  rw [himg, Finset.card_image_of_injective _ hsucc_inj,
    card_filter_fiber_of_injective _ hcs_inj u]

/-- **M11 — edge in-degree = injective fibre count** (the M8 computation for the residual edge). -/
theorem SimpleResidualPath.card_edge_in {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (SP : SimpleResidualPath cap s t f) (u : V) :
    (Finset.univ.filter (fun v => SP.edge v u)).card
      = if (∃ i : Fin SP.n, SP.p i.succ = u) then 1 else 0 := by
  classical
  have hcs_inj : Function.Injective (fun i : Fin SP.n => SP.p i.castSucc) :=
    SP.hp_inj.comp (Fin.castSucc_injective SP.n)
  have hsucc_inj : Function.Injective (fun i : Fin SP.n => SP.p i.succ) :=
    SP.hp_inj.comp (Fin.succ_injective SP.n)
  have himg : Finset.univ.filter (fun v => SP.edge v u)
      = (Finset.univ.filter (fun i : Fin SP.n => SP.p i.succ = u)).image
          (fun i : Fin SP.n => SP.p i.castSucc) := by
    ext v
    simp only [SimpleResidualPath.edge, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨i, h1, h2⟩; exact ⟨i, h2, h1⟩
    · rintro ⟨i, h1, h2⟩; exact ⟨i, h2, h1⟩
  rw [himg, Finset.card_image_of_injective _ hcs_inj,
    card_filter_fiber_of_injective _ hsucc_inj u]

section
open List
set_option linter.unusedSectionVars false

/-- **★★ M11 (Step 1) — the mixed directed dedup capstone.** Residual reachability `s ⇝ t`
(`Relation.ReflTransGen (ResidualStep cap f) s t`) with `s ≠ t` yields a `SimpleResidualPath`. This is
M9's `simpleForwardPath_of_reachable` with `ForwardResidualStep` replaced by the mixed `ResidualStep`,
REUSING M9's generic dedup `exists_nodup_isChain_list` (generic in the step relation). -/
theorem simpleResidualPath_of_reachable {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (hst : s ≠ t)
    (hreach : Relation.ReflTransGen (ResidualStep cap f) s t) :
    Nonempty (SimpleResidualPath cap s t f) := by
  obtain ⟨w, hc, hh, hl, hnd⟩ := exists_nodup_isChain_list hreach
  have hwne : w ≠ [] := by rintro rfl; simp at hh
  have hlen1 : 1 ≤ w.length := List.length_pos_iff_ne_nil.mpr hwne
  have h0 : w[0]'(by omega) = s := by
    have e : w[0]? = some s := by rw [← head?_eq_getElem?]; exact hh
    rw [getElem?_eq_getElem (by omega)] at e; simpa using e
  have hL : w[w.length - 1]'(by omega) = t := by
    have e : w[w.length - 1]? = some t := by rw [← getLast?_eq_getElem?]; exact hl
    rw [getElem?_eq_getElem (by omega)] at e; simpa using e
  have hlen2 : 2 ≤ w.length := by
    rcases Nat.lt_or_ge w.length 2 with h | h
    · exfalso; apply hst
      have hone : w.length = 1 := by omega
      have e0 : w[0]? = some s := by rw [← head?_eq_getElem?]; exact hh
      have eL : w[0]? = some t := by
        have := hl; rw [getLast?_eq_getElem?, hone] at this; simpa using this
      rw [e0] at eL; exact Option.some.injEq _ _ |>.mp eL
    · exact h
  have hN' : w.length - 1 + 1 = w.length := by omega
  refine ⟨{
    n := w.length - 1
    hn := by omega
    p := fun i => w.get (Fin.cast hN' i)
    hp_inj := by
      intro x y hxy
      simp only [List.get_eq_getElem] at hxy
      exact Fin.cast_injective hN'
        ((List.nodup_iff_injective_get.mp hnd) (by simpa [List.get_eq_getElem] using hxy))
    hp0 := by
      simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_zero]; exact h0
    hplast := by
      simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_last]; exact hL
    hstep := by
      intro i
      have hi1 : (i : ℕ) + 1 < w.length := by have := i.2; omega
      have hstep := isChain_iff_getElem.mp hc i.val hi1
      show ResidualStep cap f (w.get (Fin.cast hN' i.castSucc)) (w.get (Fin.cast hN' i.succ))
      simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_castSucc, Fin.val_succ]
      exact hstep
  }⟩

end

/-- **★★ M11 (Step 2) — the tagging: a simple residual path yields a `ResidualAugPath`.** Each path edge
is tagged forward (`Pf`, has slack) or backward (`Pb`, no slack ⟹ backflow). `Pf`/`Pb` disjoint with
union the path edges, so the combined degree splits as `#Pf + #Pb = #edge`, and edge degree is M8's
injective fibre count — giving the `ResidualAugPath` degree structure. This is the mixed-direction
analogue of `SimpleForwardPath.toForwardAugPath`. -/
def SimpleResidualPath.toResidualAugPath {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (SP : SimpleResidualPath cap s t f) : ResidualAugPath cap s t f := by
  classical
  haveI : NeZero SP.n := ⟨by have := SP.hn; omega⟩
  -- the disjoint-union card split, both directions: `#Pf + #Pb = #edge`.
  have hsplit_out : ∀ w, (Finset.univ.filter (fun v => SP.Pf w v)).card
        + (Finset.univ.filter (fun v => SP.Pb w v)).card
      = (Finset.univ.filter (fun v => SP.edge w v)).card := by
    intro w
    have hdisj : Disjoint (Finset.univ.filter (fun v => SP.Pf w v))
        (Finset.univ.filter (fun v => SP.Pb w v)) := by
      rw [Finset.disjoint_left]
      intro v hpf hpb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleResidualPath.Pf,
        SimpleResidualPath.Pb] at hpf hpb
      exact hpb.2 hpf.2
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleResidualPath.Pf, SimpleResidualPath.Pb]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      by_cases hsl : 0 < cap w v - f w v
      · exact Or.inl ⟨he, hsl⟩
      · exact Or.inr ⟨he, hsl⟩
  have hsplit_in : ∀ w, (Finset.univ.filter (fun u => SP.Pf u w)).card
        + (Finset.univ.filter (fun u => SP.Pb u w)).card
      = (Finset.univ.filter (fun u => SP.edge u w)).card := by
    intro w
    have hdisj : Disjoint (Finset.univ.filter (fun u => SP.Pf u w))
        (Finset.univ.filter (fun u => SP.Pb u w)) := by
      rw [Finset.disjoint_left]
      intro v hpf hpb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleResidualPath.Pf,
        SimpleResidualPath.Pb] at hpf hpb
      exact hpb.2 hpf.2
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleResidualPath.Pf, SimpleResidualPath.Pb]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      by_cases hsl : 0 < cap v w - f v w
      · exact Or.inl ⟨he, hsl⟩
      · exact Or.inr ⟨he, hsl⟩
  exact {
    Pf := SP.Pf
    Pb := SP.Pb
    hDeg := by
      intro w hws hwt
      rw [hsplit_out w, hsplit_in w, SP.card_edge_out w, SP.card_edge_in w]
      have hiff : (∃ i : Fin SP.n, SP.p i.castSucc = w) ↔ (∃ i : Fin SP.n, SP.p i.succ = w) := by
        have cs : (∃ i : Fin SP.n, SP.p i.castSucc = w)
            ↔ (∃ j : Fin (SP.n + 1), j ≠ Fin.last SP.n ∧ SP.p j = w) := by
          constructor
          · rintro ⟨i, rfl⟩; exact ⟨i.castSucc, Fin.castSucc_ne_last i, rfl⟩
          · rintro ⟨j, hj, rfl⟩; exact ⟨j.castPred hj, by rw [Fin.castSucc_castPred]⟩
        have sc : (∃ i : Fin SP.n, SP.p i.succ = w)
            ↔ (∃ j : Fin (SP.n + 1), j ≠ 0 ∧ SP.p j = w) := by
          constructor
          · rintro ⟨i, rfl⟩; exact ⟨i.succ, Fin.succ_ne_zero i, rfl⟩
          · rintro ⟨j, hj, rfl⟩; exact ⟨j.pred hj, by rw [Fin.succ_pred]⟩
        rw [cs, sc]
        constructor
        · rintro ⟨j, _, rfl⟩
          exact ⟨j, fun hj0 => hws (by rw [hj0, SP.hp0]), rfl⟩
        · rintro ⟨j, _, rfl⟩
          exact ⟨j, fun hjl => hwt (by rw [hjl, SP.hplast]), rfl⟩
      simp only [hiff]
    hs := by
      rw [hsplit_out s, hsplit_in s, SP.card_edge_out s, SP.card_edge_in s]
      have hex : ∃ i : Fin SP.n, SP.p i.castSucc = s := ⟨0, by rw [Fin.castSucc_zero', SP.hp0]⟩
      have hnex : ¬ ∃ i : Fin SP.n, SP.p i.succ = s := by
        rintro ⟨i, hi⟩; exact Fin.succ_ne_zero i (SP.hp_inj (hi.trans SP.hp0.symm))
      rw [if_pos hex, if_neg hnex]
    ht := by
      rw [hsplit_out t, hsplit_in t, SP.card_edge_out t, SP.card_edge_in t]
      have hnex : ¬ ∃ i : Fin SP.n, SP.p i.castSucc = t := by
        rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i (SP.hp_inj (hi.trans SP.hplast.symm))
      have hex : ∃ i : Fin SP.n, SP.p i.succ = t := by
        have hidx : (⟨SP.n - 1, by have := SP.hn; omega⟩ : Fin SP.n).succ = Fin.last SP.n := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_last]
          have := SP.hn; omega
        exact ⟨⟨SP.n - 1, by have := SP.hn; omega⟩, by rw [hidx]; exact SP.hplast⟩
      rw [if_neg hnex, if_pos hex]
    hfslack := by
      rintro u v ⟨_, hsl⟩
      linarith
    hbpos := by
      rintro u v ⟨⟨i, hi1, hi2⟩, hnf⟩
      have hstep := SP.hstep i
      rw [hi1, hi2] at hstep
      rcases hstep with h | h
      · exact absurd h hnf
      · exact h
  }

/-- **★★ M11 (Steps 3+4) — the general Ford–Fulkerson `haug`, DERIVED.** Residual reachability `s ⇝ t`
(`Relation.ReflTransGen (ResidualStep cap f) s t`) with `s ≠ t` yields a strictly larger `s`-`t` flow — no
forward/backward restriction, no carried augmentation. The mixed directed dedup
(`simpleResidualPath_of_reachable`) produces a simple residual path, the tagging
(`toResidualAugPath`) its `ResidualAugPath` degree structure, `ε` is the min per-edge margin (forward slack
on `Pf`, backflow on `Pb`) over the finite nonempty edge set, and `residualAugPath_augments` (M10) closes
it. This is the FULL Ford–Fulkerson augmenting-path input, now machine-checked. -/
theorem residualReachable_augments {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hf : IsSTFlow cap s t f) (hst : s ≠ t)
    (hreach : Relation.ReflTransGen (ResidualStep cap f) s t) :
    ∃ g, IsSTFlow cap s t g ∧ flowValue f s < flowValue g s := by
  classical
  obtain ⟨SP⟩ := simpleResidualPath_of_reachable hf hst hreach
  -- backflow on backward-tagged edges (the residual step with forward slack failing forces `0 < f v u`)
  have hbpos : ∀ u v, SP.Pb u v → 0 < f v u := by
    rintro u v ⟨⟨i, hi1, hi2⟩, hnf⟩
    have hstep := SP.hstep i
    rw [hi1, hi2] at hstep
    rcases hstep with h | h
    · exact absurd h hnf
    · exact h
  -- `Pf`/`Pb` are disjoint tags of each path edge
  have hdisj : ∀ u v, SP.Pb u v → ¬ SP.Pf u v := fun u v hpb hpf => hpb.2 hpf.2
  -- the source has a residual out-edge (the first path step), so the combined edge set is nonempty
  set i0 : Fin SP.n := ⟨0, SP.hn⟩ with hi0
  have hcs0 : SP.p i0.castSucc = s := by
    have hzero : i0.castSucc = (0 : Fin (SP.n + 1)) := by apply Fin.ext; simp [hi0]
    rw [hzero, SP.hp0]
  obtain ⟨v0, hv0⟩ : ∃ v, SP.Pf s v ∨ SP.Pb s v := by
    refine ⟨SP.p i0.succ, ?_⟩
    have he : SP.edge s (SP.p i0.succ) := ⟨i0, hcs0, rfl⟩
    by_cases hsl : 0 < cap s (SP.p i0.succ) - f s (SP.p i0.succ)
    · exact Or.inl ⟨he, hsl⟩
    · exact Or.inr ⟨he, hsl⟩
  set E : Finset (V × V) :=
    Finset.univ.filter (fun p : V × V => SP.Pf p.1 p.2 ∨ SP.Pb p.1 p.2) with hE
  have hEne : E.Nonempty :=
    ⟨(s, v0), by rw [hE, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hv0⟩⟩
  set margin : V × V → ℝ :=
    fun p => if SP.Pf p.1 p.2 then cap p.1 p.2 - f p.1 p.2 else f p.2 p.1 with hmargin
  set ε : ℝ := E.inf' hEne margin with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef, Finset.lt_inf'_iff]
    intro p hp
    rw [hE, Finset.mem_filter] at hp
    rcases hp.2 with hpf | hpb
    · rw [hmargin]; simp only [if_pos hpf]
      have := hpf.2; linarith
    · rw [hmargin]; simp only
      by_cases hpf : SP.Pf p.1 p.2
      · rw [if_pos hpf]; have := hpf.2; linarith
      · rw [if_neg hpf]; exact hbpos p.1 p.2 hpb
  have hfcap : ∀ u v, SP.Pf u v → f u v + ε ≤ cap u v := by
    intro u v huv
    have hmem : (u, v) ∈ E := by rw [hE, Finset.mem_filter]; exact ⟨Finset.mem_univ _, Or.inl huv⟩
    have hle : ε ≤ margin (u, v) := Finset.inf'_le margin hmem
    rw [hmargin] at hle; simp only [if_pos huv] at hle
    have := huv.2; linarith
  have hbε : ∀ u v, SP.Pb u v → ε ≤ f v u := by
    intro u v huv
    have hmem : (u, v) ∈ E := by rw [hE, Finset.mem_filter]; exact ⟨Finset.mem_univ _, Or.inr huv⟩
    have hle : ε ≤ margin (u, v) := Finset.inf'_le margin hmem
    rw [hmargin] at hle; simp only [if_neg (hdisj u v huv)] at hle
    exact hle
  exact residualAugPath_augments hf SP.toResidualAugPath hst ε hεpos hfcap hbε

/-- **★★★ M11 (Step 5) — max-flow = min-cut, the augmentation `haug` DISCHARGED.** For a maximum `s`-`t`
flow `f` (`s ≠ t`), the flow value equals the capacity of the residual-reachable cut, with NO carried
augmentation hypothesis. The `haug` that M4/M5 carried is now PROVED: since
`t ∈ residualCut ↔ ReflTransGen (ResidualStep cap f) s t` (`mem_residualCut`),
`residualReachable_augments` supplies it. So the hard half of max-flow = min-cut is conditional ONLY on
max-flow EXISTENCE (`IsMaxSTFlow`) — the single remaining Ford–Fulkerson carry (compactness / termination),
everything else (the augmenting path augments, no augmenting path ⟹ saturating cut, capstone) derived. -/
theorem exact_rt_maxFlow_mincut_unconditional {cap : V → V → ℝ} {s t : V} {f : V → V → ℝ}
    (hmax : IsMaxSTFlow cap s t f) (hst : s ≠ t) :
    flowValue f s = cutCapacity cap (residualCut cap f s) := by
  apply exact_rt_maxFlow_mincut hmax hst
  intro ht
  exact residualReachable_augments hmax.1 hst (mem_residualCut.mp ht)

/-! ### M12 — max-flow EXISTENCE via compactness, and the UNCONDITIONAL capstone

M11 left max-flow = min-cut conditional ONLY on (c) **max-flow EXISTENCE** (`IsMaxSTFlow`). M12
discharges it by the standard compactness (extreme-value) argument. The set of `s`-`t` flows
`{f | IsSTFlow cap s t f} ⊆ V → V → ℝ` is:

* **nonempty** — the zero flow is an `s`-`t` flow (nonneg `0 ≤ 0`, capacity `0 ≤ cap` by `hcap`,
  conservation `vertexExcess 0 = 0`);
* **closed** — a finite intersection of the closed conditions `{f | 0 ≤ f u v}` and
  `{f | f u v ≤ cap u v}` (`isClosed_le` of continuous evaluations) and `{f | vertexExcess f v = 0}`
  (`isClosed_eq`), each intersected over the finite vertex index (`isClosed_iInter`);
* **bounded** — `0 ≤ f u v ≤ cap u v` forces `‖f‖ ≤ ‖cap‖` in the sup norm, so the flow set sits
  inside `Metric.closedBall 0 ‖cap‖`.

`V → V → ℝ` is a finite-dimensional real normed space, hence a `ProperSpace`, so closed + bounded ⟹
**compact** (`Metric.isCompact_of_isClosed_isBounded`, Heine–Borel). `flowValue · s = vertexExcess · s`
is continuous (evaluation + finite sums + subtraction), so it **attains a maximum** on the nonempty
compact flow set (`IsCompact.exists_isMaxOn`) — that maximiser is an `IsMaxSTFlow`.

Feeding it into `exact_rt_maxFlow_mincut_unconditional` yields the UNCONDITIONAL finite max-flow =
min-cut theorem `maxFlow_min_cut`, carrying ONLY `cap`-nonnegativity — the standard finite
Ford–Fulkerson statement, fully machine-checked. -/

/-- **★★★ M12 — max-flow EXISTENCE.** For any nonnegative capacity `cap`, a maximum `s`-`t` flow
exists. The `s`-`t` flow set is nonempty (the zero flow), closed and bounded in the
finite-dimensional space `V → V → ℝ`, hence compact (Heine–Borel); `flowValue · s` is continuous and
attains its maximum there. -/
theorem exists_maxSTFlow (cap : V → V → ℝ) (s t : V) (hcap : ∀ u v, 0 ≤ cap u v) :
    ∃ f, IsMaxSTFlow cap s t f := by
  classical
  -- evaluation `f ↦ f u v` is continuous
  have hev : ∀ u v, Continuous (fun f : V → V → ℝ => f u v) :=
    fun u v => (continuous_apply v).comp (continuous_apply u)
  -- `f ↦ vertexExcess f w` is continuous
  have hVE : ∀ w, Continuous (fun f : V → V → ℝ => vertexExcess f w) := by
    intro w
    show Continuous (fun f : V → V → ℝ => (∑ v, f w v) - (∑ v, f v w))
    exact (continuous_finsetSum _ (fun v _ => hev w v)).sub
      (continuous_finsetSum _ (fun v _ => hev v w))
  -- the flow set
  set S : Set (V → V → ℝ) := {f | IsSTFlow cap s t f} with hS
  -- nonempty: the zero flow
  have hne : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨fun u v => ?_, fun u v => ?_, fun v _ _ => ?_⟩
    · simp
    · simpa using hcap u v
    · simp [vertexExcess]
  -- closed: intersection of closed conditions
  have hc1 : IsClosed {f : V → V → ℝ | ∀ u v, 0 ≤ f u v} := by
    have he : {f : V → V → ℝ | ∀ u v, 0 ≤ f u v} = ⋂ u, ⋂ v, {f : V → V → ℝ | 0 ≤ f u v} := by
      ext f; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact isClosed_iInter fun u => isClosed_iInter fun v =>
      isClosed_le continuous_const (hev u v)
  have hc2 : IsClosed {f : V → V → ℝ | ∀ u v, f u v ≤ cap u v} := by
    have he : {f : V → V → ℝ | ∀ u v, f u v ≤ cap u v}
        = ⋂ u, ⋂ v, {f : V → V → ℝ | f u v ≤ cap u v} := by
      ext f; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact isClosed_iInter fun u => isClosed_iInter fun v =>
      isClosed_le (hev u v) continuous_const
  have hc3 : IsClosed {f : V → V → ℝ | ∀ v, v ≠ s → v ≠ t → vertexExcess f v = 0} := by
    have he : {f : V → V → ℝ | ∀ v, v ≠ s → v ≠ t → vertexExcess f v = 0}
        = ⋂ v, ⋂ _ : v ≠ s, ⋂ _ : v ≠ t, {f : V → V → ℝ | vertexExcess f v = 0} := by
      ext f; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (hVE v) continuous_const
  have hclosed : IsClosed S := by
    have he : S = {f : V → V → ℝ | ∀ u v, 0 ≤ f u v} ∩ {f : V → V → ℝ | ∀ u v, f u v ≤ cap u v}
        ∩ {f : V → V → ℝ | ∀ v, v ≠ s → v ≠ t → vertexExcess f v = 0} := by
      ext f
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    rw [he]
    exact (hc1.inter hc2).inter hc3
  -- bounded: `S ⊆ closedBall 0 ‖cap‖`
  have hbdd : Bornology.IsBounded S := by
    apply (Metric.isBounded_closedBall (x := (0 : V → V → ℝ)) (r := ‖cap‖)).subset
    intro f hf
    have hf' : IsSTFlow cap s t f := hf
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg cap)]
    intro u
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg cap)]
    intro v
    have h1 : (0 : ℝ) ≤ f u v := hf'.nonneg u v
    have h2 : f u v ≤ cap u v := hf'.capacity u v
    have hcapuv : ‖cap u v‖ ≤ ‖cap‖ :=
      (norm_le_pi_norm (cap u) v).trans (norm_le_pi_norm cap u)
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    calc f u v ≤ cap u v := h2
      _ ≤ |cap u v| := le_abs_self _
      _ = ‖cap u v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖cap‖ := hcapuv
  -- compact (Heine–Borel: `V → V → ℝ` is a finite-dim `ProperSpace`)
  have hcompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  -- `flowValue · s` is continuous and attains its max on the nonempty compact flow set
  have hcont : Continuous (fun f : V → V → ℝ => flowValue f s) := hVE s
  obtain ⟨f, hfS, hfmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
  exact ⟨f, hfS, fun g hg => hfmax hg⟩

/-- **★★★★ THE FINITE MAX-FLOW = MIN-CUT THEOREM (unconditional).** For any nonnegative capacity
`cap` on a finite vertex set with `s ≠ t`, there is an `s`-`t` flow whose value equals the capacity of
the residual-reachable cut `residualCut cap f s`. Combining M12's max-flow existence
(`exists_maxSTFlow`) with M11's `exact_rt_maxFlow_mincut_unconditional` (max-flow = min-cut for a
maximum flow, augmentation `haug` fully discharged), this is the finite Ford–Fulkerson statement
carrying ONLY the standard `cap`-nonnegativity hypothesis — every combinatorial and analytic
ingredient machine-checked here (M1–M12). -/
theorem maxFlow_min_cut (cap : V → V → ℝ) (s t : V) (hst : s ≠ t) (hcap : ∀ u v, 0 ≤ cap u v) :
    ∃ f, IsSTFlow cap s t f ∧ flowValue f s = cutCapacity cap (residualCut cap f s) := by
  obtain ⟨f, hmax⟩ := exists_maxSTFlow cap s t hcap
  exact ⟨f, hmax.1, exact_rt_maxFlow_mincut_unconditional hmax hst⟩

/-- **★★ EXACT RT — the full optimality statement, UNCONDITIONAL: `ExactRT`'s Ford–Fulkerson gap
DISCHARGED.** `ExactRT.exact_rt_of_saturating` reduced the exact Ryu–Takayanagi equality to the
*existence of a saturating witness* (a flow `f` and a separating cut `C` with
`flowValue f s = cutCapacity cap C`), citing that existence — the Ford–Fulkerson / Menger content —
as the Mathlib-gap frontier. That witness now EXISTS as a machine-checked theorem: the maximum flow
(`exists_maxSTFlow`) together with its residual-reachable cut is saturating (`maxFlow_min_cut`), so
exact RT holds with NO carried witness. The result: for `s ≠ t` and nonnegative capacities there is a
flow `f` and a separating cut `C` such that `f` maximizes the flow value over all `s`-`t` flows AND `C`
minimizes the capacity over all separating cuts, with the two equal — the exact RT equality, now
UNCONDITIONAL (carrying only `cap`-nonnegativity). This is the finite `V → V → ℝ` network model. -/
theorem exact_rt_unconditional (cap : V → V → ℝ) (s t : V) (hst : s ≠ t)
    (hcap : ∀ u v, 0 ≤ cap u v) :
    ∃ (f : V → V → ℝ) (C : Finset V), IsSTFlow cap s t f ∧ s ∈ C ∧ t ∉ C ∧
      flowValue f s = cutCapacity cap C ∧
      (∀ f', IsSTFlow cap s t f' → flowValue f' s ≤ flowValue f s) ∧
      (∀ C', s ∈ C' → t ∉ C' → cutCapacity cap C ≤ cutCapacity cap C') := by
  obtain ⟨f, hmax⟩ := exists_maxSTFlow cap s t hcap
  have hnr : t ∉ residualCut cap f s :=
    exact_rt_of_maxFlow hmax hst
      (fun ht => residualReachable_augments hmax.1 hst (mem_residualCut.mp ht))
  have hsat : flowValue f s = cutCapacity cap (residualCut cap f s) :=
    exact_rt_maxFlow_mincut_unconditional hmax hst
  have hrt := exact_rt_of_saturating hmax.1 source_mem_residualCut hnr hsat
  exact ⟨f, residualCut cap f s, hmax.1, source_mem_residualCut, hnr, hsat, hrt.1, hrt.2⟩

end QIQTH.QG
