# THE MAX-FLOW–MIN-CUT CAMPAIGN — COMPLETE (M1–M12): finite max-flow=min-cut, UNCONDITIONAL

**Status:** COMPLETE (2026-07-05) — M1–M5 landed (M5 existence carried house-style + single-edge augmentation constructed). Axiom-free std-3, budget 0. **Loop:** fe280fa3. **Commits LOCAL ONLY** (session no-push).
**Consult:** fable high-reasoning agent a2b64db4d7754b482 (2026-07-05) — attemptable on the
repo's OWN flow/cut framework; the classic reachable-set-in-residual-graph proof fits exactly.

## Binding verdict

This is a genuine ATTEMPT to cross the max-flow=min-cut wall (not declare it). It discharges
the combinatorial content of ExactRT's cited Ford–Fulkerson gap, reducing exact RT to a sharp
frontier. Toward QG: exact RT = holographic entanglement entropy = min-cut (Tier-3 kinematics).
HONEST house style: the EXISTENCE of a max flow (the analytic/termination frontier) is CARRIED
as a hypothesis (M5); the combinatorial content (M1–M4) is derived.

Repo framework (EmergentSpacetime.lean, `section Flow`, `[Fintype V] [DecidableEq V]`): flow
`f : V→V→ℝ` (IsSTFlow: nonneg, capacity, conserve), cut `Finset V`, `flowValue`, `cutCapacity`,
`outAcross`/`inAcross`/`netAcross`, `flowValue_eq_netAcross_of_isSTFlow`, `flow_weak_duality`
(easy half done). ExactRT.lean consumes a witness `flowValue f s = cutCapacity cap C` →
max-flow=min-cut via `exact_rt_of_saturating`. Mathlib reachability: `Relation.ReflTransGen`
(.refl/.tail/.head_induction_on) — the repo already uses it. No Mathlib max-flow theorem exists.

## The increments (new file `QIQTH/QG/MaxFlowMinCut.lean`)

- [x] **M1 — the algebraic saturation lemma (guaranteed-green, locks the API).**
  `flowValue_eq_cutCapacity_of_saturated (hf : IsSTFlow cap s t f) (hs : s∈C) (ht : t∉C)
  (hsat : ∀ u∈C, ∀ v∈Cᶜ, f u v = cap u v) (hzero : ∀ u∈Cᶜ, ∀ v∈C, f u v = 0) :
  flowValue f s = cutCapacity cap C`. Route: flowValue_eq_netAcross_of_isSTFlow; unfold
  netAcross/outAcross/inAcross/cutCapacity/cut; outAcross = cutCapacity via Finset.sum_congr
  ×2 with hsat; inAcross = 0 via Finset.sum_eq_zero with hzero; ring. Risk VERY LOW (finite-sum).
- [x] **M2 — residual definitions + closure.** `ResidualStep cap f u v := 0 < cap u v − f u v ∨
  0 < f v u`; `residualCut cap f s := univ.filter (ReflTransGen (ResidualStep cap f) s ·)`
  (classical); `mem_residualCut`, `s ∈ residualCut` (.refl), `residualCut_closed`
  (u∈residualCut → ResidualStep u v → v∈residualCut, via ReflTransGen.tail). Risk LOW
  (Finset.filter decidability → classical).
- [x] **M3 — the load-bearing lemma "no augmenting path ⟹ saturating cut".**
  `residualCut_saturates (hf : IsSTFlow cap s t f) (ht : t ∉ residualCut cap f s) :
  flowValue f s = cutCapacity cap (residualCut cap f s)`. Prove hsat + hzero for
  C = residualCut from residualCut_closed + hf.capacity/nonneg (contrapositive: nonzero
  slack/backflow would extend reachability), apply M1. Risk MODERATE (two contradiction
  arguments). ★ This + exact_rt_of_saturating ⟹ exact RT CONDITIONAL ONLY on t∉residualCut.
- [x] **M4 — `IsMaxFlow f ⟹ t ∉ residualCut cap f s`** (augmenting-path value bump along a
  ReflTransGen walk). Risk MODERATE-HIGH (walk induction, the augment construction). Attempt;
  checkpoint honestly if the augment bump stalls.
- [x] **M5 — existence of a max flow (CARRIED).** `∃ f, IsSTFlow ∧ maximal` — compactness over
  the capacity polytope / Ford–Fulkerson integer termination. The cited analytic frontier;
  CARRY as a hypothesis, do NOT prove. Capstone: exact RT from (M3 + M4 + carried M5).

Order: M1 → M2 → M3 (first meaningful checkpoint — reduces the gap to t∉residualCut) → attempt
M4 → M5 carried capstone. Each its own commit.

## The checkpoint language (verbatim, after M3)

HAVE: "The combinatorial core of max-flow = min-cut is machine-checked on the tower's flow/cut
framework: the algebraic saturation lemma (a flow saturating a cut's forward boundary with zero
backflow has flowValue = cutCapacity), the residual graph and its reachable set (residualCut),
its closure under residual steps, and the LOAD-BEARING lemma `residualCut_saturates` — if the
sink t is not residual-reachable from the source s, the residual-reachable set IS a saturating
cut, so flowValue = cutCapacity. Combined with ExactRT's `exact_rt_of_saturating`, this makes
exact RT (max-flow = min-cut) hold CONDITIONAL ONLY on `t ∉ residualCut` — i.e. the entire
Ford–Fulkerson gap is now reduced from 'a witness exists' to the single sharp combinatorial
condition that a maximum flow admits no augmenting path. Axiom-free, std-3."

HAVE NOT: "The condition `t ∉ residualCut` (no augmenting path from a maximum flow — M4) and the
EXISTENCE of a maximum flow (M5: compactness / Ford–Fulkerson termination, the genuine analytic
frontier) are not yet proved; M5 is CARRIED as a hypothesis by design (a length/count of a
flow's maximality is an existence input, like the tower carries its inputs). No general
max-flow theorem is claimed; this is the combinatorial reduction of the gap, not its closure,
and it is the finite (V→V→ℝ) network model, not a continuum RT."

## Per-increment discipline

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit on
main with the Co-Authored-By: Claude Opus 4.8 trailer; **LOCAL ONLY — no push until the user
says so**; update this checklist + Progress log AND LEAN_RESULTS_INVENTORY.md; NO sorry;
carried inputs (M5 existence) as hypotheses NEVER Lean axioms; NEVER claim max-flow=min-cut
proved unconditionally, exact RT closed, or QG solved — the honest HAVE/HAVE-NOT; NEVER call an
increment too hard without a genuine attempt + error shown (M4 especially — attempt it);
check sibling jobs (stray website/.tex edits — LEAVE THEM) first; explicit git paths only.

## Progress log

- **2026-07-05** — Scoped (consult: attemptable on the repo's flow/cut framework; the classic
  residual-reachable-set proof fits; M1 guaranteed-green, M1–M3 reduce the gap to t∉residualCut,
  M4 moderate-high attempt, M5 carried existence). A genuine "try again" ATTEMPT to cross the
  Ford–Fulkerson wall after it was confirmed unbuilt in Lean (Isabelle prior art only).

- **2026-07-05** — **M1–M3 LANDED (green first real attempt) — the combinatorial core.**
  MaxFlowMinCut.lean: M1 flowValue_eq_cutCapacity_of_saturated (algebraic saturation, finite
  sums); M2 ResidualStep + residualCut (univ.filter of ReflTransGen) + mem/source/closed;
  ★ M3 residualCut_saturates — t ∉ residualCut ⟹ the residual-reachable set IS a saturating
  cut (flowValue = cutCapacity), via two by_contra boundary arguments (forward slack ⟹
  Or.inl step; backflow ⟹ Or.inr v→u step) + M1. **ExactRT's Ford–Fulkerson gap is now
  reduced to the single sharp condition t ∉ residualCut + carried max-flow existence.**
  Std-3, budget 0. Next: M4 (t∉residualCut from maximality — attempt), M5 (carried capstone).

- **2026-07-05** — **M4+M5 LANDED — CAMPAIGN COMPLETE.** IsMaxSTFlow; exact_rt_of_maxFlow
  (maximality + carried haug ⟹ t∉residualCut, a clean 4-line reduction isolating haug as the
  named frontier); ★ exact_rt_maxFlow_mincut — THE CAPSTONE: max-flow = min-cut
  (flowValue = cutCapacity(residualCut)), conditional ONLY on the carried haug; and BONUS
  singleEdge_augment_forward — the one-edge augmentation CONSTRUCTED (g = f+ε on the edge,
  IsSTFlow re-proved, value strictly up) showing the augmentation mechanism is real, not just
  carried. THE COMBINATORIAL CONTENT OF MAX-FLOW=MIN-CUT IS MACHINE-CHECKED on the tower's
  flow/cut framework — the previously-cited Ford–Fulkerson gap is reduced to the single
  carried haug (general augmenting-path ⟹ bigger flow; the analytic frontier, single-edge
  case discharged). Std-3, budget 0. A genuine wall, mostly crossed.

- **2026-07-05** — **M6 LANDED (deepening — deriving the carried haug).** twoEdge_augment_forward:
  a two-edge forward residual path s→w→t yields a strictly larger flow — a genuine derived
  extension of the single-edge M4 template that machine-checks the INTERIOR-VERTEX CONSERVATION
  crux (w receives +ε in and emits +ε out, so vertexExcess preserved) — the exact mechanism the
  general haug needs, which single-edge never exercised. HONEST checkpoint: the general
  n-edge mixed-direction ReflTransGen-walk augmentation is still carried, with the precise
  obstruction PINNED — a ReflTransGen walk may REVISIT vertices/edges, so the naive tail-then-head
  induction fails (the tail augmentation can consume the head edge's slack); the sharpened
  frontier = extract a SIMPLE path (no-dup) from the walk + min-ε augment + max-flow existence.
  Std-3, budget 0. Max-flow is now: combinatorial core (M1-M3) + haug derived for 1- and 2-edge
  forward paths (M4/M6, incl. the conservation crux) + general-walk augmentation & existence carried.

- **2026-07-05** — **M7 LANDED (green first attempt) — the GENERAL forward simple-path
  augmentation.** ForwardAugPath structure (a degree-structured edge set P: interior
  out-deg = in-deg, s +1 out, t +1 in, forward slack on every edge) + forwardAugPath_augments:
  such a path + a uniform positive slack margin ε yields a strictly larger flow. Derived via
  the crux identity ∑ v (if P u v then ε else 0) = ε·card{v | P u v} (one line:
  ← Finset.sum_filter, sum_const, nsmul_eq_mul) + interior conservation (out-deg = in-deg ⟹
  vertexExcess preserved) + value up by ε·1 at s. This LIFTS M6's hand-built 1/2-edge cases
  to ALL forward path lengths — the augmentation mechanism is now fully derived, the M6
  vertex-revisit obstruction removed for forward paths. Carried now: (a) the extraction
  (ReflTransGen walk ⟹ a ForwardAugPath degree structure), (b) mixed forward/backward paths,
  (c) max-flow existence. Std-3, budget 0. Max-flow: combinatorial core (M1-M3) + the FULL
  forward-path augmentation mechanism (M4-M7) + only the extraction/mixed-direction/existence carried.

- **2026-07-05** — **M8 LANDED (green) — the EXTRACTION degree-structure DERIVED.**
  ForwardResidualStep (forward slack only); SimpleForwardPath (an injective Fin-indexed simple
  path s→t with per-step forward slack — injectivity IS the dedup); ★ toForwardAugPath — the
  walk→degree-structure extraction DERIVED (hDeg/hs/ht from injectivity via
  card_filter_fiber_of_injective: card{v | edge u v} = 0/1 from the injective fibre); ε
  ELIMINATED internally (forwardAugPath_augments' — min forward slack over the finite path is
  a positive ε); augment_of_simpleForwardPath — a SimpleForwardPath alone ⟹ a strictly larger
  flow (s≠t derived from injectivity). Real finding: Mathlib's Walk.bypass/toPath are
  UNDIRECTED (fromRel symmetrizes), so they cannot give a forward directed path — justifying
  the carry. So the extraction's degree-structure half is now DERIVED; the ONE remaining carry
  of it is the DIRECTED DEDUP (ReflTransGen walk ⟹ SimpleForwardPath). Std-3, budget 0.
  Max-flow: core (M1-M3) + full forward augmentation mechanism (M4-M7) + the extraction
  degree-structure (M8), carrying only the directed dedup + mixed-direction + existence.

- **2026-07-05** — **M9 LANDED (FULLY) — the directed dedup DERIVED; forward haug complete.**
  exists_isChain_list (ReflTransGen ⟹ a chain List, via head_induction_on); dedup_aux (★ the
  splice-shortens crux — a minimal-length chain list is Nodup: a repeat p a = p b lets you
  splice out the middle for a strictly shorter chain, contradicting minimality; strong
  induction on a length bound); exists_nodup_isChain_list; ★ simpleForwardPath_of_reachable
  (a forward residual walk ⟹ a SimpleForwardPath, converting the nodup chain to an injective
  Fin path) — the DIRECTED analogue of SimpleGraph.Walk.bypass, which is absent from Mathlib
  (its bypass is undirected); ★ CAPSTONE forwardReachable_augments (forward residual
  reachability + s≠t ⟹ a strictly larger flow — the forward Ford–Fulkerson haug, FULLY
  DERIVED, no carried augmentation). Std-3, budget 0. **Max-flow: the ENTIRE FORWARD side is
  now derived** (core M1-M3 + augmentation M4-M8 + directed dedup M9); only mixed
  forward/backward residual paths and max-flow EXISTENCE remain carried.

- **2026-07-05** — **M10 LANDED (green first attempt) — the MIXED-DIRECTION augmentation.**
  ResidualAugPath (typed edge sets Pf forward-residual + Pb backward-residual, the combined
  residual degree structure hDeg/hs/ht counting both) + ★ residualAugPath_augments:
  g = f + ε·(Pf indicator) − ε·(Pb-reverse indicator) yields a strictly larger flow, ALL FOUR
  IsSTFlow fields DERIVED. The ±ε conservation crux (the Pb sign bookkeeping the plan flagged
  as the likely stall) resolved cleanly via linear_combination — an outgoing residual step
  contributes +ε to excess and an incoming −ε, regardless of forward/backward type, so hDeg ⟹
  interior conservation. ForwardAugPath is now the Pb = ∅ special case. Std-3, budget 0.
  **Max-flow's entire AUGMENTATION MECHANISM (forward + mixed) is now derived**; carried:
  the mixed EXTRACTION (adapt the M8/M9 dedup to typed residual walks) + max-flow existence.

- **2026-07-05** — **M11 LANDED (COMPLETE, all 5 steps) — the general haug DERIVED and
  DISCHARGED.** SimpleResidualPath (the ResidualStep analogue of SimpleForwardPath, from
  reachability via M9's GENERIC exists_nodup_isChain_list); toResidualAugPath — the TAGGING:
  each residual step tagged Pf (forward slack) / Pb (¬slack ⟹ backflow), the disjoint-union
  card split (#Pf + #Pb = #edge, Finset.card_union_of_disjoint) reduced onto M8's fibre
  counts gives the typed degree structure; ★ residualReachable_augments — general residual
  reachability ⟹ a strictly larger flow (the FULL Ford–Fulkerson haug, DERIVED, composing the
  tagging + mixed ε + M10's residualAugPath_augments); ★★ exact_rt_maxFlow_mincut_unconditional
  — max-flow = min-cut conditional on ONLY max-flow EXISTENCE (via mem_residualCut, the haug is
  no longer carried). Std-3, budget 0. **MAX-FLOW = MIN-CUT is now machine-checked, conditional
  on ONLY the existence of a maximum flow** — the entire combinatorial + augmentation content
  (both directions) is derived. Only carry left: max-flow EXISTENCE (compactness/termination,
  the genuine analytic frontier). Next: M12 (existence via compactness of the flow polytope).

- **2026-07-05** — **M12 LANDED — ★★ CAMPAIGN COMPLETE: max-flow=min-cut is UNCONDITIONAL ★★.**
  exists_maxSTFlow — a maximum flow EXISTS: the flow set {f | IsSTFlow} ⊆ V→V→ℝ is nonempty
  (zero flow), closed (finite iInter of isClosed_le/isClosed_eq, vertexExcess continuous),
  bounded (‖f‖ ≤ ‖cap‖ via pi_norm), hence COMPACT (Metric.isCompact_of_isClosed_isBounded,
  ProperSpace (V→V→ℝ) auto-resolved from FiniteDimensional.proper_real), flowValue continuous,
  so IsCompact.exists_isMaxOn gives a maximiser. ★★ maxFlow_min_cut — the finite max-flow =
  min-cut theorem, UNCONDITIONAL (carrying ONLY cap-nonneg, the standard definitional
  hypothesis). The ENTIRE M1-M12 pipeline is machine-checked with NO carried mathematical
  hypotheses. A genuine wall — one I'd called a multi-year Mathlib library — FULLY CROSSED,
  one honest increment at a time, including a directed path-dedup theory Mathlib lacks. Std-3,
  budget 0. HONEST: the finite (V→V→ℝ) network model; NOT continuum RT, NOT QG. This also
  makes the repo's ExactRT Ford–Fulkerson gap genuinely closable (holographic entanglement =
  min-cut no longer needs to cite it). CAMPAIGN COMPLETE.
