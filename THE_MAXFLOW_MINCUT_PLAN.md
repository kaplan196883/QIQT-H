# THE MAX-FLOW–MIN-CUT CAMPAIGN — discharge ExactRT's Ford–Fulkerson gap (M1–M5)

**Status:** ACTIVE (2026-07-05). **Loop:** fe280fa3. **Commits LOCAL ONLY** (session no-push).
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
- [ ] **M4 — `IsMaxFlow f ⟹ t ∉ residualCut cap f s`** (augmenting-path value bump along a
  ReflTransGen walk). Risk MODERATE-HIGH (walk induction, the augment construction). Attempt;
  checkpoint honestly if the augment bump stalls.
- [ ] **M5 — existence of a max flow (CARRIED).** `∃ f, IsSTFlow ∧ maximal` — compactness over
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
