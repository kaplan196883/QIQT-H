# METRIC-FROM-STATE campaign — deriving geometry as an OUTPUT of an entangled state

**Date:** 2026-07-09. **Parent:** `QG_GEOMETRY_AS_OUTPUT_PLAN.md` (Phase 1–3), refined into an execution
plan after auditing what's reusable. **Goal:** the first Lean theorem where a **metric is the OUTPUT**
of an explicit finite entangled state — moving `g` from hypothesis to conclusion.

## The pipeline (one new link; the back half is REUSE)

```
  explicit finite state ψ  ──►  cut-rank profile  ──►  adjacency graph G(ψ)  ──►  metric d_ψ = G(ψ).dist
        [Step A: NEW]              [Step A: NEW]         [Step B: NEW link]        [Step C: REUSE graphDist]
                                                          + area = min-cut         [REUSE MaxFlowMinCut/RecordMincut]
```

**Anti-circularity (binding):** the substrate/index type must depend only on `V, q` — NEVER on the
graph's edges. The graph appears only in the *state* (correlation pattern), and is *recovered* from the
state's cut-rank by strict submultiplicativity. Decoding `rankMIAdj ψ = G` must be a proved theorem,
not definitional.

## Reuse map (what's already axiom-free)
- `EmergentSpacetime.graphDist_isPseudometric` / `graphDist_isFiniteMetric` — graph → genuine metric (Step C).
- `QG/MaxFlowMinCut.exact_rt_unconditional` — flow = min-cut on the derived graph (area).
- `RecordMincut.mincut_bounds_distinguishable_records` + cut-rank/records — capacity across a cut.
- (later, Phase 6) `CHMTransport`/`ModularHamiltonianOp`/JLMS generator-sum — for δmetric ↔ δmodular-energy.

## Brick sequence (each: green `lake build`, `#print axioms` std-3, budget 0, AxiomAudit pin, LOCAL commit)

**STATUS (2026-07-09): M1–M5 + M3b + QIT layer + 2D + CONTINUUM LIMIT all DONE — axiom-free, budget 0,
full library green.** Since the M1–M5 line below, the campaign extended substantially (all committed):
- **M3b** (`BellCutRank.lean`): `rank_bellFlattening_eq_pow_crossingCard` — the area IS the Bell-state
  Schmidt rank `q^crossingCard` (genuine entanglement, flattening level).
- **QIT layer — the "cited gap" is now CLOSED** (`ReducedDensity.lean`): `schmidtRank_eq_flattening_rank`
  (rank ρ_A = rank M, ρ_A = M·Mᴴ PSD, trace = ‖ψ‖²), `partialTraceRight_pureDensity` (Tr_B|ψ⟩⟨ψ| = ρ_A),
  `bell_schmidtRank_eq_pow_crossingCard` — the area is the genuine REDUCED-DENSITY Schmidt rank. Remaining
  gap narrowed to the general MIXED-state partial-trace API (not needed for pure states).
- **2D** (`MetricRefinement2D.lean`): `square_grid_scaledDist_eq_l1` — the box-product grid metric refines
  the unit SQUARE with the L¹ (taxicab) metric; `dist_boxProd_of_reachable` (from Mathlib `edist_boxProd`).
- **CONTINUUM LIMIT — sampling upgraded to CONVERGENCE** (`ContinuumLimit.lean`): C1
  `hausdorffDist_chainGridSet_tendsto` (finite geometries → [0,1] in Hausdorff distance), C2
  `toGHSpace_chainGridNC_tendsto` (abstract finite metric spaces → [0,1] in Gromov–Hausdorff space).
  **1D limit IS Riemannian** (flat, L¹=Euclidean); ≥2D is L¹/Finsler NOT Riemannian (isotropy = the wall).

The remaining honest frontier: **isotropy** — a graph family (random-geometric / long-range) whose GH
limit is the EUCLIDEAN/Riemannian metric in ≥2D (research-grade, needs probability infra); the torus
(cycleGraph → circle, ~250–600 lines modular arithmetic); the general mixed-state partial trace; and the
dynamical source (why a physical state carries this entanglement — the genuine open wall). See
`CONTINUUM_LIMIT_UNDERSTANDING.md`.

---

**STATUS (2026-07-09): M1–M5 DONE — axiom-free, budget 0, full library green.**
`MetricFromState.lean`: `rankMIGraph_eq` (state decodes its graph), `decodedDist_isFiniteMetric`
(state-derived metric), `crossingCard_pair_defect` + `explicitProfile_rankMIGraph_eq` (crossing-count
area functional of a REAL graph decodes back to it — defect PROVEN), `crossingCard_symm` (M5: the AREA
is a property of the CUT, RT-consistent). `MetricRefinement.lean` (M4): `pathGraph_dist` (Mathlib gap
proved), `chain_scaledDist_eq_interval` (the chain's state-derived metric refines the unit interval).
Geometry-as-output is non-vacuous for real graphs AND refines a 1D continuum.
**NEXT: M3b** — the QUANTUM realization: a Bell-pair state on graph edges whose Schmidt rank across a
cut IS `q^crossingCard`, replacing the combinatorial boundary with genuine entanglement. This is the
deep step (and likely the tensor/Schmidt-rank infrastructure wall) — CONSULT GPT-5.5 on Mathlib
finite-Schmidt-rank/`TensorProduct` tractability; if it needs heavy new infra, CHECKPOINT with the
exact gap. The honest capacity-bound `records ≤ q^area` (replacing `HolographicCapacityBound`)
presupposes this quantum flattening.

- **M1 — decoder correctness (Step B core).** New file `QIQTH/MetricFromState.lean`. Given a graph
  `G : SimpleGraph V` (finite, decidable adjacency) and a `cutRank : Finset V → ℕ` with the crossing
  profile `cutRank A = q ^ crossingCard G A` (`crossingCard` = # edges with exactly one endpoint in A),
  `q ≥ 2`, prove `rankMIAdj cutRank = G`, where `rankMIAdj` has
  `Adj u v ⟺ cutRank {u} * cutRank {v} > cutRank {u,v}` (strict rank submultiplicativity = positive
  Rényi-0 mutual information; no logs). Pure graph combinatorics + `Nat` pow monotonicity. Non-circular:
  the crossing profile is the state's property (discharged in M3), decoding is a theorem.
- **M2 — metric output (Step C, reuse).** `decodedDist cutRank := (rankMIAdj cutRank).dist`; from M1 +
  connectivity, `decodedDist = G.dist` and `IsMetric decodedDist` (reuse `graphDist_isFiniteMetric`).
  Capstone corollary: for the path graph, `∃ (cutRank profile), decodedDist = interval distance` —
  geometry-as-output for an explicit 1D chain.
- **M3 — explicit state realizes the profile (Step A).** Construct an explicit finite object whose
  cut-rank IS `q ^ crossingCard G A`. FIRST the CLASSICAL version (shared-variable "complete pair
  register" indexed by `V×V`, correlated iff `{u,v}∈G`; cut-rank = product of crossing-pair
  dimensions) — pure `Fintype.card`/`Finset.prod` combinatorics, no Hilbert space. Then (M3b, if
  tractable) the Bell-pair quantum version (`cutRank` = Schmidt rank, via `tensorProduct_cutRank_mul`).
- **M4 — refinement knob.** `chainState N q`; `scaledDecodedDist N := decodedDist / (N-1)` refines the
  unit interval (`= |i/(N-1) − j/(N-1)|`, and every point of `[0,1]` within `1/(2(N-1))` of a vertex).
- **M5 — area = min-cut on the derived graph.** Tie `cutRank`/`crossingCard` to
  `exact_rt_unconditional` / `mincut_bounds_distinguishable_records`: the boundary area of `A` (log
  cut-rank / crossing count) equals the min-cut of the derived graph — capacity↔area as a theorem for
  the explicit state (replacing the `HolographicCapacityBound` typeclass in this instance).

## Honest scope firewall (every commit)
This derives a **finite spatial graph-metric from an explicit entangled state** — geometry as OUTPUT,
non-circular, axiom-free. It is NOT a continuum Riemannian metric (M4 only refines a 1D interval/lattice
metric; higher-dim curvature is research-grade), NOT GR (δmetric-from-δstate + a non-assumed first law
is the later Phase-6 wall), and it does NOT derive WHY the physical state has this entanglement (the
dynamical source stays the open wall). Carried inputs (the state's cut-rank profile, connectivity) are
HYPOTHESES/explicit constructions, NEVER axioms; NO circular/definitional discharge of the decoding.
NEVER claim continuum geometry, GR, numerical-G, or QG.

## Discipline
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<mod>` GREEN; `#print axioms` std-3; budget check
(LONG timeout ~420000ms) budget 0; AxiomAudit pins; wire into `QIQTH.lean`; commits LOCAL ONLY — DO NOT
PUSH; `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`; explicit git paths (never
`-A`); check sibling jobs first; new graph/measure files: import the Mathlib SimpleGraph/metric deps.
CONSULT GPT-5.5 (plain) before each hard brick on exact v4.30.0 SimpleGraph API. NO sorry.
