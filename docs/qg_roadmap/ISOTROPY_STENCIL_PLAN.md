# ISOTROPY campaign — toward a EUCLIDEAN (Riemannian) ≥2D continuum limit (increasing stencil)

**Date:** 2026-07-09. **Parent:** `CONTINUUM_LIMIT_UNDERSTANDING.md`, `METRIC_FROM_STATE_PLAN.md`.
**Companion no-go (proved):** `IsotropyNoGo.lean` — the taxicab plane embeds in NO inner-product space
(unique-midpoint invariant), so NO fixed bounded-degree lattice can give a Riemannian ≥2D limit
(square→L¹, king→L^∞, weighted diagonals→octagon — all polyhedral norms).

## The route (GPT-5.5-pro triaged): deterministic INCREASING STENCIL

Fixed stencils are dead (no-go). Randomness (RGG) is research-grade (concentration/coverage infra
Mathlib lacks). The tractable positive route is **deterministic**: on the lattice `{0..N}²`, connect
`x ~ y` iff `0 < ‖x−y‖₂ ≤ R` (the stencil = all lattice offsets in a Euclidean disk of radius `R`).
As `R → ∞` with `R/N → 0` (edges stay microscopic), the **unweighted hop metric scaled by `R/N`**
converges to the **Euclidean** distance — the allowed directions fill the disk, restoring isotropy.

- **Lower bound (easy):** each hop moves ≤ `R` in `‖·‖₂` ⟹ `‖x−y‖₂ ≤ R·hops` (walk induction, the
  same pattern as `natDist_le_walk_length`) ⟹ `(R/N)·hops ≥ ‖x−y‖₂/N`.
- **Upper bound (the crux):** round the straight segment `x→y` into chunks of Euclidean length
  ≤ `R−√2`; lattice-round each waypoint (rounding moves a point ≤ `√2/2·2 = √2`), so consecutive
  rounded points differ by ≤ `R` ⟹ a walk of `≤ ⌈‖x−y‖₂/(R−√2)⌉` hops ⟹
  `(R/N)·hops ≤ (R/(R−√2))·‖x−y‖₂/N + R/N`.
- **Distortion:** `‖x−y‖₂/N ≤ (R/N)·dist ≤ (R/(R−√2))·‖x−y‖₂/N + R/N` — Euclidean up to factor
  `R/(R−√2) → 1` and additive `R/N → 0`.

## HONEST scope firewall (binding, every commit)

- The isotropy is inserted **through the stencil rule** (the Euclidean disk `‖x−y‖₂ ≤ R` selects the
  edges). The graph *metric* is intrinsic (hop geodesics), and the limit is genuinely Euclidean — but
  this is NOT "isotropy emerging from a fixed local combinatorial rule" (that is impossible for fixed
  stencils, per the no-go, and open for random/dynamical rules — the cited wall). State this always.
- Edges must stay microscopic: `R_N → ∞` AND `R_N/N → 0` (else the complete-graph/extrinsic cheat).
- NOT curved Riemannian (the limit is FLAT Euclidean), NOT dimension/topology emergence, NOT the
  dynamical source, NOT GR, NOT numerical-G, NOT QG.

## Brick sequence (each: green build, `#print axioms` std-3, budget 0, AxiomAudit pin, LOCAL commit)

- **I1 — the stencil graph + LOWER bound.** `stencilGraph N R : SimpleGraph (Fin (N+1) × Fin (N+1))`
  with `Adj x y ↔ x ≠ y ∧ ‖x−y‖₂ ≤ R` (state via squared integer norm `(dx² + dy² ≤ R²)` to stay in
  `ℕ`/`ℤ` — avoid `Real.sqrt` in the adjacency). Lower bound `euclid x y ≤ R·(stencilGraph N R).dist x y`
  by walk induction (each edge moves ≤ R). Tractable now.
- **I2 — the UPPER bound (crux).** Construct the segment-rounding walk: `≤ ⌈‖x−y‖₂/(R−2)⌉`-ish hops
  (use a safety margin ≥ √2 rounded up to 2 to stay in ℕ/ℤ arithmetic). The walk construction is the
  heavy part (lattice rounding of segment waypoints + staying inside the box `{0..N}²` — convexity of
  the box keeps waypoints inside). Fable-subagent OK; verify independently.
- **I3 — the DISTORTION theorem + limit.** Package: for `R_N = ⌊√N⌋` (so `R_N→∞`, `R_N/N→0`),
  `(R_N/N)·dist` converges to the Euclidean distance uniformly on the unit square's grid points.
- **I4 — GH convergence to the EUCLIDEAN square.** Reuse the C1/C2 pipeline (`hausdorffDist_le_of_mem_dist`,
  `ghDist_le_nonemptyCompacts_dist`): the stencil geometries converge in Gromov–Hausdorff space to
  `([0,1]², ‖·‖₂)` — a genuine flat **Riemannian** (Euclidean) 2D continuum limit from graph geodesics.
  This is the positive complement of the no-go.
- **(cited, NOT attempted)** the RGG/random route; isotropy from a local/dynamical rule; curvature.

## Discipline
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<mod>` GREEN; `#print axioms` std-3; budget check
(LONG timeout ~420000ms) budget 0; AxiomAudit pins; wire `QIQTH.lean`; commits LOCAL ONLY — DO NOT PUSH;
`Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`; explicit git paths (never `-A`,
never `website/`); check sibling jobs first; CONSULT GPT-5.5 (plain) before each hard brick; NO sorry;
carried inputs as HYPOTHESES never axioms; checkpoint precisely at any genuine Mathlib gap.
