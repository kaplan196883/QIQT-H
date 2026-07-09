# DIMENSION-GENERIC STENCIL campaign — the EUCLIDEAN d-cube limit for EVERY d (3D included)

**Date:** 2026-07-09. **Parent:** `ISOTROPY_STENCIL_PLAN.md` (2D campaign COMPLETE: I1–I4, commits
793b122e / 02eb65bd / c8230d0e / 9ce66683). **Trigger:** user asked "and 3D?" — the honest answer is
"same proof, port not research"; this campaign does it ONCE for all d, with d = 3 as an explicit corollary.

## Goal

For every dimension `d ≥ 1`: the lattice `{0..N}^d` (vertex type `Fin d → Fin (N+1)`), with edges given
by the integer Euclidean-ball stencil `Σᵢ (xᵢ−yᵢ)² ≤ R²` and the intrinsic scaled hop metric
`(R_N/N)·hopDist`, converges in **Gromov–Hausdorff space to the Euclidean unit cube**
`([0,1]^d, ‖·‖₂) ⊂ EuclideanSpace ℝ (Fin d)`. Explicit corollaries at `d = 2` (consistency with the
2D campaign) and **`d = 3` (the headline)**.

## The one new ingredient vs 2D: the margin

2D used safety margin 2 (rounding moves each endpoint ≤ √2/2). Generic d:

- `margin d := Nat.sqrt d + 1` — **sqrt-free** ℕ definition with `d < (margin d)²`, hence
  `(Real.sqrt d) ≤ margin d` (via `Nat.lt_succ_sqrt`).
- Per-coordinate rounding estimate (same as I2): `(Δround)² ≤ (Δreal)² + 2|Δreal| + 1`.
- Sum over d coordinates + **Cauchy–Schwarz** `(Σ|Δreal_i|)² ≤ d·Σ(Δreal_i)²`:
  `Σ(Δround_i)² ≤ (R−m)² + 2·√d·(R−m) + d ≤ (R−m)² + 2m(R−m) + m² = R²` using `√d ≤ m` twice.
  So chunks of Euclidean length ≤ `R − margin d` round to adjacent lattice points — the walk closes
  with `≤ ⌈eucl/(R−m)⌉` hops whenever `R ≥ margin d + 1`.
- Diameter: `eucl ≤ √d·N ≤ (margin d)·N` (uniformizes the distortion error).
- Net: coordinate rounding puts every cube point within `√d/(2N) ≤ (margin d)/N` of the grid.
- Schedule `R_N = Nat.sqrt N` as before; for each FIXED d, eventually `R_N ≥ margin d + 1`, and the
  distortion error (shape `(margin d)²/(√N − margin d) + √N/N`-ish) → 0.

Everything else is the 2D proof with `Fin 2`-sums replaced by `Finset.sum` over `Fin d`.

## Reuse (verbatim or near)

- `QIQTH.StencilWalk.walk_of_lazy_chain` — already generic in the graph/vertex type: REUSE as-is.
- `round_diff_sq_le`-style per-coordinate bounds (I2) — same statements, reuse or restate.
- The I4 GH pipeline (`ghDist_le_of_approx_subsets` with s = univ, ε₁ = 0; type-synonym MetricSpace;
  `Finite.compactSpace`; `tendsto_iff_dist_tendsto_zero` + squeeze) — same skeleton, `Fin d` target.
- `EuclideanSpace ℝ (Fin d)` elements: WithLp is a structure — build points via `WithLp.toLp`/the
  `!₂[..]`-free route (`(WithLp.equiv 2 _).symm fun i => …` or `WithLp.toLp 2 fun i => …`).

## STATUS (2026-07-10): CAMPAIGN COMPLETE — G1 + G2 + G3 + G4 all DONE, axiom-free std-3, budget 0, committed local

- **G1** `StencilDimGraph.lean` (81e23a80): d-lattice graph, margin lemmas, lower bound, diameter.
- **G2** `StencilDimWalk.lean` (560196bc): the d-dimensional rounding walk; closing estimate
  `(R−m)² + 2m(R−m) + m² = R²` via Cauchy–Schwarz + `√d ≤ m` + `d < m²`; connectivity; pinch.
- **G3** `StencilDimDistortion.lean` (075113f5): uniform pinch, `distortionErrorD = m²/(√N−m) + √N/N → 0`,
  uniform-in-pair convergence for every fixed d.
- **G4** `StencilDimGH.lean` (6b9a7e4d): **CAPSTONE `stencilD_toGHSpace_tendsto_unitCube` — for EVERY
  dimension d, the intrinsic scaled stencil graph-metric spaces GH-converge to the flat EUCLIDEAN unit
  cube `[0,1]^d`**; explicit `stencil3D_toGHSpace_tendsto_unitCube` (the headline) and `stencil2D`
  (recovers I4). Quantitative: `ghDist ≤ distortionErrorD d N/2 + margin d/N`.
- All four bricks landed FIRST-BUILD GREEN (the 2D campaign was a faithful template). Honesty firewall
  in every header: **d is an INPUT, not emergent**; isotropy inserted via the stencil rule; FLAT.

## Brick sequence (each: green build, `#print axioms` std-3, budget 0, AxiomAudit pin, wire QIQTH.lean, LOCAL commit)

- **G1 — `StencilDimGraph.lean`: graph + margin + LOWER bound.** `sqDistD d N x y : ℤ := Σᵢ (xᵢ−yᵢ)²`;
  `stencilGraphD d N R : SimpleGraph (Fin d → Fin (N+1))` (Adj = `x ≠ y ∧ sqDistD ≤ R²`, decidable);
  `embD : (Fin d → Fin (N+1)) → EuclideanSpace ℝ (Fin d)`; `euclD = dist ∘ embD`; `euclD_eq_sqrt`;
  `margin d := Nat.sqrt d + 1` + `lt_margin_sq : d < (margin d)^2` + `sqrt_le_margin : Real.sqrt d ≤ margin d`;
  `euclD_le_of_adj` (hop ≤ R); `euclD_le_R_mul_dist` (walk induction; `Reachable` HYPOTHESIS until G2);
  diameter `euclD_le_margin_mul_N : euclD x y ≤ margin d * N`.
- **G2 — `StencilDimWalk.lean`: the generic rounding walk (crux).** Segment waypoints per coordinate;
  per-coordinate `(Δround)² ≤ (Δreal)² + 2|Δreal| + 1`; Cauchy–Schwarz step
  `(Σ|aᵢ|)² ≤ d·Σaᵢ²` (Mathlib `Finset.sq_sum_le_card_mul_sum_sq` or prove via `inner_mul_le_norm_mul_norm`);
  the closing estimate `Σ(Δround)² ≤ (R−m)² + 2√d(R−m) + d ≤ R²` for `R ≥ m+1`, `√d ≤ m`;
  `stencilD_walk_exists (hR : margin d + 1 ≤ R) : ∃ w, w.length ≤ ⌈euclD/(R−(margin d))⌉₊`;
  `stencilD_reachable` (discharges G1's hypothesis); `stencilD_dist_le : (dist:ℝ) ≤ euclD/(R−m) + 1`.
  REUSE `walk_of_lazy_chain`. Box-membership of rounded waypoints via per-coordinate clamp (I2's `wayPt` pattern).
- **G3 — `StencilDimDistortion.lean`: pinch + schedule + limit (per fixed d).** `scaledD_dist_pinch`
  (`euclD/N ≤ (R/N)·dist ≤ euclD/N + error`, error uniform via the diameter bound);
  `distortionErrorD d N` (explicit, shape `m²/(√N−m) + m·√N/N`-ish — derive the exact constants);
  `scaledD_dist_sub_euclD_le` (for N past a d-dependent threshold, e.g. `(margin d + 1)² ≤ N`);
  `distortionErrorD_tendsto_zero (d)`; `stencilD_scaled_metric_tendsto_euclD (d)` (∀ε>0 ∃N₀ ∀N≥N₀ ∀xy, uniform).
- **G4 — `StencilDimGH.lean`: CAPSTONE.** `stencilRD N = max (margin d + 1) (Nat.sqrt N)`; type synonym
  `ScaledStencilD d N` with intrinsic MetricSpace (N = 0 singleton; connectivity from G2);
  `unitCube d ⊆ EuclideanSpace ℝ (Fin d)` compact+nonempty (closed ∩ bounded, ⊆ closedBall 0 (margin d + 1));
  `ΦembD` + `dist_ΦembD = euclD/N`; `unitCubeD_net` (grid is `(margin d)/N`-net via coordinate rounding);
  `ghDist_stencilD_le`; **capstone `stencilD_toGHSpace_tendsto_unitCube (d) : Tendsto
  (fun N => toGHSpace (ScaledStencilD d N)) atTop (𝓝 (toGHSpace ↥(unitCube d)))` for EVERY d**;
  explicit named corollaries **`stencil3D_toGHSpace_tendsto_unitCube` (d = 3)** and d = 2.

## HONEST scope firewall (binding, every commit)

- **Dimension d is an INPUT** (the chosen lattice), NOT emergent — this campaign says nothing about why
  space is 3-dimensional; deriving d is a genuinely open, deeper question. State this always.
- Isotropy is inserted **through the stencil rule** (Euclidean-ball edge test) — NOT emergence from a
  fixed local rule (impossible per `IsotropyNoGo`) nor from dynamics (the cited wall).
- Edges microscopic: `R_N → ∞`, `R_N/N → 0`.
- The limit is the FLAT cube — NOT curved Riemannian, NOT emergent topology, NOT GR, NOT numerical-G, NOT QG.

## Discipline

`~/.elan/bin/lake build QIQTH.<mod>` GREEN; `#print axioms` std-3 (independent scratchpad probe);
`bash lean/mathlib/scripts/axiom_budget_check.sh` (LONG ~420000ms) budget 0; AxiomAudit pins; wire
`QIQTH.lean`; commits LOCAL ONLY — DO NOT PUSH; `Co-Authored-By: Claude Opus 4.8 (1M context)
<noreply@anthropic.com>`; explicit git paths (never `-A`, never `website/`); check sibling jobs first;
ONE bg fable subagent per brick (own module, NO git), verified INDEPENDENTLY before commit; NO sorry;
carried inputs as HYPOTHESES never axioms; checkpoint precisely at any genuine Mathlib gap.
