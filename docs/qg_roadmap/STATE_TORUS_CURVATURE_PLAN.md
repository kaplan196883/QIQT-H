# STATE-WIRE + TORUS + CURVATURE campaign — three tracks on top of the stencil chain

**Date:** 2026-07-10. **Parents:** `ISOTROPY_STENCIL_PLAN.md` (2D, COMPLETE), `DIM_GENERIC_STENCIL_PLAN.md`
(every d, COMPLETE). **User directive:** "a b and c — in the loop" = all three follow-ups, sequenced by
tractability: **A (state-wire, gluing) → C (torus, moderate) → B (curvature, research-grade, consult-first,
honest checkpoint permitted).**

## Track A — STATE→GEOMETRY→GH end-to-end (gluing; 1 brick)

Make "a d-dimensional Euclidean continuum as the OUTPUT of an entangled state" one machine-checked chain.
All pieces exist:
- `MetricFromState.explicitProfile G hq : CutRankProfile G` (crossing-count boundary, defect PROVEN) +
  `explicitProfile_rankMIGraph_eq : rankMIGraph (explicitProfile G hq) = G` + `decodedDist_eq : decodedDist =
  graphDist G` — the decoder recovers ANY decidable graph from its cut-rank profile.
- `BellCutRank.rank_bellFlattening_eq_pow_crossingCard` — the profile is realized by GENUINE entanglement:
  Bell-pair states on the edges have Schmidt rank `q^crossingCard` across every cut (+ `ReducedDensity`:
  = the reduced-density Schmidt rank).
- `StencilDimGH.stencilD_toGHSpace_tendsto_unitCube` — the stencil graph metric → Euclidean cube.

**A1 — `StencilFromState.lean`.** Instantiate at `G = stencilGraphD d N (stencilRD d N)`:
`stencilProfile d N := explicitProfile (stencilGraphD …) (q=2)`; theorems: (i) decode
`rankMIGraph (stencilProfile d N) = stencilGraphD d N (stencilRD d N)`; (ii) metric identity — the
`ScaledStencilD` intrinsic dist IS the scaled decoded dist: `dist (toScaledD x) (toScaledD y) =
(stencilRD/N)·decodedDist (stencilProfile d N) x y`; (iii) Bell grounding — the profile's boundary at every
cut is realized as a Bell-flattening rank exponent (`rank_bellFlattening_eq_pow_crossingCard` applied with
the stencil crossing-edge type); (iv) **END-TO-END CAPSTONE `state_decoded_geometry_tendsto_unitCube`**:
for every d, the metric spaces whose distance is the (scaled) state-DECODED distance converge in GH space
to the Euclidean unit cube — G4's capstone restated with the decoded metric on the nose (proved equal),
d = 3 corollary. HONEST: the state family is CONSTRUCTED to carry the stencil pattern (the dynamical
source of the entanglement stays the cited wall); everything else as before.

## Track C — the d-TORUS: same machine, different global TOPOLOGY (2–3 bricks)

Target: **the flat d-torus** `PiLp 2 (fun _ : Fin d => AddCircle (1:ℝ))` — Mathlib has
`NormedAddCommGroup (AddCircle p)` (`AddCircle.norm_eq : ‖x‖ = |x − round(p⁻¹x)·p|` = wrap distance,
`Analysis/Normed/Group/AddCircle.lean`), and `PiLp 2` gives the L² product; compact (pi of compact) +
nonempty. The limit is still FLAT — what changes is the **global topology** (no boundary, nontrivial π₁).

- **T1 — cyclic stencil graph + wrap distance.** Vertex `Fin d → ZMod N` (or Fin N with wrap). Integer
  wrap-distance per coordinate `wrapDist a b = min (a−b).val ((b−a).val)`-style (sqrt-free, symmetric);
  `sqDistT = Σ wrapDist²`; `torusGraphD d N R` (Adj = x ≠ y ∧ sqDistT ≤ R²); the torus embedding
  `x ↦ (x/N : AddCircle 1)^d` and the geodesic identity: torus dist of embedded points =
  `√(Σ (wrapDist/N)²)` (per-coordinate `AddCircle.norm_eq` + PiLp norm formula) — the analogue of the
  cast bridge. Lower bound (hop moves ≤ R) as in G1.
- **T2 — the wrap-aware rounding walk.** Choose per coordinate the minimizing lift (unwrap y to the
  representative nearest x within ±N/2), run the G2 straight-line rounding walk on the LIFTED segment in
  ℤ (reuse `seg`/`round_diff_sq_le`/Cauchy–Schwarz/`walk_of_lazy_chain`), then project mod N — projection
  preserves adjacency (wrapDist ≤ |lift difference|). Pinch + distortion as G3.
- **T3 — GH capstone `torusD_toGHSpace_tendsto_flatTorus`**: intrinsic scaled cyclic-stencil spaces →
  the flat d-torus in GH space (net = coordinate rounding on `AddCircle` representatives; same
  `ghDist_le_of_approx_subsets` skeleton). d = 3, d = 2, d = 1 (the circle) corollaries.
  CONSULT GPT-5.5 (plain) before T1 on the AddCircle/PiLp API details (norm_eq forms, compactness
  instances, quotient coercions).

## STATUS (2026-07-10)
- **Track A COMPLETE** (78d8b78f): `StencilFromState.lean` — end-to-end state→decoded-metric→GH-cube,
  packaged ∃-version + 3D headline; Bell grounding at the reduced-density Schmidt-rank level.
- **Track C COMPLETE** (T1 b2a3fe44, T2 f8d741e1, T3 b6b0c462): the flat d-torus GH limit —
  `torusD_toGHSpace_tendsto_flatTorus` ∀d, with `torus1D` (THE CIRCLE), `torus2D`, `torus3D`
  (periodic 3-space). Sharper pinch than the cube (torus diameter m/2). Topology INSERTED via the
  wrap rule — transport, not emergence.
- **Track B COMPLETE at the B1 checkpoint** (B0 consult + B1 e77a2d52): `TripodGH.lean` — the TRIPOD
  is a GH limit of subdivided star graphs (EXACT isometric embedding, ε₂ = 0, ghDist ≤ 1/(n+1)) AND
  provably embeds in NO real inner-product space (`tripod_no_isometric_embedding_into_inner`, via the
  IsotropyNoGo unique-midpoint invariant) — the first machine-checked NON-EUCLIDEAN limit in the
  program, honestly labelled (CAT(0) singular tree: non-manifold/branching, NOT positive curvature).
  **The cone with deficit angle (concentrated positive curvature) remains CITED, not attempted** —
  the consult flagged its triangle inequality/apex-unfolding as the genuine pain point.
- **CAMPAIGN COMPLETE (2026-07-10).** All three user-directed tracks (a=state-wire, b=curvature-first-
  step, c=torus) shipped axiom-free at std-3, budget 0, local commits only.

## Track B continuation — THE CONE: COMPLETE (2026-07-10)
- **B2a COMMITTED 13644d3e**: `ConeMetric.lean` — Cone θ compact metric space (two-case
  `lawCos_triangle`), **THE CURVATURE THEOREM `cone_no_isometric_embedding_into_inner` (θ < 2π)**
  via the double bisector midpoints (radius cos(θ/4), distances sin(θ/4), separation sin(θ/2) > 0,
  merging only at θ = 2π) — concentrated positive curvature 2π−θ machine-checked.
- **B2b COMMITTED d6b08e72**: `ConeGH.lean` — `polarGrid_toGHSpace_tendsto_cone`: finite polar-grid
  clouds (exact isometric pullback, ε₂ = 0; net error 1/(n+1) + θ/(2(n+2))) GH-converge to the cone.
  **The program's first positive-curvature GH limit.**
- Remaining cited (NOT attempted): the INTRINSIC graph-geodesic (rounding-walk) approximation near
  the bending apex; smooth curved surfaces (sphere etc.).

## Track B continuation (user: "continue the curvature space", 2026-07-10): THE CONE

**B2 — the cone with deficit angle: genuine CONCENTRATED POSITIVE CURVATURE.** `Cone θ` (0 < θ ≤ 2π):
apex + points (r, φ), r ∈ (0,1], φ ∈ **AddCircle θ** (reuse the torus circle machinery). Since the
angular distance δ = ‖φ₁−φ₂‖ ≤ θ/2 ≤ π, the metric is the SINGLE law-of-cosines formula
`√(r₁²+r₂²−2r₁r₂cos δ)` (apex = r→0 limit; through-apex r₁+r₂ is never shorter for θ ≤ 2π).
- **B2a — `ConeMetric.lean`**: the metric space (triangle inequality: case δ₁₂+δ₂₃ ≤ π via THREE
  EXPLICIT PLANAR POINTS + Mathlib dist_triangle + cos-monotone; case > π via `d ≥ r₁ − r₂cos δ`
  twice + `cos δ₁₂ + cos δ₂₃ ≤ 0`); compactness (continuous surjection from Icc × AddCircle θ, using
  `2−2cos δ ≤ δ²` ⟹ dist ≤ |Δr| + δ); **THE CURVATURE THEOREM `cone_no_isometric_embedding_into_inner`
  (θ < 2π)**: points at maximal angular separation θ/2 have TWO distinct metric midpoints (the two
  bisectors at radius cos(θ/4), both at distance sin(θ/4)) ⟹ the IsotropyNoGo unique-midpoint
  invariant kills every inner-product embedding. Concentrated curvature 2π−θ at the apex, as a theorem.
- **B2b — `ConeGH.lean`**: polar-grid finite clouds (radii k/(n+1) × angles j·θ/(n+1) via
  ZMod → AddCircle) with the PULLBACK metric (exact isometry, ε₂ = 0), net error ≲ (1+θ)/(n+1);
  `ghDist_cone_le`; capstone `polarGrid_toGHSpace_tendsto_cone`.
- **HONEST (binding)**: the curvature is CONCENTRATED (Alexandrov cone point, deficit 2π−θ) — NOT a
  smooth Riemann tensor; B2b's finite spaces carry the INDUCED metric (exact isometric clouds, like
  the tripod stars) — the INTRINSIC graph-geodesic (rounding-walk) version near a bending apex stays
  the CITED frontier (geodesics are no longer straight lines in any single chart); θ and the geometry
  are INPUTS; NOT GR, NOT numerical-G, NOT QG.

### B1 — the TRIPOD (metric tree): the first NON-FLAT (non-locally-Euclidean) GH limit
`Tripod := Option (Fin 3 × Ioc 0 1)` (none = apex, some (i,t) = arm point): dist none-some = t,
same-arm |s−t|, cross-arm s+t; MetricSpace by finite casework; compact via the 1-Lipschitz surjection
from `Fin 3 × Icc 0 1`. **The honesty upgrade — non-Euclideanness as a THEOREM**: reuse
`IsotropyNoGo.inner_metric_midpoint_eq_affine_midpoint` — the apex is the metric midpoint of ALL
THREE endpoint pairs (d = 2, halves = 1), forcing f(B) = f(C) in any inner-product space while
d(B,C) = 2: `tripod_no_isometric_embedding_into_inner`. GH: the subdivided star's intrinsic scaled
graph metric embeds EXACTLY (ε₂ = 0 — same-arm |k−l|/n, cross-arm (k+l)/n on the nose), grid is a
1/n-net ⟹ `ghDist ≤ 1/n → 0`; capstone `star_toGHSpace_tendsto_tripod`. HONEST LABEL (binding):
the tripod is a CAT(0) singular TREE — "non-flat" means NON-MANIFOLD / NON-LOCALLY-EUCLIDEAN /
embeds in no inner-product space; it is NOT positive curvature, NOT a curved surface, NOT smooth
Riemannian; the branching is INSERTED through the star topology. NOT GR, NOT numerical-G, NOT QG.

## Track B — CURVATURE (research-grade; consult-first; checkpoint honestly)

The stencil machine so far only produces FLAT limits. Genuine curvature needs a position-dependent
construction. **B0 (consult + scoping):** ask GPT-5.5 for the most tractable genuinely-non-flat target.
Leading candidate: **the cone with deficit angle** (curvature as a concentrated Alexandrov singularity —
the honest "first curved space": explicit metric formula via unwrapping, no smooth-manifold machinery);
alternative: a conformally-flat 2D metric `f(x)²·(dx²+dy²)` with position-dependent stencil radius
`R(x) ≈ R/f(x)` (research-grade: geodesics are no longer straight lines — the rounding-walk template
breaks; expect only partial results). **B1+ :** attempt ONLY the consult-vetted tractable core; if the
wall is real, CHECKPOINT with the exact gap (A + C are already the shipped value). NEVER fake; NEVER
claim curved-Riemannian emergence unless the theorem actually states it.

## HONEST scope firewall (binding, every commit)
- Track A: the state is CONSTRUCTED to carry the stencil correlation pattern — decoding is a theorem,
  but WHY a physical state would carry it (dynamics) stays the cited wall.
- Track C: the torus topology is INSERTED through the wrap rule, exactly as isotropy was through the
  stencil rule; the limit is FLAT; d is an INPUT.
- Track B: no curvature claim without the theorem; concentrated (Alexandrov) curvature ≠ smooth Riemann
  tensor; say which one is proved.
- All: NOT emergent dimension/topology-from-dynamics, NOT GR, NOT numerical-G, NOT QG.

## Discipline
Same as the stencil campaigns: ONE bg fable subagent per brick (own module, NO git), independent
verification (rebuild + scratchpad `#print axioms` std-3 probe + no-sorry grep) before commit; wire
`QIQTH.lean` + AxiomAudit pins; full budget check (LONG ~420000ms, budget 0); commits LOCAL ONLY —
DO NOT PUSH; explicit git paths (never `-A`, never `website/`); check sibling jobs first;
`Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`; NO sorry; hypotheses never axioms.
