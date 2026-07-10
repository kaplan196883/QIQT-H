# STATE-WIRE-2 + SPHERE + INTRINSIC-CONE campaign — the three continuations

## STATUS (2026-07-10): CAMPAIGN COMPLETE — all three tracks, all 8 bricks, [AF] std-3, budget 0
- **Track W COMPLETE**: W1 `TorusFromState.lean` (9b64686e) — state-decoded flat d-torus ∀d, the
  CIRCLE headline (first state-decoded nontrivial topology); W2 `TripodFromState.lean` (56917bf1) —
  star SimpleGraph + geodesic identity `starGraph_dist_eq` + the first state-decoded NON-EUCLIDEAN
  limit.
- **Track S COMPLETE**: S1 `SphereMetric.lean` (864938ea) — the intrinsic great-circle sphere,
  chord↔angle bridge, `sphere_no_isometric_embedding_into_inner` (4th midpoint-invariant use);
  S2 `SphereGH.lean` (6219f8b6) — `sphereGrid_toGHSpace_tendsto_sphere`, the first SMOOTH
  curved-space GH limit (rate 3π²/(4(m+1))).
- **Track K COMPLETE (no checkpoint needed — the crux closed fully)**: K1 `ConeIntrinsicGraph.lean`
  (f5e4c557); K2 `ConeIntrinsicWalk.lean` (33aefb48) — THE CRUX: the unfolded-segment walk; the
  SECTOR LEMMA (waypoint args pinned in [0,s], s < π — the Complex.arg branch cut never approached;
  θ < 2π load-bearing) makes the pullback distance-nonexpanding; hop metric PINCHED;
  K3 `ConeIntrinsicGH.lean` (2003b4cb) — `coneIntrinsic_toGHSpace_tendsto_cone`: POSITIVE CURVATURE
  FROM PURE HOP-COUNTING; K4 `ConeFromState.lean` (184eb374) — the first state-decoded
  positive-curvature limit.
- **The two completed families**: intrinsic graph-geodesic {cube, torus, tripod, cone} and
  state-decoded {interval, cube ∀d, torus ∀d/circle, tripod, cone} — both spanning
  {flat, flat-periodic, branching, positively-curved}. Cited frontiers: sphere-intrinsic-hop,
  smooth-target intrinsic walks, the dynamical source.

**Date:** 2026-07-10. **Parents:** `STATE_TORUS_CURVATURE_PLAN.md` (A/C/B1/B2 complete: state-wire cube,
d-torus, tripod, cone). **User directive:** "1, 2 and 3" = (1) intrinsic hop-metric cone, (2) smooth
target = the sphere, (3) state-wire for the new geometries. **Sequenced by tractability: W (state-wire,
gluing) → S (sphere, one new metric space + the same GH pipeline) → K (intrinsic cone, the hard one).**

**De-risk checks done (pin v4.30.0):** `angle_le_angle_add_angle (x y z : V) : angle x z ≤ angle x y +
angle y z` EXISTS (Geometry/Euclidean/Angle/Unoriented/TriangleInequality.lean:194) — the sphere's
intrinsic triangle inequality is free. `Complex.cos_arg`/`Complex.sin_arg` exist — the intrinsic-cone
unfolding route is viable.

## Track W — state-wire the torus and the tripod (gluing; 1–2 bricks)

Mirror `StencilFromState.lean` (track A): the decoder `explicitProfile` + `rankMIGraph_eq` works for ANY
finite graph with decidable adjacency.
- **W1 — `TorusFromState.lean`**: profile of `torusGraphD d (N+1) (stencilRD d (N+1))` at q = 2;
  decode theorem; metric identity with `ScaledTorusD` (its dist IS (stencilRD/(N+1))·graph dist — same
  rfl-tight chain as the cube); Bell grounding (reuse `bell_schmidtRank_eq_pow_crossingCard`); packaged
  ∃-capstone: a Bell-realized profile family whose decoded scaled metrics GH-converge to the FLAT d-TORUS
  (+ d = 1 circle and d = 3 corollaries).
- **W2 — `TripodFromState.lean`**: the star needs an actual `SimpleGraph` first — build `starGraph n`
  (apex ∼ (i,1); (i,k) ∼ (i,k±1); decidable) and prove `(starGraph n).dist = starHop` (path-graph
  distance casework; `pathGraph_dist` machinery exists in MetricRefinement). Then profile → decode →
  metric identity via `scaledStar_dist_eq` (dist = starHop/(n+1)) → packaged ∃-capstone: decoded
  geometries → THE TRIPOD (the first state-decoded NON-EUCLIDEAN limit).
- **Cone state-wire**: NOT possible yet — the polar clouds carry the induced (non-graph) metric. It
  becomes possible exactly when track K delivers the intrinsic cone graph. Revisit after K.

## Track S — the SPHERE: the first smooth-target GH limit (2 bricks)

The intrinsic (great-circle) sphere. Mathlib's `Metric.sphere` carries the CHORD metric (extrinsic);
the intrinsic metric is `InnerProductGeometry.angle x y` (= arccos⟪x,y⟫ on unit vectors), and its
triangle inequality is Mathlib's `angle_le_angle_add_angle` — FREE.
- **S1 — `SphereMetric.lean`**: `IntrinsicSphere := {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ = 1}` with
  `dist x y := InnerProductGeometry.angle x.1 y.1`; MetricSpace (self/comm free; triangle = the Mathlib
  lemma; eq_of_dist_eq_zero: angle = 0 on unit vectors ⟹ equal — `angle_eq_zero_iff`-style: angle x y = 0
  ↔ x ≠ 0 ∧ ∃ r > 0, y = r•x; with ‖x‖=‖y‖=1 ⟹ r = 1); CompactSpace (the chord and angle topologies
  agree: chord = 2 sin(angle/2), two-sided bounds (2/π)·angle ≤ chord ≤ angle ⟹ the identity map from
  the chord-metric sphere (compact: closed bounded subtype of ℝ³... Metric.sphere compact) is a
  homeomorphism — or directly: continuous surjection from the chord sphere via the ≤-Lipschitz bound
  angle ≤ (π/2)·chord); **THE CURVATURE THEOREM `sphere_no_isometric_embedding_into_inner`**: the SAME
  unique-midpoint invariant, fourth use — the north/south poles (distance π) have MANY metric midpoints:
  any two distinct equator points (each at angle π/2 from both poles, at positive distance from each
  other) ⟹ no inner-product embedding. Positive curvature EVERYWHERE (not just concentrated) — but state
  honestly: the THEOREM is still just non-flatness via midpoints; "curvature +1 everywhere" is the
  citation, not the formalized statement.
- **S2 — `SphereGH.lean`**: lat-long finite clouds (poles + grid θ_i = i·π/m, φ_j = j·2π/m via the
  AddCircle/ZMod machinery, embedded as unit vectors (sin θ cos φ, sin θ sin φ, cos θ)) with the PULLBACK
  metric (exact isometry); net lemma (every unit vector within O(1/m) in ANGLE of a grid point — round
  θ = arccos z and the azimuth; the chord→angle bound converts coordinate rounding to angle error);
  `ghDist_sphere_le` (ε₂ = 0); CAPSTONE `latLongGrid_toGHSpace_tendsto_sphere` — **the first SMOOTH
  curved-space GH limit** (honest label: smooth as a SPACE; the formalized non-flatness is the midpoint
  obstruction, not a Riemann tensor).

## Track K — the INTRINSIC hop-metric cone (the hard one; 3 bricks; θ < 2π)

The honest upgrade of B2b: a geometric GRAPH on the polar grid (adjacency = cone distance ≤ ρ_n,
decidable up to real-comparison decidability — use a RATIONAL/squared test or `Classical.dec` +
noncomputable adjacency with `DecidableRel` via `Classical.decPred`... design choice: adjacency via the
SQUARED law-of-cosines radicand ≤ ρ² — still real-valued; decidability is NOT needed for the metric
(SimpleGraph.dist works classically); the explicitProfile decoder needs DecidableRel — obtain it via
`Classical.dec` instance (the decoder is about math content, not computation)). Whose INTRINSIC scaled
hop metric GH-converges to `Cone θ`.
- **K1 — `ConeIntrinsicGraph.lean`**: the geometric graph `coneGraph θ n ρ` on `PolarGrid θ n` (Adj =
  x ≠ y ∧ coneDist ≤ ρ); LOWER bound (hop moves ≤ ρ ⟹ coneDist ≤ ρ·hops, walk induction — the G1
  pattern verbatim); the mesh lemma (the grid is an ε_n-net with ε_n = 1/(n+1) + θ/(2(n+2)), from B2b's
  cone_net).
- **K2 — `ConeIntrinsicWalk.lean` (THE CRUX)**: the unfolded-segment walk. For grid points P₁ = (r₁,φ₁),
  P₂ = (r₂,φ₂) with angular distance δ = ‖φ₁−φ₂‖ ≤ θ/2 < π: unfold to the plane (P₁ at angle 0, P₂ at
  angle δ — real representatives), take the straight segment, waypoints at spacing ρ − 2ε; convert each
  planar waypoint (x,y) back to polar via **`Complex.arg`** (r_i = ‖(x,y)‖ > 0 — the segment misses the
  origin since δ < π; α_i = arg(x + yI), with `Complex.cos_arg`/`sin_arg` giving r_i·cos α_i = x etc.);
  the cone points Q_i = (r_i, φ₁ + (α_i : AddCircle θ)). KEY ESTIMATES: consecutive cone distance =
  lawCos r_i r_{i+1} ‖α_i − α_{i+1}‖ ≤ lawCos r_i r_{i+1} |α_i − α_{i+1}| (AddCircle norm ≤ |repr| +
  F3 monotone) = planar distance of consecutive waypoints (the F4 planar identity, both directions) =
  spacing. Snap each Q_i to the grid (ε mesh, the Lipschitz bound coneDist_fromPolar_le) ⟹ consecutive
  snapped ≤ ρ ⟹ walk of ≤ ⌈d/(ρ−2ε)⌉ hops. Also r_i ≤ max r₁ r₂ ≤ 1 (segment convexity of the norm)
  and the endpoints snap exactly. Connectivity + `coneDist ≤ ρ·hops` + `hops ≤ d/(ρ−2ε) + 1`.
- **K3 — `ConeIntrinsicGH.lean`**: schedule ρ_n → 0 with ε_n/ρ_n → 0 (e.g. ρ_n = √ε_n-ish or
  ρ_n = (n+1)^{−1/2} against ε_n ~ (n+1)^{−1}); the pinch ⟹ uniform distortion → 0 (the G3 pattern);
  the intrinsic type synonym with the scaled hop MetricSpace (the G4/T3 pattern); ghDist via
  ghDist_le_of_approx_subsets (ε₂ = distortion, ε₃ = mesh); CAPSTONE
  `coneIntrinsic_toGHSpace_tendsto_cone (θ < 2π)` — **positive curvature from PURE HOP-COUNTING**.
  Then (K4, optional if green) the cone state-wire: profile of coneGraph decodes it (Classical
  DecidableRel), closing track W's cone gap.
- CHECKPOINT PERMISSION: K2 is research-grade (arg manipulations along a segment). If a genuine wall
  appears after a real attempt, checkpoint precisely — W + S + K1 are already shipped value.

## HONEST scope firewall (binding, every commit)
- All geometric structure (wrap, branching, deficit angle, roundness) is INSERTED through the
  rules/definitions and TRANSPORTED to the limits — nothing emerges; d, θ, the sphere are INPUTS.
- The states (track W) are CONSTRUCTED to carry the patterns; the dynamical source stays the open wall.
- The sphere's formalized non-flatness = the midpoint obstruction (an inner-product no-embedding
  theorem), NOT a formalized Riemann tensor or sectional-curvature computation.
- The intrinsic cone (track K) inserts the cone geometry through the adjacency rule (coneDist ≤ ρ),
  exactly as the stencil inserted isotropy.
- NOT GR, NOT numerical-G, NOT QG.

## Discipline
Unchanged: ONE bg fable subagent per brick (own module, NO git); independent verification (rebuild +
scratchpad `#print axioms` std-3 probe + no-sorry grep); AxiomAudit pins; wire `QIQTH.lean`; full budget
check (LONG ~420000ms, budget 0); commits LOCAL ONLY — DO NOT PUSH; explicit git paths; NO sorry;
hypotheses never axioms; checkpoint precisely at genuine walls.
