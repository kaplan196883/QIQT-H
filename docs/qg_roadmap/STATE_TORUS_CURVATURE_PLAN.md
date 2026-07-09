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
