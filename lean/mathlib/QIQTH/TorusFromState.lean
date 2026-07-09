/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# TORUS FROM STATE — the end-to-end chain: entangled-state profile → decoded graph →
decoded metric → GH limit = the FLAT d-TORUS (track W brick 1)

Brick W1 of the STATE-WIRE-2 track (`docs/qg_roadmap/STATEWIRE2_SPHERE_INTRINSIC_CONE_PLAN.md`):
the **composition** of three previously proven, axiom-free layers, glued at
`G = torusGraphD` — the torus mirror of the cube state-wire brick
(`QIQTH/StencilFromState.lean`):

    Bell state ──► cut-rank profile ──► decoded graph ──► decoded metric ──► GH limit = (ℝ/ℤ)ᵈ
    (BellCutRank +      (this file:       (MetricFromState  (MetricFromState   (TorusStencilGH
     ReducedDensity:    `torusProfile`,    `rankMIGraph_eq`:  `decodedDist`:     `torusD_toGHSpace_
     Schmidt rank =     the crossing-      `torusProfile_     `scaledTorus_      tendsto_flatTorus`:
     q^boundary)        count profile)     decodes`)          dist_eq_decoded`)  the capstone)

Each arrow is a theorem proved in an earlier file — here they are composed at the d-dimensional
CYCLIC (wrap-around) stencil graph:

* `torusProfile d N` — the explicit crossing-count cut-rank profile (bond dimension `q = 2`)
  of the cyclic stencil graph `torusGraphD d (N+1) (stencilRD d (N+1))`
  (`MetricFromState.explicitProfile`).
* `torusProfile_decodes` — **THE DECODE**: the profile's strict rank-submultiplicativity
  pattern recovers the cyclic stencil graph, `rankMIGraph (torusProfile d N) = torusGraphD …`
  (`MetricFromState.rankMIGraph_eq`, a theorem, not a definition).
* `scaledTorus_dist_eq_decoded` — **THE METRIC IDENTITY**: the intrinsic scaled cyclic-stencil
  metric of `TorusStencilGH` IS the state-decoded metric, rescaled:
  `dist x y = (R_{N+1}/(N+1)) · decodedDist (torusProfile d N) x y`.
* `torusProfile_boundary_realized` — **THE BELL GROUNDING**: across EVERY cut `A`, the
  profile's boundary exponent is realized as the genuine reduced-density Schmidt rank of an
  explicit Bell-pair product state (`ReducedDensity.bell_schmidtRank_eq_pow_crossingCard`).
* `state_decoded_geometry_tendsto_flatTorus` (+ the packaged `'` version, the `d = 1` CIRCLE
  corollary and the `d = 3` corollary) — **THE END-TO-END CAPSTONE**: there is a family of
  cut-rank profiles, realized by Bell entanglement, whose decoded, scaled metrics are exactly
  the metrics of a sequence of finite spaces converging in Gromov–Hausdorff space to the FLAT
  d-TORUS `(ℝ/ℤ)ᵈ` with the L² metric.

**The new content vs the cube brick**: the state-decoded geometry now carries NONTRIVIAL
GLOBAL TOPOLOGY — the limit has no boundary and nontrivial fundamental group (`π₁ ≠ 0`; at
`d = 1` it is THE CIRCLE `S¹ = ℝ/ℤ`) — the first state-decoded limit with nontrivial topology.

## Scope firewall (HONEST)

* **The topology is INSERTED, not emergent.**  The nontrivial global topology enters through
  the wrap rule (the `ZMod` cyclic structure) of the graph the state is built on: the
  state/profile is CONSTRUCTED to carry the cyclic correlation pattern.  The decoding is a
  theorem, but WHY a physical state would carry exactly this entanglement — the dynamical
  source of the profile — remains the cited open wall.  Nothing here derives the state (or
  its topology) from dynamics.
* **The dimension `d` is an INPUT** — the chosen lattice — NOT emergent; the theorem holds for
  every `d` and says nothing about why physical space is 3-dimensional.
* **The limit is FLAT** — vs the cube brick the topology changed, the curvature did NOT; the
  flat torus is not a curved Riemannian manifold.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.TorusStencilGH
import QIQTH.MetricFromState
import QIQTH.BellCutRank
import QIQTH.ReducedDensity

namespace QIQTH.TorusFromState

open QIQTH.TorusStencilGraph QIQTH.TorusStencilGH QIQTH.StencilDimGH QIQTH.MetricFromState
  Filter Topology

/-! ## 1 — the crossing-count cut-rank profile of the cyclic stencil graph -/

/-- **The torus profile**: the explicit crossing-count cut-rank profile of the d-dimensional
cyclic stencil graph at bond dimension `q = 2` — boundary = the genuine edge-crossing count,
defect PROVEN (`crossingCard_pair_defect`), no carried hypotheses. -/
def torusProfile (d N : ℕ) :
    QIQTH.MetricFromState.CutRankProfile (torusGraphD d (N + 1) (stencilRD d (N + 1))) :=
  explicitProfile _ (le_refl 2)

/-- The profile's boundary function is the cyclic stencil graph's crossing-edge count
(definitional). -/
@[simp] lemma torusProfile_boundary (d N : ℕ) (A : Finset (Fin d → ZMod (N + 1))) :
    (torusProfile d N).boundary A
      = QIQTH.MetricFromState.crossingCard (torusGraphD d (N + 1) (stencilRD d (N + 1))) A :=
  rfl

/-! ## 2 — THE DECODE: the profile recovers the cyclic stencil graph -/

/-- **THE DECODE.**  The strict rank-submultiplicativity pattern of the torus profile — the
positive Rényi-0 mutual-information adjacency — recovers the cyclic stencil graph exactly:
`rankMIGraph (torusProfile d N) = torusGraphD d (N+1) (stencilRD d (N+1))`.  The graph — and
with it the wrap-around topology — is an OUTPUT of the cut-rank data (a theorem,
`rankMIGraph_eq`, not a definition). -/
theorem torusProfile_decodes (d N : ℕ) :
    rankMIGraph (torusProfile d N) = torusGraphD d (N + 1) (stencilRD d (N + 1)) :=
  rankMIGraph_eq (torusProfile d N)

/-! ## 3 — THE METRIC IDENTITY: the GH-converging metric IS the decoded metric -/

/-- **THE METRIC IDENTITY.**  The intrinsic scaled cyclic-stencil metric of `TorusStencilGH` —
the very metric whose spaces GH-converge to the flat d-torus — is exactly the state-decoded
metric of the torus profile, rescaled by `R_{N+1}/(N+1)`:

    dist (toScaledT x) (toScaledT y) = (R_{N+1}/(N+1)) · decodedDist (torusProfile d N) x y.

Both sides unfold to `(R_{N+1}/(N+1)) · (torusGraphD …).dist x y`: the left by
`scaledTorusD_dist_eq`, the right by `decodedDist_eq` + `torusProfile_decodes` +
`graphDist G x y = (G.dist x y : ℝ)`. -/
theorem scaledTorus_dist_eq_decoded (d N : ℕ) (x y : Fin d → ZMod (N + 1)) :
    dist (toScaledT x : ScaledTorusD d N) (toScaledT y)
      = ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
          * QIQTH.MetricFromState.decodedDist (torusProfile d N) x y := by
  rw [scaledTorusD_dist_eq, decodedDist_eq]
  rfl

/-! ## 4 — THE BELL GROUNDING: the boundary exponent is a genuine Schmidt rank -/

/-- **THE BELL GROUNDING.**  Across EVERY cut `A`, the torus profile's boundary function is
realized as the genuine reduced-density Schmidt rank of an explicit Bell-pair product state
(one 2-dimensional maximally-entangled pair per crossing edge):
`schmidtRank = 2 ^ boundary A`.  The decoded geometry's "area" is honest entanglement, not
merely a combinatorial count (`ReducedDensity.bell_schmidtRank_eq_pow_crossingCard`). -/
theorem torusProfile_boundary_realized (d N : ℕ) (A : Finset (Fin d → ZMod (N + 1))) :
    QIQTH.ReducedDensity.schmidtRank
        (QIQTH.BellCutRank.bellFlattening ℂ 2 (Fin ((torusProfile d N).boundary A)))
      = 2 ^ (torusProfile d N).boundary A := by
  rw [torusProfile_boundary]
  exact QIQTH.ReducedDensity.bell_schmidtRank_eq_pow_crossingCard 2 _ A (Fintype.card_fin _)

/-! ## 5 — THE END-TO-END CAPSTONE -/

/-- **THE END-TO-END CAPSTONE (state-decoded geometry → the flat d-torus).**  The finite
metric spaces GH-converging to the flat d-torus are, pointwise-provably
(`scaledTorus_dist_eq_decoded`), the spaces of the STATE-DECODED metric: the metric decoded
from the crossing-count cut-rank profile `torusProfile d N`, whose boundary exponents are
genuine Bell-state Schmidt ranks (`torusProfile_boundary_realized`).  The convergence itself
is `torusD_toGHSpace_tendsto_flatTorus` (brick T3); the packaged version
`state_decoded_geometry_tendsto_flatTorus'` carries the decoding formally in the statement. -/
theorem state_decoded_geometry_tendsto_flatTorus (d : ℕ) :
    Filter.Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledTorusD d N)) Filter.atTop
      (𝓝 (GromovHausdorff.toGHSpace (FlatTorus d))) :=
  torusD_toGHSpace_tendsto_flatTorus d

/-- **THE PACKAGED CAPSTONE.**  There is a family of cut-rank profiles — realized by explicit
Bell entanglement across every cut — whose decoded, scaled metrics are EXACTLY the metrics of
a sequence of finite spaces converging in Gromov–Hausdorff space to the FLAT d-TORUS
`(ℝ/ℤ)ᵈ` with the L² metric: entangled-state profile → decoded graph → decoded metric →
continuum limit with nontrivial global topology, every arrow a theorem.  (The topology is
inserted through the wrap rule the profile is built on — see the scope firewall.) -/
theorem state_decoded_geometry_tendsto_flatTorus' (d : ℕ) :
    ∃ P : ∀ N, QIQTH.MetricFromState.CutRankProfile
        (torusGraphD d (N + 1) (stencilRD d (N + 1))),
      (∀ N (x y : Fin d → ZMod (N + 1)),
        dist (toScaledT x : ScaledTorusD d N) (toScaledT y)
          = ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
              * QIQTH.MetricFromState.decodedDist (P N) x y) ∧
      Filter.Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledTorusD d N)) Filter.atTop
        (𝓝 (GromovHausdorff.toGHSpace (FlatTorus d))) :=
  ⟨fun N => torusProfile d N, fun N x y => scaledTorus_dist_eq_decoded d N x y,
    torusD_toGHSpace_tendsto_flatTorus d⟩

/-- **THE CIRCLE HEADLINE (d = 1)**: a Bell-profile family whose decoded geometry converges in
Gromov–Hausdorff space to THE CIRCLE `S¹ = ℝ/ℤ` — the first state-decoded limit carrying
nontrivial TOPOLOGY (no boundary, `π₁ = ℤ`).  (The cyclic topology is CHOSEN through the wrap
rule, not derived.) -/
theorem state_decoded_geometry_tendsto_circle :
    ∃ P : ∀ N, QIQTH.MetricFromState.CutRankProfile
        (torusGraphD 1 (N + 1) (stencilRD 1 (N + 1))),
      (∀ N (x y : Fin 1 → ZMod (N + 1)),
        dist (toScaledT x : ScaledTorusD 1 N) (toScaledT y)
          = ((stencilRD 1 (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
              * QIQTH.MetricFromState.decodedDist (P N) x y) ∧
      Filter.Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledTorusD 1 N)) Filter.atTop
        (𝓝 (GromovHausdorff.toGHSpace (FlatTorus 1))) :=
  state_decoded_geometry_tendsto_flatTorus' 1

/-- **THE HEADLINE (d = 3)**: the state-decoded geometry of the 3-dimensional cyclic-stencil
profiles GH-converges to the flat 3-torus — 3D space with periodic topology.  (The dimension 3
and the periodic topology are both CHOSEN, not derived.) -/
theorem state_decoded_geometry_tendsto_flatTorus_3D :
    ∃ P : ∀ N, QIQTH.MetricFromState.CutRankProfile
        (torusGraphD 3 (N + 1) (stencilRD 3 (N + 1))),
      (∀ N (x y : Fin 3 → ZMod (N + 1)),
        dist (toScaledT x : ScaledTorusD 3 N) (toScaledT y)
          = ((stencilRD 3 (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
              * QIQTH.MetricFromState.decodedDist (P N) x y) ∧
      Filter.Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledTorusD 3 N)) Filter.atTop
        (𝓝 (GromovHausdorff.toGHSpace (FlatTorus 3))) :=
  state_decoded_geometry_tendsto_flatTorus' 3

end QIQTH.TorusFromState
