/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# STENCIL FROM STATE — the end-to-end chain: entangled-state profile → decoded graph →
decoded metric → Gromov–Hausdorff limit = the Euclidean cube (track A capstone)

Brick A1 of the STATE-WIRE track (`docs/qg_roadmap/STATE_TORUS_CURVATURE_PLAN.md`): the
**composition** of three previously proven, axiom-free layers, glued at `G = stencilGraphD`:

    Bell state ──► cut-rank profile ──► decoded graph ──► decoded metric ──► GH limit = [0,1]ᵈ
    (BellCutRank +      (this file:       (MetricFromState  (MetricFromState   (StencilDimGH
     ReducedDensity:    `stencilProfile`,  `rankMIGraph_eq`:  `decodedDist`:     `stencilD_toGHSpace_
     Schmidt rank =     the crossing-      `stencilProfile_   `scaledStencil_    tendsto_unitCube`:
     q^boundary)        count profile)     decodes`)          dist_eq_decoded`)  the capstone)

Each arrow is a theorem proved in an earlier file — here they are composed at the d-dimensional
stencil graph:

* `stencilProfile d N` — the explicit crossing-count cut-rank profile (bond dimension `q = 2`)
  of the stencil graph `stencilGraphD d N (stencilRD d N)` (`MetricFromState.explicitProfile`).
* `stencilProfile_decodes` — **THE DECODE**: the profile's strict rank-submultiplicativity
  pattern recovers the stencil graph, `rankMIGraph (stencilProfile d N) = stencilGraphD …`
  (`MetricFromState.rankMIGraph_eq`, a theorem, not a definition).
* `scaledStencil_dist_eq_decoded` — **THE METRIC IDENTITY**: the intrinsic scaled stencil
  metric of `StencilDimGH` IS the state-decoded metric, rescaled:
  `dist x y = (R_N/N) · decodedDist (stencilProfile d N) x y`.
* `stencilProfile_boundary_realized` — **THE BELL GROUNDING**: across EVERY cut `A`, the
  profile's boundary exponent is realized as the genuine reduced-density Schmidt rank of an
  explicit Bell-pair product state (`ReducedDensity.bell_schmidtRank_eq_pow_crossingCard`).
* `state_decoded_geometry_tendsto_unitCube` (+ the packaged `'` version and the `d = 3`
  corollary) — **THE END-TO-END CAPSTONE**: there is a family of cut-rank profiles, realized
  by Bell entanglement, whose decoded, scaled metrics are exactly the metrics of a sequence of
  finite spaces converging in Gromov–Hausdorff space to the EUCLIDEAN unit cube `([0,1]ᵈ, ‖·‖₂)`.

## Scope firewall (HONEST)

* **The state/profile is CONSTRUCTED to carry the stencil correlation pattern.**  The decoding
  is a theorem, but WHY a physical state would carry exactly this entanglement — the dynamical
  source of the profile — remains the cited open wall.  Nothing here derives the state from
  dynamics.
* **The dimension `d` is an INPUT** — the chosen lattice — NOT emergent; the theorem holds for
  every `d` and says nothing about why physical space is 3-dimensional.
* **Isotropy is inserted through the stencil rule** (the Euclidean-ball edge test), not
  emergent from a fixed local combinatorial rule (impossible, per `IsotropyNoGo`) nor from
  dynamics.
* The limit is the FLAT cube — not a curved Riemannian manifold; NOT GR, NOT numerical-G,
  NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.StencilDimGH
import QIQTH.MetricFromState
import QIQTH.BellCutRank
import QIQTH.ReducedDensity

namespace QIQTH.StencilFromState

open QIQTH.StencilDimGraph QIQTH.StencilDimGH QIQTH.MetricFromState Filter Topology

/-! ## 1 — the crossing-count cut-rank profile of the stencil graph -/

/-- **The stencil profile**: the explicit crossing-count cut-rank profile of the d-dimensional
stencil graph at bond dimension `q = 2` — boundary = the genuine edge-crossing count, defect
PROVEN (`crossingCard_pair_defect`), no carried hypotheses. -/
def stencilProfile (d N : ℕ) :
    QIQTH.MetricFromState.CutRankProfile (stencilGraphD d N (stencilRD d N)) :=
  explicitProfile _ (le_refl 2)

/-- The profile's boundary function is the stencil graph's crossing-edge count (definitional). -/
@[simp] lemma stencilProfile_boundary (d N : ℕ) (A : Finset (Fin d → Fin (N + 1))) :
    (stencilProfile d N).boundary A
      = QIQTH.MetricFromState.crossingCard (stencilGraphD d N (stencilRD d N)) A := rfl

/-! ## 2 — THE DECODE: the profile recovers the stencil graph -/

/-- **THE DECODE.**  The strict rank-submultiplicativity pattern of the stencil profile — the
positive Rényi-0 mutual-information adjacency — recovers the stencil graph exactly:
`rankMIGraph (stencilProfile d N) = stencilGraphD d N (stencilRD d N)`.  The graph is an
OUTPUT of the cut-rank data (a theorem, `rankMIGraph_eq`, not a definition). -/
theorem stencilProfile_decodes (d N : ℕ) :
    rankMIGraph (stencilProfile d N) = stencilGraphD d N (stencilRD d N) :=
  rankMIGraph_eq (stencilProfile d N)

/-! ## 3 — THE METRIC IDENTITY: the GH-converging metric IS the decoded metric -/

/-- **THE METRIC IDENTITY.**  The intrinsic scaled stencil metric of `StencilDimGH` — the very
metric whose spaces GH-converge to the Euclidean cube — is exactly the state-decoded metric of
the stencil profile, rescaled by `R_N/N`:

    dist (toScaledD x) (toScaledD y) = (R_N/N) · decodedDist (stencilProfile d N) x y.

Both sides unfold to `(R_N/N) · (stencilGraphD …).dist x y`: the left by
`scaledStencilD_dist_eq`, the right by `decodedDist_eq` + `stencilProfile_decodes` +
`graphDist G x y = (G.dist x y : ℝ)`. -/
theorem scaledStencil_dist_eq_decoded (d N : ℕ) (x y : Fin d → Fin (N + 1)) :
    dist (toScaledD x : ScaledStencilD d N) (toScaledD y)
      = ((stencilRD d N : ℝ) / (N : ℝ))
          * QIQTH.MetricFromState.decodedDist (stencilProfile d N) x y := by
  rw [scaledStencilD_dist_eq, decodedDist_eq]
  rfl

/-! ## 4 — THE BELL GROUNDING: the boundary exponent is a genuine Schmidt rank -/

/-- **THE BELL GROUNDING.**  Across EVERY cut `A`, the stencil profile's boundary function is
realized as the genuine reduced-density Schmidt rank of an explicit Bell-pair product state
(one 2-dimensional maximally-entangled pair per crossing edge):
`schmidtRank = 2 ^ boundary A`.  The decoded geometry's "area" is honest entanglement, not
merely a combinatorial count (`ReducedDensity.bell_schmidtRank_eq_pow_crossingCard`). -/
theorem stencilProfile_boundary_realized (d N : ℕ) (A : Finset (Fin d → Fin (N + 1))) :
    QIQTH.ReducedDensity.schmidtRank
        (QIQTH.BellCutRank.bellFlattening ℂ 2 (Fin ((stencilProfile d N).boundary A)))
      = 2 ^ (stencilProfile d N).boundary A := by
  rw [stencilProfile_boundary]
  exact QIQTH.ReducedDensity.bell_schmidtRank_eq_pow_crossingCard 2 _ A (Fintype.card_fin _)

/-! ## 5 — THE END-TO-END CAPSTONE -/

/-- **THE END-TO-END CAPSTONE (state-decoded geometry → the Euclidean cube).**  The finite
metric spaces GH-converging to the Euclidean unit cube are, pointwise-provably
(`scaledStencil_dist_eq_decoded`), the spaces of the STATE-DECODED metric: the metric decoded
from the crossing-count cut-rank profile `stencilProfile d N`, whose boundary exponents are
genuine Bell-state Schmidt ranks (`stencilProfile_boundary_realized`).  The convergence itself
is `stencilD_toGHSpace_tendsto_unitCube` (brick G4); the packaged version
`state_decoded_geometry_tendsto_unitCube'` carries the decoding formally in the statement. -/
theorem state_decoded_geometry_tendsto_unitCube (d : ℕ) :
    Filter.Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledStencilD d N)) Filter.atTop
      (𝓝 (GromovHausdorff.toGHSpace ↥(unitCube d))) :=
  stencilD_toGHSpace_tendsto_unitCube d

/-- **THE PACKAGED CAPSTONE.**  There is a family of cut-rank profiles — realized by explicit
Bell entanglement across every cut — whose decoded, scaled metrics are EXACTLY the metrics of
a sequence of finite spaces converging in Gromov–Hausdorff space to the Euclidean unit cube
`([0,1]ᵈ, ‖·‖₂)`: entangled-state profile → decoded graph → decoded metric → Euclidean
continuum limit, every arrow a theorem. -/
theorem state_decoded_geometry_tendsto_unitCube' (d : ℕ) :
    ∃ P : ∀ N, QIQTH.MetricFromState.CutRankProfile (stencilGraphD d N (stencilRD d N)),
      (∀ N (x y : Fin d → Fin (N + 1)),
        dist (toScaledD x : ScaledStencilD d N) (toScaledD y)
          = ((stencilRD d N : ℝ) / (N : ℝ))
              * QIQTH.MetricFromState.decodedDist (P N) x y) ∧
      Filter.Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledStencilD d N)) Filter.atTop
        (𝓝 (GromovHausdorff.toGHSpace ↥(unitCube d))) :=
  ⟨fun N => stencilProfile d N, fun N x y => scaledStencil_dist_eq_decoded d N x y,
    stencilD_toGHSpace_tendsto_unitCube d⟩

/-- **THE HEADLINE (d = 3)**: the state-decoded geometry of the 3-dimensional stencil profiles
GH-converges to the Euclidean unit cube `[0,1]³`.  (The dimension 3 is CHOSEN, not derived.) -/
theorem state_decoded_geometry_tendsto_unitCube_3D :
    ∃ P : ∀ N, QIQTH.MetricFromState.CutRankProfile (stencilGraphD 3 N (stencilRD 3 N)),
      (∀ N (x y : Fin 3 → Fin (N + 1)),
        dist (toScaledD x : ScaledStencilD 3 N) (toScaledD y)
          = ((stencilRD 3 N : ℝ) / (N : ℝ))
              * QIQTH.MetricFromState.decodedDist (P N) x y) ∧
      Filter.Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledStencilD 3 N)) Filter.atTop
        (𝓝 (GromovHausdorff.toGHSpace ↥(unitCube 3))) :=
  state_decoded_geometry_tendsto_unitCube' 3

end QIQTH.StencilFromState
