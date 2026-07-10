/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# CONE FROM STATE — the end-to-end chain to the first state-decoded POSITIVE-CURVATURE limit
(brick K4, campaign finale)

Final brick of the STATE-WIRE-2 track
(`docs/qg_roadmap/STATEWIRE2_SPHERE_INTRINSIC_CONE_PLAN.md`): the **composition** of the
previously proven, axiom-free layers, glued at `G = coneGraph θ n (rhoEff θ n)` — the cone
mirror of the cube/torus/tripod state-wire bricks (`QIQTH/StencilFromState.lean`,
`QIQTH/TorusFromState.lean`, `QIQTH/TripodFromState.lean`):

    Bell state ──► cut-rank profile ──► decoded graph ──► decoded metric ──► GH limit = Cone θ
    (BellCutRank +      (this file:       (MetricFromState  (MetricFromState   (ConeIntrinsicGH
     ReducedDensity:    `coneProfile`,     `rankMIGraph_eq`:  `decodedDist`:     `coneIntrinsic_
     Schmidt rank =     the crossing-      `coneProfile_      `intrinsicCone_    toGHSpace_tendsto_
     q^boundary)        count profile)     decodes`)          dist_eq_decoded`)  cone`: the capstone)

Each arrow is a theorem proved in an earlier file — here they are composed at the geometric
cone graph on the polar grid:

* `coneProfile θ n` — the explicit crossing-count cut-rank profile (bond dimension `q = 2`)
  of the geometric cone graph `coneGraph θ n (rhoEff θ n)` (`MetricFromState.explicitProfile`).
* `coneProfile_decodes` — **THE DECODE**: the profile's strict rank-submultiplicativity
  pattern recovers the geometric graph, `rankMIGraph (coneProfile θ n) = coneGraph …`
  (`MetricFromState.rankMIGraph_eq`, a theorem, not a definition).
* `intrinsicCone_dist_eq_decoded` — **THE METRIC IDENTITY**: the intrinsic scaled hop metric
  of `ConeIntrinsicGH` IS the state-decoded metric, rescaled:
  `dist x y = rhoEff θ n · decodedDist (coneProfile θ n) x y`.
* `coneProfile_boundary_realized` — **THE BELL GROUNDING**: across EVERY cut `A`, the
  profile's boundary exponent is realized as the genuine reduced-density Schmidt rank of an
  explicit Bell-pair product state (`ReducedDensity.bell_schmidtRank_eq_pow_crossingCard`).
* `state_decoded_geometry_tendsto_cone` — **THE END-TO-END CAPSTONE**: there is a family of
  cut-rank profiles, realized by Bell entanglement, whose decoded, scaled metrics are exactly
  the metrics of a sequence of finite spaces converging in Gromov–Hausdorff space to the CONE
  of total angle `θ < 2π`.

**The new content vs the earlier state-wire bricks**: the state-decoded limit now carries
GENUINE (concentrated) POSITIVE CURVATURE — the cone's apex has deficit angle `2π − θ > 0`,
and the cone is provably NOT isometrically embeddable in any real inner-product space
(`ConeMetric.cone_no_isometric_embedding_into_inner`).  This completes the state-decoded
family {interval, cube ∀d, torus ∀d / circle, tripod, cone} =
{flat-with-boundary, flat, flat-periodic, branching, positively-curved}.

**Classical decidability, noted honestly**: the cone graph's adjacency rule is a real-number
comparison (`dist x y ≤ ρ`), decided classically (`instDecidableRelConeGraphAdj` via
`Classical.dec`) — the profile is a mathematical object, not an executable program; the
decoding theorem is exact regardless.

## Scope firewall (HONEST)

* **The deficit angle — and the whole cone geometry — is INSERTED, not emergent.**  The
  curvature enters through the adjacency rule (proximity in the cone metric) that the graph —
  and hence the profile — is built on: the state/profile is CONSTRUCTED to carry the cone's
  proximity pattern.  The decoding is a theorem, but WHY a physical state would carry exactly
  this entanglement — the dynamical source of the profile — remains the cited open wall.
  Nothing here derives the state (or its curvature) from dynamics.  Recovery, not emergence.
* **`θ` is an INPUT** — a chosen deficit angle, not derived.
* **The curvature is CONCENTRATED** — an Alexandrov cone point, NOT a smooth Riemann tensor,
  NOT a Riemannian manifold.  Away from the apex the cone is flat.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.ConeIntrinsicGH
import QIQTH.MetricFromState
import QIQTH.BellCutRank
import QIQTH.ReducedDensity

namespace QIQTH.ConeFromState

open QIQTH.ConeMetric QIQTH.ConeGH QIQTH.ConeIntrinsicGraph QIQTH.ConeIntrinsicGH
  QIQTH.MetricFromState Filter Topology

/-! ## 0 — instances: the polar grid is a finite decidable vertex type -/

instance instDecidableEqPolarGrid (θ : ℝ) (n : ℕ) : DecidableEq (PolarGrid θ n) :=
  inferInstanceAs (DecidableEq (Option ({k : Fin (n + 2) // k ≠ 0} × ZMod (n + 2))))

instance instFintypePolarGrid (θ : ℝ) (n : ℕ) : Fintype (PolarGrid θ n) :=
  inferInstanceAs (Fintype (Option ({k : Fin (n + 2) // k ≠ 0} × ZMod (n + 2))))

section ConeWire

variable (θ : ℝ) [Fact (0 < θ)] [Fact (θ < 2 * Real.pi)]

/-! ## 1 — the crossing-count cut-rank profile of the geometric cone graph -/

/-- **The cone profile**: the explicit crossing-count cut-rank profile of the geometric cone
graph at the effective radius `rhoEff θ n`, bond dimension `q = 2` — boundary = the genuine
edge-crossing count, defect PROVEN (`crossingCard_pair_defect`), no carried hypotheses.
Noncomputable because the cone graph's adjacency (a real-number proximity test) is decided
classically — the profile is a mathematical object, and the decoding below is exact. -/
noncomputable def coneProfile (n : ℕ) :
    QIQTH.MetricFromState.CutRankProfile (coneGraph θ n (rhoEff θ n)) :=
  explicitProfile _ (le_refl 2)

/-- The profile's boundary function is the cone graph's crossing-edge count (definitional). -/
@[simp] lemma coneProfile_boundary (n : ℕ) (A : Finset (PolarGrid θ n)) :
    (coneProfile θ n).boundary A
      = QIQTH.MetricFromState.crossingCard (coneGraph θ n (rhoEff θ n)) A :=
  rfl

/-! ## 2 — THE DECODE: the profile recovers the geometric cone graph -/

/-- **THE DECODE.**  The strict rank-submultiplicativity pattern of the cone profile — the
positive Rényi-0 mutual-information adjacency — recovers the geometric cone graph exactly:
`rankMIGraph (coneProfile θ n) = coneGraph θ n (rhoEff θ n)`.  The GEOMETRIC graph — proximity
in the cone metric, deficit angle and all — is an OUTPUT of the cut-rank data (a theorem,
`rankMIGraph_eq`, not a definition). -/
theorem coneProfile_decodes (n : ℕ) :
    rankMIGraph (coneProfile θ n) = coneGraph θ n (rhoEff θ n) :=
  rankMIGraph_eq (coneProfile θ n)

/-! ## 3 — THE METRIC IDENTITY: the GH-converging metric IS the decoded metric -/

/-- **THE METRIC IDENTITY.**  The intrinsic scaled hop metric of `ConeIntrinsicGH` — the very
metric whose spaces GH-converge to the cone — is exactly the state-decoded metric of the cone
profile, rescaled by the effective radius:

    dist (toIntrinsic x) (toIntrinsic y) = rhoEff θ n · decodedDist (coneProfile θ n) x y.

Both sides unfold to `rhoEff θ n · (coneGraph θ n (rhoEff θ n)).dist x y`: the left by
`intrinsicCone_dist_eq`, the right by `decodedDist_eq` + `coneProfile_decodes` +
`graphDist G x y = (G.dist x y : ℝ)`. -/
theorem intrinsicCone_dist_eq_decoded (n : ℕ) (x y : PolarGrid θ n) :
    dist (toIntrinsic x : IntrinsicConeSpace θ n) (toIntrinsic y)
      = rhoEff θ n * QIQTH.MetricFromState.decodedDist (coneProfile θ n) x y := by
  rw [intrinsicCone_dist_eq, decodedDist_eq]
  rfl

/-! ## 4 — THE BELL GROUNDING: the boundary exponent is a genuine Schmidt rank -/

/-- **THE BELL GROUNDING.**  Across EVERY cut `A`, the cone profile's boundary function is
realized as the genuine reduced-density Schmidt rank of an explicit Bell-pair product state
(one 2-dimensional maximally-entangled pair per crossing edge):
`schmidtRank = 2 ^ boundary A`.  The decoded geometry's "area" is honest entanglement, not
merely a combinatorial count (`ReducedDensity.bell_schmidtRank_eq_pow_crossingCard`). -/
theorem coneProfile_boundary_realized (n : ℕ) (A : Finset (PolarGrid θ n)) :
    QIQTH.ReducedDensity.schmidtRank
        (QIQTH.BellCutRank.bellFlattening ℂ 2 (Fin ((coneProfile θ n).boundary A)))
      = 2 ^ (coneProfile θ n).boundary A := by
  rw [coneProfile_boundary]
  exact QIQTH.ReducedDensity.bell_schmidtRank_eq_pow_crossingCard 2 _ A (Fintype.card_fin _)

/-! ## 5 — THE END-TO-END CAPSTONE -/

/-- **THE PACKAGED CAPSTONE — the first state-decoded POSITIVE-CURVATURE limit (campaign
finale).**  There is a family of cut-rank profiles — realized by explicit Bell entanglement
across every cut (`coneProfile_boundary_realized`) — whose decoded, scaled metrics are
EXACTLY the metrics (`intrinsicCone_dist_eq_decoded`) of a sequence of finite spaces
converging in Gromov–Hausdorff space to the CONE of total angle `θ < 2π`
(`coneIntrinsic_toGHSpace_tendsto_cone`, brick K3): entangled-state profile → decoded graph →
decoded metric → continuum limit with CONCENTRATED POSITIVE CURVATURE (deficit angle
`2π − θ`, provably not flat: `ConeMetric.cone_no_isometric_embedding_into_inner`), every
arrow a theorem.  This completes the state-decoded family
{interval, cube ∀d, torus ∀d / circle, tripod, cone} =
{flat-with-boundary, flat, flat-periodic, branching, positively-curved}.
(The deficit angle is INSERTED through the adjacency rule the profile is built on — see the
scope firewall.) -/
theorem state_decoded_geometry_tendsto_cone :
    ∃ P : ∀ n, QIQTH.MetricFromState.CutRankProfile (coneGraph θ n (rhoEff θ n)),
      (∀ n (x y : PolarGrid θ n),
        dist (toIntrinsic x : IntrinsicConeSpace θ n) (toIntrinsic y)
          = rhoEff θ n * QIQTH.MetricFromState.decodedDist (P n) x y) ∧
      Filter.Tendsto (fun n : ℕ => GromovHausdorff.toGHSpace (IntrinsicConeSpace θ n))
        Filter.atTop (𝓝 (GromovHausdorff.toGHSpace (Cone θ))) :=
  ⟨fun n => coneProfile θ n, fun n x y => intrinsicCone_dist_eq_decoded θ n x y,
    coneIntrinsic_toGHSpace_tendsto_cone θ⟩

end ConeWire

end QIQTH.ConeFromState
