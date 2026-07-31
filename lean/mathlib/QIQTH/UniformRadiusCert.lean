/-
  UniformRadiusCert — J4-60 (Brick-A entry point): the UNIFORM-RADIUS CERTIFICATE.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no vacuous certificate)

  This file replaces the opaque per-`q` `expRho`/`hr_lt` confinement+nondeg content of
  `CommonNondegRadius` with a SINGLE uniform radius `r > 0` over the compact base set `K`, certified
  by an explicit structure `UniformConfinedTubeOn` and its UNCONDITIONAL constructor
  `uniformConfinedTubeOn_exists` (hypotheses ONLY `hC` + `IsCompact K`).

  * `UniformConfinedTubeOn g gi hC hK r` — a `Prop` structure bundling, for a uniform radius `r`:
      - `hr    : 0 < r`;
      - `hconf : ∀ q ∈ K, ∀ v, ‖v‖ ≤ r → <the uniform tube through (q,v) is a confined geodesic
                 integral curve>` (the IC / geodesic-ODE / `C₀‖v‖`-confinement shape of
                 `geodesic_apriori_confinement_uniform`, phrased on the canonical `uniformFlowTube`);
      - `hnondeg : ∀ q ∈ K, ∀ v, ‖v‖ < r → IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v)`.

  * `uniformConfinedTubeOn_exists` — the KEY deliverable: `∃ r > 0, UniformConfinedTubeOn g gi hC hK r`
    from `hC` + `IsCompact K` ALONE, with `r := min ρ_K ρ₀`:
      - `ρ_K := uniformFlowRadius g gi hC hK` (J4-17 compact-uniform confinement radius);
      - `ρ₀` from `uniformFlowExp_common_nondeg_radius` (J4-56 uniform fderiv-nondeg radius).
    `hconf` is discharged from `uniformFlowTube_spec` (restrict `‖v‖ ≤ r ≤ ρ_K`); `hnondeg` from
    J4-56 (restrict `‖v‖ < r ≤ ρ₀`).  NO `expRho`, NO `hr_lt`; the fields genuinely HOLD.

  ## FIREWALL — deliberately OMITTED fields (SUBSEQUENT Brick-A bricks; NOT carried here)

  The certificate is kept MINIMAL-and-real: it carries ONLY the confinement + fderiv-nondeg content
  that is fully constructible now.  It does NOT include:

    (a) a `uniformFlowExp`-PULLBACK-metric nondegeneracy field
        `∀ q ∈ K, ∀ ‖v‖ < r, IsUnit (matToCLM (<uniformFlowExp pullback metric> q v))`.  This needs
        (i) a `uniformFlowExp` pullback metric (analogue of `expPullbackMetric`), and (ii) a HINGE
        `IsUnit (fderiv …) → IsUnit (matToCLM …)` (analogue of `expPullbackMetric_isUnit_of_fderiv_isUnit`,
        J4-58) built for `uniformFlowExp`.  Neither exists yet — future brick.

    (b) a uniform C³ (pullback) regularity field.  This needs a uniform C⁴ regularity input for
        `uniformFlowExp` — future brick.

  Including either now would force a firewalled/vacuous proof, so they are OMITTED, not smuggled.
-/
import QIQTH.UniformFlowNondegClose
import QIQTH.UniformFlowNondeg
import QIQTH.BoundedGeometryConfine
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **The uniform-radius confined-tube certificate over a compact base set `K`.**

For a single uniform radius `r > 0`, this bundles, uniformly over all base points `q ∈ K`:

* `hconf` — for `‖v‖ ≤ r`, the canonical uniform tube `uniformFlowTube … q v` through `(q, v)` is a
  genuine confined geodesic integral curve: initial condition `(q, v)`, solves the geodesic ODE on
  `(-2, 2) ⊇ [0,1]`, and is `C₀‖v‖`-confined near the equilibrium `(q, 0)` on `[0,1]` (the output
  shape of `geodesic_apriori_confinement_uniform`, phrased on `uniformFlowTube`);
* `hnondeg` — for `‖v‖ < r`, the differential of the uniform-flow exp endpoint map
  `uniformFlowExp g gi hC hK q` at `v` is invertible.

This is the entry point of the Brick-A re-architecture: it replaces the opaque per-`q`
`expRho`/`hr_lt` confinement+nondeg content with a SINGLE uniform radius (`uniformConfinedTubeOn_exists`).
It deliberately does NOT carry the `uniformFlowExp` pullback-metric nondegeneracy or the uniform C³
regularity — those are subsequent bricks (see the file header firewall). -/
structure UniformConfinedTubeOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (r : ℝ) : Prop where
  /-- The certified radius is positive. -/
  hr : 0 < r
  /-- Uniform confinement: for `q ∈ K` and `‖v‖ ≤ r`, the uniform tube through `(q, v)` has initial
  condition `(q, v)`, solves the geodesic ODE on `(-2, 2)`, and is `C₀‖v‖`-confined near `(q, 0)`
  on `[0,1]`. -/
  hconf : ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ r →
    uniformFlowTube g gi hC hK q v 0 = (q, v) ∧
    (∀ t ∈ Set.Ioo (-2 : ℝ) 2,
      HasDerivAt (uniformFlowTube g gi hC hK q v)
        (geodesicField g gi (uniformFlowTube g gi hC hK q v t)) t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖uniformFlowTube g gi hC hK q v t - ((q, 0) : Point n × Point n)‖
        ≤ uniformFlowConst g gi hC hK * ‖v‖)
  /-- Uniform fderiv-nondegeneracy: for `q ∈ K` and `‖v‖ < r`, the differential of the uniform-flow
  exp endpoint map is invertible. -/
  hnondeg : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r →
    IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v)

/-- **The uniform-radius certificate is UNCONDITIONALLY constructible.**

From `hC` (Christoffel `C^∞`) + `IsCompact K` ALONE there is a single positive radius `r > 0` (namely
`r := min ρ_K ρ₀`, the smaller of the J4-17 compact-uniform confinement radius `ρ_K` and the J4-56
uniform fderiv-nondegeneracy radius `ρ₀`) on which the certificate `UniformConfinedTubeOn` holds.

No `expRho`, no `hr_lt`; the confinement field is discharged from `uniformFlowTube_spec` and the
fderiv-nondeg field from `uniformFlowExp_common_nondeg_radius`. -/
theorem uniformConfinedTubeOn_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), UniformConfinedTubeOn g gi hC hK r := by
  -- J4-56: the uniform fderiv-nondegeneracy radius `ρ₀ > 0`.
  obtain ⟨ρ₀, hρ₀pos, hnd⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  -- J4-17: the compact-uniform confinement radius `ρ_K > 0`.
  have hρKpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨min (uniformFlowRadius g gi hC hK) ρ₀, lt_min hρKpos hρ₀pos, ?_⟩
  refine ⟨lt_min hρKpos hρ₀pos, ?_, ?_⟩
  · -- Confinement: restrict `‖v‖ ≤ r ≤ ρ_K` and invoke the uniform tube spec.
    intro q hq v hv
    have hvρK : ‖v‖ ≤ uniformFlowRadius g gi hC hK := le_trans hv (min_le_left _ _)
    exact uniformFlowTube_spec g gi hC hK q hq v hvρK
  · -- Nondegeneracy: restrict `‖v‖ < r ≤ ρ₀` and invoke J4-56.
    intro q hq v hv
    have hvρ₀ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_right _ _)
    exact hnd q hq v hvρ₀

/-- **Certificate ⟹ downstream fderiv-nondegeneracy.**  The `hnondeg` content of the certificate,
exposed as a standalone consumer-facing corollary: on the certified radius, the differential of the
uniform-flow exp endpoint map is invertible for every `q ∈ K` and `‖v‖ < r`. -/
theorem UniformConfinedTubeOn.fderiv_isUnit {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {r : ℝ}
    (cert : UniformConfinedTubeOn g gi hC hK r)
    {q : Point n} (hq : q ∈ K) {v : Point n} (hv : ‖v‖ < r) :
    IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v) :=
  cert.hnondeg q hq v hv

end QIQTH.ExpMap
