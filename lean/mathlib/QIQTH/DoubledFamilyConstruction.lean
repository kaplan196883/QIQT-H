/-
  DoubledFamilyConstruction — J4-40: constructing the doubled-family SUPPLY for the CLOSE bridge
  `expMap_common_nondeg_radius_of_doubled_supply` (`JacobiDoubledFamily.lean`).

  ## Goal of the brick

  The CLOSE bridge `(J)` (compact-uniform local exp-nondegeneracy radius) is proved in
  `JacobiDoubledFamily.lean` from a CARRIED doubled-family SUPPLY over the compact `K`: the doubled
  integral-curve family `Y q v a b s τ` (integral curves of `G = doubledField g gi`), the doubled
  linearized field `Vf`, a per-`(q,v)` compact convex confinement set `S q v`, the first-jet link
  `hlink`, and the base second-jet / geometry data.  The J4-40 mission is to CONSTRUCT that supply so
  the bridge's hypotheses become PROVED rather than carried.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  Two self-contained, non-circular, green REUSE cores for the `(S1a)` doubled integral-curve
  packaging, plus the doubled-field equilibrium building block for the confinement argument:

  * `doubledField_prod_hasDerivAt` — **the `(S1a)`/`hYode` repackaging core.**  A pure product-rule
    fact: if `P` solves the geodesic phase ODE `P' = geodesicField (P τ)` and `J` solves the Jacobi
    (linearized) ODE `J' = DF(P τ)·J` along `P`, then the PAIR `τ ↦ (P τ, J τ)` is a genuine integral
    curve of `doubledField g gi`.  This is EXACTLY the content of the bridge's `hYode`: a
    `doubledField` integral curve = (geodesic phase-flow ⊗ Jacobi field), so `hYode` for `Y = (P, J)`
    is nothing more than differentiating the pair.  This confirms that `hYode` is a REPACKAGING of a
    confined geodesic tube (`geodesic_apriori_confinement_uniform`, engine (1)) and a Jacobi field
    along it — NOT new ODE existence.

  * `doubledField_equilibrium` — `((q,0),(0,0))` is a zero of `doubledField g gi` (both the geodesic
    factor, via `geodesicField_equilibrium`, and the linearized factor, by linearity applied to the
    zero seed).  This is the doubled analog of `geodesicField_equilibrium`, the building block for a
    doubled a-priori-confinement / equilibrium-uniqueness argument.

  * `doubledField_prod_mem_prod` — product-set confinement packaging: if `P τ ∈ S₁` and `J τ ∈ S₂`
    then `(P τ, J τ) ∈ S₁ ×ˢ S₂`; with `S₁, S₂` compact convex balls the product is compact convex.
    The `(S1b)` shape for a product confinement set.

  ## HONEST CHECKPOINT (binding) — why `(J)` is NOT closed self-contained here

  **STRUCTURAL BLOCKER (surfaced this brick).**  The bridge's confinement hypothesis is
      `hmem : ∀ s : ℝ, ∀ τ ∈ Icc 0 1, Y q v a b s τ ∈ S q v`
  together with the affine initial-condition hypothesis
      `hIC : ∀ s : ℝ, Y q v a b s 0 − Y q v a b 0 0 = s • ((0,a),(0,0))`,
  and `S q v` depends on NEITHER `a`, `b`, nor `s`.  For `a ≠ 0` the value `Y q v a b s 0` traces the
  UNBOUNDED affine line `((q, v + s·a),(0,b))` as `s` ranges over `ℝ`, so it CANNOT lie in the compact
  set `S q v` for all `s`.  Hence the supply `(hmem ∧ hIC)` is UNSATISFIABLE for `a ≠ 0`.  The same
  `∀ s : ℝ` confinement is baked into `doubledField_variation_exists_uncond` and `hid_of_doubled_data`
  (`JacobiOperatorBaseDeriv` / `JacobiOperatorFDeriv`).  So `(J)` CANNOT be closed as a self-contained
  theorem through this bridge without WEAKENING `∀ s : ℝ` to a bounded window `s ∈ Icc (-σ) σ`
  throughout the doubled-family engines — a change to those (other) files, out of scope for this brick.

  Consequently this file does NOT discharge any bridge binder (each carries the un-satisfiable `∀ s`
  confinement); it lands the calculus/geometry REUSE cores that a corrected (bounded-`s`) construction
  would consume, and confirms (via `doubledField_prod_hasDerivAt`) that `hYode` is a repackaging of the
  existing geodesic-tube + Jacobi-field engines.  It does NOT build the doubled families, does NOT
  smuggle `hid`/`hlink`, NOT the generic `[0,1]` linear-ODE existence for the Jacobi field over an
  arbitrary base curve (the existing `expJet2Fund` concatenation is welded to `expTube`), NOT `Vf`,
  NOT the covariant `D²/dτ²`, NOT Raychaudhuri, NOT `a₁ = R/6`.
-/
import QIQTH.JacobiDoubledFamily
import QIQTH.VelocitySecondJetId
import QIQTH.VelocityJacobiBaseDep
import QIQTH.BasepointJacobi2
import QIQTH.BoundedGeometryConfine
import QIQTH.FlowVelocityJacobiField
import QIQTH.UniformFlowBridge
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **The `(S1a)`/`hYode` repackaging core — a `doubledField` integral curve = geodesic phase-flow ⊗
    Jacobi field.**  If `P : ℝ → Point n × Point n` solves the geodesic phase ODE
    `P' = geodesicField (P τ)` at `τ`, and `J : ℝ → Point n × Point n` solves the Jacobi (linearized)
    ODE `J' = fderiv (geodesicField) (P τ) (J τ)` along `P` at `τ`, then the PAIR
    `τ ↦ (P τ, J τ) : (Point n × Point n) × (Point n × Point n)` is a genuine integral curve of
    `doubledField g gi` at `τ`:
        `HasDerivAt (fun t => (P t, J t)) (doubledField g gi (P τ, J τ)) τ`.

    This is EXACTLY the bridge's `hYode` for `Y = fun t => (P t, J t)`: since
    `doubledField g gi (P τ, J τ) = (geodesicField (P τ), fderiv (geodesicField) (P τ) (J τ))`, the
    pair's derivative (by `HasDerivAt.prod`) is by definition the doubled field at the pair.  So `hYode`
    is a REPACKAGING — pure product rule — of a geodesic curve `P` (e.g. the confined tube from
    `geodesic_apriori_confinement_uniform`) and a Jacobi field `J` along it, NOT new ODE existence. -/
theorem doubledField_prod_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    {P J : ℝ → Point n × Point n} {τ : ℝ}
    (hP : HasDerivAt P (geodesicField g gi (P τ)) τ)
    (hJ : HasDerivAt J (fderiv ℝ (geodesicField g gi) (P τ) (J τ)) τ) :
    HasDerivAt (fun t => (P t, J t)) (doubledField g gi (P τ, J τ)) τ := by
  have h := hP.prodMk hJ
  simpa [doubledField] using h

/-- **The doubled-field equilibrium.**  `((q,0),(0,0))` is a zero of `doubledField g gi`: the geodesic
    factor vanishes by `geodesicField_equilibrium`, and the linearized factor
    `fderiv (geodesicField) (q,0) (0,0)` vanishes because a continuous-linear map sends `0 ↦ 0`.  The
    doubled analog of `geodesicField_equilibrium`; the equilibrium building block for a doubled a-priori
    confinement / equilibrium-uniqueness argument. -/
theorem doubledField_equilibrium (g gi : Point n → Fin n → Fin n → ℝ) (q : Point n) :
    doubledField g gi (((q, 0), (0, 0)) : (Point n × Point n) × (Point n × Point n)) = 0 := by
  refine Prod.ext ?_ ?_
  · show geodesicField g gi ((q, 0) : Point n × Point n) = 0
    exact geodesicField_equilibrium g gi q
  · show (fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n)) (0, 0) = 0
    exact map_zero _

/-- **Product-set confinement packaging (`(S1b)` shape).**  If the geodesic factor `P τ` lies in `S₁`
    and the Jacobi factor `J τ` lies in `S₂`, then the doubled pair `(P τ, J τ)` lies in the product
    confinement set `S₁ ×ˢ S₂`.  With `S₁, S₂` compact convex (e.g. closed balls, cf.
    `IsCompact.prod` / `Convex.prod`) the product is compact convex — the shape the bridge's
    `hScompact`/`hSconvex`/`hmem` want for a product confinement set. -/
theorem doubledField_prod_mem_prod {P J : ℝ → Point n × Point n} {τ : ℝ}
    {S₁ S₂ : Set (Point n × Point n)} (hP : P τ ∈ S₁) (hJ : J τ ∈ S₂) :
    (P τ, J τ) ∈ S₁ ×ˢ S₂ :=
  Set.mk_mem_prod hP hJ

end QIQTH.ExpMap
