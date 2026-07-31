/-
  JacobiUniformSupply — J4-38: the UNIFORM SUPPLY residual for the compact-uniform local `a₁ = R/6`
  gate `(J)`.

  ## Context

  `JacobiOperatorFDeriv` (J4-37) landed `hid_of_doubled_data`, the POINTWISE assembly of the
  second-order velocity jet identification `hid`

      `(fderiv ℝ (fun w => fderiv ℝ Fam w) v) a b = (Zf a b 1).1`

  from GENUINE data: the doubled families `Y`/`Vf` (integral curves of `G = doubledField g gi`
  through the perturbed IC), the first-jet link `hlink`, the jet-map regularity `hdiff`, and the
  `Zf` second-variation ODE data.  What REMAINS to DISCHARGE the `(J)` capstone
  `expMap_common_nondeg_radius_of_velocity_ode_data` (`FlowVelocityJacobiField`) is the CONSTRUCTION
  residual: supply those hypotheses over the compact `K`, uniformly.

  This file lands the EASIEST of the three supply ingredients — **(S3) the jet-map
  differentiability** `hdiff` — as a compiled, DERIVED theorem, and firewalls the remaining two
  (`(S1)` the doubled families with confinement, `(S2)` the first-jet link `hlink`) honestly.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `expMap_jetMap_differentiableAt` — **(S3), pointwise.**  For a base point `q` and a velocity `v`
    strictly inside the exp-nondegeneracy ball `Metric.ball 0 (expRho g gi hC q)`, the jet map
    `w ↦ fderiv ℝ (expMap g gi hC q) w` is `DifferentiableAt ℝ` at `v`.  DERIVED from
    `expMap_contDiffOn_four` (`exp_q ∈ C⁴` on the open ball): the ball is open so `ContDiffOn 4`
    restricts to `ContDiffAt 4` at `v`, whence `ContDiffAt.fderiv_right` gives `ContDiffAt 1` of the
    jet map, and `.differentiableAt le_rfl` yields differentiability.  This is EXACTLY the `hdiff`
    hypothesis of `hid_of_doubled_data`.

  * `expMap_jetMap_differentiableAt_uniform` — **(S3), uniform over `K`.**  The same, over a compact
    `K` and every `v` in the closed ball `Metric.closedBall 0 r` with a single `r < expRho g gi hC q`
    (`q ∈ K`) — the precise shape the `(J)` capstone consumes `hdiff` in.  DERIVED by feeding the
    strict-inclusion `closedBall 0 r ⊆ ball 0 (expRho …)` into the pointwise lemma.

  ## HONEST CHECKPOINT (binding) — what is discharged and what remains

  This lands `(S3)`, the jet-map differentiability, as a compiled theorem, DERIVED from
  `exp_q ∈ C⁴` with NO carried regularity input beyond `hC` (the genuine `C^∞` Christoffel datum) and
  compactness of `K`.

  `(J)` is NOT discharged here.  Producing `hid` via `hid_of_doubled_data` over `K` still requires,
  BESIDES `(S3)`:
    * `(S1)` the doubled families `Y a b s τ` / variation fields `Vf a b τ` exhibited as genuine
      integral curves of `G = doubledField g gi` through the perturbed IC `((q, v+s·a),(0,b))` resp.
      the linearized IC, confined in a compact convex `S` for `τ ∈ [0,1]`, uniformly over `K` (the
      geodesic a-priori confinement `geodesic_apriori_confinement_uniform` ⊗ Jacobi/linearized
      existence packaged as a doubled flow);
    * `(S2)` the first-jet value link `hlink : (Y a b s 1).2.1 = fderiv ℝ (Fam q) (v+s•a) b`, wiring
      the doubled family's Jacobi endpoint to `fderiv ℝ (expMap g gi hC q)` (the `(h1)`
      identification `flowVelocity_endpoint_position_hasFDerivAt_exists`).
  Those two — the uniform construction of the doubled families as genuine flows and the value
  identification of their Jacobi endpoints with `fderiv (exp_q)` — are the precise remaining SUPPLY
  residual.  They are NOT constructed here, and this file does NOT smuggle `hid`/`hbnd`/`hunif`/
  `hFoplip`, NOT the doubled families, NOT the `(J)` conclusion, NOT `a₁ = R/6`.
-/
import QIQTH.JacobiOperatorFDeriv
import QIQTH.FlowVelocityJacobiField
import QIQTH.VelocitySecondJetId
import QIQTH.BoundedGeometryConfine
import QIQTH.ExpMapContDiffFour
import QIQTH.UniformFlowBridge
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **(S3) — the jet-map differentiability `hdiff`, pointwise.**  For a base point `q` and a velocity
    `v` in the open exp-nondegeneracy ball `Metric.ball 0 (expRho g gi hC q)`, the velocity jet map
    `w ↦ fderiv ℝ (expMap g gi hC q) w` is `DifferentiableAt ℝ` at `v`.

    DERIVED: `expMap_contDiffOn_four` gives `ContDiffOn ℝ 4 (expMap g gi hC q)` on the open ball; the
    ball is a neighbourhood of `v`, so `ContDiffOn.contDiffAt` yields `ContDiffAt ℝ 4` at `v`; then
    `ContDiffAt.fderiv_right` (with `1 + 1 ≤ 4`) gives `ContDiffAt ℝ 1` of the jet map, whence
    `.differentiableAt le_rfl`.  This is EXACTLY the `hdiff` hypothesis of `hid_of_doubled_data`. -/
theorem expMap_jetMap_differentiableAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q : Point n) {v : Point n}
    (hv : v ∈ Metric.ball (0 : Point n) (expRho g gi hC q)) :
    DifferentiableAt ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v := by
  -- `exp_q ∈ C⁴` on the open nondegeneracy ball.
  have hC4 : ContDiffOn ℝ 4 (expMap g gi hC q)
      (Metric.ball (0 : Point n) (expRho g gi hC q)) :=
    expMap_contDiffOn_four g gi hC q
  -- the open ball is a neighbourhood of `v`, so `ContDiffOn` restricts to `ContDiffAt`.
  have hnhds : Metric.ball (0 : Point n) (expRho g gi hC q) ∈ 𝓝 v :=
    Metric.isOpen_ball.mem_nhds hv
  have hAt : ContDiffAt ℝ 4 (expMap g gi hC q) v := hC4.contDiffAt hnhds
  -- one Fréchet order down: the jet map is `ContDiffAt 1`.
  have hjet : ContDiffAt ℝ 1 (fun w => fderiv ℝ (expMap g gi hC q) w) v :=
    hAt.fderiv_right (by norm_num)
  exact hjet.differentiableAt (by norm_num)

/-- **(S3) — the jet-map differentiability `hdiff`, uniform over a compact `K`.**  For a compact set
    `K` of base points and a single radius `r` with `r < expRho g gi hC q` for every `q ∈ K`, the
    velocity jet map `w ↦ fderiv ℝ (expMap g gi hC q) w` is `DifferentiableAt ℝ` at every `v` in the
    closed ball `Metric.closedBall 0 r` — the precise shape the `(J)` capstone
    `expMap_common_nondeg_radius_of_velocity_ode_data` consumes `hdiff` in.

    DERIVED: `closedBall 0 r ⊆ ball 0 (expRho g gi hC q)` from `r < expRho …`, then the pointwise
    `expMap_jetMap_differentiableAt`. -/
theorem expMap_jetMap_differentiableAt_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} {r : ℝ}
    (hr_lt : ∀ q ∈ K, r < expRho g gi hC q) :
    ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      DifferentiableAt ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v := by
  intro q hq v hv
  have hsub : Metric.closedBall (0 : Point n) r
      ⊆ Metric.ball (0 : Point n) (expRho g gi hC q) :=
    Metric.closedBall_subset_ball (hr_lt q hq)
  exact expMap_jetMap_differentiableAt g gi hC q (hsub hv)

end QIQTH.ExpMap
