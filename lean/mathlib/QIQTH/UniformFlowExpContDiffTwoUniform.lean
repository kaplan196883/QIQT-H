/-
  UniformFlowExpContDiffTwoUniform — Plan v6 Task I (floor): the UNCONDITIONAL `ContDiffOn ℝ 2`
  target shape for the flow-exponential on the uniform confinement ball.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is one brick of
  the Plan-v6 program to ELIMINATE `expRho` from the C⁴-regularity chain feeding `hCConv`.

  ── CONTEXT.  The existing chart-C⁴ result `ChartThirdJet.uniformFlowExp_contDiffAt_four` borrows its
  regularity from the `ExpMap.expMap_contDiffOn_four` tower via the overlap bridge
  `expMap_eq_uniformFlowExp_on_overlap`, valid only on `‖v‖ < min (expRho z) (uniformFlowRadius)`.
  That is why the opaque `.choose`-fixed per-base-point radius `expRho` (no continuity, no relation to
  `uniformFlowRadius`) infects the whole downstream `hCConv` chain (`hReach : uniformFlowRadius ≤
  expRho q` is the unprovable wall).  Plan v6 re-derives the regularity DIRECTLY on the uniform tube.

  ── WHAT LANDS (the target SHAPE, UNCONDITIONAL, at order 2 — no `expRho` anywhere).
    • `uniformFlowExp_contDiffOn_two_uniform` — for every `q ∈ K`,
          `ContDiffOn ℝ 2 (uniformFlowExp g gi hC hK q) (Metric.ball 0 (uniformFlowRadius g gi hC hK))`.
      DERIVED by packaging the banked, unconditional, per-point
      `HeatResidualBound.contDiffAt2_uniformFlowExp` (`ContDiffAt ℝ 2 (uniformFlowExp q) v` at every
      `‖v‖ < uniformFlowRadius`, built bespoke from the three uniform-tube Fréchet layers
      `uniformFlowExp_hasFDerivAt` / `uniformFlowExp_fderiv_hasFDerivAt` /
      `uniformFlowExp_hessianMap_differentiableAt`, all `expRho`-free) into `ContDiffOn` on the open
      ball via `ContDiffAt.contDiffWithinAt`.

  ── HONEST SCOPE.  This is the order-2 realisation of the Plan-v6 target
        `uniformFlowExp_contDiffOn_four_uniform : ∀ q ∈ K, ContDiffOn ℝ 4 (uniformFlowExp …)
           (ball 0 uniformFlowRadius)` (UNCONDITIONAL).
      C² is the highest order for which the uniform-tube variational tower is ALREADY closed
      unconditionally in-repo (up to the third Fréchet jet `uniformFlowExp_hessianMap_differentiableAt`,
      whose existence gives `D²φ` continuity ⟹ C²).  Climbing to C³/C⁴ requires extending the uniform-
      tube variational (doubling) tower one/two more jet orders (the fourth/fifth jet), a separate large
      construction; this file banks the honest order-2 floor of the target shape.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.PullbackNaturalityLocal

open QIQTH.Curvature QIQTH.ExpMap
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- **★ `uniformFlowExp_contDiffOn_two_uniform`.**  UNCONDITIONAL `ContDiffOn ℝ 2` of the flow
    exponential `φ_q := uniformFlowExp g gi hC hK q` on the uniform confinement ball
    `Metric.ball 0 (uniformFlowRadius g gi hC hK)`, for every base point `q ∈ K`.  NO `expRho`.
    DERIVED by promoting the banked, unconditional, per-point `contDiffAt2_uniformFlowExp` to
    `ContDiffOn` on the open ball (`ContDiffAt.contDiffWithinAt`).  The order-2 realisation of the
    Plan-v6 `expRho`-free target shape.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_contDiffOn_two_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    ContDiffOn ℝ 2 (uniformFlowExp g gi hC hK q)
      (Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  exact (contDiffAt2_uniformFlowExp g gi hC hK q hq v hv).contDiffWithinAt

end QIQTH.HeatResidualBound
