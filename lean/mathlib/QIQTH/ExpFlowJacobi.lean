/-
  ExpFlowJacobi — the COORDINATE second-order Jacobi equation for the exp-differential flow columns.

  This applies the neighbourhood-localized second-order Jacobi ODE
  (`jacobiVariation_secondOrder_nhds`, JacobiSecondOrderLocal.lean) to the ACTUAL columns of the
  exponential differential flow `Φ` supplied by `expDiff_flow_isGeodesicVariation`
  (ExpDiffVariation.lean).  For each fixed direction `w`, the flow column
  `V_w(τ) = (Φ τ) w` is a geodesic-variation field along the geodesic tube `expTube p v` on `[0,1]`
  (`HasDerivWithinAt … (Icc 0 1)`).  At any INTERIOR parameter `t ∈ (0,1)`, `Icc 0 1 ∈ 𝓝 t` upgrades
  the within-interval derivative to an honest `HasDerivAt`, so the geodesic-variation system holds
  `∀ᶠ` in `𝓝 t`, and `jacobiVariation_secondOrder_nhds` delivers the coordinate second-order Jacobi
  equation for the flow column:

        ξ''(t) = −jacobiOperator g gi (expTube … t).1 (expTube … t).2 (ξ t) (η t),
        ξ(τ) = ((Φ τ) w).1,  η(τ) = ((Φ τ) w).2.

  HONEST SCOPE.  This is still the COORDINATE form of the second-order Jacobi equation applied to the
  genuine exp-flow columns.  It does NOT prove the curvature identification `jacobiOperator = R̃`
  (the checkpointed #3 analytic core), nor the matrix form `B'' = −R̃ B`, nor `a₁ = R/6`.  It also
  keeps the `Φ 0 = id` and `fderiv exp_p v = π ∘ Φ(1) ∘ ι` data so the column flow remains tied to
  the actual differential of the exponential map.
-/
import Mathlib
import QIQTH.ExpDiffVariation
import QIQTH.JacobiSecondOrderLocal

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **The coordinate second-order Jacobi equation for the exp-differential flow columns at an
    interior parameter.**

    From `expDiff_flow_isGeodesicVariation` we obtain the exp-differential operator flow `Φ` with
    `Φ 0 = id`, `fderiv (expMap p) v = π ∘ Φ(1) ∘ ι`, and the first-order geodesic-variation system
    for each column `V_w(τ) = (Φ τ) w` on `[0,1]`.  At interior `t ∈ (0,1)`, `Icc 0 1 ∈ 𝓝 t` lets us
    upgrade the within-interval derivative to `HasDerivAt`, so the geodesic-variation hypothesis holds
    `∀ᶠ` in `𝓝 t`.  Applying `jacobiVariation_secondOrder_nhds` yields, for every direction `w`, the
    coordinate second-order Jacobi ODE for the position part `ξ = ((Φ ·) w).1`:
        `ξ''(t) = −jacobiOperator g gi (expTube … t).1 (expTube … t).2 (ξ t) ((Φ t w).2)`.

    Still the COORDINATE form; this does NOT prove `jacobiOperator = R̃`, `B'' = −R̃ B`, or
    `a₁ = R/6`. -/
theorem expFlow_column_coordinate_jacobi (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < QIQTH.ExpMap.expRho g gi hC p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      HasFDerivAt (QIQTH.ExpMap.expMap g gi hC p)
        (QIQTH.ExpMap.expJetPi.comp ((Φ 1).comp QIQTH.ExpMap.expJetIota)) v ∧
      ∀ w : Point n × Point n,
        HasDerivAt (deriv (fun τ => ((Φ τ) w).1))
          (-jacobiOperator g gi
              (QIQTH.ExpMap.expTube g gi hC p v t).1 (QIQTH.ExpMap.expTube g gi hC p v t).2
              ((Φ t) w).1 ((Φ t) w).2) t := by
  obtain ⟨Φ, hΦ0, hFD, hflow⟩ := expDiff_flow_isGeodesicVariation g gi hC p v hv
  refine ⟨Φ, hΦ0, hFD, fun w => ?_⟩
  -- The geodesic-variation system for the column `V_w(τ) = (Φ τ) w`, held `∀ᶠ` near `t`.
  have hVar : ∀ᶠ τ in nhds t,
      IsGeodesicVariationAt g gi
        (fun s => QIQTH.ExpMap.expTube g gi hC p v s) (fun s => (Φ s) w) τ := by
    refine Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) (fun τ hτ => ?_)
    -- On the interior interval, upgrade the within-`Icc` derivative to a genuine `HasDerivAt`.
    have hwithin := hflow w τ (Set.mem_Icc.mpr ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)
    exact hwithin.hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
  -- Apply the neighbourhood-localized second-order Jacobi ODE to the column flow.
  exact jacobiVariation_secondOrder_nhds g gi hC
    (γ := fun s => QIQTH.ExpMap.expTube g gi hC p v s) (V := fun s => (Φ s) w) hVar

end QIQTH.ExpMap
