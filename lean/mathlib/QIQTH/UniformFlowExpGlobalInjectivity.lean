/-
  UniformFlowExpGlobalInjectivity — J4-871: GLOBAL `Set.InjOn` of the recentring chart
  `uniformFlowExp q` on the uniform source ball `ball 0 δ₀`, K-uniformly.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  No `sorry`, no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE.

  J4-870 (`ChartJetHFdFrontierClosed`) reduced `MixedDirectionsFieldHessianEnvelope.hFd` to the
  `GateFatExterior` gate-geometry predicate, and flagged that a Lean discharge of the fat-exterior
  fact for the CONCRETE flow-ball gate `S z = uniformFlowExp z '' ball 0 c` needs GLOBAL INJECTIVITY of
  `uniformFlowExp z` on a neighbourhood of `closedBall 0 c` — a fact NOT among the banked LOCAL-inverse
  germs (`uniformFlowExp_localInverse_exists`).

  This brick supplies exactly that missing global injectivity, K-uniformly, from the already-banked
  near-identity contraction bound:

    * `UniformChartRadius.uniformFlowExp_approximatesLinearOn` gives, at a single uniform radius
      `δ₀ > 0` and constant `c < 1`, `ApproximatesLinearOn (uniformFlowExp q) (id) (ball 0 δ₀) c` for
      every `q ∈ K` — i.e. `‖φ_q x − φ_q y − (x − y)‖ ≤ c‖x − y‖`.

    * Mathlib's `ApproximatesLinearOn.injOn` turns a near-identity contraction (`c < ‖f'⁻¹‖⁻¹`) into
      `Set.InjOn` on the source set.  For the approximating equiv `f' = id`, `‖f'⁻¹‖⁻¹ = 1`, so the
      already-established `c < 1` is EXACTLY the injectivity threshold.  The result is
      `uniformFlowExp_injOn`: a single uniform `δ₀` on which `uniformFlowExp q` is injective on
      `ball 0 δ₀` for every `q ∈ K`.  (The `Subsingleton (Point 0)` degenerate dimension is dispatched
      by the left disjunct.)

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.UniformChartRadius

open Set Metric
open QIQTH.Curvature QIQTH.ExpMap
open scoped Topology NNReal

namespace QIQTH.UniformFlowExpGlobalInjectivity

variable {n : ℕ}

/-- **★ J4-871 — global `InjOn` of the recentring chart on the uniform ball.**  There is a single
    radius `δ₀ > 0` (uniform over the compact `K`) such that for every `q ∈ K`, the recentring chart
    `φ_q = uniformFlowExp g gi hC hK q` is INJECTIVE on `Metric.ball 0 δ₀`.  Proof: the K-uniform
    near-identity `ApproximatesLinearOn (φ_q) id (ball 0 δ₀) c` (constant `c < 1`) is a contraction
    below the injectivity threshold `‖id⁻¹‖⁻¹ = 1`, so `ApproximatesLinearOn.injOn` fires.  Hypotheses
    ONLY the genuine geometric data `hC` + `IsCompact K`. -/
theorem uniformFlowExp_injOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ q ∈ K, Set.InjOn (uniformFlowExp g gi hC hK q) (Metric.ball 0 δ₀) := by
  obtain ⟨δ₀, hδ₀, c, hc1, happ⟩ :=
    QIQTH.HeatResidualBound.uniformFlowExp_approximatesLinearOn g gi hC hK
  refine ⟨δ₀, hδ₀, fun q hq => (happ q hq).injOn ?_⟩
  by_cases hsub : Subsingleton (Point n)
  · exact Or.inl hsub
  · right
    haveI hnt : Nontrivial (Point n) := not_subsingleton_iff_nontrivial.mp hsub
    -- `N = ‖(refl.symm : Point n →L[ℝ] Point n)‖₊ = ‖id‖₊ = 1`, so `N⁻¹ = 1 > c`.
    have hN : ‖((ContinuousLinearEquiv.refl ℝ (Point n)).symm : Point n →L[ℝ] Point n)‖₊ = 1 := by
      rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl]
      exact ContinuousLinearMap.nnnorm_id
    rw [hN]
    simpa using hc1

end QIQTH.UniformFlowExpGlobalInjectivity

section AxiomChecks
open QIQTH.UniformFlowExpGlobalInjectivity
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms uniformFlowExp_injOn
end AxiomChecks
