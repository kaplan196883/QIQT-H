/-
  UniformFlowCoherentChartReconciliation — plan `tranquil-stargazing-fox.md` Task F: reconcile the
  genuinely COHERENT jointly-`ContDiffAt ℝ 2` chart `chartCoherent` (J4-855,
  `UniformFlowCoherentJointChart.lean`) with the `Classical.choose`-built downstream inverse chart
  `uniformInverseChart` (`UniformChartRadius.lean`).

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / local-inverse-uniqueness plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DELIVERABLE — Task F: the joint local equality + its consequence.

  * `uniformInverseChart_eq_coherent_near_diag` — ★ for `K := Metric.closedBall q₀ 1`, the COHERENT
    chart `chartCoherent` of J4-855 and the downstream `Classical.choose` chart `uniformInverseChart`
    AGREE as functions of BOTH the base point and the charted point, EVENTUALLY on a neighbourhood of
    the diagonal `(q₀, q₀)`:
        `(fun ξ => uniformInverseChart g gi hC hK ξ.1 ξ.2) =ᶠ[𝓝 (q₀,q₀)]
         (fun ξ => chartCoherent ξ.1 ξ.2)`.
    Proof = local-inverse UNIQUENESS: `chartCoherent` is a RIGHT inverse of `uniformFlowExp ξ.1`
    (`exp_{ξ.1}(chartCoherent ξ.1 ξ.2) = ξ.2`, J4-855 property (3)), while `uniformInverseChart ξ.1`
    is a LEFT-inverse germ (`uniformInverseChart ξ.1 (exp_{ξ.1} z) = z` near small `z`,
    `uniformInverseChart_huniformChart`).  For `ξ` near `(q₀,q₀)`: `ξ.1 ∈ K`, and `chartCoherent`'s
    joint continuity + `chartCoherent q₀ q₀ = 0` put `v := chartCoherent ξ.1 ξ.2` inside the uniform
    germ radius `δ₀`; then `uniformInverseChart ξ.1 ξ.2 = uniformInverseChart ξ.1 (exp_{ξ.1} v) = v`.

  * `uniformInverseChart_jointContDiffAt_diag` — ★★ THE PRIZE COROLLARY: the downstream chart is
    itself JOINTLY `ContDiffAt ℝ 2` at the diagonal,
        `ContDiffAt ℝ 2 (fun ξ => uniformInverseChart g gi hC hK ξ.1 ξ.2) (q₀, q₀)`,
    obtained by transporting `chartCoherent`'s joint `ContDiffAt ℝ 2` across the local equality
    (`ContDiffAt.congr_of_eventuallyEq`).  This is the exact JOINT (base-point-dependent) second-order
    regularity of the `Classical.choose` chart that the ~150-increment campaign (J4-681→791) repeatedly
    found ABSENT — now genuinely established, near the diagonal, for the concrete `uniformInverseChart`.

  ## WHAT THIS FILE DOES NOT DO (and the honest limit for Task G).
  It establishes joint `ContDiffAt ℝ 2` of `uniformInverseChart` at the diagonal (a NEIGHBOURHOOD-
  quality fact).  It does NOT — and CANNOT from this local datum — discharge the LITERAL structures
  `JointSecondOrderRNCRegularity` / `…Mixed`, because their jet fields (`hJetV`/`hJetPi`/…) are
  quantified `∀ y` GLOBALLY (`HasDerivAt … at every `y`), which no LOCAL chart (coherent or otherwise)
  can satisfy — the chart is `C²` only near the diagonal and takes junk values off the IFT image.  So
  Task G's literal discharge is blocked by the interfaces' unguarded universal quantifiers, NOT by any
  remaining regularity gap.  a₁=R/6 remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.
-/
import Mathlib
import QIQTH.UniformFlowCoherentJointChart
import QIQTH.UniformChartRadius

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★ Task-F — joint local equality of the coherent chart and the downstream `uniformInverseChart`.**
    For `K := Metric.closedBall q₀ 1`, the COHERENT jointly-`ContDiffAt ℝ 2` chart `chartCoherent`
    (J4-855) and the `Classical.choose`-built `uniformInverseChart` agree as functions of BOTH the base
    point and the charted point, eventually on a neighbourhood of the diagonal `(q₀,q₀)`.  Via
    local-inverse uniqueness: `chartCoherent` is a right inverse and `uniformInverseChart` a left-inverse
    germ of the SAME forward map `uniformFlowExp`.  Returns the coherent chart bundled with all three of
    its J4-855 properties PLUS the equality, so downstream consumers get one packaged object. -/
theorem uniformInverseChart_eq_coherent_near_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ∃ chartCoherent : Point n → Point n → Point n,
      ContDiffAt ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
        ((q₀, q₀) : Point n × Point n) ∧
      chartCoherent q₀ q₀ = 0 ∧
      (∀ᶠ ξ in nhds ((q₀, q₀) : Point n × Point n),
        uniformFlowExp g gi hC (isCompact_closedBall q₀ 1) ξ.1 (chartCoherent ξ.1 ξ.2) = ξ.2) ∧
      (fun ξ : Point n × Point n =>
          uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) ξ.1 ξ.2)
        =ᶠ[nhds ((q₀, q₀) : Point n × Point n)]
        (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2) := by
  classical
  set hK : IsCompact (Metric.closedBall q₀ 1) := isCompact_closedBall q₀ 1 with hKdef
  set K : Set (Point n) := Metric.closedBall q₀ 1 with hKsetdef
  -- the coherent chart (J4-855).
  obtain ⟨chartCoherent, hcd, hval, hinv⟩ := uniformFlow_coherent_joint_chart g gi hC q₀
  refine ⟨chartCoherent, hcd, hval, hinv, ?_⟩
  -- the uniform left-inverse germ at a single radius δ₀ over K.
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  -- (a) the base point lands in the open ball ⊆ K.
  have hball : ∀ᶠ ξ in nhds ((q₀, q₀) : Point n × Point n), ξ.1 ∈ Metric.ball q₀ 1 := by
    have hopen : IsOpen {ξ : Point n × Point n | ξ.1 ∈ Metric.ball q₀ 1} :=
      Metric.isOpen_ball.preimage continuous_fst
    have hmem : ((q₀, q₀) : Point n × Point n) ∈ {ξ : Point n × Point n | ξ.1 ∈ Metric.ball q₀ 1} :=
      Metric.mem_ball_self one_pos
    exact hopen.mem_nhds hmem
  -- (b) the coherent chart value stays within the germ radius δ₀ (joint continuity + value 0).
  have hsmall : ∀ᶠ ξ in nhds ((q₀, q₀) : Point n × Point n),
      chartCoherent ξ.1 ξ.2 ∈ Metric.ball (0 : Point n) δ₀ := by
    have hcont : ContinuousAt (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
        ((q₀, q₀) : Point n × Point n) := hcd.continuousAt
    refine hcont.eventually_mem ?_
    show Metric.ball (0 : Point n) δ₀ ∈ nhds (chartCoherent q₀ q₀)
    rw [hval]
    exact Metric.ball_mem_nhds 0 hδ₀
  filter_upwards [hinv, hball, hsmall] with ξ hξinv hξball hξsmall
  -- ξ.1 ∈ K.
  have hξ1K : ξ.1 ∈ K := by
    rw [hKsetdef]; exact Metric.ball_subset_closedBall hξball
  -- v := chartCoherent ξ.1 ξ.2 with ‖v‖ < δ₀.
  set v : Point n := chartCoherent ξ.1 ξ.2 with hvdef
  have hvδ₀ : ‖v‖ < δ₀ := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hξsmall
  -- the left-inverse germ at v.
  obtain ⟨hgerm, _hWc2⟩ := (hchart ξ.1 hξ1K).1 v hvδ₀
  have hleft : uniformInverseChart g gi hC hK ξ.1 (uniformFlowExp g gi hC hK ξ.1 v) = v :=
    hgerm.eq_of_nhds
  -- rewrite the forward image via the coherent right inverse.
  have hforward : uniformFlowExp g gi hC hK ξ.1 v = ξ.2 := hξinv
  rw [hforward] at hleft
  -- conclude equality of the two charts at ξ.
  show uniformInverseChart g gi hC hK ξ.1 ξ.2 = chartCoherent ξ.1 ξ.2
  rw [← hvdef]; exact hleft

/-- **★★ Task-F PRIZE COROLLARY — joint `ContDiffAt ℝ 2` of the downstream chart at the diagonal.**
    The concrete `Classical.choose`-built `uniformInverseChart g gi hC hK` is itself JOINTLY
    `ContDiffAt ℝ 2` at the diagonal point `(q₀,q₀)`, for `K := Metric.closedBall q₀ 1` — obtained by
    transporting the COHERENT chart's joint `ContDiffAt ℝ 2` (J4-855) across the local equality
    `uniformInverseChart_eq_coherent_near_diag` via `ContDiffAt.congr_of_eventuallyEq`.  This is the
    exact JOINT (base-point-dependent) second-order regularity of the incoherent per-base-point chart
    that the ~150-increment campaign found ABSENT from Mathlib and this repo — now genuinely established
    near the diagonal.  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_jointContDiffAt_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ContDiffAt ℝ 2
      (fun ξ : Point n × Point n =>
        uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) ξ.1 ξ.2)
      ((q₀, q₀) : Point n × Point n) := by
  obtain ⟨_chartCoherent, hcd, _hval, _hinv, hEq⟩ :=
    uniformInverseChart_eq_coherent_near_diag g gi hC q₀
  exact hcd.congr_of_eventuallyEq hEq

end QIQTH.ExpMap
