/-
  UniformFlowCoherentChartReconciliationGeneralK — GENERALIZATION of J4-856
  (`UniformFlowCoherentChartReconciliation.lean`) from the FIXED `K := Metric.closedBall q₀ 1` to an
  ARBITRARY compact `K` and an ARBITRARY interior base point `z₀ ∈ interior K`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / local-inverse-uniqueness plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DELIVERABLES.

  * `uniformInverseChart_eq_coherent_near_diag_generalK` — **general-`K` Task F.**  For an arbitrary
    compact `K` and interior base point `z₀ ∈ interior K`, the COHERENT chart `chartCoherent`
    (general-`K` J4-855) and the `Classical.choose`-built `uniformInverseChart g gi hC hK` AGREE as
    functions of BOTH the base point and the charted point, eventually on a neighbourhood of the
    diagonal `(z₀, z₀)`.  Same local-inverse uniqueness argument as J4-856.

  * `uniformInverseChart_jointContDiffAt_diag_generalK` — **★★ THE general-`K` PRIZE COROLLARY.**  The
    concrete `Classical.choose`-built `uniformInverseChart g gi hC hK` is itself JOINTLY
    `ContDiffAt ℝ 2` at each interior-diagonal point `(z₀, z₀)`, for an ARBITRARY compact `K` matching
    the capstone's `{K : Set (Point n)} (hK : IsCompact K)` interface.  This lifts the fixed-`K`
    diagonal regularity of J4-856 to the abstract `K` the a₁=R/6 capstone actually quantifies over.

  * `uniformInverseChart_jointContDiffOn_tube` — **the diagonal-TUBE joint `ContDiffOn ℝ 2`.**  There
    is an OPEN set `T` containing the whole interior diagonal `{(z,z) : z ∈ interior K}` on which
    `fun ξ => uniformInverseChart g gi hC hK ξ.1 ξ.2` is jointly `ContDiffOn ℝ 2`.  Assembled from the
    per-interior-point diagonal `ContDiffAt` as a union of the open C²-neighbourhoods.

  ## WHAT THIS FILE DOES NOT DO (and the honest limit).
  It establishes joint `ContDiffOn ℝ 2` of `uniformInverseChart` on an open tube around the interior
  diagonal, for an arbitrary compact `K`.  It does NOT — and cannot from this local datum — discharge
  the LITERAL `JointSecondOrderRNCRegularity` structure whose jet fields are quantified `∀ y`
  GLOBALLY.  a₁=R/6 remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.
-/
import Mathlib
import QIQTH.UniformFlowCoherentJointChartGeneralK
import QIQTH.UniformChartRadius

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★ general-`K` Task F — joint local equality of the coherent chart and `uniformInverseChart`.**
    For an arbitrary compact `K` and interior base point `z₀ ∈ interior K`, the general-`K` COHERENT
    chart `chartCoherent` and the `Classical.choose`-built `uniformInverseChart g gi hC hK` agree as
    functions of BOTH the base point and the charted point, eventually on a neighbourhood of the
    diagonal `(z₀,z₀)`.  Via local-inverse uniqueness (same as J4-856). -/
theorem uniformInverseChart_eq_coherent_near_diag_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K) :
    ∃ chartCoherent : Point n → Point n → Point n,
      ContDiffAt ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
        ((z₀, z₀) : Point n × Point n) ∧
      chartCoherent z₀ z₀ = 0 ∧
      (∀ᶠ ξ in nhds ((z₀, z₀) : Point n × Point n),
        uniformFlowExp g gi hC hK ξ.1 (chartCoherent ξ.1 ξ.2) = ξ.2) ∧
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2)
        =ᶠ[nhds ((z₀, z₀) : Point n × Point n)]
        (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2) := by
  classical
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz₀)
  -- the coherent chart (general-`K` J4-855).
  obtain ⟨chartCoherent, hcd, hval, hinv⟩ :=
    uniformFlow_coherent_joint_chart_generalK g gi hC hK z₀ hz₀
  refine ⟨chartCoherent, hcd, hval, hinv, ?_⟩
  -- the uniform left-inverse germ at a single radius δ₀ over K.
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  -- (a) the base point lands in `ball z₀ r₁ ⊆ K`.
  have hball : ∀ᶠ ξ in nhds ((z₀, z₀) : Point n × Point n), ξ.1 ∈ Metric.ball z₀ r₁ := by
    have hopen : IsOpen {ξ : Point n × Point n | ξ.1 ∈ Metric.ball z₀ r₁} :=
      Metric.isOpen_ball.preimage continuous_fst
    have hmem : ((z₀, z₀) : Point n × Point n) ∈ {ξ : Point n × Point n | ξ.1 ∈ Metric.ball z₀ r₁} :=
      Metric.mem_ball_self hr₁pos
    exact hopen.mem_nhds hmem
  -- (b) the coherent chart value stays within the germ radius δ₀ (joint continuity + value 0).
  have hsmall : ∀ᶠ ξ in nhds ((z₀, z₀) : Point n × Point n),
      chartCoherent ξ.1 ξ.2 ∈ Metric.ball (0 : Point n) δ₀ := by
    have hcont : ContinuousAt (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
        ((z₀, z₀) : Point n × Point n) := hcd.continuousAt
    refine hcont.eventually_mem ?_
    show Metric.ball (0 : Point n) δ₀ ∈ nhds (chartCoherent z₀ z₀)
    rw [hval]
    exact Metric.ball_mem_nhds 0 hδ₀
  filter_upwards [hinv, hball, hsmall] with ξ hξinv hξball hξsmall
  -- ξ.1 ∈ K.
  have hξ1K : ξ.1 ∈ K := interior_subset (hr₁sub hξball)
  -- v := chartCoherent ξ.1 ξ.2 with ‖v‖ < δ₀.
  set v : Point n := chartCoherent ξ.1 ξ.2 with hvdef
  have hvδ₀ : ‖v‖ < δ₀ := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hξsmall
  -- the left-inverse germ at v.
  obtain ⟨hgerm, _hWc2⟩ := (hchart ξ.1 hξ1K).1 v hvδ₀
  have hleft : uniformInverseChart g gi hC hK ξ.1 (uniformFlowExp g gi hC hK ξ.1 v) = v :=
    hgerm.eq_of_nhds
  have hforward : uniformFlowExp g gi hC hK ξ.1 v = ξ.2 := hξinv
  rw [hforward] at hleft
  show uniformInverseChart g gi hC hK ξ.1 ξ.2 = chartCoherent ξ.1 ξ.2
  rw [← hvdef]; exact hleft

/-- **★★ general-`K` Task-F PRIZE COROLLARY — joint `ContDiffAt ℝ 2` of the downstream chart at each
    interior-diagonal point.**  The concrete `Classical.choose`-built `uniformInverseChart g gi hC hK`
    is itself JOINTLY `ContDiffAt ℝ 2` at each interior-diagonal point `(z₀,z₀)`, `z₀ ∈ interior K`,
    for an ARBITRARY compact `K` — transported from the coherent chart across the local equality via
    `ContDiffAt.congr_of_eventuallyEq`.  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_jointContDiffAt_diag_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K) :
    ContDiffAt ℝ 2
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2)
      ((z₀, z₀) : Point n × Point n) := by
  obtain ⟨_chartCoherent, hcd, _hval, _hinv, hEq⟩ :=
    uniformInverseChart_eq_coherent_near_diag_generalK g gi hC hK z₀ hz₀
  exact hcd.congr_of_eventuallyEq hEq

/-- **The diagonal-TUBE joint `ContDiffOn ℝ 2`.**  There is an OPEN set `T` containing the whole
    interior diagonal `{(z,z) : z ∈ interior K}` on which `fun ξ => uniformInverseChart g gi hC hK ξ.1
    ξ.2` is jointly `ContDiffOn ℝ 2`.  Assembled from the per-interior-point diagonal `ContDiffAt`
    (`uniformInverseChart_jointContDiffAt_diag_generalK`) as the union of the open C²-neighbourhoods
    supplied by each `ContDiffAt`.  This is the genuine base-point-dependent second-order joint
    regularity over a neighbourhood of the diagonal, for an arbitrary compact `K`. -/
theorem uniformInverseChart_jointContDiffOn_tube (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ T : Set (Point n × Point n), IsOpen T ∧
      (∀ z ∈ interior K, ((z, z) : Point n × Point n) ∈ T) ∧
      ContDiffOn ℝ 2
        (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) T := by
  classical
  set f : Point n × Point n → Point n :=
    fun ξ => uniformInverseChart g gi hC hK ξ.1 ξ.2 with hfdef
  -- the OPEN set where `f` is jointly `ContDiffAt ℝ 2`.
  set T : Set (Point n × Point n) := {ξ | ContDiffAt ℝ 2 f ξ} with hTdef
  have hTopen : IsOpen T := by
    rw [hTdef]
    -- ContDiffAt is an open condition: each point has a C²-neighbourhood.
    rw [isOpen_iff_mem_nhds]
    intro ξ hξ
    have hξ' : ContDiffAt ℝ 2 f ξ := hξ
    obtain ⟨u, hu_nhds, hu_cd⟩ := hξ'.contDiffOn (m := 2) le_rfl (by norm_num)
    obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.mp hu_nhds
    refine Filter.mem_of_superset (hVopen.mem_nhds hVmem) ?_
    intro ζ hζ
    show ContDiffAt ℝ 2 f ζ
    exact (hu_cd.mono hVsub).contDiffAt (hVopen.mem_nhds hζ)
  refine ⟨T, hTopen, ?_, ?_⟩
  · intro z hz
    show ContDiffAt ℝ 2 f ((z, z) : Point n × Point n)
    exact uniformInverseChart_jointContDiffAt_diag_generalK g gi hC hK z hz
  · intro ξ hξ
    have hcda : ContDiffAt ℝ 2 f ξ := hξ
    exact hcda.contDiffWithinAt

end QIQTH.ExpMap
