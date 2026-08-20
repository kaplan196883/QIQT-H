/-
  JointRNCRegularityInterfaceLocalGeneralK — GENERALIZATION of J4-857
  (`JointRNCRegularityInterfaceLocal.lean`) from the FIXED compact `K := Metric.closedBall q₀ 1`
  to an ARBITRARY compact `K` and an ARBITRARY INTERIOR base point `z₀ ∈ interior K`, feeding it the
  ABSTRACT-`K` joint `ContDiffAt ℝ 2` regularity of J4-884
  (`ExpMap.uniformInverseChart_jointContDiffAt_diag_generalK`) in place of the fixed-`K` input J4-856.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  local-analysis extraction: from `ContDiffAt ℝ 2` of the concrete abstract-`K` `uniformInverseChart`
  at an interior-diagonal point, it reads off the standard Taylor/jet bounds on a small ball.
  No `sorry`, no new axioms, no vacuous / unsatisfiable hypotheses, no conclusion-in-disguise,
  no existing file edited.  `a₁=R/6` stays CONDITIONAL on {hDuhamel, hDConv, hCConv}.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE DOES (and does NOT do).

  J4-857 built the neighbourhood-gated, correctly-normalized (positive-identity) local RNC-regularity
  bundle `JointSecondOrderRNCRegularityLocal` and PROVED it, but only for the FIXED compact
  `K := closedBall q₀ 1` at the diagonal, because its regularity input
  `uniformInverseChart_jointContDiffAt_diag` (J4-856) was fixed-`K`.  J4-884 lifted that regularity
  to an ARBITRARY compact `K` (matching the a₁=R/6 capstone's `{K : Set (Point n)} (hK : IsCompact K)`
  interface) at each interior-diagonal point.  This file MIRRORS J4-857's exact Taylor-remainder
  extraction technique but feeds it J4-884's abstract-`K` input, producing the abstract-`K` local
  interface `JointSecondOrderRNCRegularityLocalGeneralK` and its genuine, non-vacuous discharge
  `jointRNCRegularityLocalGeneralK_of_diag`.

  ## THE LOCAL INTERFACE — `JointSecondOrderRNCRegularityLocalGeneralK g gi hC hK z₀ hz₀ r C_W C_P C_Q i`.
  For an ARBITRARY compact `K`, interior base point `z₀ ∈ interior K`, and the fixed-base slice
  `V := uniformInverseChart g gi hC hK z₀`, on the ball `Metric.ball z₀ r`, with the CORRECT
  positive-identity normalization:
    • `hval`   — `V z₀ = 0` (the base charts to the origin);
    • `hVc2`   — `V` is `ContDiffAt ℝ 2` at `z₀` (the proved abstract-`K` joint regularity, restricted);
    • `hdiff`  — `V` is differentiable on the ball;
    • `hVdisp` — SECOND-ORDER displacement `‖V z − (z − z₀)‖ ≤ C_W‖z − z₀‖²` (identity to O(‖·‖²));
    • `hJet1`  — FIRST-jet modulus `‖DV_z(eᵢ) − eᵢ‖ ≤ C_P‖z − z₀‖`;
    • `hJet2`  — BOUNDED SECOND jet `‖D²V_z‖ ≤ C_Q`.
  Every field is genuinely PROVED (`jointRNCRegularityLocalGeneralK_of_diag`).  NONE equals `a₁ = R/6`.

  ## HONEST DISTANCE.  As with J4-857, this does NOT shrink `A1R6CapstoneConditionalOnRNC`'s hypothesis
  list: the banked sliver consumer requires the GLOBAL-`∀ y`, reflected-sign LITERAL
  `JointSecondOrderRNCRegularity` structure, which this neighbourhood-gated, positive-sign variant
  deliberately does not match.  What this file DOES establish, for the first time, is that the joint
  second-order regularity the campaign sought is GENUINELY TRUE and quantitatively extractable for the
  concrete chart at an arbitrary compact `K` / arbitrary interior base point — the object the capstone
  actually quantifies over — not merely at the assembly's fixed `closedBall q₀ 1`.
-/
import Mathlib
import QIQTH.UniformFlowCoherentChartReconciliationGeneralK
import QIQTH.PullbackNaturalityLocal
import QIQTH.SliverAssembly

open Filter Finset
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open scoped Topology BigOperators

namespace QIQTH.JointRNCRegularityLocalGeneralK

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ############################################################################
    ### The three diagonal "value + regularity" facts, at a GENERAL interior base `z₀ ∈ interior K`.
    ############################################################################ -/

/-- **Slice `C²`, DERIVED FROM the abstract-`K` joint diag result.**  The fixed-base slice
    `V := uniformInverseChart g gi hC hK z₀` is `ContDiffAt ℝ 2` at `z₀`, obtained by composing the
    JOINT abstract-`K` `ContDiffAt ℝ 2` map (`uniformInverseChart_jointContDiffAt_diag_generalK`,
    J4-884) with the smooth inclusion `z ↦ (z₀, z)`.  General-`K` analogue of J4-857's
    `uniformInverseChart_slice_contDiffAt_diag`. -/
theorem uniformInverseChart_slice_contDiffAt_diag_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K) :
    ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z₀) z₀ := by
  have hF := uniformInverseChart_jointContDiffAt_diag_generalK g gi hC hK z₀ hz₀
  have hmk : ContDiffAt ℝ 2 (fun z : Point n => ((z₀, z) : Point n × Point n)) z₀ :=
    ContDiffAt.prodMk contDiffAt_const contDiffAt_id
  have hcomp := hF.comp z₀ hmk
  simpa [Function.comp] using hcomp

/-- **Slice value `V z₀ = 0`, DERIVED.**  The base point charts to the origin, from the left-inverse
    germ at `v = 0` through `exp_{z₀}(0) = z₀`.  General-`K` analogue of J4-857's
    `uniformInverseChart_slice_value_diag`. -/
theorem uniformInverseChart_slice_value_diag_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K) :
    uniformInverseChart g gi hC hK z₀ z₀ = 0 := by
  have hz₀K : z₀ ∈ K := interior_subset hz₀
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨hgermC2, _⟩ := hspec z₀ hz₀K
  have hgerm := (hgermC2 0 (by rw [norm_zero]; exact hδ₀)).1
  have h := hgerm.eq_of_nhds
  rwa [uniformFlowExp_zero g gi hC hK z₀ hz₀K] at h

/-- **`Dφ_{z₀}(0) = Id`, DERIVED.**  The recentring exp chart's Jacobian at the origin is the identity.
    General-`K` analogue of J4-857's `uniformInverseChart_expFderiv_id_diag`. -/
theorem uniformInverseChart_expFderiv_id_diag_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K) :
    HasFDerivAt (uniformFlowExp g gi hC hK z₀)
      (ContinuousLinearMap.id ℝ (Point n)) 0 := by
  have hz₀K : z₀ ∈ K := interior_subset hz₀
  have hR : ‖(0 : Point n)‖ < uniformFlowRadius g gi hC hK := by
    rw [norm_zero]; exact uniformFlowRadius_pos g gi hC hK
  have hφdiff : DifferentiableAt ℝ (uniformFlowExp g gi hC hK z₀) 0 :=
    (contDiffAt2_uniformFlowExp g gi hC hK z₀ hz₀K 0 hR).differentiableAt (by norm_num)
  have hfderiv_id : fderiv ℝ (uniformFlowExp g gi hC hK z₀) 0
      = ContinuousLinearMap.id ℝ (Point n) := by
    obtain ⟨ρ₀, hρ₀, C_D, _, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
    have h0ρ : ‖(0 : Point n)‖ < ρ₀ := by rw [norm_zero]; exact hρ₀
    have hb := hnear z₀ hz₀K 0 h0ρ
    rw [norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  rw [← hfderiv_id]; exact hφdiff.hasFDerivAt

/-- **Slice Jacobian `DV_{z₀}(z₀) = Id`, DERIVED.**  POSITIVE sign, confirming the genuine geodesic
    inverse chart is `z ↦ z − z₀ + O(‖·‖²)`.  Route: differentiate the left-inverse germ
    `V(φ_{z₀} z) = z` at `z = 0`.  General-`K` analogue of J4-857's
    `uniformInverseChart_slice_fderiv_id_diag`. -/
theorem uniformInverseChart_slice_fderiv_id_diag_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K) :
    fderiv ℝ (uniformInverseChart g gi hC hK z₀) z₀
      = ContinuousLinearMap.id ℝ (Point n) := by
  have hz₀K : z₀ ∈ K := interior_subset hz₀
  set W := uniformInverseChart g gi hC hK z₀ with hWdef
  set φ := uniformFlowExp g gi hC hK z₀ with hφdef
  have hφfd : HasFDerivAt φ (ContinuousLinearMap.id ℝ (Point n)) 0 :=
    uniformInverseChart_expFderiv_id_diag_generalK g gi hC hK z₀ hz₀
  have hWdiff : DifferentiableAt ℝ W z₀ :=
    (uniformInverseChart_slice_contDiffAt_diag_generalK g gi hC hK z₀ hz₀).differentiableAt (by norm_num)
  have hφ0 : φ 0 = z₀ := uniformFlowExp_zero g gi hC hK z₀ hz₀K
  have hWfd0 : HasFDerivAt W (fderiv ℝ W z₀) (φ 0) := by rw [hφ0]; exact hWdiff.hasFDerivAt
  have hcomp : HasFDerivAt (fun z => W (φ z))
      ((fderiv ℝ W z₀).comp (ContinuousLinearMap.id ℝ (Point n))) 0 := hWfd0.comp 0 hφfd
  -- the left-inverse germ at `v = 0`.
  have hgerm : (fun z => W (φ z)) =ᶠ[nhds (0 : Point n)] (fun z => z) := by
    obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
    obtain ⟨hgermC2, _⟩ := hspec z₀ hz₀K
    exact (hgermC2 0 (by rw [norm_zero]; exact hδ₀)).1
  have hid_fd : HasFDerivAt (fun z : Point n => z)
      ((fderiv ℝ W z₀).comp (ContinuousLinearMap.id ℝ (Point n))) 0 :=
    hcomp.congr_of_eventuallyEq hgerm.symm
  have huniq := hid_fd.unique (hasFDerivAt_id 0)
  rwa [ContinuousLinearMap.comp_id] at huniq

/-! ############################################################################
    ### The local, correctly-normalized ABSTRACT-`K` interface bundle + its genuine discharge.
    ############################################################################ -/

/-- **★ `JointSecondOrderRNCRegularityLocalGeneralK`.**  The neighbourhood-gated, CORRECTLY-NORMALIZED
    (positive-identity) local variant of `JointSecondOrderRNCRegularity`, for an ARBITRARY compact `K`
    and interior base point `z₀ ∈ interior K`: quantitative joint second-order regularity of the
    concrete inverse chart `V := uniformInverseChart g gi hC hK z₀` on the ball `Metric.ball z₀ r`.
    Every field is genuinely provable from `uniformInverseChart_jointContDiffAt_diag_generalK` — see
    `jointRNCRegularityLocalGeneralK_of_diag`.  NOT `a₁ = R/6`. -/
structure JointSecondOrderRNCRegularityLocalGeneralK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K)
    (r C_W C_P C_Q : ℝ) (i : Fin n) : Prop where
  hr : 0 < r
  hCW : 0 ≤ C_W
  hCP : 0 ≤ C_P
  hCQ : 0 ≤ C_Q
  /-- The base charts to the origin. -/
  hval : uniformInverseChart g gi hC hK z₀ z₀ = 0
  /-- `V` is `C²` at the base point (the proved abstract-`K` joint regularity, restricted to the slice). -/
  hVc2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z₀) z₀
  /-- `V` is differentiable throughout the gate ball. -/
  hdiff : ∀ z ∈ Metric.ball z₀ r,
    DifferentiableAt ℝ (uniformInverseChart g gi hC hK z₀) z
  /-- SECOND-ORDER displacement: `V` is the identity to `O(‖z − z₀‖²)` (POSITIVE sign). -/
  hVdisp : ∀ z ∈ Metric.ball z₀ r,
    ‖uniformInverseChart g gi hC hK z₀ z - (z - z₀)‖ ≤ C_W * ‖z - z₀‖ ^ 2
  /-- FIRST-jet modulus: `∂ᵢ V = eᵢ + O(‖z − z₀‖)`. -/
  hJet1 : ∀ z ∈ Metric.ball z₀ r,
    ‖fderiv ℝ (uniformInverseChart g gi hC hK z₀) z (unitVec i) - unitVec i‖
      ≤ C_P * ‖z - z₀‖
  /-- BOUNDED SECOND jet: `‖D²V‖ ≤ C_Q` throughout the gate ball. -/
  hJet2 : ∀ z ∈ Metric.ball z₀ r,
    ‖fderiv ℝ (fun w => fderiv ℝ (uniformInverseChart g gi hC hK z₀) w) z‖
      ≤ C_Q

/-- **★★★ `jointRNCRegularityLocalGeneralK_of_diag` — THE PAYOFF: the abstract-`K` local interface is
    INHABITED.**  Genuinely, non-vacuously discharged from the proved abstract-`K` joint
    `ContDiffAt ℝ 2` of the concrete `uniformInverseChart` at each interior-diagonal point
    (`uniformInverseChart_jointContDiffAt_diag_generalK`, J4-884): for an ARBITRARY compact `K` and
    interior base point `z₀ ∈ interior K` there is a ball radius `r > 0` and finite constants
    `C_W, C_P, C_Q ≥ 0` such that the fixed-base slice satisfies the full quantitative second-order
    RNC-regularity bundle.  General-`K` analogue of J4-857's `jointRNCRegularityLocal_of_diag`.
    NOT `a₁ = R/6`. -/
theorem jointRNCRegularityLocalGeneralK_of_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K) (i : Fin n) :
    ∃ r C_W C_P C_Q : ℝ,
      JointSecondOrderRNCRegularityLocalGeneralK g gi hC hK z₀ hz₀ r C_W C_P C_Q i := by
  classical
  set V := uniformInverseChart g gi hC hK z₀ with hVdef
  -- proved facts.
  have hVc2 : ContDiffAt ℝ 2 V z₀ :=
    uniformInverseChart_slice_contDiffAt_diag_generalK g gi hC hK z₀ hz₀
  have hval : V z₀ = 0 := uniformInverseChart_slice_value_diag_generalK g gi hC hK z₀ hz₀
  have hVfd_id : fderiv ℝ V z₀ = ContinuousLinearMap.id ℝ (Point n) :=
    uniformInverseChart_slice_fderiv_id_diag_generalK g gi hC hK z₀ hz₀
  -- V' = first derivative on a nbhd `u`; V'' its ContDiffAt ℝ 1 derivative-of-derivative.
  obtain ⟨V', ⟨u, hu_nhds, hVderiv⟩, hV'c1⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (1 + 1 : ℕ) V z₀ by exact_mod_cast hVc2)
  obtain ⟨V'', ⟨u2, hu2_nhds, hV'deriv⟩, hV''c0⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (0 + 1 : ℕ) V' z₀ by exact_mod_cast hV'c1)
  -- `V' z₀ = fderiv V z₀ = id`.
  have hV'z₀ : V' z₀ = ContinuousLinearMap.id ℝ (Point n) := by
    have hmem : z₀ ∈ u := mem_of_mem_nhds hu_nhds
    have := (hVderiv z₀ hmem).fderiv
    rw [← this, hVfd_id]
  -- second-derivative bound near z₀ via continuity of V''.
  set M : ℝ := ‖V'' z₀‖ + 1 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hcont : ContinuousAt V'' z₀ := hV''c0.continuousAt
  have hbound_ev : ∀ᶠ z in nhds z₀, ‖V'' z‖ ≤ M := by
    have hmem : Set.Iio M ∈ nhds ‖V'' z₀‖ := Iio_mem_nhds (by rw [hMdef]; linarith)
    have h := (hcont.norm) hmem
    filter_upwards [h] with z hz
    exact le_of_lt hz
  -- assemble the gate ball `Metric.ball z₀ r ⊆ u ∩ u2 ∩ {‖V'' ·‖ ≤ M}`.
  have hset : u ∩ u2 ∩ {z | ‖V'' z‖ ≤ M} ∈ nhds z₀ :=
    Filter.inter_mem (Filter.inter_mem hu_nhds hu2_nhds) hbound_ev
  obtain ⟨r, hr0, hsub⟩ := Metric.mem_nhds_iff.mp hset
  refine ⟨r, M, M * ‖unitVec i‖, M, ?_⟩
  -- helper: pointwise facts on the ball.
  have hz_u : ∀ z ∈ Metric.ball z₀ r, z ∈ u := fun z hz => ((hsub hz).1).1
  have hz_u2 : ∀ z ∈ Metric.ball z₀ r, z ∈ u2 := fun z hz => ((hsub hz).1).2
  have hz_bd : ∀ z ∈ Metric.ball z₀ r, ‖V'' z‖ ≤ M := fun z hz => (hsub hz).2
  have hz₀ball : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr0
  -- operator-form first-jet modulus `‖V' z − id‖ ≤ M ‖z − z₀‖`, via mean value over segment.
  have hBop : ∀ z ∈ Metric.ball z₀ r,
      ‖V' z - ContinuousLinearMap.id ℝ (Point n)‖ ≤ M * ‖z - z₀‖ := by
    intro z hz
    have hseg_ball : segment ℝ z₀ z ⊆ Metric.ball z₀ r :=
      (convex_ball z₀ r).segment_subset hz₀ball hz
    have hderiv : ∀ w ∈ segment ℝ z₀ z, HasFDerivWithinAt V' (V'' w) (segment ℝ z₀ z) w :=
      fun w hw => (hV'deriv w (hz_u2 w (hseg_ball hw))).hasFDerivWithinAt
    have hbd : ∀ w ∈ segment ℝ z₀ z, ‖V'' w‖ ≤ M := fun w hw => hz_bd w (hseg_ball hw)
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbd
      (convex_segment z₀ z) (left_mem_segment ℝ z₀ z) (right_mem_segment ℝ z₀ z)
    rw [hV'z₀] at hmv
    simpa [norm_sub_rev] using hmv
  refine ⟨hr0, hM0, by positivity, hM0, hval, hVc2, ?_, ?_, ?_, ?_⟩
  · -- hdiff
    intro z hz; exact (hVderiv z (hz_u z hz)).differentiableAt
  · -- hVdisp (second-order displacement) via mean value on the affine remainder over the segment.
    intro z hz
    set R : Point n → Point n := fun w => V w - (w - z₀) with hRdef
    have hseg_ball : segment ℝ z₀ z ⊆ Metric.ball z₀ r :=
      (convex_ball z₀ r).segment_subset hz₀ball hz
    have hseg_cb : segment ℝ z₀ z ⊆ Metric.closedBall z₀ ‖z - z₀‖ :=
      (convex_closedBall z₀ ‖z - z₀‖).segment_subset
        (Metric.mem_closedBall_self (norm_nonneg _))
        (by rw [Metric.mem_closedBall, dist_eq_norm])
    have hRderiv : ∀ w ∈ segment ℝ z₀ z,
        HasFDerivWithinAt R (V' w - ContinuousLinearMap.id ℝ (Point n)) (segment ℝ z₀ z) w := by
      intro w hw
      have hVw : HasFDerivAt V (V' w) w := hVderiv w (hz_u w (hseg_ball hw))
      have haff : HasFDerivAt (fun w : Point n => w - z₀) (ContinuousLinearMap.id ℝ (Point n)) w :=
        (hasFDerivAt_id w).sub_const z₀
      exact (hVw.sub haff).hasFDerivWithinAt
    have hRbd : ∀ w ∈ segment ℝ z₀ z,
        ‖V' w - ContinuousLinearMap.id ℝ (Point n)‖ ≤ M * ‖z - z₀‖ := by
      intro w hw
      have hwr : ‖w - z₀‖ ≤ ‖z - z₀‖ := by
        have := hseg_cb hw; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
      calc ‖V' w - ContinuousLinearMap.id ℝ (Point n)‖
          ≤ M * ‖w - z₀‖ := hBop w (hseg_ball hw)
        _ ≤ M * ‖z - z₀‖ := by exact mul_le_mul_of_nonneg_left hwr hM0
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hRderiv hRbd
      (convex_segment z₀ z) (left_mem_segment ℝ z₀ z) (right_mem_segment ℝ z₀ z)
    -- `R z₀ = 0`, `R z = V z − (z − z₀)`.
    have hRz₀ : R z₀ = 0 := by rw [hRdef]; simp [hval]
    rw [hRz₀] at hmv
    calc ‖V z - (z - z₀)‖ = ‖R z - 0‖ := by rw [hRdef]; simp
      _ ≤ M * ‖z - z₀‖ * ‖z - z₀‖ := hmv
      _ = M * ‖z - z₀‖ ^ 2 := by ring
  · -- hJet1: apply the operator bound to `unitVec i`.
    intro z hz
    have hop := hBop z hz
    have : ‖(V' z - ContinuousLinearMap.id ℝ (Point n)) (unitVec i)‖
        ≤ ‖V' z - ContinuousLinearMap.id ℝ (Point n)‖ * ‖unitVec i‖ :=
      (V' z - ContinuousLinearMap.id ℝ (Point n)).le_opNorm (unitVec i)
    have hfd : fderiv ℝ V z = V' z := (hVderiv z (hz_u z hz)).fderiv
    rw [hfd]
    calc ‖V' z (unitVec i) - unitVec i‖
        = ‖(V' z - ContinuousLinearMap.id ℝ (Point n)) (unitVec i)‖ := by
          rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      _ ≤ ‖V' z - ContinuousLinearMap.id ℝ (Point n)‖ * ‖unitVec i‖ := this
      _ ≤ (M * ‖z - z₀‖) * ‖unitVec i‖ := by
          exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)
      _ = M * ‖unitVec i‖ * ‖z - z₀‖ := by ring
  · -- hJet2: `fderiv (fderiv V) z = fderiv V' z = V'' z`, bounded by `M`.
    intro z hz
    have hballnhds : Metric.ball z₀ r ∈ nhds z := Metric.isOpen_ball.mem_nhds hz
    have hfeq : fderiv ℝ V =ᶠ[nhds z] V' := by
      filter_upwards [hballnhds] with w hw
      exact (hVderiv w (hz_u w hw)).fderiv
    have h1 : fderiv ℝ (fun w => fderiv ℝ V w) z = fderiv ℝ V' z := hfeq.fderiv_eq
    have h2 : fderiv ℝ V' z = V'' z := (hV'deriv z (hz_u2 z hz)).fderiv
    rw [h1, h2]
    exact hz_bd z hz

end QIQTH.JointRNCRegularityLocalGeneralK

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.JointRNCRegularityLocalGeneralK
#print axioms uniformInverseChart_slice_contDiffAt_diag_generalK
#print axioms uniformInverseChart_slice_value_diag_generalK
#print axioms uniformInverseChart_slice_fderiv_id_diag_generalK
#print axioms jointRNCRegularityLocalGeneralK_of_diag
end AxiomChecks
