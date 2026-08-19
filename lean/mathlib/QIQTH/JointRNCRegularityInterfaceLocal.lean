/-
  JointRNCRegularityInterfaceLocal — plan `tranquil-stargazing-fox.md` culmination: the FIRST genuinely
  NON-VACUOUS, machine-checked joint second-order RNC-chart regularity fact of the whole a₁=R/6
  chart-regularity campaign (J4-681→856), extracted MECHANICALLY from the now-PROVED joint C² regularity
  `ExpMap.uniformInverseChart_jointContDiffAt_diag` (J4-856).

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  local-analysis extraction: from `ContDiffAt ℝ 2` of the concrete `uniformInverseChart` at the diagonal,
  it reads off the standard Taylor/jet bounds on a small ball.  No `sorry`, no new axioms, no vacuous /
  unsatisfiable hypotheses, no conclusion-in-disguise, no existing file edited.  `a₁=R/6` stays
  CONDITIONAL on {hDuhamel, hDConv, hCConv}.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE EXISTS (and what it DOES and does NOT do vs. the literal `JointSecondOrderRNCRegularity`).

  The banked structures `JointRNCRegularityInterface.JointSecondOrderRNCRegularity` (J4-792) and its
  mixed twin (J4-794) are the named differential-geometry frontier of the order-2 sliver rate.  They are
  NOT literally dischargeable from `uniformInverseChart_jointContDiffAt_diag` for TWO independent reasons,
  documented honestly in `UniformFlowCoherentChartReconciliation.lean` and re-confirmed here:

    (i)  their jet fields (`hJetV`/`hJetPi`/`hJetQ`) are quantified `∀ y` GLOBALLY (`HasDerivAt … y` at
         EVERY `y`), while the proved regularity is `C²` only NEAR the diagonal — off the IFT image the
         `Classical.choose` chart takes junk values, so no global jet can hold;
    (ii) a SIGN/normalization mismatch: the interface's `hVdisp_on` demands `chart z ≈ −z` (reflected),
         whereas the genuine geodesic inverse chart is `chart z ≈ z − z₀` (POSITIVE identity to first
         order — `chartField_fderiv_center` proves `DV_z(z) = Id`, not `−Id`).  Downstream the sign is
         immaterial because the van-Vleck Gaussian `gaussDdim` is EVEN, but the banked consumer
         hard-codes the `+z` form, so the literal structure is not consumer-compatible either.

  So a LITERAL discharge of `JointSecondOrderRNCRegularity` is structurally blocked at the INTERFACE
  boundary (unguarded `∀ y` + hard-coded reflected sign), NOT by any remaining regularity gap — the
  regularity itself is now PROVED.  This file therefore does the honest, genuinely-new thing: it defines
  the CORRECTLY-NORMALIZED, NEIGHBOURHOOD-GATED variant `JointSecondOrderRNCRegularityLocal` and PROVES
  an instance of it, unconditionally, from `uniformInverseChart_jointContDiffAt_diag`.

  ## THE LOCAL INTERFACE — `JointSecondOrderRNCRegularityLocal g gi hC q₀ r C_W C_P C_Q i`.
  For `K := Metric.closedBall q₀ 1` and the fixed-base slice `V := uniformInverseChart g gi hC hK q₀`,
  on the ball `Metric.ball q₀ r`, with the CORRECT positive-identity normalization:
    • `hval`   — `V q₀ = 0` (the base charts to the origin);
    • `hVc2`   — `V` is `ContDiffAt ℝ 2` at `q₀` (the proved joint regularity, restricted to the slice);
    • `hdiff`  — `V` is differentiable on the ball;
    • `hVdisp` — SECOND-ORDER displacement `‖V z − (z − q₀)‖ ≤ C_W‖z − q₀‖²` (identity to O(‖·‖²));
    • `hJet1`  — FIRST-jet modulus `‖DV_z(eᵢ) − eᵢ‖ ≤ C_P‖z − q₀‖`;
    • `hJet2`  — BOUNDED SECOND jet `‖D²V_z‖ ≤ C_Q`.
  Every field is genuinely PROVED (`jointRNCRegularityLocal_of_diag`), so this bundle is INHABITED — the
  first non-vacuous, non-hypothetical joint second-order RNC regularity certificate in the campaign.
  NONE of the fields equals `a₁ = R/6`.

  ## HONEST DISTANCE.  This does NOT shrink `A1R6CapstoneConditionalOnRNC`'s hypothesis list: the banked
  sliver consumer requires the GLOBAL-`∀ y`, reflected-sign literal structure (see (i)/(ii) above), which
  this local variant deliberately does not match.  Re-threading the capstone would require re-deriving the
  entire sliver chain with neighbourhood-gated, positive-sign hypotheses (a large, separate engineering
  task, NOT a math gap — the Gaussian evenness makes the sign immaterial in principle).  What this file
  DOES establish, for the first time, is that the joint second-order regularity the campaign spent
  ~150 increments seeking is GENUINELY TRUE and quantitatively extractable for the concrete chart.
-/
import Mathlib
import QIQTH.UniformFlowCoherentChartReconciliation
import QIQTH.ChartJetBounds
import QIQTH.SliverAssembly

open Filter Finset
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open scoped Topology BigOperators

namespace QIQTH.JointRNCRegularityLocal

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ############################################################################
    ### The three diagonal "value + regularity" facts, at a GENERAL base `q₀`.
    ############################################################################ -/

/-- **Slice `C²`, DERIVED FROM the joint diag result.**  The fixed-base slice
    `V := uniformInverseChart g gi hC (closedBall q₀ 1) q₀` is `ContDiffAt ℝ 2` at `q₀`, obtained by
    composing the JOINT `ContDiffAt ℝ 2` map (`uniformInverseChart_jointContDiffAt_diag`, J4-856) with
    the smooth inclusion `z ↦ (q₀, z)`.  This is the genuinely-new general-base regularity the
    ~150-increment campaign found absent (`ChartJetBounds` only had the assembly base `0`). -/
theorem uniformInverseChart_slice_contDiffAt_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ContDiffAt ℝ 2 (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀) q₀ := by
  have hF := uniformInverseChart_jointContDiffAt_diag g gi hC q₀
  have hmk : ContDiffAt ℝ 2 (fun z : Point n => ((q₀, z) : Point n × Point n)) q₀ :=
    ContDiffAt.prodMk contDiffAt_const contDiffAt_id
  have hcomp := hF.comp q₀ hmk
  -- `(fun ξ => uniformInverseChart … ξ.1 ξ.2) ∘ (fun z => (q₀, z)) = uniformInverseChart … q₀`.
  simpa [Function.comp] using hcomp

/-- **Slice value `V q₀ = 0`, DERIVED.**  The base point charts to the origin: `uniformInverseChart …
    q₀ q₀ = 0`, from the left-inverse germ at `v = 0` through `exp_{q₀}(0) = q₀`.  General-base
    analogue of `chartField_centerValue_base0`. -/
theorem uniformInverseChart_slice_value_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀ q₀ = 0 := by
  set hK := isCompact_closedBall q₀ 1 with hKdef
  have hq₀ : q₀ ∈ Metric.closedBall q₀ 1 := Metric.mem_closedBall_self (by norm_num)
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨hgermC2, _⟩ := hspec q₀ hq₀
  have hgerm := (hgermC2 0 (by rw [norm_zero]; exact hδ₀)).1
  have h := hgerm.eq_of_nhds
  rwa [uniformFlowExp_zero g gi hC hK q₀ hq₀] at h

/-- **`Dφ_{q₀}(0) = Id`, DERIVED.**  The recentring exp chart's Jacobian at the origin is the identity,
    general-base analogue of `expFlow_fderiv_id_center`. -/
theorem uniformInverseChart_expFderiv_id_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    HasFDerivAt (uniformFlowExp g gi hC (isCompact_closedBall q₀ 1) q₀)
      (ContinuousLinearMap.id ℝ (Point n)) 0 := by
  set hK := isCompact_closedBall q₀ 1 with hKdef
  have hq₀ : q₀ ∈ Metric.closedBall q₀ 1 := Metric.mem_closedBall_self (by norm_num)
  have hR : ‖(0 : Point n)‖ < uniformFlowRadius g gi hC hK := by
    rw [norm_zero]; exact uniformFlowRadius_pos g gi hC hK
  have hφdiff : DifferentiableAt ℝ (uniformFlowExp g gi hC hK q₀) 0 :=
    (contDiffAt2_uniformFlowExp g gi hC hK q₀ hq₀ 0 hR).differentiableAt (by norm_num)
  have hfderiv_id : fderiv ℝ (uniformFlowExp g gi hC hK q₀) 0
      = ContinuousLinearMap.id ℝ (Point n) := by
    obtain ⟨ρ₀, hρ₀, C_D, _, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
    have h0ρ : ‖(0 : Point n)‖ < ρ₀ := by rw [norm_zero]; exact hρ₀
    have hb := hnear q₀ hq₀ 0 h0ρ
    rw [norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  rw [← hfderiv_id]; exact hφdiff.hasFDerivAt

/-- **Slice Jacobian `DV_{q₀}(q₀) = Id`, DERIVED.**  The fixed-base slice's Jacobian at the base point is
    the identity — POSITIVE sign, confirming the genuine geodesic inverse chart is `z ↦ z − q₀ + O(‖·‖²)`,
    NOT the reflected `−z` the literal interface models.  Route: differentiate the left-inverse germ
    `V(φ_{q₀} z) = z` at `z = 0` with `Dφ_{q₀}(0) = Id` and `V` differentiable at `φ_{q₀}(0) = q₀`.
    General-base analogue of `chartField_fderiv_center`. -/
theorem uniformInverseChart_slice_fderiv_id_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    fderiv ℝ (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀) q₀
      = ContinuousLinearMap.id ℝ (Point n) := by
  set hK := isCompact_closedBall q₀ 1 with hKdef
  have hq₀ : q₀ ∈ Metric.closedBall q₀ 1 := Metric.mem_closedBall_self (by norm_num)
  set W := uniformInverseChart g gi hC hK q₀ with hWdef
  set φ := uniformFlowExp g gi hC hK q₀ with hφdef
  have hφfd : HasFDerivAt φ (ContinuousLinearMap.id ℝ (Point n)) 0 :=
    uniformInverseChart_expFderiv_id_diag g gi hC q₀
  have hWdiff : DifferentiableAt ℝ W q₀ :=
    (uniformInverseChart_slice_contDiffAt_diag g gi hC q₀).differentiableAt (by norm_num)
  have hφ0 : φ 0 = q₀ := uniformFlowExp_zero g gi hC hK q₀ hq₀
  have hWfd0 : HasFDerivAt W (fderiv ℝ W q₀) (φ 0) := by rw [hφ0]; exact hWdiff.hasFDerivAt
  have hcomp : HasFDerivAt (fun z => W (φ z))
      ((fderiv ℝ W q₀).comp (ContinuousLinearMap.id ℝ (Point n))) 0 := hWfd0.comp 0 hφfd
  -- the left-inverse germ at `v = 0`.
  have hgerm : (fun z => W (φ z)) =ᶠ[nhds (0 : Point n)] (fun z => z) := by
    obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
    obtain ⟨hgermC2, _⟩ := hspec q₀ hq₀
    exact (hgermC2 0 (by rw [norm_zero]; exact hδ₀)).1
  have hid_fd : HasFDerivAt (fun z : Point n => z)
      ((fderiv ℝ W q₀).comp (ContinuousLinearMap.id ℝ (Point n))) 0 :=
    hcomp.congr_of_eventuallyEq hgerm.symm
  have huniq := hid_fd.unique (hasFDerivAt_id 0)
  rwa [ContinuousLinearMap.comp_id] at huniq

/-! ############################################################################
    ### The local, correctly-normalized interface bundle + its genuine discharge.
    ############################################################################ -/

/-- **★ `JointSecondOrderRNCRegularityLocal`.**  The neighbourhood-gated, CORRECTLY-NORMALIZED
    (positive-identity) local variant of `JointSecondOrderRNCRegularity`: quantitative joint
    second-order regularity of the concrete inverse chart `V := uniformInverseChart g gi hC hK q₀` on the
    ball `Metric.ball q₀ r`.  Unlike the literal (globally-`∀ y`, reflected-sign) interface, EVERY field
    here is genuinely provable from `uniformInverseChart_jointContDiffAt_diag` — see
    `jointRNCRegularityLocal_of_diag`.  NOT `a₁ = R/6`. -/
structure JointSecondOrderRNCRegularityLocal
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) (r C_W C_P C_Q : ℝ) (i : Fin n) : Prop where
  hr : 0 < r
  hCW : 0 ≤ C_W
  hCP : 0 ≤ C_P
  hCQ : 0 ≤ C_Q
  /-- The base charts to the origin. -/
  hval : uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀ q₀ = 0
  /-- `V` is `C²` at the base point (the proved joint regularity, restricted to the fixed-base slice). -/
  hVc2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀) q₀
  /-- `V` is differentiable throughout the gate ball. -/
  hdiff : ∀ z ∈ Metric.ball q₀ r,
    DifferentiableAt ℝ (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀) z
  /-- SECOND-ORDER displacement: `V` is the identity to `O(‖z − q₀‖²)` (POSITIVE sign). -/
  hVdisp : ∀ z ∈ Metric.ball q₀ r,
    ‖uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀ z - (z - q₀)‖ ≤ C_W * ‖z - q₀‖ ^ 2
  /-- FIRST-jet modulus: `∂ᵢ V = eᵢ + O(‖z − q₀‖)`. -/
  hJet1 : ∀ z ∈ Metric.ball q₀ r,
    ‖fderiv ℝ (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀) z (unitVec i) - unitVec i‖
      ≤ C_P * ‖z - q₀‖
  /-- BOUNDED SECOND jet: `‖D²V‖ ≤ C_Q` throughout the gate ball. -/
  hJet2 : ∀ z ∈ Metric.ball q₀ r,
    ‖fderiv ℝ (fun w => fderiv ℝ (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀) w) z‖
      ≤ C_Q

/-- **★★★ `jointRNCRegularityLocal_of_diag` — THE PAYOFF: the local interface is INHABITED.**
    Genuinely, non-vacuously discharged from the proved joint `ContDiffAt ℝ 2` of the concrete
    `uniformInverseChart` at the diagonal (`uniformInverseChart_jointContDiffAt_diag`, J4-856): there is a
    ball radius `r > 0` and finite constants `C_W, C_P, C_Q ≥ 0` such that the fixed-base slice satisfies
    the full quantitative second-order RNC-regularity bundle.  This is the FIRST machine-checked,
    non-hypothetical instance of a joint second-order RNC regularity fact for the concrete chart in the
    entire a₁=R/6 chart-regularity campaign.  NOT `a₁ = R/6`. -/
theorem jointRNCRegularityLocal_of_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) (i : Fin n) :
    ∃ r C_W C_P C_Q : ℝ,
      JointSecondOrderRNCRegularityLocal g gi hC q₀ r C_W C_P C_Q i := by
  classical
  set hK := isCompact_closedBall q₀ 1 with hKdef
  set V := uniformInverseChart g gi hC hK q₀ with hVdef
  -- proved facts.
  have hVc2 : ContDiffAt ℝ 2 V q₀ := uniformInverseChart_slice_contDiffAt_diag g gi hC q₀
  have hval : V q₀ = 0 := uniformInverseChart_slice_value_diag g gi hC q₀
  have hVfd_id : fderiv ℝ V q₀ = ContinuousLinearMap.id ℝ (Point n) :=
    uniformInverseChart_slice_fderiv_id_diag g gi hC q₀
  -- V' = first derivative on a nbhd `u`; V'' its ContDiffAt ℝ 1 derivative-of-derivative.
  obtain ⟨V', ⟨u, hu_nhds, hVderiv⟩, hV'c1⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (1 + 1 : ℕ) V q₀ by exact_mod_cast hVc2)
  obtain ⟨V'', ⟨u2, hu2_nhds, hV'deriv⟩, hV''c0⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (0 + 1 : ℕ) V' q₀ by exact_mod_cast hV'c1)
  -- `V' q₀ = fderiv V q₀ = id`.
  have hV'q₀ : V' q₀ = ContinuousLinearMap.id ℝ (Point n) := by
    have hmem : q₀ ∈ u := mem_of_mem_nhds hu_nhds
    have := (hVderiv q₀ hmem).fderiv
    rw [← this, hVfd_id]
  -- second-derivative bound near q₀ via continuity of V''.
  set M : ℝ := ‖V'' q₀‖ + 1 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hcont : ContinuousAt V'' q₀ := hV''c0.continuousAt
  have hbound_ev : ∀ᶠ z in nhds q₀, ‖V'' z‖ ≤ M := by
    have hmem : Set.Iio M ∈ nhds ‖V'' q₀‖ := Iio_mem_nhds (by rw [hMdef]; linarith)
    have h := (hcont.norm) hmem
    filter_upwards [h] with z hz
    exact le_of_lt hz
  -- assemble the gate ball `Metric.ball q₀ r ⊆ u ∩ u2 ∩ {‖V'' ·‖ ≤ M}`.
  have hset : u ∩ u2 ∩ {z | ‖V'' z‖ ≤ M} ∈ nhds q₀ :=
    Filter.inter_mem (Filter.inter_mem hu_nhds hu2_nhds) hbound_ev
  obtain ⟨r, hr0, hsub⟩ := Metric.mem_nhds_iff.mp hset
  refine ⟨r, M, M * ‖unitVec i‖, M, ?_⟩
  -- helper: pointwise facts on the ball.
  have hz_u : ∀ z ∈ Metric.ball q₀ r, z ∈ u := fun z hz => ((hsub hz).1).1
  have hz_u2 : ∀ z ∈ Metric.ball q₀ r, z ∈ u2 := fun z hz => ((hsub hz).1).2
  have hz_bd : ∀ z ∈ Metric.ball q₀ r, ‖V'' z‖ ≤ M := fun z hz => (hsub hz).2
  have hq₀ball : q₀ ∈ Metric.ball q₀ r := Metric.mem_ball_self hr0
  -- operator-form first-jet modulus `‖V' z − id‖ ≤ M ‖z − q₀‖`, via mean value over segment.
  have hBop : ∀ z ∈ Metric.ball q₀ r,
      ‖V' z - ContinuousLinearMap.id ℝ (Point n)‖ ≤ M * ‖z - q₀‖ := by
    intro z hz
    have hseg_ball : segment ℝ q₀ z ⊆ Metric.ball q₀ r :=
      (convex_ball q₀ r).segment_subset hq₀ball hz
    have hderiv : ∀ w ∈ segment ℝ q₀ z, HasFDerivWithinAt V' (V'' w) (segment ℝ q₀ z) w :=
      fun w hw => (hV'deriv w (hz_u2 w (hseg_ball hw))).hasFDerivWithinAt
    have hbd : ∀ w ∈ segment ℝ q₀ z, ‖V'' w‖ ≤ M := fun w hw => hz_bd w (hseg_ball hw)
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbd
      (convex_segment q₀ z) (left_mem_segment ℝ q₀ z) (right_mem_segment ℝ q₀ z)
    rw [hV'q₀] at hmv
    simpa [norm_sub_rev] using hmv
  refine ⟨hr0, hM0, by positivity, hM0, hval, hVc2, ?_, ?_, ?_, ?_⟩
  · -- hdiff
    intro z hz; exact (hVderiv z (hz_u z hz)).differentiableAt
  · -- hVdisp (second-order displacement) via mean value on the affine remainder over the segment.
    intro z hz
    set R : Point n → Point n := fun w => V w - (w - q₀) with hRdef
    have hseg_ball : segment ℝ q₀ z ⊆ Metric.ball q₀ r :=
      (convex_ball q₀ r).segment_subset hq₀ball hz
    have hseg_cb : segment ℝ q₀ z ⊆ Metric.closedBall q₀ ‖z - q₀‖ :=
      (convex_closedBall q₀ ‖z - q₀‖).segment_subset
        (Metric.mem_closedBall_self (norm_nonneg _))
        (by rw [Metric.mem_closedBall, dist_eq_norm])
    have hRderiv : ∀ w ∈ segment ℝ q₀ z,
        HasFDerivWithinAt R (V' w - ContinuousLinearMap.id ℝ (Point n)) (segment ℝ q₀ z) w := by
      intro w hw
      have hVw : HasFDerivAt V (V' w) w := hVderiv w (hz_u w (hseg_ball hw))
      have haff : HasFDerivAt (fun w : Point n => w - q₀) (ContinuousLinearMap.id ℝ (Point n)) w :=
        (hasFDerivAt_id w).sub_const q₀
      exact (hVw.sub haff).hasFDerivWithinAt
    have hRbd : ∀ w ∈ segment ℝ q₀ z,
        ‖V' w - ContinuousLinearMap.id ℝ (Point n)‖ ≤ M * ‖z - q₀‖ := by
      intro w hw
      have hwr : ‖w - q₀‖ ≤ ‖z - q₀‖ := by
        have := hseg_cb hw; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
      calc ‖V' w - ContinuousLinearMap.id ℝ (Point n)‖
          ≤ M * ‖w - q₀‖ := hBop w (hseg_ball hw)
        _ ≤ M * ‖z - q₀‖ := by exact mul_le_mul_of_nonneg_left hwr hM0
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hRderiv hRbd
      (convex_segment q₀ z) (left_mem_segment ℝ q₀ z) (right_mem_segment ℝ q₀ z)
    -- `R q₀ = 0`, `R z = V z − (z − q₀)`.
    have hRq₀ : R q₀ = 0 := by rw [hRdef]; simp [hval]
    rw [hRq₀] at hmv
    calc ‖V z - (z - q₀)‖ = ‖R z - 0‖ := by rw [hRdef]; simp
      _ ≤ M * ‖z - q₀‖ * ‖z - q₀‖ := hmv
      _ = M * ‖z - q₀‖ ^ 2 := by ring
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
      _ ≤ (M * ‖z - q₀‖) * ‖unitVec i‖ := by
          exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)
      _ = M * ‖unitVec i‖ * ‖z - q₀‖ := by ring
  · -- hJet2: `fderiv (fderiv V) z = fderiv V' z = V'' z`, bounded by `M`.
    intro z hz
    -- on the open ball, `fderiv V = V'`, hence `=ᶠ[𝓝 z]`.
    have hballnhds : Metric.ball q₀ r ∈ nhds z := Metric.isOpen_ball.mem_nhds hz
    have hfeq : fderiv ℝ V =ᶠ[nhds z] V' := by
      filter_upwards [hballnhds] with w hw
      exact (hVderiv w (hz_u w hw)).fderiv
    have h1 : fderiv ℝ (fun w => fderiv ℝ V w) z = fderiv ℝ V' z := hfeq.fderiv_eq
    have h2 : fderiv ℝ V' z = V'' z := (hV'deriv z (hz_u2 z hz)).fderiv
    rw [h1, h2]
    exact hz_bd z hz

end QIQTH.JointRNCRegularityLocal

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.JointRNCRegularityLocal
#print axioms uniformInverseChart_slice_contDiffAt_diag
#print axioms uniformInverseChart_slice_value_diag
#print axioms uniformInverseChart_slice_fderiv_id_diag
#print axioms jointRNCRegularityLocal_of_diag
end AxiomChecks
