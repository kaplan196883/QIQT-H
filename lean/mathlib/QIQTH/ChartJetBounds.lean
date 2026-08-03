/-
  QIQTH / HeatResidualBound — ChartJetBounds.lean  (J4-132)

  ==========================================================================================
  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel
  campaign.  It is NOT a₁ = R/6, and it proves NOTHING about R/6.  It supplies the S3
  CHART-JET data — existence + center values of the FIELD-slot jets of the K-uniform inverse
  chart `V_z := fun x => uniformInverseChart g gi hC hK z x` (base `z` FIXED, field slot `x`,
  evaluated at the field center `x = 0`) — that feeds the exact Hessian normal form
  `ChartJetHessian.gaussComp_pd_pd` / `gaussComp_amp_center_decomp` (J4-130).

  ------------------------------------------------------------------------------------------
  WHAT THE CONSTRUCTION GIVES (raw data read out of the tower before writing).

  * `uniformInverseChart g gi hC hK z` is the `ApproximatesLinearOn`-IFT partial-homeomorph
    inverse `E_z.symm` of the recentring chart `φ_z = uniformFlowExp g gi hC hK z`
    (`UniformChartRadius.lean`).  Its ONLY field-slot regularity in the tower is
        `uniformInverseChart_huniformChart` :  ∃ δ₀ > 0, ∀ q ∈ K, ∀ v, ‖v‖ < δ₀ →
            (germ)  (fun z ↦ W_q (φ_q z)) =ᶠ[𝓝 v] id   ∧   ContDiffAt ℝ 2 (W_q) (φ_q v).
    That is `C²` regularity at the IMAGE points `φ_q v`, NOT directly at a field point `x`.
    To land the jet AT the field center `x = 0` one needs `0 = φ_z v₀` for some `‖v₀‖ < δ₀`.
    At the ASSEMBLY point `z = 0` this holds with `v₀ = 0` because `φ_0 0 = 0`
    (`uniformFlowExp_zero`), so at the center the `C²` field regularity is TOWER-DERIVED,
    UNCONDITIONALLY (given `0 ∈ K`).  Off center it is carried as the honest labelled
    hypothesis `hreg : ContDiffAt ℝ 2 (W_z) 0` (satisfiable exactly when `0` lies in the
    chart-image ball of base `z`; never the conclusion).

  ------------------------------------------------------------------------------------------
  DERIVED vs CARRIED.

  DERIVED (unconditional, given `0 ∈ K`):
    * `chartField_contDiffAt_center`, `chartField_germ_center`  — the field-slot `C²` + the
      left-inverse germ AT the field center of the ASSEMBLY-point chart `V_0`.
    * `expFlow_fderiv_id_center`                                — `Dφ_0(0) = Id`.
    * `chartField_fderiv_center`                                — `DV_0(0) = Id`  (J2a, fderiv).
    * `chartField_firstJet_center` / `_single`                 — the first FIELD jet in the
      exact `gaussComp` line shape:  `P 0 i k = δ_{ik}`, i.e. `P i = eᵢ = Pi.single i 1`
      (J2a VERBATIM).
    * `chartField_centerValue_base0`                           — `V_0 0 = 0`.
    * `chartField_centerJet_term_vanishes_base0`               — for EVERY second jet `Q`, the
      `gaussComp_amp_center_decomp` centerJet contraction `∑ₖ (V_0 0)ₖ · Qₖ = 0`.  THE
      CENTERJET TERM DIES AT THE ASSEMBLY POINT (`V_0 0 = 0`), UNCONDITIONALLY IN `Q`.

  DERIVED (conditional on the honest labelled `C²` carry `hreg`, for a GENERAL base `z`):
    * `chartField_firstJet_of_contDiffAt`  — the first FIELD jet exists in the `gaussComp`
      line shape with value `P i = DV_z(0)(eᵢ)` (the i-th column of `DW_z(0)`).  This is
      J1a for the general base; the center case specializes it via `DV_0(0) = Id`.

  CARRIED (documented, NOT proved here — the recognized regularity walls):
    * J1b (SECOND field-jet existence `Q`) and the deeper J2b value `D²V_0(0) = 0`.  The
      value `D²V_0(0) = 0` is the inverse-of-inverse image of the exp SECOND jet at the
      center: `D²V_0(0) = −DV_0(0)∘D²φ_0(0)∘(DV_0(0),DV_0(0)) = −D²φ_0(0)` (since `DV_0(0)=Id`),
      and `D²φ_0(0) = 0` under the capstone gauge `hΓ : christoffel(0) = 0` (the leading
      second jet of the geodesic exp at the center is `−½Γ(0)(·,·)`).  The tower has NO
      exp-second-jet-at-center lemma and NO Mathlib second-derivative-of-inverse in the
      `pd`-line form, so `D²V_0(0) = 0` is CARRIED.  ⚠ VERDICT (the bankable intelligence):
      the centerJet DIES at the assembly point — proved here at the CONTRACTION level
      (`chartField_centerJet_term_vanishes_base0`, unconditional) and, at the raw jet level
      `D²V_0(0)=0`, reduced to the two labelled gauge facts above.
    * J3 (the base-point `z`-modulus `‖P i(z) − eᵢ‖ ≤ C_P‖z‖`, `‖Q i(z)‖ ≤ C_Q`).  This needs
      base-point (`z`-slot) regularity of the `.choose`-built chart, the recognized blocker
      (2) of `ChartWrapperConcrete`/`InverseChartDisplacement`; CARRIED.

  NO `sorry`; NO new axioms; NO `expRho` in statements; every hypothesis is satisfiable,
  non-vacuous, and never the conclusion.  Reusable BRICK; NOT `a₁ = R/6`.
  ==========================================================================================
-/
import Mathlib
import QIQTH.ChartWrapperConcrete

open Filter Finset
open QIQTH.Curvature QIQTH.ExpMap
open scoped Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    Elementary line helpers:  `s ↦ update 0 i s` and its derivative `eᵢ`.
    ############################################################################### -/

/-- The coordinate line `s ↦ update 0 i s` is `s ↦ s • eᵢ` (with `eᵢ = Pi.single i 1`). -/
theorem update_zero_eq_smul_single (i : Fin n) (s : ℝ) :
    Function.update (0 : Point n) i s = s • (Pi.single i (1 : ℝ)) := by
  funext j
  rw [Pi.smul_apply, Pi.single_apply, Function.update_apply, smul_eq_mul]
  by_cases h : j = i <;> simp [h]

/-- `update 0 i 0 = 0`. -/
theorem update_zero_zero (i : Fin n) : Function.update (0 : Point n) i (0 : ℝ) = 0 := by
  funext j; simp [Function.update_apply]

/-- **Line derivative.**  `s ↦ update 0 i s` has `HasDerivAt` value `eᵢ = Pi.single i 1` at `s = 0`. -/
theorem hasDerivAt_update_zero_line (i : Fin n) :
    HasDerivAt (fun s : ℝ => Function.update (0 : Point n) i s) (Pi.single i (1 : ℝ)) 0 := by
  have hfun : (fun s : ℝ => Function.update (0 : Point n) i s)
      = (fun s : ℝ => s • (Pi.single i (1 : ℝ))) := by
    funext s; exact update_zero_eq_smul_single i s
  rw [hfun]
  simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Point n)

/-! ###############################################################################
    J1 (regularity) + germ AT the field center of the ASSEMBLY-point chart `V_0`.
    ############################################################################### -/

/-- **J1 (regularity, DERIVED).**  At the assembly base `z = 0 ∈ K`, the field-slot chart
    `V_0 = uniformInverseChart g gi hC hK 0` is `C²` at the field center `0`.
    From `uniformInverseChart_huniformChart` at the image point `φ_0 0 = 0`
    (`uniformFlowExp_zero`). -/
theorem chartField_contDiffAt_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK 0) 0 := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨hgermC2, _⟩ := hspec 0 h0K
  obtain ⟨_, hC2⟩ := hgermC2 0 (by rw [norm_zero]; exact hδ₀)
  rwa [uniformFlowExp_zero g gi hC hK 0 h0K] at hC2

/-- **J1 (germ, DERIVED).**  The left-inverse germ of `V_0` at the field center:
    `(fun z ↦ V_0 (φ_0 z)) =ᶠ[𝓝 0] id`. -/
theorem chartField_germ_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    (fun z => uniformInverseChart g gi hC hK 0 (uniformFlowExp g gi hC hK 0 z))
      =ᶠ[nhds (0 : Point n)] (fun z => z) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨hgermC2, _⟩ := hspec 0 h0K
  exact (hgermC2 0 (by rw [norm_zero]; exact hδ₀)).1

/-- **J1 (center value, DERIVED).**  `V_0 0 = uniformInverseChart g gi hC hK 0 0 = 0`
    (the left-inverse germ value at `v = 0`, through `φ_0 0 = 0`). -/
theorem chartField_centerValue_base0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    uniformInverseChart g gi hC hK 0 0 = 0 := by
  have h : uniformInverseChart g gi hC hK 0 (uniformFlowExp g gi hC hK 0 0) = 0 :=
    (chartField_germ_center g gi hC hK h0K).eq_of_nhds
  rwa [uniformFlowExp_zero g gi hC hK 0 h0K] at h

/-! ###############################################################################
    J2a — the CENTER first-field-jet:  `Dφ_0(0) = Id`, `DV_0(0) = Id`, `P i = eᵢ`.
    ############################################################################### -/

/-- **Helper — `Dφ_0(0) = Id`.**  The recentring chart's Jacobian at the center is the
    identity, from the near-identity bound `‖Dφ_0(v) − Id‖ ≤ C_D·‖v‖` at `v = 0`. -/
theorem expFlow_fderiv_id_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    HasFDerivAt (uniformFlowExp g gi hC hK 0) (ContinuousLinearMap.id ℝ (Point n)) 0 := by
  have hR : ‖(0 : Point n)‖ < uniformFlowRadius g gi hC hK := by
    rw [norm_zero]; exact uniformFlowRadius_pos g gi hC hK
  have hφdiff : DifferentiableAt ℝ (uniformFlowExp g gi hC hK 0) 0 :=
    (contDiffAt2_uniformFlowExp g gi hC hK 0 h0K 0 hR).differentiableAt (by norm_num)
  have hfderiv_id : fderiv ℝ (uniformFlowExp g gi hC hK 0) 0 = ContinuousLinearMap.id ℝ (Point n) := by
    obtain ⟨ρ₀, hρ₀, C_D, _, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
    have h0ρ : ‖(0 : Point n)‖ < ρ₀ := by rw [norm_zero]; exact hρ₀
    have hb := hnear 0 h0K 0 h0ρ
    rw [norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  rw [← hfderiv_id]; exact hφdiff.hasFDerivAt

/-- **★ J2a (fderiv form, DERIVED) — `DV_0(0) = Id`.**  The field-slot Jacobian of the
    inverse chart at the assembly point is the identity.  Route: differentiate the
    left-inverse germ `V_0(φ_0 z) = z` at `z = 0`, where `Dφ_0(0) = Id`
    (`expFlow_fderiv_id_center`) and `V_0` is differentiable (`chartField_contDiffAt_center`);
    the chain rule + uniqueness of the Fréchet derivative give `DV_0(0) ∘ Id = Id`. -/
theorem chartField_fderiv_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    fderiv ℝ (uniformInverseChart g gi hC hK 0) 0 = ContinuousLinearMap.id ℝ (Point n) := by
  set W := uniformInverseChart g gi hC hK 0 with hWdef
  set φ := uniformFlowExp g gi hC hK 0 with hφdef
  have hφfd : HasFDerivAt φ (ContinuousLinearMap.id ℝ (Point n)) 0 :=
    expFlow_fderiv_id_center g gi hC hK h0K
  have hWdiff : DifferentiableAt ℝ W 0 :=
    (chartField_contDiffAt_center g gi hC hK h0K).differentiableAt (by norm_num)
  have hφ0 : φ 0 = 0 := uniformFlowExp_zero g gi hC hK 0 h0K
  have hWfd0 : HasFDerivAt W (fderiv ℝ W 0) (φ 0) := by rw [hφ0]; exact hWdiff.hasFDerivAt
  have hcomp : HasFDerivAt (fun z => W (φ z))
      ((fderiv ℝ W 0).comp (ContinuousLinearMap.id ℝ (Point n))) 0 := hWfd0.comp 0 hφfd
  have hgerm := chartField_germ_center g gi hC hK h0K
  have hid_fd : HasFDerivAt (fun z : Point n => z)
      ((fderiv ℝ W 0).comp (ContinuousLinearMap.id ℝ (Point n))) 0 :=
    hcomp.congr_of_eventuallyEq hgerm.symm
  have huniq := hid_fd.unique (hasFDerivAt_id 0)
  rwa [ContinuousLinearMap.comp_id] at huniq

/-- **★★ J2a (line/`gaussComp` shape, DERIVED) — `P 0 i k = δ_{ik}`.**  In the exact first
    `i`-line jet shape consumed by `ChartJetHessian.gaussComp_pd_pd`
    (`hV1 : HasDerivAt (fun s ↦ V (update x i s) k) (P x k) (x i)`), the assembly-point chart's
    first FIELD jet at the field center is `P 0 i k = if k = i then 1 else 0`, i.e. the i-th
    jet vector is `eᵢ = Pi.single i 1`.  Direct from `DV_0(0) = Id`
    (`chartField_fderiv_center`) chained with the coordinate-line derivative
    `hasDerivAt_update_zero_line`. -/
theorem chartField_firstJet_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (i k : Fin n) :
    HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK 0 (Function.update 0 i s) k)
      (if k = i then (1 : ℝ) else 0) ((0 : Point n) i) := by
  set W := uniformInverseChart g gi hC hK 0 with hWdef
  have hWdiff : DifferentiableAt ℝ W 0 :=
    (chartField_contDiffAt_center g gi hC hK h0K).differentiableAt (by norm_num)
  have hWfd : HasFDerivAt W (ContinuousLinearMap.id ℝ (Point n)) 0 := by
    have := hWdiff.hasFDerivAt
    rwa [chartField_fderiv_center g gi hC hK h0K] at this
  -- rewrite the base point of the outer HasFDerivAt to `line 0 = 0`.
  have hWfd' : HasFDerivAt W (ContinuousLinearMap.id ℝ (Point n))
      (Function.update (0 : Point n) i (0 : ℝ)) := by rw [update_zero_zero]; exact hWfd
  have hcomp : HasDerivAt (fun s : ℝ => W (Function.update 0 i s))
      (Pi.single i (1 : ℝ)) 0 := by
    have h := hWfd'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_update_zero_line i)
    simpa using h
  have hk := (hasDerivAt_pi.mp hcomp) k
  simp only [Pi.zero_apply]
  rw [Pi.single_apply] at hk
  exact hk

/-- **J2a (vector form, DERIVED) — `P 0 i = eᵢ`.**  The i-th first FIELD jet vector of the
    assembly-point chart at the field center is `eᵢ = Pi.single i 1`. -/
theorem chartField_firstJet_single_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (i : Fin n) :
    HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK 0 (Function.update 0 i s))
      (Pi.single i (1 : ℝ)) ((0 : Point n) i) := by
  set W := uniformInverseChart g gi hC hK 0 with hWdef
  have hWdiff : DifferentiableAt ℝ W 0 :=
    (chartField_contDiffAt_center g gi hC hK h0K).differentiableAt (by norm_num)
  have hWfd : HasFDerivAt W (ContinuousLinearMap.id ℝ (Point n)) 0 := by
    have := hWdiff.hasFDerivAt
    rwa [chartField_fderiv_center g gi hC hK h0K] at this
  have hWfd' : HasFDerivAt W (ContinuousLinearMap.id ℝ (Point n))
      (Function.update (0 : Point n) i (0 : ℝ)) := by rw [update_zero_zero]; exact hWfd
  have h := hWfd'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_update_zero_line i)
  simp only [Pi.zero_apply]
  simpa using h

/-! ###############################################################################
    J1a (general base) — first field-jet existence from the labelled `C²` carry.
    ############################################################################### -/

/-- **★ J1a (general base, DERIVED conditional on the labelled `C²` carry).**  For any base
    `z` with the honest field-slot regularity `hreg : ContDiffAt ℝ 2 (V_z) 0` (satisfiable
    whenever `0` lies in the chart-image ball of base `z`; never the conclusion), the first
    FIELD jet exists in the exact `gaussComp_pd_pd` `hV1` line shape, with value the i-th
    column of the inverse-chart Jacobian `DV_z(0)`:
        `HasDerivAt (fun s ↦ V_z (update 0 i s) k) ((DV_z(0)) eᵢ) k) (0 i)`.
    At the assembly base this specializes to `chartField_firstJet_center` via `DV_0(0)=Id`. -/
theorem chartField_firstJet_of_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) 0) (i k : Fin n) :
    HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update 0 i s) k)
      (fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (Pi.single i (1 : ℝ)) k)
      ((0 : Point n) i) := by
  set W := uniformInverseChart g gi hC hK z with hWdef
  have hWdiff : DifferentiableAt ℝ W 0 := hreg.differentiableAt (by norm_num)
  have hWfd' : HasFDerivAt W (fderiv ℝ W 0) (Function.update (0 : Point n) i (0 : ℝ)) := by
    rw [update_zero_zero]; exact hWdiff.hasFDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => W (Function.update 0 i s))
      (fderiv ℝ W 0 (Pi.single i (1 : ℝ))) 0 := by
    have h := hWfd'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_update_zero_line i)
    simpa using h
  have hk := (hasDerivAt_pi.mp hcomp) k
  simpa only [Pi.zero_apply] using hk

/-! ###############################################################################
    J2b — the centerJet contraction dies at the assembly point (DERIVED, ∀ Q).
    ############################################################################### -/

/-- **★★ J2b (VERDICT — DERIVED, unconditional in `Q`).**  The `gaussComp_amp_center_decomp`
    centerJet contraction `∑ₖ (V_0 0)ₖ · Qₖ` — the coefficient of the odd-parity centerJet
    term `gaussDdim τ (V_0 0)·(−(∑ₖ (V_0 0)ₖ·Qₖ)/(2τ))·A 0` — VANISHES at the assembly point
    for EVERY candidate second field-jet `Q`, because `V_0 0 = 0`
    (`chartField_centerValue_base0`).  THE CENTERJET TERM DIES AT THE ASSEMBLY POINT.

    (This banks the "centerJet dies" finding at the contraction level, independent of the raw
    jet-level value `D²V_0(0) = 0`, which is CARRIED — see the file header: it reduces to
    `D²φ_0(0) = 0` under the gauge `christoffel(0) = 0`.) -/
theorem chartField_centerJet_term_vanishes_base0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (Q : Fin n → ℝ) :
    (∑ k, uniformInverseChart g gi hC hK 0 0 k * Q k) = 0 := by
  have hV0 : uniformInverseChart g gi hC hK 0 0 = 0 :=
    chartField_centerValue_base0 g gi hC hK h0K
  rw [hV0]
  simp

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.chartField_contDiffAt_center
#print axioms QIQTH.HeatResidualBound.chartField_germ_center
#print axioms QIQTH.HeatResidualBound.chartField_centerValue_base0
#print axioms QIQTH.HeatResidualBound.expFlow_fderiv_id_center
#print axioms QIQTH.HeatResidualBound.chartField_fderiv_center
#print axioms QIQTH.HeatResidualBound.chartField_firstJet_center
#print axioms QIQTH.HeatResidualBound.chartField_firstJet_single_center
#print axioms QIQTH.HeatResidualBound.chartField_firstJet_of_contDiffAt
#print axioms QIQTH.HeatResidualBound.chartField_centerJet_term_vanishes_base0
