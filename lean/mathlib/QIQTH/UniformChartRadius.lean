/-
  UniformChartRadius — J4-100: the K-UNIFORM chart radius, discharging `huniformChart`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What J4-99 (`RadiusOrdering.lean`) left, and what this file delivers (ns `QIQTH.HeatResidualBound`).

  J4-99's summit `gatedWitness_hEboundW_final` reduced the width-2 residual primitive `hEboundW` (for the
  CONCRETE gated witness) to a SINGLE isolated input `huniformChart`: a K-UNIFORM radius `δ₀ > 0` on
  which the base-point inverse chart is the genuine `C²` left inverse of `φ_q = uniformFlowExp g gi hC hK q`
  and the chart-image balls are open with compact-image closure, for EVERY `q ∈ K`.  The per-`q` version
  already exists (`basepointChart_exists`, `chartImage_ball_open_closure`); the residue was the K-uniform
  IFT SOURCE-ball radius.

  This file forces it via Mathlib's quantitative inverse function theorem
  (`ApproximatesLinearOn`), which — unlike `ContDiffAt.toOpenPartialHomeomorph` — EXPOSES the source set.

    * (U1) `uniformFlowExp_approximatesLinearOn` — from the K-uniform near-identity Jacobian bound
      `‖Dφ_q(v) − Id‖ ≤ C_D‖v‖` (`uniformFlowExp_fderiv_near_id_quant`) and the mean value inequality on
      the convex ball, `φ_q` approximates the identity linearly on a UNIFORM ball `ball 0 δ₀` with a
      uniform constant `c < 1`, for every `q ∈ K`.

    * (U2) `uniformInverseChart` + `uniformInverseChart_spec` / `uniformChartImage_ball_open_closure` —
      the ApproximatesLinearOn partial homeomorph (source = `ball 0 δ₀` EXACTLY) yields, at the UNIFORM
      radius `δ₀`, the left-inverse germ, the `C²`-regularity of the inverse chart, and the open-image /
      compact-image-closure facts.  This is exactly the `huniformChart` SHAPE, for the concrete uniform
      chart, at a single radius over the compact `K`.

    * (U3) `gatedWitness_hEboundW_unconditional` — the summit, FULLY UNCONDITIONAL: the concrete gated
      witness built on `uniformInverseChart` obeys the width-2 `hEboundW` primitive, with hypotheses
      ONLY the genuine geometric/heat data.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.RadiusOrdering
import QIQTH.NearIsometryBudget
import QIQTH.HunifTrichotomy
import QIQTH.UniformFlowNondegClose
import QIQTH.PullbackNaturalityLocal

open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open QIQTH.HeatParametrixOrder
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open QIQTH.RadialDistance QIQTH.RNCDecay
open Set Filter
open scoped BigOperators Topology NNReal

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### (U1) The uniform ApproximatesLinearOn instance for `φ_q` on a uniform ball. -/

/-- **★ U1 — `uniformFlowExp_approximatesLinearOn`.**  There is a single radius `δ₀ > 0` and a single
    constant `c < 1` (both uniform over the compact `K`) such that for every `q ∈ K`, the recentring
    chart `φ_q = uniformFlowExp g gi hC hK q` approximates the identity linearly on `ball 0 δ₀` with
    constant `c`:
        `∀ x y ∈ ball 0 δ₀, ‖φ_q x − φ_q y − (x − y)‖ ≤ c‖x − y‖`.
    Proof: the K-uniform near-identity Jacobian bound `‖Dφ_q(v) − Id‖ ≤ C_D‖v‖` gives, on the convex
    ball, `‖D(φ_q − id)(w)‖ ≤ C_D·δ₀` uniformly; the mean value inequality integrates this.  Choosing
    `δ₀ ≤ 1/(2(C_D+1))` makes `c := C_D·δ₀ < 1`.  Hypotheses ONLY `hC` + `IsCompact K`. -/
theorem uniformFlowExp_approximatesLinearOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∃ c : ℝ≥0, (c : ℝ) < 1 ∧ ∀ q ∈ K,
      ApproximatesLinearOn (uniformFlowExp g gi hC hK q)
        (ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n)
        (Metric.ball 0 δ₀) c := by
  obtain ⟨ρ₀, hρ₀, C_D, hCD0, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  have hRpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  have hden : 0 < 2 * (C_D + 1) := by positivity
  set δ₀ : ℝ := min (min ρ₀ (uniformFlowRadius g gi hC hK)) (1 / (2 * (C_D + 1))) with hδ₀def
  have hδ₀pos : 0 < δ₀ := lt_min (lt_min hρ₀ hRpos) (by positivity)
  have hδ₀ρ₀ : δ₀ ≤ ρ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₀R : δ₀ ≤ uniformFlowRadius g gi hC hK := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₀den : δ₀ ≤ 1 / (2 * (C_D + 1)) := min_le_right _ _
  have hCDδ_nonneg : (0 : ℝ) ≤ C_D * δ₀ := mul_nonneg hCD0 hδ₀pos.le
  have hCDδ_lt1 : C_D * δ₀ < 1 := by
    have h1 : C_D * δ₀ ≤ C_D * (1 / (2 * (C_D + 1))) := by
      apply mul_le_mul_of_nonneg_left hδ₀den hCD0
    have h2 : C_D * (1 / (2 * (C_D + 1))) < 1 := by
      rw [mul_one_div, div_lt_one hden]
      nlinarith [hCD0]
    linarith
  refine ⟨δ₀, hδ₀pos, ⟨C_D * δ₀, hCDδ_nonneg⟩, ?_, ?_⟩
  · -- `(c : ℝ) = C_D * δ₀ < 1`.
    simpa using hCDδ_lt1
  · intro q hq x hx y hy
    rw [mem_ball_zero_iff] at hx hy
    -- The auxiliary map `f w = φ_q w − w`, with fderiv `Dφ_q(w) − Id` bounded by `C_D·δ₀`.
    set f : Point n → Point n := fun w => uniformFlowExp g gi hC hK q w - w with hfdef
    have hdiff : ∀ w ∈ Metric.ball (0 : Point n) δ₀, DifferentiableAt ℝ f w := by
      intro w hw
      rw [mem_ball_zero_iff] at hw
      have hφ : DifferentiableAt ℝ (uniformFlowExp g gi hC hK q) w :=
        (contDiffAt2_uniformFlowExp g gi hC hK q hq w (lt_of_lt_of_le hw hδ₀R)).differentiableAt
          (by norm_num)
      exact hφ.sub differentiableAt_id
    have hbound : ∀ w ∈ Metric.ball (0 : Point n) δ₀, ‖fderiv ℝ f w‖ ≤ C_D * δ₀ := by
      intro w hw
      rw [mem_ball_zero_iff] at hw
      have hφ : DifferentiableAt ℝ (uniformFlowExp g gi hC hK q) w :=
        (contDiffAt2_uniformFlowExp g gi hC hK q hq w (lt_of_lt_of_le hw hδ₀R)).differentiableAt
          (by norm_num)
      have hfd : fderiv ℝ f w
          = fderiv ℝ (uniformFlowExp g gi hC hK q) w - ContinuousLinearMap.id ℝ (Point n) := by
        rw [hfdef, fderiv_fun_sub hφ differentiableAt_fun_id, fderiv_fun_id]
      rw [hfd]
      calc ‖fderiv ℝ (uniformFlowExp g gi hC hK q) w - ContinuousLinearMap.id ℝ (Point n)‖
          ≤ C_D * ‖w‖ := hnear q hq w (lt_of_lt_of_le hw hδ₀ρ₀)
        _ ≤ C_D * δ₀ := by apply mul_le_mul_of_nonneg_left hw.le hCD0
    have hmvt := (convex_ball (0 : Point n) δ₀).norm_image_sub_le_of_norm_fderiv_le
      hdiff hbound (mem_ball_zero_iff.mpr hy) (mem_ball_zero_iff.mpr hx)
    -- `f x − f y = φ_q x − φ_q y − (x − y)`.
    have hfxy : uniformFlowExp g gi hC hK q x - uniformFlowExp g gi hC hK q y - (x - y)
        = f x - f y := by simp only [hfdef]; exact sub_sub_sub_comm _ _ _ _
    have hidapp : (ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n) (x - y) = x - y := by
      simp
    rw [hidapp, hfxy]
    calc ‖f x - f y‖
        ≤ C_D * δ₀ * ‖x - y‖ := hmvt
      _ = (↑(⟨C_D * δ₀, hCDδ_nonneg⟩ : ℝ≥0) : ℝ) * ‖x - y‖ := by norm_num

/-! ### (U2) The uniform inverse chart at the UNIFORM radius — the `huniformChart` shape. -/

/-- **U2 (existence) — the uniform inverse chart data at a SINGLE radius over `K`.**  From U1's
    `ApproximatesLinearOn` instance (constant `c < 1`, source EXACTLY `ball 0 δ₀`) and the K-uniform
    nondegeneracy radius, there is a single `δ₀ > 0` on which, for EVERY `q ∈ K`, the IFT partial
    homeomorph `E_q` of `φ_q` (`⇑E_q = φ_q`, `E_q.source = ball 0 δ₀`) supplies a `C²` left-inverse chart
    `W = E_q.symm` with the germ + `C²` at every `‖v‖ < δ₀`, and the open-image / compact-image-closure
    facts on every sub-ball `0 < c < δ₀`.  The uniform source radius is the point ApproximatesLinearOn
    exposes and `ContDiffAt.toOpenPartialHomeomorph` did not. -/
theorem uniformChart_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ q ∈ K, ∃ W : Point n → Point n,
      (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => W (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 W (uniformFlowExp g gi hC hK q v)) ∧
      (∀ c : ℝ, 0 < c → c < δ₀ →
        IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
        closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
          ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c) := by
  obtain ⟨δ₁, hδ₁, c, hc1, hAL⟩ := uniformFlowExp_approximatesLinearOn g gi hC hK
  obtain ⟨ρnd, hρnd, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  have hRpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  set δ₀ : ℝ := min δ₁ (min ρnd (uniformFlowRadius g gi hC hK)) with hδ₀def
  have hδ₀pos : 0 < δ₀ := lt_min hδ₁ (lt_min hρnd hRpos)
  have hδ₀δ₁ : δ₀ ≤ δ₁ := min_le_left _ _
  have hδ₀ρnd : δ₀ ≤ ρnd := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₀R : δ₀ ≤ uniformFlowRadius g gi hC hK := le_trans (min_le_right _ _) (min_le_right _ _)
  -- The `refl`-equiv nondegeneracy condition consumed by the ApproximatesLinearOn IFT.
  have hcN : Subsingleton (Point n) ∨
      c < ‖((ContinuousLinearEquiv.refl ℝ (Point n)).symm : Point n →L[ℝ] Point n)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial (Point n) with hs | hns
    · exact Or.inl hs
    · refine Or.inr ?_
      haveI := hns
      have hcoe : ((ContinuousLinearEquiv.refl ℝ (Point n)).symm : Point n →L[ℝ] Point n)
          = ContinuousLinearMap.id ℝ (Point n) := by simp
      rw [hcoe]
      have hid : ‖ContinuousLinearMap.id ℝ (Point n)‖₊ = 1 := by simp
      rw [hid, inv_one]
      exact_mod_cast hc1
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro q hq
  have hALq : ApproximatesLinearOn (uniformFlowExp g gi hC hK q)
      (ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n) (Metric.ball 0 δ₀) c :=
    (hAL q hq).mono_set (Metric.ball_subset_ball hδ₀δ₁)
  set E : OpenPartialHomeomorph (Point n) (Point n) :=
    hALq.toOpenPartialHomeomorph (uniformFlowExp g gi hC hK q) (Metric.ball 0 δ₀) hcN
      Metric.isOpen_ball with hEdef
  have hEcoe : (⇑E : Point n → Point n) = uniformFlowExp g gi hC hK q :=
    hALq.toOpenPartialHomeomorph_coe _ _ hcN Metric.isOpen_ball
  have hEsrc : E.source = Metric.ball (0 : Point n) δ₀ :=
    hALq.toOpenPartialHomeomorph_source _ _ hcN Metric.isOpen_ball
  refine ⟨(E.symm : Point n → Point n), ?_, ?_⟩
  · intro v hv
    have hvsrc : v ∈ E.source := by rw [hEsrc]; exact mem_ball_zero_iff.mpr hv
    have hev : (⇑E) v = uniformFlowExp g gi hC hK q v := by rw [hEcoe]
    refine ⟨?_, ?_⟩
    · filter_upwards [E.eventually_left_inverse hvsrc] with z hz
      rw [← hEcoe]; exact hz
    · have hvρnd : ‖v‖ < ρnd := lt_of_lt_of_le hv hδ₀ρnd
      have hvR : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv hδ₀R
      have htgt : uniformFlowExp g gi hC hK q v ∈ E.target := by
        rw [← hev]; exact E.map_source hvsrc
      have hsymmpt : (⇑E.symm) (uniformFlowExp g gi hC hK q v) = v := by
        rw [← hev]; exact E.left_inv hvsrc
      have hUv : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v) := hnondeg q hq v hvρnd
      set fev : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.ofUnit hUv.unit with hfev
      have hcoev : (fev : Point n →L[ℝ] Point n) = fderiv ℝ (uniformFlowExp g gi hC hK q) v := by
        apply ContinuousLinearMap.ext; intro x
        have h1 : (fev : Point n →L[ℝ] Point n) x = (hUv.unit : Point n →L[ℝ] Point n) x := rfl
        rw [h1, hUv.unit_spec]
      have hfv : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK q) v :=
        contDiffAt2_uniformFlowExp g gi hC hK q hq v hvR
      have hf'v : HasFDerivAt (uniformFlowExp g gi hC hK q) (fev : Point n →L[ℝ] Point n) v := by
        rw [hcoev]; exact (hfv.differentiableAt (by norm_num)).hasFDerivAt
      apply E.contDiffAt_symm (f₀' := fev) htgt
      · rw [hsymmpt, hEcoe]; exact hf'v
      · rw [hsymmpt, hEcoe]; exact hfv
  · intro cc hcc0 hccδ
    have hballsub : Metric.ball (0 : Point n) cc ⊆ E.source := by
      rw [hEsrc]; exact Metric.ball_subset_ball hccδ.le
    have hcballsub : Metric.closedBall (0 : Point n) cc ⊆ E.source := by
      rw [hEsrc]; intro x hx; rw [mem_closedBall_zero_iff] at hx
      exact mem_ball_zero_iff.mpr (lt_of_le_of_lt hx hccδ)
    refine ⟨?_, ?_⟩
    · have hop := E.isOpen_image_of_subset_source Metric.isOpen_ball hballsub
      rwa [hEcoe] at hop
    · have hcompact : IsCompact (E '' Metric.closedBall 0 cc) :=
        (isCompact_closedBall (0 : Point n) cc).image_of_continuousOn (E.continuousOn.mono hcballsub)
      have hcl := closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hcompact.isClosed
      rwa [hEcoe] at hcl

/-- **U2 (radius) — the uniform chart radius `δ₀`.** -/
noncomputable def uniformChartRadius (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) : ℝ :=
  (uniformChart_exists g gi hC hK).choose

open Classical in
/-- **U2 (the named UNIFORM inverse chart).**  On the base set it is the ApproximatesLinearOn partial
    homeomorph's inverse (uniform source `ball 0 δ₀`), off it the zero default.  Unlike
    `basepointInverseChart`, its germ + `C²` hold at a SINGLE radius `uniformChartRadius` over all `q`. -/
noncomputable def uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) : Point n → Point n → Point n :=
  fun q => if hq : q ∈ K then
    ((uniformChart_exists g gi hC hK).choose_spec.2 q hq).choose else fun _ => 0

/-- **★★ U2 — `uniformInverseChart_huniformChart`: the `huniformChart` SHAPE, for the concrete uniform
    chart, at a SINGLE radius over `K`.**  Exactly the isolated input J4-99's summit consumed, but
    DISCHARGED (proved, not assumed) — for `uniformInverseChart` in place of `basepointInverseChart`. -/
theorem uniformInverseChart_huniformChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ q ∈ K,
      (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z))
            =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v)) ∧
      (∀ c : ℝ, 0 < c → c < δ₀ →
        IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
        closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
          ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c) := by
  refine ⟨(uniformChart_exists g gi hC hK).choose,
    (uniformChart_exists g gi hC hK).choose_spec.1, ?_⟩
  intro q hq
  have hWeq : uniformInverseChart g gi hC hK q
      = ((uniformChart_exists g gi hC hK).choose_spec.2 q hq).choose := by
    simp only [uniformInverseChart, dif_pos hq]
  obtain ⟨hgermC2, hOC⟩ := ((uniformChart_exists g gi hC hK).choose_spec.2 q hq).choose_spec
  refine ⟨?_, hOC⟩
  intro v hv
  rw [hWeq]
  exact hgermC2 v hv

/-! ### (U3) The fully unconditional `hEboundW` primitive — chart-generic engine + uniform chart. -/

/-- **U3 (generic cover) — `gatedWitness_hEboundW_of_good_gen`: T3's cover discharge, for an ARBITRARY
    inverse chart `W`.**  Verbatim `HunifTrichotomy.gatedWitness_hEboundW_of_good` with the concrete
    `basepointInverseChart` replaced by an abstract `W : Point n → Point n → Point n`; the cover
    machinery (`gatedKernel_hEboundW_of_cover`) and the cutoff collar are chart-generic. -/
theorem gatedWitness_hEboundW_of_good_gen (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b B : ℝ) (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (W : Point n → Point n → Point n)
    (hgood : ∀ q ∈ K, ∃ c : ℝ, b < c ∧
      (∀ τ, 0 < τ → ∀ v : Point n, ‖v‖ < c →
        |heatOp g gi (globalCutoffParametrixWitness Θ u a b W) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ B * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) ∧
      (∀ v : Point n, ‖v‖ ≤ c → W q (uniformFlowExp g gi hC hK q v) = v) ∧
      (∀ v : Point n, ‖v‖ ≤ c → ContinuousAt (W q) (uniformFlowExp g gi hC hK q v)) ∧
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
      closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
        ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c) :
    ∃ S : Point n → Set (Point n), ∀ τ p q, 0 < τ →
      |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitness Θ u a b W)) τ p q|
        ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  classical
  set H : ℝ → Point n → Point n → ℝ :=
    globalCutoffParametrixWitness Θ u a b W with hHdef
  set cf : Point n → ℝ := fun q => if hq : q ∈ K then (hgood q hq).choose else 0 with hcfdef
  refine ⟨fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q), ?_⟩
  refine gatedKernel_hEboundW_of_cover g gi K _ H B hB ?_
  intro q hq τ hτ p
  have hcfq : cf q = (hgood q hq).choose := dif_pos hq
  set c₀ : ℝ := (hgood q hq).choose with hc0def
  obtain ⟨hbc, hbnd, hinv, hcont, hopen, hclos⟩ := (hgood q hq).choose_spec
  have hSqeq : uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)
      = uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀ := by rw [hcfq]
  rw [hSqeq]
  have hb0 : 0 < b := lt_trans ha hab
  by_cases hpS : p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀
  · refine Or.inl ⟨hopen.mem_nhds hpS, ?_⟩
    obtain ⟨w, hw, hwp⟩ := hpS
    rw [mem_ball_zero_iff] at hw
    have hb := hbnd τ hτ w hw
    rw [hwp] at hb
    exact hb
  · by_cases hpcl : p ∈ closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀)
    · obtain ⟨w', hw', hw'p⟩ := hclos hpcl
      rw [mem_closedBall_zero_iff] at hw'
      have hnormeq : ‖w'‖ = c₀ := by
        rcases lt_or_eq_of_le hw' with hlt | heq
        · exact absurd (⟨w', mem_ball_zero_iff.mpr hlt, hw'p⟩ :
            p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀) hpS
        · exact heq
      have hWp : W q p = w' := by
        rw [← hw'p]; exact hinv w' hw'
      have hb2 : b ^ 2 < rncRadialSq (W q p) := by
        rw [hWp]
        have h1 : ‖w'‖ ^ 2 ≤ rncRadialSq w' := by
          have hle := norm_le_rncRadial w'
          have := rncRadial_sq w'
          nlinarith [norm_nonneg w', rncRadial_nonneg w', hle, this]
        nlinarith [h1, hnormeq, hb0, hbc]
      have hcontp : ContinuousAt (W q) p := by
        rw [← hw'p]; exact hcont w' hw'
      have hNnhds :
          (W q) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w} ∈ nhds p :=
        hcontp.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hb2)
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · refine Filter.Eventually.of_forall (fun t => ?_)
        simp only [hHdef, globalCutoffParametrixWitness]
        rw [radialCutoff_eq_zero ha hab (le_of_lt hb2), zero_mul]
      · filter_upwards [hNnhds] with p' hp'
        have hp'2 : b ^ 2 < rncRadialSq (W q p') := hp'
        simp only [hHdef, globalCutoffParametrixWitness]
        rw [radialCutoff_eq_zero ha hab (le_of_lt hp'2), zero_mul]
    · refine Or.inr (Or.inl ?_)
      have hsub : (closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀))ᶜ
          ⊆ {p' : Point n | p' ∉ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀} :=
        fun x hx hxS => hx (subset_closure hxS)
      exact Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hpcl) hsub

/-- **U3 (generic summit) — `gatedWitness_hEboundW_final_gen`: J4-99's summit, for an ARBITRARY chart
    `W` with the `huniformChart` SHAPE.**  Verbatim `RadiusOrdering.gatedWitness_hEboundW_final` with
    `basepointInverseChart` replaced by `W`; the τ-uniformity (R2 hoist) and radius ordering (R1
    ceiling-threaded engine) are chart-independent, so the argument goes through for any `W` whose germ /
    `C²` / open / closure facts hold at a single uniform radius `δ₀`. -/
theorem gatedWitness_hEboundW_final_gen (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (W : Point n → Point n → Point n)
    (huniformChart : ∃ δ₀ > (0 : ℝ), ∀ q ∈ K,
      (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => W q (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (W q) (uniformFlowExp g gi hC hK q v)) ∧
      (∀ c : ℝ, 0 < c → c < δ₀ →
        IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
        closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
          ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c)) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
      ∀ τ p q, 0 < τ →
        |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitness Θ u a b W)) τ p q|
          ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  obtain ⟨δ₀, hδ₀, hchart⟩ := huniformChart
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  obtain ⟨r₁, hr₁pos, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hC hK
  set ρc : ℝ := min (min rN δ₀) r₁ with hρcdef
  have hρc : 0 < ρc := lt_min (lt_min hrNpos hδ₀) hr₁pos
  have hρc_rN : ρc ≤ rN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρc_δ₀ : ρc ≤ δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρc_r₁ : ρc ≤ r₁ := min_le_right _ _
  obtain ⟨a, b, B0, ha, hab, hbρc, hB0, hAbound⟩ :=
    cutoffResidual_uniformFlow_unconditional_tau_narrow_below g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ u hw0smooth hw0flat ρc hρc
  refine ⟨a, b, B0 * Real.sqrt (2 / (3 / 2)) ^ n, ha, hab, by positivity, ?_⟩
  apply gatedWitness_hEboundW_of_good_gen g gi hC hK Θ u a b (B0 * Real.sqrt (2 / (3 / 2)) ^ n) ha hab
    (by positivity) W
  intro q hq
  set c : ℝ := (b + ρc) / 2 with hcdef
  have hbc : b < c := by rw [hcdef]; linarith
  have hcρc : c < ρc := by rw [hcdef]; linarith
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hc_rN : c < rN := lt_of_lt_of_le hcρc hρc_rN
  have hc_δ₀ : c < δ₀ := lt_of_lt_of_le hcρc hρc_δ₀
  have hc_r₁ : c < r₁ := lt_of_lt_of_le hcρc hρc_r₁
  obtain ⟨hchartGerm, hchartOC⟩ := hchart q hq
  refine ⟨c, hbc, ?_, ?_, ?_, ?_⟩
  · intro τ hτ v hv
    have hvN : ‖v‖ < rN := lt_trans hv hc_rN
    have hvδ₀ : ‖v‖ < δ₀ := lt_trans hv hc_δ₀
    have hvr₁ : ‖v‖ < r₁ := lt_trans hv hc_r₁
    obtain ⟨hgerm, hWc2⟩ := hchartGerm v hvδ₀
    have hg1 : ∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v) :=
      fun a' b' => (hg a' b').contDiffAt.of_le le_top
    have hU : IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) :=
      hgnd (uniformFlowExp g gi hC hK q v)
    have hGGi : ∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
        * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0 :=
      fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc
    have hGiG : ∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
        * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0 :=
      metricInv_left_of_right
        (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')
        (fun a' b' => gi (uniformFlowExp g gi hC hK q v) a' b')
        (hgnd (uniformFlowExp g gi hC hK q v))
        (fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc)
    have hf : ContDiffAt ℝ 2
        (fun x => globalCutoffParametrixWitness Θ u a b W τ x q)
        (uniformFlowExp g gi hC hK q v) := by
      have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 0 Θ u τ y)
          (W q (uniformFlowExp g gi hC hK q v)) := by
        apply ContDiffAt.mul
        · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
        · have hHeq : (heatParametrix 0 Θ u τ : Point n → ℝ)
              = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y := by
            funext x; rw [heatParametrix_folded]; simp
          have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u τ) := by
            rw [hHeq]; exact (gaussDdim_contDiff τ).mul hw0smooth
          exact hH.contDiffAt.of_le le_top
      exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
    have hpt : W q (uniformFlowExp g gi hC hK q v) = v := by
      simpa using hgerm.eq_of_nhds
    have hprofilegerm :
        (fun z => globalCutoffParametrixWitness Θ u a b W τ
            (uniformFlowExp g gi hC hK q z) q)
          =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) := by
      filter_upwards [hgerm] with z hz
      have hz' : W q (uniformFlowExp g gi hC hK q z) = z := hz
      simp only [globalCutoffParametrixWitness, hz']
    have hlap : laplaceBeltrami g gi
          (fun p => globalCutoffParametrixWitness Θ u a b W τ p q)
          (uniformFlowExp g gi hC hK q v)
        = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q)
            (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v := by
      have hn := hnat
        (fun x => globalCutoffParametrixWitness Θ u a b W τ x q)
        q hq v hvN hg1 hf hU hGGi hGiG
      rw [← hn]
      exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
        (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
        _ _ v hprofilegerm
    have htransport :
        heatOp g gi (globalCutoffParametrixWitness Θ u a b W) τ
            (uniformFlowExp g gi hC hK q v) q
          = radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v := by
      simp only [heatOp]
      have hterm1fun :
          (fun s => globalCutoffParametrixWitness Θ u a b W s
              (uniformFlowExp g gi hC hK q v) q)
            = (fun s => radialCutoff a b v * heatParametrix 0 Θ u s v) := by
        funext s
        simp only [globalCutoffParametrixWitness, hpt]
      rw [hterm1fun, deriv_const_mul_field, hlap]
    rw [htransport]
    have hnarrow := hAbound τ hτ q hq v
    have htransfer :
        gaussDdim (3 / 2 * τ) v
          ≤ Real.sqrt (2 / (3 / 2)) ^ n
              * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) :=
      gaussDdim_le_gaussDdim_chart (c := 3 / 2) (d := 2) (by norm_num) (by norm_num) hτ
        (hdisp q hq v hvr₁)
    calc |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
              - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                  (uniformFlowPullbackMetricInv g gi hC hK q)
                  (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v|
        ≤ B0 * gaussDdim (3 / 2 * τ) v := hnarrow
      _ ≤ B0 * (Real.sqrt (2 / (3 / 2)) ^ n
            * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) :=
          mul_le_mul_of_nonneg_left htransfer hB0
      _ = B0 * Real.sqrt (2 / (3 / 2)) ^ n
            * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by ring
  · intro v hv
    have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
    simpa using (hchartGerm v hvδ₀).1.eq_of_nhds
  · intro v hv
    have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
    exact (hchartGerm v hvδ₀).2.continuousAt
  · exact hchartOC c hc0 hc_δ₀

/-- **★★★★ U3 CAPSTONE — `gatedWitness_hEboundW_unconditional`: the `hEboundW` PRIMITIVE, FULLY
    UNCONDITIONAL.**

    For the concrete gated witness built on the K-UNIFORM inverse chart `uniformInverseChart`, delivers
    the exact width-2 `hEboundW` primitive shape
        `∃ a b B S, 0<a ∧ a<b ∧ 0≤B ∧ ∀ τ p q, 0<τ →
           |heatOp g gi (gatedKernel K S H_w) τ p q| ≤ B · baseKernelW 2 0 τ p q`,
    with hypotheses ONLY the genuine geometric/heat data (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`/
    `Θ`/`u`/`hw0smooth`/`hw0flat`).  The former sole residue `huniformChart` is now DISCHARGED
    (`uniformInverseChart_huniformChart`) via the quantitative inverse function theorem
    (`ApproximatesLinearOn`).  NOT `a₁ = R/6`.  This is the `hunif` summit. -/
theorem gatedWitness_hEboundW_unconditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
      ∀ τ p q, 0 < τ →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hC hK))) τ p q|
          ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  gatedWitness_hEboundW_final_gen g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw0smooth hw0flat
    (uniformInverseChart g gi hC hK) (uniformInverseChart_huniformChart g gi hC hK)

end QIQTH.HeatResidualBound
