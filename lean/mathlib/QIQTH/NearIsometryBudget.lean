/-
  NearIsometryBudget — J4-96: DISCHARGING the near-isometry width budget `hdisp` (ball-local) of the
  M3 consumer-width per-base-point chart-Gaussian bound (`WidthMarginEngine.lean`, ns
  `QIQTH.HeatResidualBound`).

  ## Context — the one carried input of J4-95.

  `globalWitness_residual_bound_chartGaussian` carried a single genuine physical input:
    `hdisp : ∀ q ∈ K, ∀ v : Point n,
        3/2 * rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ 2 * rncRadialSq v`
  (the recentring chart `φ_q = uniformFlowExp q` is near-isometric enough that
  `(3/2)·‖φ_q v − q‖² ≤ 2·‖v‖²`).  As stated it is GLOBAL (`∀ v`), which is FALSE in general (the
  geodesic flow drives `rncRadialSq (φ_q v − q)` unboundedly for large `v`); but the M3 consumer only
  APPLIES it at ball points `‖v‖ < r₀`.  So the correct — and provable — form is BALL-LOCAL.

  ## What this file delivers (all DERIVED from `hC` + `IsCompact K`; NO `sorry`, no `expRho` in
  statements, NOT `a₁ = R/6`).

  * (D1) `uniformFlowExp_zero` — the zero-velocity geodesic is constant: `φ_q 0 = q`.  Trivial from the
    tube confinement `‖φ_q v − q‖ ≤ C₀‖v‖` at `v = 0` (no ODE-uniqueness engine needed).
  * (near-id) `uniformFlowExp_fderiv_near_id_quant` — the UNCONDITIONAL uniform near-identity Jacobian
    bound `‖Dφ_q(v) − Id‖ ≤ C_D·‖v‖` over `q ∈ K`, `‖v‖ < ρ₀`.  This is the Grönwall/Jacobi tail of
    `uniformFlowExp_common_nondeg_radius_quant` (`UniformInverseMetric.lean`), which only exposed the
    inverse bound; here the near-identity operator bound is EXTRACTED as a standalone conclusion (the
    exposed second-jet Hessian route carries a firewalled `hdiag`, so it cannot be used unconditionally).
  * (D2) `uniformFlowExp_displacement_bound` — the QUADRATIC displacement bound
    `‖φ_q v − q − v‖ ≤ C_D·‖v‖·‖v‖` over `q ∈ K`, `‖v‖ < ρ₀`, from D1 + the near-identity bound via the
    segment mean-value inequality on `w ↦ φ_q w − w` (derivative `Dφ_q − Id`, bounded by `C_D·‖v‖`).
  * (D3) `uniformFlowExp_hdisp_ball` — the ball-local `hdisp`: `∃ r₁ > 0, ∀ q ∈ K, ∀ ‖v‖ < r₁`,
    `3/2·rncRadialSq (φ_q v − q) ≤ 2·rncRadialSq v`, from D2 via the ℓ²-direct expansion
    `∑ (v+e)ᵢ² ≤ rncRadialSq v·(1 + 2n·C_D·r₁ + n·C_D²·r₁²)` (shrink `r₁` — the dimension factor `n` is
    ABSORBED into `r₁`, no `n`-obstruction).
  * (CAPSTONE) `globalWitness_residual_bound_chartGaussian_final` — the M3 consumer-width bound with
    `hdisp` DISCHARGED (restated ball-local): hypotheses ONLY the genuine
    `hg/hC/hK/hgnd/hgsymm/hinvF/hframeK` + `Θ/u/hw0smooth/hw0flat`.  Fully unconditional in-chart.
-/
import Mathlib
import QIQTH.WidthMarginEngine
import QIQTH.UniformInverseMetric
import QIQTH.UniformFlowFDeriv

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.RadialDistance
open QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.RNCDecay QIQTH.TrueHeatKernel
open Set Filter
open scoped Topology NNReal BigOperators Matrix

namespace QIQTH.ExpMap

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### (D1) The zero-velocity geodesic is constant:  `φ_q 0 = q`. -/

/-- **★ J4-96 (D1) — `uniformFlowExp g gi hC hK q 0 = q`.**  The zero-velocity confined geodesic tube is
    the constant curve `(q, 0)` on `[0,1]`: its confinement bound is `‖tube q 0 t − (q,0)‖ ≤ C₀·‖0‖ = 0`,
    forcing `tube q 0 1 = (q,0)`, whose position slot is `q`.  No ODE-uniqueness engine needed. -/
theorem uniformFlowExp_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    uniformFlowExp g gi hC hK q 0 = q := by
  have h0ρ : ‖(0 : Point n)‖ ≤ uniformFlowRadius g gi hC hK := by
    rw [norm_zero]; exact (uniformFlowRadius_pos g gi hC hK).le
  have hconf := uniformFlowTube_spec_conf g gi hC hK q hq 0 h0ρ 1
    (Set.right_mem_Icc.mpr zero_le_one)
  rw [norm_zero, mul_zero] at hconf
  have heq : uniformFlowTube g gi hC hK q 0 1 = ((q, 0) : Point n × Point n) :=
    sub_eq_zero.mp (norm_le_zero_iff.mp hconf)
  rw [uniformFlowExp_eq, heq]

/-! ### The UNCONDITIONAL uniform near-identity Jacobian bound. -/

/-- **★ J4-96 (near-id) — extraction of `‖Dφ_q(v) − Id‖ ≤ C_D·‖v‖`.**

    There is a single radius `ρ₀ > 0` and constant `C_D ≥ 0` such that for every `q ∈ K`, `‖v‖ < ρ₀`,
    the uniform-flow exp Jacobian `Dφ_q(v) = fderiv ℝ (uniformFlowExp g gi hC hK q) v` satisfies the
    near-identity bound `‖Dφ_q(v) − Id‖ ≤ C_D·‖v‖`.

    This is exactly the Grönwall/Jacobi tail of `uniformFlowExp_common_nondeg_radius_quant`
    (`UniformInverseMetric.lean`, which only exposed the derived INVERSE bound `‖(Dφ_q)⁻¹‖ ≤ 2`): the
    zero-velocity flat Jacobi field `Jflat_δ τ = (τ·δ, δ)` has endpoint `δ`, and the two-base linear-ODE
    comparison `linODE_twopoint_diff_bound` bounds the velocity-Jacobi endpoint against it by
    `M₂·C₀·e^{K_f}·‖v‖ = C_D·‖v‖`.  Hypotheses ONLY `hC` + `IsCompact K` (unconditional). -/
theorem uniformFlowExp_fderiv_near_id_quant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      ‖fderiv ℝ (uniformFlowExp g gi hC hK q) v - ContinuousLinearMap.id ℝ (Point n)‖ ≤ C_D * ‖v‖ := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, 0, le_refl (0 : ℝ), ?_⟩
    intro q hq
    simp only [hKe, Set.mem_empty_iff_false] at hq
  -- Uniform radius / constant.
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  obtain ⟨p₀, hp₀⟩ := hKne
  obtain ⟨R, hRsub⟩ := hK.isBounded.subset_closedBall p₀
  have hR0 : 0 ≤ R := by
    have h := hRsub hp₀; rw [Metric.mem_closedBall, dist_self] at h; exact h
  set Rbase : ℝ := R + ‖p₀‖ with hRbasedef
  have hRbase0 : 0 ≤ Rbase := by rw [hRbasedef]; positivity
  set RG : ℝ := Rbase + C₀ * ρ with hRGdef
  have hRG0 : 0 ≤ RG := by rw [hRGdef]; positivity
  set S : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) RG with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  have h0S : (0 : Point n × Point n) ∈ S := by rw [hSdef]; exact Metric.mem_closedBall_self hRG0
  have hdiffglob : Differentiable ℝ (fderiv ℝ (geodesicField g gi)) :=
    ((contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top).differentiable (by simp)
  obtain ⟨M₂, hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
      (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
        (by simp)).norm
    obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn ⟨(0 : Point n × Point n), h0S⟩ hcontr.continuousOn
    exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
      norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x),
      fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  obtain ⟨K₀, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) hSconv hScompact
  set C_D : ℝ := M₂ * C₀ * Real.exp Kf with hCDdef
  have hCD0 : 0 ≤ C_D := by
    rw [hCDdef]; exact mul_nonneg (mul_nonneg hM₂0 hC₀nn) (Real.exp_pos _).le
  have hCD1 : (0 : ℝ) < 2 * (C_D + 1) := by linarith [hCD0]
  set ρ₀ : ℝ := min ρ (1 / (2 * (C_D + 1))) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := lt_min hρ0 (div_pos one_pos hCD1)
  refine ⟨ρ₀, hρ₀pos, C_D, hCD0, ?_⟩
  intro q hq v hv
  have hvr : ‖v‖ < ρ := lt_of_lt_of_le hv (by rw [hρ₀def]; exact min_le_left _ _)
  have hvρ : ‖v‖ ≤ ρ := hvr.le
  have hvle : ‖v‖ ≤ 1 / (2 * (C_D + 1)) :=
    le_of_lt (lt_of_lt_of_le hv (by rw [hρ₀def]; exact min_le_right _ _))
  have hqbase : ‖q‖ ≤ Rbase := by
    have hmb := hRsub hq
    rw [Metric.mem_closedBall, dist_eq_norm] at hmb
    calc ‖q‖ = ‖(q - p₀) + p₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖q - p₀‖ + ‖p₀‖ := norm_add_le _ _
      _ ≤ R + ‖p₀‖ := by linarith [hmb]
      _ = Rbase := by rw [hRbasedef]
  have hqn : ‖((q, 0) : Point n × Point n)‖ ≤ Rbase := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg q)]; exact hqbase
  have hqmem : ((q, 0) : Point n × Point n) ∈ S := by
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]
    calc ‖((q, 0) : Point n × Point n)‖ ≤ Rbase := hqn
      _ ≤ RG := by rw [hRGdef]; exact le_add_of_nonneg_right (mul_nonneg hC₀nn hρ0.le)
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  set Wf : Point n → ℝ → Point n × Point n :=
    fun δ => uniformFlowTube g gi hC hK q (v + δ) with hWfdef
  have hle : ∀ δ : Point n, ‖δ‖ ≤ σ → ‖v + δ‖ ≤ ρ := by
    intro δ hδ
    refine (norm_add_le v δ).trans ?_
    rw [hσdef] at hδ; linarith
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Wf δ) (geodesicField g gi (Wf δ τ)) τ := by
    intro δ hδ τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK q hq (v + δ) (hle δ hδ) τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, Wf δ τ ∈ S := by
    intro δ hδ τ hτ
    rw [hSdef, Metric.mem_closedBall]
    have hconf : ‖Wf δ τ - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v + δ‖ :=
      uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) (hle δ hδ) τ hτ
    have hc : C₀ * ‖v + δ‖ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left (hle δ hδ) hC₀nn
    calc dist (Wf δ τ) (0 : Point n × Point n)
        ≤ dist (Wf δ τ) ((q, 0) : Point n × Point n)
            + dist ((q, 0) : Point n × Point n) (0 : Point n × Point n) := dist_triangle _ _ _
      _ = ‖Wf δ τ - ((q, 0) : Point n × Point n)‖ + ‖((q, 0) : Point n × Point n)‖ := by
            rw [dist_eq_norm, dist_zero_right]
      _ ≤ C₀ * ρ + Rbase := add_le_add (le_trans hconf hc) hqn
      _ = RG := by rw [hRGdef]; ring
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → Wf δ 0 - Wf 0 0 = ((0, δ) : Point n × Point n) := by
    intro δ hδ
    have h1 : Wf δ 0 = (q, v + δ) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + δ) (hle δ hδ)
    have h2 : Wf 0 0 = (q, v + 0) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + 0) (hle 0 h0σ)
    rw [h1, h2, Prod.mk_sub_mk, sub_self, add_zero, add_sub_cancel_left]
  have hbasecont : ContinuousOn (Wf 0) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + 0) (hle 0 h0σ) τ hτoo).continuousAt).continuousWithinAt
  set V : Point n → ℝ → Point n × Point n :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont ((0, δ) : Point n × Point n)).choose
    with hVdef
  have hV0 : ∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n) :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((0, δ) : Point n × Point n)).choose_spec.1
  have hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (Wf 0 τ) (V δ τ)) τ :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((0, δ) : Point n × Point n)).choose_spec.2
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂ := hM₂
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Wf 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKf (Wf 0 τ) (hmem 0 h0σ τ hτ)
  obtain ⟨L, hLeq, hFD⟩ :=
    flowVelocity_endpoint_hasFDerivAt_window_exists g gi hC hKf0 hσ ht1 hSconv hbound2 hLip
      hWode hVode hV0 hIC hKb hmem
  set Lpos : Point n →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp L with hLposdef
  have hLpos_apply : ∀ δ : Point n, Lpos δ = (V δ 1).1 := fun δ => by
    show (L δ).1 = (V δ 1).1
    rw [hLeq δ]
  have hFDpos : HasFDerivAt (fun δ => (Wf δ 1).1) Lpos 0 := by
    have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp (0 : Point n) hFD
    simpa [hLposdef, Function.comp] using this
  have hfun : (fun δ => (Wf δ 1).1) = (fun δ => uniformFlowExp g gi hC hK q (v + δ)) := by
    funext δ; rw [hWfdef]; rw [uniformFlowExp_eq]
  rw [hfun] at hFDpos
  have hshift : HasFDerivAt (fun u : Point n => u - v) (ContinuousLinearMap.id ℝ (Point n)) v :=
    (hasFDerivAt_id v).sub_const v
  have hFDpos0 : HasFDerivAt (fun δ => uniformFlowExp g gi hC hK q (v + δ)) Lpos (v - v) := by
    rw [sub_self]; exact hFDpos
  have hcomp : HasFDerivAt (fun u => uniformFlowExp g gi hC hK q (v + (u - v)))
      (Lpos.comp (ContinuousLinearMap.id ℝ (Point n))) v :=
    hFDpos0.comp (f := fun u : Point n => u - v) v hshift
  have hfun2 : (fun u => uniformFlowExp g gi hC hK q (v + (u - v)))
      = uniformFlowExp g gi hC hK q := by
    funext u; congr 1; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  have hFDexp : HasFDerivAt (uniformFlowExp g gi hC hK q) Lpos v := hcomp
  have hjac0 : ∀ ξ η : Point n, jacobiOperator g gi q (0 : Point n) ξ η = 0 := by
    intro ξ η; funext i; simp [jacobiOperator]
  have hnearId : ∀ δ : Point n, ‖Lpos δ - δ‖ ≤ (C_D * ‖v‖) * ‖δ‖ := by
    intro δ
    set Jf : ℝ → Point n × Point n := fun τ => ((τ • δ, δ) : Point n × Point n) with hJf
    have hX1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (V δ)
        (fderiv ℝ (geodesicField g gi) (Wf 0 t) (V δ t) + (0 : Point n × Point n)) t := by
      intro t ht; rw [add_zero]; exact hVode δ t ht
    have hX2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Jf
        (fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n) (Jf t) + (0 : Point n × Point n)) t := by
      intro t ht
      have hJt : Jf t = ((t • δ, δ) : Point n × Point n) := by simp only [hJf]
      have hA2 : fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n) (Jf t)
          = ((δ, 0) : Point n × Point n) := by
        rw [hJt, geodesicField_fderiv_eq_jacobiOperator g gi hC q 0 (t • δ) δ, hjac0 (t • δ) δ]; simp
      rw [hA2, add_zero]
      have hJfe : Jf = fun τ : ℝ => τ • ((δ, 0) : Point n × Point n) + ((0, δ) : Point n × Point n) := by
        funext τ; rw [hJf]; simp [Prod.smul_mk, Prod.mk_add_mk]
      have hd : HasDerivAt Jf (((δ : Point n), (0 : Point n)) : Point n × Point n) t := by
        rw [hJfe]
        simpa using
          ((hasDerivAt_id t).smul_const ((δ, 0) : Point n × Point n)).add_const ((0, δ) : Point n × Point n)
      exact hd
    have h0eq : V δ 0 = Jf 0 := by rw [hV0 δ]; simp only [hJf, zero_smul]
    have hAd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖fderiv ℝ (geodesicField g gi) (Wf 0 t)
          - fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n)‖ ≤ M₂ * C₀ * ‖v‖ := by
      intro t ht
      have hconf0 : ‖Wf 0 t - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v + 0‖ :=
        uniformFlowTube_spec_conf g gi hC hK q hq (v + 0) (hle 0 h0σ) t ht
      have hmvt := hSconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
        (f := fderiv ℝ (geodesicField g gi)) (fun x _ => hdiffglob x) hbound2 hqmem (hmem 0 h0σ t ht)
      refine le_trans hmvt ?_
      calc M₂ * ‖Wf 0 t - ((q, 0) : Point n × Point n)‖
          ≤ M₂ * (C₀ * ‖v + 0‖) := mul_le_mul_of_nonneg_left hconf0 hM₂0
        _ = M₂ * C₀ * ‖v‖ := by rw [add_zero]; ring
    have hXb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Jf t‖ ≤ ‖δ‖ := by
      intro t ht
      rw [hJf]
      show ‖((t • δ, δ) : Point n × Point n)‖ ≤ ‖δ‖
      rw [Prod.norm_def]
      apply max_le
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc t * ‖δ‖ ≤ 1 * ‖δ‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          _ = ‖δ‖ := one_mul _
      · exact le_refl _
    have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖(fun _ : ℝ => (0 : Point n × Point n)) t - (fun _ : ℝ => (0 : Point n × Point n)) t‖
          ≤ (0 : ℝ) := by intro t ht; simp
    have hgron := linODE_twopoint_diff_bound (E := Point n × Point n)
      (A₁ := fun t => fderiv ℝ (geodesicField g gi) (Wf 0 t))
      (A₂ := fun _ => fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n))
      (b₁ := fun _ => (0 : Point n × Point n)) (b₂ := fun _ => (0 : Point n × Point n))
      (X₁ := V δ) (X₂ := Jf) (K := Kf) (Dcoef := M₂ * C₀ * ‖v‖) (Xb := ‖δ‖) (Dsrc := 0)
      hKf0 hX1 hX2 h0eq hKb hAd hXb hbd 1 ht1
    have hJf1 : (Jf 1).1 = δ := by simp only [hJf, one_smul]
    calc ‖Lpos δ - δ‖
        = ‖(V δ 1).1 - (Jf 1).1‖ := by rw [hLpos_apply δ, hJf1]
      _ = ‖(V δ 1 - Jf 1).1‖ := by rw [Prod.fst_sub]
      _ ≤ ‖V δ 1 - Jf 1‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ (M₂ * C₀ * ‖v‖ * ‖δ‖ + 0) * Real.exp Kf := hgron
      _ = (C_D * ‖v‖) * ‖δ‖ := by rw [hCDdef]; ring
  have hopnorm : ‖Lpos - ContinuousLinearMap.id ℝ (Point n)‖ ≤ C_D * ‖v‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hCD0 (norm_nonneg v)) (fun δ => ?_)
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    exact hnearId δ
  have hfd : fderiv ℝ (uniformFlowExp g gi hC hK q) v = Lpos := hFDexp.fderiv
  rw [hfd]; exact hopnorm

/-! ### (D2) The quadratic displacement bound `‖φ_q v − q − v‖ ≤ C_D·‖v‖·‖v‖`. -/

/-- **★ J4-96 (D2) — quadratic near-identity displacement.**  For `q ∈ K`, `‖v‖ < ρ₀`,
    `‖φ_q v − q − v‖ ≤ C_D·‖v‖·‖v‖`.  From D1 (`φ_q 0 = q`) + the near-identity Jacobian bound
    (`‖Dφ_q − Id‖ ≤ C_D·‖·‖`) via the segment mean-value inequality on `w ↦ φ_q w − w` (whose derivative
    is `Dφ_q − Id`, bounded on the segment `[0,v]` by `C_D·‖v‖`). -/
theorem uniformFlowExp_displacement_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_D * ‖v‖ * ‖v‖ := by
  obtain ⟨ρ₁, hρ₁pos, C_D, hCD0, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  set ρK : ℝ := uniformFlowRadius g gi hC hK with hρK
  set r : ℝ := min ρ₁ ρK with hr
  have hrpos : 0 < r := lt_min hρ₁pos (uniformFlowRadius_pos g gi hC hK)
  have hrρ₁ : r ≤ ρ₁ := by rw [hr]; exact min_le_left _ _
  have hrρK : r ≤ ρK := by rw [hr]; exact min_le_right _ _
  refine ⟨r, hrpos, C_D, hCD0, ?_⟩
  intro q hq v hv
  -- Points on the segment [0,v] have norm ≤ ‖v‖.
  have hseg_norm : ∀ x ∈ segment ℝ (0 : Point n) v, ‖x‖ ≤ ‖v‖ := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    rw [smul_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    have hb1 : b ≤ 1 := by linarith
    calc b * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  have hxρK : ∀ x ∈ segment ℝ (0 : Point n) v, ‖x‖ < ρK :=
    fun x hx => lt_of_le_of_lt (hseg_norm x hx) (lt_of_lt_of_le hv hrρK)
  have hxρ₁ : ∀ x ∈ segment ℝ (0 : Point n) v, ‖x‖ < ρ₁ :=
    fun x hx => lt_of_le_of_lt (hseg_norm x hx) (lt_of_lt_of_le hv hrρ₁)
  -- φ_q is differentiable on the segment, with `fderiv` given by `uniformFlowExp_hasFDerivAt`.
  have hHFDat : ∀ x ∈ segment ℝ (0 : Point n) v,
      HasFDerivAt (uniformFlowExp g gi hC hK q) (fderiv ℝ (uniformFlowExp g gi hC hK q) x) x := by
    intro x hx
    obtain ⟨L, hL⟩ := uniformFlowExp_hasFDerivAt g gi hC hK q hq x (hxρK x hx)
    rw [hL.fderiv]; exact hL
  have hdiff : ∀ x ∈ segment ℝ (0 : Point n) v,
      DifferentiableAt ℝ (fun w => uniformFlowExp g gi hC hK q w - w) x :=
    fun x hx => ((hHFDat x hx).sub (hasFDerivAt_id x)).differentiableAt
  have hbound : ∀ x ∈ segment ℝ (0 : Point n) v,
      ‖fderiv ℝ (fun w => uniformFlowExp g gi hC hK q w - w) x‖ ≤ C_D * ‖v‖ := by
    intro x hx
    have hHFD : HasFDerivAt (fun w => uniformFlowExp g gi hC hK q w - w)
        (fderiv ℝ (uniformFlowExp g gi hC hK q) x - ContinuousLinearMap.id ℝ (Point n)) x :=
      (hHFDat x hx).sub (hasFDerivAt_id x)
    rw [hHFD.fderiv]
    calc ‖fderiv ℝ (uniformFlowExp g gi hC hK q) x - ContinuousLinearMap.id ℝ (Point n)‖
        ≤ C_D * ‖x‖ := hnear q hq x (hxρ₁ x hx)
      _ ≤ C_D * ‖v‖ := mul_le_mul_of_nonneg_left (hseg_norm x hx) hCD0
  have hmvt := (convex_segment (𝕜 := ℝ) (0 : Point n) v).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (left_mem_segment ℝ (0 : Point n) v) (right_mem_segment ℝ (0 : Point n) v)
  have hφ0 : uniformFlowExp g gi hC hK q (0 : Point n) = q := uniformFlowExp_zero g gi hC hK q hq
  simp only [hφ0, sub_zero] at hmvt
  -- `hmvt : ‖φ_q v - v - q‖ ≤ C_D * ‖v‖ * ‖v‖`
  rw [show uniformFlowExp g gi hC hK q v - q - v
        = uniformFlowExp g gi hC hK q v - v - q from by abel]
  exact hmvt

end QIQTH.ExpMap

namespace QIQTH.HeatResidualBound

open QIQTH.ExpMap

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### An ℓ² expansion helper for `rncRadialSq`. -/

/-- `rncRadialSq (v + e) ≤ rncRadialSq v + 2n·(‖v‖·‖e‖) + n·‖e‖²` — the coordinatewise expansion
    `∑ (vᵢ+eᵢ)² = ∑vᵢ² + 2∑vᵢeᵢ + ∑eᵢ²` with the cross/square sums bounded by the sup-norm (`n` terms,
    each `≤ ‖v‖·‖e‖` resp. `≤ ‖e‖²`). -/
theorem rncRadialSq_add_le (v e : Point n) :
    rncRadialSq (v + e) ≤ rncRadialSq v + 2 * (n : ℝ) * (‖v‖ * ‖e‖) + (n : ℝ) * ‖e‖ ^ 2 := by
  have hexp : rncRadialSq (v + e)
      = rncRadialSq v + (∑ i, 2 * ((v i) * (e i))) + ∑ i, (e i) ^ 2 := by
    simp only [rncRadialSq, Pi.add_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hexp]
  have hcross : (∑ i, 2 * ((v i) * (e i))) ≤ 2 * (n : ℝ) * (‖v‖ * ‖e‖) := by
    calc (∑ i, 2 * ((v i) * (e i))) ≤ ∑ _i : Fin n, 2 * (‖v‖ * ‖e‖) := by
          apply Finset.sum_le_sum
          intro i _
          have hle : (v i) * (e i) ≤ |v i| * |e i| := by rw [← abs_mul]; exact le_abs_self _
          have h2 : |v i| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
          have h3 : |e i| ≤ ‖e‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm e i
          have hprod : |v i| * |e i| ≤ ‖v‖ * ‖e‖ :=
            mul_le_mul h2 h3 (abs_nonneg _) (norm_nonneg _)
          calc 2 * ((v i) * (e i)) ≤ 2 * (|v i| * |e i|) :=
                mul_le_mul_of_nonneg_left hle (by norm_num)
            _ ≤ 2 * (‖v‖ * ‖e‖) := mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ = 2 * (n : ℝ) * (‖v‖ * ‖e‖) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hsq : (∑ i, (e i) ^ 2) ≤ (n : ℝ) * ‖e‖ ^ 2 := by
    calc (∑ i, (e i) ^ 2) ≤ ∑ _i : Fin n, ‖e‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have h3 : |e i| ≤ ‖e‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm e i
          calc (e i) ^ 2 = |e i| ^ 2 := by rw [sq_abs]
            _ ≤ ‖e‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = (n : ℝ) * ‖e‖ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  linarith

/-! ### (D3) The ball-local near-isometry width budget `hdisp`. -/

/-- **★ J4-96 (D3) — ball-local `hdisp`.**  There is `r₁ > 0` such that for every `q ∈ K`, `‖v‖ < r₁`,
    `3/2·rncRadialSq (φ_q v − q) ≤ 2·rncRadialSq v`.  From the quadratic displacement bound (D2)
    `‖φ_q v − q − v‖ ≤ C_D·‖v‖²` via the ℓ² expansion `rncRadialSq_add_le` with `e = φ_q v − q − v`:
    `rncRadialSq (v + e) ≤ rncRadialSq v·(1 + 2n·C_D·r₁ + n·C_D²·r₁²)`, and `r₁` is shrunk so the
    correction factor is `≤ 4/3` (the dimension `n` is absorbed into `r₁` — no `n`-obstruction). -/
theorem uniformFlowExp_hdisp_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₁ →
      3 / 2 * rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ 2 * rncRadialSq v := by
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hdisp2⟩ := uniformFlowExp_displacement_bound g gi hC hK
  set D : ℝ := 2 * (n : ℝ) * C_D + (n : ℝ) * C_D ^ 2 + 1 with hD
  have hDpos : 0 < D := by
    have h1 : 0 ≤ 2 * (n : ℝ) * C_D := mul_nonneg (by positivity) hCD0
    have h2 : 0 ≤ (n : ℝ) * C_D ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg C_D)
    rw [hD]; linarith
  set r₁ : ℝ := min ρ₀ (min 1 (1 / (3 * D))) with hr₁
  have hr₁pos : 0 < r₁ := lt_min hρ₀pos (lt_min one_pos (by positivity))
  refine ⟨r₁, hr₁pos, ?_⟩
  intro q hq v hv
  have hvρ₀ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (by rw [hr₁]; exact min_le_left _ _)
  have he : ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_D * ‖v‖ * ‖v‖ := hdisp2 q hq v hvρ₀
  set e : Point n := uniformFlowExp g gi hC hK q v - q - v with hedef
  have hxe : uniformFlowExp g gi hC hK q v - q = v + e := by rw [hedef]; abel
  rw [hxe]
  have hadd := rncRadialSq_add_le v e
  have hrv : (0 : ℝ) ≤ rncRadialSq v := rncRadialSq_nonneg v
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hne : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  have hnvsq : ‖v‖ ^ 2 ≤ rncRadialSq v := by
    have h := norm_le_rncRadial v
    calc ‖v‖ ^ 2 ≤ (rncRadial v) ^ 2 := pow_le_pow_left₀ hnv h 2
      _ = rncRadialSq v := rncRadial_sq v
  have he2 : ‖e‖ ≤ C_D * ‖v‖ ^ 2 := by rw [sq, ← mul_assoc]; exact he
  have hvr1 : ‖v‖ ≤ r₁ := hv.le
  have hr1_le1 : r₁ ≤ 1 := by rw [hr₁]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr1_leD : r₁ ≤ 1 / (3 * D) := by rw [hr₁]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- term bounds
  have hnvsq_r1 : ‖v‖ ^ 2 ≤ r₁ ^ 2 := by nlinarith [hvr1, hnv, hr₁pos.le]
  have hT1 : ‖v‖ * ‖e‖ ≤ C_D * r₁ * rncRadialSq v := by
    have h1 : ‖v‖ * ‖e‖ ≤ ‖v‖ * (C_D * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left he2 hnv
    have h2 : ‖v‖ ^ 2 * ‖v‖ ≤ rncRadialSq v * r₁ := mul_le_mul hnvsq hvr1 hnv hrv
    nlinarith [h1, mul_le_mul_of_nonneg_left h2 hCD0]
  have hT2 : ‖e‖ ^ 2 ≤ C_D ^ 2 * r₁ ^ 2 * rncRadialSq v := by
    have he2sq : ‖e‖ ^ 2 ≤ (C_D * ‖v‖ ^ 2) ^ 2 := pow_le_pow_left₀ hne he2 2
    have hv4 : ‖v‖ ^ 2 * ‖v‖ ^ 2 ≤ rncRadialSq v * r₁ ^ 2 :=
      mul_le_mul hnvsq hnvsq_r1 (sq_nonneg _) hrv
    nlinarith [he2sq, mul_le_mul_of_nonneg_left hv4 (sq_nonneg C_D)]
  -- coefficient bound
  have hr1sq : r₁ ^ 2 ≤ r₁ := by nlinarith [hr₁pos.le, hr1_le1]
  have hnC2 : (0 : ℝ) ≤ (n : ℝ) * C_D ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg C_D)
  have hbig : 2 * (n : ℝ) * C_D * r₁ + (n : ℝ) * C_D ^ 2 * r₁ ^ 2 ≤ D * r₁ := by
    rw [hD]; nlinarith [mul_nonneg hnC2 (sub_nonneg.mpr hr1sq), hr₁pos.le]
  have hr1D : D * r₁ ≤ 1 / 3 := by
    calc D * r₁ ≤ D * (1 / (3 * D)) := mul_le_mul_of_nonneg_left hr1_leD hDpos.le
      _ = 1 / 3 := by
          rw [mul_one_div, div_eq_iff (mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) hDpos.ne')]; ring
  have hcoef : 2 * (n : ℝ) * C_D * r₁ + (n : ℝ) * C_D ^ 2 * r₁ ^ 2 ≤ 1 / 3 := le_trans hbig hr1D
  -- middle bound
  have hM : 2 * (n : ℝ) * (‖v‖ * ‖e‖) + (n : ℝ) * ‖e‖ ^ 2 ≤ 1 / 3 * rncRadialSq v := by
    nlinarith [mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hT2 (Nat.cast_nonneg n),
      mul_le_mul_of_nonneg_right hcoef hrv, hrv]
  linarith [hadd, hM]

/-! ### (CAPSTONE) The M3 consumer-width bound with `hdisp` discharged. -/

/-- **★★ J4-96 CAPSTONE — the CONSUMER-WIDTH per-base-point chart-Gaussian bound, `hdisp` DISCHARGED.**

    Identical to `globalWitness_residual_bound_chartGaussian` (M3, `WidthMarginEngine.lean`) but with the
    near-isometry width budget `hdisp` no longer carried: it is discharged BALL-LOCALLY by
    `uniformFlowExp_hdisp_ball` (D3) and applied only at the ball points `‖v‖ < r₀` where the M3 consumer
    uses it (`r₀ := min r₀' r₁`).  Hypotheses are ONLY the genuine geometric/heat data
    `hg/hC/hK/hgnd/hgsymm/hinvF/hframeK` + `Θ/u/hw0smooth/hw0flat`.  Fully unconditional in-chart. -/
theorem globalWitness_residual_bound_chartGaussian_final (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧
      ∀ (τ : ℝ) (q : Point n), q ∈ K → 0 < τ →
        ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
          |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
              (uniformFlowExp g gi hC hK q v) q|
            ≤ B * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by
  obtain ⟨r₁, hr₁pos, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hC hK
  obtain ⟨a, b, B, ha, hab, hB, hbound⟩ :=
    globalWitness_residual_bound_inChart_final_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B * Real.sqrt (2 / (3 / 2)) ^ n, ha, hab, by positivity, ?_⟩
  intro τ q hq hτ
  obtain ⟨r₀, hr₀, hboundinner⟩ := hbound τ q hq hτ
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁pos, ?_⟩
  intro v hv
  have hvr₀ : ‖v‖ < r₀ := lt_of_lt_of_le hv (min_le_left _ _)
  have hvr₁ : ‖v‖ < r₁ := lt_of_lt_of_le hv (min_le_right _ _)
  have hnarrow := hboundinner v hvr₀
  have htransfer :
      gaussDdim (3 / 2 * τ) v
        ≤ Real.sqrt (2 / (3 / 2)) ^ n
            * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) :=
    gaussDdim_le_gaussDdim_chart (c := 3 / 2) (d := 2) (by norm_num) (by norm_num) hτ
      (hdisp q hq v hvr₁)
  calc |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
            (uniformFlowExp g gi hC hK q v) q|
      ≤ B * gaussDdim (3 / 2 * τ) v := hnarrow
    _ ≤ B * (Real.sqrt (2 / (3 / 2)) ^ n
          * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) :=
        mul_le_mul_of_nonneg_left htransfer hB
    _ = B * Real.sqrt (2 / (3 / 2)) ^ n
          * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by ring

end QIQTH.HeatResidualBound
