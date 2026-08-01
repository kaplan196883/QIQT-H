/-
  UniformInverseMetric — J4-80b (Route B): the uniform INVERSE-metric bound for the `uniformFlowExp`
  pullback metric `g̃`, the exact ingredient firewalled by J4-80 (`UniformResidualB.lean`).

  ## Context — the firewalled MISSING statement (J4-80 header).

  `UniformResidualB.uniformResidual_forwardMetric_packet` delivered uniform FORWARD-metric `C⁰/C¹/C²`
  bounds + `IsUnit (fderiv uniformFlowExp)` + `IsUnit (matToCLM g̃)` over `q∈K`, `‖v‖<r₀`, but explicitly
  did NOT deliver a UNIFORM NORM bound on the inverse metric `g̃⁻¹`:

    MISSING:  `∃ r₀>0, ∃ Kinv, ∀ q∈K, ∀ ‖v‖<r₀,
                 ‖Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b))‖ ≤ Kinv`
              (whence entrywise `|g̃⁻¹(v) i j| ≤ Kinv`).

  This file DELIVERS that statement (`uniformInverseMetric_bound`) via **Route B** (congruence
  factorization `g̃ = Jᵀ·(g∘F)·J`), in three pieces:

    (P1) `uniformFlowExp_common_nondeg_radius_quant` — uniform QUANTITATIVE Jacobian-inverse bound:
         `IsUnit (fderiv uniformFlowExp) ∧ ‖Ring.inverse (fderiv uniformFlowExp)‖ ≤ 2`, re-deriving the
         near-identity Grönwall/Neumann tail of `uniformFlowExp_common_nondeg_radius` (which DISCARDED the
         constant) and keeping the operator-norm bound `‖fderiv − id‖ ≤ C_D·‖v‖ ≤ 1/2`, then the
         geometric-series inverse bound `‖(1−t)⁻¹‖ ≤ (1−‖t‖)⁻¹ ≤ 2`.

    (P2) `uniformFlowExp_baseMetricInv_uniform_bound` — uniform base-metric-inverse bound on the endpoint
         tube: with the GENUINE global nondegeneracy `hgnd : ∀ y, IsUnit (matToCLM (g y))`, the map
         `y ↦ ‖Ring.inverse (matToCLM (g y))‖` is CONTINUOUS (units are open; `Ring.inverse` continuous at
         units) so the tube-EVT bound confines it by a single `Kb` over `q∈K`, `‖v‖ ≤ ρ_K`.

    (P3) inverse congruence + capstone: `matToCLM g̃ = matToCLM(Jᵀ)·(g∘F)_op·J`, so
         `Ring.inverse (matToCLM g̃) = J⁻¹·(g∘F)⁻¹·(Jᵀ_op)⁻¹` with `‖J⁻¹‖ ≤ 2`, `‖(g∘F)⁻¹‖ ≤ Kb`, and a
         dimension-crude `‖(Jᵀ_op)⁻¹‖ ≤ 2n²` (transpose-inverse = `(jacMat J⁻¹)ᵀ`-operator, entries `≤ 2`
         via `‖J⁻¹‖ ≤ 2`, summed).

  Hypotheses of the capstone are ONLY `hg` (metric regularity) + `hC` (Christoffel `C^∞`) + `IsCompact K`
  + `hgnd` (global base-metric nondegeneracy — a GENUINE Riemannian input, satisfiable by `g = δ`, NOT the
  conclusion).  No `sorry`, no new axioms, no `expRho`, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowNondegClose
import QIQTH.UniformFlowMetricC2Bound
import QIQTH.UniformFlowPullback
import Mathlib

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric
open Set Filter
open scoped Topology NNReal BigOperators Matrix

namespace QIQTH.ExpMap

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### Neumann geometric-series inverse-norm bound (general normed ring). -/

/-- **Neumann pointwise inverse-norm bound.**  In a normed ring with summable geometric series and
    `‖1‖ ≤ 1`, if `‖t‖ < 1` then `‖Ring.inverse (1 − t)‖ ≤ (1 − ‖t‖)⁻¹`.  (Geometric-series sum bound.) -/
theorem norm_ringInverse_one_sub_le {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    (hR1 : ‖(1 : R)‖ ≤ 1) (t : R) (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ (1 - ‖t‖)⁻¹ := by
  rw [← geom_series_eq_inverse t h]
  calc ‖∑' k : ℕ, t ^ k‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖t‖)⁻¹ := tsum_geometric_le_of_norm_lt_one t h
    _ ≤ (1 - ‖t‖)⁻¹ := by linarith

/-! ### (P1) — uniform QUANTITATIVE Jacobian-inverse bound for `uniformFlowExp`. -/

/-- **★ J4-80b (P1) — uniform quantitative nondegeneracy: the Jacobian inverse is bounded by `2`.**

    There is a SINGLE radius `ρ₀ > 0` such that for every `q ∈ K` and every velocity `v` with `‖v‖ < ρ₀`
    the uniform-flow exp Jacobian `fderiv ℝ (uniformFlowExp g gi hC hK q) v` is a unit AND its ring
    inverse has operator norm `≤ 2`.  This RE-DERIVES the near-identity Grönwall/Neumann tail of
    `uniformFlowExp_common_nondeg_radius` (which discards the constant), keeping the quantitative bound
    `‖fderiv − id‖ ≤ C_D·‖v‖ ≤ 1/2`, then applies the geometric-series inverse-norm bound.  Hypotheses
    ONLY `hC` (Christoffel `C^∞`) + `IsCompact K`. -/
theorem uniformFlowExp_common_nondeg_radius_quant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v)
      ∧ ‖Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK q) v)‖ ≤ 2 := by
  classical
  have hR1 : ‖(1 : Point n →L[ℝ] Point n)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id_le
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, ?_⟩
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
  refine ⟨ρ₀, hρ₀pos, ?_⟩
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
  have hCDhalf : C_D * ‖v‖ ≤ 1 / 2 := by
    have h1 : C_D * ‖v‖ ≤ C_D * (1 / (2 * (C_D + 1))) := mul_le_mul_of_nonneg_left hvle hCD0
    have h2 : C_D * (1 / (2 * (C_D + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hCD1]; nlinarith [hCD0]
    linarith
  have hnorm1 : ‖(1 : Point n →L[ℝ] Point n) - Lpos‖ < 1 := by
    have hone : (1 : Point n →L[ℝ] Point n) = ContinuousLinearMap.id ℝ (Point n) :=
      ContinuousLinearMap.one_def
    rw [hone, norm_sub_rev]
    exact lt_of_le_of_lt hopnorm (by linarith [hCDhalf])
  rw [hfd]
  refine ⟨?_, ?_⟩
  · have hu := isUnit_one_sub_of_norm_lt_one hnorm1
    rwa [sub_sub_cancel] at hu
  · -- ‖Ring.inverse Lpos‖ ≤ 2 via the Neumann bound with `t = 1 − Lpos`.
    set t : Point n →L[ℝ] Point n := (1 : Point n →L[ℝ] Point n) - Lpos with ht_def
    have hthalf : ‖t‖ ≤ 1 / 2 := by
      have e1 : ‖t‖ = ‖Lpos - ContinuousLinearMap.id ℝ (Point n)‖ := by
        rw [ht_def, norm_sub_rev, ContinuousLinearMap.one_def]
      rw [e1]; exact le_trans hopnorm hCDhalf
    have ht1' : ‖t‖ < 1 := lt_of_le_of_lt hthalf (by norm_num)
    have hLpos_eq : (1 : Point n →L[ℝ] Point n) - t = Lpos := by rw [ht_def]; abel
    have hbound := norm_ringInverse_one_sub_le hR1 t ht1'
    rw [hLpos_eq] at hbound
    have h2 : (1 - ‖t‖)⁻¹ ≤ 2 := by
      have hpos : (0 : ℝ) < 1 / 2 := by norm_num
      have hle : (1 : ℝ) / 2 ≤ 1 - ‖t‖ := by linarith [hthalf]
      have h3 := one_div_le_one_div_of_le hpos hle
      rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num, one_div] at h3
      exact h3
    exact le_trans hbound h2

/-! ### (P2) — uniform base-metric-inverse bound on the endpoint tube. -/

/-- **★ J4-80b (P2) — uniform base-metric-inverse bound on the flow-endpoint tube.**

    With the GENUINE global base-metric nondegeneracy `hgnd : ∀ y, IsUnit (matToCLM (g y))` (a standard
    Riemannian hypothesis, satisfiable by `g = δ`, NOT the conclusion), there is a single constant `Kb ≥ 0`
    bounding `‖Ring.inverse (matToCLM (g (uniformFlowExp q v)))‖` over all `q ∈ K` and `‖v‖ ≤ ρ_K`.

    Route: the scalar `φ y = ‖Ring.inverse (matToCLM (g y))‖` is CONTINUOUS — `y ↦ matToCLM (g y)` is
    continuous (`hg` entries), every value is a unit (`hgnd`), `Ring.inverse` is continuous at units
    (`NormedRing.inverse_continuousAt`), and the norm is continuous — so the tube-EVT bound
    (`uniformFlowExp_tube_continuous_bound`) confines it by a single `Kb`. -/
theorem uniformFlowExp_baseMetricInv_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b))) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ q ∈ K, ∀ v : Point n,
      ‖v‖ ≤ uniformFlowRadius g gi hC hK →
      ‖Ring.inverse (matToCLM (fun a b => g (uniformFlowExp g gi hC hK q v) a b))‖ ≤ Kb := by
  have hm : Continuous (fun y : Point n => matToCLM (fun a b => g y a b)) := by
    simp only [matToCLM]
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    exact ((hg a b).continuous).smul continuous_const
  have hφcont : Continuous (fun y : Point n => ‖Ring.inverse (matToCLM (fun a b => g y a b))‖) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hcU : IsUnit (matToCLM (fun a b => g y a b)) := hgnd y
    have hinvCont : ContinuousAt Ring.inverse (matToCLM (fun a b => g y a b)) := by
      rw [← hcU.unit_spec]; exact NormedRing.inverse_continuousAt hcU.unit
    have hcomp : ContinuousAt (fun z : Point n => Ring.inverse (matToCLM (fun a b => g z a b))) y :=
      ContinuousAt.comp (f := fun z : Point n => matToCLM (fun a b => g z a b))
        hinvCont hm.continuousAt
    exact hcomp.norm
  obtain ⟨G, hG0, hGb⟩ := uniformFlowExp_tube_continuous_bound g gi hC hK
    (fun y => ‖Ring.inverse (matToCLM (fun a b => g y a b))‖) hφcont
  refine ⟨G, hG0, ?_⟩
  intro q hq v hv
  have hb := hGb q hq v hv
  rwa [abs_of_nonneg (norm_nonneg _)] at hb

/-! ### (P3) — matrix/operator bridge helpers for the inverse congruence. -/

/-- `Ring.inverse` on a two-sided inverse pair: if `a*b=1` and `b*a=1` then `Ring.inverse a = b`. -/
theorem ringInverse_eq_of_mul_eq_one {R : Type*} [MonoidWithZero R] {a b : R}
    (h1 : a * b = 1) (h2 : b * a = 1) : Ring.inverse a = b := by
  have hval : a = ↑(Units.mk a b h1 h2) := rfl
  rw [hval, Ring.inverse_unit]
  rfl

/-- `Ring.inverse` of a product of units reverses: `(a*b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ`. -/
theorem ringInverse_mul_of_isUnit {R : Type*} [MonoidWithZero R] {a b : R}
    (ha : IsUnit a) (hb : IsUnit b) :
    Ring.inverse (a * b) = Ring.inverse b * Ring.inverse a := by
  obtain ⟨ua, rfl⟩ := ha
  obtain ⟨ub, rfl⟩ := hb
  rw [← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev,
    Units.val_mul]

/-- `matToCLM (1 : Matrix) = 1` (the operator `mulVec` of the identity matrix is the identity). -/
theorem matToCLM_one : matToCLM ((1 : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  funext i
  rw [matToCLM_apply, ContinuousLinearMap.one_apply]
  simp [Matrix.one_apply, Finset.sum_ite_eq]

/-- `matToCLM` is multiplicative: `matToCLM (A*B) = matToCLM A * matToCLM B` (matrix product ↦ operator
    composition), since it factors through the algebra equivalences `toLinAlgEquiv'` and `End.toCLM`. -/
theorem matToCLM_mul (A B : Matrix (Fin n) (Fin n) ℝ) :
    matToCLM ((A * B : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ)
      = matToCLM (A : Fin n → Fin n → ℝ) * matToCLM (B : Fin n → Fin n → ℝ) := by
  simp only [matToCLM_eq_algEquiv, map_mul]

/-- `matToCLM` is injective (evaluate on `Pi.single b 1` to read off entry `(i,b)`). -/
theorem matToCLM_injective : Function.Injective (matToCLM (n := n)) := by
  intro M N h
  funext i b
  have hh := congrFun (congrArg (fun T : Point n →L[ℝ] Point n => (T (Pi.single b 1) : Point n)) h) i
  simp only [matToCLM_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hh
  exact hh

/-- `‖elemCLM a b‖ ≤ 1` (a matrix-unit operator has operator norm at most `1` in the sup norm). -/
theorem norm_elemCLM_le_one (a b : Fin n) : ‖elemCLM a b‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  have hval : elemCLM a b v = v b • (Pi.single a (1 : ℝ) : Point n) := by
    funext i; rw [elemCLM_apply]; simp [Pi.smul_apply, smul_eq_mul]
  rw [hval, norm_smul, Pi.norm_single, norm_one, mul_one]
  exact norm_le_pi_norm v b

/-- Crude operator-norm bound: `‖matToCLM M‖ ≤ ∑_{a,b} |M a b|` (triangle inequality + `‖elemCLM‖ ≤ 1`). -/
theorem norm_matToCLM_le_sum (M : Fin n → Fin n → ℝ) :
    ‖matToCLM M‖ ≤ ∑ a, ∑ b, |M a b| := by
  rw [matToCLM]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  calc |M a b| * ‖elemCLM a b‖ ≤ |M a b| * 1 :=
        mul_le_mul_of_nonneg_left (norm_elemCLM_le_one a b) (abs_nonneg _)
    _ = |M a b| := mul_one _

/-! ### (P3) — the congruence inverse-norm bound (general in the Jacobian CLM). -/

/-- **★ J4-80b (P3-core) — inverse-norm bound for a congruence `Jᵀ·G·J` of operators.**

    For any Jacobian CLM `J` (a unit, `‖J⁻¹‖ ≤ cJ`) and base matrix `G` (with `matToCLM G` a unit,
    `‖(matToCLM G)⁻¹‖ ≤ cG`), the operator inverse of the congruence `matToCLM (Jᵀ·G·J)` is
    `J⁻¹·(matToCLM G)⁻¹·(matToCLM Jᵀ)⁻¹`; the transpose factor's inverse is the operator of
    `(jacMat J⁻¹)ᵀ` whose entries are `≤ ‖J⁻¹‖ ≤ cJ`, giving `‖(matToCLM Jᵀ)⁻¹‖ ≤ cJ·n²`, hence

      `‖Ring.inverse (matToCLM (Jᵀ·G·J))‖ ≤ cJ · cG · (cJ·n²)`. -/
theorem norm_ringInverse_matToCLM_congr_le
    (J : Point n →L[ℝ] Point n) (G : Matrix (Fin n) (Fin n) ℝ)
    (hJu : IsUnit J) (cJ : ℝ) (hJinv : ‖Ring.inverse J‖ ≤ cJ)
    (hGu : IsUnit (matToCLM (G : Fin n → Fin n → ℝ)))
    (cG : ℝ) (hGinv : ‖Ring.inverse (matToCLM (G : Fin n → Fin n → ℝ))‖ ≤ cG) :
    ‖Ring.inverse (matToCLM (((jacMat J)ᵀ * G * jacMat J : Matrix (Fin n) (Fin n) ℝ)
        : Fin n → Fin n → ℝ))‖ ≤ cJ * cG * (cJ * (n : ℝ) * (n : ℝ)) := by
  -- Matrix identities `jacMat J · jacMat J⁻¹ = 1` and its reverse, via `matToCLM` injectivity.
  have hJRJ : (jacMat J * jacMat (Ring.inverse J) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    apply matToCLM_injective
    rw [matToCLM_mul, matToCLM_jacMat, matToCLM_jacMat, matToCLM_one]
    exact Ring.mul_inverse_cancel J hJu
  have hRJJ : (jacMat (Ring.inverse J) * jacMat J : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    apply matToCLM_injective
    rw [matToCLM_mul, matToCLM_jacMat, matToCLM_jacMat, matToCLM_one]
    exact Ring.inverse_mul_cancel J hJu
  -- The transpose operator `matToCLM Jᵀ` is a unit with inverse `matToCLM (jacMat J⁻¹)ᵀ`.
  have hprod1 : matToCLM ((jacMat (Ring.inverse J))ᵀ : Fin n → Fin n → ℝ)
      * matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ) = 1 := by
    rw [← matToCLM_mul, ← Matrix.transpose_mul, hJRJ, Matrix.transpose_one, matToCLM_one]
  have hprod2 : matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ)
      * matToCLM ((jacMat (Ring.inverse J))ᵀ : Fin n → Fin n → ℝ) = 1 := by
    rw [← matToCLM_mul, ← Matrix.transpose_mul, hRJJ, Matrix.transpose_one, matToCLM_one]
  have hTu : IsUnit (matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ)) :=
    ⟨Units.mk _ (matToCLM ((jacMat (Ring.inverse J))ᵀ : Fin n → Fin n → ℝ)) hprod2 hprod1, rfl⟩
  have hTcinv_eq : Ring.inverse (matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ))
      = matToCLM ((jacMat (Ring.inverse J))ᵀ : Fin n → Fin n → ℝ) :=
    ringInverse_eq_of_mul_eq_one hprod2 hprod1
  -- Entrywise bound `|(jacMat J⁻¹)ᵀ a b| ≤ cJ`.
  have hentry : ∀ a b : Fin n,
      |((jacMat (Ring.inverse J))ᵀ : Matrix (Fin n) (Fin n) ℝ) a b| ≤ cJ := by
    intro a b
    rw [Matrix.transpose_apply, jacMat]
    calc |(Ring.inverse J) (Pi.single a 1) b|
        = ‖(Ring.inverse J) (Pi.single a 1) b‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(Ring.inverse J) (Pi.single a 1)‖ := norm_le_pi_norm _ b
      _ ≤ ‖Ring.inverse J‖ * ‖(Pi.single a (1 : ℝ) : Point n)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Ring.inverse J‖ * 1 := by rw [Pi.norm_single, norm_one]
      _ = ‖Ring.inverse J‖ := mul_one _
      _ ≤ cJ := hJinv
  have hTinv_bound : ‖Ring.inverse (matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ))‖
      ≤ cJ * (n : ℝ) * (n : ℝ) := by
    rw [hTcinv_eq]
    refine le_trans (norm_matToCLM_le_sum _) ?_
    calc ∑ a : Fin n, ∑ b : Fin n, |((jacMat (Ring.inverse J))ᵀ : Fin n → Fin n → ℝ) a b|
        ≤ ∑ _a : Fin n, ∑ _b : Fin n, cJ :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hentry a b
      _ = cJ * (n : ℝ) * (n : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- Decompose the congruence operator and invert the product of units.
  have hdecomp : matToCLM (((jacMat J)ᵀ * G * jacMat J : Matrix (Fin n) (Fin n) ℝ)
        : Fin n → Fin n → ℝ)
      = matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ) * matToCLM (G : Fin n → Fin n → ℝ) * J := by
    rw [matToCLM_mul, matToCLM_mul, matToCLM_jacMat]
  have hInvEq : Ring.inverse (matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ)
        * matToCLM (G : Fin n → Fin n → ℝ) * J)
      = Ring.inverse J * (Ring.inverse (matToCLM (G : Fin n → Fin n → ℝ))
          * Ring.inverse (matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ))) := by
    rw [ringInverse_mul_of_isUnit (hTu.mul hGu) hJu, ringInverse_mul_of_isUnit hTu hGu]
  rw [hdecomp, hInvEq]
  have hcJ0 : 0 ≤ cJ := le_trans (norm_nonneg _) hJinv
  have hcG0 : 0 ≤ cG := le_trans (norm_nonneg _) hGinv
  calc ‖Ring.inverse J * (Ring.inverse (matToCLM (G : Fin n → Fin n → ℝ))
          * Ring.inverse (matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ)))‖
      ≤ ‖Ring.inverse J‖ * ‖Ring.inverse (matToCLM (G : Fin n → Fin n → ℝ))
          * Ring.inverse (matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ))‖ := norm_mul_le _ _
    _ ≤ ‖Ring.inverse J‖ * (‖Ring.inverse (matToCLM (G : Fin n → Fin n → ℝ))‖
          * ‖Ring.inverse (matToCLM ((jacMat J)ᵀ : Fin n → Fin n → ℝ))‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ cJ * (cG * (cJ * (n : ℝ) * (n : ℝ))) :=
        mul_le_mul hJinv (mul_le_mul hGinv hTinv_bound (norm_nonneg _) hcG0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcJ0
    _ = cJ * cG * (cJ * (n : ℝ) * (n : ℝ)) := by ring

/-! ### (P3) — the capstone: uniform inverse-metric bound (the firewalled J4-80 statement). -/

/-- **★ J4-80b — the uniform INVERSE-metric bound for the `uniformFlowExp` pullback metric `g̃`.**

    The exact statement firewalled by J4-80 (`UniformResidualB`): from `hg` (metric regularity),
    `hC` (Christoffel `C^∞`), `IsCompact K`, and the GENUINE global base-metric nondegeneracy
    `hgnd : ∀ y, IsUnit (matToCLM (g y))`, there is ONE common radius `r₀ > 0` and ONE constant
    `Kinv = 2·Kb·(2n²)` such that for every `q ∈ K` and `‖v‖ < r₀`:
    * `g̃(v)` is nondegenerate, `IsUnit (matToCLM g̃(v))`;
    * the inverse metric is uniformly bounded, `‖Ring.inverse (matToCLM g̃(v))‖ ≤ Kinv`;
    * entrywise, `|g̃⁻¹(v) i j| ≤ Kinv` for all `i j` (with `g̃⁻¹` extracted as
      `(Ring.inverse (matToCLM g̃(v))) (Pi.single j 1) i`, matching `expPullbackMetricInv`).

    Route B: (P1) `‖J⁻¹‖ ≤ 2`, (P2) `‖(g∘F)⁻¹‖ ≤ Kb`, (P3) congruence `g̃ = Jᵀ·(g∘F)·J`.  Hypotheses ONLY
    `hg`, `hC`, `IsCompact K`, `hgnd` (all genuine; `hgnd` satisfiable by `g = δ`, NOT the conclusion).
    No `sorry`, no new axioms, no `expRho`.  NOT `a₁ = R/6`. -/
theorem uniformInverseMetric_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b))) :
    ∃ r₀ > (0 : ℝ), ∃ Kinv : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
      IsUnit (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b))
      ∧ ‖Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b))‖ ≤ Kinv
      ∧ ∀ i j : Fin n,
          |(Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)))
              (Pi.single j 1) i| ≤ Kinv := by
  obtain ⟨ρ₁, hρ₁0, hP1⟩ := uniformFlowExp_common_nondeg_radius_quant g gi hC hK
  obtain ⟨Kb, hKb0, hP2⟩ := uniformFlowExp_baseMetricInv_uniform_bound g gi hg hC hK hgnd
  refine ⟨min ρ₁ (uniformFlowRadius g gi hC hK),
    lt_min hρ₁0 (uniformFlowRadius_pos g gi hC hK),
    2 * Kb * (2 * (n : ℝ) * (n : ℝ)), ?_⟩
  intro q hq v hv
  have hvρ₁ : ‖v‖ < ρ₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hvρK : ‖v‖ ≤ uniformFlowRadius g gi hC hK :=
    le_of_lt (lt_of_lt_of_le hv (min_le_right _ _))
  obtain ⟨hJu, hJinv⟩ := hP1 q hq v hvρ₁
  have hGu : IsUnit (matToCLM (fun a b => g (uniformFlowExp g gi hC hK q v) a b)) :=
    hgnd (uniformFlowExp g gi hC hK q v)
  have hGinv : ‖Ring.inverse (matToCLM (fun a b => g (uniformFlowExp g gi hC hK q v) a b))‖ ≤ Kb :=
    hP2 q hq v hvρK
  have hgtu : IsUnit (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)) :=
    uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit g gi hC hK q v hJu hGu
  -- The congruence identity `g̃ = Jᵀ·(g∘F)·J` (entrywise, as in the nondeg hinge).
  have hcong : (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)
      = (((jacMat (fderiv ℝ (uniformFlowExp g gi hC hK q) v))ᵀ
          * Matrix.of (fun a b => g (uniformFlowExp g gi hC hK q v) a b)
          * jacMat (fderiv ℝ (uniformFlowExp g gi hC hK q) v) : Matrix (Fin n) (Fin n) ℝ)
          : Fin n → Fin n → ℝ) := by
    funext i j
    simp only [uniformFlowPullbackMetric, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      jacMat, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hnormbound :
      ‖Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b))‖
        ≤ 2 * Kb * (2 * (n : ℝ) * (n : ℝ)) := by
    have hgen := norm_ringInverse_matToCLM_congr_le
      (fderiv ℝ (uniformFlowExp g gi hC hK q) v)
      (Matrix.of (fun a b => g (uniformFlowExp g gi hC hK q v) a b))
      hJu 2 hJinv hGu Kb hGinv
    rw [hcong]
    exact hgen
  refine ⟨hgtu, hnormbound, ?_⟩
  intro i j
  calc |(Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)))
          (Pi.single j 1) i|
      = ‖(Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)))
          (Pi.single j 1) i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)))
          (Pi.single j 1)‖ := norm_le_pi_norm _ i
    _ ≤ ‖Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b))‖
          * ‖(Pi.single j (1 : ℝ) : Point n)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b))‖ * 1 := by
          rw [Pi.norm_single, norm_one]
    _ = ‖Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b))‖ :=
          mul_one _
    _ ≤ 2 * Kb * (2 * (n : ℝ) * (n : ℝ)) := hnormbound

end QIQTH.ExpMap
