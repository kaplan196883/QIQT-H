/-
  UniformFlowNondegClose — J4-56 (K3): CLOSING the compact-uniform exp-nondegeneracy gate (J) for the
  UNIFORM-flow exp endpoint `uniformFlowExp`, with the GENUINE uniform radius (NO opaque `expRho`).

  ## Context

  * K1 (`UniformFlowNondeg`) built `uniformFlowExp g gi hC hK q : Point n → Point n`, the position
    endpoint of the compact-uniform confined geodesic tube through `(q, w)`, with a single uniform
    confinement radius `ρ_K = uniformFlowRadius` and constant `C₀ = uniformFlowConst`.
  * K2 (`UniformFlowFDeriv`, `uniformFlowExp_hasFDerivAt`) proved Fréchet-differentiability of
    `uniformFlowExp q` in `w`, with the derivative equal to the velocity Jacobi endpoint operator of
    the base tube — hypotheses ONLY `hC` + `IsCompact K`, no `expRho`.

  ## What lands here (K3 — DERIVED; no `sorry`, no hyp = conclusion, no smuggled `IsUnit`, no `expRho`)

  `uniformFlowExp_common_nondeg_radius` — **(J)-for-F.**
    `∃ ρ₀>0, ∀ q∈K, ∀ v, ‖v‖<ρ₀ → IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v)`,
  with hypotheses ONLY `hC` (Christoffel `C^∞`) + `IsCompact K`.  NO `expRho`, NO carried `IsUnit`/
  `HasFDerivAt`.

  ## Proof route (GPT-5.5-sketched; fully discharged)

  The endpoint operator is `L_v : δ ↦ (V^v_δ 1).1`, where `V^v_δ` solves the linear Jacobi ODE
  `V' = DF(tube^v τ)·V`, `V(0)=(0,δ)`, along the tube through `(q,v)` (`F = geodesicField`).

  * **L₀ = id (zero-velocity Jacobi is the shear).**  The FLAT Jacobi field `Jflat_δ τ = (τ·δ, δ)`
    solves `V' = DF(q,0)·V` with the SAME IC, because `DF(q,0)(ξ,η) = (η, -jacobiOperator g gi q 0 ξ η)`
    and `jacobiOperator g gi q 0 ξ η = 0` (every term of the Jacobi operator carries a factor of the
    zero velocity).  Its endpoint position is `(Jflat_δ 1).1 = δ`.

  * **‖L_v − id‖ ≤ C_D·‖v‖ uniformly over `q∈K` (Grönwall).**  Comparing `V^v_δ` (base tube through
    `(q,v)`, coefficient `DF(tube^v τ)`) with `Jflat_δ` (coefficient the CONSTANT `DF(q,0)`) via the
    two-base linear-ODE comparison Grönwall `linODE_twopoint_diff_bound`: the coefficient gap is
    `‖DF(tube^v τ) − DF(q,0)‖ ≤ M₂·‖tube^v τ − (q,0)‖ ≤ M₂·C₀·‖v‖` (fderiv mean-value inequality on a
    SINGLE compact convex phase set `S★` covering all tubes, times the uniform confinement), and
    `‖Jflat_δ τ‖ ≤ ‖δ‖`, giving `‖(V^v_δ 1).1 − δ‖ ≤ (M₂·C₀·e^{K_f})·‖v‖·‖δ‖`, i.e.
    `‖L_v − id‖ ≤ C_D·‖v‖` with the UNIFORM `C_D = M₂·C₀·e^{K_f}` (constants over `S★`, uniform in `q`).

  * **Neumann ⟹ IsUnit.**  For `‖v‖ < min(ρ_K, 1/(2(C_D+1)))`, `‖1 − L_v‖ = ‖L_v − id‖ < 1`, so
    `L_v = 1 − (1 − L_v)` is a unit (`isUnit_one_sub_of_norm_lt_one`), and
    `fderiv (uniformFlowExp q) v = L_v` (`HasFDerivAt.fderiv`).

  The whole endpoint-operator `L_v` and its differentiability are RE-CONSTRUCTED here (via the σ-windowed
  velocity-slot capstone `flowVelocity_endpoint_hasFDerivAt_window_exists`) so the operator is EXPLICIT
  (`L_v δ = (V^v_δ 1).1`) — a prerequisite for the near-identity bound, which K2's existential form does
  not expose.  This is exactly K2's construction plus the Grönwall/Neumann tail; no new geometric input.

  DERIVED vs carried: everything is derived from `hC` + `IsCompact K`.  No physical/geometric input is
  carried beyond those two.
-/
import QIQTH.UniformFlowFDeriv
import QIQTH.UniformFlowNondeg
import QIQTH.UniformFlowTransfer
import QIQTH.SecondVariationLipschitz
import QIQTH.GenericJacobiExists
import QIQTH.JacobiEquation
import QIQTH.BasepointJetModulus
import QIQTH.BoundedGeometry
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **K3 — the COMMON compact-uniform nondegeneracy radius for the uniform-flow exp endpoint.**

    There is a SINGLE radius `ρ₀ > 0` such that for every `q ∈ K` and every velocity `v` with
    `‖v‖ < ρ₀`, the uniform-flow exp Jacobian `fderiv ℝ (uniformFlowExp g gi hC hK q) v` is invertible
    (`IsUnit`).  This is the compact-uniform (J) gate for `F = uniformFlowExp`, with hypotheses ONLY
    `hC` (Christoffel `C^∞`) + `IsCompact K` — NO opaque per-`q` injectivity radius `expRho`, NO carried
    `IsUnit`/`HasFDerivAt`. -/
theorem uniformFlowExp_common_nondeg_radius (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v) := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- Vacuous over an empty base set.
    refine ⟨1, one_pos, ?_⟩
    intro q hq
    simp only [hKe, Set.mem_empty_iff_false] at hq
  -- Uniform radius / constant.
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- Enclose `K` in a ball to bound `‖(q, 0)‖` uniformly.
  obtain ⟨p₀, hp₀⟩ := hKne
  obtain ⟨R, hRsub⟩ := hK.isBounded.subset_closedBall p₀
  have hR0 : 0 ≤ R := by
    have h := hRsub hp₀; rw [Metric.mem_closedBall, dist_self] at h; exact h
  set Rbase : ℝ := R + ‖p₀‖ with hRbasedef
  have hRbase0 : 0 ≤ Rbase := by rw [hRbasedef]; positivity
  set RG : ℝ := Rbase + C₀ * ρ with hRGdef
  have hRG0 : 0 ≤ RG := by rw [hRGdef]; positivity
  -- A SINGLE compact convex phase set covering all base tubes for `q ∈ K`, `‖w‖ ≤ ρ`.
  set S : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) RG with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  have h0S : (0 : Point n × Point n) ∈ S := by rw [hSdef]; exact Metric.mem_closedBall_self hRG0
  -- Global smoothness of the field Jacobian.
  have hdiffglob : Differentiable ℝ (fderiv ℝ (geodesicField g gi)) :=
    ((contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top).differentiable (by simp)
  -- Uniform C² field bound over `S`.
  obtain ⟨M₂, hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
      (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
        (by simp)).norm
    obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn ⟨(0 : Point n × Point n), h0S⟩ hcontr.continuousOn
    exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
      norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x),
      fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  -- Uniform Jacobi-coefficient bound and uniform field-Lipschitz constant over `S`.
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  obtain ⟨K₀, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) hSconv hScompact
  -- The UNIFORM near-identity constant.
  set C_D : ℝ := M₂ * C₀ * Real.exp Kf with hCDdef
  have hCD0 : 0 ≤ C_D := by
    rw [hCDdef]; exact mul_nonneg (mul_nonneg hM₂0 hC₀nn) (Real.exp_pos _).le
  have hCD1 : (0 : ℝ) < 2 * (C_D + 1) := by linarith [hCD0]
  -- The common nondegeneracy radius.
  set ρ₀ : ℝ := min ρ (1 / (2 * (C_D + 1))) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := lt_min hρ0 (div_pos one_pos hCD1)
  refine ⟨ρ₀, hρ₀pos, ?_⟩
  intro q hq v hv
  -- `v` inside both windows.
  have hvr : ‖v‖ < ρ := lt_of_lt_of_le hv (by rw [hρ₀def]; exact min_le_left _ _)
  have hvρ : ‖v‖ ≤ ρ := hvr.le
  have hvle : ‖v‖ ≤ 1 / (2 * (C_D + 1)) :=
    le_of_lt (lt_of_lt_of_le hv (by rw [hρ₀def]; exact min_le_right _ _))
  -- `‖(q, 0)‖ ≤ Rbase`, and `(q, 0) ∈ S`.
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
  -- The window `σ = ρ − ‖v‖ > 0` and perturbed uniform tubes.
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  set Wf : Point n → ℝ → Point n × Point n :=
    fun δ => uniformFlowTube g gi hC hK q (v + δ) with hWfdef
  have hle : ∀ δ : Point n, ‖δ‖ ≤ σ → ‖v + δ‖ ≤ ρ := by
    intro δ hδ
    refine (norm_add_le v δ).trans ?_
    rw [hσdef] at hδ; linarith
  -- perturbed-tube data.
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
  -- base-tube continuity for Jacobi existence.
  have hbasecont : ContinuousOn (Wf 0) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + 0) (hle 0 h0σ) τ hτoo).continuousAt).continuousWithinAt
  -- the base-tube velocity Jacobi solutions.
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
  -- the windowed first-jet capstone: the EXPLICIT endpoint Jacobi operator.
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂ := hM₂
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Wf 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKf (Wf 0 τ) (hmem 0 h0σ τ hτ)
  obtain ⟨L, hLeq, hFD⟩ :=
    flowVelocity_endpoint_hasFDerivAt_window_exists g gi hC hKf0 hσ ht1 hSconv hbound2 hLip
      hWode hVode hV0 hIC hKb hmem
  -- project onto the position component and recentre by the translation `δ ↦ v + δ`.
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
  -- `HasFDerivAt (uniformFlowExp q) Lpos v`; hence `fderiv = Lpos`.
  have hFDexp : HasFDerivAt (uniformFlowExp g gi hC hK q) Lpos v := hcomp
  -- `jacobiOperator` vanishes at zero velocity.
  have hjac0 : ∀ ξ η : Point n, jacobiOperator g gi q (0 : Point n) ξ η = 0 := by
    intro ξ η; funext i; simp [jacobiOperator]
  -- the UNIFORM near-identity bound `‖L_v δ − δ‖ ≤ (C_D·‖v‖)·‖δ‖`.
  have hnearId : ∀ δ : Point n, ‖Lpos δ - δ‖ ≤ (C_D * ‖v‖) * ‖δ‖ := by
    intro δ
    set Jf : ℝ → Point n × Point n := fun τ => ((τ • δ, δ) : Point n × Point n) with hJf
    -- the flat Jacobi field solves `V' = DF(q,0)·V`, `V(0)=(0,δ)`.
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
  -- operator-norm near-identity bound.
  have hopnorm : ‖Lpos - ContinuousLinearMap.id ℝ (Point n)‖ ≤ C_D * ‖v‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hCD0 (norm_nonneg v)) (fun δ => ?_)
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    exact hnearId δ
  -- `fderiv = Lpos`, then Neumann series.
  have hfd : fderiv ℝ (uniformFlowExp g gi hC hK q) v = Lpos := hFDexp.fderiv
  rw [hfd]
  have hCDv : C_D * ‖v‖ < 1 := by
    have h1 : C_D * ‖v‖ ≤ C_D * (1 / (2 * (C_D + 1))) := mul_le_mul_of_nonneg_left hvle hCD0
    have h2 : C_D * (1 / (2 * (C_D + 1))) < 1 := by
      rw [mul_one_div, div_lt_one hCD1]; nlinarith [hCD0]
    exact lt_of_le_of_lt h1 h2
  have hnorm1 : ‖(1 : Point n →L[ℝ] Point n) - Lpos‖ < 1 := by
    have hone : (1 : Point n →L[ℝ] Point n) = ContinuousLinearMap.id ℝ (Point n) :=
      ContinuousLinearMap.one_def
    rw [hone, norm_sub_rev]
    exact lt_of_le_of_lt hopnorm hCDv
  have hu := isUnit_one_sub_of_norm_lt_one hnorm1
  rwa [sub_sub_cancel] at hu

end QIQTH.ExpMap
