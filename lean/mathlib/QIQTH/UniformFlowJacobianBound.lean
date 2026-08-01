/-
  UniformFlowJacobianBound — J4-63 (Brick-A β): a UNIFORM operator-norm bound on the differential of
  the UNIFORM-flow exp endpoint `uniformFlowExp`, over the compact base set `K`, carried with the
  GENUINE uniform radius `ρ_K` (`uniformFlowRadius`) — NO opaque per-`q` `expRho`.

  ## Context

  * K1 (`UniformFlowNondeg`) built `uniformFlowExp g gi hC hK q : Point n → Point n`, the position
    endpoint of the compact-uniform confined geodesic tube through `(q, w)`, with a single uniform
    confinement radius `ρ_K = uniformFlowRadius` and constant `C₀ = uniformFlowConst`.
  * K2 (`UniformFlowFDeriv`, `uniformFlowExp_hasFDerivAt`) proved Fréchet-differentiability of
    `uniformFlowExp q` in `w`, with the derivative equal to the velocity Jacobi endpoint operator of
    the base tube.
  * K3 (`UniformFlowNondegClose`, `uniformFlowExp_common_nondeg_radius`) re-constructed that endpoint
    operator `L_v δ = (V^v_δ 1).1` EXPLICITLY (via the σ-windowed velocity-slot capstone) and derived
    the near-identity / Neumann bound making it a unit.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled bound, no `expRho`)

  `uniformFlowExp_fderiv_uniform_bound` — **the uniform Jacobian bound.**
    `∃ Mj, ∀ q∈K, ∀ v, ‖v‖ < ρ_K → ‖fderiv ℝ (uniformFlowExp g gi hC hK q) v‖ ≤ Mj`,
  with hypotheses ONLY `hC` (Christoffel `C^∞`) + `IsCompact K`.  The constant is `Mj = e^{K_f}`, GENUINELY
  q-independent (`K_f` is the field-Jacobian sup over the SINGLE compact convex phase set `S★` covering all
  base tubes for `q∈K`, `‖w‖≤ρ_K`).  NO `expRho`.

  `uniformFlowExp_fderiv_uniform_bound_closedBall` — the closed-ball packaging on `‖v‖ ≤ ρ_K/2`.

  ## Proof route (Grönwall on the endpoint Jacobi operator; opNorm)

  Re-construct the endpoint operator EXACTLY as in K3 (this is K2's construction plus the tail — the
  σ-windowed velocity-slot capstone `flowVelocity_endpoint_hasFDerivAt_window_exists` supplies the CLM
  `L δ = V δ 1` and `HasFDerivAt (uniformFlowExp q) Lpos v` where `Lpos δ = (V δ 1).1`), so that
  `fderiv ℝ (uniformFlowExp q) v = Lpos` (`HasFDerivAt.fderiv`).  Then a Grönwall norm bound on the
  Jacobi factor — `‖V δ τ‖ ≤ gronwallBound ‖(0,δ)‖ K_f 0 τ`
  (`norm_le_gronwallBound_of_norm_deriv_right_le`, `ε = 0`, coefficient `‖DF(tube τ)‖ ≤ K_f`), evaluated at
  `τ = 1` — gives `‖V δ 1‖ ≤ ‖δ‖·e^{K_f}`, hence `‖Lpos δ‖ = ‖(V δ 1).1‖ ≤ ‖V δ 1‖ ≤ ‖δ‖·e^{K_f}`, hence
  `‖Lpos‖ ≤ e^{K_f}` (`ContinuousLinearMap.opNorm_le_bound`).  This is exactly J4-46's Jacobi Grönwall
  (`DoubledFamilyConfine`) fed into J4-56's explicit-operator reconstruction (`UniformFlowNondegClose`),
  with the near-identity/Neumann tail replaced by the raw operator-norm bound.  NO joint continuity in
  `(q,v)` is needed — the bound is q-uniform because `S★`, `K_f` are.

  DERIVED vs carried: everything is derived from `hC` + `IsCompact K`.  No physical/geometric input carried.
-/
import QIQTH.UniformFlowFDeriv
import QIQTH.UniformFlowNondegClose
import QIQTH.UniformFlowNondeg
import QIQTH.GenericJacobiExists
import QIQTH.BoundedGeometry
import QIQTH.UniformRadiusCert
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **J4-63 — the UNIFORM Jacobian (differential-norm) bound for the uniform-flow exp endpoint.**

    There is a SINGLE constant `Mj` such that for every `q ∈ K` and every velocity `v` with
    `‖v‖ < ρ_K` (`ρ_K = uniformFlowRadius`), the operator norm of the uniform-flow exp Jacobian
    `fderiv ℝ (uniformFlowExp g gi hC hK q) v` is `≤ Mj`.  Hypotheses ONLY `hC` (Christoffel `C^∞`) +
    `IsCompact K`.  The witness is `Mj = e^{K_f}` with `K_f` the field-Jacobian sup over the single
    compact convex phase set covering all base tubes — GENUINELY q-independent.  NO `expRho`. -/
theorem uniformFlowExp_fderiv_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ Mj : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < uniformFlowRadius g gi hC hK →
      ‖fderiv ℝ (uniformFlowExp g gi hC hK q) v‖ ≤ Mj := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- Vacuous over an empty base set.
    refine ⟨0, ?_⟩
    intro q hq v hv
    rw [hKe] at hq; exact absurd hq (Set.notMem_empty q)
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
  -- The uniform Jacobian bound witness.
  refine ⟨Real.exp Kf, ?_⟩
  intro q hq v hv
  have hvr : ‖v‖ < ρ := hv
  have hvρ : ‖v‖ ≤ ρ := hvr.le
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
  -- the base-tube velocity Jacobi solutions (globally defined in the seed).
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
  have hFDexp : HasFDerivAt (uniformFlowExp g gi hC hK q) Lpos v := hcomp
  -- `fderiv = Lpos`.
  have hfd : fderiv ℝ (uniformFlowExp g gi hC hK q) v = Lpos := hFDexp.fderiv
  rw [hfd]
  -- ===== Grönwall on the endpoint Jacobi operator: `‖V δ 1‖ ≤ ‖δ‖·e^{K_f}`. =====
  have hVendpoint : ∀ δ : Point n, ‖V δ 1‖ ≤ ‖δ‖ * Real.exp Kf := by
    intro δ
    have hVcont : ContinuousOn (V δ) (Set.Icc (0 : ℝ) 1) :=
      fun τ hτ => ((hVode δ τ hτ).continuousAt).continuousWithinAt
    have hnorm0δ : ‖((0 : Point n), δ)‖ = ‖δ‖ := by rw [Prod.norm_def]; simp
    have hVbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖V δ x‖ ≤ gronwallBound ‖((0 : Point n), δ)‖ Kf 0 (x - 0) :=
      norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖((0 : Point n), δ)‖)
        (K := Kf) (ε := 0) (a := 0) (b := 1) hVcont
        (fun x hx => (hVode δ x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
        (le_of_eq (by rw [hV0 δ]))
        (fun x hx => by
          have hle := (fderiv ℝ (geodesicField g gi) (Wf 0 x)).le_opNorm (V δ x)
          calc ‖fderiv ℝ (geodesicField g gi) (Wf 0 x) (V δ x)‖
              ≤ ‖fderiv ℝ (geodesicField g gi) (Wf 0 x)‖ * ‖V δ x‖ := hle
            _ ≤ Kf * ‖V δ x‖ :=
                mul_le_mul_of_nonneg_right (hKb x (Set.Ico_subset_Icc_self hx)) (norm_nonneg _)
            _ = Kf * ‖V δ x‖ + 0 := by ring)
    have h1 := hVbound 1 ht1
    rw [sub_zero, gronwallBound_ε0, hnorm0δ] at h1
    refine h1.trans (le_of_eq ?_)
    rw [mul_one]
  -- `‖Lpos δ‖ = ‖(V δ 1).1‖ ≤ ‖V δ 1‖ ≤ ‖δ‖·e^{K_f}`, hence `‖Lpos‖ ≤ e^{K_f}`.
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (fun δ => ?_)
  calc ‖Lpos δ‖
      = ‖(V δ 1).1‖ := by rw [hLpos_apply δ]
    _ ≤ ‖V δ 1‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ ‖δ‖ * Real.exp Kf := hVendpoint δ
    _ = Real.exp Kf * ‖δ‖ := by ring

/-- **J4-63 (closed-ball packaging).**  Same uniform Jacobian bound on the closed velocity ball
    `‖v‖ ≤ ρ_K/2` (a fixed uniform radius `< ρ_K`), the form directly consumed by the pullback-metric
    entry bounds. -/
theorem uniformFlowExp_fderiv_uniform_bound_closedBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ Mj : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ r₀ →
      ‖fderiv ℝ (uniformFlowExp g gi hC hK q) v‖ ≤ Mj := by
  obtain ⟨Mj, hMj⟩ := uniformFlowExp_fderiv_uniform_bound g gi hC hK
  have hρ0 : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨uniformFlowRadius g gi hC hK / 2, by positivity, Mj, ?_⟩
  intro q hq v hv
  refine hMj q hq v ?_
  calc ‖v‖ ≤ uniformFlowRadius g gi hC hK / 2 := hv
    _ < uniformFlowRadius g gi hC hK := by linarith

end QIQTH.ExpMap
