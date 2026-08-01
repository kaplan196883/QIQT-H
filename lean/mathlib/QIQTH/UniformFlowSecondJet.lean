/-
  UniformFlowSecondJet — J4-65 (Brick-A β): the SECOND-order velocity regularity of the UNIFORM-flow
  exp endpoint `uniformFlowExp`, in the form of the intrinsic SECOND-VARIATION field along the uniform
  tube together with a UNIFORM (over `q ∈ K`, `‖v‖ ≤ r₀`) Grönwall norm bound, quadratic in the
  variation direction — the opening rung of the sub-tower toward `g̃ ∈ C²` (`uniformFlowExp ∈ C³`).

  ## Context

  * K1 (`UniformFlowNondeg`) built the uniform confined geodesic tube `uniformFlowTube g gi hC hK q v`
    with a single uniform confinement radius `ρ_K = uniformFlowRadius` and constant
    `C₀ = uniformFlowConst`; its endpoint position is `uniformFlowExp g gi hC hK q`.
  * K2 (`UniformFlowFDeriv`, `uniformFlowExp_hasFDerivAt`) proved FIRST-order Fréchet differentiability
    in the IC `w`, the derivative being the velocity Jacobi endpoint operator (a σ-windowed two-sided
    little-o argument).
  * J4-63 (`UniformFlowJacobianBound`, `uniformFlowExp_fderiv_uniform_bound`) gave the UNIFORM
    operator-norm bound `‖fderiv (uniformFlowExp q) v‖ ≤ Mj = e^{K_f}` via a HOMOGENEOUS Grönwall on the
    endpoint velocity Jacobi field.

  ## What lands here (R1; DERIVED; no `sorry`, no hyp = conclusion, no smuggled 2nd-order conclusion,
  no `expRho`)

  `uniformFlowTube_secondVariation_uniform_bound` — **R1.**  There is one uniform radius `r₀ = ρ_K/2 > 0`
  and one uniform constant `M₂j ≥ 0` such that for every `q ∈ K`, every `v` with `‖v‖ ≤ r₀`, and every
  variation direction `a`, along the base tube `Y = uniformFlowTube g gi hC hK q v` there exist:
    * the FIRST-variation (velocity Jacobi) field `V` with `V 0 = (0, a)` solving the linearized geodesic
      ODE `V' = DF(Y τ)·V`;
    * the intrinsic SECOND-variation field `Zf` with `Zf 0 = 0` solving the INHOMOGENEOUS second-variation
      ODE `Zf' = DF(Y τ)·Zf + D²F(Y τ)(V,V)` — the source being quadratic in the first variation;
  and the UNIFORM Grönwall norm bound `‖Zf τ‖ ≤ M₂j · ‖a‖²` for all `τ ∈ [0,1]`.

  The constants `M₂j` (and `r₀`) are chosen BEFORE introducing `q, v, a`: `K_f` (field-Jacobian sup) and
  `M₂` (second-field sup) are taken over the SINGLE compact convex phase set `S` covering all base tubes
  for `q ∈ K`, `‖w‖ ≤ ρ_K`, so the bound is genuinely `q`-uniform.  NO `expRho`.

  ## Proof route (within-derivative Grönwall on `[0,1]` — no padding wall)

  The Grönwall NORM bound only ever consumes RIGHT (within-`Ici`) derivatives on `Ico 0 1`
  (`norm_le_gronwallBound_of_norm_deriv_right_le`), so the whole construction can be carried on the
  CLOSED `[0,1]` with `HasDerivWithinAt`, never touching a padded interval (the uniform tube is
  continuous only on the OPEN `(-2,2)`, so the two-sided `[-1,2]` engines of `SecondVariationSupply` do
  NOT apply to it).  We therefore add a `[0,1]`-only inhomogeneous within-derivative ODE solver
  (`linODE_inhomog_within_exists_on_Icc`, via the classical state-augmentation trick on `E × ℝ`) and run:
    * the base tube confined in `S` (K1 confinement), continuous on `[0,1]`;
    * `V` from the homogeneous `[0,1]` solver `geodesicJacobi_exists_on_Icc`, with
      `‖V τ‖ ≤ ‖a‖·e^{K_f}` (homogeneous Grönwall, `ε = 0`);
    * `Zf` from `linODE_inhomog_within_exists_on_Icc`, source `D²F(Y)(V,V)` with `‖·‖ ≤ M₂·(‖a‖ e^{K_f})²`,
      giving `‖Zf τ‖ ≤ gronwallBound 0 K_f (M₂(‖a‖e^{K_f})²) 1 = ‖a‖²·M₂j` (`gronwallBound` monotone in
      the endpoint and linear in the source slot at seed `0`).

  ## HONEST CHECKPOINT (binding) — what remains FIREWALLED

  This lands R1 (the intrinsic second-variation field along the uniform tube + its uniform, quadratic
  Grönwall norm bound), all DERIVED from `hC` + `IsCompact K`.  It does NOT land:
    * R2 — the operator-valued `HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp q) w) B₂ v` (the jet map's
      Fréchet derivative / the Hessian's EXISTENCE).  `hid_of_doubled_data` (`JacobiOperatorFDeriv`)
      identifies its VALUE `= (Zf 1).1` but PRESUPPOSES that differentiability (`hdiff`); producing
      `hdiff` for `uniformFlowExp` needs the two-sided second-order little-o argument (the padded-tube
      doubled-field flow), one order above K2.  CARRIED.
    * R3 — the uniform bound `‖fderiv (fun w => fderiv (uniformFlowExp q) w) v‖ ≤ M₂j` on the Hessian
      operator norm.  Given R2 (existence + the `(Zf 1).1` identification) it is R1's bound read off at
      `τ = 1`; without R2 the object does not yet exist.  CARRIED.

  It does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.UniformFlowFDeriv
import QIQTH.UniformFlowJacobianBound
import QIQTH.SecondVariationSupply
import QIQTH.SecondVariationLipschitz
import QIQTH.UniformFlowNondeg
import QIQTH.BoundedGeometry
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000

/-! ### Generic within-derivative helpers -/

section WithinHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **`Icc`-within right-derivative on `[0,1]` ⟹ `Ici`-within right-derivative.**  For `x ∈ [0,1)`,
    the closed-interval within derivative refines to the right-ray within derivative that
    `norm_le_gronwallBound_of_norm_deriv_right_le` and `constant_of_has_deriv_right_zero` consume.
    (`Icc 0 1 ∈ 𝓝[Ici x] x` since `Ici x ∩ Iio 1 = Ico x 1 ⊆ Icc 0 1` for `0 ≤ x`.) -/
theorem hasDerivWithinAt_Ici_of_Icc01 {f : ℝ → E} {f' : E} {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (h : HasDerivWithinAt f f' (Set.Icc (0 : ℝ) 1) x) :
    HasDerivWithinAt f f' (Set.Ici x) x := by
  refine h.mono_of_mem_nhdsWithin ?_
  have h1 : Set.Iio (1 : ℝ) ∈ 𝓝 x := isOpen_Iio.mem_nhds hx.2
  have hsub : Set.Ici x ∩ Set.Iio 1 ⊆ Set.Icc (0 : ℝ) 1 :=
    fun y hy => ⟨le_trans hx.1 hy.1, le_of_lt hy.2⟩
  exact Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici x) h1) hsub

end WithinHelpers

/-! ### `gronwallBound` at seed `0` is linear in the source slot -/

/-- At seed `δ = 0`, `gronwallBound` is homogeneous (linear) in the source `ε`-slot:
    `gronwallBound 0 K (c·ε) x = c · gronwallBound 0 K ε x`. -/
theorem gronwallBound_zero_mul_ε (K x c ε : ℝ) :
    gronwallBound 0 K (c * ε) x = c * gronwallBound 0 K ε x := by
  rcases eq_or_ne K 0 with hK | hK
  · subst hK; simp only [gronwallBound_K0]; ring
  · simp only [gronwallBound_of_K_ne_0 hK]; ring

/-! ### Inhomogeneous linear-ODE existence on `[0,1]` (within derivatives) -/

section InhomogWithin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Inhomogeneous linear-ODE existence on `[0,1]`, within derivatives.**  For a continuous
    time-dependent bounded operator `A` and continuous source `src` on `[0,1]`, and a seed `w₀`, there
    is `J : ℝ → E` with `J 0 = w₀` solving `J' τ = A τ (J τ) + src τ` on `[0,1]` with genuine
    `HasDerivWithinAt` (right derivatives).  This is the `[0,1]` within-derivative analogue of
    `linODE_inhomog_exists_on_Icc` (which needs the two-sided padded `[-1,2]`, unavailable for the
    uniform tube).  DERIVED by the classical state-augmentation trick on `E × ℝ`: solve the homogeneous
    augmented system `Ã τ (X,u) = (A τ X + u • src τ, 0)` (continuous linear) via the repo's `[0,1]`
    within solver `linODE_exists_on_Icc`; the `ℝ`-tracker `u` has zero right derivative, hence `u ≡ 1`
    (`constant_of_has_deriv_right_zero`), recovering the affine source. -/
theorem linODE_inhomog_within_exists_on_Icc (A : ℝ → (E →L[ℝ] E)) (src : ℝ → E)
    (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1))
    (hsrc : ContinuousOn src (Set.Icc (0 : ℝ) 1)) (w₀ : E) :
    ∃ J : ℝ → E, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt J (A τ (J τ) + src τ) (Set.Icc (0 : ℝ) 1) τ := by
  classical
  set Ã : ℝ → ((E × ℝ) →L[ℝ] (E × ℝ)) := fun τ =>
    (ContinuousLinearMap.inl ℝ E ℝ).comp
      ((A τ).comp (ContinuousLinearMap.fst ℝ E ℝ)
        + (ContinuousLinearMap.snd ℝ E ℝ).smulRight (src τ)) with hÃdef
  have hApp : ∀ (τ : ℝ) (z : E × ℝ), Ã τ z = (A τ z.1 + z.2 • src τ, (0 : ℝ)) := by
    intro τ z
    simp [hÃdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply]
  have hÃcont : ContinuousOn Ã (Set.Icc (0 : ℝ) 1) := by
    have h1 : ContinuousOn (fun τ => (A τ).comp (ContinuousLinearMap.fst ℝ E ℝ))
        (Set.Icc (0 : ℝ) 1) := hA.clm_comp continuousOn_const
    have h2 : ContinuousOn
        (fun τ => (ContinuousLinearMap.snd ℝ E ℝ).smulRight (src τ)) (Set.Icc (0 : ℝ) 1) := by
      have := (continuousOn_const (c :=
        ContinuousLinearMap.smulRightL ℝ (E × ℝ) E (ContinuousLinearMap.snd ℝ E ℝ))).clm_apply hsrc
      simpa [ContinuousLinearMap.smulRightL_apply_apply] using this
    exact continuousOn_const.clm_comp (h1.add h2)
  obtain ⟨J, hJ0, hJd⟩ := linODE_exists_on_Icc Ã hÃcont (w₀, (1 : ℝ))
  -- the `ℝ`-tracker `u := (J ·).2` has zero right derivative on `[0,1]`.
  have hu0 : (J 0).2 = 1 := by rw [hJ0]
  have hud : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => (J t).2) 0 (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have h := (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivWithinAt τ (hJd τ hτ)
    have hz : (Ã τ (J τ)).2 = (0 : ℝ) := by rw [hApp]
    simpa [ContinuousLinearMap.coe_snd', hz] using h
  have hucont : ContinuousOn (fun t => (J t).2) (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hud τ hτ).continuousWithinAt
  have huconst : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (J τ).2 = 1 := by
    intro τ hτ
    have hc := constant_of_has_deriv_right_zero hucont
      (fun x hx => hasDerivWithinAt_Ici_of_Icc01 hx (hud x (Set.Ico_subset_Icc_self hx))) τ hτ
    rw [hc]; exact hu0
  refine ⟨fun t => (J t).1, by show (J 0).1 = w₀; rw [hJ0], fun τ hτ => ?_⟩
  have h := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivWithinAt τ (hJd τ hτ)
  have hval : (Ã τ (J τ)).1 = A τ (J τ).1 + src τ := by
    rw [hApp, huconst τ hτ, one_smul]
  simpa [ContinuousLinearMap.coe_fst', hval] using h

end InhomogWithin

/-! ### R1 — the intrinsic second-variation field of the uniform flow, with a uniform quadratic bound -/

variable {n : ℕ}

/-- **R1 (J4-65) — the intrinsic SECOND-variation field of the uniform-flow tube, with a UNIFORM,
    quadratic-in-direction Grönwall norm bound.**

    There is one uniform velocity radius `r₀ = ρ_K/2 > 0` and one uniform constant `M₂j ≥ 0` such that
    for every `q ∈ K`, every `v` with `‖v‖ ≤ r₀`, and every variation direction `a`, along the base tube
    `Y = uniformFlowTube g gi hC hK q v` there exist a first-variation (velocity Jacobi) field `V`
    (`V 0 = (0,a)`, solving `V' = DF(Y)·V`) and the second-variation field `Zf` (`Zf 0 = 0`, solving the
    inhomogeneous ODE `Zf' = DF(Y)·Zf + D²F(Y)(V,V)`) with
        `∀ τ ∈ [0,1], ‖Zf τ‖ ≤ M₂j · ‖a‖²`.

    Hypotheses ONLY `hC` (Christoffel `C^∞`) + `IsCompact K`.  The constants are `q`-independent (sups
    over the SINGLE compact convex phase set covering all base tubes).  NO `expRho`, NO carried
    second-order conclusion.  See the module firewall for R2/R3. -/
theorem uniformFlowTube_secondVariation_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ M₂j : ℝ, 0 ≤ M₂j ∧
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ r₀ → ∀ a : Point n,
        ∃ V Zf : ℝ → Point n × Point n,
          V 0 = ((0 : Point n), a) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivWithinAt V
              (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (V τ))
              (Set.Icc (0 : ℝ) 1) τ) ∧
          Zf 0 = 0 ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivWithinAt Zf
              (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (Zf τ)
                + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q v τ)
                    (V τ) (V τ))
              (Set.Icc (0 : ℝ) 1) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Zf τ‖ ≤ M₂j * ‖a‖ ^ 2) := by
  classical
  -- Uniform radius / constant.
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- Field smoothness.
  have hgf : ContDiff ℝ (⊤ : WithTop ℕ∞) (geodesicField g gi) := contDiff_geodesicField g gi hC
  have hDfcont : Continuous (fderiv ℝ (geodesicField g gi)) := hgf.continuous_fderiv (by simp)
  have hD2f : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ (geodesicField g gi))) :=
    (hgf.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- Vacuous over an empty base set.
    refine ⟨ρ / 2, by positivity, 0, le_refl 0, ?_⟩
    intro q hq v hv a
    rw [hKe] at hq; exact absurd hq (Set.notMem_empty q)
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
  -- Uniform field-Jacobian bound over `S`.
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  -- The uniform second-variation constant, chosen BEFORE `intro q v a`.
  set C₂ : ℝ := M₂ * (Real.exp Kf) ^ 2 with hC₂def
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂def]; positivity
  set M₂j : ℝ := gronwallBound 0 Kf C₂ 1 with hM₂jdef
  have hM₂j0 : 0 ≤ M₂j := by
    have hmono := gronwallBound_mono (δ := 0) (K := Kf) (ε := C₂) (le_refl 0) hC₂0 hKf0
      (show (0 : ℝ) ≤ 1 by norm_num)
    rwa [gronwallBound_x0] at hmono
  refine ⟨ρ / 2, by positivity, M₂j, hM₂j0, ?_⟩
  intro q hq v hv a
  have hvρ : ‖v‖ ≤ ρ := le_trans hv (by linarith)
  -- Base tube through `(q, v)`.
  set Y : ℝ → Point n × Point n := uniformFlowTube g gi hC hK q v with hYdef
  -- `‖(q, 0)‖ ≤ Rbase`.
  have hqbase : ‖q‖ ≤ Rbase := by
    have hmb := hRsub hq
    rw [Metric.mem_closedBall, dist_eq_norm] at hmb
    calc ‖q‖ = ‖(q - p₀) + p₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖q - p₀‖ + ‖p₀‖ := norm_add_le _ _
      _ ≤ R + ‖p₀‖ := by linarith [hmb]
      _ = Rbase := by rw [hRbasedef]
  have hqn : ‖((q, 0) : Point n × Point n)‖ ≤ Rbase := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg q)]; exact hqbase
  -- Base tube stays in `S` on `[0,1]`.
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y τ ∈ S := by
    intro τ hτ
    rw [hSdef, Metric.mem_closedBall]
    have hconf : ‖Y τ - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ :=
      uniformFlowTube_spec_conf g gi hC hK q hq v hvρ τ hτ
    have hc : C₀ * ‖v‖ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ hC₀nn
    calc dist (Y τ) (0 : Point n × Point n)
        ≤ dist (Y τ) ((q, 0) : Point n × Point n)
            + dist ((q, 0) : Point n × Point n) (0 : Point n × Point n) := dist_triangle _ _ _
      _ = ‖Y τ - ((q, 0) : Point n × Point n)‖ + ‖((q, 0) : Point n × Point n)‖ := by
            rw [dist_eq_norm, dist_zero_right]
      _ ≤ C₀ * ρ + Rbase := add_le_add (le_trans hconf hc) hqn
      _ = RG := by rw [hRGdef]; ring
  -- Base tube continuity on `[0,1]`.
  have hYcont : ContinuousOn Y (Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq v hvρ τ hτoo).continuousAt).continuousWithinAt
  -- Field-Jacobian bound along the base tube.
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y τ)‖ ≤ Kf :=
    fun τ hτ => hKf (Y τ) (hmem τ hτ)
  -- ===== First variation: velocity Jacobi field seeded `(0, a)`, `[0,1]` within solver. =====
  obtain ⟨V, hV0, hVd⟩ := geodesicJacobi_exists_on_Icc g gi hC Y hYcont ((0 : Point n), a)
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hVd τ hτ).continuousWithinAt
  -- Homogeneous Grönwall: `‖V τ‖ ≤ ‖a‖·e^{Kf}` on `[0,1]`.
  have hnorm0a : ‖((0 : Point n), a)‖ = ‖a‖ := by rw [Prod.norm_def]; simp
  have hVbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖V τ‖ ≤ ‖a‖ * Real.exp Kf := by
    intro τ hτ
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le (f := V)
      (f' := fun x => fderiv ℝ (geodesicField g gi) (Y x) (V x))
      (δ := ‖((0 : Point n), a)‖) (K := Kf) (ε := 0) (a := 0) (b := 1) hVcont
      (fun x hx => hasDerivWithinAt_Ici_of_Icc01 hx (hVd x (Set.Ico_subset_Icc_self hx)))
      (le_of_eq (by rw [hV0]))
      (fun x hx => by
        have hle := (fderiv ℝ (geodesicField g gi) (Y x)).le_opNorm (V x)
        calc ‖fderiv ℝ (geodesicField g gi) (Y x) (V x)‖
            ≤ ‖fderiv ℝ (geodesicField g gi) (Y x)‖ * ‖V x‖ := hle
          _ ≤ Kf * ‖V x‖ :=
              mul_le_mul_of_nonneg_right (hKb x (Set.Ico_subset_Icc_self hx)) (norm_nonneg _)
          _ = Kf * ‖V x‖ + 0 := by ring)
      τ hτ
    rw [sub_zero, gronwallBound_ε0, hnorm0a] at hgw
    refine hgw.trans ?_
    have hexp : Real.exp (Kf * τ) ≤ Real.exp Kf := by
      apply Real.exp_le_exp.mpr
      calc Kf * τ ≤ Kf * 1 := mul_le_mul_of_nonneg_left hτ.2 hKf0
        _ = Kf := mul_one _
    exact mul_le_mul_of_nonneg_left hexp (norm_nonneg a)
  -- ===== Second variation: inhomogeneous ODE `Zf' = DF·Zf + D²F(V,V)`, seed `0`. =====
  set A : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)) :=
    fun τ => fderiv ℝ (geodesicField g gi) (Y τ) with hAdef
  set Src : ℝ → Point n × Point n :=
    fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (V τ) with hSrcdef
  have hAcont : ContinuousOn A (Set.Icc (0 : ℝ) 1) := hDfcont.comp_continuousOn hYcont
  have hSrccont : ContinuousOn Src (Set.Icc (0 : ℝ) 1) := by
    have h0 : ContinuousOn (fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ))
        (Set.Icc (0 : ℝ) 1) := hD2f.continuous.comp_continuousOn hYcont
    exact (h0.clm_apply hVcont).clm_apply hVcont
  obtain ⟨Zf, hZ0, hZd⟩ :=
    linODE_inhomog_within_exists_on_Icc A Src hAcont hSrccont (0 : Point n × Point n)
  -- Source norm bound: `‖Src τ‖ ≤ M₂·(‖a‖ e^{Kf})²`.
  set Smax : ℝ := M₂ * (‖a‖ * Real.exp Kf) ^ 2 with hSmaxdef
  have hSmax : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Src τ‖ ≤ Smax := by
    intro τ hτ
    have h1 := (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)).le_opNorm (V τ)
    have h2 := ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)) (V τ)).le_opNorm (V τ)
    have hVτ : ‖V τ‖ ≤ ‖a‖ * Real.exp Kf := hVbnd τ hτ
    have hVτ0 : 0 ≤ ‖V τ‖ := norm_nonneg _
    have hstep : ‖Src τ‖ ≤ M₂ * ‖V τ‖ * ‖V τ‖ := by
      calc ‖Src τ‖ = ‖(fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)) (V τ) (V τ)‖ := by
              rw [hSrcdef]
        _ ≤ ‖(fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)) (V τ)‖ * ‖V τ‖ := h2
        _ ≤ (‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)‖ * ‖V τ‖) * ‖V τ‖ :=
              mul_le_mul_of_nonneg_right h1 hVτ0
        _ = ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)‖ * ‖V τ‖ * ‖V τ‖ := by ring
        _ ≤ M₂ * ‖V τ‖ * ‖V τ‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hM₂ (Y τ) (hmem τ hτ)) hVτ0) hVτ0
    refine hstep.trans ?_
    rw [hSmaxdef]
    have hsq : ‖V τ‖ * ‖V τ‖ ≤ (‖a‖ * Real.exp Kf) * (‖a‖ * Real.exp Kf) :=
      mul_le_mul hVτ hVτ hVτ0 (by positivity)
    calc M₂ * ‖V τ‖ * ‖V τ‖ = M₂ * (‖V τ‖ * ‖V τ‖) := by ring
      _ ≤ M₂ * ((‖a‖ * Real.exp Kf) * (‖a‖ * Real.exp Kf)) :=
            mul_le_mul_of_nonneg_left hsq hM₂0
      _ = M₂ * (‖a‖ * Real.exp Kf) ^ 2 := by ring
  -- Grönwall on `Zf`: `‖Zf τ‖ ≤ gronwallBound 0 Kf Smax τ`.
  have hZcont : ContinuousOn Zf (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hZd τ hτ).continuousWithinAt
  have hZbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Zf τ‖ ≤ gronwallBound 0 Kf Smax τ := by
    intro τ hτ
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le (f := Zf)
      (f' := fun x => A x (Zf x) + Src x)
      (δ := 0) (K := Kf) (ε := Smax) (a := 0) (b := 1) hZcont
      (fun x hx => hasDerivWithinAt_Ici_of_Icc01 hx (hZd x (Set.Ico_subset_Icc_self hx)))
      (by rw [hZ0]; simp)
      (fun x hx => by
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
        calc ‖A x (Zf x) + Src x‖ ≤ ‖A x (Zf x)‖ + ‖Src x‖ := norm_add_le _ _
          _ ≤ ‖A x‖ * ‖Zf x‖ + ‖Src x‖ := by
                gcongr; exact (A x).le_opNorm (Zf x)
          _ ≤ Kf * ‖Zf x‖ + Smax := by
                gcongr
                · exact hKb x hxIcc
                · exact hSmax x hxIcc)
      τ hτ
    rwa [sub_zero] at hgw
  -- Assemble: `‖Zf τ‖ ≤ M₂j · ‖a‖²`.
  refine ⟨V, Zf, hV0, hVd, hZ0, ?_, ?_⟩
  · intro τ hτ
    have := hZd τ hτ
    rwa [hAdef, hSrcdef] at this
  · intro τ hτ
    have hSmaxnn : 0 ≤ Smax := by rw [hSmaxdef]; positivity
    have hmono := gronwallBound_mono (δ := 0) (K := Kf) (ε := Smax) (le_refl 0) hSmaxnn hKf0 hτ.2
    have hSmaxeq : Smax = ‖a‖ ^ 2 * C₂ := by rw [hSmaxdef, hC₂def]; ring
    calc ‖Zf τ‖ ≤ gronwallBound 0 Kf Smax τ := hZbnd τ hτ
      _ ≤ gronwallBound 0 Kf Smax 1 := hmono
      _ = gronwallBound 0 Kf (‖a‖ ^ 2 * C₂) 1 := by rw [hSmaxeq]
      _ = ‖a‖ ^ 2 * gronwallBound 0 Kf C₂ 1 := gronwallBound_zero_mul_ε Kf 1 (‖a‖ ^ 2) C₂
      _ = M₂j * ‖a‖ ^ 2 := by rw [hM₂jdef]; ring

end QIQTH.ExpMap
