/-
  UniformFlowThirdJet — J4-71 (Brick-A β): BEGIN the C³ layer.  The intrinsic THIRD-VARIATION field
  along the UNIFORM-flow exp tube `uniformFlowTube`, together with a UNIFORM (over `q ∈ K`, `‖v‖ ≤ r₀`)
  Grönwall norm bound, CUBIC in the variation direction — the opening rung (W1) of the C³ sub-tower
  toward `g̃ ∈ C²` (`uniformFlowExp ∈ C³`).  This mirrors J4-65 (`uniformFlowTube_secondVariation_uniform_bound`)
  ONE ORDER UP.

  ## Context

  * The C² layer is CLOSED: R1 (`uniformFlowTube_secondVariation_uniform_bound`, this file's template) built
    the intrinsic SECOND-variation field with a uniform quadratic Grönwall bound; R2/R3
    (`uniformFlowExp_fderiv_hasFDerivAt`, `uniformFlowExp_hessian_opNorm_le`) closed Hessian existence + the
    uniform Hessian operator-norm bound.
  * The next layer is C³: the residual chain needs `uniformFlowExp ∈ C³` — a 3rd velocity derivative whose
    existence + uniform bound mirror the C² climb one order higher.

  ## What lands here (W1; DERIVED; no `sorry`, no hyp = conclusion, no smuggled 3rd-order conclusion, no `expRho`)

  `uniformFlowTube_thirdVariation_uniform_bound` — **W1.**  There is one uniform radius `r₀ = ρ_K/2 > 0`
  and one uniform constant `M₃j ≥ 0` such that for every `q ∈ K`, every `v` with `‖v‖ ≤ r₀`, and every
  variation direction `a`, along the base tube `Y = uniformFlowTube g gi hC hK q v` there exist:
    * the FIRST-variation (velocity Jacobi) field `V` with `V 0 = (0, a)` solving `V' = DF(Y)·V`;
    * the SECOND-variation field `W` with `W 0 = 0` solving `W' = DF(Y)·W + D²F(Y)(V,V)`;
    * the intrinsic THIRD-variation field `Z₃` with `Z₃ 0 = 0` solving the INHOMOGENEOUS third-variation
      ODE `Z₃' = DF(Y)·Z₃ + [D³F(Y)(V,V,V) + 2·D²F(Y)(V,W) + D²F(Y)(W,V)]`;
  and the UNIFORM Grönwall norm bound `‖Z₃ τ‖ ≤ M₃j · ‖a‖³` for all `τ ∈ [0,1]`.

  The third-variation source `Src₃ = D³F(V,V,V) + 2·D²F(V,W) + D²F(W,V)` is exactly what one obtains by
  differentiating the second-variation ODE `W' = DF·W + D²F(V,V)` in the deformation parameter (`∂_ε V = W`,
  no symmetry of `D²F` assumed; the `2·D²F(V,W) + D²F(W,V)` is the un-collapsed form of the standard
  `3·D²F(V,W)`), written as the four-summand `D³F(V,V,V) + D²F(V,W) + D²F(V,W) + D²F(W,V)`.

  The constants `M₃j` (and `r₀`) are chosen BEFORE introducing `q, v, a`: `Kf` (field-Jacobian sup), `M₂`
  (D²F sup) and `M₃` (D³F sup) are taken over the SINGLE compact phase ball `S` covering all base tubes for
  `q ∈ K`, `‖w‖ ≤ ρ_K`, so the bound is genuinely `q`-uniform.  NO `expRho`.

  ## Proof route (within-derivative Grönwall on `[0,1]`)

  Identical shape to R1.  Build the base tube confined in `S` (K1 confinement); `V` from the homogeneous
  `[0,1]` solver `geodesicJacobi_exists_on_Icc` (`‖V‖ ≤ ‖a‖·e^{Kf}`); `W` from the inhomogeneous within-solver
  `linODE_inhomog_within_exists_on_Icc` with source `D²F(V,V)` (`‖W‖ ≤ M₂j·‖a‖²`, the R1 bound); `Z₃` from the
  SAME solver with the richer cubic source `Src₃` (`‖Src₃‖ ≤ Smax = ‖a‖³·C₃`), giving
  `‖Z₃ τ‖ ≤ gronwallBound 0 Kf Smax 1 = ‖a‖³·M₃j`.

  ## HONEST CHECKPOINT (binding) — the remaining C³ map (FIREWALLED)

  This lands W1 (the intrinsic third-variation field along the uniform tube + its uniform, cubic Grönwall
  norm bound), all DERIVED from `hC` + `IsCompact K`.  It does NOT land:
    * W2 — the per-seed THIRD-jet EXISTENCE: `HasFDerivAt (fun w => B₂(w)) B₃ v` for the Hessian map, whose
      VALUE would be identified `= ((V₃ 1).?)` by a `hid_of_doubled_data`-analogue ONE ORDER UP (the tripled
      doubled-field flow).  CARRIED.
    * W3 — the uniform bound `‖B₃(q,v)‖ ≤ M₃j` on the third-derivative operator norm (given W2, W1's bound
      read off at `τ = 1`, plus a polarization assembly one order up).  CARRIED.
    * W4 — the assembly `uniformFlowExp ∈ C³` ⟹ `g̃ ∈ C²` and the residual Raychaudhuri wiring.  CARRIED.

  It does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.UniformFlowHessianDiag
import QIQTH.UniformFlowSecondJet
import QIQTH.UniformFlowSecondFDeriv
import QIQTH.SecondVariationSourceLip
import QIQTH.UniformFlowNondeg
import QIQTH.BoundedGeometry
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 10

variable {n : ℕ}

/-! ### W1 — the intrinsic third-variation field of the uniform flow, with a uniform cubic bound -/

/-- **W1 (J4-71) — the intrinsic THIRD-variation field of the uniform-flow tube, with a UNIFORM,
    cubic-in-direction Grönwall norm bound.**

    There is one uniform velocity radius `r₀ = ρ_K/2 > 0` and one uniform constant `M₃j ≥ 0` such that for
    every `q ∈ K`, every `v` with `‖v‖ ≤ r₀`, and every variation direction `a`, along the base tube
    `Y = uniformFlowTube g gi hC hK q v` there exist a first-variation (velocity Jacobi) field `V`
    (`V 0 = (0,a)`, solving `V' = DF(Y)·V`), the second-variation field `W` (`W 0 = 0`, solving
    `W' = DF(Y)·W + D²F(Y)(V,V)`), and the third-variation field `Z₃` (`Z₃ 0 = 0`, solving
    `Z₃' = DF(Y)·Z₃ + [D³F(Y)(V,V,V) + D²F(Y)(V,W) + D²F(Y)(V,W) + D²F(Y)(W,V)]`) with
        `∀ τ ∈ [0,1], ‖Z₃ τ‖ ≤ M₃j · ‖a‖³`.

    Hypotheses ONLY `hC` (Christoffel `C^∞`) + `IsCompact K`.  The constants are `q`-independent (sups over
    the SINGLE compact phase ball covering all base tubes for `q ∈ K`, `‖w‖ ≤ ρ_K`).  NO `expRho`, NO carried
    third-order conclusion.  See the module firewall for W2/W3/W4. -/
theorem uniformFlowTube_thirdVariation_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ M₃j : ℝ, 0 ≤ M₃j ∧
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ r₀ → ∀ a : Point n,
        ∃ V W Z₃ : ℝ → Point n × Point n,
          V 0 = ((0 : Point n), a) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivWithinAt V
              (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (V τ))
              (Set.Icc (0 : ℝ) 1) τ) ∧
          W 0 = 0 ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivWithinAt W
              (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (W τ)
                + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q v τ)
                    (V τ) (V τ))
              (Set.Icc (0 : ℝ) 1) τ) ∧
          Z₃ 0 = 0 ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivWithinAt Z₃
              (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (Z₃ τ)
                + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
                      (uniformFlowTube g gi hC hK q v τ) (V τ) (V τ) (V τ)
                  + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q v τ)
                      (V τ) (W τ)
                  + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q v τ)
                      (V τ) (W τ)
                  + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q v τ)
                      (W τ) (V τ)))
              (Set.Icc (0 : ℝ) 1) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Z₃ τ‖ ≤ M₃j * ‖a‖ ^ 3) := by
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
  have hD3fcont : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) :=
    hD2f.continuous_fderiv (by simp)
  -- One compact phase ball covering all base tubes for `q ∈ K`, `‖w‖ ≤ ρ`.
  obtain ⟨R, hRsub⟩ := hK.isBounded.subset_closedBall (0 : Point n)
  set Rb : ℝ := max R 0 with hRbdef
  have hRb0 : 0 ≤ Rb := le_max_right _ _
  set RG : ℝ := Rb + C₀ * ρ with hRGdef
  have hRG0 : 0 ≤ RG := by rw [hRGdef]; positivity
  set S : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) RG with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have h0S : (0 : Point n × Point n) ∈ S := by rw [hSdef]; exact Metric.mem_closedBall_self hRG0
  -- Uniform field-Jacobian sup over `S`.
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  -- Uniform D²F sup over `S`.
  obtain ⟨M₂, hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
      hD2f.continuous.norm
    obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn ⟨(0 : Point n × Point n), h0S⟩ hcontr.continuousOn
    exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖, norm_nonneg _,
      fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  -- Uniform D³F sup over `S`.
  obtain ⟨M₃, hM₃0, hM₃⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) z‖ ≤ Kb := by
    have hcontr : Continuous
        (fun z => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) z‖) := hD3fcont.norm
    obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn ⟨(0 : Point n × Point n), h0S⟩ hcontr.continuousOn
    exact ⟨‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x‖, norm_nonneg _,
      fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  -- The uniform constants, chosen BEFORE `intro q v a`.
  set C₂ : ℝ := M₂ * (Real.exp Kf) ^ 2 with hC₂def
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂def]; positivity
  set M₂j : ℝ := gronwallBound 0 Kf C₂ 1 with hM₂jdef
  have hM₂j0 : 0 ≤ M₂j := by
    have hmono := gronwallBound_mono (δ := 0) (K := Kf) (ε := C₂) (le_refl 0) hC₂0 hKf0
      (show (0 : ℝ) ≤ 1 by norm_num)
    rwa [gronwallBound_x0] at hmono
  set C₃ : ℝ := M₃ * (Real.exp Kf) ^ 3 + 3 * M₂ * (Real.exp Kf) * M₂j with hC₃def
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃def]; positivity
  set M₃j : ℝ := gronwallBound 0 Kf C₃ 1 with hM₃jdef
  have hM₃j0 : 0 ≤ M₃j := by
    have hmono := gronwallBound_mono (δ := 0) (K := Kf) (ε := C₃) (le_refl 0) hC₃0 hKf0
      (show (0 : ℝ) ≤ 1 by norm_num)
    rwa [gronwallBound_x0] at hmono
  refine ⟨ρ / 2, by positivity, M₃j, hM₃j0, ?_⟩
  intro q hq v hv a
  have hvρ : ‖v‖ ≤ ρ := le_trans hv (by linarith)
  -- Base tube through `(q, v)`.
  set Y : ℝ → Point n × Point n := uniformFlowTube g gi hC hK q v with hYdef
  -- `‖q‖ ≤ Rb`.
  have hqRb : ‖q‖ ≤ Rb := by
    have := hRsub hq; rw [Metric.mem_closedBall, dist_zero_right] at this
    exact le_trans this (le_max_left _ _)
  -- Base tube stays in `S` on `[0,1]`.
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y τ ∈ S := by
    intro τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]
    have hconf : ‖Y τ - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ :=
      uniformFlowTube_spec_conf g gi hC hK q hq v hvρ τ hτ
    have hqn : ‖((q, 0) : Point n × Point n)‖ ≤ Rb := by
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg q)]; exact hqRb
    calc ‖Y τ‖ = ‖(Y τ - ((q, 0) : Point n × Point n)) + ((q, 0) : Point n × Point n)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖Y τ - ((q, 0) : Point n × Point n)‖ + ‖((q, 0) : Point n × Point n)‖ := norm_add_le _ _
      _ ≤ C₀ * ρ + Rb := add_le_add (le_trans hconf (mul_le_mul_of_nonneg_left hvρ hC₀nn)) hqn
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
  -- ===== Second variation: inhomogeneous ODE `W' = DF·W + D²F(V,V)`, seed `0`. =====
  set A : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)) :=
    fun τ => fderiv ℝ (geodesicField g gi) (Y τ) with hAdef
  set Src2 : ℝ → Point n × Point n :=
    fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (V τ) with hSrc2def
  have hAcont : ContinuousOn A (Set.Icc (0 : ℝ) 1) := hDfcont.comp_continuousOn hYcont
  have hSrc2cont : ContinuousOn Src2 (Set.Icc (0 : ℝ) 1) := by
    have h0 : ContinuousOn (fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ))
        (Set.Icc (0 : ℝ) 1) := hD2f.continuous.comp_continuousOn hYcont
    exact (h0.clm_apply hVcont).clm_apply hVcont
  obtain ⟨W, hW0, hWd⟩ :=
    linODE_inhomog_within_exists_on_Icc A Src2 hAcont hSrc2cont (0 : Point n × Point n)
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hWd τ hτ).continuousWithinAt
  -- Source bound for `W`: `‖Src2 τ‖ ≤ M₂·(‖a‖ e^{Kf})²`.
  have hSmax2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖Src2 x‖ ≤ M₂ * (‖a‖ * Real.exp Kf) ^ 2 := by
    intro x hx
    have h1 := (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y x)).le_opNorm (V x)
    have h2 := ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y x)) (V x)).le_opNorm (V x)
    have hVx : ‖V x‖ ≤ ‖a‖ * Real.exp Kf := hVbnd x hx
    have hVx0 : 0 ≤ ‖V x‖ := norm_nonneg _
    have hstep : ‖Src2 x‖ ≤ M₂ * ‖V x‖ * ‖V x‖ := by
      calc ‖Src2 x‖ = ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y x) (V x) (V x)‖ := by
              simp only [hSrc2def]
        _ ≤ ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y x) (V x)‖ * ‖V x‖ := h2
        _ ≤ (‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y x)‖ * ‖V x‖) * ‖V x‖ :=
              mul_le_mul_of_nonneg_right h1 hVx0
        _ = ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y x)‖ * ‖V x‖ * ‖V x‖ := by ring
        _ ≤ M₂ * ‖V x‖ * ‖V x‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hM₂ (Y x) (hmem x hx)) hVx0) hVx0
    refine hstep.trans ?_
    have hsq : ‖V x‖ * ‖V x‖ ≤ (‖a‖ * Real.exp Kf) * (‖a‖ * Real.exp Kf) :=
      mul_le_mul hVx hVx hVx0 (by positivity)
    calc M₂ * ‖V x‖ * ‖V x‖ = M₂ * (‖V x‖ * ‖V x‖) := by ring
      _ ≤ M₂ * ((‖a‖ * Real.exp Kf) * (‖a‖ * Real.exp Kf)) := mul_le_mul_of_nonneg_left hsq hM₂0
      _ = M₂ * (‖a‖ * Real.exp Kf) ^ 2 := by ring
  -- Grönwall bound for `W`: `‖W τ‖ ≤ M₂j·‖a‖²`.
  have hWbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖W τ‖ ≤ M₂j * ‖a‖ ^ 2 := by
    intro τ hτ
    have hWgron : ‖W τ‖ ≤ gronwallBound 0 Kf (M₂ * (‖a‖ * Real.exp Kf) ^ 2) τ := by
      have hgw := norm_le_gronwallBound_of_norm_deriv_right_le (f := W)
        (f' := fun x => A x (W x) + Src2 x)
        (δ := 0) (K := Kf) (ε := M₂ * (‖a‖ * Real.exp Kf) ^ 2) (a := 0) (b := 1) hWcont
        (fun x hx => hasDerivWithinAt_Ici_of_Icc01 hx (hWd x (Set.Ico_subset_Icc_self hx)))
        (by rw [hW0]; simp)
        (fun x hx => by
          have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
          calc ‖A x (W x) + Src2 x‖ ≤ ‖A x (W x)‖ + ‖Src2 x‖ := norm_add_le _ _
            _ ≤ ‖A x‖ * ‖W x‖ + ‖Src2 x‖ := by gcongr; exact (A x).le_opNorm (W x)
            _ ≤ Kf * ‖W x‖ + M₂ * (‖a‖ * Real.exp Kf) ^ 2 := by
                  gcongr
                  · exact hKb x hxIcc
                  · exact hSmax2 x hxIcc)
        τ hτ
      rwa [sub_zero] at hgw
    have hmono := gronwallBound_mono (δ := 0) (K := Kf) (ε := M₂ * (‖a‖ * Real.exp Kf) ^ 2)
      (le_refl 0) (by positivity) hKf0 hτ.2
    have heq : M₂ * (‖a‖ * Real.exp Kf) ^ 2 = ‖a‖ ^ 2 * C₂ := by rw [hC₂def]; ring
    calc ‖W τ‖ ≤ gronwallBound 0 Kf (M₂ * (‖a‖ * Real.exp Kf) ^ 2) τ := hWgron
      _ ≤ gronwallBound 0 Kf (M₂ * (‖a‖ * Real.exp Kf) ^ 2) 1 := hmono
      _ = gronwallBound 0 Kf (‖a‖ ^ 2 * C₂) 1 := by rw [heq]
      _ = ‖a‖ ^ 2 * gronwallBound 0 Kf C₂ 1 := gronwallBound_zero_mul_ε Kf 1 (‖a‖ ^ 2) C₂
      _ = M₂j * ‖a‖ ^ 2 := by rw [hM₂jdef]; ring
  -- ===== Third variation: inhomogeneous ODE `Z₃' = DF·Z₃ + Src₃`, seed `0`. =====
  set Src3 : ℝ → Point n × Point n := fun τ =>
    fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ) (V τ) (V τ)
    + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (W τ)
    + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (W τ)
    + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (W τ) (V τ) with hSrc3def
  have hSrc3cont : ContinuousOn Src3 (Set.Icc (0 : ℝ) 1) := by
    have hD2c : ContinuousOn (fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ))
        (Set.Icc (0 : ℝ) 1) := hD2f.continuous.comp_continuousOn hYcont
    have hD3c : ContinuousOn
        (fun τ => fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ))
        (Set.Icc (0 : ℝ) 1) := hD3fcont.comp_continuousOn hYcont
    have t1 : ContinuousOn
        (fun τ => fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ) (V τ) (V τ))
        (Set.Icc (0 : ℝ) 1) := ((hD3c.clm_apply hVcont).clm_apply hVcont).clm_apply hVcont
    have t2 : ContinuousOn
        (fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (W τ))
        (Set.Icc (0 : ℝ) 1) := (hD2c.clm_apply hVcont).clm_apply hWcont
    have t3 : ContinuousOn
        (fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (W τ) (V τ))
        (Set.Icc (0 : ℝ) 1) := (hD2c.clm_apply hWcont).clm_apply hVcont
    simp only [hSrc3def]
    exact ((t1.add t2).add t2).add t3
  obtain ⟨Z₃, hZ30, hZ3d⟩ :=
    linODE_inhomog_within_exists_on_Icc A Src3 hAcont hSrc3cont (0 : Point n × Point n)
  have hZ3cont : ContinuousOn Z₃ (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hZ3d τ hτ).continuousWithinAt
  -- Source bound for `Z₃`: `‖Src3 τ‖ ≤ Smax`.
  set Smax : ℝ :=
    M₃ * (‖a‖ * Real.exp Kf) ^ 3 + 3 * M₂ * (‖a‖ * Real.exp Kf) * (M₂j * ‖a‖ ^ 2) with hSmaxdef
  have hSrc3bnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Src3 τ‖ ≤ Smax := by
    intro τ hτ
    have hVτ : ‖V τ‖ ≤ ‖a‖ * Real.exp Kf := hVbnd τ hτ
    have hWτ : ‖W τ‖ ≤ M₂j * ‖a‖ ^ 2 := hWbnd τ hτ
    have hD3sup : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ)‖ ≤ M₃ :=
      hM₃ (Y τ) (hmem τ hτ)
    have hD2sup : ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)‖ ≤ M₂ := hM₂ (Y τ) (hmem τ hτ)
    -- Term bound: `‖D³F(Yτ)(Vτ,Vτ,Vτ)‖ ≤ M₃·(‖a‖ e^{Kf})³`.
    have hD3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ) (V τ) (V τ)‖
        ≤ M₃ * (‖a‖ * Real.exp Kf) ^ 3 := by
      have e1 := (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ) (V τ)).le_opNorm (V τ)
      have e2 := (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ)).le_opNorm (V τ)
      have e3 := (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ)).le_opNorm (V τ)
      calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ) (V τ) (V τ)‖
          ≤ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ) (V τ)‖ * ‖V τ‖ := e1
        _ ≤ (‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ)‖ * ‖V τ‖) * ‖V τ‖ :=
              mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
        _ ≤ ((‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ)‖ * ‖V τ‖) * ‖V τ‖) * ‖V τ‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right e3 (norm_nonneg _)) (norm_nonneg _)
        _ ≤ ((M₃ * (‖a‖ * Real.exp Kf)) * (‖a‖ * Real.exp Kf)) * (‖a‖ * Real.exp Kf) := by
              gcongr
        _ = M₃ * (‖a‖ * Real.exp Kf) ^ 3 := by ring
    -- Term bound: `‖D²F(Yτ)(Vτ,Wτ)‖ ≤ M₂·(‖a‖ e^{Kf})·(M₂j‖a‖²)`.
    have hD2vw : ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (W τ)‖
        ≤ M₂ * (‖a‖ * Real.exp Kf) * (M₂j * ‖a‖ ^ 2) := by
      have e1 := (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ)).le_opNorm (W τ)
      have e2 := (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)).le_opNorm (V τ)
      calc ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (W τ)‖
          ≤ ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ)‖ * ‖W τ‖ := e1
        _ ≤ (‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)‖ * ‖V τ‖) * ‖W τ‖ :=
              mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
        _ ≤ (M₂ * (‖a‖ * Real.exp Kf)) * (M₂j * ‖a‖ ^ 2) := by
              gcongr
        _ = M₂ * (‖a‖ * Real.exp Kf) * (M₂j * ‖a‖ ^ 2) := by ring
    -- Term bound: `‖D²F(Yτ)(Wτ,Vτ)‖ ≤ M₂·(M₂j‖a‖²)·(‖a‖ e^{Kf})`.
    have hD2wv : ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (W τ) (V τ)‖
        ≤ M₂ * (M₂j * ‖a‖ ^ 2) * (‖a‖ * Real.exp Kf) := by
      have e1 := (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (W τ)).le_opNorm (V τ)
      have e2 := (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)).le_opNorm (W τ)
      calc ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (W τ) (V τ)‖
          ≤ ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (W τ)‖ * ‖V τ‖ := e1
        _ ≤ (‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ)‖ * ‖W τ‖) * ‖V τ‖ :=
              mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
        _ ≤ (M₂ * (M₂j * ‖a‖ ^ 2)) * (‖a‖ * Real.exp Kf) := by
              gcongr
        _ = M₂ * (M₂j * ‖a‖ ^ 2) * (‖a‖ * Real.exp Kf) := by ring
    -- Assemble the four-summand source, bound by triangle + term bounds.
    simp only [hSrc3def]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) (le_refl _)) ?_
    refine le_trans (add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)) ?_
    refine le_trans (add_le_add (add_le_add (add_le_add hD3 hD2vw) hD2vw) hD2wv) ?_
    rw [hSmaxdef]; apply le_of_eq; ring
  -- Grönwall on `Z₃`: `‖Z₃ τ‖ ≤ gronwallBound 0 Kf Smax τ`.
  have hZ3bnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Z₃ τ‖ ≤ gronwallBound 0 Kf Smax τ := by
    intro τ hτ
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le (f := Z₃)
      (f' := fun x => A x (Z₃ x) + Src3 x)
      (δ := 0) (K := Kf) (ε := Smax) (a := 0) (b := 1) hZ3cont
      (fun x hx => hasDerivWithinAt_Ici_of_Icc01 hx (hZ3d x (Set.Ico_subset_Icc_self hx)))
      (by rw [hZ30]; simp)
      (fun x hx => by
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
        calc ‖A x (Z₃ x) + Src3 x‖ ≤ ‖A x (Z₃ x)‖ + ‖Src3 x‖ := norm_add_le _ _
          _ ≤ ‖A x‖ * ‖Z₃ x‖ + ‖Src3 x‖ := by gcongr; exact (A x).le_opNorm (Z₃ x)
          _ ≤ Kf * ‖Z₃ x‖ + Smax := by
                gcongr
                · exact hKb x hxIcc
                · exact hSrc3bnd x hxIcc)
      τ hτ
    rwa [sub_zero] at hgw
  -- ===== Assemble. =====
  refine ⟨V, W, Z₃, hV0, hVd, hW0, ?_, hZ30, ?_, ?_⟩
  · -- `W` ODE in the stated form.
    intro τ hτ
    have h := hWd τ hτ
    rwa [hAdef, hSrc2def] at h
  · -- `Z₃` ODE in the stated form.
    intro τ hτ
    have h := hZ3d τ hτ
    rwa [hAdef, hSrc3def] at h
  · -- Uniform cubic bound.
    intro τ hτ
    have hSmaxnn : 0 ≤ Smax := by rw [hSmaxdef]; positivity
    have hmono := gronwallBound_mono (δ := 0) (K := Kf) (ε := Smax) (le_refl 0) hSmaxnn hKf0 hτ.2
    have hSmaxeq : Smax = ‖a‖ ^ 3 * C₃ := by rw [hSmaxdef, hC₃def]; ring
    calc ‖Z₃ τ‖ ≤ gronwallBound 0 Kf Smax τ := hZ3bnd τ hτ
      _ ≤ gronwallBound 0 Kf Smax 1 := hmono
      _ = gronwallBound 0 Kf (‖a‖ ^ 3 * C₃) 1 := by rw [hSmaxeq]
      _ = ‖a‖ ^ 3 * gronwallBound 0 Kf C₃ 1 := gronwallBound_zero_mul_ε Kf 1 (‖a‖ ^ 3) C₃
      _ = M₃j * ‖a‖ ^ 3 := by rw [hM₃jdef]; ring

end QIQTH.ExpMap
