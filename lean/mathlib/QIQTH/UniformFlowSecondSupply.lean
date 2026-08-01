/-
  UniformFlowSecondSupply — J4-67 (Brick-A β, R2 climb): the base-velocity-perturbed CONFINED doubled
  uniform-tube SUPPLY (R2-a), the exposure of the K2 endpoint Jacobi operator (R2-b), and the resulting
  per-direction Fréchet second-jet of `uniformFlowExp`.

  ## Context

  * J4-66 (`UniformFlowSecondFDeriv`, `doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists`) built the
    ENABLER: given a base-velocity-perturbed doubled uniform-tube SUPPLY (integral curves `W δ` of
    `G = doubledField g gi` with `W δ 0 − W 0 0 = ((0,δ),(0,0))`, confined in a compact convex product
    ball, plus the doubled-linearized field `V δ`), it yields
        `∃ L, (∀ δ, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0`.
  * K1 (`UniformFlowNondeg`) built `uniformFlowTube`/`uniformFlowExp`.  K2 (`UniformFlowFDeriv`,
    `uniformFlowExp_hasFDerivAt`) proved the first-order Fréchet derivative of `uniformFlowExp` in the
    IC (only `∃ L`, the operator NOT exposed).  R1 (`UniformFlowSecondJet`) built the intrinsic
    second-variation field with a uniform quadratic bound.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled 2nd-order conclusion,
  no `expRho`)

  * `uniformFlowExp_fderiv_apply_eq` (**R2-b enabler**) — **the K2 endpoint Jacobi operator, EXPOSED.**
    For `q ∈ K`, `‖w‖ < ρ_K`, and ANY velocity Jacobi field `J` along the base tube
    `uniformFlowTube g gi hC hK q w` with `J 0 = (0, b)`, the K2 Fréchet derivative applied to `b` IS the
    Jacobi endpoint's position component:
        `fderiv ℝ (uniformFlowExp g gi hC hK q) w b = (J 1).1`.
    DERIVED by reproducing the K2 window-capstone construction (`flowVelocity_endpoint_hasFDerivAt_window_exists`)
    to obtain `fderiv = Lpos` with `Lpos b = (V b 1).1`, then `jacobiSol_unique` identifying the K2 base
    Jacobi `V b` with the supplied `J` (same base tube, same seed).  This is the identification K2's `∃ L`
    does not expose and which R2-b needs.

  * `uniformFlow_doubledEndpoint_baseVelocity_hasFDerivAt` (**R2-a**) — **the base-velocity-perturbed
    confined doubled uniform-tube supply, fed to J4-66.**  For `q ∈ K`, `‖v‖ < ρ_K`, and a fixed
    variation seed `b`, there is a velocity-Jacobi family `Jf` (each `Jf δ` a genuine
    `geodesicField`-linearized field along `uniformFlowTube q (v+δ)`, seed `(0,b)`) and a continuous-linear
    `L` such that the DOUBLED-flow endpoint
        `δ ↦ (uniformFlowTube g gi hC hK q (v+δ) 1, Jf δ 1)`
    is Fréchet-differentiable at `0` with derivative `L`.  The supply is a GENUINE confined
    `G`-integral-curve family: the first factor is the confined uniform tube (K1), the second factor the
    velocity Jacobi field along it (`geodesicJacobi_narrowpad_continuousOn`, with a Grönwall confinement
    ball), the pair a `doubledField` integral curve (`doubledField_prod_hasDerivAt`), the doubled-linearized
    field `V δ` along the fixed base doubled curve (`doubledVariation_narrowpad_hasDerivAt_Icc`).  NOT
    vacuous; NO `expRho`.

  * `uniformFlowExp_fderiv_apply_hasFDerivAt` (**R2-b**) — **the per-direction Fréchet second-jet of
    `uniformFlowExp`.**  For `q ∈ K`, `‖v‖ < ρ_K`, and each variation seed `b`, the applied jet map
        `w ↦ fderiv ℝ (uniformFlowExp g gi hC hK q) w b`
    has a Fréchet derivative at `v`:
        `∃ L₂, HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w b) L₂ v`.
    DERIVED: project the R2-a doubled endpoint's `.2.1` component (J4-66's `L`), rewrite it (on the
    velocity window, via `uniformFlowExp_fderiv_apply_eq`) as `fderiv (uniformFlowExp q) (v+δ) b`, and
    recentre `δ ↦ v + δ`.

  ## HONEST FIREWALL (binding) — what R2 (the full Hessian's EXISTENCE) still needs

  R2-a and R2-b land here fully.  The FINAL R2 target
      `∃ B₂, HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) B₂ v`
  (the CLM-VALUED jet map `w ↦ fderiv (uniformFlowExp q) w`, valued in `Point n →L[ℝ] Point n`) is NOT
  closed here.  R2-b gives, for EACH seed `b`, the Fréchet derivative of the SCALAR-slot map
  `w ↦ fderiv (uniformFlowExp q) w b`; assembling these into the operator-norm little-o for the
  CLM-valued map (uniform over `‖b‖ ≤ 1`) is the remaining obligation.  In finite dimensions it reduces
  to the linear iso `(Point n →L[ℝ] Point n) ≃L (Point n)^n` (differentiability of a CLM-valued map ⟺
  differentiability of its evaluations on a basis) — a genuine but codebase-absent assembly, CARRIED.
  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.UniformFlowSecondFDeriv
import QIQTH.UniformFlowSecondJet
import QIQTH.DoubledVariationField
import QIQTH.DoubledFamilyConstruction
import QIQTH.UniformFlowFDeriv
import QIQTH.UniformFlowNondeg
import QIQTH.GenericJacobiExists
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-! ### R2-b enabler — the K2 endpoint Jacobi operator, exposed as a Jacobi endpoint -/

/-- **R2-b enabler — the K2 endpoint Jacobi operator is the velocity Jacobi endpoint.**  For `q ∈ K`,
    `‖w‖ < ρ_K`, and ANY velocity Jacobi field `J` along the base tube `uniformFlowTube g gi hC hK q w`
    (seed `J 0 = (0, b)`, solving `J' = DF(tube)·J` on `[0,1]`), the K2 Fréchet derivative of
    `uniformFlowExp` at `w`, applied to the direction `b`, equals the Jacobi endpoint's position:
        `fderiv ℝ (uniformFlowExp g gi hC hK q) w b = (J 1).1`.
    Reproduces the K2 window-capstone (`flowVelocity_endpoint_hasFDerivAt_window_exists`) to get
    `fderiv = Lpos`, `Lpos b = (V b 1).1`, then `jacobiSol_unique` (`V b` and `J` are Jacobi along the
    SAME base tube with the SAME seed). -/
theorem uniformFlowExp_fderiv_apply_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (w : Point n)
    (hw : ‖w‖ < uniformFlowRadius g gi hC hK) (b : Point n)
    (J : ℝ → Point n × Point n) (hJ0 : J 0 = ((0 : Point n), b))
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q w τ) (J τ)) τ) :
    fderiv ℝ (uniformFlowExp g gi hC hK q) w b = (J 1).1 := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  set σ : ℝ := ρ - ‖w‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  set Wf : Point n → ℝ → Point n × Point n :=
    fun δ => uniformFlowTube g gi hC hK q (w + δ) with hWfdef
  have hle : ∀ δ : Point n, ‖δ‖ ≤ σ → ‖w + δ‖ ≤ ρ := by
    intro δ hδ
    refine (norm_add_le w δ).trans ?_
    rw [hσdef] at hδ; linarith
  set S : Set (Point n × Point n) := Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  have hC₀ρ0 : 0 ≤ C₀ * ρ := mul_nonneg hC₀nn hρ0.le
  have hqmem : ((q, 0) : Point n × Point n) ∈ S := by
    rw [hSdef]; exact Metric.mem_closedBall_self hC₀ρ0
  obtain ⟨M₂, _hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
      (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
        (by simp)).norm
    obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn ⟨(q, 0), hqmem⟩ hcontr.continuousOn
    exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
      norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x),
      fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  obtain ⟨K₀, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) hSconv hScompact
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Wf δ) (geodesicField g gi (Wf δ τ)) τ := by
    intro δ hδ τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK q hq (w + δ) (hle δ hδ) τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, Wf δ τ ∈ S := by
    intro δ hδ τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖Wf δ τ - ((q, 0) : Point n × Point n)‖
        ≤ C₀ * ‖w + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (w + δ) (hle δ hδ) τ hτ
      _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left (hle δ hδ) hC₀nn
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → Wf δ 0 - Wf 0 0 = ((0, δ) : Point n × Point n) := by
    intro δ hδ
    have h1 : Wf δ 0 = (q, w + δ) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (w + δ) (hle δ hδ)
    have h2 : Wf 0 0 = (q, w + 0) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (w + 0) (hle 0 h0σ)
    rw [h1, h2, Prod.mk_sub_mk, sub_self, add_zero, add_sub_cancel_left]
  have hbasecont : ContinuousOn (Wf 0) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (w + 0) (hle 0 h0σ) τ hτoo).continuousAt).continuousWithinAt
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
  have hFDpos : HasFDerivAt (fun δ => (Wf δ 1).1) Lpos 0 := by
    have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp (0 : Point n) hFD
    simpa [hLposdef, Function.comp] using this
  have hfun : (fun δ => (Wf δ 1).1) = (fun δ => uniformFlowExp g gi hC hK q (w + δ)) := by
    funext δ; rw [hWfdef]; rw [uniformFlowExp_eq]
  rw [hfun] at hFDpos
  have hshift : HasFDerivAt (fun u : Point n => u - w) (ContinuousLinearMap.id ℝ (Point n)) w :=
    (hasFDerivAt_id w).sub_const w
  have hFDpos0 : HasFDerivAt (fun δ => uniformFlowExp g gi hC hK q (w + δ)) Lpos (w - w) := by
    rw [sub_self]; exact hFDpos
  have hcomp : HasFDerivAt (fun u => uniformFlowExp g gi hC hK q (w + (u - w)))
      (Lpos.comp (ContinuousLinearMap.id ℝ (Point n))) w :=
    hFDpos0.comp (f := fun u : Point n => u - w) w hshift
  have hfun2 : (fun u => uniformFlowExp g gi hC hK q (w + (u - w)))
      = uniformFlowExp g gi hC hK q := by
    funext u; congr 1; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  have hFDexp : HasFDerivAt (uniformFlowExp g gi hC hK q) Lpos w := hcomp
  have hfd : fderiv ℝ (uniformFlowExp g gi hC hK q) w = Lpos := hFDexp.fderiv
  rw [hfd]
  -- `Lpos b = (V b 1).1`.
  have hLposb : Lpos b = (V b 1).1 := by
    rw [hLposdef]; show (L b).1 = (V b 1).1; rw [hLeq b]
  rw [hLposb]
  -- `V b` and `J` are Jacobi along the SAME base tube with the SAME seed: `V b 1 = J 1`.
  have hbaseeq : Wf 0 = uniformFlowTube g gi hC hK q w := by
    rw [hWfdef]; simp only [add_zero]
  have hY0uniq : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (uniformFlowTube g gi hC hK q w)
        (geodesicField g gi (uniformFlowTube g gi hC hK q w τ)) τ := by
    intro τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK q hq w hw.le τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hKbuniq : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q w τ)‖ ≤ Kf := by
    intro τ hτ
    refine hKf (uniformFlowTube g gi hC hK q w τ) ?_
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖uniformFlowTube g gi hC hK q w τ - ((q, 0) : Point n × Point n)‖
        ≤ C₀ * ‖w‖ := uniformFlowTube_spec_conf g gi hC hK q hq w hw.le τ hτ
      _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hw.le hC₀nn
  have hVbode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V b)
        (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q w τ) (V b τ)) τ := by
    intro τ hτ
    have := hVode b τ hτ
    rwa [hbaseeq] at this
  have huniq : V b 1 = J 1 :=
    jacobiSol_unique g gi hKf0 hY0uniq hKbuniq hVbode hJode
      (by rw [hV0 b, hJ0]) ht1
  rw [huniq]

/-! ### R2-a — the base-velocity-perturbed confined doubled uniform-tube supply -/

/-- **R2-a — the base-velocity-perturbed confined doubled uniform-tube supply, fed to J4-66.**  For
    `q ∈ K`, `‖v‖ < ρ_K`, and a fixed variation seed `b`, there is a velocity-Jacobi family `Jf` and a
    continuous-linear `L` such that:
      * each `Jf δ` (for `‖δ‖ ≤ ρ_K − ‖v‖`) is a GENUINE velocity Jacobi field along the perturbed base
        tube `uniformFlowTube g gi hC hK q (v+δ)`, with seed `Jf δ 0 = (0, b)` and the linearized ODE;
      * the DOUBLED-flow endpoint `δ ↦ (uniformFlowTube g gi hC hK q (v+δ) 1, Jf δ 1)` is
        Fréchet-differentiable at `0` with derivative `L`.
    The supply is genuine (not vacuous): first factor = confined uniform tube (K1); second factor =
    velocity Jacobi along it (`geodesicJacobi_narrowpad_continuousOn`, Grönwall-confined); pair = a
    `doubledField` integral curve (`doubledField_prod_hasDerivAt`); doubled-linearized field via
    `doubledVariation_narrowpad_hasDerivAt_Icc`; fed to `doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists`.
    NO `expRho`. -/
theorem uniformFlow_doubledEndpoint_baseVelocity_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (b : Point n) :
    ∃ Jf : Point n → ℝ → Point n × Point n,
      (∀ δ : Point n, ‖δ‖ ≤ uniformFlowRadius g gi hC hK - ‖v‖ →
        Jf δ 0 = ((0 : Point n), b) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Jf δ)
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jf δ τ)) τ)) ∧
      ∃ L : Point n →L[ℝ] (Point n × Point n) × (Point n × Point n),
        HasFDerivAt
          (fun δ => ((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1) :
            (Point n × Point n) × (Point n × Point n))) L 0 := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  have hle : ∀ δ : Point n, ‖δ‖ ≤ σ → ‖v + δ‖ ≤ ρ := by
    intro δ hδ
    refine (norm_add_le v δ).trans ?_
    rw [hσdef] at hδ; linarith
  have hadm0 : ‖v + (0 : Point n)‖ ≤ ρ := by rw [add_zero]; exact hv.le
  -- Uniform `fderiv (geodesicField)` bound over the geodesic-tube confinement ball, for the Jacobi
  -- Grönwall confinement.
  have hAcompact : IsCompact (Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ)) :=
    isCompact_closedBall _ _
  obtain ⟨Kb, hKb0, hKbbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hAcompact
  set Jbound : ℝ := ‖((0 : Point n), b)‖ * Real.exp Kb with hJbounddef
  have hJbound0 : 0 ≤ Jbound := by rw [hJbounddef]; positivity
  -- The confinement product set.
  set S : Set ((Point n × Point n) × (Point n × Point n)) :=
    Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) ×ˢ
      Metric.closedBall (0 : Point n × Point n) Jbound with hSdef
  have hScompact : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hSconvex : Convex ℝ S := (convex_closedBall _ _).prod (convex_closedBall _ _)
  -- Per-δ velocity Jacobi field along the perturbed tube (genuine when `‖v+δ‖ ≤ ρ`).
  have key : ∀ δ : Point n, ∃ Jc : ℝ → Point n × Point n,
      (‖v + δ‖ ≤ ρ →
        Jc 0 = ((0 : Point n), b) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt Jc
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jc τ)) τ) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ Jbound) ∧
        ContinuousOn Jc (Set.Icc (-(1/2) : ℝ) (3/2))) := by
    intro δ
    by_cases h : ‖v + δ‖ ≤ ρ
    · set P : ℝ → Point n × Point n := uniformFlowTube g gi hC hK q (v + δ) with hPdef
      have hPcont : ContinuousOn P (Set.Icc (-(1/2) : ℝ) (3/2)) := by
        intro τ hτ
        have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + δ) h τ hτoo).continuousAt).continuousWithinAt
      obtain ⟨Jc, hJc0, hJcode, hJcpad⟩ :=
        geodesicJacobi_narrowpad_continuousOn g gi hC P hPcont ((0 : Point n), b)
      have hfderivbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (geodesicField g gi) (P x)‖ ≤ Kb := by
        intro x hx
        refine hKbbd (P x) ?_
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖P x - ((q, 0) : Point n × Point n)‖
            ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) h x hx
          _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left h hC₀nn
      have hJcont : ContinuousOn Jc (Set.Icc (0 : ℝ) 1) :=
        fun τ hτ => ((hJcode τ hτ).continuousAt).continuousWithinAt
      have hJgw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖Jc x‖ ≤ gronwallBound ‖((0 : Point n), b)‖ Kb 0 (x - 0) :=
        norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖((0 : Point n), b)‖)
          (K := Kb) (ε := 0) (a := 0) (b := 1) hJcont
          (fun x hx => (hJcode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
          (le_of_eq (by rw [hJc0]))
          (fun x hx => by
            have hle' := (fderiv ℝ (geodesicField g gi) (P x)).le_opNorm (Jc x)
            calc ‖fderiv ℝ (geodesicField g gi) (P x) (Jc x)‖
                ≤ ‖fderiv ℝ (geodesicField g gi) (P x)‖ * ‖Jc x‖ := hle'
              _ ≤ Kb * ‖Jc x‖ :=
                  mul_le_mul_of_nonneg_right (hfderivbd x (Set.Ico_subset_Icc_self hx)) (norm_nonneg _)
              _ = Kb * ‖Jc x‖ + 0 := by ring)
      have hJcbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ Jbound := by
        intro τ hτ
        have h1 := hJgw τ hτ
        rw [sub_zero, gronwallBound_ε0] at h1
        refine h1.trans ?_
        rw [hJbounddef]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Real.exp_le_exp]
        calc Kb * τ ≤ Kb * 1 := mul_le_mul_of_nonneg_left hτ.2 hKb0
          _ = Kb := mul_one _
      exact ⟨Jc, fun _ => ⟨hJc0, hJcode, hJcbnd, hJcpad⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  set Jf : Point n → ℝ → Point n × Point n := fun δ => Classical.choose (key δ) with hJfdef
  -- The base doubled curve `W 0 = (uniformFlowTube q v, Jf 0)`, padded continuous.
  set W0 : ℝ → (Point n × Point n) × (Point n × Point n) :=
    fun τ => (uniformFlowTube g gi hC hK q (v + 0) τ, Jf 0 τ) with hW0def
  have hP0cont : ContinuousOn (fun τ => uniformFlowTube g gi hC hK q (v + 0) τ)
      (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + 0) hadm0 τ hτoo).continuousAt).continuousWithinAt
  have hJf0pad : ContinuousOn (Jf 0) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    (Classical.choose_spec (key 0) hadm0).2.2.2
  have hW0pad : ContinuousOn W0 (Set.Icc (-(1/2) : ℝ) (3/2)) := hP0cont.prodMk hJf0pad
  -- The doubled-linearized field `V δ` along the fixed base doubled curve `W0`.
  have varkey : ∀ δ : Point n, ∃ Vc : ℝ → (Point n × Point n) × (Point n × Point n),
      Vc 0 = (((0 : Point n), δ), ((0 : Point n), (0 : Point n))) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt Vc (fderiv ℝ (doubledField g gi) (W0 τ) (Vc τ)) τ) := by
    intro δ
    exact doubledVariation_narrowpad_hasDerivAt_Icc g gi hC W0 hW0pad
      (((0 : Point n), δ), ((0 : Point n), (0 : Point n)))
  set Vf : Point n → ℝ → (Point n × Point n) × (Point n × Point n) :=
    fun δ => Classical.choose (varkey δ) with hVfdef
  -- The base-velocity seed CLM `δ ↦ ((0,δ),(0,0))`.
  set seedCLM : Point n →L[ℝ] (Point n × Point n) × (Point n × Point n) :=
    (ContinuousLinearMap.inl ℝ (Point n × Point n) (Point n × Point n)).comp
      (ContinuousLinearMap.inr ℝ (Point n) (Point n)) with hseedCLMdef
  have hseed_eq : ∀ δ : Point n,
      seedCLM δ = (((0 : Point n), δ), ((0 : Point n), (0 : Point n))) := by
    intro δ
    simp [hseedCLMdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, Prod.ext_iff]
  have hseednorm : ∀ δ : Point n, ‖seedCLM δ‖ = ‖δ‖ := by
    intro δ
    rw [hseed_eq δ]
    simp [Prod.norm_def, norm_nonneg]
  -- Discharge the J4-66 hypotheses.
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => (uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t))
        (doubledField g gi (uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ)) τ := by
    intro δ hδ τ hτ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨_, hJcode, _, _⟩ := Classical.choose_spec (key δ) hadm
    have hP := uniformFlowTube_spec_ode g gi hC hK q hq (v + δ) hadm τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact doubledField_prod_hasDerivAt g gi hP (hJcode τ hτ)
  have hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Vf δ) (fderiv ℝ (doubledField g gi) (W0 τ) (Vf δ τ)) τ :=
    fun δ => (Classical.choose_spec (varkey δ)).2
  have hV0 : ∀ δ : Point n, Vf δ 0 = seedCLM δ := by
    intro δ
    rw [hseed_eq δ]
    exact (Classical.choose_spec (varkey δ)).1
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ →
      ((uniformFlowTube g gi hC hK q (v + δ) 0, Jf δ 0) :
          (Point n × Point n) × (Point n × Point n))
        - (uniformFlowTube g gi hC hK q (v + 0) 0, Jf 0 0) = seedCLM δ := by
    intro δ hδ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    have hJfδ0 : Jf δ 0 = ((0 : Point n), b) := (Classical.choose_spec (key δ) hadm).1
    have hJf00 : Jf 0 0 = ((0 : Point n), b) := (Classical.choose_spec (key 0) hadm0).1
    have h1 : uniformFlowTube g gi hC hK q (v + δ) 0 = (q, v + δ) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + δ) hadm
    have h2 : uniformFlowTube g gi hC hK q (v + 0) 0 = (q, v + 0) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + 0) hadm0
    rw [h1, h2, hJfδ0, hJf00, hseed_eq δ]
    simp only [add_zero, Prod.mk_sub_mk, sub_self, add_sub_cancel_left]
    rfl
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ) :
        (Point n × Point n) × (Point n × Point n)) ∈ S := by
    intro δ hδ τ hτ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨_, _, hJcbnd, _⟩ := Classical.choose_spec (key δ) hadm
    rw [hSdef, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖uniformFlowTube g gi hC hK q (v + δ) τ - ((q, 0) : Point n × Point n)‖
          ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) hadm τ hτ
        _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hadm hC₀nn
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hJcbnd τ hτ
  -- Feed J4-66.
  obtain ⟨L, _hLeq, hFD⟩ :=
    doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists g gi hC
      (W := fun δ t => (uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t))
      (V := Vf) (seed := seedCLM) (S := S) (σ := σ)
      hScompact hSconvex hσ ht1 hseednorm hWode hVode hV0 hIC hmem
  refine ⟨Jf, ?_, L, hFD⟩
  intro δ hδ
  obtain ⟨hJc0, hJcode, _, _⟩ := Classical.choose_spec (key δ) (hle δ hδ)
  exact ⟨hJc0, hJcode⟩

/-! ### R2-b — the per-direction Fréchet second-jet of `uniformFlowExp` -/

/-- **R2-b — the per-direction Fréchet second-jet of `uniformFlowExp`.**  For `q ∈ K`, `‖v‖ < ρ_K`, and
    each variation seed `b`, the applied jet map `w ↦ fderiv ℝ (uniformFlowExp g gi hC hK q) w b` has a
    Fréchet derivative at `v`:
        `∃ L₂, HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w b) L₂ v`.
    DERIVED: from R2-a's doubled endpoint Fréchet derivative `L`, project the `.2.1` component; rewrite
    (on the open velocity window `‖δ‖ < ρ_K − ‖v‖ ∈ 𝓝 0`, via `uniformFlowExp_fderiv_apply_eq`) as
    `fderiv (uniformFlowExp q) (v+δ) b`; recentre `δ ↦ v + δ`.  NO `expRho`. -/
theorem uniformFlowExp_fderiv_apply_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (b : Point n) :
    ∃ L₂ : Point n →L[ℝ] Point n,
      HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w b) L₂ v := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  obtain ⟨Jf, hJf, L, hFD⟩ :=
    uniformFlow_doubledEndpoint_baseVelocity_hasFDerivAt g gi hC hK q hq v hv b
  -- Project the `.2.1` component of the doubled endpoint.
  set proj21 : ((Point n × Point n) × (Point n × Point n)) →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp
      (ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)) with hproj21def
  set L₂ : Point n →L[ℝ] Point n := proj21.comp L with hL₂def
  have hFDproj : HasFDerivAt (fun δ => (Jf δ 1).1) L₂ 0 := by
    have hc := proj21.hasFDerivAt.comp (0 : Point n) hFD
    have hfe : (⇑proj21 ∘ fun δ => ((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1) :
        (Point n × Point n) × (Point n × Point n))) = (fun δ => (Jf δ 1).1) := by
      funext δ
      show proj21 (uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1) = (Jf δ 1).1
      simp [hproj21def, ContinuousLinearMap.comp_apply]
    rw [hfe] at hc
    exact hc
  -- On the open velocity window, `(Jf δ 1).1 = fderiv (uniformFlowExp q) (v+δ) b`.
  have hEq : (fun δ => (Jf δ 1).1)
      =ᶠ[𝓝 (0 : Point n)]
      (fun δ => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + δ) b) := by
    have hball : Metric.ball (0 : Point n) σ ∈ 𝓝 (0 : Point n) :=
      Metric.ball_mem_nhds _ hσ
    refine Filter.eventuallyEq_of_mem hball (fun δ hδ => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hδ
    have hδσ : ‖δ‖ ≤ σ := hδ.le
    have hvδ : ‖v + δ‖ < ρ := by
      refine lt_of_le_of_lt (norm_add_le v δ) ?_
      rw [hσdef] at hδ; linarith
    obtain ⟨hJc0, hJcode⟩ := hJf δ hδσ
    exact (uniformFlowExp_fderiv_apply_eq g gi hC hK q hq (v + δ) hvδ b (Jf δ) hJc0 hJcode).symm
  -- transfer the derivative across the eventual equality.
  have hFDproj2 : HasFDerivAt (fun δ => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + δ) b) L₂ 0 :=
    hFDproj.congr_of_eventuallyEq hEq.symm
  -- Recentre `δ ↦ v + δ` (i.e. `w ↦ w − v`).
  have hshift : HasFDerivAt (fun u : Point n => u - v) (ContinuousLinearMap.id ℝ (Point n)) v :=
    (hasFDerivAt_id v).sub_const v
  have hFD0 : HasFDerivAt (fun δ => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + δ) b) L₂ (v - v) := by
    rw [sub_self]; exact hFDproj2
  have hcomp : HasFDerivAt (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + (u - v)) b)
      (L₂.comp (ContinuousLinearMap.id ℝ (Point n))) v :=
    hFD0.comp (f := fun u : Point n => u - v) v hshift
  have hfun2 : (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + (u - v)) b)
      = (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w b) := by
    funext u; congr 2; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  exact ⟨L₂, hcomp⟩

end QIQTH.ExpMap
