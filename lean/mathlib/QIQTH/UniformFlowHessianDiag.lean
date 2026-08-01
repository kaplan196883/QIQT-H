/-
  # UniformFlowHessianDiag — R3 CLOSED: the uniform DIAGONAL Hessian bound for `uniformFlowExp`.

  Brick-A(β) regularity climb.  J4-69 (`UniformFlowHessianBound`) reduced the uniform operator-norm bound
  on the uniform-flow exp Hessian `B₂(q,v) = fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp q) w) v` to a
  UNIFORM DIAGONAL bound `hdiag : ‖B₂ a a‖ ≤ M‖a‖²` (symmetry + polarization ⟹ `‖B₂‖ ≤ 2M`,
  `uniformFlowExp_hessian_opNorm_le_of_diag_bound`).  This file DISCHARGES `hdiag`, closing R3.

  ## What lands (DERIVED; no `sorry`, no hyp = conclusion, no smuggled bound/conclusion, no `expRho`)

  * `doubledField_fderiv_fst_apply` — the first-component block formula `(DG(e)·u).1 = DF(e.1)·u.1`
    (mirror of `doubledField_fderiv_snd_apply`), used to bound the doubled variation field's first factor.

  * `uniformFlowExp_hessian_diag_bound` (**V1 + V2**) — the uniform diagonal bound.  For a fixed base
    point `q ∈ K` and velocity `‖v‖ < ρ_K/2`, build the scalar-`s` two-sided doubled family
        `Y a b s = (uniformFlowTube q (v+s·a), velocity-Jacobi seeded (0,b))`,
    the doubled linearized field `Vf a b` (seed `((0,a),(0,0))`) along `Y a b 0`, and take the
    SECOND-VARIATION field as its second factor `Zf a b := (Vf a b ·).2` — which solves the exact
    inhomogeneous second-variation ODE by `doubledField_secondFactor_ode`.  Feeding these (plus the
    first-jet link `uniformFlowExp_fderiv_apply_eq` for `hlink`, and jet-map differentiability from R2
    `uniformFlowExp_fderiv_hasFDerivAt`) to `hid_of_doubled_data` yields the VALUE identification
        `B₂(q,v) a a = ((Vf a a 1).2).1`.
    A Grönwall bound on `(Vf a a ·).2` (source quadratic in the first variation, ‖·‖ ≤ ‖a‖·e^{C₁}) gives
        `‖(Vf a a 1).2‖ ≤ M·‖a‖²`,  `M = gronwallBound 0 C₁ (C₂·e^{2C₁}) 1`
    uniform over `q ∈ K`, `‖v‖ < ρ_K/2` (`C₁, C₂` are field sups over ONE compact phase ball).  Hence
    `hdiag` with `r₀ = ρ_K/2`.  DERIVED — the value id is `hid_of_doubled_data` (a compiled theorem),
    not assumed; `M` is a genuine uniform constant, not the conclusion.

  * `uniformFlowExp_hessian_opNorm_le` (**V3 — R3 CLOSED, UNCONDITIONAL**) — feeds the diagonal bound to
    `uniformFlowExp_hessian_opNorm_le_of_diag_bound`, giving
        `∃ r₀ > 0, r₀ ≤ ρ_K ∧ ∃ M', ∀ q ∈ K, ∀ ‖v‖ < r₀, ‖B₂(q,v)‖ ≤ M'`
    from ONLY `hC` + `IsCompact K`.  No carried `hdiag`, no `expRho`.

  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.UniformFlowHessianBound
import QIQTH.UniformFlowSecondJet
import QIQTH.UniformFlowSecondSupply
import QIQTH.UniformFlowHessian
import QIQTH.JacobiOperatorFDeriv
import QIQTH.UniformFlowSecondFDeriv
import QIQTH.DoubledVariationField
import QIQTH.DoubledFamilyConstruction
import QIQTH.UniformFlowNondeg
import QIQTH.BoundedGeometry
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-! ### First-component block formula for `DG` -/

/-- **Block formula for the first component of `DG`.**  With `G = doubledField g gi` and
    `F = geodesicField g gi`, the first `State`-component of the Fréchet derivative applied to a direction
    `u` is `(fderiv G e u).1 = DF(e.1)·u.1`.  DERIVED: `(G ·).1 = F ∘ fst` definitionally; project the
    Fréchet derivative of `G` by the `fst` CLM and identify by `HasFDerivAt.unique`. -/
theorem doubledField_fderiv_fst_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (e u : (Point n × Point n) × (Point n × Point n)) :
    ((fderiv ℝ (doubledField g gi) e) u).1
      = fderiv ℝ (geodesicField g gi) e.1 u.1 := by
  have hGdiff : Differentiable ℝ (doubledField g gi) :=
    (contDiff_doubledField g gi hC).differentiable (by simp)
  have hFdiff : Differentiable ℝ (geodesicField g gi) :=
    (contDiff_geodesicField g gi hC).differentiable (by simp)
  have hG : HasFDerivAt (doubledField g gi) (fderiv ℝ (doubledField g gi) e) e :=
    (hGdiff e).hasFDerivAt
  have hproj : HasFDerivAt (fun x => (doubledField g gi x).1)
      ((ContinuousLinearMap.fst ℝ (Point n × Point n) (Point n × Point n)).comp
        (fderiv ℝ (doubledField g gi) e)) e :=
    (ContinuousLinearMap.fst ℝ (Point n × Point n) (Point n × Point n)).hasFDerivAt.comp e hG
  have hF : HasFDerivAt
      (fun x : (Point n × Point n) × (Point n × Point n) => geodesicField g gi x.1)
      ((fderiv ℝ (geodesicField g gi) e.1).comp
        (ContinuousLinearMap.fst ℝ (Point n × Point n) (Point n × Point n))) e :=
    (hFdiff e.1).hasFDerivAt.comp e hasFDerivAt_fst
  have heq : (fun x : (Point n × Point n) × (Point n × Point n) => (doubledField g gi x).1)
      = (fun x => geodesicField g gi x.1) := rfl
  rw [heq] at hproj
  have huniq := hproj.unique hF
  have hval := DFunLike.congr_fun huniq u
  simpa [ContinuousLinearMap.comp_apply] using hval

/-! ### V1 + V2 — the uniform diagonal Hessian bound -/

/-- **V1 + V2 — the uniform DIAGONAL Hessian bound for `uniformFlowExp`.**  There is a uniform velocity
    radius `r₀ = ρ_K/2 > 0` and a uniform constant `M ≥ 0` such that for every `q ∈ K`, every `v` with
    `‖v‖ < r₀`, and every direction `a`,
        `‖(fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v) a a‖ ≤ M · ‖a‖²`.
    Hypotheses ONLY `hC` + `IsCompact K`.  The value identification `B₂ a a = ((Vf a a 1).2).1` is
    `hid_of_doubled_data` (DERIVED, not assumed); `M` is a genuine uniform Grönwall constant.  NO
    `expRho`, NO carried `hdiag`. -/
theorem uniformFlowExp_hessian_diag_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), r₀ ≤ uniformFlowRadius g gi hC hK ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ a : Point n,
        ‖(fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v) a a‖
          ≤ M * ‖a‖ ^ 2 := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- One compact phase ball covering all base tubes for `q ∈ K`, `‖w‖ ≤ ρ`.
  obtain ⟨R, hRsub⟩ := hK.isBounded.subset_closedBall (0 : Point n)
  set Rb : ℝ := max R 0 with hRbdef
  have hRb0 : 0 ≤ Rb := le_max_right _ _
  set RG : ℝ := Rb + C₀ * ρ with hRGdef
  have hRG0 : 0 ≤ RG := by rw [hRGdef]; positivity
  set S₀ : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) RG with hS₀def
  have hS₀c : IsCompact S₀ := isCompact_closedBall _ _
  have h0S₀ : (0 : Point n × Point n) ∈ S₀ := by rw [hS₀def]; exact Metric.mem_closedBall_self hRG0
  -- Uniform field-Jacobian and C²-field sups over `S₀`.
  obtain ⟨C₁, hC₁0, hC₁⟩ := geodesicField_fderiv_bddOn_compact g gi hC hS₀c
  obtain ⟨C₂, hC₂0, hC₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S₀, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
      (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
        (by simp)).norm
    obtain ⟨x, hxS, hx⟩ := hS₀c.exists_isMaxOn ⟨(0 : Point n × Point n), h0S₀⟩ hcontr.continuousOn
    exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
      norm_nonneg _, fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  set E : ℝ := Real.exp C₁ with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  set M : ℝ := gronwallBound 0 C₁ (C₂ * E ^ 2) 1 with hMdef
  have hM0 : 0 ≤ M := by
    have hmono := gronwallBound_mono (δ := 0) (K := C₁) (ε := C₂ * E ^ 2) (le_refl 0)
      (by positivity) hC₁0 (show (0 : ℝ) ≤ 1 by norm_num)
    rwa [gronwallBound_x0] at hmono
  refine ⟨ρ / 2, by positivity, by linarith, M, hM0, ?_⟩
  intro q hq v hv
  have hvρ : ‖v‖ < ρ := lt_trans hv (by linarith)
  -- `‖q‖ ≤ Rb`.
  have hqRb : ‖q‖ ≤ Rb := by
    have := hRsub hq
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact le_trans this (le_max_left _ _)
  -- Tube-into-`S₀` for any admissible base velocity.
  have htubeS₀ : ∀ w : Point n, ‖w‖ ≤ ρ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      uniformFlowTube g gi hC hK q w τ ∈ S₀ := by
    intro w hw τ hτ
    rw [hS₀def, Metric.mem_closedBall, dist_zero_right]
    have hconf : ‖uniformFlowTube g gi hC hK q w τ - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖ :=
      uniformFlowTube_spec_conf g gi hC hK q hq w hw τ hτ
    have hqn : ‖((q, 0) : Point n × Point n)‖ ≤ Rb := by
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg q)]; exact hqRb
    calc ‖uniformFlowTube g gi hC hK q w τ‖
        = ‖(uniformFlowTube g gi hC hK q w τ - ((q, 0) : Point n × Point n)) + ((q, 0) : Point n × Point n)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖uniformFlowTube g gi hC hK q w τ - ((q, 0) : Point n × Point n)‖ + ‖((q, 0) : Point n × Point n)‖ :=
          norm_add_le _ _
      _ ≤ C₀ * ρ + Rb := add_le_add (le_trans hconf (mul_le_mul_of_nonneg_left hw hC₀nn)) hqn
      _ = RG := by rw [hRGdef]; ring
  -- Field-Jacobian bound along a tube.
  have hKbtube : ∀ w : Point n, ‖w‖ ≤ ρ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q w τ)‖ ≤ C₁ :=
    fun w hw τ hτ => hC₁ _ (htubeS₀ w hw τ hτ)
  -- ===== The velocity-window and the per-`(a,b,s)` Jacobi supply. =====
  set σ : Point n → Point n → ℝ := fun a _ => ρ / (4 * (1 + ‖a‖)) with hσdef
  have hσpos : ∀ a b : Point n, 0 < σ a b := fun a b => by rw [hσdef]; exact div_pos hρ0 (by positivity)
  have hwin : ∀ (a : Point n) (s : ℝ), s ∈ Set.Icc (-(σ a a)) (σ a a) → ‖v + s • a‖ < ρ := by
    intro a s hs
    have habs : |s| ≤ σ a a := abs_le.mpr ⟨hs.1, hs.2⟩
    have hσa : σ a a * ‖a‖ ≤ ρ / 4 := by
      have hval : σ a a = ρ / (4 * (1 + ‖a‖)) := by rw [hσdef]
      rw [hval, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg a, hρ0.le]
    have h1 : ‖v + s • a‖ ≤ ‖v‖ + |s| * ‖a‖ := by
      calc ‖v + s • a‖ ≤ ‖v‖ + ‖s • a‖ := norm_add_le _ _
        _ = ‖v‖ + |s| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h2 : |s| * ‖a‖ ≤ σ a a * ‖a‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg a)
    have : ‖v‖ + |s| * ‖a‖ < ρ / 2 + ρ / 4 := by
      have := hv; nlinarith [h2, hσa]
    linarith [h1, this]
  -- Jacobi supply (genuine when `‖v+s•a‖ < ρ`), with Grönwall confinement `‖J‖ ≤ ‖(0,b)‖·E`.
  have hnorm0 : ∀ b : Point n, ‖((0 : Point n), b)‖ = ‖b‖ := by
    intro b; rw [Prod.norm_def]; simp
  have keyJ : ∀ (a b : Point n) (s : ℝ), ∃ Jc : ℝ → Point n × Point n,
      (‖v + s • a‖ < ρ →
        Jc 0 = ((0 : Point n), b) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt Jc
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + s • a) τ) (Jc τ)) τ) ∧
        ContinuousOn Jc (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ ‖((0 : Point n), b)‖ * E)) := by
    intro a b s
    by_cases h : ‖v + s • a‖ < ρ
    · have hle : ‖v + s • a‖ ≤ ρ := h.le
      have hPcont : ContinuousOn (uniformFlowTube g gi hC hK q (v + s • a)) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
        intro τ hτ
        have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + s • a) hle τ hτoo).continuousAt).continuousWithinAt
      obtain ⟨Jc, hJc0, hJcode, hJcpad⟩ :=
        geodesicJacobi_narrowpad_continuousOn g gi hC (uniformFlowTube g gi hC hK q (v + s • a)) hPcont
          ((0 : Point n), b)
      have hJcont : ContinuousOn Jc (Set.Icc (0 : ℝ) 1) :=
        fun τ hτ => (hJcode τ hτ).continuousAt.continuousWithinAt
      have hbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ ‖((0 : Point n), b)‖ * E := by
        intro τ hτ
        have hgw := norm_le_gronwallBound_of_norm_deriv_right_le (f := Jc)
          (f' := fun x => fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + s • a) x) (Jc x))
          (δ := ‖((0 : Point n), b)‖) (K := C₁) (ε := 0) (a := 0) (b := 1) hJcont
          (fun x hx => (hJcode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
          (le_of_eq (by rw [hJc0]))
          (fun x hx => by
            have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
            have hle' := (fderiv ℝ (geodesicField g gi)
              (uniformFlowTube g gi hC hK q (v + s • a) x)).le_opNorm (Jc x)
            calc ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + s • a) x) (Jc x)‖
                ≤ ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + s • a) x)‖ * ‖Jc x‖ := hle'
              _ ≤ C₁ * ‖Jc x‖ :=
                  mul_le_mul_of_nonneg_right (hKbtube _ hle x hxIcc) (norm_nonneg _)
              _ = C₁ * ‖Jc x‖ + 0 := by ring)
          τ hτ
        rw [sub_zero, gronwallBound_ε0] at hgw
        refine hgw.trans ?_
        rw [hEdef]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Real.exp_le_exp]
        calc C₁ * τ ≤ C₁ * 1 := mul_le_mul_of_nonneg_left hτ.2 hC₁0
          _ = C₁ := mul_one _
      exact ⟨Jc, fun _ => ⟨hJc0, hJcode, hJcpad, hbnd⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  set Jf : Point n → Point n → ℝ → ℝ → Point n × Point n :=
    fun a b s => Classical.choose (keyJ a b s) with hJfdef
  -- The scalar-`s` doubled family.
  set Y : Point n → Point n → ℝ → ℝ → (Point n × Point n) × (Point n × Point n) :=
    fun a b s t => (uniformFlowTube g gi hC hK q (v + s • a) t, Jf a b s t) with hYdef
  -- `‖v + 0•a‖ < ρ`.
  have hw0 : ∀ a : Point n, ‖v + (0 : ℝ) • a‖ < ρ := by
    intro a; rw [zero_smul, add_zero]; exact hvρ
  -- The doubled linearized field along `Y a b 0`.
  have keyV : ∀ a b : Point n, ∃ Vc : ℝ → (Point n × Point n) × (Point n × Point n),
      Vc 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt Vc (fderiv ℝ (doubledField g gi) (Y a b 0 τ) (Vc τ)) τ) := by
    intro a b
    have hbasecont : ContinuousOn (Y a b 0) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
      have hPcont : ContinuousOn (uniformFlowTube g gi hC hK q (v + (0 : ℝ) • a))
          (Set.Icc (-(1/2) : ℝ) (3/2)) := by
        intro τ hτ
        have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + (0 : ℝ) • a) (hw0 a).le τ hτoo).continuousAt).continuousWithinAt
      have hJcont : ContinuousOn (Jf a b 0) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
        (Classical.choose_spec (keyJ a b 0) (hw0 a)).2.2.1
      exact hPcont.prodMk hJcont
    exact doubledVariation_narrowpad_hasDerivAt_Icc g gi hC (Y a b 0) hbasecont
      (((0 : Point n), a), ((0 : Point n), (0 : Point n)))
  set Vf : Point n → Point n → ℝ → (Point n × Point n) × (Point n × Point n) :=
    fun a b => Classical.choose (keyV a b) with hVfdef
  set Zf : Point n → Point n → ℝ → Point n × Point n :=
    fun a b τ => (Vf a b τ).2 with hZfdef
  -- ===== Discharge the `hid_of_doubled_data` hypotheses. =====
  -- R2: jet-map differentiability at `v`.
  obtain ⟨B₂, hB₂⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq v hvρ
  have hdiff : DifferentiableAt ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v :=
    hB₂.differentiableAt
  -- hYode.
  have hYode : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y a b s) (doubledField g gi (Y a b s τ)) τ := by
    intro a b s hs τ hτ
    -- Only the diagonal window matters for the bound; use `hwin` at `b = a` via the σ shape.
    have hsρ : ‖v + s • a‖ < ρ := by
      have : σ a b = σ a a := by rw [hσdef]
      rw [this] at hs; exact hwin a s hs
    obtain ⟨hJc0, hJcode, _, _⟩ := Classical.choose_spec (keyJ a b s) hsρ
    have hP := uniformFlowTube_spec_ode g gi hC hK q hq (v + s • a) hsρ.le τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact doubledField_prod_hasDerivAt g gi hP (hJcode τ hτ)
  -- hVode / hV0.
  have hVode : ∀ a b : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Vf a b) (fderiv ℝ (doubledField g gi) (Y a b 0 τ) (Vf a b τ)) τ :=
    fun a b => (Classical.choose_spec (keyV a b)).2
  have hV0 : ∀ a b : Point n, Vf a b 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))) :=
    fun a b => (Classical.choose_spec (keyV a b)).1
  -- hIC.
  have hIC : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b),
      Y a b s 0 - Y a b 0 0 = s • (((0 : Point n), a), ((0 : Point n), (0 : Point n))) := by
    intro a b s hs
    have hsρ : ‖v + s • a‖ < ρ := by
      have : σ a b = σ a a := by rw [hσdef]
      rw [this] at hs; exact hwin a s hs
    have hJfs0 : Jf a b s 0 = ((0 : Point n), b) := (Classical.choose_spec (keyJ a b s) hsρ).1
    have hJf00 : Jf a b 0 0 = ((0 : Point n), b) := (Classical.choose_spec (keyJ a b 0) (hw0 a)).1
    have h1 : uniformFlowTube g gi hC hK q (v + s • a) 0 = (q, v + s • a) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + s • a) hsρ.le
    have h2 : uniformFlowTube g gi hC hK q (v + (0 : ℝ) • a) 0 = (q, v + (0 : ℝ) • a) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + (0 : ℝ) • a) (hw0 a).le
    show (uniformFlowTube g gi hC hK q (v + s • a) 0, Jf a b s 0)
        - (uniformFlowTube g gi hC hK q (v + (0 : ℝ) • a) 0, Jf a b 0 0) = _
    rw [h1, h2, hJfs0, hJf00, zero_smul, add_zero]
    simp only [Prod.mk_sub_mk, sub_self, add_sub_cancel_left, Prod.smul_mk, smul_zero,
      Prod.mk_zero_zero]
  -- hmem.
  set S : Point n → Point n → Set ((Point n × Point n) × (Point n × Point n)) :=
    fun _ b => Metric.closedBall (0 : (Point n × Point n) × (Point n × Point n)) (RG + ‖b‖ * E)
    with hSdef
  have hScompact : ∀ a b : Point n, IsCompact (S a b) := fun a b => isCompact_closedBall _ _
  have hSconvex : ∀ a b : Point n, Convex ℝ (S a b) := fun a b => convex_closedBall _ _
  have hmem : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Y a b s τ ∈ S a b := by
    intro a b s hs τ hτ
    have hsρ : ‖v + s • a‖ < ρ := by
      have : σ a b = σ a a := by rw [hσdef]
      rw [this] at hs; exact hwin a s hs
    obtain ⟨_, _, _, hJcbnd⟩ := Classical.choose_spec (keyJ a b s) hsρ
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]
    have htube : ‖uniformFlowTube g gi hC hK q (v + s • a) τ‖ ≤ RG := by
      have := htubeS₀ (v + s • a) hsρ.le τ hτ
      rw [hS₀def, Metric.mem_closedBall, dist_zero_right] at this; exact this
    have hJ : ‖Jf a b s τ‖ ≤ ‖b‖ * E := (hJcbnd τ hτ).trans_eq (by rw [hnorm0 b])
    show ‖(uniformFlowTube g gi hC hK q (v + s • a) τ, Jf a b s τ)‖ ≤ RG + ‖b‖ * E
    rw [Prod.norm_def]
    apply max_le
    · linarith [htube, mul_nonneg (norm_nonneg b) hE0.le]
    · linarith [hJ, hRG0]
  -- hlink (via the R2-b enabler).
  have hlink : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b),
      (Y a b s 1).2.1 = fderiv ℝ (uniformFlowExp g gi hC hK q) (v + s • a) b := by
    intro a b s hs
    have hsρ : ‖v + s • a‖ < ρ := by
      have : σ a b = σ a a := by rw [hσdef]
      rw [this] at hs; exact hwin a s hs
    obtain ⟨hJc0, hJcode, _, _⟩ := Classical.choose_spec (keyJ a b s) hsρ
    show (Jf a b s 1).1 = fderiv ℝ (uniformFlowExp g gi hC hK q) (v + s • a) b
    exact (uniformFlowExp_fderiv_apply_eq g gi hC hK q hq (v + s • a) hsρ b (Jf a b s) hJc0 hJcode).symm
  -- hZf (Zf = second factor of Vf, via `doubledField_secondFactor_ode`).
  have hZf : ∀ a b : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ => Zf a b τ)
        (fderiv ℝ (geodesicField g gi) (Y a b 0 τ).1 (Zf a b τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a b 0 τ).1 (Vf a b τ).1 (Y a b 0 τ).2) τ := by
    intro a b τ hτ
    exact doubledField_secondFactor_ode g gi hC (hVode a b) τ hτ
  -- h0 / hKb.
  have h0 : ∀ a b : Point n, (Vf a b 0).2 = Zf a b 0 := fun a b => rfl
  have hKb : ∀ a b : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y a b 0 τ).1‖ ≤ C₁ := by
    intro a b τ hτ
    show ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + (0 : ℝ) • a) τ)‖ ≤ C₁
    exact hKbtube _ (hw0 a).le τ hτ
  -- ===== Feed `hid_of_doubled_data`. =====
  have hhid := hid_of_doubled_data g gi hC
    (Fam := uniformFlowExp g gi hC hK q) (Zf := Zf) (v := v) (σ := σ) (S := S)
    hC₁0 hσpos hScompact hSconvex Y Vf hdiff hYode hVode hV0 hIC hmem hlink hZf h0 hKb
  -- ===== The Grönwall bound on the diagonal second-variation endpoint. =====
  intro a
  -- First factor `U = (Vf a a ·).1` is a velocity Jacobi field seeded `(0,a)`: `‖U τ‖ ≤ ‖a‖·E`.
  set U : ℝ → Point n × Point n := fun τ => (Vf a a τ).1 with hUdef
  have hUode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt U (fderiv ℝ (geodesicField g gi) (Y a a 0 τ).1 (U τ)) τ := by
    intro τ hτ
    have hproj := (ContinuousLinearMap.fst ℝ (Point n × Point n)
      (Point n × Point n)).hasFDerivAt.comp_hasDerivAt τ (hVode a a τ hτ)
    have hval : (fderiv ℝ (doubledField g gi) (Y a a 0 τ) (Vf a a τ)).1
        = fderiv ℝ (geodesicField g gi) (Y a a 0 τ).1 (Vf a a τ).1 :=
      doubledField_fderiv_fst_apply g gi hC (Y a a 0 τ) (Vf a a τ)
    have hproj2 : HasDerivAt U ((fderiv ℝ (doubledField g gi) (Y a a 0 τ) (Vf a a τ)).1) τ := hproj
    rw [hval] at hproj2
    exact hproj2
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hUode τ hτ).continuousAt.continuousWithinAt
  have hU0 : U 0 = ((0 : Point n), a) := by
    show (Vf a a 0).1 = ((0 : Point n), a); rw [hV0 a a]
  have hbaseS₀ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (Y a a 0 τ).1 ∈ S₀ := by
    intro τ hτ
    show uniformFlowTube g gi hC hK q (v + (0 : ℝ) • a) τ ∈ S₀
    exact htubeS₀ _ (hw0 a).le τ hτ
  have hUbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖U τ‖ ≤ ‖a‖ * E := by
    intro τ hτ
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le (f := U)
      (f' := fun x => fderiv ℝ (geodesicField g gi) (Y a a 0 x).1 (U x))
      (δ := ‖((0 : Point n), a)‖) (K := C₁) (ε := 0) (a := 0) (b := 1) hUcont
      (fun x hx => (hUode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (le_of_eq (by rw [hU0]))
      (fun x hx => by
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
        have hle' := (fderiv ℝ (geodesicField g gi) (Y a a 0 x).1).le_opNorm (U x)
        calc ‖fderiv ℝ (geodesicField g gi) (Y a a 0 x).1 (U x)‖
            ≤ ‖fderiv ℝ (geodesicField g gi) (Y a a 0 x).1‖ * ‖U x‖ := hle'
          _ ≤ C₁ * ‖U x‖ := mul_le_mul_of_nonneg_right (hC₁ _ (hbaseS₀ x hxIcc)) (norm_nonneg _)
          _ = C₁ * ‖U x‖ + 0 := by ring)
      τ hτ
    rw [sub_zero, gronwallBound_ε0, hnorm0 a] at hgw
    refine hgw.trans ?_
    rw [hEdef]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.exp_le_exp]
    calc C₁ * τ ≤ C₁ * 1 := mul_le_mul_of_nonneg_left hτ.2 hC₁0
      _ = C₁ := mul_one _
  -- Jacobi factor `(Y a a 0 ·).2 = Jf a a 0`: `‖·‖ ≤ ‖a‖·E`.
  have hJbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖(Y a a 0 τ).2‖ ≤ ‖a‖ * E := by
    intro τ hτ
    exact ((Classical.choose_spec (keyJ a a 0) (hw0 a)).2.2.2 τ hτ).trans_eq (by rw [hnorm0 a])
  -- Second factor `Z2 = (Vf a a ·).2 = Zf a a`: Grönwall with quadratic source.
  set Z2 : ℝ → Point n × Point n := fun τ => (Vf a a τ).2 with hZ2def
  have hZ2ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Z2 (fderiv ℝ (geodesicField g gi) (Y a a 0 τ).1 (Z2 τ)
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 τ).1 (U τ) (Y a a 0 τ).2) τ := by
    intro τ hτ
    exact doubledField_secondFactor_ode g gi hC (hVode a a) τ hτ
  have hZ2cont : ContinuousOn Z2 (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hZ2ode τ hτ).continuousAt.continuousWithinAt
  have hZ20 : Z2 0 = 0 := by
    show (Vf a a 0).2 = 0; rw [hV0 a a]; rfl
  set ε : ℝ := C₂ * (‖a‖ * E) ^ 2 with hεdef
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hZ2bnd : ‖Z2 1‖ ≤ M * ‖a‖ ^ 2 := by
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le (f := Z2)
      (f' := fun x => fderiv ℝ (geodesicField g gi) (Y a a 0 x).1 (Z2 x)
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1 (U x) (Y a a 0 x).2)
      (δ := 0) (K := C₁) (ε := ε) (a := 0) (b := 1) hZ2cont
      (fun x hx => (hZ2ode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (by rw [hZ20]; simp)
      (fun x hx => by
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
        have hsrc : ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1 (U x) (Y a a 0 x).2‖
            ≤ ε := by
          have h1 := (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1).le_opNorm (U x)
          have h2 := ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1) (U x)).le_opNorm
            (Y a a 0 x).2
          have hstep : ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1 (U x) (Y a a 0 x).2‖
              ≤ C₂ * ‖U x‖ * ‖(Y a a 0 x).2‖ := by
            calc ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1 (U x) (Y a a 0 x).2‖
                ≤ ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1 (U x)‖ * ‖(Y a a 0 x).2‖ := h2
              _ ≤ (‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1‖ * ‖U x‖) * ‖(Y a a 0 x).2‖ :=
                  mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
              _ = ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1‖ * ‖U x‖ * ‖(Y a a 0 x).2‖ := by ring
              _ ≤ C₂ * ‖U x‖ * ‖(Y a a 0 x).2‖ :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (hC₂ _ (hbaseS₀ x hxIcc)) (norm_nonneg _)) (norm_nonneg _)
          refine hstep.trans ?_
          rw [hεdef]
          have hU := hUbnd x hxIcc
          have hJ := hJbnd x hxIcc
          have hprod : ‖U x‖ * ‖(Y a a 0 x).2‖ ≤ (‖a‖ * E) * (‖a‖ * E) :=
            mul_le_mul hU hJ (norm_nonneg _) (by positivity)
          calc C₂ * ‖U x‖ * ‖(Y a a 0 x).2‖ = C₂ * (‖U x‖ * ‖(Y a a 0 x).2‖) := by ring
            _ ≤ C₂ * ((‖a‖ * E) * (‖a‖ * E)) := mul_le_mul_of_nonneg_left hprod hC₂0
            _ = C₂ * (‖a‖ * E) ^ 2 := by ring
        calc ‖fderiv ℝ (geodesicField g gi) (Y a a 0 x).1 (Z2 x)
              + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1 (U x) (Y a a 0 x).2‖
            ≤ ‖fderiv ℝ (geodesicField g gi) (Y a a 0 x).1 (Z2 x)‖
              + ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a a 0 x).1 (U x) (Y a a 0 x).2‖ :=
              norm_add_le _ _
          _ ≤ C₁ * ‖Z2 x‖ + ε :=
              add_le_add
                (le_trans ((fderiv ℝ (geodesicField g gi) (Y a a 0 x).1).le_opNorm (Z2 x))
                  (mul_le_mul_of_nonneg_right (hC₁ _ (hbaseS₀ x hxIcc)) (norm_nonneg _)))
                hsrc)
      1 (Set.right_mem_Icc.mpr (by norm_num))
    rw [sub_zero] at hgw
    -- `gronwallBound 0 C₁ ε 1 = M * ‖a‖²`.
    have hεeq : ε = ‖a‖ ^ 2 * (C₂ * E ^ 2) := by rw [hεdef]; ring
    calc ‖Z2 1‖ ≤ gronwallBound 0 C₁ ε 1 := hgw
      _ = gronwallBound 0 C₁ (‖a‖ ^ 2 * (C₂ * E ^ 2)) 1 := by rw [hεeq]
      _ = ‖a‖ ^ 2 * gronwallBound 0 C₁ (C₂ * E ^ 2) 1 :=
          gronwallBound_zero_mul_ε C₁ 1 (‖a‖ ^ 2) (C₂ * E ^ 2)
      _ = M * ‖a‖ ^ 2 := by rw [hMdef]; ring
  -- Assemble: value id (hid) + endpoint bound.
  have hval : (fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v) a a = (Zf a a 1).1 :=
    hhid a a
  calc ‖(fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v) a a‖
      = ‖(Zf a a 1).1‖ := by rw [hval]
    _ = ‖(Z2 1).1‖ := rfl
    _ ≤ ‖Z2 1‖ := by
        rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ M * ‖a‖ ^ 2 := hZ2bnd

/-! ### V3 — R3 CLOSED, unconditional -/

/-- **V3 — R3 CLOSED (unconditional).**  The UNIFORM operator-norm bound on the uniform-flow exp Hessian
    over a compact base set, from ONLY `hC` (Christoffel `C^∞`) + `IsCompact K`:
        `∃ r₀ > 0, r₀ ≤ ρ_K ∧ ∃ M', ∀ q ∈ K, ∀ ‖v‖ < r₀,
            ‖fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v‖ ≤ M'`.
    DERIVED by feeding the uniform diagonal bound `uniformFlowExp_hessian_diag_bound` to the polarization
    assembly `uniformFlowExp_hessian_opNorm_le_of_diag_bound` (J4-69).  NO carried `hdiag`, NO `expRho`. -/
theorem uniformFlowExp_hessian_opNorm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), r₀ ≤ uniformFlowRadius g gi hC hK ∧ ∃ M' : ℝ,
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
        ‖fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v‖ ≤ M' := by
  obtain ⟨r₀, hr₀0, hr₀ρ, M, hM0, hdiag⟩ := uniformFlowExp_hessian_diag_bound g gi hC hK
  obtain ⟨M', hM'⟩ :=
    uniformFlowExp_hessian_opNorm_le_of_diag_bound g gi hC hK hM0 hr₀ρ
      (fun q hq v hv a => hdiag q hq v hv a)
  exact ⟨r₀, hr₀0, hr₀ρ, M', hM'⟩

end QIQTH.ExpMap
