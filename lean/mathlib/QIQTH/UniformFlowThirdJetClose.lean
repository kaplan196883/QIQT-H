/-
  UniformFlowThirdJetClose — J4-74 (Brick-A β, C³ climb): the VALUE-IDENTITY (Z1) and the closure of W2.

  ## Context

  * J4-73 (`QuadrupleFlowSupply`, `uniformFlow_quadrupleEndpoint_component_hasFDerivAt`) delivers the
    base-velocity Fréchet derivative of the doubled-linearized endpoint's `.2.1` component: for `q ∈ K`,
    `‖v‖ < ρ_K`, seeds `a b`, families `Jf δ` (velocity-Jacobi, seed `(0,b)`, along `uniformFlowTube q (v+δ)`)
    and `Uf δ` (`doubledField`-linearized, seed `((0,a),(0,0))`, along `(uniformFlowTube q (v+δ), Jf δ)`),
    there is `L₃` with `HasFDerivAt (fun δ => (Uf δ 1).2.1) L₃ 0`.
  * J4-70 (`UniformFlowHessianDiag`) established, at a fixed base velocity, the value identification
    `hid_of_doubled_data` bridging the doubled second-variation endpoint to the Hessian jet
    `B₂ = fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u)`.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no `expRho`)

  * `uniformFlowExp_hessian_value_id` (**Z1, the value-identity**) — for any admissible base velocity `v`
    (`‖v‖ < ρ_K`), seeds `a b`, and ANY genuine velocity-Jacobi field `J` (seed `(0,b)` along
    `uniformFlowTube q v`) and doubled-linearized field `U` (seed `((0,a),(0,0))` along
    `(uniformFlowTube q v, J)`),
        `(fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) v) a b = (U 1).2.1`.
    DERIVED: build the scalar-`s` doubled supply at velocity `v` (à la J4-70), feed
    `hid_of_doubled_data` to get `B₂ v a b = (Vf a b 1).2.1` for the constructed `Vf a b`, then IDENTIFY
    the constructed field's endpoint with the given `U`'s via ODE uniqueness — `jacobiSol_unique`
    (the Jacobi factors agree along the shared tube) then `autonomousLinODE_unique` (the
    `doubledField`-linearized fields agree along the shared base curve, same seed).  The value id is
    `hid_of_doubled_data` (a compiled theorem), not assumed.  Slot order: `B₂ · a b` with `a` the
    base-velocity (`Uf` seed) direction and `b` the Jacobi (`Jf` seed) direction — matches J4-73 exactly,
    NO symmetry bridge needed.

  * `uniformFlow_thirdJet_hasFDerivAt` (**W2, the per-seed THIRD jet**) — for `q ∈ K`, `‖v‖ < ρ_K`,
    seeds `a b`,
        `∃ L₃, HasFDerivAt (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) a b) L₃ v`.
    DERIVED by transferring J4-73's `HasFDerivAt (fun δ => (Uf δ 1).2.1) L₃ 0` across the eventual
    equality `(Uf δ 1).2.1 = B₂ (v+δ) a b` (Z1 on the open velocity window `‖δ‖ < ρ_K − ‖v‖ ∈ 𝓝 0`) via
    `HasFDerivAt.congr_of_eventuallyEq`, then recentring `δ ↦ v + δ` exactly as R2-b recentred R2-a.
    W2 CLOSED.  NO `expRho`.

  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.  W3 (uniform `‖B₃‖` bound) and W4
  (`uniformFlowExp ∈ C³ ⟹ g̃ ∈ C²`) remain the next steps.
-/
import QIQTH.QuadrupleFlowSupply
import QIQTH.UniformFlowHessianDiag
import QIQTH.UniformFlowHessianBound
import QIQTH.UniformFlowHessian
import QIQTH.JacobiOperatorFDeriv
import QIQTH.UniformFlowSecondFDeriv
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

variable {n : ℕ}

/-! ### Z1 — the value-identity: the doubled-linearized endpoint `.2.1` IS the Hessian jet `B₂ a b` -/

/-- **Z1 — the value-identity.**  For a base point `q ∈ K`, an admissible base velocity `v`
    (`‖v‖ < ρ_K`), seeds `a b`, and a genuine velocity-Jacobi field `J` (seed `(0,b)`, along the tube
    `uniformFlowTube q v`) together with a genuine `doubledField`-linearized field `U` (seed
    `((0,a),(0,0))`, along the doubled base curve `(uniformFlowTube q v, J)`),
        `(fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) v) a b = (U 1).2.1`.
    DERIVED via `hid_of_doubled_data` (built at velocity `v`) plus the ODE-uniqueness identification of
    the constructed doubled variation field's endpoint with `U 1`.  The slot order is `B₂ · a b`
    (`a` = base-velocity `U`-seed direction, `b` = Jacobi `J`-seed direction). -/
theorem uniformFlowExp_hessian_value_id (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b : Point n)
    (J : ℝ → Point n × Point n)
    (hJ0 : J 0 = ((0 : Point n), b))
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (J τ)) τ)
    (U : ℝ → (Point n × Point n) × (Point n × Point n))
    (hU0 : U 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))))
    (hUode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt U
        (fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q v τ, J τ) (U τ)) τ) :
    (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) v) a b = (U 1).2.1 := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  have hvρ : ‖v‖ < ρ := hv
  -- One compact phase ball covering all base tubes for `q ∈ K`, `‖w‖ ≤ ρ`.
  obtain ⟨R, hRsub⟩ := hK.isBounded.subset_closedBall (0 : Point n)
  set Rb : ℝ := max R 0 with hRbdef
  have hRb0 : 0 ≤ Rb := le_max_right _ _
  set RG : ℝ := Rb + C₀ * ρ with hRGdef
  have hRG0 : 0 ≤ RG := by rw [hRGdef]; positivity
  set S₀ : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) RG with hS₀def
  have hS₀c : IsCompact S₀ := isCompact_closedBall _ _
  obtain ⟨C₁, hC₁0, hC₁⟩ := geodesicField_fderiv_bddOn_compact g gi hC hS₀c
  set E : ℝ := Real.exp C₁ with hEdef
  have hE0 : 0 < E := Real.exp_pos _
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
  set σ : Point n → Point n → ℝ := fun a _ => (ρ - ‖v‖) / (2 * (1 + ‖a‖)) with hσdef
  have hσpos : ∀ a b : Point n, 0 < σ a b := fun a b => by
    rw [hσdef]; exact div_pos (by linarith) (by positivity)
  have hwin : ∀ (a : Point n) (s : ℝ), s ∈ Set.Icc (-(σ a a)) (σ a a) → ‖v + s • a‖ < ρ := by
    intro a s hs
    have habs : |s| ≤ σ a a := abs_le.mpr ⟨hs.1, hs.2⟩
    have hσa : σ a a * ‖a‖ ≤ (ρ - ‖v‖) / 2 := by
      have hval : σ a a = (ρ - ‖v‖) / (2 * (1 + ‖a‖)) := by rw [hσdef]
      rw [hval, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg a, (show (0 : ℝ) < ρ - ‖v‖ by linarith)]
    have h1 : ‖v + s • a‖ ≤ ‖v‖ + |s| * ‖a‖ := by
      calc ‖v + s • a‖ ≤ ‖v‖ + ‖s • a‖ := norm_add_le _ _
        _ = ‖v‖ + |s| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h2 : |s| * ‖a‖ ≤ σ a a * ‖a‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg a)
    linarith [h1, h2, hσa]
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
  set Y : Point n → Point n → ℝ → ℝ → (Point n × Point n) × (Point n × Point n) :=
    fun a b s t => (uniformFlowTube g gi hC hK q (v + s • a) t, Jf a b s t) with hYdef
  have hw0 : ∀ a : Point n, ‖v + (0 : ℝ) • a‖ < ρ := by
    intro a; rw [zero_smul, add_zero]; exact hvρ
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
  obtain ⟨B₂, hB₂⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq v hvρ
  have hdiff : DifferentiableAt ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v :=
    hB₂.differentiableAt
  have hYode : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y a b s) (doubledField g gi (Y a b s τ)) τ := by
    intro a b s hs τ hτ
    have hsρ : ‖v + s • a‖ < ρ := by
      have : σ a b = σ a a := by rw [hσdef]
      rw [this] at hs; exact hwin a s hs
    obtain ⟨hJc0, hJcode, _, _⟩ := Classical.choose_spec (keyJ a b s) hsρ
    have hP := uniformFlowTube_spec_ode g gi hC hK q hq (v + s • a) hsρ.le τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact doubledField_prod_hasDerivAt g gi hP (hJcode τ hτ)
  have hVode : ∀ a b : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Vf a b) (fderiv ℝ (doubledField g gi) (Y a b 0 τ) (Vf a b τ)) τ :=
    fun a b => (Classical.choose_spec (keyV a b)).2
  have hV0 : ∀ a b : Point n, Vf a b 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))) :=
    fun a b => (Classical.choose_spec (keyV a b)).1
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
  have hlink : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b),
      (Y a b s 1).2.1 = fderiv ℝ (uniformFlowExp g gi hC hK q) (v + s • a) b := by
    intro a b s hs
    have hsρ : ‖v + s • a‖ < ρ := by
      have : σ a b = σ a a := by rw [hσdef]
      rw [this] at hs; exact hwin a s hs
    obtain ⟨hJc0, hJcode, _, _⟩ := Classical.choose_spec (keyJ a b s) hsρ
    show (Jf a b s 1).1 = fderiv ℝ (uniformFlowExp g gi hC hK q) (v + s • a) b
    exact (uniformFlowExp_fderiv_apply_eq g gi hC hK q hq (v + s • a) hsρ b (Jf a b s) hJc0 hJcode).symm
  have hZf : ∀ a b : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ => Zf a b τ)
        (fderiv ℝ (geodesicField g gi) (Y a b 0 τ).1 (Zf a b τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a b 0 τ).1 (Vf a b τ).1 (Y a b 0 τ).2) τ := by
    intro a b τ hτ
    exact doubledField_secondFactor_ode g gi hC (hVode a b) τ hτ
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
  -- ===== Uniqueness identification: the constructed `Vf a b 1 = U 1`. =====
  -- Step A: the internal Jacobi factor `Jf a b 0` equals `J` on `[0,1]` (`jacobiSol_unique`).
  have htube0 : uniformFlowTube g gi hC hK q (v + (0 : ℝ) • a) = uniformFlowTube g gi hC hK q v := by
    rw [zero_smul, add_zero]
  obtain ⟨hJc0', hJcode', _, _⟩ := Classical.choose_spec (keyJ a b 0) (hw0 a)
  have hJf00ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Jf a b 0)
        (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (Jf a b 0 τ)) τ := by
    intro τ hτ
    rw [← htube0]
    exact hJcode' τ hτ
  have hJeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, J τ = Jf a b 0 τ := by
    intro τ hτ
    refine jacobiSol_unique g gi hC₁0
      (Y0 := uniformFlowTube g gi hC hK q v) (J₁ := J) (J₂ := Jf a b 0)
      (fun t ht => ?_) (fun t ht => ?_) hJode hJf00ode ?_ hτ
    · exact uniformFlowTube_spec_ode g gi hC hK q hq v hvρ.le t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact hKbtube v hvρ.le t ht
    · rw [hJ0]; exact hJc0'.symm
  -- The shared base doubled curve `Y a b 0 τ = (uniformFlowTube q v τ, J τ)` on `[0,1]`.
  have hbase : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Y a b 0 τ = (uniformFlowTube g gi hC hK q v τ, J τ) := by
    intro τ hτ
    show (uniformFlowTube g gi hC hK q (v + (0 : ℝ) • a) τ, Jf a b 0 τ)
        = (uniformFlowTube g gi hC hK q v τ, J τ)
    rw [htube0, (hJeq τ hτ)]
  -- Step B: the constructed `Vf a b` and the given `U` are equal on `[0,1]` (`autonomousLinODE_unique`).
  -- Bound `‖D(doubledField)(Y a b 0 τ)‖ ≤ Kd` over the compact confinement `S a b`.
  obtain ⟨Kd, hKd0, hKdbd⟩ := doubledField_fderiv_bddOn_compact g gi hC (hScompact a b)
  have hmem0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y a b 0 τ ∈ S a b :=
    hmem a b 0 (Set.mem_Icc.mpr ⟨by linarith [hσpos a b], (hσpos a b).le⟩)
  have hY0ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y a b 0) (doubledField g gi (Y a b 0 τ)) τ :=
    hYode a b 0 (Set.mem_Icc.mpr ⟨by linarith [hσpos a b], (hσpos a b).le⟩)
  have hKbd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (doubledField g gi) (Y a b 0 τ)‖ ≤ Kd :=
    fun τ hτ => hKdbd (Y a b 0 τ) (hmem0 τ hτ)
  have hUode' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt U (fderiv ℝ (doubledField g gi) (Y a b 0 τ) (U τ)) τ := by
    intro τ hτ
    have := hUode τ hτ
    rwa [← hbase τ hτ] at this
  have hVeqU : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Vf a b τ = U τ := by
    intro τ hτ
    refine autonomousLinODE_unique (doubledField g gi) hKd0
      (Y0 := Y a b 0) (J₁ := Vf a b) (J₂ := U)
      hY0ode hKbd (hVode a b) hUode' ?_ hτ
    rw [hV0 a b, hU0]
  -- ===== Assemble. =====
  have hval : (fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v) a b = (Zf a b 1).1 :=
    hhid a b
  rw [hval]
  show (Vf a b 1).2.1 = (U 1).2.1
  rw [hVeqU 1 (Set.right_mem_Icc.mpr zero_le_one)]

/-! ### W2 — the per-seed THIRD jet (closed) -/

/-- **W2 — the per-seed third jet of `uniformFlowExp`.**  For `q ∈ K`, `‖v‖ < ρ_K`, and seeds `a b`,
    the applied Hessian jet `w ↦ (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) a b` is Fréchet-
    differentiable at `v`:
        `∃ L₃, HasFDerivAt (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) a b) L₃ v`.
    DERIVED by transferring J4-73's `HasFDerivAt (fun δ => (Uf δ 1).2.1) L₃ 0` across the eventual
    equality `(Uf δ 1).2.1 = B₂ (v+δ) a b` (Z1 on the open window `‖δ‖ < ρ_K − ‖v‖ ∈ 𝓝 0`) then
    recentring `δ ↦ v + δ`.  NO `expRho`. -/
theorem uniformFlow_thirdJet_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b : Point n) :
    ∃ L₃ : Point n →L[ℝ] Point n,
      HasFDerivAt
        (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) a b) L₃ v := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  obtain ⟨Jf, Uf, hprops, L₃, hFD⟩ :=
    uniformFlow_quadrupleEndpoint_component_hasFDerivAt g gi hC hK q hq v hv a b
  -- Z1 on the open velocity window: `(Uf δ 1).2.1 = B₂ (v+δ) a b`.
  have hEq : (fun δ => (Uf δ 1).2.1)
      =ᶠ[𝓝 (0 : Point n)]
      (fun δ => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + δ)) a b) := by
    have hball : Metric.ball (0 : Point n) σ ∈ 𝓝 (0 : Point n) := Metric.ball_mem_nhds _ hσ
    refine Filter.eventuallyEq_of_mem hball (fun δ hδ => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hδ
    have hδσ : ‖δ‖ ≤ ρ - ‖v‖ := by rw [← hσdef]; exact hδ.le
    have hvδ : ‖v + δ‖ < ρ := by
      refine lt_of_le_of_lt (norm_add_le v δ) ?_
      rw [hσdef] at hδ; linarith
    obtain ⟨hJf0, hJfode, hUf0, hUfode⟩ := hprops δ hδσ
    exact (uniformFlowExp_hessian_value_id g gi hC hK q hq (v + δ) hvδ a b
      (Jf δ) hJf0 hJfode (Uf δ) hUf0 hUfode).symm
  -- Transfer the derivative across the eventual equality.
  have hFD2 : HasFDerivAt
      (fun δ => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + δ)) a b) L₃ 0 :=
    hFD.congr_of_eventuallyEq hEq.symm
  -- Recentre `δ ↦ v + δ` (i.e. `w ↦ w − v`).
  have hshift : HasFDerivAt (fun u : Point n => u - v) (ContinuousLinearMap.id ℝ (Point n)) v :=
    (hasFDerivAt_id v).sub_const v
  have hFD0 : HasFDerivAt
      (fun δ => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + δ)) a b) L₃
      (v - v) := by
    rw [sub_self]; exact hFD2
  have hcomp : HasFDerivAt
      (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + (w - v))) a b)
      (L₃.comp (ContinuousLinearMap.id ℝ (Point n))) v :=
    hFD0.comp (f := fun w : Point n => w - v) v hshift
  have hfun2 : (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + (w - v))) a b)
      = (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) a b) := by
    funext w; congr 3; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  exact ⟨L₃, hcomp⟩

end QIQTH.ExpMap
