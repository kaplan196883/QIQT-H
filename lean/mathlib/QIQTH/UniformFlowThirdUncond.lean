/-
  UniformFlowThirdUncond — J4-78 (Brick-A β, C³ climb): the CUBIC diagonal bound on the third jet
  `B₃` of `uniformFlowExp`, closing **W3 UNCONDITIONAL** via the COMPARISON-FIELD route.

  ## Context

  * W1 (`UniformFlowThirdJet`, `uniformFlowTube_thirdVariation_uniform_bound`) — the intrinsic THIRD-
    variation field `Z₃` along the base tube with a UNIFORM cubic bound `‖Z₃ τ‖ ≤ M₃j·‖a‖³`, plus the
    first/second-variation fields `V`, `W` and their within-`[0,1]` ODEs.
  * J4-73 (`QuadrupleFlowSupply`, `uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt`) — the base-
    velocity Fréchet first-jet of the QUADRUPLED-flow endpoint (`Φ̃ = genericDoubled (doubledField)`),
    which DISCARDS the engine's `L δ = V δ 1` clause.
  * J4-77 (`UniformFlowThirdDiag`, `uniformFlowExp_thirdDeriv_diag_value_perSeed`) — the diagonal value
    id `B₃ a a a = L₃ a` with `L₃` the per-seed W2 jet.
  * J4-76 (`UniformFlowThirdBoundClose`, `uniformFlowExp_thirdDeriv_opNorm_le_of_diag_bound`) — the
    trilinear polarization bound `hdiag ⟹ ‖B₃‖ ≤ (9/2)M`, CONDITIONAL on the diagonal cubic bound.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no `expRho`)

  * `genericDoubled_fderiv_fst_apply` / `genericDoubled_fderiv_snd_apply` — the field-agnostic block
    formulas for `D(genericDoubled Φ)` (mirror of `doubledField_fderiv_{fst,snd}_apply` one level up).
  * `fderiv_fderiv_doubledField_apply` (+ `_fst` / `_snd` corollaries) — the `D²(doubledField)` applied
    block formula in terms of `D²F`, `D³F` (`F = geodesicField`).
  * `autonomousLinODE_within_unique` — abstract linearized-ODE uniqueness with `HasDerivWithinAt` fields
    on `[0,1]` (within variant of `autonomousLinODE_unique`).
  * `doubledPair_hasDerivWithinAt` — `(V,W)` (first + second variation) solves the `doubledField`-
    linearized ODE along `(Y, V)`.
  * `comparisonField_hasDerivWithinAt` — the packed comparison field `Xcmp = ((V,W),(W,Z₃))` solves the
    `Φ̃`-linearized ODE along the base quadruple curve `((Y,V),(V,W))`.

  ## HONEST FIREWALL — see the theorem-level checkpoint near the W3 capstone.
-/
import QIQTH.UniformFlowThirdDiag
import QIQTH.UniformFlowThirdBoundClose
import QIQTH.UniformFlowThirdJet
import QIQTH.QuadrupleFlowSupply
import QIQTH.UniformFlowSecondFDeriv
import QIQTH.UniformFlowHessianDiag
import QIQTH.JacobiOperatorFDeriv
import QIQTH.UniformFlowThirdFDeriv
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.AutonomousDep
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

/-! ### Field-agnostic block formulas for `D(genericDoubled Φ)` -/

section GenericBlock

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **First-component block formula for `D(genericDoubled Φ)`.**  Mirror of
    `doubledField_fderiv_fst_apply` one level up: `(D(genericDoubled Φ)(e)·u).1 = DΦ(e.1)·u.1`. -/
theorem genericDoubled_fderiv_fst_apply (Φ : E → E)
    (hΦ : ContDiff ℝ (⊤ : WithTop ℕ∞) Φ) (e u : E × E) :
    ((fderiv ℝ (genericDoubled Φ) e) u).1 = fderiv ℝ Φ e.1 u.1 := by
  have hGdiff : Differentiable ℝ (genericDoubled Φ) :=
    (contDiff_genericDoubled hΦ).differentiable (by simp)
  have hFdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hG : HasFDerivAt (genericDoubled Φ) (fderiv ℝ (genericDoubled Φ) e) e :=
    (hGdiff e).hasFDerivAt
  have hproj : HasFDerivAt (fun x => (genericDoubled Φ x).1)
      ((ContinuousLinearMap.fst ℝ E E).comp (fderiv ℝ (genericDoubled Φ) e)) e :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp e hG
  have hF : HasFDerivAt (fun x : E × E => Φ x.1)
      ((fderiv ℝ Φ e.1).comp (ContinuousLinearMap.fst ℝ E E)) e :=
    (hFdiff e.1).hasFDerivAt.comp e hasFDerivAt_fst
  have heq : (fun x : E × E => (genericDoubled Φ x).1) = (fun x => Φ x.1) := rfl
  rw [heq] at hproj
  have huniq := hproj.unique hF
  have hval := DFunLike.congr_fun huniq u
  simpa [ContinuousLinearMap.comp_apply] using hval

/-- **Second-component block formula for `D(genericDoubled Φ)`.**  Mirror of
    `doubledField_fderiv_snd_apply`: `(D(genericDoubled Φ)(e)·u).2 = DΦ(e.1)·u.2 + D²Φ(e.1)(u.1)(e.2)`. -/
theorem genericDoubled_fderiv_snd_apply (Φ : E → E)
    (hΦ : ContDiff ℝ (⊤ : WithTop ℕ∞) Φ) (e u : E × E) :
    ((fderiv ℝ (genericDoubled Φ) e) u).2
      = fderiv ℝ Φ e.1 u.2 + fderiv ℝ (fderiv ℝ Φ) e.1 u.1 e.2 := by
  have hFdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hdFdiff : Differentiable ℝ (fderiv ℝ Φ) :=
    ((hΦ.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top)).differentiable (by simp)
  have hF : HasFDerivAt Φ (fderiv ℝ Φ e.1) e.1 := (hFdiff e.1).hasFDerivAt
  have hdF : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) e.1) e.1 := (hdFdiff e.1).hasFDerivAt
  have h1 : HasFDerivAt (fun p : E × E => Φ p.1)
      ((fderiv ℝ Φ e.1).comp (ContinuousLinearMap.fst ℝ E E)) e :=
    hF.comp e hasFDerivAt_fst
  have hc : HasFDerivAt (fun p : E × E => fderiv ℝ Φ p.1)
      ((fderiv ℝ (fderiv ℝ Φ) e.1).comp (ContinuousLinearMap.fst ℝ E E)) e :=
    hdF.comp e hasFDerivAt_fst
  have hu : HasFDerivAt (fun p : E × E => p.2) (ContinuousLinearMap.snd ℝ E E) e :=
    hasFDerivAt_snd
  have h2 := hc.clm_apply hu
  have hprod : HasFDerivAt (genericDoubled Φ)
      (((fderiv ℝ Φ e.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        (((fderiv ℝ Φ e.1).comp (ContinuousLinearMap.snd ℝ E E))
          + ((fderiv ℝ (fderiv ℝ Φ) e.1).comp (ContinuousLinearMap.fst ℝ E E)).flip e.2)) e :=
    h1.prodMk h2
  rw [hprod.fderiv]
  simp [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

end GenericBlock

/-! ### The `D²(doubledField)` applied block formula (in terms of `D²F`, `D³F`) -/

section SecondBlock

variable {n : ℕ}

/-- Evaluation commutes with `fderiv`: for `H : X → V →L W` differentiable at `x`,
    `fderiv ℝ H x v u = fderiv ℝ (fun y => H y u) x v`. -/
private theorem fderiv_clm_apply_const {X V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {H : X → V →L[ℝ] W} {x v : X} {u : V} (hH : DifferentiableAt ℝ H x) :
    fderiv ℝ H x v u = fderiv ℝ (fun y : X => H y u) x v := by
  have hev : HasFDerivAt (fun y : X => H y u)
      ((ContinuousLinearMap.apply ℝ W u).comp (fderiv ℝ H x)) x := by
    simpa using (ContinuousLinearMap.apply ℝ W u).hasFDerivAt.comp x hH.hasFDerivAt
  rw [hev.fderiv]
  simp [ContinuousLinearMap.comp_apply]

/-- **`D²(doubledField)` applied block formula.**  With `F = geodesicField g gi`, `G = doubledField g gi`,
      `(D²G(e)(w)(u)).1 = D²F(e.1)(w.1)(u.1)`
      `(D²G(e)(w)(u)).2 = D²F(e.1)(w.1)(u.2) + D³F(e.1)(w.1)(u.1)(e.2) + D²F(e.1)(u.1)(w.2)`. -/
theorem fderiv_fderiv_doubledField_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (e w u : (Point n × Point n) × (Point n × Point n)) :
    ((fderiv ℝ (fderiv ℝ (doubledField g gi)) e) w u).1
        = fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1 w.1 u.1
      ∧ ((fderiv ℝ (fderiv ℝ (doubledField g gi)) e) w u).2
        = fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1 w.1 u.2
          + fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) e.1 w.1 u.1 e.2
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1 u.1 w.2 := by
  -- regularity
  have hDFcd : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (geodesicField g gi)) :=
    contDiff_fderiv_geodesicField g gi hC
  have hGcd : ContDiff ℝ (⊤ : WithTop ℕ∞) (doubledField g gi) := contDiff_doubledField g gi hC
  have hDG : DifferentiableAt ℝ (fderiv ℝ (doubledField g gi)) e :=
    ((hGcd.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).differentiable (by simp)).differentiableAt
  have hDF : DifferentiableAt ℝ (fderiv ℝ (geodesicField g gi)) e.1 :=
    (hDFcd.differentiable (by simp)).differentiableAt
  have hDDF : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) e.1 :=
    ((hDFcd.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).differentiable (by simp)).differentiableAt
  -- ev-commute
  have hD2eval : ((fderiv ℝ (fderiv ℝ (doubledField g gi)) e) w) u
      = fderiv ℝ (fun e' => fderiv ℝ (doubledField g gi) e' u) e w :=
    fderiv_clm_apply_const hDG
  -- rewrite the evaluated first derivative componentwise
  have hfun : (fun e' : (Point n × Point n) × (Point n × Point n) => fderiv ℝ (doubledField g gi) e' u)
      = (fun e' => (fderiv ℝ (geodesicField g gi) e'.1 u.1,
          fderiv ℝ (geodesicField g gi) e'.1 u.2
            + fderiv ℝ (fderiv ℝ (geodesicField g gi)) e'.1 u.1 e'.2)) := by
    funext e'
    exact Prod.ext (doubledField_fderiv_fst_apply g gi hC e' u)
      (doubledField_fderiv_snd_apply g gi hC e' u)
  -- differentiate the RHS
  have hfst : HasFDerivAt (fun z : (Point n × Point n) × (Point n × Point n) => z.1)
      (ContinuousLinearMap.fst ℝ (Point n × Point n) (Point n × Point n)) e := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun z : (Point n × Point n) × (Point n × Point n) => z.2)
      (ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)) e := hasFDerivAt_snd
  have hDF_fst : HasFDerivAt (fun z : (Point n × Point n) × (Point n × Point n) => fderiv ℝ (geodesicField g gi) z.1)
      ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1).comp
        (ContinuousLinearMap.fst ℝ (Point n × Point n) (Point n × Point n))) e :=
    hDF.hasFDerivAt.comp e hfst
  have hDDF_fst : HasFDerivAt
      (fun z : (Point n × Point n) × (Point n × Point n) => fderiv ℝ (fderiv ℝ (geodesicField g gi)) z.1)
      ((fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) e.1).comp
        (ContinuousLinearMap.fst ℝ (Point n × Point n) (Point n × Point n))) e :=
    hDDF.hasFDerivAt.comp e hfst
  have h1 : HasFDerivAt (fun z : (Point n × Point n) × (Point n × Point n) => fderiv ℝ (geodesicField g gi) z.1 u.1)
      ((ContinuousLinearMap.apply ℝ (Point n × Point n) u.1).comp
        ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1).comp
          (ContinuousLinearMap.fst ℝ (Point n × Point n) (Point n × Point n)))) e :=
    (ContinuousLinearMap.apply ℝ (Point n × Point n) u.1).hasFDerivAt.comp e hDF_fst
  have h2a : HasFDerivAt (fun z : (Point n × Point n) × (Point n × Point n) => fderiv ℝ (geodesicField g gi) z.1 u.2)
      ((ContinuousLinearMap.apply ℝ (Point n × Point n) u.2).comp
        ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1).comp
          (ContinuousLinearMap.fst ℝ (Point n × Point n) (Point n × Point n)))) e :=
    (ContinuousLinearMap.apply ℝ (Point n × Point n) u.2).hasFDerivAt.comp e hDF_fst
  have hA : HasFDerivAt
      (fun z : (Point n × Point n) × (Point n × Point n) => fderiv ℝ (fderiv ℝ (geodesicField g gi)) z.1 u.1)
      ((ContinuousLinearMap.apply ℝ ((Point n × Point n) →L[ℝ] (Point n × Point n)) u.1).comp
        ((fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) e.1).comp
          (ContinuousLinearMap.fst ℝ (Point n × Point n) (Point n × Point n)))) e :=
    (ContinuousLinearMap.apply ℝ ((Point n × Point n) →L[ℝ] (Point n × Point n)) u.1).hasFDerivAt.comp
      e hDDF_fst
  have h2b := hA.clm_apply hsnd
  have hEval := hfun.symm ▸ (h1.prodMk (h2a.add h2b))
  refine ⟨?_, ?_⟩
  · rw [hD2eval, hEval.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
  · rw [hD2eval, hEval.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    abel

/-- First-component corollary of `fderiv_fderiv_doubledField_apply`. -/
theorem fderiv_fderiv_doubledField_fst (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (e w u : (Point n × Point n) × (Point n × Point n)) :
    ((fderiv ℝ (fderiv ℝ (doubledField g gi)) e) w u).1
      = fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1 w.1 u.1 :=
  (fderiv_fderiv_doubledField_apply g gi hC e w u).1

/-- Second-component corollary of `fderiv_fderiv_doubledField_apply`. -/
theorem fderiv_fderiv_doubledField_snd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (e w u : (Point n × Point n) × (Point n × Point n)) :
    ((fderiv ℝ (fderiv ℝ (doubledField g gi)) e) w u).2
      = fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1 w.1 u.2
        + fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) e.1 w.1 u.1 e.2
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1 u.1 w.2 :=
  (fderiv_fderiv_doubledField_apply g gi hC e w u).2

end SecondBlock

/-! ### Abstract linearized-ODE uniqueness, within `[0,1]` -/

section WithinUnique

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Within-`[0,1]` linearized-ODE uniqueness.**  Two `HasDerivWithinAt`-solutions of the linearized
    ODE `J' = DΦ(Y0)·J` along a curve `Y0` (with `‖DΦ(Y0 τ)‖ ≤ K`) that agree at `0` agree on `[0,1]`.
    Within-derivative mirror of `autonomousLinODE_unique`. -/
theorem autonomousLinODE_within_unique (Φ : E → E) {K : ℝ} (hK0 : 0 ≤ K)
    {Y0 J₁ J₂ : ℝ → E}
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ Φ (Y0 τ)‖ ≤ K)
    (hJ1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt J₁ (fderiv ℝ Φ (Y0 τ) (J₁ τ)) (Set.Icc (0 : ℝ) 1) τ)
    (hJ2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt J₂ (fderiv ℝ Φ (Y0 τ) (J₂ τ)) (Set.Icc (0 : ℝ) 1) τ)
    (h0 : J₁ 0 = J₂ 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    J₁ t = J₂ t := by
  set R : ℝ → E := fun τ => J₁ τ - J₂ τ with hRdef
  have hRd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt R (fderiv ℝ Φ (Y0 τ) (R τ)) (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    simpa [hRdef, map_sub] using (hJ1 τ hτ).sub (hJ2 τ hτ)
  have hRcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hRd τ hτ).continuousWithinAt
  have hR0 : ‖R 0‖ ≤ 0 := by rw [hRdef]; simp [h0]
  have hbnd : ‖R t‖ ≤ gronwallBound 0 K 0 (t - 0) :=
    norm_le_gronwallBound_of_norm_deriv_right_le (f := R)
      (f' := fun τ => fderiv ℝ Φ (Y0 τ) (R τ)) (δ := 0) (K := K) (ε := 0) (a := 0) (b := 1)
      hRcont
      (fun x hx => hasDerivWithinAt_Ici_of_Icc01 hx (hRd x (Set.Ico_subset_Icc_self hx)))
      hR0
      (fun x hx => by
        have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
        calc ‖fderiv ℝ Φ (Y0 x) (R x)‖
            ≤ ‖fderiv ℝ Φ (Y0 x)‖ * ‖R x‖ := (fderiv ℝ Φ (Y0 x)).le_opNorm (R x)
          _ ≤ K * ‖R x‖ := mul_le_mul_of_nonneg_right (hKb x hx') (norm_nonneg _)
          _ = K * ‖R x‖ + 0 := by ring)
      t ht
  rw [sub_zero, gronwallBound_ε0_δ0] at hbnd
  have hRt : R t = 0 := norm_le_zero_iff.mp hbnd
  rw [hRdef] at hRt
  exact sub_eq_zero.mp hRt

end WithinUnique

/-! ### The doubled pair `(V,W)` solves the `doubledField`-linearized ODE along `(Y,V)` -/

section ComparisonFields

variable {n : ℕ}

/-- **`(V,W)` solves the `doubledField`-linearized ODE along `(Y,V)`.**  If `V` solves the Jacobi ODE
    along `Y` and `W` the second-variation ODE, then `τ ↦ (V τ, W τ)` solves
    `U' = D(doubledField)((Y,V))·U`. -/
theorem doubledPair_hasDerivWithinAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y V W : ℝ → Point n × Point n} {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hVd : HasDerivWithinAt V (fderiv ℝ (geodesicField g gi) (Y τ) (V τ)) (Set.Icc (0 : ℝ) 1) τ)
    (hWd : HasDerivWithinAt W (fderiv ℝ (geodesicField g gi) (Y τ) (W τ)
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (V τ)) (Set.Icc (0 : ℝ) 1) τ) :
    HasDerivWithinAt (fun t => (V t, W t))
      (fderiv ℝ (doubledField g gi) (Y τ, V τ) (V τ, W τ)) (Set.Icc (0 : ℝ) 1) τ := by
  have hd := hVd.prodMk hWd
  have heq : fderiv ℝ (doubledField g gi) (Y τ, V τ) (V τ, W τ)
      = (fderiv ℝ (geodesicField g gi) (Y τ) (V τ),
          fderiv ℝ (geodesicField g gi) (Y τ) (W τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (V τ)) :=
    Prod.ext (doubledField_fderiv_fst_apply g gi hC (Y τ, V τ) (V τ, W τ))
      (doubledField_fderiv_snd_apply g gi hC (Y τ, V τ) (V τ, W τ))
  rw [heq]; exact hd

/-- **The comparison field `Xcmp = ((V,W),(W,Z₃))` solves the `Φ̃`-linearized ODE along the base
    quadruple curve `((Y,V),(V,W))`.**  Here `Φ̃ = genericDoubled (doubledField g gi)`.  DERIVED from the
    `V`/`W`/`Z₃` within-ODEs (W1's shapes) via the `D(genericDoubled)`, `D(doubledField)`,
    `D²(doubledField)` block formulas — the algebra core of the cubic bound. -/
theorem comparisonField_hasDerivWithinAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y V W Z₃ : ℝ → Point n × Point n} {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hVd : HasDerivWithinAt V (fderiv ℝ (geodesicField g gi) (Y τ) (V τ)) (Set.Icc (0 : ℝ) 1) τ)
    (hWd : HasDerivWithinAt W (fderiv ℝ (geodesicField g gi) (Y τ) (W τ)
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (V τ)) (Set.Icc (0 : ℝ) 1) τ)
    (hZ3d : HasDerivWithinAt Z₃ (fderiv ℝ (geodesicField g gi) (Y τ) (Z₃ τ)
        + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ) (V τ) (V τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (W τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (W τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (W τ) (V τ))) (Set.Icc (0 : ℝ) 1) τ) :
    HasDerivWithinAt (fun t => ((V t, W t), (W t, Z₃ t)))
      (fderiv ℝ (genericDoubled (doubledField g gi))
        ((Y τ, V τ), (V τ, W τ)) ((V τ, W τ), (W τ, Z₃ τ))) (Set.Icc (0 : ℝ) 1) τ := by
  -- The within-derivative of the packed field, with W1's RHS values.
  have hd := (hVd.prodMk hWd).prodMk (hWd.prodMk hZ3d)
  -- The algebra: the block-formula RHS equals W1's packed RHS.
  set e : (Point n × Point n) × (Point n × Point n) := (Y τ, V τ) with hedef
  set X1 : Point n × Point n := V τ with hX1def
  have hgen1 := genericDoubled_fderiv_fst_apply (doubledField g gi) (contDiff_doubledField g gi hC)
    ((Y τ, V τ), (V τ, W τ)) ((V τ, W τ), (W τ, Z₃ τ))
  have hgen2 := genericDoubled_fderiv_snd_apply (doubledField g gi) (contDiff_doubledField g gi hC)
    ((Y τ, V τ), (V τ, W τ)) ((V τ, W τ), (W τ, Z₃ τ))
  have heq : fderiv ℝ (genericDoubled (doubledField g gi))
      ((Y τ, V τ), (V τ, W τ)) ((V τ, W τ), (W τ, Z₃ τ))
      = ((fderiv ℝ (geodesicField g gi) (Y τ) (V τ),
          fderiv ℝ (geodesicField g gi) (Y τ) (W τ)
            + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (V τ)),
        (fderiv ℝ (geodesicField g gi) (Y τ) (W τ)
            + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (V τ),
          fderiv ℝ (geodesicField g gi) (Y τ) (Z₃ τ)
          + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Y τ) (V τ) (V τ) (V τ)
            + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (W τ)
            + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (V τ) (W τ)
            + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y τ) (W τ) (V τ)))) := by
    refine Prod.ext ?_ ?_
    · -- first factor via genericDoubled fst = D(doubledField)((Y,V))·(V,W)
      rw [hgen1]
      refine Prod.ext ?_ ?_
      · rw [doubledField_fderiv_fst_apply g gi hC (Y τ, V τ) (V τ, W τ)]
      · rw [doubledField_fderiv_snd_apply g gi hC (Y τ, V τ) (V τ, W τ)]
    · -- second factor via genericDoubled snd = D(doubledField)((Y,V))·(W,Z₃) + D²(doubledField)(…)
      rw [hgen2]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_add, doubledField_fderiv_fst_apply g gi hC (Y τ, V τ) (W τ, Z₃ τ),
          fderiv_fderiv_doubledField_fst g gi hC (Y τ, V τ) (V τ, W τ) (V τ, W τ)]
      · rw [Prod.snd_add, doubledField_fderiv_snd_apply g gi hC (Y τ, V τ) (W τ, Z₃ τ),
          fderiv_fderiv_doubledField_snd g gi hC (Y τ, V τ) (V τ, W τ) (V τ, W τ)]
        abel
  rw [heq]; exact hd

end ComparisonFields

/-! ### The quadruple-flow supply, KEEPING the engine's linearized-field clause -/

section WithField

variable {n : ℕ}

/-- **The quadruple-flow supply with the `Φ̃`-linearized field EXPOSED (re-plumb of J4-73).**  Same as
    `uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt` but additionally returns the globally
    defined `Φ̃`-linearized family `Vf` along the base quadruple curve `W0`, with the engine's
    `∀ δ, L δ = Vf δ 1` clause KEPT (J4-73 discards it).  `Φ̃ = genericDoubled (doubledField g gi)`. -/
theorem uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt_withField
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b : Point n) :
    ∃ Jf : Point n → ℝ → Point n × Point n,
    ∃ Uf : Point n → ℝ → (Point n × Point n) × (Point n × Point n),
      (∀ δ : Point n, ‖δ‖ ≤ uniformFlowRadius g gi hC hK - ‖v‖ →
        Jf δ 0 = ((0 : Point n), b) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Jf δ)
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jf δ τ)) τ) ∧
        Uf δ 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Uf δ)
            (fderiv ℝ (doubledField g gi)
              (uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ) (Uf δ τ)) τ)) ∧
      ∃ Vf : Point n → ℝ → ((Point n × Point n) × (Point n × Point n)) ×
          ((Point n × Point n) × (Point n × Point n)),
        (∀ δ : Point n, Vf δ 0
          = ((((0 : Point n), δ), ((0 : Point n), (0 : Point n))),
              (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))))) ∧
        (∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Vf δ)
            (fderiv ℝ (genericDoubled (doubledField g gi))
              (((uniformFlowTube g gi hC hK q (v + 0) τ, Jf 0 τ), Uf 0 τ)) (Vf δ τ)) τ) ∧
        ContinuousOn
          (fun τ => (((uniformFlowTube g gi hC hK q (v + 0) τ, Jf 0 τ), Uf 0 τ) :
            ((Point n × Point n) × (Point n × Point n)) ×
              ((Point n × Point n) × (Point n × Point n)))) (Set.Icc (0 : ℝ) 1) ∧
        ∃ L : Point n →L[ℝ]
            ((Point n × Point n) × (Point n × Point n)) × ((Point n × Point n) × (Point n × Point n)),
          (∀ δ : Point n, L δ = Vf δ 1) ∧
          HasFDerivAt
            (fun δ => (((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1), Uf δ 1) :
              ((Point n × Point n) × (Point n × Point n)) ×
                ((Point n × Point n) × (Point n × Point n)))) L 0 := by
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
  have hAcompact : IsCompact (Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ)) :=
    isCompact_closedBall _ _
  obtain ⟨Kb, hKb0, hKbbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hAcompact
  set Jbound : ℝ := ‖((0 : Point n), b)‖ * Real.exp Kb with hJbounddef
  have hJbound0 : 0 ≤ Jbound := by rw [hJbounddef]; positivity
  set Sdbl : Set ((Point n × Point n) × (Point n × Point n)) :=
    Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) ×ˢ
      Metric.closedBall (0 : Point n × Point n) Jbound with hSdbldef
  have hSdblcompact : IsCompact Sdbl := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨Kb2, hKb20, hKb2bd⟩ := doubledField_fderiv_bddOn_compact g gi hC hSdblcompact
  set Useed : (Point n × Point n) × (Point n × Point n) :=
    (((0 : Point n), a), ((0 : Point n), (0 : Point n))) with hUseeddef
  set Ubound : ℝ := ‖Useed‖ * Real.exp Kb2 with hUbounddef
  have hUbound0 : 0 ≤ Ubound := by rw [hUbounddef]; positivity
  set S : Set (((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n))) :=
    Sdbl ×ˢ Metric.closedBall (0 : (Point n × Point n) × (Point n × Point n)) Ubound with hSdef
  have hScompact : IsCompact S := hSdblcompact.prod (isCompact_closedBall _ _)
  have hSconvex : Convex ℝ S :=
    ((convex_closedBall _ _).prod (convex_closedBall _ _)).prod (convex_closedBall _ _)
  have hcontDbl : Continuous (fderiv ℝ (doubledField g gi)) :=
    (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
  have key : ∀ δ : Point n,
      ∃ Jc : ℝ → Point n × Point n,
      ∃ Uc : ℝ → (Point n × Point n) × (Point n × Point n),
        (‖v + δ‖ ≤ ρ →
          Jc 0 = ((0 : Point n), b) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Jc
              (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ Jbound) ∧
          ContinuousOn Jc (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
          Uc 0 = Useed ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Uc
              (fderiv ℝ (doubledField g gi)
                (uniformFlowTube g gi hC hK q (v + δ) τ, Jc τ) (Uc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uc τ‖ ≤ Ubound) ∧
          ContinuousOn Uc (Set.Icc (-(1/2) : ℝ) (3/2))) := by
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
      have hYdblpad : ContinuousOn (fun τ => (P τ, Jc τ)) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
        hPcont.prodMk hJcpad
      set Adbl : ℝ → (((Point n × Point n) × (Point n × Point n)) →L[ℝ]
          ((Point n × Point n) × (Point n × Point n))) :=
        fun τ => fderiv ℝ (doubledField g gi) (P τ, Jc τ) with hAdbldef
      have hAdbl : ContinuousOn Adbl (Set.Icc (-(1/2) : ℝ) (3/2)) :=
        hcontDbl.comp_continuousOn hYdblpad
      obtain ⟨Uc, hUc0, hUcode, hUcpad⟩ :=
        linODE_exists_narrowpad_continuousOn Adbl hAdbl Useed
      have hUcont : ContinuousOn Uc (Set.Icc (0 : ℝ) 1) :=
        fun τ hτ => ((hUcode τ hτ).continuousAt).continuousWithinAt
      have hfderiv2bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (doubledField g gi) (P x, Jc x)‖ ≤ Kb2 := by
        intro x hx
        refine hKb2bd (P x, Jc x) ?_
        rw [hSdbldef, Set.mem_prod]
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_eq_norm]
          calc ‖P x - ((q, 0) : Point n × Point n)‖
              ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) h x hx
            _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left h hC₀nn
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hJcbnd x hx
      have hUgw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖Uc x‖ ≤ gronwallBound ‖Useed‖ Kb2 0 (x - 0) :=
        norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖Useed‖)
          (K := Kb2) (ε := 0) (a := 0) (b := 1) hUcont
          (fun x hx => (hUcode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
          (le_of_eq (by rw [hUc0]))
          (fun x hx => by
            have hle' := (fderiv ℝ (doubledField g gi) (P x, Jc x)).le_opNorm (Uc x)
            calc ‖fderiv ℝ (doubledField g gi) (P x, Jc x) (Uc x)‖
                ≤ ‖fderiv ℝ (doubledField g gi) (P x, Jc x)‖ * ‖Uc x‖ := hle'
              _ ≤ Kb2 * ‖Uc x‖ :=
                  mul_le_mul_of_nonneg_right (hfderiv2bd x (Set.Ico_subset_Icc_self hx)) (norm_nonneg _)
              _ = Kb2 * ‖Uc x‖ + 0 := by ring)
      have hUcbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uc τ‖ ≤ Ubound := by
        intro τ hτ
        have h1 := hUgw τ hτ
        rw [sub_zero, gronwallBound_ε0] at h1
        refine h1.trans ?_
        rw [hUbounddef]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Real.exp_le_exp]
        calc Kb2 * τ ≤ Kb2 * 1 := mul_le_mul_of_nonneg_left hτ.2 hKb20
          _ = Kb2 := mul_one _
      refine ⟨Jc, Uc, fun _ => ⟨hJc0, hJcode, hJcbnd, hJcpad, hUc0, ?_, hUcbnd, hUcpad⟩⟩
      intro τ hτ; have := hUcode τ hτ; rwa [hAdbldef] at this
    · exact ⟨fun _ => 0, fun _ => 0, fun h' => absurd h' h⟩
  set Jf : Point n → ℝ → Point n × Point n := fun δ => Classical.choose (key δ) with hJfdef
  set Uf : Point n → ℝ → (Point n × Point n) × (Point n × Point n) :=
    fun δ => Classical.choose (Classical.choose_spec (key δ)) with hUfdef
  have hspec : ∀ δ : Point n, ‖v + δ‖ ≤ ρ →
      Jf δ 0 = ((0 : Point n), b) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Jf δ)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jf δ τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jf δ τ‖ ≤ Jbound) ∧
      ContinuousOn (Jf δ) (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
      Uf δ 0 = Useed ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Uf δ)
          (fderiv ℝ (doubledField g gi)
            (uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ) (Uf δ τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uf δ τ‖ ≤ Ubound) ∧
      ContinuousOn (Uf δ) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    fun δ => Classical.choose_spec (Classical.choose_spec (key δ))
  have hP0cont : ContinuousOn (fun τ => uniformFlowTube g gi hC hK q (v + 0) τ)
      (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + 0) hadm0 τ hτoo).continuousAt).continuousWithinAt
  obtain ⟨_, _, _, hJf0pad, _, _, _, hUf0pad⟩ := hspec 0 hadm0
  set W0 : ℝ → ((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n)) :=
    fun τ => ((uniformFlowTube g gi hC hK q (v + 0) τ, Jf 0 τ), Uf 0 τ) with hW0def
  have hW0pad : ContinuousOn W0 (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    (hP0cont.prodMk hJf0pad).prodMk hUf0pad
  have hcontQuad : Continuous (fderiv ℝ (genericDoubled (doubledField g gi))) :=
    (contDiff_quadrupledField g gi hC).continuous_fderiv (by simp)
  set Aquad : ℝ → ((((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n))) →L[ℝ]
      (((Point n × Point n) × (Point n × Point n)) ×
        ((Point n × Point n) × (Point n × Point n)))) :=
    fun τ => fderiv ℝ (genericDoubled (doubledField g gi)) (W0 τ) with hAquaddef
  have hAquad : ContinuousOn Aquad (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    hcontQuad.comp_continuousOn hW0pad
  set seedInner : Point n →L[ℝ] (Point n × Point n) × (Point n × Point n) :=
    (ContinuousLinearMap.inl ℝ (Point n × Point n) (Point n × Point n)).comp
      (ContinuousLinearMap.inr ℝ (Point n) (Point n)) with hseedInnerdef
  set seedCLM : Point n →L[ℝ]
      ((Point n × Point n) × (Point n × Point n)) × ((Point n × Point n) × (Point n × Point n)) :=
    (ContinuousLinearMap.inl ℝ ((Point n × Point n) × (Point n × Point n))
      ((Point n × Point n) × (Point n × Point n))).comp seedInner with hseedCLMdef
  have hseed_eq : ∀ δ : Point n,
      seedCLM δ = ((((0 : Point n), δ), ((0 : Point n), (0 : Point n))),
        (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))) := by
    intro δ
    simp [hseedCLMdef, hseedInnerdef, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.ext_iff]
  have hseednorm : ∀ δ : Point n, ‖seedCLM δ‖ = ‖δ‖ := by
    intro δ; rw [hseed_eq δ]; simp [Prod.norm_def, norm_nonneg]
  have varkey : ∀ δ : Point n,
      ∃ Vc : ℝ → ((Point n × Point n) × (Point n × Point n)) ×
          ((Point n × Point n) × (Point n × Point n)),
        Vc 0 = seedCLM δ ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt Vc
            (fderiv ℝ (genericDoubled (doubledField g gi)) (W0 τ) (Vc τ)) τ) := by
    intro δ
    obtain ⟨Vc, hVc0, hVcode, _⟩ := linODE_exists_narrowpad_continuousOn Aquad hAquad (seedCLM δ)
    refine ⟨Vc, hVc0, fun τ hτ => ?_⟩
    have := hVcode τ hτ; rwa [hAquaddef] at this
  set Vf : Point n → ℝ → ((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n)) :=
    fun δ => Classical.choose (varkey δ) with hVfdef
  set W : Point n → ℝ → ((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n)) :=
    fun δ t => ((uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t), Uf δ t) with hWdef
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hΦcd : ContDiff ℝ (⊤ : WithTop ℕ∞) (genericDoubled (doubledField g gi)) :=
    contDiff_quadrupledField g gi hC
  have hdiff : ∀ x ∈ S, DifferentiableAt ℝ (genericDoubled (doubledField g gi)) x :=
    fun x _ => (hΦcd.differentiable (by simp)).differentiableAt
  have hΦcd' : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (genericDoubled (doubledField g gi))) :=
    hΦcd.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top
  have hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ (genericDoubled (doubledField g gi))) x :=
    fun x _ => (hΦcd'.differentiable (by simp)).differentiableAt
  obtain ⟨M₂, _hM₂0, hbound2⟩ := quadrupledField_fderiv2_bddOn_compact g gi hC hScompact
  obtain ⟨Kf, hKf0, hKfbd⟩ := quadrupledField_fderiv_bddOn_compact g gi hC hScompact
  set K₀ : NNReal := ⟨Kf, hKf0⟩ with hK₀def
  have hLip : LipschitzOnWith K₀ (genericDoubled (doubledField g gi)) S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hdiff x (by trivial))
      (fun x hx => by rw [← NNReal.coe_le_coe]; simpa [hK₀def] using hKfbd x hx)
      hSconvex
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ)
        (genericDoubled (doubledField g gi) (W δ τ)) τ := by
    intro δ hδ τ hτ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨_, hJfode, _, _, _, hUfode, _, _⟩ := hspec δ hadm
    have hP := uniformFlowTube_spec_ode g gi hC hK q hq (v + δ) hadm τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hYode : HasDerivAt (fun t => (uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t))
        (doubledField g gi (uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ)) τ :=
      doubledField_prod_hasDerivAt g gi hP (hJfode τ hτ)
    exact genericDoubled_prod_hasDerivAt (doubledField g gi) hYode (hUfode τ hτ)
  have hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Vf δ)
        (fderiv ℝ (genericDoubled (doubledField g gi)) (W0 τ) (Vf δ τ)) τ :=
    fun δ => (Classical.choose_spec (varkey δ)).2
  have hV0 : ∀ δ : Point n, Vf δ 0 = seedCLM δ :=
    fun δ => (Classical.choose_spec (varkey δ)).1
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S := by
    intro δ hδ τ hτ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨_, _, hJfbnd, _, _, _, hUfbnd, _⟩ := hspec δ hadm
    rw [hWdef, hSdef, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [hSdbldef, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖uniformFlowTube g gi hC hK q (v + δ) τ - ((q, 0) : Point n × Point n)‖
            ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) hadm τ hτ
          _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hadm hC₀nn
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hJfbnd τ hτ
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hUfbnd τ hτ
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (genericDoubled (doubledField g gi)) (W0 τ)‖ ≤ Kf := by
    intro τ hτ
    have hmem0 := hmem 0 h0σ τ hτ
    have : W 0 τ = W0 τ := by rw [hWdef, hW0def]
    rw [this] at hmem0
    exact hKfbd (W0 τ) hmem0
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = seedCLM δ := by
    intro δ hδ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨hJfδ0, _, _, _, hUfδ0, _, _, _⟩ := hspec δ hadm
    obtain ⟨hJf00, _, _, _, hUf00, _, _, _⟩ := hspec 0 hadm0
    have h1 : uniformFlowTube g gi hC hK q (v + δ) 0 = (q, v + δ) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + δ) hadm
    have h2 : uniformFlowTube g gi hC hK q (v + 0) 0 = (q, v + 0) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + 0) hadm0
    simp only [hWdef]
    rw [h1, h2, hJfδ0, hJf00, hUfδ0, hUf00, hUseeddef, hseed_eq δ]
    simp only [Prod.mk_sub_mk, sub_self, add_zero, add_sub_cancel_left, Prod.mk_zero_zero]
  obtain ⟨L, hLeq, hFD⟩ :=
    autonomousFlow_endpoint_hasFDerivAt_window_exists (genericDoubled (doubledField g gi))
      (W := W) (V := Vf) (seed := seedCLM) (S := S) hKf0 hσ ht1 hSconvex hdiff hdiff2 hbound2 hLip
      hseednorm hWode hVode hV0 hIC hKb hmem
  have hIccsub : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (-(1/2) : ℝ) (3/2) := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨Jf, Uf, ?_, Vf, ?_, hVode, ?_, L, hLeq, ?_⟩
  · intro δ hδ
    obtain ⟨hJfδ0, hJfode, _, _, hUfδ0, hUfode, _, _⟩ := hspec δ (hle δ hδ)
    exact ⟨hJfδ0, hJfode, hUfδ0, hUfode⟩
  · intro δ; exact (hV0 δ).trans (hseed_eq δ)
  · exact hW0pad.mono hIccsub
  · have hfe : (fun δ => W δ 1)
        = (fun δ => (((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1), Uf δ 1) :
            ((Point n × Point n) × (Point n × Point n)) ×
              ((Point n × Point n) × (Point n × Point n)))) := by
      funext δ; rw [hWdef]
    rw [hfe] at hFD
    exact hFD

end WithField

/-! ### X1 — the diagonal CUBIC bound, and X2 — W3 UNCONDITIONAL -/

section Uncond

variable {n : ℕ}

/-- **X1 — the uniform diagonal CUBIC bound on `B₃`.**  There is a uniform radius `r₀ > 0` (`r₀ ≤ ρ_K`)
    and constant `M₃'` such that for `q ∈ K`, `‖v‖ < r₀`, direction `a`,
        `‖(fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) v) a a a‖
            ≤ M₃' · ‖a‖³`.
    DERIVED via the COMPARISON-FIELD route: J4-77's diagonal value id `B₃ a a a = L₃ a`, the re-plumbed
    quadruple engine (`…_withField`, exposing the `Φ̃`-linearized field `Vf` and its `L δ = Vf δ 1`
    clause), the ODE-uniqueness identification `Vf a = Xcmp = ((V,W),(W,Z₃))` (W1's fields) via
    `comparisonField_hasDerivWithinAt` + `autonomousLinODE_within_unique`, and W1's cubic bound
    `‖Z₃ 1‖ ≤ M₃j·‖a‖³`.  `M₃' = M₃j`.  Hypotheses ONLY `hC` + `IsCompact K`.  NO `expRho`. -/
theorem uniformFlowExp_thirdDeriv_diag_cubic_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), r₀ ≤ uniformFlowRadius g gi hC hK ∧ ∃ M₃' : ℝ, 0 ≤ M₃' ∧
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ a : Point n,
        ‖(fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v)
            a a a‖ ≤ M₃' * ‖a‖ ^ 3 := by
  classical
  obtain ⟨r₀W, hr₀W0, M₃j, hM₃j0, hW1⟩ := uniformFlowTube_thirdVariation_uniform_bound g gi hC hK
  have hρ0 : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨min r₀W (uniformFlowRadius g gi hC hK), lt_min hr₀W0 hρ0, min_le_right _ _, M₃j, hM₃j0,
    ?_⟩
  intro q hq v hv a
  have hvr0W : ‖v‖ ≤ r₀W := le_of_lt (lt_of_lt_of_le hv (min_le_left _ _))
  have hvρ : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv (min_le_right _ _)
  -- W1's intrinsic first/second/third variation fields along the base tube.
  obtain ⟨V, W, Z₃, hV0, hVd, hW0, hWd, hZ30, hZ3d, hZ3bnd⟩ := hW1 q hq v hvr0W a
  -- J4-77: the diagonal value id `B₃ a a a = L₃ a`.
  obtain ⟨L₃77, hL₃77FD, hB₃eq⟩ :=
    uniformFlowExp_thirdDeriv_diag_value_perSeed g gi hC hK q hq v hvρ a
  -- withField: the re-plumbed quadruple engine (diagonal seeds `a a`), Vf exposed + `L δ = Vf δ 1`.
  obtain ⟨Jf, Uf, hprops, Vf, hVf0, hVfode, hW0cont, L, hLeq, hFD⟩ :=
    uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt_withField g gi hC hK q hq v hvρ a a
  -- The projection `Ẽ → Point n`, `x ↦ x.2.2.1`.
  set proj : (((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n))) →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp
      ((ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).comp
        (ContinuousLinearMap.snd ℝ ((Point n × Point n) × (Point n × Point n))
          ((Point n × Point n) × (Point n × Point n)))) with hprojdef
  -- Component derivative: `HasFDerivAt (fun δ => (Uf δ 1).2.1) (proj.comp L) 0`.
  have hcompFD : HasFDerivAt (fun δ => (Uf δ 1).2.1) (proj.comp L) 0 := by
    have hc := proj.hasFDerivAt.comp (0 : Point n) hFD
    have hfe : (⇑proj ∘ fun δ => (((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1), Uf δ 1) :
        ((Point n × Point n) × (Point n × Point n)) ×
          ((Point n × Point n) × (Point n × Point n))))
        = (fun δ => (Uf δ 1).2.1) := by
      funext δ; simp [hprojdef]
    rw [hfe] at hc
    exact hc
  -- Z1 on the open velocity window: `(Uf δ 1).2.1 = f₂ (v+δ) a a`.
  have hEq : (fun δ => (Uf δ 1).2.1)
      =ᶠ[𝓝 (0 : Point n)]
      (fun δ => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + δ)) a a) := by
    have hball : Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK - ‖v‖) ∈ 𝓝 (0 : Point n) :=
      Metric.ball_mem_nhds _ (by linarith)
    refine Filter.eventuallyEq_of_mem hball (fun δ hδ => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hδ
    have hδσ : ‖δ‖ ≤ uniformFlowRadius g gi hC hK - ‖v‖ := hδ.le
    have hvδ : ‖v + δ‖ < uniformFlowRadius g gi hC hK := by
      refine lt_of_le_of_lt (norm_add_le v δ) ?_; linarith
    obtain ⟨hJf0, hJfode, hUf0, hUfode⟩ := hprops δ hδσ
    exact (uniformFlowExp_hessian_value_id g gi hC hK q hq (v + δ) hvδ a a
      (Jf δ) hJf0 hJfode (Uf δ) hUf0 hUfode).symm
  -- Transfer + recentre to `HasFDerivAt (fun w => f₂ w a a) (proj.comp L) v`.
  have hFD2 : HasFDerivAt
      (fun δ => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + δ)) a a)
      (proj.comp L) 0 :=
    hcompFD.congr_of_eventuallyEq hEq.symm
  have hshift : HasFDerivAt (fun u : Point n => u - v) (ContinuousLinearMap.id ℝ (Point n)) v :=
    (hasFDerivAt_id v).sub_const v
  have hFD0 : HasFDerivAt
      (fun δ => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + δ)) a a)
      (proj.comp L) (v - v) := by rw [sub_self]; exact hFD2
  have hcomp : HasFDerivAt
      (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + (w - v))) a a)
      ((proj.comp L).comp (ContinuousLinearMap.id ℝ (Point n))) v :=
    hFD0.comp (f := fun w : Point n => w - v) v hshift
  have hfun2 : (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) (v + (w - v))) a a)
      = (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) a a) := by
    funext w; rw [show v + (w - v) = w from by abel]
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  -- `L₃77 = proj.comp L` by uniqueness of the Fréchet derivative.
  have hL₃eq : L₃77 = proj.comp L := hL₃77FD.unique hcomp
  -- ===== Identify `Jf 0 = V`, `Uf 0 = (V, W)` on `[0,1]` (within-uniqueness). =====
  have hadm0 : ‖(0 : Point n)‖ ≤ uniformFlowRadius g gi hC hK - ‖v‖ := by
    rw [norm_zero]; linarith
  obtain ⟨hJf00, hJf0ode, hUf00, hUf0ode⟩ := hprops 0 hadm0
  simp only [add_zero] at hJf0ode hUf0ode
  -- base tube continuity + field bounds.
  have hYcont : ContinuousOn (uniformFlowTube g gi hC hK q v) (Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq v hvρ.le τ hτoo).continuousAt).continuousWithinAt
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := fun τ hτ => (hVd τ hτ).continuousWithinAt
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1) := fun τ hτ => (hWd τ hτ).continuousWithinAt
  -- geodesicField-Jacobian bound along the tube.
  obtain ⟨KG, hKGbd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun τ => fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ))
    (((contDiff_geodesicField g gi hC).continuous_fderiv (by simp)).comp_continuousOn hYcont)
  have hKGb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ)‖ ≤ max KG 0 :=
    fun τ hτ => (hKGbd τ hτ).trans (le_max_left _ _)
  have hJf0eqV : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Jf 0 τ = V τ := by
    intro τ hτ
    refine autonomousLinODE_within_unique (geodesicField g gi) (le_max_right KG 0)
      (Y0 := uniformFlowTube g gi hC hK q v) (J₁ := Jf 0) (J₂ := V) hKGb
      (fun s hs => (hJf0ode s hs).hasDerivWithinAt) hVd ?_ hτ
    rw [hJf00, hV0]
  -- doubledField-Jacobian bound along `(tube, V)`.
  obtain ⟨KD, hKDbd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun τ => fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q v τ, V τ))
    (((contDiff_doubledField g gi hC).continuous_fderiv (by simp)).comp_continuousOn
      (hYcont.prodMk hVcont))
  have hKDb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q v τ, V τ)‖ ≤ max KD 0 :=
    fun τ hτ => (hKDbd τ hτ).trans (le_max_left _ _)
  have hUf0eqVW : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Uf 0 τ = (V τ, W τ) := by
    intro τ hτ
    refine autonomousLinODE_within_unique (doubledField g gi) (le_max_right KD 0)
      (Y0 := fun t => (uniformFlowTube g gi hC hK q v t, V t)) (J₁ := Uf 0)
      (J₂ := fun t => (V t, W t)) hKDb ?_ ?_ ?_ hτ
    · intro s hs
      have h : HasDerivWithinAt (Uf 0)
          (fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q v s, Jf 0 s) (Uf 0 s))
          (Set.Icc (0 : ℝ) 1) s := (hUf0ode s hs).hasDerivWithinAt
      rw [hJf0eqV s hs] at h
      exact h
    · intro s hs
      exact doubledPair_hasDerivWithinAt g gi hC hs (hVd s hs) (hWd s hs)
    · simp [hUf00, hV0, hW0]
  -- ===== Identify `Vf a = Xcmp` on `[0,1]` (within-uniqueness at `Φ̃`). =====
  set Bc : ℝ → ((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n)) :=
    fun τ => ((uniformFlowTube g gi hC hK q v τ, V τ), (V τ, W τ)) with hBcdef
  have hBccont : ContinuousOn Bc (Set.Icc (0 : ℝ) 1) :=
    (hYcont.prodMk hVcont).prodMk (hVcont.prodMk hWcont)
  obtain ⟨KQ, hKQbd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun τ => fderiv ℝ (genericDoubled (doubledField g gi)) (Bc τ))
    (((contDiff_quadrupledField g gi hC).continuous_fderiv (by simp)).comp_continuousOn hBccont)
  have hKQb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (genericDoubled (doubledField g gi)) (Bc τ)‖ ≤ max KQ 0 :=
    fun τ hτ => (hKQbd τ hτ).trans (le_max_left _ _)
  have hVfaBc : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (Vf a)
        (fderiv ℝ (genericDoubled (doubledField g gi)) (Bc τ) (Vf a τ)) (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have h : HasDerivWithinAt (Vf a)
        (fderiv ℝ (genericDoubled (doubledField g gi))
          (((uniformFlowTube g gi hC hK q (v + 0) τ, Jf 0 τ), Uf 0 τ)) (Vf a τ))
        (Set.Icc (0 : ℝ) 1) τ := (hVfode a τ hτ).hasDerivWithinAt
    have hbase : ((uniformFlowTube g gi hC hK q (v + 0) τ, Jf 0 τ), Uf 0 τ) = Bc τ := by
      rw [hBcdef, add_zero, hJf0eqV τ hτ, hUf0eqVW τ hτ]
    rw [hbase] at h
    exact h
  have hXcmpBc : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => ((V t, W t), (W t, Z₃ t)))
        (fderiv ℝ (genericDoubled (doubledField g gi)) (Bc τ) ((V τ, W τ), (W τ, Z₃ τ)))
        (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have := comparisonField_hasDerivWithinAt g gi hC hτ (hVd τ hτ) (hWd τ hτ) (hZ3d τ hτ)
    rw [hBcdef]; exact this
  have hVfaEq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Vf a τ = ((V τ, W τ), (W τ, Z₃ τ)) := by
    intro τ hτ
    refine autonomousLinODE_within_unique (genericDoubled (doubledField g gi)) (le_max_right KQ 0)
      (Y0 := Bc) (J₁ := Vf a) (J₂ := fun t => ((V t, W t), (W t, Z₃ t))) hKQb
      (fun s hs => by simpa using hVfaBc s hs)
      (fun s hs => by simpa using hXcmpBc s hs) ?_ hτ
    simp [hVf0, hV0, hW0, hZ30]
  -- ===== Assemble the cubic bound. =====
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hval : (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v)
      a a a = (Z₃ 1).1 := by
    rw [hB₃eq, hL₃eq]
    show proj (L a) = (Z₃ 1).1
    rw [hLeq a, hVfaEq 1 ht1]
    simp [hprojdef]
  rw [hval]
  calc ‖(Z₃ 1).1‖ ≤ ‖Z₃ 1‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ M₃j * ‖a‖ ^ 3 := hZ3bnd 1 ht1

/-- **X2 — W3 UNCONDITIONAL.**  The uniform operator-norm bound on the third jet `B₃` of `uniformFlowExp`
    over a compact `K`, from ONLY `hC` + `IsCompact K` — no carried diagonal bound.  Feeds X1's cubic
    diagonal bound to `uniformFlowExp_thirdDeriv_opNorm_le_of_diag_bound` (J4-76). -/
theorem uniformFlowExp_thirdDeriv_opNorm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ M₃ : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
      ‖fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v‖ ≤ M₃ := by
  obtain ⟨r₀, hr₀0, hrρ, M₃', hM₃'0, hdiag⟩ :=
    uniformFlowExp_thirdDeriv_diag_cubic_bound g gi hC hK
  obtain ⟨M₃, hM₃⟩ :=
    uniformFlowExp_thirdDeriv_opNorm_le_of_diag_bound g gi hC hK hM₃'0 hrρ hdiag
  exact ⟨r₀, hr₀0, M₃, hM₃⟩

end Uncond

end QIQTH.ExpMap
