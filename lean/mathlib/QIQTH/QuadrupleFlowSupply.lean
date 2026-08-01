/-
  QuadrupleFlowSupply — J4-73 (Brick-A β, C³ climb): the QUADRUPLE-flow SUPPLY (Y1/Y2/Y3), the
  base-velocity Fréchet derivative of the quadrupled-flow endpoint, one order up from J4-67's R2-a arc.

  ## Context

  * J4-66 (`UniformFlowSecondFDeriv`, `autonomousFlow_endpoint_hasFDerivAt_window_exists`) is the
    field-AGNOSTIC σ-windowed Fréchet FIRST-jet engine: for a field `Φ`, a base-perturbed family `W δ`
    of `Φ`-integral curves confined in a compact convex `S`, GLOBALLY defined `Φ`-linearized fields
    `V δ`, and a norm-preserving seed, the endpoint `δ ↦ W δ t` is Fréchet-differentiable at `0`.
  * J4-67 (`UniformFlowSecondSupply`, R2-a `uniformFlow_doubledEndpoint_baseVelocity_hasFDerivAt`) fed
    the base-velocity-perturbed CONFINED DOUBLED uniform-tube supply to that engine with
    `Φ := doubledField g gi`, yielding the per-direction Fréchet SECOND jet of `uniformFlowExp`.
  * J4-72 (`UniformFlowThirdFDeriv`) built the QUADRUPLED field `Φ̃ := genericDoubled (doubledField g gi)`
    with its full regularity supply (`contDiff_quadrupledField`, `quadrupledField_fderiv_bddOn_compact`,
    `quadrupledField_fderiv2_bddOn_compact`) — the engine-regularity inputs one order up.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled 3rd-order conclusion,
  no `expRho`)

  * `genericDoubled_prod_hasDerivAt` (**Y1, field-agnostic**) — the `Φ̃`-integral-curve repackaging: if
    `Y` is a `Φ`-integral curve (`Y' = Φ(Y)`) and `U` is the `Φ`-linearized field along it
    (`U' = DΦ(Y)·U`), then the pair `(Y, U)` is a genuine `genericDoubled Φ`-integral curve.  Pure
    product rule — the exact analogue of `doubledField_prod_hasDerivAt` one order up.

  * `uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt` (**Y2+Y3, the quadruple-flow supply**) —
    for `q ∈ K`, `‖v‖ < ρ_K`, and seeds `a b`, there are a velocity-Jacobi family `Jf` (seed `(0,b)`,
    the geodesic-linearized field along `uniformFlowTube q (v+δ)`) and a doubled-linearized family `Uf`
    (seed `((0,a),(0,0))`, the `doubledField`-linearized field along the doubled base curve
    `(uniformFlowTube q (v+δ), Jf δ)`) such that the QUADRUPLED-flow endpoint
        `δ ↦ (((uniformFlowTube q (v+δ) 1, Jf δ 1), Uf δ 1))`
    is Fréchet-differentiable at `0`.  A GENUINE confined `Φ̃`-integral-curve family: the doubled base
    curve is the R2-a confined doubled uniform tube; the `Uf` factor is a genuine `doubledField`-
    linearized field along it (`linODE_exists_narrowpad_continuousOn`, Grönwall-confined via
    `doubledField_fderiv_bddOn_compact`); the pair is a `Φ̃`-integral curve (`genericDoubled_prod_hasDerivAt`);
    the `Φ̃`-linearized field along the fixed base quadruple curve via `linODE_exists_narrowpad_continuousOn`;
    fed to `autonomousFlow_endpoint_hasFDerivAt_window_exists` with `Φ := Φ̃`, discharging all quadruple-
    field regularity inputs from J4-72.  NOT vacuous; NO `expRho`.

  * `uniformFlow_quadrupleEndpoint_component_hasFDerivAt` (**Y3′, the projected scalar-slot component**) —
    the base-velocity Fréchet derivative of the doubled-linearized endpoint's `.2.1` component:
        `∃ L₃, HasFDerivAt (fun δ => (Uf δ 1).2.1) L₃ 0`.
    DERIVED by projecting `.2.2.1` of the Y3 endpoint derivative.

  ## HONEST FIREWALL (binding) — what W2 still needs (Y4, the value-identification)

  Y1/Y2/Y3/Y3′ land here fully.  The per-seed THIRD-jet target W2
      `∃ L₃, HasFDerivAt (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) a b) L₃ v`
  is NOT closed here.  What remains is the value-IDENTIFICATION (Y4), one order up from J4-67's
  `uniformFlowExp_fderiv_apply_eq`/R2-b:
      `(Uf δ 1).2.1 = fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w b) (v+δ) a`
  on the velocity window — i.e. that the `doubledField`-linearized (second-variation) endpoint's `.2.1`
  component IS the `a`-derivative of the applied second jet `w ↦ fderiv (uniformFlowExp q) w b`.  This is
  the `hid_of_doubled_data`/`uniformFlowExp_fderiv_apply_eq` value-id ONE ORDER UP (a
  `doubledVariation`-endpoint ↔ second-jet-derivative identity), plus the recentre `δ ↦ v+δ`.  Once that
  identity is in hand, `uniformFlow_quadrupleEndpoint_component_hasFDerivAt` recentres to W2 exactly as
  R2-b recentred R2-a.  CARRIED.  W3 (uniform `‖B₃‖` bound) and W4 (`uniformFlowExp ∈ C³ ⟹ g̃ ∈ C²`)
  CARRIED as before.  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.  NO `expRho`.
-/
import QIQTH.UniformFlowThirdFDeriv
import QIQTH.UniformFlowSecondSupply
import QIQTH.UniformFlowHessianDiag
import QIQTH.UniformFlowSecondFDeriv
import QIQTH.DoubledVariationField
import QIQTH.DoubledFamilyConstruction
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.AutonomousDep
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

/-! ### Y1 — the `Φ̃`-integral-curve repackaging (field-agnostic) -/

section GenericProd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Y1 — a `genericDoubled Φ`-integral curve = `Φ`-integral curve ⊗ `Φ`-linearized field.**  If `Y`
    solves the `Φ`-flow ODE `Y' = Φ(Y)` and `U` solves the `Φ`-linearized ODE `U' = DΦ(Y)·U` along `Y`,
    then the PAIR `τ ↦ (Y τ, U τ)` is a genuine integral curve of `genericDoubled Φ`:
        `HasDerivAt (fun t => (Y t, U t)) (genericDoubled Φ (Y τ, U τ)) τ`.
    Field-agnostic mirror of `doubledField_prod_hasDerivAt` one order up: since
    `genericDoubled Φ (Y τ, U τ) = (Φ (Y τ), fderiv ℝ Φ (Y τ) (U τ))`, the pair's derivative
    (`HasDerivAt.prodMk`) is by definition `Φ̃` at the pair — pure product rule. -/
theorem genericDoubled_prod_hasDerivAt (Φ : E → E) {Y U : ℝ → E} {τ : ℝ}
    (hY : HasDerivAt Y (Φ (Y τ)) τ)
    (hU : HasDerivAt U (fderiv ℝ Φ (Y τ) (U τ)) τ) :
    HasDerivAt (fun t => (Y t, U t)) (genericDoubled Φ (Y τ, U τ)) τ := by
  have h := hY.prodMk hU
  simpa [genericDoubled] using h

end GenericProd

/-! ### Y2 + Y3 — the base-velocity-perturbed confined quadruple uniform-tube supply -/

section Supply

variable {n : ℕ}

/-- **Y2+Y3 — the base-velocity-perturbed confined quadruple uniform-tube supply, fed to J4-66.**  For
    `q ∈ K`, `‖v‖ < ρ_K`, and seeds `a b`, there are a velocity-Jacobi family `Jf` and a doubled-
    linearized family `Uf` such that, for `‖δ‖ ≤ ρ_K − ‖v‖`:
      * `Jf δ` is the geodesic-linearized (velocity Jacobi) field along `uniformFlowTube q (v+δ)`, seed
        `Jf δ 0 = (0, b)` (the R2-a inner Jacobi factor);
      * `Uf δ` is the `doubledField`-linearized field along the doubled base curve
        `(uniformFlowTube q (v+δ), Jf δ)`, seed `Uf δ 0 = ((0,a),(0,0))` (the base-velocity second
        variation);
    and the QUADRUPLED-flow endpoint `δ ↦ (((uniformFlowTube q (v+δ) 1, Jf δ 1), Uf δ 1))` is Fréchet-
    differentiable at `0`.  GENUINE confined `Φ̃`-integral-curve supply (not vacuous); NO `expRho`. -/
theorem uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
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
      ∃ L : Point n →L[ℝ]
          ((Point n × Point n) × (Point n × Point n)) × ((Point n × Point n) × (Point n × Point n)),
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
  -- Geodesic-factor confinement ball + uniform `fderiv (geodesicField)` bound for the Jacobi Grönwall.
  have hAcompact : IsCompact (Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ)) :=
    isCompact_closedBall _ _
  obtain ⟨Kb, hKb0, hKbbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hAcompact
  set Jbound : ℝ := ‖((0 : Point n), b)‖ * Real.exp Kb with hJbounddef
  have hJbound0 : 0 ≤ Jbound := by rw [hJbounddef]; positivity
  -- Doubled base confinement ball (= R2-a's `S`) + uniform `fderiv (doubledField)` bound.
  set Sdbl : Set ((Point n × Point n) × (Point n × Point n)) :=
    Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) ×ˢ
      Metric.closedBall (0 : Point n × Point n) Jbound with hSdbldef
  have hSdblcompact : IsCompact Sdbl := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨Kb2, hKb20, hKb2bd⟩ := doubledField_fderiv_bddOn_compact g gi hC hSdblcompact
  set Useed : (Point n × Point n) × (Point n × Point n) :=
    (((0 : Point n), a), ((0 : Point n), (0 : Point n))) with hUseeddef
  set Ubound : ℝ := ‖Useed‖ * Real.exp Kb2 with hUbounddef
  have hUbound0 : 0 ≤ Ubound := by rw [hUbounddef]; positivity
  -- The full quadruple confinement set.
  set S : Set (((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n))) :=
    Sdbl ×ˢ Metric.closedBall (0 : (Point n × Point n) × (Point n × Point n)) Ubound with hSdef
  have hScompact : IsCompact S := hSdblcompact.prod (isCompact_closedBall _ _)
  have hSconvex : Convex ℝ S :=
    ((convex_closedBall _ _).prod (convex_closedBall _ _)).prod (convex_closedBall _ _)
  have hcontDbl : Continuous (fderiv ℝ (doubledField g gi)) :=
    (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
  -- Per-δ: velocity Jacobi `Jc` and doubled-linearized `Uc`, genuine + confined when `‖v+δ‖ ≤ ρ`.
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
      -- doubled base curve `(P, Jc)`, padded continuous.
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
  -- The base quadruple curve `W0 = ((tube v, Jf 0), Uf 0)`, padded continuous.
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
  -- The `Φ̃`-linearized field `Vf δ` along the fixed base quadruple curve `W0`.
  have hcontQuad : Continuous (fderiv ℝ (genericDoubled (doubledField g gi))) :=
    (contDiff_quadrupledField g gi hC).continuous_fderiv (by simp)
  set Aquad : ℝ → ((((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n))) →L[ℝ]
      (((Point n × Point n) × (Point n × Point n)) ×
        ((Point n × Point n) × (Point n × Point n)))) :=
    fun τ => fderiv ℝ (genericDoubled (doubledField g gi)) (W0 τ) with hAquaddef
  have hAquad : ContinuousOn Aquad (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    hcontQuad.comp_continuousOn hW0pad
  -- The base-velocity seed CLM `δ ↦ (((0,δ),(0,0)),((0,0),(0,0)))`.
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
  -- The per-δ `Φ̃`-linearized field along `W0`, seed `seedCLM δ`.
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
  -- The perturbed quadruple family `W̃ δ = ((tube (v+δ), Jf δ), Uf δ)`.
  set W : Point n → ℝ → ((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n)) :=
    fun δ t => ((uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t), Uf δ t) with hWdef
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  -- Engine regularity inputs (one order up, from J4-72).
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
  -- Discharge the engine's supply hypotheses.
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
  -- Feed the abstract first-jet engine with `Φ := Φ̃`.
  obtain ⟨L, _hLeq, hFD⟩ :=
    autonomousFlow_endpoint_hasFDerivAt_window_exists (genericDoubled (doubledField g gi))
      (W := W) (V := Vf) (seed := seedCLM) (S := S) hKf0 hσ ht1 hSconvex hdiff hdiff2 hbound2 hLip
      hseednorm hWode hVode hV0 hIC hKb hmem
  refine ⟨Jf, Uf, ?_, L, ?_⟩
  · intro δ hδ
    obtain ⟨hJfδ0, hJfode, _, _, hUfδ0, hUfode, _, _⟩ := hspec δ (hle δ hδ)
    exact ⟨hJfδ0, hJfode, hUfδ0, hUfode⟩
  · -- rewrite the engine endpoint `W δ 1` into the stated tuple.
    have hfe : (fun δ => W δ 1)
        = (fun δ => (((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1), Uf δ 1) :
            ((Point n × Point n) × (Point n × Point n)) ×
              ((Point n × Point n) × (Point n × Point n)))) := by
      funext δ; rw [hWdef]
    rw [hfe] at hFD
    exact hFD

/-! ### Y3′ — the projected doubled-linearized endpoint's `.2.1` component -/

/-- **Y3′ — the base-velocity Fréchet derivative of the doubled-linearized endpoint's `.2.1`
    component.**  Projecting `.2` (the `Uf` factor) then `.2.1` of the quadruple-flow endpoint derivative
    (Y3), the map `δ ↦ (Uf δ 1).2.1` is Fréchet-differentiable at `0`.  This is the object the W2
    value-identification (Y4, firewalled) rewrites to the third jet
    `fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp q) w b) (v+δ) a`.  NO `expRho`. -/
theorem uniformFlow_quadrupleEndpoint_component_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
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
      ∃ L₃ : Point n →L[ℝ] Point n,
        HasFDerivAt (fun δ => (Uf δ 1).2.1) L₃ 0 := by
  obtain ⟨Jf, Uf, hprops, L, hFD⟩ :=
    uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt g gi hC hK q hq v hv a b
  refine ⟨Jf, Uf, hprops, ?_⟩
  -- projection `Ẽ → Point n`, `((_,_),(u1,u2)) ↦ u2.1`.
  set proj : (((Point n × Point n) × (Point n × Point n)) ×
      ((Point n × Point n) × (Point n × Point n))) →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp
      ((ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).comp
        (ContinuousLinearMap.snd ℝ ((Point n × Point n) × (Point n × Point n))
          ((Point n × Point n) × (Point n × Point n)))) with hprojdef
  refine ⟨proj.comp L, ?_⟩
  have hc := proj.hasFDerivAt.comp (0 : Point n) hFD
  have hfe : (⇑proj ∘ fun δ => (((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1), Uf δ 1) :
      ((Point n × Point n) × (Point n × Point n)) ×
        ((Point n × Point n) × (Point n × Point n))))
      = (fun δ => (Uf δ 1).2.1) := by
    funext δ
    simp [hprojdef]
  rw [hfe] at hc
  exact hc

end Supply

end QIQTH.ExpMap

