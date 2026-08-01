/-
  UniformFlowThirdBoundClose — J4-76 (Brick-A β, C³ climb): the CLM-VALUED third jet, its two
  symmetries (P2), and the W3 operator-norm bound (conditional on the diagonal cubic bound, P1
  firewalled) for `uniformFlowExp`.

  ## Context

  * W1 (`UniformFlowThirdJet`, `uniformFlowTube_thirdVariation_uniform_bound`) — the intrinsic THIRD-
    variation field `Z₃` along the base tube with a UNIFORM diagonal cubic bound `‖Z₃ τ‖ ≤ M₃j·‖a‖³`.
  * W2 (`UniformFlowThirdJetClose`, `uniformFlow_thirdJet_hasFDerivAt`) — the per-seed THIRD jet
    existence `∃ L₃, HasFDerivAt (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) a b) L₃ v`.
  * J4-75 (`UniformFlowThirdBound`, `trilinear_opNorm_le_of_symm_diag_bound`) — a fully-symmetric bounded
    trilinear `B` with `‖B a a a‖ ≤ M‖a‖³` (`M ≥ 0`) has `‖B‖ ≤ (9/2)M`.
  * R2 (`UniformFlowHessian`, `uniformFlowExp_fderiv_hasFDerivAt`) — the CLM-valued Hessian
    `HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp q) w) B₂ v` at every interior velocity.
  * R3 (`UniformFlowHessianBound`, `uniformFlowExp_hessian_symm` + `bilinear_opNorm_le_of_symm_diag_bound`
    + `uniformFlowExp_hessian_opNorm_le_of_diag_bound`) — the C² analogue landed here ONE ORDER DOWN,
    conditional on the diagonal Hessian bound.

  ## The chosen `B₃` form

  `B₃(q,v) := fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v`
        `: Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n`
  — the GENUINE (non-vacuous) CLM-valued third Fréchet jet: the `w`-derivative of the CLM-valued Hessian
  map, packaged as a trilinear CLM.  `B₃ c a b` = (derivative direction `c`, Hessian slots `a`, `b`).
  This is the piRing-lifted CLM-valued form the mission calls out — it admits the P2 proofs (its slots
  are genuine iterated Fréchet derivatives, so Clairaut applies) and W4 can consume it (`‖B₃(q,v)‖` is
  the operator norm the C³ bound speaks about).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no `expRho`)

  * `uniformFlowExp_hessianMap_differentiableAt` (**D1, the CLM-valued third jet**) — the CLM-valued
    Hessian map `w ↦ fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w` is Fréchet-differentiable at
    `v` (`‖v‖ < ρ_K`).  DERIVED by the DOUBLE `differentiableAt_pi` / `ContinuousLinearEquiv.piRing`
    lift of W2's per-seed derivatives on the standard basis — exactly R2's lift ONE ORDER UP (an extra
    `piRing` layer for the doubled codomain `Point n →L[ℝ] Point n →L[ℝ] Point n`).  So
    `B₃ = fderiv ℝ (…) v` is the GENUINE derivative, not a junk `fderiv`.

  * `uniformFlowExp_thirdJet_symm23` (**P2/hs23**) — `B₃ c a b = B₃ c b a` (swap the two Hessian slots).
    DERIVED from `uniformFlowExp_hessian_symm` (the Hessian is a symmetric bilinear form on the ball) via
    `Filter.EventuallyEq.fderiv_eq` fed the flip continuous-linear equivalence: `flip ∘ f₂ =ᶠ f₂` ⟹
    `flip ∘L B₃ = B₃`.

  * `uniformFlowExp_thirdJet_symm12` (**P2/hs12**) — `B₃ c a b = B₃ a c b` (swap the derivative
    direction with the first Hessian slot).  DERIVED via Clairaut
    (`second_derivative_symmetric_of_eventually_of_real`) for the map `u ↦ fderiv ℝ (uniformFlowExp q) u b`,
    whose first derivative is `ev_b ∘L (Hessian)` (eventual, from R2) and whose second derivative is
    `(ev_b ∘L ·) ∘L B₃` (from D1).

  * `uniformFlowExp_thirdDeriv_opNorm_le_of_diag_bound` (**W3, assembled, CONDITIONAL on the diagonal
    cubic bound**) — given a uniform diagonal bound `‖B₃(q,v) a a a‖ ≤ M‖a‖³` over `K`, `‖v‖ < r₀ ≤ ρ_K`,
    the two symmetries plus `trilinear_opNorm_le_of_symm_diag_bound` give the UNIFORM operator-norm bound
        `∃ M', ∀ q ∈ K, ∀ ‖v‖ < r₀, ‖B₃(q,v)‖ ≤ M'`   (with `M' = (9/2)·M`).
    This is the exact one-order-up mirror of R3's `uniformFlowExp_hessian_opNorm_le_of_diag_bound`.  The
    diagonal bound `hdiag` is a GENUINE carried input, NOT the conclusion.  NO `expRho`.

  ## HONEST FIREWALL (binding) — P1, the diagonal VALUE ID (the one carried input)

  W3 is closed CONDITIONALLY on the uniform diagonal cubic bound `‖B₃(q,v) a a a‖ ≤ M₃j·‖a‖³`.  What is
  NOT discharged here is **P1**, the diagonal VALUE identification one order up from Z1
  (`uniformFlowExp_hessian_value_id`):
      `B₃(q,v) a a a = (Z₃ 1).?`  connecting the diagonal of the genuine third jet to W1's intrinsic
  third-variation field endpoint `Z₃` (`uniformFlowTube_thirdVariation_uniform_bound`, `‖Z₃ 1‖ ≤ M₃j‖a‖³`).
  As with R3's firewalled diagonal Hessian bound, this is a whole-file identification brick: the diagonal
  is `d/ds[B₂(v+s·a) a a]|₀`, which by Z1 is `d/ds[(U_s 1).2.1]|₀`, the object J4-73's quadruple machinery
  differentiates; the `s`-linearization of the `(J_s, U_s)` system is precisely W1's third-variation ODE
  (`Src₃ = D³F(V,V,V) + 2·D²F(V,W) + D²F(W,V)`), so ODE-uniqueness identifies the two endpoints, whence
  W1's cubic bound.  That identification is CARRIED (a genuine input, not assumed as the conclusion), NOT
  firewalled by a vacuous hypothesis.  W3 with P1 in hand is a one-line specialization of the theorem
  below with `M := M₃j`.

  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.  NO `expRho`.  W4 (`uniformFlowExp ∈ C³ ⟹
  g̃ ∈ C²` assembly) remains the next step.
-/
import QIQTH.UniformFlowThirdBound
import QIQTH.UniformFlowThirdJetClose
import QIQTH.QuadrupleFlowSupply
import QIQTH.UniformFlowThirdJet
import QIQTH.UniformFlowHessianBound
import QIQTH.UniformFlowHessian
import QIQTH.JacobiOperatorFDeriv
import QIQTH.UniformFlowSecondFDeriv
import QIQTH.UniformFlowThirdFDeriv
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

variable {n : ℕ}

/-! ### D1 — the CLM-valued third jet (double-piRing lift of W2) -/

/-- **D1 — the CLM-valued Hessian map is Fréchet-differentiable at `v`.**  For `q ∈ K` and `‖v‖ < ρ_K`,
    the operator-valued Hessian map
        `w ↦ fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w
              : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n)`
    is `DifferentiableAt ℝ` at `v`.  Assembled from W2 (`uniformFlow_thirdJet_hasFDerivAt`) — the per-seed
    third jets on the standard basis `(Pi.single i 1, Pi.single j 1)` — via the DOUBLE evaluation `≃L`
    `ContinuousLinearEquiv.piRing` and `differentiableAt_pi`, exactly mirroring R2's single-layer lift.
    Hence `fderiv ℝ (…) v` is the GENUINE third Fréchet jet. -/
theorem uniformFlowExp_hessianMap_differentiableAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) :
    DifferentiableAt ℝ
      (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v := by
  classical
  set f2 : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w with hf2def
  -- Outer evaluation `≃L`: `(Point n →L (Point n →L Point n)) ≃L (Fin n → (Point n →L Point n))`.
  set Φ₂ : (Point n →L[ℝ] Point n →L[ℝ] Point n) ≃L[ℝ] (Fin n → (Point n →L[ℝ] Point n)) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n →L[ℝ] Point n) (Fin n) with hΦ₂def
  -- Inner evaluation `≃L`: `(Point n →L Point n) ≃L (Fin n → Point n)`.
  set Φ₁ : (Point n →L[ℝ] Point n) ≃L[ℝ] (Fin n → Point n) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n) (Fin n) with hΦ₁def
  -- Each doubled-basis-coordinate evaluation is differentiable at `v` (W2).
  have hij : ∀ i : Fin n, DifferentiableAt ℝ (fun w => (f2 w) (Pi.single i 1)) v := by
    intro i
    have hΦ₁F : DifferentiableAt ℝ (fun w => Φ₁ ((f2 w) (Pi.single i 1))) v := by
      rw [differentiableAt_pi]
      intro j
      have hEq : (fun w => Φ₁ ((f2 w) (Pi.single i 1)) j)
          = (fun w => (f2 w) (Pi.single i 1) (Pi.single j 1)) := by
        funext w; rfl
      rw [hEq]
      obtain ⟨L₃, hL₃⟩ :=
        uniformFlow_thirdJet_hasFDerivAt g gi hC hK q hq v hv (Pi.single i 1) (Pi.single j 1)
      exact hL₃.differentiableAt
    exact Φ₁.comp_differentiableAt_iff.mp hΦ₁F
  -- Hence `Φ₂ ∘ f2` is differentiable at `v` via `differentiableAt_pi`.
  have hΦ₂F : DifferentiableAt ℝ (fun w => Φ₂ (f2 w)) v := by
    rw [differentiableAt_pi]
    intro i
    have hEq : (fun w => Φ₂ (f2 w) i) = (fun w => (f2 w) (Pi.single i 1)) := by
      funext w; rfl
    rw [hEq]
    exact hij i
  -- Transfer differentiability across the outer `≃L`.
  exact Φ₂.comp_differentiableAt_iff.mp hΦ₂F

/-! ### P2/hs23 — symmetry in the two Hessian slots -/

/-- **P2/hs23 — the third jet is symmetric in the two Hessian slots.**  For `q ∈ K`, `‖v‖ < ρ_K`,
        `B₃ c a b = B₃ c b a`,   `B₃ := fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) v`.
    DERIVED from `uniformFlowExp_hessian_symm` (`f₂ w` is symmetric for `‖w‖ < ρ_K`) via
    `Filter.EventuallyEq.fderiv_eq` and the flip continuous-linear equivalence:
    `flip ∘ f₂ =ᶠ[𝓝 v] f₂` ⟹ `flip ∘L B₃ = B₃`. -/
theorem uniformFlowExp_thirdJet_symm23 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (c a b : Point n) :
    (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) c a b
      = (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) c b a := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set f2 : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w with hf2def
  set B₃ : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n := fderiv ℝ f2 v with hB₃def
  have hD1 : HasFDerivAt f2 B₃ v :=
    (uniformFlowExp_hessianMap_differentiableAt g gi hC hK q hq v hv).hasFDerivAt
  -- The flip continuous-linear equivalence, as a CLM.
  set flipL : (Point n →L[ℝ] Point n →L[ℝ] Point n) →L[ℝ] (Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (Point n) (Point n) (Point n)).toContinuousLinearMap with hflipLdef
  have hflipL_apply : ∀ T : Point n →L[ℝ] Point n →L[ℝ] Point n, flipL T = T.flip := by
    intro T; rfl
  -- `flip ∘ f₂ =ᶠ[𝓝 v] f₂` on the open uniform ball (a nbhd of `v`).
  have hev : (fun w => flipL (f2 w)) =ᶠ[𝓝 v] (fun w => f2 w) := by
    have hball : Metric.ball (0 : Point n) ρ ∈ 𝓝 v := by
      refine Metric.isOpen_ball.mem_nhds ?_
      rw [Metric.mem_ball, dist_zero_right]; exact hv
    refine Filter.eventuallyEq_of_mem hball (fun w hw => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [hflipL_apply]
    refine ContinuousLinearMap.ext (fun x => ContinuousLinearMap.ext (fun y => ?_))
    rw [ContinuousLinearMap.flip_apply]
    exact uniformFlowExp_hessian_symm g gi hC hK q hq w hw y x
  -- Take Fréchet derivatives at `v`: `flip ∘L B₃ = B₃`.
  have hfd1 : fderiv ℝ (fun w => flipL (f2 w)) v = flipL.comp B₃ :=
    (flipL.hasFDerivAt.comp v hD1).fderiv
  have hcollapse : flipL.comp B₃ = B₃ := by
    have h : fderiv ℝ (fun w => flipL (f2 w)) v = fderiv ℝ (fun w => f2 w) v :=
      hev.fderiv_eq
    rw [hfd1] at h
    rw [h]
  -- Read off the slot symmetry.
  have hcflip : (B₃ c).flip = B₃ c := by
    have := congrArg (fun T => T c) hcollapse
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [hflipL_apply] at this
    exact this
  show (B₃ c) a b = (B₃ c) b a
  calc (B₃ c) a b = (B₃ c).flip b a := (ContinuousLinearMap.flip_apply _ _ _).symm
    _ = (B₃ c) b a := by rw [hcflip]

/-! ### P2/hs12 — symmetry in the derivative direction and the first Hessian slot -/

/-- **P2/hs12 — the third jet is symmetric in the derivative direction and the first Hessian slot.**
    For `q ∈ K`, `‖v‖ < ρ_K`,
        `B₃ c a b = B₃ a c b`,   `B₃ := fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) v`.
    DERIVED via Clairaut (`second_derivative_symmetric_of_eventually_of_real`) for `G_b : u ↦ fderiv ℝ
    (uniformFlowExp q) u b`: its first derivative is `ev_b ∘L (Hessian)` (eventual, from R2's
    `uniformFlowExp_fderiv_hasFDerivAt`) and its second derivative is `(ev_b ∘L ·) ∘L B₃` (from D1). -/
theorem uniformFlowExp_thirdJet_symm12 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (c a b : Point n) :
    (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) c a b
      = (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) a c b := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set f1 : Point n → (Point n →L[ℝ] Point n) :=
    fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u with hf1def
  set f2 : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n) := fun w => fderiv ℝ f1 w with hf2def
  set B₃ : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n := fderiv ℝ f2 v with hB₃def
  have hD1 : HasFDerivAt f2 B₃ v :=
    (uniformFlowExp_hessianMap_differentiableAt g gi hC hK q hq v hv).hasFDerivAt
  -- Evaluation-at-`b` CLM `ev_b : (Point n →L Point n) →L Point n`, `ev_b T = T b`.
  set ev_b : (Point n →L[ℝ] Point n) →L[ℝ] Point n :=
    ContinuousLinearMap.apply ℝ (Point n) b with hev_bdef
  have hev_b_apply : ∀ T : Point n →L[ℝ] Point n, ev_b T = T b := fun T => rfl
  -- Post-composition CLM `comp_ev_b : (Point n →L Point n →L Point n) →L (Point n →L Point n)`.
  set comp_ev_b : (Point n →L[ℝ] Point n →L[ℝ] Point n) →L[ℝ] (Point n →L[ℝ] Point n) :=
    ContinuousLinearMap.compL ℝ (Point n) (Point n →L[ℝ] Point n) (Point n) ev_b with hcomp_ev_bdef
  have hcomp_ev_b_apply : ∀ T : Point n →L[ℝ] Point n →L[ℝ] Point n, comp_ev_b T = ev_b.comp T :=
    fun T => rfl
  -- `G_b := fun u => f1 u b` = `ev_b ∘ f1`.
  -- (i) eventual first derivative: `HasFDerivAt G_b (comp_ev_b (f2 y)) y` for `‖y‖ < ρ`.
  have hf : ∀ᶠ y in 𝓝 v, HasFDerivAt (fun u => (f1 u) b) (comp_ev_b (f2 y)) y := by
    have hball : Metric.ball (0 : Point n) ρ ∈ 𝓝 v := by
      refine Metric.isOpen_ball.mem_nhds ?_
      rw [Metric.mem_ball, dist_zero_right]; exact hv
    refine Filter.eventually_of_mem hball (fun y hy => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hy
    obtain ⟨B, hB⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq y hy
    -- `hB : HasFDerivAt f1 B y`, and `f2 y = fderiv f1 y = B`.
    have hBeq : f2 y = B := by rw [hf2def]; exact hB.fderiv
    have hcomp := ev_b.hasFDerivAt.comp y hB
    -- `⇑ev_b ∘ f1 = fun u => f1 u b`; `ev_b.comp B = comp_ev_b (f2 y)`.
    rw [hcomp_ev_b_apply, hBeq]
    exact hcomp
  -- (ii) second derivative: `HasFDerivAt (fun w => comp_ev_b (f2 w)) (comp_ev_b.comp B₃) v`.
  have hx : HasFDerivAt (fun w => comp_ev_b (f2 w)) (comp_ev_b.comp B₃) v :=
    comp_ev_b.hasFDerivAt.comp v hD1
  -- Clairaut.
  have hsymm := second_derivative_symmetric_of_eventually_of_real
    (f := fun u => (f1 u) b) (f' := fun w => comp_ev_b (f2 w)) (f'' := comp_ev_b.comp B₃)
    (x := v) hf hx a c
  -- Reduce `(comp_ev_b.comp B₃) a c = B₃ a c b`, `(comp_ev_b.comp B₃) c a = B₃ c a b`.
  have hval : ∀ p r : Point n, (comp_ev_b.comp B₃) p r = (B₃ p) r b := by
    intro p r
    simp only [ContinuousLinearMap.comp_apply, hcomp_ev_b_apply, hev_b_apply]
  rw [hval a c, hval c a] at hsymm
  -- `hsymm : (B₃ a) c b = (B₃ c) a b`.
  show (B₃ c) a b = (B₃ a) c b
  exact hsymm.symm

/-! ### W3 — the uniform operator-norm bound on the third jet (conditional on the diagonal bound) -/

/-- **W3 (assembled, conditional).**  Given a uniform DIAGONAL cubic bound over `K`
    (`‖B₃(q,v) a a a‖ ≤ M‖a‖³` for `q ∈ K`, `‖v‖ < r₀ ≤ ρ_K`,
    `B₃(q,v) := fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) v`),
    the two symmetries (`uniformFlowExp_thirdJet_symm12`, `uniformFlowExp_thirdJet_symm23`) plus the
    trilinear polarization operator-norm bound (`trilinear_opNorm_le_of_symm_diag_bound`) give the
    UNIFORM operator-norm bound
        `∃ M', ∀ q ∈ K, ∀ ‖v‖ < r₀, ‖B₃(q,v)‖ ≤ M'`   (with `M' = (9/2)·M`), uniform over `q ∈ K`.
    The diagonal bound `hdiag` is a GENUINE carried input (the firewalled P1 value id + W1's cubic bound),
    NOT the conclusion.  This is the exact one-order-up mirror of R3's
    `uniformFlowExp_hessian_opNorm_le_of_diag_bound`.  No `expRho`. -/
theorem uniformFlowExp_thirdDeriv_opNorm_le_of_diag_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {r₀ M : ℝ} (hM : 0 ≤ M)
    (hrρ : r₀ ≤ uniformFlowRadius g gi hC hK)
    (hdiag : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ a : Point n,
      ‖(fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) a a a‖
        ≤ M * ‖a‖ ^ 3) :
    ∃ M' : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
      ‖fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v‖ ≤ M' := by
  refine ⟨(9 / 2) * M, ?_⟩
  intro q hq v hv
  have hvρ : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv hrρ
  exact trilinear_opNorm_le_of_symm_diag_bound
    (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v)
    (fun u v' w => uniformFlowExp_thirdJet_symm12 g gi hC hK q hq v hvρ u v' w)
    (fun u v' w => uniformFlowExp_thirdJet_symm23 g gi hC hK q hq v hvρ u v' w)
    hM (fun a => hdiag q hq v hv a)

end QIQTH.ExpMap
