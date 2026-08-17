/-
  UniformFlowExpContDiffThreeUniform — Plan v6 Task I (C³ climb, capstone): the per-seed FOURTH jet
  (`W2↑`), the CLM-valued third-jet map differentiability (triple-piRing lift), the per-point `C³`
  assembly, and the UNCONDITIONAL `ContDiffOn ℝ 3` target shape for the flow-exponential on the uniform
  confinement ball.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  NOT `a₁ = R/6`.  This closes the order-3 realisation of the Plan-v6 target
  `uniformFlowExp_contDiffOn_four_uniform` — re-deriving the C³ regularity DIRECTLY on the uniform tube,
  with NO `expRho` anywhere.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms, NO `expRho`).
    • `uniformFlow_fourthJet_hasFDerivAt` (**W2↑**) — for `q ∈ K`, `‖v‖ < ρ_K`, seeds `a b c`, the
        applied third jet `w ↦ (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w') w) c a b`
        is Fréchet-differentiable at `v`.  DERIVED by transferring the octuple-flow endpoint derivative
        (`uniformFlow_octupleEndpoint_component_hasFDerivAt`, J4-778) across the eventual equality
        `(Tf δ 1).2.2.1 = B₃ (v+δ) c a b` (Z1↑, `uniformFlowExp_thirdJet_value_id`, J4-780) on the open
        velocity window, then recentring `δ ↦ v + δ` — the exact W2 template one order up.
    • `uniformFlowExp_thirdJetMap_differentiableAt` (**D1↑**) — the CLM-valued third-jet map
        `w ↦ fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w') w` is
        `DifferentiableAt ℝ` at `v`.  Assembled from W2↑ via the TRIPLE evaluation `≃L`
        `ContinuousLinearEquiv.piRing` + `differentiableAt_pi` on the standard basis — exactly the
        double-piRing `uniformFlowExp_hessianMap_differentiableAt` lift ONE ORDER UP.
    • `contDiffAt3_uniformFlowExp` — `ContDiffAt ℝ 3 (uniformFlowExp q) v` for `‖v‖ < ρ_K`, assembled
        from the FOUR Fréchet layers (`uniformFlowExp_hasFDerivAt`, `uniformFlowExp_fderiv_hasFDerivAt`,
        `uniformFlowExp_hessianMap_differentiableAt`, and D1↑), each valid on the ball, fed three times
        through `contDiffAt_succ_iff_hasFDerivAt` with the last step `contDiffAt_zero` via `ContinuousOn`
        of the third jet.  The order-3 mirror of `contDiffAt2_uniformFlowExp`.
    • `uniformFlowExp_contDiffOn_three_uniform` (**★ the target shape**) — for every `q ∈ K`,
          `ContDiffOn ℝ 3 (uniformFlowExp g gi hC hK q) (Metric.ball 0 (uniformFlowRadius g gi hC hK))`.
      UNCONDITIONAL; NO `expRho`.  The order-3 realisation of the Plan-v6 target.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowExpFourthJetValueId
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

variable {n : ℕ}

/-! ### W2↑ — the per-seed FOURTH jet (closed) -/

/-- **W2↑ — the per-seed fourth jet of `uniformFlowExp`.**  For `q ∈ K`, `‖v‖ < ρ_K`, and seeds `a b c`,
    the applied third jet
        `w ↦ (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w') w) c a b`
    is Fréchet-differentiable at `v`:
        `∃ L₄, HasFDerivAt (fun w => (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w') w) c a b) L₄ v`.
    DERIVED by transferring J4-778's `HasFDerivAt (fun δ => (Tf δ 1).2.2.1) L₄ 0` across the eventual
    equality `(Tf δ 1).2.2.1 = B₃ (v+δ) c a b` (Z1↑ on the open window `‖δ‖ < ρ_K − ‖v‖ ∈ 𝓝 0`) then
    recentring `δ ↦ v + δ`.  NO `expRho`. -/
theorem uniformFlow_fourthJet_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b c : Point n) :
    ∃ L₄ : Point n →L[ℝ] Point n,
      HasFDerivAt
        (fun w => (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w)
          c a b) L₄ v := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  obtain ⟨Jf, Uf, Tf, hprops, L₄, hFD⟩ :=
    uniformFlow_octupleEndpoint_component_hasFDerivAt g gi hC hK q hq v hv a b c
  -- Z1↑ on the open velocity window: `(Tf δ 1).2.2.1 = B₃ (v+δ) c a b`.
  have hEq : (fun δ => (Tf δ 1).2.2.1)
      =ᶠ[𝓝 (0 : Point n)]
      (fun δ => (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w')
        (v + δ)) c a b) := by
    have hball : Metric.ball (0 : Point n) σ ∈ 𝓝 (0 : Point n) := Metric.ball_mem_nhds _ hσ
    refine Filter.eventuallyEq_of_mem hball (fun δ hδ => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hδ
    have hδσ : ‖δ‖ ≤ ρ - ‖v‖ := by rw [← hσdef]; exact hδ.le
    have hvδ : ‖v + δ‖ < ρ := by
      refine lt_of_le_of_lt (norm_add_le v δ) ?_
      rw [hσdef] at hδ; linarith
    obtain ⟨hJf0, hJfode, hUf0, hUfode, hTf0, hTfode⟩ := hprops δ hδσ
    exact (uniformFlowExp_thirdJet_value_id g gi hC hK q hq (v + δ) hvδ a b c
      (Jf δ) hJf0 hJfode (Uf δ) hUf0 hUfode (Tf δ) hTf0 hTfode).symm
  -- Transfer the derivative across the eventual equality.
  have hFD2 : HasFDerivAt
      (fun δ => (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w')
        (v + δ)) c a b) L₄ 0 :=
    hFD.congr_of_eventuallyEq hEq.symm
  -- Recentre `δ ↦ v + δ` (i.e. `w ↦ w − v`).
  have hshift : HasFDerivAt (fun u : Point n => u - v) (ContinuousLinearMap.id ℝ (Point n)) v :=
    (hasFDerivAt_id v).sub_const v
  have hFD0 : HasFDerivAt
      (fun δ => (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w')
        (v + δ)) c a b) L₄ (v - v) := by
    rw [sub_self]; exact hFD2
  have hcomp : HasFDerivAt
      (fun w => (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w')
        (v + (w - v))) c a b)
      (L₄.comp (ContinuousLinearMap.id ℝ (Point n))) v :=
    hFD0.comp (f := fun w : Point n => w - v) v hshift
  have hfun2 : (fun w => (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w')
        (v + (w - v))) c a b)
      = (fun w => (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w)
        c a b) := by
    funext w; congr 3; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  exact ⟨L₄, hcomp⟩

/-! ### D1↑ — the CLM-valued third-jet map (triple-piRing lift of W2↑) -/

/-- **D1↑ — the CLM-valued third-jet map is Fréchet-differentiable at `v`.**  For `q ∈ K` and
    `‖v‖ < ρ_K`, the operator-valued third-jet map
        `w ↦ fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w') w
              : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n)`
    is `DifferentiableAt ℝ` at `v`.  Assembled from W2↑ (`uniformFlow_fourthJet_hasFDerivAt`) — the
    per-seed fourth jets on the standard basis `(Pi.single i 1, Pi.single j 1, Pi.single k 1)` — via the
    TRIPLE evaluation `≃L` `ContinuousLinearEquiv.piRing` and `differentiableAt_pi`, exactly mirroring
    the double-layer `uniformFlowExp_hessianMap_differentiableAt` lift ONE ORDER UP.  Hence
    `fderiv ℝ (…) v` is the GENUINE fourth Fréchet jet. -/
theorem uniformFlowExp_thirdJetMap_differentiableAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) :
    DifferentiableAt ℝ
      (fun w => fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w)
      v := by
  classical
  set f3 : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    fun w => fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w
    with hf3def
  -- Outermost evaluation `≃L`.
  set Φ₃ : (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n)
        ≃L[ℝ] (Fin n → (Point n →L[ℝ] Point n →L[ℝ] Point n)) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n →L[ℝ] Point n →L[ℝ] Point n) (Fin n) with hΦ₃def
  -- Middle evaluation `≃L`.
  set Φ₂ : (Point n →L[ℝ] Point n →L[ℝ] Point n) ≃L[ℝ] (Fin n → (Point n →L[ℝ] Point n)) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n →L[ℝ] Point n) (Fin n) with hΦ₂def
  -- Inner evaluation `≃L`.
  set Φ₁ : (Point n →L[ℝ] Point n) ≃L[ℝ] (Fin n → Point n) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n) (Fin n) with hΦ₁def
  -- Each triple-basis-coordinate evaluation is differentiable at `v` (W2↑).
  have hi : ∀ i : Fin n, DifferentiableAt ℝ (fun w => (f3 w) (Pi.single i 1)) v := by
    intro i
    have hΦ₂F : DifferentiableAt ℝ (fun w => Φ₂ ((f3 w) (Pi.single i 1))) v := by
      rw [differentiableAt_pi]
      intro j
      have hΦ₁F : DifferentiableAt ℝ
          (fun w => Φ₁ ((f3 w) (Pi.single i 1) (Pi.single j 1))) v := by
        rw [differentiableAt_pi]
        intro k
        have hEq : (fun w => Φ₁ ((f3 w) (Pi.single i 1) (Pi.single j 1)) k)
            = (fun w => (f3 w) (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)) := by
          funext w; rfl
        rw [hEq]
        -- W2↑ applies its slots as `c a b` (derivative direction first); pass args so that
        -- `c = single i`, `a = single j`, `b = single k`, giving the `(i, j, k)` order the lift needs.
        obtain ⟨L₄, hL₄⟩ :=
          uniformFlow_fourthJet_hasFDerivAt g gi hC hK q hq v hv
            (Pi.single j 1) (Pi.single k 1) (Pi.single i 1)
        exact hL₄.differentiableAt
      exact Φ₁.comp_differentiableAt_iff.mp hΦ₁F
    exact Φ₂.comp_differentiableAt_iff.mp hΦ₂F
  -- Hence `Φ₃ ∘ f3` is differentiable at `v` via `differentiableAt_pi`.
  have hΦ₃F : DifferentiableAt ℝ (fun w => Φ₃ (f3 w)) v := by
    rw [differentiableAt_pi]
    intro i
    have hEq : (fun w => Φ₃ (f3 w) i) = (fun w => (f3 w) (Pi.single i 1)) := by
      funext w; rfl
    rw [hEq]
    exact hi i
  exact Φ₃.comp_differentiableAt_iff.mp hΦ₃F

/-! ### C³ — the per-point assembly -/

/-- **`contDiffAt3_uniformFlowExp` — `uniformFlowExp` is `ContDiffAt ℝ 3` on the regularity ball.**
    Assembled from the FOUR proven Fréchet layers, EACH valid at every ball point:
      * `uniformFlowExp_hasFDerivAt` (`Dφ` exists on the ball),
      * `uniformFlowExp_fderiv_hasFDerivAt` (`D²φ` exists on the ball),
      * `uniformFlowExp_hessianMap_differentiableAt` (`D³φ` exists on the ball),
      * `uniformFlowExp_thirdJetMap_differentiableAt` (`D⁴φ` exists on the ball ⟹ `D³φ` continuous),
    fed three times through `contDiffAt_succ_iff_hasFDerivAt` with the last step `contDiffAt_zero`
    discharged by `ContinuousOn` of `D³φ`.  The order-3 mirror of `contDiffAt2_uniformFlowExp`.  NO
    `expRho`. -/
theorem contDiffAt3_uniformFlowExp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) :
    ContDiffAt ℝ 3 (uniformFlowExp g gi hC hK q) v := by
  have hballnhds : Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) ∈ nhds v :=
    Metric.isOpen_ball.mem_nhds (by rwa [mem_ball_zero_iff])
  have hL1 : ∀ w ∈ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK),
      HasFDerivAt (uniformFlowExp g gi hC hK q) (fderiv ℝ (uniformFlowExp g gi hC hK q) w) w := by
    intro w hw; rw [mem_ball_zero_iff] at hw
    obtain ⟨L, hL⟩ := uniformFlowExp_hasFDerivAt g gi hC hK q hq w hw
    rw [hL.fderiv]; exact hL
  have hL2 : ∀ w ∈ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK),
      HasFDerivAt (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u)
        (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) w := by
    intro w hw; rw [mem_ball_zero_iff] at hw
    obtain ⟨B₂, hB₂⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq w hw
    rw [hB₂.fderiv]; exact hB₂
  have hL3 : ∀ w ∈ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK),
      HasFDerivAt (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w')
        (fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w) w := by
    intro w hw; rw [mem_ball_zero_iff] at hw
    exact (uniformFlowExp_hessianMap_differentiableAt g gi hC hK q hq w hw).hasFDerivAt
  have hL4 : ∀ w ∈ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK),
      DifferentiableAt ℝ
        (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'')
        w := by
    intro w hw; rw [mem_ball_zero_iff] at hw
    exact uniformFlowExp_thirdJetMap_differentiableAt g gi hC hK q hq w hw
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (uniformFlowExp g gi hC hK q), ⟨_, hballnhds, hL1⟩, ?_⟩
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u), ⟨_, hballnhds, hL2⟩, ?_⟩
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w'),
      ⟨_, hballnhds, hL3⟩, ?_⟩
  exact contDiffAt_zero.mpr
    ⟨_, hballnhds, fun w hw => ((hL4 w hw).continuousAt).continuousWithinAt⟩

end QIQTH.ExpMap

namespace QIQTH.HeatResidualBound

open QIQTH.Curvature QIQTH.ExpMap
open scoped Topology

variable {n : ℕ}

/-- **★ `uniformFlowExp_contDiffOn_three_uniform`.**  UNCONDITIONAL `ContDiffOn ℝ 3` of the flow
    exponential `φ_q := uniformFlowExp g gi hC hK q` on the uniform confinement ball
    `Metric.ball 0 (uniformFlowRadius g gi hC hK)`, for every base point `q ∈ K`.  NO `expRho`.
    DERIVED by promoting the unconditional, per-point `contDiffAt3_uniformFlowExp` to `ContDiffOn` on
    the open ball (`ContDiffAt.contDiffWithinAt`).  The order-3 realisation of the Plan-v6 `expRho`-free
    target shape (one order above `uniformFlowExp_contDiffOn_two_uniform`).  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_contDiffOn_three_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    ContDiffOn ℝ 3 (uniformFlowExp g gi hC hK q)
      (Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  exact (contDiffAt3_uniformFlowExp g gi hC hK q hq v hv).contDiffWithinAt

end QIQTH.HeatResidualBound
