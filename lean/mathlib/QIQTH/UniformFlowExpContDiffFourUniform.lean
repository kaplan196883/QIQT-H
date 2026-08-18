/-
  UniformFlowExpContDiffFourUniform — Plan v7 Task M (C⁴ climb, capstone): the per-seed FIFTH jet
  (`W2↑↑`), the CLM-valued fourth-jet map differentiability (quadruple-piRing lift), the per-point `C⁴`
  assembly, and the UNCONDITIONAL `ContDiffOn ℝ 4` target shape for the flow-exponential on the uniform
  confinement ball.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  NOT `a₁ = R/6`.  This closes the order-4 realisation of the Plan-v6/v7 target
  `uniformFlowExp_contDiffOn_four_uniform` — re-deriving the C⁴ regularity DIRECTLY on the uniform tube,
  with NO `expRho` anywhere.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms, NO `expRho`).
    • `uniformFlow_fifthJet_hasFDerivAt` (**W2↑↑**) — for `q ∈ K`, `‖v‖ < ρ_K`, seeds `a b c d`, the
        applied fourth jet
          `w ↦ (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
              fderiv ℝ (uniformFlowExp q) u) w') w'') w) d c a b`
        is Fréchet-differentiable at `v`.  DERIVED by transferring the hexadecuple-flow endpoint
        derivative (`uniformFlow_hexadecupleEndpoint_component_hasFDerivAt`) across the eventual equality
        `(Sf δ 1).2.2.2.1 = B₄ (v+δ) d c a b` (`Z1↑↑`, `uniformFlowExp_fourthJet_value_id`) on the open
        velocity window, then recentring `δ ↦ v + δ`.  The exact `W2↑` template one order up.
    • `uniformFlowExp_fourthJetMap_differentiableAt` (**D1↑↑**) — the CLM-valued fourth-jet map
        `w ↦ fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u)
              w') w'') w` is `DifferentiableAt ℝ` at `v`.  Assembled from `W2↑↑` via the QUADRUPLE
        evaluation `≃L` `ContinuousLinearEquiv.piRing` + `differentiableAt_pi` on the standard basis —
        the triple-piRing `uniformFlowExp_thirdJetMap_differentiableAt` lift ONE ORDER UP.
    • `contDiffAt4_uniformFlowExp` — `ContDiffAt ℝ 4 (uniformFlowExp q) v` for `‖v‖ < ρ_K`, assembled
        from the FIVE proven Fréchet layers, fed four times through `contDiffAt_succ_iff_hasFDerivAt`
        with the last step `contDiffAt_zero` via `ContinuousOn` of the fourth jet.  The order-4 mirror of
        `contDiffAt3_uniformFlowExp`.
    • `uniformFlowExp_contDiffOn_four_uniform` (**★ the target shape**) — for every `q ∈ K`,
          `ContDiffOn ℝ 4 (uniformFlowExp g gi hC hK q) (Metric.ball 0 (uniformFlowRadius g gi hC hK))`.
      UNCONDITIONAL; NO `expRho`.  The order-4 realisation of the Plan-v6/v7 target.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowExpFifthJetValueId
import QIQTH.UniformFlowHexadecupleSupply
import QIQTH.UniformFlowExpContDiffThreeUniform
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

variable {n : ℕ}

/-! ### W2↑↑ — the per-seed FIFTH jet (closed) -/

/-- **W2↑↑ — the per-seed fifth jet of `uniformFlowExp`.**  For `q ∈ K`, `‖v‖ < ρ_K`, and seeds
    `a b c d`, the applied fourth jet
        `w ↦ (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
            fderiv ℝ (uniformFlowExp q) u) w') w'') w) d c a b`
    is Fréchet-differentiable at `v`.  DERIVED by transferring the hexadecuple endpoint derivative
    `HasFDerivAt (fun δ => (Sf δ 1).2.2.2.1) L₅ 0` across the eventual equality
    `(Sf δ 1).2.2.2.1 = B₄ (v+δ) d c a b` (`Z1↑↑` on the open window `‖δ‖ < ρ_K − ‖v‖ ∈ 𝓝 0`) then
    recentring `δ ↦ v + δ`.  NO `expRho`. -/
theorem uniformFlow_fifthJet_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b c d : Point n) :
    ∃ L₅ : Point n →L[ℝ] Point n,
      HasFDerivAt
        (fun w => (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
          fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') w) d c a b) L₅ v := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  obtain ⟨Jf, Uf, Tf, Sf, hprops, L₅, hFD⟩ :=
    uniformFlow_hexadecupleEndpoint_component_hasFDerivAt g gi hC hK q hq v hv a b c d
  -- Z1↑↑ on the open velocity window: `(Sf δ 1).2.2.2.1 = B₄ (v+δ) d c a b`.
  have hEq : (fun δ => (Sf δ 1).2.2.2.1)
      =ᶠ[𝓝 (0 : Point n)]
      (fun δ => (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
        fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') (v + δ)) d c a b) := by
    have hball : Metric.ball (0 : Point n) σ ∈ 𝓝 (0 : Point n) := Metric.ball_mem_nhds _ hσ
    refine Filter.eventuallyEq_of_mem hball (fun δ hδ => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hδ
    have hδσ : ‖δ‖ ≤ ρ - ‖v‖ := by rw [← hσdef]; exact hδ.le
    have hvδ : ‖v + δ‖ < ρ := by
      refine lt_of_le_of_lt (norm_add_le v δ) ?_
      rw [hσdef] at hδ; linarith
    obtain ⟨hJf0, hJfode, hUf0, hUfode, hTf0, hTfode, hSf0, hSfode⟩ := hprops δ hδσ
    exact (uniformFlowExp_fourthJet_value_id g gi hC hK q hq (v + δ) hvδ a b c d
      (Jf δ) hJf0 hJfode (Uf δ) hUf0 hUfode (Tf δ) hTf0 hTfode (Sf δ) hSf0 hSfode).symm
  -- Transfer the derivative across the eventual equality.
  have hFD2 : HasFDerivAt
      (fun δ => (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
        fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') (v + δ)) d c a b) L₅ 0 :=
    hFD.congr_of_eventuallyEq hEq.symm
  -- Recentre `δ ↦ v + δ`.
  have hshift : HasFDerivAt (fun u : Point n => u - v) (ContinuousLinearMap.id ℝ (Point n)) v :=
    (hasFDerivAt_id v).sub_const v
  have hFD0 : HasFDerivAt
      (fun δ => (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
        fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') (v + δ)) d c a b) L₅ (v - v) := by
    rw [sub_self]; exact hFD2
  have hcomp : HasFDerivAt
      (fun w => (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
        fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') (v + (w - v))) d c a b)
      (L₅.comp (ContinuousLinearMap.id ℝ (Point n))) v :=
    hFD0.comp (f := fun w : Point n => w - v) v hshift
  have hfun2 : (fun w => (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
        fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') (v + (w - v))) d c a b)
      = (fun w => (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
        fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') w) d c a b) := by
    funext w; rw [show v + (w - v) = w by abel]
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  exact ⟨L₅, hcomp⟩

/-! ### D1↑↑ — the CLM-valued fourth-jet map (quadruple-piRing lift of W2↑↑) -/

/-- **D1↑↑ — the CLM-valued fourth-jet map is Fréchet-differentiable at `v`.**  For `q ∈ K` and
    `‖v‖ < ρ_K`, the operator-valued fourth-jet map
        `w ↦ fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u)
              w') w'') w`
    is `DifferentiableAt ℝ` at `v`.  Assembled from `W2↑↑` — the per-seed fifth jets on the standard
    basis `(single i, single j, single k, single l)` — via the QUADRUPLE evaluation `≃L`
    `ContinuousLinearEquiv.piRing` and `differentiableAt_pi`, mirroring the triple-layer
    `uniformFlowExp_thirdJetMap_differentiableAt` lift ONE ORDER UP.  Hence `fderiv ℝ (…) v` is the
    GENUINE fifth Fréchet jet. -/
theorem uniformFlowExp_fourthJetMap_differentiableAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) :
    DifferentiableAt ℝ
      (fun w => fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
        fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') w)
      v := by
  classical
  set f4 : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    fun w => fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
      fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') w
    with hf4def
  -- Outermost evaluation `≃L`.
  set Φ₄ : (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n)
        ≃L[ℝ] (Fin n → (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n)) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ)
      (E := Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n) (Fin n) with hΦ₄def
  set Φ₃ : (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n)
        ≃L[ℝ] (Fin n → (Point n →L[ℝ] Point n →L[ℝ] Point n)) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n →L[ℝ] Point n →L[ℝ] Point n) (Fin n) with hΦ₃def
  set Φ₂ : (Point n →L[ℝ] Point n →L[ℝ] Point n) ≃L[ℝ] (Fin n → (Point n →L[ℝ] Point n)) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n →L[ℝ] Point n) (Fin n) with hΦ₂def
  set Φ₁ : (Point n →L[ℝ] Point n) ≃L[ℝ] (Fin n → Point n) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n) (Fin n) with hΦ₁def
  -- Each quadruple-basis-coordinate evaluation is differentiable at `v` (W2↑↑).
  have hi : ∀ i : Fin n, DifferentiableAt ℝ (fun w => (f4 w) (Pi.single i 1)) v := by
    intro i
    have hΦ₃F : DifferentiableAt ℝ (fun w => Φ₃ ((f4 w) (Pi.single i 1))) v := by
      rw [differentiableAt_pi]
      intro j
      have hΦ₂F : DifferentiableAt ℝ
          (fun w => Φ₂ ((f4 w) (Pi.single i 1) (Pi.single j 1))) v := by
        rw [differentiableAt_pi]
        intro k
        have hΦ₁F : DifferentiableAt ℝ
            (fun w => Φ₁ ((f4 w) (Pi.single i 1) (Pi.single j 1) (Pi.single k 1))) v := by
          rw [differentiableAt_pi]
          intro l
          have hEq : (fun w => Φ₁ ((f4 w) (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)) l)
              = (fun w => (f4 w) (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)) := by
            funext w; rfl
          rw [hEq]
          -- W2↑↑ applies its slots as `d c a b` (derivative direction first); pass args so that
          -- `d = single i`, `c = single j`, `a = single k`, `b = single l`.
          obtain ⟨L₅, hL₅⟩ :=
            uniformFlow_fifthJet_hasFDerivAt g gi hC hK q hq v hv
              (Pi.single k 1) (Pi.single l 1) (Pi.single j 1) (Pi.single i 1)
          exact hL₅.differentiableAt
        exact Φ₁.comp_differentiableAt_iff.mp hΦ₁F
      exact Φ₂.comp_differentiableAt_iff.mp hΦ₂F
    exact Φ₃.comp_differentiableAt_iff.mp hΦ₃F
  -- Hence `Φ₄ ∘ f4` is differentiable at `v` via `differentiableAt_pi`.
  have hΦ₄F : DifferentiableAt ℝ (fun w => Φ₄ (f4 w)) v := by
    rw [differentiableAt_pi]
    intro i
    have hEq : (fun w => Φ₄ (f4 w) i) = (fun w => (f4 w) (Pi.single i 1)) := by
      funext w; rfl
    rw [hEq]
    exact hi i
  exact Φ₄.comp_differentiableAt_iff.mp hΦ₄F

/-! ### C⁴ — the per-point assembly -/

/-- **`contDiffAt4_uniformFlowExp` — `uniformFlowExp` is `ContDiffAt ℝ 4` on the regularity ball.**
    Assembled from the FIVE proven Fréchet layers, EACH valid at every ball point, fed four times through
    `contDiffAt_succ_iff_hasFDerivAt` with the last step `contDiffAt_zero` discharged by `ContinuousOn`
    of `D⁴φ`.  The order-4 mirror of `contDiffAt3_uniformFlowExp`.  NO `expRho`. -/
theorem contDiffAt4_uniformFlowExp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) :
    ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK q) v := by
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
      HasFDerivAt
        (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'')
        (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
          fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') w) w := by
    intro w hw; rw [mem_ball_zero_iff] at hw
    exact (uniformFlowExp_thirdJetMap_differentiableAt g gi hC hK q hq w hw).hasFDerivAt
  have hL5 : ∀ w ∈ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK),
      DifferentiableAt ℝ
        (fun w''' => fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
          fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') w''')
        w := by
    intro w hw; rw [mem_ball_zero_iff] at hw
    exact uniformFlowExp_fourthJetMap_differentiableAt g gi hC hK q hq w hw
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (uniformFlowExp g gi hC hK q), ⟨_, hballnhds, hL1⟩, ?_⟩
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u), ⟨_, hballnhds, hL2⟩, ?_⟩
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w'),
      ⟨_, hballnhds, hL3⟩, ?_⟩
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
      fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w''),
      ⟨_, hballnhds, hL4⟩, ?_⟩
  exact contDiffAt_zero.mpr
    ⟨_, hballnhds, fun w hw => ((hL5 w hw).continuousAt).continuousWithinAt⟩

end QIQTH.ExpMap

namespace QIQTH.HeatResidualBound

open QIQTH.Curvature QIQTH.ExpMap
open scoped Topology

variable {n : ℕ}

/-- **★ `uniformFlowExp_contDiffOn_four_uniform`.**  UNCONDITIONAL `ContDiffOn ℝ 4` of the flow
    exponential `φ_q := uniformFlowExp g gi hC hK q` on the uniform confinement ball
    `Metric.ball 0 (uniformFlowRadius g gi hC hK)`, for every base point `q ∈ K`.  NO `expRho`.
    DERIVED by promoting the unconditional, per-point `contDiffAt4_uniformFlowExp` to `ContDiffOn` on
    the open ball (`ContDiffAt.contDiffWithinAt`).  The order-4 realisation of the Plan-v6/v7 `expRho`-free
    target shape (one order above `uniformFlowExp_contDiffOn_three_uniform`).  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_contDiffOn_four_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    ContDiffOn ℝ 4 (uniformFlowExp g gi hC hK q)
      (Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  exact (contDiffAt4_uniformFlowExp g gi hC hK q hq v hv).contDiffWithinAt

end QIQTH.HeatResidualBound
