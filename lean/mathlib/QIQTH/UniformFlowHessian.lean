/-
  # J4-68 — R2: the CLM-valued Hessian existence for the uniform-flow exp map.

  Brick-A(β) regularity climb.  R2-b (`uniformFlowExp_fderiv_apply_hasFDerivAt`,
  `UniformFlowSecondSupply.lean`) gives, for EACH seed `b`, the per-direction Fréchet second-jet
      `∃ L₂, HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w b) L₂ v`.
  This file LIFTS those per-seed derivatives to the CLM-VALUED jet map
      `w ↦ fderiv ℝ (uniformFlowExp g gi hC hK q) w   :   Point n → (Point n →L[ℝ] Point n)`,
  i.e. proves R2:
      `∃ B₂, HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) B₂ v`.

  The lift is the finite-dimensional assembly the SecondSupply header flagged as CARRIED.  It uses the
  Mathlib evaluation continuous-linear-equivalence
      `ContinuousLinearEquiv.piRing (Fin n) : ((Fin n → ℝ) →L[ℝ] Point n) ≃L[ℝ] (Fin n → Point n)`
  (with `Point n = Fin n → ℝ`, so the source is `Point n →L[ℝ] Point n`), whose evaluation on a
  coordinate is `L (Pi.single i 1)`.  Under this `≃L`, differentiability of the CLM-valued map is
  equivalent (via `ContinuousLinearEquiv.comp_differentiableAt_iff`) to differentiability of its
  composite with `Φ`, which by `differentiableAt_pi` reduces to differentiability of each coordinate
  `w ↦ (F w) (Pi.single i 1)` — exactly R2-b with seed `b = Pi.single i 1`.

  The uniform Hessian bound (R3) is NOT closed here: the relation between `‖B₂‖` (a bilinear/double-CLM
  operator norm) and the R1 second-variation endpoint bound `‖Zf 1‖ ≤ M₂j‖a‖²`
  (`uniformFlowTube_secondVariation_uniform_bound`) requires an opNorm identification of `B₂` with the
  second-variation field that is a separate, heavier obligation — CARRIED (firewalled).
  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.UniformFlowSecondSupply
import QIQTH.UniformFlowSecondJet
import QIQTH.UniformFlowFDeriv
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-! ### R2 — the CLM-valued Hessian (second Fréchet jet) of the uniform-flow exp map exists. -/

/-- **R2 — the CLM-valued second Fréchet jet of `uniformFlowExp` exists.**  For `q ∈ K` and
    `‖v‖ < ρ_K`, the operator-valued first-jet map
        `F : w ↦ fderiv ℝ (uniformFlowExp g gi hC hK q) w   :   Point n → (Point n →L[ℝ] Point n)`
    has a Fréchet derivative at `v`:
        `∃ B₂ : Point n →L[ℝ] (Point n →L[ℝ] Point n),
            HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) B₂ v`.
    Assembled from R2-b (`uniformFlowExp_fderiv_apply_hasFDerivAt`) — the per-seed derivatives on the
    standard basis `Pi.single i 1` — via the evaluation `≃L` `ContinuousLinearEquiv.piRing` and
    `differentiableAt_pi`.  This is a GENUINE CLM-valued `HasFDerivAt`; `B₂` is the Fréchet derivative,
    not an assumption. -/
theorem uniformFlowExp_fderiv_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) :
    ∃ B₂ : Point n →L[ℝ] (Point n →L[ℝ] Point n),
      HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) B₂ v := by
  classical
  -- The CLM-valued first-jet map.
  set F : Point n → (Point n →L[ℝ] Point n) :=
    fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w with hFdef
  -- Evaluation-on-standard-basis continuous linear equivalence
  --   `(Point n →L[ℝ] Point n) ≃L[ℝ] (Fin n → Point n)`.
  set Φ : (Point n →L[ℝ] Point n) ≃L[ℝ] (Fin n → Point n) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n) (Fin n) with hΦdef
  -- Each basis-coordinate evaluation is differentiable at `v` (R2-b, seed `b = Pi.single i 1`).
  have hcomp_i : ∀ i : Fin n, DifferentiableAt ℝ (fun w => (F w) (Pi.single i 1)) v := by
    intro i
    obtain ⟨L₂, hL₂⟩ :=
      uniformFlowExp_fderiv_apply_hasFDerivAt g gi hC hK q hq v hv (Pi.single i 1)
    exact hL₂.differentiableAt
  -- Hence `Φ ∘ F` is differentiable at `v` via `differentiableAt_pi`.
  have hΦF : DifferentiableAt ℝ (fun w => Φ (F w)) v := by
    rw [differentiableAt_pi]
    intro i
    have hEq : (fun w => Φ (F w) i) = (fun w => (F w) (Pi.single i 1)) := by
      funext w
      rfl
    rw [hEq]
    exact hcomp_i i
  -- Transfer differentiability across the `≃L`.
  have hF : DifferentiableAt ℝ F v := Φ.comp_differentiableAt_iff.mp hΦF
  exact ⟨fderiv ℝ F v, hF.hasFDerivAt⟩

end QIQTH.ExpMap
