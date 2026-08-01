/-
  UniformFlowThirdDiag — J4-77 (Brick-A β, C³ climb): the DIAGONAL VALUE-ID (P1) for the CLM-valued
  third jet `B₃` of `uniformFlowExp`, identifying `B₃(q,v) a a a` with the per-seed third jet `L₃`
  (`uniformFlow_thirdJet_hasFDerivAt`, W2) — the one-order-up mirror of Z1's
  (`uniformFlowExp_hessian_value_id`) directional value identification.

  ## Context

  * D1 (`UniformFlowThirdBoundClose`, `uniformFlowExp_hessianMap_differentiableAt`) — the CLM-valued
    Hessian map `f₂ : w ↦ fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w` is `DifferentiableAt ℝ`
    at `v` (`‖v‖ < ρ_K`), so `B₃(q,v) := fderiv ℝ f₂ v : Point n →L Point n →L Point n →L Point n` is
    the GENUINE third Fréchet jet.
  * W2 (`UniformFlowThirdJetClose`, `uniformFlow_thirdJet_hasFDerivAt`) — the per-seed THIRD jet
    `∃ L₃, HasFDerivAt (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) a b) L₃ v`.
  * W3 (`UniformFlowThirdBoundClose`, `uniformFlowExp_thirdDeriv_opNorm_le_of_diag_bound`) — the uniform
    operator-norm bound on `B₃`, CONDITIONAL on the diagonal cubic bound `‖B₃(q,v) a a a‖ ≤ M‖a‖³`.
  * `clm_fderiv_value_of_directional` (`JacobiOperatorFDeriv`) — the one-order-down template: from
    `HasFDerivAt (fun w => fderiv ℝ Fam w) B v` + a scalar directional `HasDerivAt` it reads off `B a b`.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no `expRho`)

  * `uniformFlowExp_thirdDeriv_diag_value_perSeed` (**P1, the diagonal VALUE-ID**) — for `q ∈ K`,
    `‖v‖ < ρ_K`, and a direction `a`, there is a per-seed third jet `L₃` (the W2 jet at seeds `(a,a)`)
    with
        `HasFDerivAt (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) a a) L₃ v`   AND
        `(fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) v) a a a = L₃ a`.
    DERIVED, mirroring `clm_fderiv_value_of_directional` ONE ORDER UP: `B₃ := fderiv ℝ f₂ v`
    (`HasFDerivAt f₂ B₃ v` from D1) chained along the line `s ↦ v + s • a` and evaluated at the two
    Hessian slots `(a, a)` yields `HasDerivAt (fun s => (f₂ (v + s • a)) a a) (B₃ a a a) 0`; W2's jet
    chained along the same line yields `HasDerivAt (fun s => (f₂ (v + s • a)) a a) (L₃ a) 0`; the two
    scalar directional derivatives are equal by `HasDerivAt.unique`, whence `B₃ a a a = L₃ a`.

  ## HONEST FIREWALL (binding) — the residual for W3 unconditional

  This identifies the diagonal of the abstract third jet `B₃ a a a` with the CONCRETE per-seed third jet
  `L₃ a` (`L₃` = J4-73's projected quadruple-flow endpoint derivative).  What is NOT discharged here is
  the uniform CUBIC BOUND on that concrete jet,
        `‖L₃ a‖ ≤ M₃j · ‖a‖³`   (uniform over `q ∈ K`, `‖v‖ < r₀`),
  which is what W1 (`uniformFlowTube_thirdVariation_uniform_bound`, `‖Z₃ 1‖ ≤ M₃j‖a‖³`) controls at the
  field level.  Bridging `L₃ a` to W1's `Z₃`-endpoint requires the `L δ = V δ 1` clause of the abstract
  first-jet engine (`autonomousFlow_endpoint_hasFDerivAt_window_exists`) — which J4-73
  (`uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt`) discards — plus the comparison field
  `Xcmp τ = ((V τ, W τ), (W τ, Z₃ τ))` solving the packed `Φ̃`-linearized ODE along the base quadruple
  curve, identified with the engine's linearized field by ODE uniqueness (`autonomousLinODE_unique`).
  That comparison-field bridge is a whole self-contained brick (it re-plumbs the engine's linearized
  clause, which is not exposed by the imported J4-73 signature).  It is CARRIED (a genuine input, not a
  vacuous firewall).  With it in hand, `uniformFlowExp_thirdDeriv_diag_value_perSeed` feeds the diagonal
  bound `‖B₃ a a a‖ = ‖L₃ a‖ ≤ M₃j‖a‖³` to `uniformFlowExp_thirdDeriv_opNorm_le_of_diag_bound`,
  discharging W3 (`M := M₃j`).  W3 therefore remains CONDITIONAL (exactly as in J4-76), now firewalled
  at the concrete `L₃`-cubic-bound rather than the abstract `B₃`-diagonal.

  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.  NO `expRho`.  W4 (`uniformFlowExp ∈ C³ ⟹
  g̃ ∈ C²` assembly) remains the next step.
-/
import QIQTH.UniformFlowThirdBoundClose
import QIQTH.UniformFlowThirdJetClose
import QIQTH.QuadrupleFlowSupply
import QIQTH.UniformFlowThirdJet
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

/-! ### P1 — the diagonal value-identity: `B₃ a a a = L₃ a` -/

/-- **P1 — the diagonal VALUE-ID for the third jet of `uniformFlowExp`.**  For `q ∈ K`, `‖v‖ < ρ_K`,
    and a direction `a`, there is a per-seed third jet `L₃` (the W2 jet at seeds `(a, a)`) such that
      * `HasFDerivAt (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) a a) L₃ v`, and
      * `(fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) v) a a a = L₃ a`.

    DERIVED, mirroring `clm_fderiv_value_of_directional` ONE ORDER UP.  Write
    `f₂ w := fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w` and `B₃ := fderiv ℝ f₂ v`
    (`HasFDerivAt f₂ B₃ v` from D1, `uniformFlowExp_hessianMap_differentiableAt`).  Chaining `B₃` along
    the line `s ↦ v + s • a` and evaluating both Hessian slots at `a` gives
    `HasDerivAt (fun s => (f₂ (v + s • a)) a a) (B₃ a a a) 0`; W2's jet chained along the same line
    gives the same directional map with derivative `L₃ a`; `HasDerivAt.unique` reads off `B₃ a a a =
    L₃ a`.  NO `expRho`. -/
theorem uniformFlowExp_thirdDeriv_diag_value_perSeed (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a : Point n) :
    ∃ L₃ : Point n →L[ℝ] Point n,
      HasFDerivAt
        (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) a a) L₃ v ∧
      (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) a a a
        = L₃ a := by
  classical
  set f2 : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w with hf2def
  set B₃ : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n := fderiv ℝ f2 v with hB₃def
  -- D1: the CLM-valued Hessian map is Fréchet-differentiable at `v`, so `B₃` is the genuine third jet.
  have hD1 : HasFDerivAt f2 B₃ v :=
    (uniformFlowExp_hessianMap_differentiableAt g gi hC hK q hq v hv).hasFDerivAt
  -- W2: the per-seed third jet at seeds `(a, a)`.
  obtain ⟨L₃, hL₃⟩ := uniformFlow_thirdJet_hasFDerivAt g gi hC hK q hq v hv a a
  refine ⟨L₃, hL₃, ?_⟩
  -- The base line `s ↦ v + s • a` has derivative `a` at `0`.
  have hline : HasDerivAt (fun s : ℝ => v + s • a) a 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • a) a 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
    exact h1.const_add v
  -- Chain `B₃` along the line: `HasDerivAt (fun s => f₂ (v + s • a)) (B₃ a) 0`.
  have hD1' : HasFDerivAt f2 B₃ (v + (0 : ℝ) • a) := by simpa using hD1
  have hcomp : HasDerivAt (fun s : ℝ => f2 (v + s • a)) (B₃ a) 0 := by
    simpa using hD1'.comp_hasDerivAt 0 hline
  -- The double evaluation-at-`a` CLM `ev : (Point n →L Point n →L Point n) →L Point n`, `T ↦ T a a`.
  set E1 : (Point n →L[ℝ] Point n →L[ℝ] Point n) →L[ℝ] (Point n →L[ℝ] Point n) :=
    ContinuousLinearMap.apply ℝ (Point n →L[ℝ] Point n) a with hE1def
  set E2 : (Point n →L[ℝ] Point n) →L[ℝ] Point n :=
    ContinuousLinearMap.apply ℝ (Point n) a with hE2def
  set ev : (Point n →L[ℝ] Point n →L[ℝ] Point n) →L[ℝ] Point n := E2.comp E1 with hevdef
  have hev_apply : ∀ T : Point n →L[ℝ] Point n →L[ℝ] Point n, ev T = T a a := fun T => rfl
  -- Evaluate the line-chain at `(a, a)`: `HasDerivAt (fun s => (f₂ (v + s • a)) a a) (B₃ a a a) 0`.
  have heval : HasDerivAt (fun s : ℝ => (f2 (v + s • a)) a a) (B₃ a a a) 0 := by
    have h := ev.hasFDerivAt.comp_hasDerivAt 0 hcomp
    simpa [hev_apply] using h
  -- W2's jet chained along the same line: `HasDerivAt (fun s => (f₂ (v + s • a)) a a) (L₃ a) 0`.
  have hL₃' : HasFDerivAt
      (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) a a) L₃
      (v + (0 : ℝ) • a) := by simpa using hL₃
  have hdir : HasDerivAt (fun s : ℝ => (f2 (v + s • a)) a a) (L₃ a) 0 := by
    have h := hL₃'.comp_hasDerivAt 0 hline
    simpa [hf2def] using h
  -- Read off `B₃ a a a = L₃ a` by uniqueness of the scalar directional derivative.
  exact heval.unique hdir

end QIQTH.ExpMap
