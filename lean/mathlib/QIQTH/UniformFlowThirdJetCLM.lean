/-
  UniformFlowThirdJetCLM — J4-678 (Brick-A β, C³ climb, CLM-ASSEMBLY): the operator-valued THIRD jet of
  `uniformFlowExp`, assembled from the banked per-seed scalar third jets (W2) exactly as R2's CLM-valued
  Hessian was assembled from the per-seed second jets.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It lifts the
  per-seed SCALAR third jets of `uniformFlowExp` (banked as `uniformFlowExp_thirdJet_apply_hasFDerivAt`,
  W2) into a genuine OPERATOR-NORM (CLM-valued) third Fréchet jet — the little-o-in-operator-norm upgrade,
  not merely pointwise-in-seed differentiability.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous/unsatisfiable hypotheses, no conclusion-in-a-hyp.  std-3 only.  No existing file is
  edited.  NO `expRho`.  Does NOT touch Raychaudhuri (L3).

  ── CONTEXT (what was already banked).
    * R2 `UniformFlowHessian` `uniformFlowExp_fderiv_hasFDerivAt` — the CLM-VALUED SECOND jet: the
      operator-valued first-jet map `w ↦ fderiv ℝ (uniformFlowExp q) w` has a Fréchet derivative
      `B₂ : Point n →L (Point n →L Point n)` at `v`.  Assembled from the per-seed second jets (R2-b) via
      the evaluation `≃L` `ContinuousLinearEquiv.piRing` + `differentiableAt_pi`.
    * W2 `UniformFlowThirdJetClose2` `uniformFlowExp_thirdJet_apply_hasFDerivAt` — the per-seed SCALAR
      third jet: for each `a b`, `w ↦ fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u b) w a` has a
      Fréchet derivative `L₃ : Point n →L Point n` at `v`.  This is pointwise-in-`(a,b)`, NOT the operator.
    * `HbaseJ2Assembly` `fderiv2_apply_eq_of_hasFDerivAt` — the generic CLM commute (the `apply b` post-
      composition chain rule) turning `fderiv ℝ (fun w => F w b) v` into `fderiv ℝ (fderiv ℝ F) v · b`.

  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `uniformFlowExp_thirdJet_hasFDerivAt` — **★★ the CLM-VALUED THIRD jet (the assembly upgrade).**  For
      `q ∈ K`, `‖v‖ < ρ_K`, the operator-valued SECOND-jet map
        `F₂ : w ↦ fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp … q) u) w : Point n → (Point n →L Point n →L Point n)`
      has a Fréchet derivative `B₃ : Point n →L Point n →L Point n →L Point n` at `v`:
        `∃ B₃, HasFDerivAt (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp … q) u) w) B₃ v`.
      DERIVED, mirroring R2 one order up: a DOUBLE `ContinuousLinearEquiv.piRing` + `differentiableAt_pi`
      reduces operator-norm differentiability of `F₂` to differentiability of each scalar coordinate
      `w ↦ (F₂ w)(eᵢ)(eⱼ)`; the generic `apply`-post-composition commute rewrites `(F₂ w)(a)(b) =
      fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u b) w a` on the velocity ball (a nbhd of `v`), which
      IS W2's per-seed scalar third jet.  Finite-dimensionality of `Point n` supplies the assembly for
      free — exactly as it did for R2.  NOT `a₁ = R/6`.

    * `uniformFlowExp_thirdJet_opNorm_le_of_symm_diag_bound` — **W3 (assembled, CONDITIONAL).**  The exact
      one-order-up analogue of R3's `uniformFlowExp_hessian_opNorm_le_of_diag_bound`.  Given a uniform
      DIAGONAL cubic bound `‖B₃(q,v) a a a‖ ≤ M‖a‖³` and full SYMMETRY of `B₃` (the two transpositions),
      the generic polarization brick `trilinear_opNorm_le_of_symm_diag_bound` yields the UNIFORM
      operator-norm bound `∃ M', ∀ q ∈ K, ∀ ‖v‖ < r₀, ‖B₃(q,v)‖ ≤ M'` (`M' = (9/2)·M`).  The diagonal
      bound + symmetry are GENUINE carried inputs (P1 the diagonal value-id, P2 third-order Clairaut),
      NOT the conclusion — precisely the two firewalled residues `UniformFlowThirdBound` names.

  ⚠ WHAT REMAINS (NOT here): the diagonal value-id `B₃(q,v)(a,a,a) = (Z₃ 1).1` (P1) and third-order
  symmetry (P2), which discharge the two carried hypotheses of the conditional W3; and W4
  (`uniformFlowExp ∈ C³ ⟹ g̃ ∈ C²`) + the residual Raychaudhuri wiring.  NOT `a₁ = R/6`; a₁ = R/6 remains
  CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import QIQTH.UniformFlowThirdJetClose2
import QIQTH.UniformFlowHessian
import QIQTH.UniformFlowThirdBound
import QIQTH.HbaseJ2Assembly
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

variable {n : ℕ}

/-! ### The CLM-valued third jet of `uniformFlowExp` (the operator-norm assembly upgrade). -/

/-- **★★ The CLM-valued THIRD Fréchet jet of `uniformFlowExp` exists.**  For `q ∈ K` and `‖v‖ < ρ_K`, the
    operator-valued SECOND-jet map
        `F₂ : w ↦ fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w`
              `: Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n)`
    has a Fréchet derivative at `v`:
        `∃ B₃ : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n, HasFDerivAt F₂ B₃ v`.
    Assembled from W2 (`uniformFlowExp_thirdJet_apply_hasFDerivAt`) — the per-seed scalar third jets on the
    standard basis `Pi.single i 1`, `Pi.single j 1` — via a DOUBLE evaluation `≃L`
    `ContinuousLinearEquiv.piRing`, `differentiableAt_pi`, and the generic `apply`-post-composition commute
    identifying `(F₂ w)(a)(b) = fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u b) w a` on the velocity
    ball.  Mirrors R2's `uniformFlowExp_fderiv_hasFDerivAt` one order up; `B₃` is the Fréchet derivative,
    not an assumption.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_thirdJet_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) :
    ∃ B₃ : Point n →L[ℝ] (Point n →L[ℝ] (Point n →L[ℝ] Point n)),
      HasFDerivAt
        (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) B₃ v := by
  classical
  -- Differentiability of the CLM-valued FIRST jet `fderiv ℝ (uniformFlowExp q)` on the velocity ball (R2).
  have hf1diff : ∀ w : Point n, ‖w‖ < uniformFlowRadius g gi hC hK →
      DifferentiableAt ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w := by
    intro w hw
    obtain ⟨B₂w, hB₂w⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq w hw
    exact hB₂w.differentiableAt
  -- The `apply b`-post-composition commute: `(F₂ w)(a)(b) = fderiv (fun u => fderiv(exp q) u b) w a`.
  have hcommute : ∀ w : Point n, ‖w‖ < uniformFlowRadius g gi hC hK → ∀ a b : Point n,
      (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) a b
        = fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u b) w a := by
    intro w hw a b
    have hev : HasFDerivAt (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u b)
        ((ContinuousLinearMap.apply ℝ (Point n) b).comp
          (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w)) w := by
      have h := (ContinuousLinearMap.apply ℝ (Point n) b).hasFDerivAt.comp w (hf1diff w hw).hasFDerivAt
      simpa [Function.comp, ContinuousLinearMap.apply_apply] using h
    rw [hev.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  -- The velocity ball is a neighbourhood of `v`.
  have hballv : Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) ∈ 𝓝 v := by
    refine Metric.isOpen_ball.mem_nhds ?_
    rw [Metric.mem_ball, dist_zero_right]; exact hv
  -- The CLM-valued second-jet map and the two evaluation equivalences.
  set F₂ : Point n → (Point n →L[ℝ] (Point n →L[ℝ] Point n)) :=
    fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w with hF₂def
  set Φ₁ : (Point n →L[ℝ] (Point n →L[ℝ] Point n)) ≃L[ℝ] (Fin n → (Point n →L[ℝ] Point n)) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n →L[ℝ] Point n) (Fin n) with hΦ₁def
  set Φ₂ : (Point n →L[ℝ] Point n) ≃L[ℝ] (Fin n → Point n) :=
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Point n) (Fin n) with hΦ₂def
  -- Differentiability of `F₂` at `v` via the double piRing peel (mirrors R2's forward style one order up).
  have hΦ₁F₂ : DifferentiableAt ℝ (fun w => Φ₁ (F₂ w)) v := by
    -- outer peel: each coordinate `w ↦ (F₂ w)(eᵢ)` differentiable.
    rw [differentiableAt_pi]
    intro i
    have hEqi : (fun w => Φ₁ (F₂ w) i) = (fun w => (F₂ w) (Pi.single i 1)) := by
      funext w; rfl
    rw [hEqi]
    -- inner peel: each scalar coordinate `w ↦ (F₂ w)(eᵢ)(eⱼ)` differentiable.
    have hΦ₂Fi : DifferentiableAt ℝ (fun w => Φ₂ ((F₂ w) (Pi.single i 1))) v := by
      rw [differentiableAt_pi]
      intro j
      have hEqj : (fun w => Φ₂ ((F₂ w) (Pi.single i 1)) j)
          = (fun w => (F₂ w) (Pi.single i 1) (Pi.single j 1)) := by
        funext w; rfl
      rw [hEqj]
      -- W2: the per-seed scalar third jet at `a = eᵢ`, `b = eⱼ`.
      obtain ⟨L₃, hL₃⟩ :=
        uniformFlowExp_thirdJet_apply_hasFDerivAt g gi hC hK q hq v hv (Pi.single i 1) (Pi.single j 1)
      -- the coordinate agrees with W2's function on the ball (a nbhd of `v`).
      have hEq : (fun w => (F₂ w) (Pi.single i 1) (Pi.single j 1))
          =ᶠ[𝓝 v]
          (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u (Pi.single j 1)) w
            (Pi.single i 1)) := by
        refine Filter.eventuallyEq_of_mem hballv (fun w hw => ?_)
        rw [Metric.mem_ball, dist_zero_right] at hw
        exact hcommute w hw (Pi.single i 1) (Pi.single j 1)
      exact hL₃.differentiableAt.congr_of_eventuallyEq hEq
    exact Φ₂.comp_differentiableAt_iff.mp hΦ₂Fi
  have hF₂diff : DifferentiableAt ℝ F₂ v := Φ₁.comp_differentiableAt_iff.mp hΦ₁F₂
  exact ⟨fderiv ℝ F₂ v, hF₂diff.hasFDerivAt⟩

/-! ### W3 (assembled, conditional) — the uniform operator-norm bound on the third jet. -/

/-- **W3 (assembled, CONDITIONAL).**  The one-order-up analogue of R3's
    `uniformFlowExp_hessian_opNorm_le_of_diag_bound`.  Given, uniformly over `q ∈ K` and `‖v‖ < r₀ ≤ ρ_K`,
    a DIAGONAL cubic bound `‖B₃(q,v) a a a‖ ≤ M‖a‖³` and full SYMMETRY of the third jet
        `B₃(q,v) := fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v`
    (the two transpositions `hs12`, `hs23`), the generic polarization brick
    `trilinear_opNorm_le_of_symm_diag_bound` gives the UNIFORM operator-norm bound
        `∃ M', ∀ q ∈ K, ∀ ‖v‖ < r₀, ‖B₃(q,v)‖ ≤ M'`   (`M' = (9/2)·M`).
    The diagonal bound + symmetry are GENUINE carried inputs (P1 the diagonal value-id to W1's intrinsic
    third-variation field; P2 third-order Clairaut), NOT the conclusion.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_thirdJet_opNorm_le_of_symm_diag_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {r₀ M : ℝ} (hM : 0 ≤ M)
    (_hrρ : r₀ ≤ uniformFlowRadius g gi hC hK)
    (hs12 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ x y z : Point n,
      (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) x y z
        = (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) y x z)
    (hs23 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ x y z : Point n,
      (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) x y z
        = (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) x z y)
    (hdiag : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ a : Point n,
      ‖(fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) a a a‖
        ≤ M * ‖a‖ ^ 3) :
    ∃ M' : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
      ‖fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v‖ ≤ M' := by
  refine ⟨(9 / 2) * M, ?_⟩
  intro q hq v hv
  exact trilinear_opNorm_le_of_symm_diag_bound
    (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v)
    (hs12 q hq v hv) (hs23 q hq v hv) hM (hdiag q hq v hv)

end QIQTH.ExpMap
