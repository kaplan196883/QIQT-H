/-
  UniformFlowThirdJetCLMUncond — J4-679 (Brick-A β, C³ climb): discharge the CLM-assembly W3.  The
  just-banked CLM-valued conditional W3 (`uniformFlowExp_thirdJet_opNorm_le_of_symm_diag_bound`, J4-678)
  carried THREE genuine inputs — P1 (the diagonal cubic bound `hdiag`) and P2 (the two symmetries
  `hs12`, `hs23`).  This file DISCHARGES all three from ALREADY-BANKED unconditional bricks and produces
  the UNCONDITIONAL CLM operator-norm bound on the third jet, closing the CLM loop of the C³ climb.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It only wires
  three previously-banked bricks into the banked conditional CLM theorem, removing its carried
  hypotheses.  No `sorry`, no `:= True`, no new axioms, no vacuous/unsatisfiable hypotheses, no
  conclusion-in-a-hyp.  std-3 only.  No existing file is edited.  NO `expRho`.  Does NOT touch
  Raychaudhuri (L3).

  ── WHY THE CARRIED INPUTS ARE ALREADY DISCHARGED (the "wall" was route-specific, and already broken).

    * P1 — the diagonal cubic bound `‖B₃(q,v) a a a‖ ≤ M‖a‖³`.  The `UniformFlowThirdBound` firewall
      warned that the *naive per-slot Grönwall* on the quadruple field blows up: the doubled base curve's
      confinement radius grows with `‖a‖,‖b‖`, so the exponential Grönwall constant is not polynomial.
      That obstruction is REAL but ROUTE-SPECIFIC.  J4-78 (`UniformFlowThirdUncond`,
      `uniformFlowExp_thirdDeriv_diag_cubic_bound`, X1) sidesteps it entirely via the COMPARISON-FIELD /
      ODE-UNIQUENESS route: the quadruple engine's endpoint field is IDENTIFIED (by `HasDerivWithinAt`
      uniqueness, `autonomousLinODE_within_unique`) with W1's comparison field `((V,W),(W,Z₃))` — whose
      TOP factor `Z₃` is the intrinsic third-variation field carried along the FIXED base tube, so its
      Grönwall constant `Kf` is the (a-INDEPENDENT) field-Jacobian sup over one compact phase ball and
      W1's bound `‖Z₃ 1‖ ≤ M₃j‖a‖³` is genuinely cubic and uniform.  Uniqueness needs no good constant;
      the cubic bound rides on the triangular fixed-base field, not the naive vector Grönwall.  Hence the
      "bounded-domain rescue" for the exponential is UNNECESSARY — the exponential never appears on the
      surviving route.  X1 is unconditional (only `hC` + `IsCompact K`).

    * P2 — the two symmetries `hs12` (`B₃ x y z = B₃ y x z`) and `hs23` (`B₃ x y z = B₃ x z y`).  Both are
      banked in J4-76 (`UniformFlowThirdBoundClose`): `uniformFlowExp_thirdJet_symm12` (Clairaut
      `second_derivative_symmetric_of_eventually_of_real` on `u ↦ fderiv (uniformFlowExp q) u b`) and
      `uniformFlowExp_thirdJet_symm23` (the flip continuous-linear equivalence on the eventually-symmetric
      Hessian).  Both hold for every `‖v‖ < ρ_K`.

  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `uniformFlowExp_thirdJet_opNorm_le_uncond` — **★ the UNCONDITIONAL CLM operator-norm bound on the
      third jet.**  For a uniform velocity radius `r₀ > 0` (`r₀ ≤ ρ_K`) there is a uniform `M'` with
        `∀ q ∈ K, ∀ ‖v‖ < r₀,
            ‖fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp … q) u) w) v‖ ≤ M'`,
      from ONLY `hC` (Christoffel `C^∞`) + `IsCompact K` — NO carried `hdiag`, `hs12`, `hs23`.  DERIVED by
      feeding X1's diagonal cubic bound + the two symmetries into the banked conditional CLM theorem
      `uniformFlowExp_thirdJet_opNorm_le_of_symm_diag_bound`.  This is the exact object the C³ climb's W4
      assembly consumes (`‖B₃(q,v)‖`), now with all three W3 inputs discharged.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import QIQTH.UniformFlowThirdJetCLM
import QIQTH.UniformFlowThirdUncond
import QIQTH.UniformFlowThirdBoundClose
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

variable {n : ℕ}

/-- **★ W3 UNCONDITIONAL, CLM form.**  The uniform operator-norm bound on the CLM-valued third jet
    `B₃(q,v) := fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v`
    over a compact base set `K`, from ONLY `hC` + `IsCompact K` — with NO carried diagonal bound and NO
    carried symmetries.  DERIVED by discharging the three carried inputs of the banked conditional CLM
    theorem `uniformFlowExp_thirdJet_opNorm_le_of_symm_diag_bound`:
      * P1 (`hdiag`) via `uniformFlowExp_thirdDeriv_diag_cubic_bound` (X1, the comparison-field route);
      * P2 (`hs12`) via `uniformFlowExp_thirdJet_symm12` (Clairaut);
      * P2 (`hs23`) via `uniformFlowExp_thirdJet_symm23` (flip equivalence).
    The radius `r₀` and constant `M₃'` are X1's genuine uniform data (`r₀ ≤ ρ_K`); `M' = (9/2)·M₃'`.
    NOT `a₁ = R/6`. -/
theorem uniformFlowExp_thirdJet_opNorm_le_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), r₀ ≤ uniformFlowRadius g gi hC hK ∧ ∃ M' : ℝ,
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
        ‖fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v‖ ≤ M' := by
  -- P1 (X1): the uniform diagonal cubic bound, with its own radius `r₀ ≤ ρ_K` and constant `M₃'`.
  obtain ⟨r₀, hr₀0, hrρ, M₃', hM₃'0, hdiag⟩ :=
    uniformFlowExp_thirdDeriv_diag_cubic_bound g gi hC hK
  -- Feed P1 + the two P2 symmetries into the banked conditional CLM theorem.
  obtain ⟨M', hM'⟩ :=
    uniformFlowExp_thirdJet_opNorm_le_of_symm_diag_bound g gi hC hK hM₃'0 hrρ
      (fun q hq v hv x y z =>
        uniformFlowExp_thirdJet_symm12 g gi hC hK q hq v (lt_of_lt_of_le hv hrρ) x y z)
      (fun q hq v hv x y z =>
        uniformFlowExp_thirdJet_symm23 g gi hC hK q hq v (lt_of_lt_of_le hv hrρ) x y z)
      hdiag
  exact ⟨r₀, hr₀0, hrρ, M', hM'⟩

end QIQTH.ExpMap
