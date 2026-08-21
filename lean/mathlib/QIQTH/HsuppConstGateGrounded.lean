/-
  HsuppConstGateGrounded — grounding the census-side `hSupp` small-gate carry for the LIVE concrete gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick.  No `sorry`, no `:= True`, no new axioms, no vacuous / unsatisfiable hypotheses, no result
  that is a conclusion-in-disguise.  std-3 only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  The modulo-G2 census closure (`CensusIntegratedModuloG2.censusBound_integrated_
  moduloG2` / `hcross_integrated_moduloG2`) carries, per gate record `D`, the small-gate UPPER
  containment
      `hSupp : ∀ z ∈ K, 0 ∈ S z → ‖z‖ < D.r`
  for a GENERAL gate family `S : Point n → Set (Point n)`.  This is the OPPOSITE containment to the
  G2 gate carry (`∃ rS>0, ball 0 rS ⊆ {z | 0 ∈ S z}`, a LOWER one, grounded in `G2ConstGateGrounded`):
  hSupp bounds the base points that can reach the origin, from ABOVE.

  ## THE LIVE CONCRETE GATE.  The top-level `A1R6CoreAtGate.wide_a1_R6_core_AT_CONSTRADIUS` chain runs
  every per-gate slot at the ONE shared syntactic gate
      `constGate g gi hC hK c := fun z => uniformFlowExp g gi hC hK z '' Metric.ball 0 c`.

  ## THE DISCHARGE (all DERIVED from the bank; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
  For `S = constGate g gi hC hK c`, `0 ∈ S z` unfolds to `∃ w ∈ ball 0 c, uniformFlowExp z w = 0` —
  the flow at base `z` reaches the origin from a velocity `w` with `‖w‖ < c`.  The banked forward
  quadratic displacement bound
      `ExpMap.uniformFlowExp_displacement_bound : ∃ ρ₀>0, ∃ C_D≥0, ∀ q∈K, ∀ v, ‖v‖<ρ₀ →
          ‖uniformFlowExp q v − q − v‖ ≤ C_D·‖v‖·‖v‖`
  then pins `z` down: with `c ≤ ρ₀` (so `‖w‖ < ρ₀`) and `uniformFlowExp z w = 0`,
      `‖z + w‖ = ‖uniformFlowExp z w − z − w‖ ≤ C_D·‖w‖²`,
  hence `‖z‖ ≤ ‖z + w‖ + ‖w‖ ≤ ‖w‖ + C_D·‖w‖² < c·(1 + C_D·c)`.  So under the radius COUPLING
  `c·(1 + C_D·c) ≤ D.r`, every origin-reaching base point `z` has `‖z‖ < D.r` — exactly `hSupp`.

  This CONVERTS the abstract per-`D` `hSupp` carry into a CONCRETE geometric consequence, modulo a
  single explicit radius inequality between the gate radius `c` and `D.r` (the flow constants `ρ₀`,
  `C_D` exposed existentially, exactly as `G2ConstGateGrounded` exposed `rS`).  gpt-5.6-sol (high)
  audit: SOUND and non-vacuous; the coupling direction is OPPOSITE to G2's (G2 needs `c` large
  relative to a lower ball, hSupp needs `c` small relative to `D.r`), and the two are JOINTLY
  satisfiable on a non-empty `c`-window (`(1+C_W)·rS ≤ c ≤ min ρ₀ U`).

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.A1R6CoreAtGate
import QIQTH.InverseChartNormalJets
import QIQTH.NearIsometryBudget
import QIQTH.FrozenGauss

open Filter Set Metric
open QIQTH.Curvature QIQTH.ExpMap QIQTH.A1R6CoreAtGate QIQTH.InverseChartNormalJets
open scoped Topology ContDiff

namespace QIQTH.HsuppConstGateGrounded

variable {n : ℕ}

/-- **★★★ `hsupp_for_constGate` — the census-side `hSupp` small-gate carry, GROUNDED for the live
    concrete gate, modulo a single explicit radius coupling.**  For the shared syntactic
    constant-radius flow-ball gate `S := constGate g gi hC hK c`, there exist flow constants
    `ρ₀ > 0`, `C_D ≥ 0` (the banked forward quadratic-displacement constants) such that for EVERY
    gate record `D` and every gate radius `c` with `0 < c`, `c ≤ ρ₀`, and the radius COUPLING
    `c·(1 + C_D·c) ≤ D.r`, the UPPER small-gate containment
        `∀ z ∈ K, 0 ∈ constGate g gi hC hK c z → ‖z‖ < D.r`
    holds.  This is the EXACT `hSupp` slot shape of `CensusIntegratedModuloG2.censusBound_integrated_
    moduloG2`, specialized to the live gate.  DERIVED from the bank; NOT `a₁ = R/6`. -/
theorem hsupp_for_constGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_D : ℝ, 0 ≤ C_D ∧
      ∀ (D : FixedFlowGateData g gi hC hK) {c : ℝ}, 0 < c → c ≤ ρ₀ →
        c * (1 + C_D * c) ≤ D.r →
        ∀ z ∈ K, (0 : Point n) ∈ constGate g gi hC hK c z → ‖z‖ < D.r := by
  classical
  obtain ⟨ρ₀, hρ₀, C_D, hCD0, hbnd⟩ := uniformFlowExp_displacement_bound g gi hC hK
  refine ⟨ρ₀, hρ₀, C_D, hCD0, ?_⟩
  intro D c hc hcρ hcoup z hzK hmem
  -- unfold `0 ∈ constGate … c z`:  `∃ w ∈ ball 0 c, uniformFlowExp z w = 0`.
  obtain ⟨w, hwmem, hweq⟩ :
      (0 : Point n) ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c := hmem
  have hwn : ‖w‖ < c := mem_ball_zero_iff.mp hwmem
  have hwρ₀ : ‖w‖ < ρ₀ := lt_of_lt_of_le hwn hcρ
  have hwnn : 0 ≤ ‖w‖ := norm_nonneg w
  -- forward displacement:  `‖z + w‖ ≤ C_D·‖w‖²`.
  have hDisp : ‖uniformFlowExp g gi hC hK z w - z - w‖ ≤ C_D * ‖w‖ * ‖w‖ := hbnd z hzK w hwρ₀
  have hzw : ‖z + w‖ ≤ C_D * ‖w‖ * ‖w‖ := by
    have hrw : uniformFlowExp g gi hC hK z w - z - w = -(z + w) := by rw [hweq]; abel
    rw [hrw, norm_neg] at hDisp; exact hDisp
  -- `‖z‖ ≤ ‖z + w‖ + ‖w‖ ≤ ‖w‖ + C_D·‖w‖²`.
  have htri : ‖z‖ ≤ ‖z + w‖ + ‖w‖ := by
    calc ‖z‖ = ‖(z + w) - w‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖z + w‖ + ‖w‖ := norm_sub_le _ _
  have hzle : ‖z‖ ≤ ‖w‖ + C_D * ‖w‖ * ‖w‖ := by linarith
  -- `‖w‖ + C_D·‖w‖² < c·(1 + C_D·c)`, then the coupling closes it.
  have hstrict : ‖w‖ + C_D * ‖w‖ * ‖w‖ < c * (1 + C_D * c) := by
    nlinarith [hwn, hCD0, hwnn, hc.le, mul_nonneg hCD0 hwnn,
      mul_nonneg hCD0 (mul_nonneg (sub_nonneg.mpr hwn.le) (add_nonneg hwnn hc.le))]
  exact lt_of_le_of_lt hzle (lt_of_lt_of_le hstrict hcoup)

/-- **★★ `hsupp_constGate_coupling_satisfiable` — the radius coupling is satisfiable for ANY gate
    record with a positive gate radius.**  Given the flow constants `ρ₀ > 0`, `C_D ≥ 0` and any
    `D.r > 0`, there is a strictly-positive gate radius `c` with `c ≤ ρ₀` and `c·(1 + C_D·c) ≤ D.r`
    — so `hsupp_for_constGate`'s coupling is never vacuously unsatisfiable, and small enough gates
    always satisfy the UPPER containment.  (Choose `c := min ρ₀ (min 1 (D.r/(1 + C_D)))`.)
    NOT `a₁ = R/6`. -/
theorem hsupp_constGate_coupling_satisfiable {ρ₀ C_D r : ℝ}
    (hρ₀ : 0 < ρ₀) (hCD0 : 0 ≤ C_D) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ c ≤ ρ₀ ∧ c * (1 + C_D * c) ≤ r := by
  have h1CD : (0 : ℝ) < 1 + C_D := by linarith
  set c : ℝ := min ρ₀ (min 1 (r / (1 + C_D))) with hcdef
  have hc_ρ₀ : c ≤ ρ₀ := min_le_left _ _
  have hc_1 : c ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc_r : c ≤ r / (1 + C_D) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hc0 : 0 < c := lt_min hρ₀ (lt_min one_pos (by positivity))
  refine ⟨c, hc0, hc_ρ₀, ?_⟩
  -- `1 + C_D·c ≤ 1 + C_D` (from `c ≤ 1`), and `c·(1 + C_D) ≤ r` (from `c ≤ r/(1+C_D)`).
  have hfac : 1 + C_D * c ≤ 1 + C_D := by nlinarith [hCD0, hc_1, hc0.le]
  have hcr : c * (1 + C_D) ≤ r := by
    have := mul_le_mul_of_nonneg_left hc_r (le_of_lt h1CD)
    calc c * (1 + C_D) = (1 + C_D) * c := by ring
      _ ≤ (1 + C_D) * (r / (1 + C_D)) := mul_le_mul_of_nonneg_left hc_r (le_of_lt h1CD)
      _ = r := by rw [mul_div_cancel₀ _ (ne_of_gt h1CD)]
  calc c * (1 + C_D * c) ≤ c * (1 + C_D) := mul_le_mul_of_nonneg_left hfac hc0.le
    _ ≤ r := hcr

/-- **★★ `hsupp_for_constGate_satisfiable` — NON-VACUITY against a GENUINE metric.**  The hypothesis
    bundle of `hsupp_for_constGate` is jointly inhabited by a CONCRETE Riemannian instance — the flat
    (frozen) metric `g = gi = Id`, `K = closedBall 0 1` — at which the flow constants exist and, for
    any `D` with a positive gate radius, a positive gate radius `c` satisfying the coupling exists.
    So the discharge is not vacuously true through impossible antecedents.  NOT `a₁ = R/6`. -/
theorem hsupp_for_constGate_satisfiable :
    ∃ (g gi : Point n → Fin n → Fin n → ℝ)
      (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
      (K : Set (Point n)) (hK : IsCompact K),
        ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_D : ℝ, 0 ≤ C_D ∧
          (∀ (D : FixedFlowGateData g gi hC hK) {c : ℝ}, 0 < c → c ≤ ρ₀ →
            c * (1 + C_D * c) ≤ D.r →
            ∀ z ∈ K, (0 : Point n) ∈ constGate g gi hC hK c z → ‖z‖ < D.r) ∧
          (∀ D : FixedFlowGateData g gi hC hK,
            ∃ c : ℝ, 0 < c ∧ c ≤ ρ₀ ∧ c * (1 + C_D * c) ≤ D.r) := by
  classical
  set A : Fin n → Fin n → ℝ := fun i j => if i = j then (1 : ℝ) else 0 with hA
  have hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (fun _ => A) (fun _ => A) a b c y) := by
    intro a b c
    have h : (fun y => christoffel (fun _ => A) (fun _ => A) a b c y)
        = (fun _ : Point n => (0 : ℝ)) :=
      funext fun y => QIQTH.FrozenGauss.christoffel_const A A a b c y
    rw [h]; exact contDiff_const
  have hK : IsCompact (Metric.closedBall (0 : Point n) 1) := isCompact_closedBall _ _
  obtain ⟨ρ₀, hρ₀, C_D, hCD0, hbnd⟩ :=
    hsupp_for_constGate (fun _ => A) (fun _ => A) hC hK
  refine ⟨fun _ => A, fun _ => A, hC, Metric.closedBall (0 : Point n) 1, hK,
    ρ₀, hρ₀, C_D, hCD0, hbnd, ?_⟩
  intro D
  -- `D.r > 0` from the structure invariants `0 < a < b < r`.
  have hDr : 0 < D.r := lt_trans (lt_trans D.ha D.hab) D.hbr
  exact hsupp_constGate_coupling_satisfiable hρ₀ hCD0 hDr

end QIQTH.HsuppConstGateGrounded

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HsuppConstGateGrounded
#print axioms hsupp_for_constGate
#print axioms hsupp_constGate_coupling_satisfiable
#print axioms hsupp_for_constGate_satisfiable
end AxiomChecks
