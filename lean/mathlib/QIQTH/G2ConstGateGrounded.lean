/-
  G2ConstGateGrounded — grounding the census-side G2 gate carry for the LIVE concrete gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick.  No `sorry`, no `:= True`, no new axioms, no vacuous / unsatisfiable hypotheses, no result
  that is a conclusion-in-disguise.  std-3 only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  The modulo-G2 census closure (`CensusHballrateModuloG2`/`CensusIntegratedModuloG2`)
  carries a SINGLE census-side gate hypothesis
      `hS : ∃ rS > 0, Metric.ball 0 rS ⊆ {z | 0 ∈ S z}`
  for a GENERAL gate family `S : Point n → Set (Point n)`.  The J4-961 report flagged this as a
  genuinely NEW ungrounded carry: the teeth theorem there proves only CONSISTENCY at a test gate
  (`S z := ball z 1`), NOT the live instance for the campaign's ACTUAL concrete gate.

  ## THE LIVE CONCRETE GATE.  The top-level `A1R6CoreAtGate.wide_a1_R6_core_AT_CONSTRADIUS` chain runs
  every per-gate slot at the ONE shared syntactic gate
      `constGate g gi hChr hK c := fun z => uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`
  (`A1R6CoreAtGate.constGate`), the J4-316 constant-radius flow-ball gate.

  ## THE DISCHARGE (all DERIVED from the bank; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
  For this concrete `S = constGate g gi hChr hK c`, `0 ∈ S z` unfolds to
      `∃ w ∈ ball 0 c, uniformFlowExp g gi hChr hK z w = 0`,
  i.e. the flow at base `z` reaches the origin from a velocity `w` of norm `< c`.  The banked
  inverse-chart facts supply EXACTLY such a witness `w := uniformInverseChart g gi hChr hK z 0`:
      • `HeatResidualBound.chartW0_rightInverse` : `uniformFlowExp z (W₀ z) = 0`  (`‖z‖ < rRI`, `z∈K`);
      • `HeatResidualBound.chartW0_displacement` : `‖W₀ z + z‖ ≤ C_W·‖z‖²`         (`‖z‖ < r₁`, `z∈K`),
        whence `‖W₀ z‖ ≤ (1 + C_W)·‖z‖` for `‖z‖ ≤ 1`.
  Choosing `rS := min (min εK r₁) (min rRI (min 1 (c/(1+C_W))))` (`εK` = a `𝓝 0` ball radius inside
  `K`) makes, for every `z ∈ ball 0 rS`: `z ∈ K`, `‖W₀ z‖ < c` (so `W₀ z ∈ ball 0 c`), and
  `uniformFlowExp z (W₀ z) = 0` — hence `0 ∈ constGate g gi hChr hK c z`.

  This is a straightforward specialization of the SAME `hzfacts` computation banked in
  `C2CarrierCollapse.c2_carriers_discharged`; here we only need the origin-reaching witness, not the
  full six-carrier bundle.  NON-VACUITY: all hypotheses `{hC, hK, h0Kmem, 0<c}` are inhabited by any
  Riemannian metric with a positive gate radius; the returned `rS` is strictly positive and the
  subset genuine (the gate `{z | 0 ∈ constGate … c z}` is a proper neighbourhood, not `univ`).
  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.A1R6CoreAtGate
import QIQTH.InverseChartDisplacement
import QIQTH.ResidueThreading
import QIQTH.FrozenGauss

open Filter Set Metric
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.A1R6CoreAtGate
open scoped Topology ContDiff

namespace QIQTH.G2ConstGateGrounded

variable {n : ℕ}

/-- **★★★ `g2_for_constGate` — the census-side G2 gate carry, GROUNDED for the live concrete gate.**
    For the shared syntactic constant-radius flow-ball gate `S := constGate g gi hC hK c` (`0 < c`),
    there is a strictly positive radius `rS` such that `Metric.ball 0 rS ⊆ {z | 0 ∈ S z}` — i.e. the
    ORIGIN lies in the gate for every base point near the origin.  This is the EXACT predicate shape
    of the `hS` carry in `CensusHballrateModuloG2.hballrate_moduloG2` /
    `CensusIntegratedModuloG2.censusBound_integrated_moduloG2`, specialized to the live gate.

    The witness at base `z` is the inverse-chart origin coordinate
    `w := uniformInverseChart g gi hC hK z 0`, which the banked lemmas certify satisfies
    `uniformFlowExp z w = 0` and `‖w‖ ≤ (1+C_W)‖z‖ < c`.  DERIVED from the bank; NOT `a₁ = R/6`. -/
theorem g2_for_constGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    {c : ℝ} (hc : 0 < c) :
    ∃ rS : ℝ, 0 < rS ∧
      Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ constGate g gi hC hK c z} := by
  classical
  -- banked ingredients.
  obtain ⟨εK, hεK0, hεKsub⟩ := Metric.mem_nhds_iff.mp h0Kmem
  obtain ⟨r₁, hr₁0, C_W, hCW0, hD1⟩ := chartW0_displacement g gi hC hK
  obtain ⟨rRI, hrRI0, hRIspec⟩ := chartW0_rightInverse g gi hC hK
  have h1CW : (0 : ℝ) < 1 + C_W := by linarith
  -- the census gate radius: strictly below every field radius, `1`, and `c/(1+C_W)`.
  set rS : ℝ := min (min εK r₁) (min rRI (min 1 (c / (1 + C_W)))) with hrSdef
  have hrS_εK : rS ≤ εK := le_trans (min_le_left _ _) (min_le_left _ _)
  have hrS_r₁ : rS ≤ r₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrS_rRI : rS ≤ rRI := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrS_1 : rS ≤ 1 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hrS_cW : rS ≤ c / (1 + C_W) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hrS0 : 0 < rS :=
    lt_min (lt_min hεK0 hr₁0) (lt_min hrRI0 (lt_min one_pos (by positivity)))
  refine ⟨rS, hrS0, ?_⟩
  intro z hz
  have hzn : ‖z‖ < rS := mem_ball_zero_iff.mp hz
  -- `z ∈ K`.
  have zK : z ∈ K := hεKsub (mem_ball_zero_iff.mpr (lt_of_lt_of_le hzn hrS_εK))
  have hzr₁ : ‖z‖ < r₁ := lt_of_lt_of_le hzn hrS_r₁
  have hzrRI : ‖z‖ < rRI := lt_of_lt_of_le hzn hrS_rRI
  have hz1 : ‖z‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hzn hrS_1)
  have hznn : 0 ≤ ‖z‖ := norm_nonneg z
  -- the origin-reaching witness `w := W₀ z`.
  set w : Point n := uniformInverseChart g gi hC hK z 0 with hwdef
  have hDisp : ‖w + z‖ ≤ C_W * ‖z‖ * ‖z‖ := hD1 z zK hzr₁
  have hRIz : uniformFlowExp g gi hC hK z w = 0 := hRIspec z zK hzrRI
  -- `‖w‖ ≤ (1+C_W)‖z‖`.
  have hWle : ‖w‖ ≤ (1 + C_W) * ‖z‖ := by
    have htri : ‖w‖ ≤ ‖w + z‖ + ‖z‖ := by
      calc ‖w‖ = ‖(w + z) - z‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖w + z‖ + ‖z‖ := norm_sub_le _ _
    nlinarith [htri, hDisp, mul_nonneg (mul_nonneg hCW0 hznn) (sub_nonneg.mpr hz1)]
  -- `‖w‖ < c`.
  have hWc : ‖w‖ < c := by
    have hstep : (1 + C_W) * ‖z‖ < (1 + C_W) * rS :=
      mul_lt_mul_of_pos_left hzn h1CW
    have hlt : (1 + C_W) * rS ≤ c := by
      have := (mul_le_mul_of_nonneg_left hrS_cW (le_of_lt h1CW))
      rwa [mul_div_cancel₀ _ (ne_of_gt h1CW)] at this
    exact lt_of_le_of_lt hWle (lt_of_lt_of_le hstep hlt)
  -- assemble `0 ∈ constGate … c z = uniformFlowExp z '' ball 0 c`.
  have hwmem : w ∈ Metric.ball (0 : Point n) c := mem_ball_zero_iff.mpr hWc
  show (0 : Point n) ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c
  exact ⟨w, hwmem, hRIz⟩

/-- **★★ `g2_for_constGate_satisfiable` — NON-VACUITY witness (against a GENUINE metric).**  The
    hypothesis bundle `{hC, hK compact, K ∈ 𝓝 0, 0 < c}` of `g2_for_constGate` is jointly inhabited
    by a CONCRETE Riemannian instance — the flat (frozen) metric `g = gi = Id`, `K = closedBall 0 1`,
    `c = 1` — and, at that instance, `g2_for_constGate` genuinely PRODUCES a strictly-positive census
    gate radius `rS` with `ball 0 rS ⊆ {z | 0 ∈ constGate … z}`.  So the discharge is not vacuously
    true through impossible antecedents.  (Flat Christoffels vanish, `FrozenGauss.christoffel_const`,
    hence `hC` is `contDiff_const`; `closedBall` is compact in the proper space `Fin n → ℝ` and is a
    `𝓝 0` neighbourhood.)  NOT `a₁ = R/6`. -/
theorem g2_for_constGate_satisfiable :
    ∃ (g gi : Point n → Fin n → Fin n → ℝ)
      (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
      (K : Set (Point n)) (hK : IsCompact K),
        K ∈ 𝓝 (0 : Point n) ∧
        ∃ rS : ℝ, 0 < rS ∧
          Metric.ball (0 : Point n) rS
            ⊆ {z | (0 : Point n) ∈ constGate g gi hC hK (1 : ℝ) z} := by
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
  have hmem : Metric.closedBall (0 : Point n) 1 ∈ 𝓝 (0 : Point n) :=
    Metric.closedBall_mem_nhds _ one_pos
  exact ⟨fun _ => A, fun _ => A, hC, Metric.closedBall (0 : Point n) 1, hK, hmem,
    g2_for_constGate (fun _ => A) (fun _ => A) hC hK hmem one_pos⟩

end QIQTH.G2ConstGateGrounded
