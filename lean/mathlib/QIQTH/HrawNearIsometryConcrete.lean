/-
  HrawNearIsometryConcrete — J4-361: THE CONCRETE TWO-SIDED NEAR-ISOMETRY (`hraw` step 2, the
  T1-hypothesis of the banked chart→ambient transfer).  Ledger `docs/qg_roadmap/JET4_TOWER_PLAN.md`
  §§ J4-359 / J4-360 / J4-361; consumes `HrawChartTransfer.chartTransfer_from_nearIsometry` /
  `HrawChartTransfer.nearIsometry_budgets` whose EXACT T1-hypothesis shape is
      `|rncRadialSq v − rncRadialSq z| ≤ (1/4)·rncRadialSq z`,  `z := uniformFlowExp … q v − q`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  concrete near-isometry brick feeding the LABELLED input `hraw`.  No `sorry` (header prose excepted),
  no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or
  trivially yielding) the conclusion, no existing file edited, nothing committed.  `a₁ = R/6` stays
  CONDITIONAL on the whole convergence / geometric-wiring stack AND on `hraw`/`hD2Hexpand`/`hPd2conv`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ROUTE (N1 → N2 → N3).

  •  (N1) THE FLOW-DISPLACEMENT BOUND.  `‖uniformFlowExp g gi hC hK q v − q − v‖ ≤ C_D·‖v‖·‖v‖` — the
     geodesic's second-order deviation from the straight line, BANKED verbatim as
     `QIQTH.ExpMap.uniformFlowExp_displacement_bound` (D2 of `NearIsometryBudget.lean`, itself the
     segment mean-value inequality on `w ↦ φ_q w − w` off the near-identity Jacobian bound D1, whose
     velocity control is the compact-uniform geodesic confinement).  We re-export it as
     `flowDisplacement_bound`.  (Bank-inventory verdict: N1 is DERIVED already — no new ODE work.)

  •  (N2) THE RADIAL-SQUARE COMPARISON.  For any `v z : Point n`, letting `e := z − v`,
        `|rncRadialSq v − rncRadialSq z| ≤ 2·n·(‖v‖+‖z‖)·‖z−v‖ + n·‖z−v‖²`
     (`rncRadialSq_abs_sub_le`).  Proof: two applications of the banked ℓ² expansion
     `HeatResidualBound.rncRadialSq_add_le` — `z = v + e` (upper) and `v = z + (−e)` (lower) — bounded
     by the common `2·n·(‖v‖+‖z‖)·‖e‖ + n·‖e‖²`.  Convention: `rncRadialSq w = ∑ wᵢ²` (ℓ²), and the
     ambient norm on `Point n = Fin n → ℝ` is the sup-norm, so the `n`-cofactors are honest.

  •  (N3) THE (1/4)-BUDGET.  With `z := uniformFlowExp … q v − q` and `e = z − v`, N1 gives
     `‖e‖ ≤ C_D·‖v‖²`, so N2's RHS is `O(‖v‖³)`.  A shrunk gate `‖v‖ < r*` (explicit,
     `r* = min ρ₀ (min 1 (min (1/(2C_D+1)) (1/(16(5nC_D+nC_D²)+1))))`) makes `C_D‖v‖ ≤ 1/2`, hence the
     bootstrap `‖z‖ ≥ ‖v‖/2` and (via `‖z‖² ≤ rncRadialSq z`) the LOWER control `rncRadialSq z ≥
     ‖v‖²/4`; the `O(‖v‖³)` numerator is then ≤ `‖v‖²/16 ≤ (1/4)·rncRadialSq z`.  Delivered as
     `nearIsometry_concrete` — the EXACT T1-hypothesis on the explicit shrunk gate.

  ## DELIVERABLES.
  •  (N1) `flowDisplacement_bound` — banked re-export of the quadratic flow displacement bound.
  •  (N2) `rncRadialSq_abs_sub_le` — the abstract two-sided radial comparison.
  •  (N3) `nearIsometry_concrete` — `∃ r*>0, ∀ q∈K, ∀ v, ‖v‖<r* →
        |rncRadialSq v − rncRadialSq (uniformFlowExp … q v − q)| ≤ (1/4)·rncRadialSq (uniformFlowExp … q v − q)`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.NearIsometryBudget
import QIQTH.InverseChartDisplacement

open Set Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatResidualBound
open scoped Topology BigOperators

namespace QIQTH.HrawNearIsometryConcrete

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### (N1) — the flow-displacement bound (banked re-export).
    ############################################################################### -/

/-- **★ (N1) — `flowDisplacement_bound`.**  THE QUADRATIC FLOW-DISPLACEMENT BOUND, re-exported verbatim
    from `QIQTH.ExpMap.uniformFlowExp_displacement_bound` (D2, `NearIsometryBudget.lean`): there are
    `ρ₀ > 0` and `C_D ≥ 0` such that for every `q ∈ K` and `‖v‖ < ρ₀`,
        `‖uniformFlowExp g gi hC hK q v − q − v‖ ≤ C_D·‖v‖·‖v‖`.
    This is the geodesic's second-order deviation from the straight line — the classical ODE estimate,
    already DERIVED in the bank (segment mean-value on `w ↦ φ_q w − w` off the near-identity Jacobian
    bound, whose velocity control is the compact-uniform geodesic confinement).  NOT `a₁ = R/6`. -/
theorem flowDisplacement_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_D * ‖v‖ * ‖v‖ :=
  QIQTH.ExpMap.uniformFlowExp_displacement_bound g gi hC hK

/-! ###############################################################################
    ### (N2) — the abstract two-sided radial-square comparison.
    ############################################################################### -/

/-- **★ (N2) — `rncRadialSq_abs_sub_le`.**  THE ABSTRACT TWO-SIDED RADIAL COMPARISON.  For any two
    points `v z : Point n`,
        `|rncRadialSq v − rncRadialSq z| ≤ 2·n·(‖v‖+‖z‖)·‖z−v‖ + n·‖z−v‖²`.
    Two applications of the banked ℓ² expansion `HeatResidualBound.rncRadialSq_add_le`, at `z = v + e`
    (`e := z−v`; the UPPER excess `rncRadialSq z − rncRadialSq v ≤ 2n‖v‖‖e‖ + n‖e‖²`) and at
    `v = z + (−e)` (the LOWER excess `rncRadialSq v − rncRadialSq z ≤ 2n‖z‖‖e‖ + n‖e‖²`), each bounded
    by the symmetric `2n(‖v‖+‖z‖)‖e‖ + n‖e‖²`.  NOT `a₁ = R/6`. -/
theorem rncRadialSq_abs_sub_le (v z : Point n) :
    |rncRadialSq v - rncRadialSq z|
      ≤ 2 * (n : ℝ) * (‖v‖ + ‖z‖) * ‖z - v‖ + (n : ℝ) * ‖z - v‖ ^ 2 := by
  -- UPPER: `rncRadialSq z ≤ rncRadialSq v + 2n·‖v‖‖z−v‖ + n·‖z−v‖²` (from `z = v + (z−v)`).
  have hUp : rncRadialSq z
      ≤ rncRadialSq v + 2 * (n : ℝ) * (‖v‖ * ‖z - v‖) + (n : ℝ) * ‖z - v‖ ^ 2 := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_add_le v (z - v)
    rwa [show v + (z - v) = z from by abel] at h
  -- LOWER: `rncRadialSq v ≤ rncRadialSq z + 2n·‖z‖‖z−v‖ + n·‖z−v‖²` (from `v = z + (−(z−v))`).
  have hLo : rncRadialSq v
      ≤ rncRadialSq z + 2 * (n : ℝ) * (‖z‖ * ‖z - v‖) + (n : ℝ) * ‖z - v‖ ^ 2 := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_add_le z (-(z - v))
    rw [show z + (-(z - v)) = v from by abel] at h
    simp only [norm_neg] at h
    exact h
  have p1 : (0 : ℝ) ≤ 2 * (n : ℝ) * (‖v‖ * ‖z - v‖) := by positivity
  have p2 : (0 : ℝ) ≤ 2 * (n : ℝ) * (‖z‖ * ‖z - v‖) := by positivity
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [hUp, p2]
  · nlinarith [hLo, p1]

/-! ###############################################################################
    ### (N3) — the concrete (1/4)-near-isometry on the explicit shrunk gate.
    ############################################################################### -/

/-- **★★ (N3) — `nearIsometry_concrete`.**  THE CONCRETE TWO-SIDED NEAR-ISOMETRY (the T1-hypothesis of
    `HrawChartTransfer.chartTransfer_from_nearIsometry` / `nearIsometry_budgets`).  There is an explicit
    shrunk gate radius `r* > 0` such that for every `q ∈ K` and `‖v‖ < r*`, with `z := uniformFlowExp
    g gi hC hK q v − q` the ambient displacement of the exp point,
        `|rncRadialSq v − rncRadialSq z| ≤ (1/4)·rncRadialSq z`.
    N1 (`flowDisplacement_bound`) supplies `‖z−v‖ ≤ C_D·‖v‖²`; N2 (`rncRadialSq_abs_sub_le`) turns it
    into the `O(‖v‖³)` comparison; the gate `r* = min ρ₀ (min 1 (min (1/(2C_D+1)) (1/(16·M+1))))`,
    `M = 5nC_D + nC_D²`, forces `C_D‖v‖ ≤ 1/2` ⟹ `‖z‖ ≥ ‖v‖/2` ⟹ (via `‖z‖² ≤ rncRadialSq z`)
    `rncRadialSq z ≥ ‖v‖²/4`, whence `O(‖v‖³) ≤ ‖v‖²/16 ≤ (1/4)·rncRadialSq z`.  NOT `a₁ = R/6`. -/
theorem nearIsometry_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r →
      |rncRadialSq v - rncRadialSq (uniformFlowExp g gi hC hK q v - q)|
        ≤ 1 / 4 * rncRadialSq (uniformFlowExp g gi hC hK q v - q) := by
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hdisp⟩ := flowDisplacement_bound g gi hC hK
  have hN0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- the coefficient `M = 5nC_D + nC_D²` and the gate-shrinking denominator `D = 16M+1`.
  set M : ℝ := 5 * (n : ℝ) * C_D + (n : ℝ) * C_D ^ 2 with hMdef
  have hM0 : 0 ≤ M := by
    have a1 : 0 ≤ 5 * (n : ℝ) * C_D := mul_nonneg (by positivity) hCD0
    have a2 : 0 ≤ (n : ℝ) * C_D ^ 2 := mul_nonneg hN0 (sq_nonneg C_D)
    rw [hMdef]; linarith
  set D : ℝ := 16 * M + 1 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; linarith
  have h2C1pos : 0 < 2 * C_D + 1 := by linarith
  -- the explicit shrunk gate radius.
  set r : ℝ := min ρ₀ (min 1 (min (1 / (2 * C_D + 1)) (1 / D))) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min hρ₀pos (lt_min one_pos (lt_min (div_pos one_pos h2C1pos) (div_pos one_pos hDpos)))
  refine ⟨r, hrpos, ?_⟩
  intro q hq v hv
  -- the four gate consequences.
  have hvρ₀ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (by rw [hrdef]; exact min_le_left _ _)
  have hv1 : ‖v‖ ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hv (by rw [hrdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)))
  have hvC : ‖v‖ ≤ 1 / (2 * C_D + 1) :=
    le_of_lt (lt_of_lt_of_le hv
      (by rw [hrdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hvD : ‖v‖ ≤ 1 / D :=
    le_of_lt (lt_of_lt_of_le hv
      (by rw [hrdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  -- the ambient displacement of the exp point.
  set z : Point n := uniformFlowExp g gi hC hK q v - q with hz
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  -- N1 at `(q, v)`.
  have hE : ‖z - v‖ ≤ C_D * ‖v‖ * ‖v‖ := by
    have h := hdisp q hq v hvρ₀
    rwa [show uniformFlowExp g gi hC hK q v - q - v = z - v from by rw [hz]] at h
  -- `C_D‖v‖ ≤ 1/2` from the `1/(2C_D+1)` gate.
  have hkey : ‖v‖ * (2 * C_D + 1) ≤ 1 := (le_div_iff₀ h2C1pos).mp hvC
  have hCr : C_D * ‖v‖ ≤ 1 / 2 := by nlinarith [hkey, hv0]
  -- `‖z−v‖ ≤ (1/2)‖v‖`  and  `‖z−v‖ ≤ C_D‖v‖²`.
  have hEub2 : ‖z - v‖ ≤ 1 / 2 * ‖v‖ := by
    nlinarith [hE, mul_le_mul_of_nonneg_right hCr hv0]
  have hE_le : ‖z - v‖ ≤ C_D * ‖v‖ ^ 2 := by nlinarith [hE]
  -- triangle bounds relating `‖z‖` and `‖v‖`.
  have hZub : ‖z‖ ≤ ‖v‖ + ‖z - v‖ := by
    have h := norm_add_le v (z - v); rwa [show v + (z - v) = z from by abel] at h
  have htri : ‖v‖ ≤ ‖z‖ + ‖z - v‖ := by
    have h := norm_add_le z (-(z - v))
    rw [show z + (-(z - v)) = v from by abel, norm_neg] at h; exact h
  -- the lower control on `rncRadialSq z`.
  have hZlb : ‖v‖ / 2 ≤ ‖z‖ := by linarith [htri, hEub2]
  have hsq : (‖v‖ / 2) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hZlb 2
  have hrz_lb : ‖v‖ ^ 2 / 4 ≤ rncRadialSq z := by
    have hns := QIQTH.HeatResidualBound.norm_sq_le_rncRadialSq z
    nlinarith [hsq, hns]
  -- the `O(‖v‖³)` numerator control.
  have hZ32 : ‖z‖ ≤ 3 / 2 * ‖v‖ := by linarith [hZub, hEub2]
  have hVZ : ‖v‖ + ‖z‖ ≤ 5 / 2 * ‖v‖ := by linarith [hZ32]
  have hNC2 : (0 : ℝ) ≤ (n : ℝ) * C_D ^ 2 := mul_nonneg hN0 (sq_nonneg C_D)
  have hV43 : ‖v‖ ^ 4 ≤ ‖v‖ ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hv1 (pow_nonneg hv0 3); nlinarith [h]
  have hTerm1 : 2 * (n : ℝ) * (‖v‖ + ‖z‖) * ‖z - v‖ ≤ 5 * (n : ℝ) * C_D * ‖v‖ ^ 3 := by
    have h1 : (‖v‖ + ‖z‖) * ‖z - v‖ ≤ (5 / 2 * ‖v‖) * (C_D * ‖v‖ ^ 2) :=
      mul_le_mul hVZ hE_le (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
    nlinarith [h2]
  have hTerm2 : (n : ℝ) * ‖z - v‖ ^ 2 ≤ (n : ℝ) * C_D ^ 2 * ‖v‖ ^ 4 := by
    have h3 : ‖z - v‖ ^ 2 ≤ (C_D * ‖v‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE_le 2
    have h4 := mul_le_mul_of_nonneg_left h3 hN0
    nlinarith [h4]
  have hLHScomb : 2 * (n : ℝ) * (‖v‖ + ‖z‖) * ‖z - v‖ + (n : ℝ) * ‖z - v‖ ^ 2
      ≤ 5 * (n : ℝ) * C_D * ‖v‖ ^ 3 + (n : ℝ) * C_D ^ 2 * ‖v‖ ^ 4 := by linarith [hTerm1, hTerm2]
  have hRHScomb : 5 * (n : ℝ) * C_D * ‖v‖ ^ 3 + (n : ℝ) * C_D ^ 2 * ‖v‖ ^ 4 ≤ M * ‖v‖ ^ 3 := by
    rw [hMdef]; nlinarith [mul_le_mul_of_nonneg_left hV43 hNC2]
  -- `M·‖v‖ ≤ 1/16` from the `1/D` gate, whence `M·‖v‖³ ≤ ‖v‖²/16`.
  have hMV : M * ‖v‖ ≤ 1 / 16 := by
    have h1 : M * ‖v‖ ≤ M * (1 / D) := mul_le_mul_of_nonneg_left hvD hM0
    have h2 : M * (1 / D) ≤ 1 / 16 := by
      rw [mul_one_div, div_le_iff₀ hDpos, hDdef]; nlinarith [hM0]
    linarith [h1, h2]
  have hMV3 : M * ‖v‖ ^ 3 ≤ 1 / 16 * ‖v‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hMV (sq_nonneg ‖v‖); nlinarith [h]
  -- assemble.
  calc |rncRadialSq v - rncRadialSq z|
      ≤ 2 * (n : ℝ) * (‖v‖ + ‖z‖) * ‖z - v‖ + (n : ℝ) * ‖z - v‖ ^ 2 := rncRadialSq_abs_sub_le v z
    _ ≤ 5 * (n : ℝ) * C_D * ‖v‖ ^ 3 + (n : ℝ) * C_D ^ 2 * ‖v‖ ^ 4 := hLHScomb
    _ ≤ M * ‖v‖ ^ 3 := hRHScomb
    _ ≤ 1 / 16 * ‖v‖ ^ 2 := hMV3
    _ ≤ 1 / 4 * rncRadialSq z := by linarith [hrz_lb]

end QIQTH.HrawNearIsometryConcrete

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HrawNearIsometryConcrete.flowDisplacement_bound
#print axioms QIQTH.HrawNearIsometryConcrete.rncRadialSq_abs_sub_le
#print axioms QIQTH.HrawNearIsometryConcrete.nearIsometry_concrete
