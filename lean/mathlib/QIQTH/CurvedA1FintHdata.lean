/-
  CurvedA1FintHdata — J4-575: SOURCING the NEAR-ISOMETRY conjunct of the `hdata`-family for the
  genuinely-curved witness `g^K = curvedRNCMetric κ` (κ < 0), on its honest near-`0` domain.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## CONTEXT — the `hdata`-family.
  `curved_hFint_hFar_general` / `curved_hFint_hFirstEnv_at_gate` carry a per-`(i,τ,z)` geometric jet
  bundle `hdata`, a conjunction of FOUR conjuncts:
    (1) the inverse-chart first jet `HasDerivAt (fun r => uniformInverseChart … z (update 0 i r) k) …`,
    (2) the Jacobian-column bound `|Pval k| ≤ L`,
    (3) the amplitude value/derivative bounds `PdiffAt (chartFieldAmp …) i 0` ∧ `|A(0)| ≤ Ba`
        ∧ `|∂A(0)| ≤ Bd`,
    (4) the two-sided near-isometry `½·rncRadialSq z ≤ rncRadialSq (W₀ z)` (lower, hFar) and/or
        `rncRadialSq (W₀ z) ≤ 2·rncRadialSq z` (upper, hFirstEnv), `W₀ z := uniformInverseChart … z 0`.

  ## WHAT LANDS HERE (DERIVED axiom-free; NOT `a₁ = R/6`).
    • `curved_hdata_nearIsometry_at_gate` — ★★ conjunct (4) for `g^K`, BOTH sides at once, on the honest
      near-`0` gate `‖z‖ < r`:
          `(1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)  ∧  rncRadialSq (W₀ z) ≤ 2·rncRadialSq z`.
      DIRECTLY from the banked two-sided error `HeatResidualBound.chartW0_rncRadialSq_error`
      (`|rncRadialSq (W₀ z) − rncRadialSq z| ≤ L·‖z‖·rncRadialSq z`), instantiated at `curvedRNCMetric κ`
      / `curvedRNCInv κ`, shrinking the radius so `L·‖z‖ ≤ 1/2` (⟹ lower `≥ (1−½)·r² = ½·r²` and upper
      `≤ (1+½)·r² ≤ 2·r²`).  Both constants `½`, `2` are GENUINELY TRUE for the RNC chart of `g^K` — they
      are the honest slack of the near-identity displacement `W₀ z ≈ −z` (`chartW0_displacement`), NOT a
      shipped-false bound.
    • `curved_hdata_nearIsometry_at_gate_curved_satisfiable` — the CURVED (not-secretly-flat) gate:
      for `κ ≠ 0`, `n ≥ 2`, `Ric(0) = n(n−1)κ ≠ 0`, so the near-isometry is discharged at a genuinely
      curved witness (`curvedRNCMetric_ricci_trace_diag_ne`).

  ## PRECISE DEPTH VERDICT — what conjunct (4) does / does not discharge.
    • hFirstEnv (`curved_hFint_hFirstEnv_at_gate`) carries `hdata` ONLY on `‖z‖ < (curvedGate).r`, and uses
      the UPPER near-isometry `rncRadialSq (W₀ z) ≤ 2·rncRadialSq z`.  This lemma's domain and both bounds
      MATCH — the near-isometry conjunct of hFirstEnv's `hdata` is now BANKED (thin).
    • hFar (`curved_hFint_hFar_general`) carries `hdata` for ALL `z ∈ K` (annulus `‖z‖ ≥ r` included) and
      uses the LOWER near-isometry there.  The banked near-isometry is a NEAR-`0` fact — off the gate ball
      it is genuine NEW chart-jet geometry (indeed the whole-space `∀ z` form is FALSE, off-`K` collapse
      `wholeSpace_coercivity_unsatisfiable`).  So the FAR-FIELD lower coercivity for `z ∈ K`, `‖z‖ ≥ r`
      is the DEEP residual — this lemma sources ONLY the near-`0` portion of hFar's conjunct (4).
    • Conjuncts (1)/(2) (inverse-chart first jet + `|Pval| ≤ L`) and (3) (uniform amplitude bounds
      `Ba`/`Bd`) remain owed: `PdiffAt (chartFieldAmp …) i 0` is banked pointwise
      (`AmplitudeFamilyDischarge.amp_pdiffAt_center`) but the UNIFORM-over-`K∩ball` constants `Ba`/`Bd`/`L`
      need a compactness uniformization step (medium depth, not built here).

  ⚠  a₁ = R/6 remains CONDITIONAL.  Sourcing conjunct (4) near `0` does NOT make it unconditional — the
  far-field lower coercivity, conjuncts (1)/(2)/(3), `hsrc`, `hOffCollarTail`, the convergence trio, and
  `hInnerCont` all remain owed.
-/
import QIQTH.CurvedA1FintHFarSource
import QIQTH.InverseChartDisplacement

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness
open scoped Topology BigOperators

namespace QIQTH.CurvedA1FintHdata

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### THE NEAR-ISOMETRY conjunct (4) of the `hdata`-family for `g^K`, near `0`.
    ############################################################################### -/

/-- **★★ J4-575 — `curved_hdata_nearIsometry_at_gate`.**  The two-sided near-isometry conjunct (4) of
    the `hdata`-family for the genuinely-curved witness `g^K = curvedRNCMetric κ`, on its honest near-`0`
    gate `‖z‖ < r`:
        `(1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)  ∧  rncRadialSq (W₀ z) ≤ 2·rncRadialSq z`,
    `W₀ z := uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0`.  DERIVED from the
    banked two-sided error `chartW0_rncRadialSq_error` (`|rncRadialSq (W₀ z) − rncRadialSq z| ≤
    L·‖z‖·rncRadialSq z`), shrinking the radius so `L·‖z‖ ≤ 1/2`.  Both constants `½`, `2` are genuinely
    true for the RNC chart (the near-identity displacement `W₀ z ≈ −z`).  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_nearIsometry_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ z ∈ K, ‖z‖ < r →
      (1 / 2 : ℝ) * rncRadialSq z
          ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
      ∧ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
          ≤ 2 * rncRadialSq z := by
  obtain ⟨r₀, hr₀, L, hL0, hbd⟩ :=
    chartW0_rncRadialSq_error (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
  refine ⟨min r₀ (1 / (2 * (L + 1))), lt_min hr₀ (by positivity), ?_⟩
  intro z hzK hzr
  have hzr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzL : ‖z‖ < 1 / (2 * (L + 1)) := lt_of_lt_of_le hzr (min_le_right _ _)
  obtain ⟨hlow, hup⟩ := hbd z hzK hzr₀
  have hnn : (0 : ℝ) ≤ rncRadialSq z := rncRadialSq_nonneg z
  -- `L·‖z‖ ≤ 1/2` on the shrunk gate.
  have hLz : L * ‖z‖ ≤ 1 / 2 := by
    have hstep : L * ‖z‖ ≤ L * (1 / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hzL.le hL0
    have hbound : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith [hL0] : (0 : ℝ) < 2 * (L + 1))]
      nlinarith [hL0]
    linarith
  -- the error term `L·‖z‖·rncRadialSq z ≤ ½·rncRadialSq z`.
  have hprod : L * ‖z‖ * rncRadialSq z ≤ (1 / 2 : ℝ) * rncRadialSq z :=
    mul_le_mul_of_nonneg_right hLz hnn
  refine ⟨?_, ?_⟩
  · -- lower: `rncRadialSq z − L‖z‖·r² ≤ W₀`, and `rncRadialSq z − ½·r² = ½·r²`.
    linarith [hlow, hprod]
  · -- upper: `W₀ ≤ rncRadialSq z + L‖z‖·r² ≤ (3/2)·r² ≤ 2·r²`.
    linarith [hup, hprod, hnn]

/-! ###############################################################################
    ### the CURVED (not-secretly-flat) satisfiability GATE.
    ############################################################################### -/

/-- **★ J4-575 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the near-isometry
    conjunct is discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.  The
    two-sided near-isometry is the honest slack of the near-identity RNC chart — it holds WITH `Ric ≠ 0`,
    not a flatness statement.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_nearIsometry_at_gate_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintHdata

section AxiomChecks
open QIQTH.CurvedA1FintHdata
#print axioms curved_hdata_nearIsometry_at_gate
#print axioms curved_hdata_nearIsometry_at_gate_curved_satisfiable
end AxiomChecks
