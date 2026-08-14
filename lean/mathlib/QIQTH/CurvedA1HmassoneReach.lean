/-
  CurvedA1HmassoneReach — J4-738: UNIFYING the mass-side pre-ρ carriers of
  `CurvedA1HmassoneFinal.curved_hmassone_final_at_gate` around ONE geometric input — the
  origin-REACH of the flow-exp.  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT
  `a₁ = R/6`; proves NOTHING about the coefficient value.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-591 (`curved_hmassone_final_at_gate`) reduced the center-gauge curved capstone's
  base-mass limit `hmassone` to FIVE pre-`ρ` carriers `{rS, hKball, hSact, hWslice, hDom}`:
    • `rS`/`hKball` : a ball `ball 0 rS ⊆ K`;
    • `hSact`       : the gate is ACTIVE at the origin — `0 ∈ constGate … c z` for `z ∈ ball 0 rS`;
    • `hWslice`     : per-`τ` witness-slice measurability;
    • `hDom`        : the zeroth Gaussian domination.

  ── ★★ THE FINDING (J4-738).  Three of these four are the SAME geometric fact.  The gate
     `constGate g gi hChr hK c z = uniformFlowExp g gi hChr hK z '' ball 0 c` is the flow-ball
     image, so
        `0 ∈ constGate … c z  ↔  ∃ v, ‖v‖ < c ∧ uniformFlowExp … z v = 0`   (`constGate_zero_mem_iff_reach`)
     — i.e. `hSact` IS the origin-REACH at gate radius `c`.  And the witness-slice measurability
     `hWslice` is discharged CARRY-FREE by the banked `CurvedRNCChartReach.curvedRNC_hWslice_carryFree`
     from the SAME origin-reach (at the produced radius `ρW`), with ZERO residual measurability
     sub-carry.  Composing: `curved_hmassone_final_from_reach` produces the EXACT `hmassone` limit
     of `curved_hmassone_final_at_gate` with `hSact` and `hWslice` REPLACED by the single geometric
     origin-reach input (stated at the two radii `ρW` — for the measurability discharge — and `c`
     — for the gate activation; both instances of ONE satisfiable reach fact), the trivially-fat
     `rS`/`hKball`, and the still-carried Gaussian domination `hDom`.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `constGate_zero_mem_iff_reach` — the gate-activation ↔ origin-reach bridge (pure
      `Set.mem_image` + `Metric.mem_ball` unfold of `constGate`).
    • `curved_hmassone_final_from_reach` — ★★ the carrier-unified `hmassone`: the base-mass limit
      with the measurability+gate-activation carriers `{hSact, hWslice}` discharged from the single
      origin-reach input.  The only remaining pre-`ρ` carriers are the trivially-satisfiable
      `rS`/`hKball` and the Gaussian domination `hDom` — plus `κ < 0` (fat, genuinely curved base).
    • `curved_hmassone_reach_satisfiable` — the NON-VACUITY certificate (re-export): the curved
      base is genuinely curved (`∃ w, 1 < det g^κ w`), so the reduction is NOT the flat kernel and
      NOT a `K = {0}` collapse.

  ── HONEST RESIDUAL.  This CONTRACTS the mass-side carrier surface from five heterogeneous carriers
     to the single geometric origin-REACH input (`∀ z ∈ K, ∃ v small, φ_z v = 0` — the K-uniform
     injectivity-radius reachability, the `ExpRhoReachability`-family GENUINE input carried
     throughout the curved chain, e.g. in the banked `CurvedA1ReBase.rebased_hmeas_at_gate`) plus the
     Gaussian domination `hDom` and the fat curved base.  None of these is the `a₁` conclusion.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  This is a carrier-bookkeeping
  brick: it re-expresses WHICH satisfiable geometric input the curved `hmassone` rests on, unifying
  the reach-family carriers; it establishes nothing new about the coefficient.  No `sorry`, no new
  axioms, no `:= True`, no vacuous / conclusion-in-disguise hypothesis, no existing file edited,
  nothing committed.
-/
import Mathlib
import QIQTH.CurvedA1HmassoneFinal
import QIQTH.CurvedRNCChartReach

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ChartImageAIConcrete QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.RadialDistance QIQTH.ExpMap
open scoped Topology

namespace QIQTH.CurvedA1HmassoneReach

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The gate-activation ↔ origin-reach bridge. -/

/-- **`constGate_zero_mem_iff_reach` — the gate is active at the origin iff the origin is reachable.**
    Since `constGate g gi hChr hK c z = uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`, the
    origin lies in the gate iff some velocity `v` with `‖v‖ < c` flows to it:
        `0 ∈ constGate g gi hChr hK c z  ↔  ∃ v, ‖v‖ < c ∧ uniformFlowExp g gi hChr hK z v = 0`.
    Pure `Set.mem_image` + `Metric.mem_ball` unfold.  NOT `a₁ = R/6`. -/
theorem constGate_zero_mem_iff_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) (z : Point n) :
    (0 : Point n) ∈ constGate g gi hChr hK c z
      ↔ ∃ v : Point n, ‖v‖ < c ∧ uniformFlowExp g gi hChr hK z v = 0 := by
  simp only [constGate, Set.mem_image, Metric.mem_ball, dist_zero_right]

/-! ### ★★ The carrier-unified base-mass limit. -/

/-- **★★ `curved_hmassone_final_from_reach` — the curved `hmassone` with `{hSact, hWslice}`
    discharged from a single origin-REACH input.**  Produces the EXACT base-mass limit of
    `CurvedA1HmassoneFinal.curved_hmassone_final_at_gate`, but with the gate-activation carrier
    `hSact` supplied from the origin-reach at gate radius `c` (via `constGate_zero_mem_iff_reach`)
    and the witness-slice measurability `hWslice` discharged CARRY-FREE from the origin-reach at the
    produced radius `ρW` (via the banked `CurvedRNCChartReach.curvedRNC_hWslice_carryFree`).

    The only remaining pre-`ρ` carriers are the trivially-fat `rS`/`hKball` (`ball 0 rS ⊆ K`) and the
    zeroth Gaussian domination `hDom` — plus `κ < 0` (the fat, genuinely curved base).  The two
    reach antecedents (at `ρW` and at `c`) are the SAME satisfiable geometric fact (K-uniform
    injectivity-radius reachability of the origin) at two radii.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hmassone_final_from_reach (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ρW > (0 : ℝ),
      (∀ z ∈ K, ∃ v : Point n, ‖v‖ < ρW ∧
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z v = 0) →
      ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
        (∀ z ∈ K, ∃ v : Point n, ‖v‖ < c ∧
          uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z v = 0) →
        ∀ rS : ℝ, 0 < rS → Metric.ball (0 : Point n) rS ⊆ K →
        ∀ lam τ₀ CW : ℝ, 0 < lam → 0 < τ₀ → 0 ≤ CW →
        (∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
          |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z|
            ≤ CW * gaussDdim (lam * τ) z) →
        ∃ ρ > (0 : ℝ),
          Tendsto (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
              (epsSeq m) (0 : Point n) z) atTop (𝓝 1) := by
  obtain ⟨ρW, hρW, hWimpl⟩ :=
    QIQTH.CurvedRNCChartReach.curvedRNC_hWslice_carryFree κ hκ hChr hK a b
  refine ⟨ρW, hρW, fun hReachW => ?_⟩
  obtain ⟨δ₀, hδ₀, hWslice⟩ := hWimpl hReachW
  refine ⟨δ₀, hδ₀, fun c hc hcδ hReachC rS hrS hKball lam τ₀ CW hlam hτ₀ hCW hDom => ?_⟩
  -- discharge `hSact` from the origin-reach at radius `c`.
  have hSact : ∀ z ∈ Metric.ball (0 : Point n) rS,
      (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z := by
    intro z hz
    exact (constGate_zero_mem_iff_reach _ _ hChr hK c z).mpr (hReachC z (hKball hz))
  exact QIQTH.CurvedA1HmassoneFinal.curved_hmassone_final_at_gate κ hκ.le hChr hK h0Kmem
    a b c ha hab rS hrS hKball hSact (hWslice c hc hcδ)
    lam τ₀ CW hlam hτ₀ hCW hDom

/-! ### Non-vacuity: the curved base is genuinely curved (re-export). -/

/-- **`curved_hmassone_reach_satisfiable` — the NON-VACUITY certificate.**  For `κ < 0`, `n ≥ 2`
    the curved base is GENUINELY curved (`∃ w, 1 < det g^κ w`), so the carrier-unified reduction is
    NOT secretly the flat kernel and NOT a `K = {0}` collapse.  Re-exports the banked certificate.
    NOT `a₁ = R/6`. -/
theorem curved_hmassone_reach_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    Matrix.det (curvedRNCMetric κ (0 : Point n)) = 1
      ∧ ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  QIQTH.CurvedA1HmassoneFinal.curved_hmassone_final_curved_satisfiable κ hκ hn

end QIQTH.CurvedA1HmassoneReach

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HmassoneReach

#print axioms constGate_zero_mem_iff_reach
#print axioms curved_hmassone_final_from_reach
#print axioms curved_hmassone_reach_satisfiable

end AxiomChecks
