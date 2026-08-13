/-
  CurvedHDConvSlotThreading — J4-679: thread the W1-FREE `hDConv_AT_GATE` path at the CURVED witness by
  CERTIFYING, at the exact `constGate` gauge the capstone consumes, the two GEOMETRY-CLOSED slots of
  `QIQTH.HDConvGateThreading.hDConv_AT_GATE`: the width-3/2 `hEdom` (from the closed width campaign
  J4-672…677) and the RNC gauge triple `hgi`/`hΓ` (from the center-only curved gauge).  ONE census
  brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about `R/6` (R/6
  stays a labelled carrier; the analytic arrow census stays owed).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — A CENSUS CERTIFICATE, NOTHING ELSE.  This file does NOT discharge the `hDConv`
  ARROW of `CurvedCapstoneHCHInterFed.curved_wide_a1_R6_trunc_hIntCHInterFed`.  It certifies that TWO
  of `hDConv_AT_GATE`'s ~50 hypotheses — the width-3/2 `hEdom` (the sole census family the width
  campaign closed) and the RNC gauge pair `MemGaugeGi`/`MemGaugeGamma` — are GEOMETRY-CLOSED at the
  curved witness (`g^K = curvedRNCMetric κ`, `κ < 0`, seed `K = {0}`), at the SAME `constGate … c`
  gauge the capstone's `cW` gate uses, from ONLY the standing smoothness carries `hChr`+`hw`.

  ── WHY THIS IS NOT THE FULL `hDConv` DISCHARGE (the two threading walls, documented honestly).
     (W-census)  `hDConv_AT_GATE` carries ~40 further ANALYTIC census members with NO curved geometry
        supplier: the DaLimLU differentiation-under-∫∫ families (`hQ1`/`hFmeas`/`hFint`/`hF'meas`/
        `hbdd`/`hbound`/`hdiff`/`hbnd`), `MemLapFull`/`MemAdjLo`/`MemAdjHi`/`MemECombine`,
        `hIlo`/`hIhi`, the F2 pile (`hMeasFII`/`hInnerCont`/`hnb`/`hFmeas_d`/…/`hpardiff`/`hCross`),
        and the frozen/moving boundary list for `hbdryLU_CONCRETE` (`hWmeas`/`hffro_*`/`hfmov_*`/
        `hWDom`/`hmass`/`hmassone`/`hmod`/`hsup`).  These are the J4-677-ledger "still owed for the
        arrows" census; feeding `hDConv` would REPLACE the single `DifferentiableAt` arrow with this
        ~40-member labelled bundle — a LONGER carry list, not a shorter one.
     (W-width/gate)  The capstone's other arrows (`hInt`/`hInter`/`hEboundW_le`) live at the WIDTH-2
        gate produced by `curvedRNC_heatOp_dom_pkg` (its own `∃ (a,b,c)`), whereas `hDConv_AT_GATE`'s
        `hEdom` requires WIDTH-3/2, produced by `curvedRNC_hEdom_width32_from_geometry` at ITS OWN
        `∃ (a,b,c)`.  Width-3/2 does not dominate width-2 (the campaign's absorption is one-directional
        `4/3 < 3/2 ≤ 2` on the supplier side, not a bound conversion), so no single `∃`-chosen gate
        carries both — the two suppliers cannot be unified onto the capstone's `cW` gate as-is.
     ⟹ threading `hDConv` INTO `curved_wide_a1_R6_trunc_hIntCHInterFed` is BLOCKED on (W-census) +
        (W-width/gate); this file lands the geometry-closable fraction as an honest certificate.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses, no existing file edited.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CurvedHgateGlue
import QIQTH.CurvedA1FrameAudit
import QIQTH.CurvedRNCBaseWitnessDomAdom
import QIQTH.A1R6CoreAtGate

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.DaLimLUWallRecon
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.CurvedHDConvSlotThreading

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The two geometry-closed `hDConv_AT_GATE` slots at the curved `constGate` gauge.
    ############################################################################### -/

/-- **★★★ J4-679 — `curvedHDConv_fed_slots_at_constGate`.**  The TWO geometry-closed hypothesis slots
    of `QIQTH.HDConvGateThreading.hDConv_AT_GATE`, certified at the curved witness
    (`g^K = curvedRNCMetric κ`, `κ < 0`, seed `K = {0}`) at the SAME `constGate … c` gauge the
    capstone's `cW` gate uses, from ONLY the standing smoothness carries `hChr`+`hw`:

      • the RNC gauge pair `hgi = MemGaugeGi (curvedRNCInv κ)` and
        `hΓ = MemGaugeGamma (curvedRNCMetric κ) (curvedRNCInv κ)` — via the center-only curved gauge
        `CurvedA1FrameAudit.curved_gauge_from_center` (no `hframeK`);
      • the width-3/2 `hEdom` slot (on `heatOp g^K gi^K H_G`) — the EXACT `hDConv_AT_GATE` `hEdom`
        shape at `constGate` — via the closed width campaign
        `CurvedHgateGlue.curvedRNC_hEdom_width32_from_geometry` (gate rewritten from the inline
        flow-ball form to `constGate`, definitionally equal);
      • the width-3/2 `hAdom` slot (on the WITNESS `vanVleckGatedWitness` itself) — via
        `CurvedRNCBaseWitnessDomAdom.curvedRNC_baseWitness_dom_adom` — at its OWN ∃-gate (each width
        supplier chooses its own flow-ball radius; NO common-gate claim is made across B and C).

    ⚠ THIS IS NOT the `hDConv` arrow discharge — the remaining ~40 analytic census members of
    `hDConv_AT_GATE` (DaLimLU diff-under-∫∫ families, `MemLapFull`/`MemAdj*`/`MemECombine`, F2 pile,
    frozen/moving boundary list) have no curved supplier, and the width-2 vs width-3/2 gate suppliers
    do not unify (file header, walls W-census + W-width/gate).  ⚠ NOT `a₁ = R/6`. -/
theorem curvedHDConv_fed_slots_at_constGate (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ)) :
    -- (fed slot A) the RNC gauge pair `hgi`/`hΓ`:
    (MemGaugeGi (n := n) (curvedRNCInv κ)
      ∧ MemGaugeGamma (n := n) (curvedRNCMetric κ) (curvedRNCInv κ))
    -- (fed slot B) the width-3/2 `hEdom` slot (on `heatOp g^K gi^K H_G`) at the `constGate` gauge:
    ∧ (∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
        ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
          |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
                (QIQTH.A1R6CoreAtGate.constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b) τ p q|
            ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    -- (fed slot C) the width-3/2 `hAdom` slot (on the WITNESS itself) — at its OWN ∃-gate
    -- (independent of slot B's gate; each supplier chooses its own flow-ball radius):
    ∧ (∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∃ c > (0 : ℝ), ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
          |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
              (QIQTH.A1R6CoreAtGate.constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) 1 2 τ p q|
            ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) := by
  refine ⟨QIQTH.CurvedA1FrameAudit.curved_gauge_from_center κ hκ, ?_, ?_⟩
  · -- fed slot B: the width-3/2 `hEdom`.
    obtain ⟨a, b, c, ha, hab, hbc, E₀, E₁, hE₀, hE₁, hEdom⟩ :=
      QIQTH.CurvedHgateGlue.curvedRNC_hEdom_width32_from_geometry κ hκ hChr hw
    refine ⟨a, b, c, ha, hab, hbc, E₀, E₁, hE₀, hE₁, ?_⟩
    -- `constGate … c` is definitionally the inline flow-ball gate `width32` produced its bound for.
    simpa only [QIQTH.A1R6CoreAtGate.constGate] using hEdom
  · -- fed slot C: the width-3/2 `hAdom` on the witness, at radii `1 < 2`, window cap `τ0fr = 1`.
    obtain ⟨A₀, A₁, hA₀, hA₁, c, hc, CW, lam, _hCW, _hlam, hAdom, _hWDom⟩ :=
      QIQTH.CurvedRNCBaseWitnessDomAdom.curvedRNC_baseWitness_dom_adom κ hκ hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
        (1 : ℝ) (2 : ℝ) (by norm_num) (by norm_num) (1 : ℝ) (by norm_num) hw
    exact ⟨A₀, A₁, hA₀, hA₁, c, hc, hAdom⟩

/-! ###############################################################################
    ### NON-VACUITY — the fed slots live at a GENUINELY-CURVED witness (`κ ≠ 0`, `n ≥ 2`).
    ############################################################################### -/

/-- **★ J4-679 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The witness underlying
    `curvedHDConv_fed_slots_at_constGate` is genuinely curved: for `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `curvedRNCMetric κ` is nonzero.  So the fed gauge/`hEdom` slots
    are certified at a genuinely curved metric (`κ = −1`, `n = 2`), not the flat `δ`.  NOT `a₁ = R/6`. -/
theorem curvedHDConv_fed_slots_at_constGate_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  QIQTH.CurvedRNCGaussWitness.curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedHDConvSlotThreading

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CurvedHDConvSlotThreading
#print axioms curvedHDConv_fed_slots_at_constGate
#print axioms curvedHDConv_fed_slots_at_constGate_curved_satisfiable
end AxiomChecks
