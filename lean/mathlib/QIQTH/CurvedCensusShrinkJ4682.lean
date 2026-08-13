/-
  CurvedCensusShrinkJ4682 — J4-682: POST-UNIFICATION W-CENSUS RE-INVENTORY + tractable discharges.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE DOES (census bookkeeping only — NOT `a₁ = R/6`).

  The J4-679…681 unified-gate capstone (`CurvedCapstoneUnifiedGate.curved_wide_a1_R6_trunc_unifiedGate`)
  leaves the three Duhamel arrows (`hDuhamel`/`hDConv`/`hCConv`) as inner hypotheses whose discharge
  routes reduce to the ~40-member W-census carried by `HDConvGateThreading.hDConv_AT_GATE`.  This file
  RE-INVENTORIES that census against the banked width/gate machinery at the unified gate and LANDS the
  tractable members as a single geometry-closed certificate, at the SAME `constGate … c` gauge the
  capstone's `cW` gate consumes, from ONLY the standing smoothness carries `hChr`/`hw`/`hu`.

  ── THE THREE TIERS, RE-INVENTORIED (verdicts proved / recorded below).
     (T-CLOSED)  fully geometry-closed on standing carries — CERTIFIED here in one conjunction:
        • the RNC gauge pair `hgi = MemGaugeGi`, `hΓ = MemGaugeGamma`
            (via `CurvedA1FrameAudit.curved_gauge_from_center`, center-only gauge, no `hframeK`);
        • the DaLimLU inner-continuity slot `hInnerCont`
            (via `CurvedA1Hmeas.curved_hInnerCont_closed` — takes ONLY `hChr`/`hw`/`hu`);
        • the Levi tail-vanishing `hFzero` (via `DaLimEasyTranche.hFzero_concrete`).

     (T-DEGEN)  ⚠ THE HONEST STRUCTURAL FINDING.  `hInnerCont` (and the sibling measurability members
        `hMeasFII`/`hWmeas`/`hffro_meas`/`hfmov_meas`/`hFmeas`/`hFint`) close CHEAPLY at the seed
        `K = {0}` because the singleton gate kills the witness z-slice off the origin
        (`CurvedA1Hmeas.curved_gatedWitness_offOrigin_zero`): `z ↦ W τ 0 z` is `0` for every `z ≠ 0`,
        hence a.e.-`0`, so every inner pairing `∫ z, W(u−s) 0 z · L s z 0` is a.e. the constant `0`.
        This is a DEGENERACY, not analytic strength: the SAME null-supported slice that makes the
        measurability tier trivial makes `∫ z, W(εₘ) 0 z → 0 ≠ 1`, i.e. it BLOCKS `hmassone`.

     (T-BLOCKED-cp466)  `hmassone`/`hmass` are NOT dischargeable at `K = {0}`.  We RE-EXPORT the proof:
        `CurvedA1Hmassone.curved_hmassone_gate_forces_nontrivial_K` shows the gate-activation antecedent
        (`ball 0 ρ ⊆ K` ∧ gate active on the ball) FORCES `∃ z ∈ K, z ≠ 0` — jointly UNSATISFIABLE at
        `K = {0}` (the cp466 trap: `hframeK ≡ δ-on-K` forces `K = {0}` ⟹ K-gated `∫ z = 0` ⟹ `hmassone`
        can't `→ 1`).  So `hmassone` stays OWED and requires a CENTER-ONLY mass-one reformulation
        (not the gate-forced form), exactly as the mass tier of the census.

     (T-REDUCED)  the remaining T1 measurability/integrability members (`hFint(+_d)`/`hFmeas(+_d)`/
        `hF'meas(+_d)`/`hMeasFII`/`hWmeas`/`hffro_meas`/`hfmov_meas`/`hII_hi`) each have a curved
        `_at_gate` supplier whose sub-data reduces to {width-fed Gaussian dominations `hEdom`/`hAdom`/
        `hWDom` (now ✓ at the unified gate)} + {joint strip continuity of
        `witnessFieldDeriv`/`leviSeries`}, and the latter reduces to the chart-IFT bundle
        (`UngatedChainRule.witnessFieldDeriv_jointContinuousOn`: `hunit`/`hmaps`/`hWdiff`/`hIFT`/`hGate`)
        — STILL OWED.  So this tier is one interface (chart continuity) away from closing, not yet closed.

     (T-NOSUPPLIER)  genuinely analytic, no curved supplier: `hQ1`, `hbdd`/`hbound`/`hdiff`/`hbnd`,
        `MemLapFull`/`MemAdjLo`/`MemECombine`, `hIlo`/`hIhi`, `hFdom`, `hCross`/`L`, `hpardiff`,
        `hnb`/`hbdd_d`/`hbound_d`, `hmod`/`hsup`, plus the hDuhamel-route `dataLevi`/`dataAmp`/`hPd2conv`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — A CENSUS CERTIFICATE, NOTHING ELSE.  This file discharges NO arrow of the
  capstone, closes NOTHING of the `R/6` coefficient extraction, and adds NO analysis.  It (i) certifies
  the T-CLOSED members in one conjunction, and (ii) re-exports the cp466 block on `hmassone`.  R/6 stays
  a labelled carrier; the arrows and the T-REDUCED / T-NOSUPPLIER census stay owed.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses, no existing file edited.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CurvedA1Hmeas
import QIQTH.CurvedA1FrameAudit
import QIQTH.CurvedA1Hmassone
import QIQTH.DaLimEasyTranche

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.A1R6CoreAtGate
open QIQTH.DaLimLUWallRecon
open scoped BigOperators ContDiff Topology

namespace QIQTH.CurvedCensusShrinkJ4682

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (T-CLOSED) — the geometry-closed census members in ONE conjunction.
    ############################################################################### -/

/-- **★★★ J4-682 — `curved_census_closed_bundle`.**  The W-census members that are FULLY
    geometry-closed on the standing carries, certified together at the curved witness
    (`g^K = curvedRNCMetric κ`, `κ < 0`, seed `K = {0}`), at the SAME `constGate … c` gauge the
    capstone's `cW` gate uses, from ONLY `hChr`/`hw`/`hu`:

      • the RNC gauge pair `MemGaugeGi`/`MemGaugeGamma` (center-only gauge, no `hframeK`);
      • the Levi tail-vanishing `hFzero` (at every gate parameter);
      • the DaLimLU inner-continuity `hInnerCont` on its own ∃-gate.

    ⚠ `hInnerCont` here closes CHEAPLY via the singleton-gate degeneracy (the witness z-slice is
    a.e.-`0` off the origin — `curved_gatedWitness_offOrigin_zero`); the same degeneracy blocks
    `hmassone` (see `curved_census_hmassone_blocked`).  ⚠ NOT `a₁ = R/6`. -/
theorem curved_census_closed_bundle (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k))
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T) :
    -- (T-CLOSED slot A) the RNC gauge pair:
    (MemGaugeGi (n := n) (curvedRNCInv κ)
      ∧ MemGaugeGamma (n := n) (curvedRNCMetric κ) (curvedRNCInv κ))
    -- (T-CLOSED slot B) `hFzero` (Levi tail vanishes for nonpositive time) at every gate parameter:
    ∧ (∀ c a b : ℝ, ∀ s : ℝ, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)) s z y = 0)
    -- (T-CLOSED slot C) the DaLimLU inner-continuity `hInnerCont` on its own ∃-gate:
    ∧ (∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
        ∀ u ∈ U, ContinuousOn
          (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
              (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                    ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
                  a b)) s z 0)
          (Set.Ioo 0 u)) := by
  refine ⟨QIQTH.CurvedA1FrameAudit.curved_gauge_from_center κ hκ, ?_, ?_⟩
  · -- (slot B) `hFzero` — the Levi series vanishes for nonpositive time (structural).
    intro c a b s hs z y
    exact QIQTH.DaLimEasyTranche.hFzero_concrete (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b hn s hs z y
  · -- (slot C) `hInnerCont` — fully geometry-closed from the standing carries.
    exact QIQTH.CurvedA1Hmeas.curved_hInnerCont_closed κ hκ hn hChr hw hu T hT U hUT

/-! ###############################################################################
    ### (T-BLOCKED-cp466) — the `hmassone` block, RE-EXPORTED.
    ############################################################################### -/

/-- **★★ J4-682 — `curved_census_hmassone_blocked`.**  The census verdict that `hmassone` is NOT a
    tractable discharge at the seed `K = {0}`.  Its gate-activation antecedent — a radius `ρ > 0` with
    the ball `Metric.ball 0 ρ ⊆ K` on which the gate is active — FORCES `K` to contain a point `≠ 0`,
    which is impossible for `K = {0}`.  Hence `hmassone` stays OWED (needs a center-only mass-one
    reformulation, not the gate-forced form).  This RE-EXPORTS
    `CurvedA1Hmassone.curved_hmassone_gate_forces_nontrivial_K`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_census_hmassone_blocked (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hGgate : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      z ∈ K ∧ (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z) :
    ∃ z : Point n, z ∈ K ∧ z ≠ (0 : Point n) :=
  QIQTH.CurvedA1Hmassone.curved_hmassone_gate_forces_nontrivial_K κ hChr hK c ρ hρ hn hGgate

/-- Corollary: at the seed `K = {0}` the `hmassone` gate-activation antecedent is UNSATISFIABLE. -/
theorem curved_census_hmassone_blocked_at_singleton (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (c : ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hGgate : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      z ∈ ({(0 : Point n)} : Set (Point n))
        ∧ (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c z) :
    False := by
  obtain ⟨z, hzK, hz0⟩ := curved_census_hmassone_blocked κ hChr
    (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c ρ hρ hn hGgate
  exact hz0 (by simpa using hzK)

/-! ###############################################################################
    ### NON-VACUITY — the certificate lives at a GENUINELY-CURVED witness (`κ ≠ 0`, `n ≥ 2`).
    ############################################################################### -/

/-- **★ J4-682 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The witness underlying
    `curved_census_closed_bundle` is genuinely curved: for `κ ≠ 0`, `n ≥ 2` the diagonal metric-Hessian
    trace (`Ric(0)`) of `curvedRNCMetric κ` is nonzero.  NOT `a₁ = R/6`. -/
theorem curved_census_closed_bundle_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  QIQTH.CurvedRNCGaussWitness.curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedCensusShrinkJ4682

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CurvedCensusShrinkJ4682
#print axioms curved_census_closed_bundle
#print axioms curved_census_hmassone_blocked
#print axioms curved_census_hmassone_blocked_at_singleton
#print axioms curved_census_closed_bundle_curved_satisfiable
end AxiomChecks
