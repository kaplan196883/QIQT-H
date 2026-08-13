/-
  WhiteHInnerContLegADischarged — J4-714 (Route (β) BRICK 5, rethread): `hlegA` OFF THE LIST.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE VERDICT.  `WhiteHInnerContGeomClosed.white_hInnerCont_closed_final` (banked 3ed249ca) carries
     `hlegA` — the leg-(a) reparam-kernel-factor `ContinuousWithinAt` family — as a LABELLED
     hypothesis.  This file DISCHARGES it: `white_hlegA_of_reach` (J4-714,
     `WhiteHlegADischarge.lean`) builds `hlegA` from the LOCALITY / REACH certificate
     `{hn, hagree, hSopen, hSreach, hspec germ, radii c < δ₀}`, and this file feeds that into the
     banked final, so the composed continuity carries the certificate list with `hlegA` REPLACED by
     the discharge cert.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `white_hInnerCont_closed_final2` — ★★★ the composed whitened inner-pairing interior-time
      continuity with `htermBox` DISCHARGED through the `hInterior`-free tie AND `hlegA` DISCHARGED
      through the reach substrate — carrying the certificate list with `hlegA` GONE (replaced by
      `{Wg, hagree, c, δ₀, hcδ, hSopen, hSreach, hspec}`).

  ── HONEST RESIDUAL — THE FINAL CERTIFICATE LIST AFTER THE `hlegA` DISCHARGE (NOT the conclusion,
     NOT `a₁ = R/6`; `hInterior` GONE, `hlegA` GONE):
    A. co-instantiated at the shared gate: `C, hC0, hpkg, hEmeas, hWmeas, (wA, Cpre, A₀, A₁), hval`.
    B. the FINAL certificates: `hnull` (null-frontier), `hbase` (`k = 0` raw-kernel seed), and the
       `hlegA` DISCHARGE cert `{Wg, hagree, c, δ₀, hcδ, hSopen, hSreach, hspec germ}` — at the
       CONCRETE flow-ball gate this cert is BANKED (`whiteChart_rep_concrete` +
       `uniformInverseChart_huniformChart`; reach is the identity `S w = flowBall_w(c)`).
    C. window: `Uwin`, `hU1`.

  ⚠  HONEST FIREWALL.  `hlegA` discharge rethread ONLY.  THIS FILE IS **NOT** `a₁ = R/6` and proves
  NOTHING about `R/6`.  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
  existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.
-/
import Mathlib
import QIQTH.WhiteHInnerContGeomClosed
import QIQTH.WhiteHlegADischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz QIQTH.HeatResidualBound
open QIQTH.PullbackMetric QIQTH.ExpMap
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.CurvedA1CenterAmp
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteAnnulus
open QIQTH.WhiteBridge QIQTH.WhiteS1C
open QIQTH.LeviSeries
open QIQTH.GaussianWidthTolerant
open QIQTH.WhiteHInnerContGeomClosed QIQTH.WhiteHlegADischarge
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteHInnerContLegADischarged

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `white_hInnerCont_closed_final2` — `hlegA` DISCHARGED.**  Same conclusion as
    `WhiteHInnerContGeomClosed.white_hInnerCont_closed_final`, but `hlegA` is no longer a hypothesis:
    it is BUILT in-line from the reach discharge `white_hlegA_of_reach` fed the LOCALITY / REACH
    certificate `{Wg, hagree, c, δ₀, hcδ, hSopen, hSreach, hspec germ}`.  ⚠ CONDITIONAL on the
    certificate list (file header A/B/C).  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final2 (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    -- A. co-instantiated width-`whiteLam` pkg / S1 / value data
    (C : ℝ) (hC0 : 0 ≤ C)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW (whiteLam κ hκ hKc) 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    (hWmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      whiteGatedWitness κ hκ hKc S a b w.1 w.2.1 w.2.2))
    (wA Cpre A₀ A₁ : ℝ) (hwA0 : 0 < wA) (hCpre0 : 0 ≤ Cpre) (hA₀0 : 0 ≤ A₀) (hA₁0 : 0 ≤ A₁)
    (hval : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |whiteGatedWitness κ hκ hKc S a b τ p q|
        ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q))
    -- B. the null-frontier cert + the `k = 0` seed
    (hnull : ∀ z₀ : Point n, volume {w : Point n | z₀ ∈ frontier (S w)} = 0)
    (hbase : ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      ContinuousOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R'))
    -- B'. the `hlegA` DISCHARGE cert (replaces the leg-(a) family) — reach substrate inputs
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (c δ₀ : ℝ) (hcδ : c < δ₀)
    (hSopen : ∀ w : Point n, w ∈ Kset → IsOpen (S w))
    (hSreach : ∀ w : Point n, w ∈ Kset →
        S w ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w ''
          Metric.ball (0 : Point n) c)
    (hspec : ∀ w : Point n, w ∈ Kset →
        (∀ v : Point n, ‖v‖ < δ₀ →
          (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc w z)) =ᶠ[nhds v] (fun z => z) ∧
          ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w)
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v)))
    -- C. window
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) := by
  -- DISCHARGE `hlegA` from the reach substrate.
  have hlegA := white_hlegA_of_reach hn κ hκ hKc S a b Wg hagree c δ₀ hcδ hSopen hSreach hspec
  -- feed the banked `hInterior`-free / `hlegA`-carrying final.
  exact white_hInnerCont_closed_final κ hκ hKc S a b C hC0 hpkg hEmeas hWmeas
    wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval hnull hlegA hbase Uwin hU1

#check @white_hInnerCont_closed_final2

end QIQTH.WhiteHInnerContLegADischarged

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHInnerContLegADischarged
#print axioms white_hInnerCont_closed_final2
end AxiomChecks
