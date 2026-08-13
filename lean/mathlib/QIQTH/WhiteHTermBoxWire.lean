/-
  WhiteHTermBoxWire — J4-700: THE `htermBox` MEASURABILITY + BOUND CARRIES DISCHARGED at the whitened
  defect kernel.  Composes the banked `iterE` OUTER engine (`IterEEngineWiring.iterE_jointContinuousOn_wired`)
  at `E := whiteDefectKernel κ hκ hKc S a b`, feeding the whitened one-step width-`lam` bound
  (`WhiteLeviMajorWire.white_hEbound_zero`), the whitened per-step integrability
  (`white_hInt_zero`), and the parametric-Fubini `u`-measurability
  (`InnerEngineRecursion.convStepIntegral_u_aestronglyMeasurable_wired`, discharged OUTRIGHT from the
  single S1 base measurability), so that the whitened `iterE` termwise box continuity `htermBox` owes
  EXACTLY two honest analytic carries: the flow-ball base continuity `hbase` and the recursive inner
  convolution-step joint continuity `hcont`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a
  regularity / wiring brick that removes the DERIVABLE carries (`hEbound`, `hInt`, `hEmeas`→`hmeas`) of
  the whitened `htermBox` by threading the banked whitened suppliers into the banked OUTER `iterE`
  engine.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis
  equal to (or trivially yielding) the conclusion, no existing file edited, nothing committed, nothing
  wired into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT `htermBox` IS (the surviving carry of `WhiteHInnerContTermBox.white_hInnerCont_modulo_termBox`).
     For every window value `u`, interior floor `τ₀/2`, radius `R'`, and level `k`, the joint
     `(τ,z)`-continuity of the whitened iterate
        `p ↦ iterE (whiteDefectKernel κ hκ hKc S a b) (k+1) p.1 p.2 0`
     on `Icc (τ₀/2) u ×ˢ closedBall 0 R'`.  The banked OUTER engine reduces this ALL-`k` box continuity
     to four slots — `hEbound` / `hInt` / `hmeas` / `{hbase, hcont}`; the first three are DERIVABLE from
     banked whitened material and are DISCHARGED here, leaving only `hbase` (flow-ball) + `hcont`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `white_htermBox_of_hbase_hcont` — ★★ the CORE reduction: for the τ-gated whitened defect at
      gate-parametric `{S, a, b, C, lam}` (`0 ≤ C`, `2 ≤ lam`, capstone-`hpkg`, S1 `hEmeas`), on the
      positive-time box `Icc t₁ t₂ ×ˢ closedBall 0 R`, the ALL-`k` termwise joint continuity of
      `iterE (whiteDefectKernel …) (k+1)` — reduced to EXACTLY the two carries `hbase` (the `(·,·,0)`
      slice continuity) and `hcont` (the a.e.-`u` inner convolution-step joint continuity).  The width
      one-step bound is `white_hEbound_zero`, the integrability `white_hInt_zero`, the `u`-measurability
      `convStepIntegral_u_aestronglyMeasurable_wired` (from the S1 base measurability alone).
    * `white_htermBox_of_flowBall_hcont` — ★★★ the flow-ball variant: the SAME output with `hbase`
      FURTHER discharged from the banked flow-ball continuity theorem
      `WhiteHJetCont.whiteDefectKernel_jointContinuousOn_of_flowBall` (the geometry data — chart germ,
      gate openness, and the reach containment `closedBall 0 R ⊆ flowExp 0 '' ball c` — carried).  The
      SOLE surviving analytic carry is then `hcont`.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
    * `hcont` — the a.e.-`u` joint `(τ,z)`-continuity of the inner convolution-step spatial integral
      `p ↦ ∫ w, E (p.1−p.1·u) p.2 w · iterE E (k+1) (p.1·u) w 0` (`E = whiteDefectKernel …`), the genuine
      RECURSIVE parametric-continuity brick (`InnerEngineRecursion` factors it into the S-dom Gaussian
      dominator + the Gap-A general-`w` base continuity + the Gap-B `iterE` time-continuity).
    * REACH ALIGNMENT.  `htermBox`'s CONSUMER (`WhiteLeviMajorWire.white_leviJoint_window_modulo_termBox`)
      needs the Levi joint continuity on `Ioc 0 u ×ˢ univ`, i.e. `htermBox` at ALL radii `R'`.  The
      flow-ball `hbase` covers only `R' ≤ chart reach` (`closedBall 0 R' ⊆ flowExp 0 '' ball c`); the
      `white_htermBox_of_flowBall_hcont` variant is therefore reach-restricted, and the `R' > reach`
      regime remains a labelled residual (dischargeable by the gate-vanishing extension —
      `whiteDefectKernel = 0` outside the gate — not built here).  `white_htermBox_of_hbase_hcont`
      sidesteps this by carrying `hbase` at the given `R` directly.

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteLeviMajorWire
import QIQTH.InnerEngineRecursion
import QIQTH.WhiteHJetCont

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.ExpMap
open QIQTH.CurvedA1CenterAmp QIQTH.WhiteWitness QIQTH.WhiteAmbient
open QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteLeviMajorWire
open QIQTH.InnerEngineRecursion QIQTH.IterEEngineWiring QIQTH.WhiteHJetCont
open scoped Topology BigOperators

namespace QIQTH.WhiteHTermBoxWire

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★ the CORE reduction — `hEbound` / `hInt` / `hmeas` discharged, `hbase`+`hcont` left.
    ############################################################################### -/

/-- **★★ `white_htermBox_of_hbase_hcont` — the whitened `htermBox` measurability + bound carries GONE.**
    On the positive-time box `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`), the ALL-`k` termwise joint
    `(τ,z)`-continuity of `p ↦ iterE (whiteDefectKernel κ hκ hKc S a b) (k+1) p.1 p.2 0`, reduced to
    EXACTLY the two honest analytic carries:
      • `hbase` — the `(·,·,0)`-slice joint continuity of the whitened one-step defect (the flow-ball
        germ output);
      • `hcont` — the a.e.-`u` inner convolution-step joint continuity (the recursive brick).
    The width-`lam` one-step bound (`white_hEbound_zero`, constant `2C`), the per-step integrability
    (`white_hInt_zero`), and the parametric-Fubini `u`-measurability
    (`convStepIntegral_u_aestronglyMeasurable_wired`, from the single S1 `hEmeas`) are all DISCHARGED.
    ⚠ CONDITIONAL on the capstone-`hpkg` and the S1 `hEmeas` (labelled).  NOT `a₁ = R/6`. -/
theorem white_htermBox_of_hbase_hcont (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    (hbase : ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hcont : ∀ k : ℕ, ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
          * iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  exact iterE_jointContinuousOn_wired (whiteDefectKernel κ hκ hKc S a b) lam (2 * C)
    hlam0 (by linarith) t₁ t₂ R ht₁
    (fun τ p q hτ => white_hEbound_zero κ hκ hKc S a b C lam hC hpkg τ p q hτ)
    (white_hInt_zero κ hκ hKc S a b C lam hC hlam0 hpkg hEmeas)
    hbase
    (convStepIntegral_u_aestronglyMeasurable_wired (whiteDefectKernel κ hκ hKc S a b) t₁ t₂ R
      (whiteDefectKernel_stronglyMeasurable κ hκ hKc S a b hEmeas))
    hcont

/-! ###############################################################################
    ### ★★★ the flow-ball variant — `hbase` further discharged, ONLY `hcont` left.
    ############################################################################### -/

/-- **★★★ `white_htermBox_of_flowBall_hcont` — `hbase` discharged from the flow-ball germ.**  The SAME
    ALL-`k` whitened `htermBox` box continuity as `white_htermBox_of_hbase_hcont`, but with the `hbase`
    slot FURTHER discharged by the banked flow-ball continuity theorem
    `WhiteHJetCont.whiteDefectKernel_jointContinuousOn_of_flowBall`.  The geometry data — the chart germ
    `hspec`, the gate agreement `hagree`/openness `hSopen`, and the reach containments
    `closedBall 0 R ⊆ S 0` and `closedBall 0 R ⊆ flowExp 0 '' ball c` — are carried; on that data the
    SOLE surviving analytic carry is the recursive `hcont`.
    ⚠ REACH-RESTRICTED: `hballC` forces `R ≤ chart reach` (see file header); the `R > reach` regime is a
    separate labelled residual.  ⚠ CONDITIONAL on `hpkg`, `hEmeas`, and the flow-ball geometry.
    NOT `a₁ = R/6`. -/
theorem white_htermBox_of_flowBall_hcont (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R c δ₀ : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (h0K : (0 : Point n) ∈ Kset) (hSopen : IsOpen (S 0))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hcδ : c < δ₀)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc 0 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc 0 z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc 0)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v)))
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    (hcont : ∀ k : ℕ, ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
          * iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  white_htermBox_of_hbase_hcont κ hκ hKc S a b C lam hC hlam2 t₁ t₂ R ht₁ hpkg hEmeas
    (whiteDefectKernel_jointContinuousOn_of_flowBall hn κ hκ hKc S a b Wg hagree
      t₁ t₂ R c δ₀ ht₁ ht₂ h0K hSopen hballS hcδ hspec hballC)
    hcont

#check @white_htermBox_of_hbase_hcont
#check @white_htermBox_of_flowBall_hcont

end QIQTH.WhiteHTermBoxWire

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHTermBoxWire
#print axioms white_htermBox_of_hbase_hcont
#print axioms white_htermBox_of_flowBall_hcont
end AxiomChecks
