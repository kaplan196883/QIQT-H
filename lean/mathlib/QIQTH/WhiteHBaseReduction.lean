/-
  WhiteHBaseReduction — J4-695: THE `hbase` REDUCTION AT THE WHITENED WITNESS.  The joint `(τ,z)`
  continuity of the whitened one-step Levi residual `whiteDefectKernel`, split (as
  `HeatOpWitnessContinuity.parametrixResidualN_jointContinuousOn_of_parts` does for the parametrix
  normal form) into its `∂_τ`-term and `Δ_z`-term continuities, and the `∂_τ`-term further reduced —
  via the banked closed-form time-derivative identity `WhiteS1.whiteWitness_tauDeriv_eq_rep` — to the
  joint continuity of the EXPLICIT representative field `whiteTauDerivRep`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a
  parametric-continuity REDUCTION brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE SPLIT.  `whiteDefectKernel = heatOp g^κ gi^κ (whiteGatedWitness)` on the window `(0,1]`
     (`WhiteBridge.whiteDefectKernel_eq`), and `heatOp g gi K τ x y` is DEFINITIONALLY
       `deriv (fun u => K u x y) τ − laplaceBeltrami g gi (fun p => K τ p y) x`
     (`TrueHeatKernel.heatOp`).  So on a positive-time box `Icc t₁ t₂ ×ˢ closedBall 0 R` with
     `0 < t₁` and `t₂ ≤ 1` (inside the window), the residual joint continuity splits by
     `ContinuousOn.sub` into:
       (hDcont) the `∂_τ` term `p ↦ deriv (fun u => whiteGatedWitness … u p.2 0) p.1`, and
       (hLcont) the `Δ_z` term `p ↦ laplaceBeltrami g^κ gi^κ (fun z => whiteGatedWitness … p.1 z 0) p.2`.

  ── THE `∂_τ`-TERM REDUCTION (the honest progress).  The banked `whiteWitness_tauDeriv_eq_rep` proves
     the POINTWISE identity `deriv (fun u => whiteGatedWitness … u p.2 0) p.1 = whiteTauDerivRep … (p.1,p.2,0)`
     at EVERY `(τ,z)` (on-gate `τ > 0` product-rule closed form; on-gate `τ ≤ 0` and off-gate `0`).  So
     the `∂_τ`-term continuity `hDcont` is `ContinuousOn.congr`-EQUAL to the continuity of the EXPLICIT
     representative field `whiteTauDerivRep` — reducing `hDcont` to `hRepCont` (a DIFFERENT, explicit
     function's continuity, NOT the conclusion).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `whiteDefectKernel_jointContinuousOn_of_parts` — ★★ THE `hbase` SPLIT.  Joint `ContinuousOn` of
      `whiteDefectKernel … p.1 p.2 0` on the in-window positive-time box, from `hDcont` + `hLcont`.
    • `white_hDterm_jointContinuousOn_of_repCont` — ★ THE `∂_τ` REDUCTION.  `hDcont` from the explicit
      representative field's joint continuity `hRepCont`, via `whiteWitness_tauDeriv_eq_rep`.
    • `whiteDefectKernel_jointContinuousOn_modulo_rep_and_L` — ★★★ the composed whitened `hbase`,
      discharged down to EXACTLY `{hRepCont (the ∂_τ representative field), hLcont (the Δ_z term)}`.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT a₁ = R/6).
     The two carried continuity bricks are the genuine remaining analytic work:
       • `hRepCont` — the joint `(τ,z)` continuity of `whiteTauDerivRep κ a b Kset S Wg (τ,z,0)`.  On a
         box SITTING INSIDE THE GATE (`0 ∈ Kset`, `closedBall 0 R ⊆ S 0`, `τ > 0`) the gate indicator
         is constantly ON, so `whiteTauDerivRep` collapses to the closed form
         `χ·(√det·((∑ᵢ vᵢ²/(4τ²) − 1/(2τ))·G_τ(v)))`, `v = whiteInvChart 0 z` — a composition of
         continuous functions IF the chart `z ↦ whiteInvChart 0 z` is continuous in the field point
         (the in-gate `uniformInverseChart` continuity, the "C⁵ machinery"; available in-gate from the
         chart germ spec).  That box-inside-gate collapse + chart-composition continuity is the honest
         remaining `∂_τ` brick — not attempted here.
       • `hLcont` — the `Δ_z`-term joint continuity: `laplaceBeltrami` involves SECOND field derivatives
         of `whiteGatedWitness` (Gaussian/cutoff Hessian ∘ chart, needing the chart's second field
         jets — the (S1-b) order-2 territory).  The larger remaining brick — not attempted here.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteS1
import QIQTH.WhiteBridge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteS1
open scoped Topology

namespace QIQTH.WhiteHBaseReduction

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (B1) — the `hbase` SPLIT: whitened residual = ∂_τ term − Δ_z term (in-window).
    ############################################################################### -/

/-- **★★ `whiteDefectKernel_jointContinuousOn_of_parts` — THE `hbase` SPLIT.**  Joint `ContinuousOn`
    of the whitened one-step Levi residual `p ↦ whiteDefectKernel κ hκ hKc S a b p.1 p.2 0` on the
    IN-WINDOW positive-time box `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`, `t₂ ≤ 1`), from the joint
    continuity of its two constituent terms:
      • `hDcont` — the `∂_τ` term `p ↦ deriv (fun u => whiteGatedWitness … u p.2 0) p.1`;
      • `hLcont` — the `Δ_z` term `p ↦ laplaceBeltrami g^κ gi^κ (fun z => whiteGatedWitness … p.1 z 0) p.2`.
    Route: on the box `whiteDefectKernel = heatOp …` (`whiteDefectKernel_eq`, `τ ∈ (0,1]`), and `heatOp`
    is definitionally their difference, so `ContinuousOn.sub` + `ContinuousOn.congr`.  This is the
    whitened mirror of `HeatOpWitnessContinuity.parametrixResidualN_jointContinuousOn_of_parts`.
    Neither carried piece is the conclusion.  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_of_parts (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (hDcont : ContinuousOn
      (fun p : ℝ × Point n => deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u p.2 0) p.1)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine (hDcont.sub hLcont).congr ?_
  intro p hp
  have hp1 : p.1 ∈ Set.Icc t₁ t₂ := hp.1
  have hτ : 0 < p.1 := lt_of_lt_of_le ht₁ hp1.1
  have hτ1 : p.1 ≤ 1 := le_trans hp1.2 ht₂
  show whiteDefectKernel κ hκ hKc S a b p.1 p.2 0
      = deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u p.2 0) p.1
        - laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
            (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) p.2
  rw [whiteDefectKernel_eq κ hκ hKc S a b hτ hτ1 p.2 0, heatOp]

/-! ###############################################################################
    ### (B2) — the `∂_τ`-term reduction to the explicit representative field.
    ############################################################################### -/

/-- **★ `white_hDterm_jointContinuousOn_of_repCont` — THE `∂_τ`-TERM REDUCTION.**  The `∂_τ` term
    `p ↦ deriv (fun u => whiteGatedWitness κ hκ hKc S a b u p.2 0) p.1` is jointly `ContinuousOn` any
    set `s` PROVIDED the EXPLICIT representative field `p ↦ whiteTauDerivRep κ a b Kset S Wg (p.1,p.2,0)`
    is (that is `hRepCont`), via the banked pointwise closed-form identity
    `WhiteS1.whiteWitness_tauDeriv_eq_rep` (`ContinuousOn.congr`).  `Wg` is any chart representative
    agreeing with `whiteInvChart` on the gate (`hagree`).  `hRepCont` is a DIFFERENT, explicit
    function's continuity — NOT the conclusion.  NOT `a₁ = R/6`. -/
theorem white_hDterm_jointContinuousOn_of_repCont (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (s : Set (ℝ × Point n))
    (hRepCont : ContinuousOn
      (fun p : ℝ × Point n => whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, 0)) s) :
    ContinuousOn
      (fun p : ℝ × Point n => deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u p.2 0) p.1) s :=
  hRepCont.congr (fun p _ =>
    whiteWitness_tauDeriv_eq_rep hn κ hκ hKc S a b Wg hagree (p.1, p.2, 0))

/-! ###############################################################################
    ### (B3) — the composed whitened `hbase`, modulo `{hRepCont, hLcont}`.
    ############################################################################### -/

/-- **★★★ `whiteDefectKernel_jointContinuousOn_modulo_rep_and_L` — THE COMPOSED WHITENED `hbase`.**
    Joint `ContinuousOn` of the whitened one-step Levi residual on the in-window positive-time box,
    discharged down to EXACTLY the two honest surviving continuity bricks:
      • `hRepCont` — the joint continuity of the explicit `∂_τ` representative field `whiteTauDerivRep`;
      • `hLcont` — the joint continuity of the `Δ_z` term.
    The `∂_τ` term is supplied by `white_hDterm_jointContinuousOn_of_repCont` (from `hRepCont`), then
    combined with `hLcont` through `whiteDefectKernel_jointContinuousOn_of_parts`.  This is the exact
    `hbase` shape the `IterEContinuity` iterated engine ingests, MODULO `{hRepCont, hLcont}`.  NOT
    `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_modulo_rep_and_L (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (hRepCont : ContinuousOn
      (fun p : ℝ × Point n => whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, 0))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  whiteDefectKernel_jointContinuousOn_of_parts κ hκ hKc S a b t₁ t₂ R ht₁ ht₂
    (white_hDterm_jointContinuousOn_of_repCont hn κ hκ hKc S a b Wg hagree _ hRepCont)
    hLcont

#check @whiteDefectKernel_jointContinuousOn_of_parts
#check @white_hDterm_jointContinuousOn_of_repCont
#check @whiteDefectKernel_jointContinuousOn_modulo_rep_and_L

end QIQTH.WhiteHBaseReduction

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHBaseReduction
#print axioms whiteDefectKernel_jointContinuousOn_of_parts
#print axioms white_hDterm_jointContinuousOn_of_repCont
#print axioms whiteDefectKernel_jointContinuousOn_modulo_rep_and_L
end AxiomChecks
