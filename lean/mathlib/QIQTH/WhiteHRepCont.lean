/-
  WhiteHRepCont — J4-696: THE `hRepCont` BRICK — joint `(τ,z)` continuity of the explicit `∂_τ`
  representative field `whiteTauDerivRep` on the in-window IN-GATE box.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a
  parametric-continuity brick — the nearest member of the `WhiteHBaseReduction` residue
  `{hEmeas, hRepCont, hLcont, hstep}`.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE COLLAPSE.  On a box `Icc t₁ t₂ ×ˢ closedBall 0 R` SITTING INSIDE THE GATE — that is
     `0 ∈ Kset`, `closedBall 0 R ⊆ S 0`, and `0 < t₁` (so `0 < τ`) — the gate indicator inside
     `whiteTauDerivRep κ a b Kset S Wg (τ, z, 0)` is CONSTANTLY ON, so the field collapses to the
     closed form
       `χ(v) · (√det g^κ(0) · ((∑ᵢ vᵢ²/(4τ²) − 1/(2τ)) · G_τ(v)))`,  `v = whiteInvChart 0 z`,
     (`Set.indicator_of_mem`, and `hagree` to identify `Wg (0,z) = whiteInvChart 0 z` in-gate).

  ── THE COMPOSITION.  That closed form is jointly `ContinuousOn` the box:
       • `χ(v) = radialCutoff a b v` — `radialCutoff_contDiff` ∘ the chart continuity;
       • `√det g^κ(0)` — a constant;
       • `∑ᵢ vᵢ²/(4τ²) − 1/(2τ)` — `continuousOn_finsetSum`; each term is a `.div` with the
         `τ`-power denominators non-vanishing on the positive-time box (`0 < t₁`);
       • `G_τ(v) = gaussDdim τ v` — the banked strip continuity `gaussDdim_continuousOn_pos`
         composed with `(τ, whiteInvChart 0 z)`.
     The ONE analytic input is the in-gate chart continuity `hVcont` of `z ↦ whiteInvChart 0 z` on
     `closedBall 0 R` (the "C⁵ machinery" germ, banked in-gate from the flow-ball chart spec) — a
     STRICTLY lower-level, DIFFERENT function's continuity, NEVER the conclusion.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `white_hRepCont` — ★★ the joint `(τ,z)` continuity of `whiteTauDerivRep κ a b Kset S Wg (τ,z,0)`
      on the in-window in-gate box, discharged down to the in-gate chart continuity `hVcont` and the
      gate-geometry inputs `{0 ∈ Kset, closedBall 0 R ⊆ S 0}`.
    • `whiteDefectKernel_jointContinuousOn_modulo_L` — ★★★ the composed whitened `hbase`, with the
      `∂_τ` representative-field residue `hRepCont` NOW DISCHARGED via `white_hRepCont`, leaving the
      `Δ_z` term `hLcont` as the sole surviving CONTINUITY residue (plus the in-gate chart germ
      `hVcont` and the gate geometry, both strictly lower-level, non-conclusion inputs).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteHBaseReduction
import QIQTH.InnerKernelJointMeas

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteS1
open QIQTH.WhiteHBaseReduction
open scoped Topology BigOperators

namespace QIQTH.WhiteHRepCont

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (C1) — `hRepCont`: joint continuity of the `∂_τ` representative field.
    ############################################################################### -/

/-- **★★ `white_hRepCont` — THE `∂_τ` REPRESENTATIVE-FIELD CONTINUITY.**  On the in-window in-gate
    box `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`, so `0 < τ`) sitting INSIDE the gate (`0 ∈ Kset`,
    `closedBall 0 R ⊆ S 0`) the gate indicator inside `whiteTauDerivRep` is constantly ON, so the
    field collapses (`Set.indicator_of_mem` + `hagree` on the gate) to the closed form
    `χ(v)·(√det g^κ(0)·((∑ᵢ vᵢ²/(4τ²) − 1/(2τ))·G_τ(v)))`, `v = whiteInvChart 0 z`, which is jointly
    continuous from the in-gate chart continuity `hVcont`, `radialCutoff_contDiff`,
    `gaussDdim_continuousOn_pos`, and the non-vanishing `τ`-power denominators.  The carried `hVcont`
    is a DIFFERENT, strictly lower-level function's continuity — NEVER the conclusion.  NOT
    `a₁ = R/6`. -/
theorem white_hRepCont (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hVcont : ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc 0 z)
        (Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n => whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, 0))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  -- the positive-time floor on the box.
  have hτ0 : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R), (0 : ℝ) < p.1 :=
    fun p hp => lt_of_lt_of_le ht₁ hp.1.1
  -- the chart continuity, transported to the box (via `Prod.snd`).
  have hVz : ContinuousOn (fun p : ℝ × Point n => whiteInvChart κ hκ hKc 0 p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    hVcont.comp continuous_snd.continuousOn (fun p hp => hp.2)
  -- the cutoff factor.
  have hcut : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc 0 p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    ((radialCutoff_contDiff a b).continuous).comp_continuousOn hVz
  -- the denominators are non-vanishing on the positive-time box.
  have hden1 : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R),
      (4 * p.1 ^ 2) ≠ 0 := fun p hp => by have h := hτ0 p hp; positivity
  have hden2 : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R),
      (2 * p.1) ≠ 0 := fun p hp => by have h := hτ0 p hp; positivity
  -- the DeWitt-type coefficient sum.
  have hsum : ContinuousOn
      (fun p : ℝ × Point n =>
        ∑ i : Fin n, ((whiteInvChart κ hκ hKc 0 p.2) i ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
    apply continuousOn_finsetSum
    intro i _
    refine ContinuousOn.sub ?_ ?_
    · exact ContinuousOn.div (((continuous_apply i).comp_continuousOn hVz).pow 2)
        (continuousOn_const.mul ((continuous_fst.pow 2).continuousOn)) hden1
    · exact continuousOn_const.div (continuousOn_const.mul continuous_fst.continuousOn) hden2
  -- the Gaussian, via the banked strip continuity composed with `(τ, whiteInvChart 0 z)`.
  have hgauss : ContinuousOn
      (fun p : ℝ × Point n => gaussDdim p.1 (whiteInvChart κ hκ hKc 0 p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    QIQTH.InnerKernelJointMeas.gaussDdim_continuousOn_pos.comp
      (continuous_fst.continuousOn.prodMk hVz)
      (fun p hp => hτ0 p hp)
  -- the assembled closed form is continuous.
  have hG : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc 0 p.2)
        * (Real.sqrt (Matrix.det (curvedRNCMetric κ (0 : Point n)))
            * ((∑ i : Fin n, ((whiteInvChart κ hκ hKc 0 p.2) i ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)))
                * gaussDdim p.1 (whiteInvChart κ hκ hKc 0 p.2))))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    hcut.mul (continuousOn_const.mul (hsum.mul hgauss))
  -- the field equals the closed form on the box.
  refine hG.congr ?_
  intro p hp
  have hτp : (0 : ℝ) < p.1 := hτ0 p hp
  have hmem : ((p.1, p.2, 0) : ℝ × Point n × Point n) ∈
      {w : ℝ × Point n × Point n | (w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2) ∧ 0 < w.1} :=
    ⟨⟨h0K, hballS hp.2⟩, hτp⟩
  have hWV : Wg (0, p.2) = whiteInvChart κ hκ hKc 0 p.2 :=
    (hagree (p.1, p.2, 0) h0K (hballS hp.2)).symm
  have hval : whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, 0)
      = radialCutoff a b (Wg (0, p.2)) * (Real.sqrt (Matrix.det (curvedRNCMetric κ (0 : Point n)))
          * ((∑ i : Fin n, ((Wg (0, p.2)) i ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)))
              * gaussDdim p.1 (Wg (0, p.2)))) := by
    simp only [whiteTauDerivRep]
    rw [Set.indicator_of_mem hmem]
  simp only []
  rw [hval, hWV]

/-! ###############################################################################
    ### (C2) — the composed whitened `hbase`, with `hRepCont` discharged.
    ############################################################################### -/

/-- **★★★ `whiteDefectKernel_jointContinuousOn_modulo_L` — THE COMPOSED WHITENED `hbase`.**  Joint
    `ContinuousOn` of the whitened one-step Levi residual on the in-window positive-time box, with the
    `∂_τ` representative-field residue `hRepCont` NOW DISCHARGED via `white_hRepCont` (from the in-gate
    chart continuity `hVcont` + the gate geometry `{0 ∈ Kset, closedBall 0 R ⊆ S 0}`).  The SOLE
    surviving CONTINUITY residue is the `Δ_z` term `hLcont`.  This threads through
    `whiteDefectKernel_jointContinuousOn_modulo_rep_and_L`.  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_modulo_L (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hVcont : ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc 0 z)
        (Metric.closedBall (0 : Point n) R))
    (hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  whiteDefectKernel_jointContinuousOn_modulo_rep_and_L hn κ hκ hKc S a b Wg hagree t₁ t₂ R ht₁ ht₂
    (white_hRepCont κ hκ hKc S a b Wg hagree t₁ t₂ R ht₁ h0K hballS hVcont)
    hLcont

#check @white_hRepCont
#check @whiteDefectKernel_jointContinuousOn_modulo_L

end QIQTH.WhiteHRepCont

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHRepCont
#print axioms white_hRepCont
#print axioms whiteDefectKernel_jointContinuousOn_modulo_L
end AxiomChecks
