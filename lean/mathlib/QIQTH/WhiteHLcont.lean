/-
  WhiteHLcont — J4-697 (ii): THE `hLcont` SCOPE-AND-START — the `Δ_z` Laplace–Beltrami term of the
  whitened defect reduced to its two named CHART-JET continuity residues (metric + Christoffel layer
  DISCHARGED).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a
  metric-algebra REDUCTION brick.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited,
  nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE SHAPE.  The `Δ_z` term carried by `whiteDefectKernel_jointContinuousOn_modulo_L` is
       `p ↦ laplaceBeltrami g^κ gi^κ (fun z => whiteGatedWitness … p.1 z 0) p.2`,
     which unfolds (`laplaceBeltrami`) to
       `∑ᵢ ∑ⱼ gi^κ(p.2)ᵢⱼ · ( ∂ᵢ∂ⱼ f(p.2) − ∑ₖ Γᵏᵢⱼ(p.2)·∂ₖ f(p.2) )`,  `f = fun z => W…p.1 z 0`.
     The `Δ_z` continuity therefore factors into
       • the inverse-metric coefficients `gi^κ(p.2)ᵢⱼ` — `curvedRNCInv_contDiff` (`C^∞`, `κ ≤ 0`);
       • the Christoffel coefficients `Γᵏᵢⱼ(p.2)` — `curvedRNC_hChr` (`C^∞`);
       • the SECOND spatial jet `∂ᵢ∂ⱼ f` and FIRST spatial jet `∂ₖ f` of the whitened field,
         JOINTLY in `(τ, z)` — the two IRREDUCIBLE chart-jet continuity inputs.
     This file DISCHARGES the metric + Christoffel + finite-sum + product/subtraction algebra layer,
     isolating the `Δ_z` residue to EXACTLY the two named field-jet continuities `{hHessCont, hGradCont}`
     — the honest "one derivative up" analogue of J4-696's `hRepCont`-modulo-`hVcont` reduction.  The
     jet-CONTINUITY inputs (as opposed to the banked jet-MEASURABILITY in `WhiteS1P2`) are the surviving
     analytic content, to be supplied from the `C⁵` second-jet tower.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `white_hLterm_continuousOn_of_jets` — ★★ the `Δ_z`-term joint `ContinuousOn` on the in-window box,
      reduced to `{hHessCont, hGradCont}` (the second/first spatial-jet joint continuities), with the
      inverse-metric and Christoffel coefficient continuity DISCHARGED internally.

  ⚠  STILL NOT `a₁ = R/6`.  The two jet-continuity inputs are a STRICTLY lower-level, DIFFERENT
     function's continuity — NEVER the conclusion.
-/
import Mathlib
import QIQTH.WhiteHRepCont
import QIQTH.WhiteHVcont

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteS1
open QIQTH.WhiteHBaseReduction QIQTH.WhiteHRepCont QIQTH.WhiteHVcont
open scoped Topology BigOperators

namespace QIQTH.WhiteHLcont

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (L1) — the `Δ_z` term, reduced to its two named chart-jet continuities.
    ############################################################################### -/

/-- **★★ `white_hLterm_continuousOn_of_jets` — THE `Δ_z`-TERM REDUCTION.**  The Laplace–Beltrami term
    of the whitened defect,
      `p ↦ laplaceBeltrami g^κ gi^κ (fun z => whiteGatedWitness … p.1 z 0) p.2`,
    is jointly `ContinuousOn` the in-window box `Icc t₁ t₂ ×ˢ closedBall 0 R`, GIVEN the joint
    continuity of the SECOND spatial jet `∂ᵢ∂ⱼ` (`hHessCont`) and the FIRST spatial jet `∂ₖ`
    (`hGradCont`) of the whitened field.  The inverse-metric coefficients (`curvedRNCInv_contDiff`,
    `C^∞`, `κ ≤ 0`) and the Christoffel coefficients (`curvedRNC_hChr`, `C^∞`) are DISCHARGED here; the
    two jet continuities are the sole surviving analytic residue.  This is EXACTLY the `hLcont`
    hypothesis carried by `whiteDefectKernel_jointContinuousOn_modulo_L`, modulo `{hHessCont, hGradCont}`.
    NOT `a₁ = R/6`. -/
theorem white_hLterm_continuousOn_of_jets (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ)
    (hGradCont : ∀ k : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) k p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hHessCont : ∀ i j : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  simp only [laplaceBeltrami]
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  -- the inverse-metric coefficient `gi^κ(p.2)ᵢⱼ` is continuous (`C^∞`).
  have hgi : ContinuousOn (fun p : ℝ × Point n => curvedRNCInv κ p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    (((curvedRNCInv_contDiff κ hκ i j).continuous).comp continuous_snd).continuousOn
  refine hgi.mul (ContinuousOn.sub (hHessCont i j) ?_)
  -- the Christoffel contraction `∑ₖ Γᵏᵢⱼ(p.2)·∂ₖ f(p.2)`.
  apply continuousOn_finsetSum
  intro k _
  have hΓ : ContinuousOn
      (fun p : ℝ × Point n =>
        christoffel (curvedRNCMetric κ) (curvedRNCInv κ) k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    (((curvedRNC_hChr κ hκ k i j).continuous).comp continuous_snd).continuousOn
  exact hΓ.mul (hGradCont k)

/-! ###############################################################################
    ### (L2) — the composed whitened `hbase`, `hVcont`-free, modulo the chart jets.
    ############################################################################### -/

/-- **★★★ `whiteDefectKernel_jointContinuousOn_modulo_jets` — THE WHITENED `hbase`, REDUCED TO THE
    CHART JETS.**  Joint `ContinuousOn` of the whitened one-step Levi residual on the in-window
    positive-time box, with BOTH surviving continuity residues of
    `whiteDefectKernel_jointContinuousOn_modulo_L` now reduced:
      • the `∂_τ` side — `hVcont` DISCHARGED via `whiteInvChart_continuousOn_flowBall` (from the
        flow-ball gate geometry `{0 ∈ Kset, closedBall 0 R ⊆ flow-ball(c), c < δ₀}` + the banked germ);
      • the `Δ_z` side — `hLcont` reduced (`white_hLterm_continuousOn_of_jets`) to EXACTLY the two named
        chart-jet continuities `{hHessCont, hGradCont}`, with the metric + Christoffel layer discharged.
    The SOLE surviving CONTINUITY residues are therefore the second/first spatial-jet joint continuities
    of the whitened field — strictly lower-level, DIFFERENT functions, never the conclusion.  NOT
    `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_modulo_jets (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R c δ₀ : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (h0K : (0 : Point n) ∈ Kset)
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
    (hGradCont : ∀ k : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) k p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hHessCont : ∀ i j : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  whiteDefectKernel_jointContinuousOn_modulo_L hn κ hκ hKc S a b Wg hagree t₁ t₂ R ht₁ ht₂ h0K hballS
    (whiteInvChart_continuousOn_flowBall κ hκ hKc h0K δ₀ hspec R c hcδ hballC)
    (white_hLterm_continuousOn_of_jets κ hκ hKc S a b t₁ t₂ R hGradCont hHessCont)

#check @white_hLterm_continuousOn_of_jets
#check @whiteDefectKernel_jointContinuousOn_modulo_jets

end QIQTH.WhiteHLcont

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHLcont
#print axioms white_hLterm_continuousOn_of_jets
#print axioms whiteDefectKernel_jointContinuousOn_modulo_jets
end AxiomChecks
