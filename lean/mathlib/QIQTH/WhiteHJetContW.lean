/-
  WhiteHJetContW — J4-702 (Gap-A): THE BASE-`q` PARAMETERIZATION of the whitened `hbase` joint
  `(τ,z)` continuity.  The banked J4-698 capstone
  `WhiteHJetCont.whiteDefectKernel_jointContinuousOn_of_flowBall` supplies the `(·,·,0)`-SLICE only;
  the inner-engine recursion carry `InnerEngineRecursion.hcontE` (Gap-A) needs joint `(τ,z)`
  continuity of the whitened defect kernel at a GENERAL fixed SECOND spatial argument `q = w`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It re-runs the
  banked base-`0` continuity tower at an arbitrary base point `q` — every underlying primitive is
  ALREADY base-general (`whiteWitness_tauDeriv_eq_rep`, `whiteInvChart_continuousAt_flowBall`, the
  gate-congr germs, the §A jet engine, the §B/§C joint smoothness); only the base-`0` WRAPPERS were
  literal-`0`-anchored, and this file re-instantiates them at `q`.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED / soundly re-instantiated; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `whiteCutKernel_contDiffAt_joint_at` — §C at base `q`: the whitened cut-kernel base-`q` slice
      `(τ,z) ↦ whiteCutKernel … τ z q` is jointly `ContDiffAt ℝ 2` for `τ > 0` given the base-`q`
      chart germ `C²`.
    * `white_hGradCont_at` / `white_hHessCont_at` — the first/second spatial-jet joint continuities of
      the whitened field at base `q` (the §A engine ∘ §C at `q`, gate-congr at `q`).
    * `white_hLterm_continuousOn_of_jets_at` — the `Δ_z` Laplace–Beltrami term at base `q`, reduced to
      the two named jets (metric + Christoffel layer discharged — base-INDEPENDENT, at the field point).
    * `white_hRepCont_at` — the `∂_τ` representative field `whiteTauDerivRep … (τ,z,q)` joint continuity,
      in-gate collapse at base `q` (`q ∈ Kset`, `closedBall 0 R ⊆ S q`) + the base-`q` chart continuity.
    * `whiteInvChart_continuousOn_flowBall_at` — the base-`q` chart continuity on `closedBall 0 R` from
      the base-`q` flow-ball reach + germ (`whiteInvChart_continuousAt_flowBall` is already general).
    * `whiteDefectKernel_jointContinuousOn_of_parts_at` /
      `white_hDterm_jointContinuousOn_of_repCont_at` — the base-`q` `heatOp` split wrappers.
    * `whiteDefectKernel_jointContinuousOn_of_flowBall_at` — ★★★ the base-`q` capstone: joint `(τ,z)`
      continuity of `(τ,z) ↦ whiteDefectKernel … τ z q` on `Icc t₁ t₂ ×ˢ closedBall 0 R`, from the
      base-`q` flow-ball geometry `{q ∈ Kset, IsOpen (S q), closedBall 0 R ⊆ S q, closedBall 0 R ⊆
      flow-ball_q(c), c < δ₀, base-q germ}` — the EXACT `hcontE`/Gap-A shape (after the continuous time
      reparam `τ ↦ τ − τ·u`) at a general base `q = w`.
    * `whiteDefectKernel_jointContinuousOn_at_offBase` — the OFF-`Kset` leg: for `q ∉ Kset` the whitened
      defect kernel vanishes identically, so the base-`q` slice is trivially jointly continuous — the
      other half of the a.e.-`w` Gap-A split (no geometry needed).

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT a₁ = R/6).
    The base-`q` flow-ball geometry `{IsOpen (S q), closedBall 0 R ⊆ S q, closedBall 0 R ⊆ flow-ball_q(c),
    base-q germ}` is a labelled GEOMETRIC certificate (the re-centered analogue of the banked base-`0`
    reach containment) — supplied, not proved here; and the a.e.-`w` ASSEMBLY over `Kset` (uniform reach
    across bases) is downstream.

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteHJetCont
import QIQTH.WhiteHVcont
import QIQTH.WhiteHLcont
import QIQTH.WhiteS1P1
import QIQTH.WhiteS1P2

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteS1
open QIQTH.WhiteHBaseReduction QIQTH.WhiteHRepCont QIQTH.WhiteHVcont QIQTH.WhiteHLcont
open QIQTH.WhiteHJetCont QIQTH.WhiteS1P1 QIQTH.WhiteS1P2
open scoped Topology BigOperators

namespace QIQTH.WhiteHJetContW

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §C@q — THE WHITENED CUT KERNEL, JOINTLY `C²` AT A GENERAL BASE `q`.
    ############################################################################### -/

/-- **★ `whiteCutKernel_contDiffAt_joint_at`.**  The base-`q` analogue of
    `WhiteHJetCont.whiteCutKernel_contDiffAt_joint`: the whitened cutoff kernel base-`q` field slice
    `(τ,z) ↦ whiteCutKernel κ … τ z q = χ(V_q z)·(√det g^κ(q)·G_τ(V_q z))` is jointly `ContDiffAt ℝ 2`
    at `(τ,z)` whenever `τ > 0` and the raw chart `uniformInverseChart … q` is `ContDiffAt ℝ 2` at
    `z`.  Mechanical base-`0`→`q` re-instantiation.  NOT `a₁ = R/6`. -/
theorem whiteCutKernel_contDiffAt_joint_at (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (q : Point n) (τ : ℝ) (z : Point n) (hτ : 0 < τ)
    (hC2 : ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) z) :
    ContDiffAt ℝ 2 (fun p : ℝ × Point n => whiteCutKernel κ hκ hKc a b p.1 p.2 q) (τ, z) := by
  have hV0z : ContDiffAt ℝ 2 (fun x : Point n => whiteInvChart κ hκ hKc q x) z := by
    have hcd : ContDiff ℝ (2 : WithTop ℕ∞) (fun v : Point n => whiteUnvel κ q v) :=
      (whiteUnvel κ q).contDiff
    have hlin : ContDiffAt ℝ 2 (fun v : Point n => whiteUnvel κ q v)
        (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q z) := hcd.contDiffAt
    have h := hlin.comp z hC2
    simpa [whiteInvChart, Function.comp] using h
  have hsnd : ContDiffAt ℝ 2 (fun p : ℝ × Point n => p.2) (τ, z) := contDiffAt_snd
  have hV : ContDiffAt ℝ 2 (fun p : ℝ × Point n => whiteInvChart κ hκ hKc q p.2) (τ, z) := by
    have he : (fun p : ℝ × Point n => whiteInvChart κ hκ hKc q p.2)
        = (fun x : Point n => whiteInvChart κ hκ hKc q x) ∘ (fun p : ℝ × Point n => p.2) := rfl
    rw [he]; exact hV0z.comp (τ, z) hsnd
  have hpair : ContDiffAt ℝ 2
      (fun p : ℝ × Point n => (p.1, whiteInvChart κ hκ hKc q p.2)) (τ, z) :=
    contDiffAt_fst.prodMk hV
  have hgauss : ContDiffAt ℝ 2
      (fun p : ℝ × Point n => gaussDdim p.1 (whiteInvChart κ hκ hKc q p.2)) (τ, z) := by
    have he : (fun p : ℝ × Point n => gaussDdim p.1 (whiteInvChart κ hκ hKc q p.2))
        = (fun r : ℝ × Point n => gaussDdim r.1 r.2)
          ∘ (fun p : ℝ × Point n => (p.1, whiteInvChart κ hκ hKc q p.2)) := rfl
    rw [he]
    exact ((gaussDdim_contDiffAt_pos τ (whiteInvChart κ hκ hKc q z) hτ).of_le le_top).comp (τ, z) hpair
  have hχ : ContDiffAt ℝ 2
      (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc q p.2)) (τ, z) := by
    have hcut : ContDiffAt ℝ 2 (radialCutoff a b : Point n → ℝ) (whiteInvChart κ hκ hKc q z) :=
      (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have he : (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc q p.2))
        = (fun v : Point n => radialCutoff a b v)
          ∘ (fun p : ℝ × Point n => whiteInvChart κ hκ hKc q p.2) := rfl
    rw [he]; exact hcut.comp (τ, z) hV
  have hrw : (fun p : ℝ × Point n => whiteCutKernel κ hκ hKc a b p.1 p.2 q)
      = fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc q p.2)
          * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
              * gaussDdim p.1 (whiteInvChart κ hκ hKc q p.2)) := by
    funext p; simp only [whiteCutKernel, whiteAmbientKernel]
  rw [hrw]
  exact hχ.mul (contDiffAt_const.mul hgauss)

/-! ###############################################################################
    ### §D@q — THE FIRST/SECOND SPATIAL-JET CONTINUITIES OF THE WHITENED FIELD AT BASE `q`.
    ############################################################################### -/

/-- **★★ `white_hGradCont_at`** — the base-`q` first-jet continuity (base-`0`→`q` mirror of
    `WhiteHJetCont.white_hGradCont`).  NOT `a₁ = R/6`. -/
theorem white_hGradCont_at (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (q : Point n)
    (hqK : q ∈ Kset) (hSopen : IsOpen (S q))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S q)
    (hchart : ∀ z ∈ Metric.closedBall (0 : Point n) R,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) z)
    (k : Fin n) :
    ContinuousOn
      (fun p : ℝ × Point n => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) k p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hHbox : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R),
      ContDiffAt ℝ 2 (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 q) p := by
    intro p hp
    have hτ : 0 < p.1 := lt_of_lt_of_le ht₁ hp.1.1
    exact whiteCutKernel_contDiffAt_joint_at κ hκ hKc a b q p.1 p.2 hτ (hchart p.2 hp.2)
  have heng := pd_snd_jointContinuousOn
    (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 q) hHbox k
  refine heng.congr (fun p hp => ?_)
  have hpS : p.2 ∈ S q := hballS hp.2
  simpa [whiteFieldDeriv] using
    whiteFieldDeriv_gate_congr κ hκ hKc S a b k p.1 q p.2 hqK hSopen hpS

/-- **★★ `white_hHessCont_at`** — the base-`q` second-jet continuity (base-`0`→`q` mirror of
    `WhiteHJetCont.white_hHessCont`).  NOT `a₁ = R/6`. -/
theorem white_hHessCont_at (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (q : Point n)
    (hqK : q ∈ Kset) (hSopen : IsOpen (S q))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S q)
    (hchart : ∀ z ∈ Metric.closedBall (0 : Point n) R,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) z)
    (i j : Fin n) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hHbox : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R),
      ContDiffAt ℝ 2 (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 q) p := by
    intro p hp
    have hτ : 0 < p.1 := lt_of_lt_of_le ht₁ hp.1.1
    exact whiteCutKernel_contDiffAt_joint_at κ hκ hKc a b q p.1 p.2 hτ (hchart p.2 hp.2)
  have heng := pd_pd_snd_jointContinuousOn
    (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 q) hHbox i j
  refine heng.congr (fun p hp => ?_)
  have hpS : p.2 ∈ S q := hballS hp.2
  simpa [whiteFieldDeriv2] using
    whiteFieldDeriv2_gate_congr κ hκ hKc S a b i j p.1 q p.2 hqK hSopen hpS

/-! ###############################################################################
    ### `Δ_z`@q — THE LAPLACE–BELTRAMI TERM AT BASE `q`, REDUCED TO THE JETS.
    ############################################################################### -/

/-- **★★ `white_hLterm_continuousOn_of_jets_at`** — base-`q` mirror of
    `WhiteHLcont.white_hLterm_continuousOn_of_jets`.  The metric / Christoffel layer is at the FIELD
    point `p.2` (base-INDEPENDENT), so only the base is threaded through the jets.  NOT `a₁ = R/6`. -/
theorem white_hLterm_continuousOn_of_jets_at (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (q : Point n)
    (hGradCont : ∀ k : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) k p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hHessCont : ∀ i j : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  simp only [laplaceBeltrami]
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  have hgi : ContinuousOn (fun p : ℝ × Point n => curvedRNCInv κ p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    (((curvedRNCInv_contDiff κ hκ i j).continuous).comp continuous_snd).continuousOn
  refine hgi.mul (ContinuousOn.sub (hHessCont i j) ?_)
  apply continuousOn_finsetSum
  intro k _
  have hΓ : ContinuousOn
      (fun p : ℝ × Point n =>
        christoffel (curvedRNCMetric κ) (curvedRNCInv κ) k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    (((curvedRNC_hChr κ hκ k i j).continuous).comp continuous_snd).continuousOn
  exact hΓ.mul (hGradCont k)

/-! ###############################################################################
    ### `∂_τ`@q — THE REPRESENTATIVE-FIELD CONTINUITY AT BASE `q`, IN-GATE COLLAPSE.
    ############################################################################### -/

/-- **★★ `white_hRepCont_at`** — base-`q` mirror of `WhiteHRepCont.white_hRepCont`.  On the in-window
    in-gate box (`q ∈ Kset`, `closedBall 0 R ⊆ S q`, `0 < τ`) the gate indicator inside
    `whiteTauDerivRep … (τ,z,q)` is constantly ON, collapsing to the closed form at
    `v = whiteInvChart q z`, jointly continuous from the base-`q` chart continuity `hVcont`.  NOT
    `a₁ = R/6`. -/
theorem white_hRepCont_at (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (q : Point n)
    (hqK : q ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S q)
    (hVcont : ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc q z)
        (Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n => whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, q))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hτ0 : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R), (0 : ℝ) < p.1 :=
    fun p hp => lt_of_lt_of_le ht₁ hp.1.1
  have hVz : ContinuousOn (fun p : ℝ × Point n => whiteInvChart κ hκ hKc q p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    hVcont.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hcut : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc q p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    ((radialCutoff_contDiff a b).continuous).comp_continuousOn hVz
  have hden1 : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R),
      (4 * p.1 ^ 2) ≠ 0 := fun p hp => by have h := hτ0 p hp; positivity
  have hden2 : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R),
      (2 * p.1) ≠ 0 := fun p hp => by have h := hτ0 p hp; positivity
  have hsum : ContinuousOn
      (fun p : ℝ × Point n =>
        ∑ i : Fin n, ((whiteInvChart κ hκ hKc q p.2) i ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
    apply continuousOn_finsetSum
    intro i _
    refine ContinuousOn.sub ?_ ?_
    · exact ContinuousOn.div (((continuous_apply i).comp_continuousOn hVz).pow 2)
        (continuousOn_const.mul ((continuous_fst.pow 2).continuousOn)) hden1
    · exact continuousOn_const.div (continuousOn_const.mul continuous_fst.continuousOn) hden2
  have hgauss : ContinuousOn
      (fun p : ℝ × Point n => gaussDdim p.1 (whiteInvChart κ hκ hKc q p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    QIQTH.InnerKernelJointMeas.gaussDdim_continuousOn_pos.comp
      (continuous_fst.continuousOn.prodMk hVz)
      (fun p hp => hτ0 p hp)
  have hG : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc q p.2)
        * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
            * ((∑ i : Fin n, ((whiteInvChart κ hκ hKc q p.2) i ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)))
                * gaussDdim p.1 (whiteInvChart κ hκ hKc q p.2))))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    hcut.mul (continuousOn_const.mul (hsum.mul hgauss))
  refine hG.congr ?_
  intro p hp
  have hτp : (0 : ℝ) < p.1 := hτ0 p hp
  have hmem : ((p.1, p.2, q) : ℝ × Point n × Point n) ∈
      {w : ℝ × Point n × Point n | (w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2) ∧ 0 < w.1} :=
    ⟨⟨hqK, hballS hp.2⟩, hτp⟩
  have hWV : Wg (q, p.2) = whiteInvChart κ hκ hKc q p.2 :=
    (hagree (p.1, p.2, q) hqK (hballS hp.2)).symm
  have hval : whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, q)
      = radialCutoff a b (Wg (q, p.2)) * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
          * ((∑ i : Fin n, ((Wg (q, p.2)) i ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)))
              * gaussDdim p.1 (Wg (q, p.2)))) := by
    simp only [whiteTauDerivRep]
    rw [Set.indicator_of_mem hmem]
  simp only []
  rw [hval, hWV]

/-! ###############################################################################
    ### Vcont@q — THE BASE-`q` CHART CONTINUITY ON `closedBall 0 R`.
    ############################################################################### -/

/-- **`whiteInvChart_continuousOn_flowBall_at`** — base-`q` mirror of
    `WhiteHVcont.whiteInvChart_continuousOn_flowBall` (the pointwise germ
    `whiteInvChart_continuousAt_flowBall` is ALREADY base-general).  NOT `a₁ = R/6`. -/
theorem whiteInvChart_continuousOn_flowBall_at (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hqK : q ∈ Kset) (δ₀ : ℝ)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v)))
    (R c : ℝ) (hcδ : c < δ₀)
    (hball : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
          Metric.ball (0 : Point n) c) :
    ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc q z)
      (Metric.closedBall (0 : Point n) R) := by
  apply continuousOn_of_forall_continuousAt
  intro z hz
  exact whiteInvChart_continuousAt_flowBall κ hκ hKc q hqK δ₀ hspec c hcδ z (hball hz)

/-! ###############################################################################
    ### SPLIT@q — THE `heatOp` SPLIT WRAPPERS AT BASE `q`.
    ############################################################################### -/

/-- **`white_hDterm_jointContinuousOn_of_repCont_at`** — base-`q` mirror of
    `WhiteHBaseReduction.white_hDterm_jointContinuousOn_of_repCont` (`whiteWitness_tauDeriv_eq_rep` is
    base-general).  NOT `a₁ = R/6`. -/
theorem white_hDterm_jointContinuousOn_of_repCont_at (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (q : Point n) (s : Set (ℝ × Point n))
    (hRepCont : ContinuousOn
      (fun p : ℝ × Point n => whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, q)) s) :
    ContinuousOn
      (fun p : ℝ × Point n => deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u p.2 q) p.1) s :=
  hRepCont.congr (fun p _ =>
    whiteWitness_tauDeriv_eq_rep hn κ hκ hKc S a b Wg hagree (p.1, p.2, q))

/-- **`whiteDefectKernel_jointContinuousOn_of_parts_at`** — base-`q` mirror of
    `WhiteHBaseReduction.whiteDefectKernel_jointContinuousOn_of_parts` (`whiteDefectKernel_eq` /
    `heatOp` are base-general).  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_of_parts_at (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1) (q : Point n)
    (hDcont : ContinuousOn
      (fun p : ℝ × Point n => deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u p.2 q) p.1)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 q)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine (hDcont.sub hLcont).congr ?_
  intro p hp
  have hp1 : p.1 ∈ Set.Icc t₁ t₂ := hp.1
  have hτ : 0 < p.1 := lt_of_lt_of_le ht₁ hp1.1
  have hτ1 : p.1 ≤ 1 := le_trans hp1.2 ht₂
  show whiteDefectKernel κ hκ hKc S a b p.1 p.2 q
      = deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u p.2 q) p.1
        - laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
            (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) p.2
  rw [whiteDefectKernel_eq κ hκ hKc S a b hτ hτ1 p.2 q, heatOp]

/-! ###############################################################################
    ### CAPSTONE@q — THE BASE-`q` JOINT `(τ,z)` CONTINUITY (Gap-A supplier).
    ############################################################################### -/

/-- **★★★ `whiteDefectKernel_jointContinuousOn_of_flowBall_at` — THE BASE-`q` `hbase`.**  Joint
    `ContinuousOn` of the whitened one-step Levi residual base-`q` slice
    `(τ,z) ↦ whiteDefectKernel … τ z q` on the in-window positive-time box, from the base-`q` flow-ball
    geometry.  This is EXACTLY the (Gap-A / `hcontE`) shape of `InnerEngineRecursion` at a general
    second spatial argument `q = w` (after the continuous time reparam `τ ↦ τ − τ·u`).  The base-`0`
    `WhiteHJetCont.whiteDefectKernel_jointContinuousOn_of_flowBall` is the `q = 0` case.
    ⚠ CONDITIONAL on the labelled base-`q` geometric certificate `{q ∈ Kset, IsOpen (S q),
    closedBall 0 R ⊆ S q, closedBall 0 R ⊆ flow-ball_q(c), c < δ₀, base-q germ hspec}` — the re-centered
    analogue of the banked base-`0` reach containment.  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_of_flowBall_at (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (q : Point n) (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R c δ₀ : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (hqK : q ∈ Kset) (hSopen : IsOpen (S q))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S q)
    (hcδ : c < δ₀)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v)))
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
          Metric.ball (0 : Point n) c) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 q)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hchart : ∀ z ∈ Metric.closedBall (0 : Point n) R,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) z := by
    intro z hz
    obtain ⟨v, hv, hvz⟩ := hballC hz
    have hvδ : ‖v‖ < δ₀ := lt_trans (mem_ball_zero_iff.mp hv) hcδ
    have := (hspec v hvδ).2
    rwa [hvz] at this
  have hVcont : ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc q z)
      (Metric.closedBall (0 : Point n) R) :=
    whiteInvChart_continuousOn_flowBall_at κ hκ hKc q hqK δ₀ hspec R c hcδ hballC
  have hRep : ContinuousOn
      (fun p : ℝ × Point n => whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, q))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    white_hRepCont_at κ hκ hKc S a b Wg hagree t₁ t₂ R ht₁ q hqK hballS hVcont
  have hDcont : ContinuousOn
      (fun p : ℝ × Point n => deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u p.2 q) p.1)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    white_hDterm_jointContinuousOn_of_repCont_at hn κ hκ hKc S a b Wg hagree q _ hRep
  have hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    white_hLterm_continuousOn_of_jets_at κ hκ hKc S a b t₁ t₂ R q
      (white_hGradCont_at κ hκ hKc S a b t₁ t₂ R ht₁ q hqK hSopen hballS hchart)
      (white_hHessCont_at κ hκ hKc S a b t₁ t₂ R ht₁ q hqK hSopen hballS hchart)
  exact whiteDefectKernel_jointContinuousOn_of_parts_at κ hκ hKc S a b t₁ t₂ R ht₁ ht₂ q hDcont hLcont

/-! ###############################################################################
    ### REPARAM@q — THE EXACT Gap-A / `hcontE` INTEGRAND SHAPE (`τ ↦ τ − τ·u`).
    ############################################################################### -/

/-- **★★ `whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at` — THE Gap-A / `hcontE` FACTOR.**
    For a fixed `u ∈ (0,1)` and fixed base `w = q`, the time-reparametrized whitened defect kernel
        `(τ,z) ↦ whiteDefectKernel … (τ − τ·u) z q`
    is jointly `ContinuousOn` the box `Icc t₁ t₂ ×ˢ closedBall 0 R` — this is EXACTLY the per-`w` fibre
    of the `InnerEngineRecursion.hcontE` (Gap-A) slot at `E = whiteDefectKernel`.  Route: the continuous
    reparam `φ(τ,z) = (τ − τ·u, z) = (τ(1−u), z)` maps the box into `Icc (t₁(1−u)) (t₂(1−u)) ×ˢ
    closedBall 0 R` (`0 < 1−u`), where the base-`q` capstone applies at the shrunk positive-time window
    (spatial geometry is `u`-independent), then `ContinuousOn.comp`.  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (q : Point n) (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (u t₁ t₂ R c δ₀ : ℝ) (hu0 : 0 < u) (hu1 : u < 1) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (hqK : q ∈ Kset) (hSopen : IsOpen (S q))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S q)
    (hcδ : c < δ₀)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v)))
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
          Metric.ball (0 : Point n) c) :
    ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 q)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  -- the base-`q` capstone at the shrunk positive-time window `[t₁(1−u), t₂(1−u)]`.
  have ht₁' : 0 < t₁ * (1 - u) := mul_pos ht₁ h1u
  have ht₂' : t₂ * (1 - u) ≤ 1 := by
    rcases le_total 0 t₂ with ht | ht
    · have hle : t₂ * (1 - u) ≤ t₂ * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) ht
      rw [mul_one] at hle
      exact le_trans hle ht₂
    · nlinarith [mul_nonneg (neg_nonneg.mpr ht) (le_of_lt h1u)]
  have hbase := whiteDefectKernel_jointContinuousOn_of_flowBall_at hn κ hκ hKc S a b q Wg hagree
    (t₁ * (1 - u)) (t₂ * (1 - u)) R c δ₀ ht₁' ht₂' hqK hSopen hballS hcδ hspec hballC
  -- the continuous reparam `φ(τ,z) = (τ − τ·u, z)`.
  have hφ : ContinuousOn (fun p : ℝ × Point n => (p.1 - p.1 * u, p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    (by fun_prop : Continuous (fun p : ℝ × Point n => (p.1 - p.1 * u, p.2))).continuousOn
  -- `φ` maps the original box into the shrunk-time box.
  have hmaps : Set.MapsTo (fun p : ℝ × Point n => (p.1 - p.1 * u, p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)
      (Set.Icc (t₁ * (1 - u)) (t₂ * (1 - u)) ×ˢ Metric.closedBall (0 : Point n) R) := by
    rintro p ⟨hpτ, hpz⟩
    refine ⟨⟨?_, ?_⟩, hpz⟩
    · have : t₁ * (1 - u) ≤ p.1 * (1 - u) :=
        mul_le_mul_of_nonneg_right hpτ.1 (le_of_lt h1u)
      simpa [mul_one_sub] using this
    · have : p.1 * (1 - u) ≤ t₂ * (1 - u) :=
        mul_le_mul_of_nonneg_right hpτ.2 (le_of_lt h1u)
      simpa [mul_one_sub] using this
  exact hbase.comp hφ hmaps

/-! ###############################################################################
    ### OFF-BASE@q — THE `q ∉ Kset` LEG (trivial vanishing, no geometry).
    ############################################################################### -/

/-- **`whiteDefectKernel_jointContinuousOn_at_offBase`** — for `q ∉ Kset` the whitened defect kernel
    base-`q` slice vanishes identically (the base gate `q ∉ Kset` kills the `heatOp`), so it is jointly
    `ContinuousOn` ANY set with NO geometric input.  The other half of the a.e.-`w` Gap-A split.  NOT
    `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_at_offBase (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (q : Point n) (hq : q ∉ Kset)
    (s : Set (ℝ × Point n)) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 q) s := by
  have hzero : (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 q)
      = fun _ : ℝ × Point n => (0 : ℝ) := by
    funext p
    by_cases hw : 0 < p.1 ∧ p.1 ≤ 1
    · rw [whiteDefectKernel_eq κ hκ hKc S a b hw.1 hw.2 p.2 q]
      exact whiteGated_heatOp_zero_offGate κ hκ hKc S a b p.1 p.2 q (Or.inl hq)
    · simp only [whiteDefectKernel, if_neg hw]
  rw [hzero]
  exact continuousOn_const

#check @whiteCutKernel_contDiffAt_joint_at
#check @white_hGradCont_at
#check @white_hHessCont_at
#check @white_hLterm_continuousOn_of_jets_at
#check @white_hRepCont_at
#check @whiteInvChart_continuousOn_flowBall_at
#check @white_hDterm_jointContinuousOn_of_repCont_at
#check @whiteDefectKernel_jointContinuousOn_of_parts_at
#check @whiteDefectKernel_jointContinuousOn_of_flowBall_at
#check @whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at
#check @whiteDefectKernel_jointContinuousOn_at_offBase

end QIQTH.WhiteHJetContW

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHJetContW
#print axioms whiteCutKernel_contDiffAt_joint_at
#print axioms white_hGradCont_at
#print axioms white_hHessCont_at
#print axioms white_hLterm_continuousOn_of_jets_at
#print axioms white_hRepCont_at
#print axioms whiteInvChart_continuousOn_flowBall_at
#print axioms white_hDterm_jointContinuousOn_of_repCont_at
#print axioms whiteDefectKernel_jointContinuousOn_of_parts_at
#print axioms whiteDefectKernel_jointContinuousOn_of_flowBall_at
#print axioms whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at
#print axioms whiteDefectKernel_jointContinuousOn_at_offBase
end AxiomChecks
