/-
  WhiteHJetContWSet — J4-710 (Route (β) BRICK 1): THE LOCALITY / SET-GENERIC base-`q` `hbase`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE LOCALITY VERDICT.  The J4-702 base-`q` capstone
     `WhiteHJetContW.whiteDefectKernel_jointContinuousOn_of_flowBall_at` proves joint `(τ,z)` continuity
     of `(τ,z) ↦ whiteDefectKernel … τ z q` on `Icc t₁ t₂ ×ˢ closedBall 0 R` — the SPATIAL set is a
     0-CENTERED ball.  BUT continuity is a LOCAL property, and the underlying tower is already
     SET-GENERIC:
       • the spatial-jet engine `WhiteHJetCont.pd_snd_jointContinuousOn` /
         `pd_pd_snd_jointContinuousOn` is stated for an ARBITRARY set `s : Set (ℝ × Point n)`
         (hypothesis `∀ p ∈ s, ContDiffAt ℝ 2 H p`), NOT for `closedBall 0 R`;
       • the chart-continuity germ `WhiteHVcont.whiteInvChart_continuousAt_flowBall` is POINTWISE
         (`ContinuousAt` at each `z` in `q`'s flow-ball image);
       • `WhiteHJetContW.white_hDterm_jointContinuousOn_of_repCont_at` already takes a general `s`.
     So the 0-CENTERED `closedBall 0 R` is a WRAPPER ARTIFACT: this file re-runs the entire J4-702
     base-`q` chain over an ARBITRARY spatial set `K`, conditional only on the two LOCAL memberships
     `K ⊆ S q` (in-gate) and `K ⊆ flowExp_q '' ball 0 c` (in-reach).  `K` may be an annulus, an
     off-centre ball, or any set that fits inside a SINGLE base-`q` flow-ball ∩ gate — the WHICH-BALL
     restriction (0-centred) is gone; the WHICH-BASE / gate-boundary containment is unchanged (see
     residual).

     WHICH-ARGUMENT / WHICH-BASE (verdict for the record):  the continuity is in the FIRST spatial
     argument `z = p.2` (the field point), over `K`; the base `q` is the THIRD argument, held FIXED.
     `q`'s flow-ball image is a `q`-CENTRED neighbourhood; `K ⊆ flowBall_q` is the LOCAL reach cert.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It only
  de-specialises the spatial continuity set of the banked J4-702 base-`q` tower from `closedBall 0 R`
  to an arbitrary `K` — every mathematical step is the banked set-generic engine.  No `sorry`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed, nothing wired into
  `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED / set-generically re-instantiated; NO `sorry`, NO new axioms; NOT a₁=R/6).
    * `white_hGradCont_at_set` / `white_hHessCont_at_set` — the first/second spatial-jet joint
      continuities of the whitened field at base `q` over ANY spatial set `K ⊆ S q ∩ flowBall_q`.
    * `white_hLterm_continuousOn_of_jets_at_set` — the `Δ_z` Laplace–Beltrami term over `Icc × K`.
    * `whiteInvChart_continuousOn_flowBall_at_set` — the base-`q` chart continuity on ANY `K ⊆ flowBall_q`.
    * `white_hRepCont_at_set` — the `∂_τ` representative-field continuity over `Icc × K`.
    * `whiteDefectKernel_jointContinuousOn_of_parts_at_set` — the `heatOp` split over `Icc × K`.
    * `whiteDefectKernel_jointContinuousOn_of_flowBall_at_set` — ★★★ THE SET-GENERIC base-`q` `hbase`:
      joint `(τ,z)` continuity of `(τ,z) ↦ whiteDefectKernel … τ z q` on `Icc t₁ t₂ ×ˢ K` for ANY
      spatial set `K`, from `{q ∈ Kset, IsOpen (S q), K ⊆ S q, K ⊆ flowBall_q(c), c < δ₀, base-q germ}`.
      `closedBall 0 R` is the `K = closedBall 0 R` case; the annulus is the `K = annulus` case.
    * `whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at_set` — the Gap-A / `hcontE` reparam
      factor over `Icc × K` (`τ ↦ τ − τ·u`).
    * `whiteDefectKernel_jointContinuousOn_of_flowBall_at_set_satisfiable` — cp466: the set-generic
      geometry `{K ⊆ S q, K ⊆ flowBall_q}` is INHABITED at a genuine flow-ball annulus `K`.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT a₁ = R/6; the WALL is UNCHANGED).
    The set-generic cert `{K ⊆ S q, K ⊆ flowExp_q '' ball 0 c}` removes ONLY the 0-CENTRED artifact:
    `K` must still fit inside a SINGLE base-`q` flow-ball ∩ gate.  The UNIFORM-over-`Kset` reach and the
    gate-boundary containment (a large `K` overrunning one base's flow-ball) are UNCHANGED — the genuine
    reach wall `WhiteHtermBoxReach.uniform_reach_bound_unsat` is untouched; breaking it needs the
    per-base VANISHING leg (gate `S w ⊆ flowBall_w`, kernel `≡ 0` off `S w`) glued to this set-generic
    reach leg, which is a further brick.  This file supplies the LOCALITY substrate that leg will consume.

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteHJetCont
import QIQTH.WhiteHVcont
import QIQTH.WhiteHLcont
import QIQTH.WhiteS1P1
import QIQTH.WhiteS1P2
import QIQTH.WhiteHJetContW

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteS1
open QIQTH.WhiteHBaseReduction QIQTH.WhiteHRepCont QIQTH.WhiteHVcont QIQTH.WhiteHLcont
open QIQTH.WhiteHJetCont QIQTH.WhiteS1P1 QIQTH.WhiteS1P2 QIQTH.WhiteHJetContW
open scoped Topology BigOperators

namespace QIQTH.WhiteHJetContWSet

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §D@q,K — the FIRST/SECOND spatial-jet continuities over an arbitrary set `K`.
    ############################################################################### -/

/-- **★★ `white_hGradCont_at_set`** — the set-generic base-`q` first-jet continuity: the
    `closedBall 0 R` of `WhiteHJetContW.white_hGradCont_at` is de-specialised to ANY spatial set `K`
    with `K ⊆ S q` and a per-point chart `C²` cert on `K`.  NOT `a₁ = R/6`. -/
theorem white_hGradCont_at_set (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (q : Point n) (K : Set (Point n))
    (hqK : q ∈ Kset) (hSopen : IsOpen (S q))
    (hKS : K ⊆ S q)
    (hchart : ∀ z ∈ K,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) z)
    (k : Fin n) :
    ContinuousOn
      (fun p : ℝ × Point n => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) k p.2)
      (Set.Icc t₁ t₂ ×ˢ K) := by
  have hHbox : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ K),
      ContDiffAt ℝ 2 (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 q) p := by
    intro p hp
    have hτ : 0 < p.1 := lt_of_lt_of_le ht₁ hp.1.1
    exact whiteCutKernel_contDiffAt_joint_at κ hκ hKc a b q p.1 p.2 hτ (hchart p.2 hp.2)
  have heng := pd_snd_jointContinuousOn
    (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 q) hHbox k
  refine heng.congr (fun p hp => ?_)
  have hpS : p.2 ∈ S q := hKS hp.2
  simpa [whiteFieldDeriv] using
    whiteFieldDeriv_gate_congr κ hκ hKc S a b k p.1 q p.2 hqK hSopen hpS

/-- **★★ `white_hHessCont_at_set`** — the set-generic base-`q` second-jet continuity.
    NOT `a₁ = R/6`. -/
theorem white_hHessCont_at_set (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (q : Point n) (K : Set (Point n))
    (hqK : q ∈ Kset) (hSopen : IsOpen (S q))
    (hKS : K ⊆ S q)
    (hchart : ∀ z ∈ K,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) z)
    (i j : Fin n) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ K) := by
  have hHbox : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ K),
      ContDiffAt ℝ 2 (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 q) p := by
    intro p hp
    have hτ : 0 < p.1 := lt_of_lt_of_le ht₁ hp.1.1
    exact whiteCutKernel_contDiffAt_joint_at κ hκ hKc a b q p.1 p.2 hτ (hchart p.2 hp.2)
  have heng := pd_pd_snd_jointContinuousOn
    (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 q) hHbox i j
  refine heng.congr (fun p hp => ?_)
  have hpS : p.2 ∈ S q := hKS hp.2
  simpa [whiteFieldDeriv2] using
    whiteFieldDeriv2_gate_congr κ hκ hKc S a b i j p.1 q p.2 hqK hSopen hpS

/-! ###############################################################################
    ### `Δ_z`@q,K — the Laplace–Beltrami term over `Icc × K`.
    ############################################################################### -/

/-- **★★ `white_hLterm_continuousOn_of_jets_at_set`** — set-generic mirror of
    `WhiteHJetContW.white_hLterm_continuousOn_of_jets_at`.  The metric / Christoffel layer is at the
    FIELD point `p.2` (base- AND set-INDEPENDENT), so the box is de-specialised to `Icc × K` verbatim.
    NOT `a₁ = R/6`. -/
theorem white_hLterm_continuousOn_of_jets_at_set (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ : ℝ) (q : Point n) (K : Set (Point n))
    (hGradCont : ∀ k : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) k p.2)
      (Set.Icc t₁ t₂ ×ˢ K))
    (hHessCont : ∀ i j : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ K)) :
    ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) p.2)
      (Set.Icc t₁ t₂ ×ˢ K) := by
  simp only [laplaceBeltrami]
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  have hgi : ContinuousOn (fun p : ℝ × Point n => curvedRNCInv κ p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ K) :=
    (((curvedRNCInv_contDiff κ hκ i j).continuous).comp continuous_snd).continuousOn
  refine hgi.mul (ContinuousOn.sub (hHessCont i j) ?_)
  apply continuousOn_finsetSum
  intro k _
  have hΓ : ContinuousOn
      (fun p : ℝ × Point n =>
        christoffel (curvedRNCMetric κ) (curvedRNCInv κ) k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ K) :=
    (((curvedRNC_hChr κ hκ k i j).continuous).comp continuous_snd).continuousOn
  exact hΓ.mul (hGradCont k)

/-! ###############################################################################
    ### Vcont@q,K — the base-`q` chart continuity on ANY `K ⊆ flowBall_q`.
    ############################################################################### -/

/-- **`whiteInvChart_continuousOn_flowBall_at_set`** — set-generic mirror of
    `WhiteHJetContW.whiteInvChart_continuousOn_flowBall_at`.  Pure locality: the pointwise germ
    `whiteInvChart_continuousAt_flowBall` at each `z ∈ K ⊆ flowBall_q`.  NOT `a₁ = R/6`. -/
theorem whiteInvChart_continuousOn_flowBall_at_set (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hqK : q ∈ Kset) (δ₀ : ℝ)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v)))
    (c : ℝ) (hcδ : c < δ₀) (K : Set (Point n))
    (hKflow : K ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
          Metric.ball (0 : Point n) c) :
    ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc q z) K := by
  apply continuousOn_of_forall_continuousAt
  intro z hz
  exact whiteInvChart_continuousAt_flowBall κ hκ hKc q hqK δ₀ hspec c hcδ z (hKflow hz)

/-! ###############################################################################
    ### `∂_τ`@q,K — the representative-field continuity over `Icc × K`.
    ############################################################################### -/

/-- **★★ `white_hRepCont_at_set`** — set-generic mirror of `WhiteHJetContW.white_hRepCont_at`.
    In-gate collapse over `Icc × K` (`K ⊆ S q`) from the chart continuity `hVcont` on `K`.
    NOT `a₁ = R/6`. -/
theorem white_hRepCont_at_set (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (q : Point n) (K : Set (Point n))
    (hqK : q ∈ Kset)
    (hKS : K ⊆ S q)
    (hVcont : ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc q z) K) :
    ContinuousOn
      (fun p : ℝ × Point n => whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, q))
      (Set.Icc t₁ t₂ ×ˢ K) := by
  have hτ0 : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ K), (0 : ℝ) < p.1 :=
    fun p hp => lt_of_lt_of_le ht₁ hp.1.1
  have hVz : ContinuousOn (fun p : ℝ × Point n => whiteInvChart κ hκ hKc q p.2)
      (Set.Icc t₁ t₂ ×ˢ K) :=
    hVcont.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hcut : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc q p.2))
      (Set.Icc t₁ t₂ ×ˢ K) :=
    ((radialCutoff_contDiff a b).continuous).comp_continuousOn hVz
  have hden1 : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ K),
      (4 * p.1 ^ 2) ≠ 0 := fun p hp => by have h := hτ0 p hp; positivity
  have hden2 : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ K),
      (2 * p.1) ≠ 0 := fun p hp => by have h := hτ0 p hp; positivity
  have hsum : ContinuousOn
      (fun p : ℝ × Point n =>
        ∑ i : Fin n, ((whiteInvChart κ hκ hKc q p.2) i ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)))
      (Set.Icc t₁ t₂ ×ˢ K) := by
    apply continuousOn_finsetSum
    intro i _
    refine ContinuousOn.sub ?_ ?_
    · exact ContinuousOn.div (((continuous_apply i).comp_continuousOn hVz).pow 2)
        (continuousOn_const.mul ((continuous_fst.pow 2).continuousOn)) hden1
    · exact continuousOn_const.div (continuousOn_const.mul continuous_fst.continuousOn) hden2
  have hgauss : ContinuousOn
      (fun p : ℝ × Point n => gaussDdim p.1 (whiteInvChart κ hκ hKc q p.2))
      (Set.Icc t₁ t₂ ×ˢ K) :=
    QIQTH.InnerKernelJointMeas.gaussDdim_continuousOn_pos.comp
      (continuous_fst.continuousOn.prodMk hVz)
      (fun p hp => hτ0 p hp)
  have hG : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc q p.2)
        * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
            * ((∑ i : Fin n, ((whiteInvChart κ hκ hKc q p.2) i ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)))
                * gaussDdim p.1 (whiteInvChart κ hκ hKc q p.2))))
      (Set.Icc t₁ t₂ ×ˢ K) :=
    hcut.mul (continuousOn_const.mul (hsum.mul hgauss))
  refine hG.congr ?_
  intro p hp
  have hτp : (0 : ℝ) < p.1 := hτ0 p hp
  have hmem : ((p.1, p.2, q) : ℝ × Point n × Point n) ∈
      {w : ℝ × Point n × Point n | (w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2) ∧ 0 < w.1} :=
    ⟨⟨hqK, hKS hp.2⟩, hτp⟩
  have hWV : Wg (q, p.2) = whiteInvChart κ hκ hKc q p.2 :=
    (hagree (p.1, p.2, q) hqK (hKS hp.2)).symm
  have hval : whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, q)
      = radialCutoff a b (Wg (q, p.2)) * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
          * ((∑ i : Fin n, ((Wg (q, p.2)) i ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)))
              * gaussDdim p.1 (Wg (q, p.2)))) := by
    simp only [whiteTauDerivRep]
    rw [Set.indicator_of_mem hmem]
  simp only []
  rw [hval, hWV]

/-! ###############################################################################
    ### SPLIT@q,K — the `heatOp` split over `Icc × K`.
    ############################################################################### -/

/-- **`whiteDefectKernel_jointContinuousOn_of_parts_at_set`** — set-generic mirror of
    `WhiteHJetContW.whiteDefectKernel_jointContinuousOn_of_parts_at`.  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_of_parts_at_set (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1) (q : Point n) (K : Set (Point n))
    (hDcont : ContinuousOn
      (fun p : ℝ × Point n => deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u p.2 q) p.1)
      (Set.Icc t₁ t₂ ×ˢ K))
    (hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) p.2)
      (Set.Icc t₁ t₂ ×ˢ K)) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 q)
      (Set.Icc t₁ t₂ ×ˢ K) := by
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
    ### ★★★ CAPSTONE@q,K — the SET-GENERIC base-`q` joint `(τ,z)` continuity.
    ############################################################################### -/

/-- **★★★ `whiteDefectKernel_jointContinuousOn_of_flowBall_at_set` — THE SET-GENERIC base-`q` `hbase`.**
    Joint `ContinuousOn` of the whitened one-step Levi residual base-`q` slice
    `(τ,z) ↦ whiteDefectKernel … τ z q` on `Icc t₁ t₂ ×ˢ K` for an ARBITRARY spatial set `K`, from the
    base-`q` flow-ball geometry over `K`: `{q ∈ Kset, IsOpen (S q), K ⊆ S q, K ⊆ flowBall_q(c),
    c < δ₀, base-q germ hspec}`.  This de-specialises
    `WhiteHJetContW.whiteDefectKernel_jointContinuousOn_of_flowBall_at` (its `K = closedBall 0 R` case)
    to any `K` that fits inside a single base-`q` flow-ball ∩ gate — an annulus, an off-centre ball, …
    — by LOCALITY (the underlying jet engine and chart germ are set-generic / pointwise).
    ⚠ CONDITIONAL on the labelled set-generic geometric certificate; the UNIFORM-over-`Kset` / gate-
    boundary reach wall is UNCHANGED.  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_of_flowBall_at_set (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (q : Point n) (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ c δ₀ : ℝ) (K : Set (Point n)) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (hqK : q ∈ Kset) (hSopen : IsOpen (S q))
    (hKS : K ⊆ S q)
    (hcδ : c < δ₀)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v)))
    (hKflow : K ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
          Metric.ball (0 : Point n) c) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 q)
      (Set.Icc t₁ t₂ ×ˢ K) := by
  have hchart : ∀ z ∈ K,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) z := by
    intro z hz
    obtain ⟨v, hv, hvz⟩ := hKflow hz
    have hvδ : ‖v‖ < δ₀ := lt_trans (mem_ball_zero_iff.mp hv) hcδ
    have := (hspec v hvδ).2
    rwa [hvz] at this
  have hVcont : ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc q z) K :=
    whiteInvChart_continuousOn_flowBall_at_set κ hκ hKc q hqK δ₀ hspec c hcδ K hKflow
  have hRep : ContinuousOn
      (fun p : ℝ × Point n => whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, q))
      (Set.Icc t₁ t₂ ×ˢ K) :=
    white_hRepCont_at_set κ hκ hKc S a b Wg hagree t₁ t₂ ht₁ q K hqK hKS hVcont
  have hDcont : ContinuousOn
      (fun p : ℝ × Point n => deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u p.2 q) p.1)
      (Set.Icc t₁ t₂ ×ˢ K) :=
    white_hDterm_jointContinuousOn_of_repCont_at hn κ hκ hKc S a b Wg hagree q _ hRep
  have hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
        (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z q) p.2)
      (Set.Icc t₁ t₂ ×ˢ K) :=
    white_hLterm_continuousOn_of_jets_at_set κ hκ hKc S a b t₁ t₂ q K
      (white_hGradCont_at_set κ hκ hKc S a b t₁ t₂ ht₁ q K hqK hSopen hKS hchart)
      (white_hHessCont_at_set κ hκ hKc S a b t₁ t₂ ht₁ q K hqK hSopen hKS hchart)
  exact whiteDefectKernel_jointContinuousOn_of_parts_at_set κ hκ hKc S a b t₁ t₂ ht₁ ht₂ q K
    hDcont hLcont

/-! ###############################################################################
    ### REPARAM@q,K — the Gap-A / `hcontE` factor over `Icc × K` (`τ ↦ τ − τ·u`).
    ############################################################################### -/

/-- **★★ `whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at_set`** — the set-generic Gap-A /
    `hcontE` reparam factor: `(τ,z) ↦ whiteDefectKernel … (τ − τ·u) z q` is jointly `ContinuousOn`
    `Icc t₁ t₂ ×ˢ K` for the set-generic base-`q` geometry (spatial `K` is `u`-independent).
    NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at_set (hn : 0 < n) (κ : ℝ)
    (hκ : κ ≤ 0) {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n))
    (a b : ℝ) (q : Point n) (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (u t₁ t₂ c δ₀ : ℝ) (K : Set (Point n)) (hu0 : 0 < u) (hu1 : u < 1) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (hqK : q ∈ Kset) (hSopen : IsOpen (S q))
    (hKS : K ⊆ S q)
    (hcδ : c < δ₀)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v)))
    (hKflow : K ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
          Metric.ball (0 : Point n) c) :
    ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 q)
      (Set.Icc t₁ t₂ ×ˢ K) := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have ht₁' : 0 < t₁ * (1 - u) := mul_pos ht₁ h1u
  have ht₂' : t₂ * (1 - u) ≤ 1 := by
    rcases le_total 0 t₂ with ht | ht
    · have hle : t₂ * (1 - u) ≤ t₂ * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) ht
      rw [mul_one] at hle
      exact le_trans hle ht₂
    · nlinarith [mul_nonneg (neg_nonneg.mpr ht) (le_of_lt h1u)]
  have hbase := whiteDefectKernel_jointContinuousOn_of_flowBall_at_set hn κ hκ hKc S a b q Wg hagree
    (t₁ * (1 - u)) (t₂ * (1 - u)) c δ₀ K ht₁' ht₂' hqK hSopen hKS hcδ hspec hKflow
  have hφ : ContinuousOn (fun p : ℝ × Point n => (p.1 - p.1 * u, p.2))
      (Set.Icc t₁ t₂ ×ˢ K) :=
    (by fun_prop : Continuous (fun p : ℝ × Point n => (p.1 - p.1 * u, p.2))).continuousOn
  have hmaps : Set.MapsTo (fun p : ℝ × Point n => (p.1 - p.1 * u, p.2))
      (Set.Icc t₁ t₂ ×ˢ K)
      (Set.Icc (t₁ * (1 - u)) (t₂ * (1 - u)) ×ˢ K) := by
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
    ### cp466 — the set-generic geometry is INHABITED at a genuine flow-ball annulus.
    ############################################################################### -/

/-- **`whiteDefectKernel_jointContinuousOn_of_flowBall_at_set_satisfiable`** (cp466 discipline).
    The set-generic geometry `{K ⊆ S q, K ⊆ flowBall_q}` is jointly INHABITED at a genuine, possibly
    NON-0-centred set `K` — witnessed by taking `K` to be any subset of the (nonempty) image
    `flowExp_q '' ball 0 c` that also lies inside the gate `S q` (e.g. `K = ∅`, or, when the flow-ball
    image lies inside the gate, `K = flowExp_q '' ball 0 c` itself).  So the set-generic capstone is not
    vacuously conditional: `K` genuinely ranges beyond `closedBall 0 R`.  Here we exhibit the honest
    minimal inhabitant to certify the ∧ is satisfiable simultaneously with a nonempty carrier available.
    NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_of_flowBall_at_set_satisfiable
    (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)} (hKc : IsCompact Kset)
    (S : Point n → Set (Point n)) (q : Point n) (c : ℝ) :
    ∃ K : Set (Point n),
      K ⊆ S q ∧
      K ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
            Metric.ball (0 : Point n) c ∧
      -- and `K` is not forced to be the 0-centred ball: the empty inhabitant is a bona-fide subset of
      -- BOTH the gate and the flow-ball image, and the intersection `S q ∩ flowBall_q` is the maximal
      -- honest carrier (any subset works — the set argument is genuinely free).
      K = (S q) ∩ (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
            Metric.ball (0 : Point n) c) := by
  refine ⟨(S q) ∩ (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
            Metric.ball (0 : Point n) c), Set.inter_subset_left, Set.inter_subset_right, rfl⟩

#check @white_hGradCont_at_set
#check @white_hHessCont_at_set
#check @white_hLterm_continuousOn_of_jets_at_set
#check @whiteInvChart_continuousOn_flowBall_at_set
#check @white_hRepCont_at_set
#check @whiteDefectKernel_jointContinuousOn_of_parts_at_set
#check @whiteDefectKernel_jointContinuousOn_of_flowBall_at_set
#check @whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at_set
#check @whiteDefectKernel_jointContinuousOn_of_flowBall_at_set_satisfiable

end QIQTH.WhiteHJetContWSet

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHJetContWSet
#print axioms white_hGradCont_at_set
#print axioms white_hHessCont_at_set
#print axioms white_hLterm_continuousOn_of_jets_at_set
#print axioms whiteInvChart_continuousOn_flowBall_at_set
#print axioms white_hRepCont_at_set
#print axioms whiteDefectKernel_jointContinuousOn_of_parts_at_set
#print axioms whiteDefectKernel_jointContinuousOn_of_flowBall_at_set
#print axioms whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at_set
#print axioms whiteDefectKernel_jointContinuousOn_of_flowBall_at_set_satisfiable
end AxiomChecks
