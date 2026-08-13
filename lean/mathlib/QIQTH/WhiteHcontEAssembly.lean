/-
  WhiteHcontEAssembly — J4-703 (Gap-A ASSEMBLY): THE a.e.-`w` PACKAGING of the J4-702 per-`w`
  base-`q` fibres into the EXACT `InnerEngineRecursion.hcontE` (Gap-A) slot of `innerStep_cont_ae`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE Gap-A SLOT.  `InnerEngineRecursion.innerStep_cont_ae` (and its `hcontE` argument) needs, at
     `E := whiteDefectKernel κ hκ hKc S a b`, the a.e.-`u` / a.e.-`w` reparametrized base continuity
        `∀ᵐ u ∂(volume.restrict (Ioc 0 1)), ∀ᵐ w ∂volume,
           ContinuousOn (fun p => whiteDefectKernel … (p.1 − p.1·u) p.2 w)
             (Icc t₁ t₂ ×ˢ closedBall 0 R)`.
     J4-702 (`WhiteHJetContW`) banked the TWO per-`w` fibres of this slot:
       • `whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at` — the `w ∈ Kset` leg, CONDITIONAL
         on the base-`w` flow-ball geometry `{IsOpen (S w), closedBall 0 R ⊆ S w, base-w germ hspec,
         closedBall 0 R ⊆ flowExp_w '' ball 0 c}`;
       • `whiteDefectKernel_jointContinuousOn_at_offBase` — the `w ∉ Kset` leg, UNCONDITIONAL (the
         whitened defect vanishes identically off the base gate).
     This file SPLITS the a.e.-`w` quantifier over `w ∈ Kset` vs `w ∉ Kset` and assembles the two fibres
     into the Gap-A slot, carrying the base-`w` geometry as ONE explicitly-named ∀-`q∈Kset` labelled
     certificate `hgeom` (the SCOPING VERDICT: the base-`q` reach `closedBall 0 R ⊆ S q` / `⊆ flowExp_q
     '' ball 0 c` is a 0-CENTERED ball inside a `q`-CENTERED flow-ball, which the banked
     `WhiteS1C.white_hpkgBound_at_radius` supplies only as per-`q` FATNESS `q ∈ S q`, NOT as this
     0-centered containment uniformly across `Kset` — so uniform geometry FAILS and the honest
     a.e.-parametric geometry certificate is carried, not discharged).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a purely
  MEASURE-THEORETIC packaging brick (a.e.-`u` drop of the null endpoint `u = 1`, an `∀ w` case split on
  `w ∈ Kset` feeding the two banked fibres).  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `white_hcontE_ae_of_baseGeom` — ★★★ the Gap-A slot: `∀ᵐ u, ∀ᵐ w, ContinuousOn (reparam base-`w`
      whitened defect) box`, from the ∀-`q∈Kset` base geometry certificate `hgeom`.  The a.e.-`u` leg
      drops the null endpoint `u = 1` (`Real.volume_singleton`); the inner leg is `∀ w` by the Kset
      case split (reparam fibre in-gate, offBase fibre off-gate) — stronger than a.e.-`w`.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT a₁ = R/6).
    * `hgeom` — the ∀-`q∈Kset` base-`w` flow-ball geometry `{IsOpen (S q), closedBall 0 R ⊆ S q,
      base-q germ hspec, closedBall 0 R ⊆ flowExp_q '' ball 0 c}` (the re-centered analogue of the
      banked base-`0` reach containment; the SCOPING verdict is that it is NOT uniform over `Kset` — a
      labelled geometric certificate, carried).

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteHJetContW
import QIQTH.InnerEngineRecursion

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp
open QIQTH.ExpMap QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open QIQTH.WhiteHJetCont QIQTH.WhiteHJetContW
open scoped Topology BigOperators

namespace QIQTH.WhiteHcontEAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ the Gap-A slot: a.e.-`u` / a.e.-`w` reparam base continuity from `hgeom`.
    ############################################################################### -/

/-- **★★★ `white_hcontE_ae_of_baseGeom` — the `InnerEngineRecursion.hcontE` (Gap-A) slot.**
    At `E := whiteDefectKernel κ hκ hKc S a b`, the a.e.-`u` / a.e.-`w` reparametrized base-`w` joint
    `(τ,z)` continuity
        `∀ᵐ u ∂(volume.restrict (Ioc 0 1)), ∀ᵐ w ∂volume,
           ContinuousOn (fun p => whiteDefectKernel … (p.1 − p.1·u) p.2 w) (Icc t₁ t₂ ×ˢ closedBall 0 R)`,
    assembled from the two banked J4-702 per-`w` fibres:
      • `w ∈ Kset`: `whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at` at the base-`w`
        geometry drawn from `hgeom`;
      • `w ∉ Kset`: `whiteDefectKernel_jointContinuousOn_at_offBase` (unconditional).
    The a.e.-`u` leg drops the null endpoint `u = 1` (so `0 < u < 1`, feeding the reparam positivity);
    the inner leg is proved for EVERY `w` (a stronger `ae_of_all`).  This is EXACTLY the `hcontE`
    argument of `innerStep_cont_ae`.
    ⚠ CONDITIONAL on `hagree` and the ∀-`q∈Kset` base geometry certificate `hgeom` (a labelled geometric
    carry — NOT uniform over `Kset`; see file header).  NOT `a₁ = R/6`. -/
theorem white_hcontE_ae_of_baseGeom (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R c δ₀ : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1) (hcδ : c < δ₀)
    (hgeom : ∀ q ∈ Kset,
        IsOpen (S q)
      ∧ Metric.closedBall (0 : Point n) R ⊆ S q
      ∧ (∀ v : Point n, ‖v‖ < δ₀ →
          (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
          ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q)
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v))
      ∧ Metric.closedBall (0 : Point n) R ⊆
          uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
            Metric.ball (0 : Point n) c) :
    ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ∀ᵐ w ∂(volume : Measure (Point n)),
        ContinuousOn
          (fun p : ℝ × Point n =>
            whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  -- a.e.-`u` leg: drop the null endpoint `u = 1`, so `0 < u < 1`.
  have hne1 : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), u ≠ (1:ℝ) := by
    refine ae_restrict_of_ae ?_
    have hmem : ({(1:ℝ)} : Set ℝ)ᶜ ∈ (ae volume) := by
      rw [mem_ae_iff, compl_compl, Real.volume_singleton]
    filter_upwards [hmem] with u hu
    simpa using hu
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hne1] with u hu hune
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := lt_of_le_of_ne hu.2 hune
  -- inner leg: prove for EVERY `w` by the `Kset` case split.
  refine ae_of_all _ (fun w => ?_)
  by_cases hwK : w ∈ Kset
  · -- in-gate leg: the banked reparam base-`w` fibre at the geometry from `hgeom`.
    obtain ⟨hSopen, hballS, hspec, hballC⟩ := hgeom w hwK
    exact whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at hn κ hκ hKc S a b w Wg hagree
      u t₁ t₂ R c δ₀ hu0 hu1 ht₁ ht₂ hwK hSopen hballS hcδ hspec hballC
  · -- off-gate leg: the whitened defect vanishes identically, so continuity is unconditional.
    have hzero : (fun p : ℝ × Point n =>
          whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w)
        = fun _ : ℝ × Point n => (0 : ℝ) := by
      funext p
      by_cases hpw : 0 < p.1 - p.1 * u ∧ p.1 - p.1 * u ≤ 1
      · rw [whiteDefectKernel_eq κ hκ hKc S a b hpw.1 hpw.2 p.2 w]
        exact whiteGated_heatOp_zero_offGate κ hκ hKc S a b (p.1 - p.1 * u) p.2 w (Or.inl hwK)
      · simp only [whiteDefectKernel, if_neg hpw]
    rw [hzero]
    exact continuousOn_const

#check @white_hcontE_ae_of_baseGeom

end QIQTH.WhiteHcontEAssembly

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHcontEAssembly
#print axioms white_hcontE_ae_of_baseGeom
end AxiomChecks
