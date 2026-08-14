/-
  WhiteHflowTruncConditional — J4-735 (C): THE HONEST TERMINAL RESTATEMENT of the whitened tower,
  with the opaque bundled `hflowTruncNear` REPLACED by three EXPLICIT, individually-satisfiable
  geometric hypotheses.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` (`R/6` stays a labelled carrier, untouched).
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE DELIVERABLE (per the J4-735 strategic review).
    `WhiteHflowTruncConcrete.white_hInnerCont_closed_final10` carried the near-only base-varying-flow
    contraction data as a SINGLE opaque bundle `hflowTruncNear` — the three clamp-centred clauses
    (contraction / v-Lipschitz / frontier→sphere-image) fused into one per-`z₀` existential.  That bundle
    hid WHICH geometric facts are genuinely needed and buried the contraction constant's `O(‖v‖)`
    smallness inside an existential.

    This file UNBUNDLES it.  `white_hInnerCont_final10_conditional` has the SAME conclusion and the same
    hypotheses as `final10`, except `hflowTruncNear` is replaced by THREE transparent, individually-named
    geometric hypotheses — the honest terminal surface of the whitened tower:

    * `hcontrLip` (the SMALLNESS leg) — for each near `z₀`, an EXPLICIT contraction modulus `M < 1` such
      that `u ↦ φ_u v − u` is `LipschitzOnWith M` on the truncation window, for every sphere direction
      `v`.  This is the once-buried `Dc = M₂·C₀·‖v‖` smallness, now EXPOSED as a named `M < 1` hypothesis
      (dischargeable from `BaseFlowHderFamilyFixedRadius.baseDisplacement_windowed_lipschitz_fixedRadius`
      whenever the v-independent rate `M₂fix·C₀·c·e^{Kc} < 1`, i.e. `c` small enough — the honest
      fixed-radius smallness condition of J4-735 (B)).  The clamp-composition into a `ContractingWith`
      solver map is discharged internally by `white_flowTruncNear_contr_clause_of_windowLip`.

    * `hvLip` (the WIDTH leg) — the uniform v-slot Lipschitz modulus `Cv` of the clamp-based flow, a
      genuine σ-interior-window geometric input (dischargeable from
      `WhiteFlowTruncNearClauses.white_flowTruncNear_vLip_clause` given `closedBall z₀ r ⊆ Kset` and a
      reach-radius bump `c < c' ≤ ρ₀`).

    * `hfrontImg` (the FRONTIER/INJECTIVITY leg) — the null-frontier→sphere-image containment
      `{w | z₀ ∈ frontier (S w)} ⊆ {w | ∃ v ∈ sphere 0 c, φ_w v = z₀}`, a genuine C¹-sphere-image
      geometric input (fed by the elementary image-annulus lemma
      `ImageAnnulusFrontier.frontier_image_ball_subset_image_sphere` when `S w = φ_w '' ball 0 c`).

    THIS IS THE STOPPING POINT for the `hflowData` thread (per strategic review): the whitened tower is
    now CONDITIONAL on {`hcontrLip` (fixed-radius smallness), `hvLip` (width), `hfrontImg` (frontier)} as
    EXPLICIT geometric hypotheses, not an opaque bundle.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteHflowTruncConcrete
import QIQTH.WhiteFlowTruncNearClauses

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteAnnulus
open QIQTH.WhiteHJetCont QIQTH.WhiteHBaseExtend
open QIQTH.WhiteHInnerContLegADischarged
open QIQTH.WhiteHBaseGateCollarDischarge
open QIQTH.WhiteHnullFlowReduction
open QIQTH.BaseFlowGlobalContraction
open QIQTH.BaseFlowTruncationWindow
open QIQTH.WhiteFlowTruncNearClauses
open QIQTH.WhiteHflowTruncConcrete
open scoped Topology ENNReal NNReal

namespace QIQTH.WhiteHflowTruncConditional

variable {n : ℕ}

/-- **★★★ J4-735 (C) — THE HONEST TERMINAL RESTATEMENT.**  `white_hInnerCont_closed_final10` with the
opaque bundled near-only contraction data `hflowTruncNear` REPLACED by three explicit, individually
satisfiable geometric hypotheses (all quantified over the inhabited frontier bad set only):

* `hr : 0 ≤ r` — the truncation radius is nonnegative (true at the concrete witness).
* `hcontrLip` — the EXPOSED contraction SMALLNESS: an explicit `M < 1` with `u ↦ φ_u v − u`
  `LipschitzOnWith M` on `closedBall z₀ r` for every `v ∈ sphere 0 c`.  (Fixed-radius smallness leg.)
* `hvLip` — the uniform v-slot Lipschitz modulus `Cv` of the clamp-based flow.  (Width leg.)
* `hfrontImg` — the null-frontier→sphere-image containment.  (Frontier/injectivity leg.)

The bundle `hflowTruncNear` is reconstructed internally: `hcontrLip` is turned into the clamp-centred
`ContractingWith` clause by `white_flowTruncNear_contr_clause_of_windowLip`; `hvLip` and `hfrontImg`
supply clauses (ii)/(iii) verbatim.  Then `white_hInnerCont_closed_final10` is applied.  The result is
the honest conditional entailment: GIVEN the three named geometric inputs, the whitened inner-pairing
interior-time continuity holds at the concrete curved witness.  ⚠ NOT `a₁ = R/6`. -/
theorem white_hInnerCont_final10_conditional (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
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
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (c δ₀ : ℝ) (hcδ : c < δ₀)
    (r ρ : ℝ) (hρr : ρ ≤ r) (hr : 0 ≤ r)
    (hreach : ∀ w : Point n, S w ⊆ Metric.closedBall w ρ)
    -- (C1) the SMALLNESS leg — an explicit contraction modulus `M < 1` on the window.
    (hcontrLip : ∀ z₀ : Point n, {w : Point n | z₀ ∈ frontier (S w)}.Nonempty →
        ∃ M : ℝ≥0, M < 1 ∧
          ∀ v ∈ Metric.sphere (0 : Point n) c,
            LipschitzOnWith M
              (fun u => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc u v - u) (Metric.closedBall z₀ r))
    -- (C2) the WIDTH leg — the uniform v-slot Lipschitz modulus of the clamp-based flow.
    (hvLip : ∀ z₀ : Point n, {w : Point n | z₀ ∈ frontier (S w)}.Nonempty →
        ∃ Cv : ℝ≥0,
          ∀ v ∈ Metric.sphere (0 : Point n) c, ∀ v' ∈ Metric.sphere (0 : Point n) c, ∀ w : Point n,
            dist (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
                  (coordClamp z₀ r w) v)
                (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
                  (coordClamp z₀ r w) v')
              ≤ (Cv : ℝ) * dist v v')
    -- (C3) the FRONTIER/INJECTIVITY leg — the null-frontier→sphere-image containment.
    (hfrontImg : ∀ z₀ : Point n, {w : Point n | z₀ ∈ frontier (S w)}.Nonempty →
        {w : Point n | z₀ ∈ frontier (S w)} ⊆
          {w : Point n | ∃ v ∈ Metric.sphere (0 : Point n) c,
            uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v = z₀})
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
    (R : ℝ) (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    (C_D : ℝ) (hCD0 : 0 ≤ C_D)
    (hdisp0 : ∀ v : Point n, ‖v‖ ≤ c →
        ‖uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v - v‖
          ≤ C_D * ‖v‖ * ‖v‖)
    (hclosclause : closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc 0 '' Metric.ball 0 c)
      ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.closedBall 0 c)
    (hbR : b * (1 + C_D * c) < R)
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) := by
  -- Reconstruct the opaque bundle `hflowTruncNear` from the three transparent geometric hypotheses.
  have hflowTruncNear : ∀ z₀ : Point n, {w : Point n | z₀ ∈ frontier (S w)}.Nonempty →
      ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
      (∀ v ∈ Metric.sphere (0 : Point n) c,
        ContractingWith Kc
          (fun w => z₀ -
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
                (coordClamp z₀ r w) v - coordClamp z₀ r w + w) + w)) ∧
      (∀ v ∈ Metric.sphere (0 : Point n) c, ∀ v' ∈ Metric.sphere (0 : Point n) c, ∀ w : Point n,
        dist (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
              (coordClamp z₀ r w) v)
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
              (coordClamp z₀ r w) v')
            ≤ (Cv : ℝ) * dist v v') ∧
      {w : Point n | z₀ ∈ frontier (S w)} ⊆
        {w : Point n | ∃ v ∈ Metric.sphere (0 : Point n) c,
          uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v = z₀} := by
    intro z₀ hne
    obtain ⟨M, hM1, hg⟩ := hcontrLip z₀ hne
    obtain ⟨Cv, hCv⟩ := hvLip z₀ hne
    refine ⟨M, Cv, hM1, ?_, hCv, hfrontImg z₀ hne⟩
    exact white_flowTruncNear_contr_clause_of_windowLip κ hκ hKc z₀ r c hr M hM1 hg
  exact white_hInnerCont_closed_final10 hn κ hκ hKc S a b ha hab C hC0 hpkg hEmeas hWmeas
    wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval Wg hagree c δ₀ hcδ r ρ hρr hreach hflowTruncNear
    hSopen hSreach hspec R h0K hballS hballC C_D hCD0 hdisp0 hclosclause hbR Uwin hU1

end QIQTH.WhiteHflowTruncConditional

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHflowTruncConditional
#check @white_hInnerCont_final10_conditional
#print axioms white_hInnerCont_final10_conditional
end AxiomChecks
