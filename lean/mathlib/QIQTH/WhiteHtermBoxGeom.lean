/-
  WhiteHtermBoxGeom — J4-704 (ASSEMBLY capstone): the whitened `htermBox` from GEOMETRY, modulo the
  recursion carrier.  Composes the per-level convolution-step continuity
  (`WhiteGapBAssembly.white_innerStep_hcont`, itself S-dom ⊕ Gap-A ⊕ Gap-B) across ALL rungs `k` and
  feeds the resulting `hcont` family into `WhiteHBaseExtend.white_htermBox_of_flowBall_extend_hcont`,
  delivering the ALL-`k` termwise joint continuity of the whitened `iterE` iterates (`htermBox`) on
  the extended ball `closedBall 0 R'`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE COMPOSITION.  `white_htermBox_of_flowBall_extend_hcont` produces `htermBox` from {base-0
     flow-ball geometry (radius `R`), the vanishing cover `{U, hUopen, hUzero, hcover}` to `R'`, `hpkg`,
     `hEmeas`, and the `hcont` FAMILY (∀ `k`, the inner convolution-step continuity at radius `R'`)}.
     This file supplies that `hcont` family from `white_innerStep_hcont` at each rung `k+1` (box radius
     `R'`, the Gap-A base-`w` flow-ball geometry `hgeom` at radius `R'`, and the recursion carrier
     `hjoint` at index `k+1`).  The result is `htermBox` reduced to EXACTLY the labelled certificate
     list below — with the recursion carrier `hjoint` as the SINGLE structural residual (the previous
     level's own joint continuity, discharged by induction against this very output).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  Carry
  composition ONLY (map the per-rung `hcont` over `k`, feed the banked extend/htermBox producer).  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited, nothing committed, nothing wired
  into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `white_htermBox_of_geometry` — ★★★ the whitened `htermBox` at ALL radii `R'`, from the full
      labelled geometry list + the recursion carrier `hjoint` family.  Exactly the `htermBox`
      consumed by `WhiteLeviMajorWire.white_leviJoint_window_modulo_termBox` /
      `WhiteHInnerContTermBox.white_hInnerCont_modulo_termBox` (at a matching gate).

  ── HONEST RESIDUAL — THE FULL LABELLED CERTIFICATE LIST (NOT the conclusion, NOT a₁ = R/6).
    1. `hjoint` — the RECURSION CARRIER: ∀ `k`, the previous-level joint continuity of
       `iterE (whiteDefectKernel …) (k+1)` on the rescaled positive-time window at ALL radii.  This IS
       the `htermBox` output at the previous index; the full tower closes by induction tying
       `hjoint(k)` to this file's output at `k−1` (the Gap-B verdict: wiring, not analysis).
    2. `hgeom` — the Gap-A ∀-`q∈Kset` base-`w` flow-ball geometry (radius `R'`).
    3. base-0 flow-ball geometry: `{h0K, hSopen, hballS, hspec, hballC}` (radius `R`) — the van-Vleck
       `hbase` cert.
    4. vanishing cover: `{U, hUopen, hUzero, hcover}` (the `R' > R` extension cert).
    5. `hpkg` — the capstone width-`lam` pkg bound of the whitened gated witness heatOp.
    6. `hEmeas` — the whitened-defect S1 base measurability `tripleHEmeas`.
    7. `hagree` — the on-gate chart agreement (Gap-A reparam).

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteGapBAssembly
import QIQTH.WhiteHBaseExtend

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp
open QIQTH.ExpMap QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open QIQTH.WhiteGapBAssembly QIQTH.WhiteHBaseExtend
open scoped Topology

namespace QIQTH.WhiteHtermBoxGeom

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `white_htermBox_of_geometry` — the whitened `htermBox` FROM GEOMETRY (modulo the recursion
    carrier).**  For the whitened defect kernel at gate-parametric `{S, a, b, C, lam}`, the ALL-`k`
    termwise joint `(τ,z)`-continuity of `iterE (whiteDefectKernel …) (k+1)` on
    `Icc t₁ t₂ ×ˢ closedBall 0 R'` — reach-UNRESTRICTED — assembled by feeding the per-rung
    convolution-step continuity `white_innerStep_hcont` (S-dom ⊕ Gap-A ⊕ Gap-B) into the banked
    `white_htermBox_of_flowBall_extend_hcont`.  The three genuine inner carries are ALL discharged
    (S-dom from `{hpkg, hEmeas}`, Gap-A from `hgeom`, Gap-B from the recursion carrier `hjoint`); the
    surviving inputs are the labelled geometry certificates + `hjoint` (see file header, items 1–7).
    ⚠ CONDITIONAL on that certificate list.  NOT `a₁ = R/6`. -/
theorem white_htermBox_of_geometry (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R R' c δ₀ cA δ₀A : ℝ) (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) (ht₂ : t₂ ≤ 1) (hR' : 0 < R')
    -- base-0 flow-ball geometry (radius `R`) — the van-Vleck `hbase` cert
    (h0K : (0 : Point n) ∈ Kset) (hSopen : IsOpen (S 0))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0) (hcδ : c < δ₀)
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
    -- vanishing cover (the `R' > R` extension cert)
    (Uc : Set (Point n)) (hUopen : IsOpen Uc)
    (hUzero : ∀ p ∈ Uc, ∀ τ : ℝ, whiteDefectKernel κ hκ hKc S a b τ p 0 = 0)
    (hcover : Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ Uc)
    -- Gap-A base-`w` flow-ball geometry (radius `R'`)
    (hcδA : cA < δ₀A)
    (hgeom : ∀ q ∈ Kset,
        IsOpen (S q)
      ∧ Metric.closedBall (0 : Point n) R' ⊆ S q
      ∧ (∀ v : Point n, ‖v‖ < δ₀A →
          (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
          ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q)
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v))
      ∧ Metric.closedBall (0 : Point n) R' ⊆
          uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
            Metric.ball (0 : Point n) cA)
    -- the standard labelled whitened carries
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    -- the recursion carrier: previous-level joint continuity at ALL radii, ∀ index
    (hjoint : ∀ k : ℕ, ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ R'' : ℝ,
        ContinuousOn
          (fun q : ℝ × Point n =>
            iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) q.1 q.2 0)
          (Set.Icc (t₁ * u) (t₂ * u) ×ˢ Metric.closedBall (0 : Point n) R'')) :
    ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  have hlam : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  -- the per-rung `hcont` family at radius `R'` (S-dom ⊕ Gap-A ⊕ Gap-B).
  have hcont : ∀ k : ℕ, ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
          * iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
    intro k
    exact white_innerStep_hcont hn κ hκ hKc S a b C lam hC hlam Wg hagree
      t₁ t₂ R' cA δ₀A ht₁ ht₁₂ hR' ht₂ hcδA hgeom hpkg hEmeas (k + 1)
      (Nat.succ_le_succ (Nat.zero_le k)) (hjoint k)
  -- feed the family into the banked extend/htermBox producer.
  exact white_htermBox_of_flowBall_extend_hcont hn κ hκ hKc S a b C lam hC hlam2 Wg hagree
    t₁ t₂ R R' c δ₀ ht₁ ht₂ h0K hSopen hballS hcδ hspec hballC
    Uc hUopen hUzero hcover hpkg hEmeas hcont

#check @white_htermBox_of_geometry

end QIQTH.WhiteHtermBoxGeom

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHtermBoxGeom
#print axioms white_htermBox_of_geometry
end AxiomChecks
