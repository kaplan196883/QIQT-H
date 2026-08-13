/-
  WhiteGapBAssembly — J4-704 (Gap-B + per-level hcont ASSEMBLY).  Discharges the `hcontIter`
  (Gap-B) slot of `InnerEngineRecursion.innerStep_cont_ae` at the whitened kernel as pure WIRING of
  the recursion's own previous-level joint continuity, then assembles the three INNER carries
  (S-dom ⊕ Gap-A ⊕ Gap-B) into the per-level convolution-step joint continuity `hcont`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── ★★ THE Gap-B VERDICT (the finding).  The `hcontIter` slot
        `∀ᵐ u, ∀ᵐ w, ContinuousOn (fun p => iterE E k (p.1·u) w 0) (Icc t₁ t₂ ×ˢ closedBall 0 R)`
     is NOT an analytic wall — it is WIRING.  The integrand depends on `p` ONLY through the rescaled
     TIME `p.1·u` (the second spatial arg is the FIXED `w`, the third is `0`), so it is the map
        `p ↦ (p.1·u, w) ↦ iterE E k (p.1·u) w 0 = (fun q => iterE E k q.1 q.2 0) ∘ (fun p => (p.1·u, w))`.
     For FIXED `u > 0` the affine time map lands `Icc t₁ t₂` inside `Icc (t₁·u) (t₂·u)` (a POSITIVE
     window, bounded away from `0`), and `w ∈ closedBall 0 ‖w‖`.  Hence the JOINT `(time, first-spatial)`
     continuity of `iterE E k` on `Icc (t₁·u) (t₂·u) ×ˢ closedBall 0 R'` — at ANY radius `R'` (take
     `R' = ‖w‖`) — composes through the continuous `p ↦ (p.1·u, w)` to give the slot.  That joint
     continuity is EXACTLY the recursion's OWN output at the previous level (`iterE E k` with
     `k = (k−1)+1`, the `htermBox` at index `k−1`), re-based to the rescaled positive-time window.  So
     Gap-B = re-indexing the recursion carrier, NOT new analysis.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a purely
  TOPOLOGICAL wiring brick (`ContinuousOn.comp` of the recursion carrier through an affine time map) +
  a carry-composition into `innerStep_cont_ae`.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `hcontIter_of_jointCont_fixed_u` — the Gap-B wire at fixed `u > 0`: from the previous-level
      joint continuity of `iterE E k` on the rescaled positive-time window (∀ radius `R'`), the
      `∀ w` (hence a.e.-`w`) time-continuity slot, by `ContinuousOn.comp`.
    * `white_hcontIter_ae` — the a.e.-`u` / a.e.-`w` `hcontIter` slot, from the `u`-family of the
      recursion carrier (window-uniform on `Ioc 0 1`).
    * `white_innerStep_hcont` — ★★★ the per-level convolution-step joint continuity `hcont` (the exact
      `hcont` argument of `iterE_succ_jointContinuousOn_wired` / `white_htermBox_of_flowBall_extend_hcont`),
      assembled by `innerStep_cont_ae` from the three INNER carries: S-dom (`white_hSdom`), Gap-A
      (`white_hcontE_ae_of_baseGeom`), Gap-B (`white_hcontIter_ae`), with the integrand measurability
      DERIVED from `hEmeas` (`whiteDefectKernel_stronglyMeasurable`).

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT a₁ = R/6).
    * `hjoint` — the recursion carrier: the previous-level joint continuity of `iterE (whiteDefectKernel …) k`
      on the rescaled positive-time window at ALL radii.  This is the `htermBox` at index `k−1`; closing
      the full tower ties `hjoint(k)` to the output at `k−1` by induction (via
      `WhiteHBaseExtend.white_htermBox_of_flowBall_extend_hcont`).
    * `hgeom` — the Gap-A base-`w` flow-ball geometry certificate (from `WhiteHcontEAssembly`).
    * `hpkg`, `hEmeas` — the standard labelled whitened carries.

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteSdomInner
import QIQTH.WhiteHcontEAssembly
import QIQTH.InnerEngineRecursion

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp
open QIQTH.ExpMap QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open QIQTH.InnerEngineRecursion QIQTH.WhiteSdomInner QIQTH.WhiteHcontEAssembly
open scoped Topology

namespace QIQTH.WhiteGapBAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## The Gap-B wire — `hcontIter` from the recursion's own previous-level carrier.
    ############################################################################### -/

/-- **`hcontIter_of_jointCont_fixed_u` — THE Gap-B WIRE (fixed `u`).**  For a FIXED `u > 0`, from the
    previous-level joint `(time, first-spatial)` continuity of `iterE E k` on the rescaled POSITIVE-time
    window `Icc (t₁·u) (t₂·u) ×ˢ closedBall 0 R'` — at ANY radius `R'` — the `hcontIter` inner slot
        `∀ w, ContinuousOn (fun p => iterE E k (p.1·u) w 0) (Icc t₁ t₂ ×ˢ closedBall 0 R)`,
    by `ContinuousOn.comp` of the carrier (at `R' = ‖w‖`) through the continuous affine time map
    `p ↦ (p.1·u, w)` (which lands the box `Icc t₁ t₂` in `Icc (t₁·u) (t₂·u)` since `u > 0`, and `w` in
    `closedBall 0 ‖w‖`).  Pure wiring; NOT `a₁ = R/6`. -/
theorem hcontIter_of_jointCont_fixed_u
    (E : ℝ → Point n → Point n → ℝ) (k : ℕ) (t₁ t₂ R u : ℝ) (hu0 : 0 < u)
    (hjoint : ∀ R' : ℝ, ContinuousOn (fun q : ℝ × Point n => iterE E k q.1 q.2 0)
        (Set.Icc (t₁ * u) (t₂ * u) ×ˢ Metric.closedBall (0 : Point n) R')) :
    ∀ w : Point n, ContinuousOn (fun p : ℝ × Point n => iterE E k (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro w
  have hcomp : (fun p : ℝ × Point n => iterE E k (p.1 * u) w 0)
      = (fun q : ℝ × Point n => iterE E k q.1 q.2 0) ∘ (fun p : ℝ × Point n => (p.1 * u, w)) := rfl
  rw [hcomp]
  refine (hjoint ‖w‖).comp
    ((continuous_fst.mul continuous_const).prodMk continuous_const).continuousOn ?_
  intro p hp
  obtain ⟨hps, -⟩ := hp
  have hps1 : t₁ ≤ p.1 := hps.1
  have hps2 : p.1 ≤ t₂ := hps.2
  refine ⟨⟨mul_le_mul_of_nonneg_right hps1 hu0.le,
    mul_le_mul_of_nonneg_right hps2 hu0.le⟩, ?_⟩
  simp only [Metric.mem_closedBall, dist_zero_right, le_refl]

/-- **`white_hcontIter_ae` — the a.e.-`u` / a.e.-`w` `hcontIter` slot.**  From the `u`-family of the
    recursion carrier (the previous-level joint continuity of `iterE E k` on the rescaled positive-time
    window at ALL radii, window-uniform over `u ∈ Ioc 0 1`), the EXACT `hcontIter` argument of
    `InnerEngineRecursion.innerStep_cont_ae`.  The inner leg is proved for EVERY `w` (`ae_of_all`,
    stronger than a.e.-`w`).  NOT `a₁ = R/6`. -/
theorem white_hcontIter_ae
    (E : ℝ → Point n → Point n → ℝ) (k : ℕ) (t₁ t₂ R : ℝ)
    (hjoint : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ R' : ℝ,
        ContinuousOn (fun q : ℝ × Point n => iterE E k q.1 q.2 0)
          (Set.Icc (t₁ * u) (t₂ * u) ×ˢ Metric.closedBall (0 : Point n) R')) :
    ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ∀ᵐ w ∂(volume : Measure (Point n)),
        ContinuousOn (fun p : ℝ × Point n => iterE E k (p.1 * u) w 0)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact ae_of_all _ (hcontIter_of_jointCont_fixed_u E k t₁ t₂ R u hu.1 (hjoint u hu.1 hu.2))

/-! ###############################################################################
    ## ★★★ The per-level convolution-step joint continuity `hcont` (S-dom ⊕ Gap-A ⊕ Gap-B).
    ############################################################################### -/

/-- **★★★ `white_innerStep_hcont` — THE PER-LEVEL `hcont`.**  The a.e.-`u` inner convolution-step joint
    continuity at the whitened defect kernel — the EXACT `hcont` argument consumed by
    `IterEEngineWiring.iterE_succ_jointContinuousOn_wired` /
    `WhiteHBaseExtend.white_htermBox_of_flowBall_extend_hcont`:
        `∀ᵐ u, ContinuousOn (fun p => ∫ w, whiteDefectKernel … (p.1−p.1·u) p.2 w
             · iterE (whiteDefectKernel …) k (p.1·u) w 0) (Icc t₁ t₂ ×ˢ closedBall 0 R)`,
    assembled by `InnerEngineRecursion.innerStep_cont_ae` from the THREE INNER carries:
      • S-dom — `white_hSdom` (the `p`-uniform integrable spatial dominator);
      • Gap-A — `white_hcontE_ae_of_baseGeom` (E's reparam base continuity, geometry `hgeom`);
      • Gap-B — `white_hcontIter_ae` (the recursion carrier `hjoint`, re-indexed by the Gap-B wire),
    with the integrand measurability DERIVED from `hEmeas` (`whiteDefectKernel_stronglyMeasurable`).
    ⚠ CONDITIONAL on `{hpkg, hEmeas, hgeom, hagree, hjoint}`.  NOT `a₁ = R/6`. -/
theorem white_innerStep_hcont (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC0 : 0 ≤ C) (hlam : 0 < lam)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R c δ₀ : ℝ) (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) (hR : 0 < R) (ht₂ : t₂ ≤ 1) (hcδ : c < δ₀)
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
            Metric.ball (0 : Point n) c)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    (k : ℕ) (hk : 1 ≤ k)
    (hjoint : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ R' : ℝ,
        ContinuousOn
          (fun q : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) k q.1 q.2 0)
          (Set.Icc (t₁ * u) (t₂ * u) ×ˢ Metric.closedBall (0 : Point n) R')) :
    ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n =>
          ∫ w, whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
            * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  obtain ⟨bnd, hbnd_int, hbound⟩ :=
    white_hSdom κ hκ hKc S a b C lam hC0 hlam hpkg hEmeas k hk t₁ t₂ R ht₁ ht₁₂ hR
  exact innerStep_cont_ae (whiteDefectKernel κ hκ hKc S a b) hk t₁ t₂ R bnd
    (whiteDefectKernel_stronglyMeasurable κ hκ hKc S a b hEmeas)
    hbnd_int hbound
    (white_hcontE_ae_of_baseGeom hn κ hκ hKc S a b Wg hagree t₁ t₂ R c δ₀ ht₁ ht₂ hcδ hgeom)
    (white_hcontIter_ae (whiteDefectKernel κ hκ hKc S a b) k t₁ t₂ R hjoint)

#check @hcontIter_of_jointCont_fixed_u
#check @white_hcontIter_ae
#check @white_innerStep_hcont

end QIQTH.WhiteGapBAssembly

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteGapBAssembly
#print axioms hcontIter_of_jointCont_fixed_u
#print axioms white_hcontIter_ae
#print axioms white_innerStep_hcont
end AxiomChecks
