/-
  WhiteHInnerContGeom — J4-706: THE GATE-THREADING.  The whitened inner-pairing time-continuity with
  the `htermBox` carry DISCHARGED in-line via `WhiteHtermBoxUncond.white_htermBox_unconditional_k`
  (banked 71460d9e), so the composed continuity carries ONLY the labelled geometry / vanishing / value
  certificates — NO `htermBox` hypothesis.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── CONTEXT.  `WhiteHInnerContTermBox.white_hInnerCont_modulo_termBox` (c86dbca6) reduced the whitened
     inner-pairing interior-time continuity to a SINGLE surviving carry — the whitened `iterE` termwise
     joint continuity `htermBox` (∀ `u ∈ U` ∀ `τ₀ ∈ (0,u]` ∀ `R'` ∀ `k`, `ContinuousOn (iterE E (k+1))`
     on `Icc (τ₀/2) u ×ˢ closedBall 0 R'`).  `WhiteHtermBoxUncond.white_htermBox_unconditional_k`
     (71460d9e) PRODUCES exactly this box — `∀ k` ∀ positive sub-window `Icc s₁ s₂` (`0 < s₁ ≤ s₂ ≤ 1`)
     ∀ radius `R'` — with the recursion carrier `hjoint` discharged by a `Nat.rec`, carrying only the
     labelled geometry / off-gate vanishing certificates.

  ── THE THREADING (option a, GATE-PARAMETRIC).  We do NOT re-derive the internal supplier
     co-instantiation (`white_hpkgBound_at_radius` / `white_tripleHEmeas_uniform` / value suppliers);
     that co-instantiation is EXACTLY `white_hInnerCont_modulo_termBox`'s own obtain-chain at the internal
     shared radius `c = min(δp,δS,δV,δW)/2`, and re-elaborating it verbatim risks whnf blow-up.  Instead we
     state the composed continuity GATE-PARAMETRICALLY — taking the co-instantiated data
     `{C, hpkg, hEmeas, hWmeas, wA, Cpre, A₀, A₁, hval}` and the labelled producer geometry certificates
     as hypotheses at an abstract gate `{S, a, b}` — and thread `white_htermBox_unconditional_k` (fed the
     SAME `{hpkg, hEmeas}` co-instantiation plus the geometry certs) into the `htermBox` slot via a
     window/radius SHAPE ADAPTER (`s₁ := τ₀/2`, `s₂ := u`, `R' := R'`; `u ≤ 1` from the window).  The
     `white_hInnerCont_modulo_termBox` STEP 1–3 (Levi joint continuity ⊕ witness-factor time continuity
     ⊕ the generic dominated-continuity builder) then compose verbatim.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `white_hInnerCont_of_geometry` — ★★★ the composed whitened inner-pairing interior-time continuity
      with `htermBox` DISCHARGED (via `white_htermBox_unconditional_k`), carrying ONLY the labelled
      certificate list below.  For gate-parametric `{S, a, b}`, the co-instantiated width-`whiteLam`
      pkg / S1 / value data, and the labelled geometry / off-gate vanishing certificates, the interior
      continuity of the whitened inner pairing holds on `Ioo 0 u`, ∀ `u ∈ Uwin` (`Uwin ⊆ (·,1]`).
    • `white_hEoffFirst_of_gateSubset` — the hEoffFirst SHARPENING: a CONCRETE off-gate first-argument
      vanishing at a NONEMPTY open `U`, from a uniform gate-containment `S w ⊆ closedBall 0 M` (∀ `w`),
      via `whiteGated_heatOp_zero_offGate` (gate-locally-off leg) — the `U = (closedBall 0 M)ᶜ` witness.

  ── HONEST RESIDUAL — THE FULL LABELLED CERTIFICATE LIST (NOT the conclusion, NOT a₁ = R/6; `htermBox` GONE).
    A. co-instantiated at the shared gate (the `white_hInnerCont_modulo_termBox` obtain-chain output):
       1. `C`, `hC0` — the width-`whiteLam` pkg constant + nonnegativity.
       2. `hpkg` — the capstone width-`whiteLam` pkg bound of the whitened gated witness `heatOp`.
       3. `hEmeas` — the whitened-defect S1 base measurability `tripleHEmeas`.
       4. `hWmeas` — the whitened gated-witness value strong measurability.
       5. `wA, Cpre, A₀, A₁` (+ nonneg) and `hval` — the whitened witness value Gaussian domination.
    B. genuinely-external labelled geometry / vanishing certificates (the producer inputs):
       6. `Wg`, `hagree` — the on-gate chart agreement (Gap-A reparam).
       7. `R, c, δ₀, cA, δ₀A`, `hRpos` — the bounded van-Vleck reach + gate radii.
       8. `Uoff, hUopen, hEoffFirst, hcover` — the off-gate first-argument vanishing + open cover.
       9. `h0K, hSopen, hballS, hcδ, hspec, hballC` — the base-`0` flow-ball geometry at reach `R`.
      10. `hcδA, hgeom` — the Gap-A base-`w` ∀-`q∈Kset` flow-ball geometry at reach `R`.
    C. window: `Uwin`, `hU1 : ∀ u ∈ Uwin, u ≤ 1`.

  ⚠  HONEST FIREWALL.  Gate-threading ONLY — the `htermBox` residue of J4-699 discharged by the J4-705
  induction tie, carrying the labelled certificate list.  THIS FILE IS **NOT** `a₁ = R/6` and proves
  NOTHING about `R/6` (`R/6` is a labelled carrier, untouched).  No `sorry`, no `admit`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.
-/
import Mathlib
import QIQTH.WhiteHInnerContTermBox
import QIQTH.WhiteHtermBoxUncond

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.CurvedA1CenterAmp
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteAnnulus QIQTH.WhiteGated
open QIQTH.WhiteBridge QIQTH.WhiteHBdomAllRows QIQTH.WhiteS1C
open QIQTH.WhiteHInnerContFinal
open QIQTH.WhiteLeviConvergenceTrio
open QIQTH.WhiteLeviMajorWire
open QIQTH.WhiteHcontWitnessFactor
open QIQTH.CurvedRNCVanVleckBound
open QIQTH.LeviSeries
open QIQTH.GaussianWidthTolerant
open QIQTH.WhiteHtermBoxUncond
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteHInnerContGeom

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ the composed continuity, `htermBox` DISCHARGED via the induction tie.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_of_geometry` — `htermBox` DISCHARGED, carrying ONLY labelled certificates.**
    For gate-parametric `{S, a, b}`, the co-instantiated width-`whiteLam` pkg / S1 / value data
    `{C, hpkg, hEmeas, hWmeas, wA, Cpre, A₀, A₁, hval}` (exactly the `white_hInnerCont_modulo_termBox`
    obtain-chain output at the shared internal gate), and the labelled producer geometry / off-gate
    vanishing certificates, the whitened inner-pairing interior-time continuity holds on `Ioo 0 u`,
    ∀ `u ∈ Uwin` (`Uwin ⊆ (·,1]`).  The `htermBox` carry of J4-699 is DISCHARGED in-line by
    `WhiteHtermBoxUncond.white_htermBox_unconditional_k` (the J4-705 `Nat.rec` induction tie) fed the
    SAME `{hpkg, hEmeas}` co-instantiation plus the geometry certs, adapted to the box shape by the
    window/radius adapter (`s₁ := τ₀/2`, `s₂ := u`, `R' := R'`; `u ≤ 1` from `hU1`).  STEP 1–3 (Levi
    joint continuity ⊕ witness-factor time continuity ⊕ the generic dominated-continuity builder)
    compose verbatim from `white_hInnerCont_modulo_termBox`.
    ⚠ CONDITIONAL on the labelled certificate list (file header A/B/C).  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_of_geometry (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    -- A. co-instantiated width-`whiteLam` pkg / S1 / value data (shared gate obtain-chain output)
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
    -- B. genuinely-external labelled geometry / vanishing certificates
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (R c δ₀ cA δ₀A : ℝ) (hRpos : 0 < R)
    (Uoff : Set (Point n)) (hUopen : IsOpen Uoff)
    (hEoffFirst : ∀ (τ : ℝ) (z w : Point n), z ∈ Uoff →
        whiteDefectKernel κ hκ hKc S a b τ z w = 0)
    (hcover : ∀ R' : ℝ, Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ Uoff)
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
    (hcδA : cA < δ₀A)
    (hgeom : ∀ q ∈ Kset,
        IsOpen (S q)
      ∧ Metric.closedBall (0 : Point n) R ⊆ S q
      ∧ (∀ v : Point n, ‖v‖ < δ₀A →
          (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
          ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q)
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v))
      ∧ Metric.closedBall (0 : Point n) R ⊆
          uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
            Metric.ball (0 : Point n) cA)
    -- C. window
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) := by
  have hlam0 : (0 : ℝ) < whiteLam κ hκ hKc :=
    lt_of_lt_of_le two_pos (whiteLam_ge_two κ hκ hKc)
  -- DISCHARGE `htermBox` via the J4-705 induction tie, fed the SAME co-instantiation + geometry.
  have hprodK : ∀ k : ℕ, ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      ContinuousOn
        (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') :=
    white_htermBox_unconditional_k hn κ hκ hKc S a b C (whiteLam κ hκ hKc) hC0
      (whiteLam_ge_two κ hκ hKc) Wg hagree R c δ₀ cA δ₀A hRpos
      Uoff hUopen hEoffFirst hcover h0K hSopen hballS hcδ hspec hballC hcδA hgeom hpkg hEmeas
  -- SHAPE ADAPTER: `s₁ := τ₀/2`, `s₂ := u`, `R' := R'`; `u ≤ 1` from the window.
  have htermBox : ∀ u ∈ Uwin, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) u, ∀ R' : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n =>
          iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) u ×ˢ Metric.closedBall (0 : Point n) R') := by
    intro u hu τ₀ hτ₀ R' k
    have h1 : 0 < τ₀ / 2 := by linarith [hτ₀.1]
    have h2 : τ₀ / 2 ≤ u := by linarith [hτ₀.1, hτ₀.2]
    exact hprodK k (τ₀ / 2) u R' h1 h2 (hU1 u hu)
  -- STEP 1: reduce the Levi joint continuity to the (now proved) `htermBox`.
  have hJoint : ∀ u ∈ Uwin, ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (whiteDefectKernel κ hκ hKc S a b) p.1 p.2 0)
      (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (Point n))) :=
    white_leviJoint_window_modulo_termBox κ hκ hKc S a b C
      (whiteLam κ hκ hKc) hC0 (whiteLam_ge_two κ hκ hKc) Uwin hpkg hEmeas htermBox
  -- STEP 1b: the width-`whiteLam` Levi row bound (B-slot).
  obtain ⟨C_L, hC_L, hBdom⟩ :=
    white_leviSeries_full_row κ hκ hKc S a b C (whiteLam κ hκ hKc)
      hC0 (whiteLam_ge_two κ hκ hKc) hpkg hEmeas
  -- STEP 1c: the interior slice measurability `hmeas` (witness slice × Levi `z`-slice).
  have hmeas : ∀ u ∈ Uwin, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable
        (fun z => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
          * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
        (volume : Measure (Point n)) := by
    intro u hu s₀ hs₀
    refine Filter.eventually_of_mem (Ioo_mem_nhds hs₀.1 hs₀.2) (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have hs1 : s ≤ 1 := le_of_lt (lt_of_lt_of_le hs.2 (hU1 u hu))
    have hAslice : AEStronglyMeasurable
        (fun z : Point n => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z)
        (volume : Measure (Point n)) :=
      (hWmeas.comp_measurable
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    have hBslice : AEStronglyMeasurable
        (fun z : Point n => leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
        (volume : Measure (Point n)) :=
      white_leviSeries_zmeas κ hκ hKc S a b C (whiteLam κ hκ hKc) hC0
        (whiteLam_ge_two κ hκ hKc) hpkg hEmeas s hs0 hs1 0
    exact hAslice.mul hBslice
  -- STEP 2: the `hcont` slot = discharged witness factor × extracted Levi time-continuity.
  have hcont : ∀ u ∈ Uwin, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
      ContinuousAt
        (fun s => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
          * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0) s₀ := by
    intro u hu s₀ hs₀
    refine Filter.Eventually.of_forall (fun z => ?_)
    exact (whiteWitness_time_continuousAt κ hκ hKc S a b u z hs₀.1 hs₀.2).mul
      (leviTimeCont_of_jointStrip (whiteDefectKernel κ hκ hKc S a b) u
        (hJoint u hu) hs₀.1 hs₀.2 z)
  -- STEP 3: the generic builder composes value + Levi B-slot + `hmeas` + `hcont`.
  exact QIQTH.CurvedA1HContDomGen.hInnerCont_of_dominations_generic
    (whiteGatedWitness κ hκ hKc S a b)
    (leviSeries (whiteDefectKernel κ hκ hKc S a b))
    1 Uwin hU1 wA (whiteLam κ hκ hKc) hwA0 hlam0 Cpre A₀ A₁ C_L hCpre0 hA₀0 hA₁0 hC_L
    hval (fun s hs hsT z y => hBdom s z y hs hsT) hmeas hcont

/-! ###############################################################################
    ### the hEoffFirst SHARPENING — a NONEMPTY off-gate first-argument vanishing.
    ############################################################################### -/

/-- **`white_hEoffFirst_of_gateSubset` — the hEoffFirst sharpening at a NONEMPTY `U`.**
    If EVERY gate value is uniformly contained in a bounded ball `S w ⊆ closedBall 0 M`, then the
    complement `U = (closedBall 0 M)ᶜ` is a NONEMPTY open off-gate region on which the whitened defect
    kernel vanishes in its FIRST spatial argument: `z ∈ U → whiteDefectKernel κ hκ hKc S a b τ z w = 0`.
    The vanishing is the gate-locally-off leg of `whiteGated_heatOp_zero_offGate` (`{p' | p' ∉ S w}` is
    a neighbourhood of `z` because `U` is open and `U ⊆ {p' | p' ∉ S w}`), transported through
    `whiteDefectKernel_eq` (in-window) / the off-window `if_neg` branch.
    ⚠ CONDITIONAL on the uniform gate-containment `hMbound`.  NOT `a₁ = R/6`. -/
theorem white_hEoffFirst_of_gateSubset (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b M : ℝ)
    (hMbound : ∀ w : Point n, S w ⊆ Metric.closedBall (0 : Point n) M) :
    ∀ (τ : ℝ) (z w : Point n), z ∈ (Metric.closedBall (0 : Point n) M)ᶜ →
      whiteDefectKernel κ hκ hKc S a b τ z w = 0 := by
  intro τ z w hz
  -- `{p' | p' ∉ S w}` is a neighbourhood of `z`: `z` sits in the open complement of `closedBall 0 M ⊇ S w`.
  have hsub : (Metric.closedBall (0 : Point n) M)ᶜ ⊆ {p' : Point n | p' ∉ S w} :=
    fun x hx hxS => hx (hMbound w hxS)
  have hopen : IsOpen (Metric.closedBall (0 : Point n) M)ᶜ :=
    Metric.isClosed_closedBall.isOpen_compl
  have hoff : {p' : Point n | p' ∉ S w} ∈ nhds z :=
    Filter.mem_of_superset (hopen.mem_nhds hz) hsub
  by_cases hτ : 0 < τ ∧ τ ≤ 1
  · rw [whiteDefectKernel_eq κ hκ hKc S a b hτ.1 hτ.2 z w]
    exact whiteGated_heatOp_zero_offGate κ hκ hKc S a b τ z w (Or.inr hoff)
  · simp only [whiteDefectKernel, if_neg hτ]

#check @white_hInnerCont_of_geometry
#check @white_hEoffFirst_of_gateSubset

end QIQTH.WhiteHInnerContGeom

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHInnerContGeom
#print axioms white_hInnerCont_of_geometry
#print axioms white_hEoffFirst_of_gateSubset
end AxiomChecks
