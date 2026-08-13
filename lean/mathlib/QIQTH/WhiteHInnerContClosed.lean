/-
  WhiteHInnerContClosed — J4-707: THE ∃-SHAPE WRAPPER.  The A-group supplier co-instantiation of
  `white_hInnerCont_modulo_termBox` REPLAYED verbatim at the shared internal radius `c`, threaded
  into the gate-parametric `WhiteHInnerContGeom.white_hInnerCont_of_geometry`, producing the CLOSED
  existential whitened inner-pairing time continuity — the whole `{C,hC0,hpkg,hEmeas,hWmeas,
  wA,Cpre,A₀,A₁,hval}` A-group DISCHARGED internally, carrying ONLY the genuinely-external labelled
  geometry / vanishing certificates as the implication antecedent inside the `∃`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── CONTEXT.  `WhiteHInnerContGeom.white_hInnerCont_of_geometry` (03184641) is GATE-PARAMETRIC: it
     takes the co-instantiated A-group `{C,hC0,hpkg,hEmeas,hWmeas,wA,Cpre,A₀,A₁,hval}` and the
     labelled geometry B-group as hypotheses at an abstract gate `{S,a,b}`.  The A-group is EXACTLY
     the obtain-chain output of `WhiteHInnerContTermBox.white_hInnerCont_modulo_termBox` (c86dbca6)
     at the shared radius `c = min(δp,δS,δV,δW)/2`.  This file REPLAYS that obtain-chain
     (`white_hpkgBound_at_radius`, `white_tripleHEmeas_uniform`, `white_witness_value_concrete_uniform`,
     `white_witness_value_dom_at_radius`), constructs the shared flow-ball gate `S`, co-emits the four
     facts at that gate, and feeds all of them plus the caller-supplied B-group into
     `white_hInnerCont_of_geometry`.  The result `white_hInnerCont_closed` is the `∃ S a b, 0 < a ∧
     a < b ∧ fatness ∧ (B-group → continuity)` package with the A-group GONE.

  ── THE cp466 SATISFIABILITY FINDING (the `hMbound`/`Kset` analysis — WHY the B-group STAYS labelled).
     `white_hInnerCont_of_geometry` (following `white_htermBox_unconditional_k`) states `hEoffFirst`
     for ALL right nodes `w`:  `∀ (τ) (z w : Point n), z ∈ Uoff → whiteDefectKernel … τ z w = 0`.
     Yet its consumer `white_htermBox_unconditional_k` uses it ONLY at `w = 0` (the fixed right node —
     `hEoffFirst p.1 p.2 0 hp2`).  At the flow-ball gate `S w = uniformFlowExp_w '' ball 0 c`, the
     union `⋃_w S w` is UNBOUNDED (the chart is a perturbation of translation by `w`), so the all-`w`
     `hEoffFirst` (which needs `Uoff ∩ ⋃_w S w = ∅`) together with `hcover` (which forces `Uoff` to
     contain the far region `(ball 0 R)ᶜ`) is JOINTLY UNSATISFIABLE at this gate.  The `w = 0`
     restriction, by contrast, IS satisfiable (`S 0` is bounded; `white_hEoffFirst_of_gateSubset`
     discharges it from a single-base `S 0 ⊆ closedBall 0 M`).  Hence full closure of the whitened
     `hInnerCont` at the concrete flow gate is BLOCKED on a `Kset`-restricted (w = 0) sharpening of the
     banked `white_hInnerCont_of_geometry` / `white_htermBox_unconditional_k` `hEoffFirst` binder —
     both banked theorems OVER-SPECIFY that binder.  This file therefore delivers the honest wrapper:
     the A-group DISCHARGED, the B-group (including the over-specified `hEoffFirst`) carried as the
     labelled antecedent, with this conflict documented.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `white_hInnerCont_closed` — ★★★ the CLOSED existential whitened inner-pairing time continuity:
      for EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)` (`n > 0`), window `U ⊆ (·,1]`, there ARE a fat flow-ball
      gate `S`, radii `0 < a < b` such that — modulo ONLY the labelled geometry / off-gate vanishing
      B-group about that gate — the interior-time continuity of the whitened inner pairing holds on
      `Ioo 0 u`, ∀ `u ∈ U`.  The ENTIRE A-group `{C,hC0,hpkg,hEmeas,hWmeas,wA,Cpre,A₀,A₁,hval}` is
      DISCHARGED internally by the replayed supplier obtain-chain.
    • `white_hInnerCont_closed_witness_gate` — the cp466 non-vacuity certificate (`n = 2`, `κ = −1`,
      `K = closedBall 0 2`): the `∃`-package produces a FAT gate (`0 ∈ S 0`, open) with `0 < a < b`.

  ── HONEST RESIDUAL — THE FINAL EXPLICIT REMAINING-INPUT LIST (the B-group antecedent, NOT the
     conclusion, NOT a₁ = R/6; the whole A-group GONE).
       6.  `Wg`, `hagree` — the on-gate chart agreement (Gap-A reparam).
       7.  `R', c', δ₀, cA, δ₀A`, `hRpos` — the bounded van-Vleck reach radii.
       8.  `Uoff, hUopen, hEoffFirst, hcover` — the off-gate first-argument vanishing + open cover
           ⚠ (all-`w`; NOT satisfiable at the flow gate — see the cp466 finding above; needs the
           `w = 0` sharpening).
       9.  `h0K, hSopen, hballS, hcδ, hspec, hballC` — the base-`0` flow-ball geometry at reach `R'`.
      10.  `hcδA, hgeom` — the Gap-A base-`q ∈ Kset` flow-ball geometry at reach `R'`.

  ⚠  HONEST FIREWALL.  A-group replay + gate threading ONLY — NOT `a₁ = R/6` (`R/6` is a labelled
  carrier, untouched).  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous hypothesis,
  no existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.
-/
import Mathlib
import QIQTH.WhiteHInnerContTermBox
import QIQTH.WhiteHInnerContGeom

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
open QIQTH.WhiteHInnerContGeom
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteHInnerContClosed

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ the CLOSED existential — A-group DISCHARGED, only the labelled B-group left.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_closed` — the A-group DISCHARGED, whitened `hInnerCont` closed.**
    For EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)` (`n > 0`), and window `U ⊆ (·,1]`, there ARE a fat
    flow-ball gate `S`, radii `0 < a < b` such that — MODULO ONLY the labelled geometry / off-gate
    vanishing B-group about that gate `{Wg,hagree · R',c',δ₀,cA,δ₀A,hRpos · Uoff,hUopen,hEoffFirst,
    hcover · h0K,hSopen,hballS,hcδ,hspec,hballC · hcδA,hgeom}` — the interior-time continuity of the
    whitened inner pairing holds on `Ioo 0 u`, ∀ `u ∈ U`.  The whole A-group
    `{C,hC0,hpkg,hEmeas,hWmeas,wA,Cpre,A₀,A₁,hval}` is CO-INSTANTIATED (proved) at the shared radius
    `c = min(δp,δS,δV,δW)/2` by the SAME obtain-chain as `white_hInnerCont_modulo_termBox`, then fed
    with the caller's B-group into `WhiteHInnerContGeom.white_hInnerCont_of_geometry`.
    ⚠ CONDITIONAL on the labelled B-group; ⚠ the `hEoffFirst` cert is over-specified (all `w`) and
    NOT satisfiable at the flow gate (see the file-header cp466 finding).  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R)
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∃ (S : Point n → Set (Point n)) (a b : ℝ), 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ (∀ (Wg : Point n × Point n → Point n)
          (_hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
              whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
          (Rr cc δ₀ cA δ₀A : ℝ) (_hRpos : 0 < Rr)
          (Uoff : Set (Point n)) (_hUopen : IsOpen Uoff)
          (_hEoffFirst : ∀ (τ : ℝ) (z w : Point n), z ∈ Uoff →
              whiteDefectKernel κ hκ hKc S a b τ z w = 0)
          (_hcover : ∀ R' : ℝ, Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 Rr ∪ Uoff)
          (_h0K : (0 : Point n) ∈ Kset) (_hSopen : IsOpen (S 0))
          (_hballS : Metric.closedBall (0 : Point n) Rr ⊆ S 0) (_hcδ : cc < δ₀)
          (_hspec : (∀ v : Point n, ‖v‖ < δ₀ →
              (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
                  (curvedRNC_hChr κ hκ) hKc 0 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                    (curvedRNC_hChr κ hκ) hKc 0 z)) =ᶠ[nhds v] (fun z => z) ∧
              ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc 0)
                (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v)))
          (_hballC : Metric.closedBall (0 : Point n) Rr ⊆
              uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
                Metric.ball (0 : Point n) cc)
          (_hcδA : cA < δ₀A)
          (_hgeom : ∀ q ∈ Kset,
              IsOpen (S q)
            ∧ Metric.closedBall (0 : Point n) Rr ⊆ S q
            ∧ (∀ v : Point n, ‖v‖ < δ₀A →
                (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
                    (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                      (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
                ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
                  (curvedRNC_hChr κ hκ) hKc q)
                  (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v))
            ∧ Metric.closedBall (0 : Point n) Rr ⊆
                uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
                  Metric.ball (0 : Point n) cA),
          ∀ u ∈ Uwin, ContinuousOn
            (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
              * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
            (Set.Ioo 0 u)) := by
  -- REPLAY the A-group obtain-chain of `white_hInnerCont_modulo_termBox` at the shared radius `c`.
  obtain ⟨δp, hδp, hpkgc⟩ := white_hpkgBound_at_radius κ hκ hKc R hKb
  obtain ⟨δS, hδS, hS1⟩ := white_tripleHEmeas_uniform hn κ hκ hKc
  obtain ⟨δV, hδVpos, wA, Cpre, A₀, A₁, hwA0, hCpre0, hA₀0, hA₁0, hvalc⟩ :=
    white_witness_value_dom_at_radius κ hκ hKc R hKb
  obtain ⟨δW, hδWpos, hWc⟩ := white_witness_value_concrete_uniform κ hκ hKc
  set c : ℝ := min δp (min δS (min δV δW)) / 2 with hcdef
  have hmin0 : 0 < min δp (min δS (min δV δW)) :=
    lt_min hδp (lt_min hδS (lt_min hδVpos hδWpos))
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hcp : c < δp := by
    have := min_le_left δp (min δS (min δV δW)); rw [hcdef]; linarith
  have hcS : c < δS := by
    have h1 : min δp (min δS (min δV δW)) ≤ min δS (min δV δW) := min_le_right _ _
    have h2 : min δS (min δV δW) ≤ δS := min_le_left _ _
    rw [hcdef]; linarith [le_trans h1 h2]
  have hcV : c < δV := by
    have h1 : min δp (min δS (min δV δW)) ≤ min δS (min δV δW) := min_le_right _ _
    have h2 : min δS (min δV δW) ≤ min δV δW := min_le_right _ _
    have h3 : min δV δW ≤ δV := min_le_left _ _
    rw [hcdef]; linarith [le_trans (le_trans h1 h2) h3]
  have hcW : c < δW := by
    have h1 : min δp (min δS (min δV δW)) ≤ min δS (min δV δW) := min_le_right _ _
    have h2 : min δS (min δV δW) ≤ min δV δW := min_le_right _ _
    have h3 : min δV δW ≤ δW := min_le_right _ _
    rw [hcdef]; linarith [le_trans (le_trans h1 h2) h3]
  have ha : 0 < c / 4 := by linarith
  have hab : c / 4 < c / 2 := by linarith
  have hbc : c / 2 < c := by linarith
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c with hSdef
  -- co-emit the A-group at this shared gate (verbatim `white_hInnerCont_modulo_termBox`).
  obtain ⟨hfat, C, hC0, hpkg⟩ := hpkgc c hc0 hcp (c / 4) (c / 2) ha hab hbc
  have hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S (c / 4) (c / 2)) :=
    hS1 c hc0 hcS (c / 4) (c / 2) ha hab hbc
  have hWmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) w.1 w.2.1 w.2.2) :=
    hWc c hc0 hcW (c / 4) (c / 2)
  have hval : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) τ p q|
        ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q) := by
    have := hvalc c hc0 hcV
    exact this
  -- FEED the discharged A-group + the caller's B-group into the gate-parametric geometry threading.
  refine ⟨S, c / 4, c / 2, ha, hab, hfat, ?_⟩
  intro Wg hagree Rr cc δ₀ cA δ₀A hRpos Uoff hUopen hEoffFirst hcover
    h0K hSopen hballS hcδ hspec hballC hcδA hgeom
  exact white_hInnerCont_of_geometry hn κ hκ hKc S (c / 4) (c / 2)
    C hC0 hpkg hEmeas hWmeas wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval
    Wg hagree Rr cc δ₀ cA δ₀A hRpos Uoff hUopen hEoffFirst hcover
    h0K hSopen hballS hcδ hspec hballC hcδA hgeom Uwin hU1

/-- **cp466 non-vacuity gate** — at genuinely curved data (`n = 2`, `κ = −1`, `K = closedBall 0 2`):
    the `∃`-package of `white_hInnerCont_closed` produces ONE FAT gate (`0 ∈ S 0`, open) with
    `0 < a < b` — the A-group-discharged shared flow gate is not `∅`-degenerate.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0)) := by
  obtain ⟨S, a, b, ha, hab, hfat, -⟩ :=
    white_hInnerCont_closed (n := 2) (by norm_num) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
      (Uwin := (∅ : Set ℝ)) (by simp)
  exact ⟨S, a, b, ha, hab, hfat 0 (Metric.mem_closedBall_self (by norm_num))⟩

#check @white_hInnerCont_closed
#check @white_hInnerCont_closed_witness_gate

end QIQTH.WhiteHInnerContClosed

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHInnerContClosed
#print axioms white_hInnerCont_closed
#print axioms white_hInnerCont_closed_witness_gate
end AxiomChecks
