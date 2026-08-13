/-
  WhiteHInnerContGeomClosed — J4-713 (Route (β) BRICK 4, rethread): THE `hInterior`-FREE THREADING.

  The whitened inner-pairing interior-time continuity with the `htermBox` carry DISCHARGED via the
  `hInterior`-FREE per-level tie `WhiteHtermBoxWClosed.white_htermBox_unconditional_k_closed` (J4-713)
  instead of the `hInterior`-carrying `WhiteHtermBoxWCover.white_htermBox_unconditional_k_cover` (J4-712).
  So the composed continuity carries the FINAL certificate list — `{hnull, hlegA, hbase}` + `{hpkg,
  hEmeas}` — with `hInterior` REPLACED by its leg (a) family `hlegA` (leg (b), the iterate time slice,
  is DERIVED inside the tie from the box IH).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── CONTEXT.  `WhiteHInnerContGeomCover.white_hInnerCont_closed_cover` (3af90701) discharged `htermBox`
     via `white_htermBox_unconditional_k_cover` — carrying the labelled `hInterior` (the full-integrand
     interior `ContinuousWithinAt` family, whose OPEN leg was the iterate time slice).  This file swaps
     the discharger for `white_htermBox_unconditional_k_closed`, whose surviving inputs are `{hnull,
     hlegA, hbase}` + `{hpkg, hEmeas}` — `hInterior` GONE (leg (b) derived; leg (a) = `hlegA`).  STEP 1–3
     compose VERBATIM from `white_hInnerCont_closed_cover`; only the `hprodK` discharger changes.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `white_hInnerCont_closed_final` — ★★★ the composed whitened inner-pairing interior-time continuity
      with `htermBox` DISCHARGED through the `hInterior`-free tie, carrying ONLY the FINAL certificate
      list.  For gate-parametric `{S, a, b}`, the co-instantiated width-`whiteLam` pkg / S1 / value
      A-group, and the certificates `{hnull, hlegA, hbase}`, the interior continuity of the whitened
      inner pairing holds on `Ioo 0 u`, ∀ `u ∈ Uwin` (`Uwin ⊆ (·,1]`).

  ── HONEST RESIDUAL — THE FINAL LABELLED CERTIFICATE LIST (NOT the conclusion, NOT a₁ = R/6; the
     uniform-reach wall + group-8 GONE; `hjoint` GONE; **`hInterior` GONE — leg (b) DERIVED**).
    A. co-instantiated at the shared gate (the `white_hInnerCont_modulo_termBox` obtain-chain output):
       1. `C`, `hC0`; 2. `hpkg`; 3. `hEmeas`; 4. `hWmeas`; 5. `wA, Cpre, A₀, A₁` (+ nonneg) and `hval`.
    B. the FINAL certificates:
       6. `hnull` — the null-frontier cert `∀ z₀, volume {w | z₀ ∈ frontier (S w)} = 0`.
       7. `hlegA` — the leg-(a) reparam-kernel-factor `ContinuousWithinAt` family at interior field
          points (the J4-710 set-generic `_at_set` reparam substrate on a small in-gate ball; LABELLED).
       8. `hbase` — the `k = 0` raw-kernel continuity seed.
    C. window: `Uwin`, `hU1 : ∀ u ∈ Uwin, u ≤ 1`.

  ⚠  HONEST FIREWALL.  `hInterior`-free threading ONLY.  THIS FILE IS **NOT** `a₁ = R/6` and proves
  NOTHING about `R/6` (`R/6` is a labelled carrier, untouched).  No `sorry`, no `admit`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.
-/
import Mathlib
import QIQTH.WhiteHInnerContTermBox
import QIQTH.WhiteHtermBoxWClosed

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
open QIQTH.WhiteHtermBoxWClosed
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteHInnerContGeomClosed

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ the composed continuity, `htermBox` DISCHARGED via the `hInterior`-free tie.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_closed_final` — `htermBox` DISCHARGED via the `hInterior`-free tie.**
    For gate-parametric `{S, a, b}`, the co-instantiated width-`whiteLam` pkg / S1 / value A-group, and
    the FINAL certificates `{hnull, hlegA, hbase}`, the whitened inner-pairing interior-time continuity
    holds on `Ioo 0 u`, ∀ `u ∈ Uwin` (`Uwin ⊆ (·,1]`).  The `htermBox` carry is DISCHARGED in-line by
    `WhiteHtermBoxWClosed.white_htermBox_unconditional_k_closed` (the J4-713 `hInterior`-free tie: leg (b)
    is derived from the box IH, leg (a) is `hlegA`) fed the SAME `{hpkg, hEmeas}` co-instantiation plus
    the certificates, adapted to the box shape by the window/radius adapter.  STEP 1–3 compose verbatim
    from `white_hInnerCont_closed_cover`.  ⚠ CONDITIONAL on the labelled certificate list (file header
    A/B/C).  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
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
    -- B. the FINAL certificates
    (hnull : ∀ z₀ : Point n, volume {w : Point n | z₀ ∈ frontier (S w)} = 0)
    (hlegA : ∀ (u : ℝ), 0 < u → u ≤ 1 → ∀ (s₁ s₂ ρ : ℝ),
        0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 → 0 < ρ →
      ∀ p₀ ∈ (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ),
      ∀ w : Point n, w ∈ Kset → p₀.2 ∈ interior (S w) →
        ContinuousWithinAt
          (fun p : ℝ × Point n =>
            whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) p₀)
    (hbase : ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      ContinuousOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R'))
    -- C. window
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) := by
  have hlam0 : (0 : ℝ) < whiteLam κ hκ hKc :=
    lt_of_lt_of_le two_pos (whiteLam_ge_two κ hκ hKc)
  -- DISCHARGE `htermBox` via the J4-713 `hInterior`-FREE tie, fed the SAME co-instantiation + certs.
  have hprodK : ∀ k : ℕ, ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      ContinuousOn
        (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') :=
    white_htermBox_unconditional_k_closed κ hκ hKc S a b C (whiteLam κ hκ hKc) hC0
      (whiteLam_ge_two κ hκ hKc) hpkg hEmeas hnull hlegA hbase
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

#check @white_hInnerCont_closed_final

end QIQTH.WhiteHInnerContGeomClosed

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHInnerContGeomClosed
#print axioms white_hInnerCont_closed_final
end AxiomChecks
