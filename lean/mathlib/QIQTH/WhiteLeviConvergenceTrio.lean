/-
  WhiteLeviConvergenceTrio — J4-692: THE LEVI CONVERGENCE TRIO, extracted at the whitened witness,
  composing into the `hmeas` carry DISCHARGED.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── CONTEXT.  `WhiteHInnerContFinal.white_hInnerCont_final` (J4-691) discharged the S1 `hEmeas`
     carry, dropping the composed whitened inner-pairing time-continuity carries to `{hmeas, hcont}`.
     `hmeas` still hid the whitened Levi `z`-slice `AEStronglyMeasurable` — the Levi-convergence
     `LeviSeriesLocalData` / `hFsum` data, "the convergence trio".

  ── ★★ THE FINDING (the extraction, the J4-676 pattern).  The trio is an EXTRACTION from banked
     termwise bounds, NOT new analysis:
       • termwise measurability: `iterE_zmeas` (IterEMeasurable) propagates the `z`-slice strong
         measurability of every `iterE (whiteDefectKernel …) k` from the SINGLE base joint
         measurability `whiteDefectKernel_stronglyMeasurable` (WhiteBridge), itself derived from the
         co-instantiated S1 `tripleHEmeas`;
       • pointwise summability: the banked row iterate bound `WhiteHBdomAllRows.iterE_row_bound_w`
         (fed by `white_hEbound_negHalf` / `white_hEuni` / `white_hInt`, all from the pkg bound +
         S1) gives `|iterE E (k+1) s z y| ≤ colC (2C) (2C) k · s^(k/2) · G_{lam·s}(z−y)`; since
         `s ≤ 1` forces `s^(k/2) ≤ 1` and `colC` is summable (`FrozenColumn.colC_summable`, the
         Γ/factorial decay), the signed Levi series is dominated by a summable scalar series ⟹
         pointwise absolute summability EVERYWHERE (a fortiori a.e.);
       • the generic `LeviSeriesLocalData.leviSeries_stronglyMeasurable_of_termwise` (measurable
         partial sums + a.e. summability ⟹ the `tsum` is strongly measurable) then closes.
     This is precisely the passage the tail engines already performed IN NORM; here it is extracted
     as the POINTWISE `z`-slice measurability.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `white_witness_value_concrete_uniform` — the whitened WITNESS joint strong measurability at the
      concrete flow-ball gate, radius-uniform with the cutoffs `a b` quantified INSIDE (the value-
      measurability threshold `δ₀` is `a,b`-independent, so `white_witness_value_concrete` transplants
      verbatim with `a b` moved past the radius quantifier) — the A-slice supplier.
    • `white_leviSeries_zmeas` — ★★ THE TRIO.  For gate-parametric `{S, a, b, C, lam}` with the pkg
      bound `hpkg` and the S1 `hEmeas`, the whitened Levi `z`-slice
      `z ↦ leviSeries (whiteDefectKernel κ … S a b) s z y` is `AEStronglyMeasurable` on `(0,1]`,
      ∀ `y`.  The B-slice supplier.
    • `white_hInnerCont_hmeas` — ★★★ the composed whitened inner-pairing time-continuity with the
      `hmeas` carry DISCHARGED at the shared co-instantiated flow-ball gate: carries drop from
      `{hmeas, hcont}` to `{hcont}` ONLY.  Same gate co-instantiation as `white_hInnerCont_final`
      plus the `a,b`-independent witness-measurability threshold `δW` folded into the shared radius.
    • `white_hInnerCont_hmeas_witness_gate` — the cp466 non-vacuity certificate (`n = 2`, `κ = −1`,
      `K = closedBall 0 2`).

  ── HONEST RESIDUAL.  The composed continuity now owes ONLY `{hcont}` (the Levi TIME-continuity,
     still open) plus the prior `K1TransportBudget` / capstone co-instantiation piles.
     `a₁ = R/6` established non-vacuously ONLY for the FLAT tower — the `R/6` value is a labelled
     carrier, untouched.

  ⚠ HONEST FIREWALL.  Trio extraction + gate co-instantiation only — NOT `a₁ = R/6`.  DERIVED from
  the banked termwise row bounds + `colC` summability + the generic `tsum` measurability lemma + the
  radius-parametric S1 / pkg / value / witness-measurability suppliers.  No `sorry`, no `admit`, no
  new axioms, no `:= True`, no vacuous hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.WhiteHInnerContFinal
import QIQTH.WhiteS1
import QIQTH.LeviSeriesLocalData
import QIQTH.IterEMeasurable
import QIQTH.ConcreteGateInstantiation

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.CurvedA1CenterAmp
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteAnnulus QIQTH.WhiteGated
open QIQTH.WhiteBridge QIQTH.WhiteHBdomAllRows QIQTH.WhiteS1C
open QIQTH.WhiteS1 QIQTH.LeviSeriesLocalData QIQTH.FrozenColumn
open QIQTH.WhiteHInnerContFinal
open QIQTH.CurvedRNCVanVleckBound
open QIQTH.LeviSeries
open QIQTH.GaussianWidthTolerant
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteLeviConvergenceTrio

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the whitened WITNESS joint measurability, radius-uniform (A-slice supplier).
    ############################################################################### -/

/-- **`white_witness_value_concrete_uniform`** — the whitened gated witness VALUE triple is jointly
    `(τ,p,q)` strongly measurable at the concrete flow-ball gate, radius-uniform with the cutoff
    radii `a b` universally quantified INSIDE the threshold.  The value-measurability threshold
    `δ₀ = min ρ δm` (chart-representative reach `ρ` + gate-set `MeasurableSet` reach `δm`) is
    INDEPENDENT of the cutoffs `a b` (which only pass through `whiteCutKernelGc`, measurable for any
    `a b`), so `WhiteS1.white_witness_value_concrete` transplants verbatim with `a b` moved past the
    radius quantifier.  NOT `a₁ = R/6`. -/
theorem white_witness_value_concrete_uniform (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ a b : ℝ,
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          w.1 w.2.1 w.2.2) := by
  obtain ⟨ρ, hρ, Wg, hWgMeas, hWagree⟩ := whiteChart_rep_concrete κ hκ hKc
  obtain ⟨δm, hδm, hδmspec⟩ :=
    QIQTH.ConcreteGateInstantiation.hKSmeas_concrete (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc
  refine ⟨min ρ δm, lt_min hρ hδm, ?_⟩
  intro c hc0 hcδ a b
  have hcρ : c ≤ ρ := le_of_lt (lt_of_lt_of_le hcδ (min_le_left _ _))
  have hcm : c < δm := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact whiteGatedWitness_value_stronglyMeasurable κ hκ hKc _ a b Wg hWgMeas
    (hδmspec c hc0 hcm) (fun w hqK hpS => hWagree c hcρ w hqK hpS)

/-! ###############################################################################
    ### §2 — ★★ THE TRIO: the whitened Levi `z`-slice `AEStronglyMeasurable` (B-slice supplier).
    ############################################################################### -/

/-- **★★ `white_leviSeries_zmeas` — THE LEVI CONVERGENCE TRIO, at the whitened witness.**  For
    gate-parametric `{S, a, b, C, lam}` (`0 ≤ C`, `2 ≤ lam`) with the capstone-`hpkgBound` shape
    `hpkg` and the co-instantiated S1 `hEmeas`, the whitened signed Levi `z`-slice
        `z ↦ leviSeries (whiteDefectKernel κ hκ hKc S a b) s z y`
    is `AEStronglyMeasurable` (for `volume`) on the window `(0,1]`, for every right node `y`.
    EXTRACTION (the J4-676 pattern): termwise `z`-measurability from `iterE_zmeas` fed the base
    `whiteDefectKernel_stronglyMeasurable`, pointwise absolute summability from the banked row bound
    `iterE_row_bound_w` dominated by the summable `colC` scalar series (`colC_summable`), composed
    through the generic `leviSeries_stronglyMeasurable_of_termwise`.  NOT `a₁ = R/6`. -/
theorem white_leviSeries_zmeas (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ y : Point n,
      AEStronglyMeasurable
        (fun z : Point n => leviSeries (whiteDefectKernel κ hκ hKc S a b) s z y)
        (volume : Measure (Point n)) := by
  intro s hs hs1 y
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  have h2C : 0 ≤ 2 * C := by linarith
  have hEbmeas := whiteDefectKernel_stronglyMeasurable κ hκ hKc S a b hEmeas
  -- termwise `z`-slice strong measurability of every signed iterate.
  have hmeas : ∀ k : ℕ,
      AEStronglyMeasurable
        (fun z : Point n =>
          (-1 : ℝ) ^ (k + 1) * iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) s z y)
        (volume : Measure (Point n)) :=
    fun k =>
      (iterE_zmeas (whiteDefectKernel κ hκ hKc S a b) hEbmeas (k + 1) (by omega) s y).const_mul _
  -- the banked row iterate bound at the whitened defect (width `lam`).
  have hrow := iterE_row_bound_w (whiteDefectKernel κ hκ hKc S a b) lam (2 * C) (2 * C)
    hlam0 h2C h2C
    (fun τ p q hτ _hτ1 => white_hEbound_negHalf κ hκ hKc S a b C lam hC hpkg τ p q hτ)
    (white_hEuni κ hκ hKc S a b C lam hpkg)
    (white_hInt κ hκ hKc S a b C lam hC hlam0 hpkg hEmeas)
  -- pointwise absolute summability EVERYWHERE, dominated by the summable `colC` series.
  have hsum : ∀ᵐ z : Point n ∂(volume : Measure (Point n)),
      Summable
        (fun k : ℕ =>
          (-1 : ℝ) ^ (k + 1) * iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) s z y) := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hCsum : Summable (fun k : ℕ => colC (2 * C) (2 * C) k * gaussDdim (lam * s) (z - y)) :=
      (colC_summable (2 * C) (2 * C) h2C h2C).mul_right _
    refine Summable.of_norm_bounded hCsum (fun k => ?_)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    have hpow : s ^ ((k : ℝ) / 2) ≤ 1 := Real.rpow_le_one hs.le hs1 (by positivity)
    have hG : 0 ≤ gaussDdim (lam * s) (z - y) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
    calc |iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) s z y|
        ≤ colC (2 * C) (2 * C) k * s ^ ((k : ℝ) / 2) * gaussDdim (lam * s) (z - y) :=
          hrow k s hs hs1 z y
      _ ≤ colC (2 * C) (2 * C) k * 1 * gaussDdim (lam * s) (z - y) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (colC_nonneg (2 * C) (2 * C) h2C h2C k)) hG
      _ = colC (2 * C) (2 * C) k * gaussDdim (lam * s) (z - y) := by ring
  have key := leviSeries_stronglyMeasurable_of_termwise
    (fun k z => (-1 : ℝ) ^ (k + 1) * iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) s z y)
    hmeas hsum
  have hrw : (fun z : Point n => leviSeries (whiteDefectKernel κ hκ hKc S a b) s z y)
      = fun z : Point n =>
          ∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) s z y :=
    rfl
  rw [hrw]; exact key

/-! ###############################################################################
    ### §3 — ★★★ the composed continuity with the `hmeas` carry DISCHARGED.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_hmeas` — THE COMPOSED WHITENED INNER-PAIRING CONTINUITY, `hmeas`
    DISCHARGED.**  For EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)` (`n > 0`), and window `U ⊆ (·,1]`, there
    ARE a fat open gate `S`, radii `0 < a < b`, and a width `lam = whiteLam ≥ 2` such that — MODULO
    ONLY the a.e.-`z` interior-time continuity `hcont` — the interior-time continuity of the whitened
    inner pairing holds on `Ioo 0 u`, ∀ `u ∈ U`.  The whitened-defect S1 measurability is
    co-instantiated (as in `white_hInnerCont_final`), the whitened-witness VALUE domination is
    discharged (`white_witness_value_dom_at_radius`), the width-`lam` Levi B-slot is discharged
    (`white_leviSeries_full_row`), AND the interior slice measurability `hmeas` is now DISCHARGED at
    the shared gate via the product of the whitened WITNESS slice (`white_witness_value_concrete_
    uniform`, threshold `δW`) and the whitened LEVI `z`-slice (`white_leviSeries_zmeas`, THE TRIO) —
    the shared radius `c = min(δp, δS, δV, δW)/2` lies below all four thresholds.
    ⚠ HONEST width `lam = whiteLam`.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_hmeas (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R)
    (U : Set ℝ) (hU1 : ∀ u ∈ U, u ≤ 1) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        ((∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
              ContinuousAt
                (fun s => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
                  * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0) s₀) →
          ∀ u ∈ U, ContinuousOn
            (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
              * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
            (Set.Ioo 0 u)) := by
  obtain ⟨δp, hδp, hpkgc⟩ := white_hpkgBound_at_radius κ hκ hKc R hKb
  obtain ⟨δS, hδS, hS1⟩ := white_tripleHEmeas_uniform hn κ hκ hKc
  obtain ⟨δV, hδVpos, wA, Cpre, A₀, A₁, hwA0, hCpre0, hA₀0, hA₁0, hvalc⟩ :=
    white_witness_value_dom_at_radius κ hκ hKc R hKb
  obtain ⟨δW, hδWpos, hWc⟩ := white_witness_value_concrete_uniform κ hκ hKc
  -- the shared radius below ALL FOUR thresholds.
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
  -- the shared gate.
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c with hSdef
  -- co-emit the four facts at this gate.
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
  -- discharge the B-slot (width-`lam` Levi bound) from the package + `hEmeas`.
  obtain ⟨C_L, hC_L, hBdom⟩ :=
    white_leviSeries_full_row κ hκ hKc S (c / 4) (c / 2) C (whiteLam κ hκ hKc)
      hC0 (whiteLam_ge_two κ hκ hKc) hpkg hEmeas
  have hlam0 : (0 : ℝ) < whiteLam κ hκ hKc :=
    lt_of_lt_of_le two_pos (whiteLam_ge_two κ hκ hKc)
  -- ★ THE `hmeas` DISCHARGE: the witness slice × the Levi `z`-slice (the trio), eventually in `s`.
  have hmeas : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable
        (fun z => whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) (u - s) 0 z
          * leviSeries (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)) s z 0)
        (volume : Measure (Point n)) := by
    intro u hu s₀ hs₀
    refine Filter.eventually_of_mem (Ioo_mem_nhds hs₀.1 hs₀.2) (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have hs1 : s ≤ 1 := le_of_lt (lt_of_lt_of_le hs.2 (hU1 u hu))
    have hAslice : AEStronglyMeasurable
        (fun z : Point n => whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) (u - s) 0 z)
        (volume : Measure (Point n)) :=
      (hWmeas.comp_measurable
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    have hBslice : AEStronglyMeasurable
        (fun z : Point n => leviSeries (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)) s z 0)
        (volume : Measure (Point n)) :=
      white_leviSeries_zmeas κ hκ hKc S (c / 4) (c / 2) C (whiteLam κ hκ hKc) hC0
        (whiteLam_ge_two κ hκ hKc) hpkg hEmeas s hs0 hs1 0
    exact hAslice.mul hBslice
  refine ⟨S, c / 4, c / 2, ha, hab, hfat, whiteLam κ hκ hKc, whiteLam_ge_two κ hκ hKc,
    fun hcont => ?_⟩
  exact QIQTH.CurvedA1HContDomGen.hInnerCont_of_dominations_generic
    (whiteGatedWitness κ hκ hKc S (c / 4) (c / 2))
    (leviSeries (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)))
    1 U hU1 wA (whiteLam κ hκ hKc) hwA0 hlam0 Cpre A₀ A₁ C_L hCpre0 hA₀0 hA₁0 hC_L
    hval (fun s hs hsT z y => hBdom s z y hs hsT) hmeas hcont

/-- **cp466 non-vacuity gate** — at genuinely curved data (`n = 2`, `κ = −1`, `K = closedBall 0 2`):
    the ∃-package of `white_hInnerCont_hmeas` produces ONE FAT gate (`0 ∈ S 0`, open) with
    `0 < a < b` and a width `lam ≥ 2` — the co-instantiated shared gate (with S1 AND `hmeas`
    discharged) is not `∅`-degenerate.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_hmeas_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ ∃ lam : ℝ, 2 ≤ lam := by
  obtain ⟨S, a, b, ha, hab, hgate, lam, hlam2, -⟩ :=
    white_hInnerCont_hmeas (n := 2) (by norm_num) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
      (U := (∅ : Set ℝ)) (by simp)
  exact ⟨S, a, b, ha, hab,
    hgate 0 (Metric.mem_closedBall_self (by norm_num)), lam, hlam2⟩

end QIQTH.WhiteLeviConvergenceTrio

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.WhiteLeviConvergenceTrio

#print axioms white_witness_value_concrete_uniform
#print axioms white_leviSeries_zmeas
#print axioms white_hInnerCont_hmeas
#print axioms white_hInnerCont_hmeas_witness_gate

end AxiomChecks
