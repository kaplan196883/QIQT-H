/-
  WhiteHInnerContFinal — J4-691: the WHITENED inner-pairing time-continuity with the S1
  measurability carry (`hEmeas`) DISCHARGED at the co-instantiated flow-ball gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── CONTEXT.  `WhiteGatePackageCombined.white_hInnerCont_combined` (J4-690) reduced the whitened
     inner-pairing time-continuity to exactly THREE carries `{S1 `hEmeas`, interior slice
     measurability `hmeas`, a.e.-`z` interior-time continuity `hcont`}`, but it left `hEmeas`
     (the whitened-defect `tripleHEmeas`) as an ANTECEDENT because its shared gate is emitted at an
     internal radius that is not guaranteed to lie below the S1 discharge threshold.

  ── ★★ THE FINDING (the co-instantiation).  The whitened `tripleHEmeas` is ALREADY a THEOREM at
     the concrete flow-ball gates: `WhiteS1C.white_tripleHEmeas_uniform` supplies it radius-uniformly
     (`∃ δS > 0, ∀ c ∈ (0,δS), ∀ 0 < a < b < c, tripleHEmeas (whiteGatedWitness (whiteFlowGate c) a b)`).
     Likewise the defect PACKAGE is radius-parametric (`WhiteS1C.white_hpkgBound_at_radius`), and the
     VALUE domination is radius-monotone (transplanted here radius-parametrically as
     `white_witness_value_dom_at_radius`, the same proof as `WhiteWitnessValueDom.white_witness_value_dom`
     with the gate radius `c ∈ (0, min δ₀ Rf)` universally quantified — every constant `{lam, Cpre,
     A₀, A₁}` is `c`-free).  Choosing ONE shared radius `c = min(δp, δS, δV)/2` below all three
     thresholds co-emits ALL THREE at the SAME gate `whiteFlowGate κ hκ hKc c` (the J4-680
     threshold-monotonicity pattern, exactly as `WhiteS1C.white_tail_O_s_unconditional` does for the
     tail).  The defect package feeds the width-`lam` full-row Levi engine
     (`WhiteHBdomAllRows.white_leviSeries_full_row`, given the co-emitted `hEmeas`) to produce the
     B-slot; the value bound is the A-slot; the generic builder
     `CurvedA1HContDomGen.hInnerCont_of_dominations_generic` composes them.  Net: the `hEmeas` carry
     is GONE — the composed continuity carries drop from `{hEmeas, hmeas, hcont}` to `{hmeas, hcont}`.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `white_witness_value_dom_at_radius` — ★ the whitened VALUE domination, radius-PARAMETRIC: one
      `(c)`-free `δV > 0` and `(c)`-free widths/amplitudes such that for EVERY gate radius
      `c ∈ (0,δV)` (cutoff radii `a = c/4 < b = c/2`) the whitened gated witness on the flow-ball gate
      satisfies the value Gaussian domination.  (Verbatim transplant of
      `WhiteWitnessValueDom.white_witness_value_dom` with the radius quantifier reordered.)
    • `white_hInnerCont_final` — ★★★ the composed whitened inner-pairing time-continuity with the
      S1 `hEmeas` carry DISCHARGED: for EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)` (`n > 0`), window
      `U ⊆ (·,1]`, there ARE a fat open gate `S`, radii `0 < a < b`, and a width `lam = whiteLam ≥ 2`
      such that — MODULO ONLY `{the interior slice measurability `hmeas`, the a.e.-`z` interior-time
      continuity `hcont`}` — the interior-time continuity of the whitened inner pairing holds on
      `Ioo 0 u`, ∀ `u ∈ U`.  The whitened-defect S1 measurability is co-instantiated (proved) at the
      shared gate, NOT carried.
    • `white_hInnerCont_final_witness_gate` — the cp466 non-vacuity certificate (`n = 2`, `κ = −1`,
      `K = closedBall 0 2`): the ∃-package produces a FAT gate (`0 ∈ S 0`, open) with `0 < a < b`
      and `lam ≥ 2` — not `∅`-degenerate.

  ── HONEST RESIDUAL.  The composed continuity now owes ONLY `{hmeas, hcont}` (plus the prior
     `K1TransportBudget` / capstone co-instantiation piles).  `hmeas` still hides the whitened Levi
     `z`-slice measurability (the Levi-convergence `LeviSeriesLocalData` / `hFsum` data — the
     convergence trio), and `hcont` the Levi TIME-continuity (open even on the vanVleck side); neither
     is discharged here.  `a₁ = R/6` established non-vacuously ONLY for the FLAT tower.

  ⚠ HONEST FIREWALL.  Gate co-instantiation only — one shared radius emitting three already-proved
  facts, discharging the S1 carry — NOT `a₁ = R/6`; the `R/6` value is a labelled carrier, untouched.
  DERIVED from the banked radius-parametric S1 / pkg suppliers + the banked value bricks + the
  gate-parametric Levi engine + the generic continuity builder.  No `sorry`, no `admit`, no new
  axioms, no `:= True`, no vacuous hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.WhiteWitnessValueDom
import QIQTH.WhiteS1C
import QIQTH.WhiteHBdomAllRows
import QIQTH.CurvedA1HContDomGen

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.CurvedA1CenterAmp
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteAnnulus QIQTH.WhiteGated
open QIQTH.WhiteBridge QIQTH.WhiteHBdomAllRows QIQTH.WhiteS1C
open QIQTH.CurvedRNCVanVleckBound
open QIQTH.LeviSeries
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteHInnerContFinal

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the whitened VALUE domination, radius-PARAMETRIC.
    ############################################################################### -/

/-- **★ `white_witness_value_dom_at_radius` — THE WHITENED VALUE DOMINATION, RADIUS-PARAMETRIC.**
    A single `(c)`-free `δV > 0` and `(c)`-free width/amplitude constants `{wA, Cpre, A₀, A₁}` such
    that for EVERY gate radius `c ∈ (0,δV)` (cutoff radii `a = c/4 < b = c/2`) the whitened gated
    witness on the flow-ball gate `whiteFlowGate κ hκ hKc c` satisfies the value Gaussian domination
        `|whiteGatedWitness κ … (whiteFlowGate … c) (c/4) (c/2) τ p q|
            ≤ (A₀ + A₁·τ)·Cpre·gaussDdim (wA·τ) (p − q)`  (∀ `τ > 0`, all `p q`).
    Verbatim transplant of `WhiteWitnessValueDom.white_witness_value_dom` with the radius `c`
    universally quantified (all constants are `c`-free; `δV = min δ₀ Rf`).  NOT `a₁ = R/6`. -/
theorem white_witness_value_dom_at_radius (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ δV : ℝ, 0 < δV ∧ ∃ wA Cpre A₀ A₁ : ℝ, 0 < wA ∧ 0 ≤ Cpre ∧ 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      ∀ c : ℝ, 0 < c → c < δV → ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q|
          ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q) := by
  classical
  obtain ⟨δ₀, hδ₀0, hspec⟩ := uniformInverseChart_huniformChart
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  set C₀ : ℝ := uniformFlowConst (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc with hC₀def
  have hC₀0 : 0 ≤ C₀ := uniformFlowConst_nonneg (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc
  set Rf : ℝ := uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc with hRfdef
  have hRf0 : 0 < Rf := uniformFlowRadius_pos (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc
  set δV : ℝ := min δ₀ Rf with hδVdef
  have hδV0 : 0 < δV := lt_min hδ₀0 hRf0
  set lam : ℝ := (n : ℝ) * C₀ ^ 2 + 1 with hlamdef
  have hlam0 : 0 < lam := by
    have : (0 : ℝ) ≤ (n : ℝ) * C₀ ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
    rw [hlamdef]; linarith
  set Amp : ℝ := Real.sqrt ((1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1)) with hAmpdef
  have hAmp0 : 0 ≤ Amp := Real.sqrt_nonneg _
  set Cpre : ℝ := Amp * Real.sqrt (lam / 1) ^ n with hCpredef
  have hCpre0 : 0 ≤ Cpre := mul_nonneg hAmp0 (pow_nonneg (Real.sqrt_nonneg _) n)
  refine ⟨δV, hδV0, lam, Cpre, 1, 0, hlam0, hCpre0, by norm_num, le_rfl, ?_⟩
  intro c hc0 hcδV τ hτ p q
  have hcδ : c ≤ δ₀ := le_of_lt (lt_of_lt_of_le hcδV (min_le_left _ _))
  have hcRf : c ≤ Rf := le_of_lt (lt_of_lt_of_le hcδV (min_le_right _ _))
  have hRHS0 : 0 ≤ (1 + 0 * τ) * Cpre * gaussDdim (lam * τ) (p - q) := by
    have hg := gaussDdim_nonneg (lam * τ) (p - q)
    have : (0 : ℝ) ≤ (1 + 0 * τ) * Cpre := by nlinarith
    exact mul_nonneg this hg
  by_cases hq : q ∈ Kset
  · by_cases hpmem : p ∈ whiteFlowGate κ hκ hKc c q
    · obtain ⟨v, hvmem, hpv⟩ := id hpmem
      have hv : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hvmem
      have hvδ : ‖v‖ < δ₀ := lt_of_lt_of_le hv hcδ
      set W : Point n := whiteUnvel κ q v with hWdef
      have hVval : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q p = v := by
        rw [← hpv]
        exact (((hspec q hq).1 v hvδ).1).eq_of_nhds
      have hInvW : whiteInvChart κ hκ hKc q p = W := by
        show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q p) = W
        rw [hVval]
      have hpW : whiteExp κ hκ hKc q W = p := by
        rw [hWdef, whiteExp_whiteUnvel κ hκ hKc q v]; exact hpv
      have hVelW : whiteVel κ q W = v := by
        rw [hWdef]; exact whiteVel_whiteUnvel κ hκ q v
      have hval : whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q
          = radialCutoff (c / 4) (c / 2) W
            * (Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * gaussDdim τ W) := by
        unfold whiteGatedWitness
        rw [gatedKernel_apply_of_mem Kset (whiteFlowGate κ hκ hKc c)
              (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ hq hpmem]
        unfold whiteCutKernel whiteAmbientKernel
        rw [hInvW]
      have hqR : rncRadialSq q ≤ (n : ℝ) * R ^ 2 := rncRadialSq_le_of_mem_closedBall (hKb hq)
      have hdetle : Matrix.det (curvedRNCMetric κ q) ≤ (1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1) :=
        curvedRNCMetric_det_le κ hκ q ((n : ℝ) * R ^ 2) hqR
      have hdetamp : Real.sqrt (Matrix.det (curvedRNCMetric κ q)) ≤ Amp :=
        Real.sqrt_le_sqrt hdetle
      have hdet0 : 0 ≤ Real.sqrt (Matrix.det (curvedRNCMetric κ q)) := Real.sqrt_nonneg _
      have hWvel : ‖whiteVel κ q W‖ ≤ Rf := by
        rw [hVelW]; exact le_of_lt (lt_of_lt_of_le hv hcRf)
      have hdisp : ‖whiteExp κ hκ hKc q W - q‖ ≤ C₀ * ‖whiteVel κ q W‖ :=
        whiteExp_displacement κ hκ hKc q hq W hWvel
      have hr2disp : rncRadialSq (whiteExp κ hκ hKc q W - q)
          ≤ (n : ℝ) * C₀ ^ 2 * rncRadialSq W := by
        have h1 : rncRadialSq (whiteExp κ hκ hKc q W - q)
            ≤ (n : ℝ) * ‖whiteExp κ hκ hKc q W - q‖ ^ 2 := by
          refine rncRadialSq_le_of_mem_closedBall
            (q := whiteExp κ hκ hKc q W - q) (r := ‖whiteExp κ hκ hKc q W - q‖) ?_
          rw [Metric.mem_closedBall, dist_zero_right]
        have h2 : ‖whiteExp κ hκ hKc q W - q‖ ^ 2 ≤ (C₀ * ‖whiteVel κ q W‖) ^ 2 := by
          have := mul_self_le_mul_self (norm_nonneg _) hdisp
          nlinarith
        have h3 : ‖whiteVel κ q W‖ ^ 2 ≤ rncRadialSq (whiteVel κ q W) := by
          have hle : ‖whiteVel κ q W‖ ≤ rncRadial (whiteVel κ q W) :=
            norm_le_rncRadial (whiteVel κ q W)
          have hsq : rncRadial (whiteVel κ q W) ^ 2 = rncRadialSq (whiteVel κ q W) := by
            rw [rncRadial, Real.sq_sqrt (rncRadialSq_nonneg _)]
          have := mul_self_le_mul_self (norm_nonneg _) hle
          nlinarith [this, hsq]
        have h4 : rncRadialSq (whiteVel κ q W) ≤ rncRadialSq W := whiteVel_radialSq_le κ hκ q W
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hnc0 : (0 : ℝ) ≤ (n : ℝ) * C₀ ^ 2 := mul_nonneg hn0 (sq_nonneg _)
        calc rncRadialSq (whiteExp κ hκ hKc q W - q)
            ≤ (n : ℝ) * ‖whiteExp κ hκ hKc q W - q‖ ^ 2 := h1
          _ ≤ (n : ℝ) * (C₀ * ‖whiteVel κ q W‖) ^ 2 := mul_le_mul_of_nonneg_left h2 hn0
          _ = (n : ℝ) * C₀ ^ 2 * ‖whiteVel κ q W‖ ^ 2 := by ring
          _ ≤ (n : ℝ) * C₀ ^ 2 * rncRadialSq (whiteVel κ q W) :=
              mul_le_mul_of_nonneg_left h3 hnc0
          _ ≤ (n : ℝ) * C₀ ^ 2 * rncRadialSq W := mul_le_mul_of_nonneg_left h4 hnc0
      have hr2disp' : rncRadialSq (p - q) ≤ (n : ℝ) * C₀ ^ 2 * rncRadialSq W := by
        rw [hpW] at hr2disp; exact hr2disp
      have hnorm : 1 * rncRadialSq (p - q) ≤ lam * rncRadialSq W := by
        have h0 : (0 : ℝ) ≤ rncRadialSq W := rncRadialSq_nonneg W
        rw [hlamdef]; nlinarith [hr2disp']
      have hcmp : gaussDdim (1 * τ) W
          ≤ Real.sqrt (lam / 1) ^ n * gaussDdim (lam * τ) (p - q) :=
        gaussDdim_le_gaussDdim_chart (by norm_num) hlam0 hτ hnorm
      have hcmp' : gaussDdim τ W
          ≤ Real.sqrt (lam / 1) ^ n * gaussDdim (lam * τ) (p - q) := by
        rw [one_mul] at hcmp; exact hcmp
      have hgW0 : 0 ≤ gaussDdim τ W := gaussDdim_nonneg τ W
      rw [hval]
      have hcut1 : |radialCutoff (c / 4) (c / 2) W| ≤ 1 := by
        rw [abs_of_nonneg (radialCutoff_nonneg _ _ W)]
        exact radialCutoff_le_one _ _ W
      calc |radialCutoff (c / 4) (c / 2) W
              * (Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * gaussDdim τ W)|
          = |radialCutoff (c / 4) (c / 2) W|
              * (Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * gaussDdim τ W) := by
            rw [abs_mul, abs_of_nonneg (mul_nonneg hdet0 hgW0)]
        _ ≤ 1 * (Amp * gaussDdim τ W) := by
            apply mul_le_mul hcut1 _ (mul_nonneg hdet0 hgW0) (by norm_num)
            exact mul_le_mul_of_nonneg_right hdetamp hgW0
        _ = Amp * gaussDdim τ W := by rw [one_mul]
        _ ≤ Amp * (Real.sqrt (lam / 1) ^ n * gaussDdim (lam * τ) (p - q)) :=
            mul_le_mul_of_nonneg_left hcmp' hAmp0
        _ = (1 + 0 * τ) * Cpre * gaussDdim (lam * τ) (p - q) := by
            rw [hCpredef]; ring
    · rw [show whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q = 0 from
        gatedKernel_apply_of_notMem Kset (whiteFlowGate κ hκ hKc c)
          (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ p q (Or.inr hpmem), abs_zero]
      exact hRHS0
  · rw [show whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q = 0 from
      gatedKernel_apply_of_notMem Kset (whiteFlowGate κ hκ hKc c)
        (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ p q (Or.inl hq), abs_zero]
    exact hRHS0

/-! ###############################################################################
    ### §2 — ★★★ the composed continuity with the S1 `hEmeas` carry DISCHARGED.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_final` — THE COMPOSED WHITENED INNER-PAIRING CONTINUITY, S1 DISCHARGED.**
    For EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)` (`n > 0`), and window `U ⊆ (·,1]`, there ARE a fat open
    gate `S`, radii `0 < a < b`, and a width `lam = whiteLam ≥ 2` such that — MODULO ONLY
    `{the interior slice measurability `hmeas`, the a.e.-`z` interior-time continuity `hcont`}` —
    the interior-time continuity of the whitened inner pairing
        `s ↦ ∫ z, whiteGatedWitness κ … (u−s) 0 z · leviSeries (whiteDefectKernel κ …) s z 0`
    holds on `Ioo 0 u`, for every `u ∈ U`.  The whitened-defect S1 measurability `tripleHEmeas` is
    CO-INSTANTIATED (proved) at the shared gate `whiteFlowGate κ hκ hKc c`,
    `c = min(δp, δS, δV)/2`, via `WhiteS1C.white_tripleHEmeas_uniform` — NOT carried.  The value
    domination is discharged via `white_witness_value_dom_at_radius`; the width-`lam` Levi B-slot via
    `WhiteHBdomAllRows.white_leviSeries_full_row` (fed the defect package
    `WhiteS1C.white_hpkgBound_at_radius` and the co-emitted `hEmeas`); the generic builder
    `CurvedA1HContDomGen.hInnerCont_of_dominations_generic` composes them.
    ⚠ HONEST width `lam = whiteLam`.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_final (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R)
    (U : Set ℝ) (hU1 : ∀ u ∈ U, u ≤ 1) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        ((∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
            AEStronglyMeasurable
              (fun z => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
                * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
              (volume : Measure (Point n))) →
          (∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
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
  -- the shared radius below all three thresholds.
  set c : ℝ := min δp (min δS δV) / 2 with hcdef
  have hmin0 : 0 < min δp (min δS δV) := lt_min hδp (lt_min hδS hδVpos)
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hcp : c < δp := by
    have := min_le_left δp (min δS δV); rw [hcdef]; linarith
  have hcS : c < δS := by
    have h1 : min δp (min δS δV) ≤ min δS δV := min_le_right _ _
    have h2 : min δS δV ≤ δS := min_le_left _ _
    rw [hcdef]; linarith [le_trans h1 h2]
  have hcV : c < δV := by
    have h1 : min δp (min δS δV) ≤ min δS δV := min_le_right _ _
    have h2 : min δS δV ≤ δV := min_le_right _ _
    rw [hcdef]; linarith [le_trans h1 h2]
  have ha : 0 < c / 4 := by linarith
  have hab : c / 4 < c / 2 := by linarith
  have hbc : c / 2 < c := by linarith
  -- the shared gate.
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c with hSdef
  -- co-emit the three facts at this gate.
  obtain ⟨hfat, C, hC0, hpkg⟩ := hpkgc c hc0 hcp (c / 4) (c / 2) ha hab hbc
  have hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S (c / 4) (c / 2)) :=
    hS1 c hc0 hcS (c / 4) (c / 2) ha hab hbc
  have hval : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) τ p q|
        ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q) := by
    have := hvalc c hc0 hcV
    -- `whiteFlowGate κ hκ hKc c` is definitionally `S`.
    exact this
  -- discharge the B-slot (width-`lam` Levi) from the package + `hEmeas`.
  obtain ⟨C_L, hC_L, hBdom⟩ :=
    white_leviSeries_full_row κ hκ hKc S (c / 4) (c / 2) C (whiteLam κ hκ hKc)
      hC0 (whiteLam_ge_two κ hκ hKc) hpkg hEmeas
  have hlam0 : (0 : ℝ) < whiteLam κ hκ hKc :=
    lt_of_lt_of_le two_pos (whiteLam_ge_two κ hκ hKc)
  refine ⟨S, c / 4, c / 2, ha, hab, hfat, whiteLam κ hκ hKc, whiteLam_ge_two κ hκ hKc,
    fun hmeas hcont => ?_⟩
  exact QIQTH.CurvedA1HContDomGen.hInnerCont_of_dominations_generic
    (whiteGatedWitness κ hκ hKc S (c / 4) (c / 2))
    (leviSeries (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)))
    1 U hU1 wA (whiteLam κ hκ hKc) hwA0 hlam0 Cpre A₀ A₁ C_L hCpre0 hA₀0 hA₁0 hC_L
    hval (fun s hs hsT z y => hBdom s z y hs hsT) hmeas hcont

/-- **cp466 non-vacuity gate** — at genuinely curved data (`n = 2`, `κ = −1`, `K = closedBall 0 2`):
    the ∃-package of `white_hInnerCont_final` produces ONE FAT gate (`0 ∈ S 0`, open) with
    `0 < a < b` and a width `lam ≥ 2` — the co-instantiated shared gate (with S1 discharged) is not
    `∅`-degenerate.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_final_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ ∃ lam : ℝ, 2 ≤ lam := by
  obtain ⟨S, a, b, ha, hab, hgate, lam, hlam2, -⟩ :=
    white_hInnerCont_final (n := 2) (by norm_num) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
      (U := (∅ : Set ℝ)) (by simp)
  exact ⟨S, a, b, ha, hab,
    hgate 0 (Metric.mem_closedBall_self (by norm_num)), lam, hlam2⟩

end QIQTH.WhiteHInnerContFinal

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.WhiteHInnerContFinal

#print axioms white_witness_value_dom_at_radius
#print axioms white_hInnerCont_final
#print axioms white_hInnerCont_final_witness_gate

end AxiomChecks
