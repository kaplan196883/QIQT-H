/-
  WhiteWitnessValueDom — J4-689 (downstream item (b′), the whitened VALUE-kernel domination):
  the missing `hWdom` slot of `WhiteHInnerCont.white_hInnerCont_of_dominations` (J4-688).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── CONTEXT.  The generic inner-pairing continuity builder consumes, alongside the whitened-defect
     Levi B-slot, a WHITENED-WITNESS VALUE Gaussian domination
        `|whiteGatedWitness κ … a b τ p q| ≤ (A₀+A₁τ)·Cpre·gaussDdim (wA·τ) (p − q)`
     at SOME positive width `wA`, with affine amplitude.  The banked whitened bounds
     (`white_hEuni` / `white_hpkgBound_discharged`) cover only the DEFECT `heatOp(whiteGatedWitness)`,
     NOT the raw value kernel.  This file lands the raw value domination.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `white_witness_value_dom` — ★★ the raw whitened VALUE domination on the concrete flow-ball
      gate `whiteFlowGate κ hκ hKc c`.  The witness is the banked `gatedKernel`-cutoff object
      `whiteGatedWitness = gatedKernel Kset S (radialCutoff·whiteAmbientKernel)`, whose VALUE is
      near-explicitly Gaussian.  OFF the gate it VANISHES (`gatedKernel_apply_of_notMem`); ON the
      gate `p = whiteExp_q w`, `whiteInvChart_q p = w`, so the value is
          `radialCutoff a b w · √det g^κ(q) · gaussDdim τ w` .
      Three uniform bounds finish it:
        (i)   `|radialCutoff a b w| ≤ 1` (banked cutoff clamp);
        (ii)  `√det g^κ(q) ≤ √((1 − κ/3·n R²)^{n−1})` (banked van-Vleck determinant control on the
              compact seed `Kset ⊆ B̄(0,R)`);
        (iii) `gaussDdim τ w ≤ √lam^n · gaussDdim (lam·τ) (p − q)` at width `lam = nC₀²+1` — the
              two-sided near-isometry: `rncRadialSq(p − q) ≤ nC₀²·rncRadialSq w` (banked tube
              confinement `whiteExp_displacement` + the whitening `rncRadialSq` contraction
              `whiteVel_radialSq_le`), fed through the banked width transfer
              `gaussDdim_le_gaussDdim_chart` (`c = 1 < d = lam`).
      Yields `wA = lam`, `A₀ = 1`, `A₁ = 0`, `Cpre = √((1−κ/3 nR²)^{n−1})·√lam^n` — the EXACT
      `hWdom` shape (affine amplitude, positive width) the builder consumes.  Mirrors the vanVleck
      value producer `CurvedRNCBaseWitnessDomAdom.curvedRNC_baseWitness_dom_adom` structurally.
    • `white_witness_value_dom_witness_gate` — the cp466 non-vacuity certificate (`n = 2`,
      `κ = −1`, `K = closedBall 0 2`): the ∃-package produces `0 < c`, `0 < a < b`, and a positive
      width `wA`, so the value domination is not `∅`-degenerate.

  ── HONEST RESIDUAL.  This is the VALUE domination on the CONCRETE flow-ball gate.  Wiring it into
     `white_hInnerCont_of_dominations` (removing its `hWdom` carry) additionally needs the B-slot
     discharger (`white_hBdom_discharged`) to CO-EMIT this exact gate handle: that discharger
     currently returns its flow-ball gate existentially (opaque `∃ S`), so a co-emitting combined
     discharger is the one remaining wire.  The mathematical content of `hWdom` is DONE here.

  ⚠ HONEST FIREWALL.  Raw value domination ONLY — NOT `a₁ = R/6`; the `R/6` value is a labelled
  carrier, untouched.  DERIVED from banked cutoff/determinant/near-isometry bricks.  No `sorry`, no
  `admit`, no new axioms, no `:= True`, no vacuous hypothesis, no existing file edited, nothing
  committed.
-/
import Mathlib
import QIQTH.WhiteGated
import QIQTH.WhiteAnnulus
import QIQTH.WidthMarginEngine
import QIQTH.CurvedRNCVanVleckBound

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.CurvedA1CenterAmp
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteAnnulus QIQTH.WhiteGated
open QIQTH.CurvedRNCVanVleckBound
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteWitnessValueDom

variable {n : ℕ}

/-- **★★ `white_witness_value_dom` — THE WHITENED-WITNESS VALUE DOMINATION.**  For EVERY `κ ≤ 0`
    and compact seed `Kset ⊆ B̄(0,R)`, there are a flow-ball gate radius `c > 0`, cutoff radii
    `0 < a < b`, a positive width `wA`, an amplitude constant `Cpre ≥ 0`, and affine constants
    `A₀, A₁ ≥ 0` such that the whitened gated witness on `whiteFlowGate κ hκ hKc c` satisfies the
    value Gaussian domination
        `|whiteGatedWitness κ hκ hKc (whiteFlowGate … c) a b τ p q|
            ≤ (A₀ + A₁·τ)·Cpre·gaussDdim (wA·τ) (p − q)`
    for all `τ > 0` and all `p q`.  Off the gate the witness vanishes; on the gate it is
    `radialCutoff·√det·gaussDdim`, dominated via the cutoff clamp, the determinant control, and the
    banked near-isometry width transfer.  This is the EXACT `hWdom` slot of
    `WhiteHInnerCont.white_hInnerCont_of_dominations`.  NOT `a₁ = R/6`. -/
theorem white_witness_value_dom (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ c : ℝ, 0 < c ∧ ∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∃ wA Cpre A₀ A₁ : ℝ, 0 < wA ∧ 0 ≤ Cpre ∧ 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
        ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
          |whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) a b τ p q|
            ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q) := by
  classical
  -- the chart-inverse germ radius + the two flow constants.
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
  -- the gate radius usable for BOTH the chart inverse (`< δ₀`) and the tube confinement (`≤ Rf`).
  set c : ℝ := min δ₀ Rf with hcdef
  have hc0 : 0 < c := lt_min hδ₀0 hRf0
  have hcδ : c ≤ δ₀ := min_le_left _ _
  have hcRf : c ≤ Rf := min_le_right _ _
  -- the width and its positivity.
  set lam : ℝ := (n : ℝ) * C₀ ^ 2 + 1 with hlamdef
  have hlam0 : 0 < lam := by
    have : (0 : ℝ) ≤ (n : ℝ) * C₀ ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
    rw [hlamdef]; linarith
  -- the amplitude constant.
  set Amp : ℝ := Real.sqrt ((1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1)) with hAmpdef
  have hAmp0 : 0 ≤ Amp := Real.sqrt_nonneg _
  set Cpre : ℝ := Amp * Real.sqrt (lam / 1) ^ n with hCpredef
  have hCpre0 : 0 ≤ Cpre :=
    mul_nonneg hAmp0 (pow_nonneg (Real.sqrt_nonneg _) n)
  refine ⟨c, hc0, c / 4, c / 2, by linarith, by linarith,
    lam, Cpre, 1, 0, hlam0, hCpre0, by norm_num, le_rfl, ?_⟩
  intro τ hτ p q
  have hRHS0 : 0 ≤ (1 + 0 * τ) * Cpre * gaussDdim (lam * τ) (p - q) := by
    have hg := gaussDdim_nonneg (lam * τ) (p - q)
    have : (0 : ℝ) ≤ (1 + 0 * τ) * Cpre := by nlinarith
    exact mul_nonneg this hg
  by_cases hq : q ∈ Kset
  · by_cases hpmem : p ∈ whiteFlowGate κ hκ hKc c q
    · -- ON GATE.  `p = whiteExp_q W`, `whiteInvChart_q p = W`, value is Gaussian.
      obtain ⟨v, hvmem, hpv⟩ := id hpmem
      have hv : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hvmem
      have hvδ : ‖v‖ < δ₀ := lt_of_lt_of_le hv hcδ
      set W : Point n := whiteUnvel κ q v with hWdef
      -- `uniformInverseChart_q p = v` (germ eq_of_nhds).
      have hVval : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q p = v := by
        rw [← hpv]
        exact (((hspec q hq).1 v hvδ).1).eq_of_nhds
      -- `whiteInvChart_q p = W`.
      have hInvW : whiteInvChart κ hκ hKc q p = W := by
        show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q p) = W
        rw [hVval]
      -- `p = whiteExp_q W`.
      have hpW : whiteExp κ hκ hKc q W = p := by
        rw [hWdef, whiteExp_whiteUnvel κ hκ hKc q v]; exact hpv
      -- `whiteVel_q W = v`.
      have hVelW : whiteVel κ q W = v := by
        rw [hWdef]; exact whiteVel_whiteUnvel κ hκ q v
      -- value of the witness on the gate.
      have hval : whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q
          = radialCutoff (c / 4) (c / 2) W
            * (Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * gaussDdim τ W) := by
        unfold whiteGatedWitness
        rw [gatedKernel_apply_of_mem Kset (whiteFlowGate κ hκ hKc c)
              (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ hq hpmem]
        unfold whiteCutKernel whiteAmbientKernel
        rw [hInvW]
      -- (ii) determinant amplitude control.
      have hqR : rncRadialSq q ≤ (n : ℝ) * R ^ 2 := rncRadialSq_le_of_mem_closedBall (hKb hq)
      have hdetle : Matrix.det (curvedRNCMetric κ q) ≤ (1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1) :=
        curvedRNCMetric_det_le κ hκ q ((n : ℝ) * R ^ 2) hqR
      have hdetamp : Real.sqrt (Matrix.det (curvedRNCMetric κ q)) ≤ Amp :=
        Real.sqrt_le_sqrt hdetle
      have hdet0 : 0 ≤ Real.sqrt (Matrix.det (curvedRNCMetric κ q)) := Real.sqrt_nonneg _
      -- (iii) near-isometry displacement control.
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
      -- assemble.
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
    · -- OFF gate (`p ∉ S q`): witness vanishes.
      rw [show whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q = 0 from
        gatedKernel_apply_of_notMem Kset (whiteFlowGate κ hκ hKc c)
          (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ p q (Or.inr hpmem), abs_zero]
      exact hRHS0
  · -- OFF gate (`q ∉ K`): witness vanishes.
    rw [show whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q = 0 from
      gatedKernel_apply_of_notMem Kset (whiteFlowGate κ hκ hKc c)
        (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ p q (Or.inl hq), abs_zero]
    exact hRHS0

/-- **cp466 non-vacuity gate** — at genuinely curved data (`n = 2`, `κ = −1`, `K = closedBall 0 2`):
    the ∃-package of `white_witness_value_dom` produces `0 < c`, `0 < a < b`, and a positive width
    `wA` — the value domination is not `∅`-degenerate.  NOT `a₁ = R/6`. -/
theorem white_witness_value_dom_witness_gate :
    ∃ c : ℝ, 0 < c ∧ ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ wA : ℝ, 0 < wA := by
  obtain ⟨c, hc0, a, b, ha, hab, wA, _Cpre, _A₀, _A₁, hwA0, -, -, -, -⟩ :=
    white_witness_value_dom (n := 2) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
  exact ⟨c, hc0, a, b, ha, hab, wA, hwA0⟩

end QIQTH.WhiteWitnessValueDom

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.WhiteWitnessValueDom

#print axioms white_witness_value_dom
#print axioms white_witness_value_dom_witness_gate

end AxiomChecks
