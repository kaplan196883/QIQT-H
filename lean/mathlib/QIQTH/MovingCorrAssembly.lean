/-
  MovingCorrAssembly — J4-281: the moving-correction ASSEMBLY toward `hMovingCorr`, plus the
  Levi joint-continuity M-test packaging (deliverable (i)) and the witness-mass lemma
  (`∫ |Wit(ε_m) 0 ·| ≤ CW`, the on-ball ingredient of deliverable (ii)).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  regularity / mass-estimate brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TWO DELIVERABLES (per the J4-281 brief).

  (i) THE LEVI JOINT CONTINUITY (M-test packaging).  `F z := leviSeries E t z 0
      = ∑' k, (−1)^(k+1) · iterE E (k+1) t z 0`.  The Levi series is a series of continuous
      convolution terms with a summable dominating envelope (the C5c geometric-over-Γ decay banked in
      `LeviSeries.leviSeries_summable` / `iterConv_bound`), so the standard Weierstrass M-test
      (`continuousOn_tsum`) upgrades TERMWISE continuity to joint continuity of the sum:

        • `leviSlice_z_continuousOn_of_termwise`  — the `z`-only slice, on `closedBall 0 R`;
        • `leviSlice_z_continuousAt_zero_of_termwise` — its corollary `ContinuousAt (·) 0`
          (= exactly the `hf_cont` shape carried by `MovingFBoundaryLim`);
        • `leviSlice_jointContinuousOn_of_termwise` — the joint `(s,z)` slice on
          `Icc t₁ t₂ ×ˢ closedBall 0 R` (feeds the uniform-continuity step of (ii)).

      HONEST GAP.  Each lemma carries, as an explicit hypothesis, the TERMWISE continuity of the
      convolution terms `(s,z) ↦ (−1)^(k+1) · iterE E (k+1) s z 0` and a summable norm-envelope.
      These are the genuine analytic ingredients of the M-test — NEITHER is the conclusion.  The
      termwise continuity of `iterE` (iterated `heatConv` convolutions of `E = heatOp g gi Wit`) is
      the residual left to a follow-on brick (the parametric-continuity-of-convolution wall); here it
      is the precisely-isolated M-test gap.  The summable envelope is satisfiable from `iterConv_bound`
      (`|iterE E k s z 0| ≤ C^k · iterKernel α k s z 0`) uniformly over the compact.

  (ii) THE WITNESS MASS `∫ |Wit(ε_m) 0 ·| ≤ CW` (the on-ball ingredient).  From the zeroth wide
      domination `|H τ z| ≤ CW · gaussDdim (lam·τ) z` (`0 < τ ≤ τ₀`) and the Gaussian total mass
      `∫ gaussDdim = 1`:

        • `witnessSlice_mass_le`  — `∫ z, |H τ z| ≤ CW`  for a single `0 < τ ≤ τ₀`;
        • `epsSeq_witnessSlice_mass_eventually_le` — `∀ᶠ m, ∫ z, |H (ε_m) z| ≤ CW`
          (`ε_m → 0⁺`, eventually `ε_m ≤ τ₀`).

      This is the bounded-mass factor `(∫_ball |Wit(ε_m)|) ≤ CW` of the on-ball estimate
      `|∫_ball Wit(ε_m)·(f_m − f)| ≤ (∫|Wit(ε_m)|)·sup_ball|f_m − f|`.  Combined with the sup-limit
      `sup_ball |f_m − f| → 0` (from (i)'s uniform continuity on the compact — CARRIED, honestly
      labelled, in the follow-on assembly) and the Gaussian off-ball tail
      (`GateAnnulusSplit.offBall_integral_tendsto_zero`), it yields `hMovingCorr`.  That final
      integral-split recombination (on/off-ball + `integral_add_compl`, with the uniform-in-`m` Levi
      envelope for the off-ball terms) is the residual left to the follow-on brick.

  ⚠  STILL NOT `a₁ = R/6`.  This brick lands the M-test packaging of the Levi joint continuity
  (isolating the termwise gap) and the witness-mass bound; it does NOT discharge `hf_cont` as a proven
  fact (that needs the termwise continuity of `iterE`) and does NOT land `hMovingCorr` unconditionally.
-/
import QIQTH.MovingFBoundaryLim

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel
open scoped Topology

namespace QIQTH.MovingCorrAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (i) — the Levi joint-continuity M-test packaging (termwise reduction).
    ############################################################################### -/

/-- **★ (i) `leviSlice_z_continuousOn_of_termwise`.**  Weierstrass M-test for the `z`-slice of the
    Levi series.  If each convolution term `z ↦ (−1)^(k+1)·iterE E (k+1) t z 0` is `ContinuousOn` the
    `closedBall 0 R`, and there is a summable norm-envelope `u` dominating the terms on the ball, then
    the Levi `0`-slice `z ↦ leviSeries E t z 0 = ∑' k, (−1)^(k+1)·iterE E (k+1) t z 0` is
    `ContinuousOn` the ball (`continuousOn_tsum`).

    HONEST: the termwise continuity (`hterm`) and the summable envelope (`hu`, `hbound`) are the
    GENUINE M-test ingredients — NEITHER is the conclusion.  The termwise continuity of the iterated
    `heatConv` convolutions is the isolated residual (a follow-on parametric-continuity brick).
    ⚠ NOT `a₁ = R/6`. -/
theorem leviSlice_z_continuousOn_of_termwise
    (E : ℝ → Point n → Point n → ℝ) (t R : ℝ) (u : ℕ → ℝ)
    (hterm : ∀ k : ℕ, ContinuousOn
      (fun z => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t z 0) (Metric.closedBall (0 : Point n) R))
    (hu : Summable u)
    (hbound : ∀ (k : ℕ) (z : Point n), z ∈ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t z 0‖ ≤ u k) :
    ContinuousOn (fun z => leviSeries E t z 0) (Metric.closedBall (0 : Point n) R) := by
  have h := continuousOn_tsum (u := u) hterm hu hbound
  simpa only [leviSeries] using h

/-- **★ (i) `leviSlice_z_continuousAt_zero_of_termwise`.**  Corollary of the M-test: on a ball of
    POSITIVE radius the `ContinuousOn` upgrades to `ContinuousAt` at the origin (the ball is a
    neighbourhood of `0`).  This is EXACTLY the `hf_cont` shape carried by
    `MovingFBoundaryLim.hBoundaryLim_concrete`
    (`ContinuousAt (fun z => leviSeries (heatOp g gi Wit) t z 0) 0`), reduced to the termwise M-test
    ingredients.  ⚠ NOT `a₁ = R/6`. -/
theorem leviSlice_z_continuousAt_zero_of_termwise
    (E : ℝ → Point n → Point n → ℝ) (t R : ℝ) (hR : 0 < R) (u : ℕ → ℝ)
    (hterm : ∀ k : ℕ, ContinuousOn
      (fun z => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t z 0) (Metric.closedBall (0 : Point n) R))
    (hu : Summable u)
    (hbound : ∀ (k : ℕ) (z : Point n), z ∈ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t z 0‖ ≤ u k) :
    ContinuousAt (fun z => leviSeries E t z 0) (0 : Point n) := by
  have hcont := leviSlice_z_continuousOn_of_termwise E t R u hterm hu hbound
  exact hcont.continuousAt (Metric.closedBall_mem_nhds (0 : Point n) hR)

/-- **★★ (i) `leviSlice_jointContinuousOn_of_termwise`.**  The JOINT `(s,z)`-continuity of the Levi
    `0`-slice on the compact `Icc t₁ t₂ ×ˢ closedBall 0 R`, again via the M-test
    (`continuousOn_tsum` on the product space).  This is the joint continuity the mission names as
    deliverable (i); it feeds the uniform-continuity-on-compact step of the moving-correction assembly
    (ii) (Heine–Cantor on the compact strip gives `sup_ball |F (t−ε_m) · − F t ·| → 0`).

    HONEST: same termwise + summable-envelope ingredients as the `z`-only version, now on the product;
    NEITHER hypothesis is the conclusion; the termwise joint continuity of `iterE` is the isolated
    residual.  ⚠ NOT `a₁ = R/6`. -/
theorem leviSlice_jointContinuousOn_of_termwise
    (E : ℝ → Point n → Point n → ℝ) (t₁ t₂ R : ℝ) (u : ℕ → ℝ)
    (hterm : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × Point n => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hu : Summable u)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0‖ ≤ u k) :
    ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have h := continuousOn_tsum (u := u) hterm hu hbound
  simpa only [leviSeries] using h

/-! ###############################################################################
    ### (ii) — the witness-mass bound `∫ |Wit(ε_m) 0 ·| ≤ CW`.
    ############################################################################### -/

/-- **★ (ii) `witnessSlice_mass_le`.**  The absolute mass of a zeroth-wide-dominated witness slice is
    bounded by the domination constant `CW`.  For a slice `H : ℝ → Point n → ℝ` with
    `|H τ z| ≤ CW · gaussDdim (lam·τ) z` (all `z`, at a single `0 < τ ≤ τ₀`),
        `∫ z, |H τ z| ≤ CW`.
    Route: `∫ |H τ| ≤ ∫ CW·gaussDdim(lam·τ)` (`integral_mono_of_nonneg`; the dominator is integrable,
    `gaussDdim_integrable`), and `∫ CW·gaussDdim(lam·τ) = CW·1 = CW` (`integral_const_mul` +
    `gaussDdim_integral_eq_one`, the Gaussian total mass one).  ⚠ NOT `a₁ = R/6`. -/
theorem witnessSlice_mass_le
    (H : ℝ → Point n → ℝ) (lam CW τ₀ : ℝ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |H τ z| ≤ CW * gaussDdim (lam * τ) z)
    (τ : ℝ) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀) :
    ∫ z, |H τ z| ≤ CW := by
  have hlamτ : 0 < lam * τ := mul_pos hlam hτ
  have hg_int : Integrable (fun z : Point n => CW * gaussDdim (lam * τ) z) volume :=
    (gaussDdim_integrable (lam * τ) hlamτ).const_mul CW
  have hle : ∫ (z : Point n), |H τ z| ≤ ∫ (z : Point n), CW * gaussDdim (lam * τ) z := by
    refine integral_mono_of_nonneg (ae_of_all _ (fun z => abs_nonneg _)) hg_int ?_
    exact ae_of_all _ (fun z => hDom τ hτ hττ₀ z)
  calc ∫ (z : Point n), |H τ z|
      ≤ ∫ (z : Point n), CW * gaussDdim (lam * τ) z := hle
    _ = CW * ∫ (z : Point n), gaussDdim (lam * τ) z := integral_const_mul CW _
    _ = CW * 1 := by rw [gaussDdim_integral_eq_one (lam * τ) hlamτ]
    _ = CW := mul_one CW

/-- **★ (ii) `epsSeq_witnessSlice_mass_eventually_le`.**  The witness mass bound along the boundary
    sequence `ε_m → 0⁺`: since `ε_m → 0` and `0 < τ₀`, eventually `ε_m ≤ τ₀`, so
        `∀ᶠ m, ∫ z, |H (ε_m) z| ≤ CW`.
    This is the uniform-in-`m` on-ball mass factor of the moving-correction estimate.
    ⚠ NOT `a₁ = R/6`. -/
theorem epsSeq_witnessSlice_mass_eventually_le
    (H : ℝ → Point n → ℝ) (lam CW τ₀ : ℝ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |H τ z| ≤ CW * gaussDdim (lam * τ) z) :
    ∀ᶠ m in atTop, ∫ z, |H (epsSeq m) z| ≤ CW := by
  have hev : ∀ᶠ m in atTop, epsSeq m ≤ τ₀ := by
    have h := epsSeq_tendsto.eventually (Iic_mem_nhds hτ₀)
    filter_upwards [h] with m hm
    exact Set.mem_Iic.mp hm
  filter_upwards [hev] with m hm
  exact witnessSlice_mass_le H lam CW τ₀ hlam hCW hτ₀ hDom (epsSeq m) (epsSeq_pos m) hm

#check @leviSlice_z_continuousOn_of_termwise
#check @leviSlice_z_continuousAt_zero_of_termwise
#check @leviSlice_jointContinuousOn_of_termwise
#check @witnessSlice_mass_le
#check @epsSeq_witnessSlice_mass_eventually_le

end QIQTH.MovingCorrAssembly

section AxiomChecks
open QIQTH.MovingCorrAssembly
#print axioms leviSlice_z_continuousOn_of_termwise
#print axioms leviSlice_z_continuousAt_zero_of_termwise
#print axioms leviSlice_jointContinuousOn_of_termwise
#print axioms witnessSlice_mass_le
#print axioms epsSeq_witnessSlice_mass_eventually_le
end AxiomChecks
