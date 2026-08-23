/-
  HFrozenAIUniform — J4-1096: the `hfroLU` abstract engine (window-uniform FROZEN approximate
  identity), the `u`-uniform sibling of `LocUnifDerivConv.movingCorr_tUniform` (L1) completing the
  `hbdryLU_of_movingCorr_frozen` (J4-... `LocUnifDerivConv.lean:300`) composer's SECOND input.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  chart-FREE, kernel-agnostic real-analysis brick.  No `sorry` (header prose excepted), no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding)
  the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT — the `hfroLU` slot.

  `LocUnifDerivConv.hbdryLU_of_movingCorr_frozen` (banked, J4-... `LocUnifDerivConv.lean:300`) is a
  FULLY ABSTRACT composer (`H F : ℝ → Point n → Point n → ℝ` free variables — no chart references in
  its own signature) needing two unsupplied inputs, `hmovLU` and `hfroLU`:

      `hfroLU : TendstoLocallyUniformlyOn
          (fun m u => ∫ z, H (epsSeq m) 0 z * F u z 0) (fun u => F u 0 0) atTop U`

  i.e. the FROZEN approximate-identity family `u ↦ ∫ z, H(ε_m) 0 z · F u z 0` (a Dirac-sequence
  concentration at `z = 0` of the slice `F u · 0`) converges to `u ↦ F u 0 0` LOCALLY UNIFORMLY on the
  open time-set `U`, as the truncation index `m → atTop` (equivalently `ε_m → 0`).  This is a DISTINCT
  gap from `hbnd`'s spatial `∂K` boundary-Christoffel wall (per J4-1095's audit, `gpt-5.6-sol`
  (high)-confirmed): it is an ordinary approximate-identity-in-a-parameter statement.

  ## WHAT THIS FILE LANDS — the `Icc ta tb`-level analytic engine (parallel to L1).

  `LocUnifDerivConv.movingCorr_tUniform` (L1) already proves the analogous `t`-UNIFORM promotion for
  the MOVING-correction term via an abstract 3ε ball/off-ball split, given an abstract witness
  dominated by a Gaussian plus an abstract joint-closeness hypothesis (`hsup`).  This file proves the
  SAME-SHAPE `t`-uniform promotion for the FROZEN term — the genuine remaining mathematical content of
  `hfroLU` — via a 3ε(+mass-defect) split:

    • `frozenAI_tUniform` — ★★★ THE FROZEN-TERM `t`-UNIFORM APPROXIMATE IDENTITY.  From
        (a) `H(τ) 0 ·` dominated by `CW · gaussDdim(lam·τ)` for `0 < τ ≤ τ₀` (`hDom`, exactly the
            `movingCorr_tUniform` shape),
        (b) the EXACT mass limit `∫ z, H(ε_m) 0 z → 1` (`hmass1` — genuinely needed: domination alone
            only bounds the mass, it cannot pin the limit to exactly `1`; `gpt-5.6-sol`-confirmed),
        (c) a GLOBAL bound `|F u z 0| ≤ Cf` (`hFbdd`, `u,z`-free),
        (d) measurability of the two slice families (`hHmeas`, `hFmeas`),
        (e) the JOINT spatial equicontinuity of `F` at `z = 0`, UNIFORM over `u ∈ [ta,tb]` (`hlocal` —
            the genuine new joint-continuity content, analogous in ROLE to L1's `hsup` and to
            `ChartImageApproxIdentity.gaussDdim_set_approx_identity_moving`'s `hlocal`, but here a
            plain deterministic ε-δ statement since the concentration parameter is `m`/`ε_m`, not a
            second continuous variable),
      concludes `TendstoUniformlyOn (fun m u => ∫ z, H (epsSeq m) 0 z * F u z 0) (fun u => F u 0 0)
        atTop (Set.Icc ta tb)`.

  ROUTE.  `∫H·(Fuz0−Fu00) + Fu00·(∫H − 1) = ∫H·Fuz0 − Fu00` (algebraic split); the FIRST term splits
  ball(0,r)/ballᶜ exactly as in L1 (on-ball via `hlocal` + the GLOBAL mass bound `∫|H| ≤ CW`,
  off-ball via the Gaussian domination tail `gaussDdim_ballCompl_mass_tendsto_zero`, reused verbatim
  from `ChartImageApproxIdentity`); the SECOND (mass-defect) term is bounded by `Cf·|mass_m − 1|`,
  eventually small by `hmass1`.  3ε-recombination.  NONE of the five hypotheses is the conclusion; all
  are genuine, independently satisfiable lower ingredients (satisfiability discussed in the theorem
  docstring below).  Does NOT unfold `uniformInverseChart` / `EnrichedChartBundle` / any per-`K`
  `Classical.choose` chart object anywhere — genuinely independent of the exhausted chart-architecture
  wall, per this dispatch's own explicit stop criterion (never triggered).

  ## HONEST REMAINING GAP (NOT closed here).

  `frozenAI_tUniform` is the `Icc ta tb`-level analytic ENGINE.  Two honest gaps remain before `hfroLU`
  is itself discharged: (i) promoting `TendstoUniformlyOn ... (Icc ta tb)` (this file) to the full
  `TendstoLocallyUniformlyOn ... U` target (a standard but unattempted local-neighbourhood wrapper —
  `U` open in `ℝ` is locally compact, so the bridge is available in principle, just not built here);
  (ii) supplying the five hypotheses (`hDom, hmass1, hFbdd, hHmeas, hFmeas, hlocal`) AT THE CONCRETE
  curved-tower instance (`H := vanVleckGatedWitness …`, `F := leviSeries(heatOp …)`) — per this file's
  own header and `LocUnifDerivConv`'s L2 discussion, the concrete `hlocal`/`hmass1` supply for the
  CONCRETE chart-built witness plausibly DOES need `uniformInverseChart`/`EnrichedChartBundle`
  machinery (as `GateAnnulusSplit.chartImage_approx_identity_final` already needed for the
  single-fixed-`f` case) — that is a SEPARATE, NOT-yet-attempted, later dispatch, and MAY be where the
  chart wall is finally met for this branch.  Neither gap is attempted here.  `a₁ = R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import QIQTH.LocUnifDerivConv

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel
open scoped Topology

namespace QIQTH.HFrozenAIUniform

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `frozenAI_tUniform`.**  The `t`-UNIFORM frozen approximate identity: the `hfroLU`
    `Icc ta tb`-level analytic engine.  See file header for the full route and honest scope.  Every
    hypothesis is satisfiable and none is the conclusion: `hDom`/`hHmeas`/`hFmeas`/`hFbdd` are the
    same shape of Gaussian-domination/measurability/global-bound carries used throughout this tower
    (e.g. `movingCorr_tUniform`'s `hDom`/`hWmeas`/`hfmov_bdd`); `hmass1` is the standard
    approximate-identity mass-normalization fact (cf. `gaussDdim_integral_eq_one` for the literal
    Gaussian, here posited for the abstract dominated witness `H`); `hlocal` is the standard joint
    equicontinuity-at-a-point fact for a family of functions on a compact parameter window (available,
    e.g., via Heine–Cantor whenever `(u,z) ↦ F u z 0` is jointly continuous on `Icc ta tb × closedBall 0
    r₀` for some `r₀ > 0` — not derived here, kept as a general external input, exactly as L1's `hsup`
    is later supplied by `EnvelopeWiringLocUnif.heine_timeShift_sup_tendsto_tUniform`).  ⚠ NOT
    `a₁ = R/6`. -/
theorem frozenAI_tUniform
    (H F : ℝ → Point n → Point n → ℝ)
    (ta tb lam CW Cf τ₀ : ℝ)
    (hlam : 0 < lam) (hCW : 0 ≤ CW) (hCf : 0 ≤ Cf) (hτ₀ : 0 < τ₀)
    (hHmeas : ∀ m : ℕ, AEStronglyMeasurable (fun z => H (epsSeq m) 0 z) volume)
    (hFmeas : ∀ u : ℝ, AEStronglyMeasurable (fun z => F u z 0) volume)
    (hFbdd : ∀ u z, |F u z 0| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |H τ 0 z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass1 : Tendsto (fun m => ∫ z, H (epsSeq m) 0 z) atTop (𝓝 (1 : ℝ)))
    (hlocal : ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ u ∈ Set.Icc ta tb, ∀ z : Point n,
        ‖z‖ < r → |F u z 0 - F u 0 0| < ε) :
    TendstoUniformlyOn
      (fun m u => ∫ z, H (epsSeq m) 0 z * F u z 0)
      (fun u => F u 0 0) atTop (Set.Icc ta tb) := by
  have hCf1 : (0 : ℝ) < Cf + 1 := by linarith
  have hCW1 : (0 : ℝ) < CW + 1 := by linarith
  have hcap : ∀ᶠ m in atTop, epsSeq m ≤ τ₀ := by
    have h := epsSeq_tendsto.eventually (Iic_mem_nhds hτ₀)
    filter_upwards [h] with m hm
    exact Set.mem_Iic.mp hm
  have hmassAbsTendsto : Tendsto (fun m => |(∫ z, H (epsSeq m) 0 z) - 1|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => (∫ z, H (epsSeq m) 0 z) - 1) atTop (𝓝 (0 : ℝ)) := by
      simpa using hmass1.sub_const 1
    simpa using h1.abs
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  -- obtain the on-ball radius `r` from `hlocal`, at scale `ε/(3(CW+1))`.
  have hεb : (0 : ℝ) < ε / (3 * (CW + 1)) := by positivity
  obtain ⟨r, hr, hlocalr⟩ := hlocal (ε / (3 * (CW + 1))) hεb
  have hεCf : (0 : ℝ) < ε / (3 * (Cf + 1)) := by positivity
  have hmassEv : ∀ᶠ m in atTop, |(∫ z, H (epsSeq m) 0 z) - 1| < ε / (3 * (Cf + 1)) :=
    hmassAbsTendsto.eventually (Iio_mem_nhds hεCf)
  -- the `u`-free off-ball Gaussian tail along `ε_m`, at radius `r`.
  have hc : Tendsto (fun τ : ℝ => lam * τ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun τ : ℝ => lam * τ) (𝓝 (0 : ℝ)) (𝓝 (lam * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hscale : Tendsto (fun τ : ℝ => lam * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact Set.mem_Ioi.mpr (mul_pos hlam (Set.mem_Ioi.mp hτ))
  have htailτ : Tendsto
      (fun τ => ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim (lam * τ) w)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (QIQTH.ChartImageApproxIdentity.gaussDdim_ballCompl_mass_tendsto_zero (n := n) r hr).comp hscale
  have hGtail : Tendsto
      (fun m => ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim (lam * epsSeq m) w)
      atTop (𝓝 0) :=
    QIQTH.MovingFBoundaryLim.tendsto_comp_epsSeq htailτ
  have htail_scaled : Tendsto
      (fun m => (2 * CW * Cf) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim (lam * epsSeq m) w)
      atTop (𝓝 0) := by
    have h := hGtail.const_mul (2 * CW * Cf)
    simpa using h
  filter_upwards [htail_scaled.eventually (Iio_mem_nhds hε3), hcap, hmassEv]
    with m htailm hcapm hmassm
  have htailm' : (2 * CW * Cf) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim (lam * epsSeq m) w
      < ε / 3 := Set.mem_Iio.mp htailm
  have hτp : 0 < epsSeq m := epsSeq_pos m
  intro u hu
  -- integrability of `H(ε_m) 0 ·` and the product `H(ε_m) 0 · * F u · 0`.
  have hInt_H : Integrable (fun z => H (epsSeq m) 0 z) volume := by
    refine Integrable.mono'
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul CW)
      (hHmeas m) (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs]
    exact hDom (epsSeq m) hτp hcapm z
  have hInt_HF : Integrable (fun z => H (epsSeq m) 0 z * F u z 0) volume := by
    refine Integrable.mono'
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf))
      ((hHmeas m).mul (hFmeas u)) (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hDom (epsSeq m) hτp hcapm z
    have h2 := hFbdd u z
    calc |H (epsSeq m) 0 z| * |F u z 0| ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCW (gaussDdim_nonneg _ _))
      _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
  -- global mass bound `∫|H(ε_m) 0 ·| ≤ CW`.
  have hHabsInt : Integrable (fun z => |H (epsSeq m) 0 z|) volume := hInt_H.abs
  have hHmassBound : (∫ z, |H (epsSeq m) 0 z|) ≤ CW := by
    have hbd : ∀ z, |H (epsSeq m) 0 z| ≤ CW * gaussDdim (lam * epsSeq m) z := fun z =>
      hDom (epsSeq m) hτp hcapm z
    calc (∫ z, |H (epsSeq m) 0 z|)
        ≤ ∫ z, CW * gaussDdim (lam * epsSeq m) z :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => abs_nonneg _))
            ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul CW)
            (ae_of_all _ hbd)
      _ = CW * ∫ z, gaussDdim (lam * epsSeq m) z := integral_const_mul _ _
      _ = CW * 1 := by rw [gaussDdim_integral_eq_one (lam * epsSeq m) (mul_pos hlam hτp)]
      _ = CW := mul_one _
  -- the algebraic rewrite: `∫HF - Fu00 = ∫H·(F−Fu00) + Fu00·(∫H − 1)`.
  have hc0 : Integrable (fun z => H (epsSeq m) 0 z * F u 0 0) volume := hInt_H.mul_const _
  have hIntDiff : Integrable (fun z => H (epsSeq m) 0 z * (F u z 0 - F u 0 0)) volume := by
    have heq : (fun z => H (epsSeq m) 0 z * (F u z 0 - F u 0 0))
        = fun z => H (epsSeq m) 0 z * F u z 0 - H (epsSeq m) 0 z * F u 0 0 := by
      funext z; ring
    rw [heq]; exact hInt_HF.sub hc0
  have hsplit : (∫ z, H (epsSeq m) 0 z * F u z 0) - F u 0 0
      = (∫ z, H (epsSeq m) 0 z * (F u z 0 - F u 0 0))
        + F u 0 0 * ((∫ z, H (epsSeq m) 0 z) - 1) := by
    have heq : (fun z => H (epsSeq m) 0 z * (F u z 0 - F u 0 0))
        = fun z => H (epsSeq m) 0 z * F u z 0 - H (epsSeq m) 0 z * F u 0 0 := by
      funext z; ring
    rw [heq, integral_sub hInt_HF hc0, integral_mul_const]
    ring
  -- the on-ball / off-ball split of the first term.
  have hInt_ball : IntegrableOn
      (fun z => H (epsSeq m) 0 z * (F u z 0 - F u 0 0)) (Metric.ball (0 : Point n) r) volume :=
    hIntDiff.integrableOn
  have hInt_off : IntegrableOn
      (fun z => H (epsSeq m) 0 z * (F u z 0 - F u 0 0)) (Metric.ball (0 : Point n) r)ᶜ volume :=
    hIntDiff.integrableOn
  have honball : |∫ z in Metric.ball (0 : Point n) r, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)|
      < ε / 3 := by
    have hmaj : IntegrableOn (fun z => (ε / (3 * (CW + 1))) * |H (epsSeq m) 0 z|)
        (Metric.ball (0 : Point n) r) volume :=
      (hHabsInt.const_mul (ε / (3 * (CW + 1)))).integrableOn
    have hbound :
        |∫ z in Metric.ball (0 : Point n) r, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)|
          ≤ (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) r, |H (epsSeq m) 0 z| := by
      rw [← Real.norm_eq_abs]
      calc ‖∫ z in Metric.ball (0 : Point n) r, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)‖
          ≤ ∫ z in Metric.ball (0 : Point n) r, ‖H (epsSeq m) 0 z * (F u z 0 - F u 0 0)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ z in Metric.ball (0 : Point n) r, (ε / (3 * (CW + 1))) * |H (epsSeq m) 0 z| := by
            refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hmaj ?_
            refine (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ (fun z hz => ?_))
            simp only [Real.norm_eq_abs, abs_mul]
            have hlt := le_of_lt (hlocalr u hu z (by simpa using hz))
            calc |H (epsSeq m) 0 z| * |F u z 0 - F u 0 0|
                ≤ |H (epsSeq m) 0 z| * (ε / (3 * (CW + 1))) :=
                  mul_le_mul_of_nonneg_left hlt (abs_nonneg _)
              _ = (ε / (3 * (CW + 1))) * |H (epsSeq m) 0 z| := by ring
        _ = (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) r, |H (epsSeq m) 0 z| :=
            integral_const_mul _ _
    have hballmass : (∫ z in Metric.ball (0 : Point n) r, |H (epsSeq m) 0 z|) ≤ CW :=
      le_trans (setIntegral_le_integral hHabsInt (ae_of_all _ (fun z => abs_nonneg _)))
        hHmassBound
    have hfin : (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) r, |H (epsSeq m) 0 z|
        ≤ (ε / (3 * (CW + 1))) * CW :=
      mul_le_mul_of_nonneg_left hballmass (le_of_lt hεb)
    have hlt' : (ε / (3 * (CW + 1))) * CW < ε / 3 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 3 * (CW + 1))]
      nlinarith [hε, hCW]
    calc |∫ z in Metric.ball (0 : Point n) r, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)|
        ≤ (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) r, |H (epsSeq m) 0 z| := hbound
      _ ≤ (ε / (3 * (CW + 1))) * CW := hfin
      _ < ε / 3 := hlt'
  have hoffball : |∫ z in (Metric.ball (0 : Point n) r)ᶜ, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)|
      < ε / 3 := by
    have hgint : IntegrableOn (fun z : Point n => (2 * CW * Cf) * gaussDdim (lam * epsSeq m) z)
        (Metric.ball (0 : Point n) r)ᶜ volume :=
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul
        (2 * CW * Cf)).integrableOn
    have hstep :
        |∫ z in (Metric.ball (0 : Point n) r)ᶜ, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)|
          ≤ (2 * CW * Cf) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim (lam * epsSeq m) w := by
      rw [← Real.norm_eq_abs]
      calc ‖∫ z in (Metric.ball (0 : Point n) r)ᶜ, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)‖
          ≤ ∫ z in (Metric.ball (0 : Point n) r)ᶜ, ‖H (epsSeq m) 0 z * (F u z 0 - F u 0 0)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ z in (Metric.ball (0 : Point n) r)ᶜ, (2 * CW * Cf) * gaussDdim (lam * epsSeq m) z := by
            refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hgint ?_
            refine ae_of_all _ (fun z => ?_)
            simp only [Real.norm_eq_abs, abs_mul]
            have h1 := hDom (epsSeq m) hτp hcapm z
            have h2 : |F u z 0 - F u 0 0| ≤ 2 * Cf := by
              have hz0 := hFbdd u z
              have h00 := hFbdd u 0
              calc |F u z 0 - F u 0 0| ≤ |F u z 0| + |F u 0 0| := abs_sub _ _
                _ ≤ Cf + Cf := add_le_add hz0 h00
                _ = 2 * Cf := by ring
            have hg0 := gaussDdim_nonneg (lam * epsSeq m) z
            calc |H (epsSeq m) 0 z| * |F u z 0 - F u 0 0|
                ≤ (CW * gaussDdim (lam * epsSeq m) z) * (2 * Cf) :=
                  mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCW hg0)
              _ = (2 * CW * Cf) * gaussDdim (lam * epsSeq m) z := by ring
        _ = (2 * CW * Cf) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim (lam * epsSeq m) w := by
            rw [integral_const_mul]
    exact lt_of_le_of_lt hstep htailm'
  have hfirstTerm : |∫ z, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)| < 2 * (ε / 3) := by
    rw [← integral_add_compl measurableSet_ball hIntDiff]
    calc |(∫ z in Metric.ball (0 : Point n) r, H (epsSeq m) 0 z * (F u z 0 - F u 0 0))
            + ∫ z in (Metric.ball (0 : Point n) r)ᶜ, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)|
        ≤ |∫ z in Metric.ball (0 : Point n) r, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)|
          + |∫ z in (Metric.ball (0 : Point n) r)ᶜ, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)| :=
          abs_add_le _ _
      _ < ε / 3 + ε / 3 := add_lt_add honball hoffball
      _ = 2 * (ε / 3) := by ring
  have hsecondTerm : |F u 0 0 * ((∫ z, H (epsSeq m) 0 z) - 1)| < ε / 3 := by
    rw [abs_mul]
    have h1 : |F u 0 0| ≤ Cf := hFbdd u 0
    have h2 : |(∫ z, H (epsSeq m) 0 z) - 1| < ε / (3 * (Cf + 1)) := hmassm
    have h3 : |F u 0 0| * |(∫ z, H (epsSeq m) 0 z) - 1| ≤ Cf * |(∫ z, H (epsSeq m) 0 z) - 1| :=
      mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have h4 : Cf * |(∫ z, H (epsSeq m) 0 z) - 1| ≤ Cf * (ε / (3 * (Cf + 1))) :=
      mul_le_mul_of_nonneg_left h2.le hCf
    have h5 : Cf * (ε / (3 * (Cf + 1))) < ε / 3 := by
      have heq : Cf * (ε / (3 * (Cf + 1))) = (Cf * ε) / (3 * (Cf + 1)) := by ring
      rw [heq, div_lt_iff₀ (by positivity : (0:ℝ) < 3 * (Cf + 1))]
      nlinarith [hε, hCf]
    linarith [h3, h4, h5]
  have hdist : dist (F u 0 0) (∫ z, H (epsSeq m) 0 z * F u z 0) < ε := by
    rw [Real.dist_eq]
    calc |F u 0 0 - ∫ z, H (epsSeq m) 0 z * F u z 0|
        = |(∫ z, H (epsSeq m) 0 z * (F u z 0 - F u 0 0))
            + F u 0 0 * ((∫ z, H (epsSeq m) 0 z) - 1)| := by
          rw [← abs_neg]; rw [show -(F u 0 0 - ∫ z, H (epsSeq m) 0 z * F u z 0)
            = (∫ z, H (epsSeq m) 0 z * F u z 0) - F u 0 0 by ring, hsplit]
      _ ≤ |∫ z, H (epsSeq m) 0 z * (F u z 0 - F u 0 0)|
          + |F u 0 0 * ((∫ z, H (epsSeq m) 0 z) - 1)| := abs_add_le _ _
      _ < 2 * (ε / 3) + ε / 3 := add_lt_add hfirstTerm hsecondTerm
      _ = ε := by ring
  exact hdist

end QIQTH.HFrozenAIUniform

section AxiomChecks
open QIQTH.HFrozenAIUniform
#print axioms frozenAI_tUniform
end AxiomChecks
