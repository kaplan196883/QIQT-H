/-
  HDerivConvComposition — J4-310: the W1-free `hDerivConv` composition.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / limit-plumbing brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT — the a₁=R/6 campaign, the W1-free boundary side.

  `DerivConvDischarge.derivConv_of_data` (J4-243) builds its last carried limit `hDerivConv` from an
  INTERNAL loc-unif boundary member `hbdryLU`, which it obtains from
  `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn` — the **W1 structural provider** (the concrete
  van-Vleck witness is Gaussian at the CHART IMAGE, not at `z`, so that provider's `hAnear` carry is
  NOT satisfiable at a general gate).  `TUniformFrozenAI.hbdryLU_W1free_of_frozen_locUnif` (T5, J4-309)
  produces EXACTLY that `hbdryLU` slot (`LocUnifDerivConv.hbdryLUTarget`) **W1-free**, carrying only the
  moving-side loc-unif `hmovLU` plus the frozen approximate-identity satisfiable list.

  ## WHAT THIS FILE LANDS.

    • (H1) `hmovLU_concrete` — the loc-unif promotion of `LocUnifDerivConv.movingCorr_tUniform`:
      `.mono hUsub |>.tendstoLocallyUniformlyOn` then a `BoundaryTrunc`-shape `.congr`.  Produces the
      exact `hmovLU` carry that T5 wants, from the satisfiable moving-side list (no `hmovLU` carry).

    • (H2) `hbdryLU_CONCRETE` — T5 fed with (H1): the W1-free `hbdryLU` slot (`hbdryLUTarget H F U`)
      under ONLY the satisfiable frozen + moving lists — NO abstract `hmovLU` carry.

    • (H3) `hDerivConv_conditional` — steps (b)+(c) of `derivConv_of_data` replicated feeding OUR
      W1-free `hbdryLU` (a hypothesis) in place of the W1 provider: `tendstoLocallyUniformlyOn_add`
      with the loc-unif `Da`-limit `hDaLimLU`, then `derivConv_tendsto`.  The whole boundary W1 pile
      (`hAnear`, `u₀`/`u₁` near-parametrix, `hBcont`, `hAmeas`, `hu₀…`) is DROPPED; the F2 regularity
      pile + `hFII` pile are retained (they are unrelated to W1).

    • (H4) `truncatedDuhamelCore_conditional` — the pile map: `hBoundaryLim` (DONE, W1-free via
      `EnvelopeWiringLocUnif.hBoundaryLim_DONE`) + `hDaLimLU` (loc-unif, → pointwise `hDaLim` at `t`
      via `.tendsto_at`) + `hDerivConv` (H3) ⟹ `TruncatedDuhamelData.TruncatedDuhamelCore`, via
      `truncatedDuhamelCore_of_daLim`.

  ## THE UNTRUNCATED-GATE VERDICT.
  The W1 flag (the `hAnear` chart-image-vs-`z` Gaussian wall) blocks the **provider-∃ EXPORT** of
  `hDuhamel`/`hDConv` at the provider-CHOSEN gate `S` (`DaLimLUConcreteDischarge` §"WHY THE PROVIDER-∃
  EXPORT … IS NOT ATTEMPTED"), NOT the FIXED-gate `hDerivConv` composition of THIS file.  At the fixed
  gate the boundary side is now W1-FREE: `hbdryLU` comes from H1/H2 (moving side = `movingCorr_tUniform`,
  engine `heine_timeShift_sup_tendsto_tUniform`, W1-free) + the frozen AI (`chartImage_approx_identity_-`
  `final`, no `hAnear`), and the pointwise `hBoundaryLim` from `hBoundaryLim_DONE` (W1-free).  So (H3)
  removes W1 from the fixed-gate `hDerivConv`; the provider-∃ export at the chosen gate is a SEPARATE
  composition, unaffected here and still blocked on W1.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import QIQTH.TUniformFrozenAI
import QIQTH.TruncatedDuhamelData

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData
open scoped Interval Topology BigOperators

namespace QIQTH.HDerivConvComposition

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (H1) — `hmovLU_concrete`: the loc-unif promotion of `movingCorr_tUniform`.
    ############################################################################### -/

/-- **★★★ (H1) `hmovLU_concrete`.**  The loc-unif promotion of `LocUnifDerivConv.movingCorr_tUniform`
    to the EXACT `hmovLU` carry that `TUniformFrozenAI.hbdryLU_W1free_of_frozen_locUnif` (T5) consumes:
        `TendstoLocallyUniformlyOn
            (fun m u => BoundaryTrunc H F m u − ∫ z, H (ε_m) 0 z · F u z 0) (fun _ => 0) atTop U`.
    Route: instantiate `movingCorr_tUniform` at `W τ z := H τ 0 z`, `fmov m u z := F (u − ε_m) z 0`,
    `ffro u z := F u z 0` (so `∫ W(ε_m)·fmov m u = BoundaryTrunc H F m u` up to `sub_sub_cancel`, and
    `∫ W(ε_m)·ffro u = ∫ z, H(ε_m) 0 z · F u z 0`); `.mono hUsub` restricts the window `[ta,tb]` to `U`,
    `.tendstoLocallyUniformlyOn` promotes, and `.congr` rewrites the moving integral into `BoundaryTrunc`.
    Every hypothesis is the satisfiable moving-side list (`hsup` = `heine_timeShift_sup_tendsto_-`
    `tUniform`; the mass/dominations/window bounds = the Levi envelope + witness domination); NONE is the
    conclusion, and there is NO abstract `hmovLU` carry.  ⚠ NOT `a₁ = R/6`. -/
theorem hmovLU_concrete
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (ρ lam CW Cf τ₀ ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (fun z => H τ (0 : Point n) z) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |H τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |H (epsSeq m) (0 : Point n) z| ≤ CW)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb) :
    TendstoLocallyUniformlyOn
      (fun m u => BoundaryTrunc H F m u - ∫ z, H (epsSeq m) (0 : Point n) z * F u z (0 : Point n))
      (fun _ => (0 : ℝ)) atTop U := by
  have hL1 := QIQTH.LocUnifDerivConv.movingCorr_tUniform
    (fun τ z => H τ (0 : Point n) z) (fun m u z => F (u - epsSeq m) z (0 : Point n))
    (fun u z => F u z (0 : Point n)) ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀
    hWmeas hfmov_meas hffro_meas hfmov_bdd hffro_bdd hDom hmass hsup
  have hLU := (hL1.mono hUsub).tendstoLocallyUniformlyOn
  exact hLU.congr (fun m u _ => by simp only [BoundaryTrunc, sub_sub_cancel])

/-! ###############################################################################
    ### (H2) — `hbdryLU_CONCRETE`: T5 fed with (H1); NO abstract `hmovLU` carry.
    ############################################################################### -/

/-- **★★★ (H2) `hbdryLU_CONCRETE`.**  The W1-free `hbdryLU` slot `LocUnifDerivConv.hbdryLUTarget H F U`
    assembled under ONLY the satisfiable frozen + moving lists — the T5 output with its `hmovLU` carry
    now discharged by (H1) `hmovLU_concrete`.  Feeds `TUniformFrozenAI.hbdryLU_W1free_of_frozen_locUnif`
    the frozen list (witness envelope + `hmassone` (T1) + `hmod` (T2) + window bound) and the moving
    loc-unif produced from the moving list (H1, engine `movingCorr_tUniform`).  NONE of the hypotheses is
    the conclusion; NONE is `hAnear` (W1 is absent from the boundary side entirely).  ⚠ NOT `a₁ = R/6`. -/
theorem hbdryLU_CONCRETE
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (ρ lam CW Cf τ₀ ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (fun z => H τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |H τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |H (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto (fun m => ∫ z, H (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb) :
    QIQTH.LocUnifDerivConv.hbdryLUTarget H F U := by
  have hmovLU := hmovLU_concrete H F U ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀
    hWmeas hfmov_meas hffro_meas hfmov_bdd hffro_bdd hDom hmass hsup hUsub
  exact QIQTH.TUniformFrozenAI.hbdryLU_W1free_of_frozen_locUnif H F U
    lam CW Cf τ₀ ta tb hlam hCW hτ₀ hWmeas hffro_meas hffro_bdd hDom hmass hmassone hmod hUsub hmovLU

/-! ###############################################################################
    ### (H3) — `hDerivConv_conditional`: `derivConv_of_data` steps (b)+(c), W1-free.
    ############################################################################### -/

/-- **★★★ (H3) `hDerivConv_conditional`.**  The `hDerivConv` pointwise limit
        `Tendsto (fun m => DaTrunc H F m t + BoundaryTrunc H F m t) atTop
           (𝓝 (deriv (fun u => heatConv H F u 0 0) t))`,
    built EXACTLY as `DerivConvDischarge.derivConv_of_data`'s internal construction EXCEPT that the
    W1 boundary provider (`BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`, needing the `hAnear`
    chart-image factorization) is REPLACED by OUR W1-free `hbdryLU : LocUnifDerivConv.hbdryLUTarget H F U`
    (produced by (H2) `hbdryLU_CONCRETE`).  The retained pile is the F2 regularity family
    (`hpar`/`htime`/`hR` via the `F2FamilyDischarge` dischargers) + the tail-integrability `hFII` pile +
    the loc-unif `Da`-limit `hDaLimLU` — NONE of which references W1.  The dropped boundary carries
    (`r₀`/`τ₀`/`u₀`/`u₁`/`hAnear`/`hu₀…`/`C₀`/`C₁`/`hBcont`/`hAmeas`/`hBmeas`/`hu₀meas`/`hu₁meas`) are the
    entire W1 pile.  Route: `truncDuhamel_hasDerivAt` per `m` → `hderiv`; `heatConv_tail_tendsto` + `hFII`
    → `hfg`; `tendstoLocallyUniformlyOn_add hDaLimLU hbdryLU` → `hDerivLU`; `derivConv_tendsto` closes.
    ⚠ CONDITIONAL on the listed carries; NONE is the conclusion.  NOT `a₁ = R/6`. -/
theorem hDerivConv_conditional (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (t T : ℝ) (_hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    -- F2 tail-integrability (`hFII`) pile (R4):
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, H τ p q = 0)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, H (u - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 u)))
    -- F2-discharge carries (R1):
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, H (u - s) 0 z * F s z 0) (Set.Ioo 0 u))
    -- F2-discharge carries (R2):
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ a, AEStronglyMeasurable
      (fun s => ∫ z, H (a - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m u,
      ‖∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0‖ ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m u,
      HasDerivAt (fun a => ∫ z, H (a - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0) a)
    -- F2-discharge carries (R3):
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen H F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen H F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen H F u (u - epsSeq m + k) 0 0
          + heatConvFrozen H F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- the hard loc-unif `Da`-limit (NOT F2):
    (hDaLimLU : TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
        (fun u => laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
              + heatConv (heatOp g gi H) F u 0 0) atTop U)
    -- ★ THE W1-FREE boundary loc-unif (our (H2) output), replacing the W1 provider:
    (hbdryLU : QIQTH.LocUnifDerivConv.hbdryLUTarget H F U) :
    Tendsto (fun m => DaTrunc H F m t + BoundaryTrunc H F m t) atTop
      (𝓝 (deriv (fun u => heatConv H F u 0 0) t)) := by
  -- F2 group → `hFII`/`hpar`/`htime`/`hR`.
  have hFII := heatConvInner_intervalIntegrable_H H F T U hUpos hUT A₀ A₁ C_L hA₀ hA₁ hC_L
    hAdom hAzero hBdom hMeasFII
  have hpar := hpar_discharge H F U nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
  have htime := htime_discharge H F U hUfloor hFII hInnerCont
  have hR := hR_discharge H F U L hLnn hCross
  -- the truncated `HasDerivAt` family.
  have hderiv : ∀ᶠ m in atTop, ∀ u ∈ U,
      HasDerivAt (fun v => heatConvFrozen H F v (v - epsSeq m) 0 0)
        (DaTrunc H F m u + BoundaryTrunc H F m u) u := by
    filter_upwards [hpar, htime, hR] with m hp ht hr
    intro u hu
    exact truncDuhamel_hasDerivAt H F m u (hp u hu) (ht u hu) (hr u hu)
  -- the tail convergence.
  have hfg : ∀ u ∈ U, Tendsto (fun m => heatConvFrozen H F u (u - epsSeq m) 0 0) atTop
      (𝓝 (heatConv H F u 0 0)) := fun u hu =>
    heatConv_tail_tendsto H F 0 0 u (hUpos u hu) epsSeq epsSeq_pos epsSeq_tendsto (hFII u hu)
  -- the loc-unif derivative limit `DaTrunc + BoundaryTrunc → D`, feeding OUR W1-free `hbdryLU`.
  have hDerivLU := tendstoLocallyUniformlyOn_add hDaLimLU hbdryLU
  -- close with `derivConv_tendsto` (W3).
  exact derivConv_tendsto H F t U hUopen htU hderiv _ hDerivLU hfg

/-! ###############################################################################
    ### (H4) — `truncatedDuhamelCore_conditional`: the pile composed into the Core.
    ############################################################################### -/

/-- **★★★ (H4) `truncatedDuhamelCore_conditional`.**  The `TruncatedDuhamelData.TruncatedDuhamelCore`
    bundle assembled from the three truncation-limit facts, with the loc-unif `Da`-limit `hDaLimLU`
    supplied pointwise-at-`t` (the distinction the Core consumer needs: `truncatedDuhamelCore_of_daLim`
    wants the POINTWISE `hDaLim`, the machinery produces the LOC-UNIF `hDaLimLU` — bridged by
    `.tendsto_at htU`):
      • `hBoundaryLim` — the pointwise boundary limit (DONE W1-free via
        `EnvelopeWiringLocUnif.hBoundaryLim_DONE`);
      • `hDaLimLU`     — the loc-unif `Da`-limit (from the `hDaLimLU_from_data` machinery, e.g.
        `DaLimLUConcreteDischarge.hDaLimLU_concrete`);
      • `hDerivConv`   — the derivative-of-convolution limit (from (H3) `hDerivConv_conditional`,
        W1-free at the fixed gate).
    Route: `truncatedDuhamelCore_of_daLim g gi Wit t hBoundaryLim (hDaLimLU.tendsto_at htU) hDerivConv`.
    Pure composition; NONE of the three is the conclusion; NONE references W1.  ⚠ NOT `a₁ = R/6`. -/
theorem truncatedDuhamelCore_conditional (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t : ℝ) (U : Set ℝ) (htU : t ∈ U)
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc Wit (leviSeries (heatOp g gi Wit)) m t) atTop
        (𝓝 (leviSeries (heatOp g gi Wit) t 0 0)))
    (hDaLimLU : TendstoLocallyUniformlyOn
        (fun m u => DaTrunc Wit (leviSeries (heatOp g gi Wit)) m u)
        (fun u => laplaceBeltrami g gi
              (fun x => heatConv Wit (leviSeries (heatOp g gi Wit)) u x 0) 0
            + heatConv (heatOp g gi Wit) (leviSeries (heatOp g gi Wit)) u 0 0) atTop U)
    (hDerivConv : Tendsto
        (fun m => DaTrunc Wit (leviSeries (heatOp g gi Wit)) m t
          + BoundaryTrunc Wit (leviSeries (heatOp g gi Wit)) m t) atTop
        (𝓝 (deriv (fun u => heatConv Wit (leviSeries (heatOp g gi Wit)) u 0 0) t))) :
    TruncatedDuhamelCore g gi Wit t :=
  truncatedDuhamelCore_of_daLim g gi Wit t hBoundaryLim (hDaLimLU.tendsto_at htU) hDerivConv

end QIQTH.HDerivConvComposition

section AxiomChecks
open QIQTH.HDerivConvComposition
#print axioms hmovLU_concrete
#print axioms hbdryLU_CONCRETE
#print axioms hDerivConv_conditional
#print axioms truncatedDuhamelCore_conditional
end AxiomChecks
