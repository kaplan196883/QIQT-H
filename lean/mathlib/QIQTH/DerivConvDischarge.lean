/-
  DerivConvDischarge — J4-243: THE `hDerivConv` DISCHARGE — closing the last carried pointwise limit
  of the `core` slot on the `a1_R6_assembled_v2'` surface.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is a pure
  RE-PLUMBING / COMPOSITION brick.  It wires the ALREADY-LANDED limit machinery of
  `DuhamelLimitWiring` + `F2FamilyDischarge` into the single carried pointwise-limit residue
  `hDerivConv` that `EnvelopeCoreDischarge.core_of_v2prime_data` (J4-242) left open, then composes the
  two so that the `TruncatedDuhamelCore` bundle needs NOTHING beyond `a1_R6_assembled_v2'`'s existing
  binders.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## THE RESIDUE.  `core_of_v2prime_data` (J4-242) reduced the opaque `core` bundle to EXACTLY three
  truncation limits, of which two were discharged FREE and the third carried:

    · `hDaLim`       ← `ETailRateBound.hDaLimLU_from_data` ∘ `daLimLU_reduces_to_pointwise`   (FREE);
    · `hBoundaryLim` ← `HeatResidualBound.boundaryTrunc_tendsto`                               (FREE);
    · `hDerivConv`   ← the SINGLE carried pointwise limit
                          `Tendsto (fun m => DaTrunc Wit F m t + BoundaryTrunc Wit F m t) atTop
                             (𝓝 (deriv (fun u => heatConv Wit F u 0 0) t))`   (SIZE-REJECTED at R3).

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## WHAT LANDS.

    (1) `derivConv_of_data` — `hDerivConv` DISCHARGED from the boundary pile + the F2 regularity pile +
        the loc-unif `Da`-limit `hDaLimLU`.  This is EXACTLY the internal `hDerivConv` build of
        `DuhamelLimitWiring.hDuhamel_final` (lines 260–287 there), lifted out standalone, with the F2
        carries `hFII`/`hpar`/`htime`/`hR` supplied by the `F2FamilyDischarge` dischargers.  Route:
          · `heatConvInner_intervalIntegrable_H` → `hFII`   (R4, F1 domination);
          · `hpar_discharge` → `hpar`                         (R2, C3ε under-∫ Leibniz);
          · `htime_discharge` → `htime`                       (R1, FTC upper-limit at the gap);
          · `hR_discharge` → `hR`                             (R3, mixed-difference little-o);
          · `truncDuhamel_hasDerivAt` (per `m`) → the truncated `HasDerivAt` family `hderiv`;
          · `heatConv_tail_tendsto` + `hFII` → the tail convergence `hfg`;
          · `boundary_tendstoLocallyUniformlyOn` (in `BoundaryTrunc` shape) → `hbdryLU`;
          · `tendstoLocallyUniformlyOn_add hDaLimLU hbdryLU` → `hDerivLU`;
          · `derivConv_tendsto` closes it.

    (2) `core_of_v2prime_data_FULL` — the `TruncatedDuhamelCore g gi Wit t` bundle built with ALL THREE
        limits discharged internally.  Builds `hDaLimLU` (via `hDaLimLU_from_data`, exactly as
        `core_of_v2prime_data`), feeds it + the boundary/F2 piles into `derivConv_of_data` to get
        `hDerivConv`, then hands `hDerivConv` to `core_of_v2prime_data`.  Its binders are a SUBSET of
        `RightInverseGeneral.a1_R6_assembled_v2'`'s own binders (the `hDaLimLU_from_data` pile + the
        boundary pile + the F2 pile, all carried at the `v2'` surface — including `hAzero`), so the
        `core` slot of `a1_R6_assembled_v2'` is now DISCHARGED with NO new data.

  Pure composition — NO new analysis.  NOT `a₁ = R/6`.

  NO `sorry`.  NO new axioms.  NO `:= True`.  NO vacuous hypotheses.
-/
import Mathlib
import QIQTH.F2FamilyDischarge
import QIQTH.EnvelopeCoreDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound
open scoped Interval Topology BigOperators

namespace QIQTH.DerivConvDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (1) `derivConv_of_data` — `hDerivConv` from the boundary + F2 piles + `hDaLimLU`.
    ############################################################################### -/

/-- **★★★ J4-243 (1) — `hDerivConv` DISCHARGED.**  The single carried pointwise limit
        `Tendsto (fun m => DaTrunc H F m t + BoundaryTrunc H F m t) atTop
           (𝓝 (deriv (fun u => heatConv H F u 0 0) t))`,
    built from the boundary parametrix interface, the F2 regularity pile (measurability / floor /
    inner-continuity / C3ε engine / cross-Lipschitz), and the hard loc-unif `Da`-limit `hDaLimLU`.
    Verbatim the internal `hDerivConv` construction of `DuhamelLimitWiring.hDuhamel_final`, with the
    F2 carries supplied by the `F2FamilyDischarge` dischargers.  ⚠ CONDITIONAL on the listed carries;
    none is the conclusion.  NOT `a₁ = R/6`. -/
theorem derivConv_of_data (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (t T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        H τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, H τ p q = 0)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn (fun x : ℝ × Point n => F x.1 x.2 0) (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => H τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    -- F2-discharge carries (R4):
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
              + heatConv (heatOp g gi H) F u 0 0) atTop U) :
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
  -- the loc-unif boundary limit, in the `BoundaryTrunc` shape.
  have hbdry0 := boundary_tendstoLocallyUniformlyOn H F T hT U hUopen hUpos hUT r₀ τ₀ hr₀ hτ₀
    u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont
    hAmeas hBmeas hu₀meas hu₁meas
  have hbdryLU : TendstoLocallyUniformlyOn (fun m u => BoundaryTrunc H F m u)
      (fun u => F u 0 0) atTop U := by
    have hfun : (fun m u => BoundaryTrunc H F m u)
        = (fun m u => ∫ z, H (epsSeq m) 0 z * F (u - epsSeq m) z 0) := by
      funext m u; simp only [BoundaryTrunc, sub_sub_cancel]
    rw [hfun]; exact hbdry0
  -- the loc-unif derivative limit `DaTrunc + BoundaryTrunc → D`.
  have hDerivLU := tendstoLocallyUniformlyOn_add hDaLimLU hbdryLU
  -- close with `hasDerivAt_of_tendstoLocallyUniformlyOn` (W3).
  exact derivConv_tendsto H F t U hUopen htU hderiv _ hDerivLU hfg

/-! ###############################################################################
    ### (2) `core_of_v2prime_data_FULL` — the `TruncatedDuhamelCore` with ALL THREE limits internal.
    ############################################################################### -/

/-- **★★★★ J4-243 (2) — `core_of_v2prime_data_FULL`.**  The `TruncatedDuhamelCore g gi Wit t` bundle
    — the opaque `core` binder of `RightInverseGeneral.a1_R6_assembled_v2'` — built INTERNALLY with
    ALL THREE truncation limits discharged, needing NOTHING beyond the data `a1_R6_assembled_v2'`
    already carries (the `hDaLimLU_from_data` pile + the boundary pile + the F2 regularity pile,
    including `hAzero`).

    Route: builds `hDaLimLU` via `ETailRateBound.hDaLimLU_from_data` (exactly as
    `EnvelopeCoreDischarge.core_of_v2prime_data`), feeds it + the boundary/F2 piles into
    `derivConv_of_data` to obtain the last carried limit `hDerivConv`, then hands `hDerivConv` to
    `core_of_v2prime_data`.  Abstract in `Wit`; `F := leviSeries (heatOp g gi Wit)`.  Genuine
    composition — NO new analysis.  NOT `a₁ = R/6`. -/
theorem core_of_v2prime_data_FULL (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    -- gauge (RNC normalization at the centre).
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    -- the `hDaLimLU_from_data` interchange trio + integrabilities + sliver amplitudes + dominations.
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : MemInterchange Wit (leviSeries (heatOp g gi Wit)) U pdpdH)
    (hLapFull : MemLapFull g gi Wit (leviSeries (heatOp g gi Wit)) U pdpdH)
    (hII_lo : MemAdjLo (leviSeries (heatOp g gi Wit)) U pdpdH)
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi Wit)) U pdpdH)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1nn : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z
            * leviSeries (heatOp g gi Wit) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L)
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi Wit τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzeroE : ∀ τ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi Wit τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi Wit) s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, leviSeries (heatOp g gi Wit) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi Wit (u - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi Wit (u - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi Wit (leviSeries (heatOp g gi Wit)))
    -- the boundary pile (near-diagonal parametrix interface for `hBoundaryLim`/`hbdryLU`).
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        Wit τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |Wit τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, Wit τ p q = 0)
    (hBcont : ContinuousOn
        (fun x : ℝ × Point n => leviSeries (heatOp g gi Wit) x.1 x.2 0)
        (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => Wit τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable
        (fun z : Point n => leviSeries (heatOp g gi Wit) s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    -- the F2 regularity pile (feeds `derivConv_of_data`).
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, Wit (u - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, Wit (u - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
        (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ a, AEStronglyMeasurable
      (fun s => ∫ z, Wit (a - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, Wit (u - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => Wit r 0 z) (u - s) * leviSeries (heatOp g gi Wit) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m u,
      ‖∫ z, deriv (fun r => Wit r 0 z) (a - s) * leviSeries (heatOp g gi Wit) s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m u,
      HasDerivAt (fun a => ∫ z, Wit (a - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
        (∫ z, deriv (fun r => Wit r 0 z) (a - s) * leviSeries (heatOp g gi Wit) s z 0) a)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen Wit (leviSeries (heatOp g gi Wit)) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen Wit (leviSeries (heatOp g gi Wit)) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen Wit (leviSeries (heatOp g gi Wit)) u (u - epsSeq m + k) 0 0
          + heatConvFrozen Wit (leviSeries (heatOp g gi Wit)) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|)) :
    TruncatedDuhamelCore g gi Wit t := by
  -- extract the uniform time floor `aT` from `hUfloor`.
  obtain ⟨aT, haT, hUlb⟩ := id hUfloor
  -- the hard loc-unif `Da`-limit — exactly the `core_of_v2prime_data` build.
  have hDaLimLU := QIQTH.ETailRateBound.hDaLimLU_from_data g gi
    Wit (leviSeries (heatOp g gi Wit))
    T U hUopen hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi
    D0 D1 hD0 hD1nn hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT
    hEdom hEzeroE hBdom hFzero hIlo hIhi hEcomb
  -- the last carried limit `hDerivConv`, discharged from the boundary + F2 piles + `hDaLimLU`.
  have hDerivConv := derivConv_of_data g gi Wit (leviSeries (heatOp g gi Wit)) t T hT
    U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross hDaLimLU
  -- compose with `core_of_v2prime_data` (which discharges `hDaLim`/`hBoundaryLim` internally).
  exact QIQTH.EnvelopeCoreDischarge.core_of_v2prime_data g gi Wit t T hT
    U hUopen htU hUpos hUT hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi
    D0 D1 hD0 hD1nn hbnd E₀ E₁ C_L hE₀ hE₁ hC_L hUfloor hEdom hEzeroE hBdom hFzero hIlo hIhi hEcomb
    r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd A₀ A₁ hA₀ hA₁ hAdom
    hBcont hAmeas hBmeas hu₀meas hu₁meas hDerivConv

end QIQTH.DerivConvDischarge

section AxiomChecks
open QIQTH.DerivConvDischarge
#print axioms derivConv_of_data
#print axioms core_of_v2prime_data_FULL
end AxiomChecks
