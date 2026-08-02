/-
  DuhamelLimitWiring — J4-123: the LIMIT-WIRING brick that discharges three of the four limit carries
  of the J4-122 reduction (`hDuhamel_of_daLim`), leaving the Duhamel-principle output conditional ONLY
  on the single hard `Da`-limit `hDaLim` (carried in its locally-uniform, specific-value form) plus the
  regularity family (F2 partials, dominations, near-diagonal parametrix).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  `TruncatedDuhamel.hDuhamel_of_daLim` (J4-122) reduced the capstone's `hDuhamel` input to
  THREE limit carries:
      `hBoundaryLim` (`BoundaryTrunc → F t 0 0`),  `hDaLim` (`DaTrunc → Δ(H*F) + E*F`, specific value),
      `hDerivConv`  (`DaTrunc + BoundaryTrunc → deriv (heatConv H F · 0 0) t`).
  This file WIRES the two "soft" carries — `hBoundaryLim` and `hDerivConv` — to already-landed content,
  and lands the `Etrunc` limit (`Etrunc → E*F`, the `E`-part of the `Da`-limit target), leaving the
  capstone conditional only on the loc-unif `Da`-limit `hDaLimLU` + the F2/domination family.

  WHAT LANDS.
    (W1)  `boundaryTrunc_tendsto` — the `hBoundaryLim` instantiation: pointwise-at-`t` of
          `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn` (via `TendstoLocallyUniformlyOn.tendsto_at`),
          reconciling the `H (t − (t − ε_m))` form by `sub_sub_cancel`.
    (W2)  `etrunc_tendsto_of_kernel` / `etrunc_tendsto` — the `Etrunc` limit `Etrunc → heatConv E F t 0 0`
          (`E = heatOp g gi H`).  Since `Etrunc = heatConvFrozen E F t (t − ε_m) 0 0` DEFINITIONALLY, this
          is the tail convergence `ConvApproximants.heatConv_tail_tendsto`, whose sole carry `hFII` is
          discharged by `ConvCarriesDischarge.heatConvInner_intervalIntegrable_gaussianDom` (F1) from the
          D1 domination of `E` and the width-2 domination of `F`.
    (H)   `truncDuhamel_hasDerivAt` — the `HasDerivAt` upgrade of `TruncatedDuhamel.truncDuhamel_deriv`:
          the truncated diagonal map has derivative `DaTrunc + BoundaryTrunc` (needed as an actual
          `HasDerivAt`, not just a `deriv`-equality, to feed `hasDerivAt_of_tendstoLocallyUniformlyOn`).
    (W3)  `derivConv_tendsto` — the `hDerivConv` wiring: `hasDerivAt_of_tendstoLocallyUniformlyOn`
          (the derivative-of-the-limit = limit-of-derivatives fact) from the truncated `HasDerivAt`
          family, the locally-uniform derivative limit, and the pointwise tail convergence, yields
          `deriv (heatConv H F · 0 0) t = D t`; `tendsto_at` then gives `hDerivConv`.
    (W4)  `hDuhamel_final` / `hDuhamel_leviSeries_final` — ★ THE CAPSTONE: threads W1 + W3 (and the
          `Da`-limit via `tendsto_at`) into `hDuhamel_of_daLim`.  The `hDerivConv`'s loc-unif derivative
          limit is assembled by `tendstoLocallyUniformlyOn_add` from `hDaLimLU` and the boundary loc-unif;
          the Levi corollary matches the capstone `hDuhamel` shape VERBATIM.

  ⚠ HONEST FIREWALL.
    LANDED (this file): W1, W2 (kernel + `heatOp` corollary), the `HasDerivAt` upgrade, W3, and the
      capstone W4 — each proven, no `sorry`, no new axioms, no `expRho` in statements.  The three "soft"
      carries `hBoundaryLim`/`Etrunc`-limit/`hDerivConv` of the J4-122 reduction are DISCHARGED to landed
      content (`boundary_tendstoLocallyUniformlyOn`, `heatConv_tail_tendsto`+F1,
      `hasDerivAt_of_tendstoLocallyUniformlyOn`).
    CARRIED (labelled, none the conclusion, none vacuous):
      • `hDaLimLU` — the sole HARD limit, in its locally-uniform SPECIFIC-VALUE form
        (`DaTrunc → Δ_g(H*F) + E*F` loc-unif on `U`); this is the `hDaLim`/`hLap` content, NOT discharged.
      • the F2 regularity family (`hpar`/`htime`/`hR`, eventual) — the away-from-singularity 2-D Leibniz
        partials feeding the truncated `HasDerivAt`.
      • the parametric dominations (`hAdom`/`hBdom`) + near-diagonal parametrix family
        (`hAnear`/`hu₀*`/`hu₁bdd`) + base measurability/continuity — the `boundary_tendstoLocallyUniformlyOn`
        interface, satisfiable by the concrete N=1 gated van-Vleck witness.
      • `hFII` — interval-integrability of the inner `H*F` pairing on `[0,u]` (the tail-convergence carry).
    NOT `a₁ = R/6` — this is ONE brick (the limit-wiring) of the campaign.
-/
import Mathlib
import QIQTH.TruncatedDuhamel
import QIQTH.BoundaryAssembly
import QIQTH.DeltaFamilyBoundary

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### W1 — the `hBoundaryLim` instantiation. -/

/-- **★ J4-123 (W1) — THE `hBoundaryLim` INSTANTIATION.**  The moving-peak boundary term converges
    pointwise at `t`:
        `BoundaryTrunc A B m t  →  B t 0 0`   as `m → ∞`.
    Pointwise-at-`t` specialization (`TendstoLocallyUniformlyOn.tendsto_at`) of the landed local-uniform
    boundary discharge `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`; the `A (t − (t − ε_m))`
    form of `BoundaryTrunc` is reconciled by `sub_sub_cancel` (`t − (t − ε_m) = ε_m`).  ⚠ CONDITIONAL on
    the same near-diagonal parametrix / domination / measurability interface as `boundary_tendsto…`;
    none is the conclusion.  NOT `a₁ = R/6`. -/
theorem boundaryTrunc_tendsto
    (A B : ℝ → Point n → Point n → ℝ) (T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        A τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |A τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |B s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn (fun x : ℝ × Point n => B x.1 x.2 0) (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => B s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    (t : ℝ) (htU : t ∈ U) :
    Tendsto (fun m => BoundaryTrunc A B m t) atTop (𝓝 (B t 0 0)) := by
  have hLU := boundary_tendstoLocallyUniformlyOn A B T hT U hUopen hUpos hUT r₀ τ₀ hr₀ hτ₀
    u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont
    hAmeas hBmeas hu₀meas hu₁meas
  have hpt := hLU.tendsto_at htU
  simpa only [BoundaryTrunc, sub_sub_cancel] using hpt

/-! ### W2 — the `Etrunc` limit. -/

/-- **★ J4-123 (W2, abstract kernel) — THE `Etrunc` LIMIT (abstract).**  For a Gaussian-dominated
    kernel `E'` (D1 domination, vanishing at nonpositive time) and a width-2-dominated `F`, the frozen
    residual convolution converges as `m → ∞`:
        `heatConvFrozen E' F t (t − ε_m) 0 0  →  heatConv E' F t 0 0`.
    This is the tail convergence `heatConv_tail_tendsto` (A2), whose sole carry `hFII` is discharged by
    `heatConvInner_intervalIntegrable_gaussianDom` (F1) from the dominations `hE'dom`/`hE'zero`/`hBdom`
    and the base `s`-measurability `hmeas`.  ⚠ CONDITIONAL only on those (landed) dominations + `hmeas`.
    NOT `a₁ = R/6`. -/
theorem etrunc_tendsto_of_kernel (E' F : ℝ → Point n → Point n → ℝ) (t T : ℝ)
    (ht : 0 < t) (htT : t ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hE'dom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |E' τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hE'zero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, E' τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ (z : Point n), E' (t - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 t))) :
    Tendsto (fun m => heatConvFrozen E' F t (t - epsSeq m) 0 0) atTop
      (𝓝 (heatConv E' F t 0 0)) := by
  have hFII := heatConvInner_intervalIntegrable_gaussianDom E' F t T ht htT A₀ A₁ C_L
    hA₀ hA₁ hC_L hE'dom hE'zero hBdom hmeas
  exact heatConv_tail_tendsto E' F 0 0 t ht epsSeq epsSeq_pos epsSeq_tendsto hFII

/-- **★★ J4-123 (W2) — THE `Etrunc` LIMIT.**  The ε-truncated residual convolution `Etrunc` converges
    to the genuine residual convolution `E*F` (`E = heatOp g gi H`):
        `Etrunc g gi H F m t  →  heatConv (heatOp g gi H) F t 0 0`.
    Since `Etrunc g gi H F m t = heatConvFrozen (heatOp g gi H) F t (t − ε_m) 0 0` DEFINITIONALLY, this
    is `etrunc_tendsto_of_kernel` at `E' := heatOp g gi H`.  ⚠ CONDITIONAL on the D1 domination of the
    residual `heatOp g gi H` (`hEdom`/`hEzero`), the width-2 domination of `F` (`hBdom`), and the base
    `s`-measurability `hmeas`.  NOT `a₁ = R/6`. -/
theorem etrunc_tendsto (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (t T : ℝ) (ht : 0 < t) (htT : t ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ (z : Point n), heatOp g gi H (t - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 t))) :
    Tendsto (fun m => Etrunc g gi H F m t) atTop
      (𝓝 (heatConv (heatOp g gi H) F t 0 0)) :=
  etrunc_tendsto_of_kernel (heatOp g gi H) F t T ht htT A₀ A₁ C_L hA₀ hA₁ hC_L
    hEdom hEzero hBdom hmeas

/-! ### H — the `HasDerivAt` upgrade of the truncated diagonal derivative. -/

/-- **★ J4-123 (H) — THE TRUNCATED DIAGONAL `HasDerivAt`.**  The `HasDerivAt` form of
    `TruncatedDuhamel.truncDuhamel_deriv` (needed as an actual `HasDerivAt`, not just a `deriv`-equality,
    to feed `hasDerivAt_of_tendstoLocallyUniformlyOn`):
        `HasDerivAt (fun v => heatConvFrozen H F v (v − ε_m) 0 0) (DaTrunc H F m u + BoundaryTrunc H F m u) u`.
    Route (verbatim the `truncDuhamel_deriv` engine, without taking `.deriv`):
    `heatConvFrozen_hasFDerivAt_of_partials` (F2) → `heatConv_eps_hasDerivAt` (V2d); the fderiv-at-`(1,1)`
    value is `DaTrunc + BoundaryTrunc` by the `fst`/`snd` calculation.  Carries the three F2 partials;
    none is the conclusion. -/
theorem truncDuhamel_hasDerivAt (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ)
    (hpar : HasDerivAt (fun a => heatConvFrozen H F a (u - epsSeq m) 0 0) (DaTrunc H F m u) u)
    (htime : HasDerivAt (fun tt => heatConvFrozen H F u tt 0 0)
        (∫ z, H (u - (u - epsSeq m)) 0 z * F (u - epsSeq m) z 0) (u - epsSeq m))
    (hR : HasFDerivAt (fun p : ℝ × ℝ =>
        heatConvFrozen H F p.1 p.2 0 0 - heatConvFrozen H F p.1 (u - epsSeq m) 0 0
          - heatConvFrozen H F u p.2 0 0) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (u, u - epsSeq m)) :
    HasDerivAt (fun v => heatConvFrozen H F v (v - epsSeq m) 0 0)
      (DaTrunc H F m u + BoundaryTrunc H F m u) u := by
  have hjoint := heatConvFrozen_hasFDerivAt_of_partials H F 0 0 u (u - epsSeq m)
    (DaTrunc H F m u) hpar htime hR
  have heps := heatConv_eps_hasDerivAt H F 0 0 u (epsSeq m) _ hjoint
  have hval : (DaTrunc H F m u • ContinuousLinearMap.fst ℝ ℝ ℝ
      + (∫ z, H (u - (u - epsSeq m)) 0 z * F (u - epsSeq m) z 0)
          • ContinuousLinearMap.snd ℝ ℝ ℝ) ((1 : ℝ), (1 : ℝ))
      = DaTrunc H F m u + BoundaryTrunc H F m u := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one,
      BoundaryTrunc]
  rw [← hval]
  exact heps

/-! ### W3 — the `hDerivConv` wiring. -/

/-- **★★ J4-123 (W3) — THE `hDerivConv` WIRING.**  The truncated diagonal derivatives converge to the
    derivative of the TRUE diagonal convolution:
        `DaTrunc H F m t + BoundaryTrunc H F m t  →  deriv (fun u => heatConv H F u 0 0) t`.
    Route: `hasDerivAt_of_tendstoLocallyUniformlyOn` (limit-of-derivatives = derivative-of-the-limit)
    from (i) the eventual truncated `HasDerivAt` family `hderiv`, (ii) the locally-uniform derivative
    limit `hDerivLU` (family `DaTrunc + BoundaryTrunc → D`), (iii) the pointwise tail convergence `hfg`
    of the truncated maps to `heatConv H F · 0 0`; this pins `deriv (heatConv H F · 0 0) t = D t`, and
    `TendstoLocallyUniformlyOn.tendsto_at` at `t` gives the stated limit.  ⚠ CONDITIONAL on
    `hderiv`/`hDerivLU`/`hfg` — each a genuine analytic carry, none the conclusion.  NOT `a₁ = R/6`. -/
theorem derivConv_tendsto (H F : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hderiv : ∀ᶠ m in atTop, ∀ u ∈ U,
        HasDerivAt (fun v => heatConvFrozen H F v (v - epsSeq m) 0 0)
          (DaTrunc H F m u + BoundaryTrunc H F m u) u)
    (D : ℝ → ℝ)
    (hDerivLU : TendstoLocallyUniformlyOn
        (fun m u => DaTrunc H F m u + BoundaryTrunc H F m u) D atTop U)
    (hfg : ∀ u ∈ U, Tendsto (fun m => heatConvFrozen H F u (u - epsSeq m) 0 0) atTop
        (𝓝 (heatConv H F u 0 0))) :
    Tendsto (fun m => DaTrunc H F m t + BoundaryTrunc H F m t) atTop
      (𝓝 (deriv (fun u => heatConv H F u 0 0) t)) := by
  have hHDA : HasDerivAt (fun u => heatConv H F u 0 0) (D t) t :=
    hasDerivAt_of_tendstoLocallyUniformlyOn hUopen hDerivLU hderiv hfg htU
  rw [hHDA.deriv]
  exact hDerivLU.tendsto_at htU

/-! ### W4 — the capstone. -/

/-- **★★★ J4-123 (W4) — THE LIMIT-WIRING CAPSTONE.**  The Duhamel-principle output `hDuhamel`
        `heatOp g gi (fun u p q => heatConv H F u p q) t 0 0 = F t 0 0 + heatConv (heatOp g gi H) F t 0 0`,
    conditional ONLY on the locally-uniform, specific-value `Da`-limit `hDaLimLU`, the F2 regularity
    family (`hpar`/`htime`/`hR`), the tail carry `hFII`, and the `boundary_tendstoLocallyUniformlyOn`
    interface (dominations + near-diagonal parametrix + measurability/continuity).  The `hBoundaryLim`
    and `hDerivConv` carries of `hDuhamel_of_daLim` are DISCHARGED here (W1 + W3); the `Da`-limit is
    supplied pointwise-at-`t` from its loc-unif form.  ⚠ CONDITIONAL only on the carries listed; none is
    the conclusion.  NOT `a₁ = R/6`. -/
theorem hDuhamel_final (g gi : Point n → Fin n → Fin n → ℝ)
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
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn (fun x : ℝ × Point n => F x.1 x.2 0) (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => H τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    (hFII : ∀ u ∈ U, IntervalIntegrable (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 u)
    (hpar : ∀ᶠ m in atTop, ∀ u ∈ U,
        HasDerivAt (fun a => heatConvFrozen H F a (u - epsSeq m) 0 0) (DaTrunc H F m u) u)
    (htime : ∀ᶠ m in atTop, ∀ u ∈ U,
        HasDerivAt (fun tt => heatConvFrozen H F u tt 0 0)
          (∫ z, H (u - (u - epsSeq m)) 0 z * F (u - epsSeq m) z 0) (u - epsSeq m))
    (hR : ∀ᶠ m in atTop, ∀ u ∈ U,
        HasFDerivAt (fun p : ℝ × ℝ =>
            heatConvFrozen H F p.1 p.2 0 0 - heatConvFrozen H F p.1 (u - epsSeq m) 0 0
              - heatConvFrozen H F u p.2 0 0) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (u, u - epsSeq m))
    (hDaLimLU : TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
        (fun u => laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
              + heatConv (heatOp g gi H) F u 0 0) atTop U) :
    heatOp g gi (fun u p q => heatConv H F u p q) t 0 0
      = F t 0 0 + heatConv (heatOp g gi H) F t 0 0 := by
  -- boundary loc-unif, in the `BoundaryTrunc` shape.
  have hbdry0 := boundary_tendstoLocallyUniformlyOn H F T hT U hUopen hUpos hUT r₀ τ₀ hr₀ hτ₀
    u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont
    hAmeas hBmeas hu₀meas hu₁meas
  have hbdryLU : TendstoLocallyUniformlyOn (fun m u => BoundaryTrunc H F m u)
      (fun u => F u 0 0) atTop U := by
    have hfun : (fun m u => BoundaryTrunc H F m u)
        = (fun m u => ∫ z, H (epsSeq m) 0 z * F (u - epsSeq m) z 0) := by
      funext m u; simp only [BoundaryTrunc, sub_sub_cancel]
    rw [hfun]; exact hbdry0
  -- the three carries of `hDuhamel_of_daLim`.
  have hBoundaryLim : Tendsto (fun m => BoundaryTrunc H F m t) atTop (𝓝 (F t 0 0)) :=
    hbdryLU.tendsto_at htU
  have hDaLim := hDaLimLU.tendsto_at htU
  have hderiv : ∀ᶠ m in atTop, ∀ u ∈ U,
      HasDerivAt (fun v => heatConvFrozen H F v (v - epsSeq m) 0 0)
        (DaTrunc H F m u + BoundaryTrunc H F m u) u := by
    filter_upwards [hpar, htime, hR] with m hp ht hr
    intro u hu
    exact truncDuhamel_hasDerivAt H F m u (hp u hu) (ht u hu) (hr u hu)
  have hfg : ∀ u ∈ U, Tendsto (fun m => heatConvFrozen H F u (u - epsSeq m) 0 0) atTop
      (𝓝 (heatConv H F u 0 0)) := fun u hu =>
    heatConv_tail_tendsto H F 0 0 u (hUpos u hu) epsSeq epsSeq_pos epsSeq_tendsto (hFII u hu)
  have hDerivLU : TendstoLocallyUniformlyOn
      (fun m u => DaTrunc H F m u + BoundaryTrunc H F m u)
      (fun u => (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
              + heatConv (heatOp g gi H) F u 0 0) + F u 0 0) atTop U :=
    tendstoLocallyUniformlyOn_add hDaLimLU hbdryLU
  have hDerivConv := derivConv_tendsto H F t U hUopen htU hderiv _ hDerivLU hfg
  exact hDuhamel_of_daLim g gi H F t hBoundaryLim hDaLim hDerivConv

/-- **★★★★ J4-123 (W4, LEVI COROLLARY) — THE LIMIT-WIRING CAPSTONE for `F := leviSeries (heatOp g gi H)`.**
    `hDuhamel_final` instantiated at the actual Levi series, matching the `hDuhamel` carry of
    `ConcreteDominations.trueKernel_diagonal_a1_eq_R6_residual_restricted_C2` VERBATIM.  Reduces that
    carry to the loc-unif `Da`-limit `hDaLimLU` + the F2/domination/near-diagonal family.  STILL
    CONDITIONAL; NOT `a₁ = R/6`. -/
theorem hDuhamel_leviSeries_final (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (t T : ℝ) (hT : 0 < T)
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
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi H) s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn
        (fun x : ℝ × Point n => leviSeries (heatOp g gi H) x.1 x.2 0) (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => H τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable
        (fun z : Point n => leviSeries (heatOp g gi H) s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    (hFII : ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, H (u - s) 0 z * leviSeries (heatOp g gi H) s z 0) volume 0 u)
    (hpar : ∀ᶠ m in atTop, ∀ u ∈ U,
        HasDerivAt (fun a => heatConvFrozen H (leviSeries (heatOp g gi H)) a (u - epsSeq m) 0 0)
          (DaTrunc H (leviSeries (heatOp g gi H)) m u) u)
    (htime : ∀ᶠ m in atTop, ∀ u ∈ U,
        HasDerivAt (fun tt => heatConvFrozen H (leviSeries (heatOp g gi H)) u tt 0 0)
          (∫ z, H (u - (u - epsSeq m)) 0 z * leviSeries (heatOp g gi H) (u - epsSeq m) z 0)
          (u - epsSeq m))
    (hR : ∀ᶠ m in atTop, ∀ u ∈ U,
        HasFDerivAt (fun p : ℝ × ℝ =>
            heatConvFrozen H (leviSeries (heatOp g gi H)) p.1 p.2 0 0
              - heatConvFrozen H (leviSeries (heatOp g gi H)) p.1 (u - epsSeq m) 0 0
              - heatConvFrozen H (leviSeries (heatOp g gi H)) u p.2 0 0)
          (0 : (ℝ × ℝ) →L[ℝ] ℝ) (u, u - epsSeq m))
    (hDaLimLU : TendstoLocallyUniformlyOn
        (fun m u => DaTrunc H (leviSeries (heatOp g gi H)) m u)
        (fun u => laplaceBeltrami g gi
                (fun x => heatConv H (leviSeries (heatOp g gi H)) u x 0) 0
              + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) u 0 0) atTop U) :
    heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
      = leviSeries (heatOp g gi H) t 0 0
        + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0 :=
  hDuhamel_final g gi H (leviSeries (heatOp g gi H)) t T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀
    u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont
    hAmeas hBmeas hu₀meas hu₁meas hFII hpar htime hR hDaLimLU

end QIQTH.HeatResidualBound
