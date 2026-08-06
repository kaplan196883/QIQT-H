/-
  HDConvGateThreading — J4-312: thread the surviving capstone `hDConv` arrow at the concrete
  van-Vleck gate, W1-FREE, following the J4-311 AT_GATE pattern.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / capstone-arrow-threading brick.  No `sorry` (header prose excepted), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## X0 — WHY `HDConvThreading.hDConv_from_banked` CANNOT BE USED AT THE GATE (load-bearing).

  The wide capstone `ProviderSideExports.wide_a1_R6_interface_discharged_v2` (J4-265) returns an
  ∃-implication whose surviving inner arrows are `hDuhamel → hDConv → hCConv → ⟨a₁ 2-jet⟩`, at the ONE
  concrete van-Vleck gate `S` that `GateOpennessExport.gatedWitnessN1_package_open` chooses.  The
  capstone's `hDConv` antecedent is EXACTLY
      `DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t`.

  The banked provider `HDConvThreading.hDConv_from_banked` (J4-209) produces exactly that
  `DifferentiableAt`, BUT its route runs through `BoundaryAssembly.hDelta_gatedWitnessN1_final` →
  `boundary_tendstoLocallyUniformlyOn`, whose `hAnear` carry (the W1 structural wall: the concrete
  witness is Gaussian at the CHART IMAGE `W z 0`, not at `z`) is NOT known satisfiable at a general
  provider-chosen gate — `DaLimLUConcreteDischarge` §"WHY THE PROVIDER-∃ EXPORT … IS NOT ATTEMPTED".
  Carrying `hAnear` would risk an unsatisfiable hypothesis, which the firewall forbids.  So
  `hDConv_from_banked` does NOT instantiate honestly at the concrete gate.

  **THE MISSING NAMED LEMMA.**  What was missing is a **W1-free** `hDConv` producer — the `DifferentiableAt`
  analog of J4-310 `HDerivConvComposition.hDerivConv_conditional` (which is the W1-free `hDerivConv`
  producer, giving `Tendsto … (𝓝 (deriv …))`).  Both rest on the SAME
  `hasDerivAt_of_tendstoLocallyUniformlyOn` core: `HeatConvDeriv.hDConv_of_deltaFamily` is precisely
  `(hasDerivAt_of_tendstoLocallyUniformlyOn hUopen hDelta hf hfg htU).differentiableAt`, consuming the
  SAME `hf` (truncated `HasDerivAt` family, `truncDuhamel_hasDerivAt`), `hfg` (tail convergence,
  `heatConv_tail_tendsto`), and `hDelta = tendstoLocallyUniformlyOn_add hDaLimLU hbdryLU` that
  `hDerivConv_conditional` builds internally — but with the OLD W1 boundary provider replaced by the
  W1-free `HDerivConvComposition.hbdryLU_CONCRETE`.  NO `hAnear` anywhere.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.

    • (Y1a) `hDConv_W1free` — the missing named lemma: the W1-free abstract `hDConv` producer.  From
      the F2 regularity pile + the `hFII` tail-integrability pile + the loc-unif `Da`-limit `hDaLimLU`
      + the W1-free boundary loc-unif `hbdryLU : LocUnifDerivConv.hbdryLUTarget H F U`, it produces
      `DifferentiableAt ℝ (fun u => heatConv H F u 0 0) t`.  Verbatim the `hDerivConv_conditional`
      construction (F2 dischargers → `hderiv`/`hfg`, `tendstoLocallyUniformlyOn_add` → `hDerivLU`)
      EXCEPT the final combinator is `hDConv_of_deltaFamily` (⟹ `DifferentiableAt`) instead of
      `derivConv_tendsto` (⟹ `Tendsto … deriv`).  Abstract in `H F`; NO `hAnear`.

    • (Y1) `hDConv_AT_GATE` — `hDConv_W1free` at the concrete `N = 1` van-Vleck gated witness with
      source `F := leviSeries (heatOp g gi H_G)` (fixed by `hFeq`, satisfiable by `rfl`), with
      `hDaLimLU` and `hbdryLU` DERIVED INTERNALLY from their concrete censuses
      (`DaLimLUConcreteDischarge.hDaLimLU_concrete` + `HDerivConvComposition.hbdryLU_CONCRETE`).  The
      surviving hypotheses are the honest satisfiable UNION — the F2 pile, the `hFII` pile, the
      `hDaLimLU` data census (RNC gauge, W2 differentiation-under-∫∫, `MemLapFull`, adjacency + strip
      integrabilities, `√ε` sliver amplitudes, residual/source Gaussian dominations, `MemECombine`),
      and the standing frozen/moving lists.  NO `hAnear`; NO `hBoundaryLim` (the pointwise boundary
      limit is needed for the Core's `hDuhamel` identity, NOT for `DifferentiableAt`).  Conclusion is
      VERBATIM the capstone `hDConv` slot at the gate.

    • (Y2) `hDConvSlot_AT_GATE` — the EXACT `hDConv` antecedent proposition of
      `wide_a1_R6_interface_discharged_v2` reproduced verbatim and proven from (Y1).  Unlike J4-311's
      `hDuhamelSlot_AT_GATE` (which extracted the `hDuhamel` identity from the `TruncatedDuhamelCore`
      bundle via `hDuhamel_of_truncatedData`), the `hDConv` slot IS the `DifferentiableAt` directly —
      no bundle extraction — so (Y2)'s conclusion coincides with (Y1)'s; (Y2) exists to certify the
      verbatim shape match to the capstone antecedent.

  ## REMAINING MAP TO `a1_R6_of_geometry`.  With `hDuhamel` (J4-311) and now `hDConv` (this file) both
  W1-free-internalizable at the concrete gate, the surviving capstone antecedent of
  `wide_a1_R6_interface_discharged_v2` drops to `hCConv → ⟨a₁ 2-jet⟩` (`CConvFacade` five-bundle
  facade).  A `v3`/`v4` capstone that internalizes `hDuhamel`+`hDConv` would still require re-running the
  residual provider to EXPORT the Core / `DifferentiableAt` for its self-chosen `S` (carrying the data
  census `∀`-gate) — a heavy intermediate, NOT materialized here (the ~130-binder capstone is never
  restated).  Also open after this brick: the `hCConv` facade discharge, the S1 `∀`-gate measurability,
  the data-census piles' satisfiability, base geometry, and `1 ≤ n`.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import QIQTH.HDerivConvComposition
import QIQTH.DaLimLUConcreteDischarge
import QIQTH.HeatConvDeriv

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.ETailRateBound QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open scoped Interval Topology BigOperators

namespace QIQTH.HDConvGateThreading

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (Y1a) — `hDConv_W1free`: the missing W1-free abstract `hDConv` producer.
    ############################################################################### -/

/-- **★★★ (Y1a) `hDConv_W1free`.**  THE MISSING NAMED LEMMA — the W1-free abstract `hDConv`
    (`DifferentiableAt`) producer, the `DifferentiableAt` analog of
    `HDerivConvComposition.hDerivConv_conditional`.  From the F2 regularity pile (`hpar`/`htime`/`hR`
    via the `F2FamilyDischarge` dischargers) + the tail-integrability `hFII` pile + the loc-unif
    `Da`-limit `hDaLimLU` + the W1-free boundary loc-unif `hbdryLU : LocUnifDerivConv.hbdryLUTarget H F U`,
    it yields `DifferentiableAt ℝ (fun u => heatConv H F u 0 0) t`.  Route is verbatim
    `hDerivConv_conditional` up to `hDerivLU := tendstoLocallyUniformlyOn_add hDaLimLU hbdryLU`, then
    the final combinator is `HeatConvDeriv.hDConv_of_deltaFamily`
    (`= (hasDerivAt_of_tendstoLocallyUniformlyOn …).differentiableAt`) — producing DIFFERENTIABILITY
    (existence), not the derivative's value.  The entire boundary W1 pile
    (`hAnear`/`u₀`/`u₁`/`hBcont`/`hAmeas`/`hu₀…`) is DROPPED; `hbdryLU` is a hypothesis (satisfiable
    W1-free via `hbdryLU_CONCRETE`).  NONE of the carries is the conclusion; NONE references `hAnear`.
    Abstract in `H F`.  ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_W1free (g gi : Point n → Fin n → Fin n → ℝ)
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
    -- ★ THE W1-FREE boundary loc-unif (satisfiable via `hbdryLU_CONCRETE`), replacing the W1 provider:
    (hbdryLU : QIQTH.LocUnifDerivConv.hbdryLUTarget H F U) :
    DifferentiableAt ℝ (fun u => heatConv H F u 0 0) t := by
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
  -- close with `hDConv_of_deltaFamily` (`hasDerivAt_of_tendstoLocallyUniformlyOn`.differentiableAt).
  exact hDConv_of_deltaFamily H F 0 0 t U hUopen htU
    (fun m v => heatConvFrozen H F v (v - epsSeq m) 0 0)
    (fun m u => DaTrunc H F m u + BoundaryTrunc H F m u)
    _ hderiv hfg hDerivLU

/-! ###############################################################################
    ### (Y1) — `hDConv_AT_GATE`: the W1-free `DifferentiableAt` slot at the concrete gate.
    ############################################################################### -/

/-- **★★★ (Y1) `hDConv_AT_GATE`.**  The capstone's `hDConv` `DifferentiableAt` slot at the concrete
    `N = 1` van-Vleck gated witness `H_G := vanVleckGatedWitness g gi hChr hK S a b` with source
    `F := leviSeries (heatOp g gi H_G)` (fixed by `hFeq`, satisfiable by `rfl`), built W1-FREE.
    `hDaLimLU` and the W1-free boundary loc-unif `hbdryLU` are DERIVED INTERNALLY from their concrete
    censuses (`DaLimLUConcreteDischarge.hDaLimLU_concrete` + `HDerivConvComposition.hbdryLU_CONCRETE`),
    then fed to (Y1a) `hDConv_W1free`.  Surviving hypotheses = the honest satisfiable UNION (F2 pile +
    `hFII` pile + `hDaLimLU` data census + frozen/moving lists).  NO `hAnear`; NO `hBoundaryLim`
    (unneeded for `DifferentiableAt`).  Conclusion is VERBATIM the capstone `hDConv` antecedent of
    `ProviderSideExports.wide_a1_R6_interface_discharged_v2`.  ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_AT_GATE (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    -- ── the `hDaLimLU` data census (from `hDaLimLU_concrete`) ────────────────────────────────────
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b) F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_lo : MemAdjLo F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_hi : MemAdjHi F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F)
    -- ── the F2 pile + `hFII` pile (for `hDConv_W1free`) ──────────────────────────────────────────
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0) c)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- ── the frozen/moving satisfiable lists (for `hbdryLU_CONCRETE`) ─────────────────────────────
    (ρ lam CW Cf τ₀ : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t := by
  subst hFeq
  -- derive the loc-unif `Da`-limit from its concrete census.
  have hDaLimLU := QIQTH.DaLimLUConcreteDischarge.hDaLimLU_concrete g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) T U hUopen hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT hEdom hFdom hFzero hIlo hIhi hEcomb
  -- derive the W1-free boundary loc-unif from the frozen/moving lists.
  have hbdryLU := QIQTH.HDerivConvComposition.hbdryLU_CONCRETE
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
  -- compose into the W1-free abstract `hDConv` producer (Y1a).
  exact hDConv_W1free g gi (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t T hT U hUopen htU
    (fun u hu => lt_of_lt_of_le haT (hUlb u hu)) hUT
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hFdom hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross hDaLimLU hbdryLU

/-! ###############################################################################
    ### (Y2) — `hDConvSlot_AT_GATE`: the exact capstone `hDConv` slot, verbatim.
    ############################################################################### -/

/-- **★★★ (Y2) `hDConvSlot_AT_GATE`.**  The EXACT `hDConv` antecedent proposition of
    `ProviderSideExports.wide_a1_R6_interface_discharged_v2` at the concrete gate, reproduced verbatim
    and proven from (Y1) `hDConv_AT_GATE`.  Unlike J4-311's `hDuhamelSlot_AT_GATE` (which extracted the
    `hDuhamel` identity from the `TruncatedDuhamelCore` bundle), the `hDConv` slot IS the
    `DifferentiableAt` directly, so its conclusion coincides with (Y1)'s; this theorem certifies the
    verbatim shape match to the capstone antecedent (same `t`-binder, same witness, same source).
    ⚠ NOT `a₁ = R/6`. -/
theorem hDConvSlot_AT_GATE (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b) F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_lo : MemAdjLo F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_hi : MemAdjHi F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0) c)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    (ρ lam CW Cf τ₀ : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t :=
  hDConv_AT_GATE g gi hChr hK S a b F hFeq t T hT U hUopen htU hUT hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub

end QIQTH.HDConvGateThreading

section AxiomChecks
open QIQTH.HDConvGateThreading
#print axioms hDConv_W1free
#print axioms hDConv_AT_GATE
#print axioms hDConvSlot_AT_GATE
end AxiomChecks
