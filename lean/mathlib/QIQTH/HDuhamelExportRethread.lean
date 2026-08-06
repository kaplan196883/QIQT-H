/-
  HDuhamelExportRethread — J4-311: re-thread the provider-∃ `hDuhamel` export through the NEW
  W1-free fixed-gate Core (`HDerivConvComposition`, J4-310), so the wide `a₁` capstone's `hDuhamel`
  arrow becomes INTERNAL (W1-free) rather than a carried antecedent.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / export-rethreading brick.  No `sorry` (header prose excepted), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## X0 — THE GATE-IDENTITY VERDICT (load-bearing; answered before any code).

  The wide capstone `ProviderSideExports.wide_a1_R6_interface_discharged_v2` (J4-265) returns an
  ∃-implication `∃ a b C' S, … ∧ (hDuhamel → hDConv → hCConv → ⟨a₁ 2-jet⟩)`, where the gate `S` is
  CHOSEN INSIDE the residual provider `hEboundW_wide_from_geometry_open_inter` by
  `GateOpennessExport.gatedWitnessN1_package_open` — the ONE concrete van-Vleck gate
  `S = uniformFlowExp '' ball 0 cw` (the `vanVleckGatedWitness`/`radialCutoff` machinery).  The
  capstone's `hDuhamel` antecedent is EXACTLY the identity
      `heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b) (leviSeries …) u p q) t 0 0`
        `= leviSeries … t 0 0 + heatConv (heatOp g gi (vanVleckGatedWitness …)) (leviSeries …) t 0 0`
  at THAT chosen `S`, which is VERBATIM `TruncatedDuhamelData.TruncatedDuhamelCore g gi
  (vanVleckGatedWitness g gi hChr hK S a b) t |>.hIdentity`.

  **VERDICT — IDENTICAL GATE, DIRECT INSTANTIATION.**  Our entire boundary chain (J4-266→310:
  `hDaLimLU_concrete`, `hBoundaryLim_DONE`, `hbdryLU_CONCRETE`, `hDerivConv_conditional`) is
  parameterized by the SAME `(S, a, b)` and speaks of the SAME `vanVleckGatedWitness g gi hChr hK S a b`.
  The J4-265 export PATTERN (strengthen the residual-provider `∃` with a per-`S` fact PROVEN at the
  concrete gate the provider chose, then `∃`-intro) applies: the provider chooses `S`, WE prove the Core
  identity at that `S`, WE `∃`-intro it.  So the instantiation is direct — no gate mismatch, no `hAnear`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.

    • (X1a) `hDerivConv_AT_GATE` — the NEW W1-free `hDerivConv` composition at the concrete gate:
      `HDerivConvComposition.hDerivConv_conditional` fed its boundary loc-unif `hbdryLU` by
      `HDerivConvComposition.hbdryLU_CONCRETE` (the W1-free boundary slot) in place of the W1 provider.
      Hypotheses = the F2 regularity pile + `hFII` tail-integrability pile + the loc-unif `Da`-limit
      `hDaLimLU` + the frozen/moving satisfiable lists.  NO `hAnear` anywhere.

    • (X1) `truncatedDuhamelCore_AT_GATE` — the Core at the concrete gate `vanVleckGatedWitness …`:
      `HDerivConvComposition.truncatedDuhamelCore_conditional` fed (a) `hBoundaryLim` (W1-free, provider
      `EnvelopeWiringLocUnif.hBoundaryLim_DONE`), (b) `hDaLimLU` (`DaLimLUWallRecon.DaLimLUGoal`,
      provider `DaLimLUConcreteDischarge.hDaLimLU_concrete`), (c) `hDerivConv` (X1a).  Conclusion:
      `TruncatedDuhamelData.TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t`.

    • (X1-FULL) `truncatedDuhamelCore_AT_GATE_FULL` — the UNION form: `truncatedDuhamelCore_AT_GATE`
      with `hDaLimLU` and `hDerivConv` DERIVED INTERNALLY from their concrete data censuses
      (`hDaLimLU_concrete` + X1a), so the surviving hypotheses are exactly the honest satisfiable union
      (F2 pile + `hFII` + the `hDaLimLU` data census + the frozen/moving lists), plus the single W1-free
      `hBoundaryLim` slot.  NO `hAnear`.

    • (X2) `hDuhamelSlot_AT_GATE` — the bridge to the EXACT capstone `hDuhamel` slot shape, via
      `TruncatedDuhamelData.hDuhamel_of_truncatedData` applied to the Core.  This IS the `hDuhamel`
      antecedent proposition of `wide_a1_R6_interface_discharged_v2`, now a THEOREM (W1-free) rather than
      a carried arrow.

  ## THE W1-FREE POINT.  In the OLD lineage (`DerivConvDischarge.core_of_v2prime_data_FULL`,
  `DaLimLUConcreteDischarge` §"WHY THE PROVIDER-∃ EXPORT … IS NOT ATTEMPTED") the ONLY W1-poisoned link
  from the Core to geometry was the OLD boundary provider
  (`BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`, needing the `hAnear` chart-image-vs-`z`
  factorization).  J4-309/310 replaced it: `hbdryLU_CONCRETE` (moving side = `movingCorr_tUniform`,
  frozen side = the chart-image approximate identity) + `hBoundaryLim_DONE` are BOTH W1-free.  The
  `Da`-limit (`hDaLimLU_concrete`) never referenced `hAnear`.  So the Core at the concrete gate — and
  hence the `hDuhamel` slot — is now internal to satisfiable geometry DATA, free of the W1 wall.

  ## REMAINING MAP TO `a1_R6_of_geometry`.  With `hDuhamel` internalizable (this file), the surviving
  capstone antecedents of `wide_a1_R6_interface_discharged_v2` drop to `hDConv → hCConv → ⟨a₁ 2-jet⟩`
  (`HDConvThreading.hDConv_from_banked` for `hDConv`, `CConvFacade` for `hCConv`).  A `v3` capstone that
  internalizes `hDuhamel` would require re-running the residual provider to EXPORT the Core identity for
  its self-chosen `S` (carrying the Core data census `∀`-gate) — an X3 the mission scopes as a heavy
  intermediate; NOT materialized here (the ~130-binder capstone is never restated, only its slot shape
  is reproduced by X2).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import QIQTH.HDerivConvComposition
import QIQTH.DaLimLUConcreteDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.ETailRateBound QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open scoped Interval Topology BigOperators

namespace QIQTH.HDuhamelExportRethread

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (X1a) — `hDerivConv_AT_GATE`: the W1-free `hDerivConv` composition.
    ############################################################################### -/

/-- **★★★ (X1a) `hDerivConv_AT_GATE`.**  The `hDerivConv` pointwise limit
        `Tendsto (fun m => DaTrunc H F m t + BoundaryTrunc H F m t) atTop
           (𝓝 (deriv (fun u => heatConv H F u 0 0) t))`,
    built from `HDerivConvComposition.hDerivConv_conditional` with its boundary loc-unif `hbdryLU`
    supplied INTERNALLY by `HDerivConvComposition.hbdryLU_CONCRETE` (the W1-free boundary slot) — the OLD
    W1 boundary provider is gone.  Hypotheses = the F2 regularity pile + the `hFII` tail-integrability
    pile + the loc-unif `Da`-limit `hDaLimLU` + the frozen/moving satisfiable lists that
    `hbdryLU_CONCRETE` consumes.  NONE references `hAnear` (W1 is absent); NONE is the conclusion.
    Abstract in `H F` (reused at the concrete gate by (X1)).  ⚠ NOT `a₁ = R/6`. -/
theorem hDerivConv_AT_GATE (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (t T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    -- F2 tail-integrability (`hFII`) pile:
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, H τ p q = 0)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, H (u - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 u)))
    -- F2-discharge carries:
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, H (u - s) 0 z * F s z 0) (Set.Ioo 0 u))
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
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen H F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen H F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen H F u (u - epsSeq m + k) 0 0
          + heatConvFrozen H F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- the hard loc-unif `Da`-limit (shared with the Core):
    (hDaLimLU : TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
        (fun u => laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
              + heatConv (heatOp g gi H) F u 0 0) atTop U)
    -- the W1-free boundary loc-unif's satisfiable frozen/moving lists:
    (ρ lam CW Cf τ₀ ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (fun z => H τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
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
    Tendsto (fun m => DaTrunc H F m t + BoundaryTrunc H F m t) atTop
      (𝓝 (deriv (fun u => heatConv H F u 0 0) t)) := by
  have hbdryLU : QIQTH.LocUnifDerivConv.hbdryLUTarget H F U :=
    QIQTH.HDerivConvComposition.hbdryLU_CONCRETE H F U ρ lam CW Cf τ₀ ta tb
      hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd hWDom hmass hmassone hmod hsup hUsub
  exact QIQTH.HDerivConvComposition.hDerivConv_conditional g gi H F t T hT U hUopen htU hUpos hUT
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hBdom hMeasFII hUfloor hInnerCont
    nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff L hLnn hCross hDaLimLU hbdryLU

/-! ###############################################################################
    ### (X1) — `truncatedDuhamelCore_AT_GATE`: the Core at the concrete gate.
    ############################################################################### -/

/-- **★★★ (X1) `truncatedDuhamelCore_AT_GATE`.**  The `TruncatedDuhamelData.TruncatedDuhamelCore` bundle
    at the concrete `N = 1` van-Vleck gated witness `H_G := vanVleckGatedWitness g gi hChr hK S a b` with
    source `F := leviSeries (heatOp g gi H_G)`, assembled from the three W1-free truncation-limit facts:
      • `hBoundaryLim` — the pointwise boundary limit at `t` (W1-free, provider
        `EnvelopeWiringLocUnif.hBoundaryLim_DONE`);
      • `hDaLimLU`     — the loc-unif `Da`-limit (`DaLimLUWallRecon.DaLimLUGoal`, provider
        `DaLimLUConcreteDischarge.hDaLimLU_concrete`);
      • `hDerivConv`   — the derivative-of-convolution limit (W1-free, provider (X1a)
        `hDerivConv_AT_GATE`).
    Route: `HDerivConvComposition.truncatedDuhamelCore_conditional`.  Pure composition; NONE of the three
    is the conclusion; NONE references `hAnear` (W1).  ⚠ NOT `a₁ = R/6`. -/
theorem truncatedDuhamelCore_AT_GATE (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (U : Set ℝ) (htU : t ∈ U)
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m t) atTop
        (𝓝 (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0)))
    (hDaLimLU : DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U)
    (hDerivConv : Tendsto
        (fun m => DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m t
          + BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m t) atTop
        (𝓝 (deriv (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t))) :
    TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t :=
  QIQTH.HDerivConvComposition.truncatedDuhamelCore_conditional g gi
    (vanVleckGatedWitness g gi hChr hK S a b) t U htU hBoundaryLim hDaLimLU hDerivConv

/-! ###############################################################################
    ### (X2) — `hDuhamelSlot_AT_GATE`: the exact capstone `hDuhamel` slot, W1-free.
    ############################################################################### -/

/-- **★★★ (X2) `hDuhamelSlot_AT_GATE`.**  The EXACT `hDuhamel` antecedent proposition of
    `ProviderSideExports.wide_a1_R6_interface_discharged_v2` at the concrete gate, produced from the
    Core (X1) via `TruncatedDuhamelData.hDuhamel_of_truncatedData`.  This is the capstone's `hDuhamel`
    arrow, now a THEOREM (W1-free from satisfiable geometry DATA), not a carried antecedent.
    ⚠ NOT `a₁ = R/6`. -/
theorem hDuhamelSlot_AT_GATE (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (t : ℝ)
    (core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t) :
    heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
      = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
        + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0 :=
  hDuhamel_of_truncatedData g gi (vanVleckGatedWitness g gi hChr hK S a b) t core

/-! ###############################################################################
    ### (X1-FULL) — `truncatedDuhamelCore_AT_GATE_FULL`: the union form.
    ############################################################################### -/

/-- **★★★ (X1-FULL) `truncatedDuhamelCore_AT_GATE_FULL`.**  The Core at the concrete gate with
    `hDaLimLU` and `hDerivConv` DERIVED INTERNALLY from their concrete data censuses
    (`DaLimLUConcreteDischarge.hDaLimLU_concrete` + (X1a) `hDerivConv_AT_GATE`).  The surviving
    hypotheses are exactly the honest satisfiable UNION — the F2 regularity pile, the `hFII`
    tail-integrability pile, the `hDaLimLU` data census (RNC gauge, `MemLapFull`, adjacency + strip
    integrabilities, `√ε` sliver amplitudes, residual/source Gaussian dominations, `MemECombine`, the W2
    differentiation-under-∫ family), and the standing frozen/moving lists — PLUS the single W1-free
    `hBoundaryLim` slot (provider `EnvelopeWiringLocUnif.hBoundaryLim_DONE`).  The source is fixed to
    `F := leviSeries (heatOp g gi H_G)` via `hFeq` (a genuine defining equation, satisfiable by `rfl`).
    NO `hAnear` anywhere; NONE of the hypotheses is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem truncatedDuhamelCore_AT_GATE_FULL (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    -- ★ the single W1-free boundary slot (provider `hBoundaryLim_DONE`):
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b) F m t) atTop
        (𝓝 (F t 0 0)))
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
    -- ── the F2 pile + `hFII` pile (for `hDerivConv_AT_GATE`) ─────────────────────────────────────
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
    TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t := by
  subst hFeq
  -- derive the loc-unif `Da`-limit from its concrete census.
  have hDaLimLU := QIQTH.DaLimLUConcreteDischarge.hDaLimLU_concrete g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) T U hUopen hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT hEdom hFdom hFzero hIlo hIhi hEcomb
  -- derive the W1-free `hDerivConv` from the F2 pile + frozen/moving lists (X1a).
  have hDerivConv := hDerivConv_AT_GATE g gi (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t T hT U hUopen htU
    (fun u hu => lt_of_lt_of_le haT (hUlb u hu)) hUT
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hFdom hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross hDaLimLU
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
  exact truncatedDuhamelCore_AT_GATE g gi hChr hK S a b t U htU hBoundaryLim hDaLimLU hDerivConv

end QIQTH.HDuhamelExportRethread

section AxiomChecks
open QIQTH.HDuhamelExportRethread
#print axioms hDerivConv_AT_GATE
#print axioms truncatedDuhamelCore_AT_GATE
#print axioms hDuhamelSlot_AT_GATE
#print axioms truncatedDuhamelCore_AT_GATE_FULL
end AxiomChecks
