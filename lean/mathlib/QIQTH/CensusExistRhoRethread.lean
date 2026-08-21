/-
  CensusExistRhoRethread — J4-954: RESHAPE the any-`S` census far-rate capstone so the trace-integral
  SPLIT RADIUS `ρ` is chosen AFTER (per) the geometry witness `D`, resolving the "ρ-prescription
  mismatch" (O1) that blocked discharging the C1 on-ball trace-rate carry `hballrate` from the
  common-witness / change-of-variables chain; then THREAD the reshaped capstone through to the ACTUAL
  downstream `hCross` consumer `hcross_of_censusIntegral_bound` (J4-929) to certify that the ultimate
  consumer ACCEPTS a geometry-determined (existentially-chosen) `ρ`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  binder-reorder / consumer-acceptance brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis (satisfiability EXHIBITED below), none equal to the conclusion, no existing
  banked file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE O1 MISMATCH (what this resolves).  The banked capstone
  `CensusAnySEnvelopeRethread.censusBound_of_geometry_gate_supp_F_ballRate_anyS` (J4-951) fixes the
  trace-integral split radius `ρ` at TOP LEVEL — **before** the `∀ D : FixedFlowGateData` binder — and
  then consumes the on-ball trace rate `hballrate` on `Metric.ball 0 ρ` at that PRESCRIBED `ρ`.  But the
  common-witness / CoV chain that would DISCHARGE `hballrate` can only bound the on-ball trace on a
  GEOMETRY-DETERMINED radius `δ = min(gate radius, chart-injectivity radius D.ρ, transport radius σ')`,
  chosen AFTER `D`.  With `ρ` prescribed before `D`, `hballrate(ρ)` at a fixed `ρ` is unobtainable from
  the CoV chain — the O1 wall.

  ## THE FIX (this file, verified sound by gpt-5.6-sol high adversarial audit).  The DOWNSTREAM consumer
  `hcross_of_censusIntegral_bound` (J4-929) is entirely **ρ-agnostic**: its `hCensusBound` hypothesis is
      `∀ s ∈ Ioo(u−ε)u, ∀ a ∈ Icc u(u+h), |∫ z, deriv(…)(a−s)·F s z 0| ≤ C_far·(u−s)^{−1/2}`
  — the integral is over ALL of `ℝⁿ` (NO `Metric.ball`), and `C_far` is a FREE scalar parameter.  So `ρ`
  is purely an INTERNAL splitting radius; it never appears in the consumer's binder.  Hence we may simply
  REORDER the capstone binders — move `ρ, MF, Cpair, hF, hballrate` INSIDE the `∀ D` binder — so the
  caller picks `ρ := δ(D)` per-`D`.  The reorder is a genuine STRENGTHENING (one `rAmp` uniform over all
  later `ρ, MF, Cpair`), but it is proved by the SAME body: `rAmp` comes from `census_amplitude_supBounds`
  which is `ρ`/`MF`/`Cpair`-INDEPENDENT, and the internal assembler
  `censusBound_of_amplitudeCarries_Fbound_ballRate_anyS` constrains `ρ` ONLY by `0 < ρ` (no `D.r ≤ ρ`, no
  `ρ ≤ ρmax`, no `τ₀ ≤ c·ρ²` coupling — the fixed-Gaussian envelope constant `Cenv` depends on `ρ` but is
  existential in the conclusion, and the width `lam` depends only on `w = 4·D.lam` and `τ₀`).

  ## WHAT LANDS.
    • `censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho` — ★★★ the RESHAPED capstone: `ρ, MF,
        Cpair, hF, hballrate` bound INSIDE `∀ D`, so the CoV chain can supply `hballrate` at the
        geometry-determined `ρ := δ(D)`.  Same conclusion (∫ over all `ℝⁿ`, `C_far` existential via `Cenv`).
    • `hcross_of_geometry_gate_supp_existRho` — ★★★ the CONSUMER-ACCEPTANCE capstone: the FULL live
        `hCross` mixed-second-difference binder (h,k > 0) follows from the reshaped-capstone carries
        (geometry + per-`D` `ρ`/`hballrate`/`hF`/`hSupp`/`hΦint`) PLUS the J4-929 differentiation carries
        (`hFmeasG`, four interval-integrabilities, `hEnv`, `H_near`, `H_zero`), via
        `hcross_of_censusIntegral_bound` at `C_far := Cpair + Cenv·√2ⁿ·√ε`.  This CERTIFIES that the
        ultimate `hCross` consumer accepts an EXISTENTIALLY-CHOSEN geometry-determined `ρ` — NO
        re-derivation of the `hcross` composition was needed.
    • non-vacuity: `existRho_innerBundle_satisfiable` (the moved-inside carry bundle jointly satisfiable,
        `K = {0}`, `S = univ`, `F ≡ 0`, `ρ = 1/4`) + `census_existRho_smallRadius_gate_exists` (the `∀ D`
        binder non-vacuous, re-exporting the banked `census_smallRadius_gate_exists`).

  ## HONEST STATUS (gpt-5.6-sol high audited).  The O1 quantifier mismatch is RESOLVED at the assembly
  boundary AND the downstream `hCross` consumer is CERTIFIED to accept the geometry-determined `ρ`.  This
  does NOT close `hballrate` (C1): the CoV chain must still (per Sol) supply, after fixing `D`, a positive
  `δ(D)`, the width-2 Levi `hF` at that `δ`, and the trace rate on `ball 0 δ(D)` — uniformly over `s,a`.
  This brick removes the STRUCTURAL O1 obstacle to that discharge; it proves none of `{hballrate,
  hDuhamel, hDConv, hCConv}`.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusAnySEnvelopeRethread
import QIQTH.HCrossDerivEngineWired

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.InverseChartNormalJets QIQTH.CensusAmpConcreteRegularity
open QIQTH.RadialDistance QIQTH.CensusTauDerivGateSplit
open QIQTH.CensusAmplitudeSupDischarge QIQTH.CensusAnySEnvelopeRethread
open QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CensusExistRhoRethread

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the RESHAPED capstone: `ρ, MF, Cpair, hF, hballrate` bound INSIDE `∀ D` (O1 fix).
    ############################################################################### -/

/-- **★★★ `censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho`.**  The reshaped far-rate capstone.
    Identical to the banked `censusBound_of_geometry_gate_supp_F_ballRate_anyS` (J4-951) EXCEPT the split
    radius `ρ` (with `MF`, `Cpair`, the off-ball F-factor bound `hF`, and the on-ball trace rate
    `hballrate`) is bound INSIDE the `∀ D` binder — so the common-witness / CoV chain may choose
    `ρ := δ(D)` (a geometry-determined radius) AFTER the gate record `D` is fixed.  The proof body is the
    SAME as J4-951: `rAmp` comes from the `ρ`/`MF`/`Cpair`-independent `census_amplitude_supBounds`, and
    the internal assembler constrains `ρ` only by `0 < ρ`.  Conclusion (∫ over ALL `ℝⁿ`, `C_far` via the
    existential `Cenv`) is unchanged and `ρ`-FREE.  NOT `a₁ = R/6`. -/
theorem censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h τ₀ : ℝ)
    (hε : 0 < ε) (hτ₀ : 0 < τ₀) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀) :
    ∃ rAmp : ℝ, 0 < rAmp ∧
      ∀ D : FixedFlowGateData g gi hC hK, D.r ≤ rAmp →
        ∀ (ρ MF Cpair : ℝ), 0 < ρ → 0 ≤ MF → 0 ≤ Cpair →
        (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          Integrable
            (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
              * F s z 0) volume) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          |∫ z in Metric.ball (0 : Point n) ρ,
            deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
              ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) →
        ∃ (lam' Cenv : ℝ), 0 < lam' ∧ 0 ≤ Cenv ∧
          ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
            |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
              ≤ (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * (u - s) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨rAmp, hrAmp, M, M', hM, hM', hampBnd, hcfBnd⟩ :=
    census_amplitude_supBounds g gi hC hK cutA cutB τ₀ hτ₀ h0Kmem hg hg0 hu
  refine ⟨rAmp, hrAmp, ?_⟩
  intro D hDr ρ MF Cpair hρ hMF hCpair hSupp hF hΦint hballrate
  -- `hAmp0` from the amplitude package (radius monotonicity `‖z‖ < D.r ≤ rAmp`).
  have hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
      |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M := by
    intro τ hτ hτ0 z _ hzr
    exact hampBnd τ hτ hτ0 z (lt_of_lt_of_le hzr hDr)
  -- `hCfield` (on the banked `censusAmpTauDeriv` slope) from the package.
  have hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M' := by
    intro z _ hzr
    exact hcfBnd z (lt_of_lt_of_le hzr hDr)
  exact censusBound_of_amplitudeCarries_Fbound_ballRate_anyS hn g gi hC hK S cutA cutB D τ₀ M M'
    hτ₀ hM hM' hAmp0 hCfield hSupp F u ε h ρ MF Cpair
    hε hρ hMF hCpair hh hcap hF hΦint hballrate

/-! ###############################################################################
    ### §B — CONSUMER ACCEPTANCE: the reshaped capstone threads through to the live `hCross` binder.
    ############################################################################### -/

/-- **★★★ `hcross_of_geometry_gate_supp_existRho`.**  The full live `hCross` mixed-second-difference binder
    (`h, k > 0` quadrant) for the concrete gated van-Vleck witness, obtained by COMPOSING the reshaped
    far-rate capstone (§A, with the geometry-determined per-`D` split radius `ρ`) with the actual
    downstream consumer `hcross_of_censusIntegral_bound` (J4-929) at `C_far := Cpair + Cenv·√2ⁿ·√ε`.  This
    CERTIFIES that the ultimate `hCross` consumer accepts an EXISTENTIALLY-CHOSEN (geometry-determined)
    `ρ`: the reshaped capstone produces the `ρ`-FREE `hCensusBound` that `hcross_of_censusIntegral_bound`
    consumes, so no re-derivation of the `hcross` composition is needed.  The caller supplies, for ANY
    fixed gate record `D` with `D.r ≤ rAmp` and ANY per-`D` split data `(ρ, MF, Cpair)`, the support fact
    `hSupp`, the off-ball F-factor bound `hF(ρ)`, integrability `hΦint`, the on-ball trace rate
    `hballrate(ρ)`, together with the J4-929 differentiation carries `hFmeasG`, the four
    interval-integrabilities, the engine bundle `hEnv`, and the cheap `H_near`/`H_zero`.  NOT `a₁ = R/6`. -/
theorem hcross_of_geometry_gate_supp_existRho (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h k τ₀ M : ℝ)
    (hε : 0 < ε) (hτ₀ : 0 < τ₀) (hh : 0 < h) (hk : 0 < k) (hM : 0 ≤ M) (hcap : ε + h ≤ τ₀) :
    ∃ rAmp : ℝ, 0 < rAmp ∧
      ∀ D : FixedFlowGateData g gi hC hK, D.r ≤ rAmp →
        ∀ (ρ MF Cpair : ℝ), 0 < ρ → 0 ≤ MF → 0 ≤ Cpair →
        (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          Integrable
            (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
              * F s z 0) volume) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          |∫ z in Metric.ball (0 : Point n) ρ,
            deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
              ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) →
        -- the J4-929 differentiation carries (opaque, banked non-vacuous):
        (∀ s u' : ℝ, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (u' - s) 0 z * F s z 0) volume) →
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
            volume (u - ε) (u - ε + k) →
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)
            volume (u - ε) (u - ε + k) →
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
            volume 0 (u - ε) →
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)
            volume 0 (u - ε) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          ∃ V ∈ 𝓝 a, ∃ Dz : Point n → ℝ,
            Integrable Dz volume ∧
            Integrable
              (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume ∧
            AEStronglyMeasurable
              (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
                * F s z 0) volume ∧
            (∀ᵐ z ∂volume, ∀ a' ∈ V,
              ‖deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s) * F s z 0‖
                ≤ Dz z) ∧
            (∀ᵐ z ∂volume, ∀ a' ∈ V,
              HasDerivAt
                (fun a' => vanVleckGatedWitness g gi hC hK S cutA cutB (a' - s) 0 z * F s z 0)
                (deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s)
                  * F s z 0) a')) →
        (∀ s ∈ Set.Icc u (u + h),
          |(∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
              - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)| ≤ 2 * M) →
        (∀ s ∈ Set.Ioi (u + h),
          (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
            - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0) = 0) →
        ∃ Cenv : ℝ, 0 ≤ Cenv ∧
          |heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F (u + h) (u - ε + k) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F (u + h) (u - ε) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F u (u - ε + k) 0 0
              + heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F u (u - ε) 0 0|
            ≤ (2 * (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) / Real.sqrt ε + 2 * M / ε)
                * (|h| * |k|) := by
  obtain ⟨rAmp, hrAmp, hcapstone⟩ :=
    censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho hn g gi hC hK S cutA cutB
      h0Kmem hg hg0 hu F u ε h τ₀ hε hτ₀ hh.le hcap
  refine ⟨rAmp, hrAmp, ?_⟩
  intro D hDr ρ MF Cpair hρ hMF hCpair hSupp hF hΦint hballrate
    hFmeasG hah_hi ha_hi hah_lo ha_lo hEnv H_near H_zero
  obtain ⟨lam', Cenv, hlam', hCenv, hAll⟩ :=
    hcapstone D hDr ρ MF Cpair hρ hMF hCpair hSupp hF hΦint hballrate
  refine ⟨Cenv, hCenv, ?_⟩
  have hCf : 0 ≤ Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε := by
    have h1 : 0 ≤ Cenv * Real.sqrt 2 ^ n * Real.sqrt ε :=
      mul_nonneg (mul_nonneg hCenv (by positivity)) (Real.sqrt_nonneg _)
    linarith
  exact hcross_of_censusIntegral_bound g gi hC hK S cutA cutB F u ε h k
    (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) M hε hh hk hCf hM
    hFmeasG hah_hi ha_hi hah_lo ha_lo hEnv hAll H_near H_zero

/-! ###############################################################################
    ### §C — NON-VACUITY (TEETH).
    ############################################################################### -/

/-- **`existRho_innerBundle_satisfiable` — TEETH for the moved-inside carry bundle.**  The reshaped
    capstone's per-`D` inner antecedent bundle `{0 < ρ, 0 ≤ MF, 0 ≤ Cpair, hSupp, hF(ρ), hΦint,
    hballrate(ρ)}` is JOINTLY satisfiable at a genuinely-nonempty census gate: `K := {0}`, `S := univ`
    (so `z ∈ K ∧ 0 ∈ S z` holds at `z = 0`), an explicit `FixedFlowGateData` `D`, `ρ := 1/4`,
    `MF = Cpair := 0`, `F ≡ 0` (so the deriv-witness integrand `Φ ≡ 0`: integrable, and both the ball-
    trace and F-factor bounds hold trivially).  Exercises the newly-moved-inside `ρ`/`hF`/`hballrate`
    binders concretely.  NOT `a₁ = R/6`. -/
theorem existRho_innerBundle_satisfiable (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (cutA cutB : ℝ) :
    ∃ (K : Set (Point n)) (hK : IsCompact K) (S : Point n → Set (Point n))
      (D : FixedFlowGateData g gi hC hK) (F : ℝ → Point n → Point n → ℝ)
      (u ε h ρ MF Cpair : ℝ),
      ((0 : Point n) ∈ K ∧ (0 : Point n) ∈ S 0) ∧
      0 < ε ∧ 0 < ρ ∧ 0 ≤ MF ∧ 0 ≤ Cpair ∧ 0 ≤ h ∧
      (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        Integrable
          (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
            * F s z 0) volume) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        |∫ z in Metric.ball (0 : Point n) ρ,
          deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
            ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) := by
  classical
  have hK0 : IsCompact ({0} : Set (Point n)) := isCompact_singleton
  refine ⟨({0} : Set (Point n)), hK0, fun _ => Set.univ,
    { a := 1 / 3, b := 1 / 2, r := 1, eta := 1 / 2, lam := 4,
      ha := by norm_num, hab := by norm_num, hbr := by norm_num,
      heta := by norm_num, hlam := by norm_num, hgap := by norm_num,
      hgate := by
        intro z hz _
        rw [Set.mem_singleton_iff] at hz; subst hz
        have h0 : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
        rw [h0, mul_zero]; exact rncRadialSq_nonneg _ },
    (fun _ _ _ => (0 : ℝ)), 0, 1 / 2, 1, 1 / 4, 0, 0,
    ⟨Set.mem_singleton_iff.mpr rfl, Set.mem_univ _⟩,
    by norm_num, by norm_num, le_refl _, le_refl _, zero_le_one, ?_, ?_, ?_, ?_⟩
  · -- hSupp: only `z = 0`; `‖0‖ = 0 < D.r = 1`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    show ‖(0 : Point n)‖ < 1
    rw [norm_zero]; exact one_pos
  · -- hF: `F ≡ 0`, so `|0| = 0 ≤ MF = 0`.
    intro s _ z _; simp
  · -- hΦint: `F ≡ 0`, so the integrand is `0`.
    intro s _ a _
    have hz : (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK0 (fun _ => Set.univ)
          cutA cutB r 0 z) (a - s) * (0 : ℝ)) = fun _ => (0 : ℝ) := by
      funext z; rw [mul_zero]
    rw [hz]; exact integrable_zero _ _ _
  · -- hballrate: `F ≡ 0`, so `|∫ 0| = 0 ≤ Cpair·… = 0`.
    intro s _ a _
    have hz : (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK0 (fun _ => Set.univ)
          cutA cutB r 0 z) (a - s) * (0 : ℝ)) = fun _ => (0 : ℝ) := by
      funext z; rw [mul_zero]
    rw [hz]
    simp

/-- **`census_existRho_smallRadius_gate_exists` — the reshaped capstone's `∀ D, D.r ≤ rAmp → …` binder is
    NON-VACUOUS.**  Valid small-radius gate records always exist (re-export of the banked
    `census_smallRadius_gate_exists`), so `censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho`
    and `hcross_of_geometry_gate_supp_existRho` are certifiably NOT vacuously quantified over `D`.
    NOT `a₁ = R/6`. -/
theorem census_existRho_smallRadius_gate_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (target : ℝ) (htarget : 0 < target) :
    ∃ D : FixedFlowGateData g gi hC hK, 0 < D.r ∧ D.r ≤ target :=
  census_smallRadius_gate_exists g gi hC hK target htarget

end QIQTH.CensusExistRhoRethread

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusExistRhoRethread
#print axioms censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho
#print axioms hcross_of_geometry_gate_supp_existRho
#print axioms existRho_innerBundle_satisfiable
#print axioms census_existRho_smallRadius_gate_exists
end AxiomChecks
