/-
  HCrossDerivEngineWired — J4-929: WIRE the banked differentiation-under-integral engine into J4-928's
  `hderiv`, collapsing the whole `hCross` (h,k>0) binder onto a SINGLE scalar census integral inequality.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE / API-LOCALIZATION brick.  No `sorry`, no new axioms, no `:= True`, no vacuous
  hypothesis, none equal to the conclusion, no existing file edited.

  ## WHERE THIS SITS (verified against the live defs + gpt-5.6-sol high go/no-go, not memory).
  J4-928 (`HCrossFarDerivBridge.lean`) reduced the live `hCross` mixed-second-difference binder (h,k>0
  quadrant) to `hcross_split_bound_of_hderiv`, whose sole hard carry is the GENERATOR IDENTITY
      `hderiv : ∀ s ∈ Ioo(u−ε)u, ∀ a ∈ Icc u (u+h), HasDerivAt (a' ↦ ∫ z, A(a'−s) x z · B s z y) (g s a) a`
  together with `hgbound : |g s a| ≤ C_far·(u−s)^{−1/2}`.  J4-928's honest report named `hderiv` "the
  opaque chart wall", packaging TWO distinct kinds of content:
    (1) DIFFERENTIATION UNDER THE `z`-INTEGRAL — turning `∂_a ∫_z Φ` into `∫_z ∂_a Φ`;
    (2) the SCALAR BOUND on the resulting census integral (the chart change-of-variables + J4-924).

  ## THE DECISIVE (re-)AUDIT (this file's content).  Content (1) is **ALREADY BANKED** for the concrete
  gated van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S cutA cutB`:
    • the engine `HeatResidualBound.heatConvInner_hasDerivAt` (Mathlib
      `hasDerivAt_integral_of_dominated_loc_of_deriv_le`) lifts a per-`z` `HasDerivAt` + an integrable
      `z`-dominator into the `z`-INTEGRAL `HasDerivAt` with derivative `∫_z ∂_a Φ`;
    • the per-`z` `HasDerivAt` is banked UNCONDITIONALLY (`WitnessTimeDeriv.witnessZTime_hasDerivAt`, J4-915);
    • the integrable Gaussian-pair dominator `Dz` is EXPLICITLY CONSTRUCTED by
      `HZDataFromCrudeEnv.witnessHZslice_of_crudeEnv` (J4-916) from the J4-911-class crude-environment
      carries (`hAcrude` DISCHARGED at J4-917, plus `hFdom`/`hmeas`/`hbase`).
  So `hderiv` at the concrete witness needs NO new differentiation content: `g s a` is FORCED to be the
  census integral `∫ z, ∂_τ(witness)·F`, and the ENTIRE remaining wall is content (2) — the pure scalar
  inequality `|∫ z, ∂_τ(witness r 0 z)|_{τ=a−s} · F s z 0| ≤ C_far·(u−s)^{−1/2}`.

  ## WHAT LANDS.
    • `censusDeriv_hasDerivAt` — ★ per `(s,a)`: the ENGINE-wired `HasDerivAt` of the census integral, with
      derivative FORCED to `∫ z, deriv(fun r ↦ witness r 0 z)(a−s)·F s z 0`.  Direct instantiation of the
      banked engine at the concrete witness with `dAu := fun τ x z ↦ deriv(fun r ↦ witness r x z) τ`.
    • `hEnv_of_witnessCrudeEnv` — ★ the PROVIDER: J4-916 (`witnessHZslice_of_crudeEnv`) supplies the exact
      per-`(s,a)` engine-carry bundle `hEnv` this file consumes (non-vacuity by construction — `hEnv` is
      INHABITED whenever the banked crude-environment carries hold, they are `hZslice`-satisfiable).
    • `hcross_of_censusIntegral_bound` — ★★★ THE CAPSTONE: the full live `hCross` binder (h,k>0) for the
      concrete witness from `{hEnv, hCensusBound, H_near, H_zero}` + the four interval-integrabilities,
      where the ONLY remaining analytic carry `hCensusBound` is the pure scalar census inequality (NO
      `HasDerivAt` / differentiation content left).  J4-928's `hderiv` is FULLY WIRED away; the residue is
      exactly content (2) = the chart-CoV + J4-924 wall.

  ## HONEST STATUS (gpt-5.6-sol high, verbatim NO-GO).  This does **NOT** close `hCross`.  The remaining
  `hCensusBound` IS the opaque chart wall, and it does NOT compose from the banked pieces: (i) the banked
  CoV `chart_gaussian_change_variables_concrete` (J4-270) is for the FIELD-slot chart
  `uniformInverseChart … 0 z`, but the census integrates the BASE slot (`uniformInverseChart … z 0`) — a
  GENUINE slot mismatch, no base-slot CoV banked; (ii) the CoV is over `ball 0 ρ`, the census over `ℝⁿ`
  (tail residue); (iii) the concrete transformed weights `(amp·F)∘V/|det|`, `(Cfield·F)∘V/|det|` are
  UNVERIFIED bounded + center-Lipschitz (J4-924's header disclaims exactly these).  So this file is a
  genuine wall-LOCALIZATION (differentiation content eliminated), NOT a wall-closure.  `hDuhamel`/`hDConv`
  remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import Mathlib
import QIQTH.HCrossFarDerivBridge
import QIQTH.HeatConvRegularity
import QIQTH.HZDataFromCrudeEnv

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.FlatHeatEquation
open QIQTH.HZDataFromCrudeEnv QIQTH.WitnessTimeDeriv
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §A — the ENGINE-wired per-`(s,a)` census-integral `HasDerivAt` (content (1), BANKED).
    ############################################################################### -/

/-- **★ `censusDeriv_hasDerivAt` — the differentiation-under-the-`z`-integral, WIRED at the concrete
    witness.**  For the concrete gated van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S cutA cutB`
    and any frozen field `F`, GIVEN the banked engine-carry bundle at `(s,a)` — a neighbourhood `V ∋ a`,
    an integrable `z`-dominator `Dz`, the base-integrability + deriv-slice-measurability, the uniform-over-`V`
    dominator bound, and the per-`z` `HasDerivAt` (all supplied by `witnessHZslice_of_crudeEnv`, J4-916) —
    the census integral is TIME-differentiable at `a` with derivative FORCED to `∫ z, ∂_τ(witness)·F`:
      `HasDerivAt (a' ↦ ∫ z, witness(a'−s) 0 z · F s z 0) (∫ z, deriv(fun r ↦ witness r 0 z)(a−s)·F s z 0) a`.
    Direct instantiation of the banked engine `heatConvInner_hasDerivAt` with
    `dAu := fun τ x z ↦ deriv(fun r ↦ witness r x z) τ`.  NOT `a₁ = R/6`. -/
theorem censusDeriv_hasDerivAt
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (s a : ℝ)
    (hFmeas : ∀ u' : ℝ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (u' - s) 0 z * F s z 0) volume)
    (V : Set ℝ) (hV : V ∈ 𝓝 a) (Dz : Point n → ℝ) (hDz : Integrable Dz volume)
    (hFint : Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume)
    (hF'meas : AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
          * F s z 0) volume)
    (hbound : ∀ᵐ z ∂volume, ∀ a' ∈ V,
        ‖deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s) * F s z 0‖
          ≤ Dz z)
    (hdiff : ∀ᵐ z ∂volume, ∀ a' ∈ V,
        HasDerivAt (fun a' => vanVleckGatedWitness g gi hC hK S cutA cutB (a' - s) 0 z * F s z 0)
          (deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s) * F s z 0) a') :
    HasDerivAt (fun a' => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (a' - s) 0 z * F s z 0)
      (∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0) a :=
  heatConvInner_hasDerivAt (vanVleckGatedWitness g gi hC hK S cutA cutB)
    (fun τ x z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r x z) τ)
    F s a 0 0 V hV hFmeas hFint hF'meas Dz hDz hbound hdiff

/-! ###############################################################################
    ### §B — the PROVIDER: J4-916 supplies the per-`(s,a)` engine-carry bundle (non-vacuity).
    ############################################################################### -/

/-- **★ `hEnv_of_witnessCrudeEnv` — the per-`(s,a)` engine-carry bundle is INHABITED by J4-916.**  The
    exact `∃ V ∈ 𝓝 a, ∃ Dz, …` bundle that `hcross_of_censusIntegral_bound`'s `hEnv` consumes is precisely
    the OUTPUT of `witnessHZslice_of_crudeEnv` (J4-916) at base point `c := a`.  Given the J4-911-class
    crude-environment carries (`hAcrude` DISCHARGED at J4-917, `hFdom`, `hmeas`, `hbase`) with the diagonal
    avoided (`τ₀ < a−s < τ₁`, `0 < s`), the bundle holds — so `hEnv` is NON-VACUOUSLY satisfiable (no
    unsatisfiable-antecedent trap): the differentiation environment is the banked J4-916 crude-env, cleanly
    separated from the census-magnitude wall.  NOT `a₁ = R/6`. -/
theorem hEnv_of_witnessCrudeEnv
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (s a : ℝ)
    (τ₀ τ₁ Ccr wL CF wF : ℝ)
    (hτ₀ : 0 < τ₀) (hwL : 0 < wL) (hCcr : 0 ≤ Ccr) (hCF : 0 ≤ CF) (hwF : 0 < wF) (hs : 0 < s)
    (hlo : τ₀ < a - s) (hhi : a - s < τ₁)
    (hAcrude : ∀ z : Point n, ∀ τ ∈ Set.Icc τ₀ τ₁,
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ|
          ≤ Ccr * τ⁻¹ * gaussDdim (wL * τ) (0 - z))
    (hFdom : ∀ z : Point n, |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hmeas : AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
          * F s z 0) volume)
    (hbase : Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume) :
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
        HasDerivAt (fun a' => vanVleckGatedWitness g gi hC hK S cutA cutB (a' - s) 0 z * F s z 0)
          (deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s) * F s z 0)
          a') :=
  witnessHZslice_of_crudeEnv g gi hC hK S cutA cutB F s a τ₀ τ₁ Ccr wL CF wF
    hτ₀ hwL hCcr hCF hwF hs hlo hhi hAcrude hFdom hmeas hbase

/-! ###############################################################################
    ### §C — THE CAPSTONE: the live `hCross` binder from a PURE scalar census inequality.
    ############################################################################### -/

/-- **★★★ `hcross_of_censusIntegral_bound` — the live `hCross` binder (h,k>0) from a SCALAR census
    inequality (all differentiation content wired away).**  For the concrete gated van-Vleck witness
    `A := vanVleckGatedWitness g gi hC hK S cutA cutB`, base times `a = u`, `b = u−ε`, shifts `h,k > 0`,
    GIVEN the four interval-integrabilities, the global slice-measurability `hFmeasG`, the per-`(s,a)`
    engine-carry bundle `hEnv` (J4-916; non-vacuous by `hEnv_of_witnessCrudeEnv`), the cheap carries
    `H_near`/`H_zero`, and — the ONLY remaining analytic obligation — the PURE SCALAR census inequality
      `hCensusBound : |∫ z, deriv(fun r ↦ witness r 0 z)(a−s) · F s z 0| ≤ C_far·(u−s)^{−1/2}`,
    the MIXED SECOND DIFFERENCE obeys the exact live `hCross` binder
        `|Δ²|  ≤  (2·C_far/√ε + 2·M/ε) · (|h|·|k|)`.
    `hderiv` is FULLY WIRED (via `censusDeriv_hasDerivAt`, forcing `g s a = ∫ z, ∂_τ(witness)·F`), so this
    localizes the whole `hCross` wall (h,k>0) to `hCensusBound` alone — a scalar integral inequality with
    NO `HasDerivAt` content, EXACTLY the chart-CoV + J4-924 residue (STILL OPEN).  NOT `a₁ = R/6`. -/
theorem hcross_of_censusIntegral_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (hk : 0 < k) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hFmeasG : ∀ s u' : ℝ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (u' - s) 0 z * F s z 0) volume)
    (hah_hi : IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
        volume (u - ε) (u - ε + k))
    (ha_hi : IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)
        volume (u - ε) (u - ε + k))
    (hah_lo : IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
        volume 0 (u - ε))
    (ha_lo : IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)
        volume 0 (u - ε))
    (hEnv : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
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
                * F s z 0) a'))
    (hCensusBound : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
            * F s z 0|
          ≤ C_far * (u - s) ^ (-(1 : ℝ) / 2))
    (H_near : ∀ s ∈ Set.Icc u (u + h),
        |(∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
            - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)| ≤ 2 * M)
    (H_zero : ∀ s ∈ Set.Ioi (u + h),
        (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
          - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0) = 0) :
    |heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F (u + h) (u - ε + k) 0 0
        - heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F (u + h) (u - ε) 0 0
        - heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F u (u - ε + k) 0 0
        + heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F u (u - ε) 0 0|
      ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (|h| * |k|) := by
  refine hcross_split_bound_of_hderiv (vanVleckGatedWitness g gi hC hK S cutA cutB) F 0 0
    u ε h k C_far M hε hh hk hCf hM hah_hi ha_hi hah_lo ha_lo
    (fun s a => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
      * F s z 0)
    ?_ hCensusBound H_near H_zero
  intro s hs a ha
  obtain ⟨V, hV, Dz, hDz, hFint, hF'meas, hbnd, hdiff⟩ := hEnv s hs a ha
  exact censusDeriv_hasDerivAt g gi hC hK S cutA cutB F s a (hFmeasG s) V hV Dz hDz hFint
    hF'meas hbnd hdiff

end QIQTH.HeatResidualBound

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms censusDeriv_hasDerivAt
#print axioms hEnv_of_witnessCrudeEnv
#print axioms hcross_of_censusIntegral_bound
end AxiomChecks
