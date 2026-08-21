/-
  CensusPhiIntegrabilityDischarge — DISCHARGE the C2 integrability carry `hΦint` of the any-`S`
  census capstone `censusBound_of_geometry_gate_supp_F_ballRate_anyS` (J4-951) to the STANDARD F2
  gate/chart measurability carriers + the banked crude `∂_τ` envelope + the width-2 Levi domination.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure carry-reduction brick: it eliminates the ABSTRACT integrability hypothesis `hΦint` of the
  most-discharged any-`S` census capstone in favour of {the two STANDARD F2 gate/chart measurability
  carriers `hKSmeas`/`hcar` already threaded through the whole live assembly, the banked crude `∂_τ`
  domination envelope `witnessTimeDeriv_domination_global_anyS` (J4-950), the abstract Levi factor's
  `z`-slice measurability `hFmeas`, and the width-2 Levi Gaussian domination `hFdom` = the
  `{hDuhamel, hDConv, hCConv}`-family object}.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, none equal to the conclusion, no existing banked file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT `hΦint` IS.  The capstone takes the OFF-window integrability of the concrete gated census
  integrand
      `hΦint : ∀ s ∈ Ioo (u-ε) u, ∀ a ∈ Icc u (u+h),
          Integrable (fun z ↦ deriv (fun r ↦ vanVleckGatedWitness … r 0 z) (a-s) · F s z 0) volume`.
  Integrability = measurability + a dominating integrable envelope.  For an ARBITRARY abstract gate
  family `S : Point n → Set (Point n)` the deriv-witness `z`-slice need not be measurable WITHOUT a
  measurability hypothesis on the gate — this is the "arbitrary-`S` gate branching" concern.

  ## THE MECHANISM (three layers).
    • (1) `censusPhi_integrable_of_measAndDom` — the DOMINATION half, PROVEN OUTRIGHT.  Given the exact
      per-slice measurability `hDmeas`, the crude `∂_τ` envelope `hcrude`
      (`|deriv τ| ≤ C·τ⁻¹·gaussDdim (4·D.lam·τ) z`) and the width-2 Levi domination `hFdom`
      (`|F s z 0| ≤ C_L·gaussDdim (2 s) z`), the integrand is dominated pointwise by
      `(C·τ⁻¹·C_L)·(gaussDdim (4·D.lam·τ) z · gaussDdim (2 s) z)`, a PRODUCT OF TWO GAUSSIANS, integrable
      by the banked `gaussDdim_pair_integrable` (any widths).  `Integrable.mono'` closes it.  `τ = a-s`
      lands in `(0, τ₀]` (from `ε+h ≤ τ₀`) and `s` in `(0, T]` (from `ε < u ≤ T`).
    • (2) `derivSlice_stronglyMeasurable_of_gateCarriers` — the MEASURABILITY reduction.  The banked
      `HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4` gives the FULL joint `(τ,p,q)`
      **StronglyMeasurable**ity of the `∂_τ` witness kernel from the STANDARD carriers `{hKSmeas, hcar}`;
      composing with the measurable section `z ↦ (τ, 0, z)` yields `StronglyMeasurable
      (fun z ↦ deriv (fun r ↦ Wit r 0 z) τ)` for the EXACT integrand (field point fixed at `0`, base `z`).
      Arbitrary-`S` branching is handled by CARRYING `hKSmeas`/`hcar`, NOT by assuming `S` nice.
    • (3) `censusPhi_integrable_of_gateCarriers` / `censusPhi_integrable_of_amplitudeCarries` — the
      COMBINED interface: build the product measurability `hDmeas` from (2) and `hFmeas`, feed (1); and a
      wrapper deriving `hcrude` INTERNALLY from the amplitude sups `hAmp0`/`hCfield`/`hSupp` via
      `witnessTimeDeriv_domination_global_anyS` — producing EXACTLY the capstone's `hΦint` binder.

  ## HONEST STATUS (gpt-5.6-sol high adversarial audit — a CONDITIONAL discharge, not unconditional).
  Under `{hKSmeas, hcar, hFmeas, hcrude (or the amplitude hypotheses producing it), hFdom}` the capstone's
  `hΦint` is DISCHARGED: the opaque `Integrable` carry is eliminated, and the per-slice measurability
  `hDmeas` is GENUINELY derived (layer 2) from the two STANDARD carriers `hKSmeas`/`hcar` that the whole
  live assembly already consumes (`tauDeriv_prod_stronglyMeasurable_v4`, `hWitDeriv_discharged`,
  `f2Pack_concrete_v3`, `constGate_hS1`).  `hcar` packages the chart-Borel measurability, which has a
  KNOWN DEFINITIONAL WALL (`ChartJointBorel.chartJoint_measurable_of_rep`: `uniformInverseChart` is built
  from `Classical.choose`, measurable only via a global representative on `K`) — so `hcar` is a STANDING
  carrier, carried upstream, NOT discharged here and NOT introduced here.  The DOMINATION content
  (layer 1) is concretely non-vacuous (`…_measAndDom_satisfiable`, `F ≡ 0`, self-contained crude envelope,
  no chart wall); the gate-set measurability is realizable at a PROPER measurable gate
  (`…_jointGate_measurable_satisfiable`, `S := ball 0 1 ≠ univ`).  NO standalone non-vacuity claim is made
  for `hcar` or for the full combined antecedent.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusAnySEnvelopeRethread
import QIQTH.HgateSatAudit
import QIQTH.CConvV2GaussianPairing

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.InverseChartNormalJets QIQTH.OnGateJets
open QIQTH.CensusTauDerivGateSplit QIQTH.CensusTauDerivAnySEnvelope
open QIQTH.CensusAmplitudeSupDischarge
open QIQTH.WitnessTimeDerivEnvelope
open QIQTH.HgateSatAudit QIQTH.CConvV2GaussianPairing
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CensusPhiIntegrabilityDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — LAYER 1: the DOMINATION half, PROVEN OUTRIGHT (product-of-two-Gaussians).
    ############################################################################### -/

/-- **★★★ `censusPhi_integrable_of_measAndDom` — the DOMINATION half of `hΦint`, PROVEN.**  Given the
    exact per-slice measurability `hDmeas`, the banked crude `∂_τ` domination envelope `hcrude`, and the
    width-2 Levi Gaussian domination `hFdom`, the concrete gated census integrand is integrable on the
    window: at `τ = a-s ∈ (0, τ₀]`, `s ∈ (0, T]`, it is dominated pointwise by
    `(C·τ⁻¹·C_L)·(gaussDdim (4·D.lam·τ) z · gaussDdim (2 s) z)`, a PRODUCT OF TWO GAUSSIANS, integrable by
    the banked `gaussDdim_pair_integrable`.  `Integrable.mono'` closes it.  NOT `a₁ = R/6`. -/
theorem censusPhi_integrable_of_measAndDom
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h τ₀ T C C_L : ℝ)
    (hεu : ε < u) (huT : u ≤ T) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀) (hC_L : 0 ≤ C_L)
    (hDmeas : ∀ s a : ℝ, AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
          * F s z 0) volume)
    (hcrude : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ|
          ≤ C * τ⁻¹ * gaussDdim (4 * D.lam * τ) z)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      Integrable (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
        * F s z 0) volume := by
  intro s hs a ha
  have hspos : 0 < s := by have := hs.1; linarith
  have hτpos : 0 < a - s := by have h1 := hs.2; have h2 := ha.1; linarith
  have hτcap : a - s ≤ τ₀ := by have h1 := hs.1; have h2 := ha.2; linarith
  have hsT : s ≤ T := le_trans (le_of_lt hs.2) huT
  -- envelope: constant × product of two Gaussians, integrable.
  have hEnv : Integrable
      (fun z : Point n => (C * (a - s)⁻¹ * C_L)
        * (gaussDdim (4 * D.lam * (a - s)) z * gaussDdim (2 * s) z)) volume :=
    (gaussDdim_pair_integrable (4 * D.lam * (a - s)) (2 * s)).const_mul _
  refine hEnv.mono' (hDmeas s a) (Filter.Eventually.of_forall (fun z => ?_))
  have hd := hcrude (a - s) hτpos hτcap z
  have hf := hFdom s hspos hsT z 0
  rw [sub_zero] at hf
  have hb : (0 : ℝ) ≤ C * (a - s)⁻¹ * gaussDdim (4 * D.lam * (a - s)) z := le_trans (abs_nonneg _) hd
  calc ‖deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0‖
      = |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)| * |F s z 0| := by
        rw [Real.norm_eq_abs, abs_mul]
    _ ≤ (C * (a - s)⁻¹ * gaussDdim (4 * D.lam * (a - s)) z) * (C_L * gaussDdim (2 * s) z) :=
        mul_le_mul hd hf (abs_nonneg _) hb
    _ = (C * (a - s)⁻¹ * C_L) * (gaussDdim (4 * D.lam * (a - s)) z * gaussDdim (2 * s) z) := by ring

/-! ###############################################################################
    ### §B — LAYER 2: the per-slice MEASURABILITY, reduced to the STANDARD `{hKSmeas, hcar}` carriers.
    ############################################################################### -/

/-- **★★ `derivSlice_stronglyMeasurable_of_gateCarriers` — the deriv-witness `z`-slice measurability
    from the STANDARD F2 carriers.**  The banked `HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4` gives
    the FULL joint `(τ,p,q)` `StronglyMeasurable`ity of the `∂_τ` witness kernel from `{hKSmeas, hcar}`;
    composing with the measurable section `z ↦ (τ, 0, z)` yields, for EVERY `τ`,
    `StronglyMeasurable (fun z ↦ deriv (fun r ↦ vanVleckGatedWitness … r 0 z) τ)` — the EXACT integrand
    slice (field point fixed at `0`, base `z`).  Arbitrary `S` is fine: its branching measurability is
    supplied by `hKSmeas`, the on-gate derivative data by `hcar`.  NOT `a₁ = R/6`. -/
theorem derivSlice_stronglyMeasurable_of_gateCarriers (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK cutA cutB w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK cutA cutB u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)) :
    ∀ τ : ℝ, StronglyMeasurable
      (fun z : Point n => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ) := by
  intro τ
  have hv4 := tauDeriv_prod_stronglyMeasurable_v4 hn g gi hC hK S cutA cutB hKSmeas hcar
  have hφ : Measurable (fun z : Point n => (τ, ((0 : Point n), z))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  exact hv4.comp_measurable hφ

/-! ###############################################################################
    ### §C — LAYER 3: the COMBINED interface — the capstone's `hΦint` binder, from the carriers.
    ############################################################################### -/

/-- **★★★ `censusPhi_integrable_of_gateCarriers` — `hΦint` from the STANDARD carriers + crude envelope +
    Levi domination.**  Combines layer 2 (deriv-witness `z`-slice `StronglyMeasurable` from `{hKSmeas,
    hcar}`) with the abstract Levi factor's `z`-slice measurability `hFmeas` to build the product
    measurability, then feeds layer 1.  Produces EXACTLY the capstone's `hΦint` binder.  NOT `a₁ = R/6`. -/
theorem censusPhi_integrable_of_gateCarriers (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK cutA cutB w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK cutA cutB u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hFmeas : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z 0) volume)
    (u ε h τ₀ T C C_L : ℝ)
    (hεu : ε < u) (huT : u ≤ T) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀) (hC_L : 0 ≤ C_L)
    (hcrude : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ|
          ≤ C * τ⁻¹ * gaussDdim (4 * D.lam * τ) z)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      Integrable (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
        * F s z 0) volume := by
  have hderivSM := derivSlice_stronglyMeasurable_of_gateCarriers hn g gi hC hK S cutA cutB hKSmeas hcar
  refine censusPhi_integrable_of_measAndDom g gi hC hK S cutA cutB D F u ε h τ₀ T C C_L
    hεu huT hh hcap hC_L ?_ hcrude hFdom
  intro s a
  exact (hderivSM (a - s)).aestronglyMeasurable.mul (hFmeas s)

/-- **★★★ `censusPhi_integrable_of_amplitudeCarries` — the capstone `hΦint`, crude envelope discharged
    INTERNALLY from the amplitude sups.**  Same conclusion as `censusPhi_integrable_of_gateCarriers`, but
    the crude `∂_τ` domination envelope is supplied INTERNALLY by the banked any-`S` supplier
    `witnessTimeDeriv_domination_global_anyS` (J4-950) from the amplitude sups `hAmp0`/`hCfield`/`hSupp`
    (already discharged upstream by `census_amplitude_supBounds`).  Produces EXACTLY the `hΦint` binder of
    `censusBound_of_amplitudeCarries_Fbound_ballRate_anyS` / `censusBound_of_geometry_gate_supp_F_ballRate_anyS`
    (J4-951), from {`hKSmeas`, `hcar`, `hFmeas`, amplitude sups, `hFdom` (width-2 Levi)}.  NOT `a₁ = R/6`. -/
theorem censusPhi_integrable_of_amplitudeCarries (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ)
    (hτ₀ : 0 < τ₀) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (F : ℝ → Point n → Point n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK cutA cutB w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK cutA cutB u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hFmeas : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z 0) volume)
    (u ε h T C_L : ℝ)
    (hεu : ε < u) (huT : u ≤ T) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀) (hC_L : 0 ≤ C_L)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      Integrable (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
        * F s z 0) volume := by
  obtain ⟨C, _hCpos, hcrude⟩ :=
    witnessTimeDeriv_domination_global_anyS hn g gi hC hK S cutA cutB D τ₀ M M'
      hτ₀ hM hM' hAmp0 hCfield hSupp
  exact censusPhi_integrable_of_gateCarriers hn g gi hC hK S cutA cutB D F hKSmeas hcar hFmeas
    u ε h τ₀ T C C_L hεu huT hh hcap hC_L hcrude hFdom

/-! ###############################################################################
    ### §D — NON-VACUITY (TEETH).
    ############################################################################### -/

/-- **Non-vacuity of the DOMINATION layer `censusPhi_integrable_of_measAndDom` — TEETH.**  For ANY
    concrete geometry `(g, gi, hC)` at the singleton gate `K := {0}`, `S := univ`, the FULL layer-1
    hypothesis bundle {`hDmeas`, `hcrude`, `hFdom`, window} is jointly satisfiable by a GENUINE positive
    configuration — `F ≡ 0` (`C_L := 0`) makes `hDmeas`/`hFdom` trivial, and the crude envelope `hcrude`
    is supplied SELF-CONTAINED by the banked any-`S` supplier `witnessTimeDeriv_domination_global_anyS`
    from the AFFINE-in-`τ` amplitude sups at `0` (NO chart-Borel wall involved) — and the conclusion is
    over the NONEMPTY window `Ioo (u-ε) u = Ioo 1 2`, `Icc u (u+h) = Icc 2 2`.  The DOMINATION content is
    therefore concretely non-vacuous.  NOT `a₁ = R/6`. -/
theorem censusPhi_integrable_of_measAndDom_satisfiable (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (cutA cutB : ℝ) :
    ∃ (K : Set (Point n)) (hK : IsCompact K) (S : Point n → Set (Point n))
      (D : FixedFlowGateData g gi hC hK) (F : ℝ → Point n → Point n → ℝ)
      (u ε h τ₀ T C C_L : ℝ),
      ε < u ∧ u ≤ T ∧ 0 ≤ h ∧ ε + h ≤ τ₀ ∧ 0 ≤ C_L ∧
      (Set.Ioo (u - ε) u).Nonempty ∧ (Set.Icc u (u + h)).Nonempty ∧
      (∀ s a : ℝ, AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
          * F s z 0) volume) ∧
      (∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ|
          ≤ C * τ⁻¹ * gaussDdim (4 * D.lam * τ) z) ∧
      (∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) := by
  classical
  have hK0 : IsCompact ({0} : Set (Point n)) := isCompact_singleton
  set D : FixedFlowGateData g gi hC hK0 :=
    { a := 1 / 3, b := 1 / 2, r := 1, eta := 1 / 2, lam := 4,
      ha := by norm_num, hab := by norm_num, hbr := by norm_num,
      heta := by norm_num, hlam := by norm_num, hgap := by norm_num,
      hgate := by
        intro z hz _
        rw [Set.mem_singleton_iff] at hz; subst hz
        have h0 : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
        rw [h0, mul_zero]; exact rncRadialSq_nonneg _ } with hDdef
  -- the amplitude sups at `K = {0}`, τ-cap `τ₀ = 1`.
  set M : ℝ := |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0|
    + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| with hMdef
  set M' : ℝ := |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| with hM'def
  have hAmp0 : ∀ τ, 0 < τ → τ ≤ 1 → ∀ z ∈ ({0} : Set (Point n)), ‖z‖ < D.r →
      |chartFieldAmp g gi hC hK0 cutA cutB τ z 0| ≤ M := by
    intro τ hτ hτ1 z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    rw [chartFieldAmp_affine_slope, hMdef]
    calc |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0 + censusAmpTauDeriv g gi hC hK0 cutA cutB 0 * τ|
        ≤ |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0 * τ| := abs_add_le _ _
      _ = |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| * τ := by rw [abs_mul, abs_of_nonneg hτ.le]
      _ ≤ |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| * 1 := by
          have := mul_le_mul_of_nonneg_left hτ1 (abs_nonneg (censusAmpTauDeriv g gi hC hK0 cutA cutB 0))
          linarith
      _ = |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| := by rw [mul_one]
  have hCfield : ∀ z ∈ ({0} : Set (Point n)), ‖z‖ < D.r →
      |censusAmpTauDeriv g gi hC hK0 cutA cutB z| ≤ M' := by
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz; exact le_refl _
  have hSupp : ∀ z ∈ ({0} : Set (Point n)), (0 : Point n) ∈ (fun _ => Set.univ) z → ‖z‖ < D.r := by
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    show ‖(0 : Point n)‖ < 1
    rw [norm_zero]; exact one_pos
  obtain ⟨C, _hCpos, hcrude⟩ :=
    witnessTimeDeriv_domination_global_anyS hn g gi hC hK0 (fun _ => Set.univ) cutA cutB D 1 M M'
      one_pos (by positivity) (abs_nonneg _) hAmp0 hCfield hSupp
  refine ⟨({0} : Set (Point n)), hK0, (fun _ => Set.univ), D, (fun _ _ _ => (0 : ℝ)),
    2, 1, 0, 1, 2, C, 0,
    by norm_num, by norm_num, le_refl _, by norm_num, le_refl _,
    ⟨(3 : ℝ) / 2, by norm_num, by norm_num⟩, ⟨2, by norm_num, by norm_num⟩, ?_, hcrude, ?_⟩
  · -- hDmeas: `F ≡ 0`, so the integrand is `0`.
    intro s a; simp only [mul_zero]; exact aestronglyMeasurable_const
  · -- hFdom: `|0| ≤ 0 * gaussDdim …`.
    intro s _ _ z y; simp

/-- **Non-vacuity of the joint-gate measurability carrier `hKSmeas` at a PROPER gate — TEETH.**  At a
    genuinely non-`univ` gate `S := fun _ ↦ ball 0 1` (so `S z ≠ univ`, `n > 0`) over the compact
    neighbourhood `K := closedBall 0 1`, the joint-gate set `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}` IS
    measurable — the intersection of the two measurable coordinate-preimages (`K` closed ⟹ measurable;
    `ball 0 1` open ⟹ measurable).  Confirms the arbitrary-`S` gate-branching concern is realizable by a
    PROPER measurable gate, so `hKSmeas` is not a vacuous carrier.  NOT `a₁ = R/6`. -/
theorem censusPhi_jointGate_measurable_satisfiable :
    MeasurableSet {w : ℝ × Point n × Point n |
      w.2.2 ∈ Metric.closedBall (0 : Point n) 1 ∧ w.2.1 ∈ Metric.ball (0 : Point n) 1} := by
  have h1 : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ Metric.closedBall (0 : Point n) 1} :=
    (measurable_snd.comp measurable_snd) measurableSet_closedBall
  have h2 : MeasurableSet {w : ℝ × Point n × Point n | w.2.1 ∈ Metric.ball (0 : Point n) 1} :=
    (measurable_fst.comp measurable_snd) measurableSet_ball
  exact h1.inter h2

end QIQTH.CensusPhiIntegrabilityDischarge

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusPhiIntegrabilityDischarge
#print axioms censusPhi_integrable_of_measAndDom
#print axioms derivSlice_stronglyMeasurable_of_gateCarriers
#print axioms censusPhi_integrable_of_gateCarriers
#print axioms censusPhi_integrable_of_amplitudeCarries
#print axioms censusPhi_integrable_of_measAndDom_satisfiable
#print axioms censusPhi_jointGate_measurable_satisfiable
end AxiomChecks
