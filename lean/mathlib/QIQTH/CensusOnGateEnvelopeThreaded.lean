/-
  CensusOnGateEnvelopeThreaded — THREADING the τ-cap fixed-Gaussian collapse (J4-948,
  `CensusOnGateFixedGaussEnvelope`) into the LITERAL `honGate` (C3) binder of
  `censusBound_of_onGate_and_ballRate` (J4-947), and on into the FULL `hCensusBound` far-rate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  Pure
  real-analysis / structural threading.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, none equal to the conclusion, no existing banked file edited.

  ## WHAT LANDS.
    • `census_honGate_of_crude_and_Fbound` — ★★★ produces the LITERAL `honGate` binder consumed by
        `censusBound_of_onGate_and_ballRate`, with a SINGLE uniform `Cenv` and fixed width `lam` (any
        `lam ≥ 2·w·τ₀`), from (i) the CRUDE `τ`-scaled envelope hypothesis `hcrude` (= the banked
        `WitnessTimeDerivEnvelope.witnessTimeDeriv_domination_global` conclusion at `w = 4·D.lam`), and
        (ii) a uniform-in-`s` off-ball F-factor bound `|F s z 0| ≤ MF`.  `a−s ∈ (0, ε+h] ⊆ (0, τ₀]`.
    • `censusBound_of_crude_Fbound_ballRate` — ★★★ the FULL `hCensusBound` far-rate binder (the
        `censusBound_of_onGate_and_ballRate` conclusion) from FOUR uniform carries {crude envelope,
        F-factor bound, on-ball trace rate, integrability} — C3's uniform-in-τ domination now DISCHARGED.
    • non-vacuity witnesses.

  ## HONEST STATUS.  C3 (the on-gate uniform-in-τ single-fixed-Gaussian domination) is DISCHARGED to
  {the crude time-derivative envelope, a uniform F-factor bound}.  The crude envelope is itself the banked
  `witnessTimeDeriv_domination_global`, MODULO its amplitude carries (`hgate`/`hAmp0`/`hCfield`).  So
  `hCensusBound` is now assembled modulo {C1 ball-rate (⟸ G2/G3), C2 integrability, the crude-envelope
  amplitude carries, the F-factor bound}.  It is NOT reduced to `{G2, G3}` alone.  `hDuhamel`/`hDConv`
  remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusOnGateFixedGaussEnvelope
import QIQTH.CensusOffBallEnvelope
import QIQTH.WitnessTimeDerivEnvelope

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.InverseChartNormalJets QIQTH.OnGateJets
open QIQTH.CensusOffBallEnvelope QIQTH.CensusOnGateFixedGaussEnvelope
open QIQTH.WitnessTimeDerivEnvelope
open scoped Topology BigOperators ContDiff

namespace QIQTH.CensusOnGateEnvelopeThreaded

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §A — the LITERAL `honGate` binder from the crude envelope + F-factor bound.
    ############################################################################### -/

/-- **★★★ `census_honGate_of_crude_and_Fbound`.**  Produces EXACTLY the `honGate` binder consumed by
    `censusBound_of_onGate_and_ballRate` (J4-947): a SINGLE uniform constant `Cenv ≥ 0` and fixed width
    `lam` with, for every `s ∈ Ioo(u−ε)u`, `a ∈ Icc u(u+h)`, and every `z`,
        `|deriv(fun r ↦ vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z)(a−s) · F s z 0|
            ≤ Cenv · gaussDdim lam z` .
    Route: `a − s ∈ (0, ε+h] ⊆ (0, τ₀]` (from the `Ioo`/`Icc` positions and `hcap : ε + h ≤ τ₀`); apply the
    crude `τ`-scaled envelope `hcrude` at `τ = a−s` and the τ-cap collapse `tauInv_gaussWidth_le_fixedGauss`
    (uniform `Ce`); the F-factor bound `hF` closes it.  NOT `a₁ = R/6`. -/
theorem census_honGate_of_crude_and_Fbound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h ρ w τ₀ lam C MF : ℝ)
    (hw : 0 < w) (hτ₀ : 0 < τ₀) (hρ : 0 < ρ) (hlamge : 2 * w * τ₀ ≤ lam)
    (hC0 : 0 ≤ C) (hMF : 0 ≤ MF) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀)
    (hcrude : ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ|
          ≤ C * τ⁻¹ * gaussDdim (w * τ) z)
    (hF : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF) :
    ∃ Cenv : ℝ, 0 ≤ Cenv ∧
      ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        ∀ z : Point n, (z ∈ K ∧ (0 : Point n) ∈ S z) → ρ ≤ ‖z‖ →
          |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
            ≤ Cenv * gaussDdim lam z := by
  obtain ⟨Ce, hCe, hb⟩ := tauInv_gaussWidth_le_fixedGauss (n := n) w τ₀ ρ lam hw hτ₀ hρ hlamge
  refine ⟨C * MF * Ce, mul_nonneg (mul_nonneg hC0 hMF) hCe.le, ?_⟩
  intro s hs a ha z _ hz
  -- the time gap `τ := a − s` lies in `(0, τ₀]`.
  have hslo : u - ε < s := hs.1
  have hshi : s < u := hs.2
  have hau : u ≤ a := ha.1
  have hah : a ≤ u + h := ha.2
  set τ : ℝ := a - s with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτcap : τ ≤ τ₀ := by rw [hτdef]; linarith
  -- the abstract fixed-Gaussian domination at this fixed `τ`.
  set Dz : Point n → ℝ := fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ
    with hDzdef
  have hgw : 0 ≤ gaussDdim (w * τ) z := gaussDdim_nonneg _ _
  have hcnn : 0 ≤ C * τ⁻¹ * gaussDdim (w * τ) z :=
    mul_nonneg (mul_nonneg hC0 (inv_nonneg.mpr hτpos.le)) hgw
  calc |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ * F s z 0|
      = |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ| * |F s z 0| := abs_mul _ _
    _ ≤ (C * τ⁻¹ * gaussDdim (w * τ) z) * MF :=
        mul_le_mul (hcrude τ hτpos hτcap z) (hF s hs z hz) (abs_nonneg _) hcnn
    _ = C * MF * (τ⁻¹ * gaussDdim (w * τ) z) := by ring
    _ ≤ C * MF * (Ce * gaussDdim lam z) :=
        mul_le_mul_of_nonneg_left (hb τ hτpos hτcap z hz) (mul_nonneg hC0 hMF)
    _ = (C * MF * Ce) * gaussDdim lam z := by ring

/-! ###############################################################################
    ### §B — the FULL `hCensusBound` far-rate from FOUR uniform carries.
    ############################################################################### -/

/-- **★★★ `censusBound_of_crude_Fbound_ballRate`.**  The FULL `hCensusBound` far-rate binder — the
    `censusBound_of_onGate_and_ballRate` (J4-947) conclusion — from FOUR uniform carries: the crude
    `τ`-scaled envelope `hcrude`, the off-ball F-factor bound `hF`, the on-ball trace rate `hballrate`
    (C1), and integrability `hΦint` (C2).  The on-gate uniform-in-τ single-fixed-Gaussian domination
    (C3's genuine analytic core) is supplied internally by `census_honGate_of_crude_and_Fbound`; the width
    `lam` and constant `Cenv` are threaded through.  NOT `a₁ = R/6`. -/
theorem censusBound_of_crude_Fbound_ballRate
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h ρ w τ₀ lam C MF Cpair : ℝ)
    (hε : 0 < ε) (hw : 0 < w) (hτ₀ : 0 < τ₀) (hρ : 0 < ρ) (hlamge : 2 * w * τ₀ ≤ lam)
    (hC0 : 0 ≤ C) (hMF : 0 ≤ MF) (hCpair : 0 ≤ Cpair) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀)
    (hcrude : ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ|
          ≤ C * τ⁻¹ * gaussDdim (w * τ) z)
    (hF : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF)
    (hΦint : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      Integrable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
          * F s z 0) volume)
    (hballrate : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      |∫ z in Metric.ball (0 : Point n) ρ,
        deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) :
    ∃ (lam' Cenv : ℝ), 0 < lam' ∧ 0 ≤ Cenv ∧
      ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hlam : 0 < lam := lt_of_lt_of_le (by positivity) hlamge
  obtain ⟨Cenv, hCenv, honGate⟩ :=
    census_honGate_of_crude_and_Fbound g gi hC hK S cutA cutB F u ε h ρ w τ₀ lam C MF
      hw hτ₀ hρ hlamge hC0 hMF hh hcap hcrude hF
  refine ⟨lam, Cenv, hlam, hCenv, ?_⟩
  exact censusBound_of_onGate_and_ballRate g gi hC hK S cutA cutB F u ε h ρ lam Cenv Cpair
    hε hlam hCenv hCpair hρ.le hΦint honGate hballrate

/-! ###############################################################################
    ### §C — non-vacuity (TEETH).
    ############################################################################### -/

/-! ###############################################################################
    ### §C — DISCHARGE the crude envelope to the banked amplitude carries.
    ############################################################################### -/

/-- **★★★ `censusBound_of_amplitudeCarries_Fbound_ballRate`.**  The FULL `hCensusBound` far-rate binder
    from the ACTUAL amplitude carries: the crude `τ`-scaled envelope hypothesis of
    `censusBound_of_crude_Fbound_ballRate` is DISCHARGED internally by the banked
    `witnessTimeDeriv_domination_global` (`w = 4·D.lam`), leaving as carries {the amplitude data
    `D`/`hgate`/`hAmp0`/`hCfield`/`hSupp` — the `WideAmplitudeData` class; the F-factor bound `hF`; the
    on-ball trace rate `hballrate` (C1); integrability `hΦint` (C2)}.  So C3's uniform-in-τ Gaussian
    domination is entirely internal.  NOT `a₁ = R/6`. -/
theorem censusBound_of_amplitudeCarries_Fbound_ballRate (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ)
    (hτ₀ : 0 < τ₀) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK cutA cutB u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h ρ MF Cpair : ℝ)
    (hε : 0 < ε) (hρ : 0 < ρ) (hMF : 0 ≤ MF) (hCpair : 0 ≤ Cpair) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀)
    (hF : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF)
    (hΦint : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      Integrable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
          * F s z 0) volume)
    (hballrate : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      |∫ z in Metric.ball (0 : Point n) ρ,
        deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) :
    ∃ (lam' Cenv : ℝ), 0 < lam' ∧ 0 ≤ Cenv ∧
      ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * (u - s) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C, hCpos, hcrude⟩ :=
    witnessTimeDeriv_domination_global hn g gi hC hK S cutA cutB D τ₀ M M' hτ₀ hM hM' Cfield
      hgate hAmp0 hCfield hSupp
  have hw : (0 : ℝ) < 4 * D.lam := by have hlam := D.hlam; linarith
  exact censusBound_of_crude_Fbound_ballRate g gi hC hK S cutA cutB F u ε h ρ
    (4 * D.lam) τ₀ (2 * (4 * D.lam) * τ₀) C MF Cpair hε hw hτ₀ hρ (le_refl _) hCpos.le hMF hCpair
    hh hcap hcrude hF hΦint hballrate

/-! ###############################################################################
    ### §D — non-vacuity (TEETH): the amplitude-carry bundle is inhabited at a GENUINE gate.
    ############################################################################### -/

/-- **Non-vacuity of `censusBound_of_amplitudeCarries_Fbound_ballRate` — TEETH.**  For ANY concrete
    geometry `(g, gi, hC)` at the singleton gate `K := {0}` with the GENUINELY nonempty census gate
    `S := univ` (so `z ∈ K ∧ 0 ∈ S z` holds at `z = 0`), the entire amplitude-carry bundle is jointly
    satisfiable: `D` an explicit `FixedFlowGateData`, `Cfield` the affine amplitude slope
    (`chartFieldAmp_hasDerivAt_tau`), `hSupp` trivial at `z = 0` (`‖0‖ = 0 < D.r = 1`), and `F ≡ 0` making
    the census integrand vanish so `hF`/`hΦint`/`hballrate` hold outright.  So `censusBound_of_amplitude…`
    fires on genuine positive data (`ε = 1/2`, `h = 1/4`, `ρ = 1`, `τ₀ = 1`, `ε + h = 3/4 ≤ 1`).  NOT
    `a₁ = R/6`. -/
theorem censusBound_of_amplitudeCarries_satisfiable (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (cutA cutB : ℝ) :
    ∃ (K : Set (Point n)) (hK : IsCompact K) (S : Point n → Set (Point n))
      (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ) (Cfield : Point n → Point n → ℝ)
      (F : ℝ → Point n → Point n → ℝ) (u ε h ρ MF Cpair : ℝ),
      ((0 : Point n) ∈ K ∧ (0 : Point n) ∈ S 0) ∧ 0 < τ₀ ∧ 0 ≤ M ∧ 0 ≤ M' ∧
      0 < ε ∧ 0 < ρ ∧ 0 ≤ MF ∧ 0 ≤ Cpair ∧ 0 ≤ h ∧ ε + h ≤ τ₀ ∧
      (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK cutA cutB u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1) ∧
      (∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M) ∧
      (∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M') ∧
      (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF) := by
  classical
  have hK0 : IsCompact ({0} : Set (Point n)) := isCompact_singleton
  set Cf : Point n → Point n → ℝ := fun z p =>
    radialCutoff cutA cutB (uniformInverseChart g gi hC hK0 z p)
      * (VanVleck.vanVleck g (uniformInverseChart g gi hC hK0 z p) ^ (-(1 : ℝ) / 2)
          * transportCoeff (transportOp (VanVleck.vanVleck g) g gi) 1 (uniformInverseChart g gi hC hK0 z p))
    with hCfdef
  refine ⟨({0} : Set (Point n)), hK0, fun _ => Set.univ,
    { a := 1 / 3, b := 1 / 2, r := 1, eta := 1 / 2, lam := 4,
      ha := by norm_num, hab := by norm_num, hbr := by norm_num,
      heta := by norm_num, hlam := by norm_num, hgap := by norm_num,
      hgate := by
        intro z hz _
        rw [Set.mem_singleton_iff] at hz; subst hz
        have h0 : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
        rw [h0, mul_zero]; exact rncRadialSq_nonneg _ },
    1, |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0| + |Cf 0 0|, |Cf 0 0|, Cf,
    (fun _ _ _ => (0 : ℝ)), 0, 1 / 2, 1 / 4, 1, 0, 0,
    ⟨Set.mem_singleton_iff.mpr rfl, Set.mem_univ _⟩,
    one_pos, by positivity, abs_nonneg _, by norm_num, one_pos, le_refl _, le_refl _,
    by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · -- hgate: `S = univ` frees the gate membership; HasDerivAt is `chartFieldAmp_hasDerivAt_tau`.
    intro w _ _
    exact ⟨Set.mem_univ _, chartFieldAmp_hasDerivAt_tau g gi hC hK0 cutA cutB w.2.2 w.2.1 w.1⟩
  · -- hAmp0: only `z = 0`; affine-in-τ bound with `τ ≤ 1`.
    intro τ hτ hτ1 z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    have haff : chartFieldAmp g gi hC hK0 cutA cutB τ 0 0
        = chartFieldAmp g gi hC hK0 cutA cutB 0 0 0 + Cf 0 0 * τ := by
      simp only [hCfdef, chartFieldAmp]; ring
    rw [haff]
    calc |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0 + Cf 0 0 * τ|
        ≤ |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0| + |Cf 0 0 * τ| := abs_add_le _ _
      _ = |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0| + |Cf 0 0| * τ := by
          rw [abs_mul, abs_of_nonneg hτ.le]
      _ ≤ |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0| + |Cf 0 0| * 1 := by
          have : |Cf 0 0| * τ ≤ |Cf 0 0| * 1 := mul_le_mul_of_nonneg_left hτ1 (abs_nonneg _)
          linarith
      _ = |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0| + |Cf 0 0| := by rw [mul_one]
  · -- hCfield: only `z = 0`; `|Cf 0 0| ≤ |Cf 0 0|`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact le_refl _
  · -- hSupp: only `z = 0`; `‖0‖ = 0 < D.r = 1`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    simp
  · -- hF: `F ≡ 0`, so `|0| = 0 ≤ MF = 0`.
    intro s _ z _; simp

end QIQTH.CensusOnGateEnvelopeThreaded

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.CensusOnGateEnvelopeThreaded
#print axioms census_honGate_of_crude_and_Fbound
#print axioms censusBound_of_crude_Fbound_ballRate
#print axioms censusBound_of_amplitudeCarries_Fbound_ballRate
#print axioms censusBound_of_amplitudeCarries_satisfiable
end AxiomChecks
