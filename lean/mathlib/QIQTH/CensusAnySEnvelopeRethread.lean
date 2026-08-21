/-
  CensusAnySEnvelopeRethread — J4-951: RE-THREAD the live census consumers off the OLD crude-envelope
  supplier `WitnessTimeDerivEnvelope.witnessTimeDeriv_domination_global` (which carries the OVER-STRONG
  `hgate`/`S=univ`-forcing gate half) onto the STRICTLY-MORE-GENERAL any-`S` envelope
  `CensusTauDerivAnySEnvelope.witnessTimeDeriv_domination_global_anyS` (J4-950), ELIMINATING the S=univ
  carry from the FULL chain up to the `hCensusBound` far-rate assembly.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  supplier-substitution / structural re-threading brick.  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis (satisfiability EXHIBITED below), none equal to the conclusion, no
  existing banked file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS ELIMINATES.  The OLD supplier `witnessTimeDeriv_domination_global` requires, alongside the
  amplitude data, the gate hypothesis
      `hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 ∧ HasDerivAt …`
  whose FIRST conjunct universally quantifies the FIELD point `w.2.1` over ALL of `Point n` — forcing
  `S q = univ` for every `q ∈ K` (the quantifier-order over-statement audited at J4-231/232 and re-flagged
  at J4-949).  The any-`S` supplier `witnessTimeDeriv_domination_global_anyS` (J4-950) proves the IDENTICAL
  conclusion
      `∃ C, 0 < C ∧ ∀ τ, 0<τ → τ≤τ₀ → ∀ z, |deriv (fun r ↦ Wit r 0 z) τ| ≤ C·τ⁻¹·gaussDdim (4·D.lam·τ) z`
  carrying ONLY `{hAmp0, hCfield (on `censusAmpTauDeriv`), hSupp}` — NO `hgate`, NO `Cfield` field, for ANY
  `S`.  Because the conclusion is byte-for-byte the same, it is a genuine drop-in.

  ## WHAT LANDS (each a strict weakening of an already-banked consumer — same conclusion, `hgate`/`Cfield`
  DROPPED, `hCfield` rephrased onto the banked `censusAmpTauDeriv` slope).
    • `censusBound_of_amplitudeCarries_Fbound_ballRate_anyS` — the FULL `hCensusBound` far-rate binder
        (J4-948's conclusion) with the crude envelope supplied INTERNALLY by the any-`S` supplier: no
        `hgate`, no `Cfield`.
    • `censusBound_of_geometry_gate_supp_F_ballRate_anyS` — the MOST-DISCHARGED capstone (J4-949's
        conclusion) with `hAmp0`/`hCfield` discharged internally (`census_amplitude_supBounds`) AND the
        over-strong `hgateS` GATE HALF **entirely REMOVED** from the binder.  This is the concrete
        elimination of the S=univ carry at the census-assembly boundary.
    • `witnessBoundD_wired_anyS`, `witnessHpardiff_wired_anyS` — the `boundD` (J4-911) and `hpardiff`
        (J4-912/916) census consumers re-wired onto the any-`S` supplier: no `hgate`, no `Cfield`.
    • non-vacuity witnesses (`…_satisfiable`) for the re-threaded bundles (genuine positive data,
        `K = {0}`, `F ≡ 0`) + the inner-`∀D`-binder non-vacuity via the banked `census_smallRadius_gate_exists`.

  ## HONEST STATUS.  The over-strong `hgate`/`S=univ` carry is ELIMINATED from the live census-assembly
  chain: `hCensusBound`'s far-rate is now assembled with NO S-membership gate on the field point.  The
  MATHEMATICAL residue is unchanged — it is a pure re-plumbing.  After this cleanup, `hCensusBound` depends
  (for the fully-discharged capstone `censusBound_of_geometry_gate_supp_F_ballRate_anyS`) on
    { standard geometry {hg, hg0, hu, h0Kmem}, a small-radius gate record `D` (`D.r ≤ rAmp`), the honest
      support fact `hSupp` (`0 ∈ S z ⟹ ‖z‖ < D.r`), the off-ball F-factor bound `hF`, C1 on-ball trace
      rate `hballrate`, C2 integrability `hΦint` } — and NO LONGER on any `S=univ`/`hgate` gate carry.
  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusTauDerivAnySEnvelope
import QIQTH.CensusOnGateEnvelopeThreaded
import QIQTH.CensusAmplitudeSupDischarge
import QIQTH.WitnessBoundDHpardiffWired

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.InverseChartNormalJets QIQTH.OnGateJets
open QIQTH.GatedTauDerivRep
open QIQTH.CensusTauDerivGateSplit QIQTH.CensusAmpConcreteRegularity
open QIQTH.CensusOffBallEnvelope QIQTH.CensusOnGateFixedGaussEnvelope
open QIQTH.CensusOnGateEnvelopeThreaded
open QIQTH.WitnessTimeDerivEnvelope QIQTH.CensusTauDerivAnySEnvelope
open QIQTH.CensusAmplitudeSupDischarge
open QIQTH.DerivDomLowerCapped QIQTH.HZDataFromCrudeEnv QIQTH.HpardiffZTimeDeriv
open QIQTH.WitnessBoundDHpardiffWired
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CensusAnySEnvelopeRethread

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the FULL far-rate binder, crude envelope supplied by the ANY-`S` supplier (no `hgate`).
    ############################################################################### -/

/-- **★★★ `censusBound_of_amplitudeCarries_Fbound_ballRate_anyS`.**  The FULL `hCensusBound` far-rate binder
    (the `censusBound_of_onGate_and_ballRate` / J4-947 conclusion), re-threaded so the crude `τ`-scaled
    envelope is discharged INTERNALLY by the any-`S` supplier `witnessTimeDeriv_domination_global_anyS`
    (J4-950).  Strictly weaker than the banked `censusBound_of_amplitudeCarries_Fbound_ballRate` (J4-948):
    the over-strong `hgate` and the `Cfield` field are DROPPED, and `hCfield` is rephrased onto the banked
    `censusAmpTauDeriv` slope.  Remaining carries: {amplitude sups `hAmp0`/`hCfield`, `hSupp`, F-factor
    bound `hF`, on-ball trace rate `hballrate` (C1), integrability `hΦint` (C2)} — with NO S-membership
    gate.  NOT `a₁ = R/6`. -/
theorem censusBound_of_amplitudeCarries_Fbound_ballRate_anyS (hn : 0 < n)
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
    witnessTimeDeriv_domination_global_anyS hn g gi hC hK S cutA cutB D τ₀ M M'
      hτ₀ hM hM' hAmp0 hCfield hSupp
  have hw : (0 : ℝ) < 4 * D.lam := by have hlam := D.hlam; linarith
  exact censusBound_of_crude_Fbound_ballRate g gi hC hK S cutA cutB F u ε h ρ
    (4 * D.lam) τ₀ (2 * (4 * D.lam) * τ₀) C MF Cpair hε hw hτ₀ hρ (le_refl _) hCpos.le hMF hCpair
    hh hcap hcrude hF hΦint hballrate

/-! ###############################################################################
    ### §B — the MOST-DISCHARGED capstone, `hgateS` GATE HALF **removed** entirely.
    ############################################################################### -/

/-- **★★★ `censusBound_of_geometry_gate_supp_F_ballRate_anyS`.**  The FULL `hCensusBound` far-rate binder
    (the `censusBound_of_onGate_and_ballRate` / J4-947 conclusion) from the standard geometry carries, with
    the amplitude sup-bounds `hAmp0`/`hCfield` discharged internally (`census_amplitude_supBounds`) AND the
    over-strong `hgateS` GATE HALF **entirely REMOVED** — the concrete elimination of the S=univ carry at
    the census-assembly boundary.  Strictly weaker than the banked `censusBound_of_geometry_gate_supp_F_ballRate`
    (J4-949): its `(∀ w, w.2.2∈K → 0<w.1 → w.2.1 ∈ S w.2.2)` hypothesis is GONE.  The caller supplies, for
    ANY fixed gate record `D` with `D.r ≤ rAmp`, only the support fact `hSupp`, integrability `hΦint` (C2),
    and the on-ball trace rate `hballrate` (C1).  NOT `a₁ = R/6`. -/
theorem censusBound_of_geometry_gate_supp_F_ballRate_anyS (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h ρ τ₀ MF Cpair : ℝ)
    (hε : 0 < ε) (hτ₀ : 0 < τ₀) (hρ : 0 < ρ) (hMF : 0 ≤ MF) (hCpair : 0 ≤ Cpair)
    (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀)
    (hF : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF) :
    ∃ rAmp : ℝ, 0 < rAmp ∧
      ∀ D : FixedFlowGateData g gi hC hK, D.r ≤ rAmp →
        (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) →
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
  intro D hDr hSupp hΦint hballrate
  -- `hAmp0` from the package (radius monotonicity `‖z‖ < D.r ≤ rAmp`).
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
    ### §C — the `boundD` (J4-911) and `hpardiff` (J4-912/916) consumers re-wired (no `hgate`).
    ############################################################################### -/

/-- **★★★ `witnessBoundD_wired_anyS`.**  The C3ε parameter-derivative dominator `boundD`, re-wired onto the
    any-`S` supplier `witnessTimeDeriv_domination_global_anyS` (J4-950) at the global cap `T + 1`.  Strictly
    weaker than the banked `witnessBoundD_wired` (J4-918): the over-strong `hgate` and the `Cfield` field are
    DROPPED, and `hCfield` is rephrased onto `censusAmpTauDeriv`.  NOT `a₁ = R/6`. -/
theorem witnessBoundD_wired_anyS (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (M M' C_L : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hC_L : 0 ≤ C_L)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ T + 1 → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hFdom : ∀ s, 0 < s → s ≤ T + 1 → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∃ boundD : ℕ → ℝ → ℝ → ℝ,
      (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m)) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ derivDomNb m u,
        ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0‖
          ≤ boundD m u s) := by
  obtain ⟨Cwit, hCwitpos, hbound⟩ :=
    witnessTimeDeriv_domination_global_anyS hn g gi hC hK S a b D (T + 1) M M'
      (by linarith) hM hM' hAmp0 hCfield hSupp
  have hlampos : 0 < D.lam := lt_trans one_pos D.hlam
  refine derivDom_boundD_of_crude
      (fun τ _ z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) τ)
      F U (fun _ _ => Cwit) (fun _ _ => 4 * D.lam) (fun _ _ => C_L) (fun _ _ => 2)
      (fun _ _ _ => hCwitpos.le) (fun _ _ _ => by show (0:ℝ) < 4 * D.lam; linarith)
      (fun _ _ _ => hC_L) (fun _ _ _ => two_pos)
      (fun s hs z => hFzero s hs z 0) ?_ ?_
  · -- hAcrude: the crude time-derivative envelope, from the global any-`S` domination.
    intro m u hu τ hτ hτcap z
    have hτcap' : τ ≤ T + 1 :=
      le_trans hτcap (by have := hUT u hu; have := epsSeq_le_one m; linarith)
    have hb := hbound τ hτ hτcap' z
    rw [← gaussDdim_zero_sub (4 * D.lam * τ) z] at hb
    exact hb
  · -- hFdom: the widened Levi envelope, centred at `0`.
    intro m u hu s hs hscap z
    have hscap' : s ≤ T + 1 :=
      le_trans hscap (by have := hUT u hu; have := epsSeq_le_one m; linarith)
    have h := hFdom s hs hscap' z 0
    simpa only [sub_zero] using h

/-- **★★★ `witnessHpardiff_wired_anyS`.**  The parametric `hpardiff` census binder, re-wired onto the
    any-`S` supplier `witnessTimeDeriv_domination_global_anyS` (J4-950) at the global cap `T + 1`.  Strictly
    weaker than the banked `witnessHpardiff_wired` (J4-918): the over-strong `hgate` and the `Cfield` field
    are DROPPED, and `hCfield` is rephrased onto `censusAmpTauDeriv`.  NOT `a₁ = R/6`. -/
theorem witnessHpardiff_wired_anyS (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (M M' C_L : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hC_L : 0 ≤ C_L)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ T + 1 → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hFdom : ∀ s, 0 < s → s ≤ T + 1 → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAmeas : ∀ (s u' : ℝ), AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (u' - s) 0 z * F s z 0) volume)
    (hDmeas : ∀ (s c : ℝ), AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0) volume)
    (hbase : ∀ (s c : ℝ), Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0) volume) :
    ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ derivDomNb m u,
      HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0) c := by
  obtain ⟨Cwit, hCwitpos, hbound⟩ :=
    witnessTimeDeriv_domination_global_anyS hn g gi hC hK S a b D (T + 1) M M'
      (by linarith) hM hM' hAmp0 hCfield hSupp
  have hlampos : 0 < D.lam := lt_trans one_pos D.hlam
  refine hpardiff_of_zTimeDeriv (vanVleckGatedWitness g gi hC hK S a b) F U derivDomNb hAmeas ?_
  intro m u hu
  refine ae_of_all _ (fun s hsmem c hc => ?_)
  have he : 0 < epsSeq m := epsSeq_pos m
  rcases le_or_gt s 0 with hs0 | hs0
  · -- `s ≤ 0`: the Levi source vanishes; the inner existential is trivial.
    refine ⟨Set.univ, Filter.univ_mem, (fun _ => 0), integrable_zero _ _ _, ?_, ?_, ?_, ?_⟩
    · have hz : (fun z => vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0)
          = fun _ => (0 : ℝ) := by funext z; rw [hFzero s hs0 z 0, mul_zero]
      rw [hz]; exact integrable_zero _ _ _
    · have hz : (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s)
            * F s z 0) = fun _ => (0 : ℝ) := by funext z; rw [hFzero s hs0 z 0, mul_zero]
      rw [hz]; exact aestronglyMeasurable_const
    · refine ae_of_all _ (fun z c' _ => ?_)
      simp [hFzero s hs0 z 0]
    · refine ae_of_all _ (fun z c' _ => ?_)
      simp only [hFzero s hs0 z 0, mul_zero]
      exact hasDerivAt_const c' (0 : ℝ)
  · -- `s > 0`: the genuine window `[εₘ/2, u+εₘ]` — fire `witnessHZslice_of_crudeEnv`.
    have hub : s ∈ Set.Ioc (min 0 (u - epsSeq m)) (max 0 (u - epsSeq m)) := hsmem
    have hsmax : s ≤ max 0 (u - epsSeq m) := hub.2
    have hue : 0 < u - epsSeq m := by
      by_contra h
      push_neg at h
      rw [max_eq_left h] at hsmax
      exact absurd (lt_of_lt_of_le hs0 hsmax) (lt_irrefl 0)
    have hsue : s ≤ u - epsSeq m := by rwa [max_eq_right hue.le] at hsmax
    have hcu : |c - u| < epsSeq m / 2 := by
      have hcb : c ∈ Metric.ball u (epsSeq m / 2) := hc
      rwa [Metric.mem_ball, Real.dist_eq] at hcb
    have hcuL : u - epsSeq m / 2 < c := by have := (abs_lt.mp hcu).1; linarith
    have hcuU : c < u + epsSeq m / 2 := by have := (abs_lt.mp hcu).2; linarith
    have hlo : epsSeq m / 2 < c - s := by linarith
    have hhi : c - s < u + epsSeq m := by linarith
    refine witnessHZslice_of_crudeEnv g gi hC hK S a b F s c
      (epsSeq m / 2) (u + epsSeq m) Cwit (4 * D.lam) C_L 2
      (by linarith) (by linarith) hCwitpos.le hC_L two_pos hs0 hlo hhi ?_ ?_
      (hDmeas s c) (hbase s c)
    · intro z τ hτmem
      have hτpos : 0 < τ := lt_of_lt_of_le (by linarith) hτmem.1
      have hτcap : τ ≤ T + 1 :=
        le_trans hτmem.2 (by have := hUT u hu; have := epsSeq_le_one m; linarith)
      have hb := hbound τ hτpos hτcap z
      rw [← gaussDdim_zero_sub (4 * D.lam * τ) z] at hb
      exact hb
    · intro z
      have hsc : s ≤ T + 1 :=
        le_trans hsue (by have := hUT u hu; have := epsSeq_le_one m; linarith)
      have h := hFdom s hs0 hsc z 0
      simpa only [sub_zero] using h

/-! ###############################################################################
    ### §D — NON-VACUITY (TEETH) for the re-threaded bundles.
    ############################################################################### -/

/-- **Non-vacuity of `censusBound_of_amplitudeCarries_Fbound_ballRate_anyS` — TEETH.**  For ANY concrete
    geometry `(g, gi, hC)` at the singleton gate `K := {0}` with the genuinely-nonempty census gate
    `S := univ` (so `z ∈ K ∧ 0 ∈ S z` at `z = 0`), the re-threaded carry bundle {`hAmp0`, `hCfield`
    (on `censusAmpTauDeriv`), `hSupp`, `hF`} is jointly satisfiable: an explicit `FixedFlowGateData` `D`,
    the amplitude sups from the AFFINE-in-`τ` structure at `0`, `hSupp` trivial (`‖0‖ = 0 < D.r = 1`), and
    `F ≡ 0`.  The over-strong `hgate` is GONE.  NOT `a₁ = R/6`. -/
theorem censusBound_of_amplitudeCarries_Fbound_ballRate_anyS_satisfiable (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (cutA cutB : ℝ) :
    ∃ (K : Set (Point n)) (hK : IsCompact K) (S : Point n → Set (Point n))
      (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ)
      (F : ℝ → Point n → Point n → ℝ) (u ε h ρ MF Cpair : ℝ),
      ((0 : Point n) ∈ K ∧ (0 : Point n) ∈ S 0) ∧ 0 < τ₀ ∧ 0 ≤ M ∧ 0 ≤ M' ∧
      0 < ε ∧ 0 < ρ ∧ 0 ≤ MF ∧ 0 ≤ Cpair ∧ 0 ≤ h ∧ ε + h ≤ τ₀ ∧
      (∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M) ∧
      (∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M') ∧
      (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF) := by
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
    1, |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0| + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0|,
    |censusAmpTauDeriv g gi hC hK0 cutA cutB 0|,
    (fun _ _ _ => (0 : ℝ)), 0, 1 / 2, 1 / 4, 1, 0, 0,
    ⟨Set.mem_singleton_iff.mpr rfl, Set.mem_univ _⟩,
    one_pos, by positivity, abs_nonneg _, by norm_num, one_pos, le_refl _, le_refl _,
    by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · -- hAmp0: only `z = 0`; affine-in-τ bound with `τ ≤ 1`.
    intro τ hτ hτ1 z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    rw [chartFieldAmp_affine_slope]
    calc |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0 + censusAmpTauDeriv g gi hC hK0 cutA cutB 0 * τ|
        ≤ |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0 * τ| := abs_add_le _ _
      _ = |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| * τ := by
          rw [abs_mul, abs_of_nonneg hτ.le]
      _ ≤ |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| * 1 := by
          have : |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| * τ
              ≤ |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| * 1 :=
            mul_le_mul_of_nonneg_left hτ1 (abs_nonneg _)
          linarith
      _ = |chartFieldAmp g gi hC hK0 cutA cutB 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 cutA cutB 0| := by rw [mul_one]
  · -- hCfield: only `z = 0`; `|·| ≤ |·|`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact le_refl _
  · -- hSupp: only `z = 0`; `‖0‖ = 0 < D.r = 1`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    show ‖(0 : Point n)‖ < 1
    rw [norm_zero]; exact one_pos
  · -- hF: `F ≡ 0`, so `|0| = 0 ≤ MF = 0`.
    intro s _ z _; simp

/-- **Non-vacuity of `witnessHpardiff_wired_anyS` — TEETH** (SUBSUMES the `witnessBoundD_wired_anyS`
    bundle).  For ANY concrete geometry `(g, gi, hC)` at the singleton gate `K := {0}` with `S := univ`,
    the FULL re-threaded bundle {`hAmp0`, `hCfield` (on `censusAmpTauDeriv`), `hSupp`, `hFzero`, `hFdom`,
    `hAmeas`, `hDmeas`, `hbase`} is jointly satisfiable — `F ≡ 0` (`C_L := 0`), `U := Icc 0 1` (`T := 1`),
    an explicit gate record `D`, amplitude sups from the AFFINE-in-`τ` structure at `0` up to the cap
    `τ ≤ T + 1 = 2`.  The over-strong `hgate` is GONE.  NOT `a₁ = R/6`. -/
theorem witnessHpardiff_wired_anyS_hyp_satisfiable (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (a b : ℝ) :
    ∃ (K : Set (Point n)) (hK : IsCompact K) (S : Point n → Set (Point n))
      (D : FixedFlowGateData g gi hC hK) (F : ℝ → Point n → Point n → ℝ)
      (T : ℝ) (U : Set ℝ) (M M' C_L : ℝ),
      (0 : Point n) ∈ K ∧ 0 < T ∧ (∀ u ∈ U, u ≤ T) ∧ 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ C_L ∧
      (∀ τ, 0 < τ → τ ≤ T + 1 → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M) ∧
      (∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M') ∧
      (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) ∧
      (∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0) ∧
      (∀ s, 0 < s → s ≤ T + 1 → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) ∧
      (∀ (s u' : ℝ), AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (u' - s) 0 z * F s z 0) volume) ∧
      (∀ (s c : ℝ), AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0)
        volume) ∧
      (∀ (s c : ℝ), Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0) volume) := by
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
    (fun _ _ _ => 0), 1, Set.Icc 0 1,
    |chartFieldAmp g gi hC hK0 a b 0 0 0| + |censusAmpTauDeriv g gi hC hK0 a b 0| * 2,
    |censusAmpTauDeriv g gi hC hK0 a b 0|, 0,
    Set.mem_singleton_iff.mpr rfl, one_pos, (fun u hu => hu.2),
    by positivity, abs_nonneg _, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hAmp0: only `z = 0`; affine-in-τ bound up to the cap `τ ≤ 2`.
    intro τ hτ hτ2 z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    rw [chartFieldAmp_affine_slope]
    have hτ2' : τ ≤ 2 := by linarith
    calc |chartFieldAmp g gi hC hK0 a b 0 0 0 + censusAmpTauDeriv g gi hC hK0 a b 0 * τ|
        ≤ |chartFieldAmp g gi hC hK0 a b 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 a b 0 * τ| := abs_add_le _ _
      _ = |chartFieldAmp g gi hC hK0 a b 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 a b 0| * τ := by
          rw [abs_mul, abs_of_nonneg hτ.le]
      _ ≤ |chartFieldAmp g gi hC hK0 a b 0 0 0|
            + |censusAmpTauDeriv g gi hC hK0 a b 0| * 2 := by
          have : |censusAmpTauDeriv g gi hC hK0 a b 0| * τ
              ≤ |censusAmpTauDeriv g gi hC hK0 a b 0| * 2 :=
            mul_le_mul_of_nonneg_left hτ2' (abs_nonneg _)
          linarith
  · -- hCfield: only `z = 0`; `|·| ≤ |·|`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact le_refl _
  · -- hSupp: only `z = 0`; `‖0‖ = 0 < 1`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    simp
  · -- hFzero: `F ≡ 0`.
    intro s _ z y; rfl
  · -- hFdom: `|0| ≤ 0 * gaussDdim …`.
    intro s _ _ z y; simp
  · -- hAmeas: `F ≡ 0`, so the integrand is `0`.
    intro s u'; simp only [mul_zero]; exact aestronglyMeasurable_const
  · -- hDmeas: same.
    intro s c; simp only [mul_zero]; exact aestronglyMeasurable_const
  · -- hbase: same.
    intro s c; simp only [mul_zero]; exact integrable_zero _ _ _

/-- **Non-vacuity of the capstone's inner `∀ D, D.r ≤ rAmp → …` binder** — valid small-radius gate records
    always exist (the banked `census_smallRadius_gate_exists`, re-exported here so
    `censusBound_of_geometry_gate_supp_F_ballRate_anyS` is certifiably NOT vacuously quantified over `D`).
    NOT `a₁ = R/6`. -/
theorem census_anyS_smallRadius_gate_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (target : ℝ) (htarget : 0 < target) :
    ∃ D : FixedFlowGateData g gi hC hK, 0 < D.r ∧ D.r ≤ target :=
  census_smallRadius_gate_exists g gi hC hK target htarget

end QIQTH.CensusAnySEnvelopeRethread

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusAnySEnvelopeRethread
#print axioms censusBound_of_amplitudeCarries_Fbound_ballRate_anyS
#print axioms censusBound_of_geometry_gate_supp_F_ballRate_anyS
#print axioms witnessBoundD_wired_anyS
#print axioms witnessHpardiff_wired_anyS
#print axioms censusBound_of_amplitudeCarries_Fbound_ballRate_anyS_satisfiable
#print axioms witnessHpardiff_wired_anyS_hyp_satisfiable
#print axioms census_anyS_smallRadius_gate_exists
end AxiomChecks
