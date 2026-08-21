/-
  HFarFullyWired — the FULL end-to-end composition of this session's H_far decomposition chain:
  simultaneously instantiate J4-971's `hfar_concrete_from_amplitude` (the live `H_far` far-envelope for
  the concrete census convolution) with the THREE carrier-reducers J4-972/973 discharging its two
  remaining honest F-side carriers `hFmeasG`, `hRint` at a SINGLE shared instantiation:
    • `hRint`   ⟵ `hRint_of_hEnv` (J4-972), from the SAME window engine bundle `hEnv` (+ `hFmeasG`);
    • `hFmeasG` ⟵ `hFmeasG_of_field_slice` (J4-973), from `{hKm, hSm0, hIn}` (banked witness-side infra)
      + the pure F-slice measurability `hFslice`;
    • `hEnv`    ⟵ `hEnv_window_of_amplitudeAndFdom` (J4-971), from amplitude sups + F-side carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE / carrier-composition brick.  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## WHAT THIS COMPOSES.  After J4-970/971/972/973 the concrete `H_far` far-envelope
  (`hfar_concrete_from_amplitude`, J4-971) carried, beyond the amplitude sups `{hAmp0, hCfield, hSupp}`
  and the F-side data `{hFdom, hmeas, hbase}`, TWO remaining honest F-side carriers `hFmeasG`, `hRint`
  plus the rate `hrate`.  This file wires those two carriers to their J4-972/973 reducers at ONE shared
  parameter set:
    - `hFmeasG` is supplied by `hFmeasG_of_field_slice` (J4-973) from the banked witness-side
      measurability infra `{hKm, hSm0, hIn}` + the pure F-slice carry `hFslice`;
    - `hRint` is supplied by `hRint_of_hEnv` (J4-972) from the window engine bundle `hEnv` (itself built
      by `hEnv_window_of_amplitudeAndFdom`, J4-971) + the just-built `hFmeasG`.
  The composition typechecks as ONE term (verified by literal build): the output type of each reducer is
  the LITERAL input type of the next consumer (`hFmeasG` : `∀ s u', AEStronglyMeasurable (witness·F)`;
  `hRint` : `∀ s, IntervalIntegrable (∫ z, ∂_τ witness · F)`) — no coercion, no restatement.

  ## THE TRANSITIVE CARRIER SURFACE (NOT proven minimal).  The fully-wired concrete `H_far` far-envelope
  `hfar_concrete_fully_wired` holds from the following carriers — this is the surface induced by the
  current lemma APIs, NOT proven logically minimal (no ablation/redundancy analysis is claimed; e.g. it
  is NOT established here that `hmeas` fails to subsume `hFslice`):
    - geometry/gate scalars + cap `{hε, hh, hCp, hulo, hcap, hM, hM', hCF, hwF}`;
    - amplitude sup-bounds `{hAmp0, hCfield, hSupp}` (the mildest accepted zeroth-amplitude class,
      J4-949/957/958);
    - F-side regularity `{hFdom (G3 F-bound), hmeas, hbase, hFslice}` — genuinely IRREDUCIBLE for an
      unconstrained free field `F`;
    - witness-side measurability infra `{hKm, hSm0, hIn}` — banked;
    - the rate `hrate` (= on-ball `hballrate` mod-G2 (J4-960) + off-ball envelope (J4-969), whose
      SCALAR chart-CoV census inequality is the opaque chart wall consuming `{hDuhamel, hDConv, hCConv}`).
  The `hFmeasG` and `hRint` carriers are NO LONGER free — they are discharged internally.  `H_far` is
  thus reduced to `{amplitude sups, F-side regularity, witness-side infra, hrate}`.

  ## NON-VACUITY POSTURE (honest).  This file introduces NO new abstract lemma — it is a pure
  `have … exact` contraction of four already-teeth'd banked theorems (J4-971/972/973), each of which
  carries its OWN non-vacuity teeth in its source file.  It deliberately does NOT add a joint-
  satisfiability teeth for the composed bundle: per gpt-5.6-sol high adversarial audit (2026-08-22),
  individual teeth do NOT compose (Sat(A) ∧ Sat(B) ⇏ Sat(A∧B)), so JOINT satisfiability of the full
  bundle `{hAmp0,hCfield,hSupp,hFdom,hmeas,hbase,hKm,hSm0,hIn,hFslice,hrate}` at a genuine (n≥2,
  non-flat) curved witness is NOT established here — its status is "unknown compatibility", with `hrate`
  (still importing the unresolved chart-CoV census assumptions `{hDuhamel,hDConv,hCConv}`) the dominant
  unknown.  This is banked STRICTLY as a CONDITIONAL wiring/bookkeeping lemma, NOT as a non-vacuous
  curved-geometry capstone.  No `:= True`, no unsatisfiable-antecedent trap is INTRODUCED by the wiring
  (measurability + bound carriers do not conflict), but joint realizability is NOT claimed proven.

  ## WHAT THIS DOES — AND DOES NOT — DO.  It is the literal one-term assembly certifying that the
  ~4-file H_far decomposition (J4-970→973) composes.  It does NOT discharge `hrate`, the G3 F-bound
  `hFdom`, the F-slice `hFslice`, nor touch the chart-CoV SCALAR census inequality (the opaque chart wall
  inside `hrate`).  It discharges NONE of `{hballrate, hDuhamel, hDConv, hCConv}` as a top-level τ-carry.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HFarEnvFromAmplitude
import QIQTH.HRintFromEngine
import QIQTH.HFmeasGFromFieldSlice

open MeasureTheory Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.InverseChartNormalJets
open QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.HeatKernelA1 QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.WitnessMeasDeriv
open QIQTH.CensusTauDerivGateSplit QIQTH.CensusTauDerivAnySEnvelope
open scoped Interval Topology BigOperators

namespace QIQTH.HFarFullyWired

variable {n : ℕ}

/-! ###############################################################################
    ### THE CAPSTONE COMPOSITION: the concrete `H_far` far-envelope with BOTH `hFmeasG` and `hRint`
    ###   discharged internally, at ONE shared instantiation of the J4-971/972/973 reducers.
    ############################################################################### -/

/-- **★★★ `hfar_concrete_fully_wired` — the live `H_far` far-envelope for the concrete census
    convolution, with the `hFmeasG` and `hRint` carriers BOTH discharged internally.**  Composes, at a
    SINGLE shared parameter set:
      • `hFmeasG_of_field_slice` (J4-973): `hFmeasG` from `{hKm, hSm0, hIn, hFslice}`;
      • `hEnv_window_of_amplitudeAndFdom` (J4-971): `hEnv` from amplitude sups + F-side carries;
      • `hRint_of_hEnv` (J4-972): `hRint` from `{hFmeasG, hEnv}`;
      • `hfar_concrete_from_amplitude` (J4-971): the far-envelope from `{amplitude, F-side, hFmeasG, hRint, hrate}`.
    Produces the exact live `H_far` argument shape
        `∀ s ∈ Ioo(u−ε)u,
           |(∫ z, witness(u+h−s) 0 z·F s z 0) − (∫ z, witness(u−s) 0 z·F s z 0)|
             ≤ Cpair·h·(u−s)^{−1/2}`
    from the transitive carrier surface `{hε, hh, hCp, hulo, hcap, hM, hM', hCF, hwF, hAmp0, hCfield,
    hSupp, hFdom, hmeas, hbase, hKm, hSm0, hIn, hFslice, hrate}` (induced by the lemma APIs, NOT proven
    logically minimal, joint realizability NOT claimed).  NOT `a₁ = R/6`. -/
theorem hfar_concrete_fully_wired (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (u ε h Cpair : ℝ)
    (hε : 0 < ε) (hh : 0 ≤ h) (hCp : 0 ≤ Cpair) (hulo : 0 ≤ u - ε)
    (D : FixedFlowGateData g gi hC hK) (τ₀cap M M' CF wF : ℝ)
    (hcap : 2 * (h + ε) ≤ τ₀cap) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hCF : 0 ≤ CF) (hwF : 0 < wF)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀cap → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (hFdom : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hmeas : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        AEStronglyMeasurable
          (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
            * F s z 0) volume)
    (hbase : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        Integrable
          (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume)
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hIn : ∀ τ : ℝ, AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) cutA cutB
        (uniformInverseChart g gi hC hK) τ (0 : Point n) z)
      (volume : Measure (Point n)))
    (hFslice : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z 0) (volume : Measure (Point n)))
    (hrate : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s) * F s z 0|
          ≤ Cpair * (c - s) ^ (-(1 : ℝ) / 2)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |(∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
          - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)|
        ≤ Cpair * h * (u - s) ^ (-(1 : ℝ) / 2) := by
  -- (1) `hFmeasG` ⟵ J4-973 (`hFmeasG_of_field_slice`) from `{hKm, hSm0, hIn, hFslice}`.
  have hFmeasG := QIQTH.HFmeasGFromFieldSlice.hFmeasG_of_field_slice
    g gi hC hK S cutA cutB F hKm hSm0 hIn hFslice
  -- (2) `hEnv` ⟵ J4-971 (`hEnv_window_of_amplitudeAndFdom`) from amplitude sups + F-side carries.
  have hEnv := QIQTH.HFarEnvFromAmplitude.hEnv_window_of_amplitudeAndFdom hn
    g gi hC hK S cutA cutB F u ε h hε hh hulo D τ₀cap M M' CF wF
    hcap hM hM' hCF hwF hAmp0 hCfield hSupp hFdom hmeas hbase
  -- (3) `hRint` ⟵ J4-972 (`hRint_of_hEnv`) from `{hFmeasG, hEnv}`.
  have hRint := QIQTH.HRintFromEngine.hRint_of_hEnv
    g gi hC hK S cutA cutB F u ε h hh hFmeasG hEnv
  -- (4) compose into the far-envelope via J4-971 (`hfar_concrete_from_amplitude`).
  exact QIQTH.HFarEnvFromAmplitude.hfar_concrete_from_amplitude hn
    g gi hC hK S cutA cutB F u ε h Cpair hε hh hCp hulo D τ₀cap M M' CF wF
    hcap hM hM' hCF hwF hAmp0 hCfield hSupp hFdom hmeas hbase hFmeasG hRint hrate

end QIQTH.HFarFullyWired

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HFarFullyWired
#print axioms hfar_concrete_fully_wired
end AxiomChecks
