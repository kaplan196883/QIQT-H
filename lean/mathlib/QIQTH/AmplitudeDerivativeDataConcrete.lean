/-
  AmplitudeDerivativeDataConcrete — J4-544: discharge the `hEndpoint`/`hAzero` carries of the
  concrete van-Vleck gated witness, and wire the `hGpow` capstone with `hEndpoint` supplied internally.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  discharges the two CHEAP, curvature-INDEPENDENT (measure-zero endpoint) carries that the
  `MemAdjHiMomentBound.hGpow_of_amplitudeData` capstone (J4-543) still binds abstractly, and precisely
  SCOPES the surviving geometric carry (the unrestricted `AmplitudeDerivativeData.hD2Hexpand`).

  ── PART A (DISCHARGED, unconditional for `n ≥ 1`).
    • `vanVleckGatedWitness_eq_zero_of_nonpos` — ★ the concrete witness vanishes at every NONPOSITIVE
        time: `∀ τ ≤ 0, ∀ p q, vanVleckGatedWitness … τ p q = 0`.  Route (verbatim from the `hker0`
        internal of `CoeffBoundsN1.heatOp_gatedWitnessN1_eq_zero_of_nonpos`): the parametrix Gaussian
        `gaussDdim τ (W q p)` vanishes at `τ ≤ 0` for `n ≥ 1` (`gaussDdim_eq_zero_of_nonpos`), so the
        whole gated `N = 1` witness is IDENTICALLY `0`.  This DISCHARGES the `hAzero` carry that appears
        as an abstract hypothesis in ~10 assembly files (`AssemblyLadderR*`, `A1R6FromLabelled*`, …).
    • `witnessSecondXDeriv_endpoint_zero` — ★ the STANDALONE `τ = 0` endpoint: `witnessSecondXDeriv …
        i 0 z = 0`.  Since the inner field slot `x' ↦ vanVleckGatedWitness … 0 x' z` is the ZERO
        function (PART A above), both `pd`'s vanish (`pd_zero_fun`).  ⚠ Sol trap AVOIDED: we prove the
        integrand identically `0` at the endpoint, never forcing a value.
    • `hEndpoint_discharged` — ★ the EXACT `hEndpoint` binder shape of `hGpow_of_amplitudeData`,
        produced UNCONDITIONALLY (no carry): `∀ m i u∈U, ∫_z witnessSecondXDeriv … i (u−u) z · F = 0`.

  ── THE WIRED CAPSTONE.
    • `hGpow_of_amplitudeData_noEndpoint` — ★★★ `MemAdjHiMomentBound.hGpow_of_amplitudeData` with the
        `hEndpoint` binder REMOVED and supplied internally from `hEndpoint_discharged` (only the
        `AmplitudeDerivativeData` bundle + `K₁`/`K₀` comparisons + window-floor data remain).

  ── PART B (SCOPED, NOT closed — the genuine geometric wall).
    The unrestricted `AmplitudeDerivativeData` for the CURVED van-Vleck witness is NOT constructible
    with bounded amplitudes: matching the concrete chart-image Gaussian `G_τ(W z 0)` to the base-point
    `G_τ(z)` of `hD2Hexpand` requires the chart near-isometry `‖W z 0‖ = ‖z‖ + O(‖z‖⁴)`, whose error
    ratio is bounded ONLY on the collar (off-collar the amplitude sup-bounds `hAampBdd` fail).  This is
    exactly why the collar-restricted variant `AmplitudeDataOnCollar.AmplitudeDerivativeDataOn` +
    concrete constructor `amplitudeDataOn_concrete` (which DISCHARGES `hD2HexpandOn` from a chart-jet
    bundle `hjets`) was built.  Sol #J4-543 confirmed: there is NO standalone `∫ ∂²ₓ H_G = 0`; the
    cancellation is UNAVOIDABLY routed through `hD2Hexpand`.  So `hD2Hexpand` (with its amplitudes +
    bounds) is the ONE surviving curved geometric carry of the unrestricted bundle — recorded here as
    `amplitudeData_concrete_residual`, NOT fabricated.

  NO `sorry`, NO `admit`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  `a₁ = R/6` remains CONDITIONAL and effectively FLAT-ONLY.  Discharging `hEndpoint`/`hAzero` does
  NOT derive the coefficient — the capped leg-2 `hLapFull`, the convergence trio, the Seeley–DeWitt
  geometric wiring, AND the curved `hD2Hexpand` amplitude carry all remain.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.MemAdjHiMomentBound
import QIQTH.ModelIntegrableW
import QIQTH.OffSVanishing

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.HeatResidualBound QIQTH.OffSVanishing QIQTH.TrueHeatKernel
open scoped Interval Topology BigOperators

namespace QIQTH.AmplitudeDerivativeDataConcrete

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART A — the concrete witness vanishes at nonpositive time (`hAzero` discharge).
    ############################################################################### -/

/-- **General helper.**  The gated `N = 1` global-cutoff parametrix witness (for ARBITRARY carried
    `Θ`, `u`, `Vmap`) vanishes at every nonpositive time when `n ≥ 1`.  The parametrix Gaussian
    `gaussDdim τ (Vmap q p)` is `0` at `τ ≤ 0` (`gaussDdim_eq_zero_of_nonpos`), so the whole radially
    cut-off witness is `0`, and every `gatedKernel` if-branch is `0`.  ⚠ NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_eq_zero_of_nonpos (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (Vmap : Point n → Point n → Point n)
    (hn : 1 ≤ n) (τ : ℝ) (hτ : τ ≤ 0) (p q : Point n) :
    gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) τ p q = 0 := by
  have hwit : globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p q = 0 := by
    simp only [globalCutoffParametrixWitnessN, heatParametrix,
      gaussDdim_eq_zero_of_nonpos hn hτ, zero_mul, mul_zero]
  simp only [gatedKernel]
  split_ifs
  · exact hwit
  · rfl
  · rfl

/-- **★ `vanVleckGatedWitness_eq_zero_of_nonpos`.**  THE `hAzero` DISCHARGE.  For `1 ≤ n`, the concrete
    gated `N = 1` van-Vleck witness vanishes at every NONPOSITIVE time:
        `∀ τ ≤ 0, ∀ p q, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0`.
    Specializes `gatedWitnessN1_eq_zero_of_nonpos` at the concrete van-Vleck `Θ`/`u`/`Vmap` after
    `unfold`.  This is the abstract `hAzero` carry of `AssemblyLadderR*` / `A1R6FromLabelled*`
    DISCHARGED for the concrete witness.  ⚠ NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitness_eq_zero_of_nonpos (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) (τ : ℝ) (hτ : τ ≤ 0) (p q : Point n) :
    vanVleckGatedWitness g gi hChr hK S a b τ p q = 0 := by
  unfold vanVleckGatedWitness
  exact gatedWitnessN1_eq_zero_of_nonpos K S _ _ a b _ hn τ hτ p q

/-! ###############################################################################
    ### PART A — the standalone `τ = 0` endpoint vanishing of the second `x`-derivative.
    ############################################################################### -/

/-- **★ `witnessSecondXDeriv_endpoint_zero`.**  THE STANDALONE `τ = 0` ENDPOINT.  For `1 ≤ n`, the
    concrete formal second-`x`-derivative of the witness vanishes at `τ = 0`:
        `witnessSecondXDeriv g gi hChr hK S a b i 0 z = 0`.
    Since the inner field slot `x' ↦ vanVleckGatedWitness … 0 x' z` is the ZERO function
    (`vanVleckGatedWitness_eq_zero_of_nonpos` at `τ = 0`), both `pd`'s vanish (`pd_zero_fun`).
    ⚠ Sol trap AVOIDED: the integrand is proved identically `0` at the endpoint, no forced value.
    ⚠ NOT `a₁ = R/6`. -/
theorem witnessSecondXDeriv_endpoint_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) (i : Fin n) (z : Point n) :
    witnessSecondXDeriv g gi hChr hK S a b i 0 z = 0 := by
  unfold witnessSecondXDeriv
  have hin : (fun x' : Point n => vanVleckGatedWitness g gi hChr hK S a b 0 x' z)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext x'
    exact vanVleckGatedWitness_eq_zero_of_nonpos g gi hChr hK S a b hn 0 le_rfl x' z
  rw [hin]
  have hmid : (fun x : Point n => pd (fun _ : Point n => (0 : ℝ)) i x)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext x; exact pd_zero_fun i x
  rw [hmid]
  exact pd_zero_fun i 0

/-! ###############################################################################
    ### PART A — the exact `hEndpoint` binder shape of `hGpow_of_amplitudeData`, unconditional.
    ############################################################################### -/

/-- **★ `hEndpoint_discharged`.**  THE `hEndpoint` DISCHARGE (exact `hGpow_of_amplitudeData` shape).
    For `1 ≤ n`, the `τ = 0` measure-zero endpoint carry — `∀ m i u∈U,
    ∫_z witnessSecondXDeriv … i (u−u) z · leviSeries … u z 0 = 0` — is PRODUCED UNCONDITIONALLY: since
    `u − u = 0` and the endpoint second-derivative vanishes (`witnessSecondXDeriv_endpoint_zero`), the
    integrand is `0` pointwise, so the integral is `0`.  NO carry.  ⚠ NOT `a₁ = R/6`. -/
theorem hEndpoint_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) (U : Set ℝ) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0 := by
  intro _m i u _hu
  have hz : ∀ z : Point n, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z = 0 := by
    intro z
    rw [sub_self]
    exact witnessSecondXDeriv_endpoint_zero g gi hChr hK S a b hn i z
  simp only [hz, zero_mul, integral_zero]

/-! ###############################################################################
    ### THE WIRED CAPSTONE — `hGpow` with `hEndpoint` supplied internally.
    ############################################################################### -/

/-- **★★★ `hGpow_of_amplitudeData_noEndpoint`.**  `MemAdjHiMomentBound.hGpow_of_amplitudeData` with the
    single measure-zero `hEndpoint` binder REMOVED and supplied INTERNALLY from `hEndpoint_discharged`
    (using only `1 ≤ n`).  Given the concrete `AmplitudeDerivativeData` bundle (`∀ i`), the uniform
    leading/mass constants `K₁`/`K₀` with the per-`i` comparisons, and the window-floor data, there is a
    SINGLE `m`- and `i`-uniform `Cpair ≥ 0` with the EXACT `hGpow` type of
    `MemAdjHiSliver.hII_hi_from_sliver`.  Pure surface reduction: it threads the banked endpoint fact in
    place of the abstract carry; closes NOTHING deeper.  The curvature remains carried inside the
    `AmplitudeDerivativeData.hD2Hexpand` amplitudes.  ⚠ NOT `a₁ = R/6`. -/
theorem hGpow_of_amplitudeData_noEndpoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T τ₀ aa : ℝ) (U : Set ℝ)
    (data : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
    (hn : 1 ≤ n)
    (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u) (hUT : ∀ u ∈ U, u ≤ T)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    (K₁ K₀ : ℝ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀)
    (hK₁bound : ∀ i : Fin n,
        (data i).L * (15 / 2 * (n : ℝ))
            + 3 / 4 * ((data i).M₁ * ((data i).C_L * gaussDdim aa (0 : Point n))) ≤ K₁)
    (hK₀bound : ∀ i : Fin n,
        (data i).M₂ * ((data i).C_L * gaussDdim aa (0 : Point n)) ≤ K₀) :
    ∃ Cpair : ℝ, 0 ≤ Cpair ∧
      ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) :=
  QIQTH.MemAdjHiMomentBound.hGpow_of_amplitudeData g gi hChr hK S a b T τ₀ aa U data
    haa hau hUT hεaa hετ₀ K₁ K₀ hK₁ hK₀ hK₁bound hK₀bound
    (hEndpoint_discharged g gi hChr hK S a b hn U)

/-! ###############################################################################
    ### PART B — the scoped surviving geometric carry (the genuine `hD2Hexpand` wall).
    ############################################################################### -/

/-- **`amplitudeData_concrete_residual`.**  THE ENUMERATED SURVIVING RESIDUE after the J4-544
    `hEndpoint`/`hAzero` grounding, for the UNRESTRICTED `AmplitudeDerivativeData` of the CURVED
    van-Vleck witness.  A genuine conjunction (non-vacuous plumbing witness), machine-checkable; each
    conjunct SATISFIABLE, none the conclusion.

    THE LEDGER (what `hGpow_of_amplitudeData_noEndpoint` carries, having shed `hEndpoint`):
      1. `hAmpGeom`  — the concrete `AmplitudeDerivativeData` bundle, whose ONE hard field is
         `hD2Hexpand`: the 3-term Leibniz-Gaussian identity matching the chart-image Gaussian
         `G_τ(W z 0)` to the base-point `G_τ(z)`.  For the CURVED witness this needs the chart
         near-isometry `‖W z 0‖ = ‖z‖ + O(‖z‖⁴)` + amplitude error-absorption, whose ratio is bounded
         ONLY on the collar (off-collar `hAampBdd` fails) — hence the banked resolution is the
         collar-restricted `AmplitudeDataOnCollar.amplitudeDataOn_concrete`, which discharges
         `hD2HexpandOn` from a chart-jet bundle.  ⚠ This is the genuine unbuilt geometric carry.
      2. `hKcompare` — the `K₁`/`K₀` uniform envelope of the per-coordinate amplitude constants.

    DISCHARGED (NOT in this ledger): `hEndpoint`/`hAzero` — the `τ = 0` measure-zero endpoint value
    (from `hEndpoint_discharged`, unconditional for `n ≥ 1`), with NO residue.  ⚠ NOT `a₁ = R/6`;
    CONDITIONAL on exactly this surface. -/
def amplitudeData_concrete_residual (hAmpGeom hKcompare : Prop) : Prop :=
  hAmpGeom ∧ hKcompare

/-- The ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem amplitudeData_concrete_residual_intro {hAmpGeom hKcompare : Prop}
    (h1 : hAmpGeom) (h2 : hKcompare) :
    amplitudeData_concrete_residual hAmpGeom hKcompare :=
  ⟨h1, h2⟩

end QIQTH.AmplitudeDerivativeDataConcrete

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AmplitudeDerivativeDataConcrete.gatedWitnessN1_eq_zero_of_nonpos
#print axioms QIQTH.AmplitudeDerivativeDataConcrete.vanVleckGatedWitness_eq_zero_of_nonpos
#print axioms QIQTH.AmplitudeDerivativeDataConcrete.witnessSecondXDeriv_endpoint_zero
#print axioms QIQTH.AmplitudeDerivativeDataConcrete.hEndpoint_discharged
#print axioms QIQTH.AmplitudeDerivativeDataConcrete.hGpow_of_amplitudeData_noEndpoint
#print axioms QIQTH.AmplitudeDerivativeDataConcrete.amplitudeData_concrete_residual_intro
