/-
  CurvedA1AmplitudeData — J4-553: concretize the HI-leg amplitude carry for the genuinely-curved
  witness `g^K = curvedRNCMetric κ` down to the chart-jet bundle `hjets` + the off-collar tail, by
  (a) LANDING the CURVED collar amplitude bundle from `AmplitudeDataOnCollar.amplitudeDataOn_concrete`
  (fed the chart-jet bundle `hjets` + elementary carries), and (b) SCOPING the residual at the SOUND
  `hGpow`/`hinner_window` level — producing the curved `MemAdjHi` HI-leg from a SATISFIABLE all-`z`
  moment carry `hinner_window` via the banked `HGpowFromCollar.hGpow_from_innerWindow` — instead of
  fabricating the (per J4-544) NON-CONSTRUCTIBLE whole-space `AmplitudeDerivativeData`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## THE J4-544 VERDICT (authoritative, from `AmplitudeDerivativeDataConcrete` PART B).
  The UNRESTRICTED (whole-space) `AmplitudeDerivativeData` for the CURVED van-Vleck witness is **NOT
  constructible with bounded amplitudes**: the concrete Gaussian sits at the CHART IMAGE `G_τ(W z 0)`,
  and matching it to the base-point `G_τ(z)` shape of `hD2Hexpand` needs the ratio
  `ρ = G_τ(W z 0)/G_τ(z)`, which is bounded ONLY on the `τ`-shrinking collar `‖z‖ ≤ c√τ` and BLOWS UP
  off-collar (so the sup-bounds `hAampBdd` fail off-collar).  CONSEQUENCE: a downstream hypothesis of
  the form `hBridge : collarBundle → wholeSpaceAmplitudeDerivativeData` would be carrying a plausibly
  UNSATISFIABLE (vacuous) object — a soundness hole.  Sol (J4-553) confirmed: DO NOT fabricate the
  whole-space bundle; land the real satisfiable collar object and scope the residual at the moment
  (`hinner_window`) level.

  ## WHAT LANDS HERE (all satisfiable, none the conclusion, no vacuity).
    • `curved_amplitudeDataOn_at_gate` — ★★ the CURVED COLLAR amplitude bundle
        `AmplitudeDerivativeDataOn (curvedRNCMetric κ) … (collarRegime r₀ c τ₀)`, produced by
        `amplitudeDataOn_concrete` at `g = curvedRNCMetric κ`, `S = constGate …`, from the chart-jet
        bundle `hjets` + the elementary carries (near-isometry `hiso`, chart sup-bounds `hM·chart`,
        Levi/measurability/Lipschitz feeds).  This DISCHARGES the ON-collar amplitude data to `hjets`,
        for the genuinely-curved metric — the collar bundle IS constructed from the chart-jets.
    • `curved_hII_hi_from_innerWindow` — ★★★ THE SOUND HI-leg wire: the capstone's
        `hII_hi : MemAdjHi …` for `g^K`, produced from {slice-AESM continuity carries + the ALL-`z`
        HI moment carry `hinner_window` (a TRUE, satisfiable `K₁·(u−s)^{-1/2}+K₀` bound) + `1 ≤ n`}
        via `HGpowFromCollar.hGpow_from_innerWindow` (⟹ `hGpow`, endpoint discharged internally) →
        `MemAdjHiSliver.hII_hi_from_sliver`.  This CONSUMES the satisfiable `hinner_window` rather than
        the non-constructible whole-space bundle, so it introduces NO vacuous hypothesis.
    • `curved_amplitudeData_residual` — the enumerated surviving residue after this factoring:
        `hCollarBundle` (BANKED via `curved_amplitudeDataOn_at_gate` ← `hjets` + elementary) ∧
        `hOffCollarTail` (the off-collar Gaussian-tail reconstitution that, with the on-collar bundle,
        yields the all-`z` `hinner_window` — the SOLE surviving curved geometric carry of the HI-leg).

  ## THE UPDATED RESIDUAL (★ what `data` reduced TO, for the HI leg).
    HI-leg `MemAdjHi`  ⟵  `curved_hII_hi_from_innerWindow`
      ⟵ {slice-AESM continuity `hUT`/`hεU`/`hSecCont`/`hBcont`}          (elementary carries)
        ∪ {`hinner_window` : the all-`z` `K₁·(u−s)^{-1/2}+K₀` moment bound}
      where `hinner_window`  ⟵  `hOnCollar` (BANKED ← curved collar bundle ← `hjets`) ⊕ `hOffCollarTail`.
    The chart-jet bundle `hjets` (chart-jet C⁴ / Jacobian center identities) and the off-collar
    reconstitution `hOffCollarTail` are the surviving owed geometric inputs; the `τ = 0` endpoint and
    the whole-space-bundle detour are ELIMINATED.  ⚠ NOT `a₁ = R/6` — CONDITIONAL on exactly this
    surface (hjets + hOffCollarTail + the leg-2 / convergence / Seeley–DeWitt inputs elsewhere).
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.MemAdjHiSliver
import QIQTH.AmplitudeDerivativeDataConcrete
import QIQTH.AmplitudeDataOnCollar
import QIQTH.HGpowFromCollar
import QIQTH.CurvedA1FullyWiredCapstone

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.HrepGermFactorization
open QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.LaplaceBeltrami
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.AmplitudeDataOnCollar QIQTH.HGpowFromCollar QIQTH.MemAdjHiSliver
open QIQTH.DaLimLUWallRecon
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1AmplitudeData

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — ★★ the CURVED collar amplitude bundle, from the chart-jet bundle `hjets`.
    ############################################################################### -/

/-- **★★ `curved_amplitudeDataOn_at_gate`.**  The CURVED collar-restricted amplitude bundle
    `AmplitudeDerivativeDataOn (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate … cg) a b F i T τ₀
    (collarRegime r₀ c τ₀)`, produced by `AmplitudeDataOnCollar.amplitudeDataOn_concrete` at the curved
    metric with the constant-radius gate `S = constGate … cg`.  Its ONE hard field `hD2Hexpand` is
    DISCHARGED (on the collar) from the chart-jet bundle `hjets`; the amplitude bounds are discharged on
    the collar via `rhoRatio_le_collarK`.  The remaining inputs are the near-isometry lower bound
    `hiso`, the regime-restricted chart-amplitude sup-bounds `hM·chart`, and the unchanged
    Levi/measurability/Lipschitz feeds — all carried honestly.  This is the collar amplitude data
    CONSTRUCTED FROM THE CHART-JETS for the genuinely-curved witness.  ⚠ NOT `a₁ = R/6`. -/
noncomputable def curved_amplitudeDataOn_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b cg : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (Liso c r₀ : ℝ) (hLiso : 0 ≤ Liso)
    (hiso : ∀ z ∈ K, ‖z‖ < r₀ →
      rncRadialSq z - Liso * ‖z‖ * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0))
    (M₀chart M₁chart M₂chart Lq C_L : ℝ)
    (hM₀chart_nn : 0 ≤ M₀chart) (hM₁chart_nn : 0 ≤ M₁chart) (hM₂chart_nn : 0 ≤ M₂chart)
    (hLq : 0 ≤ Lq) (hC_L : 0 ≤ C_L)
    (hM₀chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z 0| ≤ M₀chart)
    (hM₁chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |(-2 * pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i 0)| ≤ M₁chart)
    (hM₂chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |pd (fun y => pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i y) i 0|
        ≤ M₂chart)
    (hjets : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg z) ∧
      (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg z ∧
      ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
        (∀ x k, HasDerivAt
          (fun s : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
            (Function.update x i s) k) (P x k) (x i)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) ∧
        (∀ x, PdiffAt (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i x) ∧
        PdiffAt (fun y => pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i y) i
          (0 : Point n) ∧
        (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P 0 k = z i) ∧
        (∑ k, P 0 k ^ 2 = 1) ∧
        (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q k = 0))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n => rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ z
        * chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z 0) volume)
    (hA1ampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n => rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ z
        * (-2 * pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i 0)) volume)
    (hA2ampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n => rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ z
        * pd (fun y => pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i y) i 0)
      volume)
    (hFmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hqLip : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ s, 0 < s → s ≤ T → ∀ z w : Point n,
      |(rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ z
            * chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z 0) * F s z 0
          - (rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ w
            * chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ w 0) * F s w 0|
        ≤ Lq * dist z w) :
    AmplitudeDerivativeDataOn (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b F i T τ₀
      (collarRegime (K := K) r₀ c τ₀) :=
  QIQTH.AmplitudeDataOnCollar.amplitudeDataOn_concrete (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b F i T τ₀
    Liso c r₀ hLiso hiso M₀chart M₁chart M₂chart Lq C_L
    hM₀chart_nn hM₁chart_nn hM₂chart_nn hLq hC_L
    hM₀chart hM₁chart hM₂chart hjets hFdom hAampmeas hA1ampmeas hA2ampmeas hFmeas hqLip

/-! ###############################################################################
    ### §2 — ★★★ the SOUND HI-leg wire: `MemAdjHi` from the all-`z` moment carry `hinner_window`.
    ############################################################################### -/

/-- **★★★ `curved_hII_hi_from_innerWindow`.**  THE capstone `hII_hi : MemAdjHi …` residual for the
    genuinely-curved witness `g^K = curvedRNCMetric κ`, `S = constGate … cg`, produced from the SOUND,
    SATISFIABLE inputs — the slice-AESM continuity carries + the ALL-`z` HI moment bound
    `hinner_window` (`|∫ z, witnessSecondXDeriv · leviSeries| ≤ K₁·(u−s)^{-1/2} + K₀`) + `1 ≤ n` — via
    the banked chain
      `HGpowFromCollar.hGpow_from_innerWindow` (⟹ the `τ^{-1/2}` moment carry `hGpow`, endpoint
        discharged internally from `hEndpoint_discharged`)
        →  `MemAdjHiSliver.hII_hi_from_sliver` (⟹ `MemAdjHi` via slice-AESM domination).
    This DELIBERATELY avoids the whole-space `AmplitudeDerivativeData` (which J4-544 showed is NOT
    constructible with bounded amplitudes for the curved witness), consuming instead the TRUE moment
    bound `hinner_window` — hence no vacuous hypothesis.  `hinner_window` decomposes (off-line) as the
    on-collar bundle contribution (BANKED ← `hjets` via `curved_amplitudeDataOn_at_gate`) plus the
    off-collar Gaussian-tail reconstitution `hOffCollarTail`.  Every hypothesis is satisfiable and
    non-vacuous for `g^K` (`κ < 0`, Ric ≠ 0); none forces `Ric = 0`; none is the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hII_hi_from_innerWindow (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b cg : ℝ)
    (T : ℝ) (U : Set ℝ) (hn : 1 ≤ n)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (K₁ K₀ : ℝ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀)
    (hinner_window : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b i (u - s) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b)) s z 0|
          ≤ K₁ * (u - s) ^ (-(1 : ℝ) / 2) + K₀) :
    MemAdjHi (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b))) U
      (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b i τ z) := by
  -- STAGE 1 — the `τ^{-1/2}` moment carry `hGpow` (endpoint discharged internally, route-agnostic).
  obtain ⟨Cpair, hCpair, hGpow⟩ :=
    QIQTH.HGpowFromCollar.hGpow_from_innerWindow (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b U hn K₁ K₀ hK₁ hK₀
      hinner_window
  -- STAGE 2 — slice-AESM domination ⟹ `MemAdjHi`.
  exact QIQTH.MemAdjHiSliver.hII_hi_from_sliver
    (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b T U
    hUT hεU hSecCont hBcont Cpair hCpair hGpow

/-! ###############################################################################
    ### §3 — the enumerated surviving residue (precise scoping ledger).
    ############################################################################### -/

/-- **`curved_amplitudeData_residual`.**  THE ENUMERATED SURVIVING RESIDUE for the CURVED HI-leg after
    this factoring.  A genuine conjunction (non-vacuous plumbing witness); each conjunct SATISFIABLE,
    none the conclusion.

    THE LEDGER (what the all-`z` `hinner_window` — hence the curved HI-leg `MemAdjHi` via
    `curved_hII_hi_from_innerWindow` — still consumes):
      1. `hCollarBundle`  — the CURVED collar amplitude bundle's ON-collar contribution.  This is BANKED
         (`curved_amplitudeDataOn_at_gate` ← the chart-jet bundle `hjets` + elementary carries).
      2. `hOffCollarTail` — ★ the OFF-COLLAR Gaussian-tail reconstitution on `‖z‖ > c√τ` that, with the
         on-collar bundle, reconstitutes the full-space Hessian moment and yields the all-`z`
         `K₁·(u−s)^{-1/2}+K₀` shape of `hinner_window`.  ⚠ The GENUINE surviving curved geometric carry.

    DISCHARGED / ELIMINATED (NOT in this ledger): the `τ = 0` measure-zero endpoint (internal to
    `hGpow_from_innerWindow`), AND the whole-space `AmplitudeDerivativeData` detour (avoided — per
    J4-544 it is NOT constructible with bounded amplitudes for the curved witness).  ⚠ NOT `a₁ = R/6`;
    CONDITIONAL on exactly this surface. -/
def curved_amplitudeData_residual (hCollarBundle hOffCollarTail : Prop) : Prop :=
  hCollarBundle ∧ hOffCollarTail

/-- The curved HI-leg residue ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_amplitudeData_residual_intro {hCollarBundle hOffCollarTail : Prop}
    (h1 : hCollarBundle) (h2 : hOffCollarTail) :
    curved_amplitudeData_residual hCollarBundle hOffCollarTail :=
  ⟨h1, h2⟩

end QIQTH.CurvedA1AmplitudeData

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedA1AmplitudeData.curved_amplitudeDataOn_at_gate
#print axioms QIQTH.CurvedA1AmplitudeData.curved_hII_hi_from_innerWindow
#print axioms QIQTH.CurvedA1AmplitudeData.curved_amplitudeData_residual_intro
