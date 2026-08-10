/-
  DaLimLUMemAdjHi — J4-542.  The LEG-1 (Da-limit) LO-CAPPED capstone with the `MemAdjHi` HI-leg
  residual **DISCHARGED** into honest, satisfiable, moment-aware carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  thin WIRE: it takes the J4-541 leg-1 LO-capped capstone `DaLimLUCappedStep3.hDaLimLU_from_labelled_capped`
  and discharges its ONE carried `MemAdjHi` binder `hII_hi_res` via the banked HI-leg integrability brick
  `MemAdjHiSliver.hII_hi_from_sliver` — so the abstract `MemAdjHi` residual is replaced by the honest,
  SATISFIABLE, moment-aware carries it actually reduces to:
    •  banked s-slice AEStronglyMeasurability inputs `hSecCont`/`hBcont` (joint continuity of the pairing
       on `Ioc 0 T ×ˢ univ`; `hUT`/`hεU` are reused/derived from the capstone's own binders);
    •  the NAMED, SATISFIABLE moment-improved `τ^{-1/2}` carry `hGpow` on the SIGNED `z`-integral of the
       second-derivative pairing, with a single `m`-uniform `Cpair ≥ 0`.
  No `sorry`/`admit` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited,
  nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT CLOSED, WHAT IS CARRIED.

  CLOSED — the abstract `MemAdjHi (…) U (fun i τ z => witnessSecondXDeriv …)` binder of the leg-1 capstone
  is no longer an OPAQUE residual: it is CONSTRUCTED inside this wrapper from `hII_hi_from_sliver`, which
  bypasses the crude-`τ⁻¹` non-integrability obstruction (`∫₀^{ε_m} τ⁻¹ = +∞`) via the moment-cancellation
  `(u−s)^{-1/2}` dominator (interval-integrable, `∫₀^{ε} τ^{-1/2} = 2√ε < ∞`) dominating an a.e.-strongly-
  measurable pairing.

  CARRIED (honestly, and STRICTLY WEAKER than any false pointwise 2nd-derivative Gaussian domination):
    •  `hGpow` — the `τ^{-1/2}` bound on the SIGNED `z`-integral of the pairing.  This is TRUE for the real
       convolved heat kernel: the signed integral `∫z ∂²_xG(τ,·)·F(·)` stays `O(1)` as `τ→0` (the leading
       `τ⁻¹` cancels against `∫z ∂²G = 0`, the standard heat-kernel moment cancellation), and
       `(u−s)^{-1/2} ≥ ε₀^{-1/2}` on every HI window, so `Cpair := (sup|∫z…|)·ε₀^{1/2}` works.  It is NOT
       the clean `τ`-uniform Gaussian bound (which is FALSE at `τ→0`); it is the moment-aware
       `WideSliverBoundary` target and is genuinely satisfiable, NOT a hidden hole.
    •  `hSecCont`/`hBcont` — joint continuity of the two factors on `Ioc 0 T ×ˢ univ` (banked slice-AESM
       inputs).

  `hεU : ∀ m u ∈ U, epsSeq m ≤ u` is DERIVED from the capstone's own `hau`/`hεaa`/`haa`
  (`epsSeq m < aa/2 ≤ aa ≤ u`, `aa > 0`); `hUT` is the capstone's own `hUTle`.

  ⚠  `a₁ = R/6` remains CONDITIONAL and effectively FLAT-ONLY.  Discharging this HI-leg residual does NOT
  derive the coefficient: the leg-2 capped `hLapFull`, the LO-leg / other `MemAdjHi` targets, the
  convergence trio, and the Seeley–DeWitt geometric wiring all remain, and the moment-cancellation carry
  `hGpow` is honestly labelled (a separate concrete-kernel theorem would be needed to construct it for the
  actual kernel and thereby remove it entirely).  NOT `a₁ = R/6`. -/
import Mathlib
import QIQTH.DaLimLUCappedStep3
import QIQTH.MemAdjHiSliver

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped QIQTH.DaLimLUCappedStep2
open QIQTH.DaLimLUCappedStep3 QIQTH.MemAdjHiSliver
open scoped Interval Topology BigOperators

namespace QIQTH.DaLimLUMemAdjHi

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-542 — `hDaLimLU_from_labelled_capped_memAdjHi`.**  The leg-1 LO-capped capstone
    `DaLimLUCappedStep3.hDaLimLU_from_labelled_capped` with its ONE carried abstract `MemAdjHi` HI-leg
    residual `hII_hi_res` DISCHARGED via the banked `MemAdjHiSliver.hII_hi_from_sliver`.  The opaque
    `MemAdjHi` binder is replaced by the honest, SATISFIABLE moment-aware carries `hSecCont`/`hBcont`
    (joint-continuity / slice-AESM) + the `τ^{-1/2}` signed-integral carry `hGpow` (with `Cpair ≥ 0`).
    `hUT` reuses the capstone's `hUTle`; `hεU` is derived from `hau`/`hεaa`/`haa`.  Every hypothesis is
    SATISFIABLE and NON-VACUOUS; NONE is the conclusion; `hGpow` is genuinely true for the real convolved
    kernel (moment cancellation), not a hidden hole.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_labelled_capped_memAdjHi (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (hn : 1 ≤ n)
    -- (i) geometry / gauge raw inputs:
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0)
    -- (ii) the W2 differentiation-under-∫ family (at `F := leviSeries (heatOp g gi H_G)`):
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w)
    -- (iii) the residual-domination time floor / window:
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u) (hUTle : ∀ u ∈ U, u ≤ T)
    -- (iv) the Levi source envelope package:
    (C : ℝ) (dataLevi : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T)
    -- (v) the integrability Gaussian dominations + measurabilities (★ CAPPED: `hAdom2cap`):
    (wA CA wA2 : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    -- (v-residual, ★ DISCHARGED via the sliver brick) the moment-aware HI-leg carries:
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (Cpair : ℝ) (hCpair : 0 ≤ Cpair)
    (hGpow : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2))
    -- (vi) the √ε sliver amplitude bundle:
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    -- (vii) ★ the labelled residual gated raw bound:
    (P : ℝ) (hP : 0 ≤ P)
    (hraw : GlobalGatedRawBound g gi (vanVleckGatedWitness g gi hChr hK S a b) P)
    -- (viii) ★ the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    -- (ix) the E-combination carries:
    (hDa : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m)) :
    DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U := by
  -- ★ DISCHARGE the HI-leg `MemAdjHi` residual from the banked sliver brick.
  --   `hUT := hUTle`; `hεU` derived from `hau`/`hεaa`/`haa`  (`epsSeq m < aa/2 ≤ aa ≤ u`, `aa > 0`).
  have hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u := by
    intro m u hu
    have h1 : epsSeq m ≤ aa / 2 := le_of_lt (hεaa m)
    have h2 : aa / 2 ≤ aa := by linarith [haa]
    exact h1.trans (h2.trans (hau u hu))
  have hII_hi_res :
      MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    QIQTH.MemAdjHiSliver.hII_hi_from_sliver g gi hChr hK S a b T U
      hUTle hεU hSecCont hBcont Cpair hCpair hGpow
  -- ★★★ thread the discharged residual into the J4-541 leg-1 LO-capped capstone (all else identical).
  exact QIQTH.DaLimLUCappedStep3.hDaLimLU_from_labelled_capped g gi hChr hK S a b T U hUopen hn
    hK0 hframeK hinvF hdg0
    V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    aa haa hau hUTle C dataLevi
    wA CA wA2 CA2c hwA hCA hwA2 hCA2c hAdomHeat hAdom2cap hmeasLo hmeasHi hmeas2Lo hII_hi_res
    τ₀ dataAmp hεaa hετ₀
    P hP hraw hPd2conv
    hDa hLap hLapZ hEZ hLapS hES

end QIQTH.DaLimLUMemAdjHi

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimLUMemAdjHi.hDaLimLU_from_labelled_capped_memAdjHi
