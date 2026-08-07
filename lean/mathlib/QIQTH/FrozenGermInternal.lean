/-
  FrozenGermInternal — J4-367: discharge the frozen germ-link `hfrozen_pd1` INTERNALLY from `hQ1`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  PACKAGING / SURFACE-REDUCTION brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It
  takes the banked census-thread capstone `QIQTH.HgateCensusAssembly.hDaLimLU_from_hgate_census`
  (J4-366, READ-ONLY) and STRICTLY REDUCES its labelled surface by RETIRING the frozen-side germ-link
  binder `hfrozen_pd1`: that germ is now CONSTRUCTED INTERNALLY from the assembly's OWN `hQ1` binder
  (the W2 differentiation-under-∫ pointwise formula on the open field nbhd `V ∋ 0`, binder block (ii))
  via `QIQTH.Pd2ConvPerU.hfrozen_pd1_from_hQ1`.  NO `sorry` (header prose excepted), NO new axioms, NO
  `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to the conclusion, no existing file
  edited, nothing committed.  `a₁ = R/6` stays CONDITIONAL on the whole `hDuhamel`/convergence-trio +
  geometric-wiring stack AND on the surviving LABELLED inputs threaded here.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE KEY DESIGN DECISION — ZERO NEW LABELS.
    `hQ1` (already an assembly binder) gives, for `y ∈ V`,
      `∂ᵢ(frozen_m conv)(y) = ∫₀^{u−εₘ} ∫ witnessFieldDeriv … i (u−s) y z · leviSeries … s z 0`.
    We DEFINE that truncated `s`-integral as a concrete function of `y`:
      `fbulkInt g gi hChr hK S a b u i m := fun y ↦ ∫₀^{u−εₘ} ∫ witnessFieldDeriv … i (u−s) y z · …`,
    SPECIALIZE the census's abstract `fbulk` to `fbulkInt …`, and DISCHARGE `hfrozen_pd1` internally
    (over `V ∈ 𝓝 0`, since `V` is open and `0 ∈ V`).  No new labelled hypothesis is introduced.  The
    census hypotheses that mention `fbulk` (`hbulkderiv`, `hbulk_tendsto`) are RE-STATED of `fbulkInt …`
    — they remain the SAME satisfiable uniform-limit-of-derivatives data, now concretely ANCHORED to the
    truncated integral (`hsliver` does not mention `fbulk` and is verbatim).  `fbulkInt` is a plain
    `noncomputable def`, so `hQ1`'s RHS is definitionally `fbulkInt … u i m y` and the internal germ term
    typechecks without conversion.

  ## THE DELIVERABLE.
    `hDaLimLU_from_hgate_census_v2` — VERBATIM `hDaLimLU_from_hgate_census` with (a) the `fbulk` binder
    REMOVED (specialized to `fbulkInt …`), (b) the `hfrozen_pd1` binder REMOVED (built internally from
    `hQ1`), (c) `hbulkderiv`/`hbulk_tendsto` re-stated of `fbulkInt …`.  Same conclusion
    `DaLimLUGoal g gi (vanVleckGatedWitness …) (leviSeries …) U`.  Body = ONE application of
    `hDaLimLU_from_hgate_census` with `fbulk := fbulkInt …` and the internal `hfrozen_pd1` term.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## SURVIVING LABELLED SURFACE (after this brick).  `hfrozen_pd1` is now GONE (internal).  The
  remaining genuinely LABELLED inputs of the census assembly are:
    • `hgate` — the honest on-gate width-4/3 QUADRATIC M2-ingredient carry (the M2 derivation);
    • `dataAmp`'s `hD2Hexpand` field — the √ε sliver amplitude second-expansion hard field;
    • `hfull_pd1` — the FULL-side first-partial germ link (dischargeable from `CConvV2Facade.hfam_v2`
        via `Pd2ConvPerU.hfull_pd1_concrete`; NOT yet an assembly binder here, so still labelled).
  Everything else is banked satisfiable census/assembly data (the width-2 Gaussian model satisfies it).

  ## SATISFIABILITY / HONESTY.  `hQ1` is the banked W2 differentiation-under-∫ family; `V ∈ 𝓝 0`
  follows from `hVopen`/`hV0`; `fbulkInt` is the concrete truncated integral the sliver census already
  used.  NONE of the hypotheses equals the conclusion (`hbulkderiv`/`hbulk_tendsto` are the sliver
  uniform-limit data; the conclusion is the `DaLimLUGoal`).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GlobalRawBoundFacade
import QIQTH.HrawPreCollapse
import QIQTH.LabelledRethreadV2
import QIQTH.Pd2ConvPerU
import QIQTH.HgateCensusAssembly

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.GlobalRawBoundFacade
open scoped Interval Topology BigOperators

namespace QIQTH.FrozenGermInternal

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **`fbulkInt` — the concrete frozen-side truncated `s`-integral, as a function of the field point.**
    This is EXACTLY the RHS of the assembly's `hQ1` W2 formula read as a function of `y`:
      `fbulkInt … u i m := fun y ↦ ∫₀^{u−εₘ} ∫ witnessFieldDeriv … i (u−s) y z
          · leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0`.
    Specializing the census's abstract `fbulk` to `fbulkInt …` lets `hfrozen_pd1` be discharged from
    `hQ1` with zero new labels.  NOT `a₁ = R/6`. -/
noncomputable def fbulkInt (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (i : Fin n) (m : ℕ) : Point n → ℝ :=
  fun y => ∫ s in (0)..(u - epsSeq m),
      ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0

/-- **★★★ (U3′) — `hDaLimLU_from_hgate_census_v2`.**  VERBATIM `HgateCensusAssembly.hDaLimLU_from_hgate_census`
    with the frozen germ-link binder `hfrozen_pd1` RETIRED: it is constructed INTERNALLY from the
    assembly's own `hQ1` binder (via `Pd2ConvPerU.hfrozen_pd1_from_hQ1` over `V ∈ 𝓝 0`).  The census
    `fbulk` is SPECIALIZED to the concrete truncated integral `fbulkInt …`, and `hbulkderiv`/`hbulk_tendsto`
    are re-stated of `fbulkInt …` (same satisfiable sliver uniform-limit data, now concretely anchored).
    Same conclusion `DaLimLUGoal g gi (vanVleckGatedWitness …) (leviSeries …) U`.  Surviving labelled
    surface: `hgate` (M2-ingredient), `dataAmp`'s `hD2Hexpand` field, and `hfull_pd1` (full-side germ,
    dischargeable from `hfam_v2`).  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_hgate_census_v2 (g gi : Point n → Fin n → Fin n → ℝ)
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
    -- (v) the integrability Gaussian dominations + measurabilities:
    (wA CA wA2 CA2 : ℝ) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2 : 0 ≤ CA2)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2 : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
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
    (hmeas2Hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    -- (vi) the √ε sliver amplitude bundle:
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    -- (vii) ★ THE HONEST on-gate width-4/3 QUADRATIC carry:
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
    -- (viii) ★ THE PER-`u` SLIVER CENSUS + FULL-side germ link (frozen germ link `hfrozen_pd1` is now
    --        RETIRED — built internally from `hQ1`; `fbulk` is SPECIALIZED to `fbulkInt …`):
    (sSet : ℝ → Set (Point n))
    (hsOpen : ∀ u ∈ U, IsOpen (sSet u))
    (hsnhds : ∀ u ∈ U, sSet u ∈ 𝓝 (0 : Point n))
    (gcoef : ℝ → Fin n → Point n → ℝ)
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (bb : ℝ → Fin n → ℕ → ℝ)
    (hb : ∀ u ∈ U, ∀ i : Fin n, Tendsto (bb u i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ sSet u,
        HasFDerivAt (fbulkInt g gi hChr hK S a b u i m) (fderivBulk u i m x) x)
    (hbulk_tendsto : ∀ u ∈ U, ∀ i : Fin n, ∀ x ∈ sSet u,
        Tendsto (fun m => fbulkInt g gi hChr hK S a b u i m x) atTop (𝓝 (gcoef u i x)))
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ sSet u,
        dist (fderivBulk u i m x) (gderiv u i x) ≤ bb u i m)
    (hfull_pd1 : ∀ u ∈ U, ∀ i : Fin n,
        (fun y => pd (fun x => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y)
          =ᶠ[𝓝 (0 : Point n)] gcoef u i)
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
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U :=
  QIQTH.HgateCensusAssembly.hDaLimLU_from_hgate_census g gi hChr hK S a b T U hUopen hn
    hK0 hframeK hinvF hdg0
    V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    aa haa hau hUTle C dataLevi
    wA CA wA2 CA2 hwA hCA hwA2 hCA2 hAdomHeat hAdom2
    hmeasLo hmeasHi hmeas2Lo hmeas2Hi
    τ₀ dataAmp hεaa hετ₀
    P hP hgate
    sSet hsOpen hsnhds gcoef gderiv (fbulkInt g gi hChr hK S a b) fderivBulk bb hb
    hbulkderiv hbulk_tendsto hsliver hfull_pd1
    (fun u _hu i m => QIQTH.Pd2ConvPerU.hfrozen_pd1_from_hQ1
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u m i
      (fbulkInt g gi hChr hK S a b u i m) V (hVopen.mem_nhds hV0) (hQ1 m i u _hu))
    hDa hLap hLapZ hEZ hLapS hES

end QIQTH.FrozenGermInternal

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.FrozenGermInternal.fbulkInt
#print axioms QIQTH.FrozenGermInternal.hDaLimLU_from_hgate_census_v2
