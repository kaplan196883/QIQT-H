/-
  HgateCensusAssembly — J4-366: the U3 CENSUS-THREAD of the `hgate` `Da`-limit assembly.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  PACKAGING / RE-THREAD brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It takes the
  banked capstone `QIQTH.LabelledRethreadV2.hDaLimLU_from_hgate` (J4-364) and RETIRES its atomic per-`u`
  interchange label — binder (viii) `hPd2conv` — by consuming instead the SATISFIABLE per-`u` sliver
  census + the two first-partial germ links of `QIQTH.Pd2ConvPerU.hPd2conv_perU` (J4-365), which supplies
  exactly that `hPd2conv` conclusion.  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`,
  NO vacuous / unsatisfiable hypothesis, NONE equal to the conclusion, no existing file edited, nothing
  committed.  `a₁ = R/6` stays CONDITIONAL on the whole `hDuhamel`/convergence-trio + geometric-wiring
  stack AND on the surviving LABELLED inputs threaded here.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DELIVERABLE.
    `hDaLimLU_from_hgate_census` — VERBATIM `hDaLimLU_from_hgate` with the SINGLE labelled binder (viii)
    `hPd2conv` replaced by the per-`u` census binder block of `hPd2conv_perU`
      `{sSet, hsOpen, hsnhds, gcoef, gderiv, fbulk, fderivBulk, bb, hb, hbulkderiv, hbulk_tendsto,
        hsliver, hfull_pd1, hfrozen_pd1}`.
    Same conclusion `DaLimLUGoal g gi (vanVleckGatedWitness …) (leviSeries …) U`.  The body is ONE
    application of `hDaLimLU_from_hgate` with the (viii) slot fed by `hPd2conv_perU` on the census slice.
    No binder rename was needed: the census names (`sSet`, `bb`, `hb`, `gcoef`, …) do NOT collide with any
    existing assembly binder (`bnd`, `snb`, `dataAmp`, …).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## SURVIVING LABELLED SURFACE (after this brick).  This brick discharges the ATOMIC per-`u` `hPd2conv`
  label; the assembly now consumes the satisfiable per-`u` sliver census + the two first-partial germ
  links `hfull_pd1`/`hfrozen_pd1` instead.  The remaining genuinely LABELLED inputs are:
    • `hgate` — the honest on-gate width-4/3 QUADRATIC M2-ingredient carry (the M2 derivation);
    • `dataAmp`'s `hD2Hexpand` field — the √ε sliver amplitude second-expansion hard field;
    • the two germ links `hfull_pd1` / `hfrozen_pd1`, each dischargeable from the banked
      `CConvV2Facade.hfam_v2` (full side) and the frozen-side W2 formula.  NOTE: `hQ1` is ALREADY an
      assembly binder here, so a later brick can discharge `hfrozen_pd1` INTERNALLY from `hQ1` (via
      `Pd2ConvPerU.hfrozen_pd1_from_hQ1`) without introducing any new labelled surface.

  ## SATISFIABILITY / HONESTY.  Every carry is the banked, satisfiable, non-vacuous census / assembly
  datum: the width-2 Gaussian model satisfies the whole sliver census and the `hDaLimLU` census, `hgate`
  is the banked J4-362 satisfiable on-gate carry, and the germ links are the banked facade-v2 / W2
  families.  NONE of the hypotheses equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GlobalRawBoundFacade
import QIQTH.HrawPreCollapse
import QIQTH.LabelledRethreadV2
import QIQTH.Pd2ConvPerU

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.GlobalRawBoundFacade
open scoped Interval Topology BigOperators

namespace QIQTH.HgateCensusAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ (U3) — `hDaLimLU_from_hgate_census`.**  THE CENSUS-THREAD.  VERBATIM
    `LabelledRethreadV2.hDaLimLU_from_hgate` with its SINGLE labelled interchange binder (viii)
    `hPd2conv` replaced by the per-`u` sliver census + two first-partial germ links of
    `Pd2ConvPerU.hPd2conv_perU`.  Same conclusion `DaLimLUGoal g gi (vanVleckGatedWitness …)
    (leviSeries …) U`.  This RETIRES the atomic per-`u` `hPd2conv` label from the `hgate` assembly:
    the assembly now consumes the satisfiable per-`u` sliver census + the germ links instead.
    Surviving labelled surface: `hgate` (M2-ingredient derivation), `dataAmp`'s `hD2Hexpand` field, and
    the germ links `hfull_pd1`/`hfrozen_pd1` (each dischargeable from `hfam_v2` / the assembly's own
    `hQ1` binder — `hQ1` is ALREADY an assembly binder, so `hfrozen_pd1` can be discharged internally by
    a later brick).  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_hgate_census (g gi : Point n → Fin n → Fin n → ℝ)
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
    -- (vii) ★ THE HONEST on-gate width-4/3 QUADRATIC carry (replaces the width-1 LINEAR `hraw` label):
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
    -- (viii) ★ THE PER-`u` SLIVER CENSUS + two first-partial germ links (replaces the atomic per-`u`
    --        interchange label `hPd2conv`; the conclusion of `Pd2ConvPerU.hPd2conv_perU` IS that binder):
    (sSet : ℝ → Set (Point n))
    (hsOpen : ∀ u ∈ U, IsOpen (sSet u))
    (hsnhds : ∀ u ∈ U, sSet u ∈ 𝓝 (0 : Point n))
    (gcoef : ℝ → Fin n → Point n → ℝ)
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (fbulk : ℝ → Fin n → ℕ → Point n → ℝ)
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (bb : ℝ → Fin n → ℕ → ℝ)
    (hb : ∀ u ∈ U, ∀ i : Fin n, Tendsto (bb u i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ sSet u,
        HasFDerivAt (fbulk u i m) (fderivBulk u i m x) x)
    (hbulk_tendsto : ∀ u ∈ U, ∀ i : Fin n, ∀ x ∈ sSet u,
        Tendsto (fun m => fbulk u i m x) atTop (𝓝 (gcoef u i x)))
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ sSet u,
        dist (fderivBulk u i m x) (gderiv u i x) ≤ bb u i m)
    (hfull_pd1 : ∀ u ∈ U, ∀ i : Fin n,
        (fun y => pd (fun x => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y)
          =ᶠ[𝓝 (0 : Point n)] gcoef u i)
    (hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)] fbulk u i m)
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
  QIQTH.LabelledRethreadV2.hDaLimLU_from_hgate g gi hChr hK S a b T U hUopen hn
    hK0 hframeK hinvF hdg0
    V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    aa haa hau hUTle C dataLevi
    wA CA wA2 CA2 hwA hCA hwA2 hCA2 hAdomHeat hAdom2
    hmeasLo hmeasHi hmeas2Lo hmeas2Hi
    τ₀ dataAmp hεaa hετ₀
    P hP hgate
    (QIQTH.Pd2ConvPerU.hPd2conv_perU g gi hChr hK S a b U sSet hsOpen hsnhds
      gcoef gderiv fbulk fderivBulk bb hb hbulkderiv hbulk_tendsto hsliver hfull_pd1 hfrozen_pd1)
    hDa hLap hLapZ hEZ hLapS hES

end QIQTH.HgateCensusAssembly

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HgateCensusAssembly.hDaLimLU_from_hgate_census
