/-
  CensusGeometryThread — J4-381: THE CENSUS (a,b)-THREADING.  Wiring the geometry-derived width-3/2
  `hEdom` ∃-shape (`CommonGateShell.hEdom_from_geometry`, J4-380) into the full one-theorem `Da`-limit
  census assembly (`LabelledRethreadV2.hDaLimLU_from_labelled_v2`, J4-364).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING LABELLED census carries threaded here (the W2 differentiation-under-∫ family, the Levi
  envelope, the Gaussian dominations, the amplitude bundle, the atomic interchange carrier, and the
  E-combination facts).  This file is ONE PACKAGING / (a,b)-THREADING brick of the (still CONDITIONAL)
  campaign.  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable
  hypothesis, NONE equal to (or trivially yielding) the conclusion, NO existing file edited, nothing
  committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (T1) THE STRUCTURAL AUDIT.

  `hEdom_from_geometry` `∃`-CHOOSES the gate data `(a, b, S)` (and the coefficient pair `E₀, E₁`) from
  geometry ALONE — the surviving `hgate` on-gate label is RETIRED there.  The census assembly
  `hDaLimLU_from_labelled_v2` consumes `(S, a, b)` as FIXED parameters: every one of its ~40 census
  binders is stated AT the witness `vanVleckGatedWitness g gi hChr hK S a b` for whatever `(S, a, b)` it
  is given.  The honest resolution is therefore the `∃`-STYLE master theorem: FIRST obtain `(a, b, S)`
  (with `E₀, E₁` and the width-3/2 `hEdom` body) from the geometry, THEN quantify the census carries AT
  that geometry-chosen gate.

  ▸  NO CIRCULARITY.  No census binder CONSTRAINS `(a, b, S)` beyond "these are the witness parameters":
     the census data is *about* whatever gate is chosen (the differentiation-under-∫ identities, the
     dominations, the interchange, the E-combination — all stated at `vanVleckGatedWitness g gi hChr hK
     S a b`).  Feeding the geometry-chosen `(a, b, S)` into them changes nothing structurally; it only
     PINS which gate the census is about.

  ▸  SATISFIABILITY IS SEPARATE (honest note).  The census carries remain SATISFIABLE-SHAPED
     HYPOTHESES, now at the geometry-chosen gate.  Whether the census is satisfiable AT that particular
     `(a, b, S)` is a separate question (the width-2 Gaussian model satisfies the census SHAPE, as
     banked in `GlobalRawBoundFacade`; discharging each carry at the concrete van-Vleck gate is the
     remaining surface — see the T3 inventory below).  This file does NOT claim the census is
     discharged; it delivers the IMPLICATION `census-at-geometry-gate → DaLimLUGoal`.

  ▸  SHAPE MATCH IS VERBATIM.  The inner `∀ τ>0 ∀ p q, |heatOp …| ≤ (E₀+E₁τ)·√(3/2)ⁿ·gaussDdim ((3/2)τ)
     (p−q)` of `hEdom_from_geometry` (after the `∃ a b … ∃ S ∃ E₀ E₁` elims) is EXACTLY the body of the
     assembly's step (vii) `hEdomEx` binder — the `√(3/2)ⁿ` factor and the `(E₀+E₁τ)` linear coefficient
     are identical.  Repackaging `⟨E₀, E₁, hE₀, hE₁, hEdom⟩` feeds step (vii) directly.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (T2) THE DELIVERABLE.

  •  `hDaLimLU_from_geometry_census` — ★ the `∃`-style master theorem.  From the genuine GEOMETRY / gauge
     / smoothness / compactness inputs (`hg`/`hC=hChr`/`hw` smoothness, `hdg0`/`hg0` base gauge,
     `hframeK`/`hinvF`/`hgnd`/`hgsymm` frame/metric, `hK` compactness, `hK0` base membership) produce
         `∃ a b, ∃ S, (census carries at (S,a,b) → DaLimLUGoal g gi (vanVleckGatedWitness …) (leviSeries …) U)`.
     Curried shape (no 40-field structure): the census antecedent is the `∀`-telescope of
     `hDaLimLU_from_labelled_v2`'s binders (ii)–(ix) MINUS step (vii) (which is discharged from geometry).
     Proof: `obtain` the gate data from `hEdom_from_geometry`, then apply `hDaLimLU_from_labelled_v2`
     with step (vii) fed by `⟨E₀, E₁, hE₀, hE₁, hEdom⟩`.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (T3) THE REMAINING CENSUS SURFACE (honest inventory toward the UNCONDITIONAL `hDaLimLU`).

  The antecedent census carries that STILL stand as labelled hypotheses at the geometry-chosen gate:
    (ii)  W2 differentiation-under-∫ family — `hQ1` (frozen-side `pd`=∫ identity), `hFmeas`/`hFint`/
          `hF'meas` (measurability / interval-integrability of the field-derivative kernels), `bnd` +
          `hbdd`/`hbound`/`hdiff` (the dominated-derivative bundle).
    (iii) time floor / window — `aa` + `haa`/`hau`/`hUTle` (`0 < aa ≤ u ≤ T` on `U`).  ARITHMETIC-shaped.
    (iv)  Levi envelope — `C` + `dataLevi : LeviSeriesLocalData …` (the source-envelope bundle).
    (v)   Gaussian dominations — `wA CA wA2 CA2` + `hwA`/`hCA`/`hwA2`/`hCA2` positivity, `hAdomHeat`
          (heat-kernel Gaussian bound), `hAdom2` (2nd-x-derivative Gaussian bound), and the four
          measurabilities `hmeasLo`/`hmeasHi`/`hmeas2Lo`/`hmeas2Hi`.
    (vi)  amplitude bundle — `τ₀` + `dataAmp : AmplitudeDerivativeData …` (hard field `hD2Hexpand`),
          `hεaa`/`hετ₀` (`epsSeq` window controls).
   (viii) atomic interchange carrier — `hPd2conv` (truncated → untruncated `pd`-of-`pd` limit).
    (ix)  E-combination facts — `hDa`/`hLap` (`DaTrunc`/`LapTrunc` = ∫∫ representations), `hLapZ`/`hEZ`
          (z-integrability), `hLapS`/`hES` (s-interval-integrability).
  Step (vii) (the width-3/2 `hEdom`) is now DISCHARGED from geometry and NO longer appears.
-/
import Mathlib
import QIQTH.CommonGateShell
import QIQTH.LabelledRethreadV2

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.GlobalRawBoundFacade
open scoped Interval Topology BigOperators

namespace QIQTH.CensusGeometryThread

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (T2) — `hDaLimLU_from_geometry_census`: the ∃-style master theorem.
    ############################################################################### -/

/-- **★ (T2) — `hDaLimLU_from_geometry_census`.**  The master `∃`-style theorem threading the
    geometry-derived width-3/2 `hEdom` (`CommonGateShell.hEdom_from_geometry`) into the full census
    assembly (`LabelledRethreadV2.hDaLimLU_from_labelled_v2`).  From the genuine geometric / gauge /
    smoothness / compactness inputs it produces `∃ a b, ∃ S,` of the IMPLICATION from the census carries
    (the assembly's binders (ii)–(ix) MINUS the geometry-discharged step (vii)) to the loc-unif
    `Da`-limit `DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b) (leviSeries …) U`.  The gate
    data `(a, b, S)` is `∃`-chosen FROM GEOMETRY; the census carries are quantified AT that chosen gate.
    Curried census antecedent (no 40-field structure).  Honest: the census carries remain SATISFIABLE-
    shaped hypotheses at the geometry-chosen gate (see T3 inventory).  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_geometry_census (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (hn : 1 ≤ n)
    -- geometry / gauge / smoothness / compactness inputs (shared: feed BOTH `hEdom_from_geometry`
    -- and the assembly's step (i)):
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgnd : ∀ y : Point n, IsUnit (QIQTH.PullbackMetric.matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (QIQTH.HeatResidualBound.foldedCoeff (QIQTH.VanVleck.vanVleck g)
        (QIQTH.ParametrixFunction.transportCoeff
          (QIQTH.HeatTransportRecursion.transportOp (QIQTH.VanVleck.vanVleck g) g gi)) k))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0) :
    ∃ a b : ℝ, ∃ S : Point n → Set (Point n),
      -- (ii) the W2 differentiation-under-∫ family (at `F := leviSeries (heatOp g gi H_G)`):
      ∀ (V : Set (Point n)) (_ : IsOpen V) (_ : (0 : Point n) ∈ V)
        (snb : Set ℝ) (_ : snb ∈ 𝓝 (0 : ℝ))
        (_ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
            pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
                (u - epsSeq m) x 0) i y
              = ∫ s in (0)..(u - epsSeq m),
                  ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
                    * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (_ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (_ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume 0 (u - epsSeq m))
        (_ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (bnd : ℕ → Fin n → ℝ → ℝ)
        (_ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
            IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
        (_ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
            s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
              ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                  (Function.update (0 : Point n) i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd m i s)
        (_ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
            s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
              HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                  (Function.update (0 : Point n) i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
                (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                  (Function.update (0 : Point n) i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w)
        -- (iii) the residual-domination time floor / window:
        (aa : ℝ) (_ : 0 < aa) (_ : ∀ u ∈ U, aa ≤ u) (_ : ∀ u ∈ U, u ≤ T)
        -- (iv) the Levi source envelope package:
        (C : ℝ) (_ : LeviSeriesLocalData
            (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T)
        -- (v) the integrability Gaussian dominations + measurabilities:
        (wA CA wA2 CA2 : ℝ) (_ : 0 < wA) (_ : 0 ≤ CA) (_ : 0 < wA2) (_ : 0 ≤ CA2)
        (_ : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
            |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
              ≤ CA * gaussDdim (wA * τ) (0 - z))
        (_ : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
            |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
        (_ : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
        (_ : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
        (_ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
        (_ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
        -- (vi) the √ε sliver amplitude bundle:
        (τ₀ : ℝ)
        (_ : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
        (_ : ∀ m : ℕ, epsSeq m < aa / 2) (_ : ∀ m : ℕ, epsSeq m ≤ τ₀)
        -- (viii) the labelled atomic interchange carrier:
        (_ : ∀ u ∈ U, ∀ i : Fin n,
            Tendsto
              (fun m => pd (fun y => pd (fun x => heatConvFrozen
                  (vanVleckGatedWitness g gi hChr hK S a b)
                  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
                  (u - epsSeq m) x 0) i y) i 0)
              atTop (𝓝 (pd (fun y => pd (fun x => heatConv
                  (vanVleckGatedWitness g gi hChr hK S a b)
                  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
        -- (ix) the E-combination carries:
        (_ : ∀ (m : ℕ) (u : ℝ),
            DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
            = ∫ s in (0)..(u - epsSeq m), ∫ z,
                deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (_ : ∀ (m : ℕ) (u : ℝ),
            LapTrunc g gi (vanVleckGatedWitness g gi hChr hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
            = ∫ s in (0)..(u - epsSeq m), ∫ z,
                laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (_ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
            (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
            (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_ : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
            (fun s => ∫ z,
                laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume 0 (u - epsSeq m))
        (_ : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
            (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume 0 (u - epsSeq m)),
        DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U := by
  -- (T2) obtain the gate data `(a, b, S)` (+ `E₀ E₁` and the width-3/2 `hEdom` body) FROM GEOMETRY.
  obtain ⟨a, b, ha0, hab, S, E₀, E₁, hE₀, hE₁, hEdom⟩ :=
    QIQTH.CommonGateShell.hEdom_from_geometry g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, S, ?_⟩
  -- introduce the census carries AT the geometry-chosen gate.
  intro V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    aa haa hau hUTle C dataLevi wA CA wA2 CA2 hwA hCA hwA2 hCA2 hAdomHeat hAdom2
    hmeasLo hmeasHi hmeas2Lo hmeas2Hi τ₀ dataAmp hεaa hετ₀ hPd2conv
    hDa hLap hLapZ hEZ hLapS hES
  -- feed the assembly, with step (vii) supplied by the geometry-derived `hEdom` existential.
  exact QIQTH.LabelledRethreadV2.hDaLimLU_from_labelled_v2 g gi hChr hK S a b T U hUopen hn
    hK0 hframeK hinvF hdg0
    V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    aa haa hau hUTle C dataLevi wA CA wA2 CA2 hwA hCA hwA2 hCA2 hAdomHeat hAdom2
    hmeasLo hmeasHi hmeas2Lo hmeas2Hi τ₀ dataAmp hεaa hετ₀
    ⟨E₀, E₁, hE₀, hE₁, hEdom⟩
    hPd2conv hDa hLap hLapZ hEZ hLapS hES

end QIQTH.CensusGeometryThread

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CensusGeometryThread.hDaLimLU_from_geometry_census
