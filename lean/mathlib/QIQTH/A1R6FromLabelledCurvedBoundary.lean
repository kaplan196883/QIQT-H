/-
  A1R6FromLabelledCurvedBoundary — J4-521: the boundary-threaded curved-signature a₁ capstone.

  Built ON TOP of J4-520's `A1R6FromLabelledCurvedGauge.a1_R6_from_labelled_curved_gauge` (which already
  removed BOTH flat-only binders — the LINEAR `hraw` via J4-519's quadratic `hgate`, and the neighbourhood
  frame `hframeK : ∀ q ∈ K, g q = δ` via J4-520's pointwise `gauge_from_pointwise`).  This file removes the
  THIRD pending capstone item, the OPAQUE boundary limit member (Section H)
      `hBoundaryLim : Tendsto (fun m => BoundaryTrunc … m t) atTop (𝓝 (leviSeries … t 0 0))`
  by SUPPLYING it from the banked `EnvelopeWiringLocUnif.hBoundaryLim_DONE` — the (E1)+(E2)+(E3) assembly
  whose conclusion type, at `S := constGate g gi hChr hK c` and `hC := hChr`, matches the capstone's
  `hBoundaryLim` binder VERBATIM.

  ── THE SWAP.  The single opaque limit binder `hBoundaryLim` is REPLACED by the concrete, curved-valid,
  individually-satisfiable input list that `hBoundaryLim_DONE` carries in its place:
    • the van-Vleck heat-envelope data — `hEbound` (width-`κ` Gaussian envelope), `hInt`
      (`IterConvIntegrableW`), `hEmeas` (joint strong measurability), `hbase` (joint continuity on
      compact strips), the summable Levi tail `env`/`hu`/`hbound`, `hf_meas`;
    • the RNC exp-chart GEOMETRY bundles `hgeoBundle` / `hfgBundle` — QUADRATIC remainder
      `‖exp v − q − v‖ ≤ C‖v‖²` (curved-valid: `C_Dw` free, flat only forces `C_Dw = 0`);
    • gate activation `rS`/`hKball`/`hSact`, witness-slice measurability `hWslice`, the amplitude
      Gaussian domination `hDomB`;
    • ★ the window floor `ε₀`/`hε₀`/`hε₀t`/`hεbnd` (satisfiable by `ε₀ = 1 = epsSeq 0`, diffusion
      time `t > 1`);
    • ★ and — crucially — the SAME `LeviSeriesLocalData` package the capstone ALREADY carries
      (`dataLevi : LeviSeriesLocalData (heatOp …) CLevi T`) is REUSED as `hBoundaryLim_DONE`'s
      `hLocal`.  No new Levi package: `hLocal.hFenv` feeds (E1) → the single window-uniform `Cf`;
      `hLocal.hFmeas` feeds (E2) → the moving-slice measurability.

  `htT : t ≤ T` is derived from `hUT t htU`; `hgdet0 : det (g 0) = 1` is derived from the pointwise value
  gauge `hg0`.  Every replacement input is curved-valid (none forces `g = δ`), so the opaque boundary carry
  is GENUINELY reduced to the (curved-valid) analytic + joint-continuity + geometry data — not relabelled,
  no flatness reintroduced.

  DELIVERABLE:
  •  `a1_R6_from_labelled_curved_boundary` ★ — the capstone with all three flat-only/pending capstone
     items (`hraw`, `hframeK`, `hBoundaryLim`) resolved from the SIGNATURE — 3 of 3.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  A 3-of-3 curved-SIGNATURE capstone makes the
  flat-only obstruction GONE from the signature (coefficient-neutral — the `R/6` lives solely in
  `transportCoeff`/`htr`, untouched).  It does NOT derive curved `a₁`: the genuine analytic frontier
  (positive-time continuity of the iterated Levi convolutions feeding `hBoundaryLim_DONE`), the
  `htr`/`hGauss` geometric bridges, and a full RNC curved witness of the antecedent all REMAIN carried.
  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, no existing file edited, nothing
  committed.
-/
import Mathlib
import QIQTH.A1R6FromLabelledCurvedGauge
import QIQTH.EnvelopeWiringLocUnif

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.HEmeasRecon QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami
open QIQTH.CConvV2DerivRep QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.LeviSeriesLocalData QIQTH.GaussianWidthTolerant QIQTH.HeatKernelA1
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.NCRiemannTwoJet QIQTH.GlobalRawBoundFacade QIQTH.HDuhamelExportRethread
open QIQTH.HDConvGateThreading QIQTH.CConvV2Facade QIQTH.A1R6CoreAtGate
open QIQTH.A1R6SlotAdapters QIQTH.HDerivConvComposition
open QIQTH.RadialDistance QIQTH.LabelledRethreadV2 QIQTH.A1R6FromLabelled
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.ResidueBound QIQTH.ExpMap
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.A1R6FromLabelledCurvedBoundary

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-- **J4-521 — `a1_R6_from_labelled_curved_boundary` — THE BOUNDARY-THREADED CURVED-SIGNATURE FACADE.**
    Identical to `A1R6FromLabelledCurvedGauge.a1_R6_from_labelled_curved_gauge` (both flat-only binders
    already removed) with the THIRD pending capstone item — the OPAQUE boundary limit member
    `hBoundaryLim` (Section H) — REMOVED: it is supplied INTERNALLY from
    `EnvelopeWiringLocUnif.hBoundaryLim_DONE` at `S := constGate g gi hChr hK c`, `hC := hChr`, whose
    conclusion matches the capstone binder verbatim.  In its place the signature carries the concrete,
    curved-valid analytic + joint-continuity + RNC-geometry data (`hEbound`/`hInt`/`hEmeas`/`hbase`,
    `env`/`hu`/`hbound`, `hf_meas`, `hgeoBundle`/`hfgBundle`, gate activation, `hWslice`, `hDomB`) plus
    the window floor `ε₀`, and REUSES the capstone's existing `dataLevi : LeviSeriesLocalData … CLevi T`
    as the boundary assembly's `hLocal`.  `htT`/`hgdet0` derived internally.  Same conclusion (the a₁
    two-jet at the constant-radius gate).  All three flat-only/pending capstone items now resolved from
    the signature — 3 of 3.  ⚠ NOT `a₁ = R/6` (still CONDITIONAL: iterE positive-time continuity, the
    `htr`/`hGauss` bridges, and a full RNC curved witness remain — see file header). -/
theorem a1_R6_from_labelled_curved_boundary
    -- ═══ SECTION A — base geometry, gate, window, and window parameters (shared everywhere) ═══
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (hn : 1 ≤ n)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    -- ═══ SECTION B — gauge / smoothness (core + `htr_adapter`); `hGauss` is LABELLED ═══
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i))  -- ★ LABELLED
    -- ═══ SECTION C — the constant-radius package facts (satisfiable via `constRadius_package_and_S1`) ═══
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0))
    (hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
    -- ═══ SECTION D — the geometry-raw gauge facts for `hDaLimLU_from_hgate_gauge` (hframeK REMOVED) ═══
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    -- ═══ SECTION E — the W2 differentiation-under-∫ family (SHARED: labelled-Da AND Duhamel-FULL) ═══
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
    (hFmeas_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0‖
            ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) w)
    -- ═══ SECTION F — residual window floor (SHARED: `hDaLimLU_from_hgate_gauge` `aa` + `…_FULL` `aT`) ═══
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u)
    -- ═══ SECTION G — `hDaLimLU_from_hgate_gauge` analytic piles (Levi source, dominations, sliver) ═══
    (CLevi : ℝ) (dataLevi : QIQTH.LeviSeriesLocalData.LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) CLevi T)
    (wA CA wA2 CA2 : ℝ) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2 : 0 ≤ CA2)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2 : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeas2Hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (τ0A : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK (constGate g gi hChr hK c) a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) i T τ0A)  -- ★ hard field = hD2Hexpand (LABELLED)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ0A : ∀ m : ℕ, epsSeq m ≤ τ0A)
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (constGate g gi hChr hK c q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))  -- ★ CURVED-VALID quadratic width-4/3 gate carry
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u x 0) i y) i 0)))  -- ★ LABELLED
    (hDaEq : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (u - s)
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    -- ═══ SECTION H — `truncatedDuhamelCore_AT_GATE_FULL` specific census (hBoundaryLim REMOVED — see Section L) ═══
    (hgiMem : MemGaugeGi (n := n) gi) (hΓMem : MemGaugeGamma (n := n) g gi)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_lo : MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))))
    -- ═══ SECTION I — the F2 / `hDConv` regularity family (SHARED: `…_FULL` AND `a1_R6_slots_AT_GATE`) ═══
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ cc : ℝ, 0 < cc ∧ ∀ u ∈ U, cc ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (u - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      HasDerivAt (fun cc => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) cc)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- ═══ SECTION J — frozen/moving envelope list (SHARED: `…_FULL` AND `hbdryLU_CONCRETE`) ═══
    (ρ lam CW Cf τ0fr : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ0fr : 0 < τ0fr)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ0fr → ∀ z,
        |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop,
        ∫ z, |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb, ∀ z ∈ Metric.ball (0 : Point n) δ,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)
            - leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb, ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)
            - leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    -- ═══ SECTION K — the `hCConv` sliver census for `a1_R6_slots_AT_GATE` ═══
    (uSet : Set (Point n)) (hu_open : IsOpen uSet) (hu0 : (0 : Point n) ∈ uSet)
    (hlin : ∀ x ∈ uSet, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK (constGate g gi hChr hK c) a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z,
          witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet)
    -- ═══ SECTION L — ★ the boundary-assembly input list (REPLACES the opaque `hBoundaryLim`) ═══
    -- Supplied to `EnvelopeWiringLocUnif.hBoundaryLim_DONE` at `S := constGate g gi hChr hK c`;
    -- `dataLevi` (Section G) is REUSED as its `hLocal`; `htT`/`hgdet0` derived internally.
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (κ Cc : ℝ) (hκ : 0 < κ) (hCc0 : 0 ≤ Cc)
    (t₁ t₂ R : ℝ) (ht₁pos : 0 < t₁) (hlt₁ : t₁ < t) (hlt₂ : t < t₂) (hR : 0 < R)
    (hEbound : ∀ τ p q, 0 < τ →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ Cc * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) κ 0 Cc)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) q.1 q.2.1 q.2.2))
    (hbase : ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
        ContinuousOn (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) p.1 p.2 0)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hgeoBundle : ∀ w ∈ K, ∃ ρc cw ρ₀w C_Dw : ℝ,
        0 < ρc ∧
        ContDiffOn ℝ 2 (uniformInverseChart g gi hChr hK w) (Metric.ball w ρc) ∧
        (constGate g gi hChr hK c) w = uniformFlowExp g gi hChr hK w '' Metric.ball 0 cw ∧
        0 < cw ∧ cw < ρ₀w ∧ 0 ≤ C_Dw ∧
        (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀w →
          ‖uniformFlowExp g gi hChr hK q v - q - v‖ ≤ C_Dw * ‖v‖ * ‖v‖) ∧
        closure (uniformFlowExp g gi hChr hK w '' Metric.ball 0 cw)
          ⊆ uniformFlowExp g gi hChr hK w '' Metric.closedBall 0 cw ∧
        cw + C_Dw * cw * cw < ρc)
    (hfgBundle : ∀ w ∈ K, ∀ s₁ s₂ : ℝ, 0 < s₁ →
        ∃ Rg cw ρ₀w C_Dw : ℝ,
          0 < Rg ∧
          ContinuousOn (fun p : ℝ × Point n =>
              heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) p.1 p.2 w)
            (Set.Icc s₁ s₂ ×ˢ Metric.closedBall w Rg) ∧
          (constGate g gi hChr hK c) w = uniformFlowExp g gi hChr hK w '' Metric.ball 0 cw ∧
          0 < cw ∧ cw < ρ₀w ∧ 0 ≤ C_Dw ∧
          (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀w →
            ‖uniformFlowExp g gi hChr hK q v - q - v‖ ≤ C_Dw * ‖v‖ * ‖v‖) ∧
          closure (uniformFlowExp g gi hChr hK w '' Metric.ball 0 cw)
            ⊆ uniformFlowExp g gi hChr hK w '' Metric.closedBall 0 cw ∧
          (∀ v : Point n, ‖v‖ ≤ cw →
            uniformInverseChart g gi hChr hK w (uniformFlowExp g gi hChr hK w v) = v) ∧
          b + C_Dw * b * b < Rg)
    (env : ℕ → ℝ) (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
        p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
        ‖(-1 : ℝ) ^ (k + 1)
            * QIQTH.LeviSeries.iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (k + 1) p.1 p.2 0‖
          ≤ env k)
    (hf_meas : Measurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) t z 0))
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ (constGate g gi hChr hK c) z)
    (hWslice : ∀ τ : ℝ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z) volume)
    (lamB τ0B CWB : ℝ) (hlamB : 0 < lamB) (hτ0B : 0 < τ0B) (hCWB : 0 ≤ CWB)
    (hDomB : ∀ τ, 0 < τ → τ ≤ τ0B → ∀ z,
        |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z| ≤ CWB * gaussDdim (lamB * τ) z)
    (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀t : ε₀ < t) (hεbnd : ∀ m, epsSeq m ≤ ε₀) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- ── derived: `t ≤ T` from the window, and `det (g 0) = 1` from the pointwise value gauge `hg0`.
  have htT : t ≤ T := hUT t htU
  have hgdet0 : Matrix.det (g (0 : Point n)) = 1 := by
    have hmat : (g (0 : Point n)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      funext i j
      rw [hg0 i j, Matrix.one_apply]
    rw [hmat, Matrix.det_one]
  -- ── J4-521: SUPPLY the opaque `hBoundaryLim` from the banked envelope assembly.
  --    `dataLevi` (Section G) is REUSED as `hLocal`; its `hFenv` feeds (E1), its `hFmeas` feeds (E2).
  have hBoundaryLim := QIQTH.EnvelopeWiringLocUnif.hBoundaryLim_DONE
    g gi hChr hK h0Kmem hg hgiC hgpos (constGate g gi hChr hK c) a b ha hab hgdet0
    κ Cc hκ hCc0 t₁ t₂ R t ht₁pos hlt₁ hlt₂ hR
    hEbound hInt hEmeas hbase hgeoBundle hfgBundle env hu hbound hf_meas
    rS hrS hKball hSact hWslice lamB τ0B CWB hlamB hτ0B hCWB hDomB
    CLevi T ε₀ hε₀ hε₀t htT hεbnd dataLevi
  -- ── forward to the J4-520 curved-gauge capstone with the constructed boundary member.
  exact QIQTH.A1R6FromLabelledCurvedGauge.a1_R6_from_labelled_curved_gauge
    g gi hChr hK hK0 t T ht hT hn U hUopen htU hUpos hUT a b c C ha hab hbc hCnn
    hg hgsymm hgiC hgpos hg0 hgi hΓ hdg0 hsrc hGauss
    hpkgBound hmemS0 hopenS0 hS1 hinvF
    V hVopen hV0 snb hsnb hQ1 hFmeas_W2 hFint_W2 hF'meas_W2 bnd hbdd_W2 hbound_W2 hdiff
    aa haa hau CLevi dataLevi wA CA wA2 CA2 hwA hCA hwA2 hCA2 hAdomHeat hAdom2
    hmeasLo hmeasHi hmeas2Lo hmeas2Hi τ0A dataAmp hεaa hετ0A P hP hgate hPd2conv
    hDaEq hLap hLapZ hEZ hLapS hES
    hBoundaryLim hgiMem hΓMem hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L hE₀ hE₁ hC_L hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ0fr ta tb hρ hlam hCW hτ0fr hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
    uSet hu_open hu0 hlin sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb
    hbulkderiv hbulk_tendsto hsliver hcont

#check @a1_R6_from_labelled_curved_boundary

end QIQTH.A1R6FromLabelledCurvedBoundary

/-! ## Axiom check — the boundary-threaded curved-signature facade is std-3
    (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.A1R6FromLabelledCurvedBoundary
#print axioms a1_R6_from_labelled_curved_boundary
end AxiomChecks
