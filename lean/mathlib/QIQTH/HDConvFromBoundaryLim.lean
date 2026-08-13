/-
  HDConvFromBoundaryLim — J4-678: the W1-AGNOSTIC `hDConv` reduction — `DifferentiableAt`
  from `hDaLim` + `hBoundary`, with the `hDelta` slot internalised.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the hDelta scope, J4-678).  The diagonal-Duhamel `hDConv` `DifferentiableAt` slot of the
  restricted `a₁ = R/6` capstone is supplied by
      `ConvCarriesDischarge.hDConv_gatedWitnessN1_of_delta_final`  (J4-117),
  whose SOLE singular carry is the delta-family loc-unif limit
      `hDelta : TendstoLocallyUniformlyOn
          (fun m u => Da m u + ∫ z, Wit (u−(u−ε_m)) 0 z · B (u−ε_m) z 0)  D  atTop U`,
  bundled with the regular F1/F2 families `{hAdom, hAzero, hBdom, hMeasFII, hpar, htime, hR}`.

  `DeltaFamilyBoundary.hDelta_gatedWitnessN1_of_boundary` (J4-118) already reduces exactly this
  `hDelta` to TWO abstract carries — the `Da`-limit `hDaLim` and the delta-family BOUNDARY limit
      `hBoundary : TendstoLocallyUniformlyOn
          (fun m u => ∫ z, Wit (ε_m) 0 z · B (u−ε_m) z 0)  (fun u => B u 0 0)  atTop U`,
  with `D = fun u => DaLim u + B u 0 0`.

  ── ★ WHY THIS FILE (the W1 verdict).  There are TWO ways to feed the `hDConv` `hDelta` slot:

    (i)  the BOUNDARY-VALUE route `BoundaryAssembly.hDelta_gatedWitnessN1_final`, which discharges
         `hBoundary` from the near-diagonal parametrix factorisation
             `hAnear : Wit τ 0 z = gaussDdim τ z · (u₀ z + τ·u₁ z)`   (BASE-point Gaussian).
         ★ At the CONCRETE gate this `hAnear` is **FALSE**: the concrete witness is a CHART-IMAGE
         Gaussian `Wit τ 0 z = gaussDdim τ (W₀ z) · amp …`, peaked at `W₀ z ≠ z` — the documented
         W1 wall (`WideBoundaryLimDischarge`).  So route (i) cannot be instantiated at the witness;
         carrying its `hAnear` would be an UNSATISFIABLE hypothesis the firewall forbids.

    (ii) the W1-AGNOSTIC route of THIS FILE: carry `hBoundary` ABSTRACTLY (as the honest delta-family
         boundary limit, satisfiable via the chart-image change-of-variables approximate identity
         `ChartImageAIConcrete`, NOT via the false base-point `hAnear`), compose
         `hDelta_gatedWitnessN1_of_boundary` straight into `hDConv_gatedWitnessN1_of_delta_final`.

  WHAT LANDS.
    `hDConv_gatedWitnessN1_from_daLim_boundary` — the concrete `DifferentiableAt` `hDConv` slot for
    the gated van-Vleck witness, with the `hDelta` slot INTERNALISED and reduced to `{hDaLim,
    hBoundary}` on top of the regular F1/F2 families.  A pure term-level composition of the two
    banked suppliers; introduces NO `hAnear`, so it stays satisfiable at the concrete gate.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves nothing new about `R/6`.  This is a composition /
  limit-plumbing brick.  No `sorry`, no new axioms, no `expRho`, no `:= True`, no vacuous /
  conclusion-in-disguise hypothesis: `hDaLim`/`hBoundary` are the genuine two limit carries of the
  delta family (each strictly weaker than the `DifferentiableAt` conclusion), and the F1/F2 families
  are the banked regular carries.  No existing file is edited.
-/
import Mathlib
import QIQTH.DeltaFamilyBoundary

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-678 — THE W1-AGNOSTIC `hDConv` REDUCTION (`DifferentiableAt` FROM `hDaLim` + `hBoundary`).**
    The diagonal-Duhamel `hDConv` `DifferentiableAt` slot for the concrete gated van-Vleck witness
    `Wit := vanVleckGatedWitness g gi hC hK S a b`, `B := leviSeries (heatOp g gi Wit)`, with the sole
    singular `hDelta` carry of `hDConv_gatedWitnessN1_of_delta_final` INTERNALISED via
    `hDelta_gatedWitnessN1_of_boundary` — hence reduced to the two abstract limit carries

      • `hDaLim`   — the `Da`-limit `Da m → DaLim` loc-unif on `U` (the C3ε upper-limit-parameter side);
      • `hBoundary`— the delta-family BOUNDARY limit `∫ z, Wit (ε_m) 0 z · B (u−ε_m) z 0 → B u 0 0`
                     loc-unif on `U`,

    on top of the regular F1/F2 families `{hAdom, hAzero, hBdom, hMeasFII, hpar, htime, hR}`.

    Route: `hDelta_gatedWitnessN1_of_boundary hDaLim hBoundary` produces the `hDelta` slot in the
    EXACT shape (with `D := fun u => DaLim u + B u 0 0`), which is fed verbatim to
    `hDConv_gatedWitnessN1_of_delta_final`.

    ★ W1-AGNOSTIC.  Unlike `BoundaryAssembly.hDelta_gatedWitnessN1_final`, this carries `hBoundary`
    ABSTRACTLY and introduces NO base-point near-diagonal factorisation `hAnear` — which is FALSE at
    the concrete gate (the chart-image-Gaussian W1 wall).  `hBoundary` is the honest delta-family
    boundary limit, satisfiable via the chart-image change-of-variables approximate identity, never
    the conclusion.  ⚠ CONDITIONAL on `{hDaLim, hBoundary}` + the F1/F2 families.  NOT `a₁ = R/6`. -/
theorem hDConv_gatedWitnessN1_from_daLim_boundary (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hC hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hC hK S a b τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (Da : ℕ → ℝ → ℝ)
    (hpar : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasDerivAt (fun a' => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) a' (u - epsSeq m) 0 0)
          (Da m u) u)
    (htime : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasDerivAt (fun tt => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u tt 0 0)
          (∫ z, vanVleckGatedWitness g gi hC hK S a b (u - (u - epsSeq m)) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (u - epsSeq m) z 0)
          (u - epsSeq m))
    (hR : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasFDerivAt (fun p : ℝ × ℝ =>
            heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) p.1 p.2 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) p.1
                (u - epsSeq m) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u p.2 0 0)
          (0 : (ℝ × ℝ) →L[ℝ] ℝ) (u, u - epsSeq m))
    (DaLim : ℝ → ℝ)
    (hDaLim : TendstoLocallyUniformlyOn Da DaLim Filter.atTop U)
    (hBoundary : TendstoLocallyUniformlyOn
        (fun m u => ∫ z : Point n, vanVleckGatedWitness g gi hC hK S a b (epsSeq m) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (u - epsSeq m) z 0)
        (fun u => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) u 0 0)
        Filter.atTop U) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hC hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u 0 0) t :=
  hDConv_gatedWitnessN1_of_delta_final g gi hC hK S a b t T hT U hUopen htU hUpos hUT
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hMeasFII Da hpar htime hR
    (fun u => DaLim u
      + leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) u 0 0)
    (hDelta_gatedWitnessN1_of_boundary g gi hC hK S a b U Da DaLim hDaLim hBoundary)

end QIQTH.HeatResidualBound

/-! ### Axiom audit. -/

section AxiomChecks

#print axioms QIQTH.HeatResidualBound.hDConv_gatedWitnessN1_from_daLim_boundary

end AxiomChecks
