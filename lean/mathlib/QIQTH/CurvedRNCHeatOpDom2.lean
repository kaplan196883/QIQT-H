import QIQTH.WideWitnessAmplitude
import QIQTH.NormalFormDischarge
import QIQTH.CurvedRNCBaseWitnessDomAdom

/-!
# J4-537 — the CURVED second-`x`-derivative Gaussian envelope (`hAdom2`'s HONEST sibling)

The `a₁ = R/6` trace capstone `A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary`
exposes the binder

```
hAdom2 : ∀ i τ, 0 < τ → τ ≤ T → ∀ z,
    |witnessSecondXDeriv g gi hChr hK (constGate …) a b i τ z| ≤ CA2 · gaussDdim (wA2·τ) (0 − z)
```

with `CA2, wA2` FIXED single constants over the whole window `(0, T]`.

## ⚠ Why this brick does NOT produce that exact binder

The codebase already establishes (in `CensusDominations` (D3) and `CappedAdom2Audit`) that the clean
single-constant whole-time `hAdom2` shape is **GENUINELY FALSE** at the concrete van-Vleck witness —
not merely unproven.  The true second-`x`-derivative envelope carries a `τ⁻¹` prefactor
(`WideWitnessAmplitude.WideAmplitudeData.second_domination`):

```
|witnessSecondXDeriv … i τ z| ≤ C · τ⁻¹ · gaussDdim (lam·τ) z          (0 < τ ≤ τ₀, on the gate ball)
```

and `τ⁻¹` blows up as `τ → 0` (at `z = 0` the value grows like `τ^{-1-n/2}` against the demanded
`τ^{-n/2}`).  No fixed `CA2`, `wA2` can absorb it.  The ONLY honest consequences are the per-`m`
lower-capped family (already grounded, `HAdom2capGrounding.hAdom2cap_grounded`, J4-461) and the crude
`τ⁻¹` envelope itself.  Manufacturing the clean `hAdom2` for the genuinely-curved witness would be
UNSOUND (a false proposition).  Consulted `gpt-5.6-sol`, which confirmed: the clean `hAdom2` is false,
not unavailable; the honest increment is the curved crude-`τ⁻¹` `second_domination` instantiation, and
the result stays conditional on the carried second-jet bundle.

## What this brick DELIVERS (the honest curved sibling of J4-535 `hAdom`)

For the genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`, `Ric(0) = (n−1)Kδ ≠ 0`), the
TRUE second-`x`-derivative Gaussian envelope on the fixed-flow gate ball, with the **gate geometry
DISCHARGED** exactly as J4-535 discharged its `GateSqControl`:

* the fixed radial-cutoff / width-gap gate record `FixedFlowGateData` is BUILT for `g^K` from ONLY the
  mainline `hChr` carry via `InverseChartNormalJets.FixedFlowGateData.of_geometry` (the coarse
  inverse-chart near-isometry `chartW0_nearIsometry` ⟶ radial width gate);
* the ONLY carried residuals are the amplitude sup-bound `hAmp0` and the CHART-IMAGE second-jet two-term
  envelope `hSecondEnv` — the genuine geometric second-derivative content isolated by the banked
  `SliverCConvBatch.witnessSecondXDeriv_chartImage_expand` (per `CensusDominations` (D3), this is a real
  additional carry, NOT reducible to `hChr`+`hw`, unlike the first-derivative J4-535 case).

Route: assemble a `WideWitnessAmplitude.WideAmplitudeData` for `g^K` (with `D` discharged via
`of_geometry`) and apply the banked `WideAmplitudeData.second_domination`.

## Honest scope

`K < 0` is genuinely curved (`curvedRNCMetric_ricci_trace_diag_ne`; the radial-squeeze satisfiability is
re-exported below — the underlying budget tolerates a real contraction, NOT the flat `W z = ±z`).  This
does **not** derive the coefficient: `a₁ = R/6` still needs the whole heatOp/Levi/error-kernel
domination pile (`hEdom`/`hFdom`/`hgate` + `hEbound`/`hInt` Levi convergence), the Duhamel assembly,
and coefficient extraction, and — because the clean single-constant `hAdom2` is false — remains
**CONDITIONAL and effectively FLAT-ONLY**.  NOT `a₁ = R/6`.
-/

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.VanVleck QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.ResidueBound
open QIQTH.FlatHeatEquation QIQTH.InverseChartNormalJets QIQTH.WideWitnessAmplitude
open scoped BigOperators

namespace QIQTH.CurvedRNCHeatOpDom2

variable {n : ℕ}

/-- **The `g^K` fixed-flow gate record, discharged from `hChr` alone.**  The curved instantiation of
    `FixedFlowGateData.of_geometry`: the ordered radial-cutoff radii `0 < a < b < r`, the width-gap
    `(η, lam)` with `η < 1 < lam`, `1/lam < 1−η`, and the proved inverse-chart width gate, ALL built for
    `g^K = curvedRNCMetric K` from the coarse near-isometry — needing only the mainline `hChr` carry. -/
noncomputable def curvedGate (K : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) :
    FixedFlowGateData (curvedRNCMetric K) (curvedRNCInv K) hChr hKset :=
  FixedFlowGateData.of_geometry (curvedRNCMetric K) (curvedRNCInv K) hChr hKset

/-- **★★★ J4-537 — `curvedRNC_witnessSecondXDeriv_dom_crude`.**  THE CURVED SECOND-`x`-DERIVATIVE
    GAUSSIAN ENVELOPE (the HONEST sibling of the false clean `hAdom2`).  For the genuinely-curved witness
    `g^K = curvedRNCMetric K` (`K < 0`), a gate function `S`, a coordinate line `i`, a positive time cap
    `τ₀`, and the carried amplitude sup `hAmp0` + chart-image second-jet envelope `hSecondEnv`, the true
    `τ⁻¹` second-derivative Gaussian domination holds on the DISCHARGED fixed-flow gate ball `z ∈ Kset`,
    `‖z‖ < (curvedGate …).r`:

    `∃ C > 0, ∀ τ ∈ (0,τ₀], ∀ z ∈ Kset, ‖z‖ < r,
        |witnessSecondXDeriv g^K … i τ z| ≤ C · τ⁻¹ · gaussDdim (lam·τ) z`.

    The gate record `FixedFlowGateData` is built for `g^K` from the mainline `hChr` alone
    (`of_geometry`, mirroring how J4-535 discharged its `GateSqControl`); the sole carried residuals are
    the amplitude sup `hAmp0` and the second-jet envelope `hSecondEnv` (the genuine geometric
    second-derivative content, `CensusDominations` (D3)).  Route: `WideAmplitudeData.second_domination`.

    ⚠ This is the `τ⁻¹` envelope, NOT the clean single-constant `hAdom2` (which is FALSE at the concrete
    witness — the `τ⁻¹` prefactor blows up as `τ → 0`).  NOT `a₁ = R/6`; the coefficient stays
    CONDITIONAL and effectively FLAT-ONLY. -/
theorem curvedRNC_witnessSecondXDeriv_dom_crude
    (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset)
    (S : Point n → Set (Point n)) (i : Fin n)
    (τ₀ M B₀ B₁ : ℝ) (hτ₀ : 0 < τ₀) (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ Kset,
        ‖z‖ < (curvedGate K hChr hKset).r →
      |chartFieldAmp (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
          (curvedGate K hChr hKset).a (curvedGate K hChr hKset).b τ z 0| ≤ M)
    (hSecondEnv : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ Kset,
        ‖z‖ < (curvedGate K hChr hKset).r →
      |witnessSecondXDeriv (curvedRNCMetric K) (curvedRNCInv K) hChr hKset S
          (curvedGate K hChr hKset).a (curvedGate K hChr hKset).b i τ z|
        ≤ (B₀ + B₁ * (rncRadialSq z / τ)) * τ⁻¹
            * gaussDdim τ (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ Kset,
        ‖z‖ < (curvedGate K hChr hKset).r →
      |witnessSecondXDeriv (curvedRNCMetric K) (curvedRNCInv K) hChr hKset S
          (curvedGate K hChr hKset).a (curvedGate K hChr hKset).b i τ z|
        ≤ C * τ⁻¹ * gaussDdim ((curvedGate K hChr hKset).lam * τ) z := by
  -- Assemble the wide-amplitude data bundle for `g^K`, with the gate record DISCHARGED via `of_geometry`
  -- and only `hAmp0` / `hSecondEnv` carried; then apply the banked crude-`τ⁻¹` second domination.
  let P : WideAmplitudeData (curvedRNCMetric K) (curvedRNCInv K) hChr hKset S i :=
    { D := curvedGate K hChr hKset
      τ₀ := τ₀, M := M, B₀ := B₀, B₁ := B₁
      hτ₀ := hτ₀, hM := hM, hB₀ := hB₀, hB₁ := hB₁
      hAmp0 := hAmp0, hSecondEnv := hSecondEnv }
  exact P.second_domination

/-- **★ J4-537 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  Re-exports the J4-534/535
    radial-squeeze witness: the near-isometry budget underlying the discharged gate is inhabited by a
    GENUINELY radially-distorting map `W z = c·z`, `c = 4/5 ≠ ±1`, for every `z`.  So the curved
    second-derivative envelope tolerates the real curved-normal-coordinate contraction and is NOT the
    flat `W z = ±z`.  Curved-inhabited.  NOT `a₁ = R/6`. -/
theorem curvedRNC_witnessSecondXDeriv_dom_crude_curved_satisfiable :
    ∃ c : ℝ, c ≠ 1 ∧ c ≠ -1 ∧ ∀ z : Point n,
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (fun i => c * z i) :=
  QIQTH.CurvedRNCBaseWitnessDomCollar.curvedRNC_baseWitness_dom_collar_curved_satisfiable

end QIQTH.CurvedRNCHeatOpDom2

section AxiomChecks
open QIQTH.CurvedRNCHeatOpDom2
#print axioms curvedRNC_witnessSecondXDeriv_dom_crude
#print axioms curvedRNC_witnessSecondXDeriv_dom_crude_curved_satisfiable
end AxiomChecks
