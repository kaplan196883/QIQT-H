/-
  FixedFChartImageAI — J4-275: the fixed-`f` chart-image approximate-identity COMPLETION —
  discharging the base-varying CoV bundle (M1–M4) and the chart-image measurability into the
  J4-271 conditional capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the W1 wall of the a₁ = R/6 campaign).  The structural side of the chart-image
  approximate identity is complete:
    • `QIQTH.ChartImageAIConcrete.chartImage_approx_identity_conditional` (J4-271) proves
          `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`
      CONDITIONAL on TWELVE inputs: the base-varying (`Wbv`) CoV bundle slots
      (`hfd`/`hinj`/`hV`/`hJpos` on `ball 0 ρ`), the gate-activation `hGgate`, the τ-uniform support
      `hSupp`, the chart-image measurability/neighbourhood `hΩmeas`/`hΩnhds` for
      `Ω := Wbv '' ball 0 ρ`, and the Layer-C moving-integrand trio `hmeas`/`hbound`/`hlocal`.
    • `QIQTH.TerminalVelC2.baseVaryingIFTPackage_unconditional` (J4-274) produces the base-varying
      CoV bundle UNCONDITIONALLY (from only `hC`, `hK`, `K ∈ 𝓝 0`):
          `∃ ρ>0, ∃ V f', MeasurableSet (ball 0 ρ) ∧ M1(hfd) ∧ M2(hinj) ∧ M3(hV) ∧ M4(hJpos)
              ∧ (Ω ∈ 𝓝 0)`.

  ── WHAT LANDS HERE (honest composition; the ★ PLUG ★).
    • `chartImage_measurableSet_of_bundle` — ★ FULLY DISCHARGED.  The chart image
      `Ω = Wbv '' (ball 0 ρ)` is `MeasurableSet` whenever the base-varying chart `Wbv` is
      (within-)differentiable and injective on the measurable ball.  Route: Lusin–Souslin —
      `HasFDerivWithinAt ⟹ ContinuousOn`, and a `ContinuousOn` + `InjOn` map out of a measurable set
      in a finite-dim (Polish) space is a `MeasurableEmbedding` (`ContinuousOn.measurableEmbedding`),
      whose range `= Ω` is Borel (`MeasurableEmbedding.measurableSet_image`).  This is the exact
      pattern banked in `ConcreteGateInstantiation`.  DISCHARGES the `hΩmeas` slot.
    • `chartImage_approx_identity_of_amp` — ★★ THE PLUG.  The fixed-`f` W1 limit-value member with the
      base-varying CoV bundle (M1–M4) AND the chart-image measurability `hΩmeas` FULLY REMOVED from the
      hypothesis surface: obtaining the J4-274 bundle produces a concrete `(ρ, V, f')`, discharges
      M1–M4 and `hΩnhds` from the bundle and `hΩmeas` from the Lusin–Souslin lemma, and feeds the
      J4-271 conditional capstone.  The result is a Tendsto that is CONDITIONAL ONLY on the FIVE
      remaining honest carries (gate/support/trio), stated as an implication under the existential
      `(ρ, V, f')` the bundle produces.

  ── THE FINAL CARRY LIST of `chartImage_approx_identity_of_amp` (each a genuine, simultaneously
     satisfiable input, STRICTLY WEAKER than the conclusion — none is the Tendsto or trivially yields
     it).  For the produced `(ρ, V, f')`:
       (C1) `hGgate : ∀ z ∈ ball 0 ρ, z ∈ K ∧ 0 ∈ S z`  — the witness gate is active on the CoV ball.
             SATISFIABLE: `0 ∈ K` (interior, `h0Kmem`) and the true witness gate `S` contains `0`
             on a neighbourhood of the base `0`; choose `ρ` no larger than that gate radius (the
             bundle's `ρ` can only need to SHRINK, and Layer A is monotone under shrinking the ball —
             see the "MISMATCH INTEL" note below).
       (C2) `hSupp : ∀ τ z, z ∉ ball 0 ρ → Wit τ 0 z = 0`  — the witness vanishes off the ball, uniformly
             in `τ`.  SATISFIABLE by the wide off-gate vanishing (`gatedKernel_apply_of_notMem` is
             EVERYWHERE, τ-uniform) PROVIDED the witness's gate `S` is contained in `ball 0 ρ`; if the
             gate `S` is WIDER than `ball 0 ρ`, this is the honest ball/annulus split residual (below).
       (C3) `hmeas` — a.e.-measurability of the moving integrand `g τ w := A τ (V w)·f(V w)/|det f'(V w)|`
             on `Ω`, eventually in `τ`.  SATISFIABLE from measurability of `V` on `Ω` (the CoV inverse),
             the amplitude, `f`, and `|det| > 0`.
       (C4) `hbound` — a.e.-boundedness of `g τ` on `Ω`, eventually in `τ`.  SATISFIABLE from the
             BASE-SLOT amplitude sup-bound + `|f|` bound + `|det| ≥ c > 0`.
       (C5) `hlocal` — the JOINT `(τ,w) → (0⁺,0)` limit `g τ w → f 0`.  SATISFIABLE from the amplitude
             joint centre limit + `V w → 0` + `f` continuous at `0` + `|det f'(V w)| → 1`.
    ⚠ The trio `hmeas`/`hbound`/`hlocal` reduces to BASE-SLOT amplitude facts
    (`chartFieldAmp … τ (V w) 0` as a function of the BASE `V w`, field fixed at `0`).  The BANKED
    amplitude bank (`AmplitudeFamilyDischarge.amp_bound_*`, `amp_contDiffAt_*`) is FIELD-SLOT
    (`p ↦ chartFieldAmp … z p` at fixed base `z`).  Per the J4-271 ORIENTATION VERDICT, base-slot
    amplitude regularity is NOT banked (the same base-varying obstruction that the CoV bundle just
    solved for the GAUSSIAN argument, now for the AMPLITUDE argument), so the trio is CARRIED, not
    forced.  These are the honest, satisfiable residuals toward the moving-`f`/`hBoundaryLim` step.

  ── MISMATCH INTEL (bankable, for the next brick).  The J4-271 capstone requires the witness to
    VANISH off `ball 0 ρ` (`hSupp`) with the SAME `ρ` as the CoV ball.  The witness's own gate `S`
    (radius, say, `ρ_S`) is generally NOT tied to the bundle's CoV radius `ρ` (which is fixed by the
    IFT/exp-injectivity radius).  If `ρ_S > ρ`, `hSupp` at radius `ρ` FAILS (the witness is nonzero on
    the annulus `ball 0 ρ_S \ ball 0 ρ`).  The honest fix is the BALL/ANNULUS SPLIT already present in
    `WideBoundaryLimDischarge`: rewrite the ambient integral as (ball part) + (annulus part), send the
    ball part through this composition, and show the annulus part `→ 0` (the Gaussian tail off
    `ball 0 ρ` times the wide amplitude bound).  This file does NOT perform that split — it carries
    `hSupp` at the CoV radius, honestly flagged; the split is the identified next step.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  These are analytic composition
  bricks.  No `sorry` (prose only), no new axioms, no `:= True`, no vacuous / unsatisfiable /
  conclusion-in-disguise hypotheses: M1–M4 and `hΩmeas` are DISCHARGED (removed), and the five carries
  are the standard change-of-variables + approximate-identity inputs, each strictly weaker than the
  Tendsto conclusion.  No existing file is edited.
-/
import Mathlib
import QIQTH.ChartImageAIConcrete
import QIQTH.TerminalVelC2

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ChartImageApproxIdentity QIQTH.ChartGaussianChangeVar
open QIQTH.ChartImageAIConcrete QIQTH.TerminalVelC2
open scoped Topology

namespace QIQTH.FixedFChartImageAI

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The chart-image measurability (Lusin–Souslin) — discharging `hΩmeas`. -/

/-- **★ `chartImage_measurableSet_of_bundle` — the chart image is `MeasurableSet`.**  For the
    base-varying chart `Wbv : z ↦ uniformInverseChart g gi hC hK z 0`, if `Wbv` is
    within-differentiable (`hfd`) and injective (`hinj`) on the ball `ball 0 ρ`, then the chart image
    `Ω := Wbv '' (ball 0 ρ)` is Borel.

    ROUTE (Lusin–Souslin, the banked `ConcreteGateInstantiation` pattern).  `HasFDerivWithinAt` gives
    `ContinuousWithinAt`, hence `Wbv` is `ContinuousOn (ball 0 ρ)`; a `ContinuousOn` + `InjOn` map out
    of a measurable set in a finite-dimensional (Polish, second-countable) space is a
    `MeasurableEmbedding` of the restriction (`ContinuousOn.measurableEmbedding`), whose range —
    equal to `Ω` — is `MeasurableSet` (`MeasurableEmbedding.measurableSet_image`).  DISCHARGES the
    `hΩmeas` slot of the J4-271 conditional capstone.  NOT `a₁ = R/6`. -/
theorem chartImage_measurableSet_of_bundle
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (ρ : ℝ)
    (f' : Point n → (Point n →L[ℝ] Point n))
    (hfd : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
        (Metric.ball (0 : Point n) ρ) z)
    (hinj : Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ)) :
    MeasurableSet
      ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)) := by
  set Wbv : Point n → Point n := fun z => uniformInverseChart g gi hC hK z 0 with hWbv
  have hcont : ContinuousOn Wbv (Metric.ball (0 : Point n) ρ) :=
    fun z hz => (hfd z hz).continuousWithinAt
  have hemb : MeasurableEmbedding ((Metric.ball (0 : Point n) ρ).restrict Wbv) :=
    ContinuousOn.measurableEmbedding measurableSet_ball hcont hinj
  have hrange : Wbv '' (Metric.ball (0 : Point n) ρ)
      = Set.range ((Metric.ball (0 : Point n) ρ).restrict Wbv) :=
    (Set.range_restrict Wbv (Metric.ball (0 : Point n) ρ)).symm
  rw [hrange, ← Set.image_univ]
  exact hemb.measurableSet_image.mpr MeasurableSet.univ

/-! ### The plug — the fixed-`f` limit with M1–M4 and `hΩmeas` discharged. -/

/-- **★★ `chartImage_approx_identity_of_amp` — THE PLUG.**  The fixed-`f` W1 limit-value member with
    the base-varying change-of-variables bundle (M1–M4) AND the chart-image measurability (`hΩmeas`)
    FULLY DISCHARGED off the hypothesis surface.  From only the standing geometry `(hC, hK, K ∈ 𝓝 0)`
    there EXIST a CoV radius `ρ`, inverse `V`, and derivative field `f'` such that, provided ONLY the
    five remaining honest carries hold for that `(ρ, V, f')` —
      • `hGgate` : the witness gate is active on `ball 0 ρ`;
      • `hSupp`  : the witness vanishes off `ball 0 ρ`, τ-uniformly;
      • `hmeas`/`hbound`/`hlocal` : the Layer-C moving-integrand trio for
        `g τ w := chartFieldAmp … τ (V w) 0 · f (V w) / |(f' (V w)).det|` toward `f 0` —
    the boundary witness sampled against `f` concentrates at `f 0`:
        `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`.

    ROUTE.  Obtain the J4-274 bundle `baseVaryingIFTPackage_unconditional` → a concrete `(ρ, V, f')`
    with M1–M4 (`hfd`/`hinj`/`hV`/`hJpos`) and `Ω ∈ 𝓝 0` (`hΩnhds`); derive `hΩmeas` from
    `chartImage_measurableSet_of_bundle`; feed the J4-271 conditional capstone
    `chartImage_approx_identity_conditional`.

    ⚠ CONDITIONAL only on the five carries (see the file header's FINAL CARRY LIST for satisfiability
    of each, and the MISMATCH INTEL on the `hSupp` gate-vs-CoV-radius ball/annulus split).  Each carry
    is genuinely weaker than the conclusion; the hypothesis set is honest and non-vacuous.  NOT
    `a₁ = R/6`. -/
theorem chartImage_approx_identity_of_amp
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (S : Point n → Set (Point n)) (a b : ℝ) (f : Point n → ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      (∀ z ∈ Metric.ball (0 : Point n) ρ, z ∈ K ∧ (0 : Point n) ∈ S z) →
      (∀ τ, ∀ z, z ∉ Metric.ball (0 : Point n) ρ →
        vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z = 0) →
      (∀ᶠ τ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable
          (fun w => chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|)
          (volume.restrict
            ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)))) →
      (∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ w ∂(volume.restrict
            ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))),
          ‖chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|‖ ≤ C) →
      (∀ ε > 0, ∃ r > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ w ∂(volume.restrict
            ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))),
          ‖w‖ < r →
            ‖chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det| - f 0‖ < ε) →
      Tendsto (fun τ => ∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
  -- The J4-274 base-varying CoV bundle: a concrete `(ρ, V, f')` with M1–M4 and `Ω ∈ 𝓝 0`.
  obtain ⟨ρ, hρ, V, f', _hballmeas, hfd, hinj, hV, hJpos, hΩnhds⟩ :=
    baseVaryingIFTPackage_unconditional g gi hC hK h0Kmem
  refine ⟨ρ, hρ, V, f', fun hGgate hSupp hmeas hbound hlocal => ?_⟩
  -- Discharge `hΩmeas` via Lusin–Souslin (from the bundle's `hfd`, `hinj`).
  have hΩmeas : MeasurableSet
      ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)) :=
    chartImage_measurableSet_of_bundle g gi hC hK ρ f' hfd hinj
  -- Feed the J4-271 conditional capstone.
  exact chartImage_approx_identity_conditional g gi hC hK S a b f ρ V f'
    hfd hinj hV hJpos hGgate hSupp hΩmeas hΩnhds hmeas hbound hlocal

end QIQTH.FixedFChartImageAI

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.FixedFChartImageAI
#print axioms chartImage_measurableSet_of_bundle
#print axioms chartImage_approx_identity_of_amp
end AxiomChecks
