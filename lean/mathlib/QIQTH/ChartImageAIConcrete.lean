/-
  ChartImageAIConcrete — J4-271: the concrete chart-image approximate-identity composition
  (the A + B + C wiring) for the FIXED-`f` W1 limit-value member.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the W1 wall of the a₁ = R/6 campaign, SOL#5 three-layer plan).  All three layers of the
  chart-image approximate identity are banked:
    • LAYER C — `ChartImageApproxIdentity.gaussDdim_set_approx_identity_moving` (chart-free MOVING
      Gaussian approximate identity: `∫ w in Ω, gaussDdim τ w · g τ w → L` on `𝓝[>]0`).
    • LAYER B (abstract) — `ChartGaussianChangeVar.chart_gaussian_change_variables` (the change of
      variables `w = W z` for ANY C¹ chart with a CoV data bundle M1–M4).
    • LAYER B (concrete, J4-270) — `ChartIFTPackage.chart_gaussian_change_variables_concrete` (the
      CoV bundle for the chart `z ↦ uniformInverseChart g gi hC hK 0 z`).

  ── ★★ ORIENTATION VERDICT (LOAD-BEARING INTEL — the reason the CONCRETE capstone does NOT close). ──
    The name `W₀` is OVERLOADED across the bank with two DIFFERENT functions:
      (i)  the FACTORISATION chart (`witness_zero_eq_gauss_mul_amp`, `vanVleckGatedWitness_zero_factor`,
           `NormalFormDischarge` `W₀ z = W z 0`):  the Gaussian argument is
               `uniformInverseChart g gi hC hK z 0`  — the BASE-VARYING, FIELD-FIXED-`0` chart
               `Wbv : z ↦ uniformInverseChart g gi hC hK z 0`  (`z` in the BASE slot).
      (ii) the J4-270 IFT PACKAGE chart (`chartIFTPackage`, `chart_gaussian_change_variables_concrete`,
           `ChartJetBounds.chartField_*_center`):  the CoV bundle is built for
               `uniformInverseChart g gi hC hK 0 z`  — the BASE-FIXED-`0`, FIELD-VARYING chart
               `Wfv : z ↦ uniformInverseChart g gi hC hK 0 z`  (`z` in the FIELD slot).
    `Wbv` and `Wfv` are NOT the same function.  They agree only at `z = 0` (both `= 0`,
    `chartField_centerValue_base0`) and each has derivative `±Id` at `0`, but as maps of `z` they
    differ (different base points of the exponential chart).  The ENTIRE downstream analytic pipeline
    that reaches the boundary integral — `witness_zero_eq_gauss_mul_amp`, the wide dominations
    (`WideWitnessAmplitude.WideAmplitudeData.*`), and the goal integrand `∫ z, Wit τ 0 z · f z` —
    uses `Wbv`.  The ONLY banked CONCRETE CoV bundle (`chart_gaussian_change_variables_concrete`,
    J4-270) is for `Wfv`.  Hence the concrete `B ∘ C` composition CANNOT be plugged into the boundary
    integral: the missing brick is a base-varying IFT package (M1–M4 for `Wbv`).  Base-slot regularity
    of the `.choose`-defined uniform chart is NOT banked (all `chartField_*_center` facts are field-slot
    at base `0`), so building it is a SEPARATE, harder brick.

  ── WHAT LANDS HERE (honest, respecting the orientation verdict).
    • `boundary_integral_eq_gate_integral` — ★ LAYER A, CONCRETE & FULLY DISCHARGED.  The set-integral
      rewrite of the boundary witness onto a measurable gate region `G`, using the on-gate factorisation
      `Wit τ 0 z = gaussDdim τ (Wbv z) · chartFieldAmp … τ z 0` and off-`G` vanishing.  NO carried
      hypothesis is the conclusion (`hGgate`/`hSupp` are the honest gate-activation / support-in-`G`
      facts).
    • `boundary_integral_eq_chartImage_integral` — ★ LAYER A ∘ B(abstract).  Given a CoV data bundle
      (M1–M4) for the BASE-VARYING chart `Wbv` on `ball 0 ρ`, the boundary integral equals a genuine
      chart-image Gaussian integral `∫ w in Wbv '' (ball 0 ρ), gaussDdim τ w · (…)`.
    • `chartImage_approx_identity_conditional` — ★ THE CONDITIONAL CAPSTONE (A ∘ B ∘ C).  Given the
      `Wbv` CoV bundle on `ball 0 ρ` PLUS the Layer-C moving-integrand inputs (`hmeas`/`hbound`/`hlocal`)
      for `g τ w := chartFieldAmp … τ (V w) 0 · f (V w) / |(D Wbv (V w)).det|` toward `L := f 0`,
          `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`.
      This is the honest W1 limit-value member for fixed `f`, CONDITIONAL on the two missing inputs the
      orientation verdict isolates: (a) the base-varying CoV bundle for `Wbv`, and (b) the moving-
      integrand facts (which encode the amplitude joint limit `A τ z → 1` + `det`/`f` continuity).

  ── BANKED vs MISSING for the Layer-C inputs (`hlocal`/`hbound`), reported for the next brick.
    • BANKED / cheap: off-gate vanishing (`gatedKernel_apply_of_notMem` — EVERYWHERE off-gate, not just
      a.e.); the amplitude sup-bound on a ball (`AmplitudeFamilyDischarge.amp_bound_*` — feeds `hbound`);
      the amplitude `C²`/continuity at the field centre (`amp_contDiffAt_*`).
    • MISSING for a CONCRETE discharge: the base-varying CoV bundle (M1–M4 for `Wbv`); the JOINT
      `(τ,z) → (0⁺,0)` limit of the amplitude `chartFieldAmp … τ (V w) 0` (only per-`z` `C²` at `0` is
      banked, not the joint-in-`τ` limit); the amplitude centre normalisation `A₀(0) = 1`
      (`radialCutoff a b 0 · vanVleck g 0^(−½) · u₀(0) = 1`).  These are the `hlocal` sub-facts.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  These are analytic composition
  bricks.  No `sorry` (prose only), no new axioms, no `:= True`, no vacuous / conclusion-in-disguise
  hypotheses: the CoV data + `hmeas`/`hbound`/`hlocal` are the standard, simultaneously-satisfiable
  change-of-variables + approximate-identity inputs, each strictly weaker than the Tendsto conclusion
  (they are a.e./eventual local facts).  No existing file is edited.
-/
import Mathlib
import QIQTH.ChartImageApproxIdentity
import QIQTH.ChartGaussianChangeVar
import QIQTH.WideWitnessAmplitude

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ChartImageApproxIdentity QIQTH.ChartGaussianChangeVar
open scoped Topology

namespace QIQTH.ChartImageAIConcrete

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### LAYER A — the concrete set-integral rewrite onto the gate. -/

/-- **★ LAYER A — `boundary_integral_eq_gate_integral`.**  For a measurable gate region `G` on which
    the gate is active (`z ∈ K ∧ 0 ∈ S z`, so the factorisation holds) and off which the witness
    vanishes (support in `G`), the boundary integral rewrites as a set integral of the BASE-VARYING
    chart-image Gaussian times the concrete field amplitude:
        `∫ z, Wit τ 0 z · f z
           = ∫ z in G, gaussDdim τ (uniformInverseChart g gi hC hK z 0) · (chartFieldAmp … τ z 0 · f z)`.
    Route: off-`G` vanishing collapses the ambient integral to `∫ z in G` (indicator argument), then
    the on-gate factorisation `witness_zero_eq_gauss_mul_amp` rewrites the integrand pointwise on `G`.
    `hGgate`/`hSupp` are honest, satisfiable, non-conclusion inputs (the actual gate + support-in-`G`).
    NOT `a₁ = R/6`. -/
theorem boundary_integral_eq_gate_integral
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (f : Point n → ℝ) {G : Set (Point n)} (hGmeas : MeasurableSet G)
    (hGgate : ∀ z ∈ G, z ∈ K ∧ (0 : Point n) ∈ S z)
    (hSupp : ∀ z, z ∉ G → vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z = 0) :
    (∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
      = ∫ z in G, gaussDdim τ (uniformInverseChart g gi hC hK z 0)
            * (chartFieldAmp g gi hC hK a b τ z 0 * f z) := by
  -- Off `G` the integrand vanishes, so the ambient integral collapses to `∫ z in G`.
  have key : (∫ z in G, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
      = ∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z := by
    rw [← integral_indicator hGmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    by_cases hz : z ∈ G
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      simp only [hSupp z hz, zero_mul]
  rw [← key]
  refine setIntegral_congr_fun hGmeas (fun z hz => ?_)
  obtain ⟨hzK, h0S⟩ := hGgate z hz
  rw [QIQTH.WideWitnessAmplitude.witness_zero_eq_gauss_mul_amp g gi hC hK S a b τ hzK h0S]
  ring

/-! ### LAYER A ∘ B(abstract) — the boundary integral as a chart-image Gaussian integral. -/

/-- **★ LAYER A ∘ B — `boundary_integral_eq_chartImage_integral`.**  Given a change-of-variables data
    bundle (M1–M4) for the BASE-VARYING chart `Wbv : z ↦ uniformInverseChart g gi hC hK z 0` on the ball
    `ball 0 ρ` — a derivative field `f'`, injectivity, a left inverse `V`, positive Jacobian — together
    with the gate-activation `hGgate` and support-in-ball `hSupp` on that ball, the boundary integral
    equals a genuine chart-image Gaussian integral over `Ω := Wbv '' (ball 0 ρ)`:
        `∫ z, Wit τ 0 z · f z
           = ∫ w in Ω, gaussDdim τ w · (chartFieldAmp … τ (V w) 0 · f (V w) / |(f' (V w)).det|)`.
    Route: Layer A onto `G := ball 0 ρ`, then the abstract change of variables
    `chart_gaussian_change_variables` with `B z := chartFieldAmp … τ z 0 · f z`.  ⚠ The CoV data here
    is for `Wbv` (base-varying) — NOT the J4-270 `Wfv` package (see the ORIENTATION VERDICT): this is
    the exact orientation the concrete boundary integral needs, and the missing base-varying IFT package
    is the residual.  NOT `a₁ = R/6`. -/
theorem boundary_integral_eq_chartImage_integral
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (f : Point n → ℝ) (ρ : ℝ) (V : Point n → Point n)
    (f' : Point n → (Point n →L[ℝ] Point n))
    (hfd : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
        (Metric.ball (0 : Point n) ρ) z)
    (hinj : Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ))
    (hV : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      V (uniformInverseChart g gi hC hK z 0) = z)
    (hJpos : ∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
    (hGgate : ∀ z ∈ Metric.ball (0 : Point n) ρ, z ∈ K ∧ (0 : Point n) ∈ S z)
    (hSupp : ∀ z, z ∉ Metric.ball (0 : Point n) ρ →
      vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z = 0) :
    (∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
      = ∫ w in (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ),
          gaussDdim τ w
            * (chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|) := by
  rw [boundary_integral_eq_gate_integral g gi hC hK S a b τ f measurableSet_ball hGgate hSupp]
  exact QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables
    τ (Metric.ball (0 : Point n) ρ) (fun z => uniformInverseChart g gi hC hK z 0) V f'
    (fun z => |(f' z).det|) (fun z => chartFieldAmp g gi hC hK a b τ z 0 * f z)
    measurableSet_ball hfd hinj hV (fun _ _ => rfl) hJpos

/-! ### LAYER A ∘ B ∘ C — the conditional capstone. -/

/-- **★★ CONDITIONAL CAPSTONE — `chartImage_approx_identity_conditional`.**  The fixed-`f` W1 limit-value
    member: the boundary witness sampled against `f` concentrates at `f 0`,
        `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`,
    CONDITIONAL on
      • a change-of-variables data bundle (M1–M4) for the BASE-VARYING chart
        `Wbv : z ↦ uniformInverseChart g gi hC hK z 0` on `ball 0 ρ` (`hfd`/`hinj`/`hV`/`hJpos`),
      • the gate-activation `hGgate` on the ball and the support-in-ball `hSupp` (τ-uniform),
      • measurability & neighbourhood of the chart image `Ω := Wbv '' (ball 0 ρ)` (`hΩmeas`/`hΩnhds`),
      • the Layer-C moving-integrand inputs (`hmeas`/`hbound`/`hlocal`) for
        `g τ w := chartFieldAmp … τ (V w) 0 · f (V w) / |(f' (V w)).det|` toward `L := f 0`.
    Route: `boundary_integral_eq_chartImage_integral` rewrites each `τ` slice as the chart-image Gaussian
    integral `∫ w in Ω, gaussDdim τ w · g τ w`, then Layer C
    (`gaussDdim_set_approx_identity_moving`) delivers the limit.  ⚠ CONDITIONAL — the two hard inputs
    (the base-varying CoV bundle + the moving-integrand facts encoding the amplitude joint limit) are
    the residual the ORIENTATION VERDICT isolates; each is genuinely weaker than the conclusion, so the
    hypothesis set is honest and non-vacuous.  NOT `a₁ = R/6`. -/
theorem chartImage_approx_identity_conditional
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (f : Point n → ℝ) (ρ : ℝ) (V : Point n → Point n)
    (f' : Point n → (Point n →L[ℝ] Point n))
    (hfd : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
        (Metric.ball (0 : Point n) ρ) z)
    (hinj : Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ))
    (hV : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      V (uniformInverseChart g gi hC hK z 0) = z)
    (hJpos : ∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
    (hGgate : ∀ z ∈ Metric.ball (0 : Point n) ρ, z ∈ K ∧ (0 : Point n) ∈ S z)
    (hSupp : ∀ τ, ∀ z, z ∉ Metric.ball (0 : Point n) ρ →
      vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z = 0)
    (hΩmeas : MeasurableSet
      ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)))
    (hΩnhds : (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)
      ∈ 𝓝 (0 : Point n))
    (hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable
        (fun w => chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|)
        (volume.restrict
          ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))))
    (hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict
          ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))),
        ‖chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|‖ ≤ C)
    (hlocal : ∀ ε > 0, ∃ r > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict
          ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))),
        ‖w‖ < r →
          ‖chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det| - f 0‖ < ε) :
    Tendsto (fun τ => ∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
      (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
  -- Layer C: the moving approximate identity over the chart image `Ω`.
  have base := gaussDdim_set_approx_identity_moving (n := n) hΩmeas hΩnhds hmeas hbound hlocal
  -- Each `τ`-slice of the goal equals the chart-image Gaussian integral (Layer A ∘ B).
  have heq : ∀ τ : ℝ,
      (∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        = ∫ w in (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ),
            gaussDdim τ w
              * (chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|) := by
    intro τ
    exact boundary_integral_eq_chartImage_integral g gi hC hK S a b τ f ρ V f'
      hfd hinj hV hJpos hGgate (hSupp τ)
  exact base.congr' (Filter.Eventually.of_forall (fun τ => (heq τ).symm))

end QIQTH.ChartImageAIConcrete

/-! ### Axiom audit. -/

section AxiomChecks

open QIQTH.ChartImageAIConcrete

#print axioms boundary_integral_eq_gate_integral
#print axioms boundary_integral_eq_chartImage_integral
#print axioms chartImage_approx_identity_conditional

end AxiomChecks
