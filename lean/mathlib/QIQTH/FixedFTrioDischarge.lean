/-
  FixedFTrioDischarge — J4-277: the fixed-`f` Layer-C moving-integrand trio — the measurability
  member DISCHARGED, the amplitude centre-value PROVED, and the v2 chart-image approximate-identity
  capstone with the carry list shrunk from FIVE to FOUR.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the W1 wall of the a₁ = R/6 campaign).  The J4-275 plug
  `QIQTH.FixedFChartImageAI.chartImage_approx_identity_of_amp` delivers the fixed-`f` W1 limit
      `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`
  from the standing geometry `(hC, hK, K ∈ 𝓝 0)`, CONDITIONAL on FIVE carries for the produced CoV
  bundle `(ρ, V, f')`:
    (C1) `hGgate` — the witness gate is active on `ball 0 ρ`;
    (C2) `hSupp`  — the witness vanishes off `ball 0 ρ`, τ-uniformly;
    (C3) `hmeas`  — a.e.-measurability of the moving integrand
          `g τ w := chartFieldAmp … τ (V w) 0 · f (V w) / |(f' (V w)).det|` on `Ω := Wbv '' ball 0 ρ`;
    (C4) `hbound` — a.e.-boundedness of `g τ` on `Ω`, eventually in `τ`;
    (C5) `hlocal` — the joint `(τ,w) → (0⁺,0)` limit `g τ w → f 0`.

  ── WHAT LANDS HERE (honest composition; the ★ DISCHARGES).
    • `baseChartAmp_centre_eq_one` — ★ THE NORMALISATION, **PROVED** (not carried).  The on-diagonal
      amplitude value `A₀ = chartFieldAmp … 0 0 0 = 1`, given only the standard RNC/gauge inputs
      `0 ∈ K`, `0 < a`, `a < b`, `det g 0 = 1`.  Route: `BaseSlotAmplitude.baseSlotAmp_centreValue`
      exhibits `A₀ = radialCutoff a b 0 · (vanVleck g 0 ^ (-½) · u₀ 0)`, then the banked centre facts
      `radialCutoff_eq_one` (`rncRadialSq 0 = 0 ≤ a²`), `vanVleck_zero` (given `det g 0 = 1`),
      `transportCoeff_zero` (`u₀ ≡ 1`) collapse it to `1`.  This is EXACTLY the `hAmpCentre`
      normalisation of the J4-276 mission — here it is PROVEN, so it is no longer a carry.
    • `bundleV_mapsTo_ball` — ★ the CoV inverse maps the chart image back into the ball:
      `∀ w ∈ Ω, V w ∈ ball 0 ρ` (immediate from the M3 left-inverse identity `hV`).  A wrapper toward
      the `hbound`/`hlocal` composition (the amplitude/Jacobian facts live on the ball).
    • `chartImage_trio_hmeas` — ★★ THE MEASURABILITY MEMBER (C3) **FULLY DISCHARGED**.  From the CoV
      bundle slots (M1 `hfd`, M2 `hinj`, M3 `hV`), the metric carries `{hg,hgi,hgpos}`, and `f`
      measurable, the moving integrand `g τ` is a.e.-strongly-measurable on `Ω`, EVENTUALLY (in fact
      for every) `τ`.  ROUTE (Lusin–Souslin / `measurable_extend`, NO new carry): on the ball `Wbv`
      is a `MeasurableEmbedding` (continuous+injective, `ContinuousOn.measurableEmbedding`); the
      subtype integrand `Hsub z := amp τ ↑z 0 · f ↑z / |det (f' ↑z)|` is measurable — its Jacobian
      factor is `|det (fderiv Wbv ↑z)|` (M1 pins `f' = fderiv Wbv` on the OPEN ball; `measurable_fderiv`
      is unconditional) and its amplitude factor is `ContinuousOn` on the ball
      (`BaseSlotAmplitude.baseSlotAmp_continuousOn`, from `ContinuousOn Wbv`); `measurable_extend`
      produces a GLOBAL measurable `G` with `G ∘ (ball.restrict Wbv) = Hsub`; and `g τ` agrees with `G`
      on `Ω = range (ball.restrict Wbv)` (via M3), giving `AEStronglyMeasurable (g τ)` by `.congr`.
    • `chartImage_approx_identity_v2` — ★★ THE v2 CAPSTONE.  Internally obtains the J4-274 bundle
      `baseVaryingIFTPackage_unconditional`, discharges `hΩmeas` (`chartImage_measurableSet_of_bundle`)
      AND `hmeas` (`chartImage_trio_hmeas`), and feeds the J4-271 conditional capstone
      `ChartImageAIConcrete.chartImage_approx_identity_conditional`.  The result is a Tendsto that is
      CONDITIONAL on only FOUR carries: `hGgate`, `hSupp`, `hbound`, `hlocal` — the C3 `hmeas` carry is
      REMOVED, and the amplitude normalisation is available as the PROVED `baseChartAmp_centre_eq_one`.

  ── THE FINAL CARRY LIST of `chartImage_approx_identity_v2` (for the produced `(ρ, V, f')`).  FOUR
     genuine, simultaneously-satisfiable inputs, each strictly weaker than the Tendsto conclusion:
       (C1) `hGgate`, (C2) `hSupp` — the annulus/gate split (obstruction (B)), the identified NEXT
             brick; UNCHANGED from the J4-275 plug.
       (C4) `hbound`, (C5) `hlocal` — the a.e.-boundedness and joint limit of the moving integrand.
             These remain CARRIED here (see the HONEST RESIDUAL below for the precise reason).

  ── HONEST RESIDUAL (what is NOT done here, and WHY).
    • `hbound`/`hlocal` (C4/C5) are NOT discharged.  Both need, over the WHOLE chart image `Ω`, a
      UNIFORM amplitude sup-bound and a UNIFORM Jacobian lower bound `|det (f' ·)| ≥ c > 0`, plus the
      inverse-continuity facts `V w → 0` and `|det (f' (V w))| → 1` as `w → 0`.  The banked amplitude
      facts (`baseSlotAmp_bound`, `baseSlotAmp_joint_limit`) live on a COMPACT `closedBall`, while `Ω`
      is the image of the OPEN ball, and the exposed bundle gives `f'` only POINTWISE (no continuity of
      `f'`, no continuity of `V` on `Ω`, no open-image for sub-balls).  Closing C4/C5 cleanly requires
      an ENRICHED bundle re-running `ContDiffAt.toOpenPartialHomeomorph` to also expose `V`'s
      continuity and the sub-ball open images (so the compact `closedBall` sits inside the continuity
      region); that partial-homeomorph enrichment is a separate brick and is NOT performed here.  The
      measurability member C3, by contrast, needs NONE of that (`measurable_extend` bypasses it), which
      is why C3 lands and C4/C5 are honestly carried.
    • Obstruction (B), the `hSupp` gate-vs-CoV ball/annulus split, is a SEPARATE thread (unchanged).

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  These are analytic composition
  bricks.  No `sorry` (prose only), no new axioms, no `:= True`, no vacuous / unsatisfiable /
  conclusion-in-disguise hypotheses: `hmeas` is DISCHARGED (removed from the surface), the amplitude
  normalisation is PROVED, and the four remaining carries (`hGgate`, `hSupp`, `hbound`, `hlocal`) are
  the standard change-of-variables + approximate-identity inputs, each strictly weaker than the
  Tendsto.  `{hg,hgi,hgpos}` are the standing metric regularity/positivity carries (the RNC metric `δ`
  satisfies them).  No existing file is edited.
-/
import Mathlib
import QIQTH.FixedFChartImageAI
import QIQTH.BaseSlotAmplitude

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.VanVleck QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ChartImageAIConcrete QIQTH.TerminalVelC2 QIQTH.FixedFChartImageAI QIQTH.BaseSlotAmplitude
open scoped Topology

namespace QIQTH.FixedFTrioDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The amplitude on-diagonal normalisation — `hAmpCentre` PROVED (`A₀ = 1`). -/

/-- **★ `baseChartAmp_centre_eq_one` — the on-diagonal amplitude value is `1`, PROVED.**  Given the
    standard RNC/gauge inputs (`0 ∈ K`, `0 < a`, `a < b`, `det g 0 = 1`), the coincidence-limit
    amplitude `A₀ = chartFieldAmp … 0 0 0 = 1`.  Route: `baseSlotAmp_centreValue` exhibits
    `A₀ = radialCutoff a b 0 · (vanVleck g 0 ^ (-½) · u₀ 0)`, and the banked centre facts
    `radialCutoff_eq_one` (`rncRadialSq 0 = 0 ≤ a²`), `vanVleck_zero` (`det g 0 = 1`),
    `transportCoeff_zero` (`u₀ ≡ 1`) collapse it to `1`.  This is the labelled `hAmpCentre`
    normalisation of J4-276 — here PROVEN, so no longer a carry.  NOT `a₁ = R/6`. -/
theorem baseChartAmp_centre_eq_one (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hgdet0 : Matrix.det (g 0) = 1) :
    chartFieldAmp g gi hC hK a b 0 0 0 = 1 := by
  rw [baseSlotAmp_centreValue g gi hC hK hK0 a b]
  rw [radialCutoff_eq_one ha hab (by rw [rncRadialSq_zero]; positivity),
    vanVleck_zero g hgdet0, transportCoeff_zero]
  simp [Real.one_rpow]

/-! ### The CoV inverse maps the chart image back into the ball (wrapper). -/

/-- **★ `bundleV_mapsTo_ball` — the CoV inverse sends `Ω` into the ball.**  From the M3 left-inverse
    identity `hV` (`V (Wbv z) = z` on `ball 0 ρ`), every image point `w ∈ Ω := Wbv '' ball 0 ρ` has
    `V w ∈ ball 0 ρ`.  A wrapper toward the `hbound`/`hlocal` composition (the amplitude and Jacobian
    facts live on the ball; `V` lands there).  NOT `a₁ = R/6`. -/
theorem bundleV_mapsTo_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (ρ : ℝ) (V : Point n → Point n)
    (hV : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      V (uniformInverseChart g gi hC hK z 0) = z) :
    ∀ w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ,
      V w ∈ Metric.ball (0 : Point n) ρ := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [hV z hz]
  exact hz

/-! ### The subtype integrand measurability (measurability ingredient of C3). -/

/-- **`subtypeIntegrand_measurable` — the ball-subtype integrand is measurable.**  On the ball
    subtype, `z ↦ amp τ ↑z 0 · f ↑z / |det (f' ↑z)|` is measurable: the amplitude factor is
    `ContinuousOn` on the ball (`baseSlotAmp_continuousOn`), `f` is measurable (carried), and the
    Jacobian factor equals `|det (fderiv ℝ Wbv ↑z)|` on the OPEN ball (M1 ⟹ `f' = fderiv Wbv`),
    measurable by the unconditional `measurable_fderiv`.  NOT `a₁ = R/6`. -/
theorem subtypeIntegrand_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b τ : ℝ) (f : Point n → ℝ) (hf_meas : Measurable f)
    (ρ : ℝ) (f' : Point n → (Point n →L[ℝ] Point n))
    (hfd : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
        (Metric.ball (0 : Point n) ρ) z) :
    Measurable
      (fun z : ↥(Metric.ball (0 : Point n) ρ) =>
        chartFieldAmp g gi hC hK a b τ (↑z) 0 * f (↑z) / |(f' (↑z)).det|) := by
  have hWcont : ContinuousOn (fun z => uniformInverseChart g gi hC hK z 0)
      (Metric.ball (0 : Point n) ρ) := fun z hz => (hfd z hz).continuousWithinAt
  -- Single-slot amplitude continuity on the ball (direct product of banked ingredient continuities;
  -- mirrors `baseSlotAmp_continuousOn` at fixed `τ`, avoiding the product-filter `.comp`).
  have hampON : ContinuousOn (fun z : Point n => chartFieldAmp g gi hC hK a b τ z 0)
      (Metric.ball (0 : Point n) ρ) := by
    have hcut : ContinuousOn
        (fun z : Point n => radialCutoff a b (uniformInverseChart g gi hC hK z 0))
        (Metric.ball (0 : Point n) ρ) :=
      (radialCutoff_contDiff a b).continuous.comp_continuousOn hWcont
    have hVVc : Continuous (fun v : Point n => vanVleck g v ^ (-(1 : ℝ) / 2)) :=
      (QIQTH.CoeffContWdiffLift.vanVleck_continuous g hg hgpos).rpow_const
        (fun v => Or.inl (QIQTH.CoeffContWdiffLift.vanVleck_ne_zero g hgpos v))
    have hvv : ContinuousOn
        (fun z : Point n => vanVleck g (uniformInverseChart g gi hC hK z 0) ^ (-(1 : ℝ) / 2))
        (Metric.ball (0 : Point n) ρ) := hVVc.comp_continuousOn hWcont
    have huc := QIQTH.CoeffContWdiffLift.huc_discharged g gi hg hgi hgpos
    have hu0 : ContinuousOn
        (fun z : Point n => transportCoeff (transportOp (vanVleck g) g gi) 0
          (uniformInverseChart g gi hC hK z 0)) (Metric.ball (0 : Point n) ρ) :=
      (huc 0).comp_continuousOn hWcont
    have hu1 : ContinuousOn
        (fun z : Point n => transportCoeff (transportOp (vanVleck g) g gi) 1
          (uniformInverseChart g gi hC hK z 0)) (Metric.ball (0 : Point n) ρ) :=
      (huc 1).comp_continuousOn hWcont
    have hsum : ContinuousOn
        (fun z : Point n =>
          transportCoeff (transportOp (vanVleck g) g gi) 0 (uniformInverseChart g gi hC hK z 0)
          + transportCoeff (transportOp (vanVleck g) g gi) 1
              (uniformInverseChart g gi hC hK z 0) * τ) (Metric.ball (0 : Point n) ρ) :=
      hu0.add (hu1.mul continuousOn_const)
    have hcomb := hcut.mul (hvv.mul hsum)
    simpa only [chartFieldAmp] using hcomb
  have hamp_m : Measurable
      (fun z : ↥(Metric.ball (0 : Point n) ρ) => chartFieldAmp g gi hC hK a b τ (↑z) 0) :=
    hampON.restrict.measurable
  have hf_m : Measurable (fun z : ↥(Metric.ball (0 : Point n) ρ) => f (↑z)) :=
    hf_meas.comp measurable_subtype_coe
  have hf'eq : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      f' z = fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z :=
    fun z hz => (((hfd z hz).hasFDerivAt (Metric.isOpen_ball.mem_nhds hz)).fderiv).symm
  have hdet_eq : (fun z : ↥(Metric.ball (0 : Point n) ρ) => |(f' (↑z)).det|)
      = (fun z : ↥(Metric.ball (0 : Point n) ρ) =>
          |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (↑z)).det|) := by
    funext z; rw [hf'eq (↑z) z.2]
  have hdet_m : Measurable
      (fun z : ↥(Metric.ball (0 : Point n) ρ) => |(f' (↑z)).det|) := by
    rw [hdet_eq]
    exact ((continuous_abs.measurable.comp
      (ContinuousLinearMap.continuous_det.measurable.comp
        (measurable_fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0)))).comp
        measurable_subtype_coe)
  exact (hamp_m.mul hf_m).div hdet_m

/-! ### The measurability member C3 — `hmeas` DISCHARGED via Lusin–Souslin / `measurable_extend`. -/

/-- **★★ `chartImage_trio_hmeas` — the Layer-C measurability member (C3), FULLY DISCHARGED.**  From
    the CoV bundle slots (M1 `hfd`, M2 `hinj`, M3 `hV`), the metric carries `{hg,hgi,hgpos}`, and `f`
    measurable, the moving integrand
      `g τ w := chartFieldAmp … τ (V w) 0 · f (V w) / |(f' (V w)).det|`
    is `AEStronglyMeasurable` on `volume.restrict (Wbv '' ball 0 ρ)`, EVENTUALLY (in fact for all) `τ`.

    ROUTE (`measurable_extend`, no new carry).  `Wbv := z ↦ uniformInverseChart g gi hC hK z 0` is a
    `MeasurableEmbedding` of the ball (continuous from M1 + injective M2).  The subtype integrand
    `Hsub z := amp τ ↑z 0 · f ↑z / |det (f' ↑z)|` is measurable: the amplitude factor is `ContinuousOn`
    on the ball (`baseSlotAmp_continuousOn`, from `ContinuousOn Wbv`), `f` is measurable (carried), and
    the Jacobian factor equals `|det (fderiv ℝ Wbv ↑z)|` on the OPEN ball (M1 ⟹ `HasFDerivAt` ⟹
    `f' = fderiv Wbv`), which is measurable by the UNCONDITIONAL `measurable_fderiv`.  `measurable_extend`
    yields a GLOBAL measurable `G` with `G ∘ (ball.restrict Wbv) = Hsub`; via M3, `g τ` agrees with `G`
    on `Ω = range (ball.restrict Wbv)`, so `AEStronglyMeasurable (g τ)` follows by `.congr`.
    NOT `a₁ = R/6`. -/
theorem chartImage_trio_hmeas (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b : ℝ) (f : Point n → ℝ) (hf_meas : Measurable f)
    (ρ : ℝ) (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n))
    (hfd : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
        (Metric.ball (0 : Point n) ρ) z)
    (hinj : Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ))
    (hV : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      V (uniformInverseChart g gi hC hK z 0) = z) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable
        (fun w => chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|)
        (volume.restrict
          ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))) := by
  refine Filter.Eventually.of_forall (fun τ => ?_)
  -- Ω measurable, chart continuous on the ball.
  have hWcont : ContinuousOn (fun z => uniformInverseChart g gi hC hK z 0)
      (Metric.ball (0 : Point n) ρ) := fun z hz => (hfd z hz).continuousWithinAt
  have hΩmeas : MeasurableSet
      ((fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ) :=
    chartImage_measurableSet_of_bundle g gi hC hK ρ f' hfd hinj
  -- The measurable embedding `e = ball.restrict chart`.
  have hemb : MeasurableEmbedding
      ((Metric.ball (0 : Point n) ρ).restrict (fun z => uniformInverseChart g gi hC hK z 0)) :=
    ContinuousOn.measurableEmbedding measurableSet_ball hWcont hinj
  -- The subtype integrand measurability (extracted lemma).
  have hHsub_meas := subtypeIntegrand_measurable g gi hC hK hg hgi hgpos a b τ f hf_meas ρ f' hfd
  -- The global measurable extension `G`, agreeing with the integrand on `Ω`.
  have hG : Measurable
      (Function.extend ((Metric.ball (0 : Point n) ρ).restrict
          (fun z => uniformInverseChart g gi hC hK z 0))
        (fun z : ↥(Metric.ball (0 : Point n) ρ) =>
          chartFieldAmp g gi hC hK a b τ (↑z) 0 * f (↑z) / |(f' (↑z)).det|)
        (fun _ => 0)) :=
    hemb.measurable_extend hHsub_meas measurable_const
  have hpt : ∀ w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ,
      Function.extend ((Metric.ball (0 : Point n) ρ).restrict
          (fun z => uniformInverseChart g gi hC hK z 0))
        (fun z : ↥(Metric.ball (0 : Point n) ρ) =>
          chartFieldAmp g gi hC hK a b τ (↑z) 0 * f (↑z) / |(f' (↑z)).det|)
        (fun _ => 0) w
        = chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det| := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hext := hemb.injective.extend_apply
      (fun z : ↥(Metric.ball (0 : Point n) ρ) =>
        chartFieldAmp g gi hC hK a b τ (↑z) 0 * f (↑z) / |(f' (↑z)).det|)
      (fun _ => 0) ⟨z, hz⟩
    show Function.extend ((Metric.ball (0 : Point n) ρ).restrict
          (fun z => uniformInverseChart g gi hC hK z 0))
        (fun z : ↥(Metric.ball (0 : Point n) ρ) =>
          chartFieldAmp g gi hC hK a b τ (↑z) 0 * f (↑z) / |(f' (↑z)).det|)
        (fun _ => 0) (uniformInverseChart g gi hC hK z 0)
        = chartFieldAmp g gi hC hK a b τ (V (uniformInverseChart g gi hC hK z 0)) 0
          * f (V (uniformInverseChart g gi hC hK z 0))
          / |(f' (V (uniformInverseChart g gi hC hK z 0))).det|
    rw [hV z hz]
    exact hext
  -- Agree a.e. on `Ω`, then transfer measurability.
  have hae : (Function.extend ((Metric.ball (0 : Point n) ρ).restrict
          (fun z => uniformInverseChart g gi hC hK z 0))
        (fun z : ↥(Metric.ball (0 : Point n) ρ) =>
          chartFieldAmp g gi hC hK a b τ (↑z) 0 * f (↑z) / |(f' (↑z)).det|)
        (fun _ => 0))
      =ᵐ[volume.restrict
          ((fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ)]
      (fun w => chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|) :=
    (ae_restrict_iff' hΩmeas).mpr (Filter.Eventually.of_forall (fun w hw => hpt w hw))
  exact (hG.aestronglyMeasurable).congr hae

/-! ### The v2 capstone — `hmeas` discharged, four carries remaining. -/

/-- **★★ `chartImage_approx_identity_v2` — THE v2 CAPSTONE.**  The fixed-`f` W1 limit with the
    change-of-variables bundle (M1–M4), the chart-image measurability (`hΩmeas`), AND the Layer-C
    measurability member (`hmeas`, C3) all discharged.  From the standing geometry `(hC, hK, K ∈ 𝓝 0)`,
    the metric carries `{hg,hgi,hgpos}`, and `f` measurable, there EXIST a CoV radius `ρ`, inverse `V`,
    and derivative field `f'` such that, provided ONLY the FOUR remaining carries hold for `(ρ, V, f')`
    —
      • `hGgate` : the witness gate is active on `ball 0 ρ`;
      • `hSupp`  : the witness vanishes off `ball 0 ρ`, τ-uniformly;
      • `hbound` : a.e.-boundedness of the moving integrand on `Ω`, eventually in `τ`;
      • `hlocal` : the joint `(τ,w) → (0⁺,0)` limit of the moving integrand to `f 0` —
    the boundary witness sampled against `f` concentrates at `f 0`:
        `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`.

    ROUTE.  Obtain the J4-274 bundle `baseVaryingIFTPackage_unconditional` → concrete `(ρ, V, f')`;
    discharge `hΩmeas` (`chartImage_measurableSet_of_bundle`) and `hmeas` (`chartImage_trio_hmeas`);
    feed `chartImage_approx_identity_conditional`.  The `hmeas` (C3) carry of the J4-275 plug is
    REMOVED; the amplitude normalisation is separately PROVED (`baseChartAmp_centre_eq_one`).

    ⚠ CONDITIONAL only on the FOUR carries (`hGgate`, `hSupp`, `hbound`, `hlocal`); see the file
    header's FINAL CARRY LIST and HONEST RESIDUAL for why `hbound`/`hlocal` remain (the enriched
    partial-homeomorph bundle needed for the uniform amplitude/Jacobian bounds over `Ω` is the next
    brick).  NOT `a₁ = R/6`. -/
theorem chartImage_approx_identity_v2
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (f : Point n → ℝ) (hf_meas : Measurable f) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      (∀ z ∈ Metric.ball (0 : Point n) ρ, z ∈ K ∧ (0 : Point n) ∈ S z) →
      (∀ τ, ∀ z, z ∉ Metric.ball (0 : Point n) ρ →
        vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z = 0) →
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
  obtain ⟨ρ, hρ, V, f', _hballmeas, hfd, hinj, hV, hJpos, hΩnhds⟩ :=
    baseVaryingIFTPackage_unconditional g gi hC hK h0Kmem
  refine ⟨ρ, hρ, V, f', fun hGgate hSupp hbound hlocal => ?_⟩
  have hΩmeas : MeasurableSet
      ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)) :=
    chartImage_measurableSet_of_bundle g gi hC hK ρ f' hfd hinj
  have hmeas := chartImage_trio_hmeas g gi hC hK hg hgi hgpos a b f hf_meas ρ V f' hfd hinj hV
  exact chartImage_approx_identity_conditional g gi hC hK S a b f ρ V f'
    hfd hinj hV hJpos hGgate hSupp hΩmeas hΩnhds hmeas hbound hlocal

end QIQTH.FixedFTrioDischarge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.FixedFTrioDischarge
#print axioms baseChartAmp_centre_eq_one
#print axioms bundleV_mapsTo_ball
#print axioms subtypeIntegrand_measurable
#print axioms chartImage_trio_hmeas
#print axioms chartImage_approx_identity_v2
end AxiomChecks
