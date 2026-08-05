/-
  BaseVaryingIFTPackage — J4-272: the BASE-VARYING inverse-function-theorem / change-of-variables
  package (M1–M4) for the chart

      Wbv : z ↦ uniformInverseChart g gi hC hK z 0        (z in the BASE slot, field slot fixed = 0),

  exactly the bundle shape that `ChartImageAIConcrete.boundary_integral_eq_chartImage_integral` and
  `ChartImageAIConcrete.chartImage_approx_identity_conditional` (J4-271) consume as their missing
  gap (a).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── ★★ THE ORIENTATION LESSON (why J4-270 does NOT plug in). ──
    The name `W₀` is OVERLOADED.  The J4-270 package (`ChartIFTPackage.chartIFTPackage`) is for the
    FIELD-varying chart `Wfv : z ↦ uniformInverseChart g gi hC hK 0 z` (base fixed `0`, FIELD slot
    varying).  Its centre facts came from `ChartJetBounds` (`chartField_contDiffAt_center`,
    `chartField_centerValue_base0`, `chartField_fderiv_center`) — all FIELD-slot facts at base `0`.
    The downstream boundary integral instead uses the BASE-varying chart `Wbv`, and `Wbv ≠ Wfv`
    (they agree only at `0`).  So the base-slot regularity is a genuinely DIFFERENT question.

  ── WHAT IS PROVEN vs CARRIED (honest firewall — NOT `a₁ = R/6`).
    • ★ `baseVaryingChart_hasFDerivAt_center` — UNCONDITIONAL (given `K ∈ 𝓝 0`).  The base-slot
      chart is DIFFERENTIABLE AT THE CENTRE with derivative `-id`:
          `HasFDerivAt Wbv (↑(ContinuousLinearEquiv.neg ℝ)) 0`.
      This is DERIVED from the BANKED quadratic displacement bound
      `‖uniformInverseChart g gi hC hK z 0 + z‖ ≤ C_W ‖z‖²` (`chartW0_displacement`) — which is
      exactly the little-o statement `Wbv z - 0 - (-z) = o(‖z‖)` — together with `Wbv 0 = 0`
      (`uniformInverseChart_zero`).  The `K ∈ 𝓝 0` hypothesis is genuinely needed: OFF `K` the chart
      is the zero default (`Wbv z = 0`), so `Wbv z + z = z` is NOT `o(‖z‖)` there; the displacement
      bound only controls `z ∈ K`.  (The sign `Wbv z ≈ -z` matches `chartW0_displacement`.)

    • ★★ `baseVaryingIFTPackage` — THE M1–M4 BUNDLE, CONDITIONAL on ONE honest regularity input:
          `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`.
      Given `hbaseC2` (plus the geometry `hC`, `hK`, and `K ∈ 𝓝 0`), the package returns
      `∃ ρ>0 ∃ V f'`, the FULL change-of-variables bundle on `ball 0 ρ`:
          (M1) `∀ z ∈ ball 0 ρ, HasFDerivWithinAt Wbv (f' z) (ball 0 ρ) z`,
          (M2) `Set.InjOn Wbv (ball 0 ρ)`,
          (M3) `∀ z ∈ ball 0 ρ, V (Wbv z) = z`,
          (M4) `∀ z ∈ ball 0 ρ, 0 < |(f' z).det|`,
        plus the image neighbourhood `Wbv '' (ball 0 ρ) ∈ 𝓝 0` and `MeasurableSet (ball 0 ρ)`.
      The invertibility of the centre derivative (needed for the IFT) is supplied by the banked
      displacement bound (`fderiv Wbv 0 = -id`, `det (-id) = (-1)ⁿ ≠ 0`), so the displacement bank is
      LOAD-BEARING here.  M2/M3 are PROVEN via `ContDiffAt.toOpenPartialHomeomorph` (the J4-270
      incantation, mirrored), NOT assumed; M1 from `ContDiffAt.eventually`; M4 from det continuity.

  ── THE HONEST RESIDUAL (the precise regularity-gap map for the next brick / a consult).
    `hbaseC2 : ContDiffAt ℝ 2 Wbv 0` is the SINGLE missing input.  It is:
      * TRUE geometrically — on a neighbourhood of `0` (where `0` is a reachable exp-image of nearby
        bases) the germ/left-inverse property pins `Wbv z = (exp_z)⁻¹(0)`, the unique smooth
        exp-inverse in the base, which IS `C²` in `z`; and
      * NOT banked — `uniformInverseChart` is `.choose`-defined per base point, carrying NO base-slot
        regularity.  This is the recognized "J3 blocker" (base-`z`-slot regularity of the
        `.choose`-built chart), flagged across `ChartJetBounds` (J3), `GeneralBaseJets` (the `‖Q z‖`
        modulus), `InverseChartDisplacement` ("the base-side `C¹` … was never established"), and
        `ChartImageAIConcrete` (gap (a)).
    ALMOST-there banked facts: the pointwise centre derivative (`baseVaryingChart_hasFDerivAt_center`,
    HERE) gives `C¹` AT `0` only; the near-isometry / displacement bank gives quantitative width and
    sign but not neighbourhood differentiability; the geodesic smooth-dependence tower
    (`GeodesicSmoothDep`, `ExpMapContDiffFour`) provides base-point smooth dependence of the exp FLOW
    but has NOT been threaded through the `.choose` inverse selection to yield base-slot `C²` of
    `uniformInverseChart z 0`.  Closing `hbaseC2` = threading that smooth dependence through the
    inverse; that is a separate, harder brick.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  No `sorry` (prose only), no new
  axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses: `hbaseC2` is
  a standard, geometrically-true regularity fact strictly weaker than (and orthogonal to) the CoV
  conclusion, and `K ∈ 𝓝 0` is the natural interior-basepoint hypothesis (the consumer's `hGgate`
  forces `ball 0 ρ ⊆ K` anyway).  M2/M3 are PROVEN, not carried.  No existing file is edited.
-/
import Mathlib
import QIQTH.InverseChartDisplacement
import QIQTH.CapstoneWiring

open MeasureTheory Filter Asymptotics
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.BaseVaryingIFTPackage

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The unconditional centre derivative (from the banked displacement bound). -/

/-- **★ `baseVaryingChart_hasFDerivAt_center` — the base-slot chart is differentiable at the centre
    with derivative `-id`.**  DERIVED, UNCONDITIONALLY (given `K ∈ 𝓝 0`), from the banked quadratic
    displacement bound `‖Wbv z + z‖ ≤ C_W ‖z‖²` (`chartW0_displacement`) — which is literally the
    little-o statement of `HasFDerivAt Wbv (-id) 0` — and `Wbv 0 = 0` (`uniformInverseChart_zero`).
    The `K ∈ 𝓝 0` hypothesis is essential: off `K` the chart is the zero default, breaking the bound.
    NOT `a₁ = R/6`. -/
theorem baseVaryingChart_hasFDerivAt_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    HasFDerivAt (fun z => uniformInverseChart g gi hC hK z 0)
      ((ContinuousLinearEquiv.neg ℝ : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n)
      (0 : Point n) := by
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  have hW0 : uniformInverseChart g gi hC hK 0 0 = 0 := uniformInverseChart_zero g gi hC hK h0K
  obtain ⟨r₁, hr₁, C_W, hCW0, hbound⟩ := chartW0_displacement g gi hC hK
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hδpos : (0 : ℝ) < c / (C_W + 1) := by positivity
  filter_upwards [h0Kmem, Metric.ball_mem_nhds (0 : Point n) hr₁,
    Metric.ball_mem_nhds (0 : Point n) hδpos] with y hyK hy1 hyδ
  simp only [zero_add, hW0, sub_zero, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.neg_apply, sub_neg_eq_add]
  have hyr1 : ‖y‖ < r₁ := mem_ball_zero_iff.mp hy1
  have hydv : ‖y‖ < c / (C_W + 1) := mem_ball_zero_iff.mp hyδ
  have hb := hbound y hyK hyr1
  have hcancel : (C_W + 1) * (c / (C_W + 1)) = c := by field_simp
  have hstep : (C_W + 1) * ‖y‖ ≤ c := by
    have h := mul_le_mul_of_nonneg_left hydv.le (show (0 : ℝ) ≤ C_W + 1 by positivity)
    rwa [hcancel] at h
  have h1 : C_W * ‖y‖ ≤ c := by nlinarith [norm_nonneg y]
  calc ‖uniformInverseChart g gi hC hK y 0 + y‖
        ≤ C_W * ‖y‖ * ‖y‖ := hb
    _ ≤ c * ‖y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg y)

/-! ### The base-varying M1–M4 IFT/CoV package (conditional on base-slot `C²` at the centre). -/

/-- **★★ `baseVaryingIFTPackage` — the M1–M4 change-of-variables bundle for the BASE-VARYING chart.**
    Given the geometry (`hC`, `hK`, `K ∈ 𝓝 0`) and the single honest regularity input
    `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`, there is `ρ > 0`, a left inverse `V`, and a derivative field
    `f'` with the FULL CoV bundle on `ball 0 ρ` (M1 within-derivative field, M2 InjOn, M3 left
    inverse, M4 positive Jacobian) plus the image neighbourhood `Wbv '' (ball 0 ρ) ∈ 𝓝 0`.

    Invertibility of the centre derivative (`fderiv Wbv 0 = -id`, `det (-id) = (-1)ⁿ ≠ 0`) is
    supplied by the BANKED displacement bound via `baseVaryingChart_hasFDerivAt_center`, so `-id`
    (not `hbaseC2`) provides the IFT's invertible-derivative input; `hbaseC2` supplies only the
    neighbourhood `C²`.  M2/M3 are PROVEN from `ContDiffAt.toOpenPartialHomeomorph`, NOT assumed.
    This is EXACTLY gap (a) of `ChartImageAIConcrete.chartImage_approx_identity_conditional`.
    NOT `a₁ = R/6`. -/
theorem baseVaryingIFTPackage (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      MeasurableSet (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
            (Metric.ball (0 : Point n) ρ) z)
      ∧ Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          V (uniformInverseChart g gi hC hK z 0) = z)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
      ∧ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)
          ∈ 𝓝 (0 : Point n) := by
  classical
  set Wbv : Point n → Point n := fun z => uniformInverseChart g gi hC hK z 0 with hWbvdef
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  have hWbv0 : Wbv 0 = 0 := uniformInverseChart_zero g gi hC hK h0K
  set e : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.neg ℝ with hedef
  -- The unconditional centre derivative, in the equiv form the IFT needs.
  have hW'0 : HasFDerivAt Wbv ((e : Point n →L[ℝ] Point n)) 0 := by
    rw [hWbvdef, hedef]
    exact baseVaryingChart_hasFDerivAt_center g gi hC hK h0Kmem
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hfderiv0 : fderiv ℝ Wbv 0 = (e : Point n →L[ℝ] Point n) := hW'0.fderiv
  -- The IFT open partial homeomorph of `Wbv` at `0`.
  set Φ := hbaseC2.toOpenPartialHomeomorph Wbv hW'0 hn2 with hΦdef
  have hΦcoe : (⇑Φ : Point n → Point n) = Wbv := by
    rw [hΦdef]; exact hbaseC2.toOpenPartialHomeomorph_coe hW'0 hn2
  have h0src : (0 : Point n) ∈ Φ.source := by
    rw [hΦdef]; exact hbaseC2.mem_toOpenPartialHomeomorph_source hW'0 hn2
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.isOpen_iff.mp Φ.open_source 0 h0src
  -- C² on a neighbourhood ⟹ differentiability field near 0.
  have hevC2 : ∀ᶠ y in 𝓝 (0 : Point n), ContDiffAt ℝ 2 Wbv y := hbaseC2.eventually (by norm_num)
  have hevdiff : ∀ᶠ y in 𝓝 (0 : Point n), DifferentiableAt ℝ Wbv y :=
    hevC2.mono (fun _ hy => hy.differentiableAt (by norm_num))
  -- Jacobian-determinant continuity at 0, with value `det (-id) = (-1)ⁿ ≠ 0`.
  have hfderiv_cont : ContinuousAt (fun y => fderiv ℝ Wbv y) 0 :=
    (hbaseC2.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hdetabs_cont : ContinuousAt (fun y => |(fderiv ℝ Wbv y).det|) 0 :=
    (continuous_abs.continuousAt).comp
      ((ContinuousLinearMap.continuous_det.continuousAt).comp hfderiv_cont)
  have hdet0_ne : (fderiv ℝ Wbv 0).det ≠ 0 := by
    rw [hfderiv0]
    have hcoe : (e : Point n →L[ℝ] Point n) = -ContinuousLinearMap.id ℝ (Point n) := by
      ext x; simp [hedef]
    rw [hcoe]
    show LinearMap.det (((-ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n) ≠ 0
    have hL : (((-ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n) = (-1 : ℝ) • LinearMap.id := by
      ext x; simp
    rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ (by norm_num)
  have hdet0abs : (0 : ℝ) < |(fderiv ℝ Wbv 0).det| := abs_pos.mpr hdet0_ne
  have hevdet : ∀ᶠ y in 𝓝 (0 : Point n),
      |(fderiv ℝ Wbv 0).det| / 2 < |(fderiv ℝ Wbv y).det| :=
    hdetabs_cont.tendsto.eventually (eventually_gt_nhds (by linarith [hdet0abs]))
  -- Combine into a single small ball.
  obtain ⟨ε, hε, hεspec⟩ := Metric.eventually_nhds_iff.mp (hevdiff.and hevdet)
  refine ⟨min δ₁ ε, lt_min hδ₁ hε, (⇑Φ.symm : Point n → Point n),
    (fun z => fderiv ℝ Wbv z), measurableSet_ball, ?_, ?_, ?_, ?_, ?_⟩
  · -- M1: within-derivative field.
    intro z hz
    have hzε : dist z (0 : Point n) < ε :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    exact ((hεspec hzε).1.hasFDerivAt).hasFDerivWithinAt
  · -- M2: injectivity on the ball, from `Φ.injOn`.
    have hinjS : Set.InjOn (⇑Φ) Φ.source := Φ.injOn
    rw [hΦcoe] at hinjS
    exact hinjS.mono (fun z hz => hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz))
  · -- M3: `Φ.symm` is a left inverse on the ball.
    intro z hz
    have hzsrc : z ∈ Φ.source :=
      hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz)
    have h := Φ.left_inv hzsrc
    have hcz : (⇑Φ : Point n → Point n) z = Wbv z := congrFun hΦcoe z
    rw [hcz] at h; exact h
  · -- M4: positive Jacobian.
    intro z hz
    have hzε : dist z (0 : Point n) < ε :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    have := (hεspec hzε).2
    have hpos : (0 : ℝ) < |(fderiv ℝ Wbv z).det| := by linarith [hdet0abs]
    exact hpos
  · -- image neighbourhood glue.
    have hopen : IsOpen ((⇑Φ) '' Metric.ball (0 : Point n) (min δ₁ ε)) :=
      Φ.isOpen_image_of_subset_source Metric.isOpen_ball
        (fun z hz => hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz))
    rw [hΦcoe] at hopen
    have hmem : (0 : Point n) ∈ Wbv '' Metric.ball (0 : Point n) (min δ₁ ε) :=
      ⟨0, Metric.mem_ball_self (lt_min hδ₁ hε), hWbv0⟩
    exact hopen.mem_nhds hmem

end QIQTH.BaseVaryingIFTPackage

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.BaseVaryingIFTPackage
#print axioms baseVaryingChart_hasFDerivAt_center
#print axioms baseVaryingIFTPackage
end AxiomChecks
