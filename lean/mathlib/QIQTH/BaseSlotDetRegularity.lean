/-
  BaseSlotDetRegularity — J4-931: the DETERMINANT-FACTOR regularity brick for obstruction (iii) of
  J4-929's `hCensusBound` wall, on the BASE ball.  Discharges the concrete `1/|det (fderiv Wbv)|`
  (and paired-weight `P/|det|`) boundedness + center-Lipschitz — the determinant/ratio HALF of
  obstruction (iii) — conditional on the SAME honest residual `hbaseC2` as J4-930.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## THE WALL THIS ADDRESSES.  J4-929 localized the whole live `hCross` (h,k>0) binder to a single
  scalar census inequality `hCensusBound`, whose opaque residue = the chart change-of-variables.
  J4-930 discharged obstruction (i) (base-slot vs field-slot CoV mismatch), banking the base-slot CoV
  whose transformed weight is `B(V w)/|det (f'(V w))|` with `f' z = fderiv ℝ Wbv z` on `ball 0 ρ`.
  gpt-5.6-sol's NO-GO audit left obstructions (ii) (`ball 0 ρ` vs `ℝⁿ` tail) and (iii) (the concrete
  transformed weights bounded + center-Lipschitz, likely bottleneck `1/|det|`).

  ## WHAT LANDS (all conditional on `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`, the J4-930 residual).
    • `det_clm_contDiff` — ★ `A ↦ A.det` is `C^∞` on `Point n →L[ℝ] Point n` (mirror of Mathlib's
        `ContinuousLinearMap.continuous_det`, upgraded from `Continuous` to `ContDiff` via
        `JacobiFormula.matrix_det_contDiff` composed with the CLM→matrix continuous-linear bridge).
        This is the piece J4-925's header flagged ABSENT — supplied here by the COMPOSITION route
        (`det ∘ fderiv` is `C¹`), NOT a manual quantitative `|det A − det B| ≤ C‖A−B‖` bound.
    • `det_fderiv_contDiffAt` — ★ `z ↦ (fderiv ℝ Wbv z).det` is `ContDiffAt ℝ 1` at `0`
        (`ContDiffAt.fderiv_right hbaseC2` ∘ `det_clm_contDiff`).
    • `det_fderiv_lipschitzOn_ball` — ★ the resulting pairwise Lipschitz of the signed determinant on
        a base ball (`AmpQuantBundle.contDiffAt_one_lipschitzOn_ball`, the convex-MVT technique).
    • `absdet_fderiv_boundedBelow_ball` — ★ `1/2 ≤ |(fderiv Wbv z).det|` on a base ball (det continuity
        + `chartW0_absdet_fderiv_zero`: `|det (fderiv Wbv 0)| = 1`).
    • `det_fderiv_regularity_bundle` — ★★ THE MAIN BRICK: `∃ r>0 ∃ L_D≥0`, `|det| ≥ 1/2` AND `det`
        pairwise-Lipschitz `L_D` on `ball 0 r`.  Exactly the `D`-side input J4-925's glue consumes.
    • `recip_absdet_center_lipschitz` — ★★ `1/|det (fderiv Wbv)|` bounded by `2` and CENTER-Lipschitz
        on a base ball (feeds `reciprocal_abs_center_lipschitz`; the `two_term_census` `hcl` shape).
    • `paired_ratio_center_lipschitz` — ★★ for ANY bounded (`M_P`) + Lipschitz (`L_P`) weight `P`
        (e.g. `amp·F`), `P/|det (fderiv Wbv)|` is bounded by `2M_P` and pairwise-Lipschitz on the base
        ball (feeds `ratio_abs_lipschitzOn`).  THIS is the full obstruction-(iii) shape, on the base ball.

  ## HONEST STATUS.  Discharges the DETERMINANT/RATIO half of obstruction (iii) — but on the BASE
  (pre-image) ball, with `D z := det (fderiv Wbv z)`.  The CoV weight is on the IMAGE variable,
  `w ↦ q(V w)` with `q z := B z/|det (fderiv Wbv z)|`: boundedness transports by range containment,
  but CENTER-Lipschitz of `q∘V` genuinely needs the inverse `V` to be locally (center-)Lipschitz —
  the remaining transport, NOT built here (per gpt-5.6-sol: the true remaining bottleneck).  So this
  is a genuine advance on obstruction (iii), not its full closure.  Obstruction (ii) (`ball` vs `ℝⁿ`
  tail) and the `∘V` transport REMAIN, so `hCensusBound` / `hCross` are NOT closed.  `hDuhamel`/
  `hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GaussTauTraceChartDetFactor
import QIQTH.AmpQuantBundle
import QIQTH.ChartW0Fderiv
import QIQTH.JacobiFormula

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open scoped Topology BigOperators Matrix.Norms.Elementwise

namespace QIQTH.BaseSlotDetRegularity

variable {n : ℕ}

/-! ###############################################################################
    ### §A — `A ↦ A.det` is `C^∞` (the composition route to det-regularity).
    ############################################################################### -/

/-- **★ `det_clm_contDiff` — the operator determinant is `C^∞`.**  `A ↦ A.det` on
    `Point n →L[ℝ] Point n` is `ContDiff ℝ ⊤`.  This is the Mathlib `ContinuousLinearMap.continuous_det`
    pattern upgraded from `Continuous` to `ContDiff`: `A.det = Matrix.det (Ψ A)` where
    `Ψ = toContinuousLinearMap (toMatrix'.toLinearMap ∘ₗ coeLM ℝ)` is a continuous linear map
    (finite-dimensional), and `JacobiFormula.matrix_det_contDiff` supplies smoothness of `Matrix.det`.
    Supplies the piece J4-925's header flagged ABSENT, via COMPOSITION (no manual `|det A−det B|` bound).
    ⚠ NOT `a₁ = R/6`. -/
theorem det_clm_contDiff :
    ContDiff ℝ (1 : WithTop ℕ∞) (fun A : Point n →L[ℝ] Point n => A.det) := by
  -- The continuous-linear CLM→matrix bridge `A ↦ toMatrix' (A : →ₗ)`.
  set Ψ : (Point n →L[ℝ] Point n) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toMatrix' :
          ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ).toLinearMap.comp
        (ContinuousLinearMap.coeLM ℝ)) with hΨdef
  have hΨapp : ∀ A : Point n →L[ℝ] Point n,
      (Ψ A) = LinearMap.toMatrix' (A : Point n →ₗ[ℝ] Point n) := by
    intro A; simp [hΨdef]
  have hval : (fun A : Point n →L[ℝ] Point n => A.det)
      = (Matrix.det) ∘ (fun A : Point n →L[ℝ] Point n => Ψ A) := by
    funext A
    show A.det = Matrix.det (Ψ A)
    rw [hΨapp A]
    show LinearMap.det (A : Point n →ₗ[ℝ] Point n) = Matrix.det _
    rw [LinearMap.det_toMatrix']
  rw [hval]
  have hle : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  exact ((QIQTH.JacobiFormula.matrix_det_contDiff (n := n)).of_le hle).comp Ψ.contDiff

/-! ###############################################################################
    ### §B — `z ↦ (fderiv Wbv z).det` is `ContDiffAt 1`, hence locally Lipschitz.
    ############################################################################### -/

/-- **★ `det_fderiv_contDiffAt`.**  For the base-varying chart `Wbv z = uniformInverseChart g gi hC hK z 0`,
    given `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`, the map `z ↦ (fderiv ℝ Wbv z).det` is `ContDiffAt ℝ 1` at `0`.
    Route: `ContDiffAt.fderiv_right hbaseC2` (`fderiv Wbv` is `C¹` at `0`, `1+1≤2`) composed with
    `det_clm_contDiff`.  ⚠ NOT `a₁ = R/6`. -/
theorem det_fderiv_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ContDiffAt ℝ 1 (fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det)
      (0 : Point n) := by
  have hfd1 : ContDiffAt ℝ 1
      (fun z => fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z) (0 : Point n) :=
    hbaseC2.fderiv_right (by norm_num)
  exact ((det_clm_contDiff (n := n)).contDiffAt).comp (0 : Point n) hfd1

/-- **★ `det_fderiv_lipschitzOn_ball`.**  The signed determinant `z ↦ (fderiv ℝ Wbv z).det` is pairwise
    Lipschitz on a base ball around `0`.  Route: `det_fderiv_contDiffAt` fed to the convex-MVT technique
    `AmpQuantBundle.contDiffAt_one_lipschitzOn_ball` (the same technique as `chartAmp_base_lipschitzOn_ball`).
    ⚠ NOT `a₁ = R/6`. -/
theorem det_fderiv_lipschitzOn_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ Metric.ball (0 : Point n) r, ∀ y ∈ Metric.ball (0 : Point n) r,
        |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) x).det
            - (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) y).det| ≤ L * dist x y := by
  obtain ⟨r, hr, L, hL, hlip⟩ :=
    QIQTH.AmpQuantBundle.contDiffAt_one_lipschitzOn_ball _
      (det_fderiv_contDiffAt g gi hC hK hbaseC2)
  refine ⟨r, hr, L, hL, ?_⟩
  intro x hx y hy
  have hxb : ‖x‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hyb : ‖y‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hy
  have h := hlip x y hxb hyb
  rwa [Real.norm_eq_abs, ← dist_eq_norm] at h

/-- **★ `absdet_fderiv_boundedBelow_ball`.**  On a base ball around `0`, `|(fderiv ℝ Wbv z).det| ≥ 1/2`.
    Route: `z ↦ (fderiv Wbv z).det` is continuous at `0` (from `det_fderiv_contDiffAt`), and its modulus
    at `0` is `1` (`chartW0_absdet_fderiv_zero`), so it stays `> 1/2` on a neighbourhood.
    ⚠ NOT `a₁ = R/6`. -/
theorem absdet_fderiv_boundedBelow_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ r > (0 : ℝ), ∀ z ∈ Metric.ball (0 : Point n) r,
      (1 / 2 : ℝ) ≤ |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det| := by
  have hcontD : ContinuousAt
      (fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det) (0 : Point n) :=
    (det_fderiv_contDiffAt g gi hC hK hbaseC2).continuousAt
  have hcontAbs : ContinuousAt
      (fun z => |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|) (0 : Point n) :=
    hcontD.abs
  have hval0 : |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)).det| = 1 :=
    QIQTH.ChartW0Fderiv.chartW0_absdet_fderiv_zero g gi hC hK h0Kmem
  have hgt : ∀ᶠ z in 𝓝 (0 : Point n),
      (1 / 2 : ℝ) < |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det| := by
    have hlt : (fun _ : Point n => (1 / 2 : ℝ)) 0
        < (fun z => |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|) 0 := by
      simp only [hval0]; norm_num
    exact continuousAt_const.eventually_lt hcontAbs hlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hgt
  refine ⟨ε, hε, fun z hz => ?_⟩
  have : dist z (0 : Point n) < ε := by simpa [Metric.mem_ball] using hz
  exact le_of_lt (hball this)

/-! ###############################################################################
    ### §C — the MAIN bundle + reciprocal/ratio consumers on the base ball.
    ############################################################################### -/

/-- **★★ `det_fderiv_regularity_bundle` — THE MAIN BRICK.**  On a single base ball `ball 0 r`, the
    signed determinant `D z := (fderiv ℝ Wbv z).det` is bounded below by `1/2` AND pairwise Lipschitz
    (constant `L_D`).  This is EXACTLY the `D`-side input J4-925's `reciprocal_abs_lipschitzOn` /
    `ratio_abs_lipschitzOn` glue consumes.  Combines `det_fderiv_lipschitzOn_ball` and
    `absdet_fderiv_boundedBelow_ball` on the common radius `min`.  ⚠ NOT `a₁ = R/6`. -/
theorem det_fderiv_regularity_bundle (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ r > (0 : ℝ), ∃ L_D : ℝ, 0 ≤ L_D ∧
      (∀ z ∈ Metric.ball (0 : Point n) r,
        (1 / 2 : ℝ) ≤ |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|) ∧
      (∀ x ∈ Metric.ball (0 : Point n) r, ∀ y ∈ Metric.ball (0 : Point n) r,
        |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) x).det
            - (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) y).det| ≤ L_D * dist x y) := by
  obtain ⟨rL, hrL, L_D, hLD, hlip⟩ := det_fderiv_lipschitzOn_ball g gi hC hK hbaseC2
  obtain ⟨rc, hrc, hlb⟩ := absdet_fderiv_boundedBelow_ball g gi hC hK h0Kmem hbaseC2
  refine ⟨min rL rc, lt_min hrL hrc, L_D, hLD, ?_, ?_⟩
  · intro z hz
    exact hlb z (Metric.ball_subset_ball (min_le_right _ _) hz)
  · intro x hx y hy
    exact hlip x (Metric.ball_subset_ball (min_le_left _ _) hx)
      y (Metric.ball_subset_ball (min_le_left _ _) hy)

/-- **★★ `recip_absdet_center_lipschitz`.**  On a base ball, `w ↦ 1/|det (fderiv Wbv w)|` is bounded by
    `2` and CENTER-Lipschitz at `0`.  Feeds `two_term_census`'s `hcl` binder.  Combines the main bundle
    with J4-925's `reciprocal_abs_center_lipschitz` (`c = 1/2`, `1/c = 2`).  ⚠ NOT `a₁ = R/6`. -/
theorem recip_absdet_center_lipschitz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ r > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧
      (∀ z ∈ Metric.ball (0 : Point n) r,
        abs ((1 : ℝ) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|) ≤ 2) ∧
      (∀ z ∈ Metric.ball (0 : Point n) r,
        abs ((1 : ℝ) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|
            - 1 / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) 0).det|) ≤ C * ‖z‖) := by
  obtain ⟨r, hr, L_D, hLD, hlb, hlip⟩ :=
    det_fderiv_regularity_bundle g gi hC hK h0Kmem hbaseC2
  set D : Point n → ℝ :=
    fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det with hDdef
  obtain ⟨hb, hl⟩ :=
    reciprocal_abs_center_lipschitz (n := n) r D (1 / 2) L_D (by norm_num) hLD hr hlb hlip
  refine ⟨r, hr, L_D / (1 / 2 : ℝ) ^ 2, by positivity, ?_, ?_⟩
  · intro z hz
    exact (hb z hz).trans_eq (by norm_num)
  · intro z hz
    exact hl z hz

/-- **★★ `paired_ratio_center_lipschitz` — obstruction (iii) shape on the base ball.**  On a base ball,
    for ANY bounded (`M_P`) + pairwise-Lipschitz (`L_P`) real weight `P` (e.g. `amp·F`), the ratio
    `w ↦ P w / |det (fderiv Wbv w)|` is bounded by `2·M_P` and pairwise Lipschitz.  Combines the main
    bundle with J4-925's `ratio_abs_lipschitzOn` (`c = 1/2`).  This is the FULL obstruction-(iii)
    boundedness + Lipschitz shape, on the base (pre-image) ball.  ⚠ NOT `a₁ = R/6`. -/
theorem paired_ratio_center_lipschitz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ r > (0 : ℝ), ∃ L_D : ℝ, 0 ≤ L_D ∧
      ∀ (P : Point n → ℝ) (M_P L_P : ℝ), 0 ≤ M_P → 0 ≤ L_P →
        (∀ z ∈ Metric.ball (0 : Point n) r, |P z| ≤ M_P) →
        (∀ x ∈ Metric.ball (0 : Point n) r, ∀ y ∈ Metric.ball (0 : Point n) r,
          |P x - P y| ≤ L_P * dist x y) →
        (∀ z ∈ Metric.ball (0 : Point n) r,
          abs (P z / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|)
            ≤ M_P / (1 / 2 : ℝ)) ∧
        (∀ x ∈ Metric.ball (0 : Point n) r, ∀ y ∈ Metric.ball (0 : Point n) r,
          abs (P x / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) x).det|
              - P y / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) y).det|)
            ≤ (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * dist x y) := by
  obtain ⟨r, hr, L_D, hLD, hlb, hlip⟩ :=
    det_fderiv_regularity_bundle g gi hC hK h0Kmem hbaseC2
  refine ⟨r, hr, L_D, hLD, ?_⟩
  intro P M_P L_P hMP hLP hPbnd hPlip
  exact ratio_abs_lipschitzOn (n := n) (Metric.ball (0 : Point n) r) P
    (fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det)
    M_P L_P (1 / 2) L_D hMP hLP (by norm_num) hLD hPbnd hPlip hlb hlip

/-! ###############################################################################
    ### §D — non-vacuity (the hypothesis `hbaseC2` is genuinely satisfiable).
    ############################################################################### -/

/-- **Non-vacuity: `det_clm_contDiff` is genuinely non-trivial.**  Exhibits a point where the operator
    determinant is `≠ 0` and the map is genuinely evaluated: `(2 • id).det = 2^n ≠ 0` (n≥1 makes it
    varying, but even n=0 gives `1`).  Confirms `det_clm_contDiff` is not the zero map / vacuous.
    ⚠ NOT `a₁ = R/6`. -/
theorem det_clm_contDiff_nonvacuous :
    ((2 : ℝ) • ContinuousLinearMap.id ℝ (Point n)).det = (2 : ℝ) ^ n := by
  show LinearMap.det (((2 : ℝ) • ContinuousLinearMap.id ℝ (Point n)) : Point n →ₗ[ℝ] Point n) = _
  have hL : (((2 : ℝ) • ContinuousLinearMap.id ℝ (Point n)) : Point n →ₗ[ℝ] Point n)
      = (2 : ℝ) • LinearMap.id := by ext x; simp
  rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp

end QIQTH.BaseSlotDetRegularity

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BaseSlotDetRegularity
#print axioms det_clm_contDiff
#print axioms det_fderiv_contDiffAt
#print axioms det_fderiv_lipschitzOn_ball
#print axioms absdet_fderiv_boundedBelow_ball
#print axioms det_fderiv_regularity_bundle
#print axioms recip_absdet_center_lipschitz
#print axioms paired_ratio_center_lipschitz
#print axioms det_clm_contDiff_nonvacuous
end AxiomChecks
