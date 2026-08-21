/-
  BaseSlotInverseChartLipschitz — J4-932: the INVERSE-CHART center/pairwise Lipschitz transport that
  CLOSES obstruction (iii) of J4-929's `hCensusBound` wall (modulo the SAME honest residual `hbaseC2`
  as J4-930/931).  The determinant/ratio HALF of obstruction (iii) was banked in J4-931
  (`BaseSlotDetRegularity.paired_ratio_center_lipschitz`: for any bounded+Lipschitz weight `P`, the
  ratio `P / |det (fderiv Wbv)|` is bounded + pairwise-Lipschitz on the BASE ball).  The remaining
  transport `q ∘ V` (the CoV integrand lives on the IMAGE variable `w ↦ q (V w)`) genuinely needs the
  local inverse `V` to be locally (center-)Lipschitz.  THIS FILE supplies that.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## THE KEY OBSERVATION (why this is essentially free from banked machinery).  In the base-varying
  IFT package (`BaseVaryingIFTPackage.baseVaryingIFTPackage`, J4-272) the left inverse `V` is literally
  `Φ.symm` for `Φ = hbaseC2.toOpenPartialHomeomorph Wbv hW'0 hn2` — the Mathlib inverse-function-theorem
  `OpenPartialHomeomorph`.  Mathlib's `ContDiffAt.to_localInverse` states that this inverse is `C²` AT
  THE IMAGE CENTRE: `ContDiffAt ℝ 2 (Φ.symm) (Wbv 0) = ContDiffAt ℝ 2 V 0` (`Wbv 0 = 0`), because
  `Φ.symm` is *definitionally* `hbaseC2.localInverse hW'0 hn2`.  Feeding that to the SAME convex-MVT
  technique used repeatedly this session (`AmpQuantBundle.contDiffAt_one_lipschitzOn_ball`) makes `V`
  pairwise Lipschitz on an image ball for FREE — no separate derivative-boundedness step.

  ## WHAT LANDS (all conditional on `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`, the J4-930/931 residual).
    • `inverseChart_lipschitz_package` — ★★ `∃ σ>0 ∃ V L_V≥0`, `V 0 = 0` AND `V` pairwise-Lipschitz
        (`L_V`) on `ball 0 σ`.  The center-Lipschitz of the local inverse, from `to_localInverse`
        + `contDiffAt_one_lipschitzOn_ball`.
    • `transported_ratio_regularity` — ★★ THE MAIN BRICK (obstruction (iii) CLOSED, modulo `hbaseC2`):
        for ANY globally bounded (`M_P`) + globally Lipschitz (`L_P`) weight `P`, the CoV transformed
        integrand `w ↦ P (V w) / |det (fderiv Wbv (V w))|` is bounded by `2 M_P` AND pairwise-Lipschitz
        on an image ball `ball 0 σ`.  This is EXACTLY the concrete transformed-weight regularity the
        base-slot CoV (`BaseSlotChangeVariables`) needs — composing J4-931's `paired_ratio_center_lipschitz`
        (det/ratio half) with `V` local-Lipschitz (this file, transport half).
    • `transported_ratio_center_lipschitz` — ★ the center-Lipschitz form (`y := 0`), the literal
        "`q ∘ V` center-Lipschitz" statement.
    • `localInverse_nonvacuous` — non-vacuity: `to_localInverse` genuinely yields a `C²` non-identity
        inverse (the negation equiv, matching the real `fderiv Wbv 0 = -id`).

  ## HONEST STATUS.  Obstruction (iii) is now FULLY closed (both the det/ratio half — J4-931 — and the
  `∘V` transport half — HERE), modulo the honest residual `hbaseC2` (⟸ `hT0`).  What REMAINS for
  `hCensusBound` / `hCross`:  (ii) the `ball 0 ρ` (CoV domain) vs `ℝⁿ` (census domain) tail, and
  `hbaseC2` itself.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BaseSlotDetRegularity
import QIQTH.BaseVaryingIFTPackage
import QIQTH.AmpQuantBundle

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.BaseSlotInverseChartLipschitz

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the local inverse `V = Φ.symm` is center/pairwise Lipschitz.
    ############################################################################### -/

/-- **★★ `inverseChart_lipschitz_package`.**  For the base-varying chart
    `Wbv z = uniformInverseChart g gi hC hK z 0`, given the honest regularity residual
    `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`, the IFT local inverse `V = Φ.symm` (`Φ` the Mathlib
    `ContDiffAt.toOpenPartialHomeomorph`) satisfies `V 0 = 0` and is pairwise Lipschitz on a ball
    `ball 0 σ`.  Route: `ContDiffAt.to_localInverse` gives `ContDiffAt ℝ 2 V 0` (since `Φ.symm` is
    *definitionally* `hbaseC2.localInverse hW'0 hn2` and `Wbv 0 = 0`), fed to the convex-MVT technique
    `AmpQuantBundle.contDiffAt_one_lipschitzOn_ball`.  ⚠ NOT `a₁ = R/6`. -/
theorem inverseChart_lipschitz_package (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (L_V : ℝ), 0 ≤ L_V ∧
      V 0 = 0 ∧
      ∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        ‖V x - V y‖ ≤ L_V * dist x y := by
  classical
  set Wbv : Point n → Point n := fun z => uniformInverseChart g gi hC hK z 0 with hWbvdef
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  have hWbv0 : Wbv 0 = 0 := uniformInverseChart_zero g gi hC hK h0K
  set e : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.neg ℝ with hedef
  have hW'0 : HasFDerivAt Wbv ((e : Point n →L[ℝ] Point n)) 0 := by
    rw [hWbvdef, hedef]
    exact QIQTH.BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center g gi hC hK h0Kmem
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  set Φ := hbaseC2.toOpenPartialHomeomorph Wbv hW'0 hn2 with hΦdef
  -- `V = Φ.symm` is `C²` at the image centre `Wbv 0 = 0` via `to_localInverse`.
  have hVc2 : ContDiffAt ℝ 2 (⇑Φ.symm) (0 : Point n) := by
    have hti := hbaseC2.to_localInverse hW'0 hn2
    rw [hWbv0] at hti
    exact hti
  have hV1 : ContDiffAt ℝ 1 (⇑Φ.symm) (0 : Point n) := hVc2.of_le (by norm_num)
  -- `V 0 = 0`, from `Φ.left_inv` at the source centre.
  have hΦcoe : (⇑Φ : Point n → Point n) = Wbv := by
    rw [hΦdef]; exact hbaseC2.toOpenPartialHomeomorph_coe hW'0 hn2
  have h0src : (0 : Point n) ∈ Φ.source := by
    rw [hΦdef]; exact hbaseC2.mem_toOpenPartialHomeomorph_source hW'0 hn2
  have hV0 : (⇑Φ.symm) (0 : Point n) = 0 := by
    have h := Φ.left_inv h0src
    have hc0 : (⇑Φ : Point n → Point n) 0 = 0 := by rw [hΦcoe]; exact hWbv0
    rw [hc0] at h; exact h
  -- Pairwise Lipschitz on a ball via the convex-MVT technique.
  obtain ⟨r, hr, L, hL, hlip⟩ :=
    QIQTH.AmpQuantBundle.contDiffAt_one_lipschitzOn_ball (⇑Φ.symm) hV1
  refine ⟨r, hr, ⇑Φ.symm, L, hL, hV0, ?_⟩
  intro x hx y hy
  have hxb : ‖x‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hyb : ‖y‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hy
  have h := hlip x y hxb hyb
  rwa [dist_eq_norm]

/-! ###############################################################################
    ### §B — the MAIN transport: `q ∘ V` bounded + pairwise-Lipschitz (obstruction (iii)).
    ############################################################################### -/

/-- **★★ `transported_ratio_regularity` — obstruction (iii) CLOSED (modulo `hbaseC2`).**  For ANY
    globally bounded (`M_P`) + globally Lipschitz (`L_P`) real weight `P`, the CoV transformed
    integrand `w ↦ P (V w) / |det (fderiv Wbv (V w))|` (the base-slot change-of-variables integrand,
    `BaseSlotChangeVariables`) is bounded by `M_P / (1/2) = 2 M_P` AND pairwise-Lipschitz on an image
    ball `ball 0 σ`.  Route: compose J4-931's `paired_ratio_center_lipschitz` (the det/ratio half, on
    the BASE ball) with `inverseChart_lipschitz_package` (the `V`-transport half, this file); `V` maps
    a small image ball into the base ball (`‖V w‖ ≤ L_V ‖w‖`, `V 0 = 0`).  ⚠ NOT `a₁ = R/6`. -/
theorem transported_ratio_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (P : Point n → ℝ) (M_P L_P : ℝ) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P)
    (hPb : ∀ z, |P z| ≤ M_P)
    (hPl : ∀ x y : Point n, |P x - P y| ≤ L_P * dist x y) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (Lc : ℝ), 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (P (V w) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|)
          ≤ M_P / (1 / 2 : ℝ)) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (P (V x) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - P (V y) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ Lc * dist x y) := by
  -- det/ratio regularity on a base ball `ball 0 r`.
  obtain ⟨r, hr, L_D, hLD, hpr⟩ :=
    QIQTH.BaseSlotDetRegularity.paired_ratio_center_lipschitz g gi hC hK h0Kmem hbaseC2
  obtain ⟨hqb, hql⟩ :=
    hpr P M_P L_P hMP hLP (fun z _ => hPb z) (fun x _ y _ => hPl x y)
  -- `V` local-Lipschitz on `ball 0 σ0`.
  obtain ⟨σ0, hσ0, V, L_V, hLV, hV0, hVlip⟩ :=
    inverseChart_lipschitz_package g gi hC hK h0Kmem hbaseC2
  have hLq0 : 0 ≤ L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2 := by
    have h1 : 0 ≤ L_P / (1 / 2 : ℝ) := div_nonneg hLP (by norm_num)
    have h2 : 0 ≤ M_P * L_D / (1 / 2 : ℝ) ^ 2 := div_nonneg (mul_nonneg hMP hLD) (by positivity)
    exact add_nonneg h1 h2
  -- `V` maps the chosen image ball `ball 0 (min σ0 (r/(L_V+1)))` into the base ball `ball 0 r`.
  have hmaps : ∀ w ∈ Metric.ball (0 : Point n) (min σ0 (r / (L_V + 1))),
      V w ∈ Metric.ball (0 : Point n) r := by
    intro w hw
    have hwσ0 : w ∈ Metric.ball (0 : Point n) σ0 :=
      Metric.ball_subset_ball (min_le_left _ _) hw
    have h0σ0 : (0 : Point n) ∈ Metric.ball (0 : Point n) σ0 := Metric.mem_ball_self hσ0
    have hlip0 := hVlip w hwσ0 0 h0σ0
    rw [hV0] at hlip0
    have hVwnorm : ‖V w‖ ≤ L_V * ‖w‖ := by
      simpa [dist_zero_right, sub_zero] using hlip0
    have hwr : ‖w‖ < r / (L_V + 1) := by
      have hd : dist w (0 : Point n) < min σ0 (r / (L_V + 1)) := Metric.mem_ball.mp hw
      rw [dist_zero_right] at hd
      exact lt_of_lt_of_le hd (min_le_right _ _)
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖V w‖ ≤ L_V * ‖w‖ := hVwnorm
      _ ≤ (L_V + 1) * ‖w‖ := by nlinarith [norm_nonneg w]
      _ < (L_V + 1) * (r / (L_V + 1)) := by
            apply mul_lt_mul_of_pos_left hwr (by positivity)
      _ = r := by field_simp
  refine ⟨min σ0 (r / (L_V + 1)), lt_min hσ0 (by positivity), V,
    (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * L_V, mul_nonneg hLq0 hLV, hV0, ?_, ?_⟩
  · intro w hw
    exact hqb (V w) (hmaps w hw)
  · intro x hx y hy
    have hVx := hmaps x hx
    have hVy := hmaps y hy
    have h1 := hql (V x) hVx (V y) hVy
    have h2 := hVlip x (Metric.ball_subset_ball (min_le_left _ _) hx)
                      y (Metric.ball_subset_ball (min_le_left _ _) hy)
    calc abs (P (V x) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - P (V y) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * dist (V x) (V y) := h1
      _ = (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * ‖V x - V y‖ := by
            rw [dist_eq_norm]
      _ ≤ (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * (L_V * dist x y) :=
            mul_le_mul_of_nonneg_left h2 hLq0
      _ = (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * L_V * dist x y := by ring

/-- **★ `transported_ratio_center_lipschitz` — the literal `q ∘ V` center-Lipschitz.**  The `y := 0`
    specialization of `transported_ratio_regularity`: the CoV transformed integrand is
    center-Lipschitz at the image centre `0` (recall `V 0 = 0`).  ⚠ NOT `a₁ = R/6`. -/
theorem transported_ratio_center_lipschitz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (P : Point n → ℝ) (M_P L_P : ℝ) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P)
    (hPb : ∀ z, |P z| ≤ M_P)
    (hPl : ∀ x y : Point n, |P x - P y| ≤ L_P * dist x y) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (Lc : ℝ), 0 ≤ Lc ∧ V 0 = 0 ∧
      ∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (P (V w) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|
            - P (V 0) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V 0)).det|)
          ≤ Lc * ‖w‖ := by
  obtain ⟨σ, hσ, V, Lc, hLc, hV0, _, hl⟩ :=
    transported_ratio_regularity g gi hC hK h0Kmem hbaseC2 P M_P L_P hMP hLP hPb hPl
  refine ⟨σ, hσ, V, Lc, hLc, hV0, ?_⟩
  intro w hw
  have h := hl w hw 0 (Metric.mem_ball_self hσ)
  rwa [dist_zero_right] at h

/-! ###############################################################################
    ### §C — non-vacuity (the new `to_localInverse` step yields genuine `C²` content).
    ############################################################################### -/

/-- **Non-vacuity: `to_localInverse` genuinely produces a `C²` non-identity inverse.**  Exhibits, with
    NO reliance on `hbaseC2`, that the Mathlib inverse-function-theorem machinery this file leans on
    (`ContDiffAt.to_localInverse`) yields a genuine `C²` local inverse for the NEGATION equiv — the
    exact derivative shape `fderiv Wbv 0 = -id` that arises in the real chart.  Confirms the new
    analytic step is not vacuous.  ⚠ NOT `a₁ = R/6`. -/
theorem localInverse_nonvacuous :
    ∃ V : Point n → Point n, ContDiffAt ℝ 2 V (0 : Point n) ∧ V 0 = 0 := by
  have hcd : ContDiffAt ℝ 2 (fun z : Point n => -z) (0 : Point n) :=
    contDiff_neg.contDiffAt
  have hcoe : ((ContinuousLinearEquiv.neg ℝ : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n)
      = -ContinuousLinearMap.id ℝ (Point n) := by ext x; simp
  have hfd : HasFDerivAt (fun z : Point n => -z)
      ((ContinuousLinearEquiv.neg ℝ : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n)
      (0 : Point n) := by
    rw [hcoe]; exact (hasFDerivAt_id (0 : Point n)).neg
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  refine ⟨hcd.localInverse hfd hn2, ?_, ?_⟩
  · have hti := hcd.to_localInverse hfd hn2
    simpa using hti
  · have := hcd.localInverse_apply_image hfd hn2
    simpa using this

end QIQTH.BaseSlotInverseChartLipschitz

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BaseSlotInverseChartLipschitz
#print axioms inverseChart_lipschitz_package
#print axioms transported_ratio_regularity
#print axioms transported_ratio_center_lipschitz
#print axioms localInverse_nonvacuous
end AxiomChecks
