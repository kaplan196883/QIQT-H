/-
  HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge — J4-1024: generalizing the
  `V`/Jacobian-composition Lipschitz-at-0 mechanism (`BaseSlotInverseChartLipschitz`/
  `BaseSlotDetRegularity`, previously fixed at `q₀ = 0` and CONDITIONAL on an honest residual
  `hbaseC2`) to a GENERAL interior point `q₀`, UNCONDITIONALLY, and bridging the result into
  `HCompNearCarryTerm1DomainRestrictedBound`'s (J4-1023) abstract `Amp`-interface — the gap J4-1023
  explicitly flagged as NEW and unaddressed (the literal `nb` BRICK 2 integrand `Bfac(V w)/|det(fderiv
  W (V w))|` is NOT simply an abstract `Amp w`).  Sol (`gpt-5.6-sol`, high, 2026-08-23) plan-reviewed
  before Lean.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT'S NEW HERE (vs the pre-existing `BaseSlotInverseChartLipschitz`/`BaseSlotDetRegularity`).

  The pre-existing files fixed the field point at `q₀ = 0` and CARRIED an explicit hypothesis
  `hbaseC2 : ContDiffAt ℝ 2 Wbv 0` as an "honest residual" (not yet discharged there).  Meanwhile, a
  LATER dispatch (J4-1007/1008, `BaseSlotIFTLocalHomeomorph`/`BaseSlotM1M4Assembly`) banked an
  UNCONDITIONAL general-`q₀` analogue of exactly that fact:
  `BaseSlotIFTLocalHomeomorph.uniformInverseChart_baseSlot_contDiffAt_generalK` gives
  `ContDiffAt ℝ 2 W q₀` (`W p := uniformInverseChart g gi hC hK p q₀`) from ONLY `hK : IsCompact K` and
  `hq₀ : q₀ ∈ interior K` — NO extra hypothesis.  Composed with the (also unconditional)
  `HerrHminGeneralQ0GeneralK.uniformInverseChart_baseSlot_fderiv_neg_id_generalK`
  (`HasFDerivAt W (−Id) q₀`), the ENTIRE `hbaseC2`-conditional machinery of the two older files
  becomes UNCONDITIONAL when re-run at general `q₀` — this file re-derives it that way.

  ## WHAT LANDS.
    • §A `uniformInverseChart_baseSlot_inverse_lipschitz_package_generalK` — ★★★ UNCONDITIONALLY: the
        IFT local inverse `V` of `W` satisfies `V 0 = q₀` (since `W q₀ = 0`) and is pairwise Lipschitz
        on an IMAGE ball `ball 0 σ`.
    • §B `uniformInverseChart_baseSlot_det_fderiv_regularity_bundle_generalK` — ★★ UNCONDITIONALLY: on a
        BASE ball `ball q₀ r`, `z ↦ (fderiv W z).det` is bounded below by `1/2` and pairwise Lipschitz.
        (New helper `contDiffAt_one_lipschitzOn_ball_atPoint`, §0, shifts `AmpQuantBundle`'s
        zero-based convex-MVT Lipschitz technique to an arbitrary base point, since the pre-existing
        technique only fires at `0`.)
    • §C `transported_ratio_regularity_generalK` — ★★★★ THE MAIN BRICK: for ANY GLOBALLY bounded
        (`M_P`) + GLOBALLY pairwise-Lipschitz (`L_P`) real weight `P : Point n → ℝ`, the CoV transformed
        integrand `w ↦ P (V w) / |det (fderiv W (V w))|` is bounded + pairwise-Lipschitz on an image
        ball `ball 0 σ` — UNCONDITIONALLY, general `q₀`.  Same shape as the old file's
        `transported_ratio_regularity`, minus `hbaseC2`, minus the `q₀ = 0` restriction.
    • §D `amp_of_transported_ratio_global_lipschitz_at_zero` — ★★★★★ THE BRIDGE.  TRUNCATES §C's
        ball-only bound into a GLOBALLY-defined function `AmpExt : Point n → ℝ` (equal to the transported
        ratio inside `ball 0 σ`, constant `= P q₀` outside) satisfying EXACTLY J4-1023's interface:
        `AEStronglyMeasurable AmpExt volume` and `∀ v : Point n, |AmpExt v − AmpExt 0| ≤ L * ‖v‖` — a
        GLOBAL (not ball-restricted) Lipschitz-at-0 bound, for ANY `Point n`, not just the ball.  This is
        the precise interface `HCompNearCarryTerm1DomainRestrictedBound.hsMixed_gaussDdim_mul_amp_
        domain_restricted_bound`'s `hlip`/`hAmp` need.
    • §E `hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio` — ★★★★★
        INSTANTIATES J4-1023's capstone at `Amp := AmpExt` (built from an abstract `P`), giving the
        `nb`-domain-restricted bound for the LITERAL "`P`-composed-with-`V`-over-Jacobian" shape, for
        ANY globally bounded + globally Lipschitz `P`.

  ## HONEST SCOPE — WHAT THIS DOES **NOT** DO.  It does NOT plug in the literal geometric `Bfac`
  (`HCompNearCarryKPrimeBaseFieldCoV`'s 4-term amplitude) as `P`: `Bfac`'s OWN regularity (global
  boundedness + global Lipschitz continuity on ALL of `Point n`) is a SEPARATE, NOT-yet-established gap
  — `Bfac` is currently only characterized POINTWISE ON THE GATE (`z ∈ K`) via BRICK 1's `hfac`
  hypothesis, itself NOT discharged over the IFT-selected domain `S'` (residuals r1/r2 of
  `HCompNearCarryKPrimeBaseFieldCoV`).  So this dispatch closes the "`V`/Jacobian-composition
  Lipschitz-at-0" mechanism — for an ABSTRACT globally-regular `P` — but does NOT close `nb`'s term1
  with the LITERAL integrand.  `Bfac`'s other 3 terms (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`, `∂ⱼ∂ᵢA`) remain untouched
  regardless, and `fb` (far carry) remains SEPARATELY open.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryTerm1DomainRestrictedBound
import QIQTH.BaseSlotIFTLocalHomeomorph
import QIQTH.BaseSlotDetRegularity
import QIQTH.HerrHminGeneralQ0GeneralK
import QIQTH.AmpQuantBundle
import QIQTH.GaussTauTraceChartDetFactor
import QIQTH.HCompNearCarryTerm1AmpWeightedTail

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.BaseSlotIFTLocalHomeomorph QIQTH.BaseSlotDetRegularity
open QIQTH.HerrHminGeneralQ0GeneralK QIQTH.HCompNearCarryTerm1AmpWeightedTail
open QIQTH.HCompNearCarryTerm1DomainRestrictedBound
open scoped Topology

namespace QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §0 — a base-point-shifted convex-MVT Lipschitz helper (generalizing
    ### `AmpQuantBundle.contDiffAt_one_lipschitzOn_ball` off the origin).
    ############################################################################### -/

/-- **`contDiffAt_one_lipschitzOn_ball_atPoint`.**  Shifts `AmpQuantBundle.contDiffAt_one_
    lipschitzOn_ball` (which only fires at basepoint `0`) to an arbitrary basepoint `p`: `ContDiffAt ℝ 1
    f p` gives a ball `ball p r` on which `f` is pairwise Lipschitz. NOT `a₁ = R/6`. -/
theorem contDiffAt_one_lipschitzOn_ball_atPoint
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (p : E) (hf : ContDiffAt ℝ 1 f p) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
      ‖f x - f y‖ ≤ L * dist x y := by
  set g : E → F := fun z => f (p + z) with hgdef
  have hshift : ContDiffAt ℝ 1 (fun z : E => p + z) 0 := contDiffAt_const.add contDiffAt_id
  have hf' : ContDiffAt ℝ 1 f ((fun z : E => p + z) 0) := by simpa using hf
  have hg : ContDiffAt ℝ 1 g 0 := by
    have hcomp := ContDiffAt.comp 0 hf' hshift
    simpa [hgdef, Function.comp] using hcomp
  obtain ⟨r, hr, L, hL, hlip⟩ := QIQTH.AmpQuantBundle.contDiffAt_one_lipschitzOn_ball g hg
  refine ⟨r, hr, L, hL, ?_⟩
  intro x hx y hy
  have hxb : ‖x - p‖ < r := by
    have hd := Metric.mem_ball.mp hx
    rwa [dist_eq_norm] at hd
  have hyb : ‖y - p‖ < r := by
    have hd := Metric.mem_ball.mp hy
    rwa [dist_eq_norm] at hd
  have h := hlip (x - p) (y - p) hxb hyb
  have hgx : g (x - p) = f x := by simp [hgdef]
  have hgy : g (y - p) = f y := by simp [hgdef]
  rw [hgx, hgy] at h
  have hdd : x - p - (y - p) = x - y := by abel
  rw [hdd] at h
  rwa [dist_eq_norm]

/-! ###############################################################################
    ### §A — the local inverse `V` is center/pairwise Lipschitz, GENERAL `q₀`,
    ### UNCONDITIONALLY.
    ############################################################################### -/

/-- **★★★ `uniformInverseChart_baseSlot_inverse_lipschitz_package_generalK`.**  For `W p :=
    uniformInverseChart g gi hC hK p q₀` at ANY `q₀ ∈ interior K` — NO extra hypothesis (unlike the
    older `hbaseC2`-conditional, `q₀ = 0`-fixed `BaseSlotInverseChartLipschitz.inverseChart_lipschitz_
    package`) — the IFT local inverse `V` satisfies `V 0 = q₀` (`W q₀ = 0`) and is pairwise Lipschitz on
    an image ball `ball 0 σ`.  Route: `ContDiffAt.toOpenPartialHomeomorph` fed by the UNCONDITIONAL
    `uniformInverseChart_baseSlot_contDiffAt_generalK` (J4-1007) + `uniformInverseChart_baseSlot_fderiv_
    neg_id_generalK` (J4-1006), then `to_localInverse` + the convex-MVT technique. NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_inverse_lipschitz_package_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (L_V : ℝ), 0 ≤ L_V ∧
      V 0 = q₀ ∧
      ∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        ‖V x - V y‖ ≤ L_V * dist x y := by
  classical
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  have hq0K : q₀ ∈ K := interior_subset hq₀
  have hWq0 : W q₀ = 0 := uniformInverseChart_diag_zero_of_mem g gi hC hK hq0K
  have hbaseC2 : ContDiffAt ℝ 2 W q₀ :=
    uniformInverseChart_baseSlot_contDiffAt_generalK g gi hC hK hq₀
  have hfd0 : HasFDerivAt W (-(ContinuousLinearMap.id ℝ (Point n))) q₀ :=
    uniformInverseChart_baseSlot_fderiv_neg_id_generalK g gi hC hK hq₀
  have hW'0 : HasFDerivAt W ((negCLE n : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n) q₀ := by
    rw [negCLE_coe]; exact hfd0
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  set Φ := hbaseC2.toOpenPartialHomeomorph W hW'0 hn2 with hΦdef
  have hVc2 : ContDiffAt ℝ 2 (⇑Φ.symm) (0 : Point n) := by
    have hti := hbaseC2.to_localInverse hW'0 hn2
    rw [hWq0] at hti
    exact hti
  have hV1 : ContDiffAt ℝ 1 (⇑Φ.symm) (0 : Point n) := hVc2.of_le (by norm_num)
  have hΦcoe : (⇑Φ : Point n → Point n) = W := by
    rw [hΦdef]; exact hbaseC2.toOpenPartialHomeomorph_coe hW'0 hn2
  have hq0src : q₀ ∈ Φ.source := by
    rw [hΦdef]; exact hbaseC2.mem_toOpenPartialHomeomorph_source hW'0 hn2
  have hV0 : (⇑Φ.symm) (0 : Point n) = q₀ := by
    have h := Φ.left_inv hq0src
    have hc0 : (⇑Φ : Point n → Point n) q₀ = 0 := by rw [hΦcoe]; exact hWq0
    rw [hc0] at h; exact h
  obtain ⟨r, hr, L, hL, hlip⟩ :=
    QIQTH.AmpQuantBundle.contDiffAt_one_lipschitzOn_ball (⇑Φ.symm) hV1
  refine ⟨r, hr, ⇑Φ.symm, L, hL, hV0, ?_⟩
  intro x hx y hy
  have hxb : ‖x‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hyb : ‖y‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hy
  have h := hlip x y hxb hyb
  rw [dist_eq_norm]
  exact h

/-! ###############################################################################
    ### §B — the determinant regularity bundle, GENERAL `q₀`, UNCONDITIONALLY.
    ############################################################################### -/

/-- **★★ `uniformInverseChart_baseSlot_det_fderiv_regularity_bundle_generalK`.**  On a BASE ball
    `ball q₀ r`, `z ↦ (fderiv ℝ W z).det` (`W p := uniformInverseChart g gi hC hK p q₀`) is bounded
    below by `1/2` and pairwise Lipschitz — UNCONDITIONALLY, at ANY `q₀ ∈ interior K` (generalizing
    `BaseSlotDetRegularity.det_fderiv_regularity_bundle`'s `hbaseC2`-conditional, `q₀ = 0`-fixed
    version). NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_det_fderiv_regularity_bundle_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ r > (0 : ℝ), ∃ L_D : ℝ, 0 ≤ L_D ∧
      (∀ z ∈ Metric.ball q₀ r,
        (1 / 2 : ℝ) ≤ |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) z).det|) ∧
      (∀ x ∈ Metric.ball q₀ r, ∀ y ∈ Metric.ball q₀ r,
        |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) x).det
            - (fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) y).det| ≤ L_D * dist x y) := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  have hbaseC2 : ContDiffAt ℝ 2 W q₀ :=
    uniformInverseChart_baseSlot_contDiffAt_generalK g gi hC hK hq₀
  have hfd0 : HasFDerivAt W (-(ContinuousLinearMap.id ℝ (Point n))) q₀ :=
    uniformInverseChart_baseSlot_fderiv_neg_id_generalK g gi hC hK hq₀
  have hfderiv0 : fderiv ℝ W q₀ = -(ContinuousLinearMap.id ℝ (Point n)) := hfd0.fderiv
  -- `z ↦ (fderiv W z).det` is `ContDiffAt ℝ 1` at `q₀`.
  have hderivCDA1 : ContDiffAt ℝ 1 (fderiv ℝ W) q₀ := hbaseC2.fderiv_right (by norm_num)
  have hdetCDA : ContDiffAt ℝ 1 (fun z => (fderiv ℝ W z).det) q₀ :=
    ((QIQTH.BaseSlotDetRegularity.det_clm_contDiff (n := n)).contDiffAt).comp q₀ hderivCDA1
  -- Lipschitz on a base ball `ball q₀ rL` (via the shifted convex-MVT helper, §0).
  obtain ⟨rL, hrL, L_D, hLD, hlipD⟩ :=
    contDiffAt_one_lipschitzOn_ball_atPoint (fun z => (fderiv ℝ W z).det) q₀ hdetCDA
  -- lower bound `≥ 1/2` on a base ball `ball q₀ rc`, via continuity + value `1` at `q₀`.
  have hval0 : |(fderiv ℝ W q₀).det| = 1 := by
    rw [hfderiv0]
    have hL : ((-(ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n) = (-1 : ℝ) • LinearMap.id := by ext x; simp
    show |LinearMap.det (((-(ContinuousLinearMap.id ℝ (Point n))) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n)| = 1
    rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one, abs_pow]
    norm_num
  have hcontD : ContinuousAt (fun z => (fderiv ℝ W z).det) q₀ := hdetCDA.continuousAt
  have hcontAbs : ContinuousAt (fun z => |(fderiv ℝ W z).det|) q₀ := hcontD.abs
  have hgt : ∀ᶠ z in 𝓝 q₀, (1 / 2 : ℝ) < |(fderiv ℝ W z).det| := by
    have hlt : (fun _ : Point n => (1 / 2 : ℝ)) q₀
        < (fun z => |(fderiv ℝ W z).det|) q₀ := by simp only [hval0]; norm_num
    exact continuousAt_const.eventually_lt hcontAbs hlt
  obtain ⟨rc, hrc, hball⟩ := Metric.eventually_nhds_iff.mp hgt
  refine ⟨min rL rc, lt_min hrL hrc, L_D, hLD, ?_, ?_⟩
  · intro z hz
    have hzc : dist z q₀ < rc := lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    exact le_of_lt (hball hzc)
  · intro x hx y hy
    exact hlipD x (Metric.ball_subset_ball (min_le_left _ _) hx)
      y (Metric.ball_subset_ball (min_le_left _ _) hy)

/-! ###############################################################################
    ### §C — the MAIN transport, GENERAL `q₀`, UNCONDITIONALLY.
    ############################################################################### -/

/-- **★★★★ `transported_ratio_regularity_generalK`.**  For ANY globally bounded (`M_P`) + globally
    Lipschitz (`L_P`) weight `P`, the CoV transformed integrand `w ↦ P (V w) / |det (fderiv W (V w))|`
    (`W p := uniformInverseChart g gi hC hK p q₀`, `V` the IFT local inverse) is bounded by `2 M_P` AND
    pairwise-Lipschitz on an image ball `ball 0 σ` — UNCONDITIONALLY, at ANY `q₀ ∈ interior K`.
    Generalizes `BaseSlotInverseChartLipschitz.transported_ratio_regularity` (removes `hbaseC2`,
    generalizes `q₀`). NOT `a₁ = R/6`. -/
theorem transported_ratio_regularity_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (P : Point n → ℝ) (M_P L_P : ℝ) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P)
    (hPb : ∀ z, |P z| ≤ M_P)
    (hPl : ∀ x y : Point n, |P x - P y| ≤ L_P * dist x y) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (Lc : ℝ), 0 ≤ Lc ∧ V 0 = q₀ ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (P (V w) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V w)).det|)
          ≤ M_P / (1 / 2 : ℝ)) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (P (V x) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V x)).det|
            - P (V y) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V y)).det|)
          ≤ Lc * dist x y) := by
  obtain ⟨r, hr, L_D, hLD, hlb, hlip⟩ :=
    uniformInverseChart_baseSlot_det_fderiv_regularity_bundle_generalK g gi hC hK hq₀
  obtain ⟨hqb, hql⟩ :=
    QIQTH.HeatResidualBound.ratio_abs_lipschitzOn (Metric.ball q₀ r) P
      (fun z => (fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) z).det)
      M_P L_P (1 / 2) L_D hMP hLP (by norm_num) hLD (fun z _ => hPb z) (fun x _ y _ => hPl x y) hlb hlip
  obtain ⟨σ0, hσ0, V, L_V, hLV, hV0, hVlip⟩ :=
    uniformInverseChart_baseSlot_inverse_lipschitz_package_generalK g gi hC hK hq₀
  have hLq0 : 0 ≤ L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2 := by
    have h1 : 0 ≤ L_P / (1 / 2 : ℝ) := div_nonneg hLP (by norm_num)
    have h2 : 0 ≤ M_P * L_D / (1 / 2 : ℝ) ^ 2 := div_nonneg (mul_nonneg hMP hLD) (by positivity)
    exact add_nonneg h1 h2
  -- `V` maps a small image ball into the base ball `ball q₀ r`.
  have hmaps : ∀ w ∈ Metric.ball (0 : Point n) (min σ0 (r / (L_V + 1))),
      V w ∈ Metric.ball q₀ r := by
    intro w hw
    have hwσ0 : w ∈ Metric.ball (0 : Point n) σ0 :=
      Metric.ball_subset_ball (min_le_left _ _) hw
    have h0σ0 : (0 : Point n) ∈ Metric.ball (0 : Point n) σ0 := Metric.mem_ball_self hσ0
    have hlip0 := hVlip w hwσ0 0 h0σ0
    rw [hV0] at hlip0
    have hVwnorm : ‖V w - q₀‖ ≤ L_V * ‖w‖ := by
      simpa [dist_zero_right] using hlip0
    have hwr : ‖w‖ < r / (L_V + 1) := by
      have hd : dist w (0 : Point n) < min σ0 (r / (L_V + 1)) := Metric.mem_ball.mp hw
      rw [dist_zero_right] at hd
      exact lt_of_lt_of_le hd (min_le_right _ _)
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖V w - q₀‖ ≤ L_V * ‖w‖ := hVwnorm
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
    calc abs (P (V x) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V x)).det|
            - P (V y) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V y)).det|)
          ≤ (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * dist (V x) (V y) := h1
      _ = (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * ‖V x - V y‖ := by rw [dist_eq_norm]
      _ ≤ (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * (L_V * dist x y) :=
            mul_le_mul_of_nonneg_left h2 hLq0
      _ = (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * L_V * dist x y := by ring

/-! ###############################################################################
    ### §D — the bridge: truncating the ball-only bound to a GLOBAL Lipschitz-at-0
    ### function, matching J4-1023's exact `Amp` interface.
    ############################################################################### -/

/-- **★★★★★ `amp_of_transported_ratio_global_lipschitz_at_zero` — THE BRIDGE.**  For ANY globally
    bounded + globally Lipschitz `P`, the piecewise-truncated function
        `AmpExt w := P (V w) / |det (fderiv W (V w))|` if `‖w‖ < σ`, else `P q₀`
    (`σ` the ball radius from `transported_ratio_regularity_generalK`) is `AEStronglyMeasurable` and
    satisfies a GLOBAL Lipschitz-at-`0` bound `∀ v, |AmpExt v − AmpExt 0| ≤ L·‖v‖` — EXACTLY
    `HCompNearCarryTerm1DomainRestrictedBound`'s `hAmp`/`hlip` interface.  Outside the ball the function
    is CONSTANT at `AmpExt 0 = P q₀`, so the bound is trivial there (`0 ≤ L‖v‖`); inside the ball it is
    `transported_ratio_regularity_generalK`'s established bound.  NOT `a₁ = R/6`. -/
theorem amp_of_transported_ratio_global_lipschitz_at_zero
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (P : Point n → ℝ) (M_P L_P : ℝ) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P)
    (hPb : ∀ z, |P z| ≤ M_P) (hPl : ∀ x y : Point n, |P x - P y| ≤ L_P * dist x y) :
    ∃ (AmpExt : Point n → ℝ) (L : ℝ), 0 ≤ L ∧
      AEStronglyMeasurable AmpExt volume ∧
      (∀ v : Point n, |AmpExt v - AmpExt 0| ≤ L * ‖v‖) := by
  classical
  obtain ⟨σ, hσ, V, Lc, hLc, hV0, hbnd, hlip⟩ :=
    transported_ratio_regularity_generalK g gi hC hK hq₀ P M_P L_P hMP hLP hPb hPl
  set AmpExt : Point n → ℝ := fun w =>
    if w ∈ Metric.ball (0 : Point n) σ then
      P (V w) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V w)).det|
    else P q₀ with hAmpExtdef
  have h0mem : (0 : Point n) ∈ Metric.ball (0 : Point n) σ := Metric.mem_ball_self hσ
  have hdet0 : |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) q₀).det| = 1 := by
    have hfd0 : HasFDerivAt (fun p => uniformInverseChart g gi hC hK p q₀)
        (-(ContinuousLinearMap.id ℝ (Point n))) q₀ :=
      uniformInverseChart_baseSlot_fderiv_neg_id_generalK g gi hC hK hq₀
    rw [hfd0.fderiv]
    have hL : ((-(ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n) = (-1 : ℝ) • LinearMap.id := by ext x; simp
    show |LinearMap.det (((-(ContinuousLinearMap.id ℝ (Point n))) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n)| = 1
    rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one, abs_pow]
    norm_num
  have hAmp0 : AmpExt 0 = P q₀ := by
    rw [hAmpExtdef]
    simp only [h0mem, if_true, hV0, hdet0]
    ring
  refine ⟨AmpExt, Lc, hLc, ?_, ?_⟩
  · -- `AEStronglyMeasurable`: gluing two `AEStronglyMeasurable` pieces on `μ.restrict s`/`μ.restrict sᶜ`.
    have hballmeas : MeasurableSet (Metric.ball (0 : Point n) σ) := measurableSet_ball
    have hrawmeas : AEStronglyMeasurable
        (fun w : Point n =>
          P (V w) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V w)).det|)
        (volume.restrict (Metric.ball (0 : Point n) σ)) := by
      have hlipfun : LipschitzOnWith (Real.toNNReal Lc)
          (fun w : Point n =>
            P (V w) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V w)).det|)
          (Metric.ball (0 : Point n) σ) := by
        rw [lipschitzOnWith_iff_dist_le_mul]
        intro x hx y hy
        have h := hlip x hx y hy
        rw [Real.dist_eq]
        simpa [Real.coe_toNNReal', hLc] using h
      exact (hlipfun.continuousOn.aestronglyMeasurable hballmeas)
    have hconstmeas : AEStronglyMeasurable (fun _ : Point n => P q₀)
        (volume.restrict (Metric.ball (0 : Point n) σ)ᶜ) := aestronglyMeasurable_const
    have hpiece : AEStronglyMeasurable AmpExt volume := by
      rw [← MeasureTheory.Measure.restrict_add_restrict_compl (μ := (volume : Measure (Point n)))
        hballmeas]
      apply AEStronglyMeasurable.add_measure
      · apply AEStronglyMeasurable.congr (f := fun w : Point n =>
          P (V w) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V w)).det|)
        · exact hrawmeas
        · filter_upwards [ae_restrict_mem hballmeas] with w hw
          rw [hAmpExtdef]; simp only [hw, if_true]
      · apply AEStronglyMeasurable.congr (f := fun _ : Point n => P q₀)
        · exact hconstmeas
        · filter_upwards [ae_restrict_mem hballmeas.compl] with w hw
          rw [hAmpExtdef]
          simp only [Set.mem_compl_iff] at hw
          simp only [hw, if_false]
    exact hpiece
  · intro v
    by_cases hv : v ∈ Metric.ball (0 : Point n) σ
    · have hvraw : AmpExt v
          = P (V v) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V v)).det| := by
        rw [hAmpExtdef]; simp only [hv, if_true]
      rw [hvraw, hAmp0]
      have hb := hlip v hv 0 h0mem
      have hV0det : P (V 0) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V 0)).det|
          = P q₀ := by simp only [hV0, hdet0]; ring
      rw [hV0det] at hb
      have hdv : dist v (0 : Point n) = ‖v‖ := dist_zero_right v
      rwa [hdv] at hb
    · have hvconst : AmpExt v = P q₀ := by rw [hAmpExtdef]; simp only [hv, if_false]
      rw [hvconst, hAmp0]
      simp only [sub_self, abs_zero]
      exact mul_nonneg hLc (norm_nonneg v)

/-! ###############################################################################
    ### §E — instantiating J4-1023's capstone at the transported-ratio `Amp`.
    ############################################################################### -/

/-- **★★★★★ `hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio`.**  Instantiates
    `HCompNearCarryTerm1DomainRestrictedBound.hsMixed_gaussDdim_mul_amp_domain_restricted_bound`
    (J4-1023) at `Amp := AmpExt` built (§D) from ANY globally bounded + globally Lipschitz `P` — the
    domain-restricted bound on `nb`'s ACTUAL post-CoV domain `W''S'`, for the "`P`-composed-with-`V`-
    over-Jacobian" shape.  Does NOT yet plug in the literal geometric `Bfac` (see file docstring: `Bfac`'s
    OWN global regularity is a separate, unestablished gap).  NOT `a₁ = R/6`. -/
theorem hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (τ : ℝ) (hτ : 0 < τ) (PI PJ Q : Point n)
    (P : Point n → ℝ) (M_P L_P : ℝ) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P)
    (hPb : ∀ z, |P z| ≤ M_P) (hPl : ∀ x y : Point n, |P x - P y| ≤ L_P * dist x y) :
    ∃ (S' : Set (Point n)) (ρ : ℝ) (AmpExt : Point n → ℝ) (L : ℝ), IsOpen S' ∧ q₀ ∈ S' ∧ 0 < ρ ∧
      0 ≤ L ∧
      |∫ v : Point n in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
          gaussDdim τ v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * AmpExt v)|
        ≤ (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ
              + (n : ℝ) ^ 2 * L * ‖Q‖)
          + (Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                * (|AmpExt 0| * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                      + (1 / (2 * τ)))
                    + L * ((1 / (4 * τ ^ 2))
                          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                        + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)))
              + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
                  * (|AmpExt 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                      + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := by
  obtain ⟨AmpExt, L, hL, hAmpMeas, hAmpLip⟩ :=
    amp_of_transported_ratio_global_lipschitz_at_zero g gi hC hK hq₀ P M_P L_P hMP hLP hPb hPl
  obtain ⟨S', ρ, hS'open, hq0S', hρpos, hfinal⟩ :=
    QIQTH.HCompNearCarryTerm1DomainRestrictedBound.hsMixed_gaussDdim_mul_amp_domain_restricted_bound
      g gi hC hK hq₀ τ hτ PI PJ Q AmpExt hAmpMeas L hL hAmpLip
  exact ⟨S', ρ, AmpExt, L, hS'open, hq0S', hρpos, hL, hfinal⟩

end QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge
#print axioms contDiffAt_one_lipschitzOn_ball_atPoint
#print axioms uniformInverseChart_baseSlot_inverse_lipschitz_package_generalK
#print axioms uniformInverseChart_baseSlot_det_fderiv_regularity_bundle_generalK
#print axioms transported_ratio_regularity_generalK
#print axioms amp_of_transported_ratio_global_lipschitz_at_zero
#print axioms hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio
end AxiomChecks
