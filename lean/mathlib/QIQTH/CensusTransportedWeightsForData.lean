/-
  CensusTransportedWeightsForData — the D-PARAMETERIZED, MEASURABILITY-STRENGTHENED transported-weight
  regularity: the coherence-and-measurability bridge that unblocks the modulo-G2 `hballrate` (C1)
  assembly.  Two obstructions Sol (gpt-5.6-sol high, 2026-08-21) flagged as the sharpest remaining
  blockers to the FULL modulo-G2 `hballrate` are discharged here:

    (COH)  the banked `census_transported_weights_uniform` (J4-959) hides its internal common-witness
           `D` (it does `obtain ⟨D⟩ := baseVaryingIFTData_nonempty`), so its returned `V = D.V` cannot
           be identified with the `D.V` used by `commonWitness_cov_subball` / `commonWitness_image_*`
           in the CoV chain — an ∃-elimination coherence wall.  FIX: reprove the uniform-witness
           transported regularity as a lemma PARAMETERIZED by an external `D : BaseVaryingIFTData`, so
           the assembler obtains ONE `D` and feeds it to BOTH the CoV and this regularity.

    (MEAS) the two-term census core (`two_term_census_bound_uniform_combined`) demands the transported
           weights be GLOBALLY `AEStronglyMeasurable`, but J4-959 only exposes a BOUND on the slope
           weight `q₂` (its proof computes `q₂`'s pairwise-Lipschitz constant via
           `ratio_abs_lipschitzOn` and then DISCARDS it — `⟨hq2b, _⟩`).  A bounded function need not be
           measurable.  FIX: KEEP the discarded `q₂` Lipschitz; then BOTH `q₁, q₂` are pairwise-
           Lipschitz on `ball 0 σ`, so `LipschitzOnWith → ContinuousOn → AEStronglyMeasurable` gives the
           indicator-truncated weights global measurability for FREE — no `chartFieldAmp` continuity
           lemma, no extra `hgi`/`hgpos` carriers.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure real-analysis / structural transport brick.  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable / conclusion-in-disguise hypothesis (the `F`-carry slot satisfiability is EXHIBITED),
  no existing banked file edited.

  ## WHAT LANDS.
    • `census_transported_weights_forData` — ★★★ the D-PARAMETERIZED uniform transported-weight
        regularity: for a GIVEN `D : BaseVaryingIFTData`, ONE image radius `σ > 0` and constants
        `M₁, M₂, Lq₁, Lq₂ ≥ 0` such that for EVERY `s ∈ Ioo (u−ε) u` and EVERY `τ ∈ (0, τ₀]`, on
        `ball 0 σ` BOTH the transported amplitude weight `q₁` (bounded `M₁`, pairwise-Lipschitz `Lq₁`)
        AND the transported slope weight `q₂` (bounded `M₂`, pairwise-Lipschitz `Lq₂`) are regular —
        about the SAME `D.V` the CoV uses.  Same body as J4-959 but D-parameterized and keeping the
        `q₂` Lipschitz.
    • `aesm_indicator_of_ball_lipschitz` — ★★ the general measurability corollary: a function
        pairwise-`|·|`-Lipschitz on `ball 0 σ` has `AEStronglyMeasurable` indicator-truncation to
        `ball 0 σ` on all of `volume` (`LipschitzOnWith → ContinuousOn → aestronglyMeasurable_
        indicator_iff`).  Applied to `q₁, q₂` this discharges (MEAS).
    • `census_transported_weights_forData_Fcarry_satisfiable` — non-vacuity (TEETH: `F ≡ 0`).

  ## HONEST STATUS (gpt-5.6-sol high adversarially audited 2026-08-21).  This brick removes BOTH hard
  blockers (COH + MEAS) that Sol identified as gating the FULL modulo-G2 `hballrate` assembly, leaving
  only the "tedious but tractable" fold / integral-split / horizon-arithmetic wiring.  It does NOT by
  itself close `hballrate` (C1), `hCensusBound`, or `hCross`, and discharges NONE of `{hballrate,
  hDuhamel, hDConv, hCConv}`.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6`
  remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusAmplitudeLipDischarge
import QIQTH.BaseVaryingIFTCommonWitness
import QIQTH.BaseSlotDetRegularity
import QIQTH.GaussTauTraceChartDetFactor
import QIQTH.CensusHbaseC2Discharge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.CensusTauDerivGateSplit QIQTH.CensusAmpConcreteRegularity
open QIQTH.CensusAmplitudeSupDischarge QIQTH.CensusAmplitudeLipDischarge
open QIQTH.BaseVaryingIFTCommonWitness QIQTH.BaseSlotDetRegularity
open QIQTH.CensusHbaseC2Discharge
open scoped Topology BigOperators ContDiff

namespace QIQTH.CensusTransportedWeightsForData

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the general measurability corollary (discharges (MEAS)).
    ############################################################################### -/

/-- **★★ `aesm_indicator_of_ball_lipschitz` — pairwise-Lipschitz-on-a-ball ⟹ measurable truncation.**
    A function `q` that is pairwise-`|·|`-Lipschitz (constant `Lq ≥ 0`) on `ball 0 σ` is `ContinuousOn`
    that ball (`LipschitzOnWith.continuousOn`), hence `AEStronglyMeasurable` under `volume.restrict
    (ball 0 σ)` (`ContinuousOn.aestronglyMeasurable`), hence its indicator truncation to `ball 0 σ` is
    globally `AEStronglyMeasurable` (`aestronglyMeasurable_indicator_iff`).  This is the exact global
    measurability the two-term census core requires, obtained from ball-local Lipschitz data ALONE.
    NOT `a₁ = R/6`. -/
theorem aesm_indicator_of_ball_lipschitz (σ Lq : ℝ) (hLq : 0 ≤ Lq) (q : Point n → ℝ)
    (hlip : ∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
      |q x - q y| ≤ Lq * dist x y) :
    AEStronglyMeasurable (Set.indicator (Metric.ball (0 : Point n) σ) q) volume := by
  have hLipOn : LipschitzOnWith Lq.toNNReal q (Metric.ball (0 : Point n) σ) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq, Real.coe_toNNReal Lq hLq]
    exact hlip x hx y hy
  have hcont : ContinuousOn q (Metric.ball (0 : Point n) σ) := hLipOn.continuousOn
  have hrestrict : AEStronglyMeasurable q (volume.restrict (Metric.ball (0 : Point n) σ)) :=
    hcont.aestronglyMeasurable measurableSet_ball
  exact (aestronglyMeasurable_indicator_iff measurableSet_ball).mpr hrestrict

/-! ###############################################################################
    ### §B — the D-parameterized uniform transported-weight regularity (discharges (COH)).
    ############################################################################### -/

/-- **★★★ `census_transported_weights_forData` — the D-PARAMETERIZED uniform transported weights.**
    Identical to `census_transported_weights_uniform` (J4-959) EXCEPT the common-witness `D` is an
    EXTERNAL parameter (so the assembler can share it with the CoV chain), and the returned tuple ALSO
    exposes the slope weight `q₂`'s pairwise-Lipschitz constant `Lq₂` (which J4-959 computes but
    discards).  For the GIVEN `D`, ONE image radius `σ > 0` and constants `M₁, M₂, Lq₁, Lq₂ ≥ 0` such
    that for EVERY `s ∈ Ioo (u−ε) u` and EVERY `τ ∈ (0, τ₀]`, on `ball 0 σ`:
      • `q₁ w = chartFieldAmp … τ (D.V w) 0 · F s (D.V w) 0 / |det (fderiv Wbv (D.V w))|`
        is bounded by `M₁` and pairwise-Lipschitz `Lq₁`, and
      • `q₂ w = censusAmpTauDeriv … (D.V w) · F s (D.V w) 0 / |det (fderiv Wbv (D.V w))|`
        is bounded by `M₂` and pairwise-Lipschitz `Lq₂`.
    NOT `a₁ = R/6`. -/
theorem census_transported_weights_forData
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (D : BaseVaryingIFTData g gi hC hK) (cutA cutB τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F : ℝ → Point n → Point n → ℝ) (u ε rF M_F L_F : ℝ)
    (hrF : 0 < rF) (hMF : 0 ≤ M_F) (hLF : 0 ≤ L_F)
    (hFb : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F)
    (hFl : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
      |F s z 0 - F s w 0| ≤ L_F * dist z w) :
    ∃ (σ M₁ M₂ Lq₁ Lq₂ : ℝ),
      0 < σ ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ 0 ≤ Lq₁ ∧ 0 ≤ Lq₂ ∧
      ∀ s ∈ Set.Ioo (u - ε) u, ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
        (∀ w ∈ Metric.ball (0 : Point n) σ,
          abs (chartFieldAmp g gi hC hK cutA cutB τ (D.V w) 0 * F s (D.V w) 0
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V w)).det|) ≤ M₁) ∧
        (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
          abs (chartFieldAmp g gi hC hK cutA cutB τ (D.V x) 0 * F s (D.V x) 0
                / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V x)).det|
              - chartFieldAmp g gi hC hK cutA cutB τ (D.V y) 0 * F s (D.V y) 0
                / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V y)).det|)
            ≤ Lq₁ * dist x y) ∧
        (∀ w ∈ Metric.ball (0 : Point n) σ,
          abs (censusAmpTauDeriv g gi hC hK cutA cutB (D.V w) * F s (D.V w) 0
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V w)).det|) ≤ M₂) ∧
        (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
          abs (censusAmpTauDeriv g gi hC hK cutA cutB (D.V x) * F s (D.V x) 0
                / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V x)).det|
              - censusAmpTauDeriv g gi hC hK cutA cutB (D.V y) * F s (D.V y) 0
                / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V y)).det|)
            ≤ Lq₂ * dist x y) := by
  classical
  have hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n) :=
    wbv_contDiffAt_two g gi hC hK h0Kmem
  -- τ-uniform amplitude & slope SUP bounds.
  obtain ⟨rAs, hrAs, MA, Msl, hMA, hMsl, hampB, hslB⟩ :=
    census_amplitude_supBounds g gi hC hK cutA cutB τ₀ hτ₀ h0Kmem hg hg0 hu
  -- τ-uniform amplitude & slope LIPSCHITZ bounds.
  obtain ⟨rAl, hrAl, LA, Lsl, hLA, hLsl, hampL, hslL⟩ :=
    census_amplitude_lipBounds g gi hC hK cutA cutB τ₀ hτ₀ h0Kmem hg hg0 hu
  -- determinant regularity bundle.
  obtain ⟨rdet, hrdet, L_D, hLD, hlbdet, hdlip⟩ :=
    det_fderiv_regularity_bundle g gi hC hK h0Kmem hbaseC2
  -- common base ball radius on which ALL factor regularities hold.
  set rP : ℝ := min (min rAs rAl) (min rF rdet) with hrPdef
  have hrP0 : 0 < rP := lt_min (lt_min hrAs hrAl) (lt_min hrF hrdet)
  have hrP_As : rP ≤ rAs := le_trans (min_le_left _ _) (min_le_left _ _)
  have hrP_Al : rP ≤ rAl := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrP_F : rP ≤ rF := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrP_det : rP ≤ rdet := le_trans (min_le_right _ _) (min_le_right _ _)
  -- explicit uniform constants.
  set L_V : ℝ := D.L_V with hLVdef
  have hLV : 0 ≤ L_V := D.hLV
  set σ : ℝ := min D.σ (rP / (L_V + 1)) with hσdef
  have hσ0 : 0 < σ := lt_min D.hσ (by positivity)
  set Lrat : ℝ :=
    ((MA * L_F + M_F * LA) / (1 / 2 : ℝ) + (MA * M_F) * L_D / (1 / 2 : ℝ) ^ 2) with hLratdef
  have hLrat0 : 0 ≤ Lrat := by rw [hLratdef]; positivity
  set Lrat2 : ℝ :=
    ((Msl * L_F + M_F * Lsl) / (1 / 2 : ℝ) + (Msl * M_F) * L_D / (1 / 2 : ℝ) ^ 2) with hLrat2def
  have hLrat20 : 0 ≤ Lrat2 := by rw [hLrat2def]; positivity
  -- `V` maps `ball 0 σ` into `ball 0 rP`.
  have hmaps : ∀ w ∈ Metric.ball (0 : Point n) σ, D.V w ∈ Metric.ball (0 : Point n) rP := by
    intro w hw
    have hwσ : w ∈ Metric.ball (0 : Point n) D.σ :=
      Metric.ball_subset_ball (min_le_left _ _) hw
    have h0σ : (0 : Point n) ∈ Metric.ball (0 : Point n) D.σ := Metric.mem_ball_self D.hσ
    have hlip0 := D.hVlip w hwσ 0 h0σ
    rw [D.hV0] at hlip0
    have hVwnorm : ‖D.V w‖ ≤ L_V * ‖w‖ := by
      simpa [dist_zero_right, sub_zero, hLVdef] using hlip0
    have hwr : ‖w‖ < rP / (L_V + 1) := by
      have hd : dist w (0 : Point n) < min D.σ (rP / (L_V + 1)) := Metric.mem_ball.mp hw
      rw [dist_zero_right] at hd
      exact lt_of_lt_of_le hd (min_le_right _ _)
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖D.V w‖ ≤ L_V * ‖w‖ := hVwnorm
      _ ≤ (L_V + 1) * ‖w‖ := by nlinarith [norm_nonneg w]
      _ < (L_V + 1) * (rP / (L_V + 1)) := by
            apply mul_lt_mul_of_pos_left hwr (by positivity)
      _ = rP := by field_simp
  set detf : Point n → ℝ :=
    fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det with hdetfdef
  refine ⟨σ, (MA * M_F) / (1 / 2 : ℝ), (Msl * M_F) / (1 / 2 : ℝ), Lrat * L_V, Lrat2 * L_V,
    hσ0, by positivity, by positivity, mul_nonneg hLrat0 hLV, mul_nonneg hLrat20 hLV, ?_⟩
  intro s hs τ hτ hτ0
  have hballnorm : ∀ x ∈ Metric.ball (0 : Point n) rP, ‖x‖ < rP := by
    intro x hx; rw [← dist_zero_right]; exact Metric.mem_ball.mp hx
  -- ═══ q₁ = (amp·F)/|det| ═══
  set P₁ : Point n → ℝ := fun z => chartFieldAmp g gi hC hK cutA cutB τ z 0 * F s z 0 with hP1def
  have hP1b : ∀ x ∈ Metric.ball (0 : Point n) rP, |P₁ x| ≤ MA * M_F := by
    intro x hx
    have hxr : ‖x‖ < rP := hballnorm x hx
    have hax : |chartFieldAmp g gi hC hK cutA cutB τ x 0| ≤ MA :=
      hampB τ hτ hτ0 x (lt_of_lt_of_le hxr hrP_As)
    have hfx : |F s x 0| ≤ M_F := hFb s hs x (lt_of_lt_of_le hxr hrP_F)
    rw [hP1def, abs_mul]
    exact mul_le_mul hax hfx (abs_nonneg _) hMA
  have hP1l : ∀ x ∈ Metric.ball (0 : Point n) rP, ∀ y ∈ Metric.ball (0 : Point n) rP,
      |P₁ x - P₁ y| ≤ (MA * L_F + M_F * LA) * dist x y := by
    intro x hx y hy
    have hxr : ‖x‖ < rP := hballnorm x hx
    have hyr : ‖y‖ < rP := hballnorm y hy
    have hax : |chartFieldAmp g gi hC hK cutA cutB τ x 0| ≤ MA :=
      hampB τ hτ hτ0 x (lt_of_lt_of_le hxr hrP_As)
    have hfy : |F s y 0| ≤ M_F := hFb s hs y (lt_of_lt_of_le hyr hrP_F)
    have hampd : |chartFieldAmp g gi hC hK cutA cutB τ x 0 - chartFieldAmp g gi hC hK cutA cutB τ y 0|
        ≤ LA * dist x y :=
      hampL τ hτ hτ0 x y (lt_of_lt_of_le hxr hrP_Al) (lt_of_lt_of_le hyr hrP_Al)
    have hfd : |F s x 0 - F s y 0| ≤ L_F * dist x y :=
      hFl s hs x y (lt_of_lt_of_le hxr hrP_F) (lt_of_lt_of_le hyr hrP_F)
    have hkey : P₁ x - P₁ y
        = chartFieldAmp g gi hC hK cutA cutB τ x 0 * (F s x 0 - F s y 0)
          + F s y 0 * (chartFieldAmp g gi hC hK cutA cutB τ x 0 - chartFieldAmp g gi hC hK cutA cutB τ y 0) := by
      rw [hP1def]; ring
    rw [hkey]
    calc |chartFieldAmp g gi hC hK cutA cutB τ x 0 * (F s x 0 - F s y 0)
            + F s y 0 * (chartFieldAmp g gi hC hK cutA cutB τ x 0 - chartFieldAmp g gi hC hK cutA cutB τ y 0)|
        ≤ |chartFieldAmp g gi hC hK cutA cutB τ x 0 * (F s x 0 - F s y 0)|
            + |F s y 0 * (chartFieldAmp g gi hC hK cutA cutB τ x 0 - chartFieldAmp g gi hC hK cutA cutB τ y 0)| :=
          abs_add_le _ _
      _ = |chartFieldAmp g gi hC hK cutA cutB τ x 0| * |F s x 0 - F s y 0|
            + |F s y 0| * |chartFieldAmp g gi hC hK cutA cutB τ x 0 - chartFieldAmp g gi hC hK cutA cutB τ y 0| := by
          rw [abs_mul, abs_mul]
      _ ≤ MA * (L_F * dist x y) + M_F * (LA * dist x y) := by
          apply add_le_add
          · exact mul_le_mul hax hfd (abs_nonneg _) hMA
          · exact mul_le_mul hfy hampd (abs_nonneg _) hMF
      _ = (MA * L_F + M_F * LA) * dist x y := by ring
  obtain ⟨hq1b, hq1l⟩ :=
    ratio_abs_lipschitzOn (Metric.ball (0 : Point n) rP) P₁ detf
      (MA * M_F) (MA * L_F + M_F * LA) (1 / 2 : ℝ) L_D
      (mul_nonneg hMA hMF) (by positivity) (by norm_num) hLD
      hP1b hP1l
      (fun x hx => by rw [hdetfdef]; exact hlbdet x (Metric.ball_subset_ball hrP_det hx))
      (fun x hx y hy => by
        rw [hdetfdef]; exact hdlip x (Metric.ball_subset_ball hrP_det hx)
          y (Metric.ball_subset_ball hrP_det hy))
  -- ═══ q₂ = (slope·F)/|det| ═══
  set P₂ : Point n → ℝ := fun z => censusAmpTauDeriv g gi hC hK cutA cutB z * F s z 0 with hP2def
  have hP2b : ∀ x ∈ Metric.ball (0 : Point n) rP, |P₂ x| ≤ Msl * M_F := by
    intro x hx
    have hxr : ‖x‖ < rP := hballnorm x hx
    have hsx : |censusAmpTauDeriv g gi hC hK cutA cutB x| ≤ Msl :=
      hslB x (lt_of_lt_of_le hxr hrP_As)
    have hfx : |F s x 0| ≤ M_F := hFb s hs x (lt_of_lt_of_le hxr hrP_F)
    rw [hP2def, abs_mul]
    exact mul_le_mul hsx hfx (abs_nonneg _) hMsl
  have hP2l : ∀ x ∈ Metric.ball (0 : Point n) rP, ∀ y ∈ Metric.ball (0 : Point n) rP,
      |P₂ x - P₂ y| ≤ (Msl * L_F + M_F * Lsl) * dist x y := by
    intro x hx y hy
    have hxr : ‖x‖ < rP := hballnorm x hx
    have hyr : ‖y‖ < rP := hballnorm y hy
    have hsx : |censusAmpTauDeriv g gi hC hK cutA cutB x| ≤ Msl :=
      hslB x (lt_of_lt_of_le hxr hrP_As)
    have hfy : |F s y 0| ≤ M_F := hFb s hs y (lt_of_lt_of_le hyr hrP_F)
    have hsd : |censusAmpTauDeriv g gi hC hK cutA cutB x - censusAmpTauDeriv g gi hC hK cutA cutB y|
        ≤ Lsl * dist x y :=
      hslL x y (lt_of_lt_of_le hxr hrP_Al) (lt_of_lt_of_le hyr hrP_Al)
    have hfd : |F s x 0 - F s y 0| ≤ L_F * dist x y :=
      hFl s hs x y (lt_of_lt_of_le hxr hrP_F) (lt_of_lt_of_le hyr hrP_F)
    have hkey : P₂ x - P₂ y
        = censusAmpTauDeriv g gi hC hK cutA cutB x * (F s x 0 - F s y 0)
          + F s y 0 * (censusAmpTauDeriv g gi hC hK cutA cutB x - censusAmpTauDeriv g gi hC hK cutA cutB y) := by
      rw [hP2def]; ring
    rw [hkey]
    calc |censusAmpTauDeriv g gi hC hK cutA cutB x * (F s x 0 - F s y 0)
            + F s y 0 * (censusAmpTauDeriv g gi hC hK cutA cutB x - censusAmpTauDeriv g gi hC hK cutA cutB y)|
        ≤ |censusAmpTauDeriv g gi hC hK cutA cutB x * (F s x 0 - F s y 0)|
            + |F s y 0 * (censusAmpTauDeriv g gi hC hK cutA cutB x - censusAmpTauDeriv g gi hC hK cutA cutB y)| :=
          abs_add_le _ _
      _ = |censusAmpTauDeriv g gi hC hK cutA cutB x| * |F s x 0 - F s y 0|
            + |F s y 0| * |censusAmpTauDeriv g gi hC hK cutA cutB x - censusAmpTauDeriv g gi hC hK cutA cutB y| := by
          rw [abs_mul, abs_mul]
      _ ≤ Msl * (L_F * dist x y) + M_F * (Lsl * dist x y) := by
          apply add_le_add
          · exact mul_le_mul hsx hfd (abs_nonneg _) hMsl
          · exact mul_le_mul hfy hsd (abs_nonneg _) hMF
      _ = (Msl * L_F + M_F * Lsl) * dist x y := by ring
  obtain ⟨hq2b, hq2l⟩ :=
    ratio_abs_lipschitzOn (Metric.ball (0 : Point n) rP) P₂ detf
      (Msl * M_F) (Msl * L_F + M_F * Lsl) (1 / 2 : ℝ) L_D
      (mul_nonneg hMsl hMF) (by positivity) (by norm_num) hLD
      hP2b hP2l
      (fun x hx => by rw [hdetfdef]; exact hlbdet x (Metric.ball_subset_ball hrP_det hx))
      (fun x hx y hy => by
        rw [hdetfdef]; exact hdlip x (Metric.ball_subset_ball hrP_det hx)
          y (Metric.ball_subset_ball hrP_det hy))
  -- ═══ assemble the FOUR transported facts (inlined `∘V` transport). ═══
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- q₁ bound.
    intro w hw
    have := hq1b (D.V w) (hmaps w hw)
    simpa [hP1def, hdetfdef] using this
  · -- q₁ pairwise-Lipschitz.
    intro x hx y hy
    have hbase := hq1l (D.V x) (hmaps x hx) (D.V y) (hmaps y hy)
    have hVd : dist (D.V x) (D.V y) ≤ L_V * dist x y := by
      rw [dist_eq_norm]
      exact D.hVlip x (Metric.ball_subset_ball (min_le_left _ _) hx)
        y (Metric.ball_subset_ball (min_le_left _ _) hy)
    have hstep : Lrat * dist (D.V x) (D.V y) ≤ Lrat * (L_V * dist x y) :=
      mul_le_mul_of_nonneg_left hVd hLrat0
    have hcombined :
        abs (P₁ (D.V x) / |detf (D.V x)| - P₁ (D.V y) / |detf (D.V y)|)
          ≤ Lrat * L_V * dist x y := by
      calc abs (P₁ (D.V x) / |detf (D.V x)| - P₁ (D.V y) / |detf (D.V y)|)
          ≤ Lrat * dist (D.V x) (D.V y) := hbase
        _ ≤ Lrat * (L_V * dist x y) := hstep
        _ = Lrat * L_V * dist x y := by ring
    simpa [hP1def, hdetfdef] using hcombined
  · -- q₂ bound.
    intro w hw
    have := hq2b (D.V w) (hmaps w hw)
    simpa [hP2def, hdetfdef] using this
  · -- q₂ pairwise-Lipschitz (the KEPT part).
    intro x hx y hy
    have hbase := hq2l (D.V x) (hmaps x hx) (D.V y) (hmaps y hy)
    have hVd : dist (D.V x) (D.V y) ≤ L_V * dist x y := by
      rw [dist_eq_norm]
      exact D.hVlip x (Metric.ball_subset_ball (min_le_left _ _) hx)
        y (Metric.ball_subset_ball (min_le_left _ _) hy)
    have hstep : Lrat2 * dist (D.V x) (D.V y) ≤ Lrat2 * (L_V * dist x y) :=
      mul_le_mul_of_nonneg_left hVd hLrat20
    have hcombined :
        abs (P₂ (D.V x) / |detf (D.V x)| - P₂ (D.V y) / |detf (D.V y)|)
          ≤ Lrat2 * L_V * dist x y := by
      calc abs (P₂ (D.V x) / |detf (D.V x)| - P₂ (D.V y) / |detf (D.V y)|)
          ≤ Lrat2 * dist (D.V x) (D.V y) := hbase
        _ ≤ Lrat2 * (L_V * dist x y) := hstep
        _ = Lrat2 * L_V * dist x y := by ring
    simpa [hP2def, hdetfdef] using hcombined

/-- **Non-vacuity of the carried s-uniform `F`-regularity slot (TEETH).**  `F ≡ 0`, `M_F = L_F = 0`.
    NOT `a₁ = R/6`. -/
theorem census_transported_weights_forData_Fcarry_satisfiable (u ε : ℝ) :
    ∃ (F : ℝ → Point n → Point n → ℝ) (rF M_F L_F : ℝ),
      0 < rF ∧ 0 ≤ M_F ∧ 0 ≤ L_F ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
        |F s z 0 - F s w 0| ≤ L_F * dist z w) := by
  refine ⟨fun _ _ _ => 0, 1, 0, 0, one_pos, le_refl _, le_refl _, ?_, ?_⟩
  · intro s _ z _; simp
  · intro s _ z w _ _; simp

end QIQTH.CensusTransportedWeightsForData

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusTransportedWeightsForData
#print axioms aesm_indicator_of_ball_lipschitz
#print axioms census_transported_weights_forData
#print axioms census_transported_weights_forData_Fcarry_satisfiable
end AxiomChecks
