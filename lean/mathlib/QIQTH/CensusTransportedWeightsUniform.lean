/-
  CensusTransportedWeightsUniform — the UNIFORM-WITNESS transported-weight regularity that repairs the
  decisive quantifier-order obstruction blocking the modulo-G2 `hballrate` (C1) closure of the `hCross`
  chain, as pinned by a gpt-5.6-sol (high) adversarial audit (2026-08-21).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure real-analysis / structural transport brick.  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable / conclusion-in-disguise hypothesis (satisfiability of the F-carry slot EXHIBITED
  below), no existing banked file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBSTRUCTION (gpt-5.6-sol high, 2026-08-21).  Filling `hballrate` needs a SINGLE `Cpair` for
  ALL `(s, a)` in the census rectangle (`s ∈ Ioo (u−ε) u`, `τ = a−s ∈ (0, τ₀]`).  Via the intended CoV
  ⟶ two-term route (`censusTauDeriv_eq_onGate_on_jointGate_ball` → `commonWitness_cov_subball` → fold →
  `two_term_census_bound_uniform`), `Cpair` is built from the post-CoV transported-weight constants
  (the image radius `σ`, the transported Lipschitz `Lq`, and the bounds `M₁, M₂`).  For `Cpair` to be a
  single constant these MUST be UNIFORM over the `(s, τ)` rectangle.  But EVERY banked lemma producing
  the post-CoV transported regularity — `commonWitness_ampF_transport`,
  `census_ampF_transported_ratio_regularity`, `transported_ratio_regularity_ballLocal`, and the
  primitive `commonWitness_transport` / `transport_ballLocal_regularity` — quantifies `σ` and the
  transported Lipschitz constant EXISTENTIALLY and PER-WEIGHT (the weight `P = amp(τ,·)·F(s,·)` depends
  on `s, τ`).  So a ∃-elimination INSIDE the `∀(s,a)` binder yields FRESH `σ, Lq` per slice; Lean cannot
  identify them across separate eliminations even though morally they coincide
  (`σ = min(D.σ, rP/(L_V+1))`, `Lq = L_Q·L_V` are functions ONLY of the uniform explicit constants +
  geometry, not of the weight's values).  `∀(s,τ)∃σLq` does NOT give `∃σLq∀(s,τ)`, and no
  `Classical.choice` trick repairs it (Sol: chosen witnesses have no uniform lower/upper bound).

  ## THE FIX (this file, Sol-validated).  Reprove the transport INLINE with EXPLICIT closed-form
  witnesses, quantified OUTSIDE the `(s, τ)` rectangle.  Every source radius/constant in the closed
  forms is already uniform: amp is τ-uniform bounded (`census_amplitude_supBounds`, `MA`) + τ-uniform
  Lipschitz (`census_amplitude_lipBounds`, `LA`); the slope is τ-uniform bounded (`Msl`) + Lipschitz
  (`Lsl`); `F` is s-uniform bounded (`M_F`) + Lipschitz (`L_F`) [carried, the Levi output]; the ratio
  `·/|det|` uses `|det| ≥ 1/2` + `L_D` (`det_fderiv_regularity_bundle`); and `V = D.V` is uniformly
  `L_V`-Lipschitz with `V 0 = 0`.  So `σ := min (D.σ) (rP/(D.L_V+1))`,
  `M₁ := (MA·M_F)/(1/2)`, `M₂ := (Msl·M_F)/(1/2)`, and
  `Lq := ((MA·L_F + M_F·LA)/(1/2) + (MA·M_F)·L_D/(1/2)²)·D.L_V` are all EXPLICIT and (s,τ)-INDEPENDENT.
  The per-slice regularity is then proved via `ratio_abs_lipschitzOn` (explicit constants) + the inlined
  `D.hVlip`/`D.hV0`/mapsTo transport, for EVERY `(s, τ)` against those SAME fixed witnesses.  (Sol: the
  varying centre value `q₁(0)=amp(τ,V0)·F(s,V0)/|det(V0)|` is harmless — the two-term theorem consumes
  each weight separately and needs only the same CONSTANT `Lq`, not agreeing centres.)

  ## WHAT LANDS.
    • `census_transported_weights_uniform` — ★★★ the UNIFORM-WITNESS transported q₁/q₂ regularity:
        ONE `V, σ, M₁, M₂, Lq` (0<σ, all constants ≥0, V 0 = 0) such that for EVERY `s ∈ Ioo (u−ε) u`
        and EVERY `τ ∈ (0, τ₀]`, on the image ball `ball 0 σ` the transported amplitude weight
        `q₁ = (amp(τ,V·)·F(s,V·))/|det (fderiv Wbv (V·))|` is bounded by `M₁` and pairwise-Lipschitz
        `Lq`, and the transported slope weight `q₂ = (slope(V·)·F(s,V·))/|det (fderiv Wbv (V·))|` is
        bounded by `M₂`.  The `σ`, `M₁`, `M₂`, `Lq` are OUTSIDE the `(s,τ)` binder — the quantifier
        order `two_term_census_bound_uniform` needs for a single `Cpair`.
    • `census_transported_weights_uniform_Fcarry_satisfiable` — non-vacuity of the carried s-uniform
        `F`-regularity slot (TEETH: `F ≡ 0`, `M_F = L_F = 0`).

  ## HONEST STATUS (blunt; gpt-5.6-sol high adversarially audited 2026-08-21).  This brick supplies the
  DECISIVE quantifier-order repair — the uniform-witness transported weights — that NO banked transport
  lemma exposed.  It does NOT close `hballrate` (C1) or `hCensusBound`/`hCross`, and it discharges NONE
  of `{hballrate, hDuhamel, hDConv, hCConv}`.  Per Sol's audit the REMAINING modulo-G2 `hballrate`
  wiring is: (a) global truncation to `Ω`-indicator + `AEStronglyMeasurable` of `q₁, q₂` (from
  continuity of the `V`-composite); (b) the `integral_add` split on the image (two integrability
  proofs); (c) the CoV two-term FOLD (`commonWitness_weightMatch` on the image, matching the two-term
  integrand shape); (d) the radius choreography (`commonWitness_image_sandwich` to fit
  `Ω ⊆ ball 0 σ` while keeping an inner ball `ball 0 r ⊆ Ω`, plus the G2 joint-gate ball); (e) the
  final `two_term_census_bound_uniform` application.  NONE of that is in this file, so the FULL
  modulo-G2 `hballrate` is NOT assembled.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}` (with `hballrate`/`hCross` an OPEN
  downstream carry), UNCHANGED.  NOT `a₁ = R/6`.
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

namespace QIQTH.CensusTransportedWeightsUniform

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `census_transported_weights_uniform` — the UNIFORM-WITNESS transported-weight regularity.**
    ONE image inverse `V`, image radius `σ > 0`, and constants `M₁, M₂, Lq ≥ 0` (with `V 0 = 0`) such
    that for EVERY `s ∈ Ioo (u−ε) u` and EVERY `τ ∈ (0, τ₀]`, on `ball 0 σ`:
      • the transported amplitude weight
        `q₁ w = chartFieldAmp … cutA cutB τ (V w) 0 · F s (V w) 0 / |det (fderiv Wbv (V w))|`
        is bounded by `M₁` and pairwise-Lipschitz with constant `Lq`, and
      • the transported slope weight
        `q₂ w = censusAmpTauDeriv … cutA cutB (V w) · F s (V w) 0 / |det (fderiv Wbv (V w))|`
        is bounded by `M₂`.
    The witnesses `V, σ, M₁, M₂, Lq` are bound OUTSIDE the `(s, τ)` quantifier — the order
    `two_term_census_bound_uniform` needs to build a SINGLE `Cpair`.  This repairs the decisive
    existential-per-weight quantifier obstruction that the banked transport lemmas
    (`commonWitness_ampF_transport`, `transported_ratio_regularity_ballLocal`, …) do not.  Conditional
    on the standard geometry carriers `{hC, hK, h0Kmem, hg, hg0, hu}` and the s-uniform `F`-regularity
    `{hFb, hFl}` (the Levi output); the amplitude/slope/det uniform bounds are discharged internally.
    ⚠ NOT `a₁ = R/6`. -/
theorem census_transported_weights_uniform
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (cutA cutB τ₀ : ℝ) (hτ₀ : 0 < τ₀)
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
    ∃ (V : Point n → Point n) (σ M₁ M₂ Lq : ℝ),
      0 < σ ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ 0 ≤ Lq ∧ V 0 = 0 ∧
      ∀ s ∈ Set.Ioo (u - ε) u, ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
        (∀ w ∈ Metric.ball (0 : Point n) σ,
          abs (chartFieldAmp g gi hC hK cutA cutB τ (V w) 0 * F s (V w) 0
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|) ≤ M₁) ∧
        (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
          abs (chartFieldAmp g gi hC hK cutA cutB τ (V x) 0 * F s (V x) 0
                / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
              - chartFieldAmp g gi hC hK cutA cutB τ (V y) 0 * F s (V y) 0
                / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
            ≤ Lq * dist x y) ∧
        (∀ w ∈ Metric.ball (0 : Point n) σ,
          abs (censusAmpTauDeriv g gi hC hK cutA cutB (V w) * F s (V w) 0
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|) ≤ M₂) := by
  classical
  -- honest regularity residual, discharged unconditionally.
  have hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n) :=
    wbv_contDiffAt_two g gi hC hK h0Kmem
  -- the common-witness inverse `V = D.V`.
  obtain ⟨D⟩ := baseVaryingIFTData_nonempty g gi hC hK h0Kmem
  -- τ-uniform amplitude & slope SUP bounds.
  obtain ⟨rAs, hrAs, MA, Msl, hMA, hMsl, hampB, hslB⟩ :=
    census_amplitude_supBounds g gi hC hK cutA cutB τ₀ hτ₀ h0Kmem hg hg0 hu
  -- τ-uniform amplitude & slope LIPSCHITZ bounds.
  obtain ⟨rAl, hrAl, LA, Lsl, hLA, hLsl, hampL, hslL⟩ :=
    census_amplitude_lipBounds g gi hC hK cutA cutB τ₀ hτ₀ h0Kmem hg hg0 hu
  -- determinant regularity bundle: `|det| ≥ 1/2` and `det` `L_D`-Lipschitz on `ball 0 rdet`.
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
  have hLrat0 : 0 ≤ Lrat := by
    rw [hLratdef]; positivity
  -- `V` maps `ball 0 σ` into `ball 0 rP` (inlined transport mapsTo, from `D.hVlip`/`D.hV0`).
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
  -- the determinant, as the ratio denominator.
  set detf : Point n → ℝ :=
    fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det with hdetfdef
  refine ⟨D.V, σ, (MA * M_F) / (1 / 2 : ℝ), (Msl * M_F) / (1 / 2 : ℝ), Lrat * L_V,
    hσ0, by positivity, by positivity, mul_nonneg hLrat0 hLV, D.hV0, ?_⟩
  intro s hs τ hτ hτ0
  -- coordinate ↦ norm helper on `ball 0 rP`.
  have hballnorm : ∀ x ∈ Metric.ball (0 : Point n) rP, ‖x‖ < rP := by
    intro x hx; rw [← dist_zero_right]; exact Metric.mem_ball.mp hx
  -- ═══ q₁ = (amp·F)/|det| ═══
  -- base weight `P₁ z = amp(τ,z)·F(s,z)`, bounded + pairwise-Lipschitz on `ball 0 rP`.
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
  -- ratio regularity of `q₁_base = P₁/|det|` on `ball 0 rP` (explicit constants).
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
  obtain ⟨hq2b, _⟩ :=
    ratio_abs_lipschitzOn (Metric.ball (0 : Point n) rP) P₂ detf
      (Msl * M_F) (Msl * L_F + M_F * Lsl) (1 / 2 : ℝ) L_D
      (mul_nonneg hMsl hMF) (by positivity) (by norm_num) hLD
      hP2b hP2l
      (fun x hx => by rw [hdetfdef]; exact hlbdet x (Metric.ball_subset_ball hrP_det hx))
      (fun x hx y hy => by
        rw [hdetfdef]; exact hdlip x (Metric.ball_subset_ball hrP_det hx)
          y (Metric.ball_subset_ball hrP_det hy))
  -- ═══ assemble the three transported facts (inlined `∘V` transport). ═══
  refine ⟨?_, ?_, ?_⟩
  · -- q₁ bound on `ball 0 σ`.
    intro w hw
    have := hq1b (D.V w) (hmaps w hw)
    simpa [hP1def, hdetfdef] using this
  · -- q₁ pairwise-Lipschitz on `ball 0 σ`.
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
  · -- q₂ bound on `ball 0 σ`.
    intro w hw
    have := hq2b (D.V w) (hmaps w hw)
    simpa [hP2def, hdetfdef] using this

/-- **Non-vacuity of the carried s-uniform `F`-regularity slot (TEETH).**  The `{hMF, hLF, hFb, hFl}`
    carry bundle is satisfiable by the degenerate `F ≡ 0` with `M_F = L_F = 0` and any `rF > 0` on any
    window — confirming the transported-weights brick is NOT vacuously conditioned on an unsatisfiable
    `F`-carry.  ⚠ NOT `a₁ = R/6`. -/
theorem census_transported_weights_uniform_Fcarry_satisfiable (u ε : ℝ) :
    ∃ (F : ℝ → Point n → Point n → ℝ) (rF M_F L_F : ℝ),
      0 < rF ∧ 0 ≤ M_F ∧ 0 ≤ L_F ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
        |F s z 0 - F s w 0| ≤ L_F * dist z w) := by
  refine ⟨fun _ _ _ => 0, 1, 0, 0, one_pos, le_refl _, le_refl _, ?_, ?_⟩
  · intro s _ z _; simp
  · intro s _ z w _ _; simpa using dist_nonneg

end QIQTH.CensusTransportedWeightsUniform

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusTransportedWeightsUniform
#print axioms census_transported_weights_uniform
#print axioms census_transported_weights_uniform_Fcarry_satisfiable
end AxiomChecks
