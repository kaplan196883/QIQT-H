/-
  HZDataFromCrudeEnv — J4-916: the DATA conjuncts (i)–(iv) of J4-912's inner `z`-level family `hZ`
  SUPPLIED from a crude TIME-derivative Gaussian envelope, closing the STRUCTURE of `hZ` down to the
  same named J4-911-class carries (the differentiability conjunct (v) already discharged by J4-915).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE brick.  It supplies the four remaining DATA conjuncts of the inner `z`-level
  differentiation family `hZ` that `HpardiffZTimeDerivReduction.hpardiff_of_zTimeDeriv` (J4-912) consumes:
    (i)   the `z`-integrable dominator `Dz`,
    (ii)  the base-slice `z`-integrability,
    (iii) the derivative-slice `z`-measurability,
    (iv)  the UNIFORM-over-`V` `z`-pointwise dominator bound,
  GIVEN a crude TIME-derivative Gaussian envelope `hAcrude` (the SAME carried geometric input J4-911's
  `derivDom_boundD_of_crude` left open, of the `Ccr·τ⁻¹·gaussDdim(wL·τ)` class), the width-`2` Levi
  source bound `hFdom`, the derivative-slice measurability carry, and the base-slice integrability carry.
  The fifth conjunct (v) — the `z`-pointwise TIME `HasDerivAt` — is DISCHARGED unconditionally for the
  concrete witness by J4-915 (`WitnessTimeHasDerivAt.witnessZTime_hasDerivAt`) and threaded in via the
  passed `hDiff` slot; the concrete wrapper wires it directly.  No `sorry` (header prose excepted), no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis (satisfiability EXHIBITED below), none equal
  to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE UNIFORM-over-neighborhood SUBTLETY (gpt-5.6-sol high, GO).  Unlike J4-911's OUTER `s`-level
  scalar dominator `boundD` (a constant, uniform in `c` via peak antitonicity), the INNER `hZ` dominator
  `Dz` must dominate `‖deriv(…)(c'−s)·F s z 0‖` POINTWISE in `z` and UNIFORMLY over `c'` in a
  neighborhood `V ∋ c`.  As `c'` ranges over `V` the Gaussian width `wL·(c'−s)` VARIES, so no single
  Gaussian dominates the crude bound cleanly.  FIX: choose `V := Metric.ball c δ` with
  `δ := min (c−s−τ₀) (τ₁−(c−s)) > 0` so that every `c' ∈ V` has `c'−s ∈ [τ₀, τ₁]` (hence `> 0`, feeding
  J4-915's (v)); then the WIDTH-INTERVAL DOMINATION `gaussDdim_width_interval_dom`
  (`gaussDdim (wL·t) z ≤ √(τ₁/τ₀)ⁿ · gaussDdim (wL·τ₁) z` for `t ∈ [τ₀,τ₁]`, derived from the banked
  `HrawCampaignOne.gaussDdim_width_mono`) pins the family to the single widest Gaussian `gaussDdim(wL·τ₁)`.
  The τ⁻¹ prefactor lower-caps to `τ₀⁻¹`.  `Dz := (Ccr·τ₀⁻¹·√(τ₁/τ₀)ⁿ·CF)·gaussDdim(wL·τ₁)·gaussDdim(wF·s)`
  — a Gaussian PAIR, integrable via banked `gaussDdim_pair_integrable`.

  ⚠  STILL NOT `a₁ = R/6`.  The crude time-derivative envelope `hAcrude`, `hFdom`, and the measurability /
  base-integrability carries remain named geometric inputs — this brick REDUCES `hZ` (and hence
  `hpardiff`) to them, it does NOT discharge them.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`.
-/
import QIQTH.WitnessTimeHasDerivAt
import QIQTH.HrawCampaignOne
import QIQTH.CConvV2GaussianPairing

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing
open QIQTH.WitnessTimeDeriv
open scoped Topology BigOperators

namespace QIQTH.HZDataFromCrudeEnv

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the WIDTH-INTERVAL Gaussian domination helper.
    ############################################################################### -/

/-- **★ `gaussDdim_width_interval_dom`.**  For a time `t` in a POSITIVE interval `[τ₀, τ₁]`
    (`0 < τ₀ ≤ t ≤ τ₁`) and `0 < wL`, the Gaussian `gaussDdim (wL·t)` is dominated, UNIFORMLY over
    `t ∈ [τ₀,τ₁]`, by a fixed multiple of the WIDEST Gaussian:
        `gaussDdim (wL·t) z ≤ √(τ₁/τ₀)ⁿ · gaussDdim (wL·τ₁) z`.
    Route: rewrite `wL·t = (t/τ₁)·(wL·τ₁)` and apply the banked `HrawCampaignOne.gaussDdim_width_mono`
    (widths `t/τ₁ ≤ 1`, common scale `wL·τ₁`), giving the coefficient `√(τ₁/t)ⁿ`; then `√(τ₁/t) ≤ √(τ₁/τ₀)`
    since `t ≥ τ₀ > 0`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_width_interval_dom {wL τ₀ τ₁ t : ℝ} (hwL : 0 < wL) (hτ₀ : 0 < τ₀)
    (h0t : τ₀ ≤ t) (ht1 : t ≤ τ₁) (z : Point n) :
    gaussDdim (wL * t) z ≤ Real.sqrt (τ₁ / τ₀) ^ n * gaussDdim (wL * τ₁) z := by
  have ht : 0 < t := lt_of_lt_of_le hτ₀ h0t
  have hτ₁ : 0 < τ₁ := lt_of_lt_of_le ht ht1
  have hwτ₁ : 0 < wL * τ₁ := mul_pos hwL hτ₁
  have hw₀ : 0 < t / τ₁ := div_pos ht hτ₁
  have hle : t / τ₁ ≤ 1 := (div_le_one hτ₁).mpr ht1
  have hrw : wL * t = (t / τ₁) * (wL * τ₁) := by field_simp
  have hmono := QIQTH.HrawCampaignOne.gaussDdim_width_mono hw₀ hle hwτ₁ z
  rw [← hrw, one_mul] at hmono
  refine le_trans hmono ?_
  have hdivle : τ₁ / t ≤ τ₁ / τ₀ := div_le_div_of_nonneg_left hτ₁.le hτ₀ h0t
  have hsqrt : Real.sqrt (1 / (t / τ₁)) ≤ Real.sqrt (τ₁ / τ₀) := by
    apply Real.sqrt_le_sqrt
    rw [one_div_div]; exact hdivle
  have hpow : Real.sqrt (1 / (t / τ₁)) ^ n ≤ Real.sqrt (τ₁ / τ₀) ^ n :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt n
  exact mul_le_mul_of_nonneg_right hpow (gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### §B — the GENERIC `(A,F)` reduction: `hZ` inner body from the crude envelope + carries.
    ############################################################################### -/

/-- **★★★ J4-916 — `hZslice_of_crudeEnv`.**  THE `hZ` INNER BODY, SUPPLIED.  For any kernels `A, F` and
    a single `(s, c)` with `c − s` strictly inside a positive window `(τ₀, τ₁)`, produces the EXACT
    per-`(s,c)` inner existential of `HpardiffZTimeDerivReduction.hpardiff_of_zTimeDeriv`'s family `hZ`
    (`∃ V ∈ 𝓝 c, ∃ Dz, (i)∧(ii)∧(iii)∧(iv)∧(v)`), from named carries:
      • `hAcrude` — the crude TIME-derivative Gaussian envelope on `[τ₀,τ₁]` (the SAME carried input
        J4-911 left open; a genuine geometric residue, NOT the conclusion);
      • `hFdom`   — the width-Gaussian Levi source bound;
      • `hmeas`   — the derivative-slice `z`-measurability carry;
      • `hbase`   — the base-slice `z`-integrability carry;
      • `hDiff`   — the `z`-pointwise TIME `HasDerivAt` (conjunct (v)), for ANY `c'` with `0 < c'−s`
        (DISCHARGED for the concrete witness by J4-915 — see the wrapper below).
    The dominator `Dz` is EXPLICITLY CONSTRUCTED (a Gaussian pair), and the uniform-over-`V` bound (iv)
    uses `gaussDdim_width_interval_dom`.  NONE of the hypotheses is the conclusion.  NOT `a₁ = R/6`. -/
theorem hZslice_of_crudeEnv
    (A F : ℝ → Point n → Point n → ℝ) (s c : ℝ)
    (τ₀ τ₁ Ccr wL CF wF : ℝ)
    (hτ₀ : 0 < τ₀) (hwL : 0 < wL) (hCcr : 0 ≤ Ccr) (hCF : 0 ≤ CF) (hwF : 0 < wF) (hs : 0 < s)
    (hlo : τ₀ < c - s) (hhi : c - s < τ₁)
    (hAcrude : ∀ z : Point n, ∀ τ ∈ Set.Icc τ₀ τ₁,
        |deriv (fun r => A r 0 z) τ| ≤ Ccr * τ⁻¹ * gaussDdim (wL * τ) (0 - z))
    (hFdom : ∀ z : Point n, |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hmeas : AEStronglyMeasurable
        (fun z => deriv (fun r => A r 0 z) (c - s) * F s z 0) volume)
    (hbase : Integrable (fun z => A (c - s) 0 z * F s z 0) volume)
    (hDiff : ∀ z : Point n, ∀ c' : ℝ, 0 < c' - s →
        HasDerivAt (fun c' => A (c' - s) 0 z * F s z 0)
          (deriv (fun r => A r 0 z) (c' - s) * F s z 0) c') :
    ∃ V ∈ 𝓝 c, ∃ Dz : Point n → ℝ,
      Integrable Dz volume ∧
      Integrable (fun z => A (c - s) 0 z * F s z 0) volume ∧
      AEStronglyMeasurable
        (fun z => deriv (fun r => A r 0 z) (c - s) * F s z 0) volume ∧
      (∀ᵐ z ∂volume, ∀ c' ∈ V,
        ‖deriv (fun r => A r 0 z) (c' - s) * F s z 0‖ ≤ Dz z) ∧
      (∀ᵐ z ∂volume, ∀ c' ∈ V,
        HasDerivAt (fun c' => A (c' - s) 0 z * F s z 0)
          (deriv (fun r => A r 0 z) (c' - s) * F s z 0) c') := by
  -- the differentiation window and its radius.
  set δ : ℝ := min (c - s - τ₀) (τ₁ - (c - s)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
  -- every `c' ∈ ball c δ` has `c'−s ∈ [τ₀,τ₁]` and `0 < c'−s`.
  have hmemτ : ∀ c' ∈ Metric.ball c δ, (c' - s ∈ Set.Icc τ₀ τ₁) ∧ 0 < c' - s := by
    intro c' hc'
    rw [Metric.mem_ball, Real.dist_eq] at hc'
    have hab := abs_lt.mp hc'
    have hδ1 : δ ≤ c - s - τ₀ := by rw [hδdef]; exact min_le_left _ _
    have hδ2 : δ ≤ τ₁ - (c - s) := by rw [hδdef]; exact min_le_right _ _
    refine ⟨⟨by linarith [hab.1], by linarith [hab.2]⟩, by linarith [hab.1]⟩
  -- the CONSTANT amplitude and the Gaussian-pair dominator.
  set K : ℝ := Ccr * τ₀⁻¹ * Real.sqrt (τ₁ / τ₀) ^ n * CF with hKdef
  set Dz : ℝ → (Point n → ℝ) := fun _ z =>
    K * (gaussDdim (wL * τ₁) z * gaussDdim (wF * s) z) with hDzdef
  refine ⟨Metric.ball c δ, Metric.ball_mem_nhds c hδpos, Dz 0, ?_, hbase, hmeas, ?_, ?_⟩
  · -- (i) `Integrable Dz`.
    exact (gaussDdim_pair_integrable (wL * τ₁) (wF * s)).const_mul K
  · -- (iv) the UNIFORM-over-`V` pointwise dominator.
    refine ae_of_all _ (fun z c' hc' => ?_)
    obtain ⟨hτmem, _hτpos⟩ := hmemτ c' hc'
    rw [Real.norm_eq_abs, abs_mul]
    -- lower-cap the τ⁻¹ prefactor and width-widen the Gaussian.
    have hD := hAcrude z (c' - s) hτmem
    rw [gaussDdim_zero_sub] at hD
    have hinv : (c' - s)⁻¹ ≤ τ₀⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hτ₀ hτmem.1
    have hwid := gaussDdim_width_interval_dom hwL hτ₀ hτmem.1 hτmem.2 z
    have hCA0 : 0 ≤ Ccr * τ₀⁻¹ := mul_nonneg hCcr (by positivity)
    have hderiv_bound :
        |deriv (fun r => A r 0 z) (c' - s)|
          ≤ Ccr * τ₀⁻¹ * (Real.sqrt (τ₁ / τ₀) ^ n * gaussDdim (wL * τ₁) z) := by
      calc |deriv (fun r => A r 0 z) (c' - s)|
          ≤ Ccr * (c' - s)⁻¹ * gaussDdim (wL * (c' - s)) z := hD
        _ ≤ Ccr * τ₀⁻¹ * gaussDdim (wL * (c' - s)) z :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hCcr)
              (gaussDdim_nonneg _ _)
        _ ≤ Ccr * τ₀⁻¹ * (Real.sqrt (τ₁ / τ₀) ^ n * gaussDdim (wL * τ₁) z) :=
            mul_le_mul_of_nonneg_left hwid hCA0
    have hFz := hFdom z
    have hbnd_nn : 0 ≤ Ccr * τ₀⁻¹ * (Real.sqrt (τ₁ / τ₀) ^ n * gaussDdim (wL * τ₁) z) :=
      mul_nonneg hCA0 (mul_nonneg (by positivity) (gaussDdim_nonneg _ _))
    calc |deriv (fun r => A r 0 z) (c' - s)| * |F s z 0|
        ≤ (Ccr * τ₀⁻¹ * (Real.sqrt (τ₁ / τ₀) ^ n * gaussDdim (wL * τ₁) z))
            * (CF * gaussDdim (wF * s) z) :=
          mul_le_mul hderiv_bound hFz (abs_nonneg _) hbnd_nn
      _ = Dz 0 z := by rw [hDzdef, hKdef]; ring
  · -- (v) the `z`-pointwise TIME `HasDerivAt`, threaded from `hDiff`.
    refine ae_of_all _ (fun z c' hc' => ?_)
    exact hDiff z c' (hmemτ c' hc').2

/-- **Non-vacuity witness.**  The full hypothesis bundle of `hZslice_of_crudeEnv` is jointly satisfiable
    (`A ≡ 0`, `F ≡ 0`, concrete scalars `τ₀=1, τ₁=3, s=1, c=3` so `c−s=2 ∈ (1,3)`, all constants `1`), so
    the reduction is NOT vacuously true — no unsatisfiable-antecedent trap.  NOT `a₁ = R/6`. -/
theorem hZslice_of_crudeEnv_hyp_satisfiable :
    ∃ (A F : ℝ → Point n → Point n → ℝ) (s c τ₀ τ₁ Ccr wL CF wF : ℝ),
      0 < τ₀ ∧ 0 < wL ∧ 0 ≤ Ccr ∧ 0 ≤ CF ∧ 0 < wF ∧ 0 < s ∧ τ₀ < c - s ∧ c - s < τ₁ ∧
      (∀ z : Point n, ∀ τ ∈ Set.Icc τ₀ τ₁,
          |deriv (fun r => A r 0 z) τ| ≤ Ccr * τ⁻¹ * gaussDdim (wL * τ) (0 - z)) ∧
      (∀ z : Point n, |F s z 0| ≤ CF * gaussDdim (wF * s) z) ∧
      AEStronglyMeasurable (fun z => deriv (fun r => A r 0 z) (c - s) * F s z 0) volume ∧
      Integrable (fun z => A (c - s) 0 z * F s z 0) volume ∧
      (∀ z : Point n, ∀ c' : ℝ, 0 < c' - s →
          HasDerivAt (fun c' => A (c' - s) 0 z * F s z 0)
            (deriv (fun r => A r 0 z) (c' - s) * F s z 0) c') := by
  refine ⟨fun _ _ _ => 0, fun _ _ _ => 0, 1, 3, 1, 3, 1, 1, 1, 1,
    one_pos, one_pos, zero_le_one, zero_le_one, one_pos, one_pos, by norm_num, by norm_num,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro z τ hτ
    have hτpos : 0 < τ := lt_of_lt_of_le one_pos hτ.1
    simp only [deriv_const', abs_zero]
    exact mul_nonneg (mul_nonneg zero_le_one (inv_nonneg.mpr hτpos.le)) (gaussDdim_nonneg _ _)
  · intro z; simp only [abs_zero]
    exact mul_nonneg zero_le_one (gaussDdim_nonneg _ _)
  · simp only [mul_zero]; exact aestronglyMeasurable_const
  · simp only [mul_zero]; exact integrable_zero _ _ _
  · intro z c' _
    simp only [mul_zero]
    exact hasDerivAt_const c' (0 : ℝ)

/-! ###############################################################################
    ### §C — the CONCRETE witness wrapper: (v) discharged via J4-915.
    ############################################################################### -/

/-- **★★★ `witnessHZslice_of_crudeEnv` — the concrete gated van-Vleck instantiation.**  For
    `A := vanVleckGatedWitness g gi hC hK S a b`, produces the SAME `hZ` inner existential, with the
    differentiability conjunct (v) DISCHARGED UNCONDITIONALLY via J4-915
    (`WitnessTimeHasDerivAt.witnessZTime_hasDerivAt`, at `V := Set.Ioi s`), so the only remaining carries
    are `hAcrude` (crude TIME-derivative envelope, J4-911 class), `hFdom`, and the measurability /
    base-integrability inputs — i.e. `hpardiff` is REDUCED to exactly the J4-911-class named carries.
    NOT `a₁ = R/6`. -/
theorem witnessHZslice_of_crudeEnv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (s c : ℝ)
    (τ₀ τ₁ Ccr wL CF wF : ℝ)
    (hτ₀ : 0 < τ₀) (hwL : 0 < wL) (hCcr : 0 ≤ Ccr) (hCF : 0 ≤ CF) (hwF : 0 < wF) (hs : 0 < s)
    (hlo : τ₀ < c - s) (hhi : c - s < τ₁)
    (hAcrude : ∀ z : Point n, ∀ τ ∈ Set.Icc τ₀ τ₁,
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) τ|
          ≤ Ccr * τ⁻¹ * gaussDdim (wL * τ) (0 - z))
    (hFdom : ∀ z : Point n, |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hmeas : AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s)
          * F s z 0) volume)
    (hbase : Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0) volume) :
    ∃ V ∈ 𝓝 c, ∃ Dz : Point n → ℝ,
      Integrable Dz volume ∧
      Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0) volume ∧
      AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s)
          * F s z 0) volume ∧
      (∀ᵐ z ∂volume, ∀ c' ∈ V,
        ‖deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c' - s) * F s z 0‖ ≤ Dz z) ∧
      (∀ᵐ z ∂volume, ∀ c' ∈ V,
        HasDerivAt (fun c' => vanVleckGatedWitness g gi hC hK S a b (c' - s) 0 z * F s z 0)
          (deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c' - s) * F s z 0) c') := by
  refine hZslice_of_crudeEnv (vanVleckGatedWitness g gi hC hK S a b) F s c τ₀ τ₁ Ccr wL CF wF
    hτ₀ hwL hCcr hCF hwF hs hlo hhi hAcrude hFdom hmeas hbase ?_
  intro z c' hpos
  exact witnessZTime_hasDerivAt g gi hC hK S a b F s (Set.Ioi s)
    (fun c'' hc'' => sub_pos.mpr hc'') z c' (Set.mem_Ioi.mpr (by linarith))

end QIQTH.HZDataFromCrudeEnv

section AxiomChecks
open QIQTH.HZDataFromCrudeEnv
#print axioms gaussDdim_width_interval_dom
#print axioms hZslice_of_crudeEnv
#print axioms hZslice_of_crudeEnv_hyp_satisfiable
#print axioms witnessHZslice_of_crudeEnv
end AxiomChecks
