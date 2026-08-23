/-
  HCompNearCarryTerm2Term3DomainRestrictedBound — J4-?: the `W''S'`-domain-restricted capstone for
  `nb`'s `Bfac` summands T2/T3 (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`) AND T4/LEFTOVER (`∂ⱼ∂ᵢA`), mirroring T1's
  capstone (`HCompNearCarryTerm1DomainRestrictedBound.hsMixed_gaussDdim_mul_amp_domain_restricted_bound`,
  J4-1023) exactly, but for the STRICTLY SIMPLER `linMult`-only (T2/T3) and flat-bound-only (T4) cases.
  J4-1069's audit found T1 alone had reached this `W''S'`-domain-restricted level (via J4-1020..1028);
  T2/T3/T4's prior progress (`HCompNearCarryBfacLinearTermsLinMultBridge.lean`, J4-1041) stopped at a
  FLAT (full-`ℝⁿ`, non-domain-restricted) bound.  THIS FILE closes that specific gap.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PLAN (Sol `gpt-5.6-sol`, high, consulted BEFORE Lean — GO, minor adjustments incorporated).

  T2/T3's shared underlying quantity is `grTerm τ Q v := −(∑ k, v k * Q k) / (2 * τ)`, and
  `HCompNearCarryBfacLinearTermsLinMultBridge.grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp` (J4-1041)
  ALREADY identifies `gaussDdim τ v · (grTerm τ Q v · Amp v) = −(linMult τ Q v · Amp v)` LITERALLY (bare
  `ring`).  T1's capstone needed BOTH `heatHessMult` and `linMult` tail bounds (since `hsMixed` is a
  DIFFERENCE of a quadratic and a linear piece); T2/T3 need ONLY `linMult`'s tail bound
  (`HCompNearCarryTerm1DomainRestrictedBound.linMult_amp_subset_tail_le`, J4-1023, ALREADY generalized
  from the literal radial tail set to an ARBITRARY measurable subset — exactly the interface this file
  needs, built for T1's own use but fully reusable here verbatim) — so this is a DIRECT MECHANICAL CLONE
  of T1's `integral_add_compl`-based assembly, with the `heatHessMult` half of every step simply absent.
  Sol confirmed: (1) no new base-slot/field-slot mismatch — `W p := uniformInverseChart g gi hC hK p q₀`
  is the SAME map T1 used, `Q` is a free/generic parameter that later instantiates to `PJ`/`PI`; (2) the
  complement-tail estimate is naturally for `linMult`, transferred to `grTerm`'s shape via the pointwise
  negation identity + `integral_congr_ae`, with the sign vanishing under `|·|`; (3) reuse T1's exact
  proof skeleton, verified sound.

  T4/LEFTOVER (`flat_gaussian_mul_amp_bound`, J4-1041) needs NO tail decomposition at all — Sol flagged
  (CRITICALLY) that one must NOT derive the domain-restricted bound directly from the full-space bound
  alone (a bound on `|∫ h|` does not, by itself, control `|∫_A h|` — cancellation could make the latter
  LARGER), and must instead be RE-DERIVED from the underlying POINTWISE majorant `|G(v)·Amp(v)| ≤
  M·G(v)` (`G := gaussDdim τ v ≥ 0`), then Mathlib's `setIntegral_le_integral` (nonneg integrand,
  `Measure.restrict_le_self`) gives `∫_A (M·G) ≤ ∫_univ (M·G) = M` for ANY measurable `A`, no
  ball/tail/Lipschitz machinery whatsoever — Sol-confirmed this reasoning is correct PROVIDED
  `MeasurableSet A` and the pointwise/integrability side-conditions are carried explicitly (both done
  below, using the SAME `flat_gaussian_mul_amp_bound`-internal majorant argument, restricted to `A`).

  ## WHAT LANDS.
    • `grTerm_gaussDdim_mul_amp_domain_restricted_bound` — ★★★★★ T2/T3's `W''S'`-domain-restricted
      capstone: `∃ S' ρ, IsOpen S' ∧ q₀∈S' ∧ 0<ρ ∧ |∫_{W''S'} G·(grTerm·Amp)| ≤ [full-space G1 bound] +
      [complement-tail correction]`, for an ABSTRACT `Amp` Lipschitz-at-`0` — the T2/T3 analogue of
      J4-1023's T1 capstone.
    • `flat_gaussDdim_mul_amp_domain_restricted_bound` — ★★★★ T4/LEFTOVER's `W''S'`-domain-restricted
      capstone: `∃ S', IsOpen S' ∧ q₀∈S' ∧ |∫_{W''S'} G·Amp| ≤ M`, for an ABSTRACT merely-BOUNDED `Amp`
      — the SAME bound `M` as the flat full-space case, transferred to ANY subdomain by nonneg-integrand
      monotonicity (no tail correction needed at all — the cheapest of the four `Bfac` summands, exactly
      as J4-1041 already found at the full-space level).

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  Exactly like
  T1's capstone (J4-1023), this file's `Amp` is ABSTRACT (Lipschitz-at-`0` / merely-bounded, as
  appropriate) — it does NOT verify the LITERAL `Bfac(V w)/|det(fderiv W (V w))|` composition (chart-
  inverse-composed, Jacobian-divided) is itself Lipschitz-at-`0`/bounded in `w` for T2/T3/T4's own
  factors (`∂ⱼA`, `∂ᵢA`, `∂ⱼ∂ᵢA` — a SEPARATE gap, distinct from and in addition to J4-1023/1028's
  already-flagged `hsMixed·A` version of the same composition issue).  Does NOT discharge `hxmem` (the
  shared upstream architectural wall gating ALL FOUR `Bfac` summands equally, per J4-1041's own finding —
  UNCHANGED, NOT attempted here).  Does NOT discharge `hfac`'s literal carry over `S'` (residuals r1/r2 of
  `HCompNearCarryKPrimeBaseFieldCoV`, UNCHANGED).  Does NOT bridge the outer-`s`-integration composition
  (BRICK 2's fixed-`(s,t)` bound vs. the `HcompLeftoverSliverWindowBound`/`grTerm_sliver_window_bound_of_
  lipschitz` family's already-`s`-integrated sliver-window payoffs — a genuinely SEPARATE, unbridged
  axis, per J4-1069's frontier item 3, UNCHANGED).  Does NOT discharge `nb`, `hCConv`, or any part of
  `hcomp`.  The far-carry `fb` remains SEPARATELY open regardless.  `a₁ = R/6` remains STRICTLY
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no
  `:= True`, no vacuous/unsatisfiable hypothesis, none equal to the conclusion (both theorems are genuine
  new quantitative estimates specific to `nb`'s ACTUAL post-CoV domain `W''S'`, not restatements of the
  already-banked full-space bounds), no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge
import QIQTH.HCompNearCarryTerm1DomainRestrictedBound

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatHessMoment
open QIQTH.HeatHessMultBallTail QIQTH.HCompNearCarryTerm1LipschitzCancellation QIQTH.ExpMap
open QIQTH.HCompNearCarryTerm1AmpWeightedTail QIQTH.HCompNearCarryTerm1BallGeometry
open QIQTH.HerrHminGeneralQ0GeneralK QIQTH.BaseSlotM1M4ImageOpen
open QIQTH.HCompNearCarryTerm1DomainRestrictedBound QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge
open scoped Topology BigOperators

namespace QIQTH.HCompNearCarryTerm2Term3DomainRestrictedBound

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### PART 1 — T2/T3's `W''S'`-domain-restricted capstone (the `grTerm`/`linMult` case).
    ############################################################################### -/

/-- **★★★★★ `grTerm_gaussDdim_mul_amp_domain_restricted_bound` — THE T2/T3 CAPSTONE.**  For the
    base-slot CoV map `W p := uniformInverseChart g gi hC hK p q₀` at `q₀ ∈ interior K`, `τ > 0`, a
    chart-Jacobian jet field `Q`, and `Amp` Lipschitz-at-`0` (modulus `L ≥ 0`), the `grTerm`-weighted
    Gaussian integral RESTRICTED TO `nb`'s ACTUAL post-CoV domain `W''S'` (matching
    `HCompNearCarryKPrimeBaseFieldCoV`'s BRICK 2 outer-integral domain, EXACTLY as T1's capstone does) is
    bounded by the full-space bound (`grTerm_gaussian_mul_amp_lipschitz_bound`, J4-1041) PLUS a
    complement-tail correction (`linMult_amp_subset_tail_le`, J4-1023, composed with J4-1020's Brick B
    applied to `W''S'` itself) — the DIRECT mechanical clone of T1's `hsMixed_gaussDdim_mul_amp_domain_
    restricted_bound` (J4-1023), with the `heatHessMult` half of every step absent (T2/T3 need ONLY
    `linMult`).  ABSTRACT `Amp` only — does NOT verify the literal `∂ⱼA`/`∂ᵢA` composed-with-`V`-and-
    Jacobian object is Lipschitz-at-`0` (a SEPARATE, still-open gap, see file docstring).  NOT
    `a₁ = R/6`. -/
theorem grTerm_gaussDdim_mul_amp_domain_restricted_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (τ : ℝ) (hτ : 0 < τ) (Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    ∃ (S' : Set (Point n)) (ρ : ℝ), IsOpen S' ∧ q₀ ∈ S' ∧ 0 < ρ ∧
      |∫ v : Point n in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
          gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)|
        ≤ (n : ℝ) ^ 2 * L * ‖Q‖
          + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
              * (|Amp 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                  + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)) := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  obtain ⟨S', V, hS'open, hq0S', hinj, hV, hfd, hJpos, hWSopen⟩ :=
    uniformInverseChart_baseSlot_M1M4_image_open_generalK g gi hC hK hq₀
  set U : Set (Point n) := W '' S' with hUdef
  have hq0K : q₀ ∈ K := interior_subset hq₀
  have hWq0 : W q₀ = 0 := uniformInverseChart_diag_zero_of_mem g gi hC hK hq0K
  have h0U : (0 : Point n) ∈ U := ⟨q₀, hq0S', hWq0⟩
  obtain ⟨ρ, hρpos, hρsub⟩ := S'_ball_complement_subset_rncRadialSq_tail hWSopen h0U
  have hρsub' : Uᶜ ⊆ {v : Point n | ρ ^ 2 ≤ rncRadialSq v} := by
    intro v hv
    have := hρsub hv
    simpa using this
  have hUmeas : MeasurableSet U := hWSopen.measurableSet
  have hUcmeas : MeasurableSet Uᶜ := hUmeas.compl
  refine ⟨S', ρ, hS'open, hq0S', hρpos, ?_⟩
  -- The pointwise negation identity: `G·(grTerm·Amp) = −(linMult·Amp)`.
  have hpt1 : ∀ v : Point n, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)
      = -(linMult τ Q v * Amp v) :=
    fun v => grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp τ Q v (Amp v)
  have hLamp_int : Integrable (fun v : Point n => linMult τ Q v * Amp v) volume :=
    linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip
  have hInt : Integrable (fun v : Point n =>
      gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)) volume :=
    hLamp_int.neg.congr (ae_of_all _ (fun v => (hpt1 v).symm))
  have hsplit := integral_add_compl hUmeas hInt
  -- Full-space bound, J4-1041.
  have hGfull := grTerm_gaussian_mul_amp_lipschitz_bound τ hτ Q L hL Amp hAmp hlip
  -- Complement-tail bound: rewrite pointwise to `linMult`, then reuse J4-1023's generalized tail bound.
  have hLtail := linMult_amp_subset_tail_le τ hτ ρ Q Amp hAmp L hL hlip hUcmeas hρsub'
  have hUc_eq : ∫ v : Point n in Uᶜ, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)
      = -(∫ v : Point n in Uᶜ, linMult τ Q v * Amp v) := by
    rw [← integral_neg]
    exact setIntegral_congr_fun hUcmeas (fun v _ => hpt1 v)
  have hGtail : |∫ v : Point n in Uᶜ, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)|
      ≤ Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
          * (|Amp 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
              + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)) := by
    rw [hUc_eq, abs_neg]; exact hLtail
  have hUeq : ∫ v : Point n in U, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)
      = (∫ v : Point n, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v))
        - ∫ v : Point n in Uᶜ, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v) := by
    linarith [hsplit]
  have habs : |∫ v : Point n in U, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)|
      ≤ |∫ v : Point n, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)|
        + |∫ v : Point n in Uᶜ, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)| := by
    rw [hUeq, sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
  refine habs.trans ?_
  exact add_le_add hGfull hGtail

/-! ###############################################################################
    ### PART 2 — T4/LEFTOVER's `W''S'`-domain-restricted capstone (the flat case).
    ############################################################################### -/

/-- **★★★★ `flat_gaussDdim_mul_amp_domain_restricted_bound` — THE T4/LEFTOVER CAPSTONE.**  For the
    base-slot CoV map `W p := uniformInverseChart g gi hC hK p q₀` at `q₀ ∈ interior K`, `τ > 0`, and
    `Amp` merely BOUNDED by `M` (no Lipschitz needed), the flat Gaussian integral RESTRICTED TO `nb`'s
    ACTUAL post-CoV domain `W''S'` is bounded by the SAME `M` as the full-space bound
    (`flat_gaussian_mul_amp_bound`, J4-1041) — via the underlying pointwise majorant `|G·Amp| ≤ M·G`
    (`G := gaussDdim τ v ≥ 0`) and Mathlib's `setIntegral_le_integral` (nonneg-integrand set
    monotonicity, `Measure.restrict_le_self`), which transfers `∫ (M·G) = M` to ANY measurable subdomain
    with NO tail/ball decomposition at all — the cheapest of the four `Bfac` summands, exactly as
    J4-1041 found at the full-space level.  NOT `a₁ = R/6`. -/
theorem flat_gaussDdim_mul_amp_domain_restricted_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (τ : ℝ) (hτ : 0 < τ) (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ v : Point n, |Amp v| ≤ M) :
    ∃ (S' : Set (Point n)), IsOpen S' ∧ q₀ ∈ S' ∧
      |∫ v : Point n in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
          gaussDdim τ v * Amp v| ≤ M := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  obtain ⟨S', V, hS'open, hq0S', hinj, hV, hfd, hJpos, hWSopen⟩ :=
    uniformInverseChart_baseSlot_M1M4_image_open_generalK g gi hC hK hq₀
  set U : Set (Point n) := W '' S' with hUdef
  have hUmeas : MeasurableSet U := hWSopen.measurableSet
  refine ⟨S', hS'open, hq0S', ?_⟩
  have hGnn : ∀ v : Point n, 0 ≤ gaussDdim τ v := fun v => gaussDdim_nonneg' τ v
  have hGint : Integrable (fun v : Point n => gaussDdim τ v) volume := gaussDdim_integrable' τ hτ
  have hD_int : Integrable (fun v : Point n => M * gaussDdim τ v) volume := hGint.const_mul _
  have hptbnd : ∀ v : Point n, |gaussDdim τ v * Amp v| ≤ M * gaussDdim τ v := fun v => by
    rw [abs_mul, abs_of_nonneg (hGnn v)]
    calc gaussDdim τ v * |Amp v| ≤ gaussDdim τ v * M := by
          exact mul_le_mul_of_nonneg_left (hbound v) (hGnn v)
      _ = M * gaussDdim τ v := by ring
  have hmeas : AEStronglyMeasurable (fun v : Point n => gaussDdim τ v * Amp v) volume :=
    hGint.aestronglyMeasurable.mul hAmp
  have hint : Integrable (fun v : Point n => gaussDdim τ v * Amp v) volume :=
    hD_int.mono' hmeas (Filter.Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs]; exact hptbnd v))
  have hstep1 : |∫ v : Point n in U, gaussDdim τ v * Amp v|
      ≤ ∫ v : Point n in U, |gaussDdim τ v * Amp v| := by
    have h := norm_integral_le_integral_norm (μ := (volume.restrict U))
      (fun v : Point n => gaussDdim τ v * Amp v)
    simpa only [Real.norm_eq_abs] using h
  refine hstep1.trans ?_
  have hstep2 : ∫ v : Point n in U, |gaussDdim τ v * Amp v| ≤ ∫ v : Point n in U, M * gaussDdim τ v :=
    setIntegral_mono_on (hint.abs.integrableOn) (hD_int.integrableOn) hUmeas (fun v _ => hptbnd v)
  refine hstep2.trans ?_
  have hstep3 : ∫ v : Point n in U, M * gaussDdim τ v ≤ ∫ v : Point n, M * gaussDdim τ v :=
    setIntegral_le_integral hD_int
      (Filter.Eventually.of_forall (fun v => mul_nonneg hM (hGnn v)))
  refine hstep3.trans ?_
  rw [integral_const_mul, gaussDdim_mass_one τ hτ, mul_one]

end QIQTH.HCompNearCarryTerm2Term3DomainRestrictedBound

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm2Term3DomainRestrictedBound
#print axioms grTerm_gaussDdim_mul_amp_domain_restricted_bound
#print axioms flat_gaussDdim_mul_amp_domain_restricted_bound
end AxiomChecks
