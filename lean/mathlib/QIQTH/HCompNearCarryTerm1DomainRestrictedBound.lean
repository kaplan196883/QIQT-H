/-
  HCompNearCarryTerm1DomainRestrictedBound — J4-1023: THE ASSEMBLY DISPATCH.  Composes
  `HCompNearCarryTerm1LipschitzCancellation`'s (J4-1019) full-space G1 payoff,
  `HCompNearCarryTerm1AmpWeightedTail`'s (J4-1021) `Amp`-weighted tail bounds (GENERALIZED here from
  the literal tail set `{v | R² ≤ rncRadialSq v}` to an ARBITRARY measurable subset of it), and
  `BaseSlotM1M4ImageOpen`'s (J4-1022) `IsOpen (W''S')` + the diagonal-zero fact, into a single explicit
  bound on `nb`'s ACTUAL post-CoV (w-space) domain `W''S'` — for an ABSTRACT `Amp` weight
  Lipschitz-at-`0`.  Sol (`gpt-5.6-sol`, high, 2026-08-23) GO-confirmed the plan before Lean.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ASSEMBLY.

  (1) GENERALIZE J4-1021's tail bounds from the literal tail set `S_R := {v | R² ≤ rncRadialSq v}` to
  an ARBITRARY measurable `A ⊆ S_R`.  Every step of `heatHessMult_amp_tail_le`/`linMult_amp_tail_le`/
  `hsMixed_amp_tail_le`'s proofs is domain-generic EXCEPT the final chain from `∫_{S_R} D` down to the
  numeric moment bound (`gaussDdim_tail_mass_le`/`normPow_gaussDdim_tail_le`, both stated on the LITERAL
  `S_R`); inserting ONE extra monotonicity step `∫_A D ≤ ∫_{S_R} D` (`setIntegral_mono_set`, nonneg `D`,
  `A ⊆ S_R` via `hAsub.eventuallyLE`) before that chain closes the gap — Sol-confirmed sound, no
  Mathlib-version pitfall beyond the `.eventuallyLE` coercion already used elsewhere in this campaign
  (`ChartImageApproxIdentity.lean`).

  (2) INSTANTIATE `A := (W''S')ᶜ`, where `S'`/`W` are `BaseSlotM1M4ImageOpen`'s (J4-1022) witnesses:
  `IsOpen (W''S')` is J4-1022's own payoff; `0 ∈ W''S'` follows from `q₀ ∈ S'` (J4-1022) composed with
  `uniformInverseChart_diag_zero_of_mem` (J4-1021, `W q₀ = uniformInverseChart … q₀ q₀ = 0`).  Applying
  `S'_ball_complement_subset_rncRadialSq_tail` (J4-1020, Brick B) to `S' := W''S'`, `x := 0` (using
  `rncRadialSq (v - 0) = rncRadialSq v`) gives `∃ ρ > 0, (W''S')ᶜ ⊆ {v | ρ² ≤ rncRadialSq v}` — EXACTLY
  the literal `S_ρ` shape (1)'s generalized bounds consume.

  (3) COMBINE via `integral_add_compl` (`∫_full = ∫_{W''S'} + ∫_{(W''S')ᶜ}`, using `IsOpen (W''S')` for
  measurability and a reconstructed pointwise-identity-based integrability fact for the raw
  `gaussDdim·hsMixed·Amp` integrand) with the triangle inequality, `hsMixed_gaussDdim_mul_amp_lipschitz_
  bound`'s (J4-1019) full-space bound, and (1)+(2)'s complement-tail bound, to bound
  `|∫_{W''S'} gaussDdim τ v · (hsMixed(v,PI,PJ,Q) · Amp v)|`.

  ## WHAT THIS IS **NOT**.  `W''S'` IS, per `HCompNearCarryKPrimeBaseFieldCoV`'s (J4-1010) BRICK 2, the
  LITERAL outer-integral domain `nb`'s Bfac-term1 integral runs over after the base-slot CoV — so THIS
  dispatch's domain genuinely matches `nb`'s actual domain, not merely an abstract stand-in.  HOWEVER,
  BRICK 2's literal integrand is `Bfac (V w) / |det (fderiv W (V w))|` — `Bfac` COMPOSED WITH THE
  INVERSE MAP `V` and DIVIDED BY THE JACOBIAN DETERMINANT — NOT simply `Amp w` evaluated directly at
  `w` as THIS file's abstract theorem assumes.  Showing that composed/Jacobian-weighted object is
  itself Lipschitz-at-`0` (the literal instantiation of `hlip` this file's capstone needs) is a
  GENUINE, NEWLY-IDENTIFIED, SEPARATE gap — NOT attempted here (Sol, `gpt-5.6-sol`, high, 2026-08-23,
  consulted with this exact caveat before Lean: "bank the abstract composed-domain bound as genuine
  infrastructure … it should not be advertised as closing the literal `nb` term1 wiring … that requires
  a separate theorem" for the `V`/Jacobian composition).  Sympy check
  (`docs/qg_roadmap/rnc_sympy/hcomp_j4_1023_complement_tail_compose_check.py`): confirms the composition
  introduces NO NEW asymptotic rate (the fixed-`ρ` tail term is exponentially subleading to the G1
  `O(1/√τ)` Lipschitz term as `τ → 0⁺`), i.e. a pure compositional sanity check, not a new numeric claim.

  Does NOT discharge `nb`, `hCConv`, or any part of `hcomp`.  Does NOT address `Bfac`'s OTHER THREE
  terms (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`, `∂ⱼ∂ᵢA`) — only term1 (`hsMixed·A`) infrastructure is touched, and even
  term1 is bounded only for an ABSTRACT `Amp`, not yet the literal `V`/Jacobian-composed amplitude.  The
  far-carry `fb` remains SEPARATELY open regardless.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryTerm1AmpWeightedTail
import QIQTH.HCompNearCarryTerm1BallGeometry
import QIQTH.BaseSlotM1M4ImageOpen

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatHessMoment
open QIQTH.HeatHessMultBallTail QIQTH.HCompNearCarryTerm1LipschitzCancellation QIQTH.ExpMap
open QIQTH.HCompNearCarryTerm1AmpWeightedTail QIQTH.HCompNearCarryTerm1BallGeometry
open QIQTH.HerrHminGeneralQ0GeneralK QIQTH.BaseSlotM1M4ImageOpen
open scoped Topology BigOperators

namespace QIQTH.HCompNearCarryTerm1DomainRestrictedBound

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### PART 1 — generalizing the `Amp`-weighted tail bounds to an arbitrary
    ### measurable subset of the literal tail set.
    ############################################################################### -/

/-- **`setIntegral_subset_tail_le`** — the reusable monotonicity bridge: for a nonnegative integrable
    `f` and a measurable `A ⊆ {v | R² ≤ rncRadialSq v}`, `∫_A f ≤ ∫_{tail} f`. -/
theorem setIntegral_subset_tail_le {R : ℝ} {A : Set (Point n)}
    (hAsub : A ⊆ {v : Point n | R ^ 2 ≤ rncRadialSq v})
    {f : Point n → ℝ} (hfi : Integrable f volume) (hfnn : ∀ v, 0 ≤ f v) :
    ∫ v : Point n in A, f v ≤ ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, f v :=
  setIntegral_mono_set hfi.integrableOn (Filter.Eventually.of_forall hfnn) hAsub.eventuallyLE

/-- **★★★ `heatHessMult_amp_subset_tail_le`** — GAP (I)'s `heatHessMult` bound, generalized from the
    literal tail set to an arbitrary measurable subset `A` of it.  Same RHS as `heatHessMult_amp_tail_le`
    (J4-1021), same proof, with `setIntegral_subset_tail_le` inserted before each moment-bound step. -/
theorem heatHessMult_amp_subset_tail_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) (p q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖)
    {A : Set (Point n)} (hAmeas : MeasurableSet A)
    (hAsub : A ⊆ {v : Point n | R ^ 2 ≤ rncRadialSq v}) :
    |∫ v : Point n in A, heatHessMult τ p q v * Amp v|
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖)
          * (|Amp 0| * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                + (1 / (2 * τ)))
              + L * ((1 / (4 * τ ^ 2))
                    * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                  + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1))) := by
  have hHHAmp_int : Integrable (fun v : Point n => heatHessMult τ p q v * Amp v) volume :=
    heatHessMult_mul_lipschitzAmp_integrable τ hτ p q Amp hAmp L hlip
  have hstep1 : |∫ v : Point n in A, heatHessMult τ p q v * Amp v|
      ≤ ∫ v : Point n in A, |heatHessMult τ p q v * Amp v| := by
    have h := norm_integral_le_integral_norm (μ := (volume.restrict A))
      (fun v : Point n => heatHessMult τ p q v * Amp v)
    simpa only [Real.norm_eq_abs] using h
  refine hstep1.trans ?_
  set Cco : ℝ := (n : ℝ) ^ 2 * ‖p‖ * ‖q‖ with hCcodef
  have hCconn : 0 ≤ Cco := by rw [hCcodef]; positivity
  set c0 : ℝ := Cco * |Amp 0| / (2 * τ) with hc0def
  set c1 : ℝ := Cco * L / (2 * τ) with hc1def
  set c2 : ℝ := Cco * |Amp 0| / (4 * τ ^ 2) with hc2def
  set c3 : ℝ := Cco * L / (4 * τ ^ 2) with hc3def
  have hc0nn : 0 ≤ c0 := by rw [hc0def]; positivity
  have hc1nn : 0 ≤ c1 := by rw [hc1def]; positivity
  have hc2nn : 0 ≤ c2 := by rw [hc2def]; positivity
  have hc3nn : 0 ≤ c3 := by rw [hc3def]; positivity
  set D : Point n → ℝ := fun v =>
      c0 * gaussDdim τ v + c1 * (‖v‖ ^ 1 * gaussDdim τ v)
        + c2 * (‖v‖ ^ 2 * gaussDdim τ v) + c3 * (‖v‖ ^ 3 * gaussDdim τ v) with hDdef
  have hD_int : Integrable D volume := by
    rw [hDdef]
    exact ((((gaussDdim_integrable τ hτ).const_mul _).add
      ((normPow_gauss_integrable 1 (by norm_num) τ hτ).const_mul _)).add
      ((normPow_gauss_integrable 2 (by norm_num) τ hτ).const_mul _)).add
      ((normPow_gauss_integrable 3 (by norm_num) τ hτ).const_mul _)
  have hpt : ∀ v : Point n, |heatHessMult τ p q v * Amp v| ≤ D v := by
    intro v
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    have hAmpv : |Amp v| ≤ |Amp 0| + L * ‖v‖ := by
      calc |Amp v| = |Amp 0 + (Amp v - Amp 0)| := by ring_nf
        _ ≤ |Amp 0| + |Amp v - Amp 0| := abs_add_le _ _
        _ ≤ |Amp 0| + L * ‖v‖ := by linarith [hlip v]
    calc |heatHessMult τ p q v * Amp v| = |heatHessMult τ p q v| * |Amp v| := abs_mul _ _
      _ ≤ (Cco * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v)) * (|Amp 0| + L * ‖v‖) := by
          refine mul_le_mul (by rw [hCcodef]; exact abs_heatHessMult_le τ hτ p q v) hAmpv
            (abs_nonneg _) (by positivity)
      _ = D v := by rw [hDdef, hc0def, hc1def, hc2def, hc3def]; ring
  have hstep2 : ∫ v : Point n in A, |heatHessMult τ p q v * Amp v| ≤ ∫ v : Point n in A, D v :=
    setIntegral_mono_on (hHHAmp_int.abs.integrableOn) hD_int.integrableOn hAmeas (fun v _ => hpt v)
  refine hstep2.trans ?_
  have hDnn : ∀ v : Point n, 0 ≤ D v := by
    intro v
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    rw [hDdef]; positivity
  have hDsub : ∫ v : Point n in A, D v
      ≤ ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, D v :=
    setIntegral_subset_tail_le hAsub hD_int hDnn
  refine hDsub.trans ?_
  have hi0 : IntegrableOn (fun v : Point n => c0 * gaussDdim τ v)
      {v : Point n | R ^ 2 ≤ rncRadialSq v} volume := ((gaussDdim_integrable τ hτ).integrableOn).const_mul _
  have hi1 : IntegrableOn (fun v : Point n => c1 * (‖v‖ ^ 1 * gaussDdim τ v))
      {v : Point n | R ^ 2 ≤ rncRadialSq v} volume :=
    ((normPow_gauss_integrable 1 (by norm_num) τ hτ).integrableOn).const_mul _
  have hi2 : IntegrableOn (fun v : Point n => c2 * (‖v‖ ^ 2 * gaussDdim τ v))
      {v : Point n | R ^ 2 ≤ rncRadialSq v} volume :=
    ((normPow_gauss_integrable 2 (by norm_num) τ hτ).integrableOn).const_mul _
  have hi3 : IntegrableOn (fun v : Point n => c3 * (‖v‖ ^ 3 * gaussDdim τ v))
      {v : Point n | R ^ 2 ≤ rncRadialSq v} volume :=
    ((normPow_gauss_integrable 3 (by norm_num) τ hτ).integrableOn).const_mul _
  have hi01 : IntegrableOn (fun v : Point n =>
      c0 * gaussDdim τ v + c1 * (‖v‖ ^ 1 * gaussDdim τ v)) {v : Point n | R ^ 2 ≤ rncRadialSq v}
      volume := hi0.add hi1
  have hi012 : IntegrableOn (fun v : Point n =>
      c0 * gaussDdim τ v + c1 * (‖v‖ ^ 1 * gaussDdim τ v) + c2 * (‖v‖ ^ 2 * gaussDdim τ v))
      {v : Point n | R ^ 2 ≤ rncRadialSq v} volume := hi01.add hi2
  have hval : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, D v
      = c0 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, gaussDdim τ v)
        + c1 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 1 * gaussDdim τ v)
        + (c2 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 2 * gaussDdim τ v)
            + c3 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 3 * gaussDdim τ v)) := by
    rw [hDdef, integral_add hi012 hi3, integral_add hi01 hi2,
      integral_add hi0 hi1, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul]
    ring
  rw [hval]
  have ht0 : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n := gaussDdim_tail_mass_le τ hτ R
  have ht1 : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 1 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1) :=
    normPow_gaussDdim_tail_le 1 (by norm_num) τ hτ R (3 / 2) (by norm_num)
      (by simpa using oneD_absMoment1 (2 * τ) (by positivity))
  have ht2 : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 2 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2) :=
    normPow_gaussDdim_tail_le 2 (by norm_num) τ hτ R 2 (by norm_num)
      (oneD_absMoment2 (2 * τ) (by positivity))
  have ht3 : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 3 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3) :=
    normPow_gaussDdim_tail_le 3 (by norm_num) τ hτ R (64 * Real.sqrt 2 + 1) (by positivity)
      (oneD_absMoment3 (2 * τ) (by positivity))
  have hfinal : c0 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, gaussDdim τ v)
        + c1 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 1 * gaussDdim τ v)
        + (c2 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 2 * gaussDdim τ v)
            + c3 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 3 * gaussDdim τ v))
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * (c0 + c1 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
              + (c2 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                  + c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3))) := by
    have e0 := mul_le_mul_of_nonneg_left ht0 hc0nn
    have e1 := mul_le_mul_of_nonneg_left ht1 hc1nn
    have e2 := mul_le_mul_of_nonneg_left ht2 hc2nn
    have e3 := mul_le_mul_of_nonneg_left ht3 hc3nn
    have hcomb := add_le_add (add_le_add e0 e1) (add_le_add e2 e3)
    refine hcomb.trans_eq ?_
    ring
  refine hfinal.trans_eq ?_
  rw [hc0def, hc1def, hc2def, hc3def]
  ring

/-- **★★★ `linMult_amp_subset_tail_le`** — GAP (I)'s `linMult` bound, generalized from the literal tail
    set to an arbitrary measurable subset `A` of it.  Same RHS as `linMult_amp_tail_le` (J4-1021). -/
theorem linMult_amp_subset_tail_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) (Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖)
    {A : Set (Point n)} (hAmeas : MeasurableSet A)
    (hAsub : A ⊆ {v : Point n | R ^ 2 ≤ rncRadialSq v}) :
    |∫ v : Point n in A, linMult τ Q v * Amp v|
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
          * (|Amp 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
              + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)) := by
  have hLAmp_int : Integrable (fun v : Point n => linMult τ Q v * Amp v) volume :=
    linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip
  have hstep1 : |∫ v : Point n in A, linMult τ Q v * Amp v|
      ≤ ∫ v : Point n in A, |linMult τ Q v * Amp v| := by
    have h := norm_integral_le_integral_norm (μ := (volume.restrict A))
      (fun v : Point n => linMult τ Q v * Amp v)
    simpa only [Real.norm_eq_abs] using h
  refine hstep1.trans ?_
  set Cco : ℝ := (n : ℝ) * ‖Q‖ / (2 * τ) with hCcodef
  have hCconn : 0 ≤ Cco := by rw [hCcodef]; positivity
  set d1 : ℝ := Cco * |Amp 0| with hd1def
  set d2 : ℝ := Cco * L with hd2def
  have hd1nn : 0 ≤ d1 := by rw [hd1def]; positivity
  have hd2nn : 0 ≤ d2 := by rw [hd2def]; positivity
  set D : Point n → ℝ := fun v => d1 * (‖v‖ ^ 1 * gaussDdim τ v) + d2 * (‖v‖ ^ 2 * gaussDdim τ v)
    with hDdef
  have hD_int : Integrable D volume := by
    rw [hDdef]
    exact ((normPow_gauss_integrable 1 (by norm_num) τ hτ).const_mul _).add
      ((normPow_gauss_integrable 2 (by norm_num) τ hτ).const_mul _)
  have hpt : ∀ v : Point n, |linMult τ Q v * Amp v| ≤ D v := by
    intro v
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    have hAmpv : |Amp v| ≤ |Amp 0| + L * ‖v‖ := by
      calc |Amp v| = |Amp 0 + (Amp v - Amp 0)| := by ring_nf
        _ ≤ |Amp 0| + |Amp v - Amp 0| := abs_add_le _ _
        _ ≤ |Amp 0| + L * ‖v‖ := by linarith [hlip v]
    calc |linMult τ Q v * Amp v| = |linMult τ Q v| * |Amp v| := abs_mul _ _
      _ ≤ (Cco * ‖v‖ * gaussDdim τ v) * (|Amp 0| + L * ‖v‖) := by
          refine mul_le_mul ?_ hAmpv (abs_nonneg _) (by positivity)
          have hb := abs_linMult_le τ hτ Q v
          rw [hCcodef]; exact hb
      _ = D v := by rw [hDdef, hd1def, hd2def]; ring
  have hstep2 : ∫ v : Point n in A, |linMult τ Q v * Amp v| ≤ ∫ v : Point n in A, D v :=
    setIntegral_mono_on (hLAmp_int.abs.integrableOn) hD_int.integrableOn hAmeas (fun v _ => hpt v)
  refine hstep2.trans ?_
  have hDnn : ∀ v : Point n, 0 ≤ D v := by
    intro v
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    rw [hDdef]; positivity
  have hDsub : ∫ v : Point n in A, D v
      ≤ ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, D v :=
    setIntegral_subset_tail_le hAsub hD_int hDnn
  refine hDsub.trans ?_
  have hval : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, D v
      = d1 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 1 * gaussDdim τ v)
          + d2 * (∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 2 * gaussDdim τ v) := by
    rw [hDdef, integral_add
      (((normPow_gauss_integrable 1 (by norm_num) τ hτ).integrableOn).const_mul _)
      (((normPow_gauss_integrable 2 (by norm_num) τ hτ).integrableOn).const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hval]
  have ht1 : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 1 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1) :=
    normPow_gaussDdim_tail_le 1 (by norm_num) τ hτ R (3 / 2) (by norm_num)
      (by simpa using oneD_absMoment1 (2 * τ) (by positivity))
  have ht2 : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ 2 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2) :=
    normPow_gaussDdim_tail_le 2 (by norm_num) τ hτ R 2 (by norm_num)
      (oneD_absMoment2 (2 * τ) (by positivity))
  have hfinal := add_le_add (mul_le_mul_of_nonneg_left ht1 hd1nn) (mul_le_mul_of_nonneg_left ht2 hd2nn)
  refine hfinal.trans_eq ?_
  rw [hd1def, hd2def, hCcodef]
  ring

/-- **★★ `hsMixed_amp_subset_tail_le`** — the COMBINED subset-tail bound, generalizing
    `hsMixed_amp_tail_le` (J4-1021) to an arbitrary measurable subset `A` of the literal tail set. -/
theorem hsMixed_amp_subset_tail_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) (PI PJ Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖)
    {A : Set (Point n)} (hAmeas : MeasurableSet A)
    (hAsub : A ⊆ {v : Point n | R ^ 2 ≤ rncRadialSq v}) :
    |∫ v : Point n in A, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)|
      ≤ |∫ v : Point n in A, heatHessMult τ PI PJ v * Amp v|
          + |∫ v : Point n in A, linMult τ Q v * Amp v| := by
  have hpt1 : ∀ v : Point n, gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
      = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by
    intro v
    have hid : (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)))
        * gaussDdim τ v
      = heatHessMult τ PI PJ v - linMult τ Q v := by
      simp only [heatHessMult, linMult]; ring
    calc gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
        = ((((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ))) * gaussDdim τ v) * Amp v := by
          ring
      _ = (heatHessMult τ PI PJ v - linMult τ Q v) * Amp v := by rw [hid]
      _ = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by ring
  have hHH_int : Integrable (fun v : Point n => heatHessMult τ PI PJ v * Amp v) volume :=
    heatHessMult_mul_lipschitzAmp_integrable τ hτ PI PJ Amp hAmp L hlip
  have hL_int : Integrable (fun v : Point n => linMult τ Q v * Amp v) volume :=
    linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip
  have hcong : ∫ v : Point n in A, gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
      = (∫ v : Point n in A, heatHessMult τ PI PJ v * Amp v) - ∫ v : Point n in A, linMult τ Q v * Amp v := by
    rw [setIntegral_congr_fun hAmeas (fun v _ => hpt1 v)]
    exact integral_sub hHH_int.integrableOn hL_int.integrableOn
  rw [hcong, sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]

/-! ###############################################################################
    ### PART 2 — the assembly capstone: a bound on `nb`'s actual w-space domain `W''S'`.
    ############################################################################### -/

/-- **★★★★★ `hsMixed_gaussDdim_mul_amp_domain_restricted_bound` — THE J4-1023 CAPSTONE.**  For the
    base-slot CoV map `W p := uniformInverseChart g gi hC hK p q₀` at `q₀ ∈ interior K`, `τ > 0`, chart-
    Jacobian jet fields `PI PJ Q`, and `Amp` Lipschitz-at-`0` (modulus `L ≥ 0`), the `hsMixed`-weighted
    Gaussian integral RESTRICTED TO `nb`'s ACTUAL post-CoV domain `W''S'` (`BaseSlotM1M4ImageOpen`'s
    open image, J4-1022 — matching `HCompNearCarryKPrimeBaseFieldCoV`'s BRICK 2 outer-integral domain)
    is bounded by the full-space G1 bound (J4-1019) PLUS a complement-tail correction (this file's
    generalized Part 1 bounds, composed with J4-1020's Brick B applied to `W''S'` itself).  ABSTRACT
    `Amp` only — does NOT verify the literal `Bfac(V w)/|det|` composition is Lipschitz-at-`0` (a
    SEPARATE, newly-identified, still-open gap — see file docstring).  NOT `a₁ = R/6`. -/
theorem hsMixed_gaussDdim_mul_amp_domain_restricted_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (τ : ℝ) (hτ : 0 < τ) (PI PJ Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    ∃ (S' : Set (Point n)) (ρ : ℝ), IsOpen S' ∧ q₀ ∈ S' ∧ 0 < ρ ∧
      |∫ v : Point n in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
          gaussDdim τ v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)|
        ≤ (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ
              + (n : ℝ) ^ 2 * L * ‖Q‖)
          + (Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                * (|Amp 0| * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                      + (1 / (2 * τ)))
                    + L * ((1 / (4 * τ ^ 2))
                          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                        + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)))
              + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
                  * (|Amp 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                      + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  obtain ⟨S', V, hS'open, hq0S', hinj, hV, hfd, hJpos, hWSopen⟩ :=
    uniformInverseChart_baseSlot_M1M4_image_open_generalK g gi hC hK hq₀
  set U : Set (Point n) := W '' S' with hUdef
  -- `0 ∈ U`, via `q₀ ∈ S'` and the diagonal-vanishing fact.
  have hq0K : q₀ ∈ K := interior_subset hq₀
  have hWq0 : W q₀ = 0 := uniformInverseChart_diag_zero_of_mem g gi hC hK hq0K
  have h0U : (0 : Point n) ∈ U := ⟨q₀, hq0S', hWq0⟩
  -- Brick B applied to `U` itself, centred at `0`.
  obtain ⟨ρ, hρpos, hρsub⟩ := S'_ball_complement_subset_rncRadialSq_tail hWSopen h0U
  have hρsub' : Uᶜ ⊆ {v : Point n | ρ ^ 2 ≤ rncRadialSq v} := by
    intro v hv
    have := hρsub hv
    simpa using this
  have hUmeas : MeasurableSet U := hWSopen.measurableSet
  have hUcmeas : MeasurableSet Uᶜ := hUmeas.compl
  refine ⟨S', ρ, hS'open, hq0S', hρpos, ?_⟩
  -- Full-space integrability of the raw `hsMixed` integrand, via the pointwise heatHessMult/linMult
  -- identity (same as `hsMixed_gaussDdim_mul_amp_eq_diff`'s internal step).
  have hpt1 : ∀ v : Point n, gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
      = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by
    intro v
    have hid : (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)))
        * gaussDdim τ v
      = heatHessMult τ PI PJ v - linMult τ Q v := by
      simp only [heatHessMult, linMult]; ring
    calc gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
        = ((((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ))) * gaussDdim τ v) * Amp v := by
          ring
      _ = (heatHessMult τ PI PJ v - linMult τ Q v) * Amp v := by rw [hid]
      _ = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by ring
  have hInt : Integrable (fun v : Point n => gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)) volume := by
    have h1 := heatHessMult_mul_lipschitzAmp_integrable τ hτ PI PJ Amp hAmp L hlip
    have h2 := linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip
    exact (h1.sub h2).congr (ae_of_all _ (fun v => (hpt1 v).symm))
  have hsplit := integral_add_compl hUmeas hInt
  have hGfull := hsMixed_gaussDdim_mul_amp_lipschitz_bound τ hτ PI PJ Q Amp hAmp L hL hlip
  have hGtail0 := hsMixed_amp_subset_tail_le τ hτ ρ PI PJ Q Amp hAmp L hL hlip hUcmeas hρsub'
  have hHHtail := heatHessMult_amp_subset_tail_le τ hτ ρ PI PJ Amp hAmp L hL hlip hUcmeas hρsub'
  have hLtail := linMult_amp_subset_tail_le τ hτ ρ Q Amp hAmp L hL hlip hUcmeas hρsub'
  have hGtail := hGtail0.trans (add_le_add hHHtail hLtail)
  have hUeq : ∫ v : Point n in U, gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
      = (∫ v : Point n, gaussDdim τ v
          * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v))
        - ∫ v : Point n in Uᶜ, gaussDdim τ v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v) := by
    linarith [hsplit]
  have habs : |∫ v : Point n in U, gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)|
      ≤ |∫ v : Point n, gaussDdim τ v
          * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)|
        + |∫ v : Point n in Uᶜ, gaussDdim τ v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)| := by
    rw [hUeq, sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
  refine habs.trans ?_
  exact add_le_add hGfull hGtail

end QIQTH.HCompNearCarryTerm1DomainRestrictedBound

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm1DomainRestrictedBound
#print axioms heatHessMult_amp_subset_tail_le
#print axioms linMult_amp_subset_tail_le
#print axioms hsMixed_amp_subset_tail_le
#print axioms hsMixed_gaussDdim_mul_amp_domain_restricted_bound
end AxiomChecks
