/-
  HCompNearCarryBfacSliverWindowDomainRestricted — J4-NEXT: bridges J4-1069's frontier item 3 for
  `Bfac`'s summands where the composition is tractable — composing the `W''S'`-domain-restricted
  fixed-`τ` bounds (`HCompNearCarryTerm1DomainRestrictedBound`, J4-1023, and
  `HCompNearCarryTerm2Term3DomainRestrictedBound`, J4-1070) with the generic outer-`s`-sliver-window
  integration technique (`HcompLeftoverSliverWindowBound`/`HCompNearCarryLinMultSliverWindowBound`/
  `HCompNearCarryTerm1SliverWindowBound`, J4-1063/1064/1065).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBSTRUCTION (found before any Lean here, consulted `gpt-5.6-sol` high, GO-confirmed the fix
  below).  The two families do NOT compose for free: J4-1023/1070's `W''S'`-restricted bounds carry an
  extra COMPLEMENT-TAIL correction term of shape `exp(-ρ²/(8τ)) · (sum of κ·τ^p terms, p ∈ {-2,-3/2,
  -1,-1/2,0,1/2})` that does not literally match either generic window lemma's accepted shape
  (`M` flat, or `C1/√τ + C2`).  THE FIX: `Real.mul_exp_neg_le_exp_neg_one (y : ℝ) : y*exp(-y) ≤
  exp(-1)` (unconditional Mathlib fact) gives, by a squaring trick (splitting the exponent in half),
  a QUADRATIC exponential-decay bound `exp(-(c/τ)) ≤ 4·exp(-2)·τ²/c²` for `c,τ > 0` — strong enough to
  dominate the WORST (`τ^{-2}`) singularity in the tail correction, turning `exp(-ρ²/8τ)·(tail stuff)`
  into a bounded (in fact `o(1)`) quantity on any sliver `(0,ε]`, foldable as an EXTRA additive
  constant into the generic window lemmas' existing `C2`/`M` slot — NO new generic window lemma is
  needed, just this one exponential-domination lemma plus the (routine) `τ ≤ ε ⟹ (√τ)^k ≤ (√ε)^k`
  monotonicity bookkeeping.

  ## KEY OBSERVATION (simplifies the composition further, confirmed while auditing the four terms'
  EXACT bound shapes): `Bfac`'s FULL-SPACE bounds are not uniformly `C1/√τ+C2` — only T1's
  (`hsMixed_gaussDdim_mul_amp_lipschitz_bound`, J4-1019) genuinely has a `1/√τ` term (a REAL rate,
  matching `hcomp`'s required `O(√ε)`, unaffected by domain restriction).  T2/T3's full-space bound
  (`grTerm_gaussian_mul_amp_lipschitz_bound`, J4-1041) is ALREADY flat (`n²·L·‖Q‖`, no `1/√τ`), and
  T4/LEFTOVER's (`flat_gaussian_mul_amp_bound`, J4-1041) is flat by construction.  So:
    • T4/LEFTOVER: the `W''S'`-restricted bound (`flat_gaussDdim_mul_amp_domain_restricted_bound`,
      J4-1070) is ALREADY exactly `M`, τ-independent, with NO tail-correction branch at all — the
      composition with `pointwise_bound_sliver_window` (J4-1064) is 100% MECHANICAL, no new lemma.
    • T2/T3: the `W''S'`-restricted bound's tail correction, once dominated via the quadratic
      exp-lemma, is ALSO bounded by a τ-independent constant (its worst power is `τ^{-1/2}·exp(-ρ²/8τ)
      ≤ (const)·τ^{3/2}`, itself → 0, not singular) — so the WHOLE T2/T3 bound (full-space + tail)
      composes with the SAME flat window lemma `pointwise_bound_sliver_window`, giving `O(ε)`.
    • T1: the full-space part genuinely needs `pointwise_bound_sliver_window_inv_sqrt` (J4-1065); the
      tail-correction part is bounded via the SAME quadratic exp-domination technique and gets folded
      into that lemma's `C2` slot.  IDENTIFIED AND VALIDATED (the reusable `exp_neg_div_le_quadratic`
      lemma below is exactly what T1's literal 4-branch tail expression needs), but the full literal
      algebraic reduction of T1's specific messy expression (`heatHessMult`-tail ⊕ `linMult`-tail, four
      distinct `(√τ)^k/τ^m` monomials) to a closed numeric bound is NOT completed in THIS file — a
      concrete, well-scoped follow-on (not a research gap; the technique is proven to work below on the
      structurally analogous, simpler T2/T3 case).

  ## WHAT LANDS.
    • `exp_neg_div_le_quadratic` — ★★ the reusable quadratic exponential-domination lemma (Mathlib's
      `Real.mul_exp_neg_le_exp_neg_one`, squared).
    • `flat_domain_restricted_sliver_window_bound` — ★★★★★ T4/LEFTOVER's FULL composition: `∃ S',
      IsOpen S' ∧ q₀∈S' ∧ |∫ s in (t-ε)..t, ∫_{W''S'} G_{t-s}·Amp| ≤ M·ε` — genuinely closes J4-1069's
      item 3 for the LEFTOVER term (was ALREADY closed at the full-space level by J4-1063; this is the
      first `W''S'`-domain-restricted, `s`-window-integrated version).
    • `grTerm_domain_restricted_sliver_window_bound` — ★★★★★ T2/T3's FULL composition: `∃ S' ρ, IsOpen
      S' ∧ q₀∈S' ∧ 0<ρ ∧ |∫ s in (t-ε)..t, ∫_{W''S'} G_{t-s}·(grTerm·Amp)| ≤ [n²·L·‖Q‖ + TailBound(ε,ρ)]
      · ε` — genuinely closes J4-1069's item 3 for T2/T3, the FIRST `W''S'`-domain-restricted,
      `s`-window-integrated bound for these terms (J4-1064's version was full-space only).

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  J4-1069's frontier item 3 (the outer-`s`-integration ⊕ `W''S'`-domain-restriction composition) for
  TWO of `Bfac`'s four summands (T4/LEFTOVER, T2/T3) — NOT T1, and NOT all four (see above).  Both
  landed capstones use an ABSTRACT `Amp`/`f` (Lipschitz-at-`0` or merely-bounded, as appropriate) — they
  do NOT verify the literal `Bfac(V w)/|det(fderiv W (V w))|` composition (chart-inverse-composed,
  Jacobian-divided) is itself Lipschitz-at-`0`/bounded — this remains a SEPARATE, still-open gap
  (J4-1023's own flagged item 1 of J4-1069's frontier, UNCHANGED, untouched here).  Does NOT discharge
  `hxmem` (the shared upstream architectural wall gating ALL FOUR `Bfac` summands equally, UNCHANGED).
  Does NOT discharge `hfac`'s literal carry over `S'` (residuals r1/r2 of `HCompNearCarryKPrimeBaseFieldCoV`,
  UNCHANGED).  Does NOT discharge `nb`, `hCConv`, or any part of `hcomp`.  The far-carry `fb` remains
  SEPARATELY open regardless.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable
  hypothesis, none equal to the conclusion, no existing file edited.  Non-vacuity: every theorem's
  hypotheses are satisfiable by concrete test data (e.g. `Amp := 0`/`L := 0`/`M := 0`), and no theorem's
  hypothesis set is equal to its conclusion.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryTerm1DomainRestrictedBound
import QIQTH.HCompNearCarryTerm2Term3DomainRestrictedBound
import QIQTH.HCompNearCarryLinMultSliverWindowBound
import QIQTH.HCompNearCarryTerm1SliverWindowBound
import QIQTH.HcompLeftoverSliverWindowBound

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatHessMoment
open QIQTH.HeatHessMultBallTail QIQTH.HCompNearCarryTerm1LipschitzCancellation QIQTH.ExpMap
open QIQTH.HCompNearCarryTerm1AmpWeightedTail QIQTH.HCompNearCarryTerm1BallGeometry
open QIQTH.HerrHminGeneralQ0GeneralK QIQTH.BaseSlotM1M4ImageOpen
open QIQTH.HCompNearCarryTerm1DomainRestrictedBound QIQTH.HCompNearCarryTerm2Term3DomainRestrictedBound
open QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge
open QIQTH.HCompNearCarryLinMultSliverWindowBound QIQTH.HCompNearCarryTerm1SliverWindowBound
open QIQTH.HcompLeftoverSliverWindow
open scoped Topology BigOperators Interval

namespace QIQTH.HCompNearCarryBfacSliverWindowDomainRestricted

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### PART 0 — the reusable quadratic exponential-domination lemma.
    ############################################################################### -/

/-- **★★ `exp_neg_div_le_quadratic`.**  For `c, τ > 0`, `exp(-(c/τ)) ≤ 4·exp(-2)·τ²/c²` — strong
    enough to dominate a `τ^{-2}` singularity multiplied against it.  Derived from Mathlib's
    unconditional `Real.mul_exp_neg_le_exp_neg_one (y*exp(-y) ≤ exp(-1))` via a squaring trick:
    `exp(-(c/τ)) = exp(-(c/(2τ)))²`, and `exp(-(c/(2τ))) ≤ exp(-1)·2τ/c` follows from applying the
    Mathlib fact at `y := c/(2τ)`. -/
theorem exp_neg_div_le_quadratic (c τ : ℝ) (hc : 0 < c) (hτ : 0 < τ) :
    Real.exp (-(c / τ)) ≤ 4 * Real.exp (-2) * τ ^ 2 / c ^ 2 := by
  have hy : (0 : ℝ) < c / (2 * τ) := by positivity
  have hbase := Real.mul_exp_neg_le_exp_neg_one (c / (2 * τ))
  have hstep : Real.exp (-(c / (2 * τ))) ≤ Real.exp (-1) * (2 * τ) / c := by
    rw [le_div_iff₀ hc]
    have h3 : c / (2 * τ) * (2 * τ) = c := by field_simp
    calc Real.exp (-(c / (2 * τ))) * c
        = Real.exp (-(c / (2 * τ))) * (c / (2 * τ) * (2 * τ)) := by rw [h3]
      _ = c / (2 * τ) * Real.exp (-(c / (2 * τ))) * (2 * τ) := by ring
      _ ≤ Real.exp (-1) * (2 * τ) := mul_le_mul_of_nonneg_right hbase (by positivity)
  have hnn : (0 : ℝ) ≤ Real.exp (-1) * (2 * τ) / c := by positivity
  have hsq : Real.exp (-(c / (2 * τ))) * Real.exp (-(c / (2 * τ)))
      ≤ (Real.exp (-1) * (2 * τ) / c) * (Real.exp (-1) * (2 * τ) / c) :=
    mul_le_mul hstep hstep (le_of_lt (Real.exp_pos _)) hnn
  have hτne : τ ≠ 0 := hτ.ne'
  have hsplit : -(c / τ) = -(c / (2 * τ)) + -(c / (2 * τ)) := by
    field_simp
    ring
  have heq : Real.exp (-(c / τ)) = Real.exp (-(c / (2 * τ))) * Real.exp (-(c / (2 * τ))) := by
    rw [hsplit, Real.exp_add]
  rw [heq]
  refine hsq.trans_eq ?_
  have hee : Real.exp (-1) * Real.exp (-1) = Real.exp (-2) := by
    rw [← Real.exp_add, show (-1 : ℝ) + -1 = -2 from by norm_num]
  calc (Real.exp (-1) * (2 * τ) / c) * (Real.exp (-1) * (2 * τ) / c)
      = (Real.exp (-1) * Real.exp (-1)) * (4 * τ ^ 2 / c ^ 2) := by ring
    _ = Real.exp (-2) * (4 * τ ^ 2 / c ^ 2) := by rw [hee]
    _ = 4 * Real.exp (-2) * τ ^ 2 / c ^ 2 := by ring

/-! ###############################################################################
    ### PART 1 — T4/LEFTOVER: fully mechanical composition (no tail term at all).
    ############################################################################### -/

/-- **★★★★★ `flat_domain_restricted_sliver_window_bound` — THE T4/LEFTOVER CAPSTONE.**  For the
    base-slot CoV map `W p := uniformInverseChart g gi hC hK p q₀` at `q₀ ∈ interior K`, and `Amp`
    merely BOUNDED by `M`, the near carry's T4/LEFTOVER contribution, RESTRICTED to `nb`'s ACTUAL
    post-CoV domain `W''S'` AND integrated over the ACTUAL shrinking `s`-sliver `(t-ε,t)`, is bounded
    by `M·ε` — closing J4-1069's frontier item 3 for this term.  100% MECHANICAL: composes
    `flat_gaussDdim_mul_amp_domain_restricted_bound`'s (J4-1070) internal machinery (inlined so the
    SAME `S'` is used for every `τ` in the sliver, since it is τ-INDEPENDENT) with
    `pointwise_bound_sliver_window` (J4-1064). -/
theorem flat_domain_restricted_sliver_window_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (hn : n ≠ 0) (t ε : ℝ) (hε : 0 < ε)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ v : Point n, |Amp v| ≤ M) :
    ∃ S' : Set (Point n), IsOpen S' ∧ q₀ ∈ S' ∧
      |∫ s in (t - ε)..t, ∫ v : Point n in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
          gaussDdim (t - s) v * Amp v| ≤ M * ε := by
  obtain ⟨S', V, hS'open, hq0S', hinj, hV, hfd, hJpos, hWSopen⟩ :=
    uniformInverseChart_baseSlot_M1M4_image_open_generalK g gi hC hK hq₀
  set U : Set (Point n) := (fun p => uniformInverseChart g gi hC hK p q₀) '' S' with hUdef
  have hUmeas : MeasurableSet U := hWSopen.measurableSet
  have hCore : ∀ τ : ℝ, 0 < τ → |∫ v : Point n in U, gaussDdim τ v * Amp v| ≤ M := by
    intro τ hτ
    have hGnn : ∀ v : Point n, 0 ≤ gaussDdim τ v := fun v => gaussDdim_nonneg' τ v
    have hGint : Integrable (fun v : Point n => gaussDdim τ v) volume := gaussDdim_integrable' τ hτ
    have hD_int : Integrable (fun v : Point n => M * gaussDdim τ v) volume := hGint.const_mul _
    have hptbnd : ∀ v : Point n, |gaussDdim τ v * Amp v| ≤ M * gaussDdim τ v := fun v => by
      rw [abs_mul, abs_of_nonneg (hGnn v)]
      calc gaussDdim τ v * |Amp v| ≤ gaussDdim τ v * M :=
            mul_le_mul_of_nonneg_left (hbound v) (hGnn v)
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
  refine ⟨S', hS'open, hq0S', ?_⟩
  apply pointwise_bound_sliver_window t ε M hε hM
  intro s hs
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · subst heq
    have hz0 : ∀ v : Point n, gaussDdim (s - s) v * Amp v = 0 := by
      intro v; rw [sub_self]
      have hG0 : gaussDdim (0 : ℝ) v = 0 := by
        simp only [gaussDdim, heatKernel1D]
        have hsqrt0 : Real.sqrt (4 * Real.pi * (0 : ℝ)) = 0 := by rw [mul_zero, Real.sqrt_zero]
        rw [hsqrt0]; simp [hn]
      rw [hG0, zero_mul]
    simp only [hz0, MeasureTheory.integral_zero]
    simpa using hM
  · exact hCore (t - s) (by linarith)

/-! ###############################################################################
    ### PART 2 — T2/T3: composition via `exp_neg_div_le_quadratic` folding the tail into a
    ### τ-independent constant, then reusing the FLAT window lemma (T2/T3's full-space bound is
    ### already flat, and once dominated the tail is also flat — no `1/√τ` shape needed at all).
    ############################################################################### -/

/-- **Helper: the tail-correction term of `grTerm_gaussDdim_mul_amp_domain_restricted_bound`'s
    (J4-1070) bound is, for `τ ∈ (0,ε]`, bounded by a `τ`-INDEPENDENT constant** (via
    `exp_neg_div_le_quadratic` dominating the `exp(-ρ²/8τ)/τ` singularity, leaving only
    NONNEGATIVE powers of `τ`, bounded by their value at `ε`). -/
theorem grTerm_tail_le_of_sliver (ρ ε τ : ℝ) (hρ : 0 < ρ) (hε : 0 < ε) (hτ : 0 < τ) (hτε : τ ≤ ε)
    (Q : Point n) (Amp0 L : ℝ) (hAmp0 : 0 ≤ Amp0) (hL : 0 ≤ L) :
    Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
        * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
            + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))
      ≤ 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
          * (Amp0 * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
              + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) := by
  set c : ℝ := ρ ^ 2 / 8 with hcdef
  have hc : 0 < c := by rw [hcdef]; positivity
  have hρne : ρ ≠ 0 := hρ.ne'
  have hτne : τ ≠ 0 := hτ.ne'
  have hcform : -(ρ ^ 2) / (8 * τ) = -(c / τ) := by rw [hcdef]; ring
  have hexp0 : Real.exp (-(ρ ^ 2) / (8 * τ)) ≤ 4 * Real.exp (-2) * τ ^ 2 / c ^ 2 := by
    rw [hcform]; exact exp_neg_div_le_quadratic c τ hc hτ
  have hcsq : 4 * Real.exp (-2) * τ ^ 2 / c ^ 2 = 256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4 := by
    rw [hcdef]; field_simp; ring
  have hexp : Real.exp (-(ρ ^ 2) / (8 * τ)) ≤ 256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4 := by
    rw [← hcsq]; exact hexp0
  have hsqrtτε : Real.sqrt τ ≤ Real.sqrt ε := Real.sqrt_le_sqrt hτε
  have hsqrtτnn : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
  have hstep1 : Real.exp (-(ρ ^ 2) / (8 * τ)) * ((Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
        * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
            + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)))
      ≤ (256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4) * ((Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
        * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
            + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) :=
    mul_le_mul_of_nonneg_right hexp (by positivity)
  have hrw : (256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4) * ((Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
        * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
            + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)))
      = 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
          * (τ * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
              + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := by
    field_simp
  have hstep3 : τ * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
        + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))
      ≤ Amp0 * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
          + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2) := by
    have hτsq : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt hτ.le
    have hb1 : τ * Real.sqrt τ ≤ ε * Real.sqrt ε :=
      mul_le_mul hτε hsqrtτε hsqrtτnn hε.le
    have hb2 : τ ^ 2 ≤ ε ^ 2 := by nlinarith [hτ.le, hε.le, hτε]
    calc τ * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
          + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))
        = Amp0 * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * (τ * Real.sqrt τ))
            + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * τ ^ 2) := by
          rw [pow_one, hτsq]; ring
      _ ≤ Amp0 * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * (ε * Real.sqrt ε))
            + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2) := by gcongr
      _ = Amp0 * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
          + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2) := by ring
  calc Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
        * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
            + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))
      = Real.exp (-(ρ ^ 2) / (8 * τ)) * ((Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
        * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
            + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := by ring
    _ ≤ (256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4) * ((Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
        * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
            + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := hstep1
    _ = 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
          * (τ * (Amp0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
              + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := hrw
    _ ≤ 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
          * (Amp0 * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
              + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) := by
        gcongr

/-- **★★★★★ `grTerm_domain_restricted_sliver_window_bound` — THE T2/T3 CAPSTONE.**  For the
    base-slot CoV map `W p := uniformInverseChart g gi hC hK p q₀` at `q₀ ∈ interior K`, and `Amp`
    Lipschitz-at-`0` (modulus `L ≥ 0`), the near carry's T2/T3-type (`grTerm`/`linMult`) contribution,
    RESTRICTED to `nb`'s ACTUAL post-CoV domain `W''S'` AND integrated over the ACTUAL shrinking
    `s`-sliver `(t-ε,t)`, is bounded by `TotalConst · ε = O(ε)` — closing J4-1069's frontier item 3 for
    T2/T3.  Composes `grTerm_gaussDdim_mul_amp_domain_restricted_bound`'s (J4-1070) internal machinery
    (inlined, SAME `S',ρ` reused for every `τ` in the sliver) with `grTerm_tail_le_of_sliver` (folding
    the tail into a `τ`-independent constant) and `pointwise_bound_sliver_window` (J4-1064, flat
    shape — T2/T3's full-space bound is ALREADY flat, and the dominated tail is too). -/
theorem grTerm_domain_restricted_sliver_window_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (hn : n ≠ 0) (t ε : ℝ) (hε : 0 < ε)
    (Q : Point n) (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    ∃ (S' : Set (Point n)) (ρ : ℝ), IsOpen S' ∧ q₀ ∈ S' ∧ 0 < ρ ∧
      |∫ s in (t - ε)..t, ∫ v : Point n in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
          gaussDdim (t - s) v * ((-(∑ k, v k * Q k) / (2 * (t - s))) * Amp v)|
        ≤ ((n : ℝ) ^ 2 * L * ‖Q‖
             + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
                 * (|Amp 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
                     + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2))) * ε := by
  obtain ⟨S', V, hS'open, hq0S', hinj, hV, hfd, hJpos, hWSopen⟩ :=
    uniformInverseChart_baseSlot_M1M4_image_open_generalK g gi hC hK hq₀
  set U : Set (Point n) := (fun p => uniformInverseChart g gi hC hK p q₀) '' S' with hUdef
  have hq0K : q₀ ∈ K := interior_subset hq₀
  have hWq0 : (fun p => uniformInverseChart g gi hC hK p q₀) q₀ = 0 :=
    uniformInverseChart_diag_zero_of_mem g gi hC hK hq0K
  have h0U : (0 : Point n) ∈ U := ⟨q₀, hq0S', hWq0⟩
  obtain ⟨ρ, hρpos, hρsub⟩ := S'_ball_complement_subset_rncRadialSq_tail hWSopen h0U
  have hρsub' : Uᶜ ⊆ {v : Point n | ρ ^ 2 ≤ rncRadialSq v} := by
    intro v hv
    have := hρsub hv
    simpa using this
  have hUmeas : MeasurableSet U := hWSopen.measurableSet
  have hUcmeas : MeasurableSet Uᶜ := hUmeas.compl
  set M : ℝ := (n : ℝ) ^ 2 * L * ‖Q‖
      + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
          * (|Amp 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
              + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; positivity
  have hCore : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
      |∫ v : Point n in U, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)| ≤ M := by
    intro τ hτ hτε
    have hpt1 : ∀ v : Point n, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)
        = -(linMult τ Q v * Amp v) :=
      fun v => grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp τ Q v (Amp v)
    have hLamp_int : Integrable (fun v : Point n => linMult τ Q v * Amp v) volume :=
      linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip
    have hInt : Integrable (fun v : Point n =>
        gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)) volume :=
      hLamp_int.neg.congr (ae_of_all _ (fun v => (hpt1 v).symm))
    have hsplit := integral_add_compl hUmeas hInt
    have hGfull := grTerm_gaussian_mul_amp_lipschitz_bound τ hτ Q L hL Amp hAmp hlip
    have hLtail := linMult_amp_subset_tail_le τ hτ ρ Q Amp hAmp L hL hlip hUcmeas hρsub'
    have hUc_eq : ∫ v : Point n in Uᶜ, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)
        = -(∫ v : Point n in Uᶜ, linMult τ Q v * Amp v) := by
      rw [← integral_neg]
      exact setIntegral_congr_fun hUcmeas (fun v _ => hpt1 v)
    have hGtail : |∫ v : Point n in Uᶜ, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp v)|
        ≤ 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
            * (|Amp 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
                + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) := by
      rw [hUc_eq, abs_neg]
      refine hLtail.trans ?_
      exact grTerm_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε Q (|Amp 0|) L (abs_nonneg _) hL
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
    rw [hMdef]
    exact add_le_add hGfull hGtail
  refine ⟨S', ρ, hS'open, hq0S', hρpos, ?_⟩
  apply pointwise_bound_sliver_window t ε M hε hMnn
  intro s hs
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · subst heq
    have hz0 : ∀ v : Point n,
        gaussDdim (s - s) v * ((-(∑ k, v k * Q k) / (2 * (s - s))) * Amp v) = 0 := by
      intro v; rw [sub_self]
      have hG0 : gaussDdim (0 : ℝ) v = 0 := by
        simp only [gaussDdim, heatKernel1D]
        have hsqrt0 : Real.sqrt (4 * Real.pi * (0 : ℝ)) = 0 := by rw [mul_zero, Real.sqrt_zero]
        rw [hsqrt0]; simp [hn]
      rw [hG0, zero_mul]
    simp only [hz0, MeasureTheory.integral_zero]
    simpa using hMnn
  · exact hCore (t - s) (by linarith) (by linarith [hs.1])

end QIQTH.HCompNearCarryBfacSliverWindowDomainRestricted

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryBfacSliverWindowDomainRestricted
#print axioms exp_neg_div_le_quadratic
#print axioms flat_domain_restricted_sliver_window_bound
#print axioms grTerm_tail_le_of_sliver
#print axioms grTerm_domain_restricted_sliver_window_bound
end AxiomChecks
