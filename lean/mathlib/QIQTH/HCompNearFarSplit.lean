/-
  HCompNearFarSplit — J4-860 (plan v9 `tranquil-stargazing-fox.md`, Task B STEP 4b):
  the NEAR/FAR SPLIT of `VanVleckGatedSpatialSymmetry.hcomp`'s `∫z` integral, with the FAR half
  DISCHARGED (exponentially suppressed) and the near/far reduction wired to the concrete `kPrime`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY A SPLIT IS NEEDED.

  `hcomp` bounds the per-direction √ε sliver integral `|∫ s ∫ z (kPrime … x z)(eⱼ)| ≤ bb j`.  The
  generic-base reversal identity (J4-858, `baseSlot_eventuallyEq_neg_terminalVel_at`) and the cubic
  remainder bound (J4-859, `terminalVelAt_cubic_remainder`) that convert the base↔eval swap into an
  O(√ε) CUBIC-CANCELLATION are valid only NEAR the field point `x` (the `𝓝 x` eventual filter, and the
  `‖v‖ < r` window of the cubic bound).  But `hcomp`'s `∫z` ranges over ALL of `Point n`.  Hence a
  NEAR/FAR split at a FIXED radius `ρ`:
    • NEAR (`z ∈ ball x ρ`): the reversal-cancellation √ε bound applies — carried here as `nb`
      (the STEP-4c reversal-cancellation deliverable; NOT built in this file).
    • FAR (`z ∉ ball x ρ`): NO cancellation, but the gated van-Vleck field-Hessian is dominated by a
      Gaussian-Hessian envelope whose off-`ball` tail moment is EXPONENTIALLY suppressed in `1/ε`.

  ⚠  CORRECTION OF THE SYMPY FAR MODEL.  `hcomp_reversal_feasibility.py` STEP 3 split at radius `√ε`
  and only HAND-WAVES far control (its `tail_lim` is a NONZERO erfc constant; the verdict invokes a
  vague "prefactor τ⁻² × ds-window ε × erfc smallness").  The CORRECT split uses a FIXED `ρ`: then the
  far tail moment is `≤ (√2)ⁿ·exp(−ρ²/8τ)·(2n+1)/(2τ)` (banked `tailMoment_expSuppressed_bound`), and
  the elementary bound `exp(−a/τ)/τ ≤ 1/(e·a)` (`expNegInv_div_le`, below) makes it UNIFORMLY over the
  sliver `τ ∈ (0,ε]` bounded by a constant `∝ exp(−ρ²/(16 ε))` — so the far sliver integral is
  `≤ ε · (that constant) = O(ε·exp(−ρ²/16ε))`, i.e. superpolynomially smaller than the O(√ε) target.

  ## WHAT LANDS (all NON-vacuous — the analytic bricks are UNCONDITIONAL theorems about explicit
  functions; the reduction is a pure triangle/split identity with satisfiable hypotheses).
    • `expNegInv_div_le` — the elementary `x·e^{−x} ≤ e^{−1}` bound recast as `exp(−a/τ)/τ ≤ 1/(e·a)`.
    • `tailMoment_sliver_uniform_bound` — the FAR tail moment is UNIFORMLY (over `τ ∈ (0,ε]`) bounded
      by `√2ⁿ·(2n+1)/(2 e (R²/16))·exp(−(R²/16)/ε)`, exp-suppressed in `1/ε`.
    • `tailMoment_sliver_integral_le` — the FAR sliver integral of any `h` dominated (in norm) by the
      tail moment is `≤ (that constant)·ε` — the DISCHARGED far half (via
      `intervalIntegral.norm_integral_le_of_norm_le_const_ae`, no integrability side-condition).
    • `kPrime_sliver_near_far` — ★ the NEAR/FAR reduction for `hcomp`'s per-direction integral,
      instantiated at the concrete `kPrime`: `|∫s ∫z kPrime(eⱼ)| ≤ nb + fb` from the near carry `nb`,
      the far carry `fb`, and the two sliver interval-integrabilities.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It builds
  the FAR half of `hcomp`'s near/far split (exponentially suppressed, fully discharged) and the
  near/far REDUCTION for the concrete `kPrime`.  The NEAR half (`nb`, the reversal-cancellation √ε
  bound from J4-858/859) and the concrete FAR domination `‖∫_{ballᶜ} kPrime(eⱼ)‖ ≤ tailMoment-envelope`
  (the `kPrime`→Gaussian-Hessian-envelope plumbing) remain the STEP-4c deliverables — NOT built here.
  No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, no hypothesis equal to
  the conclusion, no existing file edited.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.FderivBulkConcrete
import QIQTH.OffCollarTailMoment
import QIQTH.SliverTailMatched
import QIQTH.ConvApproximants

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.FderivBulkConcrete
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearFarSplit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the elementary exp bound `exp(−a/τ)/τ ≤ 1/(e·a)`.
    ############################################################################### -/

/-- **`expNegInv_div_le`.**  For `a, τ > 0`, `exp(−a/τ)/τ ≤ 1/(e·a)`.  Route: with `u := a/τ > 0`,
    `exp(−a/τ)/τ = (u·exp(−u))/a`, and `u·exp(−u) ≤ exp(−1)` from `u ≤ exp(u−1)` (`add_one_le_exp`).
    The `τ`-uniform envelope of the singular Gaussian-tail prefactor.  NOT `a₁ = R/6`. -/
theorem expNegInv_div_le (a τ : ℝ) (ha : 0 < a) (hτ : 0 < τ) :
    Real.exp (-a / τ) / τ ≤ 1 / (Real.exp 1 * a) := by
  set u : ℝ := a / τ with hu
  have hupos : 0 < u := div_pos ha hτ
  have h1 : u ≤ Real.exp (u - 1) := by
    have := Real.add_one_le_exp (u - 1); linarith
  have hkey : u * Real.exp (-u) ≤ Real.exp (-1) := by
    calc u * Real.exp (-u)
        ≤ Real.exp (u - 1) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf
  have harg : -a / τ = -u := by rw [hu]; ring
  have hrw : Real.exp (-a / τ) / τ = (u * Real.exp (-u)) / a := by
    rw [harg, hu]; field_simp
  rw [hrw]
  calc (u * Real.exp (-u)) / a
      ≤ Real.exp (-1) / a := by gcongr
    _ = 1 / (Real.exp 1 * a) := by rw [Real.exp_neg]; field_simp

/-! ###############################################################################
    ### §2 — the FAR tail moment is uniformly exp-suppressed over the sliver.
    ############################################################################### -/

/-- **★★ `tailMoment_sliver_uniform_bound`.**  For a FIXED off-collar radius `R > 0` and sliver width
    `ε > 0`, the bare off-collar tail moment `tailMoment i τ R` is UNIFORMLY (over `τ ∈ (0,ε]`) bounded
    by a constant that is EXPONENTIALLY small in `1/ε`:
        `|tailMoment i τ R| ≤ √2ⁿ·(2n+1)/(2 e (R²/16))·exp(−(R²/16)/ε)`.
    Route: the banked `tailMoment_expSuppressed_bound` gives `√2ⁿ·exp(−R²/8τ)·(2n+1)/(2τ)`; split
    `exp(−R²/8τ) = exp(−(R²/16)/τ)²`, bound `exp(−(R²/16)/τ)/τ ≤ 1/(e·(R²/16))` (`expNegInv_div_le`)
    and `exp(−(R²/16)/τ) ≤ exp(−(R²/16)/ε)` (monotone, `τ ≤ ε`).  NOT `a₁ = R/6`. -/
theorem tailMoment_sliver_uniform_bound (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (i : Fin n)
    {τ : ℝ} (hτ : 0 < τ) (hτε : τ ≤ ε) :
    |SliverTailMatched.tailMoment i τ R|
      ≤ Real.sqrt 2 ^ n * (2 * (n : ℝ) + 1) / (2 * Real.exp 1 * (R ^ 2 / 16))
          * Real.exp (-(R ^ 2 / 16) / ε) := by
  have h := QIQTH.OffCollarTailMoment.tailMoment_expSuppressed_bound τ R hτ hR.le i
  refine h.trans ?_
  set A : ℝ := Real.sqrt 2 ^ n with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  -- split the Gaussian exponent in half.
  have hsplit : Real.exp (-(R ^ 2) / (8 * τ))
      = Real.exp (-(R ^ 2 / 16) / τ) * Real.exp (-(R ^ 2 / 16) / τ) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hsplit]
  -- the two pointwise pieces.
  have hEbound : Real.exp (-(R ^ 2 / 16) / τ) / τ ≤ 1 / (Real.exp 1 * (R ^ 2 / 16)) :=
    expNegInv_div_le (R ^ 2 / 16) τ (by positivity) hτ
  have hEmono : Real.exp (-(R ^ 2 / 16) / τ) ≤ Real.exp (-(R ^ 2 / 16) / ε) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr
  have hpre : (0 : ℝ) ≤ A * (2 * (n : ℝ) + 1) / 2 := by positivity
  calc A * (Real.exp (-(R ^ 2 / 16) / τ) * Real.exp (-(R ^ 2 / 16) / τ))
          * ((2 * (n : ℝ) + 1) / (2 * τ))
      = (A * (2 * (n : ℝ) + 1) / 2) * Real.exp (-(R ^ 2 / 16) / τ)
          * (Real.exp (-(R ^ 2 / 16) / τ) / τ) := by ring
    _ ≤ (A * (2 * (n : ℝ) + 1) / 2) * Real.exp (-(R ^ 2 / 16) / ε)
          * (1 / (Real.exp 1 * (R ^ 2 / 16))) := by
        gcongr
    _ = A * (2 * (n : ℝ) + 1) / (2 * Real.exp 1 * (R ^ 2 / 16))
          * Real.exp (-(R ^ 2 / 16) / ε) := by ring

/-! ###############################################################################
    ### §3 — the DISCHARGED far sliver integral bound.
    ############################################################################### -/

/-- **★★★ `tailMoment_sliver_integral_le`.**  THE DISCHARGED FAR HALF.  For any `h : ℝ → ℝ` whose norm
    is dominated on the open sliver `(t−ε, t)` by the tail moment `|tailMoment i (t−s) R|`, the sliver
    integral is bounded by the exp-suppressed constant times the sliver width `ε`:
        `‖∫ s in (t−ε)..t, h s‖ ≤ (√2ⁿ·(2n+1)/(2 e (R²/16))·exp(−(R²/16)/ε)) · ε`.
    Route: `tailMoment_sliver_uniform_bound` bounds the integrand a.e. by a CONSTANT `M` on the sliver
    (the single point `s = t`, where `τ = 0`, is null), then
    `intervalIntegral.norm_integral_le_of_norm_le_const_ae` — NO integrability side-condition.  As
    `ε → 0` this is `O(ε·exp(−(R²/16)/ε))`, superpolynomially smaller than the O(√ε) target.
    NOT `a₁ = R/6`. -/
theorem tailMoment_sliver_integral_le (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (i : Fin n)
    (t : ℝ) (h : ℝ → ℝ)
    (hbd : ∀ s ∈ Set.Ioo (t - ε) t, ‖h s‖ ≤ |SliverTailMatched.tailMoment i (t - s) R|) :
    ‖∫ s in (t - ε)..t, h s‖
      ≤ (Real.sqrt 2 ^ n * (2 * (n : ℝ) + 1) / (2 * Real.exp 1 * (R ^ 2 / 16))
          * Real.exp (-(R ^ 2 / 16) / ε)) * ε := by
  set M : ℝ := Real.sqrt 2 ^ n * (2 * (n : ℝ) + 1) / (2 * Real.exp 1 * (R ^ 2 / 16))
      * Real.exp (-(R ^ 2 / 16) / ε) with hM
  have hle : t - ε ≤ t := by linarith
  have hae : ∀ᵐ s : ℝ ∂volume, s ∈ Set.uIoc (t - ε) t → ‖h s‖ ≤ M := by
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [hne] with s hsne hmem
    rw [Set.uIoc_of_le hle] at hmem
    obtain ⟨hs1, hs2⟩ := hmem
    have hs2' : s < t := lt_of_le_of_ne hs2 hsne
    calc ‖h s‖
        ≤ |SliverTailMatched.tailMoment i (t - s) R| := hbd s ⟨hs1, hs2'⟩
      _ ≤ M := by
          rw [hM]
          exact tailMoment_sliver_uniform_bound R ε hR hε i (by linarith) (by linarith)
  calc ‖∫ s in (t - ε)..t, h s‖
      ≤ M * |t - (t - ε)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const_ae hae
    _ = M * ε := by rw [show t - (t - ε) = ε by ring, abs_of_pos hε]

/-! ###############################################################################
    ### §4 — the NEAR/FAR reduction for `hcomp`'s per-direction integral.
    ############################################################################### -/

/-- **★ `kPrime_sliver_near_far`.**  THE NEAR/FAR REDUCTION for the concrete `kPrime`, at exactly the
    level `hcomp` (`VanVleckGatedSpatialSymmetry.hcomp`) consumes, for one direction `j`:
        `|∫ s ∫ z (kPrime … x z)(eⱼ)| ≤ nb + fb`,
    from the near carry `nb` (the reversal-cancellation √ε bound on `z ∈ ball x ρ` — STEP 4c), the far
    carry `fb` (discharged, up to the `kPrime`→envelope domination, by §3), and the two sliver
    interval-integrabilities of the near / far inner integrals.  Route: the a.e. `z`-integrability
    `hzI` gives the pointwise near/far split `∫z = ∫_{ball} + ∫_{ballᶜ}` (`integral_add_compl`); the
    sliver `∫s` distributes over the sum (`intervalIntegral.integral_add`); the triangle inequality
    (`abs_add`) closes it.  Setting `nb + fb ≤ bb j` supplies the `hcomp` component.  NOT `a₁ = R/6`. -/
theorem kPrime_sliver_near_far
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (i : Fin n) (m : ℕ) (x : Point n) (j : Fin n) (ρ nb fb : ℝ)
    (hzI : ∀ s, Integrable
      (fun z => (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)) volume)
    (hnearII : IntervalIntegrable
      (fun s => ∫ z in Metric.ball x ρ, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
      volume (t - epsSeq m) t)
    (hfarII : IntervalIntegrable
      (fun s => ∫ z in (Metric.ball x ρ)ᶜ, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
      volume (t - epsSeq m) t)
    (hnear : |∫ s in (t - epsSeq m)..t,
        ∫ z in Metric.ball x ρ, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)| ≤ nb)
    (hfar : |∫ s in (t - epsSeq m)..t,
        ∫ z in (Metric.ball x ρ)ᶜ, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)| ≤ fb) :
    |∫ s in (t - epsSeq m)..t, ∫ z, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)|
      ≤ nb + fb := by
  have hsplit : ∀ s, (∫ z, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
      = (∫ z in Metric.ball x ρ, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
        + (∫ z in (Metric.ball x ρ)ᶜ, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)) := by
    intro s
    exact (integral_add_compl measurableSet_ball (hzI s)).symm
  have hcong : (∫ s in (t - epsSeq m)..t, ∫ z, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
      = ∫ s in (t - epsSeq m)..t,
          ((∫ z in Metric.ball x ρ, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
            + (∫ z in (Metric.ball x ρ)ᶜ, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))) :=
    intervalIntegral.integral_congr (fun s _ => hsplit s)
  rw [hcong, intervalIntegral.integral_add hnearII hfarII]
  exact (abs_add_le _ _).trans (add_le_add hnear hfar)

end QIQTH.HCompNearFarSplit

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HCompNearFarSplit.expNegInv_div_le
#print axioms QIQTH.HCompNearFarSplit.tailMoment_sliver_uniform_bound
#print axioms QIQTH.HCompNearFarSplit.tailMoment_sliver_integral_le
#print axioms QIQTH.HCompNearFarSplit.kPrime_sliver_near_far
