/-
  HeatHessMultBallTailBound — J4-1018: the G2 gate — a domain-restriction / Gaussian-tail bound for
  `HeatHessianMomentCancellation`'s (J4-998) exact full-space cancellation `integral_heatHessMult_eq_zero`,
  toward `VanVleckGatedSpatialSymmetry.hcomp`'s NEAR carry `nb` (per Sol `gpt-5.6-sol`'s staged G3/G2/G1
  plan, cp902/cp903; this file attacks G2 — "boundary-term control on the actual bounded integration
  domain").

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PROBLEM.  `integral_heatHessMult_eq_zero` is EXACT only over the FULL space `ℝⁿ`.  `nb`'s
  actual post-CoV domain (`HCompNearCarryKPrimeBaseFieldCoV.lean`, J4-1010) is an OPAQUE IFT-produced
  open set `S'` — reconciling `S'` with the original `ball x ρ` (residuals r3/r4) is a SEPARATE, still
  open item, NOT attempted here.  THIS FILE instead builds a general-purpose, decoupled brick: a
  quantitative bound on the "tail" correction for a FIXED radial threshold `R` (the region OUTSIDE the
  Euclidean radial ball of radius `R`, using `RadialDistance`/`HeatResidualBound`'s own `rncRadialSq`,
  the actual radial coordinate driving the Gaussian's exponent — NOT the `Point n` Pi/sup norm used
  elsewhere in `abs_heatHessMult_le`, to avoid any norm-mismatch subtlety).  Once `S'` is shown to
  CONTAIN such a ball (a SEPARATE, still-open reconciliation step — the r3/r4 residuals), this bound
  controls exactly the boundary/tail correction `∫_{S'} heatHessMult = 0 − ∫_{S'ᶜ} heatHessMult` needs.

  Sol (`gpt-5.6-sol`, high, 2026-08-23, consulted with a sympy-verified rate claim BEFORE this file)
  confirmed: (1) IF `S'` is fixed independently of `τ` (the natural reading of the IFT construction — a
  SINGLE neighbourhood produced once, not re-chosen per `τ`), a fixed ball `⊆ S'` gives `S'ᶜ ⊆` the
  tail region this file bounds — exactly what G2 needs; (2) this decoupled brick is worth banking now
  (may bypass much of the `S'` opacity via a `∀ S ⊇ ball` corollary later); (3) flagged three technical
  corrections, ALL incorporated below: the `k = 0` case needs its own direct argument (NOT covered by
  `pow_norm_mul_gauss_integral`, which requires `k ≥ 1`); the domain uses `≤`/`<` (closed tail /
  complement), not strict `<`/`>` mismatches; any `n`-dependent power is a genuine NATURAL power of a
  REAL (`(√2)^n`, matching `gaussDdim_replace_bound`'s existing convention) — no `Real.rpow`, no
  integer-division `n/2`.

  ## SYMPY VERIFICATION (`docs/qg_roadmap/rnc_sympy/hcomp_g2_ball_tail_bound_check.py`, BEFORE this
  file): (a) the elementary exponent-split inequality `exp(−r²/4τ) ≤ exp(−R²/8τ)·exp(−r²/8τ)` for
  `r² ≥ R²` holds EXACTLY (`log(rhs) − log(lhs) = (r² − R²)/(8τ) ≥ 0`); (b) `exp(−R²/8τ)` beats EVERY
  polynomial power of `τ` as `τ → 0⁺` for FIXED `R > 0` (tested `τ^a`, `a ∈ {−5,−2,−1/2,0,1/2,3}`, all
  limits `= 0`); (c) integrating the worst-case tail bound (`τ^{−2+k/2}·exp(−R²/8τ)`, `k ∈ {0,1,2,3}`,
  matching `heatHessMult`'s own `τ^{−2}` singular prefactor via `abs_heatHessMult_le`) over the sliver
  `τ ∈ (0, ε)` gives a contribution that is `o(√ε)` as `ε → 0⁺` for EVERY `k` tested — i.e. GENUINELY
  NEGLIGIBLE against the `O(√ε)` target rate `integral_heatHessMult_mul_lipschitz` already delivers from
  the full-space integral.  So the tail correction this file bounds does NOT threaten the target rate,
  PROVIDED the radial threshold is fixed (not shrinking with `τ`).

  ## WHAT LANDS.
    • `gaussDdim_tail_pointwise_le` — the pointwise `Gk`-based exponent-split bound: for `R² ≤
      rncRadialSq v` and `τ > 0`, `gaussDdim τ v ≤ exp(−R²/(8τ))·(√2)ⁿ·gaussDdim (2τ) v`.  Same route as
      the already-banked `gaussDdim_replace_bound` (S5b, `GaussianMomentEnvelope.lean`): unfold via `Gk`,
      split the exponent, recognise the rescaled-width Gaussian via `Gk_scaled`.
    • `gaussDdim_tail_mass_le` — the `k = 0` (mass) tail bound: `∫_{R² ≤ rncRadialSq v} gaussDdim τ v ≤
      exp(−R²/(8τ))·(√2)ⁿ` (extend the pointwise bound to the full space via `setIntegral_le_integral`,
      evaluate via `gaussDdim_integral_eq_one (2τ)`).
    • `normPow_gaussDdim_tail_le` — the general `k ≥ 1` weighted tail bound, reusing the ALREADY-BANKED
      `pow_norm_mul_gauss_integral` (S4b) on the extended full-space integral at `κ = 2`.
    • `heatHessMult_ball_tail_le` — ★ THE G2 PAYOFF: composing the `k = 0, 2` tail bounds with the
      already-banked pointwise majorant `abs_heatHessMult_le` and `integral_heatHessMult_eq_zero`
      (via `integral_add_compl`), an EXPONENTIALLY SMALL (in `R²/τ`) bound on
      `|∫_{rncRadialSq v < R²} heatHessMult τ p q v|` — the exact quantitative "boundary/tail control on
      the ball-restricted domain" G2 asked for.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  DECOUPLED analysis-infrastructure brick (same status as `HeatHessianMomentCancellation.lean` itself):
  a general Gaussian-tail estimate for a FIXED radial threshold `R`, NOT yet wired to the opaque `S'`
  (that identification — `ball ⊆ S'` for SOME concrete radius depending on the IFT data — is the
  SEPARATE r3/r4 reconciliation, still open, NOT attempted here).  It does NOT discharge `nb`, `hCConv`,
  or any part of `hcomp`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, none equal to the conclusion (this is genuine new quantitative estimate content, not a
  restatement of `integral_heatHessMult_eq_zero`), no existing file edited.  The leftover first-moment
  correction term `−⟨U,Q⟩/(2τ)` flagged by J4-1017 (G3) needs its OWN instance of this same `k = 1`
  tail machinery (`normPow_gaussDdim_tail_le` at `k = 1` directly supplies it) — NOT composed here,
  left for a follow-on dispatch alongside the r3/r4 reconciliation.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HeatHessianMomentCancellation
import QIQTH.GaussianMomentEnvelope

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatHessMoment
open scoped Topology BigOperators

namespace QIQTH.HeatHessMultBallTail

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### 1. The pointwise Gaussian exponent-split tail bound.
    ############################################################################### -/

/-- **★ `gaussDdim_tail_pointwise_le` — the elementary tail split.**  For `τ > 0` and `v` with
    `R² ≤ rncRadialSq v` (outside the Euclidean radial ball of radius `R`),
        `gaussDdim τ v ≤ exp(−R²/(8τ))·(√2)ⁿ·gaussDdim (2τ) v`.
    Sympy-verified FIRST (part (a)): the exponent split `−r²/(4τ) = −r²/(8τ) − r²/(8τ) ≤ −R²/(8τ) −
    r²/(8τ)` for `r² ≥ R²`.  Same route as `GaussianMomentEnvelope.gaussDdim_replace_bound` (S5b):
    unfold via `Gk`, split, recognise the rescaled-width Gaussian via `Gk_scaled`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_tail_pointwise_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) (v : Point n)
    (hv : R ^ 2 ≤ rncRadialSq v) :
    gaussDdim τ v ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) v := by
  rw [gaussDdim_eq_Gk τ v]
  set r2 : ℝ := rncRadialSq v with hr2def
  have hsplit : Gk n τ r2 = Gk n τ ((1 / 2 : ℝ) * r2) * Real.exp (-r2 / (8 * τ)) := by
    unfold Gk
    rw [show -r2 / (4 * τ) = -((1 / 2 : ℝ) * r2) / (4 * τ) + (-r2 / (8 * τ)) from by ring,
        Real.exp_add]
    ring
  have hexple : Real.exp (-r2 / (8 * τ)) ≤ Real.exp (-(R ^ 2) / (8 * τ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff_of_pos_right (show (0 : ℝ) < 8 * τ by positivity)]
    linarith [hv]
  have hs2 : (Real.sqrt (1 / 2 : ℝ))⁻¹ = Real.sqrt 2 := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ from by norm_num, Real.sqrt_inv, inv_inv]
  have hkey : Gk n τ ((1 / 2 : ℝ) * r2) = (Real.sqrt 2) ^ n * gaussDdim (2 * τ) v := by
    rw [hr2def, Gk_scaled (1 / 2) τ (by norm_num) hτ v, hs2,
        show τ / (1 / 2 : ℝ) = 2 * τ from by ring]
  have hGknn : 0 ≤ Gk n τ ((1 / 2 : ℝ) * r2) := Gk_nonneg τ _
  calc Gk n τ r2 = Gk n τ ((1 / 2 : ℝ) * r2) * Real.exp (-r2 / (8 * τ)) := hsplit
    _ ≤ Gk n τ ((1 / 2 : ℝ) * r2) * Real.exp (-(R ^ 2) / (8 * τ)) :=
        mul_le_mul_of_nonneg_left hexple hGknn
    _ = Real.exp (-(R ^ 2) / (8 * τ)) * ((Real.sqrt 2) ^ n * gaussDdim (2 * τ) v) := by
        rw [hkey]; ring
    _ = Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) v := by ring

/-- The Euclidean-radial tail set `{v | R² ≤ rncRadialSq v}` is measurable (closed, preimage of `Ici`
    under the continuous `rncRadialSq`). -/
theorem tailSet_measurableSet (R : ℝ) :
    MeasurableSet {v : Point n | R ^ 2 ≤ rncRadialSq v} :=
  (isClosed_Ici.preimage rncRadialSq_contDiff.continuous).measurableSet

/-! ###############################################################################
    ### 2. The mass (`k = 0`) tail bound.
    ############################################################################### -/

/-- **`gaussDdim_tail_mass_le` — the `k = 0` mass tail.**  `∫_{R² ≤ rncRadialSq v} gaussDdim τ v ≤
    exp(−R²/(8τ))·(√2)ⁿ`.  Extend the pointwise bound to the full space (nonneg integrand,
    `setIntegral_le_integral`) and evaluate via `gaussDdim_integral_eq_one (2τ)`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_tail_mass_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) :
    ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n := by
  set C : ℝ := Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have h2τ : (0 : ℝ) < 2 * τ := by positivity
  have hRHS_int_full : Integrable (fun v : Point n => C * gaussDdim (2 * τ) v) volume :=
    (gaussDdim_integrable (2 * τ) h2τ).const_mul _
  have hRHS_nn : 0 ≤ᵐ[volume] (fun v : Point n => C * gaussDdim (2 * τ) v) :=
    Filter.Eventually.of_forall (fun v => mul_nonneg hCnn (gaussDdim_nonneg _ _))
  have hSmeas : MeasurableSet {v : Point n | R ^ 2 ≤ rncRadialSq v} := tailSet_measurableSet R
  have hset_le : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, gaussDdim τ v
      ≤ ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, C * gaussDdim (2 * τ) v :=
    setIntegral_mono_on (gaussDdim_integrable τ hτ).integrableOn hRHS_int_full.integrableOn hSmeas
      (fun v hv => gaussDdim_tail_pointwise_le τ hτ R v hv)
  have hext : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, C * gaussDdim (2 * τ) v
      ≤ ∫ v : Point n, C * gaussDdim (2 * τ) v :=
    setIntegral_le_integral hRHS_int_full hRHS_nn
  have hfull : ∫ v : Point n, C * gaussDdim (2 * τ) v = C := by
    rw [integral_const_mul, gaussDdim_integral_eq_one (2 * τ) h2τ, mul_one]
  calc ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, gaussDdim τ v
      ≤ ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, C * gaussDdim (2 * τ) v := hset_le
    _ ≤ ∫ v : Point n, C * gaussDdim (2 * τ) v := hext
    _ = C := hfull

/-! ###############################################################################
    ### 3. The general `k ≥ 1` weighted tail bound.
    ############################################################################### -/

/-- **`normPow_gaussDdim_tail_le` — the `k ≥ 1` weighted tail.**  Parametric in a supplied 1-D
    `k`-moment bound `ck` (matching `pow_norm_mul_gauss_integral`'s own `hmom` shape at `κ = 2`):
        `∫_{R² ≤ rncRadialSq v} ‖v‖ᵏ·gaussDdim τ v
            ≤ exp(−R²/(8τ))·(√2)ⁿ·n·cₖ·(√2)ᵏ·(√τ)ᵏ`.
    Same extend-to-full-space route as `gaussDdim_tail_mass_le`, now weighted by `‖v‖ᵏ` (nonneg), using
    `pow_norm_mul_gauss_integral` (S4b) at `κ = 2` for the full-space evaluation.  NOT `a₁ = R/6`. -/
theorem normPow_gaussDdim_tail_le (k : ℕ) (hk1 : 1 ≤ k) (τ : ℝ) (hτ : 0 < τ) (R : ℝ)
    (ck : ℝ) (hck : 0 ≤ ck)
    (hmom : ∫ y : ℝ, heatKernel1D (2 * τ) y * |y| ^ k ≤ ck * (Real.sqrt (2 * τ)) ^ k) :
    ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ k * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * ck * (Real.sqrt 2) ^ k * (Real.sqrt τ) ^ k) := by
  set C : ℝ := Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have h2τ : (0 : ℝ) < 2 * τ := by positivity
  have hLHS_int_full : Integrable (fun v : Point n => ‖v‖ ^ k * gaussDdim τ v) volume :=
    normPow_gauss_integrable k hk1 τ hτ
  have hRHS_int_full : Integrable (fun v : Point n => C * (‖v‖ ^ k * gaussDdim (2 * τ) v)) volume :=
    (normPow_gauss_integrable k hk1 (2 * τ) h2τ).const_mul _
  have hRHS_nn : 0 ≤ᵐ[volume] (fun v : Point n => C * (‖v‖ ^ k * gaussDdim (2 * τ) v)) :=
    Filter.Eventually.of_forall
      (fun v => mul_nonneg hCnn (mul_nonneg (pow_nonneg (norm_nonneg v) k) (gaussDdim_nonneg _ _)))
  have hSmeas : MeasurableSet {v : Point n | R ^ 2 ≤ rncRadialSq v} := tailSet_measurableSet R
  have hpt : ∀ v ∈ {v : Point n | R ^ 2 ≤ rncRadialSq v},
      ‖v‖ ^ k * gaussDdim τ v ≤ C * (‖v‖ ^ k * gaussDdim (2 * τ) v) := by
    intro v hv
    have hb := gaussDdim_tail_pointwise_le τ hτ R v hv
    calc ‖v‖ ^ k * gaussDdim τ v
        ≤ ‖v‖ ^ k * (C * gaussDdim (2 * τ) v) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg v) k)
      _ = C * (‖v‖ ^ k * gaussDdim (2 * τ) v) := by ring
  have hset_le : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ k * gaussDdim τ v
      ≤ ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, C * (‖v‖ ^ k * gaussDdim (2 * τ) v) :=
    setIntegral_mono_on hLHS_int_full.integrableOn hRHS_int_full.integrableOn hSmeas hpt
  have hext : ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, C * (‖v‖ ^ k * gaussDdim (2 * τ) v)
      ≤ ∫ v : Point n, C * (‖v‖ ^ k * gaussDdim (2 * τ) v) :=
    setIntegral_le_integral hRHS_int_full hRHS_nn
  have hmomfull := pow_norm_mul_gauss_integral (n := n) k hk1 2 (by norm_num) τ hτ ck hck hmom
  have hfull : ∫ v : Point n, C * (‖v‖ ^ k * gaussDdim (2 * τ) v)
      ≤ C * ((n : ℝ) * ck * (Real.sqrt 2) ^ k * (Real.sqrt τ) ^ k) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hmomfull hCnn
  calc ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, ‖v‖ ^ k * gaussDdim τ v
      ≤ ∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, C * (‖v‖ ^ k * gaussDdim (2 * τ) v) := hset_le
    _ ≤ ∫ v : Point n, C * (‖v‖ ^ k * gaussDdim (2 * τ) v) := hext
    _ ≤ C * ((n : ℝ) * ck * (Real.sqrt 2) ^ k * (Real.sqrt τ) ^ k) := hfull
    _ = Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * ck * (Real.sqrt 2) ^ k * (Real.sqrt τ) ^ k) := by rw [hCdef]

/-! ###############################################################################
    ### 4. ★ THE G2 PAYOFF — the ball-restricted `heatHessMult` tail bound.
    ############################################################################### -/

/-- **★★★ `heatHessMult_ball_tail_le` — THE G2 PAYOFF.**  For `τ > 0`, `R ≥ 0`, and directions
    `p q : Point n`, the ball-restricted `heatHessMult` integral (the "tail" `∫_{sᶜ} heatHessMult`
    of the full-space exact cancellation `integral_heatHessMult_eq_zero`, on the region
    `rncRadialSq v < R²`) is bounded EXPONENTIALLY SMALL in `R²/τ`:
        `|∫_{rncRadialSq v < R²} heatHessMult τ p q v|
            ≤ exp(−R²/(8τ))·n²‖p‖‖q‖·(√2)ⁿ·[(1/(4τ²))·2·n·(√2)²·τ + (1/(2τ))]`.
    Route: `integral_add_compl` splits the (zero) full-space integral into the ball region and its
    complement `{R² ≤ rncRadialSq v}`; the complement piece is bounded by `abs_heatHessMult_le`'s
    pointwise majorant, then by `gaussDdim_tail_mass_le` (`k = 0`) and `normPow_gaussDdim_tail_le`
    (`k = 2`, via `oneD_absMoment2`).  NOT `a₁ = R/6` — a DECOUPLED tail estimate for a FIXED radial
    threshold `R`, not yet wired to the opaque IFT domain `S'` (r3/r4, still open). -/
theorem heatHessMult_ball_tail_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) (p q : Point n) :
    |∫ v : Point n in {v | rncRadialSq v < R ^ 2}, heatHessMult τ p q v|
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖) * (Real.sqrt 2) ^ n
          * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
              + (1 / (2 * τ))) := by
  set S : Set (Point n) := {v | R ^ 2 ≤ rncRadialSq v} with hSdef
  have hSmeas : MeasurableSet S := tailSet_measurableSet R
  have hScompl : Sᶜ = {v : Point n | rncRadialSq v < R ^ 2} := by
    ext v; simp [hSdef, not_le]
  have hHH_int : Integrable (fun v : Point n => heatHessMult τ p q v) volume :=
    heatHessMult_integrable τ hτ p q
  have hsplit := integral_add_compl hSmeas hHH_int
  rw [hScompl] at hsplit
  have hfull0 : ∫ v : Point n, heatHessMult τ p q v = 0 := integral_heatHessMult_eq_zero τ hτ p q
  rw [hfull0] at hsplit
  have hball_eq_negS : ∫ v : Point n in {v | rncRadialSq v < R ^ 2}, heatHessMult τ p q v
      = -(∫ v : Point n in S, heatHessMult τ p q v) := by linarith [hsplit]
  rw [hball_eq_negS, abs_neg]
  -- bound `|∫_S heatHessMult|` by `∫_S |heatHessMult|`.
  have hHH_int_S : Integrable (fun v : Point n => heatHessMult τ p q v) (volume.restrict S) :=
    hHH_int.restrict
  have hstep1 : |∫ v : Point n in S, heatHessMult τ p q v|
      ≤ ∫ v : Point n in S, |heatHessMult τ p q v| := by
    have h := norm_integral_le_integral_norm (μ := (volume.restrict S))
      (fun v : Point n => heatHessMult τ p q v)
    simpa only [Real.norm_eq_abs] using h
  refine hstep1.trans ?_
  -- bound `∫_S |heatHessMult|` by the pointwise majorant.
  have hmaj_int : IntegrableOn (fun v : Point n =>
      ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖) * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v)) S volume := by
    have h1 : Integrable (fun v : Point n => ‖v‖ ^ 2 * gaussDdim τ v) volume :=
      normPow_gauss_integrable 2 (by norm_num) τ hτ
    have h2 : Integrable (fun v : Point n => gaussDdim τ v) volume := gaussDdim_integrable τ hτ
    have h3 : Integrable (fun v : Point n =>
        ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖) * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v)) volume := by
      have heq : (fun v : Point n =>
          ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖) * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v))
          = fun v => ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖ / (4 * τ ^ 2)) * (‖v‖ ^ 2 * gaussDdim τ v)
              + ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖ / (2 * τ)) * gaussDdim τ v := by
        funext v; ring
      rw [heq]; exact (h1.const_mul _).add (h2.const_mul _)
    exact h3.integrableOn
  have hstep2 : ∫ v : Point n in S, |heatHessMult τ p q v|
      ≤ ∫ v : Point n in S, ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖)
          * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v) :=
    setIntegral_mono_on (hHH_int.abs.integrableOn) hmaj_int hSmeas
      (fun v _ => abs_heatHessMult_le τ hτ p q v)
  refine hstep2.trans ?_
  have hCoefnn : 0 ≤ (n : ℝ) ^ 2 * ‖p‖ * ‖q‖ := by positivity
  have hconst_pull : ∫ v : Point n in S, ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖)
        * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v)
      = ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖)
          * (∫ v : Point n in S, (1 / (4 * τ ^ 2)) * (‖v‖ ^ 2 * gaussDdim τ v)
                + (1 / (2 * τ)) * gaussDdim τ v) := by
    rw [← integral_const_mul]
    congr 1; funext v; ring
  rw [hconst_pull]
  have hint_split : ∫ v : Point n in S, (1 / (4 * τ ^ 2)) * (‖v‖ ^ 2 * gaussDdim τ v)
        + (1 / (2 * τ)) * gaussDdim τ v
      = (1 / (4 * τ ^ 2)) * (∫ v : Point n in S, ‖v‖ ^ 2 * gaussDdim τ v)
          + (1 / (2 * τ)) * (∫ v : Point n in S, gaussDdim τ v) := by
    rw [integral_add ((normPow_gauss_integrable 2 (by norm_num) τ hτ).integrableOn.const_mul _)
        ((gaussDdim_integrable τ hτ).integrableOn.const_mul _),
        integral_const_mul, integral_const_mul]
  rw [hint_split]
  have hk2 : ∫ v : Point n in S, ‖v‖ ^ 2 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2) :=
    normPow_gaussDdim_tail_le 2 (by norm_num) τ hτ R 2 (by norm_num) (oneD_absMoment2 (2 * τ) (by positivity))
  have hk0 : ∫ v : Point n in S, gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n :=
    gaussDdim_tail_mass_le τ hτ R
  have hτ2pos : (0 : ℝ) < 4 * τ ^ 2 := by positivity
  have hτ1pos : (0 : ℝ) < 2 * τ := by positivity
  have hstep3 : (1 / (4 * τ ^ 2)) * (∫ v : Point n in S, ‖v‖ ^ 2 * gaussDdim τ v)
        + (1 / (2 * τ)) * (∫ v : Point n in S, gaussDdim τ v)
      ≤ (1 / (4 * τ ^ 2))
          * (Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
              * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))
        + (1 / (2 * τ)) * (Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n) :=
    add_le_add (mul_le_mul_of_nonneg_left hk2 (by positivity))
      (mul_le_mul_of_nonneg_left hk0 (by positivity))
  refine (mul_le_mul_of_nonneg_left hstep3 hCoefnn).trans_eq ?_
  ring

end QIQTH.HeatHessMultBallTail
