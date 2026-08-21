/-
  CensusTwoTermSuperset — the MEASURABLE-SUPERSET analogue of the flat two-term Gaussian census
  bound, resolving the "image is not a ball" glue obligation at the CoV ⟶ two-term junction of the
  `hCensusBound` (`hCross`) assembly (gpt-5.6-sol high flagged this precise gap in the J4-95x re-audit:
  "the two-term theorem only handles the inner ball; the outer-image tail must be proved").

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure REAL-ANALYSIS adapter brick.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## WHY THIS EXISTS (the "outer-image" gap, distinct from the ball-local N1 adapter J4-944).  The
  banked `two_term_census_bound_ballLocal` (J4-944) bounds the flat two-term census integral over a
  **ball** `ball 0 r`.  But after the common-witness change of variables (`commonWitness_cov`, J4-943),
  the census is integrated over the CoV **IMAGE** `Wbv '' (ball 0 δ)`, which is **NOT** a ball.  The
  image sandwich (`commonWitness_image_sandwich`, J4-945) confines it inside `ball 0 σ'` and keeps an
  inner ball `ball 0 r ⊆ image`, but the two-term ball-local core cannot be cited on a non-ball domain.
  What the assembly actually needs is a two-term bound over an **arbitrary measurable superset**
  `Ω ⊇ ball 0 r` — the exact shape the CoV image occupies (`ball 0 r ⊆ image ⊆ ball 0 σ'`, `image`
  measurable).

  ## THE FIX (superset trace-cancellation + Gaussian outer-tail collapse).  The polynomial ("Hessian
  trace") term already has a banked **superset** form with the outer tail baked in:
  `gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz` (J4-922-lineage) bounds
    `|∫_{Ω} (∑ᵢ(zᵢ²/4τ²−1/2τ))·gaussDdim τ z·q₁ z|`
       `≤ L·n²(16√2+1)/√τ  +  3n·M₁·(√2)ⁿ·e^{−r²/8τ}·(2n+1)/(2τ)`
  for ANY measurable `Ω ⊇ ball 0 r`, with `q₁` globally bounded + center-Lipschitz on `ball 0 r`.  The
  outer tail `e^{−r²/8τ}·(2n+1)/(2τ)` collapses to a `1/√τ`-rate constant via the banked super-Gaussian
  moment `pow_mul_exp_negSq_le` (k = 2, `y = 1/√τ`, `b = r²/8`):
    `e^{−r²/8τ}/τ = (1/√τ)²·e^{−(r²/8)(1/√τ)²} ≤ 1 + 2!/(r²/8)² = 1 + 128/r⁴`  (a CONSTANT).
  The linear ("mass") term is bounded by pure Gaussian mass: `|∫_Ω gaussDdim τ z·q₂ z| ≤ M₂·∫gaussDdim
  = M₂` (`gaussDdim_integral_eq_one`).  Both constants ride `1 ≤ √T/√τ` (for `0<τ≤T`) into the `Cpair/√τ`
  shape.

  ## WHAT LANDS.
    • `two_term_census_bound_superset` — ★★ the MEASURABLE-SUPERSET flat two-term Gaussian census bound:
        for `0<τ≤T`, `r>0`, measurable `Ω ⊇ ball 0 r`, and weights `q₁,q₂` GLOBALLY bounded (`|q₁|≤M₁`,
        `|q₂|≤M₂`) with `q₁` center-Lipschitz (`L`) on `ball 0 r`,
          `|∫_{Ω}(∑ᵢ(zᵢ²/4τ²−1/2τ))·gaussDdim τ z·q₁ z  +  ∫_{Ω} gaussDdim τ z·q₂ z|
             ≤ (L·n²(16√2+1) + (3n·M₁·√2ⁿ·((2n+1)/2·(1+128/r⁴)) + M₂)·√T)/√τ` .
        Same `Cpair/√τ` shape as the ball-local core (J4-944) but over the non-ball CoV image.
    • `two_term_census_bound_superset_hyp_satisfiable` — non-vacuity with TEETH exercising a GENUINELY
        non-ball measurable superset (`Ω := ball 0 1 ∪ {isolated far point}`) and globally-bounded weights.

  ## HONEST STATUS (blunt; gpt-5.6-sol high adversarially audited the surrounding closure question).
  This removes ONLY the "image is not a ball" glue obligation for the two-term integral SHAPE, by giving
  the measurable-superset bound the CoV image occupies.  It does NOT close `hCensusBound`/`hCross`, and it
  does NOT discharge the C1 carry `hballrate`.  Per Sol's audit, the FULL modulo-G2 `hballrate` closure
  ALSO needs: (1) a restricted change of variables over `ball 0 δ` (`commonWitness_cov` is hardcoded at
  `D.ρ`); (2) measurability of the CoV image set `Ω := Wbv '' (ball 0 δ)`; (3) the indicator-drop on the
  inner ball (banked `censusTauDeriv_eq_onGate_on_jointGate_ball`, MODULO the G2 carry
  `ball ⊆ {z | 0 ∈ S z}`); (4) uniform transported constants in `s, τ`.  And per the same audit the
  UNCONDITIONAL (arbitrary-`S`) `hballrate` is a genuine **NO-GO** — the gate indicator rides into `q₁`
  destroying center-Lipschitz, so a G2-type hypothesis is genuinely required (unless the transported
  centre value vanishes).  NONE of that is in this file.  `hDuhamel`/`hDConv` remain carried; `hCConv`
  unaffected.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GaussTauTraceCancellationInnerBall
import QIQTH.CensusOnGateFixedGaussEnvelope

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound QIQTH.CensusOnGateFixedGaussEnvelope
open scoped BigOperators

namespace QIQTH.CensusTwoTermSuperset

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the MEASURABLE-SUPERSET two-term Gaussian census bound.
    ############################################################################### -/

/-- **★★ `two_term_census_bound_superset` — the MEASURABLE-SUPERSET flat two-term Gaussian census
    bound.**  For `0 < τ ≤ T`, `r > 0`, a measurable superset `Ω ⊇ ball 0 r`, and weights `q₁, q₂` that
    are measurable and GLOBALLY bounded (`|q₁|≤M₁`, `|q₂|≤M₂`) with `q₁` CENTER-Lipschitz (`L`) on the
    ball `ball 0 r`,
      `|∫_{Ω}(∑ᵢ(zᵢ²/4τ²−1/2τ))·gaussDdim τ z·q₁ z  +  ∫_{Ω} gaussDdim τ z·q₂ z|
         ≤ (L·n²(16√2+1) + (3n·M₁·√2ⁿ·((2n+1)/2·(1+128/r⁴)) + M₂)·√T)/√τ` .
    Proof: the polynomial term via the banked superset center-Lipschitz trace cancellation
    (`gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz`), whose outer Gaussian tail
    `e^{−r²/8τ}·(2n+1)/(2τ)` collapses to the constant `(2n+1)/2·(1+128/r⁴)` via `pow_mul_exp_negSq_le`;
    the mass term via `|∫_Ω gaussDdim·q₂| ≤ M₂·∫gaussDdim = M₂` (`gaussDdim_integral_eq_one`); both
    constants ride `1 ≤ √T/√τ`.  NOT `a₁ = R/6`. -/
theorem two_term_census_bound_superset
    (τ r T : ℝ) (hτ : 0 < τ) (hτT : τ ≤ T) (hr : 0 < r)
    (q₁ q₂ : Point n → ℝ)
    (L M₁ M₂ : ℝ) (hL : 0 ≤ L) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hq₁meas : AEStronglyMeasurable q₁ volume) (hq₂meas : AEStronglyMeasurable q₂ volume)
    (hq₁bnd : ∀ z, |q₁ z| ≤ M₁) (hq₂bnd : ∀ z, |q₂ z| ≤ M₂)
    (hcl : ∀ z ∈ Metric.ball (0 : Point n) r, |q₁ z - q₁ 0| ≤ L * ‖z‖)
    (Ω : Set (Point n)) (hΩ : MeasurableSet Ω) (hball : Metric.ball (0 : Point n) r ⊆ Ω) :
    |(∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z)
        + (∫ z in Ω, gaussDdim τ z * q₂ z)|
      ≤ (L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1))
          + (3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * ((2 * (n : ℝ) + 1) / 2 * (1 + 128 / r ^ 4))) + M₂)
              * Real.sqrt T) / Real.sqrt τ := by
  classical
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hsT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hrne : r ≠ 0 := ne_of_gt hr
  -- `1 ≤ √T/√τ` (for `0<τ≤T`).
  have h1leRatio : (1 : ℝ) ≤ Real.sqrt T / Real.sqrt τ := by
    rw [le_div_iff₀ hsτ, one_mul]
    exact Real.sqrt_le_sqrt hτT
  -- ═══ TERM A: the polynomial trace cancellation over the superset `Ω`. ═══
  have hA := gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz τ r hτ hr q₁ L hL
    hq₁meas M₁ hq₁bnd hcl Ω hΩ hball
  -- outer-tail collapse: `e^{−r²/8τ}/τ ≤ 1 + 128/r⁴`.
  have hy : (0 : ℝ) ≤ 1 / Real.sqrt τ := by positivity
  have hb : (0 : ℝ) < r ^ 2 / 8 := by positivity
  have hpow := pow_mul_exp_negSq_le hb 2 hy
  have hsqinv : (1 / Real.sqrt τ) ^ 2 = 1 / τ := by
    rw [div_pow, one_pow, Real.sq_sqrt hτ.le]
  have hexparg : -(r ^ 2 / 8 * (1 / Real.sqrt τ) ^ 2) = -(r ^ 2) / (8 * τ) := by
    rw [hsqinv]; ring
  rw [hexparg, hsqinv] at hpow
  -- `hpow : 1/τ * Real.exp (-(r^2)/(8*τ)) ≤ 1 + ↑(2!)/(r^2/8)^2`.
  have hfact : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have hrhs : (Nat.factorial 2 : ℝ) / (r ^ 2 / 8) ^ 2 = 128 / r ^ 4 := by
    rw [hfact]; field_simp; ring
  have htailC : Real.exp (-(r ^ 2) / (8 * τ)) / τ ≤ 1 + 128 / r ^ 4 := by
    have hconv : 1 / τ * Real.exp (-(r ^ 2) / (8 * τ)) = Real.exp (-(r ^ 2) / (8 * τ)) / τ := by
      ring
    rw [hconv, hrhs] at hpow
    exact hpow
  -- collapse the tail factor into the constant `(2n+1)/2·(1+128/r⁴)`.
  have htailfac :
      Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ))
        ≤ (2 * (n : ℝ) + 1) / 2 * (1 + 128 / r ^ 4) := by
    have hcoef : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) / 2 := by positivity
    have hstep : (2 * (n : ℝ) + 1) / 2 * (Real.exp (-(r ^ 2) / (8 * τ)) / τ)
        ≤ (2 * (n : ℝ) + 1) / 2 * (1 + 128 / r ^ 4) :=
      mul_le_mul_of_nonneg_left htailC hcoef
    calc Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ))
        = (2 * (n : ℝ) + 1) / 2 * (Real.exp (-(r ^ 2) / (8 * τ)) / τ) := by ring
      _ ≤ (2 * (n : ℝ) + 1) / 2 * (1 + 128 / r ^ 4) := hstep
  -- assemble term A: `|A| ≤ L·(…)/√τ + Ctail` where `Ctail` is a constant.
  set Ctail : ℝ := 3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * ((2 * (n : ℝ) + 1) / 2 * (1 + 128 / r ^ 4)))
    with hCtaildef
  have hCoefNN : (0 : ℝ) ≤ 3 * (n : ℝ) * M₁ * Real.sqrt 2 ^ n :=
    mul_nonneg (mul_nonneg (by positivity) hM₁) (by positivity)
  have hAtail :
      3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ)))
        ≤ Ctail := by
    rw [hCtaildef]
    have hstep := mul_le_mul_of_nonneg_left htailfac hCoefNN
    calc 3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ)))
        = (3 * (n : ℝ) * M₁ * Real.sqrt 2 ^ n)
            * (Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ))) := by ring
      _ ≤ (3 * (n : ℝ) * M₁ * Real.sqrt 2 ^ n)
            * ((2 * (n : ℝ) + 1) / 2 * (1 + 128 / r ^ 4)) := hstep
      _ = 3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * ((2 * (n : ℝ) + 1) / 2 * (1 + 128 / r ^ 4))) := by ring
  have hAfull :
      |∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z|
        ≤ L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ + Ctail := by
    refine le_trans hA ?_
    have := hAtail
    linarith
  -- ═══ TERM B: the Gaussian-mass bound `|∫_Ω gaussDdim·q₂| ≤ M₂`. ═══
  have hgm : AEStronglyMeasurable (fun z : Point n => gaussDdim τ z) volume :=
    (gaussDdim_integrable τ hτ).aestronglyMeasurable
  have hBmeas : AEStronglyMeasurable (fun z : Point n => gaussDdim τ z * q₂ z) volume :=
    hgm.mul hq₂meas
  have hdomInt : Integrable (fun z : Point n => gaussDdim τ z * M₂) volume :=
    (gaussDdim_integrable τ hτ).mul_const M₂
  have hBint : Integrable (fun z : Point n => gaussDdim τ z * q₂ z) volume := by
    refine hdomInt.mono' hBmeas (ae_of_all _ (fun z => ?_))
    have hg : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_left (hq₂bnd z) hg
  have hB : |∫ z in Ω, gaussDdim τ z * q₂ z| ≤ M₂ := by
    calc |∫ z in Ω, gaussDdim τ z * q₂ z|
        ≤ ∫ z in Ω, |gaussDdim τ z * q₂ z| := by
          have := norm_integral_le_integral_norm
            (μ := (volume : Measure (Point n)).restrict Ω) (fun z => gaussDdim τ z * q₂ z)
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∫ z in Ω, gaussDdim τ z * M₂ := by
          refine setIntegral_mono_on ?_ ?_ hΩ (fun z _ => ?_)
          · exact hBint.abs.integrableOn
          · exact hdomInt.integrableOn
          · have hg : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
            rw [abs_mul, abs_of_nonneg hg]
            exact mul_le_mul_of_nonneg_left (hq₂bnd z) hg
      _ ≤ ∫ z : Point n, gaussDdim τ z * M₂ := by
          refine setIntegral_le_integral hdomInt (ae_of_all _ (fun z => ?_))
          exact mul_nonneg (gaussDdim_nonneg τ z) hM₂
      _ = M₂ := by
          rw [integral_mul_const, gaussDdim_integral_eq_one τ hτ, one_mul]
  -- ═══ COMBINE: `|A + B| ≤ |A| + |B| ≤ CA/√τ + Ctail + M₂ ≤ Cpair/√τ`. ═══
  have hCtailNN : 0 ≤ Ctail := by
    rw [hCtaildef]
    exact mul_nonneg (mul_nonneg (by positivity) hM₁)
      (mul_nonneg (by positivity) (by positivity))
  -- constants ride `1 ≤ √T/√τ`.
  have hConstRide : Ctail + M₂ ≤ (Ctail + M₂) * (Real.sqrt T / Real.sqrt τ) := by
    have hnn : 0 ≤ Ctail + M₂ := by linarith
    calc Ctail + M₂ = (Ctail + M₂) * 1 := by ring
      _ ≤ (Ctail + M₂) * (Real.sqrt T / Real.sqrt τ) :=
          mul_le_mul_of_nonneg_left h1leRatio hnn
  have habs : |(∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z)
        + (∫ z in Ω, gaussDdim τ z * q₂ z)|
      ≤ (|∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z|)
          + |∫ z in Ω, gaussDdim τ z * q₂ z| := abs_add_le _ _
  -- final numeric assembly.
  have hfinal :
      L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ + Ctail + M₂
        ≤ (L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) + (Ctail + M₂) * Real.sqrt T) / Real.sqrt τ := by
    rw [add_div]
    have hRide : Ctail + M₂ ≤ (Ctail + M₂) * Real.sqrt T / Real.sqrt τ := by
      rw [mul_div_assoc]; exact hConstRide
    linarith
  calc |(∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z)
          + (∫ z in Ω, gaussDdim τ z * q₂ z)|
      ≤ (|∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z|)
          + |∫ z in Ω, gaussDdim τ z * q₂ z| := habs
    _ ≤ (L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ + Ctail) + M₂ := by
          linarith [hAfull, hB]
    _ = L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ + Ctail + M₂ := by ring
    _ ≤ (L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) + (Ctail + M₂) * Real.sqrt T) / Real.sqrt τ :=
          hfinal
    _ = (L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1))
          + (3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * ((2 * (n : ℝ) + 1) / 2 * (1 + 128 / r ^ 4))) + M₂)
              * Real.sqrt T) / Real.sqrt τ := by rw [hCtaildef]

/-! ###############################################################################
    ### §B — non-vacuity (with TEETH: a GENUINELY non-ball measurable superset `Ω`).
    ############################################################################### -/

/-- **Non-vacuity of `two_term_census_bound_superset` — TEETH exercising a NON-ball superset.**  The
    point of the superset adapter (vs the ball-local core J4-944) is admitting a measurable domain that
    is NOT a ball — exactly the CoV image `Wbv '' (ball 0 δ)`.  Witnessed by `Ω := ball 0 1 ∪ {p}` with
    an isolated far point `p` (the constant-`2` point, at sup-distance `≥ 1 > 0` from `0`, so
    `Ω ⊋ ball 0 1` and `Ω` is not a ball), measurable (union of an open ball and a singleton), containing
    `ball 0 r = ball 0 1`, with globally-bounded weights `q₁ = q₂ = 0` (trivially center-Lipschitz).  So
    the superset bound fires on a genuinely non-ball domain the ball-local core cannot address.  NOT
    `a₁ = R/6`. -/
theorem two_term_census_bound_superset_hyp_satisfiable (hn : 0 < n) :
    ∃ (τ r T : ℝ) (q₁ q₂ : Point n → ℝ) (L M₁ M₂ : ℝ) (Ω : Set (Point n)),
      0 < τ ∧ τ ≤ T ∧ 0 < r ∧ 0 ≤ L ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
        AEStronglyMeasurable q₁ (volume : Measure (Point n)) ∧
        AEStronglyMeasurable q₂ (volume : Measure (Point n)) ∧
        (∀ z, |q₁ z| ≤ M₁) ∧ (∀ z, |q₂ z| ≤ M₂) ∧
        (∀ z ∈ Metric.ball (0 : Point n) r, |q₁ z - q₁ 0| ≤ L * ‖z‖) ∧
        MeasurableSet Ω ∧ Metric.ball (0 : Point n) r ⊆ Ω ∧
        (∃ p : Point n, p ∈ Ω ∧ p ∉ Metric.ball (0 : Point n) 1) := by
  classical
  set p : Point n := (fun _ => (2 : ℝ)) with hpdef
  -- `p ∉ ball 0 1` (sup-distance `≥ 2 > 1`) but `p ∈ Ω`, so `Ω ⊋ ball 0 1` (genuinely non-ball).
  have hpnotin : p ∉ Metric.ball (0 : Point n) 1 := by
    rw [Metric.mem_ball, dist_zero_right, not_lt]
    have hcoord : ‖(2 : ℝ)‖ ≤ ‖p‖ := by rw [hpdef]; exact norm_le_pi_norm (fun _ => (2 : ℝ)) ⟨0, hn⟩
    have h2 : ‖(2 : ℝ)‖ = 2 := by rw [Real.norm_eq_abs]; norm_num
    rw [h2] at hcoord; linarith
  refine ⟨1, 1, 1, fun _ => 0, fun _ => 0, 0, 0, 0,
    Metric.ball (0 : Point n) 1 ∪ {p},
    one_pos, le_refl 1, one_pos, le_refl 0, le_refl 0, le_refl 0,
    aestronglyMeasurable_const, aestronglyMeasurable_const,
    (fun z => by simp), (fun z => by simp), (fun z _ => by simp),
    (measurableSet_ball.union (measurableSet_singleton p)),
    Set.subset_union_left,
    ⟨p, Set.mem_union_right _ (Set.mem_singleton p), hpnotin⟩⟩

end QIQTH.CensusTwoTermSuperset

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusTwoTermSuperset
#print axioms two_term_census_bound_superset
#print axioms two_term_census_bound_superset_hyp_satisfiable
end AxiomChecks
