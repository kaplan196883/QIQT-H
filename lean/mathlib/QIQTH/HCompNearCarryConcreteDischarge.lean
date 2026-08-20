/-
  HCompNearCarryConcreteDischarge — Plan v9 (`tranquil-stargazing-fox.md`, Task B STEP 4c, part (ii)):
  the CONCRETE identification of the near-region chart map `W` in J4-861's abstract template
  (`HCompNearCarryAssembly.chartReplace_sliver_integral_le`) with the actual REVERSAL-derived
  near-isometry `T_{x₀} = terminalVelAt` (J4-858), with the template's near-isometry data `herr`/`hmin`
  DISCHARGED from J4-859's cubic-remainder bound (`terminalVelAt_cubic_remainder`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE — closing the gap between J4-861's ABSTRACT template and the CONCRETE reversal near-isometry.

  J4-860 (`HCompNearFarSplit.kPrime_sliver_near_far`) reduced `VanVleckGatedSpatialSymmetry.hcomp`'s
  per-direction √ε sliver integral to `nb + fb`.  J4-861 (`HCompNearCarryAssembly`) proved, ABSTRACTLY
  for ANY near-isometry `W` satisfying the radial-error `herr` and coercivity `hmin` on `ball 0 R`, the
  matched near rate
      `‖∫ s in (t−ε)..t, ∫_{ball 0 R} ‖z‖^k · |G_{t−s}(Wz) − G_{t−s}(z)|‖ ≤ Cshape · (√ε)^{k+3}`,
  i.e. `O(ε^{(k+3)/2})`, superpolynomially below `O(√ε)`.  What J4-861 explicitly LEFT OPEN was the
  concrete identification of `W` with the actual reversal-derived near-isometry.

  THIS FILE supplies exactly that concrete `W`.  The generic-base reversal identity (J4-858,
  `baseSlot_eventuallyEq_neg_terminalVel_at`) makes the near-region base↔eval chart swap a NEAR-ISOMETRY
  of the radial coordinate governed by `T_{x₀} := terminalVelAt g gi hC hK x₀`, whose deviation from the
  identity is genuinely CUBIC (J4-859: `T_{x₀}(v) = v + (1/2)B(v,v) + O(‖v‖³)`, `T_{x₀}(0)=0`,
  `DT_{x₀}(0)=Id`).  From that cubic-remainder structure we extract:
    • a QUADRATIC displacement bound `‖T_{x₀}(v) − v‖ ≤ C_W·‖v‖²` on a ball (from the Hessian operator
      norm `‖B‖` plus the cubic remainder), and thence
    • the template's `herr` (`|r²_{Tv} − r²_v| ≤ L'·‖v‖³`) and `hmin` (`(1/2)r²_v ≤ r²_{Tv}`),
      via elementary coordinatewise `∑`-expansions (the near-IDENTITY companions of
      `RNCNearIsometryPointwise.nearIsometry_lower_of_quadraticDisplacement`, which handled `V ≈ −id`).
  Feeding these into J4-861's template gives the matched near rate for the CONCRETE reversal near-isometry
  `T_{x₀}` — the payoff of the J4-858/859/861 branch.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It does NOT,
  by itself, fully discharge `hcomp`'s near carry `nb`.  It discharges the CONCRETE-`W`-IDENTIFICATION
  step: the reversal near-isometry `T_{x₀}` genuinely satisfies J4-861's template hypotheses, giving the
  matched near sliver rate on the chart-replacement CANCELLATION integrand `‖z‖^k·|G_τ(T_{x₀}z) − G_τ(z)|`.
  What remains for a full `nb` discharge (honestly NOT built here) is the connection of the concrete
  `∫_{ball x ρ} (kPrime … x z)(eⱼ)` component to this chart-replacement shape — namely the MIXED normal
  form of `∂ⱼ∂ᵢ H_G` (`ChartJetHessianMixed`), the base↔field change of variables, the evenness link
  `G_τ(U z x) = G_τ(T_x(U x z))`, and the amplitude/prefactor domination — which is the mixed-normal-form
  connection (the same field-Hessian object the `MixedDirectionsFieldHessianEnvelope` thread supplies the
  FAR magnitude envelope `BF` for).  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.TerminalVelAtCubicRemainder
import QIQTH.HCompNearCarryAssembly
import QIQTH.InverseChartDisplacement

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1
open QIQTH.GeodesicReversalRouteAtPoint QIQTH.TerminalVelAtCubicRemainder
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryConcreteDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the near-IDENTITY displacement primitives (`herr` and `hmin`).
    ###
    ### These mirror `RNCNearIsometryPointwise.nearIsometry_lower_of_quadraticDisplacement`
    ### (which handled a near-`(−id)` map `V z ≈ −z`, via `‖V z + z‖`), but for a near-IDENTITY
    ### map `W z ≈ z` (via `‖W z − z‖`), and additionally deliver the radial-error bound `herr`.
    ############################################################################### -/

/-- **`rncRadialSq_error_of_displacementId`.**  For a near-IDENTITY map `W` with quadratic displacement
    `‖W z − z‖ ≤ C_W·‖z‖²` at `z` and `‖z‖ ≤ r`, the radial coordinate is disturbed only CUBICALLY:
        `|rncRadialSq (W z) − rncRadialSq z| ≤ (n·C_W·(2 + C_W·r))·‖z‖³`.
    Route (coordinatewise, `b := W z − z`, `W z i = b i + z i`):
    `rncRadialSq (W z) − rncRadialSq z = ∑ (2·bᵢ·zᵢ + bᵢ²)`, whose abs is `≤ n·(2‖b‖‖z‖ + ‖b‖²)
      ≤ n·(2·C_W‖z‖³ + C_W²·r·‖z‖³)`.  The template's `herr`.  NOT `a₁ = R/6`. -/
theorem rncRadialSq_error_of_displacementId
    (W : Point n → Point n) (C_W : ℝ) (hCW : 0 ≤ C_W) (r : ℝ) (z : Point n)
    (hzr : ‖z‖ ≤ r) (hdisp : ‖W z - z‖ ≤ C_W * ‖z‖ ^ 2) :
    |rncRadialSq (W z) - rncRadialSq z| ≤ ((n : ℝ) * C_W * (2 + C_W * r)) * ‖z‖ ^ 3 := by
  set b : Point n := W z - z with hbdef
  have hWzi : ∀ i, W z i = b i + z i := by
    intro i; rw [hbdef, Pi.sub_apply]; ring
  have hb : ‖b‖ ≤ C_W * ‖z‖ ^ 2 := hdisp
  have hbnn : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hb_i : ∀ i, |b i| ≤ ‖b‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b i
  have hz_i : ∀ i, |z i| ≤ ‖z‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z i
  -- coordinatewise expansion.
  have hexp : rncRadialSq (W z) - rncRadialSq z = ∑ i, (2 * b i * z i + b i ^ 2) := by
    simp only [rncRadialSq]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hWzi i]; ring
  -- absolute-value bound by the constant-summand `2‖b‖‖z‖ + ‖b‖²`.
  have habs : |rncRadialSq (W z) - rncRadialSq z| ≤ (n : ℝ) * (2 * (‖b‖ * ‖z‖) + ‖b‖ ^ 2) := by
    rw [hexp]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |2 * b i * z i + b i ^ 2|
        ≤ ∑ _i : Fin n, (2 * (‖b‖ * ‖z‖) + ‖b‖ ^ 2) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hterm : |2 * b i * z i + b i ^ 2| ≤ 2 * (|b i| * |z i|) + (b i) ^ 2 := by
            have e1 : |2 * b i * z i + b i ^ 2| ≤ |2 * b i * z i| + |b i ^ 2| := abs_add_le _ _
            have e2 : |2 * b i * z i| = 2 * (|b i| * |z i|) := by
              rw [show (2 : ℝ) * b i * z i = 2 * (b i * z i) by ring, abs_mul, abs_mul,
                  abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
            have e3 : |b i ^ 2| = (b i) ^ 2 := abs_of_nonneg (sq_nonneg _)
            rw [e2, e3] at e1; exact e1
          have h1 : |b i| * |z i| ≤ ‖b‖ * ‖z‖ :=
            mul_le_mul (hb_i i) (hz_i i) (abs_nonneg _) hbnn
          have h2 : (b i) ^ 2 ≤ ‖b‖ ^ 2 := by
            have := hb_i i; nlinarith [abs_nonneg (b i), sq_abs (b i)]
          nlinarith [hterm, h1, h2]
      _ = (n : ℝ) * (2 * (‖b‖ * ‖z‖) + ‖b‖ ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- convert the `‖b‖`-bound into the cubic form.
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hbz : ‖b‖ * ‖z‖ ≤ C_W * ‖z‖ ^ 3 := by
    have := mul_le_mul_of_nonneg_right hb hznn
    nlinarith [this]
  have hbsq : ‖b‖ ^ 2 ≤ C_W ^ 2 * r * ‖z‖ ^ 3 := by
    have hb2 : ‖b‖ ^ 2 ≤ (C_W * ‖z‖ ^ 2) ^ 2 := by nlinarith [hb, hbnn, mul_nonneg hCW (sq_nonneg ‖z‖)]
    have hzr3 : ‖z‖ ^ 4 ≤ r * ‖z‖ ^ 3 := by nlinarith [hzr, pow_nonneg hznn 3, hznn]
    nlinarith [hb2, hzr3, sq_nonneg C_W]
  calc |rncRadialSq (W z) - rncRadialSq z|
      ≤ (n : ℝ) * (2 * (‖b‖ * ‖z‖) + ‖b‖ ^ 2) := habs
    _ ≤ (n : ℝ) * (2 * (C_W * ‖z‖ ^ 3) + C_W ^ 2 * r * ‖z‖ ^ 3) := by
        apply mul_le_mul_of_nonneg_left _ hnn; nlinarith [hbz, hbsq]
    _ = ((n : ℝ) * C_W * (2 + C_W * r)) * ‖z‖ ^ 3 := by ring

/-- **`nearIsometry_lower_of_displacementId`.**  Near-IDENTITY companion of
    `RNCNearIsometryPointwise.nearIsometry_lower_of_quadraticDisplacement`.  For `‖W z − z‖ ≤ C_W·‖z‖²`
    and `z` inside the coercivity radius `n·C_W·‖z‖ ≤ 1/4`, the ℓ²-squared coercivity
        `(1/2)·rncRadialSq z ≤ rncRadialSq (W z)`
    holds.  Route: `rncRadialSq (W z) = rncRadialSq z + ∑ (2bᵢzᵢ + bᵢ²) ≥ rncRadialSq z − 2n‖b‖‖z‖
      ≥ rncRadialSq z − 2n·C_W‖z‖³`, and `2n·C_W‖z‖³ ≤ (1/2)‖z‖² ≤ (1/2)rncRadialSq z` via
    `n·C_W‖z‖ ≤ 1/4` and `‖z‖² ≤ rncRadialSq z`.  The template's `hmin`.  NOT `a₁ = R/6`. -/
theorem nearIsometry_lower_of_displacementId
    (W : Point n → Point n) (C_W : ℝ) (_hCW : 0 ≤ C_W) (z : Point n)
    (hdisp : ‖W z - z‖ ≤ C_W * ‖z‖ ^ 2) (hrad : (n : ℝ) * C_W * ‖z‖ ≤ 1 / 4) :
    (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (W z) := by
  set b : Point n := W z - z with hbdef
  have hWzi : ∀ i, W z i = b i + z i := by
    intro i; rw [hbdef, Pi.sub_apply]; ring
  have hb : ‖b‖ ≤ C_W * ‖z‖ ^ 2 := hdisp
  have hbnn : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hb_i : ∀ i, |b i| ≤ ‖b‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b i
  have hz_i : ∀ i, |z i| ≤ ‖z‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z i
  -- lower expansion:  `rncRadialSq (W z) − rncRadialSq z = ∑ (2bᵢzᵢ + bᵢ²) ≥ ∑ 2bᵢzᵢ`.
  have hexp : rncRadialSq (W z) - rncRadialSq z = ∑ i, (2 * b i * z i + b i ^ 2) := by
    simp only [rncRadialSq]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hWzi i]; ring
  have hlow : rncRadialSq z - rncRadialSq (W z) ≤ 2 * ((n : ℝ) * (‖z‖ * ‖b‖)) := by
    have hneg : rncRadialSq z - rncRadialSq (W z) = ∑ i, (- (2 * b i * z i) - b i ^ 2) := by
      rw [show rncRadialSq z - rncRadialSq (W z) = -(rncRadialSq (W z) - rncRadialSq z) by ring,
          hexp, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hneg]
    calc ∑ i, (- (2 * b i * z i) - b i ^ 2)
        ≤ ∑ _i : Fin n, 2 * (‖z‖ * ‖b‖) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have h1 : - (2 * b i * z i) - b i ^ 2 ≤ 2 * (- (b i * z i)) := by nlinarith [sq_nonneg (b i)]
          have h2 : - (b i * z i) ≤ |z i| * |b i| := by
            have := neg_le_abs (b i * z i)
            rw [abs_mul] at this
            nlinarith [this]
          have h3 : |z i| * |b i| ≤ ‖z‖ * ‖b‖ :=
            mul_le_mul (hz_i i) (hb_i i) (abs_nonneg _) hznn
          linarith
      _ = 2 * ((n : ℝ) * (‖z‖ * ‖b‖)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  -- `n·‖z‖·‖b‖ ≤ n·C_W·‖z‖³`.
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hstep : (n : ℝ) * (‖z‖ * ‖b‖) ≤ (n : ℝ) * C_W * ‖z‖ ^ 3 := by
    have hbz : ‖z‖ * ‖b‖ ≤ ‖z‖ * (C_W * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left hb hznn
    nlinarith [mul_le_mul_of_nonneg_left hbz hnn]
  have hzsq : ‖z‖ ^ 2 ≤ rncRadialSq z := norm_sq_le_rncRadialSq z
  have hcube : (n : ℝ) * C_W * ‖z‖ ^ 3 ≤ (1 / 4) * ‖z‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hrad (sq_nonneg ‖z‖), hznn]
  nlinarith [hlow, hstep, hcube, hzsq]

/-! ###############################################################################
    ### §2 — the QUADRATIC displacement bound for the reversal near-isometry `T_{x₀}`.
    ############################################################################### -/

/-- **★ `terminalVelAt_displacementId_quadratic`.**  The reversal-derived terminal-velocity map
    `T_{x₀} = terminalVelAt g gi hC hK x₀` is a near-IDENTITY with QUADRATIC displacement on a ball:
        `∃ r > 0, ∃ C_W ≥ 0, ∀ v, ‖v‖ < r → ‖T_{x₀}(v) − v‖ ≤ C_W·‖v‖²`.
    Extracted from J4-859's cubic remainder `‖T_{x₀}(v) − v − (1/2)•B(v,v)‖ ≤ C·‖v‖³` plus the Hessian
    operator-norm bound `‖B(v,v)‖ ≤ ‖B‖·‖v‖²`: `‖T_{x₀}(v) − v‖ ≤ (1/2)‖B‖·‖v‖² + C·r·‖v‖²` on `‖v‖<r`,
    so `C_W := (1/2)‖B‖ + C·r`.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_displacementId_quadratic (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    ∃ r > (0 : ℝ), ∃ C_W ≥ (0 : ℝ), ∀ v : Point n, ‖v‖ < r →
      ‖terminalVelAt g gi hC hK x₀ v - v‖ ≤ C_W * ‖v‖ ^ 2 := by
  obtain ⟨r, C, B, hr, hC0, _hval, _hFid, _hsymm, hcubic⟩ :=
    terminalVelAt_cubic_remainder g gi hC hK hx₀K
  refine ⟨r, hr, (1 / 2 : ℝ) * ‖B‖ + C * r, by positivity, ?_⟩
  intro v hv
  have hquad : ‖(1 / 2 : ℝ) • (B v) v‖ ≤ (1 / 2 : ℝ) * ‖B‖ * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    have hBvv : ‖(B v) v‖ ≤ ‖B‖ * ‖v‖ * ‖v‖ :=
      le_trans ((B v).le_opNorm v) (mul_le_mul_of_nonneg_right (B.le_opNorm v) (norm_nonneg v))
    nlinarith [hBvv, norm_nonneg ((B v) v)]
  have hrem : ‖terminalVelAt g gi hC hK x₀ v - v - (1 / 2 : ℝ) • (B v) v‖ ≤ C * ‖v‖ ^ 3 :=
    hcubic v hv
  have hv3 : C * ‖v‖ ^ 3 ≤ C * r * ‖v‖ ^ 2 := by
    have : ‖v‖ ^ 3 ≤ r * ‖v‖ ^ 2 := by nlinarith [hv.le, sq_nonneg ‖v‖, norm_nonneg v]
    nlinarith [this, hC0]
  calc ‖terminalVelAt g gi hC hK x₀ v - v‖
      = ‖(terminalVelAt g gi hC hK x₀ v - v - (1 / 2 : ℝ) • (B v) v) + (1 / 2 : ℝ) • (B v) v‖ := by
        congr 1; abel
    _ ≤ ‖terminalVelAt g gi hC hK x₀ v - v - (1 / 2 : ℝ) • (B v) v‖ + ‖(1 / 2 : ℝ) • (B v) v‖ :=
        norm_add_le _ _
    _ ≤ C * ‖v‖ ^ 3 + (1 / 2 : ℝ) * ‖B‖ * ‖v‖ ^ 2 := by linarith [hrem, hquad]
    _ ≤ C * r * ‖v‖ ^ 2 + (1 / 2 : ℝ) * ‖B‖ * ‖v‖ ^ 2 := by linarith [hv3]
    _ = ((1 / 2 : ℝ) * ‖B‖ + C * r) * ‖v‖ ^ 2 := by ring

/-! ###############################################################################
    ### §3 — the reversal near-isometry supplies the template's `herr` + `hmin`.
    ############################################################################### -/

/-- **★★ `terminalVelAt_nearIsometry_data`.**  THE CONCRETE `W`-IDENTIFICATION.  On an explicit ball
    `ball 0 R`, the reversal-derived near-isometry `T_{x₀} = terminalVelAt g gi hC hK x₀` satisfies BOTH
    of J4-861's template hypotheses:
        `herr : |rncRadialSq (T_{x₀} z) − rncRadialSq z| ≤ L'·‖z‖³`   (radial-coordinate cubic error),
        `hmin : (1/2)·rncRadialSq z ≤ rncRadialSq (T_{x₀} z)`         (ℓ²-squared coercivity),
    for explicit `R > 0`, `L' ≥ 0`.  Combines §2's quadratic displacement with the §1 primitives on the
    coercivity ball `R = min r (1/(4(n·C_W+1)))`.  This is the object J4-861's `weighted_chart_replace_
    bound` / `chartReplace_sliver_integral_le` consume as their abstract `W`.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_nearIsometry_data (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    ∃ R > (0 : ℝ), ∃ L' ≥ (0 : ℝ),
      (∀ z ∈ Metric.ball (0 : Point n) R,
          |rncRadialSq (terminalVelAt g gi hC hK x₀ z) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) R,
          (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (terminalVelAt g gi hC hK x₀ z)) := by
  obtain ⟨r, hr, C_W, hCW, hdisp⟩ := terminalVelAt_displacementId_quadratic g gi hC hK hx₀K
  set R : ℝ := min r (1 / (4 * ((n : ℝ) * C_W + 1))) with hRdef
  have hRpos : 0 < R := lt_min hr (by positivity)
  refine ⟨R, hRpos, (n : ℝ) * C_W * (2 + C_W * r), by positivity, ?_, ?_⟩
  · -- `herr`.
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hzr : ‖z‖ < r := lt_of_lt_of_le hz (min_le_left _ _)
    exact rncRadialSq_error_of_displacementId (terminalVelAt g gi hC hK x₀) C_W hCW r z
      hzr.le (hdisp z hzr)
  · -- `hmin`.
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hzr : ‖z‖ < r := lt_of_lt_of_le hz (min_le_left _ _)
    have hzR2 : ‖z‖ < 1 / (4 * ((n : ℝ) * C_W + 1)) := lt_of_lt_of_le hz (min_le_right _ _)
    -- coercivity radius `n·C_W·‖z‖ ≤ 1/4`.
    have hnn : (0 : ℝ) ≤ (n : ℝ) * C_W := mul_nonneg (Nat.cast_nonneg n) hCW
    have hrad : (n : ℝ) * C_W * ‖z‖ ≤ 1 / 4 := by
      have hden : (0 : ℝ) < 4 * ((n : ℝ) * C_W + 1) := by positivity
      have hmul : (n : ℝ) * C_W * ‖z‖ ≤ (n : ℝ) * C_W * (1 / (4 * ((n : ℝ) * C_W + 1))) :=
        mul_le_mul_of_nonneg_left hzR2.le hnn
      have hbound : (n : ℝ) * C_W * (1 / (4 * ((n : ℝ) * C_W + 1))) ≤ 1 / 4 := by
        rw [mul_one_div, div_le_iff₀ hden]; nlinarith [hnn]
      linarith
    exact nearIsometry_lower_of_displacementId (terminalVelAt g gi hC hK x₀) C_W hCW z
      (hdisp z hzr) hrad

/-! ###############################################################################
    ### §4 — the CONCRETE near sliver rate for the reversal near-isometry `T_{x₀}`.
    ############################################################################### -/

/-- **★★★ `terminalVelAt_chartReplace_sliver_bound`.**  THE PAYOFF: the matched near sliver rate on the
    chart-replacement CANCELLATION integrand, for the CONCRETE reversal near-isometry
    `T_{x₀} = terminalVelAt g gi hC hK x₀`:
        `‖∫ s in (t−ε)..t, ∫_{ball 0 R} ‖z‖^k · |G_{t−s}(T_{x₀}z) − G_{t−s}(z)|‖ ≤ Cshape · (√ε)^{k+3}`,
    i.e. `O(ε^{(k+3)/2})` — for `k = 0`, `O(ε^{3/2})`, superpolynomially below the `O(√ε)` `hcomp` target.
    Obtained by feeding §3's `herr`/`hmin` (discharged from J4-858/859's reversal cubic remainder) into
    J4-861's abstract template `HCompNearCarryAssembly.chartReplace_sliver_integral_le`.  The two remaining
    inputs `hWint` (base Gaussian integrability) and `hmom` (1-D `(k+3)`-moment bound) are generic,
    heat-time-uniform Gaussian facts about the fixed model, carried here as satisfiable non-vacuous
    hypotheses.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_chartReplace_sliver_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ck3 : ℝ) (hck3 : 0 ≤ ck3) :
    ∃ R > (0 : ℝ), ∃ L' ≥ (0 : ℝ),
      (∀ (_hWint : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
          IntegrableOn (fun z : Point n =>
              ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|)
            (Metric.ball 0 R) volume)
        (_hmom : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
          ∫ y : ℝ, heatKernel1D (2 * τ) y * |y| ^ (k + 3)
            ≤ ck3 * (Real.sqrt (2 * τ)) ^ (k + 3)),
        ‖∫ s in (t - ε)..t,
            ∫ z in Metric.ball (0 : Point n) R,
              ‖z‖ ^ k * |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z|‖
          ≤ (L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3)))
              * (Real.sqrt ε) ^ (k + 3)) := by
  obtain ⟨R, hR, L', hL', herr, hmin⟩ := terminalVelAt_nearIsometry_data g gi hC hK hx₀K
  refine ⟨R, hR, L', hL', ?_⟩
  intro hWint hmom
  exact QIQTH.HCompNearCarryAssembly.chartReplace_sliver_integral_le k R ε hε
    (terminalVelAt g gi hC hK x₀) L' hL' herr hmin ck3 hck3 hWint hmom t

end QIQTH.HCompNearCarryConcreteDischarge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryConcreteDischarge
#print axioms rncRadialSq_error_of_displacementId
#print axioms nearIsometry_lower_of_displacementId
#print axioms terminalVelAt_displacementId_quadratic
#print axioms terminalVelAt_nearIsometry_data
#print axioms terminalVelAt_chartReplace_sliver_bound
end AxiomChecks
