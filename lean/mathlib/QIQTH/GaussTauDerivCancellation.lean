/-
  GaussTauDerivCancellation — the 1-D Gaussian `∂_τ`-multiplier MOMENT-CANCELLATION core, the first
  genuinely-new analytic brick of the `hCross` sub-campaign (J4-910 route, piece (2)).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE brick — a standalone 1-D Gaussian moment estimate, decoupled from `H`, from the
  Levi series `F`, from the census, and from the global `∀ h, k` range of `hCross`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS BRICK.  The remaining shared-census wall `hCross`
      `|K(u+h,b+k) − K(u+h,b) − K(u,b+k) + K(u,b)| ≤ L·|h|·|k|`,  `K x y = heatConvFrozen H F x y 0 0`
  cannot be closed by the NAIVE bounded-`F` route (J4-910: log-divergence when `k` reaches the singular
  region `s → x`, `τ = x − s → 0`).  The real route needs (per J4-910, sympy- and Sol-confirmed): from
  `F`'s spatial LIPSCHITZ modulus (β = 1; ALREADY banked as `LeviLipschitz.resolvent_lipschitz_pointwise`)
  produce the INTEGRABLE-singularity derivative bound `|∂_x g(x,s)| ≲ (x−s)^{−1/2}` via the CANCELLATION
  of `∂_τ H` BEFORE taking absolute values, using the mass-conservation identity `∫_z ∂_τ G(τ)(z) dz = 0`
  and Gaussian moments.  This file banks that cancellation core in its cleanest, self-contained 1-D form.

  ## THE MULTIPLIER.  `DtauG τ z := (z²/(4τ²) − 1/(2τ))·heatKernel1D τ z`.  This is EXACTLY the `∂_τ` of
  the 1-D heat kernel `G_τ(z) = (√(4πτ))⁻¹·exp(−z²/4τ)` — by the flat heat equation
  `∂_τ G = ∂²_z G = (z²/4τ² − 1/2τ)·G` (banked `heatKernel1D_deriv2_x`) — but we use it as an EXPLICIT
  multiplier (Sol's cut), not through any derivative-under-the-integral API.

  ## WHAT LANDS.
    • `integral_DtauG_eq_zero` — the MASS-CONSERVATION CANCELLATION `∫_z DtauG τ z dz = 0`, from the
      banked 2nd / 0th moments (`gaussianSecondMoment_oneD` = `2τ`, `gaussianZerothMoment_oneD` = `1`):
      `1/(4τ²)·2τ − 1/(2τ)·1 = 0`.  This is the analytic HEART J4-910 named as unbanked.
    • `integral_DtauG_mul_lipschitz` — the payoff `τ^{−1/2}` bound: for any measurable weight `f` with
      Lipschitz modulus at `0` (`|f z − f 0| ≤ L·|z|`),
        `|∫_z DtauG τ z · f z dz| ≤ L·(16√2 + 1) / √τ`.
      Route: split `f z = f 0 + (f z − f 0)`; the `f 0` part CANCELS (mass conservation); the remainder is
      majorised by `L·(|z|³/(4τ²) + |z|/(2τ))·G` and integrated by the banked absolute moments
      `oneD_absMoment3` (`≤ (64√2+1)(√τ)³`) and `oneD_absMoment1` (`≤ (3/2)√τ`), giving the exponent
      `β/2 − 1 = −1/2` (α = 1/2 < 1 ⟹ integrable singularity downstream).

  ⚠  STILL NOT `a₁ = R/6`.  This is one leaf brick; wiring it (via `resolvent_lipschitz_pointwise`) into
  the `∂_x g` bound, the three-regime split, and the census `hCross` binder are downstream steps.  No
  `sorry`, no new axioms, no `:= True`, no vacuous hypothesis (the weight-Lipschitz bundle is inhabited —
  every genuine spatial modulus supplies it), none equal to the conclusion, no existing file edited.
-/
import Mathlib
import QIQTH.GaussianMomentEnvelope

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open scoped Topology

namespace QIQTH.HeatResidualBound

set_option maxHeartbeats 1600000

/-! ### The `∂_τ`-multiplier of the 1-D heat kernel. -/

/-- **The 1-D heat-kernel `∂_τ`-multiplier** `DtauG τ z = (z²/(4τ²) − 1/(2τ))·G_τ(z)`.  Equal to
    `∂_τ heatKernel1D τ z` (flat heat equation `∂_τ G = ∂²_z G`, `heatKernel1D_deriv2_x`), used here as an
    explicit multiplier. -/
noncomputable def DtauG (τ z : ℝ) : ℝ :=
  (z ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)) * heatKernel1D τ z

/-! ### 1. The mass-conservation cancellation. -/

/-- **★ `integral_DtauG_eq_zero` — THE MASS-CONSERVATION CANCELLATION.**  `∫_z DtauG τ z dz = 0` for
    `τ > 0`.  The `∂_τ` of the Gaussian mass is zero: `1/(4τ²)·(∫ G·z²) − 1/(2τ)·(∫ G) = 1/(4τ²)·2τ −
    1/(2τ)·1 = 0`, from the banked 2nd moment (`gaussianSecondMoment_oneD`) and mass (`gaussianZerothMoment_oneD`).
    NOT `a₁ = R/6`. -/
theorem integral_DtauG_eq_zero (τ : ℝ) (hτ : 0 < τ) :
    ∫ z : ℝ, DtauG τ z = 0 := by
  have hτne : τ ≠ 0 := hτ.ne'
  have hsq_int : Integrable (fun z : ℝ => heatKernel1D τ z * z ^ 2) volume := by
    simpa using hk_mul_sq_pow_integrable τ hτ 1
  have h0_int : Integrable (fun z : ℝ => heatKernel1D τ z) volume :=
    QIQTH.GaussianConvolution.heatKernel1D_integrable τ hτ
  have hpt : ∀ z : ℝ, DtauG τ z
      = (1 / (4 * τ ^ 2)) * (heatKernel1D τ z * z ^ 2) - (1 / (2 * τ)) * heatKernel1D τ z := by
    intro z; simp only [DtauG]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub (hsq_int.const_mul _) (h0_int.const_mul _),
      integral_const_mul, integral_const_mul,
      gaussianSecondMoment_oneD τ hτ, gaussianZerothMoment_oneD τ hτ]
  field_simp
  ring

/-! ### 2. Auxiliary: `DtauG` is integrable and the pointwise majorant. -/

/-- `DtauG τ` is integrable on `ℝ` (split into the two integrable moment pieces). -/
theorem DtauG_integrable (τ : ℝ) (hτ : 0 < τ) :
    Integrable (fun z : ℝ => DtauG τ z) volume := by
  have hsq_int : Integrable (fun z : ℝ => heatKernel1D τ z * z ^ 2) volume := by
    simpa using hk_mul_sq_pow_integrable τ hτ 1
  have h0_int : Integrable (fun z : ℝ => heatKernel1D τ z) volume :=
    QIQTH.GaussianConvolution.heatKernel1D_integrable τ hτ
  have hpt : (fun z : ℝ => DtauG τ z)
      = fun z => (1 / (4 * τ ^ 2)) * (heatKernel1D τ z * z ^ 2) - (1 / (2 * τ)) * heatKernel1D τ z := by
    funext z; simp only [DtauG]; ring
  rw [hpt]
  exact (hsq_int.const_mul _).sub (h0_int.const_mul _)

/-- The absolute majorant of `DtauG τ z`: `|DtauG τ z| ≤ (z²/(4τ²) + 1/(2τ))·G_τ(z)`.  Triangle on the
    two nonneg coefficient pieces, `G_τ > 0`. -/
theorem abs_DtauG_le (τ : ℝ) (hτ : 0 < τ) (z : ℝ) :
    |DtauG τ z| ≤ (z ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * heatKernel1D τ z := by
  have hGpos : 0 < heatKernel1D τ z := heatKernel1D_pos τ z hτ
  have hc1 : 0 ≤ z ^ 2 / (4 * τ ^ 2) := by positivity
  have hc2 : 0 ≤ 1 / (2 * τ) := by positivity
  have hcoef : |z ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| ≤ z ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ) := by
    rw [abs_le]; constructor <;> nlinarith [hc1, hc2]
  calc |DtauG τ z| = |z ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| * heatKernel1D τ z := by
        rw [DtauG, abs_mul, abs_of_nonneg hGpos.le]
    _ ≤ (z ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * heatKernel1D τ z :=
        mul_le_mul_of_nonneg_right hcoef hGpos.le

/-! ### 3. The payoff — the `τ^{−1/2}` Lipschitz-weight bound. -/

/-- **★★★ `integral_DtauG_mul_lipschitz` — THE MOMENT-CANCELLATION BOUND (piece (2) core).**  For `τ > 0`,
    `L ≥ 0`, and a measurable weight `f : ℝ → ℝ` with spatial Lipschitz modulus at the origin
    `|f z − f 0| ≤ L·|z|`,
        `|∫_z DtauG τ z · f z dz| ≤ L·(16√2 + 1) / √τ`.
    The `f 0` part cancels by `integral_DtauG_eq_zero`; the remainder is majorised by
    `L·(|z|³/(4τ²) + |z|/(2τ))·G_τ(z)` and integrated by the banked absolute moments `oneD_absMoment3`,
    `oneD_absMoment1`, collapsing to the `τ^{−1/2}` (α = 1/2 < 1) singularity.  NOT `a₁ = R/6`. -/
theorem integral_DtauG_mul_lipschitz (τ : ℝ) (hτ : 0 < τ) (L : ℝ) (hL : 0 ≤ L)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (hlip : ∀ z : ℝ, |f z - f 0| ≤ L * |z|) :
    |∫ z : ℝ, DtauG τ z * f z| ≤ L * (16 * Real.sqrt 2 + 1) / Real.sqrt τ := by
  have hτne : τ ≠ 0 := hτ.ne'
  set s : ℝ := Real.sqrt τ with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hτ
  have hs2 : s ^ 2 = τ := Real.sq_sqrt hτ.le
  -- The dominating function `D z := L·(1/(4τ²)·G|z|³ + 1/(2τ)·G|z|)`.
  set D : ℝ → ℝ := fun z =>
    L * (1 / (4 * τ ^ 2) * (heatKernel1D τ z * |z| ^ 3) + 1 / (2 * τ) * (heatKernel1D τ z * |z| ^ 1))
    with hDdef
  have hD_int : Integrable D volume := by
    rw [hDdef]
    exact (((hk_mul_abspow_integrable τ hτ 3).const_mul _).add
      ((hk_mul_abspow_integrable τ hτ 1).const_mul _)).const_mul _
  -- `DtauG τ ·` is continuous, hence the products are AEStronglyMeasurable.
  have hDtauG_cont : Continuous (fun z : ℝ => DtauG τ z) := by
    simp only [DtauG]
    exact (((continuous_pow 2).div_const _).sub continuous_const).mul (hk_continuous τ)
  -- Pointwise: `|DtauG τ z · (f z − f 0)| ≤ D z`.
  have hptbnd : ∀ z : ℝ, |DtauG τ z * (f z - f 0)| ≤ D z := by
    intro z
    have hGpos : 0 < heatKernel1D τ z := heatKernel1D_pos τ z hτ
    have habs3 : heatKernel1D τ z * z ^ 2 * |z| = heatKernel1D τ z * |z| ^ 3 := by
      rw [show |z| ^ 3 = |z| ^ 2 * |z| from by ring, sq_abs]; ring
    calc |DtauG τ z * (f z - f 0)|
        = |DtauG τ z| * |f z - f 0| := abs_mul _ _
      _ ≤ ((z ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * heatKernel1D τ z) * (L * |z|) :=
          mul_le_mul (abs_DtauG_le τ hτ z) (hlip z) (abs_nonneg _)
            (mul_nonneg (by positivity) hGpos.le)
      _ = D z := by
          have hexp : ((z ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * heatKernel1D τ z) * (L * |z|)
              = L * (1 / (4 * τ ^ 2) * (heatKernel1D τ z * z ^ 2 * |z|)
                  + 1 / (2 * τ) * (heatKernel1D τ z * |z|)) := by ring
          rw [hexp, habs3, hDdef]
          simp only [pow_one]
  -- Integrability of `DtauG τ · (f − f 0)`.
  have hmeas_diff : AEStronglyMeasurable (fun z : ℝ => DtauG τ z * (f z - f 0)) volume :=
    hDtauG_cont.aestronglyMeasurable.mul (hf.sub aestronglyMeasurable_const)
  have hint_diff : Integrable (fun z : ℝ => DtauG τ z * (f z - f 0)) volume :=
    hD_int.mono' hmeas_diff (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs]; exact hptbnd z))
  -- Integrability of `DtauG τ · f` and the cancellation split.
  have hDtauG_int : Integrable (fun z : ℝ => DtauG τ z) volume := DtauG_integrable τ hτ
  have hint_f : Integrable (fun z : ℝ => DtauG τ z * f z) volume := by
    have hsplit : (fun z : ℝ => DtauG τ z * f z)
        = fun z => DtauG τ z * (f z - f 0) + f 0 * DtauG τ z := by
      funext z; ring
    rw [hsplit]; exact hint_diff.add (hDtauG_int.const_mul _)
  have hsplit_int : ∫ z : ℝ, DtauG τ z * f z = ∫ z : ℝ, DtauG τ z * (f z - f 0) := by
    have hpt : (fun z : ℝ => DtauG τ z * f z)
        = fun z => DtauG τ z * (f z - f 0) + f 0 * DtauG τ z := by funext z; ring
    rw [hpt, integral_add hint_diff (hDtauG_int.const_mul _), integral_const_mul,
        integral_DtauG_eq_zero τ hτ, mul_zero, add_zero]
  rw [hsplit_int]
  -- `|∫ diff| ≤ ∫ |diff| ≤ ∫ D`.
  have hstep1 : |∫ z : ℝ, DtauG τ z * (f z - f 0)| ≤ ∫ z : ℝ, D z := by
    calc |∫ z : ℝ, DtauG τ z * (f z - f 0)|
        ≤ ∫ z : ℝ, |DtauG τ z * (f z - f 0)| := by
          have h := norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
            (fun z : ℝ => DtauG τ z * (f z - f 0))
          simpa only [Real.norm_eq_abs] using h
      _ ≤ ∫ z : ℝ, D z :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => abs_nonneg _))
            hD_int (Filter.Eventually.of_forall hptbnd)
  refine le_trans hstep1 ?_
  -- Evaluate `∫ D` by the banked absolute moments.
  have hDval : ∫ z : ℝ, D z
      = L * (1 / (4 * τ ^ 2) * (∫ z : ℝ, heatKernel1D τ z * |z| ^ 3)
          + 1 / (2 * τ) * (∫ z : ℝ, heatKernel1D τ z * |z| ^ 1)) := by
    rw [hDdef, integral_const_mul,
        integral_add ((hk_mul_abspow_integrable τ hτ 3).const_mul _)
          ((hk_mul_abspow_integrable τ hτ 1).const_mul _),
        integral_const_mul, integral_const_mul]
  rw [hDval]
  -- Bound each moment and collapse the `τ`-powers to `τ^{−1/2}`.
  have hm3 : ∫ z : ℝ, heatKernel1D τ z * |z| ^ 3 ≤ (64 * Real.sqrt 2 + 1) * s ^ 3 := oneD_absMoment3 τ hτ
  have hm1 : ∫ z : ℝ, heatKernel1D τ z * |z| ^ 1 ≤ 3 / 2 * s ^ 1 := oneD_absMoment1 τ hτ
  have hc1nn : 0 ≤ (1 : ℝ) / (4 * τ ^ 2) := by positivity
  have hc2nn : 0 ≤ (1 : ℝ) / (2 * τ) := by positivity
  have hbound : 1 / (4 * τ ^ 2) * (∫ z : ℝ, heatKernel1D τ z * |z| ^ 3)
        + 1 / (2 * τ) * (∫ z : ℝ, heatKernel1D τ z * |z| ^ 1)
      ≤ (16 * Real.sqrt 2 + 1) / s := by
    have hstep : 1 / (4 * τ ^ 2) * (∫ z : ℝ, heatKernel1D τ z * |z| ^ 3)
          + 1 / (2 * τ) * (∫ z : ℝ, heatKernel1D τ z * |z| ^ 1)
        ≤ 1 / (4 * τ ^ 2) * ((64 * Real.sqrt 2 + 1) * s ^ 3) + 1 / (2 * τ) * (3 / 2 * s ^ 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hm3 hc1nn) (mul_le_mul_of_nonneg_left hm1 hc2nn)
    refine le_trans hstep (le_of_eq ?_)
    -- `τ = s²`, so `s³/(4τ²) = 1/(4s)`, `s/(2τ) = 1/(2s)`; total `(16√2+1)/s`.
    have hsne : s ≠ 0 := hs.ne'
    rw [← hs2]
    field_simp
    ring
  -- Assemble with the outer `L ≥ 0`.
  calc L * (1 / (4 * τ ^ 2) * (∫ z : ℝ, heatKernel1D τ z * |z| ^ 3)
            + 1 / (2 * τ) * (∫ z : ℝ, heatKernel1D τ z * |z| ^ 1))
      ≤ L * ((16 * Real.sqrt 2 + 1) / s) := mul_le_mul_of_nonneg_left hbound hL
    _ = L * (16 * Real.sqrt 2 + 1) / s := by ring

/-! ### 4. Non-vacuity — the Lipschitz-weight hypothesis bundle is inhabited. -/

/-- **Non-vacuity witness.**  The hypothesis bundle of `integral_DtauG_mul_lipschitz` is jointly
    satisfiable by a genuine nonconstant weight: `f := id` (measurable) has `|f z − f 0| = |z| ≤ 1·|z|`
    (`L = 1`).  So the bound fires on a real Lipschitz weight, not an empty/unsatisfiable one.  NOT
    `a₁ = R/6`. -/
theorem integral_DtauG_mul_lipschitz_hyp_satisfiable (τ : ℝ) (hτ : 0 < τ) :
    ∃ (L : ℝ) (f : ℝ → ℝ), 0 ≤ L ∧ AEStronglyMeasurable f volume ∧
      (∀ z : ℝ, |f z - f 0| ≤ L * |z|) := by
  refine ⟨1, id, zero_le_one, aestronglyMeasurable_id, fun z => ?_⟩
  simp only [id_eq, sub_zero, one_mul, le_refl]

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms DtauG
#print axioms integral_DtauG_eq_zero
#print axioms DtauG_integrable
#print axioms abs_DtauG_le
#print axioms integral_DtauG_mul_lipschitz
#print axioms integral_DtauG_mul_lipschitz_hyp_satisfiable
end AxiomChecks
