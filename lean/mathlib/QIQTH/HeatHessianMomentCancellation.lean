/-
  HeatHessianMomentCancellation — the n-D heat-kernel HESSIAN moment-cancellation core: the precise
  "odd-moment / vanishing-diagonal-jet" ingredient (gpt-5.6-sol high, 2026-08-22) that the
  `VanVleckGatedSpatialSymmetry.hcomp` obligation of `hCConv` needs, and the n-D directional/bilinear
  generalization of the 1-D `GaussTauDerivCancellation.integral_DtauG_mul_lipschitz` (J4-919) that
  discharged the analogous `hCross` `H_far` wall.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE brick — a standalone n-D Gaussian moment estimate for the heat-kernel Hessian
  multiplier, decoupled from `H`, from the Levi series `F`, from the census, from the opaque chart, and
  from `hcomp` itself.  It does **NOT** discharge `hcomp`: wiring it in still requires the chart
  transport `z ↦ V = W_z(x)` (the opaque `uniformInverseChart` jets `P`, `Q` and the uniformly-Lipschitz
  transported coefficient) — the recurring `JointSecondOrderRNCRegularity` / opaque-chart wall.  What it
  DOES is eliminate the exact singularity that made the crude joint-Lipschitz TRANSPOSITION route
  (cp872 NO-GO, `τ⁻¹` log-divergent) fail: the constant mode of the Hessian multiplier cancels EXACTLY,
  leaving the integrable `τ^{−1/2}` rate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MULTIPLIER.  For `τ > 0` and directions `p q : Point n`, the **heat-kernel Hessian multiplier**
      `heatHessMult τ p q v := (⟨v,p⟩·⟨v,q⟩/(4τ²) − ⟨p,q⟩/(2τ))·G_τ(v)`,   `⟨v,p⟩ := Σ_k v_k p_k`.
  This is EXACTLY the second directional field-derivative `∂_p ∂_q G_τ(v)` of the n-D heat kernel
  (`gaussDdim`) — the multi-dimensional analogue of `DtauG` (whose diagonal `p=q=eᵢ` recovers the 1-D
  `DtauG` `∂_τ`-multiplier by the flat heat equation).  It is the closed-form scalar carried by the
  banked on-gate Hessian formula `SecondDerivEnvelope.witnessFieldDeriv2_gate_eq` (with `P`,`Q` the chart
  jets), before chart transport.

  ## WHAT LANDS.
    • `coordProd_gauss_integral` — the exact n-D SECOND CROSS-MOMENT `∫ z, z_a·z_c·G_τ(z) = if a=c then
      2τ else 0` (diagonal = `gaussianSecondMoment_oneD`, off-diagonal = `gaussianFirstMoment_oneD`
      product-vanishing).  The coordinate heart of BOTH the mass-conservation (a=c) and odd-moment (a≠c)
      cancellations.
    • `integral_dotdot_gauss` — `∫ v, ⟨v,p⟩·⟨v,q⟩·G_τ(v) = 2τ·⟨p,q⟩`.
    • `integral_heatHessMult_eq_zero` — ★ THE CANCELLATION `∫ v, heatHessMult τ p q v = 0`, from
      `(2τ⟨p,q⟩)/(4τ²) − ⟨p,q⟩/(2τ) = 0`.  The exact analogue of `integral_DtauG_eq_zero`.
    • `integral_heatHessMult_mul_lipschitz` — ★★★ THE PAYOFF `τ^{−1/2}` bound: for a weight `f` with
      Lipschitz modulus at `0` (`|f v − f 0| ≤ L‖v‖`),
        `|∫ v, heatHessMult τ p q v · f v| ≤ Cₙ·L·‖p‖·‖q‖/√τ`.
      The `f 0` part CANCELS (`integral_heatHessMult_eq_zero`); the remainder is majorised by the n-D
      3rd/1st norm moments (`pow_norm_mul_gauss_integral` at `k=3,1`), collapsing to `τ^{−1/2}`
      (α = 1/2 < 1 ⟹ interval-integrable downstream — the sliver rate `hcomp` needs).

  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis (the weight-Lipschitz bundle is
  inhabited — `f := 0`, or any genuine spatial modulus), none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GaussTauDerivCancellation
import QIQTH.GaussianMomentEnvelope
import QIQTH.DeltaFamilyBoundary

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound
open scoped Topology BigOperators

namespace QIQTH.HeatHessMoment

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **The n-D heat-kernel Hessian multiplier.**  `heatHessMult τ p q v = (⟨v,p⟩⟨v,q⟩/(4τ²) −
    ⟨p,q⟩/(2τ))·G_τ(v)` with `⟨v,p⟩ = Σ_k v_k p_k`.  Equal to `∂_p ∂_q G_τ(v)` (the n-D heat-kernel
    Hessian); the diagonal `p=q=eᵢ` recovers the 1-D `DtauG` up to the coordinate split. -/
noncomputable def heatHessMult (τ : ℝ) (p q v : Point n) : ℝ :=
  ((∑ k, v k * p k) * (∑ k, v k * q k) / (4 * τ ^ 2) - (∑ k, p k * q k) / (2 * τ))
    * gaussDdim τ v

/-! ### 1. The n-D second cross-moment. -/

/-- `heatKernel1D τ · id` is integrable (dominated by `heatKernel1D τ · |·|^1`). -/
private theorem hk_mul_id_integrable (τ : ℝ) (hτ : 0 < τ) :
    Integrable (fun y : ℝ => heatKernel1D τ y * y) volume := by
  refine (hk_mul_abspow_integrable τ hτ 1).mono'
    ((hk_continuous τ).mul continuous_id).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => ?_))
  have hknn : 0 ≤ heatKernel1D τ y := (heatKernel1D_pos τ y hτ).le
  exact le_of_eq (by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hknn, pow_one])

/-- Per-coordinate factor integrability (case split on whether `m` hits `a`/`c`). -/
private theorem coordFactor_integrable (τ : ℝ) (hτ : 0 < τ) (a c m : Fin n) :
    Integrable
      (fun y : ℝ => heatKernel1D τ y * ((if m = a then y else 1) * (if m = c then y else 1)))
      volume := by
  by_cases hma : m = a
  · by_cases hmc : m = c
    · simp only [if_pos hma, if_pos hmc]
      have : (fun y : ℝ => heatKernel1D τ y * (y * y))
          = fun y => heatKernel1D τ y * y ^ 2 := by funext y; ring
      rw [this]; simpa using hk_mul_sq_pow_integrable τ hτ 1
    · simp only [if_pos hma, if_neg hmc, mul_one]; exact hk_mul_id_integrable τ hτ
  · by_cases hmc : m = c
    · simp only [if_neg hma, if_pos hmc, one_mul]; exact hk_mul_id_integrable τ hτ
    · simp only [if_neg hma, if_neg hmc, mul_one]; exact heatKernel1D_integrable τ hτ

/-- The n-D function `z ↦ z_a·z_c·G_τ(z)` is integrable. -/
theorem coordProd_gauss_integrable (τ : ℝ) (hτ : 0 < τ) (a c : Fin n) :
    Integrable (fun z : Point n => z a * z c * gaussDdim τ z) volume := by
  have hpt : (fun z : Point n => z a * z c * gaussDdim τ z)
      = fun z => ∏ m, heatKernel1D τ (z m)
          * ((if m = a then z m else 1) * (if m = c then z m else 1)) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
    ring
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ))
    (fun m => coordFactor_integrable τ hτ a c m)

/-- **★ `coordProd_gauss_integral` — THE n-D SECOND CROSS-MOMENT.**  `∫ z, z_a·z_c·G_τ(z) = if a=c then
    2τ else 0`.  Diagonal (`a=c`) is `gaussianSecondMoment_oneD` (`= 2τ`); off-diagonal (`a≠c`) vanishes
    because the `a`-coordinate factor is the first moment `∫ G·y = 0` (`gaussianFirstMoment_oneD`).  The
    coordinate heart of the mass-conservation AND odd-moment cancellations.  NOT `a₁ = R/6`. -/
theorem coordProd_gauss_integral (τ : ℝ) (hτ : 0 < τ) (a c : Fin n) :
    ∫ z : Point n, z a * z c * gaussDdim τ z = if a = c then 2 * τ else 0 := by
  have hpt : ∀ z : Point n, z a * z c * gaussDdim τ z
      = ∏ m, heatKernel1D τ (z m)
          * ((if m = a then z m else 1) * (if m = c then z m else 1)) := by
    intro z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
    ring
  rw [integral_congr_ae (ae_of_all _ hpt),
      integral_fintype_prod_volume_eq_prod
        (fun (m : Fin n) (y : ℝ) =>
          heatKernel1D τ y * ((if m = a then y else 1) * (if m = c then y else 1)))]
  by_cases hac : a = c
  · subst hac
    -- diagonal: per-coordinate value is `if m = a then 2τ else 1`
    have hval : ∀ m : Fin n,
        (∫ y : ℝ, heatKernel1D τ y * ((if m = a then y else 1) * (if m = a then y else 1)))
          = (if m = a then 2 * τ else 1) := by
      intro m
      by_cases hm : m = a
      · simp only [if_pos hm]
        have : (fun y : ℝ => heatKernel1D τ y * (y * y)) = fun y => heatKernel1D τ y * y ^ 2 := by
          funext y; ring
        rw [this, gaussianSecondMoment_oneD τ hτ]
      · simp only [if_neg hm, mul_one]; exact gaussianZerothMoment_oneD τ hτ
    rw [Finset.prod_congr rfl (fun m _ => hval m), Fintype.prod_ite_eq', if_pos rfl]
  · -- off-diagonal: the `a`-coordinate factor is the vanishing first moment ⟹ product 0
    rw [if_neg hac]
    refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
    simp only [if_neg hac, mul_one]
    exact gaussianFirstMoment_oneD τ hτ

/-! ### 2. The bilinear second moment and the cancellation. -/

/-- **`integral_dotdot_gauss`.**  `∫ v, ⟨v,p⟩·⟨v,q⟩·G_τ(v) = 2τ·⟨p,q⟩`.  Expand the two dot products
    into a double coordinate sum, pull the finite sums out (`coordProd_gauss_integrable`), and collapse
    the diagonal via `coordProd_gauss_integral`. -/
theorem integral_dotdot_gauss (τ : ℝ) (hτ : 0 < τ) (p q : Point n) :
    ∫ v : Point n, (∑ k, v k * p k) * (∑ k, v k * q k) * gaussDdim τ v
      = 2 * τ * (∑ k, p k * q k) := by
  have hpt : ∀ v : Point n, (∑ k, v k * p k) * (∑ k, v k * q k) * gaussDdim τ v
      = ∑ k, ∑ l, (p k * q l) * (v k * v l * gaussDdim τ v) := by
    intro v
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [integral_congr_ae (ae_of_all _ hpt)]
  rw [integral_finsetSum _ (fun k _ => ?_)]
  · have hstep : ∀ k : Fin n,
        (∫ v : Point n, ∑ l, (p k * q l) * (v k * v l * gaussDdim τ v))
          = ∑ l, (p k * q l) * (if k = l then 2 * τ else 0) := by
      intro k
      rw [integral_finsetSum _ (fun l _ => (coordProd_gauss_integrable τ hτ k l).const_mul _)]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [integral_const_mul, coordProd_gauss_integral τ hτ k l]
    rw [Finset.sum_congr rfl (fun k _ => hstep k)]
    have hcollapse : ∀ k : Fin n,
        (∑ l, (p k * q l) * (if k = l then 2 * τ else 0)) = p k * q k * (2 * τ) := by
      intro k
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
      · intro l _ hlk
        rw [if_neg (fun h => hlk h.symm), mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [Finset.sum_congr rfl (fun k _ => hcollapse k)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_); ring
  · exact integrable_finsetSum _ (fun l _ => (coordProd_gauss_integrable τ hτ k l).const_mul _)

/-- **★ `integral_heatHessMult_eq_zero` — THE HESSIAN MOMENT CANCELLATION.**  `∫ v, heatHessMult τ p q v
    = 0` for `τ > 0`.  The constant mode of the heat-kernel Hessian integrates to zero:
    `(∫⟨v,p⟩⟨v,q⟩G)/(4τ²) − ⟨p,q⟩(∫G)/(2τ) = (2τ⟨p,q⟩)/(4τ²) − ⟨p,q⟩/(2τ) = 0`.  The exact n-D
    directional analogue of `integral_DtauG_eq_zero`.  NOT `a₁ = R/6`. -/
theorem integral_heatHessMult_eq_zero (τ : ℝ) (hτ : 0 < τ) (p q : Point n) :
    ∫ v : Point n, heatHessMult τ p q v = 0 := by
  have hτne : τ ≠ 0 := hτ.ne'
  have hdd_int : Integrable
      (fun v : Point n => (∑ k, v k * p k) * (∑ k, v k * q k) * gaussDdim τ v) volume := by
    have hpt : (fun v : Point n => (∑ k, v k * p k) * (∑ k, v k * q k) * gaussDdim τ v)
        = fun v => ∑ k, ∑ l, (p k * q l) * (v k * v l * gaussDdim τ v) := by
      funext v
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_); ring
    rw [hpt]
    exact integrable_finsetSum _ (fun k _ =>
      integrable_finsetSum _ (fun l _ => (coordProd_gauss_integrable τ hτ k l).const_mul _))
  have h0_int : Integrable (fun v : Point n => gaussDdim τ v) volume := gaussDdim_integrable τ hτ
  have hpt : ∀ v : Point n, heatHessMult τ p q v
      = (1 / (4 * τ ^ 2)) * ((∑ k, v k * p k) * (∑ k, v k * q k) * gaussDdim τ v)
        - ((∑ k, p k * q k) / (2 * τ)) * gaussDdim τ v := by
    intro v; simp only [heatHessMult]; ring
  rw [integral_congr_ae (ae_of_all _ hpt),
      integral_sub (hdd_int.const_mul _) (h0_int.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_dotdot_gauss τ hτ p q, gaussDdim_integral_eq_one τ hτ]
  field_simp
  ring

/-! ### 3. The pointwise majorant and the `τ^{−1/2}` Lipschitz-weight payoff. -/

/-- `heatHessMult τ p q ·` is integrable. -/
theorem heatHessMult_integrable (τ : ℝ) (hτ : 0 < τ) (p q : Point n) :
    Integrable (fun v : Point n => heatHessMult τ p q v) volume := by
  have hdd_int : Integrable
      (fun v : Point n => (∑ k, v k * p k) * (∑ k, v k * q k) * gaussDdim τ v) volume := by
    have hpt : (fun v : Point n => (∑ k, v k * p k) * (∑ k, v k * q k) * gaussDdim τ v)
        = fun v => ∑ k, ∑ l, (p k * q l) * (v k * v l * gaussDdim τ v) := by
      funext v
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_); ring
    rw [hpt]
    exact integrable_finsetSum _ (fun k _ =>
      integrable_finsetSum _ (fun l _ => (coordProd_gauss_integrable τ hτ k l).const_mul _))
  have h0_int : Integrable (fun v : Point n => gaussDdim τ v) volume := gaussDdim_integrable τ hτ
  have hpt : (fun v : Point n => heatHessMult τ p q v)
      = fun v => (1 / (4 * τ ^ 2)) * ((∑ k, v k * p k) * (∑ k, v k * q k) * gaussDdim τ v)
        - ((∑ k, p k * q k) / (2 * τ)) * gaussDdim τ v := by
    funext v; simp only [heatHessMult]; ring
  rw [hpt]; exact (hdd_int.const_mul _).sub (h0_int.const_mul _)

/-- `|⟨v,p⟩| ≤ n·‖v‖·‖p‖` for the sup norm on `Point n`. -/
private theorem abs_dot_le (v p : Point n) : |∑ k, v k * p k| ≤ (n : ℝ) * ‖v‖ * ‖p‖ := by
  calc |∑ k, v k * p k| ≤ ∑ k, |v k * p k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |v k| * |p k| := by simp only [abs_mul]
    _ ≤ ∑ _k : Fin n, ‖v‖ * ‖p‖ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v k)
          (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm p k) (abs_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * ‖v‖ * ‖p‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The absolute majorant: `|heatHessMult τ p q v| ≤ (n²‖p‖‖q‖)·(‖v‖²/(4τ²) + 1/(2τ))·G_τ(v)`. -/
theorem abs_heatHessMult_le (τ : ℝ) (hτ : 0 < τ) (p q v : Point n) :
    |heatHessMult τ p q v|
      ≤ ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖) * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v) := by
  have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
  have hdv : |∑ k, v k * p k| ≤ (n : ℝ) * ‖v‖ * ‖p‖ := abs_dot_le v p
  have hdw : |∑ k, v k * q k| ≤ (n : ℝ) * ‖v‖ * ‖q‖ := abs_dot_le v q
  have hdpq : |∑ k, p k * q k| ≤ (n : ℝ) * ‖p‖ * ‖q‖ := abs_dot_le p q
  have hnpq : 0 ≤ (n : ℝ) * ‖p‖ * ‖q‖ := by positivity
  -- bound the singular scalar's absolute value
  have hscal : |(∑ k, v k * p k) * (∑ k, v k * q k) / (4 * τ ^ 2) - (∑ k, p k * q k) / (2 * τ)|
      ≤ (n : ℝ) ^ 2 * ‖p‖ * ‖q‖ * (‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) := by
    have hτ2 : (0:ℝ) < 4 * τ ^ 2 := by positivity
    have hτ1 : (0:ℝ) < 2 * τ := by positivity
    have hX : |(∑ k, v k * p k) * (∑ k, v k * q k)| ≤ (n : ℝ) ^ 2 * ‖v‖ ^ 2 * ‖p‖ * ‖q‖ := by
      rw [abs_mul]
      calc |∑ k, v k * p k| * |∑ k, v k * q k|
          ≤ ((n : ℝ) * ‖v‖ * ‖p‖) * ((n : ℝ) * ‖v‖ * ‖q‖) :=
            mul_le_mul hdv hdw (abs_nonneg _) (by positivity)
        _ = (n : ℝ) ^ 2 * ‖v‖ ^ 2 * ‖p‖ * ‖q‖ := by ring
    have hnn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hnat : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
      calc (n : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (n : ℝ) ^ 2 := by push_cast; ring
    have hY : |∑ k, p k * q k| ≤ (n : ℝ) ^ 2 * ‖p‖ * ‖q‖ :=
      le_trans hdpq (by nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hnn2)
        (norm_nonneg p)) (norm_nonneg q)])
    have htri : |(∑ k, v k * p k) * (∑ k, v k * q k) / (4 * τ ^ 2)
          - (∑ k, p k * q k) / (2 * τ)|
        ≤ |(∑ k, v k * p k) * (∑ k, v k * q k)| / (4 * τ ^ 2)
          + |∑ k, p k * q k| / (2 * τ) := by
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_div, abs_div, abs_of_pos hτ2, abs_of_pos hτ1]
    refine htri.trans ?_
    have hb1 : |(∑ k, v k * p k) * (∑ k, v k * q k)| / (4 * τ ^ 2)
        ≤ ((n : ℝ) ^ 2 * ‖v‖ ^ 2 * ‖p‖ * ‖q‖) / (4 * τ ^ 2) :=
      (div_le_div_iff_of_pos_right hτ2).mpr hX
    have hb2 : |∑ k, p k * q k| / (2 * τ)
        ≤ ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖) / (2 * τ) :=
      (div_le_div_iff_of_pos_right hτ1).mpr hY
    calc |(∑ k, v k * p k) * (∑ k, v k * q k)| / (4 * τ ^ 2)
            + |∑ k, p k * q k| / (2 * τ)
        ≤ ((n : ℝ) ^ 2 * ‖v‖ ^ 2 * ‖p‖ * ‖q‖) / (4 * τ ^ 2)
            + ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖) / (2 * τ) := add_le_add hb1 hb2
      _ = (n : ℝ) ^ 2 * ‖p‖ * ‖q‖ * (‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) := by
          field_simp
  calc |heatHessMult τ p q v|
      = |(∑ k, v k * p k) * (∑ k, v k * q k) / (4 * τ ^ 2) - (∑ k, p k * q k) / (2 * τ)|
          * gaussDdim τ v := by
        rw [heatHessMult, abs_mul, abs_of_nonneg hGnn]
    _ ≤ ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖ * (‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ))) * gaussDdim τ v :=
        mul_le_mul_of_nonneg_right hscal hGnn
    _ = ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖) * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v) := by
        ring

/-- **★★★ `integral_heatHessMult_mul_lipschitz` — THE MOMENT-CANCELLATION PAYOFF (the `τ^{−1/2}`
    directional Hessian bound).**  For `τ > 0`, `L ≥ 0`, and a weight `f : Point n → ℝ` with spatial
    Lipschitz modulus at the origin (`|f v − f 0| ≤ L·‖v‖`),
        `|∫ v, heatHessMult τ p q v · f v| ≤ L·n³·‖p‖·‖q‖·(16√2 + 1) / √τ`.
    The `f 0` part CANCELS (`integral_heatHessMult_eq_zero`); the remainder is majorised by
    `L·n²‖p‖‖q‖·(‖v‖³/(4τ²) + ‖v‖/(2τ))·G_τ` and integrated by the n-D 3rd/1st norm moments
    (`pow_norm_mul_gauss_integral` at `k=3,1`), collapsing to `τ^{−1/2}` (α = 1/2 < 1 ⟹ interval-
    integrable over the sliver — the exact `hcomp` rate).  The n-D directional generalization of the
    1-D `GaussTauDerivCancellation.integral_DtauG_mul_lipschitz` (J4-919; same constant `16√2 + 1`).
    NOT `a₁ = R/6`. -/
theorem integral_heatHessMult_mul_lipschitz (τ : ℝ) (hτ : 0 < τ) (p q : Point n)
    (L : ℝ) (hL : 0 ≤ L) (f : Point n → ℝ) (hf : AEStronglyMeasurable f volume)
    (hlip : ∀ v : Point n, |f v - f 0| ≤ L * ‖v‖) :
    |∫ v : Point n, heatHessMult τ p q v * f v|
      ≤ L * (n : ℝ) ^ 3 * ‖p‖ * ‖q‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ := by
  set s : ℝ := Real.sqrt τ with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hτ
  have hs2 : s ^ 2 = τ := Real.sq_sqrt hτ.le
  have hpnn : 0 ≤ ‖p‖ := norm_nonneg _
  have hqnn : 0 ≤ ‖q‖ := norm_nonneg _
  set C : ℝ := (n : ℝ) ^ 2 * ‖p‖ * ‖q‖ with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  set c3 : ℝ := L * C / (4 * τ ^ 2) with hc3def
  set c1 : ℝ := L * C / (2 * τ) with hc1def
  have hc3nn : 0 ≤ c3 := by rw [hc3def]; positivity
  have hc1nn : 0 ≤ c1 := by rw [hc1def]; positivity
  -- the dominating function
  set D : ℝ → Point n → ℝ := fun _ => fun v =>
    c3 * (‖v‖ ^ 3 * gaussDdim τ v) + c1 * (‖v‖ ^ 1 * gaussDdim τ v) with hDdef
  have hD_int : Integrable (D 0) volume := by
    rw [hDdef]
    exact ((normPow_gauss_integrable 3 (by norm_num) τ hτ).const_mul _).add
      ((normPow_gauss_integrable 1 (by norm_num) τ hτ).const_mul _)
  -- pointwise: `|heatHessMult · (f − f 0)| ≤ D`
  have hptbnd : ∀ v : Point n, |heatHessMult τ p q v * (f v - f 0)| ≤ D 0 v := by
    intro v
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    calc |heatHessMult τ p q v * (f v - f 0)|
        = |heatHessMult τ p q v| * |f v - f 0| := abs_mul _ _
      _ ≤ (((n : ℝ) ^ 2 * ‖p‖ * ‖q‖) * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v))
            * (L * ‖v‖) :=
          mul_le_mul (abs_heatHessMult_le τ hτ p q v) (hlip v) (abs_nonneg _)
            (mul_nonneg (by positivity) (mul_nonneg (by positivity) hGnn))
      _ = D 0 v := by
          rw [hDdef, hc3def, hc1def, hCdef]; ring
  -- integrability of `heatHessMult · (f − f 0)`
  have hmeas_diff : AEStronglyMeasurable (fun v : Point n => heatHessMult τ p q v * (f v - f 0))
      volume :=
    (heatHessMult_integrable τ hτ p q).aestronglyMeasurable.mul (hf.sub aestronglyMeasurable_const)
  have hint_diff : Integrable (fun v : Point n => heatHessMult τ p q v * (f v - f 0)) volume :=
    hD_int.mono' hmeas_diff (Filter.Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs]; exact hptbnd v))
  -- cancellation split
  have hHM_int : Integrable (fun v : Point n => heatHessMult τ p q v) volume :=
    heatHessMult_integrable τ hτ p q
  have hsplit_int : ∫ v : Point n, heatHessMult τ p q v * f v
      = ∫ v : Point n, heatHessMult τ p q v * (f v - f 0) := by
    have hpt : (fun v : Point n => heatHessMult τ p q v * f v)
        = fun v => heatHessMult τ p q v * (f v - f 0) + f 0 * heatHessMult τ p q v := by
      funext v; ring
    rw [hpt, integral_add hint_diff (hHM_int.const_mul _), integral_const_mul,
        integral_heatHessMult_eq_zero τ hτ p q, mul_zero, add_zero]
  rw [hsplit_int]
  -- `|∫ diff| ≤ ∫ |diff| ≤ ∫ D`
  have hstep1 : |∫ v : Point n, heatHessMult τ p q v * (f v - f 0)| ≤ ∫ v : Point n, D 0 v := by
    calc |∫ v : Point n, heatHessMult τ p q v * (f v - f 0)|
        ≤ ∫ v : Point n, |heatHessMult τ p q v * (f v - f 0)| := by
          have h := norm_integral_le_integral_norm (μ := (volume : Measure (Point n)))
            (fun v : Point n => heatHessMult τ p q v * (f v - f 0))
          simpa only [Real.norm_eq_abs] using h
      _ ≤ ∫ v : Point n, D 0 v :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun v => abs_nonneg _))
            hD_int (Filter.Eventually.of_forall hptbnd)
  refine le_trans hstep1 ?_
  -- evaluate `∫ D` via the n-D norm moments
  have hDval : ∫ v : Point n, D 0 v
      = c3 * (∫ v : Point n, ‖v‖ ^ 3 * gaussDdim τ v)
        + c1 * (∫ v : Point n, ‖v‖ ^ 1 * gaussDdim τ v) := by
    rw [hDdef, integral_add ((normPow_gauss_integrable 3 (by norm_num) τ hτ).const_mul _)
        ((normPow_gauss_integrable 1 (by norm_num) τ hτ).const_mul _),
        integral_const_mul, integral_const_mul]
  rw [hDval]
  -- moment bounds (κ = 1)
  have hm3 : ∫ v : Point n, ‖v‖ ^ 3 * gaussDdim τ v ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * s ^ 3 := by
    have h := pow_norm_mul_gauss_integral (n := n) 3 (by norm_num) 1 one_pos τ hτ
      (64 * Real.sqrt 2 + 1) (by positivity)
      (by simpa [one_mul] using oneD_absMoment3 τ hτ)
    simpa [one_mul, Real.sqrt_one, hsdef] using h
  have hm1 : ∫ v : Point n, ‖v‖ ^ 1 * gaussDdim τ v ≤ (n : ℝ) * (3 / 2) * s ^ 1 := by
    have h := pow_norm_mul_gauss_integral (n := n) 1 (by norm_num) 1 one_pos τ hτ
      (3 / 2) (by norm_num)
      (by simpa [one_mul] using oneD_absMoment1 τ hτ)
    simpa [one_mul, Real.sqrt_one, hsdef] using h
  have hfin : c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * s ^ 3)
        + c1 * ((n : ℝ) * (3 / 2) * s ^ 1)
      = L * (n : ℝ) ^ 3 * ‖p‖ * ‖q‖ * (16 * Real.sqrt 2 + 1) / s := by
    rw [hc3def, hc1def, hCdef, ← hs2]
    have hsne : s ≠ 0 := hs.ne'
    field_simp
    ring
  calc c3 * (∫ v : Point n, ‖v‖ ^ 3 * gaussDdim τ v)
          + c1 * (∫ v : Point n, ‖v‖ ^ 1 * gaussDdim τ v)
      ≤ c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * s ^ 3)
          + c1 * ((n : ℝ) * (3 / 2) * s ^ 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hm3 hc3nn)
          (mul_le_mul_of_nonneg_left hm1 hc1nn)
    _ = L * (n : ℝ) ^ 3 * ‖p‖ * ‖q‖ * (16 * Real.sqrt 2 + 1) / s := hfin

/-! ### 4. Non-vacuity — the Lipschitz-weight hypothesis bundle is inhabited. -/

/-- **Non-vacuity witness.**  The hypothesis bundle of `integral_heatHessMult_mul_lipschitz` is jointly
    satisfiable by a genuine nonconstant weight: `f := (‖·‖ : Point n → ℝ)` is measurable and
    `|‖v‖ − ‖0‖| = ‖v‖ ≤ 1·‖v‖` (`L = 1`).  So the bound fires on a real Lipschitz weight, not an
    empty/unsatisfiable one.  NOT `a₁ = R/6`. -/
theorem integral_heatHessMult_mul_lipschitz_hyp_satisfiable (τ : ℝ) (_hτ : 0 < τ) :
    ∃ (L : ℝ) (f : Point n → ℝ), 0 ≤ L ∧ AEStronglyMeasurable f volume ∧
      (∀ v : Point n, |f v - f 0| ≤ L * ‖v‖) := by
  refine ⟨1, fun v => ‖v‖, zero_le_one, continuous_norm.aestronglyMeasurable, fun v => ?_⟩
  simp only [norm_zero, sub_zero, one_mul, abs_norm, le_refl]

end QIQTH.HeatHessMoment
