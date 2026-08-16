/-
  GaussianHessianCancelMixed — J4-781: the OFF-DIAGONAL (mixed-index `∂ᵢ∂ⱼ`, `i ≠ j`) companion of
  `GaussianHessianCancel.gaussian_hessian_cancel`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT (the wall this closes).

  The `√ε` sliver estimate `XUniformSliverFull.witness_sliver2_xuniform` proves an `O(√ε)` rate for the
  DIAGONAL second-field-derivative census.  Its Hessian-slice core is the banked diagonal cancellation
  `GaussianHessianCancel.gaussian_hessian_cancel`:
      `|∫_z ((zᵢ)²−2t)/(4t²)·G_t(z)·q(z)| ≤ L·(15/2·n)/√t`
  which subtracts `q(0)` using the EXACT diagonal cancellation `∫_z ((zᵢ)²−2t)/(4t²)·G_t = 0` (Hermite
  second moment `2t` minus mass-one `2t`), turning the `1/t` divergence into an integrable Lipschitz
  `τ^{−1/2}` gain.

  The MIXED (`i ≠ j`) second partial of the flat product Gaussian is
      `∂ᵢ∂ⱼ G_t(z) = (zᵢ·zⱼ)/(4t²)·G_t(z)`
  (each factor `∂ⱼ` contributes `−zⱼ/(2t)`; no `−2t` Hermite subtraction appears because the two
  directions are distinct).  Its leading Gaussian moment vanishes NOT by a Hermite subtraction but by
  PARITY:  `∫_z zᵢ·zⱼ·G_t = 0` for `i ≠ j` (the coordinate `i,j` first moments each vanish — the odd
  factorization of `gaussianMoment_diag`).  THIS is the cleaner cancellation flagged in the J4-780
  audit, and it is the sole genuinely-new analytic ingredient the mixed-direction `√ε` sliver needs
  beyond the diagonal machinery.  (Working the mixed normal form DIRECTLY, with the coordinate-aligned
  jets `Pi ≈ eᵢ`, `Pj ≈ eⱼ`, avoids the polarized non-aligned directions `Pi±Pj` of the polarization
  route `MixedSliverPolarization` entirely; the subleading remainders `⟨V,Pi⟩⟨V,Pj⟩ − zᵢzⱼ` are
  higher-order and go through the EXISTING magnitude-domination bricks with the aligned `hJ3`.)

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (ns `QIQTH.HeatResidualBound`, extending `GaussianHessianCancel`).

    • `gaussian_hessian_moment_zero_mixed` — ★ THE PARITY CANCELLATION IDENTITY.  For `t>0`, `i ≠ j`,
        `∫_z (zᵢ·zⱼ)/(4t²)·G_t(z) = 0`.  (From `gaussianMoment_diag`'s `2t·δᵢⱼ = 0`.)
    • `absMixed_coord_gaussDdim_integrable` — `|zᵢ·zⱼ/(4t²)|·G_t·|z_k|` is integrable.
    • `absMixed_coord_integral_le` — the per-coordinate bound `∫_z |zᵢ·zⱼ/(4t²)|·G_t·|z_k| ≤ 1/√t`
        (coordinatewise factorization; the worst case is `k ∉ {i,j}`, giving `(27/32)/√t ≤ 1/√t`).
    • `coordMul_gaussDdim_integrable_ne` — `(zᵢ·zⱼ)·G_t` integrable for `i ≠ j`.
    • `gaussian_hessian_cancel_mixed` — ★★ THE MIXED CANCELLATION LEMMA.  For `t>0`, `i ≠ j`, `q`
        Lipschitz (`L ≥ 0`, bounded, measurable):
          `|∫_z (zᵢ·zⱼ)/(4t²)·G_t(z)·q(z)| ≤ L·n/√t`.
        Same subtract-`q(0)` proof as the diagonal, with the parity moment-zero in place of the Hermite
        cancellation and the per-coordinate `1/√t` bound in place of `(15/2)/√t`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  reusable analytic BRICK: the mixed-index parity analogue of the banked diagonal Hessian cancellation.
  The Lipschitz/boundedness/measurability hypotheses on `q` are genuine, load-bearing, non-vacuous (the
  bound FAILS without them; the same width-2 Gaussian model that satisfies the diagonal bricks satisfies
  these); `i ≠ j` is load-bearing (at `i = j` the parity moment is `2t ≠ 0`, and one recovers the
  DIAGONAL `−2t` Hermite subtraction instead).  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.  `a₁ = R/6` remains
  CONDITIONAL.
-/
import Mathlib
import QIQTH.GaussianHessianCancel

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1-D integrability workhorses for the mixed weight. -/

/-- `heatKernel1D t · (|y|·|y|)` is integrable (`= heatKernel1D t · y²`). -/
theorem hk_absY_sq_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℝ => heatKernel1D t y * (|y| * |y|)) volume := by
  have heq : (fun y : ℝ => heatKernel1D t y * (|y| * |y|))
      = fun y => heatKernel1D t y * (y ^ 2) ^ 1 := by
    funext y; rw [pow_one, pow_two, abs_mul_abs_self]
  rw [heq]; exact hk_mul_sq_pow_integrable t ht 1

/-- `∫ heatKernel1D t · (|y|·|y|) = 2t` (the second moment, written with `|y|·|y| = y²`). -/
theorem hk_absY_sq_moment (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * (|y| * |y|) = 2 * t := by
  rw [show (fun y : ℝ => heatKernel1D t y * (|y| * |y|))
        = fun y => heatKernel1D t y * y ^ 2 from by
      funext y; rw [abs_mul_abs_self, pow_two]]
  exact gaussianSecondMoment_oneD t ht

/-- `heatKernel1D t · y` is integrable (dominated by `heatKernel1D t · |y|`). -/
theorem hk_mul_id_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℝ => heatKernel1D t y * y) volume := by
  refine (hk_absY_integrable t ht).mono'
    ((hk_continuous t).mul continuous_id).aestronglyMeasurable (ae_of_all _ (fun y => ?_))
  exact le_of_eq (by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel1D_pos t y ht).le])

/-! ### The parity cancellation identity. -/

/-- **(★ PARITY) THE MIXED CANCELLATION IDENTITY.**  For `t>0` and `i ≠ j`,
    `∫_z (zᵢ·zⱼ)/(4t²)·G_t(z) = 0`.  The `2t·δᵢⱼ` diagonal moment `gaussianMoment_diag` vanishes
    off-diagonal (the coordinate `i` and `j` first moments each integrate to `0` by oddness). -/
theorem gaussian_hessian_moment_zero_mixed (t : ℝ) (ht : 0 < t) (i j : Fin n) (hij : i ≠ j) :
    ∫ z : Point n, (z i * z j) / (4 * t ^ 2) * gaussDdim t z = 0 := by
  have hmix : (∫ z : Point n, (z i * z j) * gaussDdim t z) = 0 := by
    have h := gaussianMoment_diag n t ht i j
    rw [if_neg hij, mul_zero] at h
    rw [← h]
    refine integral_congr_ae (ae_of_all _ (fun z => ?_))
    simp only [gaussDdim]; ring
  have hAeq : (fun z : Point n => (z i * z j) / (4 * t ^ 2) * gaussDdim t z)
      = fun z => (4 * t ^ 2)⁻¹ * ((z i * z j) * gaussDdim t z) := by
    funext z; rw [div_eq_mul_inv]; ring
  rw [hAeq, integral_const_mul, hmix, mul_zero]

/-! ### Per-coordinate integrability + bound. -/

/-- `(zᵢ·zⱼ)·G_t(z)` is integrable on `Point n` for `i ≠ j`. -/
theorem coordMul_gaussDdim_integrable_ne (t : ℝ) (ht : 0 < t) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun z : Point n => (z i * z j) * gaussDdim t z) volume := by
  have hpt : (fun z : Point n => (z i * z j) * gaussDdim t z)
      = fun z => ∏ m, heatKernel1D t (z m)
          * ((if m = i then z m else 1) * (if m = j then z m else 1)) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
    ring
  have hf : ∀ m : Fin n,
      Integrable (fun y : ℝ => heatKernel1D t y
        * ((if m = i then y else 1) * (if m = j then y else 1))) volume := by
    intro m
    by_cases hmi : m = i
    · have hmj : m ≠ j := by rintro rfl; exact hij hmi.symm
      simp only [if_pos hmi, if_neg hmj, mul_one]
      exact hk_mul_id_integrable t ht
    · by_cases hmj : m = j
      · simp only [if_neg hmi, if_pos hmj, one_mul]
        exact hk_mul_id_integrable t ht
      · simp only [if_neg hmi, if_neg hmj, mul_one]
        exact heatKernel1D_integrable t ht
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-- The product form of the mixed absolute weight (shared by the integrability and the bound). -/
theorem absMixed_prod_form (t : ℝ) (i j k : Fin n) (z : Point n) :
    |z i * z j / (4 * t ^ 2)| * gaussDdim t z * |z k|
      = (4 * t ^ 2)⁻¹ * ∏ m, heatKernel1D t (z m)
          * ((if m = i then |z m| else 1) * (if m = j then |z m| else 1)
              * (if m = k then |z m| else 1)) := by
  simp only [gaussDdim]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Fintype.prod_ite_eq', Fintype.prod_ite_eq', Fintype.prod_ite_eq',
      abs_div, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 4 * t ^ 2 by positivity)]
  ring

/-- Per-factor integrability of the mixed absolute weight (`i ≠ j`). -/
theorem absMixed_factor_integrable (t : ℝ) (ht : 0 < t) (i j k m : Fin n) (hij : i ≠ j) :
    Integrable (fun y : ℝ => heatKernel1D t y
      * ((if m = i then |y| else 1) * (if m = j then |y| else 1) * (if m = k then |y| else 1)))
      volume := by
  by_cases hmi : m = i
  · have hmj : m ≠ j := by rintro rfl; exact hij hmi.symm
    by_cases hmk : m = k
    · simp only [if_pos hmi, if_neg hmj, if_pos hmk, one_mul, mul_one]
      exact hk_absY_sq_integrable t ht
    · simp only [if_pos hmi, if_neg hmj, if_neg hmk, one_mul, mul_one]
      exact hk_absY_integrable t ht
  · by_cases hmj : m = j
    · by_cases hmk : m = k
      · simp only [if_neg hmi, if_pos hmj, if_pos hmk, one_mul, mul_one]
        exact hk_absY_sq_integrable t ht
      · simp only [if_neg hmi, if_pos hmj, if_neg hmk, one_mul, mul_one]
        exact hk_absY_integrable t ht
    · by_cases hmk : m = k
      · simp only [if_neg hmi, if_neg hmj, if_pos hmk, one_mul, mul_one]
        exact hk_absY_integrable t ht
      · simp only [if_neg hmi, if_neg hmj, if_neg hmk, one_mul, mul_one]
        exact heatKernel1D_integrable t ht

/-- `|zᵢ·zⱼ/(4t²)|·G_t(z)·|z_k|` is integrable on `Point n` (`i ≠ j`). -/
theorem absMixed_coord_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i j k : Fin n) (hij : i ≠ j) :
    Integrable
      (fun z : Point n => |z i * z j / (4 * t ^ 2)| * gaussDdim t z * |z k|) volume := by
  rw [show (fun z : Point n => |z i * z j / (4 * t ^ 2)| * gaussDdim t z * |z k|)
        = fun z => (4 * t ^ 2)⁻¹ * ∏ m, heatKernel1D t (z m)
            * ((if m = i then |z m| else 1) * (if m = j then |z m| else 1)
                * (if m = k then |z m| else 1)) from
      funext (fun z => absMixed_prod_form t i j k z)]
  apply Integrable.const_mul
  rw [show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ))
    (fun m => absMixed_factor_integrable t ht i j k m hij)

/-- Product of a two-point `ite` function over `univ` (`i ≠ j`). -/
theorem prod_two_ite (a b : ℝ) (i j : Fin n) (hij : i ≠ j) :
    ∏ m : Fin n, (if m = i then a else if m = j then b else 1) = a * b := by
  have hout : ∀ m ∈ (Finset.univ : Finset (Fin n)), m ∉ ({i, j} : Finset (Fin n)) →
      (if m = i then a else if m = j then b else 1) = 1 := by
    intro m _ hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm; push_neg at hm
    rw [if_neg hm.1, if_neg hm.2]
  rw [← Finset.prod_subset (Finset.subset_univ ({i, j} : Finset (Fin n))) hout,
      Finset.prod_pair hij, if_pos rfl, if_neg (fun h => hij h.symm), if_pos rfl]

/-- Product of a three-point `ite` function over `univ` (`i,j,k` distinct). -/
theorem prod_three_ite (a b c : ℝ) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∏ m : Fin n, (if m = i then a else if m = j then b else if m = k then c else 1) = a * b * c := by
  have hout : ∀ m ∈ (Finset.univ : Finset (Fin n)), m ∉ ({i, j, k} : Finset (Fin n)) →
      (if m = i then a else if m = j then b else if m = k then c else 1) = 1 := by
    intro m _ hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm; push_neg at hm
    rw [if_neg hm.1, if_neg hm.2.1, if_neg hm.2.2]
  rw [← Finset.prod_subset (Finset.subset_univ ({i, j, k} : Finset (Fin n))) hout,
      Finset.prod_insert (by simp [hij, hik]), Finset.prod_insert (by simp [hjk]),
      Finset.prod_singleton, if_pos rfl, if_neg (fun h => hij h.symm), if_pos rfl,
      if_neg (fun h => hik h.symm), if_neg (fun h => hjk h.symm), if_pos rfl]
  ring

/-- **(★ n-D) THE PER-COORDINATE BOUND.**  For `t>0`, `i ≠ j`, and any `k`,
    `∫_z |zᵢ·zⱼ/(4t²)|·G_t(z)·|z_k| ≤ 1/√t`.  Factorizes coordinatewise: the `k=i`/`k=j` cases give
    `(2t)·(3/2·√t)/(4t²) = (3/4)/√t`; the `k ∉ {i,j}` case gives `(3/2·√t)³/(4t²) = (27/32)/√t`; both
    `≤ 1/√t`. -/
theorem absMixed_coord_integral_le (t : ℝ) (ht : 0 < t) (i j k : Fin n) (hij : i ≠ j) :
    ∫ z : Point n, |z i * z j / (4 * t ^ 2)| * gaussDdim t z * |z k|
      ≤ 1 / Real.sqrt t := by
  -- constants and moments
  set Iabs : ℝ := ∫ y : ℝ, heatKernel1D t y * |y| with hIabs
  have hIabs_nn : 0 ≤ Iabs :=
    integral_nonneg (fun y => mul_nonneg (heatKernel1D_pos t y ht).le (abs_nonneg _))
  have hIabs_le : Iabs ≤ 3 / 2 * Real.sqrt t := hk_absY_moment_le t ht
  have hIsq : (∫ y : ℝ, heatKernel1D t y * (|y| * |y|)) = 2 * t := hk_absY_sq_moment t ht
  have hwpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hwsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have h4t2 : (0 : ℝ) < 4 * t ^ 2 := by positivity
  -- arithmetic fold: `V·√t ≤ 4t²  ⟹  (4t²)⁻¹·V ≤ 1/√t`.
  have hfold : ∀ V : ℝ, V * Real.sqrt t ≤ 4 * t ^ 2 → (4 * t ^ 2)⁻¹ * V ≤ 1 / Real.sqrt t := by
    intro V hVle
    have hVdiv : V ≤ 4 * t ^ 2 / Real.sqrt t := (le_div_iff₀ hwpos).mpr hVle
    calc (4 * t ^ 2)⁻¹ * V ≤ (4 * t ^ 2)⁻¹ * (4 * t ^ 2 / Real.sqrt t) :=
          mul_le_mul_of_nonneg_left hVdiv (by positivity)
      _ = 1 / Real.sqrt t := by rw [mul_div_assoc', inv_mul_cancel₀ h4t2.ne']
  -- factorize the integral into a product of 1-D integrals
  rw [funext (fun z => absMixed_prod_form t i j k z),
      integral_const_mul,
      integral_fintype_prod_volume_eq_prod (fun m (y : ℝ) => heatKernel1D t y
        * ((if m = i then |y| else 1) * (if m = j then |y| else 1) * (if m = k then |y| else 1)))]
  -- reduce each factor to its clean value (using `i ≠ j`).
  by_cases hki : k = i
  · -- k = i: support {i,j}, product = (∫G|y|²)·(∫G|y|) = 2t·Iabs
    have hcongr : (∏ m : Fin n, ∫ y : ℝ, heatKernel1D t y
          * ((if m = i then |y| else 1) * (if m = j then |y| else 1) * (if m = k then |y| else 1)))
        = ∏ m : Fin n, (if m = i then (2 * t) else if m = j then Iabs else 1) := by
      refine Finset.prod_congr rfl (fun m _ => ?_)
      simp only [hki]
      by_cases hmi : m = i
      · have hmj : m ≠ j := by rintro rfl; exact hij hmi.symm
        simp only [if_pos hmi, if_neg hmj, one_mul, mul_one]; exact hIsq
      · by_cases hmj : m = j
        · simp only [if_neg hmi, if_pos hmj, one_mul, mul_one, hIabs]
        · simp only [if_neg hmi, if_neg hmj, mul_one]; exact gaussianZerothMoment_oneD t ht
    rw [hcongr, prod_two_ite (2 * t) Iabs i j hij]
    refine hfold ((2 * t) * Iabs) ?_
    have h1 : (2 * t) * Iabs * Real.sqrt t ≤ (2 * t) * (3 / 2 * Real.sqrt t) * Real.sqrt t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIabs_le (by positivity)) hwpos.le
    refine h1.trans ?_
    have h2 : (2 * t) * (3 / 2 * Real.sqrt t) * Real.sqrt t = 3 * t * (Real.sqrt t * Real.sqrt t) := by
      ring
    rw [h2, hwsq]; nlinarith [sq_nonneg t, ht.le]
  · by_cases hkj : k = j
    · -- k = j: support {i,j}, product = Iabs·(2t)
      have hcongr : (∏ m : Fin n, ∫ y : ℝ, heatKernel1D t y
            * ((if m = i then |y| else 1) * (if m = j then |y| else 1) * (if m = k then |y| else 1)))
          = ∏ m : Fin n, (if m = i then Iabs else if m = j then (2 * t) else 1) := by
        refine Finset.prod_congr rfl (fun m _ => ?_)
        simp only [hkj]
        by_cases hmi : m = i
        · have hmj : m ≠ j := by rintro rfl; exact hij hmi.symm
          simp only [if_pos hmi, if_neg hmj, one_mul, mul_one, hIabs]
        · by_cases hmj : m = j
          · simp only [if_neg hmi, if_pos hmj, one_mul, mul_one]; exact hIsq
          · simp only [if_neg hmi, if_neg hmj, mul_one]; exact gaussianZerothMoment_oneD t ht
      rw [hcongr, prod_two_ite Iabs (2 * t) i j hij]
      refine hfold (Iabs * (2 * t)) ?_
      have h1 : Iabs * (2 * t) * Real.sqrt t ≤ (3 / 2 * Real.sqrt t) * (2 * t) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hIabs_le (by positivity)) hwpos.le
      refine h1.trans ?_
      have h2 : (3 / 2 * Real.sqrt t) * (2 * t) * Real.sqrt t = 3 * t * (Real.sqrt t * Real.sqrt t) := by
        ring
      rw [h2, hwsq]; nlinarith [sq_nonneg t, ht.le]
    · -- k ∉ {i,j}: support {i,j,k}, product = Iabs·Iabs·Iabs
      have hki' : i ≠ k := fun h => hki h.symm
      have hkj' : j ≠ k := fun h => hkj h.symm
      have hcongr : (∏ m : Fin n, ∫ y : ℝ, heatKernel1D t y
            * ((if m = i then |y| else 1) * (if m = j then |y| else 1) * (if m = k then |y| else 1)))
          = ∏ m : Fin n, (if m = i then Iabs else if m = j then Iabs else if m = k then Iabs else 1) := by
        refine Finset.prod_congr rfl (fun m _ => ?_)
        by_cases hmi : m = i
        · have hmj : m ≠ j := by rintro rfl; exact hij hmi.symm
          have hmk : m ≠ k := by rintro rfl; exact hki' hmi.symm
          simp only [if_pos hmi, if_neg hmj, if_neg hmk, one_mul, mul_one, hIabs]
        · by_cases hmj : m = j
          · have hmk : m ≠ k := by rintro rfl; exact hkj' hmj.symm
            simp only [if_neg hmi, if_pos hmj, if_neg hmk, one_mul, mul_one, hIabs]
          · by_cases hmk : m = k
            · simp only [if_neg hmi, if_neg hmj, if_pos hmk, one_mul, mul_one, hIabs]
            · simp only [if_neg hmi, if_neg hmj, if_neg hmk, mul_one]
              exact gaussianZerothMoment_oneD t ht
      rw [hcongr, prod_three_ite Iabs Iabs Iabs i j k hij hki' hkj']
      refine hfold (Iabs * Iabs * Iabs) ?_
      -- (Iabs³)·√t ≤ ((3/2)√t)³·√t = 27/8·t² ≤ 4t²
      have hcube : Iabs * Iabs * Iabs
          ≤ (3 / 2 * Real.sqrt t) * (3 / 2 * Real.sqrt t) * (3 / 2 * Real.sqrt t) :=
        mul_le_mul (mul_le_mul hIabs_le hIabs_le hIabs_nn (by positivity)) hIabs_le hIabs_nn
          (by positivity)
      have h1 : (Iabs * Iabs * Iabs) * Real.sqrt t
          ≤ ((3 / 2 * Real.sqrt t) * (3 / 2 * Real.sqrt t) * (3 / 2 * Real.sqrt t)) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right hcube hwpos.le
      refine h1.trans ?_
      have h2 : ((3 / 2 * Real.sqrt t) * (3 / 2 * Real.sqrt t) * (3 / 2 * Real.sqrt t)) * Real.sqrt t
          = 27 / 8 * (Real.sqrt t * Real.sqrt t) * (Real.sqrt t * Real.sqrt t) := by ring
      rw [h2, hwsq]; nlinarith [sq_nonneg t, ht.le]

/-! ### The mixed cancellation lemma. -/

/-- `(zᵢ·zⱼ)/(4t²)·G_t(z)` is integrable on `Point n` (`i ≠ j`). -/
theorem coordMulHess_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun z : Point n => (z i * z j) / (4 * t ^ 2) * gaussDdim t z) volume := by
  rw [show (fun z : Point n => (z i * z j) / (4 * t ^ 2) * gaussDdim t z)
        = fun z => (4 * t ^ 2)⁻¹ * ((z i * z j) * gaussDdim t z) from by
      funext z; rw [div_eq_mul_inv]; ring]
  exact (coordMul_gaussDdim_integrable_ne t ht i j hij).const_mul _

/-- **★★ THE GAUSSIAN MIXED-HESSIAN CANCELLATION LEMMA.**  For `t>0`, `i ≠ j`, and `q` Lipschitz with
    constant `L ≥ 0` (bounded, measurable),
      `|∫_z (zᵢ·zⱼ)/(4t²)·G_t(z)·q(z)| ≤ L·n/√t`.
    Proof: subtract `q 0` via the PARITY cancellation `gaussian_hessian_moment_zero_mixed`, then
    `|∫ …·(q−q 0)| ≤ ∫ ‖…‖ ≤ ∫ L·Σₖ |zᵢzⱼ/(4t²)|·G·|z_k| = L·Σₖ(…) ≤ L·(n·1/√t)/√t` via the
    per-coordinate bound `absMixed_coord_integral_le`.  Evaluated at the origin (the RNC center).  The
    EXACT off-diagonal companion of `gaussian_hessian_cancel`. -/
theorem gaussian_hessian_cancel_mixed (t : ℝ) (ht : 0 < t) (i j : Fin n) (hij : i ≠ j)
    (q : Point n → ℝ) (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) (hqbdd : ∃ M, ∀ z, |q z| ≤ M) :
    |∫ z : Point n, (z i * z j) / (4 * t ^ 2) * gaussDdim t z * q z|
      ≤ L * n / Real.sqrt t := by
  obtain ⟨M, hM⟩ := hqbdd
  have hHessG_int : Integrable
      (fun z : Point n => (z i * z j) / (4 * t ^ 2) * gaussDdim t z) volume :=
    coordMulHess_gaussDdim_integrable t ht i j hij
  have hHessGq_int : Integrable
      (fun z : Point n => (z i * z j) / (4 * t ^ 2) * gaussDdim t z * q z) volume :=
    hHessG_int.mul_bdd hqmeas (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hM z))
  have hHessGq0_int : Integrable
      (fun z : Point n => (z i * z j) / (4 * t ^ 2) * gaussDdim t z * q 0) volume :=
    hHessG_int.mul_const (q 0)
  have hred : (∫ z : Point n, (z i * z j) / (4 * t ^ 2) * gaussDdim t z * q z)
      = ∫ z : Point n, (z i * z j) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0) := by
    have hsub : (∫ z : Point n, (z i * z j) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0))
        = (∫ z : Point n, (z i * z j) / (4 * t ^ 2) * gaussDdim t z * q z)
          - ∫ z : Point n, (z i * z j) / (4 * t ^ 2) * gaussDdim t z * q 0 := by
      rw [← integral_sub hHessGq_int hHessGq0_int]
      refine integral_congr_ae (ae_of_all _ (fun z => ?_)); ring
    rw [hsub, integral_mul_const, gaussian_hessian_moment_zero_mixed t ht i j hij, zero_mul, sub_zero]
  have hbound_pt : ∀ z : Point n,
      ‖(z i * z j) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0)‖
        ≤ ∑ k, L * (|z i * z j / (4 * t ^ 2)| * gaussDdim t z * |z k|) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gaussDdim_nonneg' t z)]
    have hdist : |q z - q 0| ≤ L * ∑ k, |z k| := by
      refine (hq z 0).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [dist_pi_le_iff (Finset.sum_nonneg (fun k _ => abs_nonneg _))]
      intro j'
      rw [Real.dist_eq]
      simp only [Pi.zero_apply, sub_zero]
      exact Finset.single_le_sum (f := fun k => |z k|) (fun k _ => abs_nonneg (z k))
        (Finset.mem_univ j')
    calc |z i * z j / (4 * t ^ 2)| * gaussDdim t z * |q z - q 0|
        ≤ |z i * z j / (4 * t ^ 2)| * gaussDdim t z * (L * ∑ k, |z k|) :=
          mul_le_mul_of_nonneg_left hdist
            (mul_nonneg (abs_nonneg _) (gaussDdim_nonneg' t z))
      _ = ∑ k, L * (|z i * z j / (4 * t ^ 2)| * gaussDdim t z * |z k|) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => by ring)
  have hB_int : Integrable
      (fun z : Point n => ∑ k, L * (|z i * z j / (4 * t ^ 2)| * gaussDdim t z * |z k|)) volume :=
    integrable_finsetSum _
      (fun k _ => (absMixed_coord_gaussDdim_integrable t ht i j k hij).const_mul L)
  rw [hred]
  calc |∫ z : Point n, (z i * z j) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0)|
      = ‖∫ z : Point n, (z i * z j) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z : Point n, ‖(z i * z j) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z : Point n, ∑ k, L * (|z i * z j / (4 * t ^ 2)| * gaussDdim t z * |z k|) :=
        integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hB_int
          (ae_of_all _ hbound_pt)
    _ = ∑ k, L * ∫ z : Point n, |z i * z j / (4 * t ^ 2)| * gaussDdim t z * |z k| := by
        rw [integral_finsetSum _
          (fun k _ => (absMixed_coord_gaussDdim_integrable t ht i j k hij).const_mul L)]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [integral_const_mul]
    _ ≤ ∑ _k : Fin n, L * (1 / Real.sqrt t) :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (absMixed_coord_integral_le t ht i j k hij) hL)
    _ = L * n / Real.sqrt t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.gaussian_hessian_moment_zero_mixed
#print axioms QIQTH.HeatResidualBound.absMixed_coord_integral_le
#print axioms QIQTH.HeatResidualBound.gaussian_hessian_cancel_mixed
