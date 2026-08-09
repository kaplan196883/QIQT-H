/-
  GaussianMomentExtraction — J4-498: the Gaussian 0/1/2-moment EXTRACTION library.

  WHAT IS DERIVED HERE (the honest boundary — read it).
  The reusable COEFFICIENT tool behind the a₁ = R/6 endgame.  The J4-497 q-audit found that the
  banked O(1/τ) heat-trace remainder is coefficient-INSUFFICIENT: the leading source must be
  EXTRACTED, not bounded.  The banked `gaussian_hessian_cancel` (in `GaussianHessianCancel`) only
  *bounds* `|∫ ∂ᵢ²G_t·q| ≤ L·C/√t → 0`; it discharges the cancellation but throws the coefficient
  away.  This file supplies the complementary EXTRACTION: the exact 0/1/2-moment identities that turn
  a degree-≤2 Taylor polynomial `B` into its value + Laplacian source at the Gaussian center `0`.

  The three base moments of the width-`t` flat product Gaussian `G_t = gaussDdim t`
  (`G_t(z) = ∏ₖ heatKernel1D t (z k)`, centered at the origin, variance `2t` per coordinate):
    • (M0) MASS ONE          `∫_z G_t = 1`                         (re-exported `gaussDdim_mass_one`);
    • (M1) ODDNESS           `∫_z z_i·G_t = 0`                     (`gaussDdim_first_moment_zero`);
    • (M2) SECOND MOMENT     `∫_z (z_i·z_j)·G_t = 2t·δ_{ij}`       (re-exported `gaussianMoment_diag`).

  THE EXTRACTION (Sol #22 step-4 algebraic heart — the `tr(D²H₀(0))` extraction via `∫z_iz_j G=2τδ`):
    • (★) `quadForm_gauss_second_moment` — for a symmetric-or-not coefficient family `H`,
              `∫_z G_t(z)·(∑_{j,k} H_{jk}·z_j z_k) = 2t·∑_j H_{jj}`.
          Since the quadratic `Q(z)=∑_{jk}H_{jk}z_jz_k` has constant Hessian `D²Q = H + Hᵀ` with
          `tr(D²Q) = 2∑_j H_{jj}`, this reads `∫ G_t·Q = t·tr(D²Q(0))`: the leading `O(t)` COEFFICIENT
          is exactly the trace of the Hessian (the Laplacian source `ΔQ`), EXTRACTED not bounded.
    • (★) `poly2_gauss_extraction` — the full degree-≤2 EXTRACTION corollary,
              `∫_z G_t(z)·(c + ∑_j b_j z_j + ∑_{jk} H_{jk} z_j z_k) = c + 2t·∑_j H_{jj}`,
          i.e. `∫ G_t·B = B(0) + t·tr(D²B(0))`: the constant survives (M0), the linear part is killed
          (M1 oddness), the quadratic part contributes the `t·ΔB(0)` source (M2).  Hence
          `(∫ G_t·B − B(0))/t = tr(D²B(0))` EXACTLY for every `t>0`.  This is the coefficient
          mechanism the q-audit says must be computed.

  ⚠ HONEST FIREWALL.
    LANDED: M0/M1/M2 in `gaussDdim` form, and the two EXTRACTION identities — UNCONDITIONALLY, EXACTLY
      (no limit, no filter), for the flat product Gaussian at the origin.  These are EXACT identities
      valid for every `t>0`; the statement `(∫ G_t·B − B(0))/t = tr(D²B(0))` is a genuine equality for
      a degree-≤2 polynomial `B`, not a τ→0 asymptotic.
    DELIBERATE SCOPE (deferred to J4-499, the E(τ) assembly): the general-`B` version — for a smooth
      `B` with a uniform 2nd-order Taylor remainder `r=o(t)`, `(∫ G_t·B − B(0))/t → tr(D²B(0))` as
      `t→0⁺` — requires a delta-family limit on the remainder and is NOT proved here.  We provide the
      EXACT polynomial core; the remainder-control step is the honest remaining gap.
    NOT built here: the per-coordinate `∫ ∂ᵢ²G_t·B → ∂ᵢ²B(0)` (the 4th-moment / by-parts route);
      the TRACE (sum over `i` of that) is what a₁ needs and is delivered directly by M2 above, so the
      4th moment is not required for the coefficient.
    This is a reusable analytic BRICK (the COEFFICIENT tool); it is NOT `a₁ = R/6`.  The value `1/6`
      is cited curved-space geometry, produced by NEITHER this file NOR the moments in it.
    No `sorry`, no new axioms, no `expRho` in statements.
-/
import Mathlib
import QIQTH.GaussianHessianCancel

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1-D linear-weight integrability workhorse. -/

/-- `heatKernel1D t · y` is integrable (dominated by `|y| ≤ 1 + y²`). -/
theorem hk_lin_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℝ => heatKernel1D t y * y) volume := by
  refine hk_mul_integrable_of_poly t ht (fun y => y) (by fun_prop) 1 1 0
    (by norm_num) (by norm_num) le_rfl (fun y => ?_)
  nlinarith [sq_nonneg (|y| - 1), sq_abs y, abs_nonneg y]

/-! ### n-D coordinate integrabilities (Fubini product factorization). -/

/-- `G_t(z)·z_i` is integrable on `Point n`. -/
theorem coord_gaussDdim_integrable_ext (t : ℝ) (ht : 0 < t) (i : Fin n) :
    Integrable (fun z : Point n => gaussDdim t z * z i) volume := by
  have hpt : (fun z : Point n => gaussDdim t z * z i)
      = fun z => ∏ m, (heatKernel1D t (z m) * (if m = i then z m else 1)) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  have hf : ∀ m : Fin n,
      Integrable (fun y : ℝ => heatKernel1D t y * (if m = i then y else 1)) volume := by
    intro m; by_cases hm : m = i
    · simp only [if_pos hm]; exact hk_lin_integrable t ht
    · simp only [if_neg hm, mul_one]; exact heatKernel1D_integrable t ht
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-- `G_t(z)·(z_i·z_k)` is integrable on `Point n`. -/
theorem coordPair_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i k : Fin n) :
    Integrable (fun z : Point n => gaussDdim t z * (z i * z k)) volume := by
  have hpt : (fun z : Point n => gaussDdim t z * (z i * z k))
      = fun z => ∏ m, (heatKernel1D t (z m)
          * ((if m = i then z m else 1) * (if m = k then z m else 1))) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq',
        Fintype.prod_ite_eq']
  have hf : ∀ m : Fin n,
      Integrable (fun y : ℝ => heatKernel1D t y
        * ((if m = i then y else 1) * (if m = k then y else 1))) volume := by
    intro m
    by_cases hmi : m = i
    · by_cases hmk : m = k
      · simp only [if_pos hmi, if_pos hmk]
        exact (hk_mul_sq_pow_integrable t ht 1).congr
          (ae_of_all _ (fun y => by ring))
      · simp only [if_pos hmi, if_neg hmk, mul_one]; exact hk_lin_integrable t ht
    · by_cases hmk : m = k
      · simp only [if_neg hmi, if_pos hmk, one_mul]; exact hk_lin_integrable t ht
      · simp only [if_neg hmi, if_neg hmk, mul_one, one_mul]; exact heatKernel1D_integrable t ht
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-! ### The three base moments (in `gaussDdim` form). -/

/-- **(M1) ODDNESS — the first moment vanishes.**  `∫_z z_i·G_t(z) = 0`.  The coordinate-`i`
    factor contributes `∫ heatKernel1D t y·y = 0` (`gaussianFirstMoment_oneD`), killing the product. -/
theorem gaussDdim_first_moment_zero (t : ℝ) (ht : 0 < t) (i : Fin n) :
    ∫ z : Point n, gaussDdim t z * z i = 0 := by
  have hpt : ∀ z : Point n, gaussDdim t z * z i
      = ∏ m, (heatKernel1D t (z m) * (if m = i then z m else 1)) := by
    intro z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  rw [integral_congr_ae (ae_of_all _ hpt),
      integral_fintype_prod_volume_eq_prod
        (fun m (y : ℝ) => heatKernel1D t y * (if m = i then y else 1))]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  show (∫ y : ℝ, heatKernel1D t y * (if i = i then y else 1)) = 0
  simp only [if_pos rfl]
  exact gaussianFirstMoment_oneD t ht

/-- **(M2) SECOND MOMENT — the `2t·δ` diagonal.**  `∫_z (z_i·z_j)·G_t(z) = 2t·δ_{ij}`.
    Re-export of `gaussianMoment_diag` in `gaussDdim` form. -/
theorem gaussDdim_second_moment (t : ℝ) (ht : 0 < t) (i j : Fin n) :
    ∫ z : Point n, gaussDdim t z * (z i * z j) = 2 * t * (if i = j then 1 else 0) := by
  simp only [gaussDdim]
  exact gaussianMoment_diag n t ht i j

/-! ### The extraction identities. -/

/-- **★ THE SECOND-MOMENT EXTRACTION (Sol #22 step-4 heart).**  For any coefficient family
    `H : Fin n → Fin n → ℝ`,
      `∫_z G_t(z)·(∑_{j,k} H_{jk}·z_j z_k) = 2t·∑_j H_{jj}`.
    The quadratic `Q(z)=∑_{jk}H_{jk}z_jz_k` has constant Hessian `D²Q = H+Hᵀ`, `tr(D²Q)=2∑_j H_{jj}`,
    so this is `∫ G_t·Q = t·tr(D²Q(0))`: the leading `O(t)` coefficient IS the Hessian trace
    (`= ΔQ`), EXTRACTED via the `2t·δ` second moment (`gaussDdim_second_moment`), not bounded. -/
theorem quadForm_gauss_second_moment (t : ℝ) (ht : 0 < t) (H : Fin n → Fin n → ℝ) :
    ∫ z : Point n, gaussDdim t z * (∑ j, ∑ k, H j k * (z j * z k))
      = 2 * t * ∑ j, H j j := by
  have hdist : ∀ z : Point n, gaussDdim t z * (∑ j, ∑ k, H j k * (z j * z k))
      = ∑ j, ∑ k, H j k * (gaussDdim t z * (z j * z k)) := by
    intro z; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
  have hint : ∀ j k : Fin n,
      Integrable (fun z : Point n => H j k * (gaussDdim t z * (z j * z k))) volume :=
    fun j k => (coordPair_gaussDdim_integrable t ht j k).const_mul (H j k)
  rw [integral_congr_ae (ae_of_all _ hdist),
      integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
  have hstep : ∀ j : Fin n,
      (∫ z : Point n, ∑ k, H j k * (gaussDdim t z * (z j * z k))) = 2 * t * H j j := by
    intro j
    rw [integral_finsetSum _ (fun k _ => hint j k)]
    have hk : ∀ k : Fin n, (∫ z : Point n, H j k * (gaussDdim t z * (z j * z k)))
        = H j k * (2 * t * (if j = k then 1 else 0)) := by
      intro k; rw [integral_const_mul, gaussDdim_second_moment t ht j k]
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_eq_single j]
    · rw [if_pos rfl]; ring
    · intro k _ hkj; rw [if_neg (fun h => hkj h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.mul_sum]

/-- **★ THE DEGREE-≤2 EXTRACTION COROLLARY.**  For a constant `c`, a gradient `b`, and a Hessian
    coefficient family `H`, the Gaussian average of `B(z) = c + ∑_j b_j z_j + ∑_{jk} H_{jk} z_j z_k` is
      `∫_z G_t(z)·B(z) = c + 2t·∑_j H_{jj}`,
    i.e. `∫ G_t·B = B(0) + t·tr(D²B(0))`.  EXACT for every `t>0`: the constant survives (mass-one M0),
    the linear part is killed (oddness M1), the quadratic part yields the `t·ΔB(0)` source (M2).  Hence
    `(∫ G_t·B − B(0))/t = tr(D²B(0))` — the extracted Laplacian coefficient. -/
theorem poly2_gauss_extraction (t : ℝ) (ht : 0 < t) (c : ℝ) (b : Fin n → ℝ)
    (H : Fin n → Fin n → ℝ) :
    ∫ z : Point n, gaussDdim t z * (c + (∑ j, b j * z j) + (∑ j, ∑ k, H j k * (z j * z k)))
      = c + 2 * t * ∑ j, H j j := by
  have hGint := gaussDdim_integrable' (n := n) t ht
  have hcint : Integrable (fun z : Point n => gaussDdim t z * c) volume := hGint.mul_const c
  have hlinint : Integrable (fun z : Point n => gaussDdim t z * (∑ j, b j * z j)) volume := by
    have he : (fun z : Point n => gaussDdim t z * (∑ j, b j * z j))
        = fun z => ∑ j, b j * (gaussDdim t z * z j) := by
      funext z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [he]
    exact integrable_finsetSum _ (fun j _ => (coord_gaussDdim_integrable_ext t ht j).const_mul (b j))
  have hquadint : Integrable
      (fun z : Point n => gaussDdim t z * (∑ j, ∑ k, H j k * (z j * z k))) volume := by
    have he : (fun z : Point n => gaussDdim t z * (∑ j, ∑ k, H j k * (z j * z k)))
        = fun z => ∑ j, ∑ k, H j k * (gaussDdim t z * (z j * z k)) := by
      funext z; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [he]
    exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun k _ => (coordPair_gaussDdim_integrable t ht j k).const_mul (H j k)))
  have hEq : (∫ z : Point n,
        gaussDdim t z * (c + (∑ j, b j * z j) + (∑ j, ∑ k, H j k * (z j * z k))))
      = ∫ z : Point n, (gaussDdim t z * c + gaussDdim t z * (∑ j, b j * z j)
          + gaussDdim t z * (∑ j, ∑ k, H j k * (z j * z k))) :=
    integral_congr_ae (ae_of_all _ (fun z => by ring))
  have hlin0 : (∫ z : Point n, gaussDdim t z * (∑ j, b j * z j)) = 0 := by
    have he : (fun z : Point n => gaussDdim t z * (∑ j, b j * z j))
        = fun z => ∑ j, b j * (gaussDdim t z * z j) := by
      funext z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [he, integral_finsetSum _ (fun j _ => (coord_gaussDdim_integrable_ext t ht j).const_mul (b j))]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [integral_const_mul, gaussDdim_first_moment_zero t ht j, mul_zero]
  have hAB : Integrable
      (fun z : Point n => gaussDdim t z * c + gaussDdim t z * (∑ j, b j * z j)) volume :=
    hcint.add hlinint
  rw [hEq, integral_add hAB hquadint, integral_add hcint hlinint]
  have hc0 : (∫ z : Point n, gaussDdim t z * c) = c := by
    rw [integral_mul_const, gaussDdim_mass_one t ht, one_mul]
  rw [hc0, hlin0, quadForm_gauss_second_moment t ht H]
  ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.gaussDdim_first_moment_zero
#print axioms QIQTH.HeatResidualBound.gaussDdim_second_moment
#print axioms QIQTH.HeatResidualBound.quadForm_gauss_second_moment
#print axioms QIQTH.HeatResidualBound.poly2_gauss_extraction
