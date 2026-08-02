/-
  SliverEstimates — J4-125: the linewise heat-sliver estimates.

  WHAT IS DERIVED HERE (the honest boundary — read it).
  The terminal `hDaLim` wall of the `a₁ = R/6` campaign requires bounding the FORMAL-derivative
  integrals of the terminal heat sliver `∫ s in (u−ε)..u, ∫ z, H(u−s,x,z)·F(s,z,0)` by `C·√ε` (or
  `C·ε`).  Building on the just-banked Gaussian-Hessian cancellation library
  (`QIQTH/GaussianHessianCancel.lean`, `gaussian_hessian_cancel`, the weighted moment bounds) and the
  boundary/convolution machinery (`gaussDdim_conv`, `gaussDdim_le_diagonal`, `B_le_MB`,
  `gaussDdim_zero_antitone`), this file proves those linewise sliver bounds:

    • (S0a)  `gaussian_grad_moment_zero` / `gaussian_grad_cancel` — the odd first-moment analogue of the
             Hessian cancellation: `∫ (zᵢ/2t)·G_t = 0`, and for `q` Lipschitz-bounded-measurable the
             gradient integral is bounded by a `t`-FREE constant `|∫ (zᵢ/2t)·G_t·q| ≤ L·(9/8·n)`
             (the gradient carries no `t`-divergence at all — better than the Hessian's `t^{−1/2}`).
    • (S0b)  `sliver_rpow` / `sliver_rpow_sub` / `sliver_bound_of_rpow` — the sliver integral
             `∫₀^ε τ^{−1/2} = 2√ε`, its `u−s` reflection, and the pointwise-bound corollary.
    • (S1)   `sliver1_zeroth_bound` — the `j = 0` sliver: for the D1-dominated `H` and width-2-dominated
             `F`, `|∫ s in (u−ε)..u, ∫ z, H(u−s) x z·F s z 0| ≤ C·ε` with `C` explicit.
    • (S2)   `sliver2_bound` — ★ THE DELIVERABLE: the formal second-`x`-derivative sliver, via the exact
             3-term Leibniz expansion `∂ᵢ²(G·A) = (∂ᵢ²G)A + 2(∂ᵢG)(∂ᵢA) + G(∂ᵢ²A)`.  Term 1 uses the
             Hessian cancellation (`τ^{−1/2}` gain, needs `Aamp·F` Lipschitz); terms 2/3 use crude
             moment bounds (no cancellation).  The sliver integral assembles to
             `≤ (L·(15/2·n) + (3/4)·M₁·C_F)·2√ε + M₂·C_F·ε`.

  ⚠ HONEST FIREWALL.
    LANDED (this file): S0a, S0b, S1, S2 — all UNCONDITIONALLY at the RNC center (spatial base handled:
      `H`/`F`/`D2H` are evaluated at `x = 0` for S2, `x` free for S1; the dominations are global).
    CARRIED (labelled deferred inputs of S1/S2, each a genuine fact, NONE the conclusion, none vacuous):
      • the D1/width-2 Gaussian dominations `hHdom`/`hFdom` (landed bounds carried parametrically);
      • for S2, the amplitude INTERFACE `hD2Hexpand` — the EXACT Leibniz 3-term shape of the `i`-th formal
        second `x`-derivative of `H` at `x = 0` (`D2H τ z = hess·G·Aamp + grad·G·A1amp + G·A2amp`),
        satisfiable by the concrete parametrix witness (this is the pointwise algebraic identity for a
        product `G·A`, not the conclusion); the amplitude bounds `hAampBdd`/`hA1ampBdd`/`hA2ampBdd`; the
        Lipschitz carry `hqLip` on the product `Aamp·F` (load-bearing ONLY for term 1's cancellation);
        and BASE measurability of the factors.
    The Lipschitz/boundedness/measurability hypotheses are genuine, load-bearing, non-vacuous (the term-1
      bound FAILS without `hqLip`; `L ≥ 0` is the standard Lipschitz-constant sign).  Reusable analytic
      BRICK; NOT `a₁ = R/6` — this discharges ONE brick (the `hDaLim` sliver estimates) of the campaign.
    No `sorry`, no new axioms, no `expRho` in statements.
-/
import Mathlib
import QIQTH.GaussianHessianCancel
import QIQTH.BoundaryAssembly

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### Foundational coordinate integrability + moment helpers (n-D factorizations). -/

/-- `|z i| · G_t(z)` is integrable on `Point n`. -/
theorem absCoord_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i : Fin n) :
    Integrable (fun z : Point n => |z i| * gaussDdim t z) volume := by
  have hpt : (fun z : Point n => |z i| * gaussDdim t z)
      = fun z => ∏ k, heatKernel1D t (z k) * (if k = i then |z k| else 1) := by
    funext z; simp only [gaussDdim]; rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']; ring
  have hf : ∀ k : Fin n,
      Integrable (fun y : ℝ => heatKernel1D t y * (if k = i then |y| else 1)) volume := by
    intro k
    by_cases hk : k = i
    · subst hk; simp only [if_pos rfl]; exact hk_absY_integrable t ht
    · simp only [if_neg hk, mul_one]; exact heatKernel1D_integrable t ht
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-- The `n`-D `|z i|`-moment factorizes to the 1-D `∫ G_t·|y| ≤ (3/2)√t`. -/
theorem absCoord_gaussDdim_integral_le (t : ℝ) (ht : 0 < t) (i : Fin n) :
    ∫ z : Point n, |z i| * gaussDdim t z ≤ 3 / 2 * Real.sqrt t := by
  have hpt : (fun z : Point n => |z i| * gaussDdim t z)
      = fun z => ∏ k, heatKernel1D t (z k) * (if k = i then |z k| else 1) := by
    funext z; simp only [gaussDdim]; rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']; ring
  rw [hpt, integral_fintype_prod_volume_eq_prod
    (fun k (y : ℝ) => heatKernel1D t y * (if k = i then |y| else 1))]
  have hprodeq : (∏ k : Fin n, ∫ y : ℝ, heatKernel1D t y * (if k = i then |y| else 1))
      = ∫ y : ℝ, heatKernel1D t y * |y| := by
    calc (∏ k : Fin n, ∫ y : ℝ, heatKernel1D t y * (if k = i then |y| else 1))
        = ∏ k : Fin n, (if k = i then (∫ y : ℝ, heatKernel1D t y * |y|) else 1) := by
          refine Finset.prod_congr rfl (fun k _ => ?_)
          by_cases hk : k = i
          · simp [hk]
          · simp only [if_neg hk, mul_one]; exact gaussianZerothMoment_oneD t ht
      _ = ∫ y : ℝ, heatKernel1D t y * |y| := Fintype.prod_ite_eq' i _
  rw [hprodeq]; exact hk_absY_moment_le t ht

/-- `z i · G_t(z)` is integrable on `Point n` (dominated by `|z i|·G_t`). -/
theorem coord_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i : Fin n) :
    Integrable (fun z : Point n => z i * gaussDdim t z) volume := by
  have hmeas : AEStronglyMeasurable (fun z : Point n => z i * gaussDdim t z) volume :=
    (continuous_apply i).aestronglyMeasurable.mul (gaussDdim_integrable' t ht).aestronglyMeasurable
  refine (absCoord_gaussDdim_integrable t ht i).mono' hmeas (ae_of_all _ (fun z => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDdim_nonneg' t z)]

/-- The `n`-D first coordinate moment vanishes: `∫ z i · G_t(z) = 0`. -/
theorem coord_gaussDdim_integral_zero (t : ℝ) (ht : 0 < t) (i : Fin n) :
    ∫ z : Point n, z i * gaussDdim t z = 0 := by
  have hpt : (fun z : Point n => z i * gaussDdim t z)
      = fun z => ∏ k, heatKernel1D t (z k) * (if k = i then z k else 1) := by
    funext z; simp only [gaussDdim]; rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']; ring
  rw [hpt, integral_fintype_prod_volume_eq_prod
    (fun k (y : ℝ) => heatKernel1D t y * (if k = i then y else 1))]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  show (∫ y : ℝ, heatKernel1D t y * (if i = i then y else 1)) = 0
  simp only [if_pos rfl]; exact gaussianFirstMoment_oneD t ht

/-- `|z i| · G_t(z) · |z k|` is integrable on `Point n`. -/
theorem absCoord_absCoord_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i k : Fin n) :
    Integrable (fun z : Point n => |z i| * gaussDdim t z * |z k|) volume := by
  have hpt : (fun z : Point n => |z i| * gaussDdim t z * |z k|)
      = fun z => ∏ m, heatKernel1D t (z m)
          * ((if m = i then |z m| else 1) * (if m = k then |z m| else 1)) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
    ring
  have hf : ∀ m : Fin n, Integrable (fun y : ℝ => heatKernel1D t y
      * ((if m = i then |y| else 1) * (if m = k then |y| else 1))) volume := by
    intro m
    by_cases hmi : m = i
    · by_cases hmk : m = k
      · simp only [if_pos hmi, if_pos hmk]
        have hcong : (fun y : ℝ => heatKernel1D t y * (|y| * |y|))
            = (fun y : ℝ => heatKernel1D t y * y ^ 2) := by
          funext y; rw [abs_mul_abs_self]; ring
        rw [hcong]
        exact (hk_mul_sq_pow_integrable t ht 1).congr (ae_of_all _ (fun y => by simp))
      · simp only [if_pos hmi, if_neg hmk, mul_one]; exact hk_absY_integrable t ht
    · by_cases hmk : m = k
      · simp only [if_neg hmi, if_pos hmk, one_mul]; exact hk_absY_integrable t ht
      · simp only [if_neg hmi, if_neg hmk, mul_one, one_mul]; exact heatKernel1D_integrable t ht
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-- The `n`-D double absolute-coordinate moment `∫ |z i|·G_t·|z k| ≤ (9/4)·t` (`t`-linear). -/
theorem absCoord_absCoord_integral_le (t : ℝ) (ht : 0 < t) (i k : Fin n) :
    ∫ z : Point n, |z i| * gaussDdim t z * |z k| ≤ 9 / 4 * t := by
  have hpt : (fun z : Point n => |z i| * gaussDdim t z * |z k|)
      = fun z => ∏ m, heatKernel1D t (z m)
          * ((if m = i then |z m| else 1) * (if m = k then |z m| else 1)) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
    ring
  rw [hpt, integral_fintype_prod_volume_eq_prod
    (fun m (y : ℝ) => heatKernel1D t y * ((if m = i then |y| else 1) * (if m = k then |y| else 1)))]
  by_cases hik : k = i
  · subst hik
    have hprodeq : (∏ m : Fin n, ∫ y : ℝ,
          heatKernel1D t y * ((if m = k then |y| else 1) * (if m = k then |y| else 1)))
        = ∫ y : ℝ, heatKernel1D t y * (|y| * |y|) := by
      calc (∏ m : Fin n, ∫ y : ℝ,
            heatKernel1D t y * ((if m = k then |y| else 1) * (if m = k then |y| else 1)))
          = ∏ m : Fin n, (if m = k then (∫ y : ℝ, heatKernel1D t y * (|y| * |y|)) else 1) := by
            refine Finset.prod_congr rfl (fun m _ => ?_)
            by_cases hm : m = k
            · simp [hm]
            · simp only [if_neg hm, one_mul, mul_one]; exact gaussianZerothMoment_oneD t ht
        _ = ∫ y : ℝ, heatKernel1D t y * (|y| * |y|) := Fintype.prod_ite_eq' k _
    rw [hprodeq]
    have hval : (∫ y : ℝ, heatKernel1D t y * (|y| * |y|)) = 2 * t := by
      rw [integral_congr_ae (ae_of_all _ (fun y =>
        show heatKernel1D t y * (|y| * |y|) = heatKernel1D t y * y ^ 2 from by
          rw [abs_mul_abs_self]; ring))]
      exact gaussianSecondMoment_oneD t ht
    rw [hval]; linarith [ht.le]
  · have hik' : i ≠ k := fun h => hik h.symm
    have hout : ∀ m ∈ (Finset.univ : Finset (Fin n)), m ∉ ({i, k} : Finset (Fin n)) →
        (if m = i then (∫ y : ℝ, heatKernel1D t y * |y|)
          else if m = k then (∫ y : ℝ, heatKernel1D t y * |y|) else 1) = 1 := by
      intro m _ hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      push_neg at hm
      simp only [if_neg hm.1, if_neg hm.2]
    have hprodeq : (∏ m : Fin n, ∫ y : ℝ,
          heatKernel1D t y * ((if m = i then |y| else 1) * (if m = k then |y| else 1)))
        = (∫ y : ℝ, heatKernel1D t y * |y|) * (∫ y : ℝ, heatKernel1D t y * |y|) := by
      have hstep : (∏ m : Fin n, ∫ y : ℝ,
            heatKernel1D t y * ((if m = i then |y| else 1) * (if m = k then |y| else 1)))
          = ∏ m : Fin n, (if m = i then (∫ y : ℝ, heatKernel1D t y * |y|)
              else if m = k then (∫ y : ℝ, heatKernel1D t y * |y|) else 1) := by
        refine Finset.prod_congr rfl (fun m _ => ?_)
        by_cases hmi : m = i
        · have hmk : ¬ m = k := by rw [hmi]; exact hik'
          simp only [if_pos hmi, if_neg hmk, mul_one]
        · by_cases hmk : m = k
          · simp only [if_neg hmi, if_pos hmk, one_mul]
          · simp only [if_neg hmi, if_neg hmk, one_mul, mul_one]; exact gaussianZerothMoment_oneD t ht
      rw [hstep, ← Finset.prod_subset (Finset.subset_univ ({i, k} : Finset (Fin n))) hout,
          Finset.prod_pair hik', if_pos rfl, if_neg hik, if_pos rfl]
    rw [hprodeq]
    have hM := hk_absY_moment_le t ht
    have hMnn : 0 ≤ ∫ y : ℝ, heatKernel1D t y * |y| :=
      integral_nonneg (fun y => mul_nonneg (heatKernel1D_pos t y ht).le (abs_nonneg _))
    calc (∫ y : ℝ, heatKernel1D t y * |y|) * (∫ y : ℝ, heatKernel1D t y * |y|)
        ≤ (3 / 2 * Real.sqrt t) * (3 / 2 * Real.sqrt t) := mul_le_mul hM hM hMnn (by positivity)
      _ = 9 / 4 * t := by
          rw [show (3 / 2 * Real.sqrt t) * (3 / 2 * Real.sqrt t)
                = 9 / 4 * (Real.sqrt t * Real.sqrt t) from by ring, Real.mul_self_sqrt ht.le]

/-! ### Coefficient-times-Gaussian integrability (gradient and Hessian). -/

/-- `(z i)/(2t)·G_t(z)` is integrable. -/
theorem gradCoeff_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i : Fin n) :
    Integrable (fun z : Point n => z i / (2 * t) * gaussDdim t z) volume := by
  have h : (fun z : Point n => z i / (2 * t) * gaussDdim t z)
      = fun z => (2 * t)⁻¹ * (z i * gaussDdim t z) := by funext z; rw [div_eq_mul_inv]; ring
  rw [h]; exact (coord_gaussDdim_integrable t ht i).const_mul _

/-- `((z i)²−2t)/(4t²)·G_t(z)` is integrable. -/
theorem hessCoeff_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i : Fin n) :
    Integrable (fun z : Point n => (z i ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z) volume := by
  have heq : (fun z : Point n => (z i ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z)
      = fun z => (4 * t ^ 2)⁻¹ * (z i ^ 2 * gaussDdim t z)
          - (4 * t ^ 2)⁻¹ * (2 * t) * gaussDdim t z := by
    funext z; rw [div_eq_mul_inv]; ring
  rw [heq]
  exact ((coordSq_gaussDdim_integrable t ht i).const_mul _).sub
    ((gaussDdim_integrable' t ht).const_mul _)

/-! ### S0a — the gradient (odd first-moment) cancellation. -/

/-- **(S0a) THE GRADIENT MOMENT VANISHES.**  `∫_z (zᵢ/2t)·G_t(z) = 0`. -/
theorem gaussian_grad_moment_zero (t : ℝ) (ht : 0 < t) (i : Fin n) :
    ∫ z : Point n, z i / (2 * t) * gaussDdim t z = 0 := by
  have h : (fun z : Point n => z i / (2 * t) * gaussDdim t z)
      = fun z => (2 * t)⁻¹ * (z i * gaussDdim t z) := by funext z; rw [div_eq_mul_inv]; ring
  rw [h, integral_const_mul, coord_gaussDdim_integral_zero t ht, mul_zero]

/-- **★ S0a — THE GAUSSIAN-GRADIENT CANCELLATION LEMMA.**  For `t>0`, `i : Fin n`, and `q` Lipschitz
    with constant `L ≥ 0` (bounded, measurable),
      `|∫_z (zᵢ/2t)·G_t(z)·q(z)| ≤ L·(9/8·n)`.
    The gradient carries NO `t`-divergence (contrast the Hessian's `t^{−1/2}`): the exact odd first
    moment lets one subtract `q 0`, and the per-coordinate integrals `∫ (|zᵢ|/2t)·G_t·|z_k| ≤ 9/8` are
    `t`-FREE.  Evaluated at the origin `x = 0` (the RNC center). -/
theorem gaussian_grad_cancel (t : ℝ) (ht : 0 < t) (i : Fin n) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) (hqbdd : ∃ M, ∀ z, |q z| ≤ M) :
    |∫ z : Point n, z i / (2 * t) * gaussDdim t z * q z| ≤ L * (9 / 8 * n) := by
  obtain ⟨M, hM⟩ := hqbdd
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have htne : t ≠ 0 := ht.ne'
  have hGradG_int : Integrable (fun z : Point n => z i / (2 * t) * gaussDdim t z) volume :=
    gradCoeff_gaussDdim_integrable t ht i
  have hGradGq_int : Integrable (fun z : Point n => z i / (2 * t) * gaussDdim t z * q z) volume :=
    hGradG_int.mul_bdd hqmeas (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hM z))
  have hGradGq0_int : Integrable (fun z : Point n => z i / (2 * t) * gaussDdim t z * q 0) volume :=
    hGradG_int.mul_const (q 0)
  have hred : (∫ z : Point n, z i / (2 * t) * gaussDdim t z * q z)
      = ∫ z : Point n, z i / (2 * t) * gaussDdim t z * (q z - q 0) := by
    have hsub : (∫ z : Point n, z i / (2 * t) * gaussDdim t z * (q z - q 0))
        = (∫ z : Point n, z i / (2 * t) * gaussDdim t z * q z)
          - ∫ z : Point n, z i / (2 * t) * gaussDdim t z * q 0 := by
      rw [← integral_sub hGradGq_int hGradGq0_int]
      refine integral_congr_ae (ae_of_all _ (fun z => ?_)); ring
    rw [hsub, integral_mul_const, gaussian_grad_moment_zero t ht i, zero_mul, sub_zero]
  have hbound_pt : ∀ z : Point n,
      ‖z i / (2 * t) * gaussDdim t z * (q z - q 0)‖
        ≤ ∑ k, L * ((1 / (2 * t)) * (|z i| * gaussDdim t z * |z k|)) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gaussDdim_nonneg' t z), abs_div,
        abs_of_pos h2t]
    have hdist : |q z - q 0| ≤ L * ∑ k, |z k| := by
      refine (hq z 0).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [dist_pi_le_iff (Finset.sum_nonneg (fun k _ => abs_nonneg _))]
      intro j; rw [Real.dist_eq]; simp only [Pi.zero_apply, sub_zero]
      exact Finset.single_le_sum (f := fun k => |z k|) (fun k _ => abs_nonneg (z k))
        (Finset.mem_univ j)
    calc |z i| / (2 * t) * gaussDdim t z * |q z - q 0|
        ≤ |z i| / (2 * t) * gaussDdim t z * (L * ∑ k, |z k|) :=
          mul_le_mul_of_nonneg_left hdist
            (mul_nonneg (div_nonneg (abs_nonneg _) h2t.le) (gaussDdim_nonneg' t z))
      _ = ∑ k, L * ((1 / (2 * t)) * (|z i| * gaussDdim t z * |z k|)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => by rw [div_eq_mul_inv]; ring)
  have hB_int : Integrable
      (fun z : Point n => ∑ k, L * ((1 / (2 * t)) * (|z i| * gaussDdim t z * |z k|))) volume :=
    integrable_finsetSum _ (fun k _ =>
      ((absCoord_absCoord_gaussDdim_integrable t ht i k).const_mul (1 / (2 * t))).const_mul L)
  rw [hred]
  calc |∫ z : Point n, z i / (2 * t) * gaussDdim t z * (q z - q 0)|
      = ‖∫ z : Point n, z i / (2 * t) * gaussDdim t z * (q z - q 0)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z : Point n, ‖z i / (2 * t) * gaussDdim t z * (q z - q 0)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z : Point n, ∑ k, L * ((1 / (2 * t)) * (|z i| * gaussDdim t z * |z k|)) :=
        integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hB_int (ae_of_all _ hbound_pt)
    _ = ∑ k, L * ((1 / (2 * t)) * ∫ z : Point n, |z i| * gaussDdim t z * |z k|) := by
        rw [integral_finsetSum _ (fun k _ =>
          ((absCoord_absCoord_gaussDdim_integrable t ht i k).const_mul (1 / (2 * t))).const_mul L)]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [integral_const_mul, integral_const_mul]
    _ ≤ ∑ _k : Fin n, L * ((1 / (2 * t)) * (9 / 4 * t)) :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (absCoord_absCoord_integral_le t ht i k)
              (by positivity)) hL)
    _ = L * (9 / 8 * n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (1 / (2 * t)) * (9 / 4 * t) = 9 / 8 from by field_simp; ring]
        ring

/-! ### S0b — the sliver rpow integral `∫₀^ε τ^{−1/2} = 2√ε`. -/

/-- `∀ᵐ x, x ≠ c` w.r.t. Lebesgue measure (single points are null). -/
theorem ae_ne_point (c : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬ x ≠ c} = {c} := by ext x; simp
  rw [hset]; exact Real.volume_singleton

/-- `(√τ)⁻¹ = τ^{−1/2}` for `τ > 0`. -/
theorem inv_sqrt_eq_rpow (τ : ℝ) (hτ : 0 < τ) : (Real.sqrt τ)⁻¹ = τ ^ (-(1 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hτ.le]
  congr 1; norm_num

/-- **(S0b) THE SLIVER RPOW INTEGRAL.**  `∫ τ in 0..ε, τ^{−1/2} = 2√ε` for `ε ≥ 0`. -/
theorem sliver_rpow (ε : ℝ) (hε : 0 ≤ ε) :
    ∫ τ in (0 : ℝ)..ε, τ ^ (-(1 : ℝ) / 2) = 2 * Real.sqrt ε := by
  rw [integral_rpow (Or.inl (show (-1 : ℝ) < -(1 : ℝ) / 2 by norm_num)),
      Real.zero_rpow (show -(1 : ℝ) / 2 + 1 ≠ 0 by norm_num), sub_zero, Real.sqrt_eq_rpow,
      show -(1 : ℝ) / 2 + 1 = 1 / (2 : ℝ) from by norm_num]
  ring

/-- Interval-integrability of the reflected sliver weight `s ↦ (u−s)^{−1/2}` on `[u−ε, u]`. -/
theorem rpow_sub_intervalIntegrable (u ε : ℝ) (_hε : 0 ≤ ε) :
    IntervalIntegrable (fun s => (u - s) ^ (-(1 : ℝ) / 2)) volume (u - ε) u := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε)
    (show (-1 : ℝ) < -(1 : ℝ) / 2 by norm_num)).comp_sub_left u
  rw [sub_zero] at h
  exact h.symm

/-- **(S0b) THE REFLECTED SLIVER.**  `∫ s in (u−ε)..u, (u−s)^{−1/2} = 2√ε`. -/
theorem sliver_rpow_sub (u ε : ℝ) (hε : 0 ≤ ε) :
    ∫ s in (u - ε)..u, (u - s) ^ (-(1 : ℝ) / 2) = 2 * Real.sqrt ε := by
  have key : ∫ s in (u - ε)..u, (u - s) ^ (-(1 : ℝ) / 2)
      = ∫ x in (u - u)..(u - (u - ε)), x ^ (-(1 : ℝ) / 2) :=
    intervalIntegral.integral_comp_sub_left (fun x => x ^ (-(1 : ℝ) / 2)) u
  rw [key, sub_self, show u - (u - ε) = ε from by ring, sliver_rpow ε hε]

/-- **(S0b) THE POINTWISE-BOUND COROLLARY.**  If `|f τ| ≤ K·τ^{−1/2}` on `Ioo 0 ε` (with `K ≥ 0` and
    `f` interval-integrable), then `|∫ τ in 0..ε, f τ| ≤ K·2√ε`. -/
theorem sliver_bound_of_rpow (ε K : ℝ) (hε : 0 ≤ ε) (_hK : 0 ≤ K) (f : ℝ → ℝ)
    (_hfii : IntervalIntegrable f volume 0 ε)
    (hf : ∀ τ ∈ Set.Ioo (0 : ℝ) ε, |f τ| ≤ K * τ ^ (-(1 : ℝ) / 2)) :
    |∫ τ in (0 : ℝ)..ε, f τ| ≤ K * (2 * Real.sqrt ε) := by
  rw [← Real.norm_eq_abs]
  calc ‖∫ τ in (0 : ℝ)..ε, f τ‖
      ≤ ∫ τ in (0 : ℝ)..ε, K * τ ^ (-(1 : ℝ) / 2) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hε ?_
          ((intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < -(1 : ℝ) / 2 by norm_num)).const_mul K)
        filter_upwards [ae_ne_point ε] with τ hτe hτmem
        have hmem : τ ∈ Set.Ioo (0 : ℝ) ε := ⟨hτmem.1, lt_of_le_of_ne hτmem.2 hτe⟩
        rw [Real.norm_eq_abs]; exact hf τ hmem
    _ = K * (2 * Real.sqrt ε) := by
        rw [intervalIntegral.integral_const_mul, sliver_rpow ε hε]

/-! ### S1 — the `j = 0` sliver bound `≤ C·ε`. -/

/-- **★ S1 — THE `j = 0` SLIVER BOUND.**  For the D1-dominated kernel `H` and the width-2-dominated
    `F`, the terminal zeroth-derivative sliver is `O(ε)`:
      `|∫ s in (u−ε)..u, ∫ z, H(u−s) x z · F s z 0| ≤ C·ε`,
    with `C = (A₀+A₁T)·√(3/2)ⁿ·C_L·gaussDdim((3/2)a) 0` explicit.  Route (mirrors `F1`/`etrunc`): the
    inner absolute integral is `≤ c·∫ gaussDdim((3/2)(u−s))(x−z)·gaussDdim(2s)(z) = c·gaussDdim(…)(x)`
    (`gaussDdim_conv`), capped `s`-uniformly by the diagonal peak + width-antitone monotonicities; then
    `norm_integral_le_of_norm_le` with a constant bound over the sliver of length `ε`.  `x` is free
    (the dominations are global).  NOT `a₁ = R/6`. -/
theorem sliver1_zeroth_bound (H F : ℝ → Point n → Point n → ℝ) (T : ℝ)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hHdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (u ε a : ℝ) (x : Point n) (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε)
    (hεa : ε < a / 2) :
    |∫ s in (u - ε)..u, ∫ z, H (u - s) x z * F s z 0|
      ≤ ((A₀ + A₁ * T) * Real.sqrt (3 / 2) ^ n * C_L * gaussDdim (3 / 2 * a) (0 : Point n)) * ε := by
  have hT0 : 0 < T := lt_of_lt_of_le ha (le_trans hau huT)
  set Cwidth : ℝ :=
    (A₀ + A₁ * T) * Real.sqrt (3 / 2) ^ n * C_L * gaussDdim (3 / 2 * a) (0 : Point n) with hCw
  have hCwnn : 0 ≤ Cwidth := by
    rw [hCw]
    exact mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hT0.le))
      (by positivity)) hC_L) (gaussDdim_nonneg' _ _)
  -- the s-uniform inner bound
  have hinner : ∀ s, 0 < u - s → u - s ≤ T → 0 < s → s ≤ T →
      |∫ z, H (u - s) x z * F s z 0| ≤ Cwidth := by
    intro s hτ hτT hs hsT
    set c : ℝ := (A₀ + A₁ * (u - s)) * Real.sqrt (3 / 2) ^ n * C_L with hc
    have hcnn : 0 ≤ c := mul_nonneg (mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hτ.le))
      (by positivity)) hC_L
    have hwpos : (0 : ℝ) < 3 / 2 * (u - s) + 2 * s := by linarith
    have hdom_int : Integrable
        (fun z => c * (gaussDdim (3 / 2 * (u - s)) (x - z) * gaussDdim (2 * s) (z - 0))) volume :=
      (gaussDdim_mul_integrable (3 / 2 * (u - s)) (2 * s) x 0).const_mul c
    calc |∫ z, H (u - s) x z * F s z 0|
        = ‖∫ z, H (u - s) x z * F s z 0‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖H (u - s) x z * F s z 0‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, c * (gaussDdim (3 / 2 * (u - s)) (x - z) * gaussDdim (2 * s) (z - 0)) := by
          refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hdom_int
            (ae_of_all _ (fun z => ?_))
          dsimp only
          rw [Real.norm_eq_abs, abs_mul]
          have hA' := hHdom (u - s) hτ x z
          have hB' := hFdom s hs hsT z 0
          calc |H (u - s) x z| * |F s z 0|
              ≤ ((A₀ + A₁ * (u - s)) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * (u - s)) (x - z))
                  * (C_L * gaussDdim (2 * s) (z - 0)) :=
                mul_le_mul hA' hB' (abs_nonneg _)
                  (mul_nonneg (mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hτ.le)) (by positivity))
                    (gaussDdim_nonneg' _ _))
            _ = c * (gaussDdim (3 / 2 * (u - s)) (x - z) * gaussDdim (2 * s) (z - 0)) := by
                rw [hc]; ring
      _ = c * ∫ z, gaussDdim (3 / 2 * (u - s)) (x - z) * gaussDdim (2 * s) (z - 0) :=
          integral_const_mul _ _
      _ = c * gaussDdim (3 / 2 * (u - s) + 2 * s) (x - 0) := by
          rw [gaussDdim_conv (3 / 2 * (u - s)) (2 * s) (by linarith) (by linarith) x 0]
      _ ≤ c * gaussDdim (3 / 2 * a) (0 : Point n) := by
          refine mul_le_mul_of_nonneg_left ?_ hcnn
          calc gaussDdim (3 / 2 * (u - s) + 2 * s) (x - 0)
              ≤ gaussDdim (3 / 2 * (u - s) + 2 * s) (0 : Point n) := gaussDdim_le_diagonal hwpos _
            _ ≤ gaussDdim (3 / 2 * a) (0 : Point n) :=
                gaussDdim_zero_antitone (by linarith) (by linarith)
      _ ≤ Cwidth := by
          rw [hCw]
          refine mul_le_mul_of_nonneg_right ?_ (gaussDdim_nonneg' _ _)
          rw [hc]
          refine mul_le_mul_of_nonneg_right ?_ hC_L
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : A₁ * (u - s) ≤ A₁ * T := mul_le_mul_of_nonneg_left (by linarith) hA₁
          linarith
  -- assemble the outer sliver
  rw [← Real.norm_eq_abs]
  calc ‖∫ s in (u - ε)..u, ∫ z, H (u - s) x z * F s z 0‖
      ≤ ∫ _s in (u - ε)..u, Cwidth := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ intervalIntegrable_const
        filter_upwards [ae_ne_point u] with s hsu hsmem
        have hs_mem : s ∈ Set.Ioo (u - ε) u := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hsu⟩
        rw [Real.norm_eq_abs]
        have hlo : u - ε > a / 2 := by linarith
        refine hinner s ?_ ?_ ?_ ?_
        · linarith [hs_mem.2]
        · linarith [hs_mem.1, hlo, huT]
        · linarith [hs_mem.1, hlo]
        · linarith [hs_mem.2, huT]
    _ = Cwidth * ε := by
        rw [intervalIntegral.integral_const, smul_eq_mul, show u - (u - ε) = ε from by ring,
          mul_comm]

/-! ### S2 — the formal second-derivative sliver (THE deliverable). -/

/-- **★★★ S2 — THE FORMAL SECOND-DERIVATIVE SLIVER BOUND.**  The `i`-th formal second-`x`-derivative
    of `H` at the RNC center, carried as `D2H` with the EXACT 3-term Leibniz expansion `hD2Hexpand`
    (`∂ᵢ²(G·A) = (∂ᵢ²G)A + 2(∂ᵢG)(∂ᵢA) + G(∂ᵢ²A)` at `x = 0`), gives a `√ε`-sliver:
      `|∫ s in (u−ε)..u, ∫ z, D2H(u−s) z · F s z 0|`
        `≤ (L·(15/2·n) + (3/4)·M₁·C_F)·2√ε + M₂·C_F·ε`,
    with `C_F = C_L·gaussDdim a 0` the `B_le_MB`-style `F`-cap.  Term 1 (Hessian) uses the exact
    cancellation `gaussian_hessian_cancel` (the `τ^{−1/2}` gain, needing `Aamp·F` Lipschitz `hqLip`);
    term 2 (gradient) uses the CRUDE odd moment `∫|z i|·G ≤ (3/2)√τ` (no cancellation); term 3 uses
    total mass one.  ⚠ CONDITIONAL on the amplitude interface (`hD2Hexpand`/amplitude bounds/`hqLip`)
    and base measurability — each a genuine fact, none the conclusion.  NOT `a₁ = R/6`. -/
theorem sliver2_bound
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (Aamp A1amp A2amp : ℝ → Point n → ℝ)
    (i : Fin n) (T τ₀ : ℝ)
    (M₀ M₁ M₂ L C_L : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hL : 0 ≤ L) (hC_L : 0 ≤ C_L)
    (u ε a : ℝ) (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεa : ε < a / 2)
    (hετ₀ : ε ≤ τ₀)
    (hD2Hexpand : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
        D2H τ z = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * Aamp τ z
          + z i / (2 * τ) * gaussDdim τ z * A1amp τ z
          + gaussDdim τ z * A2amp τ z)
    (hAampBdd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z, |Aamp τ z| ≤ M₀)
    (hA1ampBdd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z, |A1amp τ z| ≤ M₁)
    (hA2ampBdd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z, |A2amp τ z| ≤ M₂)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => Aamp τ z) volume)
    (hA1ampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A1amp τ z) volume)
    (hA2ampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A2amp τ z) volume)
    (hFmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hqLip : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ s, 0 < s → s ≤ T →
        ∀ z w : Point n, |Aamp τ z * F s z 0 - Aamp τ w * F s w 0| ≤ L * dist z w) :
    |∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z 0|
      ≤ (L * (15 / 2 * (n : ℝ)) + 3 / 4 * (M₁ * (C_L * gaussDdim a (0 : Point n)))) * (2 * Real.sqrt ε)
        + M₂ * (C_L * gaussDdim a (0 : Point n)) * ε := by
  have hT0 : 0 < T := lt_of_lt_of_le ha (le_trans hau huT)
  set C_F : ℝ := C_L * gaussDdim a (0 : Point n) with hCF_def
  have hCFnn : 0 ≤ C_F := mul_nonneg hC_L (gaussDdim_nonneg' _ _)
  -- the F cap via B_le_MB
  have hFcap : ∀ s, a / 2 ≤ s → s ≤ T → ∀ z, |F s z 0| ≤ C_F := fun s hs hsT z =>
    B_le_MB F C_L T a hC_L hFdom ha s hs hsT z
  -- the s-uniform inner bound (rpow form)
  have hinner : ∀ s, s ∈ Set.Ioo (u - ε) u →
      |∫ z, D2H (u - s) z * F s z 0|
        ≤ (L * (15 / 2 * (n : ℝ)) + 3 / 4 * (M₁ * C_F)) * (u - s) ^ (-(1 : ℝ) / 2) + M₂ * C_F := by
    intro s hsmem
    have hτpos : 0 < u - s := by linarith [hsmem.2]
    have hlo : u - ε > a / 2 := by linarith
    have hspos : 0 < s := by linarith [hsmem.1, hlo]
    have hsT : s ≤ T := by linarith [hsmem.2, huT]
    have hsa2 : a / 2 ≤ s := by linarith [hsmem.1, hlo]
    have hττ₀ : u - s < τ₀ := by linarith [hsmem.1, hετ₀]
    have hFcaps : ∀ z, |F s z 0| ≤ C_F := fun z => hFcap s hsa2 hsT z
    set τ : ℝ := u - s with hτ_def
    have hτIoo : τ ∈ Set.Ioo (0 : ℝ) τ₀ := ⟨hτpos, hττ₀⟩
    -- integrability of the three terms
    have hqbdd : ∃ M, ∀ z, |Aamp τ z * F s z 0| ≤ M :=
      ⟨M₀ * C_F, fun z => by
        rw [abs_mul]; exact mul_le_mul (hAampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₀⟩
    have hT1int : Integrable
        (fun z => (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)) volume :=
      (hessCoeff_gaussDdim_integrable τ hτpos i).mul_bdd ((hAampmeas τ).mul (hFmeas s))
        (ae_of_all _ (fun z => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hAampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₀))
    have hT2int : Integrable
        (fun z => z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)) volume :=
      (gradCoeff_gaussDdim_integrable τ hτpos i).mul_bdd ((hA1ampmeas τ).mul (hFmeas s))
        (ae_of_all _ (fun z => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hA1ampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₁))
    have hT3int : Integrable (fun z => gaussDdim τ z * (A2amp τ z * F s z 0)) volume :=
      (gaussDdim_integrable τ hτpos).mul_bdd ((hA2ampmeas τ).mul (hFmeas s))
        (ae_of_all _ (fun z => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hA2ampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₂))
    -- split into the three integrals
    have hsplit : (∫ z, D2H τ z * F s z 0)
        = (∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0))
          + (∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
          + (∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)) := by
      have hpt : ∀ z : Point n, D2H τ z * F s z 0
          = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
            + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)
            + gaussDdim τ z * (A2amp τ z * F s z 0) := by
        intro z; rw [hD2Hexpand τ hτIoo z]; ring
      have hf12 : Integrable (fun z : Point n =>
          (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
            + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)) volume := hT1int.add hT2int
      have e1 : (∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
            + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
          = (∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0))
            + ∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0) :=
        integral_add hT1int hT2int
      have e2 : (∫ z, ((z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
              + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
            + gaussDdim τ z * (A2amp τ z * F s z 0))
          = (∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
              + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
            + ∫ z, gaussDdim τ z * (A2amp τ z * F s z 0) :=
        integral_add hf12 hT3int
      rw [integral_congr_ae (ae_of_all _ hpt), e2, e1]
    -- term 1: the Hessian cancellation
    have hb1 : |∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)|
        ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ :=
      gaussian_hessian_cancel τ hτpos i (fun z => Aamp τ z * F s z 0) L hL
        (fun z w => hqLip τ hτIoo s hspos hsT z w) ((hAampmeas τ).mul (hFmeas s)) hqbdd
    -- term 2: the crude gradient moment
    have hb2 : |∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)|
        ≤ 3 / 4 * (M₁ * C_F) * (Real.sqrt τ)⁻¹ := by
      calc |∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)|
          = ‖∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ z, ‖z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ z, (1 / (2 * τ)) * (M₁ * C_F) * (|z i| * gaussDdim τ z) := by
            refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _))
              ((absCoord_gaussDdim_integrable τ hτpos i).const_mul _) (ae_of_all _ (fun z => ?_))
            dsimp only
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gaussDdim_nonneg' τ z), abs_div,
                abs_of_pos (show (0 : ℝ) < 2 * τ by linarith)]
            have hq1 : |A1amp τ z * F s z 0| ≤ M₁ * C_F := by
              rw [abs_mul]; exact mul_le_mul (hA1ampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₁
            calc |z i| / (2 * τ) * gaussDdim τ z * |A1amp τ z * F s z 0|
                ≤ |z i| / (2 * τ) * gaussDdim τ z * (M₁ * C_F) :=
                  mul_le_mul_of_nonneg_left hq1
                    (mul_nonneg (div_nonneg (abs_nonneg _) (by linarith)) (gaussDdim_nonneg' τ z))
              _ = (1 / (2 * τ)) * (M₁ * C_F) * (|z i| * gaussDdim τ z) := by ring
        _ = (1 / (2 * τ)) * (M₁ * C_F) * ∫ z, |z i| * gaussDdim τ z := integral_const_mul _ _
        _ ≤ (1 / (2 * τ)) * (M₁ * C_F) * (3 / 2 * Real.sqrt τ) := by
            refine mul_le_mul_of_nonneg_left (absCoord_gaussDdim_integral_le τ hτpos i) ?_
            exact mul_nonneg (div_nonneg zero_le_one (by linarith)) (mul_nonneg hM₁ hCFnn)
        _ = 3 / 4 * (M₁ * C_F) * (Real.sqrt τ)⁻¹ := by
            rw [show (1 / (2 * τ)) * (M₁ * C_F) * (3 / 2 * Real.sqrt τ)
                  = 3 / 4 * (M₁ * C_F) * (τ⁻¹ * Real.sqrt τ) from by ring, invT_mul_sqrt τ hτpos]
    -- term 3: total mass one
    have hb3 : |∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)| ≤ M₂ * C_F := by
      calc |∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)|
          = ‖∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ z, ‖gaussDdim τ z * (A2amp τ z * F s z 0)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ z, gaussDdim τ z * (M₂ * C_F) := by
            refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _))
              ((gaussDdim_integrable τ hτpos).mul_const _) (ae_of_all _ (fun z => ?_))
            dsimp only
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDdim_nonneg' τ z)]
            refine mul_le_mul_of_nonneg_left ?_ (gaussDdim_nonneg' τ z)
            rw [abs_mul]; exact mul_le_mul (hA2ampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₂
        _ = (∫ z, gaussDdim τ z) * (M₂ * C_F) := integral_mul_const _ _
        _ = 1 * (M₂ * C_F) := by rw [gaussDdim_integral_eq_one τ hτpos]
        _ = M₂ * C_F := one_mul _
    rw [hsplit]
    calc |(∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0))
            + (∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
            + (∫ z, gaussDdim τ z * (A2amp τ z * F s z 0))|
        ≤ |∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)|
            + |∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)|
            + |∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)| :=
          le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ + 3 / 4 * (M₁ * C_F) * (Real.sqrt τ)⁻¹ + M₂ * C_F :=
          add_le_add (add_le_add hb1 hb2) hb3
      _ = (L * (15 / 2 * (n : ℝ)) + 3 / 4 * (M₁ * C_F)) * τ ^ (-(1 : ℝ) / 2) + M₂ * C_F := by
          rw [← inv_sqrt_eq_rpow τ hτpos, div_eq_mul_inv]; ring
  -- assemble the outer sliver
  rw [← Real.norm_eq_abs]
  calc ‖∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z 0‖
      ≤ ∫ s in (u - ε)..u,
          ((L * (15 / 2 * (n : ℝ)) + 3 / 4 * (M₁ * C_F)) * (u - s) ^ (-(1 : ℝ) / 2) + M₂ * C_F) := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_
          (((rpow_sub_intervalIntegrable u ε hε0).const_mul _).add intervalIntegrable_const)
        filter_upwards [ae_ne_point u] with s hsu hsmem
        have hs_mem : s ∈ Set.Ioo (u - ε) u := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hsu⟩
        rw [Real.norm_eq_abs]; exact hinner s hs_mem
    _ = (L * (15 / 2 * (n : ℝ)) + 3 / 4 * (M₁ * C_F)) * (2 * Real.sqrt ε) + M₂ * C_F * ε := by
        rw [intervalIntegral.integral_add ((rpow_sub_intervalIntegrable u ε hε0).const_mul _)
            intervalIntegrable_const, intervalIntegral.integral_const_mul, sliver_rpow_sub u ε hε0,
            intervalIntegral.integral_const, smul_eq_mul, show u - (u - ε) = ε from by ring]
        ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.gaussian_grad_cancel
#print axioms QIQTH.HeatResidualBound.sliver_rpow
#print axioms QIQTH.HeatResidualBound.sliver_rpow_sub
#print axioms QIQTH.HeatResidualBound.sliver_bound_of_rpow
#print axioms QIQTH.HeatResidualBound.sliver1_zeroth_bound
#print axioms QIQTH.HeatResidualBound.sliver2_bound
