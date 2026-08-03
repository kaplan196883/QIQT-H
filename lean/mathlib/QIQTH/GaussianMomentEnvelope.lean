/-
  GaussianMomentEnvelope — J4-131: Sol-plan bricks S4 (weighted Gaussian moment envelope) and
  S5 (quantitative cubic chart-replacement estimate).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS HERE (the honest boundary — read it).

  Two reusable analytic bricks of the `a₁ = R/6` campaign — NOT `a₁ = R/6` itself.

  S4 — the moment envelope family.
    • (S4a) the 1-D absolute moments `∫ G_t(y)·|y|^k`, stated with `(√t)^k` (no `rpow`):
        k = 0 (mass, `= 1`), k = 1 (`≤ (3/2)√t`, reused), k = 2 (`≤ 2(√t)²`, exact `2t`),
        k = 4 (`≤ 128√2 (√t)⁴`, via the C4a absorb `hk_even_moment_le`), k = 3
        (`≤ (64√2+1)(√t)³`, via AM-GM from the k=2,4 moments).  The general even block
        `hk_even_moment_le (m)` : `∫ G_t·(y²)^m ≤ 8^m·m!·√2·t^m`.
    • (S4b) `pow_norm_mul_gauss_integral` — the n-D SUP-norm envelope: for `k ≥ 1`,
        `∫_z ‖z‖^k · G_{κt}(z) ≤ n·c_k·(√κ)^k·(√t)^k`, parametric in the supplied 1-D moment
        bound `c_k`.  Route: `‖z‖^k ≤ Σ_j |z_j|^k` (sup = max, single-coordinate lower bound), each
        coordinate term factorizes (Fubini product form) to the 1-D k-moment, others mass one.
  S5 — the quantitative cubic replacement.
    • (S5a) `exp_neg_div_sub_le` — the elementary pointwise bound
        `|e^{−a/4τ} − e^{−b/4τ}| ≤ (|a−b|/4τ)·e^{−min a b/4τ}`, via `1 − e^{−x} ≤ x`
        (`Real.add_one_le_exp`), NO MVT machinery.
    • (S5b) `gaussDdim_replace_bound` — the kernel replacement (parametric in the chart map `W`,
        exactly like `ChartGaussAdapter`): given the ℓ²-error bound `herr` and the coercivity `hmin`
        (`½·r²_z ≤ r²_{Wz}`),
        `|G_τ(Wz) − G_τ(z)| ≤ (L'‖z‖³/4τ)·(√2)^n·G_{2τ}(z)`.
    • (S5c) `weighted_chart_replace_bound` — the weighted corollary on a ball:
        `∫_{ball} ‖z‖^k·|G_τ(Wz) − G_τ(z)| ≤ C·(√τ)^{k+1}`, from S5b + S4b at `(k+3, κ=2)`.

  ⚠ HONEST FIREWALL.
    LANDED: all of S4a (k = 0..4) + the general even block; S4b (parametric in the 1-D moment);
      S5a; S5b (parametric in `W`, `L'`, with `herr`/`hmin` genuine near-isometry facts); S5c
      (parametric in `W`, with `herr`/`hmin` pointwise on the ball, the base integrability `hWint`,
      and the 1-D `(k+3)`-moment bound).
    The hypotheses (`hmom`, `herr`, `hmin`, `hWint`, `hck`, `hL'`, `hκ`, `ht`, `hτ`, `hk1`) are all
      genuine, load-bearing, satisfiable, non-vacuous, and never the conclusion.  `herr`/`hmin` are
      exactly the shapes discharged for the true chart by `InverseChartDisplacement`
      (`chartW0_rncRadialSq_error` + `chartW0_nearIsometry` with `c = 1/2`); `hWint` is the base
      measurability/integrability carry, consistent with `ChartGaussAdapter.hWmeas`.  Keeping `W`
      abstract keeps this a reusable BRICK, decoupled from the concrete chart assembly.
    NOT DONE: this is NOT `a₁ = R/6`; the geometric wiring (identifying `W` with the inverse chart,
      the sliver-integral assembly, the curvature source) lives downstream.
    No `sorry`, no new axioms, no `expRho` in statements.
-/
import Mathlib
import QIQTH.ChartGaussAdapter
import QIQTH.GaussianHessianCancel
import QIQTH.GaussianPolyBound

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianPolyBound QIQTH.GaussianConvolution
open QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### S4a — the 1-D absolute moments. -/

/-- **The general EVEN moment (C4a absorb route).**  For `t > 0` and `m : ℕ`,
    `∫ y, G_t(y)·(y²)^m ≤ 8^m·m!·√2·t^m`.  Pointwise: `(y²)^m·e^{−y²/4t} ≤ 8^m·m!·t^m·e^{−y²/8t}`
    (`gaussian_poly_absorb`), then `(√(4πt))⁻¹·e^{−y²/8t} = √2·G_{2t}(y)` (`exp_eighth_eq`) and
    the mass-one zeroth moment at width `2t`. -/
theorem hk_even_moment_le (m : ℕ) (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * (y ^ 2) ^ m
      ≤ 8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hsqrt2 : (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.sqrt (8 * Real.pi * t) = Real.sqrt 2 := by
    have h1 : Real.sqrt (8 * Real.pi * t) = Real.sqrt 2 * Real.sqrt (4 * Real.pi * t) := by
      rw [show (8 : ℝ) * Real.pi * t = 2 * (4 * Real.pi * t) from by ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h1, mul_comm (Real.sqrt 2) (Real.sqrt (4 * Real.pi * t)), ← mul_assoc,
        inv_mul_cancel₀ (Real.sqrt_pos.mpr (mul_pos (by positivity) ht)).ne', one_mul]
  have hpt : ∀ y : ℝ, heatKernel1D t y * (y ^ 2) ^ m
      ≤ (8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m) * heatKernel1D (2 * t) y := by
    intro y
    have hab := gaussian_poly_absorb m ht y
    have hApos : (0 : ℝ) ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ := by positivity
    calc heatKernel1D t y * (y ^ 2) ^ m
        = (Real.sqrt (4 * Real.pi * t))⁻¹ * ((y ^ 2) ^ m * Real.exp (-(y ^ 2) / (4 * t))) := by
          rw [heatKernel1D]; ring
      _ ≤ (Real.sqrt (4 * Real.pi * t))⁻¹
            * (8 ^ m * (m.factorial : ℝ) * t ^ m * Real.exp (-(y ^ 2) / (8 * t))) :=
          mul_le_mul_of_nonneg_left hab hApos
      _ = 8 ^ m * (m.factorial : ℝ) * t ^ m
            * ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.sqrt (8 * Real.pi * t))
            * heatKernel1D (2 * t) y := by
          rw [exp_eighth_eq t ht y]; ring
      _ = (8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m) * heatKernel1D (2 * t) y := by
          rw [hsqrt2]; ring
  have hLint : Integrable (fun y : ℝ => heatKernel1D t y * (y ^ 2) ^ m) volume :=
    hk_mul_sq_pow_integrable t ht m
  have hRint : Integrable
      (fun y : ℝ => (8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m) * heatKernel1D (2 * t) y)
      volume := (heatKernel1D_integrable (2 * t) h2t).const_mul _
  calc ∫ y, heatKernel1D t y * (y ^ 2) ^ m
      ≤ ∫ y, (8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m) * heatKernel1D (2 * t) y :=
        integral_mono_of_nonneg
          (ae_of_all _ (fun y => mul_nonneg (heatKernel1D_pos t y ht).le (by positivity)))
          hRint (ae_of_all _ hpt)
    _ = (8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m) * ∫ y, heatKernel1D (2 * t) y := by
        rw [integral_const_mul]
    _ = (8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m) * 1 := by
        rw [gaussianZerothMoment_oneD (2 * t) h2t]
    _ = 8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m := by ring

/-- **(S4a, k = 0) mass.**  `∫ y, G_t(y)·|y|^0 = 1`. -/
theorem oneD_absMoment0 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 0 = 1 := by
  simp only [pow_zero, mul_one]; exact gaussianZerothMoment_oneD t ht

/-- **(S4a, k = 1) the first absolute moment.**  `∫ y, G_t(y)·|y|^1 ≤ (3/2)(√t)^1` (reuses
    `hk_absY_moment_le`). -/
theorem oneD_absMoment1 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 1 ≤ 3 / 2 * (Real.sqrt t) ^ 1 := by
  simpa using hk_absY_moment_le t ht

/-- **(S4a, k = 2) the second absolute moment.**  `∫ y, G_t(y)·|y|^2 ≤ 2(√t)^2` (exact `2t`, via
    `gaussianSecondMoment_oneD` and `|y|² = y²`). -/
theorem oneD_absMoment2 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 2 ≤ 2 * (Real.sqrt t) ^ 2 := by
  have h : ∫ y : ℝ, heatKernel1D t y * |y| ^ 2 = 2 * t := by
    rw [← gaussianSecondMoment_oneD t ht]
    exact integral_congr_ae (ae_of_all _ (fun y => by simp only [sq_abs]))
  refine le_of_eq ?_
  rw [h, Real.sq_sqrt ht.le]

/-- **(S4a, k = 4) the fourth absolute moment.**  `∫ y, G_t(y)·|y|^4 ≤ 128√2(√t)^4` (via the C4a
    even block `hk_even_moment_le 2` and `|y|⁴ = (y²)²`, `(√t)⁴ = t²`). -/
theorem oneD_absMoment4 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 4 ≤ 128 * Real.sqrt 2 * (Real.sqrt t) ^ 4 := by
  have hconv : ∀ y : ℝ, heatKernel1D t y * |y| ^ 4 = heatKernel1D t y * (y ^ 2) ^ 2 :=
    fun y => by congr 1; rw [← sq_abs y]; ring
  rw [integral_congr_ae (ae_of_all _ hconv)]
  have h4 : (Real.sqrt t) ^ 4 = t ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ht.le]
  rw [h4]
  have hfac : (Nat.factorial 2 : ℝ) = 2 := by norm_num
  have heq : (8 : ℝ) ^ 2 * (Nat.factorial 2 : ℝ) * Real.sqrt 2 * t ^ 2 = 128 * Real.sqrt 2 * t ^ 2 := by
    rw [hfac]; ring
  linarith [hk_even_moment_le 2 t ht, heq]

/-- **(S4a, k = 3) the third absolute moment (AM-GM).**  `∫ y, G_t(y)·|y|^3 ≤ (64√2+1)(√t)^3`.
    Via `|y|³ = y²·|y| ≤ y²·(y²+t)/(2√t)` and the k=2,4 moments. -/
theorem oneD_absMoment3 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 3 ≤ (64 * Real.sqrt 2 + 1) * (Real.sqrt t) ^ 3 := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hstne : Real.sqrt t ≠ 0 := hst.ne'
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hy2int : Integrable (fun y : ℝ => heatKernel1D t y * y ^ 2) volume := by
    simpa using hk_mul_sq_pow_integrable t ht 1
  have hpt : ∀ y : ℝ, heatKernel1D t y * |y| ^ 3
      ≤ (1 / (2 * Real.sqrt t))
          * (heatKernel1D t y * (y ^ 2) ^ 2 + t * (heatKernel1D t y * y ^ 2)) := by
    intro y
    have hknn : 0 ≤ heatKernel1D t y := (heatKernel1D_pos t y ht).le
    have hamgm : |y| ≤ (y ^ 2 + t) / (2 * Real.sqrt t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|y| - Real.sqrt t), sq_abs y, hsq, abs_nonneg y]
    have h3 : |y| ^ 3 ≤ y ^ 2 * ((y ^ 2 + t) / (2 * Real.sqrt t)) := by
      have he : |y| ^ 3 = y ^ 2 * |y| := by rw [← sq_abs y]; ring
      rw [he]; exact mul_le_mul_of_nonneg_left hamgm (sq_nonneg y)
    calc heatKernel1D t y * |y| ^ 3
        ≤ heatKernel1D t y * (y ^ 2 * ((y ^ 2 + t) / (2 * Real.sqrt t))) :=
          mul_le_mul_of_nonneg_left h3 hknn
      _ = (1 / (2 * Real.sqrt t))
            * (heatKernel1D t y * (y ^ 2) ^ 2 + t * (heatKernel1D t y * y ^ 2)) := by
          field_simp; try ring
  have hInt : Integrable (fun y : ℝ => (1 / (2 * Real.sqrt t))
      * (heatKernel1D t y * (y ^ 2) ^ 2 + t * (heatKernel1D t y * y ^ 2))) volume :=
    (((hk_mul_sq_pow_integrable t ht 2).add (hy2int.const_mul t))).const_mul _
  have hmono : ∫ y, heatKernel1D t y * |y| ^ 3
      ≤ ∫ y, (1 / (2 * Real.sqrt t))
          * (heatKernel1D t y * (y ^ 2) ^ 2 + t * (heatKernel1D t y * y ^ 2)) :=
    integral_mono_of_nonneg
      (ae_of_all _ (fun y => mul_nonneg (heatKernel1D_pos t y ht).le (by positivity)))
      hInt (ae_of_all _ hpt)
  have hDval : ∫ y, (1 / (2 * Real.sqrt t))
      * (heatKernel1D t y * (y ^ 2) ^ 2 + t * (heatKernel1D t y * y ^ 2))
      = (1 / (2 * Real.sqrt t)) * ((∫ y, heatKernel1D t y * (y ^ 2) ^ 2) + t * (2 * t)) := by
    rw [integral_const_mul, integral_add (hk_mul_sq_pow_integrable t ht 2) (hy2int.const_mul t),
        integral_const_mul, gaussianSecondMoment_oneD t ht]
  have hI4 : ∫ y, heatKernel1D t y * (y ^ 2) ^ 2 ≤ 128 * Real.sqrt 2 * t ^ 2 := by
    have hfac : (Nat.factorial 2 : ℝ) = 2 := by norm_num
    have heq : (8 : ℝ) ^ 2 * (Nat.factorial 2 : ℝ) * Real.sqrt 2 * t ^ 2
        = 128 * Real.sqrt 2 * t ^ 2 := by rw [hfac]; ring
    linarith [hk_even_moment_le 2 t ht, heq]
  calc ∫ y, heatKernel1D t y * |y| ^ 3
      ≤ ∫ y, (1 / (2 * Real.sqrt t))
          * (heatKernel1D t y * (y ^ 2) ^ 2 + t * (heatKernel1D t y * y ^ 2)) := hmono
    _ = (1 / (2 * Real.sqrt t)) * ((∫ y, heatKernel1D t y * (y ^ 2) ^ 2) + t * (2 * t)) := hDval
    _ ≤ (1 / (2 * Real.sqrt t)) * (128 * Real.sqrt 2 * t ^ 2 + t * (2 * t)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hI4]
    _ = (64 * Real.sqrt 2 + 1) * (Real.sqrt t) ^ 3 := by
        have hts : t = Real.sqrt t * Real.sqrt t := hsq.symm
        set s := Real.sqrt t with hs
        rw [hts]
        field_simp
        try ring

/-! ### S4a → the 1-D `|y|^k`-moment integrability workhorse. -/

/-- `G_t(y)·|y|^k` is integrable: dominated by `G_t·(1 + (y²)^k)` (via `|y|^k ≤ 1 + (|y|^k)²`). -/
theorem hk_mul_abspow_integrable (t : ℝ) (ht : 0 < t) (k : ℕ) :
    Integrable (fun y : ℝ => heatKernel1D t y * |y| ^ k) volume := by
  refine ((heatKernel1D_integrable t ht).add (hk_mul_sq_pow_integrable t ht k)).mono'
    ((hk_continuous t).mul (continuous_abs.pow k)).aestronglyMeasurable
    (ae_of_all _ (fun y => ?_))
  have hknn : 0 ≤ heatKernel1D t y := (heatKernel1D_pos t y ht).le
  have hsq : (y ^ 2) ^ k = (|y| ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2, pow_mul, pow_mul, sq_abs]
  have hbnd : |y| ^ k ≤ 1 + (y ^ 2) ^ k := by
    rw [hsq]; nlinarith [sq_nonneg (|y| ^ k - 1), pow_nonneg (abs_nonneg y) k]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hknn (pow_nonneg (abs_nonneg y) k))]
  calc heatKernel1D t y * |y| ^ k ≤ heatKernel1D t y * (1 + (y ^ 2) ^ k) :=
        mul_le_mul_of_nonneg_left hbnd hknn
    _ = heatKernel1D t y + heatKernel1D t y * (y ^ 2) ^ k := by ring

/-! ### S4b — the n-D sup-norm moment envelope. -/

/-- The sup-norm `k`-th power is bounded by the coordinate `k`-th-power sum (for `k ≥ 1`):
    `‖z‖^k ≤ Σ_j |z_j|^k`.  The sup is a coordinate maximum, so `‖z‖^k = |z_{j₀}|^k ≤ Σ`. -/
theorem norm_pow_le_sum_abs_pow (k : ℕ) (hk1 : 1 ≤ k) (z : Point n) :
    ‖z‖ ^ k ≤ ∑ j, |z j| ^ k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hz : z = 0 := by funext i; exact i.elim0
    rw [hz, norm_zero, zero_pow (by omega : k ≠ 0)]
    exact Finset.sum_nonneg (fun j _ => pow_nonneg (abs_nonneg _) k)
  · haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j : Fin n => |z j|)
    have hzle : ‖z‖ ≤ |z j0| := by
      refine (pi_norm_le_iff_of_nonneg (abs_nonneg (z j0))).mpr (fun i => ?_)
      rw [Real.norm_eq_abs]; exact hj0 i
    calc ‖z‖ ^ k ≤ |z j0| ^ k := pow_le_pow_left₀ (norm_nonneg z) hzle k
      _ ≤ ∑ j, |z j| ^ k :=
        Finset.single_le_sum (f := fun j => |z j| ^ k)
          (fun j _ => pow_nonneg (abs_nonneg _) k) (Finset.mem_univ j0)

/-- A single-coordinate `|y|^k` moment factorizes: `∫_z |z_j|^k·G_τ(z) = ∫_y G_τ(y)·|y|^k`. -/
theorem coordAbsPow_gauss_integral (τ : ℝ) (hτ : 0 < τ) (j : Fin n) (k : ℕ) :
    ∫ z : Point n, |z j| ^ k * gaussDdim τ z = ∫ y : ℝ, heatKernel1D τ y * |y| ^ k := by
  have hpt : ∀ z : Point n, |z j| ^ k * gaussDdim τ z
      = ∏ m, (fun (m' : Fin n) (y : ℝ) => heatKernel1D τ y * (if m' = j then |y| ^ k else 1))
          m (z m) := by
    intro z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']; ring
  rw [integral_congr_ae (ae_of_all _ hpt),
      integral_fintype_prod_volume_eq_prod
        (fun (m : Fin n) (y : ℝ) => heatKernel1D τ y * (if m = j then |y| ^ k else 1))]
  have hcoord : ∀ m : Fin n,
      (∫ y : ℝ, heatKernel1D τ y * (if m = j then |y| ^ k else 1))
        = (if m = j then (∫ y : ℝ, heatKernel1D τ y * |y| ^ k) else 1) := by
    intro m
    by_cases hm : m = j
    · simp only [if_pos hm]
    · simp only [if_neg hm, mul_one]; exact gaussianZerothMoment_oneD τ hτ
  rw [Finset.prod_congr rfl (fun m _ => hcoord m), Fintype.prod_ite_eq']

/-- `|z_j|^k·G_τ(z)` is integrable on `Point n`. -/
theorem coordAbsPow_gauss_integrable (τ : ℝ) (hτ : 0 < τ) (j : Fin n) (k : ℕ) :
    Integrable (fun z : Point n => |z j| ^ k * gaussDdim τ z) volume := by
  have hpt : (fun z : Point n => |z j| ^ k * gaussDdim τ z)
      = fun z => ∏ m, heatKernel1D τ (z m) * (if m = j then |z m| ^ k else 1) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']; ring
  have hf : ∀ m : Fin n,
      Integrable (fun y : ℝ => heatKernel1D τ y * (if m = j then |y| ^ k else 1)) volume := by
    intro m
    by_cases hm : m = j
    · simp only [if_pos hm]; exact hk_mul_abspow_integrable τ hτ k
    · simp only [if_neg hm, mul_one]; exact heatKernel1D_integrable τ hτ
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-- `‖z‖^k·G_t(z)` is integrable on `Point n` (for `k ≥ 1`), dominated by `Σ_j |z_j|^k·G_t`. -/
theorem normPow_gauss_integrable (k : ℕ) (hk1 : 1 ≤ k) (t : ℝ) (ht : 0 < t) :
    Integrable (fun z : Point n => ‖z‖ ^ k * gaussDdim t z) volume := by
  have hdom : Integrable (fun z : Point n => ∑ j, |z j| ^ k * gaussDdim t z) volume :=
    integrable_finsetSum _ (fun j _ => coordAbsPow_gauss_integrable t ht j k)
  refine hdom.mono' ?_ (ae_of_all _ (fun z => ?_))
  · apply Continuous.aestronglyMeasurable
    exact (continuous_norm.pow k).mul
      (continuous_finset_prod Finset.univ
        (fun i _ => (hk_continuous t).comp (continuous_apply i)))
  · rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg z) k) (gaussDdim_nonneg _ _)),
        ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (norm_pow_le_sum_abs_pow k hk1 z) (gaussDdim_nonneg _ _)

/-- **★ S4b — THE n-D SUP-NORM MOMENT ENVELOPE.**  For `k ≥ 1`, `κ, t > 0`, and a supplied 1-D
    `k`-moment bound `hmom` (with constant `c_k ≥ 0`),
      `∫_z ‖z‖^k · G_{κt}(z) ≤ n · c_k · (√κ)^k · (√t)^k`.
    Route: `‖z‖^k ≤ Σ_j |z_j|^k` (sup = coordinate max), each coordinate term factorizes to the 1-D
    `k`-moment `≤ c_k·(√(κt))^k`, sum over `n` coordinates, and `(√(κt))^k = (√κ)^k(√t)^k`. -/
theorem pow_norm_mul_gauss_integral (k : ℕ) (hk1 : 1 ≤ k) (κ : ℝ) (hκ : 0 < κ)
    (t : ℝ) (ht : 0 < t) (ck : ℝ) (_hck : 0 ≤ ck)
    (hmom : ∫ y : ℝ, heatKernel1D (κ * t) y * |y| ^ k ≤ ck * (Real.sqrt (κ * t)) ^ k) :
    ∫ z : Point n, ‖z‖ ^ k * gaussDdim (κ * t) z
      ≤ (n : ℝ) * ck * (Real.sqrt κ) ^ k * (Real.sqrt t) ^ k := by
  have hτ : 0 < κ * t := mul_pos hκ ht
  have hdom_int : Integrable (fun z : Point n => ∑ j, |z j| ^ k * gaussDdim (κ * t) z) volume :=
    integrable_finsetSum _ (fun j _ => coordAbsPow_gauss_integrable (κ * t) hτ j k)
  have hmono : ∫ z : Point n, ‖z‖ ^ k * gaussDdim (κ * t) z
      ≤ ∫ z : Point n, ∑ j, |z j| ^ k * gaussDdim (κ * t) z := by
    refine integral_mono_of_nonneg (ae_of_all _ (fun z => ?_)) hdom_int (ae_of_all _ (fun z => ?_))
    · exact mul_nonneg (pow_nonneg (norm_nonneg z) k) (gaussDdim_nonneg _ _)
    · calc ‖z‖ ^ k * gaussDdim (κ * t) z
          ≤ (∑ j, |z j| ^ k) * gaussDdim (κ * t) z :=
            mul_le_mul_of_nonneg_right (norm_pow_le_sum_abs_pow k hk1 z) (gaussDdim_nonneg _ _)
        _ = ∑ j, |z j| ^ k * gaussDdim (κ * t) z := Finset.sum_mul _ _ _
  have hsum : ∫ z : Point n, ∑ j, |z j| ^ k * gaussDdim (κ * t) z
      = ∑ j, ∫ z : Point n, |z j| ^ k * gaussDdim (κ * t) z :=
    integral_finsetSum _ (fun j _ => coordAbsPow_gauss_integrable (κ * t) hτ j k)
  have hcoord : ∀ j : Fin n, ∫ z : Point n, |z j| ^ k * gaussDdim (κ * t) z ≤ ck * (Real.sqrt (κ * t)) ^ k := by
    intro j; rw [coordAbsPow_gauss_integral (κ * t) hτ j k]; exact hmom
  have hbig : ∑ j : Fin n, ∫ z : Point n, |z j| ^ k * gaussDdim (κ * t) z
      ≤ ∑ _j : Fin n, ck * (Real.sqrt (κ * t)) ^ k :=
    Finset.sum_le_sum (fun j _ => hcoord j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbig
  have hsqrt : (Real.sqrt (κ * t)) ^ k = (Real.sqrt κ) ^ k * (Real.sqrt t) ^ k := by
    rw [Real.sqrt_mul hκ.le, mul_pow]
  calc ∫ z : Point n, ‖z‖ ^ k * gaussDdim (κ * t) z
      ≤ ∫ z : Point n, ∑ j, |z j| ^ k * gaussDdim (κ * t) z := hmono
    _ = ∑ j, ∫ z : Point n, |z j| ^ k * gaussDdim (κ * t) z := hsum
    _ ≤ (n : ℝ) * (ck * (Real.sqrt (κ * t)) ^ k) := hbig
    _ = (n : ℝ) * ck * (Real.sqrt κ) ^ k * (Real.sqrt t) ^ k := by rw [hsqrt]; ring

/-! ### S5a — the elementary pointwise exponential difference bound. -/

/-- **★ S5a — THE POINTWISE MVT-FREE BOUND.**  For `τ > 0` and any `a, b`,
      `|e^{−a/4τ} − e^{−b/4τ}| ≤ (|a−b|/4τ)·e^{−min a b/4τ}`.
    ELEMENTARY: for `p ≤ q`, `e^{−p/4τ} − e^{−q/4τ} = e^{−p/4τ}(1 − e^{−(q−p)/4τ}) ≤ e^{−p/4τ}·(q−p)/4τ`
    using `1 − e^{−x} ≤ x` (`Real.add_one_le_exp`); the general case follows by `le_total`. -/
theorem exp_neg_div_sub_le (a b τ : ℝ) (hτ : 0 < τ) :
    |Real.exp (-a / (4 * τ)) - Real.exp (-b / (4 * τ))|
      ≤ (|a - b| / (4 * τ)) * Real.exp (-(min a b) / (4 * τ)) := by
  have key : ∀ p q : ℝ, p ≤ q →
      Real.exp (-p / (4 * τ)) - Real.exp (-q / (4 * τ))
        ≤ ((q - p) / (4 * τ)) * Real.exp (-p / (4 * τ)) := by
    intro p q hpq
    set x : ℝ := (q - p) / (4 * τ) with hx
    have hfac : Real.exp (-q / (4 * τ))
        = Real.exp (-p / (4 * τ)) * Real.exp (-x) := by
      rw [← Real.exp_add]; congr 1; rw [hx]; ring
    have h1e : 1 - Real.exp (-x) ≤ x := by
      have hh := Real.add_one_le_exp (-x); linarith
    calc Real.exp (-p / (4 * τ)) - Real.exp (-q / (4 * τ))
        = Real.exp (-p / (4 * τ)) * (1 - Real.exp (-x)) := by rw [hfac]; ring
      _ ≤ Real.exp (-p / (4 * τ)) * x :=
          mul_le_mul_of_nonneg_left h1e (Real.exp_pos _).le
      _ = x * Real.exp (-p / (4 * τ)) := by ring
      _ = ((q - p) / (4 * τ)) * Real.exp (-p / (4 * τ)) := by rw [hx]
  rcases le_total a b with hab | hba
  · have hge : Real.exp (-b / (4 * τ)) ≤ Real.exp (-a / (4 * τ)) := by
      apply Real.exp_le_exp.mpr
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    rw [abs_of_nonneg (by linarith [hge] :
          (0 : ℝ) ≤ Real.exp (-a / (4 * τ)) - Real.exp (-b / (4 * τ))),
        min_eq_left hab, abs_of_nonpos (by linarith : a - b ≤ 0),
        show -(a - b) = b - a from by ring]
    exact key a b hab
  · have hge : Real.exp (-a / (4 * τ)) ≤ Real.exp (-b / (4 * τ)) := by
      apply Real.exp_le_exp.mpr
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    rw [abs_of_nonpos (by linarith [hge] :
          Real.exp (-a / (4 * τ)) - Real.exp (-b / (4 * τ)) ≤ 0),
        min_eq_right hba, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b),
        show -(Real.exp (-a / (4 * τ)) - Real.exp (-b / (4 * τ)))
            = Real.exp (-b / (4 * τ)) - Real.exp (-a / (4 * τ)) from by ring]
    exact key b a hba

/-! ### S5b — the quantitative kernel replacement. -/

/-- **★★ S5b — THE KERNEL-REPLACEMENT BOUND.**  Parametric in the chart map `W`.  Given the ℓ²
    near-isometry error `herr : |r²_{Wz} − r²_z| ≤ L'‖z‖³` and the coercivity
    `hmin : ½·r²_z ≤ r²_{Wz}`, for `τ > 0`,
      `|G_τ(Wz) − G_τ(z)| ≤ (L'‖z‖³/4τ)·(√2)^n·G_{2τ}(z)`.
    Route: `G_τ = (√(4πτ))⁻ⁿ e^{−r²/4τ}`, S5a on the exponents, `min ≥ ½r²_z`, and the scaled-width
    identity `Gk_scaled` (`s = ½`, `(√½)⁻¹ = √2`) to recognise `(√(4πτ))⁻ⁿe^{−r²_z/8τ} = (√2)^n G_{2τ}`. -/
theorem gaussDdim_replace_bound (τ : ℝ) (hτ : 0 < τ) (W : Point n → Point n) (z : Point n)
    (L' : ℝ) (_hL' : 0 ≤ L')
    (herr : |rncRadialSq (W z) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
    (hmin : (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (W z)) :
    |gaussDdim τ (W z) - gaussDdim τ z|
      ≤ L' * ‖z‖ ^ 3 / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
  have hpnn : (0 : ℝ) ≤ rncRadialSq z := rncRadialSq_nonneg z
  rw [gaussDdim_eq_Gk τ (W z), gaussDdim_eq_Gk τ z]
  set p := rncRadialSq z with hpdef
  set q := rncRadialSq (W z) with hqdef
  have hGksub : Gk n τ q - Gk n τ p
      = (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n
          * (Real.exp (-q / (4 * τ)) - Real.exp (-p / (4 * τ))) := by
    unfold Gk; ring
  rw [hGksub, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n)]
  have hS5a := exp_neg_div_sub_le q p τ hτ
  have hmin' : (1 / 2 : ℝ) * p ≤ min q p := le_min hmin (by linarith [hpnn])
  have hexple : Real.exp (-(min q p) / (4 * τ)) ≤ Real.exp (-((1 / 2) * p) / (4 * τ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith [hmin']) (by positivity)
  have hs2 : (Real.sqrt (1 / 2))⁻¹ = Real.sqrt 2 := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ from by norm_num, Real.sqrt_inv, inv_inv]
  have hhalf : (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.exp (-((1 / 2) * p) / (4 * τ))
      = (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
    have hkey : Gk n τ ((1 / 2) * p) = (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
      rw [hpdef, Gk_scaled (1 / 2) τ (by norm_num) hτ z, hs2,
          show τ / (1 / 2) = 2 * τ from by ring]
    rw [← hkey]; rfl
  have hXnn : (0 : ℝ) ≤ (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
    mul_nonneg (by positivity) (gaussDdim_nonneg _ _)
  calc (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n
          * |Real.exp (-q / (4 * τ)) - Real.exp (-p / (4 * τ))|
      ≤ (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n
          * ((|q - p| / (4 * τ)) * Real.exp (-(min q p) / (4 * τ))) :=
        mul_le_mul_of_nonneg_left hS5a (by positivity)
    _ = (|q - p| / (4 * τ))
          * ((Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.exp (-(min q p) / (4 * τ))) := by ring
    _ ≤ (|q - p| / (4 * τ))
          * ((Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.exp (-((1 / 2) * p) / (4 * τ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hexple (by positivity)
    _ = (|q - p| / (4 * τ)) * ((Real.sqrt 2) ^ n * gaussDdim (2 * τ) z) := by rw [hhalf]
    _ ≤ (L' * ‖z‖ ^ 3 / (4 * τ)) * ((Real.sqrt 2) ^ n * gaussDdim (2 * τ) z) := by
        apply mul_le_mul_of_nonneg_right _ hXnn
        exact (div_le_div_iff_of_pos_right (by positivity)).mpr herr
    _ = L' * ‖z‖ ^ 3 / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by ring

/-! ### S5c — the weighted chart-replacement estimate on a ball. -/

/-- **★ S5c — THE WEIGHTED CHART-REPLACEMENT ESTIMATE.**  Parametric in `W`.  On `ball 0 R`, with the
    pointwise near-isometry data `herr`/`hmin`, the base integrability `hWint`, and a supplied 1-D
    `(k+3)`-moment bound `hmom` (constant `c_{k+3} ≥ 0`):
      `∫_{ball} ‖z‖^k · |G_τ(Wz) − G_τ(z)| ≤ (L'/4·(√2)^n·(n·c_{k+3}·(√2)^{k+3}))·(√τ)^{k+1}`.
    Route: S5b pointwise gives `‖z‖^k|·| ≤ (L'/4τ)(√2)^n·‖z‖^{k+3}G_{2τ}`; extend to all of space
    (nonneg), apply S4b at `(k+3, κ=2)`, and use `(√τ)^{k+3} = (√τ)^{k+1}·τ` to cancel the `1/τ`. -/
theorem weighted_chart_replace_bound (k : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (W : Point n → Point n) (R : ℝ) (L' : ℝ) (hL' : 0 ≤ L')
    (herr : ∀ z ∈ Metric.ball (0 : Point n) R, |rncRadialSq (W z) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
    (hmin : ∀ z ∈ Metric.ball (0 : Point n) R, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (W z))
    (hWint : IntegrableOn (fun z : Point n => ‖z‖ ^ k * |gaussDdim τ (W z) - gaussDdim τ z|)
        (Metric.ball 0 R) volume)
    (ck3 : ℝ) (hck3 : 0 ≤ ck3)
    (hmom : ∫ y : ℝ, heatKernel1D (2 * τ) y * |y| ^ (k + 3)
        ≤ ck3 * (Real.sqrt (2 * τ)) ^ (k + 3)) :
    ∫ z in Metric.ball (0 : Point n) R, ‖z‖ ^ k * |gaussDdim τ (W z) - gaussDdim τ z|
      ≤ (L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3)))
          * (Real.sqrt τ) ^ (k + 1) := by
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  have hconst_nonneg : (0 : ℝ) ≤ L' / (4 * τ) * (Real.sqrt 2) ^ n := by positivity
  have hptB : ∀ z ∈ Metric.ball (0 : Point n) R,
      ‖z‖ ^ k * |gaussDdim τ (W z) - gaussDdim τ z|
        ≤ (L' / (4 * τ) * (Real.sqrt 2) ^ n) * (‖z‖ ^ (k + 3) * gaussDdim (2 * τ) z) := by
    intro z hz
    have hS5b := gaussDdim_replace_bound τ hτ W z L' hL' (herr z hz) (hmin z hz)
    calc ‖z‖ ^ k * |gaussDdim τ (W z) - gaussDdim τ z|
        ≤ ‖z‖ ^ k
            * (L' * ‖z‖ ^ 3 / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z) :=
          mul_le_mul_of_nonneg_left hS5b (pow_nonneg (norm_nonneg z) k)
      _ = (L' / (4 * τ) * (Real.sqrt 2) ^ n) * (‖z‖ ^ (k + 3) * gaussDdim (2 * τ) z) := by
          rw [pow_add]; ring
  have hfull_int : Integrable (fun z : Point n =>
      (L' / (4 * τ) * (Real.sqrt 2) ^ n) * (‖z‖ ^ (k + 3) * gaussDdim (2 * τ) z)) volume :=
    (normPow_gauss_integrable (k + 3) (by omega) (2 * τ) h2τ).const_mul _
  calc ∫ z in Metric.ball (0 : Point n) R, ‖z‖ ^ k * |gaussDdim τ (W z) - gaussDdim τ z|
      ≤ ∫ z in Metric.ball (0 : Point n) R,
          (L' / (4 * τ) * (Real.sqrt 2) ^ n) * (‖z‖ ^ (k + 3) * gaussDdim (2 * τ) z) :=
        setIntegral_mono_on hWint hfull_int.integrableOn measurableSet_ball hptB
    _ ≤ ∫ z, (L' / (4 * τ) * (Real.sqrt 2) ^ n) * (‖z‖ ^ (k + 3) * gaussDdim (2 * τ) z) := by
        refine setIntegral_le_integral hfull_int (ae_of_all _ (fun z => ?_))
        exact mul_nonneg hconst_nonneg
          (mul_nonneg (pow_nonneg (norm_nonneg z) _) (gaussDdim_nonneg _ _))
    _ = (L' / (4 * τ) * (Real.sqrt 2) ^ n) * ∫ z, ‖z‖ ^ (k + 3) * gaussDdim (2 * τ) z := by
        rw [integral_const_mul]
    _ ≤ (L' / (4 * τ) * (Real.sqrt 2) ^ n)
          * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3) * (Real.sqrt τ) ^ (k + 3)) :=
        mul_le_mul_of_nonneg_left
          (pow_norm_mul_gauss_integral (k + 3) (by omega) 2 (by norm_num) τ hτ ck3 hck3 hmom)
          hconst_nonneg
    _ = (L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3)))
          * (Real.sqrt τ) ^ (k + 1) := by
        have hτne : τ ≠ 0 := hτ.ne'
        have hpow : (Real.sqrt τ) ^ (k + 3) = (Real.sqrt τ) ^ (k + 1) * τ := by
          rw [show k + 3 = (k + 1) + 2 from by ring, pow_add, Real.sq_sqrt hτ.le]
        rw [hpow]; field_simp; try ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.hk_even_moment_le
#print axioms QIQTH.HeatResidualBound.oneD_absMoment3
#print axioms QIQTH.HeatResidualBound.oneD_absMoment4
#print axioms QIQTH.HeatResidualBound.pow_norm_mul_gauss_integral
#print axioms QIQTH.HeatResidualBound.exp_neg_div_sub_le
#print axioms QIQTH.HeatResidualBound.gaussDdim_replace_bound
#print axioms QIQTH.HeatResidualBound.weighted_chart_replace_bound
