/-
  SliceBoundO1 — J4-500: upgrade the SIGNED heat-trace SLICE integral bound O(1/a) → O(1).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  No `sorry`, no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypothesis, no result equal to (or trivially yielding) the
  conclusion, no existing file edited, nothing committed.  std-3 only.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  The concrete Duhamel slice integrand pairs the Hessian-Gaussian factor
  `hessGaussFactor i a z = (z_i²−2a)/(4a²)·G_a(z) = ∂²_{z_i}G_a(z)` against an amplitude `B`.  The
  crude ABSOLUTE slice bound is `|∫_z hessGaussFactor·B| ≤ C/a` (dominant `M₀·(n+1)/(2a)`); plugged
  into the Duhamel `∫₀^τ ds` at age `a=τ−s` it LOG-DIVERGES (`∫₀^τ C/(τ−s)ds = +∞`), so the crude
  bound is COEFFICIENT-INSUFFICIENT (J4-497/499).

  ## WHAT THIS BRICK DOES (Sol #22 step 1 — signed moment-cancellation, O(1/a)→O(1)).  For a
  degree-≤2 amplitude `B(z) = c + Σ_j b_j z_j + Σ_{jk} H_{jk} z_j z_k`, the SIGNED slice integral
    `∫_z hessGaussFactor i a z · B(z) dz`
  is bounded by an O(1)-in-`a` quantity, UNIFORMLY as `a→0⁺`:
    `|∫_z hessGaussFactor i a · B| ≤ (32√2 + 1)·Σ_{jk}|H_{jk}|`.
  The mechanism is EXACT SIGNED cancellation, NOT an absolute bound:
    • the CONSTANT part `∫ hessGaussFactor·c = c·∫ hessGaussFactor = 0` — the banked 0-th moment
      cancellation (`hessGaussFactor_integral_zero`); by itself its ABSOLUTE bound is `∼ c/a = O(1/a)`;
    • the LINEAR part `∫ hessGaussFactor·z_j = 0` — oddness (`hessGaussFactor_first_moment_zero`); by
      itself its ABSOLUTE bound is `∼ O(1/√a)`;
    • only the QUADRATIC part survives, and it is genuinely `O(1)`: the mixed second moment
      `∫ |hessGaussFactor i a|·z_m² ≤ 32√2+1` is bounded UNIFORMLY in `a` (the `1/a` of the Hessian
      weight is exactly compensated by the `a` of the second moment).
  Taking absolute values BEFORE the const/linear cancellation would recover the bad `1/a`, `1/√a`
  scales — so the signed cancellation is load-bearing (per Sol).

  ## ⚠ HONEST DISTANCE (per Sol #22, J4-499).  This removes the LOG-DIVERGENCE (`O(1/a)→O(1)`), so
  `∫₀^τ O(1) ds = O(τ)` — a MARGINAL correction (q=1), NOT `O(τ²)`.  The surviving `O(1)` is a
  TRANSPORT COEFFICIENT (the amplitude Hessian `H`, controlled by `Σ|H_{jk}|` here); its CANCELLATION
  to `O(τ²)` is the SEPARATE van-Vleck 2-jet wall `D²u₀(0)=(1/6)Ric` (`VanVleckRadial` is
  const-curvature-only), which this brick does NOT and CANNOT close.  So this is `O(1/a)→O(1)`, NOT
  `O(1/a)→O(a)`.  ⚠ NOT `a₁ = R/6`.

  ## WHAT LANDS.
    ★  `hessGaussFactor_first_moment_zero` — the 1-st moment `∫ hessGaussFactor i a·z_j = 0` (oddness).
    ★  `oneD_hessW_sq_moment_le` — the NEW 1-D mixed moment `∫ G_a·(|(y²−2a)/(4a²)|·y²) ≤ 32√2+1`
       (O(1), a-independent), via the banked even-4 bound and the exact 2-nd moment.
    ★  `hessAbs_coordSq_le` — the n-D O(1) mixed second moment `∫ |hessGaussFactor i a|·z_m² ≤ 32√2+1`.
    ★★★ `hessGauss_signed_slice_O1` — THE O(1) SIGNED SLICE BOUND
         `|∫_z hessGaussFactor i a · (c + Σ b_j z_j + Σ H_{jk} z_j z_k)| ≤ (32√2+1)·Σ_{jk}|H_{jk}|`.
-/
import Mathlib
import QIQTH.SliverTailMatched
import QIQTH.GaussianMomentEnvelope
import QIQTH.GaussianMomentExtraction

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.SliverTailMatched QIQTH.GaussianConvolution

namespace QIQTH.SliceBoundO1

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### Continuity of the Hessian-Gaussian factor (for the domination integrabilities).
    ############################################################################### -/

/-- `gaussDdim τ` is continuous (finite product of continuous 1-D kernels). -/
theorem gaussDdim_continuous (τ : ℝ) : Continuous (fun z : Point n => gaussDdim τ z) := by
  simp only [gaussDdim]
  exact continuous_finset_prod _ (fun k _ => (hk_continuous τ).comp (continuous_apply k))

/-- `hessGaussFactor i τ` is continuous. -/
theorem hessGaussFactor_continuous (τ : ℝ) (i : Fin n) :
    Continuous (fun z : Point n => hessGaussFactor i τ z) := by
  simp only [hessGaussFactor]
  exact ((((continuous_apply i).pow 2).sub continuous_const).div_const _).mul
    (gaussDdim_continuous τ)

/-! ###############################################################################
    ### The 1-D odd-integral helper and the odd Hessian×linear moment.
    ############################################################################### -/

/-- If `g` is odd (`g(−x)=−g x`) then `∫ g = 0` (volume is `neg`-invariant). -/
private theorem integral_odd_eq_zero (g : ℝ → ℝ) (hodd : ∀ x, g (-x) = - g x) :
    (∫ x, g x ∂(volume : Measure ℝ)) = 0 := by
  have h1 : ∫ x, g (-x) ∂(volume : Measure ℝ) = ∫ x, g x ∂(volume : Measure ℝ) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding g
    simpa using h
  have h2 : ∫ x, g (-x) ∂(volume : Measure ℝ) = - ∫ x, g x ∂(volume : Measure ℝ) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall hodd)
  rw [h1] at h2; linarith

/-- `heatKernel1D τ` is even. -/
private theorem hk_even (τ y : ℝ) : heatKernel1D τ (-y) = heatKernel1D τ y := by
  simp only [heatKernel1D]; rw [show (-y) ^ 2 = y ^ 2 from by ring]

/-- **(1-D odd) THE HESSIAN×LINEAR MOMENT VANISHES.**  `∫ G_τ(y)·((y²−2τ)/(4τ²)·y) = 0` — the
    integrand is odd (`G_τ` even, `(y²−2τ)/(4τ²)` even, `·y` odd). -/
theorem oneD_hessW_lin_zero (τ : ℝ) :
    ∫ y : ℝ, heatKernel1D τ y * ((y ^ 2 - 2 * τ) / (4 * τ ^ 2) * y) = 0 := by
  refine integral_odd_eq_zero _ (fun y => ?_)
  rw [hk_even, show ((-y) ^ 2 - 2 * τ) / (4 * τ ^ 2) = (y ^ 2 - 2 * τ) / (4 * τ ^ 2) from by
    rw [show (-y) ^ 2 = y ^ 2 from by ring]]
  ring

/-! ###############################################################################
    ### ★ THE 1-D O(1) MIXED SECOND MOMENT of the |Hessian| weight.
    ############################################################################### -/

/-- **★ `oneD_hessW_sq_moment_le`.**  For `τ>0`,
      `∫ G_τ(y)·(|(y²−2τ)/(4τ²)|·y²) ≤ 32√2 + 1`,
    an O(1)-in-`τ` (a-independent) bound.  Via `|y²−2τ|≤y²+2τ`, then the even-4 block
    `∫ G_τ·(y²)² ≤ 128√2·τ²` (`hk_even_moment_le 2`) and the exact 2-nd moment `∫ G_τ·y² = 2τ`:
      `(1/(4τ²))·128√2·τ² + (1/(2τ))·2τ = 32√2 + 1`.  The `1/τ` of the Hessian weight is exactly
    absorbed by the `τ` of the second moment — the O(1)-in-`a` mechanism. -/
theorem oneD_hessW_sq_moment_le (τ : ℝ) (hτ : 0 < τ) :
    ∫ y : ℝ, heatKernel1D τ y * (|(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2)
      ≤ 32 * Real.sqrt 2 + 1 := by
  have htne : τ ≠ 0 := hτ.ne'
  -- pointwise domination
  have hpt : ∀ y : ℝ, heatKernel1D τ y * (|(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2)
      ≤ heatKernel1D τ y * ((1 / (4 * τ ^ 2)) * (y ^ 2) ^ 2 + (1 / (2 * τ)) * y ^ 2) := by
    intro y
    refine mul_le_mul_of_nonneg_left ?_ (heatKernel1D_pos τ y hτ).le
    have hnum : |y ^ 2 - 2 * τ| ≤ y ^ 2 + 2 * τ := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg y, hτ.le]
    calc |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2
        = |y ^ 2 - 2 * τ| / (4 * τ ^ 2) * y ^ 2 := by
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * τ ^ 2)]
      _ ≤ (y ^ 2 + 2 * τ) / (4 * τ ^ 2) * y ^ 2 := by gcongr
      _ = (1 / (4 * τ ^ 2)) * (y ^ 2) ^ 2 + (1 / (2 * τ)) * y ^ 2 := by field_simp; ring
  have he : (fun y : ℝ => heatKernel1D τ y * ((1 / (4 * τ ^ 2)) * (y ^ 2) ^ 2 + (1 / (2 * τ)) * y ^ 2))
      = fun y => (1 / (4 * τ ^ 2)) * (heatKernel1D τ y * (y ^ 2) ^ 2)
          + (1 / (2 * τ)) * (heatKernel1D τ y * (y ^ 2) ^ 1) := by
    funext y; simp only [pow_one]; ring
  have hRint : Integrable
      (fun y : ℝ => heatKernel1D τ y * ((1 / (4 * τ ^ 2)) * (y ^ 2) ^ 2 + (1 / (2 * τ)) * y ^ 2))
      volume := by
    rw [he]
    exact ((hk_mul_sq_pow_integrable τ hτ 2).const_mul _).add
      ((hk_mul_sq_pow_integrable τ hτ 1).const_mul _)
  have hmono : (∫ y : ℝ, heatKernel1D τ y * (|(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2))
      ≤ ∫ y : ℝ, heatKernel1D τ y * ((1 / (4 * τ ^ 2)) * (y ^ 2) ^ 2 + (1 / (2 * τ)) * y ^ 2) :=
    integral_mono_of_nonneg
      (ae_of_all _ (fun y => mul_nonneg (heatKernel1D_pos τ y hτ).le (by positivity)))
      hRint (ae_of_all _ hpt)
  -- evaluate/bound the RHS
  have h4 : (∫ y : ℝ, heatKernel1D τ y * (y ^ 2) ^ 2) ≤ 128 * Real.sqrt 2 * τ ^ 2 := by
    have h := hk_even_moment_le 2 τ hτ
    have he : (8 : ℝ) ^ 2 * (Nat.factorial 2 : ℝ) * Real.sqrt 2 * τ ^ 2
        = 128 * Real.sqrt 2 * τ ^ 2 := by norm_num
    linarith [h, he]
  have h2m : (∫ y : ℝ, heatKernel1D τ y * (y ^ 2) ^ 1) = 2 * τ := by
    rw [show (fun y : ℝ => heatKernel1D τ y * (y ^ 2) ^ 1)
          = fun y => heatKernel1D τ y * y ^ 2 from by funext y; rw [pow_one]]
    exact gaussianSecondMoment_oneD τ hτ
  have hA : (1 / (4 * τ ^ 2)) * (∫ y : ℝ, heatKernel1D τ y * (y ^ 2) ^ 2)
      ≤ (1 / (4 * τ ^ 2)) * (128 * Real.sqrt 2 * τ ^ 2) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have hAeq : (1 / (4 * τ ^ 2)) * (128 * Real.sqrt 2 * τ ^ 2) = 32 * Real.sqrt 2 := by
    field_simp; ring
  have hBeq : (1 / (2 * τ)) * (∫ y : ℝ, heatKernel1D τ y * (y ^ 2) ^ 1) = 1 := by
    rw [h2m]; field_simp
  calc (∫ y : ℝ, heatKernel1D τ y * (|(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2))
      ≤ ∫ y : ℝ, heatKernel1D τ y * ((1 / (4 * τ ^ 2)) * (y ^ 2) ^ 2 + (1 / (2 * τ)) * y ^ 2) :=
        hmono
    _ ≤ 32 * Real.sqrt 2 + 1 := by
        rw [he, integral_add ((hk_mul_sq_pow_integrable τ hτ 2).const_mul (1 / (4 * τ ^ 2)))
            ((hk_mul_sq_pow_integrable τ hτ 1).const_mul (1 / (2 * τ))),
            integral_const_mul, integral_const_mul]
        linarith [hA, hAeq, hBeq]

/-! ###############################################################################
    ### ★ THE 1-st MOMENT of the Hessian-Gaussian factor VANISHES.
    ############################################################################### -/

/-- **★ `hessGaussFactor_first_moment_zero`.**  For `τ>0`, `∫_z hessGaussFactor i τ z · z_j = 0`.
    Product factorization: if `j≠i` the coordinate-`j` factor is `∫ G_τ·y = 0` (`gaussianFirstMoment`);
    if `j=i` it is `∫ G_τ·((y²−2τ)/(4τ²)·y) = 0` (`oneD_hessW_lin_zero`, oddness). -/
theorem hessGaussFactor_first_moment_zero (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) :
    ∫ z : Point n, hessGaussFactor i τ z * z j = 0 := by
  have hpt : ∀ z : Point n, hessGaussFactor i τ z * z j
      = ∏ m, (heatKernel1D τ (z m)
          * ((if m = i then (z m ^ 2 - 2 * τ) / (4 * τ ^ 2) else 1) * (if m = j then z m else 1))) := by
    intro z; simp only [hessGaussFactor, gaussDdim]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
    ring
  rw [integral_congr_ae (ae_of_all _ hpt),
      integral_fintype_prod_volume_eq_prod
        (fun m (y : ℝ) => heatKernel1D τ y
          * ((if m = i then (y ^ 2 - 2 * τ) / (4 * τ ^ 2) else 1) * (if m = j then y else 1)))]
  by_cases hji : j = i
  · refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    simp only [if_pos hji, if_pos rfl]
    exact oneD_hessW_lin_zero τ
  · refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    simp only [if_neg hji, if_pos rfl, one_mul]
    exact gaussianFirstMoment_oneD τ hτ

/-! ###############################################################################
    ### ★ THE n-D O(1) MIXED SECOND MOMENT `∫ |hessGaussFactor i|·z_m² ≤ Cmix`.
    ############################################################################### -/

/-- The product form of `|hessGaussFactor i τ z|·(z_m)²`. -/
private theorem hessAbs_coordSq_prod (τ : ℝ) (i m : Fin n) (z : Point n) :
    |hessGaussFactor i τ z| * (z m) ^ 2
      = ∏ p, heatKernel1D τ (z p)
          * ((if p = i then |(z p ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1)
              * (if p = m then (z p) ^ 2 else 1)) := by
  have habs : |hessGaussFactor i τ z| = |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z := by
    simp only [hessGaussFactor, abs_mul, abs_of_nonneg (gaussDdim_nonneg' τ z)]
  rw [habs]
  simp only [gaussDdim]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  ring

/-- `|hessGaussFactor i τ z|·(z_m)²` is integrable on `Point n`. -/
theorem hessAbs_coordSq_integrable (τ : ℝ) (hτ : 0 < τ) (i m : Fin n) :
    Integrable (fun z : Point n => |hessGaussFactor i τ z| * (z m) ^ 2) volume := by
  have hf : ∀ p : Fin n, Integrable (fun y : ℝ => heatKernel1D τ y
      * ((if p = i then |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1) * (if p = m then y ^ 2 else 1)))
      volume := by
    intro p
    by_cases hpi : p = i
    · by_cases hpm : p = m
      · simp only [if_pos hpi, if_pos hpm]
        refine hk_mul_integrable_of_poly τ hτ _ (by fun_prop) 0 (1 / (2 * τ)) (1 / (4 * τ ^ 2))
          le_rfl (by positivity) (by positivity) (fun y => ?_)
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2)]
        have hnum : |y ^ 2 - 2 * τ| ≤ y ^ 2 + 2 * τ := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg y, hτ.le]
        calc |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2
            = |y ^ 2 - 2 * τ| / (4 * τ ^ 2) * y ^ 2 := by
              rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * τ ^ 2)]
          _ ≤ (y ^ 2 + 2 * τ) / (4 * τ ^ 2) * y ^ 2 := by gcongr
          _ = 0 + 1 / (2 * τ) * y ^ 2 + 1 / (4 * τ ^ 2) * (y ^ 2) ^ 2 := by
              have htne : τ ≠ 0 := hτ.ne'; field_simp; ring
      · simp only [if_pos hpi, if_neg hpm, mul_one]
        exact hk_absHess_integrable τ hτ
    · by_cases hpm : p = m
      · simp only [if_neg hpi, if_pos hpm, one_mul]
        exact (hk_mul_sq_pow_integrable τ hτ 1).congr (ae_of_all _ (fun y => by simp))
      · simp only [if_neg hpi, if_neg hpm, mul_one]
        exact heatKernel1D_integrable τ hτ
  refine ((integrable_congr (ae_of_all _ (hessAbs_coordSq_prod τ i m))).mpr ?_)
  rw [show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-- **★ `hessAbs_coordSq_le` — THE n-D O(1) MIXED SECOND MOMENT.**  For `τ>0`,
      `∫_z |hessGaussFactor i τ z|·(z_m)² ≤ 32√2 + 1`,
    UNIFORMLY in `τ` (O(1)-in-`a`).  Factorizes: `m=i` gives the 1-D mixed moment
    `oneD_hessW_sq_moment_le`; `m≠i` gives `(∫ G_τ·|(y²−2τ)/(4τ²)|)·(∫ G_τ·y²) ≤ τ⁻¹·2τ = 2`. -/
theorem hessAbs_coordSq_le (τ : ℝ) (hτ : 0 < τ) (i m : Fin n) :
    ∫ z : Point n, |hessGaussFactor i τ z| * (z m) ^ 2 ≤ 32 * Real.sqrt 2 + 1 := by
  rw [integral_congr_ae (ae_of_all _ (hessAbs_coordSq_prod τ i m)),
      integral_fintype_prod_volume_eq_prod
        (fun p (y : ℝ) => heatKernel1D τ y
          * ((if p = i then |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1) * (if p = m then y ^ 2 else 1)))]
  by_cases him : m = i
  · rw [him]
    have hprodeq : (∏ p : Fin n, ∫ y : ℝ, heatKernel1D τ y
          * ((if p = i then |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1) * (if p = i then y ^ 2 else 1)))
        = ∫ y : ℝ, heatKernel1D τ y * (|(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2) := by
      calc (∏ p : Fin n, ∫ y : ℝ, heatKernel1D τ y
            * ((if p = i then |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1) * (if p = i then y ^ 2 else 1)))
          = ∏ p : Fin n, (if p = i
              then (∫ y : ℝ, heatKernel1D τ y * (|(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2)) else 1) := by
            refine Finset.prod_congr rfl (fun p _ => ?_)
            by_cases hp : p = i
            · simp [hp]
            · simp only [if_neg hp, one_mul, mul_one]; exact gaussianZerothMoment_oneD τ hτ
        _ = ∫ y : ℝ, heatKernel1D τ y * (|(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| * y ^ 2) :=
            Fintype.prod_ite_eq' i _
    rw [hprodeq]; exact oneD_hessW_sq_moment_le τ hτ
  · have him' : i ≠ m := fun h => him h.symm
    have hout : ∀ p ∈ (Finset.univ : Finset (Fin n)), p ∉ ({i, m} : Finset (Fin n)) →
        (if p = i then (∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)|)
          else if p = m then (∫ y : ℝ, heatKernel1D τ y * y ^ 2) else 1) = 1 := by
      intro p _ hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      push_neg at hp
      simp only [if_neg hp.1, if_neg hp.2]
    have hprodeq : (∏ p : Fin n, ∫ y : ℝ, heatKernel1D τ y
          * ((if p = i then |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1) * (if p = m then y ^ 2 else 1)))
        = (∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)|)
          * (∫ y : ℝ, heatKernel1D τ y * y ^ 2) := by
      have hstep : (∏ p : Fin n, ∫ y : ℝ, heatKernel1D τ y
            * ((if p = i then |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1) * (if p = m then y ^ 2 else 1)))
          = ∏ p : Fin n, (if p = i
              then (∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)|)
              else if p = m then (∫ y : ℝ, heatKernel1D τ y * y ^ 2) else 1) := by
        refine Finset.prod_congr rfl (fun p _ => ?_)
        by_cases hpi : p = i
        · have hpm : ¬ p = m := by rw [hpi]; exact him'
          simp only [if_pos hpi, if_neg hpm, mul_one]
        · by_cases hpm : p = m
          · simp only [if_neg hpi, if_pos hpm, one_mul]
          · simp only [if_neg hpi, if_neg hpm, mul_one]
            exact gaussianZerothMoment_oneD τ hτ
      rw [hstep, ← Finset.prod_subset (Finset.subset_univ ({i, m} : Finset (Fin n))) hout,
          Finset.prod_pair him', if_pos rfl, if_neg him, if_pos rfl]
    rw [hprodeq]
    have hMh : (∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)|) ≤ τ⁻¹ :=
      hk_absHess_moment_le τ hτ
    have hMhnn : 0 ≤ ∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| :=
      integral_nonneg (fun y => mul_nonneg (heatKernel1D_pos τ y hτ).le (abs_nonneg _))
    have hM2 : (∫ y : ℝ, heatKernel1D τ y * y ^ 2) = 2 * τ := gaussianSecondMoment_oneD τ hτ
    have hcalc : (∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)|)
          * (∫ y : ℝ, heatKernel1D τ y * y ^ 2) ≤ 2 := by
      rw [hM2]
      calc (∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)|) * (2 * τ)
          ≤ τ⁻¹ * (2 * τ) := by
            refine mul_le_mul_of_nonneg_right hMh (by positivity)
        _ = 2 := by field_simp
    have h1s : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h2le : (2 : ℝ) ≤ 32 * Real.sqrt 2 + 1 := by nlinarith [h1s]
    exact le_trans hcalc h2le

/-! ###############################################################################
    ### The domination integrabilities (via `hessAbs_coordSq_integrable`).
    ############################################################################### -/

/-- `hessGaussFactor i τ · z_j` is integrable (dominated by `|hess| + |hess|·z_j²`). -/
theorem hessGaussFactor_coord_integrable (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) :
    Integrable (fun z : Point n => hessGaussFactor i τ z * z j) volume := by
  refine Integrable.mono'
    (((hessGaussFactor_integrable τ hτ i).abs).add (hessAbs_coordSq_integrable τ hτ i j))
    ((hessGaussFactor_continuous τ i).mul (continuous_apply j)).aestronglyMeasurable
    (ae_of_all _ (fun z => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |z j| ≤ 1 + (z j) ^ 2 := by
    nlinarith [sq_nonneg (|z j| - 1), sq_abs (z j), abs_nonneg (z j)]
  calc |hessGaussFactor i τ z| * |z j|
      ≤ |hessGaussFactor i τ z| * (1 + (z j) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |hessGaussFactor i τ z| + |hessGaussFactor i τ z| * (z j) ^ 2 := by ring

/-- `hessGaussFactor i τ · (z_j·z_k)` is integrable (dominated by `|hess|·z_j² + |hess|·z_k²`). -/
theorem hessGaussFactor_coordPair_integrable (τ : ℝ) (hτ : 0 < τ) (i j k : Fin n) :
    Integrable (fun z : Point n => hessGaussFactor i τ z * (z j * z k)) volume := by
  refine Integrable.mono'
    ((hessAbs_coordSq_integrable τ hτ i j).add (hessAbs_coordSq_integrable τ hτ i k))
    ((hessGaussFactor_continuous τ i).mul ((continuous_apply j).mul (continuous_apply k))).aestronglyMeasurable
    (ae_of_all _ (fun z => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |z j * z k| ≤ (z j) ^ 2 + (z k) ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|z j| - |z k|), sq_abs (z j), sq_abs (z k),
      abs_nonneg (z j), abs_nonneg (z k)]
  calc |hessGaussFactor i τ z| * |z j * z k|
      ≤ |hessGaussFactor i τ z| * ((z j) ^ 2 + (z k) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |hessGaussFactor i τ z| * (z j) ^ 2 + |hessGaussFactor i τ z| * (z k) ^ 2 := by ring

/-- **★ per-pair O(1) bound.**  `|∫_z hessGaussFactor i τ z·(z_j z_k)| ≤ 32√2 + 1`.  Via
    `|z_j z_k| ≤ (z_j²+z_k²)/2` and `hessAbs_coordSq_le`. -/
theorem hessGaussFactor_coordPair_abs_le (τ : ℝ) (hτ : 0 < τ) (i j k : Fin n) :
    |∫ z : Point n, hessGaussFactor i τ z * (z j * z k)| ≤ 32 * Real.sqrt 2 + 1 := by
  have hg : Integrable
      (fun z : Point n => (|hessGaussFactor i τ z| * (z j) ^ 2
        + |hessGaussFactor i τ z| * (z k) ^ 2) / 2) volume :=
    ((hessAbs_coordSq_integrable τ hτ i j).add (hessAbs_coordSq_integrable τ hτ i k)).div_const 2
  calc |∫ z : Point n, hessGaussFactor i τ z * (z j * z k)|
      = ‖∫ z : Point n, hessGaussFactor i τ z * (z j * z k)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z : Point n, ‖hessGaussFactor i τ z * (z j * z k)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z : Point n, (|hessGaussFactor i τ z| * (z j) ^ 2
          + |hessGaussFactor i τ z| * (z k) ^ 2) / 2 := by
        refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hg
          (ae_of_all _ (fun z => ?_))
        show ‖hessGaussFactor i τ z * (z j * z k)‖
          ≤ (|hessGaussFactor i τ z| * (z j) ^ 2 + |hessGaussFactor i τ z| * (z k) ^ 2) / 2
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |z j * z k| ≤ ((z j) ^ 2 + (z k) ^ 2) / 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|z j| - |z k|), sq_abs (z j), sq_abs (z k),
            abs_nonneg (z j), abs_nonneg (z k)]
        calc |hessGaussFactor i τ z| * |z j * z k|
            ≤ |hessGaussFactor i τ z| * (((z j) ^ 2 + (z k) ^ 2) / 2) :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = (|hessGaussFactor i τ z| * (z j) ^ 2 + |hessGaussFactor i τ z| * (z k) ^ 2) / 2 := by
              ring
    _ ≤ (32 * Real.sqrt 2 + 1) := by
        rw [integral_div, integral_add (hessAbs_coordSq_integrable τ hτ i j)
          (hessAbs_coordSq_integrable τ hτ i k)]
        have hj := hessAbs_coordSq_le τ hτ i j
        have hk := hessAbs_coordSq_le τ hτ i k
        linarith

/-! ###############################################################################
    ### ★★★ THE O(1) SIGNED SLICE BOUND.
    ############################################################################### -/

/-- **★★★ `hessGauss_signed_slice_O1` — THE O(1) SIGNED SLICE BOUND.**  For `τ>0`, any base point
    data `c` (constant), `b` (gradient), `H` (Hessian coefficients), the SIGNED slice integral of the
    Hessian-Gaussian factor against the degree-≤2 amplitude `B(z)=c+Σ_j b_j z_j+Σ_{jk}H_{jk}z_j z_k`
    obeys the O(1)-in-`τ` (a-independent) bound
      `|∫_z hessGaussFactor i τ z · B(z)| ≤ (32√2 + 1)·Σ_{jk}|H_{jk}|`.
    The constant part cancels EXACTLY (`hessGaussFactor_integral_zero`, 0-th moment), the linear part
    cancels EXACTLY (`hessGaussFactor_first_moment_zero`, oddness), only the Hessian part survives and
    is O(1) (`hessGaussFactor_coordPair_abs_le`).  This removes the log-divergence
    (`∫₀^τ O(1) ds = O(τ)`); the surviving Hessian coefficient is the TRANSPORT term whose cancellation
    to O(τ²) is the SEPARATE van-Vleck 2-jet wall.  ⚠ NOT `a₁ = R/6`. -/
theorem hessGauss_signed_slice_O1 (τ : ℝ) (hτ : 0 < τ) (i : Fin n)
    (c : ℝ) (b : Fin n → ℝ) (H : Fin n → Fin n → ℝ) :
    |∫ z : Point n, hessGaussFactor i τ z
        * (c + (∑ j, b j * z j) + (∑ j, ∑ k, H j k * (z j * z k)))|
      ≤ (32 * Real.sqrt 2 + 1) * ∑ j, ∑ k, |H j k| := by
  -- integrabilities
  have hcint : Integrable (fun z : Point n => hessGaussFactor i τ z * c) volume :=
    (hessGaussFactor_integrable τ hτ i).mul_const c
  have hlinint : Integrable (fun z : Point n => hessGaussFactor i τ z * (∑ j, b j * z j)) volume := by
    have he : (fun z : Point n => hessGaussFactor i τ z * (∑ j, b j * z j))
        = fun z => ∑ j, b j * (hessGaussFactor i τ z * z j) := by
      funext z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [he]
    exact integrable_finsetSum _
      (fun j _ => (hessGaussFactor_coord_integrable τ hτ i j).const_mul (b j))
  have hquadint : Integrable
      (fun z : Point n => hessGaussFactor i τ z * (∑ j, ∑ k, H j k * (z j * z k))) volume := by
    have he : (fun z : Point n => hessGaussFactor i τ z * (∑ j, ∑ k, H j k * (z j * z k)))
        = fun z => ∑ j, ∑ k, H j k * (hessGaussFactor i τ z * (z j * z k)) := by
      funext z; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [he]
    exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun k _ => (hessGaussFactor_coordPair_integrable τ hτ i j k).const_mul (H j k)))
  have hAB : Integrable
      (fun z : Point n => hessGaussFactor i τ z * c + hessGaussFactor i τ z * (∑ j, b j * z j))
      volume := hcint.add hlinint
  have hEq : (∫ z : Point n, hessGaussFactor i τ z
        * (c + (∑ j, b j * z j) + (∑ j, ∑ k, H j k * (z j * z k))))
      = ∫ z : Point n, (hessGaussFactor i τ z * c + hessGaussFactor i τ z * (∑ j, b j * z j)
          + hessGaussFactor i τ z * (∑ j, ∑ k, H j k * (z j * z k))) :=
    integral_congr_ae (ae_of_all _ (fun z => by ring))
  have hc0 : (∫ z : Point n, hessGaussFactor i τ z * c) = 0 := by
    rw [integral_mul_const, hessGaussFactor_integral_zero τ hτ i, zero_mul]
  have hlin0 : (∫ z : Point n, hessGaussFactor i τ z * (∑ j, b j * z j)) = 0 := by
    have he : (fun z : Point n => hessGaussFactor i τ z * (∑ j, b j * z j))
        = fun z => ∑ j, b j * (hessGaussFactor i τ z * z j) := by
      funext z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [he, integral_finsetSum _
      (fun j _ => (hessGaussFactor_coord_integrable τ hτ i j).const_mul (b j))]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [integral_const_mul, hessGaussFactor_first_moment_zero τ hτ i j, mul_zero]
  rw [hEq, integral_add hAB hquadint, integral_add hcint hlinint, hc0, hlin0, zero_add, zero_add]
  -- the surviving quadratic part.
  have hquadsum : (∫ z : Point n, hessGaussFactor i τ z * (∑ j, ∑ k, H j k * (z j * z k)))
      = ∑ j, ∑ k, H j k * ∫ z : Point n, hessGaussFactor i τ z * (z j * z k) := by
    have he : (fun z : Point n => hessGaussFactor i τ z * (∑ j, ∑ k, H j k * (z j * z k)))
        = fun z => ∑ j, ∑ k, H j k * (hessGaussFactor i τ z * (z j * z k)) := by
      funext z; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [he, integral_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun k _ => (hessGaussFactor_coordPair_integrable τ hτ i j k).const_mul (H j k)))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum _ (fun k _ => (hessGaussFactor_coordPair_integrable τ hτ i j k).const_mul (H j k))]
    exact Finset.sum_congr rfl (fun k _ => by rw [integral_const_mul])
  rw [hquadsum]
  calc |∑ j, ∑ k, H j k * ∫ z : Point n, hessGaussFactor i τ z * (z j * z k)|
      ≤ ∑ j, |∑ k, H j k * ∫ z : Point n, hessGaussFactor i τ z * (z j * z k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, |H j k * ∫ z : Point n, hessGaussFactor i τ z * (z j * z k)| :=
        Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j, ∑ k, |H j k| * (32 * Real.sqrt 2 + 1) := by
        refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_))
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hessGaussFactor_coordPair_abs_le τ hτ i j k) (abs_nonneg _)
    _ = (32 * Real.sqrt 2 + 1) * ∑ j, ∑ k, |H j k| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)

end QIQTH.SliceBoundO1

/-! ###############################################################################
    ## J4-500 LEDGER — the O(1) SIGNED SLICE BOUND (log-divergence removed).
    ###############################################################################

  WHAT LANDS.  `hessGauss_signed_slice_O1` bounds the SIGNED slice integral of the Hessian-Gaussian
  factor against a degree-≤2 amplitude by `(32√2+1)·Σ|H_{jk}|`, an O(1)-in-`a` quantity (uniform as
  `a→0⁺`).  The constant/linear parts cancel EXACTLY (signed 0-th/1-st moments); only the Hessian part
  survives, controlled by the O(1) mixed second moment `∫|hessGaussFactor i|·z_m² ≤ 32√2+1`.

  ⚠ HONEST DISTANCE.  This is `O(1/a) → O(1)` (removing the log-divergence `∫₀^τ C/(τ−s)ds = +∞`),
  giving `∫₀^τ O(1) ds = O(τ)` — a MARGINAL q=1 correction, NOT `O(τ²)`.  It is NOT `O(1/a)→O(a)`.
  The surviving O(1) is a TRANSPORT COEFFICIENT (the amplitude Hessian); its cancellation to O(τ²) is
  the SEPARATE, irreducible van-Vleck 2-jet wall `D²u₀(0)=(1/6)Ric` (VanVleckRadial const-curv-only),
  which this brick does NOT close.  ⚠ NOT `a₁ = R/6`.
-/

section AxiomChecks
open QIQTH.SliceBoundO1
#print axioms oneD_hessW_lin_zero
#print axioms oneD_hessW_sq_moment_le
#print axioms hessGaussFactor_first_moment_zero
#print axioms hessAbs_coordSq_le
#print axioms hessGaussFactor_coordPair_abs_le
#print axioms hessGauss_signed_slice_O1
end AxiomChecks
