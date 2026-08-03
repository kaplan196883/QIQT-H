/-
  InnerSliceBounds — J4-134: discharging the per-slice INNER bounds `hInner1`/`hInner2`
  carried by the J4-133 sliver assembly (`witness_sliver2_assembly`, `SliverAssembly.lean`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS BRICK IS.  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`,
  and proves NOTHING about `R/6`.  It discharges the two CRUDE per-slice inner bounds carried as
  hypotheses by the S6 assembly:
    • `hInner1` — the gradient slice `|∫ z, sTerm1 τ z · F s z 0| ≤ C₁·(u−s)^{−1/2}`;
    • `hInner2` — the mass slice `|∫ z, sTerm2 τ z · F s z 0| ≤ C₂` (`O(1)`).
  The Hessian slice `hInner0` (the "prize", requiring the entangled `G_τ(Y z)`-Hermite cancellation
  + a `‖z‖⁵` moment) remains a CARRIED input of the assembly — see the FIREWALL note below; it is a
  genuine multi-file effort per the `SliverAssembly` firewall and is not attempted here.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE ENTANGLED-ARGUMENT STRUCTURE.  The concrete normal-form slices (`SliverAssembly.sTerm1/2`)
  evaluate the Gaussian at the INVERSE-CHART image `Y z` (not at `z`):
      `sTerm1 τ z = 2·G_τ(Y z)·(−⟨Y z,P z⟩/2τ)·A₁ τ z`,      `sTerm2 τ z = G_τ(Y z)·A₂ τ z`.
  The single geometric input that tames the entangled argument is the ℓ²-COERCIVITY
  `hco : ½·r²_z ≤ r²_{Y z}` (`rncRadialSq`), which — via `Gk_anti` + `Gk_scaled` (the exact route of
  `ChartGaussAdapter.chartDiff_integrableOn` / `GaussianMomentEnvelope.gaussDdim_replace_bound`) —
  gives the pointwise domination `G_τ(Y z) ≤ (√2)ⁿ·G_{2τ}(z)` (`gaussDdim_halfcoer_le`, landed here).
  From there the two crude slices reduce to the banked machinery:
    • mass slice: `G_{2τ}(z)·G_{2s}(z)` integrates to the product-Gaussian peak `G_{2τ+2s}(0)`
      (`gaussDdim_selfmul_integral`), capped `s`-uniformly by `G_a(0)` (width-antitone);
    • gradient slice: `|⟨Y z,P z⟩| ≤ n·‖Y z‖·‖P z‖` (`abs_inner_le`) with the displacement
      `‖Y z + z‖ ≤ C_W‖z‖²` (`normY_le`) and jet modulus `‖P z − eᵢ‖ ≤ C_P‖z‖` gives a cubic
      polynomial `n(‖z‖ + (C_W+C_P)‖z‖² + C_W C_P‖z‖³)`, whose `G_{2τ}`-moments (`S4b`
      `pow_norm_mul_gauss_integral`, `k = 1,2,3`) divided by `τ` all land `≤ C·τ^{−1/2}` on `(0,τ₀]`.

  ⚠ HONEST FIREWALL — the carry list of `hInner1_discharge`/`hInner2_discharge` (each a genuine fact,
    NONE the conclusion, none vacuous, all satisfiable by the true chart pullback — e.g. the model
    `Y = −id`, `P = eᵢ`, `Q = 0`, `A_j` bounded satisfies every hypothesis simultaneously):
      • `hco` — the global ℓ²-coercivity `∀ z, ½·r²_z ≤ r²_{Y z}` (near-isometry lower bound; the
        `c = 1/2` shape of `InverseChartDisplacement.chartW0_nearIsometry`).  SATISFIABLE (`Y = −id`
        gives `r²_{Y z} = r²_z ≥ ½ r²_z`).  NON-vacuous (constrains `Y` to be radially coercive).
      • `hYdisp` — the inverse-chart displacement `∀ z, ‖Y z + z‖ ≤ C_W‖z‖²`
        (`chartW0_displacement`; the QUADRATIC gain that makes the gradient slice `τ^{−1/2}`).
      • `hJ3` — the first-jet modulus `∀ z, ‖P z − eᵢ‖ ≤ C_P‖z‖` (the labelled `J3` jet bound).
      • `hAbdd` — the amplitude sup bound (`M₁`/`M₂`); `hFdom` — the width-2 `F`-domination
        (the repo `hFdom` shape, `B_le_MB`-cappable).
    LANDED unconditionally (all std-3, axiom-free): `gaussDdim_halfcoer_le`,
      `gaussDdim_selfmul_integrable`, `gaussDdim_selfmul_integral`, `normP_le`, `hInner1_discharge`
      (the gradient `C₁·(u−s)^{−1/2}` slice), `hInner2_discharge`
      (the mass `C₂ = (√2)ⁿ M₂ C_L G_a(0)` slice).
    NOT attempted (carried by the assembly): `hInner0` (Hessian slice) — the entangled Hermite
      cancellation `gaussian_hessian_cancel` on `G_τ(Y z)` + the `‖z‖⁵`-moment envelope (the k=5 1-D
      moment is not banked); a genuine multi-file effort.  NOT `a₁ = R/6`.
    No `sorry`, no new axioms, no `expRho` in statements.  Reusable analytic BRICK.
-/
import Mathlib
import QIQTH.SliverAssembly
import QIQTH.GaussianMomentEnvelope
import QIQTH.ModelIntegrableW
import QIQTH.GaussianConvolution

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ★ The coercivity-driven argument-substitution domination.
    ############################################################################### -/

/-- **★ ARGUMENT-SUBSTITUTION DOMINATION (`c = 1/2`).**  From the ℓ²-coercivity
    `½·r²_z ≤ r²_w` (the near-isometry lower bound, `rncRadialSq`), the Gaussian evaluated at the
    entangled argument `w` is dominated by a width-doubled plain Gaussian in `z`:
      `gaussDdim τ w ≤ (√2)ⁿ · gaussDdim (2τ) z`.
    Route: `gaussDdim τ w = Gk τ r²_w ≤ Gk τ (½ r²_z)` (`Gk_anti`) `= (√½)⁻ⁿ·gaussDdim (τ/½) z`
    (`Gk_scaled`), with `(√½)⁻¹ = √2` and `τ/½ = 2τ`.  (Same route as `chartDiff_integrableOn`.) -/
theorem gaussDdim_halfcoer_le (τ : ℝ) (hτ : 0 < τ) (w z : Point n)
    (hco : (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq w) :
    gaussDdim τ w ≤ (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
  have hs2 : (Real.sqrt (1 / 2 : ℝ))⁻¹ = Real.sqrt 2 := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ from by norm_num, Real.sqrt_inv, inv_inv]
  calc gaussDdim τ w = Gk n τ (rncRadialSq w) := gaussDdim_eq_Gk τ w
    _ ≤ Gk n τ ((1 / 2 : ℝ) * rncRadialSq z) := Gk_anti τ hτ hco
    _ = (Real.sqrt (1 / 2 : ℝ))⁻¹ ^ n * gaussDdim (τ / (1 / 2)) z :=
        Gk_scaled (1 / 2) τ (by norm_num) hτ z
    _ = (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
        rw [hs2, show τ / (1 / 2 : ℝ) = 2 * τ from by ring]

/-! ###############################################################################
    Product-Gaussian mass helpers (same point `z`, two widths).
    ############################################################################### -/

/-- `z ↦ gaussDdim a z · gaussDdim b z` is integrable (from the convolution-shape integrability
    `gaussDdim_mul_integrable` at `x = y = 0`, via evenness). -/
theorem gaussDdim_selfmul_integrable (a b : ℝ) :
    Integrable (fun z : Point n => gaussDdim a z * gaussDdim b z) volume := by
  refine (gaussDdim_mul_integrable a b (0 : Point n) 0).congr (ae_of_all _ (fun z => ?_))
  simp only [gaussDdim_zero_sub, sub_zero]

/-- **The same-point product-Gaussian mass.**  `∫_z gaussDdim a z · gaussDdim b z = gaussDdim (a+b) 0`
    (`gaussDdim_conv` at `x = y = 0`, via evenness). -/
theorem gaussDdim_selfmul_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ z : Point n, gaussDdim a z * gaussDdim b z = gaussDdim (a + b) (0 : Point n) := by
  calc ∫ z : Point n, gaussDdim a z * gaussDdim b z
      = ∫ z : Point n, gaussDdim a (0 - z) * gaussDdim b (z - 0) :=
        integral_congr_ae (ae_of_all _ (fun z => by simp only [gaussDdim_zero_sub, sub_zero]))
    _ = gaussDdim (a + b) ((0 : Point n) - 0) := gaussDdim_conv a b ha hb 0 0
    _ = gaussDdim (a + b) (0 : Point n) := by rw [sub_zero]

/-! ###############################################################################
    ★ I2 — the mass slice `hInner2` discharge (`O(1)`).
    ############################################################################### -/

/-- **★ I2 — THE MASS-SLICE DISCHARGE (`hInner2`).**  For the entangled mass slice
    `sTerm2 τ z = G_τ(Y z)·A₂ τ z`, under the coercivity `hco`, amplitude bound `hA2bdd`, and the
    width-2 `F`-domination `hFdom`, the terminal per-slice mass integral is `O(1)`:
      `∀ s ∈ Ioo (u−ε) u,  |∫ z, sTerm2 Y A₂ (u−s) z · F s z 0| ≤ (√2)ⁿ·M₂·C_L·gaussDdim a 0`.
    Route: `|·| ≤ (√2)ⁿ M₂ C_L·(G_{2(u−s)}(z)·G_{2s}(z))` pointwise (`gaussDdim_halfcoer_le`), then
    the product-Gaussian mass `G_{2(u−s)+2s}(0)` (`gaussDdim_selfmul_integral`), capped by `G_a(0)`
    (width-antitone, `a ≤ 2s`).  EXACTLY the `hInner2` shape of `witness_sliver2_assembly`.
    NOT `a₁ = R/6`. -/
theorem hInner2_discharge
    (Y : Point n → Point n) (A2 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (M₂ C_L T a u ε : ℝ)
    (hM₂ : 0 ≤ M₂) (hC_L : 0 ≤ C_L)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεa : ε < a / 2)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hA2bdd : ∀ τ, ∀ z : Point n, |A2 τ z| ≤ M₂)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, sTerm2 Y A2 (u - s) z * F s z 0|
        ≤ (Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n) := by
  intro s hsmem
  have hτpos : 0 < u - s := by linarith [hsmem.2]
  have hlo : u - ε > a / 2 := by linarith
  have hspos : 0 < s := by linarith [hsmem.1, hlo]
  have hsT : s ≤ T := by linarith [hsmem.2, huT]
  have hsa2 : a / 2 ≤ s := by linarith [hsmem.1, hlo]
  have has : a ≤ 2 * s := by linarith
  set τ : ℝ := u - s with hτ_def
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  have h2s : (0 : ℝ) < 2 * s := by linarith
  set K : ℝ := (Real.sqrt 2) ^ n * M₂ * C_L with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  -- pointwise domination
  have hpt : ∀ z : Point n, ‖sTerm2 Y A2 τ z * F s z 0‖
      ≤ K * (gaussDdim (2 * τ) z * gaussDdim (2 * s) z) := by
    intro z
    rw [Real.norm_eq_abs, sTerm2, abs_mul, abs_mul,
        abs_of_nonneg (gaussDdim_nonneg' τ (Y z))]
    have hG : gaussDdim τ (Y z) ≤ (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
      gaussDdim_halfcoer_le τ hτpos (Y z) z (hco z)
    have hFz : |F s z 0| ≤ C_L * gaussDdim (2 * s) z := by
      have := hFdom s hspos hsT z 0; rwa [sub_zero] at this
    calc gaussDdim τ (Y z) * |A2 τ z| * |F s z 0|
        ≤ ((Real.sqrt 2) ^ n * gaussDdim (2 * τ) z) * M₂ * (C_L * gaussDdim (2 * s) z) := by
          refine mul_le_mul (mul_le_mul hG (hA2bdd τ z) (abs_nonneg _)
            (mul_nonneg (by positivity) (gaussDdim_nonneg' _ _))) hFz (abs_nonneg _)
            (mul_nonneg (mul_nonneg (by positivity) (gaussDdim_nonneg' _ _)) hM₂)
      _ = K * (gaussDdim (2 * τ) z * gaussDdim (2 * s) z) := by rw [hKdef]; ring
  -- dominating integrability
  have hdomint : Integrable
      (fun z : Point n => K * (gaussDdim (2 * τ) z * gaussDdim (2 * s) z)) volume :=
    (gaussDdim_selfmul_integrable (2 * τ) (2 * s)).const_mul K
  calc |∫ z, sTerm2 Y A2 τ z * F s z 0|
      = ‖∫ z, sTerm2 Y A2 τ z * F s z 0‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, ‖sTerm2 Y A2 τ z * F s z 0‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, K * (gaussDdim (2 * τ) z * gaussDdim (2 * s) z) :=
        integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hdomint (ae_of_all _ hpt)
    _ = K * ∫ z, gaussDdim (2 * τ) z * gaussDdim (2 * s) z := integral_const_mul _ _
    _ = K * gaussDdim (2 * τ + 2 * s) (0 : Point n) := by
        rw [gaussDdim_selfmul_integral (2 * τ) (2 * s) h2τ h2s]
    _ ≤ K * gaussDdim a (0 : Point n) :=
        mul_le_mul_of_nonneg_left (gaussDdim_zero_antitone ha (by linarith)) hKnn
    _ = (Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n) := by rw [hKdef]

/-! ###############################################################################
    ★ I1 — the gradient slice `hInner1` discharge (`(u−s)^{−1/2}`, CRUDE).
    ############################################################################### -/

/-- `‖P z‖ ≤ 1 + C_P·‖z‖` from `‖P z − eᵢ‖ ≤ C_P‖z‖`. -/
theorem normP_le (Pv : Point n) (i : Fin n) (CP r : ℝ)
    (hJ : ‖Pv - unitVec i‖ ≤ CP * r) : ‖Pv‖ ≤ 1 + CP * r := by
  calc ‖Pv‖ = ‖(Pv - unitVec i) + unitVec i‖ := by rw [sub_add_cancel]
    _ ≤ ‖Pv - unitVec i‖ + ‖(unitVec i : Point n)‖ := norm_add_le _ _
    _ ≤ CP * r + 1 := add_le_add hJ (norm_single_le_one i)
    _ = 1 + CP * r := by ring

/-- **★ I1 — THE GRADIENT-SLICE DISCHARGE (`hInner1`).**  For the entangled gradient slice
    `sTerm1 τ z = 2·G_τ(Y z)·(−⟨Y z,P z⟩/2τ)·A₁ τ z`, under the coercivity `hco`, the quadratic
    displacement `hYdisp` (`‖Y z + z‖ ≤ C_W‖z‖²`), the jet modulus `hJ3` (`‖P z − eᵢ‖ ≤ C_P‖z‖`),
    the amplitude bound `hA1bdd`, and the width-2 `F`-domination `hFdom`, the terminal per-slice
    gradient integral has the `(u−s)^{−1/2}` rate:
      `∀ s ∈ Ioo (u−ε) u,  |∫ z, sTerm1 Y P A₁ (u−s) z · F s z 0| ≤ C₁·(u−s)^{−1/2}`,
    with `C₁` the explicit combination (see `hC₁_def`).  Route: `G_τ(Y z) ≤ (√2)ⁿ G_{2τ}(z)`
    (`gaussDdim_halfcoer_le`); `|⟨Y z,P z⟩| ≤ n(‖z‖+C_W‖z‖²)(1+C_P‖z‖)` (`abs_inner_le`+`normY_le`
    +`normP_le`) = `P₁‖z‖+P₂‖z‖²+P₃‖z‖³`; the `G_{2τ}`-moments `k = 1,2,3`
    (`pow_norm_mul_gauss_integral`) divided by `τ` all bound by `C·(√τ)⁻¹` on `(0,τ₀]`.  EXACTLY the
    `hInner1` shape of `witness_sliver2_assembly`.  CRUDE (no cancellation).  NOT `a₁ = R/6`. -/
theorem hInner1_discharge
    (Y P : Point n → Point n) (A1 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₁ C_L T a u ε τ₀ C_W C_P : ℝ)
    (hM₁ : 0 ≤ M₁) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hA1bdd : ∀ τ, ∀ z : Point n, |A1 τ z| ≤ M₁)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, sTerm1 Y P A1 (u - s) z * F s z 0|
        ≤ ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
            * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
              + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
              + ((n : ℝ) * C_W * C_P)
                * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀)))
          * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro s hsmem
  have hτpos : 0 < u - s := by linarith [hsmem.2]
  have hlo : u - ε > a / 2 := by linarith
  have hspos : 0 < s := by linarith [hsmem.1, hlo]
  have hsT : s ≤ T := by linarith [hsmem.2, huT]
  have hsa2 : a / 2 ≤ s := by linarith [hsmem.1, hlo]
  have hττ₀ : u - s ≤ τ₀ := by linarith [hsmem.1, hετ₀]
  set τ : ℝ := u - s with hτ_def
  have hτne : τ ≠ 0 := hτpos.ne'
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  have hτ0 : (0 : ℝ) < τ₀ := lt_of_lt_of_le hτpos hττ₀
  -- constants
  set C_F : ℝ := C_L * gaussDdim a (0 : Point n) with hCF_def
  have hCFnn : 0 ≤ C_F := by rw [hCF_def]; exact mul_nonneg hC_L (gaussDdim_nonneg' _ _)
  -- F cap (B_le_MB peak bound)
  have hFcap : ∀ z : Point n, |F s z 0| ≤ C_F :=
    fun z => B_le_MB F C_L T a hC_L hFdom ha s hsa2 hsT z
  set K : ℝ := (Real.sqrt 2) ^ n * M₁ * C_F with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  set P₁ : ℝ := (n : ℝ) with hP₁_def
  set P₂ : ℝ := (n : ℝ) * (C_W + C_P) with hP₂_def
  set P₃ : ℝ := (n : ℝ) * C_W * C_P with hP₃_def
  have hP₁nn : 0 ≤ P₁ := by rw [hP₁_def]; positivity
  have hP₂nn : 0 ≤ P₂ := by rw [hP₂_def]; positivity
  have hP₃nn : 0 ≤ P₃ := by rw [hP₃_def]; positivity
  -- the cubic polynomial bound on |⟨Y z, P z⟩|
  have hpoly : ∀ z : Point n,
      |∑ k, Y z k * P z k| ≤ P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3 := by
    intro z
    have hYn : ‖Y z‖ ≤ C_W * ‖z‖ ^ 2 + ‖z‖ := normY_le (Y z) z (C_W * ‖z‖ ^ 2) (hYdisp z)
    have hPn : ‖P z‖ ≤ 1 + C_P * ‖z‖ := normP_le (P z) i C_P ‖z‖ (hJ3 z)
    have hYnn : 0 ≤ ‖Y z‖ := norm_nonneg _
    have hcast : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    calc |∑ k, Y z k * P z k|
        ≤ (n : ℝ) * ‖Y z‖ * ‖P z‖ := abs_inner_le (Y z) (P z)
      _ ≤ (n : ℝ) * (C_W * ‖z‖ ^ 2 + ‖z‖) * (1 + C_P * ‖z‖) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hYn hcast) hPn (norm_nonneg _)
            (mul_nonneg hcast (le_trans hYnn hYn))
      _ = P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3 := by
          rw [hP₁_def, hP₂_def, hP₃_def]; ring
  -- pointwise domination by the moment dominating function
  have hpt : ∀ z : Point n, ‖sTerm1 Y P A1 τ z * F s z 0‖
      ≤ K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
          + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
          + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) := by
    intro z
    have hG2nn : 0 ≤ gaussDdim (2 * τ) z := gaussDdim_nonneg' (2 * τ) z
    have hGle : gaussDdim τ (Y z) ≤ (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
      gaussDdim_halfcoer_le τ hτpos (Y z) z (hco z)
    have hpolyz : |∑ k, Y z k * P z k| ≤ P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3 := hpoly z
    have hpolynn : 0 ≤ P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3 := le_trans (abs_nonneg _) hpolyz
    -- ‖sTerm1 · F‖ as a single-fraction product form
    have habs : ‖sTerm1 Y P A1 τ z * F s z 0‖
        = gaussDdim τ (Y z) * |∑ k, Y z k * P z k| * |A1 τ z| * |F s z 0| / τ := by
      rw [Real.norm_eq_abs, sTerm1, abs_mul, abs_mul, abs_mul, abs_mul, abs_div, abs_neg, abs_two,
          abs_of_nonneg (gaussDdim_nonneg' τ (Y z)),
          abs_of_pos (show (0 : ℝ) < 2 * τ by linarith)]
      field_simp
    rw [habs, div_eq_mul_inv]
    -- the numerator product bound
    have hnum : gaussDdim τ (Y z) * |∑ k, Y z k * P z k| * |A1 τ z| * |F s z 0|
        ≤ ((Real.sqrt 2) ^ n * gaussDdim (2 * τ) z)
            * (P₁ * ‖z‖ + P₂ * ‖z‖ ^ 2 + P₃ * ‖z‖ ^ 3) * M₁ * C_F :=
      mul_le_mul
        (mul_le_mul
          (mul_le_mul hGle hpolyz (abs_nonneg _) (mul_nonneg (by positivity) hG2nn))
          (hA1bdd τ z) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by positivity) hG2nn) hpolynn))
        (hFcap z) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hG2nn) hpolynn) hM₁)
    have hfin : gaussDdim τ (Y z) * |∑ k, Y z k * P z k| * |A1 τ z| * |F s z 0|
        ≤ K * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z) + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
            + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) :=
      le_trans hnum (le_of_eq (by rw [hKdef]; ring))
    calc gaussDdim τ (Y z) * |∑ k, Y z k * P z k| * |A1 τ z| * |F s z 0| * τ⁻¹
        ≤ (K * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z) + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
            + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))) * τ⁻¹ :=
          mul_le_mul_of_nonneg_right hfin (by positivity)
      _ = K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
            + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
            + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) := by rw [one_div]; ring
  -- dominating function integrability
  have hbase_int : Integrable (fun z : Point n =>
      P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z) + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
        + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) volume :=
    (((normPow_gauss_integrable 1 (by norm_num) (2 * τ) h2τ).const_mul P₁).add
      ((normPow_gauss_integrable 2 (by norm_num) (2 * τ) h2τ).const_mul P₂)).add
      ((normPow_gauss_integrable 3 (by norm_num) (2 * τ) h2τ).const_mul P₃)
  have hdom_int : Integrable (fun z : Point n =>
      K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
        + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)
        + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))) volume :=
    hbase_int.const_mul _
  -- the moment values
  have hm1 : ∫ z : Point n, ‖z‖ ^ 1 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1 :=
    pow_norm_mul_gauss_integral 1 (by norm_num) 2 (by norm_num) τ hτpos (3 / 2) (by norm_num)
      (oneD_absMoment1 (2 * τ) h2τ)
  have hm2 : ∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2 :=
    pow_norm_mul_gauss_integral 2 (by norm_num) 2 (by norm_num) τ hτpos 2 (by norm_num)
      (oneD_absMoment2 (2 * τ) h2τ)
  have hm3 : ∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3 :=
    pow_norm_mul_gauss_integral 3 (by norm_num) 2 (by norm_num) τ hτpos (64 * Real.sqrt 2 + 1)
      (by positivity) (oneD_absMoment3 (2 * τ) h2τ)
  -- integral of the dominating function
  have hI1 := (normPow_gauss_integrable 1 (by norm_num) (2 * τ) h2τ (n := n)).const_mul P₁
  have hI2 := (normPow_gauss_integrable 2 (by norm_num) (2 * τ) h2τ (n := n)).const_mul P₂
  have hI3 := (normPow_gauss_integrable 3 (by norm_num) (2 * τ) h2τ (n := n)).const_mul P₃
  have e1 : (∫ z : Point n, P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
        + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z) := integral_add hI1 hI2
  have e2 : (∫ z : Point n, (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
          + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z)) + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
          + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) := integral_add (hI1.add hI2) hI3
  have hDval : ∫ z : Point n, K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
        + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z) + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))
      = K * (1 / τ) * (P₁ * (∫ z : Point n, ‖z‖ ^ 1 * gaussDdim (2 * τ) z)
          + P₂ * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z)
          + P₃ * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)) := by
    rw [integral_const_mul, e2, e1, integral_const_mul, integral_const_mul, integral_const_mul]
  -- the analytic core: everything ≤ C₁ · (√τ)⁻¹
  have hwpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτpos
  have hwne : Real.sqrt τ ≠ 0 := hwpos.ne'
  have hwsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτpos.le
  have hww₀ : Real.sqrt τ ≤ Real.sqrt τ₀ := Real.sqrt_le_sqrt hττ₀
  -- main inequality
  have hmain : |∫ z, sTerm1 Y P A1 τ z * F s z 0|
      ≤ K * (1 / τ) * (P₁ * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
          + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
          + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)) := by
    calc |∫ z, sTerm1 Y P A1 τ z * F s z 0|
        = ‖∫ z, sTerm1 Y P A1 τ z * F s z 0‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖sTerm1 Y P A1 τ z * F s z 0‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, K * (1 / τ) * (P₁ * (‖z‖ ^ 1 * gaussDdim (2 * τ) z)
              + P₂ * (‖z‖ ^ 2 * gaussDdim (2 * τ) z) + P₃ * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hdom_int (ae_of_all _ hpt)
      _ = K * (1 / τ) * (P₁ * (∫ z : Point n, ‖z‖ ^ 1 * gaussDdim (2 * τ) z)
            + P₂ * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim (2 * τ) z)
            + P₃ * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)) := hDval
      _ ≤ K * (1 / τ) * (P₁ * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
            + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
            + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKnn (by positivity))
          exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hm1 hP₁nn)
            (mul_le_mul_of_nonneg_left hm2 hP₂nn)) (mul_le_mul_of_nonneg_left hm3 hP₃nn)
  refine le_trans hmain ?_
  -- final algebra: substitute w := √τ (τ = w·w) to make everything a pure polynomial in w.
  rw [← inv_sqrt_eq_rpow τ hτpos]
  have hsq : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτpos.le
  set w : ℝ := Real.sqrt τ with hwdef
  -- goal now uses `w` for √τ and `w⁻¹` for (√τ)⁻¹; the only remaining `τ` is in `1/τ`.
  rw [← hsq]
  -- the deterministic pure-`w` identity (no `τ` atom left, so `field_simp; ring` closes it).
  have hlin : K * (1 / (w * w)) * (P₁ * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * w ^ 1)
        + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w ^ 2)
        + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 3))
      = K * w⁻¹ * (P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
          + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w)
          + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 2)) := by
    field_simp
    try ring
  rw [hlin]
  -- bound the (now w-linear) bracket by its `√τ₀`/`τ₀` cap using w ≤ √τ₀ and w² = τ ≤ τ₀.
  have hwle : w ≤ Real.sqrt τ₀ := hww₀
  have hw2le : w ^ 2 ≤ τ₀ := by rw [hwsq]; exact hττ₀
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hbracket :
      P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
        + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w)
        + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 2)
      ≤ P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
        + P₂ * ((4 * (n : ℝ)) * Real.sqrt τ₀)
        + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) := by
    have ht2 : P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w) ≤ P₂ * ((4 * (n : ℝ)) * Real.sqrt τ₀) := by
      apply mul_le_mul_of_nonneg_left _ hP₂nn
      rw [hsqrt2sq]
      calc (n : ℝ) * 2 * 2 * w = (4 * (n : ℝ)) * w := by ring
        _ ≤ (4 * (n : ℝ)) * Real.sqrt τ₀ := mul_le_mul_of_nonneg_left hwle (by positivity)
    have ht3 : P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 2)
        ≤ P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) := by
      apply mul_le_mul_of_nonneg_left _ hP₃nn
      apply mul_le_mul_of_nonneg_left hw2le (by positivity)
    linarith [ht2, ht3]
  have hKwnn : 0 ≤ K * w⁻¹ := mul_nonneg hKnn (inv_nonneg.mpr hwpos.le)
  calc K * w⁻¹ * (P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
          + P₂ * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * w)
          + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 2))
      ≤ K * w⁻¹ * (P₁ * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
          + P₂ * ((4 * (n : ℝ)) * Real.sqrt τ₀)
          + P₃ * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀)) :=
        mul_le_mul_of_nonneg_left hbracket hKwnn
    _ = ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
            * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
              + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
              + ((n : ℝ) * C_W * C_P)
                * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀))) * w⁻¹ := by
        rw [hKdef, hCF_def, hP₁_def, hP₂_def, hP₃_def]; ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.gaussDdim_halfcoer_le
#print axioms QIQTH.HeatResidualBound.gaussDdim_selfmul_integrable
#print axioms QIQTH.HeatResidualBound.gaussDdim_selfmul_integral
#print axioms QIQTH.HeatResidualBound.normP_le
#print axioms QIQTH.HeatResidualBound.hInner2_discharge
#print axioms QIQTH.HeatResidualBound.hInner1_discharge
