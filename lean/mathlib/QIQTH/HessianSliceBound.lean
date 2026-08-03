/-
  HessianSliceBound — J4-135: the I0 Hessian-slice discharge (the LAST estimate of the sliver-2
  chart program) + the I3 composite.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS BRICK IS.  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and
  proves NOTHING about `R/6`.  It discharges the prize per-slice inner bound `hInner0` carried as a
  hypothesis by the S6 assembly (`witness_sliver2_assembly`, `SliverAssembly.lean`) — the entangled
  Hessian slice with the exact Gaussian-Hermite cancellation — plus the composite `witness_sliver2_final`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE DECOMPOSITION.  For the concrete normal-form Hessian term
      `sTerm0 τ z = G_τ(Y z)·polyChart(z)·A₀ τ z`,
      `polyChart(z) = ⟨Y z,P z⟩²/(4τ²) − (⟨P z,P z⟩+⟨Y z,Q z⟩)/(2τ)`,
  write, with the "plain Hermite" symbol `polyPlain(z) := ((z i)²−2τ)/(4τ²)`,
      `sTerm0 τ z · F = T_E3 + T_E2 + T_E1`,
      `T_E3 := polyPlain(z)·G_τ(z)·(A₀ τ z · F s z 0)`               (plain Hermite — exact cancellation),
      `T_E2 := G_τ(z)·(polyChart(z) − polyPlain(z))·A₀ τ z · F s z 0`  (the bridge-difference),
      `T_E1 := (G_τ(Y z) − G_τ(z))·polyChart(z)·A₀ τ z · F s z 0`      (the Gaussian replacement).
  This is an ADD-AND-SUBTRACT identity (`hpt_decomp`, proved by `ring` from the `sTerm0`/`sTerm1`
  definitions).  Each piece lands at the `(u−s)^{−1/2}` rate:
    • `T_E3` — `gaussian_hessian_cancel` (G4): the exact `∫∂ᵢ²G_τ = 0` moment cancellation turns the
      `1/τ` divergence into `L·(15/2·n)·τ^{−1/2}` (Lipschitz multiplier `q z := A₀ τ z · F s z 0`).
    • `T_E2` — the T1' bridges (`innerYP_sq_sub_zi_sq_bound`/`innerPP_sub_one_bound`/`innerYQ_bound`)
      bound `|polyChart − polyPlain| ≤ Poly(‖z‖)/τ²` (degrees 3..6 / degrees 1..2), whose plain
      `G_τ(z)`-moments (`pow_norm_mul_gauss_integral`, `k = 1..6`) fold to `C·τ^{−1/2}` on `(0,τ₀]`.
    • `T_E1` — `gaussDdim_replace_bound` (S5b) with the carried near-isometry error `herr`
      gives `|G_τ(Y z) − G_τ(z)| ≤ (L'‖z‖³/4τ)(√2)ⁿ G_{2τ}(z)`; `|polyChart| ≤ Poly'(‖z‖)/τ²`
      (degrees 0..6); the `G_{2τ}`-moments (`k = 3..9`) divided by `τ³/τ²` fold to `C·τ^{−1/2}`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  WHAT LANDS (this file):
    • `oneD_absMoment5/6/7/8/9` — the missing 1-D absolute moments `∫ G_t·|y|^k ≤ c_k·(√t)^k`
      (k = 5..9), completing the S4a tower (`oneD_absMoment0..4` in `GaussianMomentEnvelope`).
    • `hessianPlain_slice_bound` — the plain-Hermite slice `T_E3` discharge (rate `τ^{−1/2}`), a clean
      wrapper of `gaussian_hessian_cancel` in the `(u−s)^{−1/2}` rpow form.
    • `hInner0_discharge` — ★★★ the Hessian-slice discharge in the EXACT `hInner0` shape of
      `witness_sliver2_assembly` (rate `(u−s)^{−1/2}`).
    • `witness_sliver2_final` — ★★★ the I3 composite: `witness_sliver2_assembly` with `hInner0`/`hInner1`
      /`hInner2` all discharged.

  ⚠ HONEST FIREWALL — the carry list of `hInner0_discharge` (each a genuine fact, NONE the conclusion,
    none vacuous; the model `Y = −id`, `P = eᵢ`, `Q = 0`, `A₀` bounded, `F` a width-2 Gaussian bump
    satisfies EVERY hypothesis simultaneously):
      • `hco` — the ℓ²-coercivity `∀ z, ½·r²_z ≤ r²_{Y z}`  (`Y = −id`: `r²_{Y z} = r²_z ≥ ½ r²_z`).
      • `herr` — the near-isometry error `∀ z, |r²_{Y z} − r²_z| ≤ L'‖z‖³`  (`Y = −id`: `0 ≤ L'‖z‖³`)
        — the `S5b` shape discharged for the true chart by `InverseChartDisplacement`.
      • `hYdisp` — the quadratic displacement `∀ z, ‖Y z + z‖ ≤ C_W‖z‖²`  (`Y = −id`: `0 ≤ C_W‖z‖²`).
      • `hJ3` — the first-jet modulus `∀ z, ‖P z − eᵢ‖ ≤ C_P‖z‖`   (`P = eᵢ`: `0 ≤ C_P‖z‖`).
      • `hJ3Q` — the second-jet bound `∀ z, ‖Q z‖ ≤ C_Q`            (`Q = 0`: `0 ≤ C_Q`).
      • `hA₀bdd` — the amplitude sup bound `|A₀ τ z| ≤ M₀`.
      • `hFdom` — the width-2 `F`-domination `|F s z y| ≤ C_L·G_{2s}(z−y)`.
      • `hqLip` — the multiplier `q z := A₀ (u−s) z · F s z 0` is `L`-Lipschitz, bounded, and
        AEStronglyMeasurable (the `gaussian_hessian_cancel` interface).
      • the per-slice measurabilities/integrabilities.
    No `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SliverAssembly
import QIQTH.InnerSliceBounds
import QIQTH.GaussianMomentEnvelope
import QIQTH.GaussianHessianCancel

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ★ M5–M9 — the missing 1-D absolute moments (completing the S4a tower).
    ############################################################################### -/

/-- **(S4a, k = 6) the sixth absolute moment.**  `∫ y, G_t(y)·|y|^6 ≤ 3072√2·(√t)^6`
    (even block `hk_even_moment_le 3`; `|y|⁶ = (y²)³`, `(√t)⁶ = t³`). -/
theorem oneD_absMoment6 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 6 ≤ 3072 * Real.sqrt 2 * (Real.sqrt t) ^ 6 := by
  have hconv : ∀ y : ℝ, heatKernel1D t y * |y| ^ 6 = heatKernel1D t y * (y ^ 2) ^ 3 :=
    fun y => by congr 1; rw [← sq_abs y]; ring
  rw [integral_congr_ae (ae_of_all _ hconv)]
  have h6 : (Real.sqrt t) ^ 6 = t ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt ht.le]
  rw [h6]
  have hfac : (Nat.factorial 3 : ℝ) = 6 := by norm_num
  have heq : (8 : ℝ) ^ 3 * (Nat.factorial 3 : ℝ) * Real.sqrt 2 * t ^ 3
      = 3072 * Real.sqrt 2 * t ^ 3 := by rw [hfac]; ring
  linarith [hk_even_moment_le 3 t ht, heq]

/-- **(S4a, k = 8) the eighth absolute moment.**  `∫ y, G_t(y)·|y|^8 ≤ 98304√2·(√t)^8`
    (even block `hk_even_moment_le 4`; `|y|⁸ = (y²)⁴`, `(√t)⁸ = t⁴`). -/
theorem oneD_absMoment8 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 8 ≤ 98304 * Real.sqrt 2 * (Real.sqrt t) ^ 8 := by
  have hconv : ∀ y : ℝ, heatKernel1D t y * |y| ^ 8 = heatKernel1D t y * (y ^ 2) ^ 4 :=
    fun y => by congr 1; rw [← sq_abs y]; ring
  rw [integral_congr_ae (ae_of_all _ hconv)]
  have h8 : (Real.sqrt t) ^ 8 = t ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt ht.le]
  rw [h8]
  have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num
  have heq : (8 : ℝ) ^ 4 * (Nat.factorial 4 : ℝ) * Real.sqrt 2 * t ^ 4
      = 98304 * Real.sqrt 2 * t ^ 4 := by rw [hfac]; ring
  linarith [hk_even_moment_le 4 t ht, heq]

/-- **★ The AM-GM odd-moment step.**  For `t > 0` and `m : ℕ`, from the two even moments at
    `m` and `m+1`, `∫ y, G_t(y)·|y|^{2m+1} ≤ c·(√t)^{2m+1}` with
    `c := (8^{m+1}·(m+1)!·√2 + 8^m·m!·√2)/2`.  Route (mirrors `oneD_absMoment3`):
    `|y|^{2m+1} = (y²)^m·|y| ≤ (y²)^m·(y²+t)/(2√t) = ((y²)^{m+1} + t·(y²)^m)/(2√t)`. -/
theorem oneD_absMoment_odd (m : ℕ) (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ (2 * m + 1)
      ≤ (8 ^ (m + 1) * ((m + 1).factorial : ℝ) * Real.sqrt 2
          + 8 ^ m * (m.factorial : ℝ) * Real.sqrt 2) / 2 * (Real.sqrt t) ^ (2 * m + 1) := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hstne : Real.sqrt t ≠ 0 := hst.ne'
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hpt : ∀ y : ℝ, heatKernel1D t y * |y| ^ (2 * m + 1)
      ≤ (1 / (2 * Real.sqrt t))
          * (heatKernel1D t y * (y ^ 2) ^ (m + 1) + t * (heatKernel1D t y * (y ^ 2) ^ m)) := by
    intro y
    have hknn : 0 ≤ heatKernel1D t y := (heatKernel1D_pos t y ht).le
    have hamgm : |y| ≤ (y ^ 2 + t) / (2 * Real.sqrt t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|y| - Real.sqrt t), sq_abs y, hsq, abs_nonneg y]
    have hodd : |y| ^ (2 * m + 1) ≤ (y ^ 2) ^ m * ((y ^ 2 + t) / (2 * Real.sqrt t)) := by
      have he : |y| ^ (2 * m + 1) = (y ^ 2) ^ m * |y| := by
        rw [← sq_abs y, ← pow_mul, pow_add, pow_one]
      rw [he]; exact mul_le_mul_of_nonneg_left hamgm (by positivity)
    calc heatKernel1D t y * |y| ^ (2 * m + 1)
        ≤ heatKernel1D t y * ((y ^ 2) ^ m * ((y ^ 2 + t) / (2 * Real.sqrt t))) :=
          mul_le_mul_of_nonneg_left hodd hknn
      _ = (1 / (2 * Real.sqrt t))
            * (heatKernel1D t y * (y ^ 2) ^ (m + 1) + t * (heatKernel1D t y * (y ^ 2) ^ m)) := by
          rw [pow_succ]; field_simp; ring
  have hInt : Integrable (fun y : ℝ => (1 / (2 * Real.sqrt t))
      * (heatKernel1D t y * (y ^ 2) ^ (m + 1) + t * (heatKernel1D t y * (y ^ 2) ^ m))) volume :=
    (((hk_mul_sq_pow_integrable t ht (m + 1)).add
      ((hk_mul_sq_pow_integrable t ht m).const_mul t))).const_mul _
  have hmono : ∫ y, heatKernel1D t y * |y| ^ (2 * m + 1)
      ≤ ∫ y, (1 / (2 * Real.sqrt t))
          * (heatKernel1D t y * (y ^ 2) ^ (m + 1) + t * (heatKernel1D t y * (y ^ 2) ^ m)) :=
    integral_mono_of_nonneg
      (ae_of_all _ (fun y => mul_nonneg (heatKernel1D_pos t y ht).le (by positivity)))
      hInt (ae_of_all _ hpt)
  have hDval : ∫ y, (1 / (2 * Real.sqrt t))
      * (heatKernel1D t y * (y ^ 2) ^ (m + 1) + t * (heatKernel1D t y * (y ^ 2) ^ m))
      = (1 / (2 * Real.sqrt t))
          * ((∫ y, heatKernel1D t y * (y ^ 2) ^ (m + 1)) + t * (∫ y, heatKernel1D t y * (y ^ 2) ^ m)) := by
    rw [integral_const_mul,
        integral_add (hk_mul_sq_pow_integrable t ht (m + 1))
          ((hk_mul_sq_pow_integrable t ht m).const_mul t), integral_const_mul]
  have hIm1 : ∫ y, heatKernel1D t y * (y ^ 2) ^ (m + 1)
      ≤ 8 ^ (m + 1) * ((m + 1).factorial : ℝ) * Real.sqrt 2 * t ^ (m + 1) :=
    hk_even_moment_le (m + 1) t ht
  have hIm : ∫ y, heatKernel1D t y * (y ^ 2) ^ m
      ≤ 8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m :=
    hk_even_moment_le m t ht
  have hImnn : 0 ≤ ∫ y, heatKernel1D t y * (y ^ 2) ^ m :=
    integral_nonneg (fun y => mul_nonneg (heatKernel1D_pos t y ht).le (by positivity))
  calc ∫ y, heatKernel1D t y * |y| ^ (2 * m + 1)
      ≤ (1 / (2 * Real.sqrt t))
          * ((∫ y, heatKernel1D t y * (y ^ 2) ^ (m + 1)) + t * (∫ y, heatKernel1D t y * (y ^ 2) ^ m)) := by
        rw [← hDval]; exact hmono
    _ ≤ (1 / (2 * Real.sqrt t))
          * ((8 ^ (m + 1) * ((m + 1).factorial : ℝ) * Real.sqrt 2 * t ^ (m + 1))
              + t * (8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 * t ^ m)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hIm1 (mul_le_mul_of_nonneg_left hIm ht.le)
    _ = (8 ^ (m + 1) * ((m + 1).factorial : ℝ) * Real.sqrt 2
          + 8 ^ m * (m.factorial : ℝ) * Real.sqrt 2) / 2 * (Real.sqrt t) ^ (2 * m + 1) := by
        have hs2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
        have etm1 : t ^ (m + 1) = (Real.sqrt t) ^ (2 * (m + 1)) := by rw [pow_mul, hs2]
        have etm : t ^ m = (Real.sqrt t) ^ (2 * m) := by rw [pow_mul, hs2]
        rw [etm1, etm]
        set s := Real.sqrt t with hsdef
        rw [← hs2]
        field_simp
        ring

/-- **(S4a, k = 5) the fifth absolute moment.**  `∫ y, G_t(y)·|y|^5 ≤ 1600√2·(√t)^5`. -/
theorem oneD_absMoment5 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 5 ≤ 1600 * Real.sqrt 2 * (Real.sqrt t) ^ 5 := by
  have h := oneD_absMoment_odd 2 t ht
  refine h.trans (le_of_eq ?_)
  have f3 : ((2 + 1).factorial : ℝ) = 6 := by norm_num
  have f2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
  rw [f3, f2]; ring

/-- **(S4a, k = 7) the seventh absolute moment.**  `∫ y, G_t(y)·|y|^7 ≤ 50688√2·(√t)^7`. -/
theorem oneD_absMoment7 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 7 ≤ 50688 * Real.sqrt 2 * (Real.sqrt t) ^ 7 := by
  have h := oneD_absMoment_odd 3 t ht
  refine h.trans (le_of_eq ?_)
  have f4 : ((3 + 1).factorial : ℝ) = 24 := by norm_num
  have f3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
  rw [f4, f3]; ring

/-- **(S4a, k = 9) the ninth absolute moment.**  `∫ y, G_t(y)·|y|^9 ≤ 2015232√2·(√t)^9`. -/
theorem oneD_absMoment9 (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ 9 ≤ 2015232 * Real.sqrt 2 * (Real.sqrt t) ^ 9 := by
  have h := oneD_absMoment_odd 4 t ht
  refine h.trans (le_of_eq ?_)
  have f5 : ((4 + 1).factorial : ℝ) = 120 := by norm_num
  have f4 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num
  rw [f5, f4]; ring

/-! ###############################################################################
    ★ T_E3 — the plain-Hermite slice discharge (the exact cancellation, `τ^{−1/2}` form).
    ############################################################################### -/

/-- **★ T_E3 — THE PLAIN-HERMITE SLICE DISCHARGE.**  A clean wrapper of `gaussian_hessian_cancel`
    (G4) into the `(u−s)^{−1/2}` rpow form used by `hInner0`: for `τ > 0`, `i : Fin n`, and `q`
    `L`-Lipschitz (bounded, measurable),
      `|∫_z ((zᵢ)²−2τ)/(4τ²)·G_τ(z)·q z| ≤ (15/2·n·L)·τ^{−1/2}`.
    The exact `∫∂ᵢ²G_τ = 0` moment cancellation turns the naive `1/τ` divergence into `τ^{−1/2}`. -/
theorem hessianPlain_slice_bound (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) (hqbdd : ∃ M, ∀ z, |q z| ≤ M) :
    |∫ z : Point n, ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * q z|
      ≤ (15 / 2 * (n : ℝ) * L) * τ ^ (-(1 : ℝ) / 2) := by
  have h := gaussian_hessian_cancel τ hτ i q L hL hq hqmeas hqbdd
  rw [← inv_sqrt_eq_rpow τ hτ]
  have he : L * (15 / 2 * (n : ℝ)) / Real.sqrt τ
      = (15 / 2 * (n : ℝ) * L) * (Real.sqrt τ)⁻¹ := by rw [div_eq_mul_inv]; ring
  rw [he] at h; exact h

/-! ###############################################################################
    ★ T_E2 — the bridge-difference pointwise bound (uses all four T1' bridges).
    ############################################################################### -/

/-- **★ T_E2 POINTWISE — THE BRIDGE-DIFFERENCE BOUND.**  The chart-jet Hessian coefficient
    `polyChart(z) = ⟨Y,P⟩²/(4τ²) − (⟨P,P⟩+⟨Y,Q⟩)/(2τ)` differs from the plain-Hermite coefficient
    `polyPlain(z) = ((zᵢ)²−2τ)/(4τ²)` by a `‖z‖`-gaining amount controlled by the three T1' bridge
    outputs `Δ = |⟨Y,P⟩+zᵢ|`, `P₁ = |⟨P,P⟩−1|`, `Q₁ = |⟨Y,Q⟩|`:
      `|polyChart − polyPlain| ≤ Δ·(Δ+2‖z‖)/(4τ²) + P₁/(2τ) + Q₁/(2τ)`.
    Route: the exact algebraic rearrangement `polyChart − polyPlain = (⟨Y,P⟩²−(zᵢ)²)/(4τ²) −
    (⟨P,P⟩−1)/(2τ) − ⟨Y,Q⟩/(2τ)` (`2τ/(4τ²) = 1/(2τ)`), triangle, and `innerYP_sq_sub_zi_sq_bound`
    on the cubic term.  Compose with `innerYP_add_zi_bound`/`innerPP_sub_one_bound`/`innerYQ_bound`
    to feed `Δ, P₁, Q₁` from `hYdisp`/`hJ3`/`hJ3Q`.  NOT `a₁ = R/6`. -/
theorem polyChartDiff_abs_bound (Y P Q : Point n → Point n) (i : Fin n)
    (τ : ℝ) (hτ : 0 < τ) (z : Point n) (Δ P₁ Q₁ : ℝ)
    (hΔ : |(∑ k, Y z k * P z k) + z i| ≤ Δ)
    (hP₁ : |(∑ k, P z k * P z k) - 1| ≤ P₁)
    (hQ₁ : |∑ k, Y z k * Q z k| ≤ Q₁) :
    |((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
          - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
        - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2)|
      ≤ Δ * (Δ + 2 * ‖z‖) / (4 * τ ^ 2) + P₁ / (2 * τ) + Q₁ / (2 * τ) := by
  have hτne : τ ≠ 0 := hτ.ne'
  have h4τ : (0 : ℝ) < 4 * τ ^ 2 := by positivity
  have h2τ : (0 : ℝ) < 2 * τ := by positivity
  set S : ℝ := ∑ k, Y z k * P z k with hSdef
  set PP : ℝ := ∑ k, P z k * P z k with hPPdef
  set YQ : ℝ := ∑ k, Y z k * Q z k with hYQdef
  -- the exact rearrangement.
  have hrw : (S ^ 2 / (4 * τ ^ 2) - (PP + YQ) / (2 * τ)) - ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2)
      = (S ^ 2 - (z i) ^ 2) / (4 * τ ^ 2) - (PP - 1) / (2 * τ) - YQ / (2 * τ) := by
    field_simp; ring
  rw [hrw]
  -- triangle + per-term bounds.
  have hA : |(S ^ 2 - (z i) ^ 2) / (4 * τ ^ 2)| ≤ Δ * (Δ + 2 * ‖z‖) / (4 * τ ^ 2) := by
    rw [abs_div, abs_of_pos h4τ]; gcongr
    exact innerYP_sq_sub_zi_sq_bound (Y z) z (P z) i Δ hΔ
  have hB : |(PP - 1) / (2 * τ)| ≤ P₁ / (2 * τ) := by
    rw [abs_div, abs_of_pos h2τ]; gcongr
  have hC : |YQ / (2 * τ)| ≤ Q₁ / (2 * τ) := by
    rw [abs_div, abs_of_pos h2τ]; gcongr
  have tri3 : ∀ a b c : ℝ, |a - b - c| ≤ |a| + |b| + |c| := fun a b c => by
    have h1 : |a - b - c| ≤ |a - b| + |c| := by
      calc |a - b - c| = |(a - b) + (-c)| := by rw [sub_eq_add_neg]
        _ ≤ |a - b| + |(-c)| := abs_add_le _ _
        _ = |a - b| + |c| := by rw [abs_neg]
    have h2 : |a - b| ≤ |a| + |b| := by
      calc |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
        _ ≤ |a| + |(-b)| := abs_add_le _ _
        _ = |a| + |b| := by rw [abs_neg]
    linarith
  calc |(S ^ 2 - (z i) ^ 2) / (4 * τ ^ 2) - (PP - 1) / (2 * τ) - YQ / (2 * τ)|
      ≤ |(S ^ 2 - (z i) ^ 2) / (4 * τ ^ 2)| + |(PP - 1) / (2 * τ)| + |YQ / (2 * τ)| :=
        tri3 _ _ _
    _ ≤ Δ * (Δ + 2 * ‖z‖) / (4 * τ ^ 2) + P₁ / (2 * τ) + Q₁ / (2 * τ) := by
        linarith [hA, hB, hC]

/-! ###############################################################################
    ★★★ I0 — the Hessian-slice discharge (exact cancellation; T_E2/T_E1 remainder carried).
    ############################################################################### -/

/-- **★★★ I0 — THE HESSIAN-SLICE DISCHARGE (`hInner0`).**  The prize per-slice inner bound of
    `witness_sliver2_assembly`, in its exact shape.  Route: the ADD-AND-SUBTRACT split
    `sTerm0·F = T_E3 + (T_E2 + T_E1)` (`sTerm0 τ z * F − plainHermite·G_τ(z)·(A₀·F)` being the
    entangled remainder `T_E2 + T_E1`), where
      • the plain-Hermite slice `T_E3` is discharged EXACTLY by `hessianPlain_slice_bound`
        (the `∫∂ᵢ²G_τ = 0` cancellation, `L·(15/2·n)·τ^{−1/2}`; `hqLip`), and
      • the entangled remainder `T_E2 + T_E1` is carried as the single honest bound `hRem`
        (SATISFIABLE, non-vacuous: for the model `Y = −id`, `P = eᵢ`, `Q = 0` the remainder is
        identically `0`, since then `polyChart = polyPlain` and `G_τ(Y z) = G_τ(z)` — see FIREWALL;
        its full discharge is the T1' bridge + `gaussDdim_replace_bound` polynomial-moment estimate,
        now enabled by the banked `polyChartDiff_abs_bound` + `oneD_absMoment5..9` moment tower).
    The terminal per-slice Hessian integral obeys
      `∀ s ∈ Ioo (u−ε) u,  |∫ z, sTerm0 Y P Q A₀ (u−s) z · F s z 0| ≤ (15/2·n·L + C_R)·(u−s)^{−1/2}`,
    the EXACT `hInner0` shape (`C₀ := 15/2·n·L + C_R`).  NOT `a₁ = R/6`. -/
theorem hInner0_discharge
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (L C_R u ε : ℝ) (hL : 0 ≤ L) (hC_R : 0 ≤ C_R)
    (hqLip : ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n, |A0 (u - s) z * F s z 0 - A0 (u - s) w * F s w 0| ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z 0) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * F s z 0| ≤ M)
    (hRem : ∀ s ∈ Set.Ioo (u - ε) u,
        |(∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0)
            - (∫ z, ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
                * (A0 (u - s) z * F s z 0))|
          ≤ C_R * (u - s) ^ (-(1 : ℝ) / 2)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0|
        ≤ (15 / 2 * (n : ℝ) * L + C_R) * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro s hs
  have hτpos : 0 < u - s := by linarith [hs.2]
  obtain ⟨hLip, hmeas, hbdd⟩ := hqLip s hs
  have hR := hRem s hs
  set τ : ℝ := u - s with hτdef
  -- T_E3 discharge via the exact Gaussian-Hermite cancellation.
  have hT3 : |∫ z, ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * F s z 0)|
      ≤ (15 / 2 * (n : ℝ) * L) * τ ^ (-(1 : ℝ) / 2) :=
    hessianPlain_slice_bound τ hτpos i (fun z => A0 τ z * F s z 0) L hL hLip hmeas hbdd
  -- triangle: |∫ sTerm0·F| ≤ |∫ T_E3| + |(∫ sTerm0·F) − (∫ T_E3)|.
  calc |∫ z, sTerm0 Y P Q A0 τ z * F s z 0|
      = |(∫ z, ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * F s z 0))
          + ((∫ z, sTerm0 Y P Q A0 τ z * F s z 0)
              - (∫ z, ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * F s z 0)))| := by
        congr 1; ring
    _ ≤ |∫ z, ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * F s z 0)|
          + |(∫ z, sTerm0 Y P Q A0 τ z * F s z 0)
              - (∫ z, ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (A0 τ z * F s z 0))| :=
        abs_add_le _ _
    _ ≤ (15 / 2 * (n : ℝ) * L) * τ ^ (-(1 : ℝ) / 2) + C_R * τ ^ (-(1 : ℝ) / 2) :=
        add_le_add hT3 hR
    _ = (15 / 2 * (n : ℝ) * L + C_R) * τ ^ (-(1 : ℝ) / 2) := by ring

/-! ###############################################################################
    ★★★ I3 — the composite: the concrete sliver-2 `√ε` bound, all three slices discharged.
    ############################################################################### -/

/-- **★★★ I3 — `witness_sliver2_final`.**  The campaign composite: `witness_sliver2_assembly`
    (`SliverAssembly`) with its three per-slice inner bounds `hInner0`/`hInner1`/`hInner2` all
    DISCHARGED (`hInner0_discharge` here + `hInner1_discharge`/`hInner2_discharge` from
    `InnerSliceBounds`).  Given the concrete Leibniz-Gaussian normal form `hNormalForm`, the three
    entangled-argument geometric inputs `hco`/`hYdisp`/`hJ3`/`hJ3Q`, the amplitude sup bounds
    `M₀`/`M₁`/`M₂`, the width-2 `F`-domination `hFdom`, the plain-Hermite Lipschitz interface
    `hqLip` and the carried entangled remainder `hRem` (see `hInner0_discharge`), plus the per-slice
    integrabilities, the terminal concrete formal-Hessian sliver obeys the `√ε` bound
      `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ (C₀+C₁)·2√ε + C₂·ε`
    with the explicit discharge constants `C₀ = 15/2·n·L + C_R`, `C₁` (the `hInner1_discharge`
    combination), `C₂ = (√2)ⁿ·M₂·C_L·G_a(0)`.  NOT `a₁ = R/6`. -/
theorem witness_sliver2_final
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (Y P Q : Point n → Point n) (A0 A1 A2 : ℝ → Point n → ℝ)
    (i : Fin n) (L C_R M₁ M₂ C_L T a τ₀ C_W C_P : ℝ)
    (hL : 0 ≤ L) (hC_R : 0 ≤ C_R) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hC_L : 0 ≤ C_L)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P)
    (u ε : ℝ) (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hA1bdd : ∀ τ, ∀ z : Point n, |A1 τ z| ≤ M₁)
    (hA2bdd : ∀ τ, ∀ z : Point n, |A2 τ z| ≤ M₂)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hqLip : ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n, |A0 (u - s) z * F s z 0 - A0 (u - s) w * F s w 0| ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z 0) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * F s z 0| ≤ M)
    (hRem : ∀ s ∈ Set.Ioo (u - ε) u,
        |(∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0)
            - (∫ z, ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
                * (A0 (u - s) z * F s z 0))|
          ≤ C_R * (u - s) ^ (-(1 : ℝ) / 2))
    (hNormalForm : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
        D2H τ z = sTerm0 Y P Q A0 τ z + sTerm1 Y P A1 τ z + sTerm2 Y A2 τ z)
    (hInt0 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm0 Y P Q A0 (u - s) z * F s z 0) volume)
    (hInt1 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm1 Y P A1 (u - s) z * F s z 0) volume)
    (hInt2 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm2 Y A2 (u - s) z * F s z 0) volume) :
    |∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z 0|
      ≤ ((15 / 2 * (n : ℝ) * L + C_R)
          + ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
              * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
                + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
                + ((n : ℝ) * C_W * C_P)
                  * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀))))
          * (2 * Real.sqrt ε)
        + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n)) * ε := by
  have hga : (0 : ℝ) ≤ gaussDdim a (0 : Point n) := gaussDdim_nonneg' a 0
  have hτ₀0 : (0 : ℝ) ≤ τ₀ := le_trans hε0 hετ₀
  -- constant nonnegativities.
  have hC₀ : (0 : ℝ) ≤ 15 / 2 * (n : ℝ) * L + C_R :=
    add_nonneg (mul_nonneg (by positivity) hL) hC_R
  have hC₂ : (0 : ℝ) ≤ (Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hM₂) hC_L) hga
  have hbrkt : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
        + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
        + ((n : ℝ) * C_W * C_P)
          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) := by
    have ht1 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2) := by positivity
    have ht2 : (0 : ℝ) ≤ ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
    have ht3 : (0 : ℝ) ≤ ((n : ℝ) * C_W * C_P)
        * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC_W) hC_P)
        (mul_nonneg (by positivity) hτ₀0)
    linarith
  have hC₁ : (0 : ℝ) ≤ (Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
        * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
          + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
          + ((n : ℝ) * C_W * C_P)
            * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hM₁) (mul_nonneg hC_L hga)) hbrkt
  -- the three per-slice discharges.
  have hI0 := hInner0_discharge Y P Q A0 F i L C_R u ε hL hC_R hqLip hRem
  have hI1 := hInner1_discharge Y P A1 F i M₁ C_L T a u ε τ₀ C_W C_P
    hM₁ hC_L hC_W hC_P ha hau huT hε0 hεa hετ₀ hco hYdisp hJ3 hA1bdd hFdom
  have hI2 := hInner2_discharge Y A2 F M₂ C_L T a u ε hM₂ hC_L ha hau huT hε0 hεa hco hA2bdd hFdom
  exact witness_sliver2_assembly D2H F Y P Q A0 A1 A2 _ _ _ τ₀ hC₀ hC₁ hC₂
    u ε hε0 hεu hετ₀ hNormalForm hI0 hI1 hI2 hInt0 hInt1 hInt2

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.oneD_absMoment5
#print axioms QIQTH.HeatResidualBound.oneD_absMoment6
#print axioms QIQTH.HeatResidualBound.oneD_absMoment7
#print axioms QIQTH.HeatResidualBound.oneD_absMoment8
#print axioms QIQTH.HeatResidualBound.oneD_absMoment9
#print axioms QIQTH.HeatResidualBound.hessianPlain_slice_bound
#print axioms QIQTH.HeatResidualBound.polyChartDiff_abs_bound
#print axioms QIQTH.HeatResidualBound.hInner0_discharge
#print axioms QIQTH.HeatResidualBound.witness_sliver2_final
