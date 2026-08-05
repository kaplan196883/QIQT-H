/-
  GaussianWidthTransfer — J4-250: wide-route brick 1, the generic Gaussian WIDTH-GAP transfer.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It builds the
  reusable, purely-analytic Gaussian width-gap comparison lemmas that the new W1 amplitude campaign
  consumes.  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise.  No existing file is edited.

  ── WHY A WIDTH GAP (the strategic point).
  The exact-width comparison `gaussDdim τ (q z) / gaussDdim τ z` is GENERALLY UNBOUNDED as `τ → 0`
  whenever `‖q z‖ < ‖z‖`, since that ratio is `exp((‖z‖²−‖q z‖²)/(4τ))`.  The fix is a STRICT WIDTH
  GAP: compare a width-`τ` Gaussian at the (radially smaller) point `w` against the WIDER width-`lamτ`
  Gaussian at `z` (`lam > 1`), under the gate `‖w‖² ≥ (1−η)‖z‖²`.  Then the leftover exponent is
  strictly negative and gives, for every `k`, a polynomial-times-Gaussian absorption bound.

  ── WHAT IS DERIVED HERE (axiom-free, no `sorry`).

    (0)  `gaussDdim_closed` — the closed form `gaussDdim t x = (√(4πt))⁻ⁿ · exp(−r²(x)/(4t))`
         (`r²(x) = rncRadialSq x`), from the product/exp-sum reduction of `heatKernel1D`.

    (1)  `gaussDdim_width_ratio_le` — THE RATIO BOUND.  For `0 < τ`, `0 < lam` and the radial gate
         `(1−η)·r²(z) ≤ r²(w)`,
             `gaussDdim τ w ≤ (√lam)ⁿ · exp(−(((1−η)−1/lam)/4)·r²(z)/τ) · gaussDdim (lamτ) z`.
         (The prefactor ratio `(√(4πτ))⁻¹ / (√(4πlamτ))⁻¹ = √lam`; the exponent split uses only the gate.)

    (2)  `pow_mul_exp_neg_le_factorial_div` — the standard calculus-free sup bound
             `yᵏ·exp(−c·y) ≤ k!/cᵏ`   (`c > 0`, `y ≥ 0`),
         via the exponential series term `(cy)ᵏ/k! ≤ exp(cy)` (`Real.pow_div_factorial_le_exp`).

    (3)  `gaussDdim_poly_absorb` — THE POLYNOMIAL ABSORPTION.  For `η < 1`, `1 < lam`, `1/lam < 1−η` and
         every `k`, an explicit `C > 0` with, uniformly over `τ > 0` and the gate,
             `(r²(z)/τ)ᵏ · gaussDdim τ w ≤ C · gaussDdim (lamτ) z`.
         Named instances `..._zero/_one/_two` (`k = 0,1,2`) and the mixed form
         `gaussDdim_absorb_mixed` (`r²(z)ʲ/τᵏ · gaussDdim τ w ≤ (C/τ^{k−j})·gaussDdim (lamτ) z`, `j ≤ k`)
         — the shapes the wide `hAnear` (`k=0`) and `hD2Hexpand` (`k=1`; `j=1,k=2`) analogues consume.

    (4)  Integrability re-exports at the shifted width `lamτ` (`gaussDdim_width_integrable`, product form
         `gaussDdim_width_mul_integrable`).

  NOT `a₁ = R/6`.  The radial gate `(1−η)·r²(z) ≤ r²(w)` is the CALLER'S obligation (brick 3 supplies
  it for the chart-image witness); nothing here assumes it holds for any particular `w`.
-/
import Mathlib
import QIQTH.RadialDistance
import QIQTH.FlatHeatEquation
import QIQTH.LeviSeries
import QIQTH.DeltaFamilyBoundary
import QIQTH.ModelIntegrableW

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatKernelA1 QIQTH.RadialDistance

namespace QIQTH.GaussianWidthTransfer

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (0) — the closed form of the `d`-dim Gaussian.
    ############################################################################### -/

/-- **The closed form.**  `gaussDdim t x = (√(4πt))⁻ⁿ · exp(−r²(x)/(4t))`, where `r²(x) = rncRadialSq x`
    is the Euclidean squared radius.  Product of the `n` one-dimensional kernels, the `(√(4πt))⁻¹`
    prefactors collecting to the `n`-th power and the exponents summing (`Real.exp_sum`).
    NOT `a₁ = R/6`. -/
theorem gaussDdim_closed (t : ℝ) (x : Point n) :
    gaussDdim t x
      = (Real.sqrt (4 * Real.pi * t))⁻¹ ^ n * Real.exp (-rncRadialSq x / (4 * t)) := by
  have key : (∑ k : Fin n, -(x k) ^ 2 / (4 * t)) = -rncRadialSq x / (4 * t) := by
    have h1 : ∀ k : Fin n, -(x k) ^ 2 / (4 * t) = (-(1 / (4 * t))) * (x k) ^ 2 :=
      fun k => by ring
    simp_rw [h1]
    rw [← Finset.mul_sum, QIQTH.RadialDistance.rncRadialSq]
    ring
  simp only [gaussDdim, QIQTH.HeatKernelA1.heatKernel1D]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, key]

/-! ###############################################################################
    ### (1) — the ratio bound (the master width-gap comparison).
    ############################################################################### -/

/-- **★ `gaussDdim_width_ratio_le` — THE WIDTH-GAP RATIO BOUND.**  For `0 < τ`, `0 < lam` and the
    radial gate `(1−η)·r²(z) ≤ r²(w)`,
        `gaussDdim τ w ≤ (√lam)ⁿ · exp(−(((1−η)−1/lam)/4)·r²(z)/τ) · gaussDdim (lamτ) z`.
    The prefactor ratio is `√lam` per dimension; the exponent inequality is exactly the gate divided by
    `4τ`.  No sign/positivity assumption on `η` or `(1−η)−1/lam` is needed here.  NOT `a₁ = R/6`. -/
theorem gaussDdim_width_ratio_le
    {τ η lam : ℝ} (hτ : 0 < τ) (hlam : 0 < lam)
    {w z : Point n} (hgate : (1 - η) * rncRadialSq z ≤ rncRadialSq w) :
    gaussDdim τ w
      ≤ (Real.sqrt lam) ^ n
        * Real.exp (-(((1 - η) - 1 / lam) / 4) * rncRadialSq z / τ)
        * gaussDdim (lam * τ) z := by
  have hlamτ : 0 < lam * τ := mul_pos hlam hτ
  -- the scalar prefactor identity `(√(4πτ))⁻¹ = √lam · (√(4π(lamτ)))⁻¹`.
  have hscal : (Real.sqrt (4 * Real.pi * τ))⁻¹
      = Real.sqrt lam * (Real.sqrt (4 * Real.pi * (lam * τ)))⁻¹ := by
    rw [show (4 * Real.pi * (lam * τ)) = lam * (4 * Real.pi * τ) by ring,
        Real.sqrt_mul hlam.le, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (Real.sqrt_pos.mpr hlam).ne', one_mul]
  -- its `n`-th-power form.
  have hpre : (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n
      = (Real.sqrt lam) ^ n * (Real.sqrt (4 * Real.pi * (lam * τ)))⁻¹ ^ n := by
    rw [← mul_pow, ← hscal]
  -- the leftover exponent collapses to `−(1−η)·r²(z)/(4τ)`.
  have hexp_arg :
      (-(((1 - η) - 1 / lam) / 4) * rncRadialSq z / τ) + (-rncRadialSq z / (4 * (lam * τ)))
        = -(1 - η) * rncRadialSq z / (4 * τ) := by
    field_simp
    ring
  -- and the gate makes it dominate `−r²(w)/(4τ)`.
  have hle_arg : -rncRadialSq w / (4 * τ) ≤ -(1 - η) * rncRadialSq z / (4 * τ) := by
    rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * τ)]
    linarith [hgate]
  have hexp : Real.exp (-rncRadialSq w / (4 * τ))
      ≤ Real.exp (-(((1 - η) - 1 / lam) / 4) * rncRadialSq z / τ)
        * Real.exp (-rncRadialSq z / (4 * (lam * τ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hexp_arg]
    exact hle_arg
  calc gaussDdim τ w
      = (Real.sqrt lam) ^ n * (Real.sqrt (4 * Real.pi * (lam * τ)))⁻¹ ^ n
          * Real.exp (-rncRadialSq w / (4 * τ)) := by
        rw [gaussDdim_closed τ w, hpre]
    _ ≤ (Real.sqrt lam) ^ n * (Real.sqrt (4 * Real.pi * (lam * τ)))⁻¹ ^ n
          * (Real.exp (-(((1 - η) - 1 / lam) / 4) * rncRadialSq z / τ)
              * Real.exp (-rncRadialSq z / (4 * (lam * τ)))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (Real.sqrt lam) ^ n
          * Real.exp (-(((1 - η) - 1 / lam) / 4) * rncRadialSq z / τ)
          * gaussDdim (lam * τ) z := by
        rw [gaussDdim_closed (lam * τ) z]; ring

/-! ###############################################################################
    ### (2) — the calculus-free polynomial sup bound.
    ############################################################################### -/

/-- **`pow_mul_exp_neg_le_factorial_div` — `yᵏ·exp(−c·y) ≤ k!/cᵏ`** for `c > 0`, `y ≥ 0`.  The
    exponential series term `(cy)ᵏ/k! ≤ exp(cy)` (`Real.pow_div_factorial_le_exp`) gives
    `cᵏ·yᵏ ≤ k!·exp(cy)`; multiplying by `exp(−cy)` and dividing by `cᵏ` closes it — no calculus,
    no differentiation.  NOT `a₁ = R/6`. -/
theorem pow_mul_exp_neg_le_factorial_div {c : ℝ} (hc : 0 < c) (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ k * Real.exp (-(c * y)) ≤ (Nat.factorial k : ℝ) / c ^ k := by
  have hck : (0 : ℝ) < c ^ k := pow_pos hc k
  have hkf : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hexp := Real.pow_div_factorial_le_exp (c * y) (mul_nonneg hc.le hy) k
  rw [mul_pow, div_le_iff₀ hkf] at hexp
  -- hexp : c^k * y^k ≤ exp(c*y) * k!
  rw [le_div_iff₀ hck]
  have hrw : y ^ k * Real.exp (-(c * y)) * c ^ k
      = (c ^ k * y ^ k) * Real.exp (-(c * y)) := by ring
  rw [hrw]
  calc (c ^ k * y ^ k) * Real.exp (-(c * y))
      ≤ (Real.exp (c * y) * (Nat.factorial k : ℝ)) * Real.exp (-(c * y)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = (Nat.factorial k : ℝ) := by
        rw [mul_comm (Real.exp (c * y)) ((Nat.factorial k : ℝ)), mul_assoc, Real.exp_neg,
            mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]

/-! ###############################################################################
    ### (3) — the polynomial absorption and its k-instances.
    ############################################################################### -/

/-- **★★ `gaussDdim_poly_absorb` — THE POLYNOMIAL ABSORPTION.**  Under the width gap
    `1/lam < 1−η` (with `η < 1`, `1 < lam`), for every `k` there is an explicit `C > 0` with,
    uniformly over `τ > 0` and every `w, z` obeying the radial gate `(1−η)·r²(z) ≤ r²(w)`,
        `(r²(z)/τ)ᵏ · gaussDdim τ w ≤ C · gaussDdim (lamτ) z`.
    `C = (√lam)ⁿ · k!/cᵏ` with `c = ((1−η)−1/lam)/4 > 0`; combines the ratio bound (1) with the sup
    bound (2).  NOT `a₁ = R/6`. -/
theorem gaussDdim_poly_absorb
    {η lam : ℝ} (hη1 : η < 1) (hlam : 1 < lam) (hlamη : 1 / lam < 1 - η) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w z : Point n),
      (1 - η) * rncRadialSq z ≤ rncRadialSq w →
        (rncRadialSq z / τ) ^ k * gaussDdim τ w ≤ C * gaussDdim (lam * τ) z := by
  have hlam0 : 0 < lam := by linarith
  have hc : 0 < ((1 - η) - 1 / lam) / 4 := by
    have : 0 < (1 - η) - 1 / lam := by linarith
    linarith
  refine ⟨(Real.sqrt lam) ^ n * ((Nat.factorial k : ℝ) / (((1 - η) - 1 / lam) / 4) ^ k), ?_, ?_⟩
  · exact mul_pos (pow_pos (Real.sqrt_pos.mpr hlam0) n)
      (div_pos (by exact_mod_cast Nat.factorial_pos k) (pow_pos hc k))
  · intro τ hτ w z hgate
    have hlamτ : 0 < lam * τ := mul_pos hlam0 hτ
    have hX : 0 ≤ rncRadialSq z / τ := div_nonneg (rncRadialSq_nonneg z) hτ.le
    have hratio := gaussDdim_width_ratio_le (n := n) hτ hlam0 hgate
    -- the sup bound, rewritten into the ratio bound's literal exponent shape.
    have hsup' : (rncRadialSq z / τ) ^ k
          * Real.exp (-(((1 - η) - 1 / lam) / 4) * rncRadialSq z / τ)
        ≤ (Nat.factorial k : ℝ) / (((1 - η) - 1 / lam) / 4) ^ k := by
      have h := pow_mul_exp_neg_le_factorial_div hc k hX
      have harg : (-(((1 - η) - 1 / lam) / 4) * rncRadialSq z / τ)
          = -(((1 - η) - 1 / lam) / 4 * (rncRadialSq z / τ)) := by ring
      rw [harg]; exact h
    calc (rncRadialSq z / τ) ^ k * gaussDdim τ w
        ≤ (rncRadialSq z / τ) ^ k
            * ((Real.sqrt lam) ^ n
                * Real.exp (-(((1 - η) - 1 / lam) / 4) * rncRadialSq z / τ)
                * gaussDdim (lam * τ) z) :=
          mul_le_mul_of_nonneg_left hratio (pow_nonneg hX k)
      _ = ((rncRadialSq z / τ) ^ k
              * Real.exp (-(((1 - η) - 1 / lam) / 4) * rncRadialSq z / τ))
            * ((Real.sqrt lam) ^ n * gaussDdim (lam * τ) z) := by ring
      _ ≤ ((Nat.factorial k : ℝ) / (((1 - η) - 1 / lam) / 4) ^ k)
            * ((Real.sqrt lam) ^ n * gaussDdim (lam * τ) z) :=
          mul_le_mul_of_nonneg_right hsup'
            (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) n)
              (QIQTH.LeviSeries.gaussDdim_pos (lam * τ) hlamτ z).le)
      _ = ((Real.sqrt lam) ^ n * ((Nat.factorial k : ℝ) / (((1 - η) - 1 / lam) / 4) ^ k))
            * gaussDdim (lam * τ) z := by ring

/-- **`k = 0` — the raw width transfer** (the wide-`hAnear` analogue).  `∃ C > 0`, uniformly,
    `gaussDdim τ w ≤ C · gaussDdim (lamτ) z`. -/
theorem gaussDdim_absorb_zero
    {η lam : ℝ} (hη1 : η < 1) (hlam : 1 < lam) (hlamη : 1 / lam < 1 - η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w z : Point n),
      (1 - η) * rncRadialSq z ≤ rncRadialSq w →
        gaussDdim τ w ≤ C * gaussDdim (lam * τ) z := by
  obtain ⟨C, hC, hb⟩ := gaussDdim_poly_absorb (n := n) hη1 hlam hlamη 0
  refine ⟨C, hC, ?_⟩
  intro τ hτ w z hgate
  have := hb τ hτ w z hgate
  simpa using this

/-- **`k = 1`** (a wide-`hD2Hexpand` prefactor).  `∃ C > 0`, uniformly,
    `(r²(z)/τ) · gaussDdim τ w ≤ C · gaussDdim (lamτ) z`. -/
theorem gaussDdim_absorb_one
    {η lam : ℝ} (hη1 : η < 1) (hlam : 1 < lam) (hlamη : 1 / lam < 1 - η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w z : Point n),
      (1 - η) * rncRadialSq z ≤ rncRadialSq w →
        (rncRadialSq z / τ) * gaussDdim τ w ≤ C * gaussDdim (lam * τ) z := by
  obtain ⟨C, hC, hb⟩ := gaussDdim_poly_absorb (n := n) hη1 hlam hlamη 1
  refine ⟨C, hC, ?_⟩
  intro τ hτ w z hgate
  have := hb τ hτ w z hgate
  simpa using this

/-- **`k = 2`** (a wide-`hD2Hexpand` prefactor).  `∃ C > 0`, uniformly,
    `(r²(z)/τ)² · gaussDdim τ w ≤ C · gaussDdim (lamτ) z`. -/
theorem gaussDdim_absorb_two
    {η lam : ℝ} (hη1 : η < 1) (hlam : 1 < lam) (hlamη : 1 / lam < 1 - η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w z : Point n),
      (1 - η) * rncRadialSq z ≤ rncRadialSq w →
        (rncRadialSq z / τ) ^ 2 * gaussDdim τ w ≤ C * gaussDdim (lam * τ) z :=
  gaussDdim_poly_absorb (n := n) hη1 hlam hlamη 2

/-- **The mixed form** (the exact wide-`hD2Hexpand` shape).  For `j ≤ k`, `∃ C > 0`, uniformly,
        `r²(z)ʲ / τᵏ · gaussDdim τ w ≤ (C / τ^{k−j}) · gaussDdim (lamτ) z`.
    The `k = j` cases are the clean absorptions; for `j < k` the leftover `1/τ^{k−j}` stays (it is
    integrable against the time integral downstream).  E.g. `hD2Hexpand`'s singular prefactor
    `z_iⱼ²/(4τ²)·G ≤ (1/(4τ))·(r²(z)/τ)·G` is the `j = 1, k = 2` instance.  NOT `a₁ = R/6`. -/
theorem gaussDdim_absorb_mixed
    {η lam : ℝ} (hη1 : η < 1) (hlam : 1 < lam) (hlamη : 1 / lam < 1 - η) (k j : ℕ) (hjk : j ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w z : Point n),
      (1 - η) * rncRadialSq z ≤ rncRadialSq w →
        (rncRadialSq z) ^ j / τ ^ k * gaussDdim τ w
          ≤ C / τ ^ (k - j) * gaussDdim (lam * τ) z := by
  obtain ⟨C, hC, hb⟩ := gaussDdim_poly_absorb (n := n) hη1 hlam hlamη j
  refine ⟨C, hC, ?_⟩
  intro τ hτ w z hgate
  have hb' := hb τ hτ w z hgate
  have hτkj : (0 : ℝ) < τ ^ (k - j) := pow_pos hτ _
  have hτj : τ ^ k = τ ^ (k - j) * τ ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjk]
  calc (rncRadialSq z) ^ j / τ ^ k * gaussDdim τ w
      = (τ ^ (k - j))⁻¹ * ((rncRadialSq z / τ) ^ j * gaussDdim τ w) := by
        rw [div_pow, hτj]; ring
    _ ≤ (τ ^ (k - j))⁻¹ * (C * gaussDdim (lam * τ) z) :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = C / τ ^ (k - j) * gaussDdim (lam * τ) z := by ring

/-! ###############################################################################
    ### (4) — integrability re-exports at the shifted width `lamτ`.
    ############################################################################### -/

/-- The width-`lamτ` Gaussian is integrable (`lam, τ > 0`).  Re-export of the banked mass-one
    integrability at `lamτ`. -/
theorem gaussDdim_width_integrable {lam τ : ℝ} (hlam : 0 < lam) (hτ : 0 < τ) :
    Integrable (fun z : Point n => gaussDdim (lam * τ) z) volume :=
  QIQTH.HeatResidualBound.gaussDdim_integrable (lam * τ) (mul_pos hlam hτ)

/-- The two-Gaussian product `z ↦ gaussDdim a (x−z)·gaussDdim b (z−y)` is integrable at all widths.
    Re-export of the banked product integrability (used to build the fixed dominator). -/
theorem gaussDdim_width_mul_integrable (a b : ℝ) (x y : Point n) :
    Integrable (fun z : Point n => gaussDdim a (x - z) * gaussDdim b (z - y)) volume :=
  QIQTH.HeatResidualBound.gaussDdim_mul_integrable a b x y

/-! ### Axiom audit (std-3 everywhere). -/

#print axioms gaussDdim_closed
#print axioms gaussDdim_width_ratio_le
#print axioms pow_mul_exp_neg_le_factorial_div
#print axioms gaussDdim_poly_absorb
#print axioms gaussDdim_absorb_zero
#print axioms gaussDdim_absorb_one
#print axioms gaussDdim_absorb_two
#print axioms gaussDdim_absorb_mixed
#print axioms gaussDdim_width_integrable
#print axioms gaussDdim_width_mul_integrable

end QIQTH.GaussianWidthTransfer
