/-
  HeatParametrixAnsatz — P2a: the heat-kernel parametrix ANSATZ as an explicit function in
  Riemannian normal coordinates, and its diagonal short-time value (the `a₁` heat-trace structure).

  WHAT IS BUILT HERE (the honest boundary — read it).
  The Minakshisundaram–Pleijel / Seeley–DeWitt parametrix for `e^{−tΔ}` in normal coordinates
  centered at a point is

      H_N(t,x) = (4πt)^{−d/2} · e^{−|x|²/(4t)} · Θ(x)^{−1/2} · Σ_{k≤N} u_k(x) · t^k ,

  where `(4πt)^{−d/2} e^{−|x|²/(4t)}` is the flat Gaussian (`QIQTH.FlatHeatEquation.gaussDdim`,
  since the radial coordinate `r² = |x|²` in RNC), `Θ` is the van-Vleck–Morette determinant, and
  the `u_k` are the DeWitt heat coefficients. This file writes `H_N` as an actual Lean function
  (`heatParametrix`) with `Θ` and the `u_k` CARRIED as function inputs — exactly as
  `QIQTH.DeWittDiagonal` carries its jet — and computes its value on the DIAGONAL `x = 0`
  (the RNC center, van-Vleck `Θ(0)=1` at coincidence):

      H_N(t,0) = (4πt)^{−d/2} · Σ_{k≤N} u_k(0) · t^k
               = (4πt)^{−d/2} · (1 + (R/6)·t + Σ_{2≤k≤N} u_k(0)·t^k)

  under the DeWitt normalization `u_0(0)=1`, `u_1(0)=R/6`. This is the diagonal `a₁`-coefficient
  structure that the heat trace `Tr e^{−tΔ} = ∫ H(t,x,x) √g dx` consumes.

  ⚠ HONEST SCOPE. This is the ANSATZ (P2a) ONLY. The van-Vleck `Θ` and the coefficients `u_k`
  are CARRIED as inputs (deriving `Θ` and the recursion `u_k` from the exponential map is P2b;
  proving `H_N` solves the curved heat equation is P2c; the error estimate / kernel existence and
  convergence is P2d; the general `a₁ = R/6` from the Seeley–DeWitt recursion is P2e — the deep
  Riemannian-heat-kernel analytic wall, absent from every proof assistant). We do NOT derive
  `u_1(0) = R/6`; it is a labelled DeWitt-normalization hypothesis. No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.FlatHeatEquation

open Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation

namespace QIQTH.HeatParametrixAnsatz

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### The value of the flat Gaussian on the diagonal (RNC center `x = 0`). -/

/-- **The 1-D heat kernel at the origin.** `G_t(0) = (√(4πt))⁻¹`, since the exponent
    `−0²/(4t) = 0` and `exp 0 = 1`. -/
theorem heatKernel1D_zero (t : ℝ) : heatKernel1D t 0 = (Real.sqrt (4 * Real.pi * t))⁻¹ := by
  simp [heatKernel1D]

/-- **#3 — the `d`-dimensional flat Gaussian on the diagonal.** `gaussDdim t 0 = G_t(0)^d`, i.e.
    the product `∏ₖ G_t(0)` over the `d` coordinates collapses to the `d`-th power. Combined with
    `heatKernel1D_zero` this is the `(4πt)^{−d/2}` heat-trace prefactor `(√(4πt))⁻ⁿ`. -/
theorem gaussDdim_diagonal (t : ℝ) :
    gaussDdim t (0 : Point n) = (heatKernel1D t 0) ^ n := by
  simp only [gaussDdim, Pi.zero_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The `(4πt)^{−d/2}` prefactor explicitly.** `gaussDdim t 0 = (√(4πt))⁻ⁿ`. -/
theorem gaussDdim_diagonal_explicit (t : ℝ) :
    gaussDdim t (0 : Point n) = ((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n := by
  rw [gaussDdim_diagonal, heatKernel1D_zero]

/-! ### The parametrix ansatz `H_N`. -/

/-- **#1 — the heat-kernel parametrix ansatz** in normal coordinates:
    `H_N(t,x) = gaussDdim t x · Θ(x)^{−1/2} · Σ_{k≤N} u_k(x) · t^k`.
    The van-Vleck determinant `Θ` and the DeWitt coefficients `u_k` are CARRIED as function
    inputs (like `QIQTH.DeWittDiagonal`'s jet); `Θ(x)^{−1/2}` uses `Real.rpow`. -/
noncomputable def heatParametrix (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t : ℝ) (x : Point n) : ℝ :=
  gaussDdim t x * (Θ x) ^ (-(1 : ℝ) / 2) * ∑ k ∈ Finset.range (N + 1), u k x * t ^ k

/-- **#2 — the parametrix on the diagonal.** At the RNC center `x = 0`, where the van-Vleck
    determinant is `Θ(0) = 1` at coincidence, the `Θ^{−1/2}` factor becomes `1^{−1/2} = 1`, so
    `H_N(t,0) = gaussDdim t 0 · Σ_{k≤N} u_k(0)·t^k`. -/
theorem heatParametrix_diagonal (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t : ℝ) (hΘ : Θ (0 : Point n) = 1) :
    heatParametrix N Θ u t (0 : Point n)
      = gaussDdim t (0 : Point n) * ∑ k ∈ Finset.range (N + 1), u k (0 : Point n) * t ^ k := by
  rw [heatParametrix, hΘ, Real.one_rpow, mul_one]

/-- **#3+#2 — the diagonal expansion.** `H_N(t,0) = G_t(0)^d · Σ_{k≤N} u_k(0)·t^k`, i.e. the
    `(4πt)^{−d/2}` prefactor times the DeWitt polynomial in `t`. -/
theorem heatParametrix_diagonal_expansion (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t : ℝ) (hΘ : Θ (0 : Point n) = 1) :
    heatParametrix N Θ u t (0 : Point n)
      = (heatKernel1D t 0) ^ n * ∑ k ∈ Finset.range (N + 1), u k (0 : Point n) * t ^ k := by
  rw [heatParametrix_diagonal N Θ u t hΘ, gaussDdim_diagonal]

/-- A generic peel of the two bottom terms of a `range (N+1)` sum, for `N ≥ 1`:
    `Σ_{k≤N} f k = f 0 + f 1 + Σ_{2≤k≤N} f k`. -/
theorem sum_range_split_two {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range (N + 1), f k
      = f 0 + f 1 + ∑ k ∈ Finset.Ico 2 (N + 1), f k := by
  rw [Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (show (0 : ℕ) < N + 1 by omega),
      Finset.sum_eq_sum_Ico_succ_bot (show (0 : ℕ) + 1 < N + 1 by omega)]
  simp only [Nat.reduceAdd, zero_add]
  rw [add_assoc]

/-- **#4 — the diagonal `a₁`-coefficient structure.** Under the DeWitt normalization
    `u_0(0) = 1` and `u_1(0) = R/6` (both CARRIED as labelled hypotheses), for `N ≥ 1`:

      H_N(t,0) = (4πt)^{−d/2} · (1 + (R/6)·t + Σ_{2≤k≤N} u_k(0)·t^k).

    This is exactly the leading `(4πt)^{−d/2}(1 + (R/6)t + higher)` short-time structure that the
    heat trace `Tr e^{−tΔ}` consumes; the `R/6` is the `a₁` coefficient (labelled input, not
    derived here — see the honest-scope note). -/
theorem heatParametrix_diagonal_a1 (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t R : ℝ) (hΘ : Θ (0 : Point n) = 1) (hN : 1 ≤ N)
    (hu0 : u 0 (0 : Point n) = 1) (hu1 : u 1 (0 : Point n) = R / 6) :
    heatParametrix N Θ u t (0 : Point n)
      = (heatKernel1D t 0) ^ n
        * (1 + (R / 6) * t + ∑ k ∈ Finset.Ico 2 (N + 1), u k (0 : Point n) * t ^ k) := by
  rw [heatParametrix_diagonal_expansion N Θ u t hΘ]
  congr 1
  rw [sum_range_split_two (fun k => u k (0 : Point n) * t ^ k) N hN]
  simp only [pow_zero, mul_one, pow_one, hu0, hu1]
