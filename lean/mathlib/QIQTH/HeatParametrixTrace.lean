/-
  HeatParametrixTrace — P2e (parametrix level): the DIAGONAL heat-TRACE of the parametrix and
  its `a₁ = (1/6)∫R` short-time coefficient.

  WHAT IS BUILT HERE (the honest boundary — read it).
  The heat trace `Tr e^{−tΔ} = ∫_M H(t,x,x) √g(x) dx` is, at the parametrix level, the diagonal
  value of the Minakshisundaram–Pleijel / Seeley–DeWitt parametrix integrated against the
  Riemannian volume. On the diagonal the Gaussian factor `e^{−|x|²/(4t)}` is `1`, so the diagonal
  parametrix value is the PURELY ALGEBRAIC quantity

      H_N(t,x,x) = (4πt)^{−d/2} · Σ_{k≤N} u_k(x,x) · t^k

  (van-Vleck `Θ(x,x)=1` at coincidence). This file models the trace as a FINITE-SAMPLE Lebesgue
  sum over a region: a `Finset ι` of sample points `pt : ι → Point n`, with the DIAGONAL Seeley
  coefficients `ud_k : Point n → ℝ` (`= u_k(x,x)`) and the volume density `w : Point n → ℝ`
  (`= √det g`) CARRIED as function inputs — exactly as the whole DeWitt/P2 line carries its jets.
  Pulling out the `(4πt)^{−d/2}` prefactor and using linearity gives the short-time expansion

      Tr H_N(t) = (4πt)^{−d/2} · Σ_{k≤N} W_k · t^k,     W_k = Σ_i u_k(x_i,x_i)·w(x_i),

  and under the DeWitt diagonal normalizations `u_0 = 1`, `u_1 = R/6` the `t¹` coefficient is

      W_1 = (1/6) · Σ_i R(x_i)·w(x_i) = (1/6)·∫R  —  the Seeley–DeWitt `a₁ = (1/6)∫R`.

  This is the closest honest in-Lean statement to "`a₁ = R/6`" as an INTEGRATED heat-trace
  coefficient short of the Levi/Duhamel kernel-existence wall.

  ⚠ HONEST SCOPE. This is the PARAMETRIX trace with CARRIED diagonal Seeley coefficients:
    • it is NOT the true `Tr e^{−tΔ}` — that requires the Levi/Duhamel construction (parametrix +
      error control / kernel existence and convergence), the deep analytic wall absent from every
      proof assistant;
    • it is NOT the general `a₁ = R/6` from the actual Seeley–DeWitt recursion — `ud_0 = 1` and
      `ud_1 = R/6` are labelled DeWitt-normalization hypotheses, carried, not derived;
    • the "trace integral" is a FINITE-SAMPLE `Finset` sum with a carried volume density `w`, NOT
      the measure-theoretic Riemannian-volume integral over the manifold (P2e-full).
  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.HeatParametrixAnsatz

open Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz

namespace QIQTH.HeatParametrixTrace

variable {n : ℕ} {ι : Type*}

set_option maxHeartbeats 800000

/-! ### The finite-sample diagonal heat trace of the parametrix. -/

/-- **#1 — the parametrix diagonal (heat) trace**, as a finite-sample Lebesgue sum over a region.
    For a `Finset` `s` of sample points `pt i : Point n`, the diagonal parametrix value at each
    point (`(4πt)^{−d/2} · Σ_{k≤N} ud_k · t^k`, the Gaussian being `1` on the diagonal) is weighted
    by the volume density `w (pt i) = √det g` and summed:

      Tr H_N(t) = Σ_{i∈s} (heatKernel1D t 0)^n · (Σ_{k≤N} ud_k(pt i)·t^k) · w(pt i).

    `ud`, `w` are CARRIED inputs (the diagonal Seeley coefficients and the volume density). -/
noncomputable def parametrixDiagTrace (N : ℕ) (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (s : Finset ι) (pt : ι → Point n) (t : ℝ) : ℝ :=
  ∑ i ∈ s, (heatKernel1D t 0) ^ n * (∑ k ∈ Finset.range (N + 1), ud k (pt i) * t ^ k) * w (pt i)

/-- The integrated `k`-th coefficient `W_k = Σ_{i∈s} ud_k(pt i)·w(pt i)` (`= ∫ u_k(x,x)·√g`). -/
def diagTraceCoeff (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (s : Finset ι) (pt : ι → Point n) (k : ℕ) : ℝ :=
  ∑ i ∈ s, ud k (pt i) * w (pt i)

/-- **#2 — the trace expansion.** Pull the `(4πt)^{−d/2}` prefactor out and use linearity (sum
    swap + factoring `t^k`): the diagonal parametrix trace is the prefactor times a polynomial in
    `t` whose `k`-th coefficient is the integrated Seeley coefficient `W_k = Σ_i ud_k(pt i)·w(pt i)`:

      Tr H_N(t) = (heatKernel1D t 0)^n · Σ_{k≤N} W_k · t^k. -/
theorem parametrixDiagTrace_expansion (N : ℕ) (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (s : Finset ι) (pt : ι → Point n) (t : ℝ) :
    parametrixDiagTrace N ud w s pt t
      = (heatKernel1D t 0) ^ n
        * ∑ k ∈ Finset.range (N + 1), diagTraceCoeff ud w s pt k * t ^ k := by
  unfold parametrixDiagTrace diagTraceCoeff
  -- Flatten both sides to double sums, swap the order, and match leaf-by-leaf.
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### The `a₁ = (1/6)∫R` heat-trace coefficient (parametrix level). -/

/-- **#3 — the `a₁ = (1/6)∫R` heat-trace coefficient.** Under the DeWitt diagonal normalizations
    `ud_0(x,x) = 1` and `ud_1(x,x) = R(x)/6` (the scalar curvature `R` carried as `scalarR`, both
    CARRIED as labelled hypotheses), for `N ≥ 1` the parametrix diagonal trace is

      Tr H_N(t) = (4πt)^{−d/2} · (Vol + (1/6)·∫R · t + Σ_{2≤k≤N} W_k · t^k),

    where `Vol = Σ_i w(pt i)` (the sampled volume), `∫R = Σ_i R(pt i)·w(pt i)` (the sampled
    curvature integral), and `W_k = Σ_i ud_k(pt i)·w(pt i)`. The `t¹` coefficient is exactly
    `(1/6)·∫R` — the Seeley–DeWitt `a₁ = (1/6)∫R` heat-trace coefficient, at the parametrix level.

    ⚠ Parametrix-level with carried coefficients: NOT the true kernel trace `Tr e^{−tΔ}` (Levi/
    Duhamel), NOT the general `a₁ = R/6` derivation, and the "integral" is a finite-sample sum. -/
theorem parametrixDiagTrace_a1 (N : ℕ) (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (scalarR : Point n → ℝ) (s : Finset ι) (pt : ι → Point n) (t : ℝ) (hN : 1 ≤ N)
    (hud0 : ∀ i, ud 0 (pt i) = 1)
    (hud1 : ∀ i, ud 1 (pt i) = scalarR (pt i) / 6) :
    parametrixDiagTrace N ud w s pt t
      = (heatKernel1D t 0) ^ n
        * ((∑ i ∈ s, w (pt i))
            + (1 / 6) * (∑ i ∈ s, scalarR (pt i) * w (pt i)) * t
            + ∑ k ∈ Finset.Ico 2 (N + 1), diagTraceCoeff ud w s pt k * t ^ k) := by
  rw [parametrixDiagTrace_expansion N ud w s pt t]
  congr 1
  -- Identify W₀ = Vol and W₁ = (1/6)·∫R under the DeWitt normalizations.
  have hW0 : diagTraceCoeff ud w s pt 0 = ∑ i ∈ s, w (pt i) := by
    unfold diagTraceCoeff
    apply Finset.sum_congr rfl
    intro i _
    rw [hud0 i, one_mul]
  have hW1 : diagTraceCoeff ud w s pt 1 = (1 / 6) * ∑ i ∈ s, scalarR (pt i) * w (pt i) := by
    unfold diagTraceCoeff
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hud1 i]
    ring
  rw [sum_range_split_two (fun k => diagTraceCoeff ud w s pt k * t ^ k) N hN]
  simp only [pow_zero, mul_one, pow_one, hW0, hW1]

/-! ### Leading term made explicit (stretch): `(4πt)^{−d/2}·Vol`. -/

/-- **#4 (stretch) — leading term explicit.** Rewriting the `(heatKernel1D t 0)^n` prefactor via
    `gaussDdim_diagonal_explicit`, the parametrix diagonal trace is manifestly `(√(4πt))⁻ⁿ`
    (`= (4πt)^{−d/2}`) times the DeWitt polynomial, so the leading short-time term is
    `(4πt)^{−d/2}·Vol`. -/
theorem parametrixDiagTrace_a1_explicit (N : ℕ) (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (scalarR : Point n → ℝ) (s : Finset ι) (pt : ι → Point n) (t : ℝ) (hN : 1 ≤ N)
    (hud0 : ∀ i, ud 0 (pt i) = 1)
    (hud1 : ∀ i, ud 1 (pt i) = scalarR (pt i) / 6) :
    parametrixDiagTrace N ud w s pt t
      = ((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n
        * ((∑ i ∈ s, w (pt i))
            + (1 / 6) * (∑ i ∈ s, scalarR (pt i) * w (pt i)) * t
            + ∑ k ∈ Finset.Ico 2 (N + 1), diagTraceCoeff ud w s pt k * t ^ k) := by
  rw [parametrixDiagTrace_a1 N ud w scalarR s pt t hN hud0 hud1, heatKernel1D_zero]

end QIQTH.HeatParametrixTrace
