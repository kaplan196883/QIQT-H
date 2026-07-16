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

/-! ### measure-theoretic upgrade — the parametrix diagonal trace as a genuine `∫ ∂μ`.

    The ONLY change from the finite-sample block above is that the "trace integral" is now a
    genuine measure-theoretic Riemannian-volume integral `∫ · ∂μ` against a CARRIED volume measure
    `μ : Measure (Point n)` (morally `dV = √det g dx`), rather than a `Finset` sample sum
    `∑_{i∈s} · w(pt i)`. Everything else is unchanged and the honest scope is identical:

    ⚠ HONEST SCOPE (same firewall as above). This is STILL the PARAMETRIX trace with CARRIED
    diagonal Seeley coefficients (`ud_0 = 1`, `ud_1 = R/6` labelled DeWitt-normalization hypotheses)
    and a CARRIED volume measure `μ`. It is:
      • NOT the true `Tr e^{−tΔ}` — that needs the Levi/Duhamel kernel existence + convergence wall;
      • NOT the general `a₁ = R/6` from the Seeley–DeWitt recursion (`ud_0=1`, `ud_1=R/6` carried);
      • the volume measure `μ` is carried, not constructed from a metric.
    The upgrade delivered here is purely that `W_k = ∫ u_k(x,x)·√g dV` and `a₁ = (1/6)∫_M R √g dV`
    are now GENUINE measure-theoretic real integrals (Mathlib `∫`, `integral_finset_sum`,
    `integral_const_mul`), not finite-sample sums. No axioms, no `sorry`. -/

open MeasureTheory

/-- **#5 — the parametrix diagonal (heat) trace as a measure-theoretic integral.** The diagonal
    parametrix value `(heatKernel1D t 0)^n · (Σ_{k≤N} ud_k(x)·t^k)` integrated against the carried
    Riemannian volume measure `μ` (morally `dV = √det g dx`), weighted by `w` (`= √det g`):

      Tr H_N(t) = ∫ x, (heatKernel1D t 0)^n · (Σ_{k≤N} ud_k(x)·t^k) · w(x) ∂μ.

    Genuine measure-theoretic analogue of `parametrixDiagTrace`; `ud`, `w`, `μ` are CARRIED. -/
noncomputable def parametrixDiagTraceInt (N : ℕ) (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (μ : Measure (Point n)) (t : ℝ) : ℝ :=
  ∫ x, (heatKernel1D t 0) ^ n * (∑ k ∈ Finset.range (N + 1), ud k x * t ^ k) * w x ∂μ

/-- The integrated `k`-th Seeley coefficient as a genuine integral,
    `W_k = ∫ u_k(x,x)·√g dV = ∫ x, ud_k(x)·w(x) ∂μ`. -/
noncomputable def diagTraceCoeffInt (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (μ : Measure (Point n)) (k : ℕ) : ℝ :=
  ∫ x, ud k x * w x ∂μ

/-- **#6 — the measure-theoretic trace expansion.** Pull the constant `(4πt)^{−d/2}` prefactor out
    of the integral (`integral_const_mul`) and split the finite `Σ_{k≤N}` out (`integral_finset_sum`,
    which needs each `fun x => ud_k(x)·w(x)` integrable — carried as `hInt`), factoring the scalar
    `t^k` (`integral_mul_const`):

      Tr H_N(t) = (heatKernel1D t 0)^n · Σ_{k≤N} W_k · t^k,   W_k = ∫ x, ud_k(x)·w(x) ∂μ.

    `hInt` is exactly the integrability side-condition Mathlib's `integral_finset_sum` demands;
    it is genuine and non-vacuous (the integral splitting fails without it). -/
theorem parametrixDiagTraceInt_expansion (N : ℕ) (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (μ : Measure (Point n)) (t : ℝ)
    (hInt : ∀ k ∈ Finset.range (N + 1), Integrable (fun x => ud k x * w x) μ) :
    parametrixDiagTraceInt N ud w μ t
      = (heatKernel1D t 0) ^ n
        * ∑ k ∈ Finset.range (N + 1), diagTraceCoeffInt ud w μ k * t ^ k := by
  unfold parametrixDiagTraceInt diagTraceCoeffInt
  -- Rewrite the integrand to `c · Σ_k (ud_k(x)·w(x))·t^k`, then use linearity of the integral.
  have key : ∀ x, (heatKernel1D t 0) ^ n * (∑ k ∈ Finset.range (N + 1), ud k x * t ^ k) * w x
      = (heatKernel1D t 0) ^ n * ∑ k ∈ Finset.range (N + 1), (ud k x * w x) * t ^ k := by
    intro x
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum (Finset.range (N + 1)) (fun k hk => (hInt k hk).mul_const (t ^ k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const]

/-- **#7 — the `a₁ = (1/6)∫_M R √g dV` heat-trace coefficient as a genuine integral.** Under the
    DeWitt diagonal normalizations `ud_0(x) = 1` and `ud_1(x) = R(x)/6` (scalar curvature `R`
    carried as `scalarR`, both CARRIED as labelled hypotheses), for `N ≥ 1`:

      Tr H_N(t) = (4πt)^{−d/2} · (Vol + (1/6)·(∫ R √g dV)·t + Σ_{2≤k≤N} W_k · t^k),

    with `W₀ = Vol = ∫ √g dV = ∫ x, w(x) ∂μ` and `W₁ = (1/6)∫ R √g dV = (1/6)∫ x, R(x)·w(x) ∂μ`.
    The `t¹` coefficient is exactly `(1/6)∫_M R √g dV` — the Seeley–DeWitt `a₁ = (1/6)∫R` heat-trace
    coefficient, now as a GENUINE measure-theoretic real integral.

    ⚠ Parametrix-level with carried `ud`/`μ`: NOT the true kernel trace `Tr e^{−tΔ}` (Levi/Duhamel),
    NOT the general `a₁ = R/6` derivation. -/
theorem parametrixDiagTraceInt_a1 (N : ℕ) (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (scalarR : Point n → ℝ) (μ : Measure (Point n)) (t : ℝ) (hN : 1 ≤ N)
    (hInt : ∀ k ∈ Finset.range (N + 1), Integrable (fun x => ud k x * w x) μ)
    (hud0 : ∀ x, ud 0 x = 1)
    (hud1 : ∀ x, ud 1 x = scalarR x / 6) :
    parametrixDiagTraceInt N ud w μ t
      = (heatKernel1D t 0) ^ n
        * ((∫ x, w x ∂μ)
            + (1 / 6) * (∫ x, scalarR x * w x ∂μ) * t
            + ∑ k ∈ Finset.Ico 2 (N + 1), diagTraceCoeffInt ud w μ k * t ^ k) := by
  rw [parametrixDiagTraceInt_expansion N ud w μ t hInt]
  congr 1
  -- Identify W₀ = Vol and W₁ = (1/6)·∫R under the DeWitt normalizations.
  have hW0 : diagTraceCoeffInt ud w μ 0 = ∫ x, w x ∂μ := by
    unfold diagTraceCoeffInt
    simp_rw [hud0, one_mul]
  have hW1 : diagTraceCoeffInt ud w μ 1 = (1 / 6) * ∫ x, scalarR x * w x ∂μ := by
    unfold diagTraceCoeffInt
    have hpt : ∀ x, ud 1 x * w x = (1 / 6) * (scalarR x * w x) := by
      intro x; rw [hud1]; ring
    simp_rw [hpt]
    rw [integral_const_mul]
  rw [sum_range_split_two (fun k => diagTraceCoeffInt ud w μ k * t ^ k) N hN]
  simp only [pow_zero, mul_one, pow_one, hW0, hW1]

/-- **#8 (stretch) — leading term explicit, measure-theoretic.** Rewriting the prefactor via
    `heatKernel1D_zero`, the measure-theoretic parametrix diagonal trace is manifestly `(√(4πt))⁻ⁿ`
    (`= (4πt)^{−d/2}`) times the DeWitt polynomial, so the leading short-time term is
    `(4πt)^{−d/2}·Vol = (4πt)^{−d/2}·∫√g dV`. -/
theorem parametrixDiagTraceInt_a1_explicit (N : ℕ) (ud : ℕ → Point n → ℝ) (w : Point n → ℝ)
    (scalarR : Point n → ℝ) (μ : Measure (Point n)) (t : ℝ) (hN : 1 ≤ N)
    (hInt : ∀ k ∈ Finset.range (N + 1), Integrable (fun x => ud k x * w x) μ)
    (hud0 : ∀ x, ud 0 x = 1)
    (hud1 : ∀ x, ud 1 x = scalarR x / 6) :
    parametrixDiagTraceInt N ud w μ t
      = ((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n
        * ((∫ x, w x ∂μ)
            + (1 / 6) * (∫ x, scalarR x * w x ∂μ) * t
            + ∑ k ∈ Finset.Ico 2 (N + 1), diagTraceCoeffInt ud w μ k * t ^ k) := by
  rw [parametrixDiagTraceInt_a1 N ud w scalarR μ t hN hInt hud0 hud1, heatKernel1D_zero]

end QIQTH.HeatParametrixTrace
