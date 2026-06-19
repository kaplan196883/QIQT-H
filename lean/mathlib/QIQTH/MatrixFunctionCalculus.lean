import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Matrix function calculus — the power derivative (toward the trace-derivative formula)

Mathlib's Fréchet derivative of `exp`/`log` is available only for *commutative* Banach algebras
(`hasFDerivAt_exp` lives in `section RCLikeCommAlgebra` with `[NormedCommRing 𝔸]`), so it does not
apply to `Matrix n n ℂ`.  This file begins building the non-commutative matrix function calculus from
the ground up, starting with the **power rule** for the one-parameter affine family `t ↦ (A + t·H)^n`:

  `d/dt (A + t·H)^n |₀ = Σ_{k=0}^{n-1} A^k · H · A^{n-1-k}`

(the non-commutative Leibniz expansion).  Its trace, by cyclicity, collapses to `n·tr(A^{n-1} H)` — the
polynomial case of the trace-derivative `d/dt Tr g(A+tH)|₀ = Tr(g'(A) H)`, which underlies the
first-order entanglement first law `δS = δ⟨K⟩`.  Proved by induction on `n` via `HasDerivAt.mul`.
Axiom-free.
-/

namespace QIQTH.MatrixCalculus

open Matrix
open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The matrix power rule:** `d/dt (A + t·H)^m |_{t=0} = Σ_{k<m} A^k · H · A^{m-1-k}` — the
    non-commutative Leibniz expansion of the derivative of a matrix power along an affine path. -/
theorem hasDerivAt_matrixPow (A H : Matrix n n ℂ) (m : ℕ) :
    HasDerivAt (fun t : ℝ => (A + t • H) ^ m)
      (∑ k ∈ Finset.range m, A ^ k * H * A ^ (m - 1 - k)) 0 := by
  induction m with
  | zero =>
      simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
      exact hasDerivAt_const 0 1
  | succ p ih =>
      have h1 : HasDerivAt (fun t : ℝ => t • H) H 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const H
      have hf : HasDerivAt (fun t : ℝ => A + t • H) H 0 := h1.const_add A
      have hmul := hf.mul ih
      have hpow : (fun t : ℝ => (A + t • H) ^ (p + 1))
          = fun t : ℝ => (A + t • H) * (A + t • H) ^ p := by
        funext t; rw [pow_succ']
      rw [hpow]
      have hd : (∑ k ∈ Finset.range (p + 1), A ^ k * H * A ^ (p + 1 - 1 - k))
          = H * (A + (0 : ℝ) • H) ^ p
            + (A + (0 : ℝ) • H) * ∑ k ∈ Finset.range p, A ^ k * H * A ^ (p - 1 - k) := by
        simp only [zero_smul, add_zero]
        rw [Finset.mul_sum, Finset.sum_range_succ' _ p, add_comm]
        congr 1
        · simp
        · refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← pow_succ',
            show p + 1 - 1 - (k + 1) = p - 1 - k from by omega]
      rw [hd]
      exact hmul

/-- **Trace collapse of the Leibniz sum:** `Tr(Σ_{k<m} A^k H A^{m-1-k}) = m · Tr(A^{m-1} H)` — by
    cyclicity every term equals `Tr(A^{m-1} H)`.  Composing with `hasDerivAt_matrixPow` (via the
    continuous-linear trace) gives the polynomial trace-derivative `d/dt Tr((A+tH)^m)|₀ = m Tr(A^{m-1}H)`,
    the polynomial case of `d/dt Tr g(A+tH)|₀ = Tr(g'(A)H)`. -/
theorem trace_leibniz_sum (A H : Matrix n n ℂ) (m : ℕ) :
    (∑ k ∈ Finset.range m, A ^ k * H * A ^ (m - 1 - k)).trace
      = (m : ℂ) * (A ^ (m - 1) * H).trace := by
  rw [Matrix.trace_sum, Finset.sum_congr rfl (fun k hk => by
    rw [Matrix.trace_mul_cycle, ← pow_add,
      show m - 1 - k + k = m - 1 from by have := Finset.mem_range.mp hk; omega]),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The trace power rule** `d/dt Tr((A + t·H)^m)|_{t=0} = m · Tr(A^{m-1} H)` — the polynomial case
    of the trace-derivative `d/dt Tr g(A+tH)|₀ = Tr(g'(A) H)`, which underlies the first-order
    entanglement first law `δS = δ⟨K⟩`.  Composes `hasDerivAt_matrixPow` with the continuous-linear
    trace (`restrictScalars ℝ`) and collapses the Leibniz sum via `trace_leibniz_sum`. -/
theorem hasDerivAt_trace_matrixPow (A H : Matrix n n ℂ) (m : ℕ) :
    HasDerivAt (fun t : ℝ => ((A + t • H) ^ m).trace) ((m : ℂ) * (A ^ (m - 1) * H).trace) 0 := by
  have hT : HasFDerivAt (fun M : Matrix n n ℂ => M.trace)
      (((Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap).restrictScalars ℝ)
      ((A + (0 : ℝ) • H) ^ m) :=
    (ContinuousLinearMap.hasFDerivAt
      (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap).restrictScalars ℝ
  have h := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hT (hasDerivAt_matrixPow A H m) rfl
  have hval : (((Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap).restrictScalars ℝ)
      (∑ k ∈ Finset.range m, A ^ k * H * A ^ (m - 1 - k))
      = (m : ℂ) * (A ^ (m - 1) * H).trace := trace_leibniz_sum A H m
  rw [← hval]
  exact h

/-- **The trace polynomial rule** (linearity lift of `hasDerivAt_trace_matrixPow`): for any finite
    ℂ-combination of powers `p(M) = Σ_{m<N} c_m M^m` (i.e. any polynomial),
    `d/dt Tr(p(A + t·H))|_{t=0} = Σ_{m<N} c_m · m · Tr(A^{m-1} H) = Tr(p'(A) H)`.  Immediate from
    `HasDerivAt.sum` + `const_smul` over the trace power rule. -/
theorem hasDerivAt_trace_sumPow (A H : Matrix n n ℂ) (c : ℕ → ℂ) (N : ℕ) :
    HasDerivAt (fun t : ℝ => (∑ m ∈ Finset.range N, c m • (A + t • H) ^ m).trace)
      (∑ m ∈ Finset.range N, c m * ((m : ℂ) * (A ^ (m - 1) * H).trace)) 0 := by
  have hfun : (fun t : ℝ => (∑ m ∈ Finset.range N, c m • (A + t • H) ^ m).trace)
      = ∑ m ∈ Finset.range N, (fun t : ℝ => c m • ((A + t • H) ^ m).trace) := by
    funext t
    simp only [Finset.sum_apply, Matrix.trace_sum, Matrix.trace_smul]
  rw [hfun]
  have h : HasDerivAt (∑ m ∈ Finset.range N, (fun t : ℝ => c m • ((A + t • H) ^ m).trace))
      (∑ m ∈ Finset.range N, c m • ((m : ℂ) * (A ^ (m - 1) * H).trace)) 0 :=
    HasDerivAt.sum (fun m _ => (hasDerivAt_trace_matrixPow A H m).const_smul (c m))
  simpa only [smul_eq_mul] using h

/-- **The trace power rule at a general base point** `d/dt Tr((A + t·H)^m)|_{t=t₀} =
    m · Tr((A + t₀·H)^{m-1} H)` — the derivative holds *everywhere*, not just at `0`.  By the affine
    shift `t ↦ t − t₀` reducing to the base-point-`0` rule with `A ↦ A + t₀·H`.  This is the form the
    entire-function (power-series) case `d/dt Tr(exp(A+tH))` consumes via `hasDerivAt_tsum`. -/
theorem hasDerivAt_trace_matrixPow_at (A H : Matrix n n ℂ) (m : ℕ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ((A + t • H) ^ m).trace)
      ((m : ℂ) * ((A + t₀ • H) ^ (m - 1) * H).trace) t₀ := by
  have key := hasDerivAt_trace_matrixPow (A + t₀ • H) H m
  have hshift : HasDerivAt (fun t : ℝ => t - t₀) 1 t₀ := (hasDerivAt_id t₀).sub_const t₀
  have h := key.scomp_of_eq t₀ hshift (sub_self t₀).symm
  simp only [one_smul] at h
  have hfun : (fun t : ℝ => ((A + t₀ • H + (t - t₀) • H) ^ m).trace)
      = fun t : ℝ => ((A + t • H) ^ m).trace := by
    funext t
    rw [add_assoc, ← add_smul, show t₀ + (t - t₀) = t from by ring]
  rw [Function.comp_def] at h
  rwa [hfun] at h