/-
  ParametrixResidualTPower — M6 / G2 (t-POWER / GENERAL-N): the ansatz-order smallness step.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE G2 QUESTION (read it).

  The Levi/Duhamel convergence machinery (`QIQTH.LeviSeries`) closes the Neumann series for the
  parametrix residual `E` from a ONE-STEP bound `|E τ p q| ≤ C · baseKernel α τ p q`, where
  `baseKernel α τ p q = τ^α · G_τ(p−q)` (`τ^α` = `Real.rpow`, `α` the "ansatz-order smallness").
  The a-priori worry (G2) was that the machinery needs a STRICTLY POSITIVE time-power `α > 0` — the
  smallness that the general-`N` parametrix `H_N = G·Σ_{k≤N} w_k t^k` is supposed to supply through
  its `O(t^N)` residual (which in turn needs the DeWitt TRANSPORT RECURSION on the `w_k`).  The
  `N = 0` residual, by contrast, only gives `α = 0` after its singular `1/t`, `1/t²` pieces are
  ABSORBED by the off-diagonal cancellation into a bare Gaussian
  (`ParametrixResidualN0Bound.residualN0_gaussian_bound` : `|E| ≤ C · gaussDdimWide`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE FINDING (G2 is VACUOUS).

  The summability does NOT need `α > 0`.  Reading the machinery verbatim:

    • `LeviSeries.modelCoeff_summable`     needs  `hα : 0 ≤ α`   (NOT `0 < α`);
    • `LeviSeries.scaledModelCoeff_summable` needs `hα : 0 ≤ α`;
    • `LeviSeries.iterConv_bound`          needs  NO `hα` at all;
    • `LeviSeries.leviSeries_summable`     needs  `hα : 0 ≤ α`.

  The reason is structural: convergence comes from the FACTORIAL (Beta-function / Γ) decay of the
  iterated convolution (`TimeSimplexBeta.iterKernel_eq`), NOT from the time-power.  At `α = 0`,

      iterKernel 0 k t x y = t^(k−1) / Γ(k) · G_t(x−y)     (k ≥ 1)      -- `iterKernel_zero_eq`,

  i.e. the CLASSICAL Levi/Duhamel heat-parametrix iteration, whose `1/Γ(k) = 1/(k−1)!` factorial
  decay beats any geometric `C^k` (the ratio test `LeviSeries.gamma_ratio_tendsto_zero` needs only
  `β = α+1 ≥ 1`, and `α = 0 ⟹ β = 1` is admitted at the boundary).  So the `α = 0` bare-Gaussian
  one-step bound — exactly what the `N = 0` absorbed residual delivers — ALREADY drives the Neumann
  series to convergence.  The general-`N` transport-recursion route is NOT the load-bearing path.

  WHAT LANDS HERE.

    • `baseKernel_zero_eq` — `baseKernel 0 τ p q = gaussDdim τ (p−q)` (`Real.rpow_zero`): the `α = 0`
      base kernel IS the bare Gaussian, with NO positive time-power.

    • `iterKernel_zero_eq` — the `α = 0` iterated-kernel formula `t^(k−1)/Γ(k) · G_t` exhibiting the
      pure factorial decay (`iterKernel_eq` at `α = 0`, `Γ(1) = 1`).

    • `leviSeries_summable_alpha_zero` — ★ THE G2 DELIVERABLE.  For the `α = 0` bare-Gaussian one-step
      bound `|E τ p q| ≤ C · gaussDdim τ (p−q)` (NO time-power), `C ≥ 0`, and the carried per-step
      integrability, the residual Neumann series converges:
          `Summable (fun k => iterE E (k+1) t x y)`.
      A direct instantiation of `LeviSeries.leviSeries_summable` at `α = 0` (`0 ≤ 0`), rewriting the
      base kernel via `baseKernel_zero_eq`.  This is the precise sense in which G2 is VACUOUS: the
      absorbed `N = 0` bound (`α = 0`) is summability-compatible; no `α > 0` and no general-`N`
      transport recursion are required for convergence.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).

  FLOOR LANDED:
    • F1 — CONFIRMED `α = 0` suffices for the Neumann summability (the α-constraint of every step is
      `0 ≤ α`, and `iterConv_bound` needs none), so G2 is resolved via the existing absorbed `N = 0`
      bound + the (now-closed) G3 width identification — no `α > 0` needed.
    • F2 — the `α = 0` summability-compatibility lemma (`leviSeries_summable_alpha_zero`) plus the
      explicit factorial-decay witness (`iterKernel_zero_eq`).
    • F3 — ASSESSMENT: G2 is **VACUOUS**.  The DeWitt transport recursion IS in fact PROVEN in the
      repo (`ParametrixFunction.transportCoeff_succ_transport_eq` : `(k+1 + r∂_r) u_{k+1} = T u_k`, a
      genuine theorem via `radialTransportSolve_transport_eq`, NOT an abstract/carried coefficient),
      so the general-`N` `O(t^N)` route WOULD be available if it were needed — but it is NOT needed
      for convergence.  (What the transport recursion IS load-bearing for is the LIMIT's coefficient
      identification `u₁(0) = R/6`, i.e. C6 / the diagonal expansion — a separate concern from G2.)

  What this is NOT:
    • NOT the WIRING of the concrete `N = 0` residual bound (`residualN0_gaussian_bound`, in single
      RNC coordinate `v` with `gaussDdimWide`) into this abstract `α = 0` interface (two-point `(p,q)`
      representation with `gaussDdim`).  The width step is G3 (closed); the `v → (p−q)` difference
      representation is the remaining M6 convergence-wiring (G1 global).
    • NOT the general-`N` `O(t^N)` residual identity (the off-diagonal general-`v` transport
      cancellation is the DEFERRED CHECKPOINT of `ParametrixResidualO1Total`); it is unnecessary for
      G2 but would sharpen the residual order if pursued.
    • NOT `a₁ = R/6` (the diagonal Seeley–DeWitt value stays carried until C6 closes).

  No `sorry`, no new axioms, no vacuous hypotheses.  Grounded in the Grigor'yan-style Gaussian
  iterated-convolution program and Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.
-/
import Mathlib
import QIQTH.GaussianWidthTolerant
import QIQTH.LeviSeries
import QIQTH.ParametrixResidualN0Bound
import QIQTH.ParametrixResidualO1Total
import QIQTH.VanVleckCancellation

open Real MeasureTheory Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TimeSimplexBeta QIQTH.LeviSeries

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### 1. The `α = 0` base kernel IS the bare Gaussian (no time-power). -/

/-- **The `α = 0` base kernel is the bare Gaussian.**  `baseKernel 0 τ p q = gaussDdim τ (p−q)`,
    since `τ^(0:ℝ) = 1` (`Real.rpow_zero`, unconditionally in `τ`).  This is the shape of the
    ABSORBED `N=0` residual bound (`residualN0_gaussian_bound` : `|E| ≤ C·gaussDdimWide`): a bare
    Gaussian with NO positive time-power, i.e. the `α = 0` case. -/
theorem baseKernel_zero_eq (τ : ℝ) (p q : Point n) :
    baseKernel (0 : ℝ) τ p q = gaussDdim τ (p - q) := by
  unfold baseKernel
  rw [Real.rpow_zero, one_mul]

/-! ### 2. The `α = 0` iterated kernel — the classical factorial decay. -/

/-- **The `α = 0` iterated-kernel formula (classical Levi/Duhamel).**  For `t > 0`, `x y`, and
    `k ≥ 1`,
        `iterKernel 0 k t x y = t^(k−1) / Γ(k) · G_t(x−y)`.
    Specialising `TimeSimplexBeta.iterKernel_eq` to `α = 0` (`Γ(0+1) = Γ(1) = 1`, `(k)(0+1) = k`):
    the `1/Γ(k) = 1/(k−1)!` factorial (Beta-function) decay is exactly the classical short-time
    heat-parametrix iteration.  It is this decay — NOT any time-power — that makes the Neumann series
    converge, which is why `α = 0` already suffices (G2 vacuous). -/
theorem iterKernel_zero_eq (t : ℝ) (ht : 0 < t) (x y : Point n) {k : ℕ} (hk : 1 ≤ k) :
    iterKernel (0 : ℝ) k t x y
      = t ^ ((k : ℝ) - 1) / Real.Gamma (k : ℝ) * gaussDdim t (x - y) := by
  rw [iterKernel_eq (0 : ℝ) (by norm_num) t ht x y hk]
  simp only [zero_add, mul_one, Real.Gamma_one, one_pow]
  ring

/-! ### 3. ★ THE G2 DELIVERABLE — the `α = 0` bare-Gaussian bound drives convergence. -/

/-- **★ G2 (t-POWER / GENERAL-N) IS VACUOUS — the `α = 0` bare-Gaussian one-step bound already drives
    the Neumann series to convergence.**  For a residual kernel `E` obeying the `α = 0` one-step bound
        `hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C · gaussDdim τ (p−q)`   (NO positive time-power),
    with `C ≥ 0` and the carried per-step integrability `hInt : IterConvIntegrable E 0 C`, the
    Levi/Duhamel Neumann series for `E` converges at every `t > 0` and `x y`:
        `Summable (fun k => iterE E (k+1) t x y)`.
    This is a DIRECT instantiation of `LeviSeries.leviSeries_summable` at `α = 0` (whose α-constraint
    is `0 ≤ α`, satisfied by `0 ≤ 0` — no `α > 0` required), rewriting `baseKernel 0` into the bare
    Gaussian via `baseKernel_zero_eq`.  The convergence is powered by the factorial (Γ) decay
    (`iterKernel_zero_eq`), not by any smallness time-power — establishing that the ABSORBED `N = 0`
    residual bound (`α = 0`) is summability-compatible, so the general-`N` transport-recursion route
    is UNNECESSARY for convergence (G2 vacuous).  NOT the concrete-residual wiring, NOT `a₁ = R/6`. -/
theorem leviSeries_summable_alpha_zero
    (E : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * gaussDdim τ (p - q))
    (hInt : IterConvIntegrable E 0 C) (t : ℝ) (ht : 0 < t) (x y : Point n) :
    Summable (fun k : ℕ => iterE E (k + 1) t x y) := by
  refine leviSeries_summable E 0 C le_rfl hC (fun τ p q hτ => ?_) hInt t ht x y
  rw [baseKernel_zero_eq]
  exact hEbound τ p q hτ

/-- **The one-step `α = 0` iterated-residual bound in bare-Gaussian form.**  A convenience corollary of
    `LeviSeries.iterConv_bound` at `α = 0`: from the bare-Gaussian one-step bound (NO time-power), the
    `k`-fold iterated residual is dominated by `C^k · iterKernel 0 k`, i.e. — via `iterKernel_zero_eq` —
    by `C^k · t^(k−1)/Γ(k) · G_t`, the classical factorial-decaying Levi term.  Confirms the `α = 0`
    domination step needs no `hα` at all. -/
theorem iterConv_bound_alpha_zero
    (E : ℝ → Point n → Point n → ℝ) (C : ℝ)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * gaussDdim τ (p - q))
    (hInt : IterConvIntegrable E 0 C) {k : ℕ} (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t) (x y : Point n) :
    |iterE E k t x y|
      ≤ C ^ k * (t ^ ((k : ℝ) - 1) / Real.Gamma (k : ℝ) * gaussDdim t (x - y)) := by
  have hbd := iterConv_bound E 0 C (fun τ p q hτ => by
    rw [baseKernel_zero_eq]; exact hEbound τ p q hτ) hInt k hk t ht x y
  rwa [iterKernel_zero_eq t ht x y hk] at hbd

end QIQTH.HeatResidualBound
