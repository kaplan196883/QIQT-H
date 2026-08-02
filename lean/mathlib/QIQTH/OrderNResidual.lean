/-
  OrderNResidual — J4-102 of the a₁=R/6 campaign: the ORDER-`N` REBUILD of the near-residual /
  witness chain (census-driven; the confirmed next piece after the J4-101 census + Sol verdict).

  WHY (the load-bearing motivation).  The hunif tower's witness hard-codes `heatParametrix 0 Θ u`
  (order-0 truncation `gauss·u₀`), but the a₁=R/6 capstone's `hHdiag` (with `hN : 1 ≤ N`) demands
  the `N ≥ 1` parametrix `gauss·(u₀ + t·u₁ + …)` — and `u₁(0) = R/6` is the extracted coefficient.
  So the residual/witness chain must run at `heatParametrix N` (minimally `N = 1`, time-dependent
  amplitude).  The J4-101 census established that `heatParametrix` and `parametrixResidualN` are
  ALREADY `N`-parametric defs, and the general-`N` residual IDENTITIES are ALREADY built
  (`HeatResidualBound.parametrixResidual_telescope_N`, `…_offdiag_absorbed`).  What was `N = 0`-baked
  was the DOWNSTREAM STATEMENT chain (the near packet consumer + the witness def), whose PROOFS turn
  out to be `N`-AGNOSTIC (`from_packet` is literally `simpa only [parametrixResidualN]`).

  WHAT IS BUILT HERE.
    • `near_uncutResidual_gaussianWide_ball_from_packet_orderN` — THE `N`-GENERIC near packet
      consumer: from an explicit-radius residual Gaussian bound on `parametrixResidualN N`, produce
      the `hEnear` ball shape on `heatParametrix N`.  This is `UniformNearEngine`'s `…_from_packet`
      with the hard-coded `0` replaced by an arbitrary `N` — the proof is identical (only unfolds
      `parametrixResidualN`), confirming the census verdict that the near engine is `N`-agnostic.
    • `parametrixResidual_one_diag_tail` — THE `N = 1` DIAGONAL RESIDUAL "one-split": the exact
      instantiation of the general-`N` telescoping at `N = 1`,
        `(∂_t − Δ_g) H_1(t,0) = − G(0)·Δ_g(w_1)(0)·t` ,
      i.e. the `t^0` order cancels against the flat-heat term and the transport recursion, leaving
      the `t^1` tail — the EXTRA `t` factor the campaign needs (vs the `t^0` residual of `N = 0`).
      The single-step folded transport recursion `hrec1 : w_1(0) = Δ_g(w_0)(0)` is carried as a
      genuine, load-bearing hypothesis (from J3/J4 `transportCoeff_succ_transport_eq` at the
      diagonal).
    • `globalCutoffParametrixWitnessN` — THE `N`-PARAMETRIC witness (the `heatParametrix N`
      generalization of `GlobalResidualWitness.globalCutoffParametrixWitness`), with
      `globalCutoffParametrixWitnessN_zero` proving it reduces to the existing `N = 0` witness
      definitionally.

  ⚠ HONEST FIREWALL (binding).  This is the `N`-generic PLUMBING + the `N = 1` diagonal algebraic
  tail.  It does NOT build the actual `N = 1` residual GAUSSIAN BOUND (the input `hRes` of the packet
  consumer) — that is the deep C³ Taylor-remainder work (the `residualN0_gaussian_bound_C3` analog at
  `N = 1`, off-diagonal, via `parametrixResidual_offdiag_absorbed`); it is CARRIED as the packet
  hypothesis exactly as the `N = 0` engine carries it.  No `a₁ = R/6`, no `expRho`.  No axioms, no
  `sorry`.
-/
import Mathlib
import QIQTH.UniformNearEngine
import QIQTH.GlobalResidualWitness

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatParametrixError
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.GaussianWidthTolerant QIQTH.RNCDecay
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### #1 — the `N`-generic near packet consumer (the census verdict, in Lean). -/

/-- **★ J4-102 (#1) — THE NEAR ENGINE, ORDER-`N` GENERIC.**  Over ANY abstract metric field `g` with
    inverse `gi` and heat profiles `Θ`/`u`, for ANY truncation order `N`, from an EXPLICIT-radius near
    residual Gaussian bound
        `hRes : ∀ v, ‖v‖ < ρ → |parametrixResidualN N g gi Θ u t v| ≤ C · gaussDdimWide t v`   (`ρ > 0`),
    we obtain the `hEnear` ball shape at outer radius `b = ρ/2`:
        `∃ b > 0, ∀ w, rncRadialSq w ≤ b² →
           |∂ₜ(heatParametrix N Θ u · t)(w) − Δ_g(heatParametrix N Θ u t)(w)| ≤ C · gaussDdimWide t w` .
    This is verbatim `UniformNearEngine.near_uncutResidual_gaussianWide_ball_from_packet` with the
    hard-coded truncation `0` replaced by the general `N`: the ball conversion (`rncRadialSq w ≤ (ρ/2)²
    ⟹ ‖w‖ ≤ ρ/2 < ρ`, via `norm_le_rncRadial`) is `N`-independent, and `parametrixResidualN N` unfolds
    definitionally to `∂ₜH − Δ_g H`.  This confirms the J4-101 census verdict that the near engine is
    `N`-agnostic.  No `expRho`; NOT `a₁ = R/6`. -/
theorem near_uncutResidual_gaussianWide_ball_from_packet_orderN
    (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {t : ℝ} (C ρ : ℝ) (hρ : 0 < ρ)
    (hRes : ∀ v : Point n, ‖v‖ < ρ →
      |parametrixResidualN N g gi Θ u t v| ≤ C * gaussDdimWide t v) :
    ∃ b : ℝ, 0 < b ∧
      ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix N Θ u s w) t
            - laplaceBeltrami g gi (heatParametrix N Θ u t) w|
          ≤ C * gaussDdimWide t w := by
  refine ⟨ρ / 2, by linarith, fun w hw => ?_⟩
  have hb0 : (0 : ℝ) ≤ ρ / 2 := by linarith
  have hnw : ‖w‖ < ρ := by
    have h1 : ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
    have h2 : rncRadial w ≤ ρ / 2 := by
      rw [rncRadial]
      calc Real.sqrt (rncRadialSq w)
          ≤ Real.sqrt ((ρ / 2) ^ 2) := Real.sqrt_le_sqrt hw
        _ = ρ / 2 := by rw [Real.sqrt_sq hb0]
    linarith
  have hs := hRes w hnw
  simpa only [parametrixResidualN] using hs

/-- **★ J4-102 — the `N = 1` instantiation of the near packet consumer** (a convenience corollary of
    `…_orderN` at `N = 1`).  From a residual Gaussian bound on `parametrixResidualN 1`, produce the
    `hEnear` ball shape on the ORDER-1 parametrix `heatParametrix 1 Θ u` (the `gauss·(u₀ + t·u₁)`
    ansatz the a₁ capstone's `hHdiag` demands).  Trivial `N := 1` specialization. -/
theorem near_uncutResidual_gaussianWide_ball_from_packet_one
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {t : ℝ} (C ρ : ℝ) (hρ : 0 < ρ)
    (hRes : ∀ v : Point n, ‖v‖ < ρ →
      |parametrixResidualN 1 g gi Θ u t v| ≤ C * gaussDdimWide t v) :
    ∃ b : ℝ, 0 < b ∧
      ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix 1 Θ u s w) t
            - laplaceBeltrami g gi (heatParametrix 1 Θ u t) w|
          ≤ C * gaussDdimWide t w :=
  near_uncutResidual_gaussianWide_ball_from_packet_orderN 1 g gi Θ u C ρ hρ hRes

/-! ### #2 — the `N = 1` diagonal residual "one-split" (the extra `t` factor). -/

/-- **★ J4-102 (#2) — THE `N = 1` DIAGONAL RESIDUAL ONE-SPLIT.**  At the RNC diagonal center `0`,
    GIVEN the single-step folded transport recursion
        `hrec1 : w_1(0) = Δ_g(w_0)(0)`   (`w_k = Θ^{−1/2}u_k`, the `k = 0` datum of J3/J4's
    `transportCoeff_succ_transport_eq` at the diagonal, where `radialDeriv (·) 0 = 0` and the leading
    coefficient `(0+1) = 1`), the heat-operator residual of the ORDER-1 parametrix is EXACTLY the
    `t^1` tail:
        `(∂_t − Δ_g) H_1(t,0) = − G(0)·Δ_g(w_1)(0)·t` .
    The order-`t^0` term cancels (flat heat equation `∂_t G = Δ_g G` at the center kills the leading
    Laplacian term; `hrec1` telescopes the remaining bracket), leaving the EXTRA `t` factor — the
    structural reason the `N = 1` residual is `O(t)·G` rather than `O(1)·G` (the `N = 0` case).  This
    is the exact `N = 1` instance of `parametrixResidual_telescope_N`.  No `a₁ = R/6`. -/
theorem parametrixResidual_one_diag_tail
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hrec1 : foldedCoeff Θ u 1 (0 : Point n)
      = laplaceBeltrami g gi (foldedCoeff Θ u 0) (0 : Point n)) :
    parametrixResidualN 1 g gi Θ u t (0 : Point n)
      = - gaussDdim t (0 : Point n)
          * laplaceBeltrami g gi (foldedCoeff Θ u 1) (0 : Point n) * t := by
  have h := parametrixResidual_telescope_N 1 g gi Θ u t ht hgi hΓ hw
    (fun k hk => by
      obtain rfl : k = 0 := Nat.lt_one_iff.mp hk
      simpa using hrec1)
  simpa using h

/-! ### #3 — the `N`-parametric global-cutoff witness (parametrizing the hard-coded `0`). -/

/-- **★ J4-102 (#3) — THE ORDER-`N` GLOBAL-CUTOFF PARAMETRIX WITNESS.**  The `heatParametrix N`
    generalization of `GlobalResidualWitness.globalCutoffParametrixWitness` (which hard-codes
    `heatParametrix 0`): `H_w^N = χ_{a,b}(V_q p)·H_N(τ, V_q p)`, the radially-cutoff order-`N`
    parametrix pulled back through the inverse chart `Vmap`.  This is the witness the a₁ capstone's
    `hHdiag` (`1 ≤ N`) requires. -/
noncomputable def globalCutoffParametrixWitnessN (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (Vmap : Point n → Point n → Point n) (τ : ℝ) (p q : Point n) : ℝ :=
  radialCutoff a b (Vmap q p) * heatParametrix N Θ u τ (Vmap q p)

/-- **The order-`N` witness reduces to the existing `N = 0` witness definitionally.**  Confirms the
    parametrization is a strict generalization: `globalCutoffParametrixWitnessN 0 = globalCutoffParametrixWitness`. -/
theorem globalCutoffParametrixWitnessN_zero (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (Vmap : Point n → Point n → Point n) (τ : ℝ) (p q : Point n) :
    globalCutoffParametrixWitnessN 0 Θ u a b Vmap τ p q
      = globalCutoffParametrixWitness Θ u a b Vmap τ p q := rfl

end QIQTH.HeatResidualBound
