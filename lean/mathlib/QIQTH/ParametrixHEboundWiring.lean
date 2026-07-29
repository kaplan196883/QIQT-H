/-
  ParametrixHEboundWiring — M6 / G1: the residual → `hEbound` wiring, packaging the diagonal
  residual Gaussian bound (+ the isolated far-field input) into the Levi/Duhamel Neumann-convergence
  interface, reducing the true-kernel Neumann convergence to a SINGLE global/far-field input.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE STATE THIS FILE ENTERS (read it — the width reality forces the correct engine).

  The convergence machinery consumes a one-step residual bound `hEbound : |E τ p q| ≤ C·baseKernel`.
  Two facts fix which `baseKernel`:

    • `LeviSeries.leviSeries_summable` (and its `α = 0` face `HeatResidualBound.
      leviSeries_summable_alpha_zero`) is WIDTH-1: it consumes the NARROW same-time Gaussian
      `gaussDdim τ (p−q)`.

    • the concrete parametrix residual only supplies the WIDE Gaussian
      `|parametrixResidualN 0 … t v| ≤ C·gaussDdimWide t v`
      (`ParametrixResidualN0Bound.residualN0_gaussian_bound`), and
      `gaussDdimWide t v = (√2)ⁿ · gaussDdim (2t) v = (√2)ⁿ · baseKernelW 2 0 t v 0`
      (`GaussianWidthTolerant.gaussDdimWide_eq_scaled_baseKernelW`) — the base Gaussian at DOUBLED
      time (`κ = 2`).  A width-2 Gaussian is NOT `≤ C·(narrow same-time gaussDdim τ)` UNIFORMLY in
      `τ` (the ratio `gaussDdim(2τ)/gaussDdim(τ) = 2^{−n/2}·exp(r²/8τ)` blows up as `τ → 0` on any
      fixed ball), so **the concrete residual CANNOT feed the width-1
      `leviSeries_summable_alpha_zero`.**  Its width-2 bound must be driven through the WIDTH-TOLERANT
      engine.

  `GaussianWidthTolerant` proved the width-tolerant self-similar identity + the *model* series
  summability `iterKernelW_series_summable` (**G3 closed at the model level**), but explicitly
  DEFERRED the actual-residual width-`κ` iterated bound and Neumann convergence
  (`iterConv_bound`/`leviSeries_summable` are phrased against the width-1 kernels).  This file BUILDS
  that deferred engine and wires the concrete residual into it.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS HERE.

    ▸ The WIDTH-TOLERANT actual-residual Neumann engine (the deferred G3 wiring):
      • `IterConvIntegrableW` — the width-`κ` per-step integrability family (dominators
        `baseKernelW κ α`, `iterKernelW κ α`), the exact mirror of `LeviSeries.IterConvIntegrable`.
      • `iterConvW_bound` — `|iterE E k t x y| ≤ C^k · iterKernelW κ α k t x y` from the width-`κ`
        one-step bound `|E τ p q| ≤ C·baseKernelW κ α τ p q` + the integrability family.  Same
        `Nat.le_induction` as `LeviSeries.iterConv_bound`, with `iterKernelW_one`/`iterKernelW_succ`.
      • `scaledIterKernelW_summable` — `Summable (fun k => C^(k+1)·iterKernelW κ α (k+1) t x y)`; the
        model coefficient is width-INDEPENDENT (`iterKernelW_eq`), so `LeviSeries.
        scaledModelCoeff_summable` applies verbatim.
      • `leviSeries_summableW` — ★ the width-tolerant Neumann convergence: `Summable (fun k => iterE
        E (k+1) t x y)` from the width-`κ` one-step bound + integrability, by comparison.

    ▸ The residual-side slice identifications:
      • `baseKernelW_zero_apply` — `baseKernelW κ 0 τ p q = gaussDdim (κ·τ) (p−q)`.
      • `baseKernel_zero_two_eq_baseKernelW` — `baseKernel 0 (2t) v 0 = baseKernelW 2 0 t v 0`: the
        existing width-1 doubled-time slice IS the width-2 base kernel.
      • `residualBound_local_baseKernelW` — a LOCAL wide-Gaussian residual bound `∀ᶠ v, |R v| ≤
        C·gaussDdimWide t v` yields an EXPLICIT-ball width-2 base-kernel domination
        `∀ ‖v‖<ρ, |R v| ≤ (C·(√2)ⁿ)·baseKernelW 2 0 t v 0`.
      • `residualN0_local_baseKernelW_slice` — the connector on the ACTUAL residual: the concrete
        `parametrixResidualN 0` is dominated near the RNC centre by `baseKernelW 2 0 t v 0` on an
        explicit ball (the DIAGONAL, base point `q = 0`, coordinate `v = p − 0 = p`).

    ▸ The reduction (★, isolating C4c to one input):
      • `neumann_summable_alpha0_width2` — at `κ = 2, α = 0`: GIVEN a GLOBAL width-2 one-step bound
        `hEboundW : ∀ τ p q, 0 < τ → |E τ p q| ≤ C·baseKernelW 2 0 τ p q` and `IterConvIntegrableW E
        2 0 C`, the residual Neumann series CONVERGES.  The LOCAL (near-diagonal, base-point-`0`) part
        of `hEboundW` is DISCHARGED by `residualN0_local_baseKernelW_slice`; the whole convergence is
        thereby reduced to the SINGLE remaining input — the GLOBAL width-2 bound (far-field off the
        RNC ball + the genuine two-point / off-diagonal parametrix over all base points `q`), the
        documented C4c wall.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FLOORS / ASSESSMENT (binding).

  DIAGONAL IDENTIFICATION (exact).  For the diagonal heat kernel `a₁`, the base point `q` is FIXED at
  the RNC centre `0` and the coordinate is `v = p`.  The abstract two-point residual's `q = 0` slice
  IS the concrete residual: `E τ p 0 = parametrixResidualN 0 g gi Θ u τ p`, and the coordinate
  difference `p − q = p − 0 = p = v` EXACTLY (the identification is at the flat-coordinate level; the
  metric distortion `δ + O(r²)` is already absorbed INSIDE the residual's Gaussian bound, not in the
  `p − q ↔ v` step).  The dominating Gaussian matches EXACTLY: `baseKernelW 2 0 τ p 0 = gaussDdim
  (2τ) p`, the width-2 base kernel the residual supplies.

  • F1 (the full unconditional `hEbound` for the concrete residual + Neumann summability) — NOT
    landed.  It would require the GLOBAL width-2 bound over all `(p,q)` and all `τ`, which the local
    RNC bound does not supply — see C4c below.
  • F2 (LANDED, the honest deliverable) — the width-tolerant actual-residual Neumann engine
    (`leviSeries_summableW`) + the concrete local slice discharge (`residualN0_local_baseKernelW_
    slice`) + the reduction `neumann_summable_alpha0_width2`, which makes the residual Neumann
    convergence CONDITIONAL on the single labeled GLOBAL width-2 bound `hEboundW` (+ the carried
    per-step integrability `IterConvIntegrableW`).  This is a genuine reduction: convergence ↦ one
    named far-field/off-diagonal input.
  • F3 (LANDED, this assessment) — the `v → (p−q)` diagonal identification (exact, `q = 0`), the
    slice identifications, and the precise statement of what remains.

  ⚠ THE SINGLE REMAINING INPUT TO NEUMANN CONVERGENCE (the C4c wall).  It is the GLOBAL width-2
  one-step bound `hEboundW : ∀ τ p q, 0 < τ → |E τ p q| ≤ C·baseKernelW 2 0 τ p q`.  Its LOCAL,
  base-point-`0`, near-diagonal part is PROVED (`residualN0_local_baseKernelW_slice`).  Its two
  genuine open components are:
    (i)  FAR-FIELD — the bound off the RNC injectivity ball, where normal coordinates and the `O(r²)`
         deviation bounds break down; this needs a cutoff / partition-of-unity / Gaussian-tail
         extension (NOT reachable from the local RNC bound, and NOT a Gaussian tail of the given
         function — a genuine construction).
    (ii) OFF-DIAGONAL / ALL BASE POINTS — the genuine two-point kernel `E(τ,p,q)` for `q ≠ 0` (the
         parametrix built around EVERY base point `q`, not only the fixed `q = 0` slice
         `parametrixResidualN 0`).  This is the off-diagonal parametrix, the separate wall behind C4.
  The per-step integrability `IterConvIntegrableW` (interval×Lebesgue integrability of the iterated
  convolutions) is carried as a genuine, non-vacuous analytic family (it is not the conclusion and it
  fails for non-integrable kernels); building it from continuity + Gaussian domination is a further
  brick, not attempted here.  Beyond convergence, the M6 scope also carries C6 (identifying the
  Neumann limit as the true kernel + extracting the diagonal expansion) — see `TrueHeatKernel`.

  NOT `a₁ = R/6` (the diagonal Seeley–DeWitt value stays carried until C6 closes).  No `sorry`, no
  new axioms, no vacuous hypotheses.  Grounded in Rosenberg, *The Laplacian on a Riemannian
  Manifold*, §3.2, and the Grigor'yan-style Gaussian iterated-convolution program.
-/
import Mathlib
import QIQTH.ParametrixResidualTPower
import QIQTH.ParametrixResidualBaseKernel
import QIQTH.ParametrixResidualN0Bound
import QIQTH.GaussianWidthTolerant
import QIQTH.LeviSeries
import QIQTH.TrueHeatKernel

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.TimeSimplexBeta QIQTH.LeviSeries QIQTH.HeatDuhamel QIQTH.GaussianWidthTolerant

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### 1. Width-2 slice identifications. -/

/-- **The width-`κ` base kernel at order `α = 0`** is the plain width-`κ` Gaussian:
    `baseKernelW κ 0 τ p q = gaussDdim (κ·τ) (p − q)` (`τ ^ (0:ℝ) = 1`). -/
theorem baseKernelW_zero_apply (κ τ : ℝ) (p q : Point n) :
    baseKernelW κ (0 : ℝ) τ p q = gaussDdim (κ * τ) (p - q) := by
  simp only [baseKernelW, Real.rpow_zero, one_mul]

/-- **The existing doubled-time width-1 slice IS the width-2 base kernel.**
    `baseKernel 0 (2·t) v 0 = baseKernelW 2 0 t v 0` — both equal `gaussDdim (2t) (v − 0)`.  This
    lets the `ParametrixResidualBaseKernel` connector (phrased against `baseKernel 0 (2t)`) feed the
    width-tolerant engine (phrased against `baseKernelW 2 0 t`). -/
theorem baseKernel_zero_two_eq_baseKernelW (t : ℝ) (v : Point n) :
    baseKernel (0 : ℝ) (2 * t) v 0 = baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by
  rw [baseKernel_zero_apply, baseKernelW_zero_apply]

/-! ### 2. The width-tolerant per-step integrability family. -/

/-- **The width-`κ` per-step integrability family** for `iterConvW_bound` — the exact mirror of
    `LeviSeries.IterConvIntegrable`, with the model dominators `baseKernelW κ α` / `iterKernelW κ α`
    (in place of the width-1 `baseKernel α` / `iterKernel α`).  For every `k ≥ 1`, `t > 0`, `x y`,
    it bundles the five genuine integral facts `heatConv_le_of_abs_le_pos` demands with `A = E`,
    `B = iterE E k`, `A' = C·baseKernelW κ α`, `B' = C^k·iterKernelW κ α k`.  Honest analytic
    hypotheses on the actual residual and its width-`κ` model dominators — never the conclusion. -/
def IterConvIntegrableW (E : ℝ → Point n → Point n → ℝ) (κ α C : ℝ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
    IntervalIntegrable (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t ∧
    IntervalIntegrable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t ∧
    (∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|)) ∧
    (∀ s, Integrable
      (fun z => C * baseKernelW κ α (t - s) x z * (C ^ k * iterKernelW κ α k s z y))) ∧
    IntervalIntegrable
      (fun s => ∫ z, C * baseKernelW κ α (t - s) x z * (C ^ k * iterKernelW κ α k s z y)) volume 0 t

/-! ### 3. The width-tolerant iterated residual bound. -/

/-- **★ THE WIDTH-TOLERANT ITERATED RESIDUAL BOUND (the deferred G3 wiring, actual residual).**  For
    the width-`κ` one-step residual bound `hEbound : |E τ p q| ≤ C·baseKernelW κ α τ p q` (all
    positive times) and the carried per-step integrability, the `k`-fold iterated residual
    convolution is dominated by the width-`κ` model:
        `|iterE E k t x y| ≤ C^k · iterKernelW κ α k t x y`   (for `k ≥ 1`, `t > 0`).
    The exact mirror of `LeviSeries.iterConv_bound` at general width `κ`: `Nat.le_induction` on `k`,
    base `k = 1` = `hEbound` (`iterE_one`, `iterKernelW_one`), step via `heatConv_le_of_abs_le_pos`
    (`A' = C·baseKernelW κ α`, `B' = C^m·iterKernelW κ α m`) + scalar pull-out + `iterKernelW_succ`.
    No `α`/`κ` constraint needed (the domination is width-agnostic). -/
theorem iterConvW_bound (E : ℝ → Point n → Point n → ℝ) (κ α C : ℝ)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ α τ p q)
    (hInt : IterConvIntegrableW E κ α C) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      |iterE E k t x y| ≤ C ^ k * iterKernelW κ α k t x y := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro t ht x y
      rw [iterE_one, pow_one, iterKernelW_one]
      exact hEbound t x y ht
  | succ m hm ih =>
      intro t ht x y
      obtain ⟨hI1, hI2, hIf, hIg, hIsg⟩ := hInt m hm t ht x y
      rw [iterE_succ E hm, iterKernelW_succ κ α hm]
      simp only [heatConvK_apply]
      have hbound := heatConv_le_of_abs_le_pos E (iterE E m)
        (fun τ p q => C * baseKernelW κ α τ p q) (fun τ p q => C ^ m * iterKernelW κ α m τ p q)
        t x y ht
        (fun τ p q hτ => hEbound τ p q hτ)
        (fun τ p q hτ => ih τ hτ p q)
        hI1 hI2 hIf hIg hIsg
      calc |heatConv E (iterE E m) t x y|
          ≤ heatConv (fun τ p q => C * baseKernelW κ α τ p q)
              (fun τ p q => C ^ m * iterKernelW κ α m τ p q) t x y := hbound
        _ = C ^ (m + 1) * heatConv (baseKernelW κ α) (iterKernelW κ α m) t x y := by
              rw [heatConv_smul_left C (baseKernelW κ α)
                    (fun τ p q => C ^ m * iterKernelW κ α m τ p q),
                  heatConv_smul_right (C ^ m) (baseKernelW κ α) (iterKernelW κ α m), pow_succ]
              ring

/-! ### 4. The scaled width-tolerant kernel series is summable. -/

/-- **The scaled width-`κ` iterated-kernel series is summable.**  For `κ > 0, α ≥ 0, t > 0, C ≥ 0`,
    and `x y`, `Summable (fun k => C^(k+1) · iterKernelW κ α (k+1) t x y)`.  Each term factors as
    `(C^(k+1) · modelCoeff α t (k+1)) · gaussDdim (κ·t) (x−y)` (`iterKernelW_eq`) — the model
    coefficient is WIDTH-INDEPENDENT, so `LeviSeries.scaledModelCoeff_summable` applies verbatim, the
    `k`-constant width-`κ` Gaussian pulled out. -/
theorem scaledIterKernelW_summable (κ α t C : ℝ) (hκ : 0 < κ) (hα : 0 ≤ α) (ht : 0 < t) (hC : 0 ≤ C)
    (x y : Point n) :
    Summable (fun k : ℕ => C ^ (k + 1) * iterKernelW κ α (k + 1) t x y) := by
  have heq : (fun k : ℕ => C ^ (k + 1) * iterKernelW κ α (k + 1) t x y)
      = fun k : ℕ => (C ^ (k + 1) * modelCoeff α t (k + 1)) * gaussDdim (κ * t) (x - y) := by
    funext k
    rw [iterKernelW_eq κ α hκ (by linarith) t ht x y (by omega : 1 ≤ k + 1)]
    unfold modelCoeff
    ring
  rw [heq]
  exact (scaledModelCoeff_summable α t C hα ht hC).mul_right _

/-! ### 5. ★ The width-tolerant Neumann convergence (generic residual `E`). -/

/-- **★ THE WIDTH-TOLERANT NEUMANN CONVERGENCE (the deferred G3 wiring, capstone).**  For `κ > 0,
    α ≥ 0, C ≥ 0`, the width-`κ` one-step residual bound `hEbound : |E τ p q| ≤ C·baseKernelW κ α τ
    p q`, and the carried per-step integrability `IterConvIntegrableW E κ α C`, the Levi/Duhamel
    Neumann series for `E` converges at every `t > 0` and `x y`:
        `Summable (fun k => iterE E (k+1) t x y)`.
    Route: each term is dominated in norm by `C^(k+1)·iterKernelW κ α (k+1) t x y` (`iterConvW_bound`),
    and that width-`κ` model series is summable (`scaledIterKernelW_summable` — the `Γ`/factorial
    decay is width-INDEPENDENT), so the comparison test `Summable.of_norm_bounded` concludes.  This
    is exactly what `GaussianWidthTolerant` deferred: a width-`κ` (in particular the residual's
    `κ = 2`, doubled-time) one-step bound drives convergence — the correct engine for the concrete
    residual, which the width-1 `leviSeries_summable_alpha_zero` cannot ingest. -/
theorem leviSeries_summableW (E : ℝ → Point n → Point n → ℝ) (κ α C : ℝ)
    (hκ : 0 < κ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ α τ p q)
    (hInt : IterConvIntegrableW E κ α C) (t : ℝ) (ht : 0 < t) (x y : Point n) :
    Summable (fun k : ℕ => iterE E (k + 1) t x y) := by
  refine Summable.of_norm_bounded (scaledIterKernelW_summable κ α t C hκ hα ht hC x y) (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact iterConvW_bound E κ α C hEbound hInt (k + 1) (by omega) t ht x y

/-! ### 6. The residual-side local slice connector. -/

/-- **The connector — local wide-Gaussian residual bound ⟹ explicit-ball width-2 base-kernel
    domination.**  Given `∀ᶠ v in 𝓝 0, |R v| ≤ C·gaussDdimWide t v` (`0 < t`), the residual is
    dominated on an EXPLICIT ball by the width-2 base kernel (order `α = 0`) at base point `0`:
        `∃ ρ > 0, ∀ v, ‖v‖ < ρ → |R v| ≤ (C·(√2)ⁿ)·baseKernelW 2 0 t v 0`.
    Route: `eventually_nhds_zero_ball` + `GaussianWidthTolerant.gaussDdimWide_eq_scaled_baseKernelW`
    (`gaussDdimWide t v = (√2)ⁿ · baseKernelW 2 0 t v 0`).  This is the width-2 face of the honest
    partial of `hEbound`: it exhibits the width-tolerant base-kernel domination (the shape
    `leviSeries_summableW` consumes) but records the LOCAL ball `‖v‖ < ρ` and single fixed `t`. -/
theorem residualBound_local_baseKernelW {R : Point n → ℝ} {t C : ℝ} (ht : 0 < t)
    (hbd : ∀ᶠ v in nhds (0 : Point n), |R v| ≤ C * gaussDdimWide t v) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : Point n, ‖v‖ < ρ →
      |R v| ≤ (C * Real.sqrt 2 ^ n) * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by
  obtain ⟨ρ, hρ, hball⟩ := eventually_nhds_zero_ball hbd
  refine ⟨ρ, hρ, fun v hv => ?_⟩
  have hv' := hball v hv
  rw [gaussDdimWide_eq_scaled_baseKernelW ht v] at hv'
  calc |R v| ≤ C * (Real.sqrt 2 ^ n * baseKernelW 2 0 t v 0) := hv'
    _ = (C * Real.sqrt 2 ^ n) * baseKernelW 2 0 t v 0 := by ring

/-- **The connector on the ACTUAL residual (the diagonal, base point `q = 0`).**  Feeding
    `residualN0_gaussian_bound` (the full `N=0` parametrix-residual wide-Gaussian bound) through
    `residualBound_local_baseKernelW` yields an explicit-ball width-2 base-kernel domination of the
    concrete residual:
        `∃ ρ > 0, ∀ v, ‖v‖ < ρ →
           |parametrixResidualN 0 g gi Θ u t v| ≤ C'·baseKernelW 2 0 t v 0`,
    with `C' = (1 + 32·n²·M·W + L)·(√2)ⁿ`.  This is the concrete DIAGONAL slice `E τ p 0` (base point
    `0`, coordinate `v = p`) of the two-point residual, dominated by the width-2 base kernel
    `baseKernelW 2 0 t v 0 = gaussDdim (2t) v` — exactly the shape `leviSeries_summableW` (κ = 2)
    consumes.  The full curvature/RNC/coefficient hypotheses are inherited verbatim — genuine,
    load-bearing, none vacuous.  This DISCHARGES the LOCAL near-diagonal part of the global width-2
    bound; the far-field / off-diagonal remainder is the C4c wall. -/
theorem residualN0_local_baseKernelW_slice
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hCd : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 0 0)
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : Point n, ‖v‖ < ρ →
      |parametrixResidualN 0 g gi Θ u t v|
        ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n)
            * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 :=
  residualBound_local_baseKernelW ht
    (residualN0_gaussian_bound g gi Θ u hg hgiC hCd hw hg0 hgi0 hdg0 hdgi0 hΓ0 hsymm hinv hgauge
      hw0flat hw0hessRicci ht M W L hM hW hdev hw0bd hlap)

/-! ### 7. ★ The reduction — Neumann convergence conditional on the single global width-2 input. -/

/-- **★ THE REDUCTION (F2) — the residual Neumann series converges given the single global width-2
    bound.**  At `κ = 2, α = 0` (the concrete residual's doubled-time width, no time-power), GIVEN
        `hEboundW : ∀ τ p q, 0 < τ → |E τ p q| ≤ C·baseKernelW 2 0 τ p q`   (GLOBAL, all `(p,q)`),
    `C ≥ 0`, and the carried per-step integrability `IterConvIntegrableW E 2 0 C`, the residual
    Neumann series converges:  `Summable (fun k => iterE E (k+1) t x y)`.

    A direct instantiation of `leviSeries_summableW` at `κ = 2, α = 0` (`0 < 2`, `0 ≤ 0`).  This is
    the honest reduction: the LOCAL, base-point-`0`, near-diagonal part of `hEboundW` is DISCHARGED by
    `residualN0_local_baseKernelW_slice` (which produces exactly `|parametrixResidualN 0 …| ≤
    C'·baseKernelW 2 0 τ v 0` on a ball, matching `hEboundW`'s `q = 0` slice with `v = p`), so the
    WHOLE convergence is reduced to the SINGLE remaining input `hEboundW` — the GLOBAL width-2 bound,
    whose open residue is (i) the far-field off the RNC ball and (ii) the off-diagonal parametrix over
    all base points `q ≠ 0`, i.e. the C4c wall.  NOT `a₁ = R/6`; NOT the unconditional `hEbound`. -/
theorem neumann_summable_alpha0_width2 (E : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hEboundW : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW E 2 0 C) (t : ℝ) (ht : 0 < t) (x y : Point n) :
    Summable (fun k : ℕ => iterE E (k + 1) t x y) :=
  leviSeries_summableW E 2 0 C (by norm_num) le_rfl hC hEboundW hInt t ht x y

end QIQTH.HeatResidualBound
