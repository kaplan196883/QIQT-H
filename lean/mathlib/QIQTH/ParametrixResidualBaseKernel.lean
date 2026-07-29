/-
  ParametrixResidualBaseKernel — M6 wiring ASSESSMENT + connector: the adapter connecting the
  parametrix residual Gaussian bound (`residualN0_gaussian_bound`) to the Levi/Duhamel convergence
  machinery's `hEbound` input (`iterConv_bound`/`leviSeries_summable`/`trueHeatKernel`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THE CONVERGENCE MACHINERY CONSUMES (verbatim).

  `LeviSeries.iterConv_bound` / `leviSeries_summable` / `TrueHeatKernel` all take the one-step
  residual bound in the shape
      `hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernel α τ p q`,
  where `E : ℝ → Point n → Point n → ℝ` is a TWO-POINT space-time kernel and
      `baseKernel α τ p q = τ ^ α * gaussDdim τ (p − q)`      (`^` = `Real.rpow`)
  is the NARROW (width-`4τ`) normalized heat Gaussian `gaussDdim τ (p−q) = (√(4πτ))⁻ⁿ·exp(−r²/4τ)`,
  scaled by the residual-order time power `τ^α`.  The bound is demanded for ALL times `τ > 0` and ALL
  point pairs `(p,q)`.

  WHAT THE RESIDUAL BOUND SUPPLIES (verbatim, `ParametrixResidualN0Bound.residualN0_gaussian_bound`):
      `∀ᶠ v in 𝓝 0, |parametrixResidualN 0 g gi Θ u t v| ≤ C · gaussDdimWide t v`,
  with `gaussDdimWide t v = (√(4πt))⁻ⁿ·exp(−r²/8t)` the WIDE (width-`8t`) Gaussian — a bound at a
  SINGLE FIXED time `t`, in a SINGLE RNC coordinate `v` (base point = RNC centre `0`), valid only
  LOCALLY (`∀ᶠ v in 𝓝 0`, i.e. on some neighborhood of the diagonal).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE HONEST GAP (three genuine mismatches — this is NOT "one clean rescaling").

    (G1) GLOBAL vs LOCAL.  `hEbound` is `∀ p q` (all of space); the residual bound is `∀ᶠ v in 𝓝 0`
         (only near the diagonal).  The Levi iteration convolves over ALL `z`, so it needs the
         residual dominated on all of space, not just near the RNC centre.  THIS IS THE DEEP GAP.

    (G2) ALL-`τ` SAME-TIME vs FIXED-`t`.  `hEbound` quantifies every `τ > 0` with the `τ^α` power;
         the residual bound is at one fixed `t` with no explicit `τ`-power (residual order `α = 0`).

    (G3) WIDTH.  `gaussDdimWide t v = 2^{n/2}·gaussDdim (2t) v` (proved below,
         `gaussDdimWide_eq_scaled_gaussDdim`): the residual's dominating Gaussian is the base Gaussian
         at DOUBLE the time.  A wide Gaussian is NOT `≤ C·(same-time narrow gaussDdim)` — the ratio
         `gaussDdim(2t)/gaussDdim(t) = 2^{-n/2}·exp(+r²/8t) → ∞`.  The machinery's exact self-similar
         convolution identity (`TimeSimplexBeta.gaussTimePow_conv_beta`) is WIDTH-LOCKED to `gaussDdim`
         at the same time, so it cannot ingest a wider-Gaussian bound as-is.

  Consequently discharging `hEbound` from `residualN0_gaussian_bound` is NOT honestly reachable
  (F1 is NOT landed — doing so would require fabricating global/same-time/same-width facts the
  residual bound does not supply).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE LANDS — F2 (a genuine, TRUE connector) + F3 (precise assessment).

    • `baseKernel_zero_apply` — `baseKernel 0 τ p q = gaussDdim τ (p − q)` (the `τ^0 = 1` reduction).

    • `gaussDdimWide_eq_scaled_gaussDdim` — ★ THE WIDTH IDENTIFICATION (F2, G3 made precise):
          `gaussDdimWide t v = (√2)ⁿ · gaussDdim (2t) v`   (`0 < t`),
      i.e. the widened Gaussian IS the base Gaussian at doubled time, times `2^{n/2}`.  Proof:
      `√(4π(2t)) = √2·√(4πt)` (`Real.sqrt_mul`) folds the prefactor; the exponents `−r²/(4·2t)` and
      `−r²/8t` coincide.

    • `gaussDdimWide_eq_scaled_baseKernel` — the same, phrased against the machinery's `baseKernel`:
          `gaussDdimWide t v = (√2)ⁿ · baseKernel 0 (2t) v 0`.

    • `eventually_nhds_zero_ball` — the `∀ᶠ → explicit-radius` promotion (F2): a neighborhood-filter
      statement at `0` on `Point n` yields an explicit ball `∃ ρ>0, ∀ v, ‖v‖<ρ → …`.

    • `residualBound_local_baseKernel` — ★ THE CONNECTOR (F2): a LOCAL wide-Gaussian residual bound
      `∀ᶠ v, |R v| ≤ C·gaussDdimWide t v` yields an EXPLICIT-radius domination by the base kernel at
      DOUBLED time: `∃ ρ>0, ∀ v, ‖v‖<ρ → |R v| ≤ (C·(√2)ⁿ)·baseKernel 0 (2t) v 0`.  This is exactly
      the honest partial of `hEbound`: it exhibits the base-kernel domination but records the three
      residual gaps (local ball `‖v‖<ρ`; single fixed doubled time `2t`; base point `0`).

    • `residualN0_local_baseKernel_bound` — the connector applied to the ACTUAL parametrix residual
      `parametrixResidualN 0`, wiring `residualN0_gaussian_bound` into the base-kernel local
      domination `|parametrixResidualN 0 … t v| ≤ C'·baseKernel 0 (2t) v 0` on an explicit ball.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FLOOR.  F1 (full `hEbound` discharge) NOT landed — genuine structural gap (G1/G2/G3).
  LANDED = F2 (`gaussDdimWide ↔ baseKernel` width identity + `∀ᶠ→ball` promotion + the local
  base-kernel connector, generic and applied to the real residual) + F3 (this assessment).

  SMALLEST NEXT M6 BRICKS (to actually reach `hEbound`, in order of depth):
    1. a GLOBAL-in-space residual bound (extend the local RNC bound off the diagonal — cutoff /
       partition-of-unity / far-field Gaussian tail), closing G1;
    2. a WIDTH-TOLERANT (rescaled) Levi iteration: rebuild `TimeSimplexBeta`'s self-similar identity
       at a general Gaussian width so an `8t`-width bound iterates to a convergent series, closing G3;
    3. the general-`N` residual `|E| ≤ C·t^{N−d/2}·G_κ` bound to supply the positive `τ`-power `α>0`
       (and the all-`τ` quantifier), closing G2.

  M6 convergence is therefore NOT "a few wiring bricks": the residual↔convergence representation has a
  genuine local/width/two-point structural gap.  This file supplies the honest wiring that DOES hold
  and pins down exactly what remains.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hyps.
-/
import Mathlib
import QIQTH.ParametrixResidualN0Bound
import QIQTH.LeviSeries
import QIQTH.TrueHeatKernel

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.TimeSimplexBeta

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### 1. `baseKernel` at residual order `α = 0`. -/

/-- **The base kernel at order `α = 0`** is the plain narrow Gaussian: `baseKernel 0 τ p q =
    gaussDdim τ (p − q)` (`τ ^ (0:ℝ) = 1` by `Real.rpow_zero`). -/
theorem baseKernel_zero_apply (τ : ℝ) (p q : Point n) :
    baseKernel (0 : ℝ) τ p q = gaussDdim τ (p - q) := by
  simp only [baseKernel, Real.rpow_zero, one_mul]

/-! ### 2. The width identification `gaussDdimWide = 2^{n/2} · gaussDdim(2t)` (G3 made precise). -/

/-- **★ THE WIDTH IDENTIFICATION (F2).**  The widened Gaussian at time `t` equals the base (narrow)
    Gaussian at DOUBLED time `2t`, times `2^{n/2} = (√2)ⁿ`:
        `gaussDdimWide t v = (√2)ⁿ · gaussDdim (2·t) v`   (`0 < t`).
    This pins down the width gap G3: the residual's dominating Gaussian is `gaussDdim` at `2t`, NOT at
    the same time `t`, so it cannot be `≤ C·gaussDdim t` uniformly.  Proof: `√(4π·2t) = √2·√(4πt)`
    (`Real.sqrt_mul`) folds the prefactor `(√(4πt))⁻ⁿ = (√2)ⁿ·(√(4π·2t))⁻ⁿ`, and the exponents
    `−r²/(4·2t)` and `−r²/8t` coincide. -/
theorem gaussDdimWide_eq_scaled_gaussDdim {t : ℝ} (ht : 0 < t) (v : Point n) :
    gaussDdimWide t v = Real.sqrt 2 ^ n * gaussDdim (2 * t) v := by
  rw [gaussDdimWide, gaussDdim_eq_exp (2 * t) v]
  have hexp : -(rncRadialSq v) / (4 * (2 * t)) = -(rncRadialSq v) / (8 * t) := by ring
  rw [hexp]
  have hs2ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrt : Real.sqrt (4 * Real.pi * (2 * t))
      = Real.sqrt 2 * Real.sqrt (4 * Real.pi * t) := by
    rw [show 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) from by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hprefac : (Real.sqrt (4 * Real.pi * t))⁻¹
      = Real.sqrt 2 * (Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ := by
    rw [hsqrt, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs2ne, one_mul]
  rw [hprefac, mul_pow]
  ring

/-- **The width identification against `baseKernel`.**  `gaussDdimWide t v = (√2)ⁿ · baseKernel 0
    (2·t) v 0` (`0 < t`): the residual's dominating Gaussian is the machinery's base kernel (order
    `α = 0`) at doubled time `2t`, evaluated at `(p,q) = (v,0)` (so `p − q = v`), times `2^{n/2}`. -/
theorem gaussDdimWide_eq_scaled_baseKernel {t : ℝ} (ht : 0 < t) (v : Point n) :
    gaussDdimWide t v = Real.sqrt 2 ^ n * baseKernel (0 : ℝ) (2 * t) v 0 := by
  rw [gaussDdimWide_eq_scaled_gaussDdim ht v, baseKernel_zero_apply, sub_zero]

/-! ### 3. The `∀ᶠ → explicit ball` promotion (F2). -/

/-- **The neighborhood-filter → explicit-ball promotion.**  A property holding `∀ᶠ v in 𝓝 0` on
    `Point n = Fin n → ℝ` holds on an explicit norm ball: `∃ ρ > 0, ∀ v, ‖v‖ < ρ → P v`.  (Metric
    neighborhood basis at `0`, `dist v 0 = ‖v‖`.)  This converts the residual bound's `∀ᶠ v in 𝓝 0`
    into a concrete radius `ρ` — the quantitative form the convergence wiring can consume. -/
theorem eventually_nhds_zero_ball {P : Point n → Prop}
    (hP : ∀ᶠ v in nhds (0 : Point n), P v) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : Point n, ‖v‖ < ρ → P v := by
  rw [Metric.eventually_nhds_iff] at hP
  obtain ⟨ε, hε, hball⟩ := hP
  refine ⟨ε, hε, fun v hv => ?_⟩
  refine hball ?_
  rw [dist_eq_norm, sub_zero]
  exact hv

/-! ### 4. ★ THE CONNECTOR — a local wide-Gaussian residual bound ⟹ explicit-ball base-kernel
    domination (at doubled time). -/

/-- **★ THE CONNECTOR (F2).**  Given a LOCAL wide-Gaussian residual bound
        `∀ᶠ v in 𝓝 0, |R v| ≤ C · gaussDdimWide t v`   (`0 < t`),
    the residual is dominated on an EXPLICIT ball by the machinery's base kernel at DOUBLED time:
        `∃ ρ > 0, ∀ v, ‖v‖ < ρ → |R v| ≤ (C · (√2)ⁿ) · baseKernel 0 (2·t) v 0`.
    This is the honest partial of the convergence machinery's `hEbound`: it exhibits the base-kernel
    domination (`baseKernel 0 (2t) v 0`) but faithfully records the three residual gaps — the LOCAL
    ball `‖v‖ < ρ` (not `∀ p q`), the single FIXED DOUBLED time `2t` (not `∀ τ`), and the base point
    `0` (single RNC coordinate).  Route: `eventually_nhds_zero_ball` + `gaussDdimWide_eq_scaled_baseKernel`. -/
theorem residualBound_local_baseKernel {R : Point n → ℝ} {t C : ℝ} (ht : 0 < t)
    (hbd : ∀ᶠ v in nhds (0 : Point n), |R v| ≤ C * gaussDdimWide t v) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : Point n, ‖v‖ < ρ →
      |R v| ≤ (C * Real.sqrt 2 ^ n) * baseKernel (0 : ℝ) (2 * t) v 0 := by
  obtain ⟨ρ, hρ, hball⟩ := eventually_nhds_zero_ball hbd
  refine ⟨ρ, hρ, fun v hv => ?_⟩
  have hv' := hball v hv
  rw [gaussDdimWide_eq_scaled_baseKernel ht v] at hv'
  calc |R v| ≤ C * (Real.sqrt 2 ^ n * baseKernel (0 : ℝ) (2 * t) v 0) := hv'
    _ = (C * Real.sqrt 2 ^ n) * baseKernel (0 : ℝ) (2 * t) v 0 := by ring

/-! ### 5. The connector applied to the ACTUAL parametrix residual `parametrixResidualN 0`. -/

/-- **The connector on the real residual (F2).**  Feeding `residualN0_gaussian_bound` (the full `N=0`
    parametrix-residual wide-Gaussian bound) through `residualBound_local_baseKernel` yields an
    explicit-ball domination of the actual residual by the base kernel at doubled time:
        `∃ ρ > 0, ∀ v, ‖v‖ < ρ →
           |parametrixResidualN 0 g gi Θ u t v| ≤ C' · baseKernel 0 (2·t) v 0`,
    with `C' = (1 + 32·n²·M·W + L)·(√2)ⁿ`.  The full curvature/RNC/coefficient hypotheses are inherited
    verbatim from `residualN0_gaussian_bound` — genuine, load-bearing, none vacuous.  This is the
    concrete wiring of the parametrix residual into the machinery's `baseKernel`; the remaining gap to
    `hEbound` is exactly G1 (local `‖v‖<ρ` → global `∀ p q`), G2 (`t` doubled/fixed → `∀ τ`, `α>0`),
    and G3's width already resolved into the doubled time `2t`.  NOT a full `hEbound`, NOT `a₁ = R/6`. -/
theorem residualN0_local_baseKernel_bound
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
            * baseKernel (0 : ℝ) (2 * t) v 0 :=
  residualBound_local_baseKernel ht
    (residualN0_gaussian_bound g gi Θ u hg hgiC hCd hw hg0 hgi0 hdg0 hdgi0 hΓ0 hsymm hinv hgauge
      hw0flat hw0hessRicci ht M W L hM hW hdev hw0bd hlap)

end QIQTH.HeatResidualBound
