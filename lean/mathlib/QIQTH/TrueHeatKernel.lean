/-
  TrueHeatKernel — Phase C6 (the CONDITIONAL CAPSTONE) of the convergence-infrastructure campaign
  (docs/qg_roadmap/CONVERGENCE_INFRASTRUCTURE_PLAN.md).

  The convergence machinery (C1–C5c) is COMPLETE:
    • `HeatDuhamel.duhamel_principle` — the Duhamel identity `(∂_t − Δ_x)(A * B) = B` for a fundamental
      solution `A`, reduced to its four analytic ingredients (carried);
    • `LeviSeries.leviSeries_summable` — the actual residual Neumann series `Σ E^{*k}` CONVERGES.

  This file ASSEMBLES the true heat kernel from the parametrix `H` and the Levi series `F`, and proves
  it solves the heat equation — the "parametrix method works" entailment — via the BUILT
  `duhamel_principle`.  It is a CONDITIONAL theorem: it carries the residual/Volterra facts as
  EXPLICIT, non-vacuous hypotheses (the residual bound itself is C4, which reduces to the off-diagonal
  parametrix — a separate wall).

  WHAT LANDS HERE.

    • `heatOp g gi K t x y := (∂_t − Δ_{g,x}) K` — the spatial heat operator on a kernel;
      `heatOp_add` — its linearity in the kernel (from `deriv_add` + `laplaceBeltrami_add`).

    • `leviSeries E t x y := ∑' k, (−1)^(k+1) · iterE E (k+1) t x y` — the SIGNED Levi/Neumann series
      `Σ (−E)^{*k}` (the alternating sign is REQUIRED by the Volterra identity `F = −E − E*F`; the
      naive positive series `Σ E^{*k}` satisfies `F = E + E*F`, the WRONG sign for the cancellation
      `(∂_t−Δ)(H + H*F) = 0`).

    • `trueHeatKernel H F t x y := H t x y + heatConv H F t x y` — the true kernel `K = H + H*F`.

    • `trueHeatKernel_heat_eqn` — ★ THE DELIVERABLE (conditional): the true kernel solves the heat
      equation `(∂_t − Δ)K = 0`, GIVEN
        - `hE`       — `(∂_t−Δ)H = E` (the parametrix residual);
        - `hDuhamel` — `(∂_t−Δ)(H*F) = F + E*F` (the `duhamel_principle` output for `H*F`);
        - `hVolterra`— `F = −E − E*F` (the Volterra identity the signed Levi series satisfies);
      plus the genuine linearity/regularity side conditions `heatOp_add` needs (t-differentiability of
      each summand, C^∞ in x of each summand).  PURE ALGEBRA on `heatOp`-linearity once the hypotheses
      are in.

    • `leviSeries_volterra` — the REACH: DERIVES `hVolterra` for `leviSeries E`, GIVEN the tsum/heatConv
      interchange `hInter : heatConv E (Σ) = Σ heatConv E (·)` (the sole genuinely-Mathlib-missing
      analytic carry — Summable-continuity of `heatConv` under `tsum`) and summability of the signed
      series.  Everything else (first-term split, `iterE_succ` index shift, sign algebra) is proved.

  ⚠ HONEST SCOPE.  This is the CONDITIONAL capstone: "convergence machinery + residual/Volterra facts
  ⟹ the true kernel solves the heat equation."  It does NOT claim the true kernel exists
  unconditionally, nor `a₁ = R/6` unconditionally — the residual bound (C4) + the diagonal-expansion
  extraction remain, and C4 reduces to the off-diagonal parametrix (a separate wall).  No axioms
  beyond the standard three, no `sorry`.
-/
import Mathlib
import QIQTH.HeatDuhamel
import QIQTH.LeviSeries

open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.LeviSeries MeasureTheory
open scoped Interval

namespace QIQTH.TrueHeatKernel

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-! ### 1. The spatial heat operator on a kernel and its linearity. -/

/-- **The spatial heat operator** `(∂_t − Δ_{g,x}) K` acting on a space-time kernel
    `K : ℝ → Point n → Point n → ℝ`, evaluated at `(t, x, y)`:
    `heatOp g gi K t x y = deriv (fun u => K u x y) t − laplaceBeltrami g gi (fun p => K t p y) x`. -/
noncomputable def heatOp (g gi : Point n → Fin n → Fin n → ℝ) (K : ℝ → Point n → Point n → ℝ)
    (t : ℝ) (x y : Point n) : ℝ :=
  deriv (fun u => K u x y) t - laplaceBeltrami g gi (fun p => K t p y) x

/-- **Linearity of the heat operator in the kernel.**  For kernels `K₁ K₂` whose scalar sections are
    `t`-differentiable at `t` and `C^∞` in `x` at `x`, `heatOp` of the (kernel) sum splits:
        `heatOp g gi (K₁ + K₂) = heatOp g gi K₁ + heatOp g gi K₂`.
    (`deriv_add` on the `∂_t` piece; `laplaceBeltrami_add` on the `Δ_x` piece; `ring` for the
    subtraction rearrangement.)  The side conditions are genuine (they fail for non-differentiable /
    non-`C²` kernels), none is the conclusion. -/
theorem heatOp_add (g gi : Point n → Fin n → Fin n → ℝ) (K₁ K₂ : ℝ → Point n → Point n → ℝ)
    (t : ℝ) (x y : Point n)
    (hD₁ : DifferentiableAt ℝ (fun u => K₁ u x y) t)
    (hD₂ : DifferentiableAt ℝ (fun u => K₂ u x y) t)
    (hC₁ : ContDiff ℝ ⊤ (fun p => K₁ t p y))
    (hC₂ : ContDiff ℝ ⊤ (fun p => K₂ t p y)) :
    heatOp g gi (fun τ p q => K₁ τ p q + K₂ τ p q) t x y
      = heatOp g gi K₁ t x y + heatOp g gi K₂ t x y := by
  simp only [heatOp]
  have hderiv : deriv (fun u => K₁ u x y + K₂ u x y) t
      = deriv (fun u => K₁ u x y) t + deriv (fun u => K₂ u x y) t := deriv_add hD₁ hD₂
  have hlap : laplaceBeltrami g gi (fun p => K₁ t p y + K₂ t p y) x
      = laplaceBeltrami g gi (fun p => K₁ t p y) x
        + laplaceBeltrami g gi (fun p => K₂ t p y) x :=
    laplaceBeltrami_add g gi (fun p => K₁ t p y) (fun p => K₂ t p y) x hC₁ hC₂
  rw [hderiv, hlap]; ring

/-! ### 2. The signed Levi series and the true heat kernel. -/

/-- **The signed Levi/Neumann series** `F = Σ_{k≥0} (−1)^(k+1) E^{*(k+1)} = −E + E*E − E*E*E + ⋯`,
    i.e. `Σ (−E)^{*k}` shifted to start at `k=1`.  This is the `F` satisfying the Volterra identity
    `F = −E − E*F` (see `leviSeries_volterra`); the alternating sign is essential.  The `tsum` is
    well-defined (equals the genuine sum) exactly where the series is summable — carried where used;
    `tsum` returns `0` otherwise. -/
noncomputable def leviSeries (E : ℝ → Point n → Point n → ℝ) : ℝ → Point n → Point n → ℝ :=
  fun t x y => ∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t x y

/-- **The true heat kernel** `K = H + H*F` (parametrix `H` corrected by the Duhamel convolution with
    the Levi series `F`). -/
noncomputable def trueHeatKernel (H F : ℝ → Point n → Point n → ℝ) : ℝ → Point n → Point n → ℝ :=
  fun t x y => H t x y + heatConv H F t x y

@[simp] theorem trueHeatKernel_apply (H F : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n) :
    trueHeatKernel H F t x y = H t x y + heatConv H F t x y := rfl

/-! ### 3. ★ THE DELIVERABLE — the conditional true-kernel heat equation. -/

/-- **★ THE C6 DELIVERABLE (conditional) — the parametrix method works.**  The true kernel
    `K = H + H*F` solves the homogeneous heat equation `(∂_t − Δ_{g,x})K = 0`, GIVEN the three genuine
    residual/Volterra facts and the linearity side conditions:

    * `hE`        — `(∂_t−Δ)H = E`, i.e. `E` IS the parametrix residual;
    * `hDuhamel`  — `(∂_t−Δ)(H*F) = F + E*F`, the Duhamel-principle output for `H*F` (this is what
      `HeatDuhamel.duhamel_principle` yields when `H` is a fundamental solution up to residual `E`);
    * `hVolterra` — `F = −E − E*F`, the Volterra identity the signed Levi series satisfies
      (`leviSeries_volterra`);
    * `hDH`,`hDConv`,`hCH`,`hCConv` — the `t`-differentiability and `C^∞`-in-`x` of the two summands
      `H` and `H*F` (needed for `heatOp_add`).

    Proof (pure algebra): `heatOp K = heatOp H + heatOp (H*F) = E + (F + E*F)`, and by `hVolterra`,
    `F = −E − E*F`, so this `= E + ((−E − E*F) + E*F) = 0`.

    ⚠ CONDITIONAL: `hE`, `hDuhamel`, `hVolterra` all hold for the true parametrix + signed Levi
    construction, but the residual bound behind them (C4) reduces to the off-diagonal parametrix — a
    separate wall.  This does NOT assert `a₁ = R/6` unconditionally, nor that the true kernel exists
    unconditionally. -/
theorem trueHeatKernel_heat_eqn (g gi : Point n → Fin n → Fin n → ℝ)
    (H E F : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hE : heatOp g gi H t x y = E t x y)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H F u p q) t x y
        = F t x y + heatConv E F t x y)
    (hVolterra : F t x y = - E t x y - heatConv E F t x y)
    (hDH : DifferentiableAt ℝ (fun u => H u x y) t)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H F u x y) t)
    (hCH : ContDiff ℝ ⊤ (fun p => H t p y))
    (hCConv : ContDiff ℝ ⊤ (fun p => heatConv H F t p y)) :
    heatOp g gi (trueHeatKernel H F) t x y = 0 := by
  -- `trueHeatKernel H F = H + (H*F)` as kernels; split `heatOp` by linearity.
  have hsplit : heatOp g gi (trueHeatKernel H F) t x y
      = heatOp g gi H t x y + heatOp g gi (fun u p q => heatConv H F u p q) t x y := by
    have := heatOp_add g gi H (fun u p q => heatConv H F u p q) t x y hDH hDConv hCH hCConv
    -- `trueHeatKernel H F` is definitionally `fun τ p q => H τ p q + heatConv H F τ p q`.
    exact this
  rw [hsplit, hE, hDuhamel, hVolterra]; ring

/-! ### 4. The Volterra identity for the signed Levi series (the REACH). -/

/-- **★ THE REACH — the Volterra identity for the signed Levi series.**  The signed Levi series
    `F = leviSeries E = Σ (−1)^(k+1) E^{*(k+1)}` satisfies the Volterra equation
        `F = −E − E*F`   (i.e. the `hVolterra` of `trueHeatKernel_heat_eqn`),
    GIVEN two genuine, non-vacuous analytic carries:

    * `hSum`   — summability of the signed series at `(t,x,y)` (holds by the C5c comparison bound
      `|iterE E k| ≤ C^k · iterKernel`, since `|(−1)^(k+1)·iterE| = |iterE|`; carried here to keep this
      identity independent of the residual-bound baggage);
    * `hInter` — the **tsum/heatConv interchange** `heatConv E (Σ) = Σ heatConv E (·)`, moving the
      space-time convolution `heatConv E (·)` through the infinite sum.  This is the SOLE
      genuinely-Mathlib-missing analytic input: it is the Summable-continuity of `heatConv` under
      `tsum` (dominated convergence / integrability of the summed integrand), which Mathlib lacks
      cleanly for the interval×Lebesgue convolution.  Non-vacuous (it fails without the summed
      integrand's integrability) and NOT the conclusion.

    Everything else is proved: split off the `k=0` term (`Summable.tsum_eq_zero_add`) giving `−E`; the
    tail reindexes by `iterE_succ` (`E^{*(k+2)} = E * E^{*(k+1)}`), the constant `(−1)^(k+1)` pulls
    through `heatConv` (`heatConv_smul_right`, unconditional), and the sign `(−1)^(k+2) = −(−1)^(k+1)`
    folds the tail into `−heatConv E F`.

    This CONVERTS the carried `hVolterra` of the capstone into the single carried interchange
    `hInter` — strictly more informative.  Still CONDITIONAL; NOT `a₁ = R/6`. -/
theorem leviSeries_volterra (E : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hSum : Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t x y))
    (hInter : heatConv E (leviSeries E) t x y
        = ∑' k : ℕ, heatConv E (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q) t x y) :
    leviSeries E t x y = - E t x y - heatConv E (leviSeries E) t x y := by
  -- Split off the `k = 0` term.
  have hsplit : (∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t x y)
      = ((-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) t x y)
        + ∑' k : ℕ, (-1 : ℝ) ^ (k + 1 + 1) * iterE E (k + 1 + 1) t x y :=
    hSum.tsum_eq_zero_add
  -- The head term is `−E`.
  have hhead : (-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) t x y = - E t x y := by
    rw [show iterE E (0 + 1) = E from iterE_one E]; ring
  -- The tail equals `−heatConv E F`.
  have htail : (∑' k : ℕ, (-1 : ℝ) ^ (k + 1 + 1) * iterE E (k + 1 + 1) t x y)
      = - heatConv E (leviSeries E) t x y := by
    rw [hInter, ← tsum_neg]
    refine tsum_congr (fun k => ?_)
    rw [heatConv_smul_right ((-1 : ℝ) ^ (k + 1)) E (iterE E (k + 1))]
    rw [show iterE E (k + 1 + 1) = heatConvK E (iterE E (k + 1)) from iterE_succ E (by omega)]
    simp only [heatConvK_apply]
    ring
  -- Assemble (LHS `leviSeries E t x y` is defeq the tsum).
  show (∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t x y) = _
  rw [hsplit, hhead, htail]; ring

/-! ### 5. The capstone with the Volterra fact discharged into the interchange. -/

/-- **The C6 capstone with `hVolterra` DISCHARGED** into the tsum/heatConv interchange.  Plugs
    `leviSeries_volterra` into `trueHeatKernel_heat_eqn` (with `F = leviSeries E`), so the true kernel
    `K = H + H*(leviSeries E)` solves the heat equation `(∂_t − Δ)K = 0` given `hE`, `hDuhamel`, the
    linearity side conditions, and the two analytic carries `hSum`/`hInter` of `leviSeries_volterra`
    (in place of `hVolterra`).  Same honest scope: CONDITIONAL, NOT `a₁ = R/6`, NOT unconditional
    existence. -/
theorem trueHeatKernel_heat_eqn_levi (g gi : Point n → Fin n → Fin n → ℝ)
    (H E : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hE : heatOp g gi H t x y = E t x y)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries E) u p q) t x y
        = leviSeries E t x y + heatConv E (leviSeries E) t x y)
    (hSum : Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t x y))
    (hInter : heatConv E (leviSeries E) t x y
        = ∑' k : ℕ, heatConv E (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q) t x y)
    (hDH : DifferentiableAt ℝ (fun u => H u x y) t)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries E) u x y) t)
    (hCH : ContDiff ℝ ⊤ (fun p => H t p y))
    (hCConv : ContDiff ℝ ⊤ (fun p => heatConv H (leviSeries E) t p y)) :
    heatOp g gi (trueHeatKernel H (leviSeries E)) t x y = 0 :=
  trueHeatKernel_heat_eqn g gi H E (leviSeries E) t x y hE hDuhamel
    (leviSeries_volterra E t x y hSum hInter) hDH hDConv hCH hCConv

end QIQTH.TrueHeatKernel
