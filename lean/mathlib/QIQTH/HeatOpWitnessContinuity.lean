/-
  HeatOpWitnessContinuity — J4-283: the (R-base) heat-operator-residual JOINT `(τ,z)`-continuity and
  the (R-dom) per-level Gaussian integrand dominations feeding the `QIQTH.IterEContinuity` (J4-282)
  parametric-continuity engines and the `QIQTH.MovingCorrAssembly` (J4-281) Levi M-test.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  parametric-continuity / domination (regularity) brick.  No `sorry` (header prose excepted), no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited.

  ── WHAT THE `iterE` ENGINE (`IterEContinuity.iterE_jointContinuousOn`) NEEDS.
     Two named residuals feed its ALL-`k` induction skeleton at `E := heatOp g gi Wit` (the Levi
     residual = one heat operator `∂_τ − Δ_z` past the gated van-Vleck witness kernel):
       (R-base) the BASE `hbase`:
           `ContinuousOn (fun p => E p.1 p.2 0) (Icc t₁ t₂ ×ˢ closedBall 0 R)`,   `0 < t₁`,
         i.e. the joint `(τ,z)`-continuity of `heatOp g gi Wit` at positive times;
       (R-dom) the per-level Gaussian-integrable dominations feeding the OUTER/INNER engines'
         `hbound`/`hbnd_int`/`hmeas`/`hcont` slots.

  ── (R-base) — THE ROUTE (identity-congruence, mission-preferred).  On a compact SITTING INSIDE THE
     GATE at positive times, the concrete kernel's hard set-gate is transparent and the parametrix
     residual `heatOp g gi Wit` EQUALS an EXPLICIT residual formula `F` (the CoeffU1Fix `htransport`
     identity / the `parametrixResidualN = deriv − laplaceBeltrami` normal form of
     `ErrorKernelFactorization`).  `F` is built from `gaussDdim`, chart jets and DeWitt coefficients —
     all banked-continuous away from `τ = 0`.  So `ContinuousOn.congr` transfers `F`'s joint
     continuity onto `heatOp g gi Wit` on the compact.  This mirrors EXACTLY the
     `KernelJointContinuity.kernelGated_jointContinuousOn_inGate` pattern (which congr-transfers the
     ungated base kernel onto the gated one in-gate).  The compact is at `τ ≥ t₁ > 0`, so there is NO
     `τ → 0` Gaussian blow-up.

  ── (R-dom) — THE ROUTE (banked one-step + iterated Gaussian bounds).  From the banked width-`κ`
     one-step residual bound `|E τ p q| ≤ C·baseKernelW κ 0 τ p q` and the banked iterated bound
     `|iterE E k s w y| ≤ C^k·iterKernelW κ 0 k s w y` (`ParametrixHEboundWiring.iterConvW_bound`,
     `t > 0`), the CONVOLUTION-STEP integrand `E(s₁) z w · iterE E k s₂ w 0` is dominated pointwise
     (in `w`) by `(C·gaussDdim(κ·s₁)(z−w))·(C^k·iterKernelW κ 0 k s₂ w 0)` — the concrete
     Gaussian×model product that the INNER engine's `w`-domination slot (`hbound`) consumes after the
     `σ = s·u` rescale (`s₁ = s − s·u`, `s₂ = s·u`, both `> 0` on the compact `t₁ > 0`).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * `heatOpWitness_jointContinuousOn_of_identity` — ★★ (R-base) THE REDUCTION.  Joint `ContinuousOn`
      of `p ↦ heatOp g gi Wit p.1 p.2 0` on `Icc t₁ t₂ ×ˢ closedBall 0 R`, from (a) the gate-local
      residual identity `heatOp g gi Wit = F` ON THE COMPACT and (b) `F`'s joint continuity.  Both are
      genuine, separable facts (a geometric identity + an explicit-formula continuity); neither is the
      conclusion.  One-line `ContinuousOn.congr`.

    * `parametrixResidualN_jointContinuousOn_of_parts` — ★ (R-base) the EXPLICIT-FORMULA CONTINUITY
      brick.  Joint `ContinuousOn` of the explicit residual `p ↦ parametrixResidualN N g gi Θ u p.1 p.2`
      from the joint continuity of its two constituent pieces — the `∂_τ` term
      `p ↦ deriv (fun s => heatParametrix N Θ u s p.2) p.1` and the `Δ_z` term
      `p ↦ laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2`.  Route: `parametrixResidualN` unfolds
      to their difference; `ContinuousOn.sub`.  This is the honest decomposition of `F`'s continuity
      into the derivative-term and Laplacian-term subproblems (the genuine remaining analytic work).

    * `iterE_jointContinuousOn_of_heatOpWitness` — ★ (COMPOSE) the ALL-`k` termwise joint continuity of
      `iterE (heatOp g gi Wit)` on the compact, obtained by feeding the (R-base) output as `hbase` into
      `IterEContinuity.iterE_jointContinuousOn` together with a per-level STEP provider `hstep` (the
      (R-dom)-dischargeable convolution step).  This is the exact `hterm` feed (modulo the harmless
      `(−1)^(k+1)` scalar) of `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise`.

    * `convStepIntegrand_pointwise_bound` — ★ (R-dom) THE POINTWISE INTEGRAND DOMINATION (model form).
      `|E s₁ z w · iterE E k s₂ w 0| ≤ (C·baseKernelW κ 0 s₁ z w)·(C^k·iterKernelW κ 0 k s₂ w 0)` from
      the banked one-step bound at `s₁` and the banked iterated bound at `s₂`.  Route: `abs_mul` +
      `mul_le_mul`.  This is the `w`-integrand dominator the INNER engine's `hbound` slot consumes.

    * `convStepIntegrand_pointwise_bound_gauss` — ★ (R-dom) the same bound with the `α = 0` base kernel
      spelled as the plain Gaussian `C·gaussDdim(κ·s₁)(z−w)` (via `baseKernelW_zero_apply`), the exact
      Gaussian shape `continuousOn_of_dominated`'s integrable-envelope construction ingests.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
     (R-base) leaves TWO carried inputs, both genuine and non-vacuous:
       • the gate-local identity `heatOp g gi Wit = F` on the compact (the CoeffU1Fix `htransport` /
         `parametrixResidualN` normal form, valid in-gate at `τ > 0`; carried as `hIdent`), and
       • `F`'s joint continuity — reduced by `parametrixResidualN_jointContinuousOn_of_parts` to the
         `∂_τ`-term and `Δ_z`-term joint continuities (the derivative/Laplacian-of-`heatParametrix`
         continuity, a genuine further brick; carried as `hDcont`/`hLcont`).
     (R-dom) LANDS the pointwise `w`-integrand domination; the remaining map is the INTEGRAL-ENVELOPE
       construction — integrate the pointwise bound over `w` to a function of `(s,u)`, bound it
       uniformly over `z ∈ closedBall 0 R`, and check its `u`-integrability on `Ioc 0 1` — feeding the
       engine's `hbnd_int`/`hmeas` slots.  That convolution-integral estimate is the honest remainder;
       it is NOT attempted here (it is a separate integration brick, not a continuity fact).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.IterEContinuity
import QIQTH.ParametrixHEboundWiring
import QIQTH.KernelJointContinuity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.HeatParametrixAnsatz QIQTH.LaplaceBeltrami
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open scoped Topology

namespace QIQTH.HeatOpWitnessContinuity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (R-base) — the heat-operator-residual JOINT continuity via gate-local identity.
    ############################################################################### -/

/-- **★★ (R-base) `heatOpWitness_jointContinuousOn_of_identity` — THE REDUCTION.**  Joint
    `ContinuousOn` of the Levi residual `p ↦ heatOp g gi Wit p.1 p.2 0` on the positive-time compact
    `Icc t₁ t₂ ×ˢ closedBall 0 R`, from the two genuine, separable inputs:
      (a) `hIdent` — the gate-local residual identity `heatOp g gi Wit p.1 p.2 0 = F p.1 p.2` holding
          ON THE COMPACT (the `CoeffU1Fix.htransport` / `parametrixResidualN` normal form, valid
          in-gate at `τ > 0`; satisfiable — flat/in-gate case);
      (b) `hFcont` — the joint continuity of the EXPLICIT residual formula `F`
          (dischargeable by `parametrixResidualN_jointContinuousOn_of_parts`).
    Route: `ContinuousOn.congr`.  This mirrors exactly
    `KernelJointContinuity.kernelGated_jointContinuousOn_inGate` (congr-transfer in-gate).  Neither
    hypothesis is the conclusion (a pointwise algebraic identity + a DIFFERENT explicit function's
    continuity).  NOT `a₁ = R/6`. -/
theorem heatOpWitness_jointContinuousOn_of_identity
    (g gi : Point n → Fin n → Fin n → ℝ) (Wit : ℝ → Point n → Point n → ℝ)
    (F : ℝ → Point n → ℝ) (t₁ t₂ R : ℝ)
    (hIdent : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      heatOp g gi Wit p.1 p.2 0 = F p.1 p.2)
    (hFcont : ContinuousOn (fun p : ℝ × Point n => F p.1 p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => heatOp g gi Wit p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  hFcont.congr hIdent

/-- **★ (R-base) `parametrixResidualN_jointContinuousOn_of_parts` — the EXPLICIT-FORMULA continuity.**
    Joint `ContinuousOn` of the explicit residual `p ↦ parametrixResidualN N g gi Θ u p.1 p.2` on any
    set `s`, from the joint continuity of its two constituent terms:
      • `hDcont` — the `∂_τ` term `p ↦ deriv (fun sc => heatParametrix N Θ u sc p.2) p.1`;
      • `hLcont` — the `Δ_z` term `p ↦ laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2`.
    Route: `parametrixResidualN` is definitionally their difference, then `ContinuousOn.sub`.  This is
    the honest decomposition of the explicit-formula continuity `hFcont` (with `F = parametrixResidualN
    N g gi Θ u`) into the derivative-term and Laplacian-term subproblems — the genuine remaining
    analytic work of (R-base).  Neither carried piece is the conclusion.  NOT `a₁ = R/6`. -/
theorem parametrixResidualN_jointContinuousOn_of_parts
    (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (s : Set (ℝ × Point n))
    (hDcont : ContinuousOn
      (fun p : ℝ × Point n => deriv (fun sc => heatParametrix N Θ u sc p.2) p.1) s)
    (hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2) s) :
    ContinuousOn (fun p : ℝ × Point n => parametrixResidualN N g gi Θ u p.1 p.2) s := by
  have hEq : (fun p : ℝ × Point n => parametrixResidualN N g gi Θ u p.1 p.2)
      = fun p : ℝ × Point n =>
          deriv (fun sc => heatParametrix N Θ u sc p.2) p.1
            - laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2 := by
    funext p; rw [parametrixResidualN]
  rw [hEq]
  exact hDcont.sub hLcont

/-! ###############################################################################
    ## (COMPOSE) — feed (R-base) into the `iterE` ALL-`k` packaging.
    ############################################################################### -/

/-- **★ (COMPOSE) `iterE_jointContinuousOn_of_heatOpWitness`.**  The ALL-`k` termwise joint continuity
    of the iterated residual `p ↦ iterE (heatOp g gi Wit) (k+1) p.1 p.2 0` on the positive-time compact
    `Icc t₁ t₂ ×ˢ closedBall 0 R`, obtained by feeding the (R-base) output
    (`heatOpWitness_jointContinuousOn_of_identity`) as the BASE `hbase` of
    `IterEContinuity.iterE_jointContinuousOn`, together with a per-level STEP provider `hstep` (each
    rung dischargeable by `IterEContinuity.iterE_succ_jointContinuousOn_of_dominated` with the (R-dom)
    dominations).  This `∀ k` output is EXACTLY the `hterm` feed (modulo the harmless `(−1)^(k+1)`
    scalar, a `ContinuousOn.const_smul`) of
    `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise`.  Carried hypotheses (`hIdent`,
    `hFcont`, `hstep`) are all genuine and non-vacuous; none is the `∀ k` conclusion.  NOT
    `a₁ = R/6`. -/
theorem iterE_jointContinuousOn_of_heatOpWitness
    (g gi : Point n → Fin n → Fin n → ℝ) (Wit : ℝ → Point n → Point n → ℝ)
    (F : ℝ → Point n → ℝ) (t₁ t₂ R : ℝ)
    (hIdent : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      heatOp g gi Wit p.1 p.2 0 = F p.1 p.2)
    (hFcont : ContinuousOn (fun p : ℝ × Point n => F p.1 p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hstep : ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE (heatOp g gi Wit) (k + 1) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)
      → ContinuousOn (fun p : ℝ × Point n => iterE (heatOp g gi Wit) (k + 2) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × Point n => iterE (heatOp g gi Wit) (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  QIQTH.IterEContinuity.iterE_jointContinuousOn (heatOp g gi Wit) t₁ t₂ R
    (heatOpWitness_jointContinuousOn_of_identity g gi Wit F t₁ t₂ R hIdent hFcont) hstep

/-! ###############################################################################
    ## (R-dom) — the per-level pointwise Gaussian integrand dominations.
    ############################################################################### -/

/-- **★ (R-dom) `convStepIntegrand_pointwise_bound` — the pointwise integrand domination (model form).**
    For the convolution-step integrand `E s₁ z w · iterE E k s₂ w 0`, from the banked width-`κ` one-step
    residual bound at `s₁` (`hE`) and the banked iterated bound at `s₂` (`hIter`,
    `ParametrixHEboundWiring.iterConvW_bound`), plus the nonnegativity of the majorant one-step factor
    (`hbase0`):
        `|E s₁ z w · iterE E k s₂ w 0| ≤ (C·baseKernelW κ 0 s₁ z w)·(C^k·iterKernelW κ 0 k s₂ w 0)`.
    Route: `abs_mul` + `mul_le_mul`.  This is the `w`-integrand dominator the INNER engine's `hbound`
    slot consumes (with `s₁ = s − s·u`, `s₂ = s·u` after the `σ = s·u` rescale).  Carried hypotheses
    are the banked bounds and a nonnegativity — none is the conclusion.  NOT `a₁ = R/6`. -/
theorem convStepIntegrand_pointwise_bound
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (k : ℕ) (s₁ s₂ : ℝ) (z w : Point n)
    (hE : |E s₁ z w| ≤ C * baseKernelW κ 0 s₁ z w)
    (hIter : |iterE E k s₂ w 0| ≤ C ^ k * iterKernelW κ 0 k s₂ w 0)
    (hbase0 : 0 ≤ C * baseKernelW κ 0 s₁ z w) :
    |E s₁ z w * iterE E k s₂ w 0|
      ≤ (C * baseKernelW κ 0 s₁ z w) * (C ^ k * iterKernelW κ 0 k s₂ w 0) := by
  rw [abs_mul]
  exact mul_le_mul hE hIter (abs_nonneg _) hbase0

/-- **★ (R-dom) `convStepIntegrand_pointwise_bound_gauss` — the Gaussian-spelled integrand domination.**
    The same `w`-integrand bound as `convStepIntegrand_pointwise_bound`, with the `α = 0` base kernel
    written as the plain width-`κ` Gaussian `C·gaussDdim(κ·s₁)(z−w)` (`baseKernelW_zero_apply`):
        `|E s₁ z w · iterE E k s₂ w 0| ≤ (C·gaussDdim(κ·s₁)(z−w))·(C^k·iterKernelW κ 0 k s₂ w 0)`.
    This is the EXACT Gaussian shape the integral-envelope construction (`continuousOn_of_dominated`'s
    `hbnd_int` slot) ingests.  NOT `a₁ = R/6`. -/
theorem convStepIntegrand_pointwise_bound_gauss
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (k : ℕ) (s₁ s₂ : ℝ) (z w : Point n)
    (hE : |E s₁ z w| ≤ C * gaussDdim (κ * s₁) (z - w))
    (hIter : |iterE E k s₂ w 0| ≤ C ^ k * iterKernelW κ 0 k s₂ w 0)
    (hbase0 : 0 ≤ C * gaussDdim (κ * s₁) (z - w)) :
    |E s₁ z w * iterE E k s₂ w 0|
      ≤ (C * gaussDdim (κ * s₁) (z - w)) * (C ^ k * iterKernelW κ 0 k s₂ w 0) := by
  rw [abs_mul]
  exact mul_le_mul hE hIter (abs_nonneg _) hbase0

#check @heatOpWitness_jointContinuousOn_of_identity
#check @parametrixResidualN_jointContinuousOn_of_parts
#check @iterE_jointContinuousOn_of_heatOpWitness
#check @convStepIntegrand_pointwise_bound
#check @convStepIntegrand_pointwise_bound_gauss

end QIQTH.HeatOpWitnessContinuity

/-! ## Axiom checks — every theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HeatOpWitnessContinuity
#print axioms heatOpWitness_jointContinuousOn_of_identity
#print axioms parametrixResidualN_jointContinuousOn_of_parts
#print axioms iterE_jointContinuousOn_of_heatOpWitness
#print axioms convStepIntegrand_pointwise_bound
#print axioms convStepIntegrand_pointwise_bound_gauss
end AxiomChecks
