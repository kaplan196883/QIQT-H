/-
  RecenterReduction — the C4c-recenter (all-base-point / `q ≠ 0`) ABSTRACT REDUCTION: the honest
  repackaging that converts the abstract width-2 target `hEboundW` into the transparent
  per-base-point Gaussian form, precisely isolating the remaining wall to "the base-0 residual
  slice, made uniform in the base point `q`."

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DELIVERS (and, honestly, what it does NOT).

  The single remaining input to the M6 true-kernel Neumann convergence — hence to the conditional
  `a₁ = R/6` capstone `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` — is the GLOBAL width-2 one-step
  residual bound
      `hEboundW : ∀ τ p q, 0 < τ → |E τ p q| ≤ C · baseKernelW 2 0 τ p q`.
  The width-kernel wrapper `baseKernelW 2 0 τ p q` (= `τ^0 · gaussDdim (2τ) (p−q)`) hides, behind its
  `κ = 2, α = 0` indices, that the bound is nothing more than a per-base-point width-2 Gaussian in the
  coordinate difference `p − q`.  `baseKernelW_zero_apply` (ParametrixHEboundWiring.lean) makes this
  EXACT: `baseKernelW 2 0 τ p q = gaussDdim (2τ) (p − q)`.

  This file records the resulting EQUIVALENCE:
      `hEboundW`  ⟺  `∀ q τ, 0 < τ → ∀ p, |E τ p q| ≤ C · gaussDdim (2τ) (p − q)`,
  i.e. the abstract width-2 target IS EXACTLY the family, over ALL base points `q`, of the same-shape
  width-2 Gaussian residual bounds.  No content is added or lost (both directions proved).

  WHY THIS IS THE HONEST ISOLATION OF THE WALL.  The `q = 0` member of the right-hand family is the
  concrete DIAGONAL parametrix residual bound: its near-diagonal part is already PROVED
  (`HeatResidualBound.residualN0_local_baseKernelW_slice`, on an explicit ball, `q = 0`, `v = p`), and
  the diagonal-chart cutoff assembly `HeatResidualBound.cutoffResidual_diag_hEboundW` extends it to a
  global width-2 bound for the concrete cutoff parametrix at base point `0`.  After this reduction the
  ENTIRE remaining obstruction to `hEboundW` — and thereby to unconditional `a₁ = R/6` — is precisely:
      MAKE THE BASE-0 RESIDUAL BOUND UNIFORM IN THE BASE POINT `q`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ STEP-1 REACHABILITY FINDING (binding, honest).  Landing a GENUINE geometric recenter (Option A —
  per-`q` instances of `cutoffResidual_diag_hEboundW`) is NOT reachable from current machinery, for a
  precise reason:

    • The repo DOES have an arbitrary-base-point exponential map `ExpMap.expMap g gi hC p v` and, more,
      an arbitrary-base-point PULLBACK METRIC `PullbackMetric.expPullbackMetric g gi hC p` = `exp_p^* g`
      together with its RNC-gauge jets AT the recentered origin: value `g̃(0) = g(p) = δ`
      (`expPullbackMetric_at_zero`), first-order flatness `∂g̃(0) = 0` (`pd_expPullbackMetric_at_zero`),
      `Γ̃(0) = 0` (`christoffel_expPullbackMetric_zero`), symmetry, the smooth inverse `g̃⁻¹` at `0`, and
      the closed second jet `∂²g̃(0)` (`pd2_expPullbackMetric_at_zero`).  So the arbitrary-center RNC
      GAUGE DATA that the residual lemmas consume at center `0` genuinely EXISTS at every base point.

    • BUT the pullback metric is only `ContDiffOn ℝ 2` ON THE EXP-BALL
      (`contDiffOn_expPullbackMetric`, SHARP: `fderiv exp_p` costs one order, so `C³ exp_p ⟹ C² g̃`),
      whereas the residual chain `cutoffResidual_diag_hEboundW` demands `ContDiff ℝ ⊤` GLOBALLY for
      `g`, `gi`, `christoffel`, plus the far-field / cutoff constructions OFF the ball
      (`ParametrixHAnnulusBounds`, `CutoffAnnulusBounds`, `CutoffResidualGlobalBound`).  The
      C²-on-a-ball data of `expPullbackMetric` cannot be fed to that ⊤-global, whole-space chain.

  Hence the recenter wall is genuinely infrastructure-scale (the "smooth-dependence of exp on the base
  point + finite-regularity residual chain" frontier), not a one-lemma gap.  The honest deliverable is
  therefore this ABSTRACT reduction, which names the wall precisely and loses nothing.  It does NOT
  prove `hEboundW`, does NOT instantiate the concrete residual at `q ≠ 0`, and is NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.ParametrixHEboundWiring

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- **The per-base-point width-2 Gaussian residual family** — the transparent form of the abstract
    width-2 target `hEboundW`.  For a residual `E`, constant `C`, this asserts that, over EVERY base
    point `q`, the residual is dominated by the same-shape width-2 (doubled-time) Gaussian in the
    coordinate difference `p − q`:
        `∀ q τ, 0 < τ → ∀ p, |E τ p q| ≤ C · gaussDdim (2τ) (p − q)`.
    Its `q = 0` member is exactly the concrete diagonal residual bound (near-diagonal part proved by
    `residualN0_local_baseKernelW_slice`; global diagonal-chart assembly
    `cutoffResidual_diag_hEboundW`). -/
def UniformPerBasePointGaussian (E : ℝ → Point n → Point n → ℝ) (C : ℝ) : Prop :=
  ∀ (q : Point n) (τ : ℝ), 0 < τ → ∀ p : Point n,
    |E τ p q| ≤ C * gaussDdim (2 * τ) (p - q)

/-- **★ THE RECENTER REDUCTION (C4c, `q ≠ 0`).**  The GLOBAL width-2 target `hEboundW` follows from
    the per-base-point width-2 Gaussian family, uniform in the base point `q`.  Pure repackaging via
    `baseKernelW_zero_apply` (`baseKernelW 2 0 τ p q = gaussDdim (2τ) (p − q)`): the width-kernel
    wrapper's `κ = 2, α = 0` indices ARE the doubled-time Gaussian, so the abstract target is exactly
    the per-`q` Gaussian bound.  This converts the abstract width-2 objective into the concrete
    per-base-point shape that the geometric residual naturally produces, isolating the wall to "the
    base-0 slice, uniform in `q`."  `huniform` is genuinely used (it IS the content); NOT `a₁ = R/6`. -/
theorem hEboundW_of_uniform_perBasePoint
    (E : ℝ → Point n → Point n → ℝ) (C : ℝ)
    (huniform : ∀ (q : Point n) (τ : ℝ), 0 < τ → ∀ p : Point n,
        |E τ p q| ≤ C * gaussDdim (2 * τ) (p - q)) :
    ∀ (τ : ℝ) (p q : Point n), 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  intro τ p q hτ
  rw [baseKernelW_zero_apply]
  exact huniform q τ hτ p

/-- **The reduction is LOSSLESS — the abstract width-2 target IS the per-base-point Gaussian family.**
    An `Iff`: `hEboundW` holds ⟺ the per-base-point width-2 Gaussian family `UniformPerBasePointGaussian`
    holds.  Both directions are the definitional rewrite `baseKernelW 2 0 τ p q = gaussDdim (2τ) (p−q)`
    (`baseKernelW_zero_apply`).  This certifies that the recenter reduction adds NO assumption and
    discards NO content: the entire remaining obstruction to `hEboundW` is EXACTLY the per-base-point
    (all `q`) width-2 Gaussian residual bound, whose `q = 0` near-diagonal slice is already proved
    (`residualN0_local_baseKernelW_slice`) and whose only open residue is uniformity in `q` — the
    C4c off-diagonal recenter wall (blocked on ⊤-global smoothness of the arbitrary-center chart; see
    the file header's Step-1 finding).  NOT `a₁ = R/6`. -/
theorem hEboundW_iff_uniform_perBasePoint (E : ℝ → Point n → Point n → ℝ) (C : ℝ) :
    (∀ (τ : ℝ) (p q : Point n), 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ↔ UniformPerBasePointGaussian E C := by
  constructor
  · intro h q τ hτ p
    rw [← baseKernelW_zero_apply]
    exact h τ p q hτ
  · exact hEboundW_of_uniform_perBasePoint E C

end QIQTH.HeatResidualBound
