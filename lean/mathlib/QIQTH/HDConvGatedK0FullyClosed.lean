/-
  HDConvGatedK0FullyClosed — ★★★ THE LITERAL top-level `hDConv` closure at the genuinely-curved
  `K = {0}` witness.  The SECOND of the analytic trio {hDuhamel, hDConv, hCConv} carried by the
  reduced `a₁ = R/6` capstone (`TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual_restricted`)
  closed in its LITERAL top-level shape (`DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp
  g gi H)) u 0 0) t`), by the SAME null-singleton `z`-gate mechanism as `hCConv` (J4-988).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  It closes the LITERAL `hDConv` hypothesis ONLY at the degenerate `K = {0}` witness (`1 ≤ n`), where
  the whole convolution `heatConv H (leviSeries (heatOp g gi H))` is IDENTICALLY ZERO (in EVERY
  argument, hence in the time variable `u`).  `a₁ = R/6` remains STRICTLY CONDITIONAL on the trio
  {hDuhamel, hDConv, hCConv}:

    • `hDConv` (this file) and `hCConv` (J4-988) close here only because the convolution collapses to
      `0` — curved geometry does NO substantive analytic work (null-singleton `z`-gate driven).
    • `hDuhamel` is **NOT** closed here — and CANNOT be, at THIS witness.  The SAME collapse that
      trivialises `hDConv`/`hCConv` gates away the approximate-identity boundary term that `hDuhamel`
      needs, so at `K = {0}` the Duhamel identity reduces to the constraint
      `heatOp g gi H t 0 0 = 0` (the parametrix residual at the diagonal, which is generically
      NONZERO — it is precisely the object whose short-time coefficient is `a₁ = R/6`).  Hence the
      trio is NOT jointly closable at `K = {0}` and there is **NO** complete non-vacuous instance of
      `a₁ = R/6` at this witness.  (See the module note below and the session ledger J4-989.)

  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MECHANISM — identical to `hCConv` (J4-988), applied in the TIME slot.

  Recall the Duhamel convolution
      `heatConv A B t x y = ∫ s in 0..t, (∫ z, A (t−s) x z · B s z y)`.
  In the `hDConv` target the left kernel is `A := H = vanVleckGatedWitness … = gatedKernel {0} S H₀`,
  and BOTH spatial arguments are frozen at `0` (`x = y = 0`); the FREE variable is now the TIME `u`.
  The gate
      `gatedKernel K S H₀ τ p q = if q ∈ K then (if p ∈ S q then H₀ τ p q else 0) else 0`
  gates the THIRD ("base point" `q`) argument by `K`.  In `A (u−s) 0 z` that third argument is the
  INNER `z`-integration variable, NOT the time `u`.  Hence for `z ∉ K = {0}` the OUTER gate fires and
  `A (u−s) 0 z = 0`, independently of `u`, `s`, `S`, and the base kernel `H₀`.  The `z`-integrand is
  supported in the null singleton `{0}`, so `∫ z, … = 0` for every `s`, every `u`, and consequently
      `heatConv (gatedKernel {0} S H₀) B u 0 0 = ∫ s in 0..u, 0 = 0`   for EVERY time `u`.
  So `(fun u => heatConv … u 0 0) = (fun _ => 0)`, which is `DifferentiableAt ℝ · t` by
  `differentiableAt_const`.

  This reuses the already-banked `HCConvGatedK0FullyClosed.heatConv_gatedK0_eqZero` (J4-988), which is
  stated for ANY time argument, field point, and final point — so specialising it to `(u, 0, 0)` is
  immediate; only the downstream property differs (`DifferentiableAt` in time here vs `ContDiff ⊤` in
  space there).

  ## WHAT LANDS (ns `QIQTH.HDConvGatedK0FullyClosed`).
    • `hDConv_gatedKernel_K0_closed` — ★ the LITERAL `hDConv` shape
      `DifferentiableAt ℝ (fun u => heatConv (gatedKernel {0} S H₀) (leviSeries (heatOp g gi
      (gatedKernel {0} S H₀))) u 0 0) t`, for ANY base kernel `H₀`.
    • `hDConv_vanVleckGatedWitness_K0_closed` — ★★★ the SAME, textually instantiated to the concrete
      `vanVleckGatedWitness` (with `hK := isCompact_singleton`), i.e. the EXACT literal top-level
      `hDConv` carry of the reduced `a₁=R/6` capstone at the curved `K = {0}` witness.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HCConvGatedK0FullyClosed

open MeasureTheory Set Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.HDConvGatedK0FullyClosed

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — the literal `hDConv` closure (time-slot analogue of `hCConv`).
    ############################################################################### -/

/-- **★ `hDConv_gatedKernel_K0_closed`.**  The LITERAL `hDConv` shape for a `K = {0}`-gated left kernel
    and the Levi series of its heat operator:
      `DifferentiableAt ℝ (fun u => heatConv (gatedKernel {0} S H₀)
        (leviSeries (heatOp g gi (gatedKernel {0} S H₀))) u 0 0) t`.
    The bracketed function is IDENTICALLY `0` in the TIME variable `u`
    (`HCConvGatedK0FullyClosed.heatConv_gatedK0_eqZero`, applied at `(u, 0, 0)`), so `DifferentiableAt`
    holds by `differentiableAt_const`.  Holds for ANY `g gi S H₀ t`. -/
theorem hDConv_gatedKernel_K0_closed (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (S : Point n → Set (Point n)) (H0 : ℝ → Point n → Point n → ℝ) (t : ℝ) :
    DifferentiableAt ℝ
      (fun u => heatConv (gatedKernel ({0} : Set (Point n)) S H0)
        (leviSeries (heatOp g gi (gatedKernel ({0} : Set (Point n)) S H0))) u 0 0) t := by
  have hfun : (fun u => heatConv (gatedKernel ({0} : Set (Point n)) S H0)
        (leviSeries (heatOp g gi (gatedKernel ({0} : Set (Point n)) S H0))) u 0 0)
      = (fun _ : ℝ => (0 : ℝ)) := by
    funext u
    exact QIQTH.HCConvGatedK0FullyClosed.heatConv_gatedK0_eqZero hn S H0 _ u 0 0
  rw [hfun]
  exact differentiableAt_const 0

/-- **★★★ `hDConv_vanVleckGatedWitness_K0_closed`.**  THE LITERAL top-level `hDConv` carry of the
    reduced `a₁ = R/6` capstone
    (`TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual_restricted`), at the concrete curved
    `K = {0}` witness (`hK := isCompact_singleton`, `1 ≤ n`):
      `DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr isCompact_singleton S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr isCompact_singleton S a b))) u 0 0) t`.
    `vanVleckGatedWitness … = gatedKernel {0} S (globalCutoffParametrixWitnessN 1 …)` by definition, so
    this is a direct instance of `hDConv_gatedKernel_K0_closed`.  The bracketed function is IDENTICALLY
    `0` in the time variable `u`, so `DifferentiableAt` is trivial.

    ⚠ This CLOSES the literal `hDConv` hypothesis, but ONLY at this degenerate `K = {0}` witness, where
    the whole convolution vanishes.  It does NOT make `a₁ = R/6` unconditional: `hDuhamel` is NOT
    closed here (and CANNOT be — at `K = {0}` it reduces to `heatOp g gi H t 0 0 = 0`, the generically
    NONZERO diagonal parametrix residual).  NON-VACUOUS: the statement is a genuine `DifferentiableAt`
    fact about a concrete function, not `True` and not a hypothesis; the hypotheses `1 ≤ n` and the
    smooth-Christoffel carrier `hChr` are ordinary satisfiable data.  NOT `a₁ = R/6`. -/
theorem hDConv_vanVleckGatedWitness_K0_closed (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b t : ℝ) :
    DifferentiableAt ℝ
      (fun u => heatConv
        (vanVleckGatedWitness g gi hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b)))
        u 0 0) t := by
  unfold vanVleckGatedWitness
  exact hDConv_gatedKernel_K0_closed hn g gi S _ t

end QIQTH.HDConvGatedK0FullyClosed

/-! ## Axiom check — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HDConvGatedK0FullyClosed
#print axioms hDConv_gatedKernel_K0_closed
#print axioms hDConv_vanVleckGatedWitness_K0_closed
end AxiomChecks
