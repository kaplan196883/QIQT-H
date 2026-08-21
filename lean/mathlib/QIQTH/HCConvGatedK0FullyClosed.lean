/-
  HCConvGatedK0FullyClosed — ★★★ THE LITERAL top-level `hCConv` closure at the genuinely-curved
  `K = {0}` witness.  FIRST time one of the analytic trio {hDuhamel, hDConv, hCConv} carried by the
  reduced `a₁ = R/6` capstone (`TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual_restricted`)
  is closed in its LITERAL top-level shape (`ContDiff ℝ ⊤ (fun p => heatConv H (leviSeries (heatOp g gi
  H)) t p 0)`), rather than an auxiliary census member.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  It closes the LITERAL `hCConv` hypothesis ONLY at the degenerate `K = {0}` witness (`1 ≤ n`), where
  the whole convolution is IDENTICALLY ZERO in `p`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  {hDuhamel, hDConv, hCConv}: `hDuhamel` is untouched, and `hCConv`/`hDConv` are closed here only at
  this single analytically-degenerate witness (curved geometry does NO substantive analytic work — the
  closure is driven purely by the null-singleton `z`-gate).  No `sorry`, no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.
  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MECHANISM — the OUTER base-point gate on the INNER `z`-integration variable.

  Recall the Duhamel convolution
      `heatConv A B t x y = ∫ s in 0..t, (∫ z, A (t−s) x z · B s z y)`.
  In the `hCConv` target the left kernel is `A := H = vanVleckGatedWitness … = gatedKernel {0} S H₀`,
  evaluated at `A (t−s) p z` with `p` the FREE `ContDiff` variable and `z` the INNER `z`-integration
  variable.  The gate
      `gatedKernel K S H₀ τ p q = if q ∈ K then (if p ∈ S q then H₀ τ p q else 0) else 0`
  gates the THIRD ("base point" `q`) argument by `K`.  In `A (t−s) p z` that third argument is `z`,
  NOT `p`.  Hence for `z ∉ K = {0}` (i.e. `z ≠ 0`) the OUTER gate fires and `A (t−s) p z = 0`,
  independently of `p`, of `S`, and of the base kernel `H₀`.

  Therefore the `z`-integrand `z ↦ A(t−s) p z · B s z y` is SUPPORTED IN the null singleton `{0}`
  (`measure_singleton`, valid for `1 ≤ n` via `Nontrivial (Point n)`), so `∫ z, … = 0` for EVERY `s`,
  EVERY `p`, EVERY `y`, and ANY right kernel `B`.  Consequently
      `heatConv (gatedKernel {0} S H₀) B t p y = ∫ s in 0..t, 0 = 0`   for every `p`,
  so `(fun p => heatConv … t p 0) = (fun _ => 0)`, which is `ContDiff ℝ ⊤` by `contDiff_const`.

  This is NOT the derivative-kernel support fact (zero field-derivative off `K`).  It is the ORIGINAL
  convolution integrand's OUTER `q = z` base-point gate — exactly the object `hCConv`'s `ContDiff`
  quantifies over.  (gpt-5.6-sol, high reasoning, audited 2026-08-22: argument-position claim CONFIRMED,
  identically-zero conclusion SOUND, closes the literal `hCConv` at this witness, `hDuhamel` remains.)

  ## WHAT LANDS (ns `QIQTH.HCConvGatedK0FullyClosed`).
    • `innerZ_integral_gatedK0_eqZero` — the inner `z`-integral of the `{0}`-gated convolution
      integrand is `0` (support in the null singleton), for ANY `S`, `H₀`, right kernel `B`, times,
      field point `p`, and final point `y`.
    • `heatConv_gatedK0_eqZero` — the FULL convolution `heatConv (gatedKernel {0} S H₀) B t p y = 0`.
    • `hCConv_gatedKernel_K0_closed` — ★ the LITERAL `hCConv` shape
      `ContDiff ℝ ⊤ (fun p => heatConv (gatedKernel {0} S H₀) (leviSeries (heatOp g gi (gatedKernel
      {0} S H₀))) t p 0)`, for ANY base kernel `H₀`.
    • `hCConv_vanVleckGatedWitness_K0_closed` — ★★★ the SAME, textually instantiated to the concrete
      `vanVleckGatedWitness` (with `hK := isCompact_singleton`), i.e. the EXACT literal top-level
      `hCConv` carry of the reduced `a₁=R/6` capstone at the curved `K = {0}` witness.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HZMassFullyClosedCurved
import QIQTH.ConvApproximants

open MeasureTheory Set Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.HCConvGatedK0FullyClosed

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — the inner `z`-integral vanishes (null-singleton base-point gate).
    ############################################################################### -/

/-- **★ `innerZ_integral_gatedK0_eqZero`.**  The inner `z`-integral of the `K = {0}`-gated convolution
    integrand vanishes.  The left kernel `gatedKernel {0} S H₀ τ p z` has its OUTER (base-point `q`)
    gate on the INNER `z`-integration variable: for `z ≠ 0` it is `0`, so the integrand
    `z ↦ gatedKernel {0} S H₀ τ p z · B s z y` is supported in the null singleton `{0}`
    (`1 ≤ n ⟹ Nontrivial (Point n) ⟹ NoAtoms volume`).  Holds for ANY `S`, `H₀`, right kernel `B`,
    times `τ s`, field point `p`, and final point `y`. -/
theorem innerZ_integral_gatedK0_eqZero (hn : 1 ≤ n)
    (S : Point n → Set (Point n)) (H0 : ℝ → Point n → Point n → ℝ)
    (B : ℝ → Point n → Point n → ℝ) (τ s : ℝ) (p y : Point n) :
    (∫ z, gatedKernel ({0} : Set (Point n)) S H0 τ p z * B s z y) = 0 := by
  have hn0 : 0 < n := by omega
  haveI : Inhabited (Fin n) := ⟨⟨0, hn0⟩⟩
  haveI : Nontrivial (Point n) := Pi.nontrivial
  refine QIQTH.HZMassFullyClosedCurved.integral_eq_zero_of_support_subset_singleton
    (μ := (volume : Measure (Point n)))
    (fun z => gatedKernel ({0} : Set (Point n)) S H0 τ p z * B s z y) (0 : Point n) ?_
  intro z hz
  rw [Set.mem_singleton_iff]
  by_contra hz0
  have hzK : z ∉ ({0} : Set (Point n)) := fun h => hz0 (Set.mem_singleton_iff.mp h)
  have hg0 : gatedKernel ({0} : Set (Point n)) S H0 τ p z = 0 :=
    gatedKernel_apply_of_notMem ({0} : Set (Point n)) S H0 τ p z (Or.inl hzK)
  exact (Function.mem_support.mp hz) (by rw [hg0, zero_mul])

/-! ###############################################################################
    ### §2 — the FULL convolution vanishes, hence the literal `hCConv` closure.
    ############################################################################### -/

/-- **★ `heatConv_gatedK0_eqZero`.**  The full Duhamel convolution with a `K = {0}`-gated LEFT kernel
    is identically `0`: every inner `z`-integral is `0` (`innerZ_integral_gatedK0_eqZero`), so the
    outer `s`-integrand is the zero function.  For ANY `S`, `H₀`, right kernel `B`, time `t`, field
    point `p`, final point `y`. -/
theorem heatConv_gatedK0_eqZero (hn : 1 ≤ n)
    (S : Point n → Set (Point n)) (H0 : ℝ → Point n → Point n → ℝ)
    (B : ℝ → Point n → Point n → ℝ) (t : ℝ) (p y : Point n) :
    heatConv (gatedKernel ({0} : Set (Point n)) S H0) B t p y = 0 := by
  rw [heatConv]
  have hinner : ∀ s : ℝ,
      (∫ z, gatedKernel ({0} : Set (Point n)) S H0 (t - s) p z * B s z y) = 0 :=
    fun s => innerZ_integral_gatedK0_eqZero hn S H0 B (t - s) s p y
  simp only [hinner]
  exact intervalIntegral.integral_zero

/-- **★ `hCConv_gatedKernel_K0_closed`.**  The LITERAL `hCConv` shape for a `K = {0}`-gated left kernel
    and the Levi series of its heat operator: `ContDiff ℝ ⊤ (fun p => heatConv (gatedKernel {0} S H₀)
    (leviSeries (heatOp g gi (gatedKernel {0} S H₀))) t p 0)`.  The bracketed function is IDENTICALLY
    `0` in `p` (`heatConv_gatedK0_eqZero`), so `ContDiff ℝ ⊤` holds by `contDiff_const`.  Holds for ANY
    `g gi S H₀ t`. -/
theorem hCConv_gatedKernel_K0_closed (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (S : Point n → Set (Point n)) (H0 : ℝ → Point n → Point n → ℝ) (t : ℝ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun p => heatConv (gatedKernel ({0} : Set (Point n)) S H0)
        (leviSeries (heatOp g gi (gatedKernel ({0} : Set (Point n)) S H0))) t p 0) := by
  have hfun : (fun p => heatConv (gatedKernel ({0} : Set (Point n)) S H0)
        (leviSeries (heatOp g gi (gatedKernel ({0} : Set (Point n)) S H0))) t p 0)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext p
    exact heatConv_gatedK0_eqZero hn S H0 _ t p 0
  rw [hfun]
  exact contDiff_const

/-- **★★★ `hCConv_vanVleckGatedWitness_K0_closed`.**  THE LITERAL top-level `hCConv` carry of the
    reduced `a₁ = R/6` capstone
    (`TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual_restricted`), at the concrete curved
    `K = {0}` witness (`hK := isCompact_singleton`, `1 ≤ n`):
      `ContDiff ℝ ⊤ (fun p => heatConv (vanVleckGatedWitness g gi hChr isCompact_singleton S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr isCompact_singleton S a b))) t p 0)`.
    `vanVleckGatedWitness … = gatedKernel {0} S (globalCutoffParametrixWitnessN 1 …)` by definition, so
    this is a direct instance of `hCConv_gatedKernel_K0_closed`.  The bracketed function is IDENTICALLY
    `0` in `p`, so `ContDiff ℝ ⊤` is trivial.

    ⚠ This CLOSES the literal `hCConv` hypothesis, but ONLY at this degenerate `K = {0}` witness, where
    the whole convolution vanishes.  It does NOT make `a₁ = R/6` unconditional: `hDuhamel` is untouched
    (and `hDConv` is likewise trivial here, but at the SAME degenerate witness).  NON-VACUOUS: the
    statement is a genuine `ContDiff` fact about a concrete function, not `True` and not a hypothesis;
    the hypotheses `1 ≤ n` and the smooth-Christoffel carrier `hChr` are ordinary satisfiable data.
    NOT `a₁ = R/6`. -/
theorem hCConv_vanVleckGatedWitness_K0_closed (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b t : ℝ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun p => heatConv
        (vanVleckGatedWitness g gi hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b)))
        t p 0) := by
  unfold vanVleckGatedWitness
  exact hCConv_gatedKernel_K0_closed hn g gi S _ t

end QIQTH.HCConvGatedK0FullyClosed

/-! ## Axiom check — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HCConvGatedK0FullyClosed
#print axioms innerZ_integral_gatedK0_eqZero
#print axioms heatConv_gatedK0_eqZero
#print axioms hCConv_gatedKernel_K0_closed
#print axioms hCConv_vanVleckGatedWitness_K0_closed
end AxiomChecks
