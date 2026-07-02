/-
  W1.5 (TYPE_II_TRACE_PLAN.md) — the log-clock weight integral: the EXACT `e^{−s}` scaling.

  The CPW dual-weight density lives on the LOG-CLOCK spectral variable (binding consult correction): the weight
  of a clock symbol `f` is `Iexp f = ∫ e^x f(x) dx`, and the dual action shifts the log-clock symbol,
  `θ_s : f ↦ f(·+s)` (W1's `dualAction` at the symbol level). The load-bearing rung is the EXACT scaling
      `Iexp (f(·+s)) = e^{−s} · Iexp f`                    (`Iexp_dualShift`)
  — a pure change of variables, but it IS the `τ∘θ_s = e^{−s}τ` mechanism: every later trace rung (W3a's
  monomial formula, W3b's eigen-core) reduces its scaling law to this identity applied to a test symbol.

  `ExpTest` = bounded measurable compactly-supported symbols (binding: NOT Schwartz — `∫e^x|f|` must converge),
  closed under the dual shift (`dualShift`) and clock modulation (`modMul`, the symbol of `λ_t·f(L)`).

  ⚠ Honest scope: the symbol/integral level of the ladder; the operator `f(L)` representation and the trace
  functional are the LATER rungs (W3a/W3b); vN closure + full CPW trace carried (plan header). Axiom-free, std-3.
-/
import Mathlib
import QIQTH.Spectral.ModulationFlow

namespace QIQTH.TypeIITrace

open MeasureTheory QIQTH.Spectral.Multiplication

/-- **A log-clock test symbol**: bounded, measurable, compactly supported (so `∫ e^x f` converges). -/
structure ExpTest where
  /-- the symbol -/
  f : ℝ → ℂ
  meas : Measurable f
  /-- a uniform bound -/
  bound : ℝ
  hbound : ∀ x, ‖f x‖ ≤ bound
  /-- the support radius -/
  rad : ℝ
  hsupp : ∀ x, x ∉ Set.Icc (-rad) rad → f x = 0

/-- **The dual shift** `θ_s : f ↦ f(·+s)` at the symbol level (W1's dual action on log-clock symbols). -/
def ExpTest.dualShift (s : ℝ) (F : ExpTest) : ExpTest where
  f := fun x => F.f (x + s)
  meas := F.meas.comp (measurable_id.add_const s)
  bound := F.bound
  hbound := fun x => F.hbound (x + s)
  rad := F.rad + |s|
  hsupp := by
    intro x hx
    apply F.hsupp
    intro hmem
    apply hx
    simp only [Set.mem_Icc] at hmem ⊢
    constructor
    · have := le_abs_self s
      linarith [hmem.1]
    · have := neg_abs_le s
      linarith [hmem.2]

/-- **Clock modulation** `f ↦ e^{itx}·f` — the symbol of `λ_t · f(L)` (normal-ordered monomials). -/
noncomputable def ExpTest.modMul (t : ℝ) (F : ExpTest) : ExpTest where
  f := fun x => modSymbol t x * F.f x
  meas := (modSymbol_measurable t).mul F.meas
  bound := F.bound
  hbound := fun x => by
    rw [norm_mul, norm_modSymbol, one_mul]
    exact F.hbound x
  rad := F.rad
  hsupp := fun x hx => by rw [F.hsupp x hx, mul_zero]

/-- The weighted symbol `e^x·f(x)` is integrable (bounded on the compact support, zero outside). -/
theorem expTest_integrable (F : ExpTest) :
    Integrable (fun x => (Real.exp x : ℂ) * F.f x) (volume : Measure ℝ) := by
  have hsupp : Function.support (fun x => (Real.exp x : ℂ) * F.f x)
      ⊆ Set.Icc (-F.rad) F.rad := by
    intro x hx
    by_contra hmem
    apply hx
    show (Real.exp x : ℂ) * F.f x = 0
    rw [F.hsupp x hmem, mul_zero]
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  apply Measure.integrableOn_of_bounded (M := Real.exp F.rad * F.bound)
  · exact (measure_Icc_lt_top).ne
  · exact ((Complex.measurable_ofReal.comp Real.measurable_exp).mul F.meas).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    exact mul_le_mul (Real.exp_le_exp.mpr hx.2) (F.hbound x) (norm_nonneg _)
      (Real.exp_pos _).le

/-- **The log-clock weight** `Iexp f = ∫ e^x f(x) dx` — the CPW density against the log-clock variable. -/
noncomputable def Iexp (F : ExpTest) : ℂ := ∫ x, (Real.exp x : ℂ) * F.f x

/-- **W1.5 CAPSTONE — the EXACT `e^{−s}` scaling:** `Iexp (θ_s f) = e^{−s} · Iexp f`. The dual shift of the
    log-clock symbol scales the weight by exactly `e^{−s}` — the mechanism of `τ∘θ_s = e^{−s}τ`, to which every
    later trace rung reduces. Pure change of variables (`u = x + s`), exact, no regularization. -/
theorem Iexp_dualShift (s : ℝ) (F : ExpTest) :
    Iexp (F.dualShift s) = (Real.exp (-s) : ℂ) * Iexp F := by
  have hg : (fun x => (Real.exp x : ℂ) * F.f (x + s))
      = fun x => (fun u => (Real.exp (u + -s) : ℂ) * F.f u) (x + s) := by
    funext x
    simp only
    rw [show x + s + -s = x from by ring]
  rw [Iexp, ExpTest.dualShift]
  simp only
  rw [hg, integral_add_right_eq_self (fun u => (Real.exp (u + -s) : ℂ) * F.f u) s]
  rw [Iexp, ← integral_const_mul]
  congr 1
  funext u
  rw [Real.exp_add]
  push_cast
  ring

/-- The scaling for modulated (normal-ordered) symbols — the exact form W3a's monomial trace consumes:
    `Iexp(θ_s(e^{itx}·f)) = e^{−s}·Iexp(e^{itx}·f)`. -/
theorem Iexp_dualShift_modMul (s t : ℝ) (F : ExpTest) :
    Iexp ((F.modMul t).dualShift s) = (Real.exp (-s) : ℂ) * Iexp (F.modMul t) :=
  Iexp_dualShift s (F.modMul t)

end QIQTH.TypeIITrace
