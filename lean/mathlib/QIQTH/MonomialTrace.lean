/-
  W3a (TYPE_II_TRACE_PLAN.md) — the monomial trace formula: `τ₀∘θ_s = e^{−s}·τ₀`, EXACTLY.

  The dual-weight trace on the crossed product's normal-ordered core monomials `π(a)·λ_t·f(L)`
  (`f : ExpTest` a log-clock symbol):
      τ₀(π(a)·λ_t·f(L)) := ω(a) · ∫ e^x e^{itx} f(x) dx  =  ω(a) · Iexp(f.modMul t)
  — the consult's normal form (binding: the density on the LOG-CLOCK variable; NO position-diagonal/[t=0] form).
  The dual action sends the monomial data to `(a, t, f(·+s))` with the phase `e^{ist}` — justified at the
  OPERATOR level by W1 (`dualAction_monomial`: θ_s(π(a)λ_t) = e^{ist}·π(a)λ_t, from
  `dualAction_mul` + `dualAction_matter` + `dualAction_clock`) — and the trace scales EXACTLY:
      `tauMonomial_dual` :  e^{its}·τ₀(a, t, f(·+s)) = e^{−s}·τ₀(a, t, f)
  (Weyl phase + W1.5's change of variables; the soft phases cancel against the density shift).

  ⚠ Honest scope: the trace FUNCTIONAL on the monomial core data (the matter part abstract, `ω : A → ℂ` the
  matter state); traciality and positivity are W3b (the eigen-core); the operator representation of `f(L)` and
  the vN closure stay with the later rungs / the carried extension. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.DualAction
import QIQTH.LogClockWeight

namespace QIQTH.TypeIITrace

open MeasureTheory QIQTH.Spectral.Multiplication QIQTH.StandardSubspaceModular

/-! ## The operator-level phase (W1 ⟹ the monomial's θ-transform) -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- **The dual action on a crossed-product monomial** `θ_s(π(a)·λ_t) = e^{ist}·π(a)·λ_t` — the operator-level
    justification for the monomial data transform `(a,t,f) ↦ e^{ist}·(a,t,f(·+s))`. From W1's
    `dualAction_mul` + `dualAction_matter` + `dualAction_clock`. -/
theorem dualAction_monomial (S : StandardSubspace H) (s t : ℝ) (a : H →L[ℂ] H) :
    dualAction s ((matterRep S a) ∘L (clockTransl t : Lp H 2 (volume : Measure ℝ) →L[ℂ] _))
      = Complex.exp (↑(s * t) * Complex.I) • ((matterRep S a) ∘L clockTransl t) := by
  rw [dualAction_mul, dualAction_matter, dualAction_clock, ContinuousLinearMap.comp_smul]

/-! ## The monomial trace functional and its exact scaling -/

variable {A : Type*}

/-- **The dual-weight trace on core monomials**: `τ₀(π(a)·λ_t·f(L)) := ω(a)·∫e^x e^{itx} f(x) dx` — the matter
    state times the log-clock–weighted, clock-modulated symbol integral (the consult's normal form). -/
noncomputable def tauMonomial (ω : A → ℂ) (a : A) (t : ℝ) (f : ExpTest) : ℂ :=
  ω a * Iexp (f.modMul t)

/-- The modulation/shift interchange: shifting the MODULATED symbol equals the Weyl phase times modulating the
    SHIFTED symbol — `Iexp((e^{itx}f)(·+s)) = e^{its}·Iexp(e^{itx}·f(·+s))`. -/
theorem Iexp_modMul_dualShift_comm (s t : ℝ) (f : ExpTest) :
    Iexp ((f.modMul t).dualShift s)
      = Complex.exp (↑(t * s) * Complex.I) * Iexp ((f.dualShift s).modMul t) := by
  rw [Iexp, Iexp, ← integral_const_mul]
  congr 1
  funext x
  simp only [ExpTest.dualShift, ExpTest.modMul]
  rw [modSymbol_add_right]
  ring

/-- **W3a CAPSTONE — the EXACT dual scaling of the monomial trace:** the θ_s-image of the monomial
    (`(a, t, f(·+s))` with the operator-level phase `e^{ist}`, `dualAction_monomial`) has trace exactly
    `e^{−s}` times the original: `e^{its}·τ₀(a,t,f(·+s)) = e^{−s}·τ₀(a,t,f)`. The Weyl phase cancels against
    the density shift (W1.5's `Iexp_dualShift`) — the CPW relative invariance `τ₀∘θ_s = e^{−s}·τ₀`, exact on
    the monomial core, no regularization. -/
theorem tauMonomial_dual (ω : A → ℂ) (a : A) (s t : ℝ) (f : ExpTest) :
    Complex.exp (↑(t * s) * Complex.I) * tauMonomial ω a t (f.dualShift s)
      = (Real.exp (-s) : ℂ) * tauMonomial ω a t f := by
  rw [tauMonomial, tauMonomial]
  rw [show Complex.exp (↑(t * s) * Complex.I) * (ω a * Iexp ((f.dualShift s).modMul t))
      = ω a * (Complex.exp (↑(t * s) * Complex.I) * Iexp ((f.dualShift s).modMul t)) from by ring]
  rw [← Iexp_modMul_dualShift_comm, Iexp_dualShift]
  ring

/-- The trace is linear in the matter state (the functional shape the eigen-core sums will use). -/
theorem tauMonomial_matter_linear (ω₁ ω₂ : A → ℂ) (a : A) (t : ℝ) (f : ExpTest) :
    tauMonomial (fun x => ω₁ x + ω₂ x) a t f = tauMonomial ω₁ a t f + tauMonomial ω₂ a t f := by
  simp only [tauMonomial]
  ring

end QIQTH.TypeIITrace
