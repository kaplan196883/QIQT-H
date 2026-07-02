/-
  W3b (TYPE_II_TRACE_PLAN.md) — the modular eigen-core: TRACIALITY and POSITIVITY of the dual-weight trace.

  The consult's tracial core: matter elements that are σ-eigenoperators (`σ_t(a) = e^{itκ}a`), packaged as
  `EigenTerm`s `(κ, a, F)` representing `π(a)·F(L)`, with the *-algebra operations at the data level:
      mul  : (κ₁+κ₂, a₁a₂, F₁(·−κ₂)·F₂)      (the covariance relation `F(L)·π(b) = π(b)·F(L−κ_b)`)
      star : (−κ, a*, conj∘F(·+κ))
      theta: the dual shift on the symbol (no phase — eigen terms carry no bare λ_t).
  The THREE trace laws, each exact:
  • `eigen_tau_dual`   — the scaling `τ₀(θ_s x) = e^{−s}·τ₀(x)` (W1.5 verbatim);
  • `eigen_tau_trace`  — **TRACIALITY** `τ₀(xy) = τ₀(yx)`: at zero total frequency the matter KMS-eigen factor
    `ω(ab) = e^κ·ω(ba)` cancels EXACTLY against the `∫e^x` change of variables; at nonzero total frequency both
    sides vanish (frequency conservation). The Type II miracle — a KMS (non-tracial) matter state becomes a
    TRACE after dressing with the log-clock density;
  • `eigen_tau_star_mul_nonneg` — **POSITIVITY** `τ₀(x*x) ≥ 0`: the symbol of `x*x` is the pointwise
    norm-square, so the weight integral is a nonneg real, times the matter positivity `ω(a*a) ≥ 0`.

  ⚠ Honest scope: the matter KMS-eigen law, frequency conservation, and matter positivity are CARRIED hypotheses
  (they are the modular-matter inputs — provable for the finite corner, abstract here); single-term/pair level
  (finite-sum positivity via frequency-block orthogonality = the W4-side extension); vN closure carried. Std-3.
-/
import Mathlib
import QIQTH.MonomialTrace

namespace QIQTH.TypeIITrace

open MeasureTheory

/-! ## ExpTest closure operations -/

/-- Any test symbol's bound is nonnegative. -/
theorem ExpTest.bound_nonneg (F : ExpTest) : 0 ≤ F.bound :=
  le_trans (norm_nonneg _) (F.hbound 0)

/-- Pointwise conjugation of a test symbol. -/
noncomputable def ExpTest.conj (F : ExpTest) : ExpTest where
  f := fun r => (starRingEnd ℂ) (F.f r)
  meas := (Complex.continuous_conj.measurable).comp F.meas
  bound := F.bound
  hbound := fun r => by rw [RCLike.norm_conj]; exact F.hbound r
  rad := F.rad
  hsupp := fun r hr => by rw [F.hsupp r hr, map_zero]

/-- The eigen-product symbol `r ↦ F₁(r−κ)·F₂(r)` (the covariance-ordered product of symbols). -/
noncomputable def ExpTest.shiftMul (κ : ℝ) (F₁ F₂ : ExpTest) : ExpTest where
  f := fun r => F₁.f (r - κ) * F₂.f r
  meas := (F₁.meas.comp (measurable_id.sub_const κ)).mul F₂.meas
  bound := F₁.bound * F₂.bound
  hbound := fun r => by
    rw [norm_mul]
    exact mul_le_mul (F₁.hbound (r - κ)) (F₂.hbound r) (norm_nonneg _) F₁.bound_nonneg
  rad := F₂.rad
  hsupp := fun r hr => by rw [F₂.hsupp r hr, mul_zero]

/-! ## The eigen-core -/

variable {A : Type*} [Mul A] [Star A]

/-- **An eigen-core term** `(κ, a, F)`, representing `π(a)·F(L)` with `a` a modular eigenoperator of frequency
    `κ` (`σ_t(a) = e^{itκ}a` — the frequency data carried with the term). -/
structure EigenTerm (A : Type*) where
  /-- the modular frequency of the matter part -/
  κ : ℝ
  /-- the matter eigenoperator -/
  a : A
  /-- the log-clock symbol -/
  F : ExpTest

/-- The eigen-core product: frequencies add, matter multiplies, and the covariance relation
    `F(L)·π(b) = π(b)·F(L−κ_b)` orders the symbols. -/
noncomputable def EigenTerm.mul (x y : EigenTerm A) : EigenTerm A where
  κ := x.κ + y.κ
  a := x.a * y.a
  F := ExpTest.shiftMul y.κ x.F y.F

/-- The eigen-core star: frequency negates, matter stars, the symbol conjugate-shifts. -/
noncomputable def EigenTerm.star (x : EigenTerm A) : EigenTerm A where
  κ := -x.κ
  a := Star.star x.a
  F := (x.F.dualShift x.κ).conj

/-- The dual action on an eigen term: the symbol shifts (no phase — no bare `λ_t` in the eigen normal form). -/
def EigenTerm.theta (s : ℝ) (x : EigenTerm A) : EigenTerm A where
  κ := x.κ
  a := x.a
  F := x.F.dualShift s

/-- **The dual-weight trace on the eigen-core**: `τ₀(π(a)F(L)) = ω(a)·Iexp(F)`. -/
noncomputable def EigenTerm.tau (ω : A → ℂ) (x : EigenTerm A) : ℂ := ω x.a * Iexp x.F

/-- **The scaling law on the eigen-core** `τ₀(θ_s x) = e^{−s}·τ₀(x)` (W1.5 verbatim). -/
theorem eigen_tau_dual (ω : A → ℂ) (s : ℝ) (x : EigenTerm A) :
    (x.theta s).tau ω = (Real.exp (-s) : ℂ) * x.tau ω := by
  rw [EigenTerm.tau, EigenTerm.theta, EigenTerm.tau, Iexp_dualShift]
  ring

/-- The eigen change-of-variables: `Iexp(F₂(·−κ)·F₁) = e^{κ}·Iexp(F₁(·+κ... )·F₂)` in the exact pairing form
    the traciality proof needs — `∫e^r F₂(r−κ)F₁(r) dr = e^{κ}·∫e^u F₁(u+κ)F₂(u) du`. -/
theorem Iexp_shiftMul_swap (κ : ℝ) (F₁ F₂ : ExpTest) :
    Iexp (ExpTest.shiftMul κ F₂ F₁)
      = (Real.exp κ : ℂ) * ∫ u : ℝ, (Real.exp u : ℂ) * (F₁.f (u + κ) * F₂.f u) := by
  have hg : (fun r : ℝ => (Real.exp r : ℂ) * ((ExpTest.shiftMul κ F₂ F₁).f r))
      = fun r : ℝ => (fun u : ℝ => (Real.exp (u + κ) : ℂ) * (F₁.f (u + κ) * F₂.f u)) (r + -κ) := by
    funext r
    show (Real.exp r : ℂ) * (F₂.f (r - κ) * F₁.f r)
        = (Real.exp (r + -κ + κ) : ℂ) * (F₁.f (r + -κ + κ) * F₂.f (r + -κ))
    rw [show r + -κ + κ = r from by ring, show r + -κ = r - κ from by ring]
    ring
  rw [Iexp, hg,
    integral_add_right_eq_self (fun u : ℝ => (Real.exp (u + κ) : ℂ) * (F₁.f (u + κ) * F₂.f u)) (-κ),
    ← integral_const_mul]
  congr 1
  funext u
  rw [Real.exp_add]
  push_cast
  ring

/-- **W3b TRACIALITY — `τ₀(x·y) = τ₀(y·x)`.** CARRIED matter inputs: the KMS-eigen law
    `ω(a·b) = e^{κ_a}·ω(b·a)` at zero total frequency, and frequency conservation (`ω` of a nonzero-frequency
    product vanishes) off it. At zero total frequency the KMS factor `e^{x.κ}` cancels EXACTLY against the
    `∫e^r` change of variables (`Iexp_shiftMul_swap`); at nonzero total frequency both sides vanish. The Type II
    mechanism: a KMS matter state becomes a TRACE after dressing with the log-clock density. -/
theorem eigen_tau_trace (ω : A → ℂ) (x y : EigenTerm A)
    (hkms : x.κ + y.κ = 0 → ω (x.a * y.a) = (Real.exp x.κ : ℂ) * ω (y.a * x.a))
    (hfreq : x.κ + y.κ ≠ 0 → ω (x.a * y.a) = 0 ∧ ω (y.a * x.a) = 0) :
    (x.mul y).tau ω = (y.mul x).tau ω := by
  by_cases h0 : x.κ + y.κ = 0
  · -- zero total frequency: KMS ⟹ e^{x.κ} factor; the change of variables produces the same factor
    rw [EigenTerm.tau, EigenTerm.tau, EigenTerm.mul, EigenTerm.mul]
    simp only
    rw [hkms h0]
    -- `y.κ = −x.κ`: the first symbol integral becomes the swapped pairing
    have hyκ : y.κ = -x.κ := by linarith
    rw [Iexp_shiftMul_swap x.κ x.F y.F]
    -- LHS symbol: `∫e^r x.F(r−y.κ)·y.F(r) = ∫e^r x.F(r+x.κ)·y.F(r)` — the same pairing
    have hL : Iexp (ExpTest.shiftMul y.κ x.F y.F)
        = ∫ u : ℝ, (Real.exp u : ℂ) * (x.F.f (u + x.κ) * y.F.f u) := by
      rw [Iexp, ExpTest.shiftMul]
      simp only
      congr 1
      funext r
      rw [hyκ, show r - -x.κ = r + x.κ from by ring]
    rw [hL]
    ring
  · -- nonzero total frequency: both matter factors vanish
    rw [EigenTerm.tau, EigenTerm.tau, EigenTerm.mul, EigenTerm.mul]
    simp only
    rw [(hfreq h0).1, (hfreq h0).2, zero_mul, zero_mul]

/-- The symbol of `x*·x` is the pointwise norm-square `r ↦ conj(F r)·F r` (`(r+κ)−κ = r` collapses the shifts). -/
theorem star_mul_symbol (x : EigenTerm A) (r : ℝ) :
    ((x.star.mul x).F).f r = (starRingEnd ℂ) (x.F.f r) * x.F.f r := by
  simp only [EigenTerm.mul, EigenTerm.star, ExpTest.shiftMul, ExpTest.conj, ExpTest.dualShift]
  rw [show r - x.κ + x.κ = r from by ring]

/-- **W3b POSITIVITY — `τ₀(x*·x) ≥ 0`** (a nonneg real). The symbol of `x*x` is the pointwise norm-square, so
    the log-clock weight integral is a nonnegative real; with the CARRIED matter positivity `ω(a*·a) ≥ 0`
    (a real), the trace of `x*·x` is a nonnegative real. -/
theorem eigen_tau_star_mul_nonneg (ω : A → ℂ) (x : EigenTerm A)
    (hpos : 0 ≤ (ω (Star.star x.a * x.a)).re ∧ (ω (Star.star x.a * x.a)).im = 0) :
    0 ≤ ((x.star.mul x).tau ω).re ∧ ((x.star.mul x).tau ω).im = 0 := by
  have hIexp : Iexp ((x.star.mul x).F) = ∫ r : ℝ, ((Real.exp r * Complex.normSq (x.F.f r) : ℝ) : ℂ) := by
    rw [Iexp]
    congr 1
    funext r
    rw [star_mul_symbol]
    rw [show (starRingEnd ℂ) (x.F.f r) * x.F.f r = (Complex.normSq (x.F.f r) : ℂ) from by
      rw [Complex.normSq_eq_conj_mul_self]]
    push_cast
    ring
  have hreal : Iexp ((x.star.mul x).F)
      = ((∫ r : ℝ, Real.exp r * Complex.normSq (x.F.f r) : ℝ) : ℂ) := by
    rw [hIexp]
    exact integral_ofReal
  have hint_nonneg : 0 ≤ ∫ r : ℝ, Real.exp r * Complex.normSq (x.F.f r) :=
    integral_nonneg fun r => mul_nonneg (Real.exp_pos r).le (Complex.normSq_nonneg _)
  have htau : (x.star.mul x).tau ω = ω (Star.star x.a * x.a) * Iexp ((x.star.mul x).F) := rfl
  rw [htau, hreal]
  constructor
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg hpos.1 hint_nonneg
  · rw [Complex.mul_im, Complex.ofReal_im, mul_zero, zero_add, hpos.2, zero_mul]

end QIQTH.TypeIITrace
