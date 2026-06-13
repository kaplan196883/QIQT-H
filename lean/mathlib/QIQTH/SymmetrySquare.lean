/-
SymmetrySquare.lean — two faces of "the square is the degree-2 invariant" (GPT-5.5-pro consult 2026-06-13).

Companion to `RotationBorn` (compact rotation ⇒ α=2). Pro identified two further sharp results on where the
square comes from:

ASPECT 1 — the bell curve and Born share the SAME square (Maxwell–Herschel). A product density invariant
under the rotation/unitary group is forced to be Gaussian, with the rotation-invariant quadratic `|z|²` in the
exponent — exactly the Born quadratic. In squared-radius coordinates the U(2)-product invariance reads
`P(a)·P(b) = P(a+b)·P(0)`; the normalized radial profile is then MULTIPLICATIVE, `H(a+b)=H(a)·H(b)`, which
forces the exponential (Gaussian) profile `H(n)=H(1)^n = exp(a·n)`. This is the exact multiplicative mirror of
the additive `f(x+y)=f(x)+f(y) ⇒ Born` bridge (`RefinementBorn`): rotation+independence ⇒ Gaussian, just as
no-signaling+additivity ⇒ Born, both built on the same degree-2 form.

ASPECT 2 — a Lorentzian boost CANNOT carry a probability (sharp no-go). A boost is a rotation by imaginary
rapidity; it preserves the *indefinite* `t²−x²`, and the light-cone direction `(1,1)` is an eigenvector with
eigenvalue `eᵡ`. Any homogeneous boost-invariant `F ≥ 0` therefore satisfies `F(1,1)=e^{χα}F(1,1)` for all χ,
forcing `F(1,1)=0`: no boost-invariant positive probability norm exists. So relativistic Born comes from the
*unitary* (Wigner) representation — which preserves the positive-definite `Σ|c|²` — never from spacetime-boost
invariance. The mirror of `RotationBorn`: compact rotation *forces* α=2; non-compact boost *forbids* any
positive norm.

HONEST SCOPE (GPT-5.5-pro): both confirm the square is the degree-2 invariant of the symmetry group; neither
derives Born from nothing (the rotation/unitary already imports the quadratic). The Maxwell–Herschel profile
is proved here on integer radial values (the classical continuous-Cauchy step to all reals is cited). No
`sorry`, no project axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace QIQTH.SymmetrySquare

/-! ### Aspect 1 — Maxwell–Herschel: rotation + independence ⇒ Gaussian (the bell curve's square = Born's) -/

/-- **The bridge (rotation-product invariance ⇒ multiplicative radial profile).** In squared-radius
coordinates, `U(2)`-invariance of a product density reads `P(a)·P(b) = P(a+b)·P(0)`; hence the normalized
radial profile `H(u) = P(u)/P(0)` is multiplicative: `H(a+b) = H(a)·H(b)`. This is the multiplicative mirror
of the additive `f(x+y)=f(x)+f(y)` Born bridge. -/
theorem rotation_product_multiplicative (P : ℝ → ℝ) (hP0 : P 0 ≠ 0)
    (hinv : ∀ a b, P a * P b = P (a + b) * P 0) (a b : ℝ) :
    P (a + b) / P 0 = (P a / P 0) * (P b / P 0) := by
  rw [div_mul_div_comm, div_eq_div_iff hP0 (mul_ne_zero hP0 hP0), hinv a b]; ring

/-- A multiplicative profile with `H 0 = 1` grows as a pure power: `H(n) = H(1)^n`. The multiplicative mirror
of `additive_nat_linear` — the discrete Gaussian-exponent law. -/
theorem multiplicative_pow (H : ℝ → ℝ) (hmul : ∀ a b, H (a + b) = H a * H b)
    (h0 : H 0 = 1) : ∀ n : ℕ, H (n : ℝ) = H 1 ^ n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ k ih => rw [Nat.cast_succ, hmul, ih, pow_succ]

/-- **The Gaussian exponent.** A positive multiplicative radial profile is `H(n) = exp(a·n)` with
`a = log H(1)` — the explicit Gaussian profile `e^{a·|z|²}` on integer squared-radii. -/
theorem gaussian_exponent (H : ℝ → ℝ) (hmul : ∀ a b, H (a + b) = H a * H b)
    (hpos : 0 < H 1) (h0 : H 0 = 1) (n : ℕ) :
    H (n : ℝ) = Real.exp (Real.log (H 1) * n) := by
  rw [multiplicative_pow H hmul h0 n,
    show Real.log (H 1) * (n : ℝ) = (n : ℝ) * Real.log (H 1) from mul_comm _ _,
    Real.exp_nat_mul, Real.exp_log hpos]

/-- **Maxwell–Herschel capstone.** A positive product density invariant under the rotation/unitary group has
the Gaussian profile `P(n)/P(0) = exp(log(P(1)/P(0))·n)` — the bell curve, with the rotation-invariant
quadratic `|z|²` in the exponent, the SAME square Born uses. -/
theorem gaussian_profile_from_rotation (P : ℝ → ℝ) (hP0 : 0 < P 0) (hP1 : 0 < P 1)
    (hinv : ∀ a b, P a * P b = P (a + b) * P 0) (n : ℕ) :
    P (n : ℝ) / P 0 = Real.exp (Real.log (P 1 / P 0) * n) :=
  gaussian_exponent (fun u => P u / P 0)
    (fun a b => rotation_product_multiplicative P (ne_of_gt hP0) hinv a b)
    (div_pos hP1 hP0) (div_self (ne_of_gt hP0)) n

/-! ### Aspect 2 — the Lorentzian boost no-go: no boost-invariant positive probability norm -/

/-- **Boosts vanish on the light cone.** A boost is a rotation by imaginary rapidity; the light-cone vector
`(1,1)` is an eigenvector with eigenvalue `eᵡ` (since `cosh χ + sinh χ = eᵡ`). So any positively-homogeneous
boost-invariant `F` obeys `F(1,1) = e^{χα}·F(1,1)` for every χ, forcing `F(1,1)=0`. -/
theorem boost_invariant_vanishes_on_lightcone (α : ℝ) (hα : 0 < α) (F : ℝ → ℝ → ℝ)
    (hhom : ∀ (lam t x : ℝ), 0 < lam → F (lam * t) (lam * x) = lam ^ α * F t x)
    (hbi : ∀ (χ t x : ℝ),
      F (t * Real.cosh χ + x * Real.sinh χ) (t * Real.sinh χ + x * Real.cosh χ) = F t x) :
    F 1 1 = 0 := by
  have key : ∀ χ : ℝ, F 1 1 = (Real.exp χ) ^ α * F 1 1 := by
    intro χ
    have hb : F (Real.exp χ) (Real.exp χ) = F 1 1 := by
      have h := hbi χ 1 1
      simp only [one_mul] at h
      rw [add_comm (Real.cosh χ) (Real.sinh χ), Real.sinh_add_cosh] at h
      exact h
    have hh : F (Real.exp χ) (Real.exp χ) = (Real.exp χ) ^ α * F 1 1 := by
      have h := hhom (Real.exp χ) 1 1 (Real.exp_pos χ)
      rwa [mul_one] at h
    calc F 1 1 = F (Real.exp χ) (Real.exp χ) := hb.symm
      _ = (Real.exp χ) ^ α * F 1 1 := hh
  have h1 : F 1 1 = Real.exp α * F 1 1 := by
    have h := key 1; rwa [Real.exp_one_rpow] at h
  have he : (1 : ℝ) < Real.exp α := by
    have := Real.exp_lt_exp.mpr hα; rwa [Real.exp_zero] at this
  have hfac : (Real.exp α - 1) * F 1 1 = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp hfac with hc | hc
  · linarith
  · exact hc

/-- **No boost-invariant positive probability norm.** Since `F` is forced to vanish on the nonzero light-cone
vector `(1,1)`, it cannot be positive on all nonzero vectors. The indefinite Minkowski signature cannot carry
a probability; relativistic Born must come from the unitary (Wigner) representation, which preserves the
positive-definite `Σ|c|²`. The mirror of `RotationBorn.rotation_invariant_iff_exponent_two`. -/
theorem no_boost_invariant_positive_norm (α : ℝ) (hα : 0 < α) (F : ℝ → ℝ → ℝ)
    (hhom : ∀ (lam t x : ℝ), 0 < lam → F (lam * t) (lam * x) = lam ^ α * F t x)
    (hbi : ∀ (χ t x : ℝ),
      F (t * Real.cosh χ + x * Real.sinh χ) (t * Real.sinh χ + x * Real.cosh χ) = F t x) :
    ¬ ∀ t x : ℝ, (t, x) ≠ (0, 0) → 0 < F t x := by
  intro hpos
  have hz := boost_invariant_vanishes_on_lightcone α hα F hhom hbi
  have hp := hpos 1 1 (by simp)
  linarith

end QIQTH.SymmetrySquare
