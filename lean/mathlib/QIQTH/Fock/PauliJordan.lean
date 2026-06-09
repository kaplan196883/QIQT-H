/-
  K-localization — toward the Pauli–Jordan spacelike-support theorem (the single remaining input for the
  literal OP3b prize).  GPT-5.5-pro flagged this as the genuine analytic wall: the localized commutator
  form `Im⟪K f, K g⟫` must vanish for spacelike-separated supports, and the naive route through the
  pointwise kernel `Δ_m(z) = ∫_θ sin(η(p_m θ, z)) dθ` is *not* absolutely convergent.

  This file proves the STRUCTURAL BACKBONE of that theorem, axiom-free and `sorry`-free:

    1. `Kform_boost_invariant` — the localized symplectic (commutator) form is Lorentz-boost invariant,
       `Kform m (β_a f) (β_a g) = Kform m f g`.  (Microcausality is a boost-invariant statement.)
    2. `minkowskiDot_massShell` — the explicit phase `η(p_m θ, z) = m (z₀ cosh θ − z₁ sinh θ)`.
    3. `minkowskiDot_massShell_spacelike` — the hyperbolic REPARAMETRIZATION: for a spacelike `z`
       (`z₁² > z₀²`) the phase is a single hyperbolic sine `η(p_m θ, z) = c · sinh(θ − φ)` — the identity
       that turns the kernel into an ODD function of `θ − φ`, the source of the cancellation.
    4. `pauliJordan_trunc_equalTime_zero` — the clean EXACT case: for an equal-time separation (`z₀ = 0`)
       the truncated kernel `∫_{−R}^{R} sin(η(p_m θ, z)) dθ = 0` for *every* `R` (odd integrand).

  The remaining steps to the full theorem (documented, NOT yet formalized) are: the general-spacelike
  pointwise limit `lim_R ∫_{−R}^{R} sin(η(p_m θ,z)) dθ = 0` (odd symmetry of `c·sinh(θ−φ)` via (3) + an
  oscillatory `1/cosh` integration-by-parts tail bound for the shifted endpoints), and the bilinear assembly
  (finite-`R` Fubini on compact supports + dominated convergence using `r ≥ r₀ > 0` on compact
  spacelike-separated sets).
-/
import QIQTH.Fock.Localization
import Mathlib.Analysis.SpecialFunctions.Arsinh

noncomputable section

open Real MeasureTheory

namespace QIQTH.Fock.Localization

/-! ### 1. Boost-invariance of the localized symplectic (commutator) form -/

/-- **The localized symplectic form is Lorentz-boost invariant**:
`Kform m (β_a f) (β_a g) = Kform m f g`.  Microcausality (`Im Kform = 0` for spacelike separation) is
therefore a boost-invariant statement.  Immediate from the amplitude-level boost-covariance `Krep_boost`
(boost = rapidity translation `θ ↦ θ + a`) and the translation invariance of Lebesgue measure on `ℝ`. -/
theorem Kform_boost_invariant (m a : ℝ) (f g : V → ℂ) :
    Kform m (boostTest a f) (boostTest a g) = Kform m f g := by
  simp only [Kform, Krep_boost]
  exact integral_add_right_eq_self
    (fun θ => (starRingEnd ℂ) (Krep m f θ) * Krep m g θ) a

/-! ### 2. The explicit mass-shell phase -/

/-- **The mass-shell phase**: `η(p_m θ, z) = m (z₀ cosh θ − z₁ sinh θ)`. -/
theorem minkowskiDot_massShell (m θ : ℝ) (z : V) :
    minkowskiDot (massShell m θ) z = m * (z 0 * Real.cosh θ - z 1 * Real.sinh θ) := by
  simp only [minkowskiDot, massShell_zero, massShell_one]
  ring

/-! ### 3. The hyperbolic reparametrization for spacelike separations -/

/-- A separation `z` is **spacelike** when `z₁² > z₀²` (i.e. `minkowskiSq z = z₀² − z₁² < 0`). -/
def Spacelike (z : V) : Prop := z 0 ^ 2 < z 1 ^ 2

/-- **The hyperbolic reparametrization.**  For a spacelike `z` the mass-shell phase is a single hyperbolic
sine: there are `c, φ` with `η(p_m θ, z) = c · sinh(θ − φ)` for all `θ`.  Hence as a function of `θ − φ` the
kernel `sin(η(p_m θ, z))` is ODD — the structural source of the Pauli–Jordan cancellation in the spacelike
region.  (Here `c = − m √(z₁²−z₀²)·sign z₁` and `φ` is the rapidity with `tanh φ = z₀/z₁`.) -/
theorem minkowskiDot_massShell_spacelike (m : ℝ) {z : V} (hz : Spacelike z) :
    ∃ c φ : ℝ, ∀ θ, minkowskiDot (massShell m θ) z = c * Real.sinh (θ - φ) := by
  have hz' : z 0 ^ 2 < z 1 ^ 2 := hz
  have hz1sq : 0 < z 1 ^ 2 := lt_of_le_of_lt (sq_nonneg _) hz'
  set r : ℝ := Real.sqrt (z 1 ^ 2 - z 0 ^ 2) with hrdef
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hrne : r ≠ 0 := hrpos.ne'
  have hrsq : r ^ 2 = z 1 ^ 2 - z 0 ^ 2 := Real.sq_sqrt (by linarith)
  -- sign of z₁
  set s : ℝ := if 0 ≤ z 1 then 1 else -1 with hsdef
  have hssq : s * s = 1 := by rw [hsdef]; split_ifs <;> ring
  have hs2 : s ^ 2 = 1 := by rw [pow_two]; exact hssq
  have hsz1' : |z 1| = s * z 1 := by
    rw [hsdef]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (lt_of_not_ge h), neg_one_mul]
  have hsz0sq : (s * z 0) ^ 2 = z 0 ^ 2 := by rw [mul_pow, hs2, one_mul]
  -- rapidity φ with sinh φ = s z₀ / r, cosh φ = |z₁| / r
  set φ : ℝ := Real.arsinh (s * z 0 / r) with hφdef
  have hsinhφ : Real.sinh φ = s * z 0 / r := Real.sinh_arsinh _
  have hcoshφ : Real.cosh φ = |z 1| / r := by
    rw [hφdef, Real.cosh_arsinh,
      show (1 : ℝ) + (s * z 0 / r) ^ 2 = (z 1 / r) ^ 2 by
        rw [div_pow, hsz0sq, div_pow]; field_simp; linarith [hrsq],
      Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hrpos]
  have hrcosh : r * Real.cosh φ = |z 1| := by rw [hcoshφ]; field_simp
  have hrsinh : r * Real.sinh φ = s * z 0 := by rw [hsinhφ]; field_simp
  refine ⟨-(m * s * r), φ, fun θ => ?_⟩
  rw [minkowskiDot_massShell, Real.sinh_sub,
    show -(m * s * r) * (Real.sinh θ * Real.cosh φ - Real.cosh θ * Real.sinh φ)
      = -(m * s) * (Real.sinh θ * (r * Real.cosh φ) - Real.cosh θ * (r * Real.sinh φ)) by ring,
    hrcosh, hrsinh, hsz1']
  linear_combination (-(m * (z 0 * Real.cosh θ - z 1 * Real.sinh θ))) * hssq

/-! ### 4. The exact equal-time vanishing of the truncated kernel -/

/-- **Equal-time vanishing.**  For an equal-time separation (`z₀ = 0`) the truncated Pauli–Jordan kernel
`∫_{−R}^{R} sin(η(p_m θ, z)) dθ = 0` for *every* `R` — the integrand `sin(η(p_m θ,z)) = sin(−m z₁ sinh θ)`
is ODD in `θ`, so the symmetric integral vanishes exactly (no limit needed).  This is the microcausality
cancellation in its cleanest form. -/
theorem pauliJordan_trunc_equalTime_zero (m R : ℝ) {z : V} (hz0 : z 0 = 0) :
    (∫ θ in (-R)..R, Real.sin (minkowskiDot (massShell m θ) z)) = 0 := by
  set g : ℝ → ℝ := fun θ => Real.sin (minkowskiDot (massShell m θ) z) with hg
  -- the integrand is odd
  have hodd : ∀ θ, g (-θ) = - g θ := by
    intro θ
    have e1 : minkowskiDot (massShell m (-θ)) z = m * z 1 * Real.sinh θ := by
      rw [minkowskiDot_massShell, hz0, Real.cosh_neg, Real.sinh_neg]; ring
    have e2 : minkowskiDot (massShell m θ) z = -(m * z 1 * Real.sinh θ) := by
      rw [minkowskiDot_massShell, hz0]; ring
    simp only [hg]
    rw [e1, e2, Real.sin_neg, neg_neg]
  -- ∫_{-R}^R g(-θ) dθ = ∫_{-R}^R g θ dθ  (comp_neg on the symmetric interval)
  have h1 : (∫ θ in (-R)..R, g (-θ)) = ∫ θ in (-R)..R, g θ := by
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R) g
    simp only [neg_neg] at h
    exact h
  -- but g(-θ) = -g θ, so the LHS is -∫ g
  have h2 : (∫ θ in (-R)..R, g (-θ)) = -∫ θ in (-R)..R, g θ := by
    rw [show (fun θ => g (-θ)) = (fun θ => -g θ) from funext hodd,
      intervalIntegral.integral_neg]
  -- hence ∫ g = -∫ g, so ∫ g = 0
  have h3 : (∫ θ in (-R)..R, g θ) = -∫ θ in (-R)..R, g θ := h1.symm.trans h2
  linarith

end QIQTH.Fock.Localization
