import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Unruh effect — the geometry of the accelerated two-point function

Jacobson's derivation cites the **Unruh temperature** `T = ℏκ/2π`. Unlike the differential geometry
(now fully machine-checked), Unruh is a quantum-field fact — but it is standard textbook mathematics
(Crispino–Higuchi–Matsas, Rev. Mod. Phys. 80 (2008); Wald, *QFT in Curved Spacetime*; Haag, *Local
Quantum Physics*), so it is formalizable. We machine-check it in its sharpest rigorous form: the
**KMS-thermality of the two-point function along a uniformly accelerated worldline**, taking the
free-field Wightman function as a labeled definition (the field-theory input) and *proving* the
thermal periodicity.

**This increment — the geometric heart (pure hyperbolic trig, no QFT, no complex analysis):** along a
Rindler worldline the Lorentzian interval is `(Δt)² − (Δx)² = (4/a²) sinh²(aΔτ/2)`. This `sinh²`
structure is the entire reason the accelerated correlator is thermal — its imaginary-proper-time
periodicity is the KMS condition at `β = 2π/a`, i.e. `T = a/2π`. (Plan: `paper_strategy/55_Unruh_Plan.md`.)
-/

namespace QIQTH.Unruh

open Real

/-- The hyperbolic identity behind the Unruh `sinh²`: `(sinh A − sinh B)² − (cosh A − cosh B)² =
4 sinh²((A−B)/2)`. The minus sign is the Lorentzian signature; the result is manifestly the squared
interval of two points on a hyperbola, periodic in the imaginary direction. -/
theorem sinh_cosh_diff_sq (A B : ℝ) :
    (sinh A - sinh B) ^ 2 - (cosh A - cosh B) ^ 2 = 4 * sinh ((A - B) / 2) ^ 2 := by
  have hA : cosh A ^ 2 - sinh A ^ 2 = 1 := cosh_sq_sub_sinh_sq A
  have hB : cosh B ^ 2 - sinh B ^ 2 = 1 := cosh_sq_sub_sinh_sq B
  have hcs : cosh (A - B) = cosh A * cosh B - sinh A * sinh B := cosh_sub A B
  have hhalf : cosh (A - B) = 2 * sinh ((A - B) / 2) ^ 2 + 1 := by
    rw [show A - B = 2 * ((A - B) / 2) from by ring, cosh_two_mul, cosh_sq]; ring
  nlinarith [hA, hB, hcs, hhalf]

/-- **Rindler-worldline interval = `(4/a²) sinh²(aΔτ/2)`.** For the uniformly accelerated trajectory
`t(τ) = a⁻¹ sinh aτ`, `x(τ) = a⁻¹ cosh aτ` (proper acceleration `a ≠ 0`), the Lorentzian interval
between proper times `τ, τ'` is `(t−t′)² − (x−x′)² = (4/a²) sinh²(a(τ−τ′)/2)`. This is the geometric
input to the two-point function `W ∝ 1/[(Δt)²−(Δx)²] = −a²/(16π²) · 1/sinh²(aΔτ/2)`. -/
theorem rindler_interval (a τ τ' : ℝ) (ha : a ≠ 0) :
    (a⁻¹ * sinh (a * τ) - a⁻¹ * sinh (a * τ')) ^ 2
        - (a⁻¹ * cosh (a * τ) - a⁻¹ * cosh (a * τ')) ^ 2
      = (4 / a ^ 2) * sinh (a * (τ - τ') / 2) ^ 2 := by
  have h := sinh_cosh_diff_sq (a * τ) (a * τ')
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  field_simp
  rw [show a * τ - a * τ' = a * (τ - τ') from by ring] at h
  nlinarith [h]

/-- **The KMS periodicity — the load-bearing analytic fact.** `sinh²` is periodic with imaginary
period `iπ`: `sinh(w − iπ)² = sinh(w)²` (since `sinh(w − iπ) = −sinh w`). With `w = aΔτ/2`, this says
the pulled-back free-field correlator `Δτ ↦ 1/sinh²(aΔτ/2)` is **periodic in imaginary proper time
with period `2π/a`** — which *is* the **KMS condition at inverse temperature `β = 2π/a`**, i.e.
thermality at the **Unruh temperature `T = a/2π = ℏκ/2π`**. -/
theorem sinh_sq_periodic (w : ℂ) :
    Complex.sinh (w - (Real.pi : ℂ) * Complex.I) ^ 2 = Complex.sinh w ^ 2 := by
  simp [Complex.sinh_sub_pi_mul_I]

/-- The same KMS periodicity stated in **proper time** `Δτ` with the physical period `iβ = 2πi/a`:
shifting `Δτ → Δτ − 2πi/a` leaves the correlator `1/sinh²(aΔτ/2)` invariant. -/
theorem kms_periodicity (a : ℂ) (ha : a ≠ 0) (Δτ : ℂ) :
    Complex.sinh (a * (Δτ - 2 * (Real.pi : ℂ) * Complex.I / a) / 2) ^ 2
      = Complex.sinh (a * Δτ / 2) ^ 2 := by
  have harg : a * (Δτ - 2 * (Real.pi : ℂ) * Complex.I / a) / 2
            = a * Δτ / 2 - (Real.pi : ℂ) * Complex.I := by
    field_simp
  rw [harg, sinh_sq_periodic]

end QIQTH.Unruh
