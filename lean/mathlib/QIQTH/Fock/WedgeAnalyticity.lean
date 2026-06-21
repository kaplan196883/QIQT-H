/-
  Wedge-mode analyticity (Item A, Phase A1 of QIQT_GR_DISCHARGE_PLAN.md).

  The analytic continuation of the localized rapidity amplitude `Krep m f θ` to complex rapidity
  `ζ = θ + iλ`, toward the free-field Hardy-space proof of `StripKMSrvd(boostUnitary, 𝒦_W)` (the
  Bisognano–Wichmann KMS property). The engine is the complexified mass shell `p_m(ζ) = (m cosh ζ, m sinh ζ)`
  with the identity `p_m(θ+iπ) = −p_m(θ)`, and the wedge-damping bound `Re(−i·p_m(θ+iλ)·x) < 0` for
  `x ∈ rightWedge`, `0 < λ < π`.

  A1a (this file, first increment): the complexified objects (`minkowskiDotℂ`, `massShellℂ`, `KrepCont`) and
  their agreement with the real-rapidity `Krep` on the real axis.
-/
import QIQTH.Fock.Localization

noncomputable section

open MeasureTheory Complex

namespace QIQTH.Fock.WedgeAnalyticity

open QIQTH.Fock.Localization

/-- **Complex Minkowski pairing** `p · x = p₀x₀ − p₁x₁` for a complex momentum `p` and a real point `x`. -/
def minkowskiDotℂ (p : Fin 2 → ℂ) (x : V) : ℂ := p 0 * (x 0 : ℂ) - p 1 * (x 1 : ℂ)

/-- **The complexified mass shell** `p_m(ζ) = (m cosh ζ, m sinh ζ)` (`ℂ`-valued momentum at complex
    rapidity `ζ`). On the real axis it is `massShell m θ`; it satisfies `p_m(ζ+iπ) = −p_m(ζ)`. -/
def massShellℂ (m : ℝ) (ζ : ℂ) : Fin 2 → ℂ := ![(m : ℂ) * Complex.cosh ζ, (m : ℂ) * Complex.sinh ζ]

/-- **The analytically continued localized amplitude** `(K_ℂ f)(ζ) = 2^{-1/2}·∫ e^{−i·p_m(ζ)·x} f(x) dx`. -/
def KrepCont (m : ℝ) (f : V → ℂ) (ζ : ℂ) : ℂ :=
  (1 / Real.sqrt 2 : ℂ) * ∫ x, Complex.exp (-Complex.I * minkowskiDotℂ (massShellℂ m ζ) x) * f x

@[simp] theorem massShellℂ_zero (m : ℝ) (ζ : ℂ) : massShellℂ m ζ 0 = (m : ℂ) * Complex.cosh ζ := rfl

@[simp] theorem massShellℂ_one (m : ℝ) (ζ : ℂ) : massShellℂ m ζ 1 = (m : ℂ) * Complex.sinh ζ := rfl

/-- On the real axis the complexified mass shell is the real one: `p_m(θ) = massShell m θ` (cast to `ℂ`). -/
theorem massShellℂ_ofReal (m θ : ℝ) (i : Fin 2) :
    massShellℂ m (θ : ℂ) i = ((massShell m θ i : ℝ) : ℂ) := by
  fin_cases i <;>
    simp [massShellℂ, massShell, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.ofReal_mul]

/-- **The `iπ`-shift identity `p_m(ζ + iπ) = −p_m(ζ)`** — the analytic engine of the boundary conjugation
    `ψ_f(θ+iπ) = conj(ψ_f(θ))`. Immediate from `cosh(ζ+iπ)=−cosh ζ`, `sinh(ζ+iπ)=−sinh ζ`. -/
theorem massShellℂ_add_pi_I (m : ℝ) (ζ : ℂ) :
    massShellℂ m (ζ + (Real.pi : ℂ) * Complex.I) = -massShellℂ m ζ := by
  funext i
  fin_cases i <;>
    simp [massShellℂ, Complex.cosh_add_pi_mul_I, Complex.sinh_add_pi_mul_I, mul_neg]

/-- The complex pairing on the real-axis mass shell is the real pairing (cast to `ℂ`). -/
theorem minkowskiDotℂ_massShellℂ_ofReal (m θ : ℝ) (x : V) :
    minkowskiDotℂ (massShellℂ m (θ : ℂ)) x = ((minkowskiDot (massShell m θ) x : ℝ) : ℂ) := by
  simp only [minkowskiDotℂ, minkowskiDot, massShellℂ_ofReal, Complex.ofReal_sub, Complex.ofReal_mul]

/-- **A1a — real-axis agreement.** The continued amplitude restricted to the real rapidity axis is the
    original localized amplitude: `(K_ℂ f)(θ) = (K f)(θ)`. -/
theorem KrepCont_ofReal (m : ℝ) (f : V → ℂ) (θ : ℝ) :
    KrepCont m f (θ : ℂ) = Krep m f θ := by
  rw [KrepCont, Krep, minkowskiFourier]
  refine congrArg (fun z => (1 / Real.sqrt 2 : ℂ) * z)
    (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
  simp only [minkowskiDotℂ_massShellℂ_ofReal]

end QIQTH.Fock.WedgeAnalyticity
