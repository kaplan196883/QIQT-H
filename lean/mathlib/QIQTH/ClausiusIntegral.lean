import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The integrand-matching kernel of Jacobson's Clausius argument

In Jacobson's derivation of the Einstein equation as an equation of state, the **per-null Clausius
relation** `a·T_{ab}k^ak^b = R_{ab}k^ak^b` (for every null `k`) is obtained from the local
equilibrium condition `δQ = T δS` on every local Rindler horizon. There the two sides are *affine-
parameter-weighted integrals along the horizon generator*:

* the heat flux `δQ = −κ ∫ λ · T_{ab}k^ak^b dλ` (the boost Killing field `χ = −κλk` contributes the
  weight `λ`),
* the entropy change `δS = η δA = −η ∫ λ · R_{ab}k^ak^b dλ` (the area change via the Raychaudhuri
  expansion `θ = −λ R_{ab}k^ak^b` near the horizon).

Clausius `δQ = T δS` (with `T = ℏκ/2π`, cancelling `κ`) then equates these `λ`-weighted integrals
**for every choice of integration limit** (every local horizon through the point), and Jacobson's key
move is to conclude that the *integrands* agree pointwise.

This file proves exactly that move, as a clean consequence of the fundamental theorem of calculus:
if `∫₀^ε λ·f(λ) dλ = ∫₀^ε λ·g(λ) dλ` for every `ε`, with `f, g` continuous, then `f = g`. (This is
independent of the horizon measure-theory and of the free-field input behind the Unruh temperature —
it is the bridge from "the Clausius integrals match" to "the stress-energy and Ricci tensors are
proportional on the null cone," which the Sylvester null-cone lemma then turns into the pointwise
tensor equation feeding `jacobson_einstein_equation_of_state`.)
-/

namespace QIQTH.ClausiusIntegral

open MeasureTheory

/-- **Integrand matching (FTC kernel of the Clausius step).** If the affine-parameter-weighted
integrals `∫₀^ε λ·f(λ) dλ` and `∫₀^ε λ·g(λ) dλ` coincide for *every* upper limit `ε` — as Clausius
`δQ = TδS` forces for the heat-flux and area-change integrands along every local horizon generator —
then the integrands coincide: `f = g`. Proof: differentiate both integrals (FTC) to get
`ε·f(ε) = ε·g(ε)`, cancel `ε ≠ 0`, and extend to `0` by continuity (`{0}ᶜ` is dense). -/
theorem integrand_eq_of_weighted_integral_eq {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ ε : ℝ, (∫ l in (0:ℝ)..ε, l * f l) = ∫ l in (0:ℝ)..ε, l * g l) :
    f = g := by
  refine Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hf hg (fun ε hε => ?_)
  have hcf : Continuous (fun l : ℝ => l * f l) := continuous_id.mul hf
  have hcg : Continuous (fun l : ℝ => l * g l) := continuous_id.mul hg
  have hF : HasDerivAt (fun u => ∫ l in (0:ℝ)..u, l * f l) (ε * f ε) ε :=
    intervalIntegral.integral_hasDerivAt_right (hcf.intervalIntegrable _ _)
      (hcf.stronglyMeasurableAtFilter _ _) hcf.continuousAt
  have hG : HasDerivAt (fun u => ∫ l in (0:ℝ)..u, l * g l) (ε * g ε) ε :=
    intervalIntegral.integral_hasDerivAt_right (hcg.intervalIntegrable _ _)
      (hcg.stronglyMeasurableAtFilter _ _) hcg.continuousAt
  rw [funext h] at hF
  have hmul : ε * f ε = ε * g ε := hF.unique hG
  exact mul_left_cancel₀ (by simpa using hε) hmul

/-- **Proportional integrand matching** — the form used in the Clausius step, with the physical
constant `c = ℏη/2π`. If `∫₀^ε λ·f = c·∫₀^ε λ·g` for every `ε` (i.e. `δQ = T δS` along every local
horizon, with `f = T_{ab}k^ak^b`, `g = R_{ab}k^ak^b`), then `f = c·g` pointwise — Jacobson's
conclusion `T_{ab}k^ak^b = (ℏη/2π)·R_{ab}k^ak^b`. -/
theorem integrand_proportional_of_weighted_integral_eq {f g : ℝ → ℝ} (c : ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ ε : ℝ, (∫ l in (0:ℝ)..ε, l * f l) = c * ∫ l in (0:ℝ)..ε, l * g l) :
    f = fun x => c * g x := by
  refine integrand_eq_of_weighted_integral_eq hf (continuous_const.mul hg) (fun ε => ?_)
  rw [h ε, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun l _ => ?_)
  ring

end QIQTH.ClausiusIntegral
