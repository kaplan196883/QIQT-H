import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Pow

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

open MeasureTheory Filter Topology

/-- **Leading coefficient of an affine-weighted integral.** For continuous `φ`, the local horizon
integral `∫₀^ε λ·φ(λ) dλ` behaves like `½φ(0)·ε²` as `ε → 0⁺`: `(∫₀^ε λ·φ)/ε² → φ(0)/2`. This is the
*leading-order* form of the integral-to-point bridge that Jacobson's argument actually uses — both the
heat flux `δQ = −κ∫λT_{kk}` and the area change `δS ∝ ∫λR_{kk}` (via Raychaudhuri `θ = −λR_{kk}`) have
this `ε²` leading behaviour, and matching their coefficients gives `T_{kk}(0) ∝ R_{kk}(0)` *at the
horizon point*. Proved by l'Hôpital: `(∫₀^ε λφ)'/(ε²)' = (ε·φ(ε))/(2ε) = φ(ε)/2 → φ(0)/2`. -/
theorem weighted_integral_div_sq_tendsto {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Tendsto (fun ε => (∫ l in (0:ℝ)..ε, l * φ l) / ε ^ 2) (𝓝[>] 0) (𝓝 (φ 0 / 2)) := by
  have hcφ : Continuous (fun l : ℝ => l * φ l) := continuous_id.mul hφ
  have hF' : ∀ x : ℝ, HasDerivAt (fun ε => ∫ l in (0:ℝ)..ε, l * φ l) (x * φ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hcφ.intervalIntegrable _ _)
      (hcφ.stronglyMeasurableAtFilter _ _) hcφ.continuousAt
  have hg' : ∀ x : ℝ, HasDerivAt (fun ε => ε ^ 2) (2 * x) x := fun x => by
    simpa using hasDerivAt_pow 2 x
  refine HasDerivAt.lhopital_zero_right_on_Ioo (a := 0) (b := 1) one_pos
    (fun x _ => hF' x) (fun x _ => hg' x) (fun x hx => mul_ne_zero two_ne_zero (ne_of_gt hx.1))
    ?_ ?_ ?_
  · simpa using tendsto_nhdsWithin_of_tendsto_nhds ((hF' 0).continuousAt.tendsto)
  · simpa using tendsto_nhdsWithin_of_tendsto_nhds ((hg' 0).continuousAt.tendsto)
  · have hev : (fun x => (x * φ x) / (2 * x)) =ᶠ[𝓝[>] 0] fun x => φ x / 2 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [mul_comm (2 : ℝ) x, mul_div_mul_left (φ x) 2 (ne_of_gt hx)]
    rw [tendsto_congr' hev]
    exact tendsto_nhdsWithin_of_tendsto_nhds (hφ.continuousAt.tendsto.div_const 2)

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

/-- **Jacobson's conclusion at the horizon point (leading-order Clausius matching).** If the local
horizon integrals satisfy `∫₀^ε λ·f = c·∫₀^ε λ·g` for every `ε` — the Clausius condition `δQ = TδS`
along the generator, with `f = T_{ab}k^ak^b`, `g = R_{ab}k^ak^b`, `c = ℏη/2π` — then the **values at
the horizon point agree**: `f(0) = c·g(0)`, i.e. `T_{ab}k^ak^b = (ℏη/2π)·R_{ab}k^ak^b` *at the point*.
Obtained by matching the `ε²` leading coefficients (`weighted_integral_div_sq_tendsto`) of the two
sides. This is the pointwise null-cone relation that, ranging over all null `k`, the Sylvester lemma
turns into the tensor equation `a·T_{ab} = R_{ab} + φ·g_{ab}` feeding the field equation. -/
theorem value_at_zero_of_weighted_integral_proportional {f g : ℝ → ℝ} (c : ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ ε : ℝ, (∫ l in (0:ℝ)..ε, l * f l) = c * ∫ l in (0:ℝ)..ε, l * g l) :
    f 0 = c * g 0 := by
  have hf2 := weighted_integral_div_sq_tendsto hf
  have hg2 := (weighted_integral_div_sq_tendsto hg).const_mul c
  have hev : (fun ε => (∫ l in (0:ℝ)..ε, l * f l) / ε ^ 2)
      =ᶠ[𝓝[>] 0] fun ε => c * ((∫ l in (0:ℝ)..ε, l * g l) / ε ^ 2) :=
    Eventually.of_forall (fun ε => by
      show (∫ l in (0:ℝ)..ε, l * f l) / ε ^ 2 = c * ((∫ l in (0:ℝ)..ε, l * g l) / ε ^ 2)
      rw [h ε, mul_div_assoc])
  have hval : f 0 / 2 = c * (g 0 / 2) := tendsto_nhds_unique_of_eventuallyEq hf2 hg2 hev
  linarith

end QIQTH.ClausiusIntegral
