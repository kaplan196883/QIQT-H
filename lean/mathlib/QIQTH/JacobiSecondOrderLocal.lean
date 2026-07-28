/-
  JacobiSecondOrderLocal — the NEIGHBORHOOD-localized second-order Jacobi ODE.

  This LOCALIZES `jacobiVariation_secondOrder` (JacobiEquation.lean, #2) from the global hypothesis
  `∀ τ, IsGeodesicVariationAt g gi γ V τ` to a hypothesis holding only on a NEIGHBORHOOD of `t`:
  `∀ᶠ τ in nhds t, IsGeodesicVariationAt g gi γ V τ`.

  WHY THIS IS THE BRIDGE.  The second-order form `ξ'' = −jacobiOperator` needs the first-order
  variational system only NEAR `t`, not for every time.  This is exactly what is available from the
  exponential flow, which supplies the geodesic-variation system only on `[0,1]` (`HasDerivWithinAt`
  on `Icc 0 1`); at an interior time `t ∈ (0,1)`, `Icc 0 1 ∈ 𝓝 t` upgrades the within-derivative to
  an honest `HasDerivAt`, and the `IsGeodesicVariationAt` hypothesis then holds `∀ᶠ` in `𝓝 t`.

  Proof (mirrors `jacobiVariation_secondOrder`, loosened to `𝓝 t`):
   * `∀ᶠ τ in 𝓝 t, ξ' = η` — the first component of the first-order system, held eventually.
   * hence `deriv ξ =ᶠ[𝓝 t] η` (each `HasDerivAt.deriv` gives `deriv ξ τ = (V τ).2` near `t`).
   * `η'(t) = −jacobiOperator …` — the second component AT `t`, from `hVar.self_of_nhds`.
   * transport `HasDerivAt η (−jacobiOperator) t` back to `deriv ξ` via
     `HasDerivAt.congr_of_eventuallyEq`.

  Still the COORDINATE second-order equation `ξ'' = −jacobiOperator`.  It does NOT prove the curvature
  identification `jacobiOperator = R̃` (the checkpointed #3 core), nor `B'' = −R̃ B`, nor `a₁ = R/6`.
-/
import Mathlib
import QIQTH.JacobiEquation

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **The second-order geodesic-deviation (Jacobi) ODE — neighbourhood-localized.**
    Loosens `jacobiVariation_secondOrder` from `∀ τ, IsGeodesicVariationAt …` to the first-order
    variational system holding only `∀ᶠ` in a neighbourhood of `t`.  Then the position part
    `ξ = (V·).1` still satisfies
        `ξ''(t) = −jacobiOperator g gi (γ t).1 (γ t).2 (ξ t) (η t)`,
    i.e. `HasDerivAt (deriv (fun τ => (V τ).1)) (−jacobiOperator …) t`.

    This is the bridge letting `jacobiVariation_secondOrder` apply to the exponential flow, which
    supplies the geodesic-variation system only on `[0,1]`; at interior `t ∈ (0,1)`, `Icc 0 1 ∈ 𝓝 t`
    upgrades `HasDerivWithinAt` to `HasDerivAt` and the hypothesis holds `∀ᶠ` in `𝓝 t`. -/
theorem jacobiVariation_secondOrder_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hVar : ∀ᶠ τ in nhds t, IsGeodesicVariationAt g gi γ V τ) :
    HasDerivAt (deriv (fun τ => (V τ).1))
      (-jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2) t := by
  -- the `DF` value in Jacobi-operator form at each time.
  have hval : ∀ τ, fderiv ℝ (geodesicField g gi) (γ τ) (V τ)
      = ((V τ).2, -jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) := by
    intro τ
    have := geodesicField_fderiv_eq_jacobiOperator g gi hC (γ τ).1 (γ τ).2 (V τ).1 (V τ).2
    simpa using this
  -- first component of the first-order system: `ξ' = η`, held eventually near `t`.
  have hfst_ev : ∀ᶠ τ in nhds t, HasDerivAt (fun τ' => (V τ').1) ((V τ).2) τ := by
    refine hVar.mono (fun τ hτ => ?_)
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ hτ
    rw [hval τ] at h
    simpa using h
  -- hence `deriv ξ =ᶠ[𝓝 t] η`.
  have heq : deriv (fun τ' => (V τ').1) =ᶠ[nhds t] (fun τ => (V τ).2) :=
    hfst_ev.mono (fun τ h => h.deriv)
  -- second component of the first-order system: `η' = −jacobiOperator` AT `t`.
  have hsnd : HasDerivAt (fun τ' => (V τ').2)
      (-jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2) t := by
    have h := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t
      hVar.self_of_nhds
    rw [hval t] at h
    simpa using h
  -- transport `HasDerivAt η (…) t` back to `deriv ξ` using `deriv ξ =ᶠ[𝓝 t] η`.
  exact hsnd.congr_of_eventuallyEq heq

end QIQTH.ExpMap
