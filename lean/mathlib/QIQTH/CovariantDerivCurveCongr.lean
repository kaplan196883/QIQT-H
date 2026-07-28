/-
  CovariantDerivCurveCongr — germ-invariance of the along-a-curve covariant derivative
  in the CURVE argument.

  The covariant derivative `covariantDerivAlong g gi γ ξ τ` reads the curve `γ` in exactly
  two places at the parameter `τ`: the Christoffel evaluation point `γ τ` and the velocity
  `deriv (fun s => γ s j) τ`.  Both are determined by the germ of `γ` at `τ`.  Hence if two
  curves agree on a neighbourhood of `τ` (`γ₁ =ᶠ[𝓝 τ] γ₂`) their covariant derivatives of the
  SAME field `ξ` coincide at `τ`.

  This is the connector used to transport parallel-frame data (built along the
  parallel-transport curve `Γc.1`) onto `expTube` via the geodesic alignment
  `Γc.1 =ᶠ expTube.1`.  Purely a congruence lemma; NOT a₁ = R/6.

  Axiom-clean, no `sorry`, no new axioms, no vacuous hypotheses: `hcurve` is a genuine
  `EventuallyEq`, supplying BOTH the pointwise value (`eq_of_nhds`) and the derivative
  (`deriv_eq`) that the definition consumes.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.CovariantJacobi

namespace QIQTH.ExpMap

open QIQTH.Curvature
open Finset Topology

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **Germ-invariance of `covariantDerivAlong` in the curve argument.**
    If `γ₁` and `γ₂` agree on a neighbourhood of `τ`, then the covariant derivative of the same
    field `ξ` along each curve agrees at `τ`.  Both the Christoffel base point `γ τ` and the
    velocity `deriv (fun s => γ s j) τ` depend only on the germ of `γ` at `τ`. -/
theorem covariantDerivAlong_curve_congr (g gi : Point n → Fin n → Fin n → ℝ)
    {γ₁ γ₂ : ℝ → Point n} {τ : ℝ} (ξ : ℝ → Point n)
    (hcurve : γ₁ =ᶠ[nhds τ] γ₂) :
    covariantDerivAlong g gi γ₁ ξ τ = covariantDerivAlong g gi γ₂ ξ τ := by
  -- velocity germ-equality, componentwise
  have hd : ∀ j : Fin n, deriv (fun s => γ₁ s j) τ = deriv (fun s => γ₂ s j) τ := by
    intro j
    have hj : (fun s => γ₁ s j) =ᶠ[nhds τ] (fun s => γ₂ s j) :=
      hcurve.mono (fun s hs => by dsimp only; rw [hs])
    exact hj.deriv_eq
  -- base-point equality
  have hpt : γ₁ τ = γ₂ τ := hcurve.eq_of_nhds
  funext i
  simp only [covariantDerivAlong_apply]
  simp_rw [hpt, hd]

end QIQTH.ExpMap
