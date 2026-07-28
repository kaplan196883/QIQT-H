import Mathlib
import QIQTH.RaychaudhuriLogDet

/-!
# Second derivative of `log det Y` = derivative of the Raychaudhuri trace

This file records the calculus connector that upgrades the first-derivative bridge
`QIQTH.ExpMap.raychaudhuri_logdet_firstderiv` (`d/ds log det Y = tr(Y' Y⁻¹) = θ_Y`) to a
statement about the *second* derivative of the log-determinant potential.

Concretely, if on a neighbourhood of `s₀` the matrix field `Y` is differentiable with derivative
`Y'` and invertible, then
```
  d²/ds² (log det Y) s₀ = d/ds (tr (Y'(s) (Y s)⁻¹)) s₀ = θ_Y' s₀.
```
The proof is a two-step calculus identity: the first derivative agrees with the Raychaudhuri
trace on a whole neighbourhood (`raychaudhuri_logdet_firstderiv` at each point), and
`Filter.EventuallyEq.deriv_eq` transports that eventual equality through `deriv`.

This is the connector giving the van-Vleck `h4` (`d²(log det Y) s₀ = −Ric − Sh`) from the frame
Raychaudhuri equation `θ_Y' = −Ric − Sh`. It is a general calculus identity only — NOT the frame
Raychaudhuri equation itself, NOT the van-Vleck discharge, NOT `a₁ = R/6`.
-/

namespace QIQTH.ExpMap

open Matrix

set_option maxHeartbeats 400000

variable {n : ℕ}

/-- **Second derivative of `log det Y` = derivative of the Raychaudhuri trace `θ_Y = tr(Y' Y⁻¹)`.**

If, on a neighbourhood of `s₀`, the matrix field `Y` has derivative `Y'` and is invertible, then
```
  d²/ds² (log det Y) s₀ = d/ds (tr (Y'(s) (Y s)⁻¹)) s₀.
```

This follows from `raychaudhuri_logdet_firstderiv` (which gives, at each point of the neighbourhood,
`deriv (fun s => log (Y s).det) s = tr (Y'(s) (Y s)⁻¹)`) together with `EventuallyEq.deriv_eq`
transporting that eventual equality through `deriv`.

It is the calculus connector supplying the van-Vleck `h4` (`d²(log det Y) s₀ = −Ric − Sh`) from the
frame Raychaudhuri equation `θ_Y' = −Ric − Sh`. A general calculus identity — NOT the frame
Raychaudhuri itself, NOT the discharge, NOT `a₁ = R/6`. -/
theorem logdet_secondDeriv_eq_trace_deriv (Y Y' : ℝ → Matrix (Fin n) (Fin n) ℝ) {s₀ : ℝ}
    (hY : ∀ᶠ s in nhds s₀, HasDerivAt Y (Y' s) s)
    (hu : ∀ᶠ s in nhds s₀, IsUnit (Y s)) :
    deriv (deriv (fun s => Real.log ((Y s).det))) s₀
      = deriv (fun s => ((Y' s) * (Y s)⁻¹).trace) s₀ := by
  have heq : deriv (fun s => Real.log ((Y s).det))
      =ᶠ[nhds s₀] (fun s => ((Y' s) * (Y s)⁻¹).trace) := by
    filter_upwards [hY, hu] with s hYs hus
    exact (raychaudhuri_logdet_firstderiv Y Y' hYs hus).deriv
  exact heq.deriv_eq

end QIQTH.ExpMap
