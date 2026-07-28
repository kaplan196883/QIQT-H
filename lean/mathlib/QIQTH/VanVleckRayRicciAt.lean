/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VanVleckRayRicciAt — the interior-point van-Vleck −Ric ODE `d²/ds²[log det g̃]|_{s₀} = −2Ric − 2Sh + 2n/s₀²`

Interior-point (`s₀ > 0`) reparametrized mirror of the `s = 1` capstone
`vanVleck_ray_secondDeriv_ricci`.  Along the geodesic ray `s ↦ s • v`, the second ray-derivative
of `log det g̃` (the log-determinant of the pullback metric `g̃ = Jᵀ · (g∘exp) · J`, with
`J = expJacobianMat` the REAL exp-map Jacobian) evaluated off the `s = 1` endpoint at a GENERIC
interior point `s₀ > 0` equals
```
  d²/ds²[log det g̃(s • v)] |_{s = s₀}  =  −2·Ric − 2·Sh + 2·n / s₀².
```
The endpoint `+2n` of `vanVleck_ray_secondDeriv_ricci` is here the general `+2n/s₀²` (recovering
`+2n` at `s₀ = 1`); the extra `1/s₀²` is the reparametrization Jacobian of the `−n·log s` rescaling
term, whose second derivative at `s₀` is `n/s₀²`.

## Assembly

Writing `Sg := deriv²(log det g̃∘ray) s₀`, `LJ'' := deriv²(log J∘ray) s₀`,
`LB'' := deriv²(log det B∘ray) s₀`, `LY'' := deriv²(log det Y∘ray) s₀`,
`Lm'' := deriv²(log det(g∘γ)∘ray) s₀`, the three landed generic-point pieces give:

* **split** (`logdet_gtilde_ray_secondDeriv_at`):     `Sg = 2·LJ'' + Lm''`
* **h2 / rescaling** (`logJ_ray_secondDeriv_eq_at`, `s₀ > 0`):  `LJ'' = LB'' + n / s₀²`
* **h3 / frame decomposition** (`deriv2_eventuallyEq_sub_half` at `t := s₀`, `G = log det Y`,
  `H = log det(g∘γ)`):                                 `LB'' = LY'' − ½·Lm''`
* **h4 / frame Raychaudhuri** (CARRIED):               `LY'' = −Ric − Sh`

Chaining and cancelling `Lm''`:
```
  Sg = 2(LB''+n/s₀²) + Lm'' = 2((LY''−½Lm'')+n/s₀²) + Lm'' = 2·LY'' + 2n/s₀² = −2Ric − 2Sh + 2n/s₀².
```
The metric-along-the-geodesic term `Lm''` cancels exactly — the hallmark of the van-Vleck identity.
The final `linarith` treats the four `deriv² F s₀` values as shared atoms and `n/s₀²` as a monomial.

## What this does and does NOT do

* It DISCHARGES the split + h2 + h3 pieces via the three landed generic-point lemmas (genuine
  invocations, shared second-derivative atoms), and combines with the CARRIED frame Raychaudhuri
  result `h4`.
* It is CONDITIONAL on standard, carried frame data: the parallel-transported Jacobi frame matrix
  `Y`, its frame-decomposition germ `hrel` near `s₀`, and the frame Raychaudhuri value `h4`
  (`θ_Y' = −Ric − Sh`).  It also assumes the no-conjugate positivity `hpos` (`0 < J` near `s₀`) and
  the interior condition `hs₀ : 0 < s₀`.
* It does NOT construct the parallel frame, does NOT discharge `h4`/`hrel` (standard Riemannian
  geometric inputs — that is the final assembly with `expFlow_frame_raychaudhuri` at interior `s₀`),
  and is NOT the heat-kernel `a₁ = R/6` coefficient.
-/

import Mathlib
import QIQTH.VanVleckGenericPoint
import QIQTH.Deriv2SubHalf
import QIQTH.JacobianDet

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.JacobianDet
open Matrix

variable {n : ℕ}

set_option maxHeartbeats 1200000

/-- **Interior-point coordinate-connection van-Vleck −Ric ODE.**  The second ray-derivative of
`log det g̃` along the geodesic `s ↦ s • v`, evaluated at a GENERIC interior point `s₀ > 0`, equals
`−2·Ric − 2·Sh + 2·n / s₀²` on the REAL exp-map Jacobian.  Reparametrized (off the `s = 1` endpoint)
mirror of `vanVleck_ray_secondDeriv_ricci`, assembling the generic-point determinant split
(`logdet_gtilde_ray_secondDeriv_at`), the generic-point rescaling second-derivative relation
(`logJ_ray_secondDeriv_eq_at`, using `hs₀ : 0 < s₀`), the frame-decomposition second-derivative
identity (`deriv2_eventuallyEq_sub_half` at `t := s₀`), and the CARRIED frame Raychaudhuri value
`h4` (`θ_Y' = −Ric − Sh`).  Conditional on the carried parallel-frame data `Y`, `hrel`, `h4`, the
no-conjugate positivity `hpos`, and the interior condition `hs₀`. -/
theorem vanVleck_ray_secondDeriv_ricci_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (Y : ℝ → Matrix (Fin n) (Fin n) ℝ) {Ric Sh : ℝ} {s₀ : ℝ} (hs₀ : 0 < s₀)
    -- split hyps:
    (hsplit : (fun s : ℝ => Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))
      =ᶠ[nhds s₀] (fun s => 2 * Real.log (expJacobianDet g gi hC p (s • v))
        + Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det)))
    (hLJev : ∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log (expJacobianDet g gi hC p (u • v))) s)
    (hLmev : ∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (u • v)) a b).det)) s)
    -- h2 hyps:
    (hpos : ∀ᶠ s in nhds s₀, 0 < expJacobianDet g gi hC p (s • v))
    (hLBev : ∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) u).det)) s)
    -- h3 hyps (frame decomposition + Y differentiability):
    (hrel : (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))
      =ᶠ[nhds s₀] (fun s => Real.log ((Y s).det) - (1/2 : ℝ) * Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det)))
    (hYev : ∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log ((Y u).det)) s)
    -- 2nd-deriv values (shared, GENUINE):
    (hLJ2 : HasDerivAt (deriv (fun s : ℝ => Real.log (expJacobianDet g gi hC p (s • v)))) (deriv (deriv (fun s : ℝ => Real.log (expJacobianDet g gi hC p (s • v)))) s₀) s₀)
    (hLm2 : HasDerivAt (deriv (fun s : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))) (deriv (deriv (fun s : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))) s₀) s₀)
    (hLB2 : HasDerivAt (deriv (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))) (deriv (deriv (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))) s₀) s₀)
    (hLY2 : HasDerivAt (deriv (fun s : ℝ => Real.log ((Y s).det))) (deriv (deriv (fun s : ℝ => Real.log ((Y s).det))) s₀) s₀)
    -- h4 (frame Raychaudhuri result, CARRIED genuine):
    (h4 : deriv (deriv (fun s : ℝ => Real.log ((Y s).det))) s₀ = - Ric - Sh) :
    deriv (deriv (fun s : ℝ => Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))) s₀
      = - 2 * Ric - 2 * Sh + 2 * (n : ℝ) / s₀ ^ 2 := by
  -- split: `Sg = 2·LJ'' + Lm''`.
  have e1 := logdet_gtilde_ray_secondDeriv_at g gi hC p v hsplit hLJev hLmev hLJ2 hLm2
  -- h2 / rescaling: `LJ'' = LB'' + n / s₀²`.
  have e2 := logJ_ray_secondDeriv_eq_at g gi hC p v hs₀ hpos hLBev hLJ2 hLB2
  -- h3 / frame decomposition: `LB'' = LY'' − ½·Lm''`.
  have e3 := deriv2_eventuallyEq_sub_half
      (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))
      (fun s : ℝ => Real.log ((Y s).det))
      (fun s : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))
      hrel hYev hLmev hLY2 hLm2
  -- Normalize `2·n/s₀²` to `2·(n/s₀²)` so `linarith` shares the `n/s₀²` monomial with `e2`.
  have hX : (2 : ℝ) * (n : ℝ) / s₀ ^ 2 = 2 * ((n : ℝ) / s₀ ^ 2) := by ring
  rw [hX]
  -- Assemble; `Lm''` cancels, and `h4` supplies `LY'' = −Ric − Sh`.
  linarith [e1, e2, e3, h4]

end QIQTH.ExpMap
