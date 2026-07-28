/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VanVleckRayRicci — the coordinate-connection CAPSTONE `d²/ds²[log det g̃] = −2Ric − 2Sh + 2n`

This closes the van-Vleck coordinate-connection arc (a).  Along the geodesic ray
`s ↦ s • v`, the second ray-derivative of `log det g̃` (the log-determinant of the pullback
metric `g̃ = Jᵀ · (g∘exp) · J`, with `J = expJacobianMat` the REAL exp-map Jacobian) equals
```
  d²/ds²[log det g̃(s • v)] |_{s=1}  =  −2·Ric − 2·Sh + 2·n.
```

## Assembly

Writing `Sg := deriv²(log det g̃∘ray) 1`, `LJ'' := deriv²(log J∘ray) 1`,
`LB'' := deriv²(log det B∘ray) 1`, `LY'' := deriv²(log det Y∘ray) 1`,
`Lm'' := deriv²(log det(g∘γ)∘ray) 1`, the four landed pieces give:

* **split** (`logdet_gtilde_ray_secondDeriv`):      `Sg = 2·LJ'' + Lm''`
* **h2 / rescaling** (`logJ_ray_secondDeriv_eq`):    `LJ'' = LB'' + n`
* **h3 / frame decomposition** (`deriv2_eventuallyEq_sub_half`, instantiated with
  `G = log det Y`, `H = log det(g∘γ)`):              `LB'' = LY'' − ½·Lm''`
* **h4 / frame Raychaudhuri** (CARRIED):             `LY'' = −Ric − Sh`

Chaining and cancelling `Lm''`:
```
  Sg = 2(LB''+n) + Lm'' = 2((LY''−½Lm'')+n) + Lm'' = 2·LY'' + 2n = −2Ric − 2Sh + 2n.
```
The metric-along-the-geodesic term `Lm''` cancels exactly — the hallmark of the van-Vleck
identity.  The final `linarith` treats the four `deriv² F 1` values as shared atoms.

## What this does and does NOT do

* It DISCHARGES the split + h2 + h3 pieces via the three landed lemmas (genuine invocations,
  shared second-derivative atoms), and combines with the CARRIED frame Raychaudhuri result `h4`.
* It is CONDITIONAL on standard, carried frame data: the parallel-transported Jacobi frame
  matrix `Y`, its frame-decomposition germ `hrel` (`log det B = log det Y − ½ log det(g∘γ)`
  near `1`), and the frame Raychaudhuri value `h4` (`θ_Y' = −Ric − Sh`).  It also assumes the
  no-conjugate positivity `hpos` (`0 < J` near `1`).
* It does NOT construct the parallel frame, does NOT discharge `h4`/`hrel` (standard Riemannian
  geometric inputs), and is NOT the heat-kernel `a₁ = R/6` coefficient.
-/

import Mathlib
import QIQTH.VanVleckLogDetSplit
import QIQTH.LogJSecondDerivRescale
import QIQTH.Deriv2SubHalf
import QIQTH.JacobianDet

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.JacobianDet
open Matrix

variable {n : ℕ}

set_option maxHeartbeats 1200000

/-- **Coordinate-connection capstone.**  The second ray-derivative of `log det g̃` along the
geodesic `s ↦ s • v` equals `−2·Ric − 2·Sh + 2·n` on the REAL exp-map Jacobian, assembling the
determinant split (`logdet_gtilde_ray_secondDeriv`), the rescaling second-derivative relation
(`logJ_ray_secondDeriv_eq`), the frame-decomposition second-derivative identity
(`deriv2_eventuallyEq_sub_half`), and the CARRIED frame Raychaudhuri value `h4`
(`θ_Y' = −Ric − Sh`).  Conditional on the carried parallel-frame data `Y`, `hrel`, `h4` and the
no-conjugate positivity `hpos`. -/
theorem vanVleck_ray_secondDeriv_ricci (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (Y : ℝ → Matrix (Fin n) (Fin n) ℝ) {Ric Sh : ℝ}
    -- split hyps:
    (hsplit : (fun s : ℝ => Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))
      =ᶠ[nhds 1] (fun s => 2 * Real.log (expJacobianDet g gi hC p (s • v))
        + Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det)))
    (hLJev : ∀ᶠ s in nhds (1:ℝ), DifferentiableAt ℝ (fun u => Real.log (expJacobianDet g gi hC p (u • v))) s)
    (hLmev : ∀ᶠ s in nhds (1:ℝ), DifferentiableAt ℝ (fun u => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (u • v)) a b).det)) s)
    -- h2 hyps:
    (hpos : ∀ᶠ s in nhds (1:ℝ), 0 < expJacobianDet g gi hC p (s • v))
    (hLBev : ∀ᶠ s in nhds (1:ℝ), DifferentiableAt ℝ (fun u => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) u).det)) s)
    -- h3 hyps (frame decomposition + Y differentiability):
    (hrel : (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))
      =ᶠ[nhds 1] (fun s => Real.log ((Y s).det) - (1/2 : ℝ) * Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det)))
    (hYev : ∀ᶠ s in nhds (1:ℝ), DifferentiableAt ℝ (fun u => Real.log ((Y u).det)) s)
    -- 2nd-deriv values (shared, GENUINE):
    (hLJ2 : HasDerivAt (deriv (fun s : ℝ => Real.log (expJacobianDet g gi hC p (s • v)))) (deriv (deriv (fun s : ℝ => Real.log (expJacobianDet g gi hC p (s • v)))) 1) 1)
    (hLm2 : HasDerivAt (deriv (fun s : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))) (deriv (deriv (fun s : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))) 1) 1)
    (hLB2 : HasDerivAt (deriv (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))) (deriv (deriv (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))) 1) 1)
    (hLY2 : HasDerivAt (deriv (fun s : ℝ => Real.log ((Y s).det))) (deriv (deriv (fun s : ℝ => Real.log ((Y s).det))) 1) 1)
    -- h4 (frame Raychaudhuri result, CARRIED genuine):
    (h4 : deriv (deriv (fun s : ℝ => Real.log ((Y s).det))) 1 = - Ric - Sh) :
    deriv (deriv (fun s : ℝ => Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))) 1
      = - 2 * Ric - 2 * Sh + 2 * (n : ℝ) := by
  -- split: `Sg = 2·LJ'' + Lm''`.
  have e1 := logdet_gtilde_ray_secondDeriv g gi hC p v hsplit hLJev hLmev hLJ2 hLm2
  -- h2 / rescaling: `LJ'' = LB'' + n`.
  have e2 := logJ_ray_secondDeriv_eq g gi hC p v hpos hLBev hLJ2 hLB2
  -- h3 / frame decomposition: `LB'' = LY'' − ½·Lm''`.
  have e3 := deriv2_eventuallyEq_sub_half
      (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))
      (fun s : ℝ => Real.log ((Y s).det))
      (fun s : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))
      hrel hYev hLmev hLY2 hLm2
  -- Assemble; `Lm''` cancels, and `h4` supplies `LY'' = −Ric − Sh`.
  linarith [e1, e2, e3, h4]

end QIQTH.ExpMap
