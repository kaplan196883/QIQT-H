/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Deriv2SubHalf — general second derivative of an eventual `F = G − ½H` combination

The **h3 tool** of the van-Vleck coordinate-connection capstone.  A pure real-analysis
identity: if a function `FB` agrees near `t` with `s ↦ G s − ½ H s`, and `G`, `H` are
eventually differentiable near `t` with second derivatives `G''`, `H''` at `t`, then
```
  deriv²(FB) t  =  G'' − ½ H''.
```

Instantiated with `FB = log det B∘ray`, `G = log det Y∘ray`, `H = log det(g∘γ)∘ray`
(from the frame decomposition `B = E·Yᵀ`, `det E = 1/√det g`, hence
`log det B = log det Y − ½ log det(g∘γ)`), this delivers `θ_B' = θ_Y' − ½ Lg''`.

## What this does and does NOT do

* It is a general calculus identity: the second derivative of an eventual `G − ½H`.
* It is **NOT** the frame decomposition `B = E·Yᵀ` itself, NOT the `−2 Ric` van-Vleck
  radial ODE, and NOT the heat-kernel coefficient `a₁ = R/6`.

Mirrors the proof structure of `QIQTH.ExpMap.logJ_ray_secondDeriv_eq`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib

namespace QIQTH.ExpMap

set_option maxHeartbeats 400000

/-- **General second derivative of an eventual `F = G − ½H` combination.**

If `FB` agrees on `𝓝 t` with `s ↦ G s − ½ H s`, `G` and `H` are eventually differentiable
near `t`, and `G''`, `H''` are the second derivatives of `G`, `H` at `t` (as `HasDerivAt`s of
their first derivatives), then
```
  deriv (deriv FB) t  =  G'' − ½ H''.
```
The h3 tool of the van-Vleck coordinate-connection capstone: with
`log det B = log det Y − ½ log det(g∘γ)` it gives `θ_B' = θ_Y' − ½ Lg''`.  A general
calculus identity; NOT the frame decomposition, NOT the `−2 Ric` van-Vleck ODE, NOT
`a₁ = R/6`. -/
theorem deriv2_eventuallyEq_sub_half (FB G H : ℝ → ℝ) {t : ℝ} {G'' H'' : ℝ}
    (hrel : FB =ᶠ[nhds t] fun s => G s - (1/2 : ℝ) * H s)
    (hGev : ∀ᶠ s in nhds t, DifferentiableAt ℝ G s)
    (hHev : ∀ᶠ s in nhds t, DifferentiableAt ℝ H s)
    (hG2 : HasDerivAt (deriv G) G'' t)
    (hH2 : HasDerivAt (deriv H) H'' t) :
    deriv (deriv FB) t = G'' - (1/2 : ℝ) * H'' := by
  -- FIRST derivative on `𝓝 t`: `deriv FB =ᶠ deriv G − ½·deriv H`.
  have hd1 : deriv FB =ᶠ[nhds t] fun s => deriv G s - (1/2 : ℝ) * deriv H s := by
    filter_upwards [hrel.eventually_nhds, hGev, hHev] with s hrel_s hGs hHs
    show deriv FB s = deriv G s - (1/2 : ℝ) * deriv H s
    -- Local germ equality ⇒ equal `deriv` at `s`.
    rw [Filter.EventuallyEq.deriv_eq hrel_s]
    -- Compute `deriv (fun u => G u − ½·H u) s = deriv G s − ½·deriv H s`.
    have hG_d : HasDerivAt G (deriv G s) s := hGs.hasDerivAt
    have hH_d : HasDerivAt H (deriv H s) s := hHs.hasDerivAt
    have hHc : HasDerivAt (fun u : ℝ => (1/2 : ℝ) * H u) ((1/2 : ℝ) * deriv H s) s :=
      hH_d.const_mul (1/2 : ℝ)
    exact (hG_d.sub hHc).deriv
  -- SECOND derivative at `t`: differentiate the RHS across `hd1`.
  rw [Filter.EventuallyEq.deriv_eq hd1]
  have hHc2 : HasDerivAt (fun s : ℝ => (1/2 : ℝ) * deriv H s) ((1/2 : ℝ) * H'') t :=
    hH2.const_mul (1/2 : ℝ)
  exact (hG2.sub hHc2).deriv

end QIQTH.ExpMap
