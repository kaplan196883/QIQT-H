/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# LogJSecondDerivRescale — the rescaling SECOND-derivative relation `LJ'' = LB'' + n`

Along the ray `s ↦ s • v`, the exp-map Jacobian `J(s • v)` and the concrete matrix Jacobi
field `B s := s • D(exp_p)_{s•v}` are tied by the standard rescaling (discharged, for THIS `B`,
in `QIQTH.JacobianRegularity.hresc_of_pos`):
```
  log J(s • v) =ᶠ[𝓝 1]  log (det (B s)) − n · log s.
```
This file differentiates that identity **twice at `s = 1`** to obtain the clean second-derivative
relation
```
  deriv²(log J∘ray) 1  =  deriv²(log det B∘ray) 1  +  n,
```
i.e. `LJ'' = LB'' + n`.  The computation:

* Differentiate once on `𝓝 1` (`Filter.EventuallyEq.deriv_eq`, `Real.hasDerivAt_log`):
  `deriv(log J∘ray) =ᶠ[𝓝 1]  fun s => deriv(log det B∘ray) s − n · s⁻¹`  (`s > 0` near `1`).
* Differentiate again at `1` (`Filter.EventuallyEq.hasDerivAt_iff`, `hasDerivAt_inv`):
  `deriv(fun s => s⁻¹) 1 = −(1²)⁻¹ = −1`, so `LJ'' = LB'' − n·(−1) = LB'' + n`.

## What this does and does NOT do

* It is the pure **rescaling** bookkeeping `log J(s•v) = log det B(s) − n log s` differentiated
  twice, conditional ONLY on `hpos` (no-conjugate-point positivity) plus the GENUINE carried
  eventual-differentiability / second-derivative data for the two pieces.
* It does **NOT** prove the full van-Vleck `−2 Ric` radial ODE, the matrix Jacobi identity
  `B'' = −R̃ B`, or the heat-kernel coefficient `a₁ = R/6`.  It is a discharge piece of the
  van-Vleck coordinate-connection capstone, feeding `LJ'' = θ_B' + n`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.JacobianDet
import QIQTH.JacobiRescale

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.ExpMap QIQTH.JacobianDet QIQTH.JacobianRegularity

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **The rescaling second-derivative relation `LJ'' = LB'' + n`.**

Differentiating the ray-rescaling `log J(s•v) =ᶠ[𝓝 1] log det B(s) − n·log s`
(`hresc_of_pos`, with `B s = s • expJacobianMat g gi hC p (s • v)`) twice at `s = 1` gives
```
  deriv²(log J∘ray) 1  =  deriv²(log det B∘ray) 1  +  n.
```
The carried data are all GENUINE analytic facts near `s = 1`: `hpos` (positivity of `J`),
`hLBev` (eventual differentiability of `log det B∘ray`), and `hLJ2`/`hLB2` (the two second
derivatives as `HasDerivAt`s of the first derivatives at `1`).  A discharge piece of the
van-Vleck coordinate-connection capstone; NOT the `−2 Ric` van-Vleck ODE, `B'' = −R̃ B`, or
`a₁ = R/6`. -/
theorem logJ_ray_secondDeriv_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (hpos : ∀ᶠ s in nhds (1:ℝ), 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v))
    (hLBev : ∀ᶠ s in nhds (1:ℝ),
      DifferentiableAt ℝ (fun u : ℝ =>
        Real.log (((fun t : ℝ => t • QIQTH.JacobianDet.expJacobianMat g gi hC p (t • v)) u).det)) s)
    {LJ'' LB'' : ℝ}
    (hLJ2 : HasDerivAt (deriv (fun s : ℝ =>
        Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)))) LJ'' 1)
    (hLB2 : HasDerivAt (deriv (fun s : ℝ =>
        Real.log (((fun t : ℝ => t • QIQTH.JacobianDet.expJacobianMat g gi hC p (t • v)) s).det)))
        LB'' 1) :
    LJ'' = LB'' + (n : ℝ) := by
  -- The rescaling germ `log J(s•v) =ᶠ[𝓝 1] log det B(s) − n·log s`.
  have hresc := QIQTH.JacobianRegularity.hresc_of_pos g gi hC p v hpos
  -- Fold the two ray-functions.
  set f : ℝ → ℝ := fun s => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)) with hf_def
  set h : ℝ → ℝ := fun s =>
    Real.log (((fun t : ℝ => t • QIQTH.JacobianDet.expJacobianMat g gi hC p (t • v)) s).det) with hh_def
  -- `s > 0` near `1`.
  have hs_pos : ∀ᶠ s in nhds (1:ℝ), (0:ℝ) < s :=
    (isOpen_Ioi).eventually_mem (by norm_num : (1:ℝ) ∈ Set.Ioi (0:ℝ))
  -- FIRST derivative on `𝓝 1`: `deriv f =ᶠ deriv h − n·(·)⁻¹`.
  have hd1 : deriv f =ᶠ[nhds (1:ℝ)] fun s => deriv h s - (n : ℝ) * s⁻¹ := by
    filter_upwards [hresc.eventually_nhds, hs_pos, hLBev] with s hres_s hspos hdiff_s
    show deriv f s = deriv h s - (n : ℝ) * s⁻¹
    -- Local germ equality ⇒ equal `deriv` at `s`.
    rw [Filter.EventuallyEq.deriv_eq hres_s]
    -- Compute `deriv (fun u => h u − n·log u) s = deriv h s − n·s⁻¹`.
    have hh_d : HasDerivAt h (deriv h s) s := hdiff_s.hasDerivAt
    have hlog : HasDerivAt (fun u : ℝ => Real.log u) s⁻¹ s :=
      Real.hasDerivAt_log (ne_of_gt hspos)
    have hnlog : HasDerivAt (fun u : ℝ => (n : ℝ) * Real.log u) ((n : ℝ) * s⁻¹) s :=
      hlog.const_mul (n : ℝ)
    exact (hh_d.sub hnlog).deriv
  -- SECOND derivative at `1`: transport `hLJ2` across `hd1`, then differentiate the RHS.
  have hLJ2' : HasDerivAt (fun s => deriv h s - (n : ℝ) * s⁻¹) LJ'' 1 :=
    hd1.hasDerivAt_iff.mp hLJ2
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-((1:ℝ) ^ 2)⁻¹) 1 :=
    hasDerivAt_inv (by norm_num : (1:ℝ) ≠ 0)
  have hninv : HasDerivAt (fun s : ℝ => (n : ℝ) * s⁻¹) ((n : ℝ) * -((1:ℝ) ^ 2)⁻¹) 1 :=
    hinv.const_mul (n : ℝ)
  have hRHS : HasDerivAt (fun s => deriv h s - (n : ℝ) * s⁻¹)
      (LB'' - (n : ℝ) * -((1:ℝ) ^ 2)⁻¹) 1 := hLB2.sub hninv
  -- Uniqueness of the derivative fixes `LJ''`, then `−(1²)⁻¹ = −1`.
  have hEq : LJ'' = LB'' - (n : ℝ) * -((1:ℝ) ^ 2)⁻¹ := hLJ2'.unique hRHS
  rw [hEq]; ring

end QIQTH.ExpMap
