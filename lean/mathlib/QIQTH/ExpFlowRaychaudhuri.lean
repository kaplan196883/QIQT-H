/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Specialization of the frame `−Ric` Raychaudhuri to the actual exp geodesic `γ = expTube`.

This file SPECIALIZES the frame-route capstone `frame_raychaudhuri_ricci_nhds`
(FrameRaychaudhuri.lean) to the ACTUAL exponential geodesic tube `γ = expTube g gi hC p v`,
evaluated at an interior parameter `t ∈ (0,1)`.

## What is discharged vs carried

* `hγ` (the geodesic ODE `γ' = geodesicField g gi (γ τ)`, held `∀ᶠ` near `t`) is **DISCHARGED**
  here from `expTube_spec`: the confined tube solves the geodesic ODE on `(-2,2) ⊇ 𝓝 t`
  (since `t ∈ (0,1) ⊆ (-2,2)`), and `Ioo_mem_nhds` promotes the pointwise statement on `(-2,2)`
  to `∀ᶠ τ in 𝓝 t`.
* `hVar` (the frame Jacobi fields `V j` are geodesic variations) and ALL of the parallel
  orthonormal FRAME data (`e`, `Yt`, regularity `hY`, `hY2`, `he`; parallelism `hpar`;
  orthonormality `hortho`; completeness `hcomplete`, `hinv`; frame decomposition `hexp`; matrix
  regularity `hYmat`, `hY'mat`; no-conjugate invertibility `hu`) are **CARRIED** verbatim as
  genuine hypotheses.  Every carried hypothesis is a real mathematical statement
  (a `HasDerivAt` / `IsGeodesicVariationAt` / an orthonormality-or-completeness identity /
  an `EventuallyEq` / an `IsUnit`); NONE is `True`/vacuous, and none assumes the conclusion.

## Honest scope

This is a genuine specialization: the exact `−Ric` Raychaudhuri equation
`θ'(t) = −Ric(γ',γ') − tr(Θ²)` for the ACTUAL exp geodesic `expTube g gi hC p v`, with the geodesic
hypothesis `hγ` no longer assumed but PROVED from the exp machinery.  It does **NOT** construct the
parallel orthonormal frame (the M2b-2 wall, still carried), does **NOT** discharge `hVar` concretely
against the exp-differential flow columns (that would couple the carried frame decomposition `hexp`
to the internally-obtained flow `Φ`), does **NOT** connect `θ` to the coordinate van-Vleck
determinant `J`, and is unrelated to the heat-kernel coefficient `a₁ = R/6`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.FrameRaychaudhuri
import QIQTH.ExpDiffVariation
import QIQTH.ExpFlowJacobi

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic Finset Matrix

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **The `−Ric` Raychaudhuri equation for the actual exp geodesic `γ = expTube`.**

Specializes `frame_raychaudhuri_ricci_nhds` to `γ := expTube g gi hC p v` at an interior parameter
`t ∈ (0,1)`.  The geodesic hypothesis `hγ` is DISCHARGED from `expTube_spec` (the confined tube
solves the geodesic ODE on `(-2,2) ⊇ 𝓝 t`); the frame Jacobi-variation hypothesis `hVar` and all of
the parallel-frame data (`e`, `Yt`, `hY`, `hY2`, `he`, `hpar`, `hortho`, `hcomplete`, `hinv`,
`hexp`, `hYmat`, `hY'mat`, `hu`) are carried as genuine hypotheses.  Under those, the expansion
scalar `θ := tr(Y' Y⁻¹)` obeys `θ'(t) = −Ric(γ'(t),γ'(t)) − tr(Θ(t)²)`, `Θ := Y' Y⁻¹`, along the
exp geodesic.  Does not construct the frame, discharge `hVar`, connect `θ` to the van-Vleck
determinant, or derive `a₁ = R/6`. -/
theorem expFlow_frame_raychaudhuri (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (V : Fin n → ℝ → Point n × Point n)
    (hVar : ∀ j, ∀ᶠ τ in nhds t,
      IsGeodesicVariationAt g gi (expTube g gi hC p v) (V j) τ)
    (e : Fin n → ℝ → Point n) (Yt : Fin n → Fin n → ℝ → ℝ)
    (hY : ∀ j i, ∀ᶠ τ in nhds t, HasDerivAt (Yt j i) (deriv (Yt j i) τ) τ)
    (hY2 : ∀ j i, ∀ᶠ τ in nhds t, HasDerivAt (deriv (Yt j i)) (deriv (deriv (Yt j i)) τ) τ)
    (he : ∀ i a, ∀ᶠ τ in nhds t, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ᶠ τ in nhds t,
      covariantDerivAlong g gi (fun τ => (expTube g gi hC p v τ).1) (e i) τ = 0)
    (hortho : ∀ i k,
      (∑ a, ∑ b, g (expTube g gi hC p v t).1 a b * e i t a * e k t b) = if i = k then (1:ℝ) else 0)
    (hcomplete : ∀ μ b, (∑ i, e i t μ * e i t b) = gi (expTube g gi hC p v t).1 μ b)
    (hinv : ∀ a μ,
      (∑ b, g (expTube g gi hC p v t).1 a b * gi (expTube g gi hC p v t).1 μ b)
        = if a = μ then (1:ℝ) else 0)
    (hexp : ∀ j,
      (fun s => fun a => ∑ i, Yt j i s * e i s a)
        =ᶠ[nhds t] (fun s => (V j s).1))
    (hYmat : HasDerivAt (fun s => (Matrix.of (fun k j => Yt j k s) : Matrix (Fin n) (Fin n) ℝ))
              (Matrix.of (fun k j => deriv (Yt j k) t)) t)
    (hY'mat : HasDerivAt
              (fun s => (Matrix.of (fun k j => deriv (Yt j k) s) : Matrix (Fin n) (Fin n) ℝ))
              (Matrix.of (fun k j => deriv (deriv (Yt j k)) t)) t)
    (hu : IsUnit (Matrix.of (fun k j => Yt j k t) : Matrix (Fin n) (Fin n) ℝ)) :
    HasDerivAt
      (fun s => ((Matrix.of (fun k j => deriv (Yt j k) s) : Matrix (Fin n) (Fin n) ℝ)
                  * (Matrix.of (fun k j => Yt j k s))⁻¹).trace)
      (-(∑ σ, ∑ ν, ricci g gi σ ν (expTube g gi hC p v t).1
              * (expTube g gi hC p v t).2 σ * (expTube g gi hC p v t).2 ν)
        - (((Matrix.of (fun k j => deriv (Yt j k) t) : Matrix (Fin n) (Fin n) ℝ)
              * (Matrix.of (fun k j => Yt j k t))⁻¹)
            * ((Matrix.of (fun k j => deriv (Yt j k) t))
              * (Matrix.of (fun k j => Yt j k t))⁻¹)).trace)
      t := by
  -- DISCHARGE `hγ`: the confined tube solves the geodesic ODE on `(-2,2) ⊇ 𝓝 t`.
  have hspec := (expTube_spec g gi hC p v (le_of_lt hv)).2.1
  have hγ : ∀ᶠ τ in nhds t,
      HasDerivAt (expTube g gi hC p v)
        (geodesicField g gi (expTube g gi hC p v τ)) τ := by
    refine Filter.eventually_of_mem
      (Ioo_mem_nhds (show (-2:ℝ) < t by linarith [ht.1]) (show t < 2 by linarith [ht.2]))
      (fun τ hτ => ?_)
    exact hspec τ hτ
  -- Apply the frame-route capstone with `γ := expTube g gi hC p v`, carrying the frame data.
  exact frame_raychaudhuri_ricci_nhds g gi hC hgsymm V hγ hVar e Yt hY hY2 he hpar hortho
    hcomplete hinv hexp hYmat hY'mat hu

end QIQTH.ExpMap
