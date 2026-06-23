/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Christoffel smoothness from metric smoothness

Discharges the `hC` hypothesis of the QIQT→GR capstone (Tier A5 of `QIQT_GR_DISCHARGEABLE_PLAN.md`): the
Christoffel symbols are `C^∞` whenever the metric `g` and its inverse `gi` are.  Route: the partial derivative
`pd f i` of a `C^∞` scalar `f` is `C^∞` (it is `y ↦ fderiv f y (e_i)`, a `clm_apply` of the `C^∞` derivative map),
and `christoffel` is a finite algebraic combination of `gi` and first derivatives of `g`.

Axiom-free.
-/
import QIQTH.Curvature

namespace QIQTH.Curvature

variable {n : ℕ}

/-- **The partial derivative of a `C^∞` scalar is `C^∞`.**  `pd f i = (fun y => fderiv ℝ f y (Pi.single i 1))`
    (`pd_eq_fderiv`, valid everywhere since `f` is differentiable), and `y ↦ fderiv ℝ f y` is `C^∞`
    (`ContDiff.fderiv_right`), so applying it to the constant basis covector `e_i` (`ContDiff.clm_apply`) is `C^∞`. -/
theorem contDiff_pd (f : Point n → ℝ) (hf : ContDiff ℝ ⊤ f) (i : Fin n) :
    ContDiff ℝ ⊤ (fun y => pd f i y) := by
  have heq : (fun y => pd f i y) = fun y => fderiv ℝ f y (Pi.single i (1 : ℝ)) := by
    funext y
    exact pd_eq_fderiv f i y (hf.differentiable (by simp)).differentiableAt
  rw [heq]
  exact (hf.fderiv_right le_top).clm_apply contDiff_const

/-- **★ Christoffel symbols are `C^∞`** — discharges `hC`.  `christoffel g gi μ ν ρ = ½·∑α gi_{μα}(∂_ν g_{αρ}
    + ∂_ρ g_{αν} − ∂_α g_{νρ})` is a finite sum of products of `gi` (`C^∞` by `hCgi`) and partial derivatives of
    `g` (`C^∞` by `contDiff_pd` + `hCg`). -/
theorem christoffel_contDiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (μ ν ρ : Fin n) :
    ContDiff ℝ ⊤ (fun y => christoffel g gi μ ν ρ y) := by
  simp only [christoffel]
  refine contDiff_const.mul (ContDiff.sum (fun α _ => (hCgi μ α).mul ?_))
  exact ((contDiff_pd (fun y => g y α ρ) (hCg α ρ) ν).add
      (contDiff_pd (fun y => g y α ν) (hCg α ν) ρ)).sub
    (contDiff_pd (fun y => g y ν ρ) (hCg ν ρ) α)

/-- **The Riemann tensor is `C^∞`** — `R^ρ_{σμν} = ∂_μΓ^ρ_{νσ} − ∂_νΓ^ρ_{μσ} + Σ_l(Γ^ρ_{μl}Γ^l_{νσ}
    − Γ^ρ_{νl}Γ^l_{μσ})` is a finite combination of `∂Γ` (`contDiff_pd` ∘ `christoffel_contDiff`) and `ΓΓ`. -/
theorem riemann_contDiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (ρ σ μ ν : Fin n) :
    ContDiff ℝ ⊤ (fun y => riemann g gi ρ σ μ ν y) := by
  simp only [riemann]
  refine ((contDiff_pd _ (christoffel_contDiff g gi hCg hCgi ρ ν σ) μ).sub
    (contDiff_pd _ (christoffel_contDiff g gi hCg hCgi ρ μ σ) ν)).add ?_
  exact ContDiff.sum (fun l _ =>
    ((christoffel_contDiff g gi hCg hCgi ρ μ l).mul (christoffel_contDiff g gi hCg hCgi l ν σ)).sub
      ((christoffel_contDiff g gi hCg hCgi ρ ν l).mul (christoffel_contDiff g gi hCg hCgi l μ σ)))

/-- **The Ricci tensor is `C^∞`** — `R_{σν} = ∑μ R^μ_{σμν}` (sum of `C^∞` Riemann components). -/
theorem ricci_contDiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (σ ν : Fin n) :
    ContDiff ℝ ⊤ (fun y => ricci g gi σ ν y) := by
  simp only [ricci]
  exact ContDiff.sum (fun μ _ => riemann_contDiff g gi hCg hCgi μ σ μ ν)

/-- **The scalar curvature is `C^∞`** — `R = ∑_{σν} g^{σν} R_{σν}` (a finite combination of `C^∞` `gi` and
    `C^∞` Ricci).  Feeds the `hreg` regularity input of the QIQT→GR capstone (Tier A4). -/
theorem scalarCurv_contDiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b)) :
    ContDiff ℝ ⊤ (fun y => scalarCurv g gi y) := by
  simp only [scalarCurv]
  exact ContDiff.sum (fun σ _ => ContDiff.sum (fun ν _ =>
    (hCgi σ ν).mul (ricci_contDiff g gi hCg hCgi σ ν)))

end QIQTH.Curvature
