/-
  Curvature — the connection/curvature tower, component-level in a coordinate patch.

  Toward closing the differential-geometry gap in the GR-emergence program (note 51): rather than the
  multi-year abstract-manifold curvature library (which Mathlib lacks), this builds the curvature tensors
  COMPONENTWISE in a fixed coordinate chart `Point n = Fin n → ℝ`, as multivariable calculus + algebra.

  Layer 0 (this file, first increment): partial derivatives, the Christoffel symbols Γ from the metric,
  the Riemann/Ricci/scalar curvature, the Einstein tensor — and the STRUCTURAL identities that need no
  analytic input (Christoffel lower-symmetry; Riemann antisymmetry in its last two indices). The
  identities requiring metric compatibility and the (second) Bianchi identity — which feed Jacobson's
  conservation+Bianchi step — are later increments (they need the differentiability bookkeeping).

  Conventions: metric `g x i j` (lower, symmetric) and its inverse `gi x i j` (upper) are supplied as
  fields `Point n → Fin n → Fin n → ℝ`; `gi` is taken as the inverse where needed (a hypothesis, not
  reconstructed). Sign convention: R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ}Γ^λ_{νσ} − Γ^ρ_{νλ}Γ^λ_{μσ}.
-/
import Mathlib

namespace QIQTH.Curvature

open Finset

variable {n : ℕ}

/-- A point of the coordinate chart. -/
abbrev Point (n : ℕ) := Fin n → ℝ

/-- Partial derivative `∂ᵢ f` of a scalar field, along the `i`-th coordinate. -/
noncomputable def pd (f : Point n → ℝ) (i : Fin n) (x : Point n) : ℝ :=
  deriv (fun t => f (Function.update x i t)) (x i)

/-- **Christoffel symbols** `Γ^μ_{νρ} = ½ g^{μα}(∂_ν g_{αρ} + ∂_ρ g_{αν} − ∂_α g_{νρ})`. -/
noncomputable def christoffel (g gi : Point n → Fin n → Fin n → ℝ)
    (μ ν ρ : Fin n) (x : Point n) : ℝ :=
  (1 / 2) * ∑ α, gi x μ α *
    (pd (fun y => g y α ρ) ν x + pd (fun y => g y α ν) ρ x - pd (fun y => g y ν ρ) α x)

/-- **Christoffel symbols are symmetric in their lower indices** (torsion-freeness), for a symmetric
    metric. Immediate from the definition — no analytic input. -/
theorem christoffel_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (μ ν ρ : Fin n) (x : Point n) :
    christoffel g gi μ ν ρ x = christoffel g gi μ ρ ν x := by
  simp only [christoffel]
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  have h3 : (fun y => g y ν ρ) = (fun y => g y ρ ν) := funext fun y => hsymm y ν ρ
  rw [h3]; ring

/-- **Riemann curvature tensor** (type (1,3)),
    `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Σ_λ (Γ^ρ_{μλ} Γ^λ_{νσ} − Γ^ρ_{νλ} Γ^λ_{μσ})`. -/
noncomputable def riemann (g gi : Point n → Fin n → Fin n → ℝ)
    (ρ σ μ ν : Fin n) (x : Point n) : ℝ :=
  pd (fun y => christoffel g gi ρ ν σ y) μ x - pd (fun y => christoffel g gi ρ μ σ y) ν x
  + ∑ l, (christoffel g gi ρ μ l x * christoffel g gi l ν σ x
        - christoffel g gi ρ ν l x * christoffel g gi l μ σ x)

/-- **Riemann is antisymmetric in its last two indices**: `R^ρ_{σμν} = −R^ρ_{σνμ}`. Immediate from the
    definition (the derivative pair and the quadratic sum each negate under `μ ↔ ν`). -/
theorem riemann_antisymm (g gi : Point n → Fin n → Fin n → ℝ)
    (ρ σ μ ν : Fin n) (x : Point n) :
    riemann g gi ρ σ μ ν x = - riemann g gi ρ σ ν μ x := by
  simp only [riemann]
  have hsum :
      (∑ l, (christoffel g gi ρ ν l x * christoffel g gi l μ σ x
           - christoffel g gi ρ μ l x * christoffel g gi l ν σ x))
      = - ∑ l, (christoffel g gi ρ μ l x * christoffel g gi l ν σ x
             - christoffel g gi ρ ν l x * christoffel g gi l μ σ x) := by
    have h0 :
        (∑ l, (christoffel g gi ρ ν l x * christoffel g gi l μ σ x
             - christoffel g gi ρ μ l x * christoffel g gi l ν σ x))
        + (∑ l, (christoffel g gi ρ μ l x * christoffel g gi l ν σ x
               - christoffel g gi ρ ν l x * christoffel g gi l μ σ x)) = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro l _; ring
    linarith
  rw [hsum]; ring

/-- **Ricci tensor** `R_{σν} = R^μ_{σμν}` (contraction on the first and third indices). -/
noncomputable def ricci (g gi : Point n → Fin n → Fin n → ℝ) (σ ν : Fin n) (x : Point n) : ℝ :=
  ∑ μ, riemann g gi μ σ μ ν x

/-- **Scalar curvature** `R = g^{σν} R_{σν}`. -/
noncomputable def scalarCurv (g gi : Point n → Fin n → Fin n → ℝ) (x : Point n) : ℝ :=
  ∑ σ, ∑ ν, gi x σ ν * ricci g gi σ ν x

/-- **Einstein tensor** `G_{σν} = R_{σν} − ½ R g_{σν}`. -/
noncomputable def einsteinTensor (g gi : Point n → Fin n → Fin n → ℝ)
    (σ ν : Fin n) (x : Point n) : ℝ :=
  ricci g gi σ ν x - (1 / 2) * scalarCurv g gi x * g x σ ν

/-! ### The covariant derivative (the connection's action on tensors) -/

/-- **Covariant derivative of a vector field** `V^μ`: `∇_ν V^μ = ∂_ν V^μ + Γ^μ_{νσ} V^σ`. -/
noncomputable def covDerivVec (g gi : Point n → Fin n → Fin n → ℝ)
    (V : Point n → Fin n → ℝ) (ν μ : Fin n) (x : Point n) : ℝ :=
  pd (fun y => V y μ) ν x + ∑ σ, christoffel g gi μ ν σ x * V x σ

/-- **Covariant derivative of a covector** `ω_μ`: `∇_ν ω_μ = ∂_ν ω_μ − Γ^σ_{νμ} ω_σ`. -/
noncomputable def covDerivCov (g gi : Point n → Fin n → Fin n → ℝ)
    (ω : Point n → Fin n → ℝ) (ν μ : Fin n) (x : Point n) : ℝ :=
  pd (fun y => ω y μ) ν x - ∑ σ, christoffel g gi σ ν μ x * ω x σ

/-- **Covariant derivative of a (0,2) tensor** `T_{μρ}`:
    `∇_ν T_{μρ} = ∂_ν T_{μρ} − Γ^σ_{νμ} T_{σρ} − Γ^σ_{νρ} T_{μσ}`. -/
noncomputable def covDeriv02 (g gi : Point n → Fin n → Fin n → ℝ)
    (T : Point n → Fin n → Fin n → ℝ) (ν μ ρ : Fin n) (x : Point n) : ℝ :=
  pd (fun y => T y μ ρ) ν x
    - ∑ σ, christoffel g gi σ ν μ x * T x σ ρ
    - ∑ σ, christoffel g gi σ ν ρ x * T x μ σ

/-- **The covariant derivative of a (0,2) tensor is symmetric in `μ,ρ` when the tensor is** — the
    lower-index symmetry is preserved (uses `christoffel_symm`). A structural check, no analytic input. -/
theorem covDeriv02_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (T : Point n → Fin n → Fin n → ℝ) (hT : ∀ y a b, T y a b = T y b a)
    (ν μ ρ : Fin n) (x : Point n) :
    covDeriv02 g gi T ν μ ρ x = covDeriv02 g gi T ν ρ μ x := by
  simp only [covDeriv02]
  have e1 : (fun y => T y μ ρ) = (fun y => T y ρ μ) := funext fun y => hT y μ ρ
  have e2 : (∑ σ, christoffel g gi σ ν μ x * T x σ ρ)
          = ∑ σ, christoffel g gi σ ν μ x * T x ρ σ := by
    apply Finset.sum_congr rfl; intro σ _; rw [hT x σ ρ]
  have e3 : (∑ σ, christoffel g gi σ ν ρ x * T x μ σ)
          = ∑ σ, christoffel g gi σ ν ρ x * T x σ μ := by
    apply Finset.sum_congr rfl; intro σ _; rw [hT x μ σ]
  rw [e1, e2, e3]; ring

end QIQTH.Curvature
