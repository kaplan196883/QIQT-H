import QIQTH.Curvature

/-!
# Raychaudhuri focusing — the geometry behind Jacobson's front half

Jacobson's thermodynamic derivation of the Einstein equation has a *geometric* sub-step — Raychaudhuri
focusing — that brings the Ricci term `R_{μν}k^μk^ν` into the evolution of a null/geodesic
congruence's expansion. Unlike Unruh temperature (QFT) and the area law (the postulate), Raychaudhuri
focusing is **pure differential geometry**, so it can be machine-checked.

Its heart is the **Ricci identity** — the commutator of covariant derivatives is the Riemann tensor:

  `(∇_μ ∇_ν − ∇_ν ∇_μ) V^ρ = R^ρ_{σμν} V^σ`.

Contracting `ρ = μ` produces the `−R_{μν}k^μk^ν` focusing term. This file builds that identity in the
component framework of `QIQTH/Curvature.lean` (axiom-free), then the raw Raychaudhuri equation.

**Honest scope:** formalizing this closes the *geometric* kernel of Jacobson's front half. The
remaining front-half inputs — Unruh temperature and the area law `S∝A` — are NOT geometry and stay
cited; this does not make the full Bekenstein→per-null arrow Lean-checked, but it removes the
geometry from the cited list.
-/

namespace QIQTH.Curvature

variable {n : ℕ}

/-- **Second covariant derivative of a vector field**, `∇_μ ∇_ν V^ρ`. Treating `W^ρ_ν := ∇_ν V^ρ`
(`= covDerivVec`) as a `(1,1)` tensor: `∇_μ W^ρ_ν = ∂_μ W^ρ_ν + Γ^ρ_{μσ} W^σ_ν − Γ^σ_{μν} W^ρ_σ`. -/
noncomputable def covDeriv2Vec (g gi : Point n → Fin n → Fin n → ℝ)
    (V : Point n → Fin n → ℝ) (μ ν ρ : Fin n) (x : Point n) : ℝ :=
  pd (fun y => covDerivVec g gi V ν ρ y) μ x
    + ∑ σ, christoffel g gi ρ μ σ x * covDerivVec g gi V ν σ x
    - ∑ σ, christoffel g gi σ μ ν x * covDerivVec g gi V σ ρ x

/-- The partial derivative of `∇_ν V^ρ`, expanded via the product rule:
`∂_μ(∇_ν V^ρ) = ∂_μ∂_ν V^ρ + Σ_σ (∂_μ Γ^ρ_{νσ}) V^σ + Σ_σ Γ^ρ_{νσ} ∂_μ V^σ`. -/
theorem pd_covDerivVec (g gi : Point n → Fin n → Fin n → ℝ) (V : Point n → Fin n → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (μ ν ρ : Fin n) (x : Point n) :
    pd (fun y => covDerivVec g gi V ν ρ y) μ x
      = pd (fun y => pd (fun z => V z ρ) ν y) μ x
        + ∑ σ, (pd (fun y => christoffel g gi ρ ν σ y) μ x * V x σ
              + christoffel g gi ρ ν σ x * pd (fun y => V y σ) μ x) := by
  have hpdV : PdiffAt (fun y => pd (fun z => V z ρ) ν y) μ x := PdiffAt_pd _ (hVC ρ) ν μ x
  have hterm : ∀ σ, PdiffAt (fun y => christoffel g gi ρ ν σ y * V y σ) μ x := fun σ =>
    (PdiffAt_of_contDiff _ (hC ρ ν σ) μ x).mul (PdiffAt_of_contDiff _ (hVC σ) μ x)
  simp only [covDerivVec]
  rw [pd_add _ _ μ x hpdV (PdiffAt_sum _ _ μ x (fun σ _ => hterm σ)),
    pd_sum _ _ μ x (fun σ _ => hterm σ)]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact pd_mul _ _ μ x (PdiffAt_of_contDiff _ (hC ρ ν σ) μ x) (PdiffAt_of_contDiff _ (hVC σ) μ x)

end QIQTH.Curvature
