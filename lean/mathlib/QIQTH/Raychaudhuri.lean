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

/-- **The Ricci identity** — the commutator of covariant derivatives is the Riemann curvature:
`(∇_μ ∇_ν − ∇_ν ∇_μ) V^ρ = R^ρ_{σμν} V^σ`. The geometric heart of Raychaudhuri focusing. -/
theorem ricci_identity (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (V : Point n → Fin n → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (μ ν ρ : Fin n) (x : Point n) :
    covDeriv2Vec g gi V μ ν ρ x - covDeriv2Vec g gi V ν μ ρ x
      = ∑ σ, riemann g gi ρ σ μ ν x * V x σ := by
  rw [covDeriv2Vec, covDeriv2Vec, pd_covDerivVec g gi V hVC hC μ ν ρ x,
      pd_covDerivVec g gi V hVC hC ν μ ρ x, pd_comm (fun z => V z ρ) ν μ x (hVC ρ)]
  simp only [covDerivVec, riemann, Finset.mul_sum, mul_add, sub_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- geodesic-direction Γ terms cancel by torsion-freeness `Γ^σ_νμ = Γ^σ_μν`
  have hF1 : (∑ x_1, christoffel g gi x_1 ν μ x * pd (fun z => V z ρ) x_1 x)
           = (∑ x_1, christoffel g gi x_1 μ ν x * pd (fun z => V z ρ) x_1 x) :=
    Finset.sum_congr rfl (fun x_1 _ => by rw [christoffel_symm g gi hsymm x_1 ν μ x])
  have hF2 : (∑ x_1, ∑ i, christoffel g gi x_1 ν μ x * (christoffel g gi ρ x_1 i x * V x i))
           = (∑ x_1, ∑ i, christoffel g gi x_1 μ ν x * (christoffel g gi ρ x_1 i x * V x i)) :=
    Finset.sum_congr rfl (fun x_1 _ => Finset.sum_congr rfl (fun i _ => by
      rw [christoffel_symm g gi hsymm x_1 ν μ x]))
  -- the `ΓΓ` curvature terms reassemble into the Riemann quadratic part (reindex via `sum_comm`)
  have h5 : (∑ x_1, ∑ i, christoffel g gi ρ μ x_1 x * (christoffel g gi x_1 ν i x * V x i))
          = (∑ x_1, (∑ x_2, christoffel g gi ρ μ x_2 x * christoffel g gi x_2 ν x_1 x) * V x x_1) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun x_1 _ => by ring))
  have h12 : (∑ x_1, ∑ i, christoffel g gi ρ ν x_1 x * (christoffel g gi x_1 μ i x * V x i))
           = (∑ x_1, (∑ x_2, christoffel g gi ρ ν x_2 x * christoffel g gi x_2 μ x_1 x) * V x x_1) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun x_1 _ => by ring))
  rw [hF1, hF2, h5, h12]
  ring

/-- **The contracted Ricci identity** — tracing the commutator on the upper index (`ρ = μ`, summed)
turns the Riemann tensor into the **Ricci tensor**: `∑_μ (∇_μ∇_ν − ∇_ν∇_μ) V^μ = R_{σν} V^σ`. This is
exactly the step that introduces the `R_{μν}` focusing term into the expansion evolution. -/
theorem ricci_identity_contracted (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (V : Point n → Fin n → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ν : Fin n) (x : Point n) :
    ∑ μ, (covDeriv2Vec g gi V μ ν μ x - covDeriv2Vec g gi V ν μ μ x)
      = ∑ σ, ricci g gi σ ν x * V x σ := by
  have hstep : (∑ μ, (covDeriv2Vec g gi V μ ν μ x - covDeriv2Vec g gi V ν μ μ x))
             = ∑ μ, ∑ σ, riemann g gi μ σ μ ν x * V x σ :=
    Finset.sum_congr rfl (fun μ _ => ricci_identity g gi hsymm V hVC hC μ ν μ x)
  rw [hstep, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun σ _ => by simp only [ricci, Finset.sum_mul])

/-- **The expansion** `θ = ∇_μ V^μ` — the covariant divergence of a vector field. -/
noncomputable def expansion (g gi : Point n → Fin n → Fin n → ℝ)
    (V : Point n → Fin n → ℝ) (x : Point n) : ℝ :=
  ∑ μ, covDerivVec g gi V μ μ x

/-- **Covariant derivative commutes with contraction** (the geodesic-direction Γ terms cancel by
torsion-freeness): the trace `∑_μ ∇_ν ∇_μ V^μ` is just the ordinary derivative of the expansion,
`∂_ν θ`. This is what turns `∇_ν(∇_μ V^μ)` into `∂_ν θ` in the Raychaudhuri derivation. -/
theorem covDeriv2Vec_trace (g gi : Point n → Fin n → Fin n → ℝ) (V : Point n → Fin n → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ν : Fin n) (x : Point n) :
    ∑ μ, covDeriv2Vec g gi V ν μ μ x = pd (fun y => expansion g gi V y) ν x := by
  have hpd : ∀ μ, PdiffAt (fun y => covDerivVec g gi V μ μ y) ν x := fun μ => by
    unfold covDerivVec
    exact (PdiffAt_pd (fun z => V z μ) (hVC μ) μ ν x).add (PdiffAt_sum _ _ ν x (fun σ _ =>
      (PdiffAt_of_contDiff _ (hC μ μ σ) ν x).mul (PdiffAt_of_contDiff _ (hVC σ) ν x)))
  have hcancel : (∑ μ, ∑ σ, christoffel g gi μ ν σ x * covDerivVec g gi V μ σ x)
               = (∑ μ, ∑ σ, christoffel g gi σ ν μ x * covDerivVec g gi V σ μ x) :=
    Finset.sum_comm
  simp only [covDeriv2Vec, expansion]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hcancel, add_sub_cancel_right]
  exact (pd_sum _ (fun μ y => covDerivVec g gi V μ μ y) ν x (fun μ _ => hpd μ)).symm

/-- **The Raychaudhuri focusing equation.** Contracting the (contracted) Ricci identity with `V`
gives the evolution of the expansion `θ` along `V`, with the **Ricci focusing term `−R_{σν}V^σV^ν`**
made explicit:

  `V^ν ∂_ν θ = Σ_{μν} V^ν ∇_μ∇_ν V^μ − R_{σν} V^σ V^ν`.

This is Jacobson's focusing step (the geometry of his front half). For a *geodesic* `V`
(`V^σ∇_σV^μ=0`) the first right-hand term equals `−(∇_μV^ν)(∇_νV^μ)` (the `−½θ²−σ²` shear part);
that geodesic simplification is the remaining (Leibniz) polish. Holds for any vector field. -/
theorem raychaudhuri_focusing (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (V : Point n → Fin n → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (x : Point n) :
    ∑ ν, V x ν * pd (fun y => expansion g gi V y) ν x
      = (∑ ν, ∑ μ, V x ν * covDeriv2Vec g gi V μ ν μ x)
        - ∑ ν, ∑ σ, ricci g gi σ ν x * V x σ * V x ν := by
  have key : ∀ ν, pd (fun y => expansion g gi V y) ν x
               = (∑ μ, covDeriv2Vec g gi V μ ν μ x) - ∑ σ, ricci g gi σ ν x * V x σ := by
    intro ν
    have h := ricci_identity_contracted g gi hsymm V hVC hC ν x
    rw [Finset.sum_sub_distrib, covDeriv2Vec_trace g gi V hVC hC ν x] at h
    linarith [h]
  simp only [key, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun σ _ => by ring))

end QIQTH.Curvature
