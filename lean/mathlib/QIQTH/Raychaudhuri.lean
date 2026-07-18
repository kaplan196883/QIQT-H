import QIQTH.Curvature
import QIQTH.ExpMap
import QIQTH.JacobiEquation
import QIQTH.CovariantJacobi

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

/-- **Partial-Leibniz of the geodesic acceleration.** For a geodesic vector field `V`
(`Σ_ν V^ν ∇_ν V^μ = 0` as a field), the divergence of the acceleration vanishes, expanded by the
product rule: `Σ_ν (∂_μ V^ν · ∇_ν V^μ + V^ν · ∂_μ(∇_ν V^μ)) = 0`. The step that lets
`Σ V^ν∇_μ∇_νV^μ` be rewritten as `−(∇_μV^ν)(∇_νV^μ)` (the `−½θ²−σ²` shear part). -/
theorem geodesic_divergence_leibniz (g gi : Point n → Fin n → Fin n → ℝ)
    (V : Point n → Fin n → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hgeo : ∀ y μ, ∑ ν, V y ν * covDerivVec g gi V ν μ y = 0)
    (μ : Fin n) (x : Point n) :
    ∑ ν, (pd (fun y => V y ν) μ x * covDerivVec g gi V ν μ x
        + V x ν * pd (fun y => covDerivVec g gi V ν μ y) μ x) = 0 := by
  have hpdcov : ∀ ν, PdiffAt (fun y => covDerivVec g gi V ν μ y) μ x := fun ν => by
    unfold covDerivVec
    exact (PdiffAt_pd (fun z => V z μ) (hVC μ) ν μ x).add (PdiffAt_sum _ _ μ x (fun σ _ =>
      (PdiffAt_of_contDiff _ (hC μ ν σ) μ x).mul (PdiffAt_of_contDiff _ (hVC σ) μ x)))
  have hzero : pd (fun y => ∑ ν, V y ν * covDerivVec g gi V ν μ y) μ x = 0 := by
    have heq : (fun y => ∑ ν, V y ν * covDerivVec g gi V ν μ y) = fun _ => (0 : ℝ) :=
      funext (fun y => hgeo y μ)
    rw [heq, pd_const]
  rw [← hzero, pd_sum _ _ μ x (fun ν _ => (PdiffAt_of_contDiff _ (hVC ν) μ x).mul (hpdcov ν))]
  exact Finset.sum_congr rfl
    (fun ν _ => (pd_mul _ _ μ x (PdiffAt_of_contDiff _ (hVC ν) μ x) (hpdcov ν)).symm)

/-- **Geodesic Leibniz identity.** For a geodesic field `V`, the Raychaudhuri second-derivative term
is the shear/expansion quadratic: `Σ_{νμ} V^ν ∇_μ∇_ν V^μ = − Σ_{μν} (∇_μ V^ν)(∇_ν V^μ)`. -/
theorem geodesic_leibniz (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (V : Point n → Fin n → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hgeo : ∀ y μ, ∑ ν, V y ν * covDerivVec g gi V ν μ y = 0)
    (x : Point n) :
    ∑ ν, ∑ μ, V x ν * covDeriv2Vec g gi V μ ν μ x
      = - ∑ μ, ∑ ν, covDerivVec g gi V μ ν x * covDerivVec g gi V ν μ x := by
  rw [eq_neg_iff_add_eq_zero]
  simp only [covDeriv2Vec]
  rw [show (∑ μ, ∑ ν, covDerivVec g gi V μ ν x * covDerivVec g gi V ν μ x)
        = ∑ μ, ∑ ν, (pd (fun y => V y ν) μ x + ∑ σ, christoffel g gi ν μ σ x * V x σ)
            * covDerivVec g gi V ν μ x
      from Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => rfl))]
  simp only [mul_add, mul_sub, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  -- P1 + P2 = Σ_μ (geodesic_divergence_leibniz μ) = 0
  have hP12 : (∑ x_1, ∑ x_2, V x x_1 * pd (fun y => covDerivVec g gi V x_1 x_2 y) x_2 x)
            + (∑ x_1, ∑ x_2, pd (fun y => V y x_2) x_1 x * covDerivVec g gi V x_2 x_1 x) = 0 := by
    rw [Finset.sum_comm (f := fun x_1 x_2 =>
          V x x_1 * pd (fun y => covDerivVec g gi V x_1 x_2 y) x_2 x), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun μ _ => ?_)
    rw [← Finset.sum_add_distrib, ← geodesic_divergence_leibniz g gi V hVC hC hgeo μ x]
    exact Finset.sum_congr rfl (fun ν _ => by ring)
  -- T1 = Σ_{μσ} Γ^μ_{μσ} (Σ_ν V^ν ∇_ν V^σ) = 0 by the geodesic equation
  have hT1 : (∑ x_1, ∑ x_2, ∑ i,
        V x x_1 * (christoffel g gi x_2 x_2 i x * covDerivVec g gi V x_1 i x)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun μ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    rw [show (∑ x_1, V x x_1 * (christoffel g gi μ μ σ x * covDerivVec g gi V x_1 σ x))
          = christoffel g gi μ μ σ x * ∑ x_1, V x x_1 * covDerivVec g gi V x_1 σ x from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ν _ => by ring), hgeo x σ, mul_zero]
  -- T2' = T3' by permuting the three summation indices (a,b,c) ↦ (b,c,a)
  have hT23 : (∑ x_1, ∑ x_2, ∑ i,
        V x x_1 * (christoffel g gi i x_2 x_1 x * covDerivVec g gi V i x_2 x))
            = (∑ x_1, ∑ x_2, ∑ i,
        christoffel g gi x_2 x_1 i x * V x i * covDerivVec g gi V x_2 x_1 x) := by
    rw [show (∑ x_1, ∑ x_2, ∑ i,
          V x x_1 * (christoffel g gi i x_2 x_1 x * covDerivVec g gi V i x_2 x))
        = ∑ a, ∑ b, ∑ c,
          christoffel g gi c b a x * V x a * covDerivVec g gi V c b x from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun c _ => by ring)))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_comm]
  linarith [hP12, hT1, hT23]

/-- **The Raychaudhuri equation** (geodesic congruence), in Jacobson's exact form:

  `V^ν ∂_ν θ = − (∇_μ V^ν)(∇_ν V^μ) − R_{σν} V^σ V^ν`.

The expansion `θ` of a geodesic congruence focuses, driven by the shear/expansion quadratic
`−(∇V)(∇V)` (Jacobson's `−½θ²−σ²`, the term he *neglects* near a stationary horizon) and the
**Ricci focusing term `−R(V,V)`** (the term he *uses*). Assembled from `raychaudhuri_focusing` and
`geodesic_leibniz`. **The full geometry of Jacobson's front half is now machine-checked, axiom-free.** -/
theorem raychaudhuri_geodesic (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (V : Point n → Fin n → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hgeo : ∀ y μ, ∑ ν, V y ν * covDerivVec g gi V ν μ y = 0)
    (x : Point n) :
    ∑ ν, V x ν * pd (fun y => expansion g gi V y) ν x
      = - (∑ μ, ∑ ν, covDerivVec g gi V μ ν x * covDerivVec g gi V ν μ x)
        - ∑ ν, ∑ σ, ricci g gi σ ν x * V x σ * V x ν := by
  rw [raychaudhuri_focusing g gi hsymm V hVC hC x, geodesic_leibniz g gi hsymm V hVC hC hgeo x]

/-- **★ Leading-order Raychaudhuri focusing at equilibrium — the geometric content of Jacobson's
`hFocus`.**  At a moment of *local equilibrium* (a stationary/bifurcation horizon, where the
shear–expansion quadratic `(∇_μV^ν)(∇_νV^μ)` vanishes — `θ = σ = ω = 0`, the condition Jacobson
imposes), the Raychaudhuri equation collapses to **pure Ricci focusing**:

  `V^ν ∂_ν θ = − R_{σν} V^σ V^ν`   (i.e. `dθ/dλ = − R_kk`).

So the focusing rate of a null geodesic congruence equals minus the contracted Ricci `R_kk` — exactly
the area-rate ↔ `R_kk` content of the `hFocus` input of `qiqt_bekenstein_gives_gr` / `qiqt_gr_from_wedge_kms`
(input #3, "standard structural regularity").  This is the kinematics of null congruences, derived from
the machine-checked `raychaudhuri_geodesic`; it presupposes no Einstein equation.  The only remaining
modelling step in `hFocus` is the identification of the abstract area first-variation rate with the
congruence expansion `θ` (the area-vs-`θ` correspondence).  Axiom-free. -/
theorem raychaudhuri_focusing_at_equilibrium (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (V : Point n → Fin n → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hgeo : ∀ y μ, ∑ ν, V y ν * covDerivVec g gi V ν μ y = 0)
    (x : Point n)
    (hequil : (∑ μ, ∑ ν, covDerivVec g gi V μ ν x * covDerivVec g gi V ν μ x) = 0) :
    ∑ ν, V x ν * pd (fun y => expansion g gi V y) ν x
      = - ∑ ν, ∑ σ, ricci g gi σ ν x * V x σ * V x ν := by
  rw [raychaudhuri_geodesic g gi hsymm V hVC hC hgeo x, hequil, neg_zero, zero_sub]

end QIQTH.Curvature

/-!
## Phase L3 addendum — the Ricci SOURCE TERM via the (covariant) Jacobi-field route

The section above builds Raychaudhuri via the Ricci identity / covariant divergence of a vector
field.  This addendum lands the SAME `−Ric(v,v)` source through the ODE-variational (Jacobi-field)
machinery of `QIQTH/JacobiEquation.lean` + `QIQTH/CovariantJacobi.lean`, which is the branch on the
critical path to the diagonal heat-kernel structure.  Two axiom-clean bricks (no `sorry`):

* `geodesicDeviation_trace_eq_ricci` — UNCONDITIONAL: the trace over the coordinate basis of the
  geodesic-deviation ("Jacobi") operator `ξ ↦ R(ξ,v)v` equals the Ricci quadratic form
  `∑_{σν} R_{σν} v^σ v^ν`.  This is the whole "relate the deviation operator to Ricci" content.

* `covariantJacobi_trace_at_center` — the traced centred covariant Jacobi equation over a
  basis-aligned family of Jacobi variations equals `−Ric(v,v)` — the Raychaudhuri source term.

⚠ SCOPE (what these are NOT): NOT the full Raychaudhuri congruence ODE `θ' + θ²/(n−1) + Ric = 0`
(the shear/expansion square and the `θ'` evolution need the matrix Jacobi field, not the traced
pointwise identity); NOT the `θ = r ∂_r log J = tr(Y⁻¹ Y')` determinant-ODE connection to K1/K2's
`det g̃ = J² · det(g∘exp)` (that needs the matrix Jacobi field, its inverse, and the
singular-at-centre limit — the labelled checkpoint); NOT `a₁ = R/6`.  All carried hypotheses of
`covariantJacobi_trace_at_center` are genuine and mirror `covariant_jacobi_equation_centered`
verbatim — none assume the conclusion; `geodesicDeviation_trace_eq_ricci` has no hypotheses beyond
`g, gi, x, v`.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **Trace identity (unconditional).**  The trace over the coordinate basis `e_i` of the
    geodesic-deviation operator `ξ ↦ R(ξ,v)v` equals the Ricci quadratic form `Ric(v,v)`:
      `∑ i, [R(e_i, v)v]^i  =  ∑_{σν} R_{σν} v^σ v^ν`.
    The basis vector `e_i = (fun k => if k = i then 1 else 0)` collapses the `μ`-sum of
    `riemannGeodesicDeviation` to `μ = i`, and `∑_i R^i_{σ i ν} = R_{σν}` is the Ricci contraction.
    No regularity or gauge hypotheses — pure finite-sum algebra. -/
theorem geodesicDeviation_trace_eq_ricci (g gi : Point n → Fin n → Fin n → ℝ) (x v : Point n) :
    ∑ i, riemannGeodesicDeviation g gi x v (fun k => if k = i then (1:ℝ) else 0) i
      = ∑ σ, ∑ ν, ricci g gi σ ν x * v σ * v ν := by
  -- Collapse the basis vector inside each `i`-summand: `μ`-sum picks out `μ = i`.
  have key : ∀ i, riemannGeodesicDeviation g gi x v (fun k => if k = i then (1:ℝ) else 0) i
      = ∑ σ, ∑ ν, riemann g gi i σ i ν x * v σ * v ν := by
    intro i
    simp only [riemannGeodesicDeviation, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [Finset.sum_ite_eq']
    simp
  simp only [key, ricci, Finset.sum_mul]
  -- Reorder `∑ i ∑ σ ∑ ν  →  ∑ σ ∑ ν ∑ i` to match the Ricci contraction `∑_i R^i_{σiν}`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.sum_comm]

/-- **Traced centred covariant Jacobi equation = the Raychaudhuri source term.**
    For a geodesic `γ = (x,v)` (`hγ`) at a Riemann-normal-coordinate centre
    (`hΓ0 : Γ(γ t).1 = 0`), and a FAMILY `V : Fin n → (ℝ → Point×Point)` of Jacobi variations
    (`hVar`) whose i-th position variation is the i-th coordinate basis vector at the base time `t`
    (`hbasis`), the trace of the covariant second derivatives equals minus the Ricci quadratic form
    of the velocity:
      `∑ i, [D²(V i)/dτ²]^i  =  −∑_{σν} R_{σν}(γ t) v^σ v^ν`   (`v = γ'`).
    Applies `covariant_jacobi_equation_centered` to each `V i` (`D²(V i)/dτ² = −R(·,v)v`), reads off
    the i-th component, substitutes the basis alignment `hbasis`, and closes with the trace identity
    `geodesicDeviation_trace_eq_ricci`.  The `−Ric(v,v)` source term of the Raychaudhuri congruence
    equation.  Regularity/gauge inputs carried verbatim from the centred covariant Jacobi equation —
    none assume the conclusion. -/
theorem covariantJacobi_trace_at_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    {γ : ℝ → Point n × Point n} {V : Fin n → (ℝ → Point n × Point n)} {t : ℝ}
    (hγ : ∀ τ, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ i, ∀ τ, IsGeodesicVariationAt g gi γ (V i) τ)
    (hΓ0 : ∀ i j k, christoffel g gi i j k (γ t).1 = 0)
    (hbasis : ∀ i, (V i t).1 = (fun k => if k = i then (1:ℝ) else 0)) :
    ∑ i, covariantSecondDeriv g gi (fun τ => (γ τ).1) (fun τ => (V i τ).1) t i
      = - ∑ σ, ∑ ν, ricci g gi σ ν (γ t).1 * (γ t).2 σ * (γ t).2 ν := by
  -- Per-field covariant Jacobi equation, i-th component, with the basis substitution.
  have step : ∀ i, covariantSecondDeriv g gi (fun τ => (γ τ).1) (fun τ => (V i τ).1) t i
      = - riemannGeodesicDeviation g gi (γ t).1 (γ t).2
          (fun k => if k = i then (1:ℝ) else 0) i := by
    intro i
    have h := congrFun (covariant_jacobi_equation_centered g gi hC hgsymm hγ (hVar i) hΓ0) i
    rw [Pi.neg_apply] at h
    rw [h, hbasis i]
  calc ∑ i, covariantSecondDeriv g gi (fun τ => (γ τ).1) (fun τ => (V i τ).1) t i
      = ∑ i, - riemannGeodesicDeviation g gi (γ t).1 (γ t).2
                (fun k => if k = i then (1:ℝ) else 0) i :=
        Finset.sum_congr rfl (fun i _ => step i)
    _ = - ∑ i, riemannGeodesicDeviation g gi (γ t).1 (γ t).2
                (fun k => if k = i then (1:ℝ) else 0) i := by
        rw [Finset.sum_neg_distrib]
    _ = - ∑ σ, ∑ ν, ricci g gi σ ν (γ t).1 * (γ t).2 σ * (γ t).2 ν := by
        rw [geodesicDeviation_trace_eq_ricci g gi (γ t).1 (γ t).2]

end QIQTH.ExpMap
