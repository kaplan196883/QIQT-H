import QIQTH.Curvature

/-!
# The Einstein field equation from the thermodynamic equation of state

This file **completes the step `EinsteinEquationOfState.lean` explicitly defers** ("conservation
`∇^μT=0` and the contracted Bianchi identity then fix `f = −½R + Λ`, giving the Einstein
equation — that last step is cited, not here").

Given
  * the **post-crux relation** `a·T_{μν} = R_{μν} + f·g_{μν}` — the per-null-direction Clausius
    relation upgraded to a tensor by `symmTensor_eq_smul_metric_of_null` (Jacobson's heat/area
    input; the differential geometry that produces it is cited physics, supplied as a hypothesis),
  * **local conservation** `∇^μ(a·T)_{μν} = 0`,
  * the **contracted Bianchi identity** `∇^μ R_{μν} = ½ ∂_ν R` (geometry — the `∇^μG_{μν}=0`
    identity whose hard lemmas are machine-checked in `Curvature.lean`),
  * **metric compatibility** `∇g = 0` (`metric_compat`),

the **Einstein field equation** follows:
      `a·T_{μν} = G_{μν} + Λ·g_{μν}`,   `G_{μν} := R_{μν} − ½R·g_{μν}`,
with `Λ := f + ½R` **covariantly constant** (`∂_ν Λ = 0`) — the cosmological constant emerging as
Jacobson's integration constant. Axiom-free; every cited input is an explicit labeled hypothesis.
-/

namespace QIQTH.Curvature

variable {n : ℕ}

/-- **Raised divergence** `∇^μ X_{μν} = g^{μρ} ∇_ρ X_{μν}` of a `(0,2)` tensor field. -/
noncomputable def div02 (g gi : Point n → Fin n → Fin n → ℝ)
    (X : Point n → Fin n → Fin n → ℝ) (ν : Fin n) (x : Point n) : ℝ :=
  ∑ μ, ∑ ρ, gi x μ ρ * covDeriv02 g gi X ρ μ ν x

/-- The raised divergence is additive in the tensor field. -/
theorem div02_add (g gi : Point n → Fin n → Fin n → ℝ)
    (X Y : Point n → Fin n → Fin n → ℝ) (x : Point n)
    (hX : ∀ a b ρ, PdiffAt (fun y => X y a b) ρ x) (hY : ∀ a b ρ, PdiffAt (fun y => Y y a b) ρ x)
    (ν : Fin n) :
    div02 g gi (fun y a b => X y a b + Y y a b) ν x = div02 g gi X ν x + div02 g gi Y ν x := by
  simp only [div02]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro μ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ρ _
  have hcd : covDeriv02 g gi (fun y a b => X y a b + Y y a b) ρ μ ν x
      = covDeriv02 g gi X ρ μ ν x + covDeriv02 g gi Y ρ μ ν x := by
    simp only [covDeriv02]
    rw [pd_add (fun y => X y μ ν) (fun y => Y y μ ν) ρ x (hX μ ν ρ) (hY μ ν ρ)]
    simp only [Finset.sum_add_distrib, mul_add]; ring
  rw [hcd]; ring

/-- **The divergence of `f·g` is `∂_ν f`.** Metric compatibility kills the connection terms; the
    inverse metric collapses the contraction. (This is what makes the cosmological-constant term
    `Λ·g` covariantly constant.) -/
theorem div02_scalar_metric (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (f : Point n → ℝ) (x : Point n) (hf : ∀ ρ, PdiffAt f ρ x)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (ν : Fin n) :
    div02 g gi (fun y a b => f y * g y a b) ν x = pd f ν x := by
  have key : ∀ ρ μ : Fin n,
      covDeriv02 g gi (fun y a b => f y * g y a b) ρ μ ν x = pd f ρ x * g x μ ν := by
    intro ρ μ
    have hmc := metric_compat g gi hsymm x (fun p q => hinv x p q) ρ μ ν
    simp only [covDeriv02] at hmc ⊢
    rw [pd_mul f (fun y => g y μ ν) ρ x (hf ρ) (hg μ ν ρ)]
    have e1 : (∑ σ, christoffel g gi σ ρ μ x * (f x * g x σ ν))
        = f x * (∑ σ, christoffel g gi σ ρ μ x * g x σ ν) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro σ _; ring
    have e2 : (∑ σ, christoffel g gi σ ρ ν x * (f x * g x μ σ))
        = f x * (∑ σ, christoffel g gi σ ρ ν x * g x μ σ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro σ _; ring
    have hg0 : pd (fun y => g y μ ν) ρ x
        = (∑ σ, christoffel g gi σ ρ μ x * g x σ ν) + (∑ σ, christoffel g gi σ ρ ν x * g x μ σ) := by
      linarith [hmc]
    rw [e1, e2, hg0]; ring
  have hcol : ∀ ρ : Fin n, (∑ μ, gi x μ ρ * g x μ ν) = if ν = ρ then (1 : ℝ) else 0 := by
    intro ρ
    rw [show (∑ μ, gi x μ ρ * g x μ ν) = ∑ μ, g x ν μ * gi x μ ρ from by
          apply Finset.sum_congr rfl; intro μ _; rw [hsymm x ν μ]; ring]
    exact hinv x ν ρ
  rw [div02, Finset.sum_congr rfl (fun μ (_ : μ ∈ Finset.univ) =>
        Finset.sum_congr rfl (fun ρ (_ : ρ ∈ Finset.univ) => by rw [key ρ μ]))]
  rw [show (∑ μ, ∑ ρ, gi x μ ρ * (pd f ρ x * g x μ ν))
        = ∑ ρ, pd f ρ x * (∑ μ, gi x μ ρ * g x μ ν) from by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro ρ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro μ _; ring]
  rw [Finset.sum_congr rfl (fun ρ (_ : ρ ∈ Finset.univ) => by rw [hcol ρ])]
  simp [Finset.sum_ite_eq, mul_ite]

/-- **The Einstein field equation as the thermodynamic equation of state** (Jacobson, PRL 1995),
    completed: from the post-crux relation + conservation + contracted Bianchi + metric
    compatibility, `a·T_{μν} = G_{μν} + Λ·g_{μν}` with `Λ := f + ½R` **covariantly constant**.
    The cited physics (Clausius/Raychaudhuri → `crux`, conservation → `conserv`) and the geometry
    (contracted Bianchi → `bianchi`) are explicit labeled hypotheses; the closure is machine-checked,
    axiom-free. `tr` is the scalar curvature `R`. -/
theorem einstein_field_equation (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (T Ric : Point n → Fin n → Fin n → ℝ) (f tr : Point n → ℝ) (a : ℝ) (x : Point n)
    (hf : ∀ ρ, PdiffAt f ρ x) (htr : ∀ ρ, PdiffAt tr ρ x)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (hRic : ∀ a b ρ, PdiffAt (fun y => Ric y a b) ρ x)
    -- post-crux Clausius relation (cited physics): `a·T_{μν} = R_{μν} + f·g_{μν}`
    (crux : ∀ y a' b, a * T y a' b = Ric y a' b + f y * g y a' b)
    -- local conservation (physics): `∇^μ(a·T)_{μν} = 0`
    (conserv : ∀ ν, div02 g gi (fun y a' b => a * T y a' b) ν x = 0)
    -- contracted Bianchi (geometry): `∇^μ R_{μν} = ½ ∂_ν R`
    (bianchi : ∀ ν, div02 g gi Ric ν x = (1 / 2 : ℝ) * pd tr ν x) :
    (∀ μ ν, a * T x μ ν
        = (Ric x μ ν - (1 / 2 : ℝ) * tr x * g x μ ν) + (f x + (1 / 2 : ℝ) * tr x) * g x μ ν)
    ∧ (∀ ν, pd (fun y => f y + (1 / 2 : ℝ) * tr y) ν x = 0) := by
  refine ⟨fun μ ν => by rw [crux x μ ν]; ring, fun ν => ?_⟩
  -- Take the divergence of the crux relation.
  have heq : (fun y a' b => a * T y a' b) = (fun y a' b => Ric y a' b + f y * g y a' b) := by
    funext y a' b; exact crux y a' b
  have h1 := conserv ν
  rw [heq, div02_add g gi Ric (fun y a' b => f y * g y a' b) x hRic
        (fun a' b ρ => (hf ρ).mul (hg a' b ρ)) ν,
      bianchi ν, div02_scalar_metric g gi hsymm hinv f x hf hg ν] at h1
  -- h1 : ½ ∂_ν tr + ∂_ν f = 0.  Conclude ∂_ν(f + ½tr) = 0.
  rw [pd_add f (fun y => (1 / 2 : ℝ) * tr y) ν x (hf ν) ((htr ν).const_mul (1 / 2 : ℝ)),
      pd_const_mul (1 / 2 : ℝ) tr ν x (htr ν)]
  linarith [h1]

end QIQTH.Curvature
