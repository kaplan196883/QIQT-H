/-
# Coordinate (component / metric 2-jet) scalar curvature R(g)

MANDATORY FIREWALL (binding, honest):

  • This is the COORDINATE / component-level scalar curvature — an ALGEBRAIC function of the
    metric's 0/1/2-jet (`ginv`, `dg`, `ddg`) via the standard
    Christoffel → Riemann → Ricci → trace contractions, with the identity
    `∂(g⁻¹) = −g⁻¹ dg g⁻¹` DEFINED into the formula (`dInvMetric`) — no Lean differentiation,
    no `Matrix.inv` derivative is ever taken.
    It is NOT the abstract coordinate-free Riemann / Levi-Civita tensor (that is the live upstream
    Mathlib effort — do not confuse the two); for ARBITRARY `(ginv, dg, ddg)` it is the formal
    coordinate expression, and tying it to an actual metric needs (carried, NOT proved here)
    `ginv = inverse(g)`, metric symmetry, and `dg`/`ddg` = the actual partial derivatives.

  • This is Phase 1 (coordinate flavor) of `HEAT_KERNEL_GAP_PLAN.md`. It does NOT discharge
    `a₁ = R/6` — that identity is the heat-kernel / Seeley–DeWitt expansion (Phases 3–4), the deep
    wall, entirely unaffected by having `R` as an object. Scalar `R` here just makes the
    `SeeleyDeWittData.R` field a computable geometric quantity.

  • NOT the conjecture, NOT the strong holographic principle, NOT QG.
    No axioms, no `sorry`.

The metric's 0/1/2-jet is carried as DATA:
  * `ginv`      : the inverse metric `g^{kl}` at the point,
  * `dg a`      : first partials `∂ₐ g_{jl}`,
  * `ddg a b`   : second partials `∂ₐ∂ᵦ g_{cd}`.
Christoffel / Riemann / Ricci / scalar-R are pure algebraic `Finset.sum` contractions.

UNIFIED WITH THE CANONICAL BASE: `QIQTH.CurvatureBridge.scalarCurvature_bridge` proves this jet-based
`scalarCurvature` EQUALS the field-based `QIQTH.Curvature.scalarCurv` (when the jets are the metric field's
actual derivatives + the carried `∂g⁻¹` identity). So this file is the *evaluable jet-interface* to the one
canonical component scalar-curvature base `Curvature.lean`, not a separate curvature — one base, two views.
-/
import Mathlib

open scoped BigOperators

namespace QIQTH.CoordinateCurvature

variable {ι : Type*} [Fintype ι]

/-- A metric / inverse-metric component array at a point. -/
abbrev Mat (ι : Type*) := Matrix ι ι ℝ

/-- `C_{ijl} = ∂ᵢ g_{jl} + ∂ⱼ g_{il} − ∂ₗ g_{ij}`. -/
def lowerGamma (dg : ι → Mat ι) (i j l : ι) : ℝ := dg i j l + dg j i l - dg l i j

/-- `Γᵏ_{ij} = ½ Σ_l g^{kl} C_{ijl}`. -/
noncomputable def christoffel (ginv : Mat ι) (dg : ι → Mat ι) (k i j : ι) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : ι, ginv k l * lowerGamma dg i j l

/-- Algebraic `∂ₐ g^{kl} = −Σ_{p,q} g^{kp} (∂ₐ g_{pq}) g^{ql}` (the `∂(g⁻¹)=−g⁻¹dg g⁻¹` identity,
    DEFINED into the formula rather than differentiated). -/
def dInvMetric (ginv : Mat ι) (dg : ι → Mat ι) (a k l : ι) : ℝ :=
  - ∑ p : ι, ∑ q : ι, ginv k p * dg a p q * ginv q l

/-- `∂ₐ C_{ijl}`; here `ddg a b c d = ∂ₐ∂ᵦ g_{cd}`. -/
def dLowerGamma (ddg : ι → ι → Mat ι) (a i j l : ι) : ℝ :=
  ddg a i j l + ddg a j i l - ddg a l i j

/-- `∂ₐ Γᵏ_{ij}` written in terms of a supplied `dginv = ∂ₐ g^{kl}`. -/
noncomputable def dChristoffelOfDInv (ginv : Mat ι) (dg : ι → Mat ι) (ddg : ι → ι → Mat ι)
    (dginv : ι → Mat ι) (a k i j : ι) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : ι,
    (dginv a k l * lowerGamma dg i j l + ginv k l * dLowerGamma ddg a i j l)

/-- Algebraic `∂ₐ Γᵏ_{ij}` from the 2-jet, with `∂ₐ g^{kl}` given by `dInvMetric`. -/
noncomputable def dChristoffel (ginv : Mat ι) (dg : ι → Mat ι) (ddg : ι → ι → Mat ι) (a k i j : ι) : ℝ :=
  dChristoffelOfDInv ginv dg ddg (fun a k l => dInvMetric ginv dg a k l) a k i j

/-- `Rᵏ_{sij}` from `Γ` and `∂Γ` (generic). Convention: the unit sphere gives scalar curvature `+2`. -/
def riemannOf (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) (k s i j : ι) : ℝ :=
  dΓ i k j s - dΓ j k i s + (∑ l : ι, Γ k i l * Γ l j s) - (∑ l : ι, Γ k j l * Γ l i s)

/-- `Rᵏ_{sij}` assembled from the metric 2-jet. -/
noncomputable def riemann (ginv : Mat ι) (dg : ι → Mat ι) (ddg : ι → ι → Mat ι) (k s i j : ι) : ℝ :=
  riemannOf (christoffel ginv dg) (dChristoffel ginv dg ddg) k s i j

/-- `Ric_{sj} = Σₖ Rᵏ_{skj}`. -/
noncomputable def ricci (ginv : Mat ι) (dg : ι → Mat ι) (ddg : ι → ι → Mat ι) (s j : ι) : ℝ :=
  ∑ k : ι, riemann ginv dg ddg k s k j

/-- ★★ Scalar curvature `R = Σ_{s,j} g^{sj} Ric_{sj}`. -/
noncomputable def scalarCurvature (ginv : Mat ι) (dg : ι → Mat ι) (ddg : ι → ι → Mat ι) : ℝ :=
  ∑ s : ι, ∑ j : ι, ginv s j * ricci ginv dg ddg s j

/-- Flat / zero-jet metric ⟹ scalar curvature `0`. -/
@[simp] theorem scalarCurvature_flat_zeroJet (ginv : Mat ι) :
    scalarCurvature ginv (fun _ => (0 : Mat ι)) (fun _ _ => (0 : Mat ι)) = 0 := by
  simp [scalarCurvature, ricci, riemann, riemannOf, christoffel, dChristoffel,
    dChristoffelOfDInv, dInvMetric, lowerGamma, dLowerGamma]

/-! ## Cross-check 1 — cone / polar-flat metric `dr² + 4 r² dθ²` at `r = 1`.

Flat away from the apex, so `R = 0`. This validates that the pipeline vanishes on a
genuinely nonzero 2-jet (unlike the trivial zero-jet check). -/
namespace ConeCheck

/-- Inverse metric `diag(1, ¼)` of `dr² + 4 r² dθ²` at `r = 1`. -/
noncomputable def coneGinv : Mat (Fin 2) := !![(1 : ℝ), 0; 0, 1/4]

/-- `∂ₐ g_{ij}` for the cone at `r = 1`: `∂_r g_{θθ} = 8`, all else `0`. -/
def coneDg (a i j : Fin 2) : ℝ := if a = 0 ∧ i = 1 ∧ j = 1 then 8 else 0

/-- `∂ₐ∂ᵦ g_{ij}` for the cone at `r = 1`: `∂_r∂_r g_{θθ} = 8`, all else `0`. -/
def coneDdg (a b i j : Fin 2) : ℝ := if a = 0 ∧ b = 0 ∧ i = 1 ∧ j = 1 then 8 else 0

/-- The cone is flat: `R = 0`. -/
theorem scalarCurvature_cone :
    scalarCurvature coneGinv (fun a => Matrix.of fun i j => coneDg a i j)
      (fun a b => Matrix.of fun i j => coneDdg a b i j) = 0 := by
  norm_num [scalarCurvature, ricci, riemann, riemannOf, christoffel, dChristoffel,
    dChristoffelOfDInv, dInvMetric, lowerGamma, dLowerGamma, coneGinv, coneDg, coneDdg,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

end ConeCheck

/-! ## Cross-check 2 — ★ unit 2-sphere at the equator (nonzero, sign-sensitive).

At the equator the metric is the identity (`g = 1`), first partials vanish, and the only
nonvanishing second partial is `∂_θ∂_θ g_{φφ} = -2`. Scalar curvature of the unit sphere is `+2`.
This catches sign errors that the flat checks cannot. -/
namespace SphereCheck

/-- Inverse metric `= 1` at the equator. -/
def sphGinv : Mat (Fin 2) := (1 : Mat (Fin 2))

/-- First partials all vanish at the equator. -/
def sphDg (_a _i _j : Fin 2) : ℝ := 0

/-- `∂ₐ∂ᵦ g_{ij}` at the equator: `∂_θ∂_θ g_{φφ} = -2`, all else `0`. -/
def sphDdg (a b i j : Fin 2) : ℝ := if a = 0 ∧ b = 0 ∧ i = 1 ∧ j = 1 then -2 else 0

/-- ★ The unit 2-sphere has scalar curvature `+2`. -/
theorem scalarCurvature_sphere :
    scalarCurvature sphGinv (fun a => Matrix.of fun i j => sphDg a i j)
      (fun a b => Matrix.of fun i j => sphDdg a b i j) = 2 := by
  norm_num [scalarCurvature, ricci, riemann, riemannOf, christoffel, dChristoffel,
    dChristoffelOfDInv, dInvMetric, lowerGamma, dLowerGamma, sphGinv, sphDg, sphDdg,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.one_apply]

end SphereCheck

end QIQTH.CoordinateCurvature
