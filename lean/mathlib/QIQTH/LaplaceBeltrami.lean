/-
  LaplaceBeltrami — the coordinate Laplace–Beltrami operator on functions.

  The FIRST brick of the P2 heat-kernel parametrix build: the operator `Δ_g` appearing in the heat
  equation `(∂_t − Δ_g)K = 0` and the parametrix error estimate, built componentwise in a fixed
  coordinate chart `Point n = Fin n → ℝ` (matching `QIQTH.Curvature`), as multivariable calculus.

  Invariant form (scalar Laplacian):
      `Δ_g f = g^{ij} (∂_i ∂_j f − Γ^k_{ij} ∂_k f)`.

  This file builds:
    • `laplaceBeltrami` — the definition, reusing `QIQTH.Curvature.pd` / `christoffel`.
    • linearity (`laplaceBeltrami_add`, `laplaceBeltrami_const_mul`) — the C² algebra;
    • `laplaceBeltrami_at_rnc_center` — at a Riemannian-normal-coordinate center (`g^{ij}=δ`, `Γ=0`)
      `Δ_g` reduces to the FLAT Laplacian `∑_i ∂_i² f`, the fact linking it to the flat heat operator
      and to `QIQTH.DeWittDiagonal.analyticLapQuadAtZero`;
    • `laplaceBeltrami_quadratic_at_center` — on a quadratic `f = ∑ Q_{ab} y_a y_b`, at an RNC center,
      `Δ_g f = 2·∑_a Q_{aa}` (the trace), matching `DeWittDiagonal.analyticLapQuadAtZero_eq_trace`.

  It does NOT build the heat semigroup / kernel / parametrix convergence, nor the general `a₁ = R/6`
  (those are P2b–e, the deep analytic wall).  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.Curvature

open Finset
open QIQTH.Curvature

namespace QIQTH.LaplaceBeltrami

variable {n : ℕ}

/-- **The coordinate Laplace–Beltrami operator on scalars**
    `Δ_g f (x) = ∑_{i,j} g^{ij}(x) (∂_i∂_j f − ∑_k Γ^k_{ij} ∂_k f)`.
    Here `gi x i j = g^{ij}` (inverse metric, upper indices) and
    `christoffel g gi k i j x = Γ^k_{ij}` (upper `k`, lower `i j`), matching `QIQTH.Curvature`. -/
noncomputable def laplaceBeltrami (g gi : Point n → Fin n → Fin n → ℝ) (f : Point n → ℝ)
    (x : Point n) : ℝ :=
  ∑ i, ∑ j, gi x i j *
    (pd (fun y => pd f j y) i x - ∑ k, christoffel g gi k i j x * pd f k x)

/-! ### Linearity (the C² algebra) -/

/-- **Additivity** `Δ_g(f+h) = Δ_g f + Δ_g h`, for `C²` (here `C^∞`) fields. -/
theorem laplaceBeltrami_add (g gi : Point n → Fin n → Fin n → ℝ) (f h : Point n → ℝ) (x : Point n)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h) :
    laplaceBeltrami g gi (fun y => f y + h y) x
      = laplaceBeltrami g gi f x + laplaceBeltrami g gi h x := by
  simp only [laplaceBeltrami]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsec : (fun y => pd (fun z => f z + h z) j y) = (fun y => pd f j y + pd h j y) := by
    funext y; exact pd_add f h j y (PdiffAt_of_contDiff f hf j y) (PdiffAt_of_contDiff h hh j y)
  rw [hsec, pd_add (fun y => pd f j y) (fun y => pd h j y) i x
      (PdiffAt_pd f hf j i x) (PdiffAt_pd h hh j i x)]
  have hΓ : (∑ k, christoffel g gi k i j x * pd (fun z => f z + h z) k x)
      = (∑ k, christoffel g gi k i j x * pd f k x)
        + (∑ k, christoffel g gi k i j x * pd h k x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_add f h k x (PdiffAt_of_contDiff f hf k x) (PdiffAt_of_contDiff h hh k x)]; ring
  rw [hΓ]; ring

/-- **Homogeneity** `Δ_g(c·f) = c·Δ_g f`, for a `C²` (here `C^∞`) field. -/
theorem laplaceBeltrami_const_mul (g gi : Point n → Fin n → Fin n → ℝ) (c : ℝ) (f : Point n → ℝ)
    (x : Point n) (hf : ContDiff ℝ ⊤ f) :
    laplaceBeltrami g gi (fun y => c * f y) x = c * laplaceBeltrami g gi f x := by
  simp only [laplaceBeltrami]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsec : (fun y => pd (fun z => c * f z) j y) = (fun y => c * pd f j y) := by
    funext y; exact pd_const_mul c f j y (PdiffAt_of_contDiff f hf j y)
  rw [hsec, pd_const_mul c (fun y => pd f j y) i x (PdiffAt_pd f hf j i x)]
  have hΓ : (∑ k, christoffel g gi k i j x * pd (fun z => c * f z) k x)
      = c * ∑ k, christoffel g gi k i j x * pd f k x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_const_mul c f k x (PdiffAt_of_contDiff f hf k x)]; ring
  rw [hΓ]; ring

/-! ### RNC-center reduction: `Δ_g` becomes the flat Laplacian at a normal-coordinate center -/

/-- **At a Riemannian-normal-coordinate center** — where `g^{ij}(x₀) = δ^{ij}` and every Christoffel
    symbol vanishes, `Γ^k_{ij}(x₀) = 0` — the Laplace–Beltrami operator reduces to the FLAT Laplacian
    `Δ_g f (x₀) = ∑_i ∂_i² f (x₀)`.  This is the fact linking `Δ_g` to the flat heat operator and to
    `QIQTH.DeWittDiagonal.analyticLapQuadAtZero`. -/
theorem laplaceBeltrami_at_rnc_center (g gi : Point n → Fin n → Fin n → ℝ) (f : Point n → ℝ)
    (x₀ : Point n) (hgi : ∀ i j, gi x₀ i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j x₀ = 0) :
    laplaceBeltrami g gi f x₀ = ∑ i, pd (fun y => pd f i y) i x₀ := by
  simp only [laplaceBeltrami, hgi, hΓ, zero_mul, Finset.sum_const_zero, sub_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (∑ j, (if i = j then (1:ℝ) else 0) * pd (fun y => pd f j y) i x₀)
      = ∑ j, (if i = j then pd (fun y => pd f j y) i x₀ else 0) from
        Finset.sum_congr rfl (fun j _ => by split <;> simp)]
  rw [Finset.sum_ite_eq]
  simp

/-! ### The flat Laplacian of a quadratic (matching `DeWittDiagonal.analyticLapQuadAtZero_eq_trace`) -/

/-- Partial derivative of a coordinate function: `∂_i (y ↦ y_a) = δ_{ai}`. -/
lemma pd_coord (a i : Fin n) (x : Point n) :
    pd (fun y => y a) i x = if a = i then 1 else 0 := by
  simp only [pd, Function.update_apply]
  by_cases h : a = i
  · subst h; simp
  · simp [h]

/-- A coordinate function is partially differentiable in every direction. -/
lemma PdiffAt_coord (a i : Fin n) (x : Point n) : PdiffAt (fun y => y a) i x := by
  by_cases h : a = i
  · subst h
    have hfun : (fun t => (Function.update x a t) a) = fun t => t := by
      funext t; simp
    simp only [PdiffAt, hfun]; fun_prop
  · have hfun : (fun t => (Function.update x i t) a) = fun _ => x a := by
      funext t; rw [Function.update_apply]; simp [h]
    simp only [PdiffAt, hfun]; exact differentiableAt_const _

/-- A constant multiple of a coordinate function is partially differentiable. -/
lemma PdiffAt_const_mul_coord (c : ℝ) (b i : Fin n) (x : Point n) :
    PdiffAt (fun y => c * y b) i x :=
  (PdiffAt_coord b i x).const_mul c

/-- A monomial `y_a·y_b` is partially differentiable in every direction. -/
lemma PdiffAt_mono (a b i : Fin n) (x : Point n) : PdiffAt (fun z => z a * z b) i x :=
  (PdiffAt_coord a i x).mul (PdiffAt_coord b i x)

/-- A single quadratic term `Q_{ab} y_a y_b` is partially differentiable in every direction. -/
lemma PdiffAt_term (Q : Fin n → Fin n → ℝ) (a b i : Fin n) (x : Point n) :
    PdiffAt (fun z => Q a b * z a * z b) i x :=
  (PdiffAt_const_mul_coord (Q a b) a i x).mul (PdiffAt_coord b i x)

/-- `∂_i(y ↦ y_a y_b) = δ_{ai} y_b + y_a δ_{bi}`. -/
lemma pd_mono (a b i : Fin n) (x : Point n) :
    pd (fun y => y a * y b) i x
      = (if a = i then (1:ℝ) else 0) * x b + x a * (if b = i then 1 else 0) := by
  rw [pd_mul (fun y => y a) (fun y => y b) i x (PdiffAt_coord a i x) (PdiffAt_coord b i x),
      pd_coord a i x, pd_coord b i x]

/-- `∂_i(y ↦ Q_{ab} y_a y_b) = (Q_{ab} δ_{ai}) y_b + (Q_{ab} δ_{bi}) y_a`. -/
lemma pd_term_eq (Q : Fin n → Fin n → ℝ) (a b i : Fin n) (y : Point n) :
    pd (fun z => Q a b * z a * z b) i y
      = (Q a b * (if a = i then (1:ℝ) else 0)) * y b
        + (Q a b * (if b = i then (1:ℝ) else 0)) * y a := by
  have e : (fun z : Point n => Q a b * z a * z b) = (fun z => Q a b * (z a * z b)) := by
    funext z; ring
  rw [e, pd_const_mul (Q a b) (fun z => z a * z b) i y (PdiffAt_mono a b i y), pd_mono a b i y]
  ring

/-- The first partial `∂_i(y ↦ Q_{ab} y_a y_b)` is itself partially differentiable. -/
lemma PdiffAt_pd_term (Q : Fin n → Fin n → ℝ) (a b i : Fin n) (x : Point n) :
    PdiffAt (fun y => pd (fun z => Q a b * z a * z b) i y) i x := by
  have hfun : (fun y => pd (fun z => Q a b * z a * z b) i y)
      = (fun y => (Q a b * (if a = i then (1:ℝ) else 0)) * y b
          + (Q a b * (if b = i then (1:ℝ) else 0)) * y a) :=
    funext (fun y => pd_term_eq Q a b i y)
  rw [hfun]
  exact (PdiffAt_const_mul_coord _ b i x).add (PdiffAt_const_mul_coord _ a i x)

/-- The flat second partial of a single term: `∂_i²(Q_{ab} y_a y_b) = 2 Q_{ab} δ_{ai} δ_{bi}`. -/
lemma pd_pd_term (Q : Fin n → Fin n → ℝ) (a b i : Fin n) (x : Point n) :
    pd (fun y => pd (fun z => Q a b * z a * z b) i y) i x
      = 2 * Q a b * (if a = i then (1:ℝ) else 0) * (if b = i then 1 else 0) := by
  have hfun : (fun y => pd (fun z => Q a b * z a * z b) i y)
      = (fun y => (Q a b * (if a = i then (1:ℝ) else 0)) * y b
          + (Q a b * (if b = i then (1:ℝ) else 0)) * y a) :=
    funext (fun y => pd_term_eq Q a b i y)
  rw [hfun]
  rw [pd_add (fun y => (Q a b * (if a = i then (1:ℝ) else 0)) * y b)
             (fun y => (Q a b * (if b = i then (1:ℝ) else 0)) * y a) i x
       (PdiffAt_const_mul_coord _ b i x) (PdiffAt_const_mul_coord _ a i x)]
  rw [pd_const_mul (Q a b * (if a = i then (1:ℝ) else 0)) (fun y => y b) i x (PdiffAt_coord b i x)]
  rw [pd_const_mul (Q a b * (if b = i then (1:ℝ) else 0)) (fun y => y a) i x (PdiffAt_coord a i x)]
  rw [pd_coord b i x, pd_coord a i x]; ring

/-- `∑_i δ_{ai} δ_{bi} = δ_{ab}`. -/
lemma sum_delta_delta (a b : Fin n) :
    (∑ i, (if a = i then (1:ℝ) else 0) * (if b = i then 1 else 0)) = if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst h
    have hidem : ∀ i, (if a = i then (1:ℝ) else 0) * (if a = i then 1 else 0)
        = if a = i then 1 else 0 := fun i => by split <;> simp
    rw [Finset.sum_congr rfl (fun i _ => hidem i), Finset.sum_ite_eq]; simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : a = i
    · subst hi; simp [Ne.symm h]
    · rw [if_neg hi, zero_mul]

/-- **The flat Laplacian of a quadratic equals twice its trace**:
    `∑_i ∂_i² (∑_{a,b} Q_{ab} y_a y_b) = 2 ∑_a Q_{aa}` — the `pd`-calculus counterpart of
    `QIQTH.DeWittDiagonal.analyticLapQuadAtZero_eq_trace`. -/
lemma flatLap_quadratic (Q : Fin n → Fin n → ℝ) (x : Point n) :
    (∑ i, pd (fun y => pd (fun z => ∑ a, ∑ b, Q a b * z a * z b) i y) i x)
      = 2 * ∑ a, Q a a := by
  classical
  -- inner first partial as a double sum
  have hf1 : ∀ (y : Point n) (i' : Fin n),
      pd (fun z => ∑ a, ∑ b, Q a b * z a * z b) i' y
        = ∑ a, ∑ b, pd (fun z => Q a b * z a * z b) i' y := by
    intro y i'
    rw [pd_sum univ (fun a => fun z => ∑ b, Q a b * z a * z b) i' y
        (fun a _ => PdiffAt_sum univ (fun b => fun z => Q a b * z a * z b) i' y
          (fun b _ => PdiffAt_term Q a b i' y))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pd_sum univ (fun b => fun z => Q a b * z a * z b) i' y
        (fun b _ => PdiffAt_term Q a b i' y)]
  -- second partial as a double sum of single-term second partials
  have hsecond : ∀ i' : Fin n,
      pd (fun y => pd (fun z => ∑ a, ∑ b, Q a b * z a * z b) i' y) i' x
        = ∑ a, ∑ b, 2 * Q a b * (if a = i' then (1:ℝ) else 0) * (if b = i' then 1 else 0) := by
    intro i'
    rw [show (fun y => pd (fun z => ∑ a, ∑ b, Q a b * z a * z b) i' y)
        = (fun y => ∑ a, ∑ b, pd (fun z => Q a b * z a * z b) i' y) from
          funext (fun y => hf1 y i')]
    rw [pd_sum univ (fun a => fun y => ∑ b, pd (fun z => Q a b * z a * z b) i' y) i' x
        (fun a _ => PdiffAt_sum univ (fun b => fun y => pd (fun z => Q a b * z a * z b) i' y) i' x
          (fun b _ => PdiffAt_pd_term Q a b i' x))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pd_sum univ (fun b => fun y => pd (fun z => Q a b * z a * z b) i' y) i' x
        (fun b _ => PdiffAt_pd_term Q a b i' x)]
    exact Finset.sum_congr rfl fun b _ => pd_pd_term Q a b i' x
  rw [Finset.sum_congr rfl (fun i _ => hsecond i)]
  -- reorder (bring `i` innermost) and collapse the delta sums
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  -- for fixed `a`: ∑ b, ∑ i, (2 Q a b δ_{ai}) δ_{bi} = 2 Q a a
  rw [Finset.sum_congr rfl (fun b _ =>
      show (∑ i, 2 * Q a b * (if a = i then (1:ℝ) else 0) * (if b = i then 1 else 0))
          = (if a = b then (2 * Q a b) else 0) from by
        rw [show (∑ i, 2 * Q a b * (if a = i then (1:ℝ) else 0) * (if b = i then 1 else 0))
            = (2 * Q a b) * ∑ i, (if a = i then (1:ℝ) else 0) * (if b = i then 1 else 0) from by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
        rw [sum_delta_delta a b]; split <;> simp)]
  rw [Finset.sum_ite_eq]; simp

/-- **On a quadratic, at an RNC center**: for `f = ∑_{a,b} Q_{ab} y_a y_b`, at a normal-coordinate
    center (`g^{ij}(x₀)=δ`, `Γ(x₀)=0`), `Δ_g f (x₀) = 2 ∑_a Q_{aa}` (twice the trace).
    Matches `QIQTH.DeWittDiagonal.analyticLapQuadAtZero_eq_trace`. -/
theorem laplaceBeltrami_quadratic_at_center (g gi : Point n → Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (x₀ : Point n)
    (hgi : ∀ i j, gi x₀ i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j x₀ = 0) :
    laplaceBeltrami g gi (fun y => ∑ a, ∑ b, Q a b * y a * y b) x₀ = 2 * ∑ a, Q a a := by
  rw [laplaceBeltrami_at_rnc_center g gi (fun y => ∑ a, ∑ b, Q a b * y a * y b) x₀ hgi hΓ]
  exact flatLap_quadratic Q x₀

end QIQTH.LaplaceBeltrami
