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

/-- Partial differentiability of `f` at `x` along coordinate `i` (the analytic hypothesis for the
    `pd` algebra below). -/
def PdiffAt (f : Point n → ℝ) (i : Fin n) (x : Point n) : Prop :=
  DifferentiableAt ℝ (fun t => f (Function.update x i t)) (x i)

/-- `∂ᵢ(f+g) = ∂ᵢf + ∂ᵢg`. -/
theorem pd_add (f g : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : PdiffAt f i x) (hg : PdiffAt g i x) :
    pd (fun y => f y + g y) i x = pd f i x + pd g i x := by
  simp only [pd]; exact deriv_add hf hg

/-- `∂ᵢ(f−g) = ∂ᵢf − ∂ᵢg`. -/
theorem pd_sub (f g : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : PdiffAt f i x) (hg : PdiffAt g i x) :
    pd (fun y => f y - g y) i x = pd f i x - pd g i x := by
  simp only [pd]; exact deriv_sub hf hg

/-- `∂ᵢ(c·f) = c·∂ᵢf`. -/
theorem pd_const_mul (c : ℝ) (f : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : PdiffAt f i x) :
    pd (fun y => c * f y) i x = c * pd f i x := by
  simp only [pd]; exact deriv_const_mul c hf

/-- `∂ᵢ(const) = 0`. -/
theorem pd_const (c : ℝ) (i : Fin n) (x : Point n) : pd (fun _ => c) i x = 0 := by
  simp only [pd]; exact deriv_const _ _

/-- A smooth field is partially differentiable in every direction at every point. -/
theorem PdiffAt_of_contDiff (f : Point n → ℝ) (hf : ContDiff ℝ ⊤ f) (i : Fin n) (x : Point n) :
    PdiffAt f i x := by
  have hg : DifferentiableAt ℝ f ((Function.update x i) (x i)) := by
    rw [Function.update_eq_self]; exact (hf.differentiable (by simp)).differentiableAt
  exact hg.comp (x i) (hasDerivAt_update x i (x i)).differentiableAt

/-- A product of partially-differentiable fields is partially differentiable. -/
theorem PdiffAt.mul {f g : Point n → ℝ} {i : Fin n} {x : Point n}
    (hf : PdiffAt f i x) (hg : PdiffAt g i x) : PdiffAt (fun y => f y * g y) i x :=
  DifferentiableAt.mul hf hg

/-- Difference of partially-differentiable fields. -/
theorem PdiffAt.sub {f g : Point n → ℝ} {i : Fin n} {x : Point n}
    (hf : PdiffAt f i x) (hg : PdiffAt g i x) : PdiffAt (fun y => f y - g y) i x :=
  DifferentiableAt.sub hf hg

/-- Sum of partially-differentiable fields. -/
theorem PdiffAt.add {f g : Point n → ℝ} {i : Fin n} {x : Point n}
    (hf : PdiffAt f i x) (hg : PdiffAt g i x) : PdiffAt (fun y => f y + g y) i x :=
  DifferentiableAt.add hf hg

/-- A finite sum of partially-differentiable fields is partially differentiable. -/
theorem PdiffAt_sum {ι : Type*} (s : Finset ι) (F : ι → Point n → ℝ) (i : Fin n) (x : Point n)
    (hF : ∀ k ∈ s, PdiffAt (F k) i x) : PdiffAt (fun y => ∑ k ∈ s, F k y) i x :=
  DifferentiableAt.fun_sum (fun k hk => hF k hk)

/-- `∂ᵢ` commutes with finite sums: `∂ᵢ(∑ₖ fₖ) = ∑ₖ ∂ᵢfₖ`. -/
theorem pd_sum {ι : Type*} (s : Finset ι) (F : ι → Point n → ℝ) (i : Fin n) (x : Point n)
    (hF : ∀ k ∈ s, PdiffAt (F k) i x) :
    pd (fun y => ∑ k ∈ s, F k y) i x = ∑ k ∈ s, pd (F k) i x := by
  simp only [pd]
  exact deriv_fun_sum (fun k hk => hF k hk)

/-- **Leibniz rule** `∂ᵢ(f·g) = (∂ᵢf)·g + f·(∂ᵢg)`. -/
theorem pd_mul (f g : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : PdiffAt f i x) (hg : PdiffAt g i x) :
    pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  have h := deriv_mul hf hg
  simp only [Function.update_eq_self] at h
  simpa only [pd] using h

/-- **`pd` as a directional `fderiv`**: `∂ᵢ g (x) = Dg(x)[eᵢ]` for `g` differentiable at `x`. The bridge
    from the coordinate partial derivative to the Fréchet derivative (chain rule through `update`). -/
theorem pd_eq_fderiv (g : Point n → ℝ) (i : Fin n) (x : Point n) (hg : DifferentiableAt ℝ g x) :
    pd g i x = fderiv ℝ g x (Pi.single i 1) := by
  have hu : HasDerivAt (Function.update x i) (Pi.single i (1 : ℝ)) (x i) := hasDerivAt_update x i (x i)
  have hg' : HasFDerivAt g (fderiv ℝ g x) ((Function.update x i) (x i)) := by
    rw [Function.update_eq_self]; exact hg.hasFDerivAt
  have h := (hg'.comp_hasDerivAt (x i) hu).deriv
  simpa only [pd, Function.comp] using h

/-- A mixed second partial equals the second Fréchet derivative bilinear form on the basis vectors. -/
theorem pd_pd_eq (f : Point n → ℝ) (i j : Fin n) (x : Point n) (hf : ContDiff ℝ ⊤ f) :
    pd (fun y => pd f j y) i x
      = fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hfd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ⊤) le_top).differentiable (by simp)
  have e1 : (fun y => pd f j y) = (fun y => (fderiv ℝ f y) (Pi.single j 1)) :=
    funext (fun y => pd_eq_fderiv f j y (hfd y))
  rw [e1, pd_eq_fderiv _ i x ((hfd2 x).clm_apply (differentiableAt_const _)),
      fderiv_clm_apply (hfd2 x) (differentiableAt_const _)]
  simp [fderiv_const]

/-- **Schwarz: mixed partial derivatives commute** `∂ᵢ∂ⱼ f = ∂ⱼ∂ᵢ f` for smooth `f`. The analytic
    keystone for the second Bianchi identity. -/
theorem pd_comm (f : Point n → ℝ) (i j : Fin n) (x : Point n) (hf : ContDiff ℝ ⊤ f) :
    pd (fun y => pd f j y) i x = pd (fun y => pd f i y) j x := by
  rw [pd_pd_eq f i j x hf, pd_pd_eq f j i x hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt le_top).eq _ _

/-- The partial derivative `∂_d f` of a smooth field is itself partially differentiable in any
    direction (`f ∈ C^∞` ⇒ `∂_d f ∈ C^∞` ⇒ differentiable). -/
theorem PdiffAt_pd (f : Point n → ℝ) (hf : ContDiff ℝ ⊤ f) (d e : Fin n) (z : Point n) :
    PdiffAt (fun y => pd f d y) e z := by
  have hfd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ⊤) le_top).differentiable (by simp)
  have hrw : (fun y => pd f d y) = (fun y => fderiv ℝ f y (Pi.single d 1)) :=
    funext (fun y => pd_eq_fderiv _ d y (hf.differentiable (by simp) y))
  have hu : DifferentiableAt ℝ (Function.update z e) (z e) :=
    (hasDerivAt_update z e (z e)).differentiableAt
  have hg : DifferentiableAt ℝ (fderiv ℝ f) ((Function.update z e) (z e)) := by
    rw [Function.update_eq_self]; exact hfd2 z
  rw [hrw]
  exact (hg.comp (z e) hu).clm_apply (differentiableAt_const _)

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

/-- **Covariant derivative of a (2,0) tensor** `T^{μρ}`:
    `∇_ν T^{μρ} = ∂_ν T^{μρ} + Γ^μ_{νκ} T^{κρ} + Γ^ρ_{νκ} T^{μκ}`. -/
noncomputable def covDeriv20 (g gi : Point n → Fin n → Fin n → ℝ)
    (T : Point n → Fin n → Fin n → ℝ) (ν μ ρ : Fin n) (x : Point n) : ℝ :=
  pd (fun y => T y μ ρ) ν x
    + ∑ κ, christoffel g gi μ ν κ x * T x κ ρ
    + ∑ κ, christoffel g gi ρ ν κ x * T x μ κ

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

/-! ### Toward metric compatibility ∇g = 0 (the defining Levi-Civita property) -/

/-- **Inverse-metric contraction.** For `gi` a right-inverse of the (symmetric) metric `g` at `x`,
    lowering an upper index then contracting returns the original: `∑σ g_{σν} (∑α g^{σα} w_α) = w_ν`. -/
theorem inv_contract (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x : Point n)
    (hinv : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0)
    (ν : Fin n) (w : Fin n → ℝ) :
    (∑ σ, g x σ ν * (∑ α, gi x σ α * w α)) = w ν := by
  have hginv : ∀ α, (∑ σ, g x σ ν * gi x σ α) = (if ν = α then 1 else 0) := by
    intro α
    have h2 : (∑ σ, g x σ ν * gi x σ α) = ∑ σ, g x ν σ * gi x σ α :=
      Finset.sum_congr rfl (fun σ _ => by rw [hsymm x σ ν])
    rw [h2, hinv ν α]
  calc (∑ σ, g x σ ν * (∑ α, gi x σ α * w α))
      = ∑ σ, ∑ α, g x σ ν * (gi x σ α * w α) := by
        apply Finset.sum_congr rfl; intro σ _; rw [Finset.mul_sum]
    _ = ∑ α, ∑ σ, g x σ ν * (gi x σ α * w α) := Finset.sum_comm
    _ = ∑ α, (∑ σ, g x σ ν * gi x σ α) * w α := by
        apply Finset.sum_congr rfl; intro α _
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro σ _; ring
    _ = ∑ α, (if ν = α then 1 else 0) * w α := by
        apply Finset.sum_congr rfl; intro α _; rw [hginv α]
    _ = w ν := by
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Lowered Christoffel symbol** `Γ_{νλμ} = ∑σ g_{σν} Γ^σ_{λμ} = ½(∂_λ g_{νμ} + ∂_μ g_{νλ} − ∂_ν g_{λμ})`
    — the inverse metric in Γ is cancelled by the lowering, via `inv_contract`. -/
theorem christoffel_lower (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x : Point n)
    (hinv : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0)
    (ν lam mu : Fin n) :
    (∑ σ, g x σ ν * christoffel g gi σ lam mu x)
      = (1 / 2) * (pd (fun y => g y ν mu) lam x + pd (fun y => g y ν lam) mu x
               - pd (fun y => g y lam mu) ν x) := by
  simp only [christoffel]
  rw [show (∑ σ, g x σ ν * ((1 / 2) * ∑ α, gi x σ α *
            (pd (fun y => g y α mu) lam x + pd (fun y => g y α lam) mu x
              - pd (fun y => g y lam mu) α x)))
        = (1 / 2) * (∑ σ, g x σ ν * (∑ α, gi x σ α *
            (pd (fun y => g y α mu) lam x + pd (fun y => g y α lam) mu x
              - pd (fun y => g y lam mu) α x)))
      from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun σ _ => by ring)]
  congr 1
  exact inv_contract g gi hsymm x hinv ν _

/-- **Metric compatibility `∇_λ g_{μν} = 0`** — the defining property of the Levi-Civita connection,
    now a THEOREM from the Christoffel definition (via `christoffel_lower`) + metric symmetry. (Needs only
    that `gi` is the inverse and `g` is symmetric — no smoothness, since `∇g` is algebraic in the `∂g`.) -/
theorem metric_compat (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x : Point n)
    (hinv : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0)
    (lam mu ν : Fin n) :
    covDeriv02 g gi g lam mu ν x = 0 := by
  simp only [covDeriv02]
  rw [show (∑ σ, christoffel g gi σ lam mu x * g x σ ν)
        = ∑ σ, g x σ ν * christoffel g gi σ lam mu x
      from Finset.sum_congr rfl (fun σ _ => mul_comm _ _)]
  rw [show (∑ σ, christoffel g gi σ lam ν x * g x mu σ)
        = ∑ σ, g x σ mu * christoffel g gi σ lam ν x
      from Finset.sum_congr rfl (fun σ _ => by rw [mul_comm]; rw [hsymm x mu σ])]
  rw [christoffel_lower g gi hsymm x hinv ν lam mu,
      christoffel_lower g gi hsymm x hinv mu lam ν]
  rw [show (fun y => g y ν mu) = (fun y => g y mu ν) from funext (fun y => hsymm y ν mu),
      show (fun y => g y ν lam) = (fun y => g y lam ν) from funext (fun y => hsymm y ν lam),
      show (fun y => g y lam mu) = (fun y => g y mu lam) from funext (fun y => hsymm y lam mu)]
  ring

/-! ### Layer 2 — the Bianchi identities -/

/-- **First Bianchi identity** (the algebraic/cyclic one): `R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0`,
    for the torsion-free (Levi-Civita) connection. Purely algebraic — the derivative terms cancel
    pairwise by Christoffel lower-symmetry (no Schwarz / mixed partials needed), and the quadratic ΓΓ
    sums cancel termwise. -/
theorem riemann_first_bianchi (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (ρ σ μ ν : Fin n) (x : Point n) :
    riemann g gi ρ σ μ ν x + riemann g gi ρ μ ν σ x + riemann g gi ρ ν σ μ x = 0 := by
  have hsum :
      (∑ l, (christoffel g gi ρ μ l x * christoffel g gi l ν σ x
           - christoffel g gi ρ ν l x * christoffel g gi l μ σ x))
    + (∑ l, (christoffel g gi ρ ν l x * christoffel g gi l σ μ x
           - christoffel g gi ρ σ l x * christoffel g gi l ν μ x))
    + (∑ l, (christoffel g gi ρ σ l x * christoffel g gi l μ ν x
           - christoffel g gi ρ μ l x * christoffel g gi l σ ν x)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro l _
    rw [christoffel_symm g gi hsymm l ν σ x, christoffel_symm g gi hsymm l μ σ x,
        christoffel_symm g gi hsymm l ν μ x]
    ring
  simp only [riemann]
  rw [show (fun y => christoffel g gi ρ ν σ y) = (fun y => christoffel g gi ρ σ ν y)
        from funext (fun y => christoffel_symm g gi hsymm ρ ν σ y),
      show (fun y => christoffel g gi ρ σ μ y) = (fun y => christoffel g gi ρ μ σ y)
        from funext (fun y => christoffel_symm g gi hsymm ρ σ μ y),
      show (fun y => christoffel g gi ρ μ ν y) = (fun y => christoffel g gi ρ ν μ y)
        from funext (fun y => christoffel_symm g gi hsymm ρ μ ν y)]
  linarith [hsum]

/-- **The derivative ("principal") part of the Riemann tensor** — `∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ}`, the
    part of `R^ρ_{σμν}` linear in `∂Γ` (the ΓΓ part dropped). -/
noncomputable def riemannLin (g gi : Point n → Fin n → Fin n → ℝ)
    (ρ σ μ ν : Fin n) (x : Point n) : ℝ :=
  pd (fun y => christoffel g gi ρ ν σ y) μ x - pd (fun y => christoffel g gi ρ μ σ y) ν x

/-- **The derivative part of the second Bianchi cyclic sum vanishes** — `∂_λ Rlin^ρ_{σμν} +
    ∂_μ Rlin^ρ_{σνλ} + ∂_ν Rlin^ρ_{σλμ} = 0` for smooth Christoffel symbols. This is the part of the
    second Bianchi identity that the SCHWARZ keystone (`pd_comm`) handles: the six second-derivative
    `∂∂Γ` terms cancel in pairs once mixed partials commute. (The full second Bianchi additionally needs
    the ΓΓ / Γ·R terms to cancel via the first Bianchi + Christoffel symmetry — the long general-coordinate
    remainder; see note 51.) -/
theorem second_bianchi_deriv_part
    (g gi : Point n → Fin n → Fin n → ℝ) (ρ σ lam mu ν : Fin n) (x : Point n)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y)) :
    pd (fun y => riemannLin g gi ρ σ mu ν y) lam x
      + pd (fun y => riemannLin g gi ρ σ ν lam y) mu x
      + pd (fun y => riemannLin g gi ρ σ lam mu y) ν x = 0 := by
  -- `∂_d Γ^a_{bc}` is partially differentiable in any direction at any point (Γ is smooth).
  have hpd : ∀ a b c d e (z : Point n),
      PdiffAt (fun y => pd (fun w => christoffel g gi a b c w) d y) e z := by
    intro a b c d e z
    have hfd2 : Differentiable ℝ (fderiv ℝ (fun w => christoffel g gi a b c w)) :=
      ((hC a b c).fderiv_right (m := ⊤) le_top).differentiable (by simp)
    have hrw : (fun y => pd (fun w => christoffel g gi a b c w) d y)
             = (fun y => fderiv ℝ (fun w => christoffel g gi a b c w) y (Pi.single d 1)) :=
      funext (fun y => pd_eq_fderiv _ d y ((hC a b c).differentiable (by simp) y))
    have hu : DifferentiableAt ℝ (Function.update z e) (z e) :=
      (hasDerivAt_update z e (z e)).differentiableAt
    have hg : DifferentiableAt ℝ (fderiv ℝ (fun w => christoffel g gi a b c w))
        ((Function.update z e) (z e)) := by
      rw [Function.update_eq_self]; exact hfd2 z
    rw [hrw]
    exact (hg.comp (z e) hu).clm_apply (differentiableAt_const _)
  simp only [riemannLin]
  rw [pd_sub _ _ lam x (hpd ρ ν σ mu lam x) (hpd ρ mu σ ν lam x),
      pd_sub _ _ mu x (hpd ρ lam σ ν mu x) (hpd ρ ν σ lam mu x),
      pd_sub _ _ ν x (hpd ρ mu σ lam ν x) (hpd ρ lam σ mu ν x)]
  rw [pd_comm (fun w => christoffel g gi ρ ν σ w) lam mu x (hC ρ ν σ),
      pd_comm (fun w => christoffel g gi ρ mu σ w) lam ν x (hC ρ mu σ),
      pd_comm (fun w => christoffel g gi ρ lam σ w) mu ν x (hC ρ lam σ)]
  ring

/-- **Expansion of `∂_λ R^ρ_{σμν}`** via linearity + Leibniz: the two `∂∂Γ` terms plus the
    `∑_l (∂Γ·Γ + Γ·∂Γ)` Leibniz terms. The differentiability side-conditions are discharged by the
    `PdiffAt_*` helpers (Γ smooth). -/
theorem pd_riemann (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (lam ρ σ μ ν : Fin n) (x : Point n) :
    pd (fun y => riemann g gi ρ σ μ ν y) lam x
      = pd (fun y => pd (fun w => christoffel g gi ρ ν σ w) μ y) lam x
        - pd (fun y => pd (fun w => christoffel g gi ρ μ σ w) ν y) lam x
        + ∑ l, (pd (fun w => christoffel g gi ρ μ l w) lam x * christoffel g gi l ν σ x
              + christoffel g gi ρ μ l x * pd (fun w => christoffel g gi l ν σ w) lam x
              - pd (fun w => christoffel g gi ρ ν l w) lam x * christoffel g gi l μ σ x
              - christoffel g gi ρ ν l x * pd (fun w => christoffel g gi l μ σ w) lam x) := by
  have hAB : PdiffAt (fun y => pd (fun w => christoffel g gi ρ ν σ w) μ y
                      - pd (fun w => christoffel g gi ρ μ σ w) ν y) lam x :=
    (PdiffAt_pd _ (hC ρ ν σ) μ lam x).sub (PdiffAt_pd _ (hC ρ μ σ) ν lam x)
  have hsumand : ∀ l : Fin n, PdiffAt (fun y => christoffel g gi ρ μ l y * christoffel g gi l ν σ y
                      - christoffel g gi ρ ν l y * christoffel g gi l μ σ y) lam x := fun l =>
    ((PdiffAt_of_contDiff _ (hC ρ μ l) lam x).mul (PdiffAt_of_contDiff _ (hC l ν σ) lam x)).sub
     ((PdiffAt_of_contDiff _ (hC ρ ν l) lam x).mul (PdiffAt_of_contDiff _ (hC l μ σ) lam x))
  simp only [riemann]
  rw [pd_add _ _ lam x hAB (PdiffAt_sum _ _ lam x (fun l _ => hsumand l)),
      pd_sub _ _ lam x (PdiffAt_pd _ (hC ρ ν σ) μ lam x) (PdiffAt_pd _ (hC ρ μ σ) ν lam x),
      pd_sum _ _ lam x (fun l _ => hsumand l)]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [pd_sub _ _ lam x
        ((PdiffAt_of_contDiff _ (hC ρ μ l) lam x).mul (PdiffAt_of_contDiff _ (hC l ν σ) lam x))
        ((PdiffAt_of_contDiff _ (hC ρ ν l) lam x).mul (PdiffAt_of_contDiff _ (hC l μ σ) lam x)),
      pd_mul _ _ lam x (PdiffAt_of_contDiff _ (hC ρ μ l) lam x) (PdiffAt_of_contDiff _ (hC l ν σ) lam x),
      pd_mul _ _ lam x (PdiffAt_of_contDiff _ (hC ρ ν l) lam x) (PdiffAt_of_contDiff _ (hC l μ σ) lam x)]
  ring

/-- **The "extra" lower-index connection terms cancel under the cyclic sum.** `∇R` (as a (1,3) tensor)
    has four `Γ·R` terms; the curvature-2-form `DF=0` proof needs only the two acting on the `ρ,σ` matrix
    indices. The other two (acting on the antisymmetric form indices `μ,ν`) cancel cyclically, by Christoffel
    symmetry + Riemann antisymmetry — reducing the second Bianchi to the clean matrix-form `DF=0`. -/
theorem bianchi_extra_terms (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (ρ σ lam mu ν : Fin n) (x : Point n) :
    (∑ κ, christoffel g gi κ lam mu x * riemann g gi ρ σ κ ν x)
    + (∑ κ, christoffel g gi κ lam ν x * riemann g gi ρ σ mu κ x)
    + (∑ κ, christoffel g gi κ mu ν x * riemann g gi ρ σ κ lam x)
    + (∑ κ, christoffel g gi κ mu lam x * riemann g gi ρ σ ν κ x)
    + (∑ κ, christoffel g gi κ ν lam x * riemann g gi ρ σ κ mu x)
    + (∑ κ, christoffel g gi κ ν mu x * riemann g gi ρ σ lam κ x) = 0 := by
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro κ _
  rw [christoffel_symm g gi hsymm κ mu lam x, christoffel_symm g gi hsymm κ ν lam x,
      christoffel_symm g gi hsymm κ ν mu x,
      riemann_antisymm g gi ρ σ ν κ x, riemann_antisymm g gi ρ σ κ mu x,
      riemann_antisymm g gi ρ σ lam κ x]
  ring

/-- The quadratic (`ΓΓ`) part of the Riemann tensor: `R^ρ_{σμν}|_quad = ∑_l (Γ^ρ_{μl}Γ^l_{νσ} − Γ^ρ_{νl}Γ^l_{μσ})`.
    As a matrix in the `(ρ,σ)` indices this is the commutator `[Γ_μ, Γ_ν]`. -/
noncomputable def riemannQuad (g gi : Point n → Fin n → Fin n → ℝ)
    (ρ σ μ ν : Fin n) (x : Point n) : ℝ :=
  ∑ l, (christoffel g gi ρ μ l x * christoffel g gi l ν σ x
      - christoffel g gi ρ ν l x * christoffel g gi l μ σ x)

/-- **The ΓΓΓ part of the second Bianchi cyclic sum vanishes — the Jacobi identity.** In the matrix-form
    `DF=0`, the cubic part is `∑_cyclic [Γ_λ, [Γ_μ, Γ_ν]] = 0` (Jacobi). In components every matrix
    triple-product appears once with each sign, matched pairwise by a single `κ ↔ e` swap of the two
    contracted indices (`Finset.sum_comm`) — no Christoffel symmetry needed. -/
theorem bianchi_GGG (g gi : Point n → Fin n → Fin n → ℝ)
    (ρ σ lam mu ν : Fin n) (x : Point n) :
    ((∑ κ, christoffel g gi ρ lam κ x * riemannQuad g gi κ σ mu ν x)
      - (∑ κ, christoffel g gi κ lam σ x * riemannQuad g gi ρ κ mu ν x))
    + ((∑ κ, christoffel g gi ρ mu κ x * riemannQuad g gi κ σ ν lam x)
      - (∑ κ, christoffel g gi κ mu σ x * riemannQuad g gi ρ κ ν lam x))
    + ((∑ κ, christoffel g gi ρ ν κ x * riemannQuad g gi κ σ lam mu x)
      - (∑ κ, christoffel g gi κ ν σ x * riemannQuad g gi ρ κ lam mu x)) = 0 := by
  -- The three left-multiplied terms (Γ^ρ_{·κ} R_quad^κ) collected as one ∑_κ∑_e integrand.
  have hL : (∑ κ, christoffel g gi ρ lam κ x * riemannQuad g gi κ σ mu ν x)
            + (∑ κ, christoffel g gi ρ mu κ x * riemannQuad g gi κ σ ν lam x)
            + (∑ κ, christoffel g gi ρ ν κ x * riemannQuad g gi κ σ lam mu x)
          = ∑ κ, ∑ e,
              (christoffel g gi ρ lam κ x * (christoffel g gi κ mu e x * christoffel g gi e ν σ x
                                            - christoffel g gi κ ν e x * christoffel g gi e mu σ x)
              + christoffel g gi ρ mu κ x * (christoffel g gi κ ν e x * christoffel g gi e lam σ x
                                            - christoffel g gi κ lam e x * christoffel g gi e ν σ x)
              + christoffel g gi ρ ν κ x * (christoffel g gi κ lam e x * christoffel g gi e mu σ x
                                            - christoffel g gi κ mu e x * christoffel g gi e lam σ x)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro κ _
    simp only [riemannQuad, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- The three right-multiplied terms (Γ^κ_{·σ} R_quad^ρ_κ) collected as one ∑_κ∑_e integrand.
  have hR : (∑ κ, christoffel g gi κ lam σ x * riemannQuad g gi ρ κ mu ν x)
            + (∑ κ, christoffel g gi κ mu σ x * riemannQuad g gi ρ κ ν lam x)
            + (∑ κ, christoffel g gi κ ν σ x * riemannQuad g gi ρ κ lam mu x)
          = ∑ κ, ∑ e,
              (christoffel g gi κ lam σ x * (christoffel g gi ρ mu e x * christoffel g gi e ν κ x
                                            - christoffel g gi ρ ν e x * christoffel g gi e mu κ x)
              + christoffel g gi κ mu σ x * (christoffel g gi ρ ν e x * christoffel g gi e lam κ x
                                            - christoffel g gi ρ lam e x * christoffel g gi e ν κ x)
              + christoffel g gi κ ν σ x * (christoffel g gi ρ lam e x * christoffel g gi e mu κ x
                                            - christoffel g gi ρ mu e x * christoffel g gi e lam κ x)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro κ _
    simp only [riemannQuad, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- Goal = Lgroup − Rgroup; swap κ↔e in Rgroup (Finset.sum_comm); integrands then match pointwise.
  have key : ((∑ κ, christoffel g gi ρ lam κ x * riemannQuad g gi κ σ mu ν x)
      - (∑ κ, christoffel g gi κ lam σ x * riemannQuad g gi ρ κ mu ν x))
    + ((∑ κ, christoffel g gi ρ mu κ x * riemannQuad g gi κ σ ν lam x)
      - (∑ κ, christoffel g gi κ mu σ x * riemannQuad g gi ρ κ ν lam x))
    + ((∑ κ, christoffel g gi ρ ν κ x * riemannQuad g gi κ σ lam mu x)
      - (∑ κ, christoffel g gi κ ν σ x * riemannQuad g gi ρ κ lam mu x))
    = ((∑ κ, christoffel g gi ρ lam κ x * riemannQuad g gi κ σ mu ν x)
        + (∑ κ, christoffel g gi ρ mu κ x * riemannQuad g gi κ σ ν lam x)
        + (∑ κ, christoffel g gi ρ ν κ x * riemannQuad g gi κ σ lam mu x))
      - ((∑ κ, christoffel g gi κ lam σ x * riemannQuad g gi ρ κ mu ν x)
        + (∑ κ, christoffel g gi κ mu σ x * riemannQuad g gi ρ κ ν lam x)
        + (∑ κ, christoffel g gi κ ν σ x * riemannQuad g gi ρ κ lam mu x)) := by ring
  rw [key, hL, hR, Finset.sum_comm (f := fun κ e =>
        christoffel g gi κ lam σ x * (christoffel g gi ρ mu e x * christoffel g gi e ν κ x
                                      - christoffel g gi ρ ν e x * christoffel g gi e mu κ x)
        + christoffel g gi κ mu σ x * (christoffel g gi ρ ν e x * christoffel g gi e lam κ x
                                      - christoffel g gi ρ lam e x * christoffel g gi e ν κ x)
        + christoffel g gi κ ν σ x * (christoffel g gi ρ lam e x * christoffel g gi e mu κ x
                                      - christoffel g gi ρ mu e x * christoffel g gi e lam κ x))]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero; intro κ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero; intro e _
  ring

/-- **Expansion of `∂_λ (R_quad)^ρ_{σμν}`** via `pd_sum` + Leibniz: the `∑_l (∂Γ·Γ + Γ·∂Γ)` terms. -/
theorem pd_riemannQuad (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (lam ρ σ μ ν : Fin n) (x : Point n) :
    pd (fun y => riemannQuad g gi ρ σ μ ν y) lam x
      = ∑ l, (pd (fun w => christoffel g gi ρ μ l w) lam x * christoffel g gi l ν σ x
            + christoffel g gi ρ μ l x * pd (fun w => christoffel g gi l ν σ w) lam x
            - pd (fun w => christoffel g gi ρ ν l w) lam x * christoffel g gi l μ σ x
            - christoffel g gi ρ ν l x * pd (fun w => christoffel g gi l μ σ w) lam x) := by
  have hsumand : ∀ l : Fin n, PdiffAt (fun y => christoffel g gi ρ μ l y * christoffel g gi l ν σ y
                      - christoffel g gi ρ ν l y * christoffel g gi l μ σ y) lam x := fun l =>
    ((PdiffAt_of_contDiff _ (hC ρ μ l) lam x).mul (PdiffAt_of_contDiff _ (hC l ν σ) lam x)).sub
     ((PdiffAt_of_contDiff _ (hC ρ ν l) lam x).mul (PdiffAt_of_contDiff _ (hC l μ σ) lam x))
  simp only [riemannQuad]
  rw [pd_sum _ _ lam x (fun l _ => hsumand l)]
  apply Finset.sum_congr rfl
  intro l _
  rw [pd_sub _ _ lam x
        ((PdiffAt_of_contDiff _ (hC ρ μ l) lam x).mul (PdiffAt_of_contDiff _ (hC l ν σ) lam x))
        ((PdiffAt_of_contDiff _ (hC ρ ν l) lam x).mul (PdiffAt_of_contDiff _ (hC l μ σ) lam x)),
      pd_mul _ _ lam x (PdiffAt_of_contDiff _ (hC ρ μ l) lam x) (PdiffAt_of_contDiff _ (hC l ν σ) lam x),
      pd_mul _ _ lam x (PdiffAt_of_contDiff _ (hC ρ ν l) lam x) (PdiffAt_of_contDiff _ (hC l μ σ) lam x)]
  ring

/-- **The ∂Γ·Γ part of the second Bianchi cyclic sum vanishes.** The first-derivative-of-`Γ` terms come
    from two places — the Leibniz derivative of `R_quad` (`pd_riemannQuad`) and the linear part of the
    `Γ·R` terms (`Γ·R_lin`). Under the cyclic sum they cancel as *identical sums up to renaming the
    contracted index* (no Christoffel symmetry, no index swap) — closed by `ring`. -/
theorem bianchi_dGamma (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ρ σ lam mu ν : Fin n) (x : Point n) :
    (pd (fun y => riemannQuad g gi ρ σ mu ν y) lam x
      + (∑ κ, christoffel g gi ρ lam κ x * riemannLin g gi κ σ mu ν x)
      - (∑ κ, christoffel g gi κ lam σ x * riemannLin g gi ρ κ mu ν x))
    + (pd (fun y => riemannQuad g gi ρ σ ν lam y) mu x
      + (∑ κ, christoffel g gi ρ mu κ x * riemannLin g gi κ σ ν lam x)
      - (∑ κ, christoffel g gi κ mu σ x * riemannLin g gi ρ κ ν lam x))
    + (pd (fun y => riemannQuad g gi ρ σ lam mu y) ν x
      + (∑ κ, christoffel g gi ρ ν κ x * riemannLin g gi κ σ lam mu x)
      - (∑ κ, christoffel g gi κ ν σ x * riemannLin g gi ρ κ lam mu x)) = 0 := by
  rw [pd_riemannQuad g gi hC lam ρ σ mu ν, pd_riemannQuad g gi hC mu ρ σ ν lam,
      pd_riemannQuad g gi hC ν ρ σ lam mu]
  simp only [riemannLin, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro x _
  ring

/-- **Covariant derivative of the (1,3) Riemann tensor** `∇_λ R^ρ_{σμν} = ∂_λ R^ρ_{σμν}
    + Γ^ρ_{λκ}R^κ_{σμν} − Γ^κ_{λσ}R^ρ_{κμν} − Γ^κ_{λμ}R^ρ_{σκν} − Γ^κ_{λν}R^ρ_{σμκ}`. -/
noncomputable def covDerivRiem (g gi : Point n → Fin n → Fin n → ℝ)
    (lam ρ σ μ ν : Fin n) (x : Point n) : ℝ :=
  pd (fun y => riemann g gi ρ σ μ ν y) lam x
    + (∑ κ, christoffel g gi ρ lam κ x * riemann g gi κ σ μ ν x)
    - (∑ κ, christoffel g gi κ lam σ x * riemann g gi ρ κ μ ν x)
    - (∑ κ, christoffel g gi κ lam μ x * riemann g gi ρ σ κ ν x)
    - (∑ κ, christoffel g gi κ lam ν x * riemann g gi ρ σ μ κ x)

/-- **The second Bianchi identity** (differential Bianchi): for the Levi-Civita connection of a smooth
    metric, the cyclic sum of covariant derivatives of the Riemann tensor vanishes,
    `∇_λ R^ρ_{σμν} + ∇_μ R^ρ_{σνλ} + ∇_ν R^ρ_{σλμ} = 0`. Proved by decomposing each `∇R` into four
    pieces — `∂∂Γ` (cancels via Schwarz, `second_bianchi_deriv_part`), `∂Γ·Γ` (`bianchi_dGamma`),
    the cubic `ΓΓΓ`/Jacobi part (`bianchi_GGG`), and the lower-index "extra" terms
    (`bianchi_extra_terms`) — each of whose cyclic sum is zero. This is the conservation identity behind
    `∇^μ G_{μν}=0` (Jacobson's contracted-Bianchi step). Established mathematics, here machine-checked
    component-level and axiom-free. -/
theorem second_bianchi (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ρ σ lam mu ν : Fin n) (x : Point n) :
    covDerivRiem g gi lam ρ σ mu ν x
      + covDerivRiem g gi mu ρ σ ν lam x
      + covDerivRiem g gi ν ρ σ lam mu x = 0 := by
  have riemann_split : ∀ a b c d : Fin n,
      riemann g gi a b c d x = riemannLin g gi a b c d x + riemannQuad g gi a b c d x :=
    fun _ _ _ _ => rfl
  have decomp : ∀ a b c : Fin n, covDerivRiem g gi a ρ σ b c x
      = pd (fun y => riemannLin g gi ρ σ b c y) a x
        + (pd (fun y => riemannQuad g gi ρ σ b c y) a x
            + (∑ κ, christoffel g gi ρ a κ x * riemannLin g gi κ σ b c x)
            - (∑ κ, christoffel g gi κ a σ x * riemannLin g gi ρ κ b c x))
        + ((∑ κ, christoffel g gi ρ a κ x * riemannQuad g gi κ σ b c x)
            - (∑ κ, christoffel g gi κ a σ x * riemannQuad g gi ρ κ b c x))
        + (- (∑ κ, christoffel g gi κ a b x * riemann g gi ρ σ κ c x)
            - (∑ κ, christoffel g gi κ a c x * riemann g gi ρ σ b κ x)) := by
    intro a b c
    have hLin : PdiffAt (fun y => riemannLin g gi ρ σ b c y) a x :=
      (PdiffAt_pd _ (hC ρ c σ) b a x).sub (PdiffAt_pd _ (hC ρ b σ) c a x)
    have hQuad : PdiffAt (fun y => riemannQuad g gi ρ σ b c y) a x :=
      PdiffAt_sum _ _ a x (fun l _ =>
        ((PdiffAt_of_contDiff _ (hC ρ b l) a x).mul (PdiffAt_of_contDiff _ (hC l c σ) a x)).sub
        ((PdiffAt_of_contDiff _ (hC ρ c l) a x).mul (PdiffAt_of_contDiff _ (hC l b σ) a x)))
    have hpd : pd (fun y => riemann g gi ρ σ b c y) a x
        = pd (fun y => riemannLin g gi ρ σ b c y) a x
          + pd (fun y => riemannQuad g gi ρ σ b c y) a x :=
      pd_add _ _ a x hLin hQuad
    have hs1 : (∑ κ, christoffel g gi ρ a κ x * riemann g gi κ σ b c x)
        = (∑ κ, christoffel g gi ρ a κ x * riemannLin g gi κ σ b c x)
          + (∑ κ, christoffel g gi ρ a κ x * riemannQuad g gi κ σ b c x) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro κ _
      rw [riemann_split κ σ b c]; ring
    have hs2 : (∑ κ, christoffel g gi κ a σ x * riemann g gi ρ κ b c x)
        = (∑ κ, christoffel g gi κ a σ x * riemannLin g gi ρ κ b c x)
          + (∑ κ, christoffel g gi κ a σ x * riemannQuad g gi ρ κ b c x) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro κ _
      rw [riemann_split ρ κ b c]; ring
    simp only [covDerivRiem]
    rw [hpd, hs1, hs2]; ring
  rw [decomp lam mu ν, decomp mu ν lam, decomp ν lam mu]
  have ha := second_bianchi_deriv_part g gi ρ σ lam mu ν x hC
  have hb := bianchi_dGamma g gi hC ρ σ lam mu ν x
  have hc := bianchi_GGG g gi ρ σ lam mu ν x
  have hd := bianchi_extra_terms g gi hsymm ρ σ lam mu ν x
  linarith [ha, hb, hc, hd]

/-- `R^ρ_{σμν}` is partially differentiable in any direction (Γ smooth). -/
theorem PdiffAt_riemann (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ρ σ μ ν lam : Fin n) (x : Point n) :
    PdiffAt (fun y => riemann g gi ρ σ μ ν y) lam x :=
  ((PdiffAt_pd _ (hC ρ ν σ) μ lam x).sub (PdiffAt_pd _ (hC ρ μ σ) ν lam x)).add
    (PdiffAt_sum _ _ lam x (fun l _ =>
      ((PdiffAt_of_contDiff _ (hC ρ μ l) lam x).mul (PdiffAt_of_contDiff _ (hC l ν σ) lam x)).sub
      ((PdiffAt_of_contDiff _ (hC ρ ν l) lam x).mul (PdiffAt_of_contDiff _ (hC l μ σ) lam x))))

/-- **The covariant derivative commutes with contraction** (the `(ρ,μ)`-trace giving Ricci):
    `∑_ρ ∇_λ R^ρ_{σρν} = ∇_λ R_{σν}`. The connection corrections for the contracted index pair cancel
    (`Finset.sum_comm`), and the remaining two assemble into the `(0,2)` covariant derivative of `Ric`.
    The key step that turns the second Bianchi into the contracted Bianchi `∇^μ G_{μν}=0`. -/
theorem covDerivRiem_contract (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (lam σ ν : Fin n) (x : Point n) :
    (∑ ρ, covDerivRiem g gi lam ρ σ ρ ν x)
      = covDeriv02 g gi (fun y a b => ricci g gi a b y) lam σ ν x := by
  have h_a : (∑ ρ, pd (fun y => riemann g gi ρ σ ρ ν y) lam x)
      = pd (fun y => ricci g gi σ ν y) lam x := by
    rw [← pd_sum Finset.univ (fun ρ y => riemann g gi ρ σ ρ ν y) lam x
          (fun ρ _ => PdiffAt_riemann g gi hC ρ σ ρ ν lam x)]
    rfl
  have h_bd : (∑ ρ, ∑ κ, christoffel g gi ρ lam κ x * riemann g gi κ σ ρ ν x)
      = (∑ ρ, ∑ κ, christoffel g gi κ lam ρ x * riemann g gi ρ σ κ ν x) := Finset.sum_comm
  have h_c : (∑ ρ, ∑ κ, christoffel g gi κ lam σ x * riemann g gi ρ κ ρ ν x)
      = (∑ κ, christoffel g gi κ lam σ x * ricci g gi κ ν x) := by
    rw [Finset.sum_comm]; simp only [ricci, Finset.mul_sum]
  have h_e : (∑ ρ, ∑ κ, christoffel g gi κ lam ν x * riemann g gi ρ σ ρ κ x)
      = (∑ κ, christoffel g gi κ lam ν x * ricci g gi σ κ x) := by
    rw [Finset.sum_comm]; simp only [ricci, Finset.mul_sum]
  simp only [covDerivRiem, covDeriv02, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith [h_a, h_bd, h_c, h_e]

/-- **`∇R` inherits Riemann's antisymmetry in the last two indices**:
    `∇_λ R^ρ_{σμν} + ∇_λ R^ρ_{σνμ} = 0`. Each of the five constituent terms pairs off via
    `riemann_antisymm` (the `∂∂` term via `pd_const_mul`). -/
theorem covDerivRiem_antisymm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (lam ρ σ μ ν : Fin n) (x : Point n) :
    covDerivRiem g gi lam ρ σ μ ν x + covDerivRiem g gi lam ρ σ ν μ x = 0 := by
  have hpd : pd (fun y => riemann g gi ρ σ μ ν y) lam x
      + pd (fun y => riemann g gi ρ σ ν μ y) lam x = 0 := by
    have hfun : (fun y => riemann g gi ρ σ μ ν y) = (fun y => (-1 : ℝ) * riemann g gi ρ σ ν μ y) := by
      funext y; rw [riemann_antisymm g gi ρ σ μ ν y]; ring
    rw [hfun, pd_const_mul (-1) _ lam x (PdiffAt_riemann g gi hC ρ σ ν μ lam x)]; ring
  have h2 : (∑ κ, christoffel g gi ρ lam κ x * riemann g gi κ σ μ ν x)
      + (∑ κ, christoffel g gi ρ lam κ x * riemann g gi κ σ ν μ x) = 0 := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro κ _
    rw [riemann_antisymm g gi κ σ μ ν x]; ring
  have h3 : (∑ κ, christoffel g gi κ lam σ x * riemann g gi ρ κ μ ν x)
      + (∑ κ, christoffel g gi κ lam σ x * riemann g gi ρ κ ν μ x) = 0 := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro κ _
    rw [riemann_antisymm g gi ρ κ μ ν x]; ring
  have h45 : (∑ κ, christoffel g gi κ lam μ x * riemann g gi ρ σ κ ν x)
      + (∑ κ, christoffel g gi κ lam μ x * riemann g gi ρ σ ν κ x) = 0 := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro κ _
    rw [riemann_antisymm g gi ρ σ κ ν x]; ring
  have h54 : (∑ κ, christoffel g gi κ lam ν x * riemann g gi ρ σ μ κ x)
      + (∑ κ, christoffel g gi κ lam ν x * riemann g gi ρ σ κ μ x) = 0 := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro κ _
    rw [riemann_antisymm g gi ρ σ μ κ x]; ring
  simp only [covDerivRiem]
  linarith [hpd, h2, h3, h45, h54]

/-- The Ricci trace via the *other* contraction (antisymmetry): `∑_ρ R^ρ_{σμρ} = −R_{σμ}`. Helper not
    needed standalone — folded into the `(ρ,ν)`-slot contraction below. -/
theorem covDerivRiem_contract' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (dir σ μ : Fin n) (x : Point n) :
    (∑ ρ, covDerivRiem g gi dir ρ σ μ ρ x)
      = - covDeriv02 g gi (fun y a b => ricci g gi a b y) dir σ μ x := by
  have key : (∑ ρ, covDerivRiem g gi dir ρ σ μ ρ x) + (∑ ρ, covDerivRiem g gi dir ρ σ ρ μ x) = 0 := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro ρ _
    exact covDerivRiem_antisymm g gi hC dir ρ σ μ ρ x
  have hcontract := covDerivRiem_contract g gi hC dir σ μ x
  linarith [key, hcontract]

/-- **The once-contracted (second) Bianchi identity** `∇_λ R_{σν} − ∇_ν R_{σλ} + ∇_ρ R^ρ_{σνλ} = 0`,
    obtained by tracing the second Bianchi over `(ρ,μ)` (`covDerivRiem_contract`/`'`). The remaining
    divergence term `∑_ρ ∇_ρ R^ρ_{σνλ}` is the Riemann divergence; contracting once more with `g^{μν}`
    yields `∇^μ G_{μν}=0`. Established mathematics, machine-checked component-level and axiom-free. -/
theorem second_bianchi_contracted (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (lam σ ν : Fin n) (x : Point n) :
    covDeriv02 g gi (fun y a b => ricci g gi a b y) lam σ ν x
      - covDeriv02 g gi (fun y a b => ricci g gi a b y) ν σ lam x
      + (∑ ρ, covDerivRiem g gi ρ ρ σ ν lam x) = 0 := by
  have hsum : (∑ ρ, (covDerivRiem g gi lam ρ σ ρ ν x + covDerivRiem g gi ρ ρ σ ν lam x
                    + covDerivRiem g gi ν ρ σ lam ρ x)) = 0 :=
    Finset.sum_eq_zero (fun ρ _ => second_bianchi g gi hsymm hC ρ σ lam ρ ν x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      covDerivRiem_contract g gi hC lam σ ν, covDerivRiem_contract' g gi hC ν σ lam] at hsum
  linarith [hsum]

/-- **Inverse-metric covariant constancy `∇_λ g^{μρ} = 0`** — the raised-index companion of
    `metric_compat`. Derived by differentiating the inverse relation `∑_σ g_{aσ}g^{σb}=δ` (so
    `∑_σ g_{aσ}∂_λ g^{σρ} = −∑_σ (∂_λ g_{aσ})g^{σρ}`), substituting `∂g` from `metric_compat`, and
    cancelling the connection terms; the contraction with `g` is then removed by invertibility.
    The tool that lets the metric pass through `∇` in the `g^{μν}`-contractions of `∇^μ G_{μν}=0`. -/
theorem inv_metric_compat (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (lam : Fin n) (x : Point n)
    (hgd : ∀ a b, PdiffAt (fun y => g y a b) lam x)
    (hgid : ∀ a b, PdiffAt (fun y => gi y a b) lam x)
    (μ ρ : Fin n) :
    covDeriv20 g gi gi lam μ ρ x = 0 := by
  have hinv_pt : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0 := fun a b => hinv x a b
  -- Two metric/inverse contraction identities used repeatedly below.
  have contract : ∀ (ν : Fin n) (c : Fin n → ℝ),
      (∑ μ', g x ν μ' * (∑ κ, c κ * gi x μ' κ)) = c ν := by
    intro ν c
    have hswap : (∑ μ', g x ν μ' * (∑ κ, c κ * gi x μ' κ))
        = ∑ κ, c κ * (∑ μ', g x ν μ' * gi x μ' κ) := by
      simp only [Finset.mul_sum]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro κ _; apply Finset.sum_congr rfl; intro μ' _; ring
    rw [hswap, Finset.sum_congr rfl (fun κ (_ : κ ∈ Finset.univ) => by rw [hinv_pt ν κ])]
    simp [Finset.sum_ite_eq, mul_ite]
  have contract2 : ∀ (A : Fin n → ℝ) (b : Fin n),
      (∑ σ, (∑ κ, A κ * g x κ σ) * gi x σ b) = A b := by
    intro A b
    have hswap : (∑ σ, (∑ κ, A κ * g x κ σ) * gi x σ b)
        = ∑ κ, A κ * (∑ σ, g x κ σ * gi x σ b) := by
      simp only [Finset.sum_mul]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro κ _; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro σ _; ring
    rw [hswap, Finset.sum_congr rfl (fun κ (_ : κ ∈ Finset.univ) => by rw [hinv_pt κ b])]
    simp [Finset.sum_ite_eq, mul_ite]
  -- ∂g from metric compatibility.
  have hmc : ∀ a b : Fin n, pd (fun y => g y a b) lam x
      = (∑ σ, christoffel g gi σ lam a x * g x σ b) + (∑ σ, christoffel g gi σ lam b x * g x a σ) := by
    intro a b
    have hm := metric_compat g gi hsymm x hinv_pt lam a b
    simp only [covDeriv02] at hm; linarith [hm]
  -- Differentiated inverse relation: ∑_σ g_{aσ} ∂_λ g^{σρ} = −∑_σ (∂_λ g_{aσ}) g^{σρ}.
  have hD : ∀ a : Fin n, (∑ σ, g x a σ * pd (fun y => gi y σ ρ) lam x)
      = - ∑ σ, pd (fun y => g y a σ) lam x * gi x σ ρ := by
    intro a
    have hconst : pd (fun y => ∑ σ, g y a σ * gi y σ ρ) lam x = 0 := by
      rw [show (fun y => ∑ σ, g y a σ * gi y σ ρ) = (fun _ => (if a = ρ then (1:ℝ) else 0))
            from funext (fun y => hinv y a ρ)]
      exact pd_const _ _ _
    rw [pd_sum Finset.univ (fun σ y => g y a σ * gi y σ ρ) lam x
          (fun σ _ => (hgd a σ).mul (hgid σ ρ))] at hconst
    rw [Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) =>
          pd_mul (fun y => g y a σ) (fun y => gi y σ ρ) lam x (hgd a σ) (hgid σ ρ)),
        Finset.sum_add_distrib] at hconst
    linarith [hconst]
  -- Contract the claim with g_{νμ}; show it vanishes for every ν.
  have hkey : ∀ ν : Fin n, (∑ μ', g x ν μ' * covDeriv20 g gi gi lam μ' ρ x) = 0 := by
    intro ν
    have hP3 : (∑ μ', g x ν μ' * (∑ κ, christoffel g gi ρ lam κ x * gi x μ' κ))
        = christoffel g gi ρ lam ν x := contract ν (fun κ => christoffel g gi ρ lam κ x)
    have hP1 : (∑ μ', g x ν μ' * pd (fun y => gi y μ' ρ) lam x)
        = - christoffel g gi ρ lam ν x
          - ∑ σ, (∑ κ, g x ν κ * christoffel g gi κ lam σ x) * gi x σ ρ := by
      rw [hD ν, Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) => by
            rw [hmc ν σ, add_mul]), Finset.sum_add_distrib]
      have e1 : (∑ σ, (∑ κ, christoffel g gi κ lam ν x * g x κ σ) * gi x σ ρ)
          = christoffel g gi ρ lam ν x := contract2 (fun κ => christoffel g gi κ lam ν x) ρ
      have e2 : (∑ σ, (∑ κ, christoffel g gi κ lam σ x * g x ν κ) * gi x σ ρ)
          = ∑ σ, (∑ κ, g x ν κ * christoffel g gi κ lam σ x) * gi x σ ρ := by
        apply Finset.sum_congr rfl; intro σ _; congr 1
        apply Finset.sum_congr rfl; intro κ _; ring
      rw [e1, e2]; ring
    have hP2 : (∑ μ', g x ν μ' * (∑ κ, christoffel g gi μ' lam κ x * gi x κ ρ))
        = ∑ σ, (∑ κ, g x ν κ * christoffel g gi κ lam σ x) * gi x σ ρ := by
      have hswap : (∑ μ', g x ν μ' * (∑ κ, christoffel g gi μ' lam κ x * gi x κ ρ))
          = ∑ κ, (∑ μ', g x ν μ' * christoffel g gi μ' lam κ x) * gi x κ ρ := by
        simp only [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro κ _; apply Finset.sum_congr rfl; intro μ' _; ring
      rw [hswap]
    simp only [covDeriv20, mul_add, Finset.sum_add_distrib]
    rw [hP1, hP2, hP3]; ring
  -- Invertibility (left inverse) removes the contraction.
  have hleft : ∀ b m : Fin n, (∑ ν, gi x b ν * g x ν m) = if b = m then (1:ℝ) else 0 := by
    intro b m
    rw [show (∑ ν, gi x b ν * g x ν m) = ∑ ν, g x m ν * gi x ν b from by
          apply Finset.sum_congr rfl; intro ν _; rw [hsymm_gi x b ν, hsymm x ν m]; ring]
    rw [hinv_pt m b]
    by_cases h : b = m
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun he => h he.symm)]
  have hinvert : covDeriv20 g gi gi lam μ ρ x
      = ∑ ν, gi x μ ν * (∑ m, g x ν m * covDeriv20 g gi gi lam m ρ x) := by
    rw [show (∑ ν, gi x μ ν * (∑ m, g x ν m * covDeriv20 g gi gi lam m ρ x))
          = ∑ m, (∑ ν, gi x μ ν * g x ν m) * covDeriv20 g gi gi lam m ρ x from by
        simp only [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro ν _; ring]
    rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => by rw [hleft μ m])]
    simp [Finset.sum_ite_eq, ite_mul]
  rw [hinvert, Finset.sum_congr rfl (fun ν (_ : ν ∈ Finset.univ) => by rw [hkey ν, mul_zero])]
  simp

/-- **Riemann in terms of the metric** (lowered first index): `g_{ρα} R^α_{σμν}` equals
    `∂_μ Γ_{ρνσ} − ∂_ν Γ_{ρμσ} − Γ^κ_{μρ}Γ_{κνσ} + Γ^κ_{νρ}Γ_{κμσ}`, where `Γ_{ρνσ}=∑_α g_{ρα}Γ^α_{νσ}`
    is the lowered Christoffel (written here as the contraction `g_{ακ}` for the connection terms). The
    `g·ΓΓ` terms produced by differentiating `g` (`metric_compat`) cancel the Riemann `ΓΓ` terms. -/
theorem lowered_riemann_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ρ σ μ ν : Fin n) (x : Point n) :
    (∑ α, g x ρ α * riemann g gi α σ μ ν x)
      = pd (fun y => ∑ α, g y ρ α * christoffel g gi α ν σ y) μ x
        - pd (fun y => ∑ α, g y ρ α * christoffel g gi α μ σ y) ν x
        - (∑ κ, christoffel g gi κ μ ρ x * (∑ α, g x α κ * christoffel g gi α ν σ x))
        + (∑ κ, christoffel g gi κ ν ρ x * (∑ α, g x α κ * christoffel g gi α μ σ x)) := by
  -- Product rule: ∑_α g_{ρα} ∂_e Γ^α_{cd} = ∂_e(∑_α g_{ρα}Γ^α_{cd}) − ∑_α (∂_e g_{ρα})Γ^α_{cd}.
  have prod : ∀ (c d e : Fin n), (∑ α, g x ρ α * pd (fun y => christoffel g gi α c d y) e x)
      = pd (fun y => ∑ α, g y ρ α * christoffel g gi α c d y) e x
        - ∑ α, pd (fun y => g y ρ α) e x * christoffel g gi α c d x := by
    intro c d e
    have hexp : pd (fun y => ∑ α, g y ρ α * christoffel g gi α c d y) e x
        = (∑ α, pd (fun y => g y ρ α) e x * christoffel g gi α c d x)
          + (∑ α, g x ρ α * pd (fun y => christoffel g gi α c d y) e x) := by
      rw [pd_sum Finset.univ (fun α y => g y ρ α * christoffel g gi α c d y) e x
            (fun α _ => (PdiffAt_of_contDiff _ (hCg ρ α) e x).mul (PdiffAt_of_contDiff _ (hC α c d) e x)),
          Finset.sum_congr rfl (fun α (_ : α ∈ Finset.univ) =>
            pd_mul (fun y => g y ρ α) (fun y => christoffel g gi α c d y) e x
              (PdiffAt_of_contDiff _ (hCg ρ α) e x) (PdiffAt_of_contDiff _ (hC α c d) e x)),
          Finset.sum_add_distrib]
    linarith [hexp]
  -- ∂g from metric compatibility, in the form `∂_c g_{ρa} = ∑_κ g_{aκ}Γ^κ_{cρ} + ∑_κ g_{ρκ}Γ^κ_{ca}`.
  have hmc : ∀ (a c : Fin n), pd (fun y => g y ρ a) c x
      = (∑ κ, g x a κ * christoffel g gi κ c ρ x) + (∑ κ, g x ρ κ * christoffel g gi κ c a x) := by
    intro a c
    have hm := metric_compat g gi hsymm x (fun p q => hinv x p q) c ρ a
    simp only [covDeriv02] at hm
    have h1 : (∑ τ, christoffel g gi τ c ρ x * g x τ a) = ∑ κ, g x a κ * christoffel g gi κ c ρ x := by
      apply Finset.sum_congr rfl; intro τ _; rw [hsymm x τ a]; ring
    have h2 : (∑ τ, christoffel g gi τ c a x * g x ρ τ) = ∑ κ, g x ρ κ * christoffel g gi κ c a x := by
      apply Finset.sum_congr rfl; intro τ _; ring
    linarith [hm, h1, h2]
  -- Expand `g_{ρα}` over the Riemann tensor.
  have hexpand : (∑ α, g x ρ α * riemann g gi α σ μ ν x)
      = (∑ α, g x ρ α * pd (fun y => christoffel g gi α ν σ y) μ x)
        - (∑ α, g x ρ α * pd (fun y => christoffel g gi α μ σ y) ν x)
        + (∑ α, g x ρ α * (∑ l, (christoffel g gi α μ l x * christoffel g gi l ν σ x
                                  - christoffel g gi α ν l x * christoffel g gi l μ σ x))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro α _; simp only [riemann]; ring
  -- Reindexing identities (each = `Finset.sum_comm` + a per-term `ring`).
  have hThirdμ : (∑ α, (∑ κ, g x α κ * christoffel g gi κ μ ρ x) * christoffel g gi α ν σ x)
      = ∑ κ, christoffel g gi κ μ ρ x * (∑ α, g x α κ * christoffel g gi α ν σ x) := by
    simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro κ _; apply Finset.sum_congr rfl; intro α _; ring
  have hThirdν : (∑ α, (∑ κ, g x α κ * christoffel g gi κ ν ρ x) * christoffel g gi α μ σ x)
      = ∑ κ, christoffel g gi κ ν ρ x * (∑ α, g x α κ * christoffel g gi α μ σ x) := by
    simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro κ _; apply Finset.sum_congr rfl; intro α _; ring
  have hSum3a : (∑ α, (∑ κ, g x ρ κ * christoffel g gi κ μ α x) * christoffel g gi α ν σ x)
      = ∑ α, g x ρ α * (∑ l, christoffel g gi α μ l x * christoffel g gi l ν σ x) := by
    simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro α _; apply Finset.sum_congr rfl; intro κ _; ring
  have hSum3b : (∑ α, (∑ κ, g x ρ κ * christoffel g gi κ ν α x) * christoffel g gi α μ σ x)
      = ∑ α, g x ρ α * (∑ l, christoffel g gi α ν l x * christoffel g gi l μ σ x) := by
    simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro α _; apply Finset.sum_congr rfl; intro κ _; ring
  rw [hexpand, prod ν σ μ, prod μ σ ν]
  simp only [hmc, add_mul, Finset.sum_add_distrib]
  rw [hThirdμ, hThirdν, hSum3a, hSum3b]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **First-pair antisymmetry of the lowered Riemann tensor**: `g_{ρα}R^α_{σμν} + g_{σα}R^α_{ρμν} = 0`,
    i.e. `R_{ρσμν}=−R_{σρμν}`. From `lowered_riemann_eq`: the `∂Γ_lower` pairs combine (via `metric_compat`
    as a *function* identity) into `∂∂g_{ρσ}` and cancel by **Schwarz** (`pd_comm`); the `ΓΓ` pairs cancel
    by the symmetry of `⟨ab,cd⟩=∑_{κα}g_{ακ}Γ^κ_{ab}Γ^α_{cd}` under `(ab)↔(cd)`. The crux of the
    metric-raising tower (piece B) — required for `g^{σν}R^ρ_{σνλ}` in `∇^μ G_{μν}=0`. -/
theorem lowered_riemann_antisymm (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ρ σ μ ν : Fin n) (x : Point n) :
    (∑ α, g x ρ α * riemann g gi α σ μ ν x) + (∑ α, g x σ α * riemann g gi α ρ μ ν x) = 0 := by
  -- `∑_α g_{aα}Γ^α_{cb} + ∑_α g_{bα}Γ^α_{ca} = ∂_c g_{ab}` as functions (metric_compat at every point).
  have hGLsum : ∀ (a b c : Fin n),
      (fun y => (∑ α, g y a α * christoffel g gi α c b y) + (∑ α, g y b α * christoffel g gi α c a y))
      = (fun y => pd (fun z => g z a b) c y) := by
    intro a b c; funext y
    have hm := metric_compat g gi hsymm y (fun p q => hinv y p q) c a b
    simp only [covDeriv02] at hm
    have h1 : (∑ α, g y b α * christoffel g gi α c a y) = ∑ κ, christoffel g gi κ c a y * g y κ b := by
      apply Finset.sum_congr rfl; intro α _; rw [hsymm y b α]; ring
    have h2 : (∑ α, g y a α * christoffel g gi α c b y) = ∑ κ, christoffel g gi κ c b y * g y a κ := by
      apply Finset.sum_congr rfl; intro α _; ring
    rw [h1, h2]; linarith [hm]
  have hPdiffGL : ∀ (a c d e : Fin n),
      PdiffAt (fun y => ∑ α, g y a α * christoffel g gi α c d y) e x := fun a c d e =>
    PdiffAt_sum _ _ e x (fun α _ =>
      (PdiffAt_of_contDiff _ (hCg a α) e x).mul (PdiffAt_of_contDiff _ (hC α c d) e x))
  -- Symmetry of the `ΓΓ` pairing under `(ab)↔(cd)`.
  have hP : ∀ (a b c d : Fin n),
      (∑ κ, christoffel g gi κ a b x * (∑ α, g x α κ * christoffel g gi α c d x))
      = (∑ κ, christoffel g gi κ c d x * (∑ α, g x α κ * christoffel g gi α a b x)) := by
    intro a b c d
    simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [hsymm x i j]; ring
  rw [lowered_riemann_eq g gi hsymm hinv hCg hC ρ σ μ ν,
      lowered_riemann_eq g gi hsymm hinv hCg hC σ ρ μ ν]
  have hpd1 : pd (fun y => ∑ α, g y ρ α * christoffel g gi α ν σ y) μ x
            + pd (fun y => ∑ α, g y σ α * christoffel g gi α ν ρ y) μ x
          = pd (fun y => pd (fun z => g z ρ σ) ν y) μ x := by
    rw [← pd_add _ _ μ x (hPdiffGL ρ ν σ μ) (hPdiffGL σ ν ρ μ), hGLsum ρ σ ν]
  have hpd2 : pd (fun y => ∑ α, g y ρ α * christoffel g gi α μ σ y) ν x
            + pd (fun y => ∑ α, g y σ α * christoffel g gi α μ ρ y) ν x
          = pd (fun y => pd (fun z => g z ρ σ) μ y) ν x := by
    rw [← pd_add _ _ ν x (hPdiffGL ρ μ σ ν) (hPdiffGL σ μ ρ ν), hGLsum ρ σ μ]
  have hschwarz : pd (fun y => pd (fun z => g z ρ σ) ν y) μ x
      = pd (fun y => pd (fun z => g z ρ σ) μ y) ν x :=
    pd_comm (fun z => g z ρ σ) μ ν x (hCg ρ σ)
  linarith [hpd1, hpd2, hschwarz, hP μ ρ ν σ, hP ν ρ μ σ]

/-- **Metric trace of the lowered Riemann tensor → Ricci**: `∑_{σν} g^{σν}(g_{βρ}R^ρ_{σνλ}) = −R_{βλ}`.
    The contraction over the *first two* lower slots, via first-pair antisymmetry
    (`lowered_riemann_antisymm`) turns into the contraction over the (1,3)-Ricci slots, and the `g^{σν}g_{σρ}=δ`
    collapse reproduces `ricci β λ = ∑_ν R^ν_{βνλ}`. The core of metric-raising tower piece C (the contraction
    identity behind `g^{σν}R^ρ_{σνλ}` in `∇^μ G_{μν}=0`). -/
theorem lowered_riemann_gi_trace (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (β lam : Fin n) (x : Point n) :
    (∑ σ, ∑ ν, gi x σ ν * (∑ ρ, g x β ρ * riemann g gi ρ σ ν lam x)) = - ricci g gi β lam x := by
  have hinv_pt : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0 := fun a b => hinv x a b
  have hcollapse : ∀ ρ ν : Fin n, (∑ σ, gi x σ ν * g x σ ρ) = if ρ = ν then (1:ℝ) else 0 := by
    intro ρ ν
    rw [show (∑ σ, gi x σ ν * g x σ ρ) = ∑ σ, g x ρ σ * gi x σ ν from by
          apply Finset.sum_congr rfl; intro σ _; rw [hsymm x σ ρ, hsymm_gi x σ ν]; ring]
    exact hinv_pt ρ ν
  -- For each ν, the σ-trace collapses to a single Riemann component.
  have hpv : ∀ ν : Fin n,
      (∑ σ, gi x σ ν * (∑ ρ, g x σ ρ * riemann g gi ρ β ν lam x)) = riemann g gi ν β ν lam x := by
    intro ν
    rw [show (∑ σ, gi x σ ν * (∑ ρ, g x σ ρ * riemann g gi ρ β ν lam x))
          = ∑ ρ, (∑ σ, gi x σ ν * g x σ ρ) * riemann g gi ρ β ν lam x from by
        simp only [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro ρ _; apply Finset.sum_congr rfl; intro σ _; ring]
    rw [Finset.sum_congr rfl (fun ρ (_ : ρ ∈ Finset.univ) => by rw [hcollapse ρ ν])]
    simp [Finset.sum_ite_eq]
  -- The `g_σρ`-contracted trace gives `+ricci`.
  have hPos : (∑ σ, ∑ ν, gi x σ ν * (∑ ρ, g x σ ρ * riemann g gi ρ β ν lam x))
      = ricci g gi β lam x := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun ν (_ : ν ∈ Finset.univ) => hpv ν), ricci]
  -- The target trace + the `g_σρ` trace vanish (first-pair antisymmetry termwise).
  have hzero : (∑ σ, ∑ ν, gi x σ ν * (∑ ρ, g x β ρ * riemann g gi ρ σ ν lam x))
             + (∑ σ, ∑ ν, gi x σ ν * (∑ ρ, g x σ ρ * riemann g gi ρ β ν lam x)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro σ _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro ν _
    rw [← mul_add, lowered_riemann_antisymm g gi hsymm hinv hCg hC β σ ν lam x, mul_zero]
  linarith [hPos, hzero]

/-- **Raised metric trace of Riemann → raised Ricci** (metric-raising tower, piece C raised):
    `∑_{σν} g^{σν} R^ρ_{σνλ} = −∑_β g^{ρβ} Ric_{βλ}`. Raises `lowered_riemann_gi_trace` through the
    `g⁻¹·g = δ` inversion. -/
theorem ricci_gi_raise (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ρ lam : Fin n) (x : Point n) :
    (∑ σ, ∑ ν, gi x σ ν * riemann g gi ρ σ ν lam x) = - ∑ β, gi x ρ β * ricci g gi β lam x := by
  have hinv_pt : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0 := fun a b => hinv x a b
  -- lowered trace `∑_{ρ'} g_{βρ'} (∑_{σν} g^{σν} R^{ρ'}_{σνλ}) = −Ric_{βλ}`.
  have hlow : ∀ β : Fin n,
      (∑ ρ', g x β ρ' * (∑ σ, ∑ ν, gi x σ ν * riemann g gi ρ' σ ν lam x)) = - ricci g gi β lam x := by
    intro β
    have hswap : (∑ ρ', g x β ρ' * (∑ σ, ∑ ν, gi x σ ν * riemann g gi ρ' σ ν lam x))
        = ∑ σ, ∑ ν, gi x σ ν * (∑ ρ', g x β ρ' * riemann g gi ρ' σ ν lam x) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro σ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro ν _
      apply Finset.sum_congr rfl; intro ρ' _; ring
    rw [hswap]; exact lowered_riemann_gi_trace g gi hsymm hsymm_gi hinv hCg hC β lam x
  -- left inverse `g⁻¹·g = δ`.
  have hleft : ∀ a b : Fin n, (∑ β, gi x a β * g x β b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [show (∑ β, gi x a β * g x β b) = ∑ β, g x b β * gi x β a from by
          apply Finset.sum_congr rfl; intro β _; rw [hsymm_gi x a β, hsymm x β b]; ring]
    rw [hinv_pt b a]
    by_cases h : a = b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun he => h he.symm)]
  -- invert: `Q^ρ = ∑_β g^{ρβ} (∑_{ρ'} g_{βρ'} Q^{ρ'})` for any vector `Q` (left-inverse `g⁻¹·g=δ`).
  have hinvert : ∀ Q : Fin n → ℝ, Q ρ = ∑ β, gi x ρ β * (∑ ρ', g x β ρ' * Q ρ') := by
    intro Q
    rw [show (∑ β, gi x ρ β * (∑ ρ', g x β ρ' * Q ρ'))
          = ∑ ρ', (∑ β, gi x ρ β * g x β ρ') * Q ρ' from by
        simp only [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro ρ' _; apply Finset.sum_congr rfl; intro β _; ring]
    rw [Finset.sum_congr rfl (fun ρ' (_ : ρ' ∈ Finset.univ) => by rw [hleft ρ ρ'])]
    simp [Finset.sum_ite_eq, ite_mul]
  rw [show (∑ σ, ∑ ν, gi x σ ν * riemann g gi ρ σ ν lam x)
        = ∑ β, gi x ρ β * (∑ ρ', g x β ρ' * (∑ σ, ∑ ν, gi x σ ν * riemann g gi ρ' σ ν lam x))
      from hinvert (fun ρ' => ∑ σ, ∑ ν, gi x σ ν * riemann g gi ρ' σ ν lam x)]
  rw [Finset.sum_congr rfl (fun β (_ : β ∈ Finset.univ) => by rw [hlow β])]
  simp [mul_neg]

/-- `Ric_{σν}` is partially differentiable in any direction (Γ smooth). -/
theorem PdiffAt_ricci (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (σ ν lam : Fin n) (x : Point n) : PdiffAt (fun y => ricci g gi σ ν y) lam x :=
  PdiffAt_sum _ _ lam x (fun μ _ => PdiffAt_riemann g gi hC μ σ μ ν lam x)

/-- **T1 of the twice-contracted Bianchi — the scalar-curvature derivative**:
    `∑_{σν} g^{σν} ∇_λ Ric_{σν} = ∂_λ R`. Product rule on `R = ∑g^{σν}Ric_{σν}` (`pd_sum`+`pd_mul`)
    plus `inv_metric_compat` (`∂g^{σν} = −Γg−Γg`) cancels the connection terms by index swaps. -/
theorem gi_trace_covDeriv_ricci (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (lam : Fin n) (x : Point n) :
    (∑ σ, ∑ ν, gi x σ ν * covDeriv02 g gi (fun y a b => ricci g gi a b y) lam σ ν x)
      = pd (fun y => scalarCurv g gi y) lam x := by
  have hgd : ∀ a b, PdiffAt (fun y => g y a b) lam x := fun a b =>
    PdiffAt_of_contDiff _ (hCg a b) lam x
  have hgid : ∀ a b, PdiffAt (fun y => gi y a b) lam x := fun a b =>
    PdiffAt_of_contDiff _ (hCgi a b) lam x
  have hRic : ∀ σ ν, PdiffAt (fun y => ricci g gi σ ν y) lam x := fun σ ν =>
    PdiffAt_ricci g gi hC σ ν lam x
  -- triple-sum index swaps
  have swap13 : ∀ (F : Fin n → Fin n → Fin n → ℝ),
      (∑ σ, ∑ ν, ∑ κ, F σ ν κ) = ∑ σ, ∑ ν, ∑ κ, F κ ν σ := by
    intro F
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun ν _ => Finset.sum_comm), Finset.sum_comm]
  have swap23 : ∀ (F : Fin n → Fin n → Fin n → ℝ),
      (∑ σ, ∑ ν, ∑ κ, F σ ν κ) = ∑ σ, ∑ ν, ∑ κ, F σ κ ν := by
    intro F
    apply Finset.sum_congr rfl; intro σ _; rw [Finset.sum_comm]
  -- product rule on the scalar curvature
  have hpd_scalar : pd (fun y => scalarCurv g gi y) lam x
      = (∑ σ, ∑ ν, pd (fun y => gi y σ ν) lam x * ricci g gi σ ν x)
        + (∑ σ, ∑ ν, gi x σ ν * pd (fun y => ricci g gi σ ν y) lam x) := by
    rw [show (fun y => scalarCurv g gi y) = (fun y => ∑ σ, ∑ ν, gi y σ ν * ricci g gi σ ν y) from rfl,
        pd_sum Finset.univ (fun σ y => ∑ ν, gi y σ ν * ricci g gi σ ν y) lam x
          (fun σ _ => PdiffAt_sum _ _ lam x (fun ν _ => (hgid σ ν).mul (hRic σ ν))),
        ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro σ _
    rw [pd_sum Finset.univ (fun ν y => gi y σ ν * ricci g gi σ ν y) lam x
          (fun ν _ => (hgid σ ν).mul (hRic σ ν)), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro ν _
    exact pd_mul (fun y => gi y σ ν) (fun y => ricci g gi σ ν y) lam x (hgid σ ν) (hRic σ ν)
  -- ∂g^{σν} from inverse-metric compatibility
  have hpd_gi : ∀ σ ν, pd (fun y => gi y σ ν) lam x
      = -(∑ κ, christoffel g gi σ lam κ x * gi x κ ν)
        - (∑ κ, christoffel g gi ν lam κ x * gi x σ κ) := by
    intro σ ν
    have hm := inv_metric_compat g gi hsymm hsymm_gi hinv lam x hgd hgid σ ν
    simp only [covDeriv20] at hm; linarith [hm]
  -- substitute `∂g` and collect the two connection sums `−C − D`
  have hS_gipd : (∑ σ, ∑ ν, pd (fun y => gi y σ ν) lam x * ricci g gi σ ν x)
      = -(∑ σ, ∑ ν, ∑ κ, christoffel g gi σ lam κ x * gi x κ ν * ricci g gi σ ν x)
        - (∑ σ, ∑ ν, ∑ κ, christoffel g gi ν lam κ x * gi x σ κ * ricci g gi σ ν x) := by
    rw [Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun ν _ => by rw [hpd_gi σ ν]))]
    simp only [sub_mul, neg_mul, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  -- the two `Γ·g·Ric` cancellations (A=C via swap13, B=D via swap23)
  have hAC : (∑ σ, ∑ ν, ∑ κ, gi x σ ν * (christoffel g gi κ lam σ x * ricci g gi κ ν x))
      = ∑ σ, ∑ ν, ∑ κ, christoffel g gi σ lam κ x * gi x κ ν * ricci g gi σ ν x := by
    rw [swap13 (fun σ ν κ => gi x σ ν * (christoffel g gi κ lam σ x * ricci g gi κ ν x))]
    apply Finset.sum_congr rfl; intro σ _; apply Finset.sum_congr rfl; intro ν _
    apply Finset.sum_congr rfl; intro κ _; ring
  have hBD : (∑ σ, ∑ ν, ∑ κ, gi x σ ν * (christoffel g gi κ lam ν x * ricci g gi σ κ x))
      = ∑ σ, ∑ ν, ∑ κ, christoffel g gi ν lam κ x * gi x σ κ * ricci g gi σ ν x := by
    rw [swap23 (fun σ ν κ => gi x σ ν * (christoffel g gi κ lam ν x * ricci g gi σ κ x))]
    apply Finset.sum_congr rfl; intro σ _; apply Finset.sum_congr rfl; intro ν _
    apply Finset.sum_congr rfl; intro κ _; ring
  simp only [covDeriv02, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hpd_scalar, hS_gipd, hAC, hBD]; ring

/-- **T3 core — contraction commutes with the Riemann divergence**: for fixed `ρ`,
    `∑_{σν} g^{σν} ∇_ρ R^ρ_{σνλ}` equals `∂_ρ S^ρ_λ + Γ^ρ_{ρκ}S^κ_λ − Γ^κ_{ρλ}S^ρ_κ`, the `(1,1)`
    covariant divergence of `S^a_b := ∑_{σν} g^{σν} R^a_{σνb}` — the `σ,ν` connection corrections of
    `covDerivRiem` cancel `∂g^{σν}` (`inv_metric_compat`) by the same swaps as T1. -/
theorem gi_trace_covDerivRiem (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ρ lam : Fin n) (x : Point n) :
    (∑ σ, ∑ ν, gi x σ ν * covDerivRiem g gi ρ ρ σ ν lam x)
      = pd (fun y => ∑ σ, ∑ ν, gi y σ ν * riemann g gi ρ σ ν lam y) ρ x
        + (∑ σ, ∑ ν, ∑ κ, gi x σ ν * (christoffel g gi ρ ρ κ x * riemann g gi κ σ ν lam x))
        - (∑ σ, ∑ ν, ∑ κ, gi x σ ν * (christoffel g gi κ ρ lam x * riemann g gi ρ σ ν κ x)) := by
  have hgd : ∀ a b, PdiffAt (fun y => g y a b) ρ x := fun a b =>
    PdiffAt_of_contDiff _ (hCg a b) ρ x
  have hgid : ∀ a b, PdiffAt (fun y => gi y a b) ρ x := fun a b =>
    PdiffAt_of_contDiff _ (hCgi a b) ρ x
  have hRiem : ∀ a b c d, PdiffAt (fun y => riemann g gi a b c d y) ρ x := fun a b c d =>
    PdiffAt_riemann g gi hC a b c d ρ x
  have swap13 : ∀ (F : Fin n → Fin n → Fin n → ℝ),
      (∑ σ, ∑ ν, ∑ κ, F σ ν κ) = ∑ σ, ∑ ν, ∑ κ, F κ ν σ := by
    intro F
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun ν _ => Finset.sum_comm), Finset.sum_comm]
  have swap23 : ∀ (F : Fin n → Fin n → Fin n → ℝ),
      (∑ σ, ∑ ν, ∑ κ, F σ ν κ) = ∑ σ, ∑ ν, ∑ κ, F σ κ ν := by
    intro F
    apply Finset.sum_congr rfl; intro σ _; rw [Finset.sum_comm]
  have hpd_S : pd (fun y => ∑ σ, ∑ ν, gi y σ ν * riemann g gi ρ σ ν lam y) ρ x
      = (∑ σ, ∑ ν, pd (fun y => gi y σ ν) ρ x * riemann g gi ρ σ ν lam x)
        + (∑ σ, ∑ ν, gi x σ ν * pd (fun y => riemann g gi ρ σ ν lam y) ρ x) := by
    rw [pd_sum Finset.univ (fun σ y => ∑ ν, gi y σ ν * riemann g gi ρ σ ν lam y) ρ x
          (fun σ _ => PdiffAt_sum _ _ ρ x (fun ν _ => (hgid σ ν).mul (hRiem ρ σ ν lam))),
        ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro σ _
    rw [pd_sum Finset.univ (fun ν y => gi y σ ν * riemann g gi ρ σ ν lam y) ρ x
          (fun ν _ => (hgid σ ν).mul (hRiem ρ σ ν lam)), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro ν _
    exact pd_mul (fun y => gi y σ ν) (fun y => riemann g gi ρ σ ν lam y) ρ x (hgid σ ν)
      (hRiem ρ σ ν lam)
  have hpd_gi : ∀ σ ν, pd (fun y => gi y σ ν) ρ x
      = -(∑ κ, christoffel g gi σ ρ κ x * gi x κ ν)
        - (∑ κ, christoffel g gi ν ρ κ x * gi x σ κ) := by
    intro σ ν
    have hm := inv_metric_compat g gi hsymm hsymm_gi hinv ρ x hgd hgid σ ν
    simp only [covDeriv20] at hm; linarith [hm]
  have hS_gipd : (∑ σ, ∑ ν, pd (fun y => gi y σ ν) ρ x * riemann g gi ρ σ ν lam x)
      = -(∑ σ, ∑ ν, ∑ κ, christoffel g gi σ ρ κ x * gi x κ ν * riemann g gi ρ σ ν lam x)
        - (∑ σ, ∑ ν, ∑ κ, christoffel g gi ν ρ κ x * gi x σ κ * riemann g gi ρ σ ν lam x) := by
    rw [Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun ν _ => by rw [hpd_gi σ ν]))]
    simp only [sub_mul, neg_mul, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hAC : (∑ σ, ∑ ν, ∑ κ, gi x σ ν * (christoffel g gi κ ρ σ x * riemann g gi ρ κ ν lam x))
      = ∑ σ, ∑ ν, ∑ κ, christoffel g gi σ ρ κ x * gi x κ ν * riemann g gi ρ σ ν lam x := by
    rw [swap13 (fun σ ν κ => gi x σ ν * (christoffel g gi κ ρ σ x * riemann g gi ρ κ ν lam x))]
    apply Finset.sum_congr rfl; intro σ _; apply Finset.sum_congr rfl; intro ν _
    apply Finset.sum_congr rfl; intro κ _; ring
  have hBD : (∑ σ, ∑ ν, ∑ κ, gi x σ ν * (christoffel g gi κ ρ ν x * riemann g gi ρ σ κ lam x))
      = ∑ σ, ∑ ν, ∑ κ, christoffel g gi ν ρ κ x * gi x σ κ * riemann g gi ρ σ ν lam x := by
    rw [swap23 (fun σ ν κ => gi x σ ν * (christoffel g gi κ ρ ν x * riemann g gi ρ σ κ lam x))]
    apply Finset.sum_congr rfl; intro σ _; apply Finset.sum_congr rfl; intro ν _
    apply Finset.sum_congr rfl; intro κ _; ring
  simp only [covDerivRiem, mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [hpd_S, hS_gipd, hAC, hBD]; ring

/-- **T3 core with `S` substituted to `−`(raised Ricci)** (via `ricci_gi_raise`): for fixed `ρ`,
    `∑_{σν} g^{σν} ∇_ρ R^ρ_{σνλ} = −∑_β g^{ρβ}∂_ρ Ric_{βλ} + ∑_{βκ} Γ^β_{ρκ}g^{ρκ}Ric_{βλ}
    + ∑_{βκ} Γ^κ_{ρλ}g^{ρβ}Ric_{βκ}`. The `Γ^ρ_{ρκ}` terms from `∂g` cancel the `∑Γ^ρ_{ρκ}S^κ` spectator. -/
theorem gi_trace_covDerivRiem_ricci (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ρ lam : Fin n) (x : Point n) :
    (∑ σ, ∑ ν, gi x σ ν * covDerivRiem g gi ρ ρ σ ν lam x)
      = - (∑ β, gi x ρ β * pd (fun y => ricci g gi β lam y) ρ x)
        + (∑ β, ∑ κ, christoffel g gi β ρ κ x * gi x ρ κ * ricci g gi β lam x)
        + (∑ β, ∑ κ, christoffel g gi κ ρ lam x * gi x ρ β * ricci g gi β κ x) := by
  have hgd : ∀ a b, PdiffAt (fun y => g y a b) ρ x := fun a b =>
    PdiffAt_of_contDiff _ (hCg a b) ρ x
  have hgid : ∀ a b, PdiffAt (fun y => gi y a b) ρ x := fun a b =>
    PdiffAt_of_contDiff _ (hCgi a b) ρ x
  have hRic : ∀ a b, PdiffAt (fun y => ricci g gi a b y) ρ x := fun a b =>
    PdiffAt_ricci g gi hC a b ρ x
  have moveκ : ∀ (F : Fin n → Fin n → Fin n → ℝ),
      (∑ σ, ∑ ν, ∑ κ, F σ ν κ) = ∑ κ, ∑ σ, ∑ ν, F σ ν κ := by
    intro F
    rw [Finset.sum_congr rfl (fun σ _ => Finset.sum_comm), Finset.sum_comm]
  have hpd_gi : ∀ a b, pd (fun y => gi y a b) ρ x
      = -(∑ κ, christoffel g gi a ρ κ x * gi x κ b) - (∑ κ, christoffel g gi b ρ κ x * gi x a κ) := by
    intro a b
    have hm := inv_metric_compat g gi hsymm hsymm_gi hinv ρ x hgd hgid a b
    simp only [covDeriv20] at hm; linarith [hm]
  have hSfun : (fun y => ∑ σ, ∑ ν, gi y σ ν * riemann g gi ρ σ ν lam y)
             = (fun y => (-1 : ℝ) * ∑ β, gi y ρ β * ricci g gi β lam y) := by
    funext y; rw [ricci_gi_raise g gi hsymm hsymm_gi hinv hCg hC ρ lam y]; ring
  have hpd_S : pd (fun y => ∑ σ, ∑ ν, gi y σ ν * riemann g gi ρ σ ν lam y) ρ x
      = -(∑ β, pd (fun y => gi y ρ β) ρ x * ricci g gi β lam x)
        - (∑ β, gi x ρ β * pd (fun y => ricci g gi β lam y) ρ x) := by
    rw [hSfun, pd_const_mul (-1) _ ρ x
          (PdiffAt_sum _ _ ρ x (fun β _ => (hgid ρ β).mul (hRic β lam))),
        pd_sum Finset.univ (fun β y => gi y ρ β * ricci g gi β lam y) ρ x
          (fun β _ => (hgid ρ β).mul (hRic β lam)),
        Finset.sum_congr rfl (fun β (_ : β ∈ Finset.univ) =>
          pd_mul (fun y => gi y ρ β) (fun y => ricci g gi β lam y) ρ x (hgid ρ β) (hRic β lam)),
        Finset.sum_add_distrib]
    ring
  have hspect1 : (∑ σ, ∑ ν, ∑ κ, gi x σ ν * (christoffel g gi ρ ρ κ x * riemann g gi κ σ ν lam x))
      = - ∑ β, ∑ κ, christoffel g gi ρ ρ κ x * gi x κ β * ricci g gi β lam x := by
    rw [moveκ (fun σ ν κ => gi x σ ν * (christoffel g gi ρ ρ κ x * riemann g gi κ σ ν lam x)),
        Finset.sum_congr rfl (fun κ (_ : κ ∈ Finset.univ) => by
          rw [show (∑ σ, ∑ ν, gi x σ ν * (christoffel g gi ρ ρ κ x * riemann g gi κ σ ν lam x))
                = christoffel g gi ρ ρ κ x * (∑ σ, ∑ ν, gi x σ ν * riemann g gi κ σ ν lam x) from by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro σ _
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ν _; ring,
            ricci_gi_raise g gi hsymm hsymm_gi hinv hCg hC κ lam x])]
    simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro β _; apply Finset.sum_congr rfl; intro κ _; ring
  have hspect2 : (∑ σ, ∑ ν, ∑ κ, gi x σ ν * (christoffel g gi κ ρ lam x * riemann g gi ρ σ ν κ x))
      = - ∑ β, ∑ κ, christoffel g gi κ ρ lam x * gi x ρ β * ricci g gi β κ x := by
    rw [moveκ (fun σ ν κ => gi x σ ν * (christoffel g gi κ ρ lam x * riemann g gi ρ σ ν κ x)),
        Finset.sum_congr rfl (fun κ (_ : κ ∈ Finset.univ) => by
          rw [show (∑ σ, ∑ ν, gi x σ ν * (christoffel g gi κ ρ lam x * riemann g gi ρ σ ν κ x))
                = christoffel g gi κ ρ lam x * (∑ σ, ∑ ν, gi x σ ν * riemann g gi ρ σ ν κ x) from by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro σ _
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ν _; ring,
            ricci_gi_raise g gi hsymm hsymm_gi hinv hCg hC ρ κ x])]
    simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro β _; apply Finset.sum_congr rfl; intro κ _; ring
  rw [gi_trace_covDerivRiem g gi hsymm hsymm_gi hinv hCg hCgi hC ρ lam x, hpd_S, hspect1, hspect2,
      Finset.sum_congr rfl (fun β (_ : β ∈ Finset.univ) => by
        rw [show pd (fun y => gi y ρ β) ρ x * ricci g gi β lam x
              = (-(∑ κ, christoffel g gi ρ ρ κ x * gi x κ β)
                  - (∑ κ, christoffel g gi β ρ κ x * gi x ρ κ)) * ricci g gi β lam x from by
            rw [hpd_gi ρ β]])]
  simp only [sub_mul, neg_mul, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end QIQTH.Curvature
