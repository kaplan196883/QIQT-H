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

end QIQTH.Curvature
