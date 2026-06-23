/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The explicit Klein–Gordon stress tensor and its covariant conservation

The QIQT→GR derivation (`WedgeKMSToGR.lean`) consumes a `conserv` hypothesis `∇·(a·T) = 0` for the matter
stress tensor.  This file begins discharging it for the *explicit* free Klein–Gordon field by constructing the
concrete stress tensor `T_{ab} = ∂_a φ ∂_b φ − ½ g_{ab} L` (with Lagrangian `L = g^{αβ}∂_αφ ∂_βφ − m²φ²`) and
reducing its covariant divergence to the purely *kinetic* identity `∇^μ K_{μν} = ½ ∂_ν L` — the only piece that
still needs the Klein–Gordon equation of motion.  The scalar/metric term is dispatched by metric compatibility
(`div02_scalar_metric`), exactly as the cosmological-constant term is.

All results axiom-free.
-/
import QIQTH.EinsteinFieldEquation

namespace QIQTH.Curvature

variable {n : ℕ}

/-- The KG **kinetic** `(0,2)` tensor `K_{ab} = ∂_a φ · ∂_b φ`. -/
noncomputable def kgKinetic (φ : Point n → ℝ) (y : Point n) (a b : Fin n) : ℝ :=
  pd φ a y * pd φ b y

/-- The KG **Lagrangian scalar** `L = g^{αβ} ∂_α φ ∂_β φ + m² φ²` (the combination appearing inside the trace
    term of the stress tensor; the sign makes `∇^μ T_{μν} = 0` close against the equation of motion `□φ = m²φ`). -/
noncomputable def kgLagr (m : ℝ) (φ : Point n → ℝ) (gi : Point n → Fin n → Fin n → ℝ)
    (y : Point n) : ℝ :=
  (∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) + m ^ 2 * (φ y) ^ 2

/-- The **Klein–Gordon stress tensor** `T_{ab} = ∂_a φ ∂_b φ − ½ g_{ab} L`. -/
noncomputable def kgStress (m : ℝ) (φ : Point n → ℝ)
    (g gi : Point n → Fin n → Fin n → ℝ) (y : Point n) (a b : Fin n) : ℝ :=
  pd φ a y * pd φ b y - (1 / 2 : ℝ) * g y a b * kgLagr m φ gi y

/-- **Conservation SPLIT.**  The covariant divergence of the KG stress tensor reduces to the kinetic
    divergence minus half the Lagrangian gradient:
    `∇^μ T_{μν} = ∇^μ K_{μν} − ½ ∂_ν L`.
    The scalar/metric term `½ g_{μν} L` is handled by metric compatibility (`div02_scalar_metric`, the same
    mechanism that makes `Λ·g` covariantly constant); what remains — the kinetic identity
    `∇^μ K_{μν} = ½ ∂_ν L` — is the Klein–Gordon equation of motion in disguise (the next brick).  This is the
    first step of discharging the `conserv` input of the free-field QIQT→GR surface. -/
theorem div02_kgStress_eq (m : ℝ) (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (x : Point n) (ν : Fin n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hKin : ∀ a b ρ, PdiffAt (fun y => kgKinetic φ y a b) ρ x)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (hL : ∀ ρ, PdiffAt (kgLagr m φ gi) ρ x) :
    div02 g gi (kgStress m φ g gi) ν x
      = div02 g gi (kgKinetic φ) ν x - (1 / 2 : ℝ) * pd (kgLagr m φ gi) ν x := by
  -- write `T = K + f·g` with `f = −½ L`
  have hfdef : (kgStress m φ g gi)
      = fun y a b => kgKinetic φ y a b + (-(1 / 2 : ℝ) * kgLagr m φ gi y) * g y a b := by
    funext y a b
    simp only [kgStress, kgKinetic]
    ring
  have hconst : ∀ ρ, PdiffAt (fun _ : Point n => -(1 / 2 : ℝ)) ρ x := fun _ => differentiableAt_const _
  have hf : ∀ ρ, PdiffAt (fun y => -(1 / 2 : ℝ) * kgLagr m φ gi y) ρ x := fun ρ => (hconst ρ).mul (hL ρ)
  have hfg : ∀ a b ρ, PdiffAt (fun y => (-(1 / 2 : ℝ) * kgLagr m φ gi y) * g y a b) ρ x :=
    fun a b ρ => (hf ρ).mul (hg a b ρ)
  rw [hfdef,
    div02_add g gi (kgKinetic φ) (fun y a b => (-(1 / 2 : ℝ) * kgLagr m φ gi y) * g y a b) x hKin hfg ν,
    div02_scalar_metric g gi hsymm hinv (fun y => -(1 / 2 : ℝ) * kgLagr m φ gi y) x hf hg ν,
    pd_const_mul (-(1 / 2 : ℝ)) (kgLagr m φ gi) ν x (hL ν)]
  ring

/-- The **covariant Hessian** of the scalar `φ`: `(∇∇φ)_{ρμ} = ∂_ρ ∂_μ φ − Γ^σ_{ρμ} ∂_σ φ` (the covariant
    derivative of the gradient covector `∂φ`).  It is symmetric in `ρ μ` (torsion-free connection), which the
    kinetic identity will use. -/
noncomputable def kgHess (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (ρ μ : Fin n) (x : Point n) : ℝ :=
  pd (fun y => pd φ μ y) ρ x - ∑ σ, christoffel g gi σ ρ μ x * pd φ σ x

/-- **Leibniz/product rule for the kinetic tensor.**  The covariant derivative of `K_{μν} = ∂_μφ ∂_νφ`
    factors through the covariant Hessian:
    `(∇_ρ K)_{μν} = (∇∇φ)_{ρμ} ∂_νφ + ∂_μφ (∇∇φ)_{ρν}`.
    Each Christoffel term in `covDeriv02` regroups (by `Finset.sum_mul`/`Finset.mul_sum`) into exactly one of
    the two Hessians, leaving the partial-derivative Leibniz term (`pd_mul`).  This is the second brick of the
    `conserv` discharge: contracting it with `g^{μρ}` and using `□φ = m²φ` + Hessian symmetry will give
    `∇^μ K_{μν} = ½ ∂_ν L`, closing conservation via `div02_kgStress_eq`. -/
theorem covDeriv02_kgKinetic (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (ρ μ ν : Fin n) (x : Point n) (hφ2 : ∀ i j, PdiffAt (fun y => pd φ i y) j x) :
    covDeriv02 g gi (kgKinetic φ) ρ μ ν x
      = kgHess φ g gi ρ μ x * pd φ ν x + pd φ μ x * kgHess φ g gi ρ ν x := by
  have hs1 : (∑ σ, christoffel g gi σ ρ μ x * pd φ σ x) * pd φ ν x
      = ∑ σ, christoffel g gi σ ρ μ x * (pd φ σ x * pd φ ν x) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun σ _ => by ring)
  have hs2 : pd φ μ x * (∑ σ, christoffel g gi σ ρ ν x * pd φ σ x)
      = ∑ σ, christoffel g gi σ ρ ν x * (pd φ μ x * pd φ σ x) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun σ _ => by ring)
  simp only [covDeriv02, kgKinetic, kgHess]
  rw [pd_mul (fun y => pd φ μ y) (fun y => pd φ ν y) ρ x (hφ2 μ ρ) (hφ2 ν ρ),
    sub_mul, mul_sub, hs1, hs2]
  ring

/-- The **d'Alembertian** `□φ = g^{μρ} (∇∇φ)_{ρμ}` (the covariant Laplace–Beltrami of the scalar `φ`). -/
noncomputable def boxField (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ) (x : Point n) : ℝ :=
  ∑ μ, ∑ ρ, gi x μ ρ * kgHess φ g gi ρ μ x

/-- **Kinetic divergence in Hessian form.**  Contracting the Leibniz rule (`covDeriv02_kgKinetic`) with the
    inverse metric splits the kinetic divergence into the `□φ` piece and a Hessian-gradient piece:
    `∇^μ K_{μν} = (□φ) ∂_νφ + g^{μρ} ∂_μφ (∇∇φ)_{ρν}`.
    The first piece is exactly where the Klein–Gordon equation `□φ = m²φ` enters; the second is `½ ∂_ν` of the
    kinetic part of `L` (by Hessian symmetry + metric compatibility) — the two facts that, with
    `div02_kgStress_eq`, close `∇^μ T_{μν} = 0`.  This is the third brick of the `conserv` discharge. -/
theorem div02_kgKinetic_eq (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (ν : Fin n) (x : Point n) (hφ2 : ∀ i j, PdiffAt (fun y => pd φ i y) j x) :
    div02 g gi (kgKinetic φ) ν x
      = boxField φ g gi x * pd φ ν x
        + ∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * kgHess φ g gi ρ ν x) := by
  have hsum : ∀ μ ρ : Fin n, gi x μ ρ * covDeriv02 g gi (kgKinetic φ) ρ μ ν x
      = gi x μ ρ * kgHess φ g gi ρ μ x * pd φ ν x
        + gi x μ ρ * (pd φ μ x * kgHess φ g gi ρ ν x) := by
    intro μ ρ; rw [covDeriv02_kgKinetic φ g gi ρ μ ν x hφ2]; ring
  simp only [div02]
  rw [Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ρ _ => hsum μ ρ))]
  simp only [Finset.sum_add_distrib]
  congr 1
  rw [boxField, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun μ _ => by rw [Finset.sum_mul])

/-- **The covariant Hessian of a scalar is symmetric** `(∇∇φ)_{ρμ} = (∇∇φ)_{μρ}`: the partial-derivative
    part commutes (`pd_comm`, smoothness) and the Christoffel part is symmetric in its lower indices
    (`christoffel_symm`, torsion-freeness).  This symmetry is exactly what turns the Hessian-gradient term into
    a perfect `∂_ν` of the kinetic scalar. -/
theorem kgHess_symm (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ) (ρ μ : Fin n) (x : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a) (hφ : ContDiff ℝ ⊤ φ) :
    kgHess φ g gi ρ μ x = kgHess φ g gi μ ρ x := by
  simp only [kgHess]
  rw [pd_comm φ ρ μ x hφ]
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => by rw [christoffel_symm g gi hsymm σ ρ μ x])

/-- **★ KG STRESS-TENSOR CONSERVATION (final assembly), conditional on the two physical/geometric facts.**
    For the explicit Klein–Gordon field, `∇^μ T_{μν} = 0` follows from exactly:
    * `hKG`  — the equation of motion `□φ = m²φ` (`boxField φ = m²·φ`); and
    * `hHessGrad` — the Hessian-gradient identity `g^{μρ} ∂_μφ (∇∇φ)_{ρν} = ½ ∂_ν(g^{αβ}∂_αφ ∂_βφ)`, the one
      place metric compatibility (`metric_compat`, `∇g = 0`) + Hessian symmetry (`kgHess_symm`) enter.
    Given these, the split (`div02_kgStress_eq`) + contraction (`div02_kgKinetic_eq`) collapse algebraically:
    `∇^μ T_{μν} = (□φ − m²φ) ∂_νφ = 0`.  This discharges the `conserv` input of the free-field QIQT→GR surface
    down to the Klein–Gordon equation of motion + the (purely geometric) Hessian-gradient metric-compatibility
    identity — no other physics. -/
theorem div02_kgStress_conserved (m : ℝ) (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (x : Point n) (ν : Fin n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hKin : ∀ a b ρ, PdiffAt (fun y => kgKinetic φ y a b) ρ x)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (hL : ∀ ρ, PdiffAt (kgLagr m φ gi) ρ x)
    (hφ2 : ∀ i j, PdiffAt (fun y => pd φ i y) j x)
    (hφd : PdiffAt φ ν x)
    (hgradSq : PdiffAt (fun y => ∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) ν x)
    (hKG : boxField φ g gi x = m ^ 2 * φ x)
    (hHessGrad : (∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * kgHess φ g gi ρ ν x))
        = (1 / 2 : ℝ) * pd (fun y => ∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) ν x) :
    div02 g gi (kgStress m φ g gi) ν x = 0 := by
  have hmsq : PdiffAt (fun y => m ^ 2 * (φ y) ^ 2) ν x := by
    have h1 : PdiffAt (fun y => (φ y) ^ 2) ν x := by
      rw [show (fun y => (φ y) ^ 2) = fun y => φ y * φ y by funext y; ring]
      exact hφd.mul hφd
    have hconst : PdiffAt (fun _ : Point n => m ^ 2) ν x := differentiableAt_const _
    exact hconst.mul h1
  have hLsplit : pd (kgLagr m φ gi) ν x
      = pd (fun y => ∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) ν x
        + pd (fun y => m ^ 2 * (φ y) ^ 2) ν x := by
    have hLeq : (kgLagr m φ gi)
        = fun y => (∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) + m ^ 2 * (φ y) ^ 2 := by
      funext y; rfl
    rw [hLeq, pd_add _ _ ν x hgradSq hmsq]
  have hmsqpd : pd (fun y => m ^ 2 * (φ y) ^ 2) ν x = m ^ 2 * (2 * φ x * pd φ ν x) := by
    rw [show (fun y => m ^ 2 * (φ y) ^ 2) = fun y => m ^ 2 * (φ y * φ y) by funext y; ring,
      pd_const_mul (m ^ 2) (fun y => φ y * φ y) ν x (hφd.mul hφd), pd_mul φ φ ν x hφd hφd]
    ring
  rw [div02_kgStress_eq m φ g gi x ν hsymm hinv hKin hg hL,
    div02_kgKinetic_eq φ g gi ν x hφ2, hKG, hHessGrad, hLsplit, hmsqpd]
  ring

/-- **Differentiated inverse relation** (`∂(g·gi = δ)`): for a pointwise inverse metric, differentiating the
    identity `∑_α g_{μα} gi^{αβ} = δ_μ^β` gives `∑_α ∂_ν(g_{μα}) gi^{αβ} + ∑_α g_{μα} ∂_ν(gi^{αβ}) = 0`.  This is
    the first step toward inverse-metric compatibility `∇gi = 0` (which then follows by contracting with `gi^{λμ}`
    and substituting `metric_compat` for `∂g`), the one geometric fact still needed for `hHessGrad`. -/
theorem pd_metric_inv_identity (g gi : Point n → Fin n → Fin n → ℝ) (μ β ν : Fin n) (x : Point n)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (hgi : ∀ a b ρ, PdiffAt (fun y => gi y a b) ρ x) :
    (∑ α, pd (fun y => g y μ α) ν x * gi x α β)
      + (∑ α, g x μ α * pd (fun y => gi y α β) ν x) = 0 := by
  have h1 : pd (fun y => ∑ α, g y μ α * gi y α β) ν x = 0 := by
    have heq : (fun y => ∑ α, g y μ α * gi y α β) = fun _ => (if μ = β then (1 : ℝ) else 0) := by
      funext y; exact hinv y μ β
    rw [heq]; exact pd_const _ ν x
  have h2 : pd (fun y => ∑ α, g y μ α * gi y α β) ν x
      = (∑ α, pd (fun y => g y μ α) ν x * gi x α β)
        + (∑ α, g x μ α * pd (fun y => gi y α β) ν x) := by
    rw [pd_sum Finset.univ (fun α y => g y μ α * gi y α β) ν x
        (fun α _ => (hg μ α ν).mul (hgi α β ν)), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun α _ =>
      pd_mul (fun y => g y μ α) (fun y => gi y α β) ν x (hg μ α ν) (hgi α β ν))
  rw [← h2, h1]

/-- **The inverse metric is a left inverse too** `∑_μ gi^{aμ} g_{μb} = δ^a_b` (from the right-inverse `hinv`
    plus symmetry of `g` and `gi`).  The δ used to extract `∂gi` in the inverse-metric compatibility. -/
theorem gi_g_delta (g gi : Point n → Fin n → Fin n → ℝ) (x : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0) (a b : Fin n) :
    (∑ μ, gi x a μ * g x μ b) = if a = b then 1 else 0 := by
  have hrw : (∑ μ, gi x a μ * g x μ b) = ∑ μ, g x b μ * gi x μ a := by
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [hsymm_gi x a μ, hsymm x μ b]; ring
  rw [hrw, hinv b a]
  rcases eq_or_ne a b with h | h
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

/-- **`∂g` in terms of the connection** `∂_ν g_{μα} = ∑σ Γ^σ_{νμ} g_{σα} + ∑σ Γ^σ_{να} g_{μσ}` — the explicit
    content of metric compatibility `∇g = 0` (`metric_compat`), unpacked from the `covDeriv02` definition. -/
theorem pd_g_eq (g gi : Point n → Fin n → Fin n → ℝ) (μ α ν : Fin n) (x : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0) :
    pd (fun y => g y μ α) ν x
      = (∑ σ, christoffel g gi σ ν μ x * g x σ α) + (∑ σ, christoffel g gi σ ν α x * g x μ σ) := by
  have h := metric_compat g gi hsymm x hinv ν μ α
  simp only [covDeriv02] at h
  linarith [h]

/-- **★ INVERSE-METRIC COMPATIBILITY `∇gi = 0`** (upper-index companion of `metric_compat`):
    `∂_ν gi^{λβ} = −∑σ Γ^λ_{νσ} gi^{σβ} − ∑σ Γ^β_{νσ} gi^{σλ}`.
    Contract the differentiated inverse relation (`pd_metric_inv_identity`) with `gi^{λμ}`, extract `∂gi^{λβ}` via
    the δ-identity `gi_g_delta`, substitute `pd_g_eq` for `∂g`, and collapse the two double sums by the
    δ-contractions `∑α g_{σα}gi^{αβ} = δ_σ^β` (`hinv`) and `∑μ gi^{λμ}g_{μσ} = δ^λ_σ` (`gi_g_delta`).  The last
    purely-geometric fact needed for `hHessGrad`. -/
theorem pd_gi_eq (g gi : Point n → Fin n → Fin n → ℝ) (lam β ν : Fin n) (x : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (hgi : ∀ a b ρ, PdiffAt (fun y => gi y a b) ρ x) :
    pd (fun y => gi y lam β) ν x
      = - (∑ σ, christoffel g gi lam ν σ x * gi x σ β)
        - (∑ σ, christoffel g gi β ν σ x * gi x σ lam) := by
  classical
  have hinvx : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0 := fun a b => hinv x a b
  -- extraction: `∑μ gi^{λμ} (∑α g_{μα} w_α) = w_λ`
  have hExtract : (∑ μ, gi x lam μ * (∑ α, g x μ α * pd (fun y => gi y α β) ν x))
      = pd (fun y => gi y lam β) ν x := by
    have e1 : (∑ μ, gi x lam μ * (∑ α, g x μ α * pd (fun y => gi y α β) ν x))
        = ∑ α, (∑ μ, gi x lam μ * g x μ α) * pd (fun y => gi y α β) ν x := by
      have e0 : (∑ μ, gi x lam μ * (∑ α, g x μ α * pd (fun y => gi y α β) ν x))
          = ∑ μ, ∑ α, gi x lam μ * g x μ α * pd (fun y => gi y α β) ν x := by
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun α _ => by ring)
      rw [e0, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [Finset.sum_mul]
    rw [e1, Finset.sum_congr rfl (fun α _ => by rw [gi_g_delta g gi x hsymm hsymm_gi hinvx lam α])]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  -- metric-contracted identity from `pd_metric_inv_identity`
  have hME : ∀ μ : Fin n, (∑ α, g x μ α * pd (fun y => gi y α β) ν x)
      = - ∑ α, pd (fun y => g y μ α) ν x * gi x α β := by
    intro μ; linarith [pd_metric_inv_identity g gi μ β ν x hinv hg hgi]
  -- inner δ-contraction A: `∑α (∑σ Γσνμ gσα) giαβ = Γβνμ`
  have hTAi : ∀ μ : Fin n,
      (∑ α, (∑ σ, christoffel g gi σ ν μ x * g x σ α) * gi x α β) = christoffel g gi β ν μ x := by
    intro μ
    have e1 : (∑ α, (∑ σ, christoffel g gi σ ν μ x * g x σ α) * gi x α β)
        = ∑ σ, christoffel g gi σ ν μ x * (∑ α, g x σ α * gi x α β) := by
      have e0 : (∑ α, (∑ σ, christoffel g gi σ ν μ x * g x σ α) * gi x α β)
          = ∑ α, ∑ σ, christoffel g gi σ ν μ x * g x σ α * gi x α β := by
        refine Finset.sum_congr rfl (fun α _ => ?_); rw [Finset.sum_mul]
      rw [e0, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun α _ => by ring)
    rw [e1, Finset.sum_congr rfl (fun σ _ => by rw [hinvx σ β])]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- Claim A: `∑μ gi^{λμ} TA_μ = ∑σ Γβνσ giσλ`
  have hClaimA : (∑ μ, gi x lam μ * (∑ α, (∑ σ, christoffel g gi σ ν μ x * g x σ α) * gi x α β))
      = ∑ σ, christoffel g gi β ν σ x * gi x σ lam := by
    rw [Finset.sum_congr rfl (fun μ _ => by rw [hTAi μ])]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [hsymm_gi x lam μ]; ring
  -- Claim B: `∑μ gi^{λμ} TB_μ = ∑σ Γλνσ giσβ` (the δ is over μ, so reorder first)
  have hClaimB : (∑ μ, gi x lam μ * (∑ α, (∑ σ, christoffel g gi σ ν α x * g x μ σ) * gi x α β))
      = ∑ σ, christoffel g gi lam ν σ x * gi x σ β := by
    have e1 : (∑ μ, gi x lam μ * (∑ α, (∑ σ, christoffel g gi σ ν α x * g x μ σ) * gi x α β))
        = ∑ μ, ∑ α, ∑ σ, gi x lam μ * g x μ σ * christoffel g gi σ ν α x * gi x α β := by
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun σ _ => by ring)
    rw [e1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.sum_comm]
    have e2 : (∑ σ, ∑ μ, gi x lam μ * g x μ σ * christoffel g gi σ ν α x * gi x α β)
        = ∑ σ, (∑ μ, gi x lam μ * g x μ σ) * (christoffel g gi σ ν α x * gi x α β) := by
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun μ _ => by ring)
    rw [e2, Finset.sum_congr rfl (fun σ _ => by rw [gi_g_delta g gi x hsymm hsymm_gi hinvx lam σ])]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  -- RHS contraction
  have hRHS : (∑ μ, gi x lam μ * (∑ α, pd (fun y => g y μ α) ν x * gi x α β))
      = (∑ σ, christoffel g gi lam ν σ x * gi x σ β)
        + (∑ σ, christoffel g gi β ν σ x * gi x σ lam) := by
    have hsub : ∀ μ, (∑ α, pd (fun y => g y μ α) ν x * gi x α β)
        = (∑ α, (∑ σ, christoffel g gi σ ν μ x * g x σ α) * gi x α β)
          + (∑ α, (∑ σ, christoffel g gi σ ν α x * g x μ σ) * gi x α β) := by
      intro μ
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [pd_g_eq g gi μ α ν x hsymm hinvx]; ring
    rw [Finset.sum_congr rfl (fun μ _ => by rw [hsub μ, mul_add]), Finset.sum_add_distrib,
      hClaimA, hClaimB, add_comm]
  -- assemble
  have hfinal : (∑ μ, gi x lam μ * (∑ α, g x μ α * pd (fun y => gi y α β) ν x))
      = - (∑ μ, gi x lam μ * (∑ α, pd (fun y => g y μ α) ν x * gi x α β)) := by
    rw [Finset.sum_congr rfl (fun μ _ => by rw [hME μ, mul_neg]), Finset.sum_neg_distrib]
  rw [← hExtract, hfinal, hRHS]
  ring

/-- **Product-rule expansion of the kinetic-scalar gradient** `∂_ν(g^{αβ}∂_αφ∂_βφ)`.  Differentiating term by
    term (`pd_sum` twice, `pd_mul` for the triple product) splits it into the `∂gi` term plus the two
    `∂(∂φ)` terms:
    `∂_ν(∑_{αβ} gi^{αβ}∂_αφ∂_βφ) = ∑_{αβ} ∂_ν(gi^{αβ})∂_αφ∂_βφ + ∑_{αβ} gi^{αβ}(∂_ν∂_αφ)∂_βφ
      + ∑_{αβ} gi^{αβ}∂_αφ(∂_ν∂_βφ)`.
    The first term meets `pd_gi_eq` (inverse-metric compatibility) and the last two meet the Hessian partials
    (`pd_comm`) in the final `hHessGrad` assembly. -/
theorem pd_gradSq_eq (φ : Point n → ℝ) (gi : Point n → Fin n → Fin n → ℝ) (ν : Fin n) (x : Point n)
    (hgi : ∀ a b ρ, PdiffAt (fun y => gi y a b) ρ x)
    (hφ2 : ∀ i j, PdiffAt (fun y => pd φ i y) j x) :
    pd (fun y => ∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) ν x
      = (∑ α, ∑ β, pd (fun y => gi y α β) ν x * (pd φ α x * pd φ β x))
        + ((∑ α, ∑ β, gi x α β * (pd (fun y => pd φ α y) ν x * pd φ β x))
          + (∑ α, ∑ β, gi x α β * (pd φ α x * pd (fun y => pd φ β y) ν x))) := by
  have hterm : ∀ α β : Fin n, pd (fun y => gi y α β * (pd φ α y * pd φ β y)) ν x
      = pd (fun y => gi y α β) ν x * (pd φ α x * pd φ β x)
        + gi x α β * (pd (fun y => pd φ α y) ν x * pd φ β x)
        + gi x α β * (pd φ α x * pd (fun y => pd φ β y) ν x) := by
    intro α β
    rw [pd_mul (fun y => gi y α β) (fun y => pd φ α y * pd φ β y) ν x (hgi α β ν)
        ((hφ2 α ν).mul (hφ2 β ν)),
      pd_mul (fun y => pd φ α y) (fun y => pd φ β y) ν x (hφ2 α ν) (hφ2 β ν)]
    ring
  rw [pd_sum Finset.univ (fun α y => ∑ β, gi y α β * (pd φ α y * pd φ β y)) ν x
      (fun α _ => PdiffAt_sum Finset.univ (fun β y => gi y α β * (pd φ α y * pd φ β y)) ν x
        (fun β _ => (hgi α β ν).mul ((hφ2 α ν).mul (hφ2 β ν))))]
  rw [Finset.sum_congr rfl (fun α _ =>
      pd_sum Finset.univ (fun β y => gi y α β * (pd φ α y * pd φ β y)) ν x
        (fun β _ => (hgi α β ν).mul ((hφ2 α ν).mul (hφ2 β ν))))]
  rw [Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => hterm α β))]
  simp only [Finset.sum_add_distrib]
  ring

/-- **The two cross gradient terms are equal** `R2 = R3`: `∑_{αβ} gi^{αβ}(∂_ν∂_αφ)∂_βφ =
    ∑_{αβ} gi^{αβ}∂_αφ(∂_ν∂_βφ)` (swap `α ↔ β`, `gi`-symmetry).  Used to fold the two `∂(∂φ)` terms of
    `pd_gradSq_eq` into one in `hHessGrad`. -/
theorem gradSq_cross_symm (φ : Point n → ℝ) (gi : Point n → Fin n → Fin n → ℝ) (ν : Fin n) (x : Point n)
    (hsymm_gi : ∀ y a b, gi y a b = gi y b a) :
    (∑ α, ∑ β, gi x α β * (pd (fun y => pd φ α y) ν x * pd φ β x))
      = ∑ α, ∑ β, gi x α β * (pd φ α x * pd (fun y => pd φ β y) ν x) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
  rw [hsymm_gi x β α]; ring

/-- **The Hessian-partial term equals `R2`** `T1 = R2`: `∑_{μρ} gi^{μρ}∂_μφ ∂_ρ∂_νφ =
    ∑_{αβ} gi^{αβ}(∂_ν∂_αφ)∂_βφ` (commute the second derivative by `pd_comm`, then relabel `μ↔β, ρ↔α` via
    `gi`-symmetry).  This is the partial-derivative half of the Hessian-gradient identity. -/
theorem hessGrad_partial_eq (φ : Point n → ℝ) (gi : Point n → Fin n → Fin n → ℝ) (ν : Fin n) (x : Point n)
    (hsymm_gi : ∀ y a b, gi y a b = gi y b a) (hφ : ContDiff ℝ ⊤ φ) :
    (∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * pd (fun y => pd φ ν y) ρ x))
      = ∑ α, ∑ β, gi x α β * (pd (fun y => pd φ α y) ν x * pd φ β x) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
  rw [pd_comm φ α ν x hφ, hsymm_gi x β α]; ring

/-- **★★ THE HESSIAN-GRADIENT IDENTITY `hHessGrad`** — the last brick of the `conserv` discharge:
    `g^{μρ}∂_μφ(∇∇φ)_{ρν} = ½ ∂_ν(g^{αβ}∂_αφ∂_βφ)`.
    Decompose the LHS `= T1 − T2` (Hessian partials minus the Christoffel term) and the RHS `= ½(R1+R2+R3)`
    (`pd_gradSq_eq`).  Then `T1 = R2` (`hessGrad_partial_eq`), `R2 = R3` (`gradSq_cross_symm`), and `T2 = −½R1`
    (the Christoffel term: substitute `pd_gi_eq` into `R1`, giving `R1 = −P − Q`; `Q = P` by α↔β; `P = T2` by a
    triple-sum reindex with `christoffel_symm` + gi-symmetry).  Algebra then closes `LHS = R2 − T2 = ½R1 + R2 =
    ½(R1+R2+R3) = RHS`.  Feeding this to `div02_kgStress_conserved` makes KG conservation `∇^μ T_{μν} = 0`
    unconditional (modulo only the matter equation of motion `□φ = m²φ`). -/
theorem hHessGrad_eq (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ) (ν : Fin n) (x : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (hgi : ∀ a b ρ, PdiffAt (fun y => gi y a b) ρ x)
    (hφ2 : ∀ i j, PdiffAt (fun y => pd φ i y) j x) (hφ : ContDiff ℝ ⊤ φ) :
    (∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * kgHess φ g gi ρ ν x))
      = (1 / 2 : ℝ) * pd (fun y => ∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) ν x := by
  classical
  -- the Christoffel term `T2 = −½ R1`
  have hT2R1 : (∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * ∑ σ, christoffel g gi σ ρ ν x * pd φ σ x))
      = -(1 / 2 : ℝ) * (∑ α, ∑ β, pd (fun y => gi y α β) ν x * (pd φ α x * pd φ β x)) := by
    -- P = T2 (triple-sum reindex)
    have hPT2 : (∑ α, ∑ β, (∑ σ, christoffel g gi α ν σ x * gi x σ β) * (pd φ α x * pd φ β x))
        = ∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * ∑ σ, christoffel g gi σ ρ ν x * pd φ σ x) := by
      have hT2 : (∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * ∑ σ, christoffel g gi σ ρ ν x * pd φ σ x))
          = ∑ μ, ∑ ρ, ∑ σ, gi x μ ρ * christoffel g gi σ ρ ν x * (pd φ μ x * pd φ σ x) := by
        refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ρ _ => ?_))
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => by ring)
      have hP : (∑ α, ∑ β, (∑ σ, christoffel g gi α ν σ x * gi x σ β) * (pd φ α x * pd φ β x))
          = ∑ α, ∑ β, ∑ σ, christoffel g gi α ν σ x * gi x σ β * (pd φ α x * pd φ β x) := by
        refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
        rw [Finset.sum_mul]
      rw [hP, hT2, Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun β _ => Finset.sum_comm
        (f := fun α σ => christoffel g gi α ν σ x * gi x σ β * (pd φ α x * pd φ β x)))]
      refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ρ _ =>
        Finset.sum_congr rfl (fun σ _ => ?_)))
      rw [christoffel_symm g gi hsymm σ ρ ν x, hsymm_gi x ρ μ]; ring
    -- Q = P (α↔β)
    have hQP : (∑ α, ∑ β, (∑ σ, christoffel g gi β ν σ x * gi x σ α) * (pd φ α x * pd φ β x))
        = ∑ α, ∑ β, (∑ σ, christoffel g gi α ν σ x * gi x σ β) * (pd φ α x * pd φ β x) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => by ring))
    -- R1 = −P − Q
    have hR1 : (∑ α, ∑ β, pd (fun y => gi y α β) ν x * (pd φ α x * pd φ β x))
        = - (∑ α, ∑ β, (∑ σ, christoffel g gi α ν σ x * gi x σ β) * (pd φ α x * pd φ β x))
          - (∑ α, ∑ β, (∑ σ, christoffel g gi β ν σ x * gi x σ α) * (pd φ α x * pd φ β x)) := by
      have hterm : ∀ α β : Fin n, pd (fun y => gi y α β) ν x * (pd φ α x * pd φ β x)
          = -((∑ σ, christoffel g gi α ν σ x * gi x σ β) * (pd φ α x * pd φ β x))
            + -((∑ σ, christoffel g gi β ν σ x * gi x σ α) * (pd φ α x * pd φ β x)) := by
        intro α β
        rw [pd_gi_eq g gi α β ν x hsymm hsymm_gi hinv hg hgi]; ring
      rw [Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => hterm α β))]
      simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring
    rw [hR1, hQP, hPT2]; ring
  -- LHS = T1 − T2
  have hLHS : (∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * kgHess φ g gi ρ ν x))
      = (∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * pd (fun y => pd φ ν y) ρ x))
        - (∑ μ, ∑ ρ, gi x μ ρ * (pd φ μ x * ∑ σ, christoffel g gi σ ρ ν x * pd φ σ x)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    simp only [kgHess]; ring
  rw [pd_gradSq_eq φ gi ν x hgi hφ2, hLHS, hessGrad_partial_eq φ gi ν x hsymm_gi hφ,
    gradSq_cross_symm φ gi ν x hsymm_gi, hT2R1]
  ring

/-- **★★★★★ KLEIN–GORDON STRESS-TENSOR CONSERVATION, DISCHARGED — `∇^μ T_{μν} = 0` for the explicit free KG
    field, axiom-free, modulo ONLY the equation of motion.**  The Hessian-gradient identity (`hHessGrad`) is now
    supplied internally by `hHessGrad_eq` (built from inverse-metric compatibility `pd_gi_eq` + the gradient
    expansion + the symmetry lemmas), so the only remaining hypothesis is `hKG : □φ = m²φ` — the matter equation
    of motion, genuine physics.  Everything geometric is machine-checked.  This DISCHARGES the `conserv` input of
    the free-field QIQT→GR surface for the explicit Klein–Gordon stress tensor: `conserv = a · (this) = 0`. -/
theorem div02_kgStress_conserved_of_KG (m : ℝ) (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (x : Point n) (ν : Fin n)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hKin : ∀ a b ρ, PdiffAt (fun y => kgKinetic φ y a b) ρ x)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (hgi : ∀ a b ρ, PdiffAt (fun y => gi y a b) ρ x)
    (hL : ∀ ρ, PdiffAt (kgLagr m φ gi) ρ x)
    (hφ2 : ∀ i j, PdiffAt (fun y => pd φ i y) j x) (hφd : PdiffAt φ ν x) (hφ : ContDiff ℝ ⊤ φ)
    (hgradSq : PdiffAt (fun y => ∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) ν x)
    (hKG : boxField φ g gi x = m ^ 2 * φ x) :
    div02 g gi (kgStress m φ g gi) ν x = 0 :=
  div02_kgStress_conserved m φ g gi x ν hsymm hinv hKin hg hL hφ2 hφd hgradSq hKG
    (hHessGrad_eq φ g gi ν x hsymm hsymm_gi hinv hg hgi hφ2 hφ)

/-- **The raised divergence scales out a constant** `∇^μ(a·X)_{μν} = a·∇^μ X_{μν}` (the connection and metric
    are linear, `a` is constant — `pd_const_mul` + `Finset.mul_sum`).  This is what carries the Einstein
    coupling `a` through the conservation law `∇·(a·T) = a·∇·T`. -/
theorem div02_const_smul (g gi : Point n → Fin n → Fin n → ℝ) (a : ℝ)
    (X : Point n → Fin n → Fin n → ℝ) (ν : Fin n) (x : Point n)
    (hX : ∀ b c ρ, PdiffAt (fun y => X y b c) ρ x) :
    div02 g gi (fun y b c => a * X y b c) ν x = a * div02 g gi X ν x := by
  have hcd : ∀ μ ρ : Fin n,
      covDeriv02 g gi (fun y b c => a * X y b c) ρ μ ν x = a * covDeriv02 g gi X ρ μ ν x := by
    intro μ ρ
    simp only [covDeriv02]
    rw [pd_const_mul a (fun y => X y μ ν) ρ x (hX μ ν ρ),
      show (∑ σ, christoffel g gi σ ρ μ x * (a * X x σ ν))
          = a * ∑ σ, christoffel g gi σ ρ μ x * X x σ ν from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun σ _ => by ring),
      show (∑ σ, christoffel g gi σ ρ ν x * (a * X x μ σ))
          = a * ∑ σ, christoffel g gi σ ρ ν x * X x μ σ from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun σ _ => by ring)]
    ring
  simp only [div02]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [hcd μ ρ]; ring

/-- **★★★★★★ THE `conserv` INPUT OF THE QIQT→GR DERIVATION, IN ITS EXACT FORM, DISCHARGED for the explicit KG
    field.**  `∇·(a·T) = 0` with `T = kgStress` (the free Klein–Gordon stress tensor): the Einstein-coupling
    constant `a` scales out (`div02_const_smul`) and the bare divergence vanishes
    (`div02_kgStress_conserved_of_KG`).  This is exactly the `conserv : ∀ x ν, div02 g gi (fun y a' b => a · T y a' b) ν x = 0`
    hypothesis consumed by `WedgeKMSToGR`/`qiqt_gr_from_wedge_kms_complete` — so the matter-conservation input is now
    a THEOREM for the explicit free scalar, modulo only the equation of motion `□φ = m²φ`. -/
theorem kg_conserv (a m : ℝ) (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (x : Point n) (ν : Fin n)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hKin : ∀ a b ρ, PdiffAt (fun y => kgKinetic φ y a b) ρ x)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (hgi : ∀ a b ρ, PdiffAt (fun y => gi y a b) ρ x)
    (hL : ∀ ρ, PdiffAt (kgLagr m φ gi) ρ x)
    (hφ2 : ∀ i j, PdiffAt (fun y => pd φ i y) j x) (hφd : PdiffAt φ ν x) (hφ : ContDiff ℝ ⊤ φ)
    (hgradSq : PdiffAt (fun y => ∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) ν x)
    (hkgS : ∀ b c ρ, PdiffAt (fun y => kgStress m φ g gi y b c) ρ x)
    (hKG : boxField φ g gi x = m ^ 2 * φ x) :
    div02 g gi (fun y b c => a * kgStress m φ g gi y b c) ν x = 0 := by
  rw [div02_const_smul g gi a (kgStress m φ g gi) ν x hkgS,
    div02_kgStress_conserved_of_KG m φ g gi x ν hsymm hsymm_gi hinv hKin hg hgi hL hφ2 hφd hφ hgradSq hKG,
    mul_zero]

/-- **★★★★★★ `conserv` FROM SMOOTHNESS ALONE — the clean drop-in.**  The same matter-conservation input
    `∇·(a·T) = 0` (`T = kgStress`), but with all the pointwise differentiability hypotheses *derived* from a
    single `ContDiff` assumption on the field `φ` and the metric components `g, gi`.  This is the form actually
    convenient to plug into `WedgeKMSToGR`/`qiqt_gr_from_wedge_kms_complete`: given a smooth free scalar on a
    smooth (symmetric, invertible) metric satisfying the Klein–Gordon equation `□φ = m²φ`, the explicit stress
    tensor is covariantly conserved. -/
theorem kg_conserv_of_contDiff (a m : ℝ) (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (x : Point n) (ν : Fin n)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hφ : ContDiff ℝ ⊤ φ)
    (hgC : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b)) (hgiC : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hKG : boxField φ g gi x = m ^ 2 * φ x) :
    div02 g gi (fun y b c => a * kgStress m φ g gi y b c) ν x = 0 := by
  have hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x :=
    fun a b ρ => PdiffAt_of_contDiff _ (hgC a b) ρ x
  have hgi : ∀ a b ρ, PdiffAt (fun y => gi y a b) ρ x :=
    fun a b ρ => PdiffAt_of_contDiff _ (hgiC a b) ρ x
  have hφ2 : ∀ i j, PdiffAt (fun y => pd φ i y) j x := fun i j => PdiffAt_pd φ hφ i j x
  have hgradSqAll : ∀ ρ, PdiffAt (fun y => ∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) ρ x := fun ρ =>
    PdiffAt_sum Finset.univ _ ρ x (fun α _ => PdiffAt_sum Finset.univ _ ρ x
      (fun β _ => (hgi α β ρ).mul ((hφ2 α ρ).mul (hφ2 β ρ))))
  have hL : ∀ ρ, PdiffAt (kgLagr m φ gi) ρ x := fun ρ => by
    rw [show (kgLagr m φ gi)
        = fun y => (∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) + m ^ 2 * (φ y) ^ 2 from by funext y; rfl]
    refine (hgradSqAll ρ).add ?_
    rw [show (fun y => m ^ 2 * (φ y) ^ 2) = fun y => m ^ 2 * (φ y * φ y) from by funext y; ring]
    exact (differentiableAt_const _).mul ((PdiffAt_of_contDiff φ hφ ρ x).mul (PdiffAt_of_contDiff φ hφ ρ x))
  have hKin : ∀ a b ρ, PdiffAt (fun y => kgKinetic φ y a b) ρ x :=
    fun a b ρ => (hφ2 a ρ).mul (hφ2 b ρ)
  have hkgS : ∀ b c ρ, PdiffAt (fun y => kgStress m φ g gi y b c) ρ x := fun b c ρ => by
    rw [show (fun y => kgStress m φ g gi y b c)
        = fun y => pd φ b y * pd φ c y - (1 / 2 : ℝ) * g y b c * kgLagr m φ gi y from by funext y; rfl]
    exact ((hφ2 b ρ).mul (hφ2 c ρ)).sub (((differentiableAt_const _).mul (hg b c ρ)).mul (hL ρ))
  exact kg_conserv a m φ g gi x ν hsymm hsymm_gi hinv hKin hg hgi hL hφ2
    (PdiffAt_of_contDiff φ hφ ν x) hφ (hgradSqAll ν) hkgS hKG

end QIQTH.Curvature
