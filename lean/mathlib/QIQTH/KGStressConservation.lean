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

end QIQTH.Curvature
