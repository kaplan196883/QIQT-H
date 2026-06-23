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

/-- The KG **Lagrangian scalar** `L = g^{αβ} ∂_α φ ∂_β φ − m² φ²`. -/
noncomputable def kgLagr (m : ℝ) (φ : Point n → ℝ) (gi : Point n → Fin n → Fin n → ℝ)
    (y : Point n) : ℝ :=
  (∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) - m ^ 2 * (φ y) ^ 2

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

end QIQTH.Curvature
