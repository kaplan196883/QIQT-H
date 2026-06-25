/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Type II crossed product, Increment 1a-0 — the modular automorphism `σ_t`

Toward the crossed-product Type II construction `M ⋊_σ ℝ` (see `CROSSED_PRODUCT_TYPE_II_SCOPE.md`), the action
being crossed is the **modular automorphism group** `σ_t(a) = Δ^{it} a Δ^{-it}`.  The project has the modular
*unitary* flow `modUnitary S t = Δ^{it}` (a strongly-continuous one-parameter unitary group); this file promotes
it to the **automorphism of bounded operators** it induces, and proves it is a one-parameter group of unital
`*`-algebra homomorphisms — the concrete `σ_t` the crossed product is built from.

This is the action-side foundation of `M ⋊_σ ℝ`.  The crossed-product Hilbert space `L²(ℝ; H)` and the
covariant representation (`π(a)ξ(s) = σ_{-s}(a)(ξ s)`, translations `λ_t`, covariance `λ_t π(a) λ_{-t} =
π(σ_t a)`) are the next sub-increment (the Bochner-space plumbing).  Axiom-free.
-/
import QIQTH.StandardSubspaceModularFlow

namespace QIQTH.StandardSubspaceModular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The modular automorphism** `σ_t(a) = Δ^{it} a Δ^{-it}` on bounded operators, built from the modular
    unitary flow `modUnitary S t`.  This is the ℝ-action the crossed product `M ⋊_σ ℝ` is formed by. -/
noncomputable def modularAut (S : StandardSubspace H) (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  modUnitary S t * a * modUnitary S (-t)

/-- `σ_0 = id`. -/
theorem modularAut_zero (S : StandardSubspace H) (a : H →L[ℂ] H) : modularAut S 0 a = a := by
  simp only [modularAut, neg_zero, modUnitary_zero, one_mul, mul_one]

/-- `σ_t(1) = 1` (unital). -/
theorem modularAut_one (S : StandardSubspace H) (t : ℝ) : modularAut S t (1 : H →L[ℂ] H) = 1 := by
  rw [modularAut, mul_one, ← modUnitary_add, add_neg_cancel, modUnitary_zero]

/-- `σ_t(a·b) = σ_t(a)·σ_t(b)` (multiplicative): conjugation by the unitary `Δ^{it}`. -/
theorem modularAut_mul (S : StandardSubspace H) (t : ℝ) (a b : H →L[ℂ] H) :
    modularAut S t (a * b) = modularAut S t a * modularAut S t b := by
  have h1 : modUnitary S (-t) * modUnitary S t = 1 := by
    rw [← modUnitary_add, neg_add_cancel, modUnitary_zero]
  simp only [modularAut]
  calc modUnitary S t * (a * b) * modUnitary S (-t)
      = modUnitary S t * a * (modUnitary S (-t) * modUnitary S t) * b * modUnitary S (-t) := by
        rw [h1]; noncomm_ring
    _ = modUnitary S t * a * modUnitary S (-t) * (modUnitary S t * b * modUnitary S (-t)) := by
        noncomm_ring

/-- **The one-parameter group law** `σ_{s+t} = σ_s ∘ σ_t` (cocycle): the modular automorphism is an ℝ-action. -/
theorem modularAut_add (S : StandardSubspace H) (s t : ℝ) (a : H →L[ℂ] H) :
    modularAut S (s + t) a = modularAut S s (modularAut S t a) := by
  simp only [modularAut]
  rw [modUnitary_add, show -(s + t) = (-t) + (-s) by ring, modUnitary_add]
  noncomm_ring

/-- `σ_t` preserves adjoints (`*`-preserving): together with `modularAut_mul`/`_one` it is a unital
    `*`-homomorphism, and with `modularAut_add` a one-parameter group of `*`-automorphisms. -/
theorem modularAut_star (S : StandardSubspace H) (t : ℝ) (a : H →L[ℂ] H) :
    star (modularAut S t a) = modularAut S t (star a) := by
  simp only [modularAut, star_mul, ContinuousLinearMap.star_eq_adjoint, modUnitary_adjoint, neg_neg]
  noncomm_ring

end QIQTH.StandardSubspaceModular
