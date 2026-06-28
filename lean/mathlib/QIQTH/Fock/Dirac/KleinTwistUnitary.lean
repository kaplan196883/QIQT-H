/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E4 (crux, completion) — the Klein twist is UNITARY: `Z* Z = 1`

The Klein twist `Z = (1 + iΓ)/(1 + i)` (`QIQTH/Fock/Dirac/KleinTwist.lean`) implements the twisted
modular duality `𝓕(W)' = Z 𝓕(W') Z*` for the electron.  For that to be a genuine *intertwiner* `Z` must
be **unitary**.  This module proves it: for any **self-adjoint** involution `γ` (`star γ = γ`,
`γ·γ = 1`) in a `ℂ`-`*`-algebra, the Klein twist satisfies
```
   Z* Z = 1.
```
Together with `kleinTwist_sq : Z² = γ` (KleinTwist.lean) this makes `Z` a unitary of order 4 (a unitary
fourth root of the parity `Γ`) — the operator the twisted duality requires.

Proof = the same expansion as `kleinTwist_sq`, with the conjugate scalars `ᾱ, β̄` on the left factor,
collapsing via `γ·γ = 1` and the two conjugate-scalar identities
`ᾱα + β̄β = 1` and `ᾱβ + β̄α = 0` (with `α = (1+i)⁻¹`, `β = i(1+i)⁻¹`).

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.

HONEST scope (ELECTRON_FIELD_PLAN §0): this completes the Klein-twist ALGEBRA (`Z²=Γ`, `Z⁴=1`, `Z*Z=1`).
The operator-algebra twisted-duality theorem `𝓕(W)'=Z𝓕(W')Z*` itself + the instantiation of `γ` as the
second-quantized parity unitary on the CAR inner-product space remain E5 (the GNS/operator-algebra
frontier).  Free Dirac only.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Tactic.NoncommRing
import QIQTH.Fock.Dirac.KleinTwist

namespace QIQTH.Fock.Dirac

open Complex

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- **The Klein twist is unitary: `Z* Z = 1`** for a self-adjoint involution `γ` in a ℂ-*-algebra. -/
theorem kleinTwist_star_mul_self {γ : A} (hsa : star γ = γ) (hγ : γ * γ = 1) :
    star (kleinTwist γ) * kleinTwist γ = 1 := by
  have hsI : star (I : ℂ) = -I := by
    rw [show star (I : ℂ) = (starRingEnd ℂ) I from rfl, Complex.conj_I]
  have ha : star ((1 + I)⁻¹) = (1 - I)⁻¹ := by
    rw [star_inv₀]; congr 1; rw [star_add, star_one, hsI]; ring
  have hb : star (I * (1 + I)⁻¹) = -I * (1 - I)⁻¹ := by
    rw [star_mul', hsI, ha]
  have h2 : (1 - I) * (1 + I) = 2 := by
    rw [show (1 - I) * (1 + I) = 1 - I ^ 2 from by ring, I_sq]; ring
  have hprod : (1 - I)⁻¹ * (1 + I)⁻¹ = 2⁻¹ := by rw [← mul_inv, h2]
  -- conjugate-scalar identities
  have s1 : star ((1 + I)⁻¹) * (1 + I)⁻¹ + star (I * (1 + I)⁻¹) * (I * (1 + I)⁻¹) = 1 := by
    rw [ha, hb,
        show (-I * (1 - I)⁻¹) * (I * (1 + I)⁻¹) = (-(I * I)) * ((1 - I)⁻¹ * (1 + I)⁻¹) from by ring,
        Complex.I_mul_I, hprod]
    norm_num
  have s2 : star ((1 + I)⁻¹) * (I * (1 + I)⁻¹) + star (I * (1 + I)⁻¹) * (1 + I)⁻¹ = 0 := by
    rw [ha, hb]; ring
  -- star Z in distributed conjugate form
  have hstarZ : star (kleinTwist γ)
      = algebraMap ℂ A (star ((1 + I)⁻¹)) + algebraMap ℂ A (star (I * (1 + I)⁻¹)) * γ := by
    rw [kleinTwist, star_add, star_mul, hsa,
        (algebraMap_star_comm ((1 + I)⁻¹)).symm, (algebraMap_star_comm (I * (1 + I)⁻¹)).symm,
        ← Algebra.commutes (star (I * (1 + I)⁻¹)) γ]
  rw [hstarZ, kleinTwist]
  set pb := algebraMap ℂ A (star ((1 + I)⁻¹)) with hpb
  set qb := algebraMap ℂ A (star (I * (1 + I)⁻¹)) with hqb
  set p := algebraMap ℂ A ((1 + I)⁻¹) with hp
  set q := algebraMap ℂ A (I * (1 + I)⁻¹) with hq
  have hpγ : p * γ = γ * p := Algebra.commutes _ _
  have hqγ : q * γ = γ * q := Algebra.commutes _ _
  have t2 : pb * (q * γ) = (pb * q) * γ := (mul_assoc pb q γ).symm
  have t3 : (qb * γ) * p = (qb * p) * γ := by rw [mul_assoc, ← hpγ, ← mul_assoc]
  have t4 : (qb * γ) * (q * γ) = (qb * q) * (γ * γ) := by
    rw [mul_assoc, ← mul_assoc γ q γ, ← hqγ, mul_assoc q γ γ, ← mul_assoc qb q (γ * γ)]
  have hpbp : pb * p = algebraMap ℂ A (star ((1 + I)⁻¹) * (1 + I)⁻¹) := by rw [hpb, hp, ← map_mul]
  have hqbq : qb * q = algebraMap ℂ A (star (I * (1 + I)⁻¹) * (I * (1 + I)⁻¹)) := by
    rw [hqb, hq, ← map_mul]
  have hpbq : pb * q = algebraMap ℂ A (star ((1 + I)⁻¹) * (I * (1 + I)⁻¹)) := by rw [hpb, hq, ← map_mul]
  have hqbp : qb * p = algebraMap ℂ A (star (I * (1 + I)⁻¹) * (1 + I)⁻¹) := by rw [hqb, hp, ← map_mul]
  have hS1 : algebraMap ℂ A (star ((1 + I)⁻¹) * (1 + I)⁻¹)
      + algebraMap ℂ A (star (I * (1 + I)⁻¹) * (I * (1 + I)⁻¹)) = 1 := by
    rw [← map_add, s1, map_one]
  have hS2 : algebraMap ℂ A (star ((1 + I)⁻¹) * (I * (1 + I)⁻¹))
      + algebraMap ℂ A (star (I * (1 + I)⁻¹) * (1 + I)⁻¹) = 0 := by
    rw [← map_add, s2, map_zero]
  have rearr : ∀ a b d₁ d₂ : A, a + d₁ * γ + (d₂ * γ + b) = (a + b) + (d₁ + d₂) * γ := by
    intro a b d₁ d₂; noncomm_ring
  rw [add_mul, mul_add, mul_add, t2, t3, t4, hγ, mul_one, hpbp, hpbq, hqbp, hqbq, rearr,
      hS1, hS2, zero_mul, add_zero]

end QIQTH.Fock.Dirac
