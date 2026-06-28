/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E4 (the crux) — the Klein twist `Z = (1 + iΓ)/(1 + i)`

The conceptual crux of putting the electron into QIQT-H (per GPT-5.5-pro, ELECTRON_FIELD_PLAN §0) is
NOT a fermionic sign on the boost — the Rindler modular flow stays the geometric boost — but the
**Z₂-graded locality + twisted modular duality** of the free Dirac field:
```
   𝓕(W)' = Z 𝓕(W') Z*,        Z = (1 + i Γ)/(1 + i),     Γ = (−1)^F.
```
`Z` is the **Klein twist** built from the fermion parity `Γ` (`QIQTH/Fock/Dirac/Parity.lean`).  This
module formalizes the defining ALGEBRAIC identity of the Klein twist, the property the twisted-duality
formula rests on:
```
   Z² = Γ          (hence  Z⁴ = Γ² = 1).
```
That `Z` squares to the parity is exactly why `Z` interpolates between a field net and its true
(Klein-twisted) commutant: applying the duality twice returns `Γ`-conjugation.  Proved here abstractly
for ANY involution `γ` (`γ·γ = 1`) in a ℂ-algebra `A` — the form that instantiates with `γ` = the
second-quantized parity unitary.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.

HONEST scope (ELECTRON_FIELD_PLAN §0,§2): this lands the Klein-twist algebra `Z² = Γ`, `Z⁴ = 1`.  Two
sub-items are CHECKPOINTED (left to the next increments, not blocked):
 - **Z unitary** `Z* Z = 1` — needs a `StarRing` structure with `γ` self-adjoint (`star γ = γ`);
 - the **twisted-duality statement** `𝓕(W)' = Z 𝓕(W') Z*` as an operator-algebra/commutant theorem —
   needs the CAR field net + commutants (E5), a genuine operator-algebra frontier.
The instantiation of `γ` as the second-quantized parity unitary `u_Γ` on the CAR Fock inner-product
space is also E5 (it needs the inner product / GNS, which the bosonic χ_R calculus does NOT supply).
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.NoncommRing
import QIQTH.Fock.Dirac.Parity

namespace QIQTH.Fock.Dirac

open Complex

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The **Klein twist** `Z = (1 + iγ)/(1 + i)` of an involution `γ` in a ℂ-algebra, written with the
scalar `(1+i)⁻¹` distributed: `Z = c·1 + (i·c)·γ` with `c = (1+i)⁻¹`.  For `γ = Γ = (−1)^F` this is the
operator whose twisted duality `𝓕(W)' = Z 𝓕(W') Z*` is the AQFT form of spin–statistics for the
electron. -/
noncomputable def kleinTwist (γ : A) : A :=
  algebraMap ℂ A ((1 + I)⁻¹) + algebraMap ℂ A (I * (1 + I)⁻¹) * γ

/-- **The defining identity of the Klein twist: `Z² = γ`.**  For any involution `γ` (`γ·γ = 1`) in a
ℂ-algebra, the Klein twist squares to `γ`.  (For `γ = Γ`, `Z² = Γ`: applying the twisted duality twice
is parity conjugation.)  Proof = expand, push the central scalars through `γ`, collapse `γ·γ = 1`, and
use the two scalar identities `α² + β² = 0` and `2αβ = 1` with `α = (1+i)⁻¹`, `β = i(1+i)⁻¹`. -/
theorem kleinTwist_sq {γ : A} (hγ : γ * γ = 1) : kleinTwist γ * kleinTwist γ = γ := by
  -- scalar identity 1:  α² + β² = 0  (β = iα ⇒ β² = −α²)
  have e1 : ((1 + I)⁻¹) ^ 2 + (I * (1 + I)⁻¹) ^ 2 = 0 := by
    have h : (I * (1 + I)⁻¹) ^ 2 = -((1 + I)⁻¹) ^ 2 := by rw [mul_pow, I_sq]; ring
    rw [h]; ring
  -- `1 + I ≠ 0`
  have hne : (1 + I) ≠ 0 := by
    have him : (1 + I).im = 1 := by simp
    intro h; rw [h] at him; simp at him
  -- `(1+I)² = 2I`
  have hsq : (1 + I) * (1 + I) = 2 * I := by
    rw [show (1 + I) * (1 + I) = 1 + 2 * I + I ^ 2 from by ring, I_sq]; ring
  -- scalar identity 2:  αβ + αβ = 1  (= 2αβ, and αβ = i/(1+i)² = i/2i = 1/2)
  have e2 : (1 + I)⁻¹ * (I * (1 + I)⁻¹) + (1 + I)⁻¹ * (I * (1 + I)⁻¹) = 1 := by
    have key : (1 + I)⁻¹ * (I * (1 + I)⁻¹) = I * ((1 + I) * (1 + I))⁻¹ := by
      rw [mul_inv]; ring
    rw [key, hsq,
        show I * (2 * I)⁻¹ + I * (2 * I)⁻¹ = (2 : ℂ) * (I * (2 * I)⁻¹) from by ring,
        show (2 : ℂ) * (I * (2 * I)⁻¹) = (2 * I) * (2 * I)⁻¹ from by ring]
    exact mul_inv_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero)
  -- expand the product
  simp only [kleinTwist]
  set p := algebraMap ℂ A ((1 + I)⁻¹) with hp
  set q := algebraMap ℂ A (I * (1 + I)⁻¹) with hq
  have hpγ : p * γ = γ * p := Algebra.commutes _ _
  have t2 : p * (q * γ) = (p * q) * γ := (mul_assoc p q γ).symm
  have t3 : (q * γ) * p = (q * p) * γ := by rw [mul_assoc, ← hpγ, ← mul_assoc]
  have hqγ : q * γ = γ * q := Algebra.commutes _ _
  have t4 : (q * γ) * (q * γ) = (q * q) * (γ * γ) := by
    rw [mul_assoc, ← mul_assoc γ q γ, ← hqγ, mul_assoc q γ γ, ← mul_assoc q q (γ * γ)]
  have hpp : p * p = algebraMap ℂ A (((1 + I)⁻¹) ^ 2) := by rw [hp, ← map_mul, ← sq]
  have hqq : q * q = algebraMap ℂ A ((I * (1 + I)⁻¹) ^ 2) := by rw [hq, ← map_mul, ← sq]
  have hpq : p * q = algebraMap ℂ A ((1 + I)⁻¹ * (I * (1 + I)⁻¹)) := by rw [hp, hq, ← map_mul]
  have hqp : q * p = algebraMap ℂ A ((1 + I)⁻¹ * (I * (1 + I)⁻¹)) := by
    rw [hq, hp, ← map_mul]; congr 1; ring
  have hα2sum : algebraMap ℂ A (((1 + I)⁻¹) ^ 2) + algebraMap ℂ A ((I * (1 + I)⁻¹) ^ 2) = 0 := by
    rw [← map_add, e1, map_zero]
  have hαβsum : algebraMap ℂ A ((1 + I)⁻¹ * (I * (1 + I)⁻¹))
      + algebraMap ℂ A ((1 + I)⁻¹ * (I * (1 + I)⁻¹)) = 1 := by
    rw [← map_add, e2, map_one]
  have rearr : ∀ a b d : A, a + d * γ + (d * γ + b) = (a + b) + (d + d) * γ := by
    intro a b d; noncomm_ring
  rw [add_mul, mul_add, mul_add, t2, t3, t4, hγ, mul_one, hpp, hpq, hqp, hqq, rearr,
      hα2sum, hαβsum, one_mul, zero_add]

/-- **`Z⁴ = 1`.**  Immediate from `Z² = γ` and `γ·γ = 1`: the Klein twist has order 4 (it is a fourth
root of unity built from the parity involution). -/
theorem kleinTwist_sq_sq {γ : A} (hγ : γ * γ = 1) :
    (kleinTwist γ * kleinTwist γ) * (kleinTwist γ * kleinTwist γ) = 1 := by
  rw [kleinTwist_sq hγ, hγ]

end QIQTH.Fock.Dirac
