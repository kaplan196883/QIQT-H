/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E2/E4-seed — the fermion parity operator `Γ = (−1)^F`

The fermion **parity operator** `Γ = (−1)^F` is the grade involution on the CAR Fock space `⋀ M`: the
algebra automorphism that negates every one-particle (odd) generator,
```
   Γ (ι m) = − ι m,        Γ ∘ Γ = id,        Γ 1 = 1.
```
It acts as `+1` on the even sector (vacuum, two-particle, …) and `−1` on the odd sector (one-particle,
three-particle, …) — the **ℤ₂ grading** of the fermionic field algebra.  This is the seed of the
ELECTRON_FIELD_PLAN crux (E4): the **Klein twist** `Z = (1 + iΓ)/(1 + i)` is built from `Γ`, and the
twisted modular duality `𝓕(W)' = Z 𝓕(W') Z*` is the AQFT form of spin–statistics for the electron.
`Γ` is also what singles out the **even / observable** subalgebra to which (per ELECTRON_FIELD_PLAN §0)
the regional records and the capacity bound attach.

Constructed directly via the exterior-algebra universal property (`ExteriorAlgebra.lift` of `−ι`), the
mirror of Mathlib's `CliffordAlgebra.involute`.  Axiom-free (standard
`propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.

HONEST scope: this lands `Γ` as a grade involution and its defining identities.  The explicit even/odd
**eigenspace decomposition** `⋀ M = (⋀ M)₊ ⊕ (⋀ M)₋` (the ±1 eigenspaces, = `⨁ₙ even ⋀ⁿ` ⊕ `⨁ₙ odd
⋀ⁿ`) and the Klein twist `Z` itself (which needs `𝕜 = ℂ` for `i`) are the next sub-items (E4).
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import QIQTH.Fock.Dirac.CAR

namespace QIQTH.Fock.Dirac

open ExteriorAlgebra

variable {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]

/-- The fermion parity operator `Γ = (−1)^F` on the CAR Fock space `⋀ M`: the grade involution negating
each one-particle generator (`Γ (ι m) = −ι m`).  Built as `lift (−ι)`, the exterior-algebra mirror of
`CliffordAlgebra.involute`. -/
def parity (𝕜 : Type*) (M : Type*) [Field 𝕜] [AddCommGroup M] [Module 𝕜 M] :
    ExteriorAlgebra 𝕜 M →ₐ[𝕜] ExteriorAlgebra 𝕜 M :=
  ExteriorAlgebra.lift 𝕜 ⟨-(ExteriorAlgebra.ι 𝕜),
    fun m => by rw [LinearMap.neg_apply, neg_mul_neg]; exact ExteriorAlgebra.ι_sq_zero m⟩

/-- `Γ` negates one-particle (odd) states: `Γ (ι m) = −ι m`. -/
@[simp] theorem parity_ι (m : M) : parity 𝕜 M (ι 𝕜 m) = - ι 𝕜 m := by
  simp [parity]

/-- The vacuum (grade 0) is even: `Γ 1 = 1` (eigenvalue `+1`). -/
@[simp] theorem parity_one : parity 𝕜 M 1 = 1 := map_one _

/-- `Γ ∘ Γ = id`: parity is an involution (`(−1)^F` squares to the identity). -/
theorem parity_comp_parity : (parity 𝕜 M).comp (parity 𝕜 M) = AlgHom.id 𝕜 _ := by
  ext m
  simp

/-- Parity is involutive: `Γ (Γ a) = a` for all `a`. -/
theorem parity_involutive : Function.Involutive (parity 𝕜 M) :=
  AlgHom.congr_fun parity_comp_parity

@[simp] theorem parity_parity (a : ExteriorAlgebra 𝕜 M) :
    parity 𝕜 M (parity 𝕜 M a) = a := parity_involutive a

/-- `Γ` as an algebra automorphism (`AlgEquiv`) — the form the Klein twist `Z` and the twisted duality
of E4 will consume. -/
def parityEquiv (𝕜 : Type*) (M : Type*) [Field 𝕜] [AddCommGroup M] [Module 𝕜 M] :
    ExteriorAlgebra 𝕜 M ≃ₐ[𝕜] ExteriorAlgebra 𝕜 M :=
  AlgEquiv.ofAlgHom (parity 𝕜 M) (parity 𝕜 M) parity_comp_parity parity_comp_parity

@[simp] theorem parityEquiv_apply (a : ExteriorAlgebra 𝕜 M) :
    parityEquiv 𝕜 M a = parity 𝕜 M a := rfl

end QIQTH.Fock.Dirac
