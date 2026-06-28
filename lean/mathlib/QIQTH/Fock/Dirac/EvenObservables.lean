/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E7/E8 (seed) — the even (Γ-fixed) observable algebra

Per the ELECTRON_FIELD_PLAN crux (§0): for the electron, **records and the capacity bound attach to the
EVEN / observable subalgebra**, not to the full graded field algebra.  Physical records and operations
must be **even** (parity-preserving); the classical/decoherent variables are **even bilinears** — the
charge current `j^μ = ψ̄γ^μψ`, the stress tensor `T_μν`, number/occupation, spin density — *not*
c-number field amplitudes (which is why the bosonic χ_R coherent-sector calculus does not transfer).

This module pins that down: the **even observables** are exactly the fixed points of the fermion parity
`Γ = (−1)^F` (`QIQTH/Fock/Dirac/Parity.lean`), and they form a genuine **subalgebra**
(`evenSubalgebra`).  The load-bearing physical fact is `isEven_ι_mul_ι`: a product of two one-particle
(odd) generators is even — so **fermion bilinears are Γ-fixed even observables**, while one-particle
states are odd (`Γ(ι m) = −ι m`).

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.

HONEST scope (ELECTRON_FIELD_PLAN §7,§8): this lands the even-observable subalgebra — the algebra to
which records/capacity attach.  The *graded regional* capacity (the block decomposition
`S(ρ_R) = H(p_q) + Σ_q p_q S(ρ_q)` over a charge/parity-graded regional algebra) and the even-observable
no-signaling re-derivation are the next E7/E8 sub-items.  Free Dirac only.
-/
import QIQTH.Fock.Dirac.Parity

namespace QIQTH.Fock.Dirac

open ExteriorAlgebra

variable {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]

/-- An observable is **even** (parity-invariant, `Γ`-eigenvalue `+1`) iff the fermion parity `Γ` fixes
it.  The even observables are the electron field's physical records (even bilinears `j^μ`, `T_μν`,
occupation), per ELECTRON_FIELD_PLAN §0. -/
def IsEven (a : ExteriorAlgebra 𝕜 M) : Prop := parity 𝕜 M a = a

/-- The vacuum (grade 0) is even. -/
theorem isEven_one : IsEven (1 : ExteriorAlgebra 𝕜 M) := map_one _

/-- `0` is even. -/
theorem isEven_zero : IsEven (0 : ExteriorAlgebra 𝕜 M) := map_zero _

/-- Even observables are closed under addition. -/
theorem isEven_add {a b : ExteriorAlgebra 𝕜 M} (ha : IsEven a) (hb : IsEven b) : IsEven (a + b) := by
  unfold IsEven at ha hb ⊢; rw [map_add, ha, hb]

/-- Even observables are closed under multiplication (even · even = even). -/
theorem isEven_mul {a b : ExteriorAlgebra 𝕜 M} (ha : IsEven a) (hb : IsEven b) : IsEven (a * b) := by
  unfold IsEven at ha hb ⊢; rw [map_mul, ha, hb]

/-- Even observables are closed under `𝕜`-scaling. -/
theorem isEven_smul (c : 𝕜) {a : ExteriorAlgebra 𝕜 M} (ha : IsEven a) : IsEven (c • a) := by
  unfold IsEven at ha ⊢; rw [map_smul, ha]

/-- Scalars (the image of `algebraMap`) are even. -/
theorem isEven_algebraMap (c : 𝕜) : IsEven (algebraMap 𝕜 (ExteriorAlgebra 𝕜 M) c) :=
  AlgHom.commutes _ _

/-- **The key physical fact: a product of two one-particle (odd) generators is EVEN.**  Hence fermion
bilinears `ψ̄ψ, j^μ = ψ̄γ^μψ, T_μν` — the electron field's records — are `Γ`-fixed even observables. -/
theorem isEven_ι_mul_ι (m m' : M) : IsEven (ι 𝕜 m * ι 𝕜 m') := by
  simp only [IsEven, map_mul, parity_ι, neg_mul_neg]

/-- One-particle states are **odd** (anti-fixed): `Γ(ι m) = −ι m`.  So a single fermion is not an even
observable (not a record) unless it vanishes. -/
theorem parity_one_particle (m : M) : parity 𝕜 M (ι 𝕜 m) = - ι 𝕜 m := parity_ι m

/-- **The even / observable subalgebra** — the `Γ`-fixed points of the CAR field algebra.  This is the
algebra to which (per ELECTRON_FIELD_PLAN §0) the electron's records and the regional capacity bound
attach.  Closed under `+`, `*`, contains the scalars; the bilinear records `ι m * ι m'` live here. -/
def evenSubalgebra (𝕜 : Type*) (M : Type*) [Field 𝕜] [AddCommGroup M] [Module 𝕜 M] :
    Subalgebra 𝕜 (ExteriorAlgebra 𝕜 M) where
  carrier := {a | IsEven a}
  mul_mem' ha hb := isEven_mul ha hb
  one_mem' := isEven_one
  add_mem' ha hb := isEven_add ha hb
  zero_mem' := isEven_zero
  algebraMap_mem' := isEven_algebraMap

@[simp] theorem mem_evenSubalgebra {a : ExteriorAlgebra 𝕜 M} :
    a ∈ evenSubalgebra 𝕜 M ↔ IsEven a := Iff.rfl

/-! ### E8 seed — even records commute with field operators (the no-signaling kernel)

The one-particle (odd) generators **anticommute**, `ι a · ι b = − ι b · ι a`; consequently a fermion
**bilinear** `ι a · ι b` (an even observable / record) **commutes** with every one-particle field
operator `ι c`.  This is the algebraic kernel of even-observable no-signaling: the electron's records,
being even bilinears, commute with the (odd) field operators — so measuring a record cannot signal
through the field algebra.  (The full bipartite statement uses the graded tensor product across
spacelike-separated regions; this is the single-algebra generator-level core.) -/

/-- The one-particle (odd) generators **anticommute**: `ι a · ι b = − (ι b · ι a)`.  (From
`ι v · ι v = 0` applied to `a + b`.) -/
theorem ι_mul_ι_swap (a b : M) : ι 𝕜 a * ι 𝕜 b = - (ι 𝕜 b * ι 𝕜 a) := by
  have h := ExteriorAlgebra.ι_sq_zero (R := 𝕜) (a + b)
  rw [map_add, add_mul, mul_add, mul_add, ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero,
      zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **An even bilinear record commutes with a field operator.**  `(ι a · ι b) · ι c = ι c · (ι a · ι b)`:
the fermion bilinear (an even observable / record, `isEven_ι_mul_ι`) commutes with the one-particle
field operator `ι c`.  Proof = two applications of the generator anticommutation.  The no-signaling
kernel for the electron's even records. -/
theorem ι_mul_ι_comm_ι (a b c : M) :
    (ι 𝕜 a * ι 𝕜 b) * ι 𝕜 c = ι 𝕜 c * (ι 𝕜 a * ι 𝕜 b) := by
  rw [mul_assoc, ι_mul_ι_swap b c, mul_neg, ← mul_assoc, ι_mul_ι_swap a c, neg_mul, neg_neg, mul_assoc]

/-- **Two even bilinear records commute.**  `(ι a · ι b) · (ι c · ι d) = (ι c · ι d) · (ι a · ι b)`:
fermion bilinears — the electron's even records (`j^μ`, `T_μν`) — pairwise commute.  Commuting
observables are jointly measurable and cannot signal between one another, so this is the no-signaling
statement for the even records themselves (a step beyond `ι_mul_ι_comm_ι`).  Proof = the bilinear
commutes with each generator (`ι_mul_ι_comm_ι`), moved through twice. -/
theorem evenBilinear_comm (a b c d : M) :
    (ι 𝕜 a * ι 𝕜 b) * (ι 𝕜 c * ι 𝕜 d) = (ι 𝕜 c * ι 𝕜 d) * (ι 𝕜 a * ι 𝕜 b) := by
  rw [← mul_assoc, ι_mul_ι_comm_ι a b c, mul_assoc, ι_mul_ι_comm_ι a b d, ← mul_assoc]

end QIQTH.Fock.Dirac
