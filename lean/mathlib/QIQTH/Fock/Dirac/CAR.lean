/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E2 — the antisymmetric (CAR) Fock space and its dimension

The fermionic (electron) Fock space is the **antisymmetric** Fock space over the one-particle space —
i.e. the **exterior algebra** `⋀ M` (Mathlib `ExteriorAlgebra 𝕜 M`).  This is the CAR (canonical
ANTIcommutation relations) counterpart of the bosonic symmetric Fock space the rest of `QIQTH/Fock/`
is built on (`SecondQuant`, `Weyl*`, CCR).

The headline of this increment is the **Fock-space dimension**: for an `n`-mode region (one-particle
space `M` with `finrank 𝕜 M = n`),
```
   dim (⋀ M) = 2 ^ n.
```
Each fermionic mode is occupied or empty — a qubit — so an `n`-mode region has `2ⁿ` basis states.
This turns the bare `2ⁿ` appearing in the E3 capacity bound (`QuasiFreeEntropy.lean`,
`fermionicGaussianEntropy_le_log_dim : S ≤ log (2ⁿ)`) into the **literal dimension of the CAR Fock
space** `N_R = dim(⋀ h_R)`, closing the loop: the quasi-free entropy of a region is bounded by the log
of the dimension of that region's fermionic Fock space — the fermionic `S_vN ≤ log N_R`.

Built directly on Mathlib's `Module.Basis.ExteriorAlgebra : Basis (Finset I) 𝕜 (ExteriorAlgebra 𝕜 M)`
(the exterior algebra over a module with basis indexed by `I` has a basis indexed by `Finset I`), plus
`Fintype.card_finset : card (Finset I) = 2 ^ card I`.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.

HONEST scope (ELECTRON_FIELD_PLAN §0,§2): this increment formalizes the antisymmetric-Fock *dimension*
(the capacity-relevant fact).  The full CAR operator algebra — creation/annihilation `a(f), a†(g)` with
`{a(f),a†(g)} = ⟪f,g⟫`, `{a(f),a(g)} = 0`, and the parity operator `Γ = (−1)^F` as the `ℤ₂`-grading
`⋀ M = (⋀ M)_even ⊕ (⋀ M)_odd` — is the next E2 sub-item (the grading instance
`DirectSum.Decomposition (fun n ↦ ⋀[𝕜]^n M)` already exists in Mathlib and is the seed for `Γ`).  The
twisted modular duality that USES `Γ` (the Klein twist `Z`) is E4, the conceptual crux.
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fintype.Card
import QIQTH.Fock.Dirac.QuasiFreeEntropy

namespace QIQTH.Fock.Dirac

open scoped BigOperators

variable {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]

/-- The antisymmetric (fermionic / CAR) Fock space over a one-particle space `M` is the exterior
algebra `⋀ M`.  The CAR counterpart of the bosonic symmetric Fock space. -/
abbrev CARFock (𝕜 : Type*) (M : Type*) [Field 𝕜] [AddCommGroup M] [Module 𝕜 M] : Type _ :=
  ExteriorAlgebra 𝕜 M

/-- **The CAR Fock-space dimension is `2ⁿ`.**  For an `n`-mode region (one-particle space with a basis
indexed by a finite `I`, `card I = n`), the antisymmetric Fock space `⋀ M` has dimension `2ⁿ`: each mode
is empty or occupied (a qubit).  Proof = Mathlib's exterior-algebra basis indexed by `Finset I`, whose
cardinality is `2 ^ card I`. -/
theorem finrank_CARFock {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] (b : Module.Basis I 𝕜 M) :
    Module.finrank 𝕜 (CARFock 𝕜 M) = 2 ^ (Module.finrank 𝕜 M) := by
  rw [Module.finrank_eq_card_basis b.ExteriorAlgebra, Fintype.card_finset,
      Module.finrank_eq_card_basis b]

/-- **The CAR capacity bound, with `N_R` the literal Fock-space dimension.**  Combining E3
(`fermionicGaussianEntropy_le_log_dim`) with the Fock dimension `dim(⋀ h_R) = 2ⁿ`: the von Neumann
entropy of a quasi-free fermionic state on an `n`-mode region is bounded by the logarithm of the
dimension of that region's antisymmetric (CAR) Fock space.  This is `S_vN ≤ log N_R` for the free Dirac
field, with `N_R = dim(CARFock 𝕜 h_R)`. -/
theorem fermionicGaussianEntropy_le_log_carFockDim {I : Type*} [Fintype I] [DecidableEq I]
    [LinearOrder I] (b : Module.Basis I 𝕜 M) {c : I → ℝ} (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) :
    fermionicGaussianEntropy c ≤ Real.log ((Module.finrank 𝕜 (CARFock 𝕜 M) : ℝ)) := by
  have hdim : (Module.finrank 𝕜 (CARFock 𝕜 M) : ℝ) = (2 : ℝ) ^ (Fintype.card I) := by
    rw [finrank_CARFock b, Module.finrank_eq_card_basis b]; push_cast; ring
  rw [hdim]
  exact fermionicGaussianEntropy_le_log_dim hc0 hc1

end QIQTH.Fock.Dirac
