/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E5 — the field-level Klein twist `Z` on the full CAR Fock (operator form)

The single-mode Klein twist `Z = (1 + iΓ)/(1 + i)` was witnessed on the `2×2` fermion parity
`diag(1,−1)` (`QIQTH/Fock/Dirac/KleinTwistWitness.lean`).  This module lifts it to the **field level**:
the twisted-duality intertwiner `Z` as an actual **operator** (`Module.End ℂ`) on the *full* CAR Fock
space `⋀ V`, built from the **field-level fermion parity** `Γ = (−1)^F = ExteriorAlgebra.map(−id)` (the
grade involution `QIQTH/Fock/Dirac/Parity.lean`, `parity`).

Since `Module.End ℂ (⋀ V)` is a `ℂ`-algebra and the field parity `Γ` is a self-adjoint *involution*
(`Γ² = 1`, from `parity_parity`), the abstract Klein-twist algebra (`QIQTH/Fock/Dirac/KleinTwist*.lean`)
**instantiates** directly on it: `Z² = Γ`, `Z⁴ = 1`, `[Z, Γ] = 0` — the field-level twisted-duality
intertwiner, now an operator on the full CAR Fock (not just the single mode).

HONEST scope (E5 frontier): this is the *algebraic* operator `Z` and its algebra on the full Fock.  The
**unitarity** `Z*Z = 1` needs the Fock-space inner product / adjoint (`star` on `Module.End`), which the
*algebraic* exterior algebra does not carry — that, plus the operator-algebra twisted-duality *theorem*
`𝓕(W)' = Z𝓕(W')Z*`, remain the deferred GNS/operator-algebra frontier.  Axiom-free (standard
`propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Dirac only.
-/
import QIQTH.Fock.Dirac.KleinTwist
import QIQTH.Fock.Dirac.Parity

namespace QIQTH.Fock.Dirac

open ExteriorAlgebra

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- **The field-level fermion parity `Γ = (−1)^F`** as an operator on the full CAR Fock `⋀ V` — the grade
involution `parity` viewed as a `Module.End ℂ (⋀ V)`. -/
noncomputable def fockParity : Module.End ℂ (ExteriorAlgebra ℂ V) := (parity ℂ V).toLinearMap

/-- `Γ` is an **involution**: `Γ² = 1` on the full CAR Fock (from `parity_parity`). -/
theorem fockParity_involutive : fockParity V * fockParity V = 1 := by
  refine LinearMap.ext fun x => ?_
  exact parity_parity x

/-- **The field-level Klein twist `Z = (1 + iΓ)/(1 + i)`** as an operator on the full CAR Fock — the
abstract `kleinTwist` instantiated on `Module.End ℂ (⋀ V)` with `γ = Γ` (the field parity). -/
noncomputable def fockKleinTwist : Module.End ℂ (ExteriorAlgebra ℂ V) := kleinTwist (fockParity V)

/-- **`Z² = Γ`** on the full CAR Fock (instantiating `kleinTwist_sq`). -/
theorem fockKleinTwist_sq : fockKleinTwist V * fockKleinTwist V = fockParity V :=
  kleinTwist_sq (fockParity_involutive V)

/-- **`Z⁴ = 1`** on the full CAR Fock — `Z` is a (field-level) operator of order 4. -/
theorem fockKleinTwist_order4 :
    (fockKleinTwist V * fockKleinTwist V) * (fockKleinTwist V * fockKleinTwist V) = 1 :=
  kleinTwist_sq_sq (fockParity_involutive V)

/-- **`[Z, Γ] = 0`** on the full CAR Fock — the field-level Klein twist commutes with the parity grading,
so the twisted duality `𝓕(W)'=Z𝓕(W')Z*` does not mix the even/odd sectors (records stay even). -/
theorem fockKleinTwist_comm_parity :
    fockKleinTwist V * fockParity V = fockParity V * fockKleinTwist V :=
  kleinTwist_comm_gamma (fockParity V)

end QIQTH.Fock.Dirac
