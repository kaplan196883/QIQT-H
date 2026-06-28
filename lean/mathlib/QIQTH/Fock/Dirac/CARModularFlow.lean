/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E5 (continuum) — the CAR field-net modular flow `Γ₋(Δ^{it})`

The continuum wedge modular flow for the electron's CAR field net is the **fermionic second
quantization** of the one-particle modular flow `Δ^{it}`.  QIQT-H already has the one-particle continuum
`Δ^{it} = modUnitary S t` (`QIQTH/Fock/StandardSubspaceModularFlow.lean`, via the RvD bounded standard
subspace) and its **bosonic** second quantization `Γ(Δ^{it}) = secondQuantModFlow`
(`QIQTH/Fock/SecondQuantModularFlow.lean`).

This module builds the **fermionic** analog: the antisymmetric (CAR) Fock space is the exterior algebra
`⋀ H` (`QIQTH/Fock/Dirac/CAR.lean`), and the second quantization of a one-particle map is the induced
exterior-algebra map `Γ₋(U) = ExteriorAlgebra.map U`.  So the electron's continuum field-level modular
flow is `Γ₋(Δ^{it}) = ExteriorAlgebra.map (modUnitary S t)` — reusing the **same** one-particle `Δ^{it}`
(the modular flow is statistics-independent at the one-particle level; only the second-quantization
functor differs, symmetric ↦ antisymmetric).

Results (axiom-free): the one-particle action `Γ₋(Δ^{it})(ι f) = ι(Δ^{it} f)`, the identity
`Γ₋(Δ^{i·0}) = id`, and the **one-parameter group law** `Γ₋(Δ^{is}) ∘ Γ₋(Δ^{it}) = Γ₋(Δ^{i(s+t)})` (from
`modUnitary_add` + the functoriality of `ExteriorAlgebra.map`).  This is the continuum CAR-net modular
flow — the field-level `Δ_W^{it}` for the electron.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.

HONEST SCOPE: this builds the second-quantized modular *flow* (the field-level modular automorphism
group on the CAR Fock).  The fermionic modular *conjugation* `J_W = Z·Γ₋(j)` (the Klein twist `Z` of
`QIQTH/Fock/Dirac/KleinTwist*` composed with the second-quantized one-particle reflection) and the
twisted duality `𝓕(W)'=Z𝓕(W')Z*` are the remaining E5/E4 pieces.  The one-particle `Δ^{it}` itself
rides the `StandardSubspace`/Type-III₁ continuum frontier (`TOMITA_TAKESAKI_ROADMAP.md`).  Free Dirac
only.
-/
import QIQTH.StandardSubspaceModularFlow
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

namespace QIQTH.Fock.Dirac

open QIQTH.StandardSubspaceModular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`Γ₋(Δ^{it})`** — the fermionic (CAR) second quantization of the one-particle continuum modular flow
`Δ^{it} = modUnitary S t`, as the induced algebra map on the antisymmetric (exterior) Fock space `⋀ H`.
The electron's continuum field-level modular flow — the fermionic analog of the bosonic
`secondQuantModFlow`, reusing the same one-particle `Δ^{it}`. -/
noncomputable def fermiSecondQuantModFlow (S : StandardSubspace H) (t : ℝ) :
    ExteriorAlgebra ℂ H →ₐ[ℂ] ExteriorAlgebra ℂ H :=
  ExteriorAlgebra.map (modUnitary S t).toLinearMap

/-- **One-particle action**: `Γ₋(Δ^{it})(ι f) = ι(Δ^{it} f)` — the modular flow on a one-particle
state. -/
@[simp] theorem fermiSecondQuantModFlow_ι (S : StandardSubspace H) (t : ℝ) (f : H) :
    fermiSecondQuantModFlow S t (ExteriorAlgebra.ι ℂ f) = ExteriorAlgebra.ι ℂ (modUnitary S t f) := by
  unfold fermiSecondQuantModFlow
  rw [ExteriorAlgebra.map_apply_ι]; rfl

/-- **`Γ₋(Δ^{i·0}) = id`** — at `t = 0` the modular flow is the identity (and fixes the vacuum). -/
theorem fermiSecondQuantModFlow_zero (S : StandardSubspace H) :
    fermiSecondQuantModFlow S 0 = AlgHom.id ℂ (ExteriorAlgebra ℂ H) := by
  unfold fermiSecondQuantModFlow
  rw [show (modUnitary S 0).toLinearMap = LinearMap.id by
        ext x; show modUnitary S 0 x = x; rw [modUnitary_zero, ContinuousLinearMap.one_apply]]
  exact ExteriorAlgebra.map_id

/-- **The one-parameter group law** `Γ₋(Δ^{is}) ∘ Γ₋(Δ^{it}) = Γ₋(Δ^{i(s+t)})` — from the group law of
the one-particle modular flow (`modUnitary_add`) and the functoriality of the exterior-algebra second
quantization (`ExteriorAlgebra.map_comp_map`).  The genuine real-time modular flow `Δ^{it}` of the
electron CAR field net, as a one-parameter ℝ-action. -/
theorem fermiSecondQuantModFlow_add (S : StandardSubspace H) (s t : ℝ) :
    (fermiSecondQuantModFlow S s).comp (fermiSecondQuantModFlow S t)
      = fermiSecondQuantModFlow S (s + t) := by
  unfold fermiSecondQuantModFlow
  rw [ExteriorAlgebra.map_comp_map]
  congr 1
  ext x
  show modUnitary S s (modUnitary S t x) = modUnitary S (s + t) x
  rw [modUnitary_add]; rfl

end QIQTH.Fock.Dirac
