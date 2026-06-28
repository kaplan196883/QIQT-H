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
import QIQTH.Fock.Dirac.Parity
import QIQTH.Fock.Dirac.EvenObservables
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

/-- **Vacuum invariance** `Γ₋(Δ^{it}) Ω = Ω`: the modular flow fixes the vacuum (the unit of the
exterior/CAR algebra), since `Γ₋(Δ^{it})` is an algebra hom. -/
@[simp] theorem fermiSecondQuantModFlow_one (S : StandardSubspace H) (t : ℝ) :
    fermiSecondQuantModFlow S t 1 = 1 := map_one _

/-- `Γ₋(Δ^{it}) ∘ Γ₋(Δ^{−it}) = id` — the modular flow at time `−t` is its inverse. -/
theorem fermiSecondQuantModFlow_comp_neg (S : StandardSubspace H) (t : ℝ) :
    (fermiSecondQuantModFlow S t).comp (fermiSecondQuantModFlow S (-t))
      = AlgHom.id ℂ (ExteriorAlgebra ℂ H) := by
  rw [fermiSecondQuantModFlow_add, add_neg_cancel, fermiSecondQuantModFlow_zero]

/-- **The modular flow acts by ALGEBRA AUTOMORPHISMS.**  `Γ₋(Δ^{it})` is an algebra *isomorphism* of the
CAR Fock `⋀ H` with inverse `Γ₋(Δ^{−it})` — the defining Tomita–Takesaki property that the modular
automorphism group `σ_t = Γ₋(Δ^{it})` lands in `Aut(𝓕)`.  Bundled as an `AlgEquiv`. -/
noncomputable def fermiModFlowEquiv (S : StandardSubspace H) (t : ℝ) :
    ExteriorAlgebra ℂ H ≃ₐ[ℂ] ExteriorAlgebra ℂ H :=
  AlgEquiv.ofAlgHom (fermiSecondQuantModFlow S t) (fermiSecondQuantModFlow S (-t))
    (fermiSecondQuantModFlow_comp_neg S t)
    (by have h := fermiSecondQuantModFlow_comp_neg S (-t); rwa [neg_neg] at h)

@[simp] theorem fermiModFlowEquiv_apply (S : StandardSubspace H) (t : ℝ)
    (x : ExteriorAlgebra ℂ H) : fermiModFlowEquiv S t x = fermiSecondQuantModFlow S t x := rfl

/-- **The modular flow commutes with the fermion parity `Γ = (−1)^F`** (`Parity.parity`):
`Γ₋(Δ^{it}) ∘ Γ = Γ ∘ Γ₋(Δ^{it})`.  Both are graded algebra homs (`Γ₋(Δ^{it}) = map U` preserves
exterior degree; `Γ` is the grade involution), so they agree on the one-particle generators.  Hence the
continuum modular flow **preserves the ℤ₂ grading — the even (record/observable) sector is invariant
under the modular dynamics**: the record/charge is conserved by the field-level modular flow (the §0/E8
"records attach to the even algebra" decision, conserved by `σ_t`). -/
theorem fermiSecondQuantModFlow_comp_parity (S : StandardSubspace H) (t : ℝ) :
    (fermiSecondQuantModFlow S t).comp (parity ℂ H)
      = (parity ℂ H).comp (fermiSecondQuantModFlow S t) := by
  ext f
  show fermiSecondQuantModFlow S t (parity ℂ H (ExteriorAlgebra.ι ℂ f))
      = parity ℂ H (fermiSecondQuantModFlow S t (ExteriorAlgebra.ι ℂ f))
  rw [parity_ι, map_neg, fermiSecondQuantModFlow_ι, parity_ι]

/-- **The modular flow keeps records as records**: `IsEven x → IsEven (Γ₋(Δ^{it}) x)`.  The even
(record/observable) sector is mapped into itself by the continuum modular dynamics — a direct consequence
of `fermiSecondQuantModFlow_comp_parity`.  So the electron's records (the even bilinears `j^μ`, `T_μν`,
number) remain records under the field-level modular flow `σ_t`: modular dynamics conserves the
even/observable algebra, at the continuum. -/
theorem fermiSecondQuantModFlow_isEven (S : StandardSubspace H) (t : ℝ)
    {x : ExteriorAlgebra ℂ H} (hx : IsEven x) : IsEven (fermiSecondQuantModFlow S t x) := by
  have h := AlgHom.congr_fun (fermiSecondQuantModFlow_comp_parity S t) x
  simp only [AlgHom.comp_apply] at h
  unfold IsEven at hx ⊢
  rw [hx] at h
  exact h.symm

end QIQTH.Fock.Dirac
