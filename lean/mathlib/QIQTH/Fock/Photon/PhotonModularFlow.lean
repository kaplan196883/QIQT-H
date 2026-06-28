/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P1/P5 — the photon continuum modular flow IS the bosonic `Γ_s(Δ^{it})` (reuse)

The photon is **bosonic** (CCR / *symmetric* Fock `Γ_s`), so — unlike the electron, whose CAR Fock needed
the *fermionic* second quantization `Γ₋ = ExteriorAlgebra.map` (`QIQTH/Fock/Dirac/CARModularFlow.lean`) —
the photon's continuum wedge modular flow `Δ_γ^{it} = Γ_s(Δ^{it})` is **exactly the existing bosonic
second-quantized modular flow** `secondQuantModFlow` (`QIQTH/Fock/SecondQuantModularFlow.lean`).  There is
nothing new to build: the one-particle continuum `Δ^{it} = modUnitary S t` (the RvD bounded standard
subspace, `StandardSubspaceModularFlow`) is statistics-independent, and the photon reuses the *same*
symmetric-Fock functor as the scalar.  Here `H` is the **physical transverse / helicity-±1 photon
one-particle space** and the flow is the geometric Rindler boost `U(Λ_W(−2πt))` (Bisognano–Wichmann).

This module simply *names* that reuse in the photon namespace and re-exports the modular-flow properties
as the photon's: the one-particle/exponential-vector action `Γ_s(Δ^{it}) e(f) = e(Δ^{it} f)`, vacuum
invariance, the identity at `t = 0`, the **one-parameter group law**, and isometry — both on the pre-Fock
space and on the Fock Hilbert-space completion.  So the photon continuum modular flow is a one-parameter
**isometric automorphism group fixing the vacuum**, reused wholesale from the bosonic substrate.  (Records
attach to the *gauge-invariant* observables, `F_μν`/`T_μν` — P6; that they are preserved by this flow is
P7.)

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Maxwell only.
-/
import QIQTH.Fock.SecondQuantModularFlow

namespace QIQTH.Fock.Photon

open QIQTH.Fock QIQTH.StandardSubspaceModular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`Δ_γ^{it} = Γ_s(Δ^{it})`** — the photon's continuum field-level modular flow on the (bosonic,
symmetric) pre-Fock space, *defined as* the existing bosonic `secondQuantModFlow`.  The photon reuses the
same symmetric-Fock second quantization as the scalar; only the one-particle space (transverse helicity
±1) differs, and the one-particle `Δ^{it}` is statistics-independent. -/
noncomputable def photonModFlow (S : StandardSubspace H) (t : ℝ) : FockPre H →ₗ[ℂ] FockPre H :=
  secondQuantModFlow S t

/-- **One-particle action**: `Γ_s(Δ^{it})(e(f)) = e(Δ^{it} f)` — the photon modular flow on an exponential
(coherent) vector boosts the one-particle label. -/
@[simp] theorem photonModFlow_expVec (S : StandardSubspace H) (t : ℝ) (f : H) :
    photonModFlow S t (FockPre.expVec f) = FockPre.expVec (modUnitary S t f) :=
  secondQuantModFlow_expVec S t f

/-- **Vacuum invariance** `Γ_s(Δ^{it}) Ω = Ω`: the photon modular flow fixes the Fock vacuum
`Ω = e(0)`. -/
@[simp] theorem photonModFlow_vacuum (S : StandardSubspace H) (t : ℝ) :
    photonModFlow S t (FockPre.expVec (0 : H)) = FockPre.expVec (0 : H) :=
  secondQuantModFlow_vacuum S t

/-- **`Γ_s(Δ^{i·0}) = id`** — at `t = 0` the photon modular flow is the identity. -/
theorem photonModFlow_zero (S : StandardSubspace H) (φ : FockPre H) :
    photonModFlow S 0 φ = φ :=
  secondQuantModFlow_zero S φ

/-- **The one-parameter group law** `Γ_s(Δ^{is}) ∘ Γ_s(Δ^{it}) = Γ_s(Δ^{i(s+t)})` — the photon continuum
modular flow is a one-parameter `ℝ`-action (the field-level `Δ_W^{it}` for the photon), reused from the
bosonic `secondQuantModFlow_add`. -/
theorem photonModFlow_add (S : StandardSubspace H) (s t : ℝ) (φ : FockPre H) :
    photonModFlow S s (photonModFlow S t φ) = photonModFlow S (s + t) φ :=
  secondQuantModFlow_add S s t φ

/-- **The photon modular flow is isometric** (preserves the Fock inner product) — a one-parameter group of
*unitaries*, the defining Tomita–Takesaki property of `Δ^{it}`. -/
theorem photonModFlow_isometric (S : StandardSubspace H) (t : ℝ) (φ ψ : FockPre H) :
    fockInner (photonModFlow S t φ : H →₀ ℂ) (photonModFlow S t ψ : H →₀ ℂ)
      = fockInner (φ : H →₀ ℂ) (ψ : H →₀ ℂ) :=
  fockInner_secondQuantModFlow S t φ ψ

/-- **`Δ_γ^{it}` on the Fock Hilbert space** — the photon modular flow extended to the completion, defined
as the bosonic `secondQuantModFlowH`. -/
noncomputable def photonModFlowH (S : StandardSubspace H) (t : ℝ) : Fock H → Fock H :=
  secondQuantModFlowH S t

/-- The photon Hilbert-space modular flow is an **isometry** (genuine unitary `Δ_γ^{it}`). -/
theorem photonModFlowH_isometry (S : StandardSubspace H) (t : ℝ) :
    Isometry (photonModFlowH S t) :=
  secondQuantModFlowH_isometry S t

/-- The photon Hilbert-space modular flow **fixes the vacuum** `Δ_γ^{it} Ω = Ω`. -/
theorem photonModFlowH_vacuum (S : StandardSubspace H) (t : ℝ) :
    photonModFlowH S t Fock.vacuum = Fock.vacuum :=
  secondQuantModFlowH_vacuum S t

end QIQTH.Fock.Photon
