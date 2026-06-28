/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P6/P7 — the photon's gauge-invariant record, GROUNDED in PhysLean's EM kinematics

The photon substrate's §0/P6 decision is **records = gauge-invariant observables**; the canonical one is
the electromagnetic **field strength** `F_μν = ∂_μ A_ν − ∂_ν A_μ` (the positive, physical content — never
the indefinite-metric `A_μ`).  Rather than rely solely on QIQT-H's own hand-built `F = dA` cohomology
(`QIQTH/Fock/Photon/PhotonFieldStrength.lean`), this module **bridges to PhysLean's reviewed
`Electromagnetism` kinematics** (`Physlib.Electromagnetism.Kinematics`), which provides
`ElectromagneticPotential`, its `fieldStrengthMatrix`, the `gaugeTransform A → A + ∂χ`, and — crucially —
`fieldStrengthMatrix_gaugeTransform`: **`F` is gauge-invariant**.

This is the second PhysLean bridge (the first, `QIQTH/Fock/Dirac/PhysLeanBridge.lean`, grounds the CAR
operator layer in PhysLean's `WickAlgebra`).  Here the photon's **gauge-invariant record** is
*defined as* PhysLean's `fieldStrengthMatrix` and shown to be (i) gauge-invariant, (ii) antisymmetric,
(iii) diagonal-free — i.e. an honest antisymmetric 2-form carrying the physical photon degrees of freedom,
with the pure-gauge redundancy `A → A + ∂χ` quotiented out at the level of the observable `F`.

HONEST scope: this is the *kinematic* (classical-field) gauge invariance of the record, grounded in
PhysLean.  The covariant (Gupta–Bleuler/BRST) quantization, the indefinite-metric Krein space, the
Maxwell `F`-net CCR, the Gauss-law boundary algebra, and the Kabat contact term remain the deferred
continuum frontier (P10).  Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.
Free Maxwell only.
-/
import Physlib.Electromagnetism.Kinematics.GaugeTransformation

namespace QIQTH.Fock.Photon

open Electromagnetism

variable {d : ℕ}

/-- **The photon's gauge-invariant record** = PhysLean's electromagnetic field-strength matrix
`F_μν = ∂_μ A_ν − ∂_ν A_μ`, built from the potential `A` (the positive/physical content).  The records of
the photon substrate are gauge-invariant observables; this is the canonical one, now grounded in
PhysLean's reviewed `Electromagnetism` kinematics rather than only QIQT-H's hand-built `F = dA`. -/
noncomputable def photonRecord (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) : ℝ :=
  A.fieldStrengthMatrix x μν

/-- **★ The photon record is gauge-invariant** (PhysLean-grounded): the field strength `F_μν` is unchanged
under a gauge transformation `A → A + ∂χ`.  So the photon's observable record does not see the pure-gauge
redundancy — exactly the §0/P6 "records = gauge-invariant" decision, now resting on PhysLean's
`fieldStrengthMatrix_gaugeTransform` (not only QIQT-H's own `PhotonFieldStrength`/`PhotonGaugeRecords`). -/
theorem photonRecord_gauge_invariant (A : ElectromagneticPotential d) (χ : SpaceTime d → ℝ)
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) (x : SpaceTime d)
    (μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) :
    photonRecord (ElectromagneticPotential.gaugeTransform χ A) x μν = photonRecord A x μν := by
  unfold photonRecord
  rw [ElectromagneticPotential.fieldStrengthMatrix_gaugeTransform A χ hA hχ]

/-- **The photon record is antisymmetric**: `F_μν = −F_νμ` (PhysLean's `fieldStrengthMatrix_antisymm`).
The record is a genuine antisymmetric 2-form — the algebraic home of the physical photon polarizations. -/
theorem photonRecord_antisymm (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ ν : Fin 1 ⊕ Fin d) :
    photonRecord A x (μ, ν) = - photonRecord A x (ν, μ) :=
  ElectromagneticPotential.fieldStrengthMatrix_antisymm A x μ ν

/-- **The photon record has vanishing diagonal**: `F_μμ = 0` (PhysLean's `fieldStrengthMatrix_diag_eq_zero`),
the immediate consequence of antisymmetry — no `μ = ν` self-component. -/
@[simp] theorem photonRecord_diag_zero (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ : Fin 1 ⊕ Fin d) :
    photonRecord A x (μ, μ) = 0 :=
  ElectromagneticPotential.fieldStrengthMatrix_diag_eq_zero A x μ

/-- **The gauge-shifted potential's record equals the original's, pointwise in every component** — the
component form of `photonRecord_gauge_invariant`, packaging the gauge invariance of the whole `F` tensor as
a function equality (`F[A+∂χ] = F[A]` as records over all `(x, μν)`). -/
theorem photonRecord_gaugeTransform_eq (A : ElectromagneticPotential d) (χ : SpaceTime d → ℝ)
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) :
    photonRecord (ElectromagneticPotential.gaugeTransform χ A) = photonRecord A := by
  funext x μν
  exact photonRecord_gauge_invariant A χ hA hχ x μν

/-- **★ The photon record is Lorentz-covariant** (PhysLean-grounded, P7): under a Lorentz transformation
`Λ` (the **boost** is the modular/Unruh flow for the wedge), the gauge-invariant record `F` transforms as a
genuine rank-2 tensor — `F(Λ·A)_μν = Σ_κρ Λ_μκ Λ_νρ · F(A)_κρ(Λ⁻¹·x)` (PhysLean's
`fieldStrengthMatrix_equivariant`).  So the modular/boost flow acts **covariantly** on the gauge-invariant
records: it does not leave the record set, it rotates it by the tensor rule — the photon analogue of the
electron's "modular flow preserves the even/observable algebra" (P7).  The records are a closed,
Lorentz-covariant family, exactly as a relativistic observable algebra must be. -/
theorem photonRecord_lorentz_covariant (A : ElectromagneticPotential d) (Λ : LorentzGroup d)
    (hA : Differentiable ℝ A) (x : SpaceTime d) (μ ν : Fin 1 ⊕ Fin d) :
    photonRecord (Λ • A) x (μ, ν)
      = ∑ κ, ∑ ρ, (Λ.1 μ κ * Λ.1 ν ρ) * photonRecord A (Λ⁻¹ • x) (κ, ρ) := by
  unfold photonRecord
  exact ElectromagneticPotential.fieldStrengthMatrix_equivariant A Λ hA x μ ν

end QIQTH.Fock.Photon
