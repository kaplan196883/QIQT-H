/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Boost covariance of the one-particle space — the boost is a unitary preserving `σ`

On the momentum/rapidity representation the KG one-particle Hilbert space is `L²(ℝ, ℂ)` (the field is
parametrised by rapidity `θ`, `k = m·sinh θ`).  A Lorentz **boost** of rapidity `β` acts on the mass
shell by `θ ↦ θ + β` — a *translation* in rapidity.  Since Lebesgue measure is translation-invariant,
pullback along the translation is a **linear isometry** of `L²`, i.e. the boost is **unitary** on the
one-particle space, and therefore preserves the inner product and the canonical form `2ℏ·Im⟪·,·⟫ = σ`.

This is the boost-covariance ingredient of `j_ℏ`, on the momentum/rapidity representation (where the
one-particle space genuinely is an `L²`, so no spacetime-Fourier / mass-shell-restriction obstruction
arises — the boost is a bona fide unitary).

## What is proved (axiom-free)

* `boostRapidity β` — the boost of rapidity `β` as a `LinearIsometry` on `Lp ℂ 2 volume` (pullback
  along `θ ↦ θ + β`, via `Lp.compMeasurePreservingₗᵢ` + translation-invariance of `volume`).
* `boostRapidity_inner` — the boost preserves the one-particle inner product `⟪·,·⟫_ℂ`.
* `two_hbar_im_boostRapidity_inner` — hence it preserves `2ℏ·Im⟪·,·⟫` = the KG symplectic form `σ`:
  the one-particle construction is boost-invariant (Lorentz-covariant at the rapidity level).

## Scope firewall (HONEST)

This is boost covariance ON THE MOMENTUM/RAPIDITY REPRESENTATION: the boost = rapidity translation is
a unitary preserving `σ`.  It rests on translation-invariance of Lebesgue measure + `LinearIsometry`
inner-product preservation.  It is NOT the geometric statement relating a spacetime Lorentz boost of
the *position-space* Cauchy data to this rapidity translation (that needs KG reconstruction +
dispersion + the on-shell mass-shell measure — a distinct research phase); NOT the full packaged
`j_ℏ`; NOT numerical-`G`; NOT QG.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure

namespace QIQTH.OneParticleBoost

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- **The boost of rapidity `β` as a linear isometry on the one-particle space `L²(ℝ,ℂ)`.**
Pullback along the rapidity translation `θ ↦ θ + β`; a `LinearIsometry` because Lebesgue `volume` is
translation-invariant (`measurePreserving_add_right`). -/
noncomputable def boostRapidity (β : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun θ => θ + β) (measurePreserving_add_right volume β)

/-- **The boost preserves the one-particle inner product** — it is unitary. -/
theorem boostRapidity_inner (β : ℝ) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ (boostRapidity β f) (boostRapidity β g) : ℂ) = inner ℂ f g :=
  (boostRapidity β).inner_map_map f g

/-- **Boost covariance of the KG symplectic form.**  The boost preserves `2ℏ·Im⟪·,·⟫` — i.e. the
one-particle construction's realization of `σ` is boost-invariant (Lorentz-covariant at the rapidity
level). -/
theorem two_hbar_im_boostRapidity_inner (ℏ β : ℝ) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    2 * ℏ * (inner ℂ (boostRapidity β f) (boostRapidity β g) : ℂ).im
      = 2 * ℏ * (inner ℂ f g : ℂ).im := by
  rw [boostRapidity_inner]

end QIQTH.OneParticleBoost
