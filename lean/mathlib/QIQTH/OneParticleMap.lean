/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The one-particle map `j_ℏ` (momentum representation) and boost-invariance of `σ`

This packages the track-A chain into a named one-particle map and its two defining properties.

`jHbar m ℏ Ψ π h` is the `L²` class of the KG positive-frequency coefficient `posFreqCoeff m ℏ Ψ π`
(the one-particle vector of the mode with Fourier-side Cauchy data `(Ψ,π)`), where `h` witnesses that
the coefficient lies in `L²` — supplied by brick-5 (`kg_posFreq_memLp`) on the `H^{1/2}⊕H^{-1/2}`
domain.  Its properties:

* `jHbar_two_hbar_im_inner_eq_sigmaK` — the canonical normalization: `2ℏ·Im⟪j_ℏ u, j_ℏ v⟫_ℂ = σ_K`
  (the capstone, in terms of `jHbar`).
* `jHbar_boost_two_hbar_im_inner_eq_sigmaK` — **boost-invariance of `σ`**: applying the rapidity boost
  `boostRapidity β` (a unitary, brick-8) to the one-particle vectors leaves `2ℏ·Im⟪·,·⟫ = σ_K`
  unchanged.  So the KG symplectic form computed through the one-particle map is the same in every
  boosted frame — the Lorentz-invariance of the construction, on the momentum/rapidity representation.

## Scope firewall (HONEST)

`jHbar` is the `MemLp.toLp` packaging of the positive-frequency coefficient (the def itself is a naming
layer); the CONTENT is the two properties — the σ-normalization (bricks 2+5+6) and its boost-invariance
(brick-8, `boostRapidity` unitary).  This is the one-particle map on the MOMENTUM/RAPIDITY
representation.  It is NOT the geometric position-space construction (relating a spacetime Lorentz boost
of the Cauchy data to `boostRapidity` needs KG reconstruction + dispersion + the on-shell mass-shell
surface measure — a distinct research phase); NOT the Fock second-quantization; NOT numerical-`G`;
NOT QG.  Conjugate symmetry, integrability, and `L²` memberships carried as HYPOTHESES.
-/
import QIQTH.PosFreqInner
import QIQTH.OneParticleBoost

namespace QIQTH.OneParticleMap

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open QIQTH.KGSymplectic QIQTH.PosFreqInner QIQTH.OneParticleBoost

/-- **The one-particle map `j_ℏ` (momentum representation).**  The `L²` class of the KG
positive-frequency coefficient of the mode with Fourier-side Cauchy data `(Ψ,π)`.  The membership `h`
is supplied by brick-5 (`kg_posFreq_memLp`) on the `H^{1/2}⊕H^{-1/2}` domain. -/
noncomputable def jHbar (m ℏ : ℝ) (Ψ π : ℝ → ℂ)
    (h : MemLp (posFreqCoeff m ℏ Ψ π) 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  h.toLp (posFreqCoeff m ℏ Ψ π)

/-- **Canonical normalization in terms of `j_ℏ`.**  `2ℏ·Im⟪j_ℏ u, j_ℏ v⟫_ℂ = σ_K` — the capstone. -/
theorem jHbar_two_hbar_im_inner_eq_sigmaK
    (m ℏ : ℝ) (hm : 0 < m) (hℏ : 0 < ℏ) (Ψ π Χ Ρ : ℝ → ℂ)
    (hconjΨ : ∀ k, Ψ (-k) = starRingEnd ℂ (Ψ k))
    (hconjπ : ∀ k, π (-k) = starRingEnd ℂ (π k))
    (hconjΧ : ∀ k, Χ (-k) = starRingEnd ℂ (Χ k))
    (hconjΡ : ∀ k, Ρ (-k) = starRingEnd ℂ (Ρ k))
    (hf : Integrable
      (fun k => starRingEnd ℂ (posFreqCoeff m ℏ Ψ π k) * posFreqCoeff m ℏ Χ Ρ k) (volume : Measure ℝ))
    (hdiag : Integrable (fun k => (htDiag m Ψ π Χ Ρ k).im) (volume : Measure ℝ))
    (hsig : Integrable
      (fun k => starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k) (volume : Measure ℝ))
    (ha : MemLp (posFreqCoeff m ℏ Ψ π) 2 (volume : Measure ℝ))
    (hb : MemLp (posFreqCoeff m ℏ Χ Ρ) 2 (volume : Measure ℝ)) :
    2 * ℏ * (inner ℂ (jHbar m ℏ Ψ π ha) (jHbar m ℏ Χ Ρ hb) : ℂ).im = sigmaK Ψ π Χ Ρ :=
  two_hbar_im_L2_inner_posFreq_eq_sigmaK m ℏ hm hℏ Ψ π Χ Ρ
    hconjΨ hconjπ hconjΧ hconjΡ hf hdiag hsig ha hb

/-- **Boost-invariance of `σ` via the one-particle map.**  Applying the rapidity boost of any `β`
(a unitary) to both one-particle vectors leaves `2ℏ·Im⟪·,·⟫ = σ_K` unchanged: the KG symplectic form
computed through `j_ℏ` is the same in every boosted frame — the Lorentz-invariance of the
construction, at the rapidity level. -/
theorem jHbar_boost_two_hbar_im_inner_eq_sigmaK
    (m ℏ : ℝ) (hm : 0 < m) (hℏ : 0 < ℏ) (β : ℝ) (Ψ π Χ Ρ : ℝ → ℂ)
    (hconjΨ : ∀ k, Ψ (-k) = starRingEnd ℂ (Ψ k))
    (hconjπ : ∀ k, π (-k) = starRingEnd ℂ (π k))
    (hconjΧ : ∀ k, Χ (-k) = starRingEnd ℂ (Χ k))
    (hconjΡ : ∀ k, Ρ (-k) = starRingEnd ℂ (Ρ k))
    (hf : Integrable
      (fun k => starRingEnd ℂ (posFreqCoeff m ℏ Ψ π k) * posFreqCoeff m ℏ Χ Ρ k) (volume : Measure ℝ))
    (hdiag : Integrable (fun k => (htDiag m Ψ π Χ Ρ k).im) (volume : Measure ℝ))
    (hsig : Integrable
      (fun k => starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k) (volume : Measure ℝ))
    (ha : MemLp (posFreqCoeff m ℏ Ψ π) 2 (volume : Measure ℝ))
    (hb : MemLp (posFreqCoeff m ℏ Χ Ρ) 2 (volume : Measure ℝ)) :
    2 * ℏ * (inner ℂ (boostRapidity β (jHbar m ℏ Ψ π ha)) (boostRapidity β (jHbar m ℏ Χ Ρ hb)) : ℂ).im
      = sigmaK Ψ π Χ Ρ := by
  rw [two_hbar_im_boostRapidity_inner]
  exact jHbar_two_hbar_im_inner_eq_sigmaK m ℏ hm hℏ Ψ π Χ Ρ
    hconjΨ hconjπ hconjΧ hconjΡ hf hdiag hsig ha hb

end QIQTH.OneParticleMap
