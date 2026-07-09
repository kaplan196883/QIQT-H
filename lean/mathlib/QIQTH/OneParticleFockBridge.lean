/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Bridge — the KG one-particle map `j_ℏ` sits inside the existing continuum Fock tower

The track-A chain (`OneParticleMap.jHbar`, with `σ = 2ℏ·Im⟪·,·⟫` and boost-invariance) was built on
`Lp ℂ 2 volume` — which is **exactly** the one-particle Hilbert space the pre-existing QIQT-H continuum
Fock tower is constructed over:

* `QIQTH.Fock.OneParticle.boostUnitary t : Lp ℂ 2 volume ≃ₗᵢ[ℂ] Lp ℂ 2 volume` — the 1+1D mass-`m`
  Lorentz boost as a one-parameter *unitary* group (rapidity = translation), and
* `QIQTH.Fock.boostFock t = Γ(boostUnitary t)` — its second quantization on the symmetric Fock space
  `FockPre (Lp ℂ 2 volume)`, with vacuum invariance `boostFock_vacuum`.

So the KG positive-frequency one-particle vectors `jHbar` are one-particle states of that existing
Fock space, and the existing `boostUnitary` is *the* boost acting on them (my `OneParticleBoost.boostRapidity`
is the same `Lp.compMeasurePreservingₗᵢ`-translation construction — a rediscovery of `boostUnitary`).

This file records the bridge: the KG symplectic form `σ_K`, expressed through `jHbar`, is invariant
under the **existing** Fock boost `boostUnitary` — hence the coefficient physics of `hTkk` embeds in the
pre-existing continuum Fock/CCR tower, whose second-quantized boost `boostFock = Γ(boostUnitary)` already
carries the Fock-level Lorentz covariance (vacuum-invariant).

## What is proved (axiom-free)

* `jHbar_boostUnitary_two_hbar_im_inner_eq_sigmaK` — `2ℏ·Im⟪boostUnitary t (j_ℏ u), boostUnitary t (j_ℏ v)⟫ = σ_K`:
  the KG symplectic form via `j_ℏ` is invariant under the **existing** Fock one-particle boost.

## Scope firewall (HONEST)

This connects the new `j_ℏ`/`σ` coefficient physics to the pre-existing Fock one-particle boost
(`boostUnitary`) and, through the existing `boostFock = Γ(boostUnitary)`, to the second-quantized
boost.  It is the momentum/rapidity representation.  It is NOT the geometric position-space boost bridge
(tilted-slice / KG-evolution infrastructure); NOT a new Fock construction (the Fock tower pre-exists);
NOT numerical-`G`; NOT QG.  Conj-symmetry, integrability, `L²` memberships carried as HYPOTHESES.
-/
import QIQTH.OneParticleMap
import QIQTH.Fock.OneParticle
import QIQTH.Fock.SecondQuant

namespace QIQTH.OneParticleFockBridge

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open QIQTH.KGSymplectic QIQTH.OneParticleMap QIQTH.Fock.OneParticle

/-- **The KG symplectic form via `j_ℏ` is invariant under the existing Fock boost `boostUnitary`.**
`2ℏ·Im⟪boostUnitary t (j_ℏ u), boostUnitary t (j_ℏ v)⟫_ℂ = σ_K` — the one-particle vectors from KG
Cauchy data transform under the pre-existing continuum Fock boost, and `σ` is preserved (Lorentz
covariance at the one-particle level, in the existing tower). -/
theorem jHbar_boostUnitary_two_hbar_im_inner_eq_sigmaK
    (m ℏ : ℝ) (hm : 0 < m) (hℏ : 0 < ℏ) (t : ℝ) (Ψ π Χ Ρ : ℝ → ℂ)
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
    2 * ℏ * (inner ℂ (boostUnitary t (jHbar m ℏ Ψ π ha)) (boostUnitary t (jHbar m ℏ Χ Ρ hb)) : ℂ).im
      = sigmaK Ψ π Χ Ρ := by
  rw [show (inner ℂ (boostUnitary t (jHbar m ℏ Ψ π ha)) (boostUnitary t (jHbar m ℏ Χ Ρ hb)) : ℂ)
        = inner ℂ (jHbar m ℏ Ψ π ha) (jHbar m ℏ Χ Ρ hb) from
      (boostUnitary t).toLinearIsometry.inner_map_map _ _]
  exact jHbar_two_hbar_im_inner_eq_sigmaK m ℏ hm hℏ Ψ π Χ Ρ
    hconjΨ hconjπ hconjΧ hconjΡ hf hdiag hsig ha hb

end QIQTH.OneParticleFockBridge
