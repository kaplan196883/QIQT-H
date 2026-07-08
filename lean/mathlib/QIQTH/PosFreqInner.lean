/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Capstone — the KG symplectic form IS `2ℏ·Im` of the one-particle Hilbert inner product

This ties the whole `Lp`/`j_ℏ` chain to the physics.  Composing:

* **brick-2** (`KGSymplectic.two_hbar_im_inner_posFreq_eq_sigmaK`): the bare-integral canonical
  normalization `2ℏ·Im(∫ conj(a)·b) = σ_K` for the KG positive-frequency coefficients
  `a = posFreqCoeff m ℏ Ψ π`, `b = posFreqCoeff m ℏ Χ Ρ`;
* **brick-6** (`OneParticleInner.two_hbar_im_L2_inner_eq_sigmaK`): the bridge from that integral to the
  genuine one-particle `L²` inner product,

gives the **Hilbert-space** statement

    2ℏ · Im ⟪a_L2, b_L2⟫_ℂ  =  σ_K(Ψ,π,Χ,Ρ)      (`two_hbar_im_L2_inner_posFreq_eq_sigmaK`)

where `a_L2, b_L2 : Lp ℂ 2 volume` are the `L²` classes of the positive-frequency coefficients.  So
the classical KG symplectic form `σ_K` equals `2ℏ` times the imaginary part of the one-particle inner
product of the canonically-`√(2ℏω)`-normalized positive-frequency modes — the coefficient physics of
the localization map `hTkk`, stated on the actual one-particle Hilbert space.

In the physical case the `L²` memberships `ha, hb` are supplied by **brick-5**
(`PosFreqDomain.kg_posFreq_memLp`, with `ω = kgOmega m`), which proves exactly that the
positive-frequency coefficient lies in `L²` on the `H^{1/2}⊕H^{-1/2}` Cauchy-data domain.

## Scope firewall (HONEST)

This is the inner-product form of the coefficient normalization — bricks 2 + 6 composed for the KG
posFreqCoeff.  It is NOT the full `j_ℏ` map (the Fourier `L²→L²` step exists in Mathlib as
`Lp.fourierTransformₗᵢ`; the bundled map + boost covariance remain).  Conjugate symmetry, the three
integrability hypotheses (brick-2), and the two `L²` memberships are carried as HYPOTHESES (never
axioms; the memberships come from brick-5).  NOT numerical-`G`; NOT QG.
-/
import QIQTH.OneParticleInner
import QIQTH.KGSymplectic

namespace QIQTH.PosFreqInner

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open QIQTH.KGSymplectic QIQTH.OneParticleInner

/-- **Capstone: `σ_K = 2ℏ·Im⟪a_L2, b_L2⟫_ℂ` for the KG positive-frequency coefficients.**

For conjugate-symmetric Fourier-side Cauchy data (transforms of real fields) with the brick-2
integrability hypotheses, and given (from brick-5) that the positive-frequency coefficients
`a = posFreqCoeff m ℏ Ψ π`, `b = posFreqCoeff m ℏ Χ Ρ` lie in `L²`, the KG symplectic pairing equals
`2ℏ` times the imaginary part of the one-particle Hilbert-space inner product of their `L²` classes. -/
theorem two_hbar_im_L2_inner_posFreq_eq_sigmaK
    (m ℏ : ℝ) (hm : 0 < m) (hℏ : 0 < ℏ) (Ψ π Χ Ρ : ℝ → ℂ)
    (hconjΨ : ∀ k, Ψ (-k) = starRingEnd ℂ (Ψ k))
    (hconjπ : ∀ k, π (-k) = starRingEnd ℂ (π k))
    (hconjΧ : ∀ k, Χ (-k) = starRingEnd ℂ (Χ k))
    (hconjΡ : ∀ k, Ρ (-k) = starRingEnd ℂ (Ρ k))
    (hf : Integrable
      (fun k => starRingEnd ℂ (posFreqCoeff m ℏ Ψ π k) * posFreqCoeff m ℏ Χ Ρ k)
      (volume : Measure ℝ))
    (hdiag : Integrable (fun k => (htDiag m Ψ π Χ Ρ k).im) (volume : Measure ℝ))
    (hsig : Integrable
      (fun k => starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k) (volume : Measure ℝ))
    (ha : MemLp (posFreqCoeff m ℏ Ψ π) 2 (volume : Measure ℝ))
    (hb : MemLp (posFreqCoeff m ℏ Χ Ρ) 2 (volume : Measure ℝ)) :
    2 * ℏ * (inner ℂ (ha.toLp (posFreqCoeff m ℏ Ψ π)) (hb.toLp (posFreqCoeff m ℏ Χ Ρ)) : ℂ).im
      = sigmaK Ψ π Χ Ρ :=
  two_hbar_im_L2_inner_eq_sigmaK ha hb
    (two_hbar_im_inner_posFreq_eq_sigmaK m ℏ hm hℏ Ψ π Χ Ρ
      hconjΨ hconjπ hconjΧ hconjΡ hf hdiag hsig)

end QIQTH.PosFreqInner
