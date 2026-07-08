/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The canonical normalization at the Hilbert-space level — `σ = 2ℏ·Im⟪·,·⟫_{L²}`

Brick-2 (`KGSymplectic.two_hbar_im_inner_posFreq_eq_sigmaK`) established the canonical-normalization
identity `2ℏ·Im(∫ conj(a)·b) = σ_K` as a statement about a **bare integral**.  This file upgrades it
to the genuine **one-particle Hilbert-space inner product** on `L²(ℝ, ℂ)`: for `L²` classes
`a_L2, b_L2 : Lp ℂ 2 volume`,

    ⟪a_L2, b_L2⟫_ℂ  =  ∫ k, conj(a k)·b k     (`L2_inner_toLp_eq_integral`)

(Mathlib's complex inner product is conjugate-linear in the first slot, so this matches the
`σ_K`/`sigmaK` convention), whence

    2ℏ · Im ⟪a_L2, b_L2⟫_ℂ  =  σ_K            (`two_hbar_im_L2_inner_eq_sigmaK`).

So the KG symplectic form is `2ℏ` times the imaginary part of the *actual one-particle inner product*
— the canonical `σ = 2ℏ·Im⟨a,a⟩` normalization, now a Hilbert-space statement, not a raw integral.
Composed with brick-5 (`kg_posFreq_memLp`, giving `MemLp` of the positive-frequency coefficient on the
`H^{1/2}⊕H^{-1/2}` domain), this is the inner-product form of the coefficient physics.

## Scope firewall (HONEST)

This bridges the bare-integral identity (brick-2) to the `L²` inner product — the canonical
normalization as a Hilbert-space fact.  It is NOT the full `j_ℏ` (the Fourier `L²→L²` step exists in
Mathlib as `Lp.fourierTransformₗᵢ`; boost covariance + the packaged one-particle map remain).
`MemLp` membership of the coefficients is carried as a hypothesis (supplied by brick-5 in the physical
case).  NOT numerical-`G`; NOT QG.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace QIQTH.OneParticleInner

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

/-- **The `L²` inner product equals the bare integral.**  For `a, b ∈ L²(ℝ,ℂ)`, the Hilbert-space
inner product of their `L²` classes is `∫ conj(a)·b` (Mathlib's `⟪·,·⟫_ℂ` is conjugate-linear in the
first argument).  Proof: `L2.inner_def` unfolds to the pointwise-inner integral, then `coeFn_toLp`
rewrites the representatives back to `a, b` a.e. -/
theorem L2_inner_toLp_eq_integral (a b : ℝ → ℂ)
    (ha : MemLp a 2 (volume : Measure ℝ)) (hb : MemLp b 2 (volume : Measure ℝ)) :
    (inner ℂ (ha.toLp a) (hb.toLp b) : ℂ)
      = ∫ k : ℝ, (starRingEnd ℂ) (a k) * b k ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with k hka hkb
  rw [hka, hkb, RCLike.inner_apply']

/-- **The canonical normalization at the Hilbert-space level.**  Given the bare-integral
normalization `2ℏ·Im(∫ conj(a)·b) = σ_K` (brick-2), the same holds for the `L²` inner product:
`2ℏ·Im⟪a_L2, b_L2⟫_ℂ = σ_K`.  This is `σ = 2ℏ·Im⟨·,·⟩` on the actual one-particle Hilbert space. -/
theorem two_hbar_im_L2_inner_eq_sigmaK {ℏ σK : ℝ} {a b : ℝ → ℂ}
    (ha : MemLp a 2 (volume : Measure ℝ)) (hb : MemLp b 2 (volume : Measure ℝ))
    (hσ : 2 * ℏ * (∫ k : ℝ, (starRingEnd ℂ) (a k) * b k ∂volume).im = σK) :
    2 * ℏ * (inner ℂ (ha.toLp a) (hb.toLp b) : ℂ).im = σK := by
  rw [L2_inner_toLp_eq_integral a b ha hb]; exact hσ

end QIQTH.OneParticleInner
