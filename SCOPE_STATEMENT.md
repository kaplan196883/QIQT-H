# Scope, Claims, and Limitations

*Paper-ready wording for the Lean 4/Mathlib construction of a Poincaré-covariant, microcausal,
σ-additive typicality measure on the 1+1-dimensional free quantum field.*

**Author:** Paweł Kapłański — **Status:** draft (quant-ph / math.FA), 2026-06-10 —
**Artifact:** Lean 4 + Mathlib, axiom-free (`propext`, `Classical.choice`, `Quot.sound` only), no `sorry`;
`lean/mathlib/QIQTH/Fock/`.

This section states *exactly* what the machine-checked development establishes and, equally important,
what it does not. Every claim below is backed by a named, `#print axioms`-audited Lean theorem; every
limitation is a deliberate, explicit boundary of the result rather than an unstated gap.

---

## 1. The defensible one-paragraph statement (for the abstract)

> In Lean 4 with Mathlib, with no `sorry` and no nonstandard axioms (only `propext`, `Classical.choice`,
> `Quot.sound`), we formalize, for the massive 1+1-dimensional free scalar field, a one-particle
> localization map `K` from real smooth compactly-supported spacetime test functions into
> `L²(ℝ, dθ)` (rapidity parametrization of the positive mass shell). We prove: **(i) microcausality** —
> `Im⟪Kf, Kg⟫ = 0` whenever the supports of `f` and `g` are spacelike separated (the Pauli–Jordan / Einstein
> causality condition), with no analytic side hypothesis on the caller; **(ii) Poincaré equivariance** —
> `K(τ_b β_a f) = U(a,b)\,Kf`, where `U(a,b) = M_b ∘ U₁(a)` is the composite of the rapidity-translation
> isometry `U₁(a)` and the unimodular multiplication isometry `(M_b ψ)(θ) = e^{-iη(p_m(θ),b)}ψ(θ)`, and
> `(a,b) ↦ U(a,b)` is a unitary **representation** of the connected Poincaré group
> `ℝ^{1,1} ⋊ SO⁺(1,1)` (the group law `U(a,b)U(a',b') = U(a+a', b + Λ_{-a}b')` is proved); **(iii)
> non-triviality** — `K` is not the zero map (explicit Gaussian witness); and **(iv)** that the associated
> σ-additive Kolmogorov probability measure `μ∞` on binary outcome histories — whose finite cylinder
> marginals are the formalized Weyl-bit Born probabilities — is **invariant under the whole connected
> Poincaré group**, for any pairwise-spacelike (microcausal) localized family of modes. The result is for
> this specified free / quasi-free (vacuum) Weyl-bit construction and for connected proper-orthochronous
> transformations; it does not address interacting fields, discrete symmetries (P, T), or uniqueness among
> unrelated typicality measures.

---

## 2. What is proved (precise claims, with the Lean names)

All names live in `namespace QIQTH.Fock.Localization` unless noted; all are `#print axioms`-clean
(standard three only) in `QIQTH/AxiomAudit.lean`.

**(C1) Microcausality (Pauli–Jordan).**
For real, smooth, compactly-supported tests `f, g` with spacelike-separated supports and mass `m ≠ 0`,
`Im⟪K f, K g⟫ = 0`.
Top-level, side-condition-free form: `K_im_inner_eq_zero_smooth` (the `L²`-integrability hypothesis
`hKint` is discharged internally by Cauchy–Schwarz on the Schwartz amplitudes). Underlying analytic
theorem: `Kform_im_eq_zero_of_spacelike`, resting on the oscillatory-integral keystone
`|∫_a^b sin(c·sinh u)\,du| ≤ 3/(|c|\cosh a)` and a dominated-convergence + Fubini assembly.

**(C2) Boost equivariance.**
`K (β_a f) = U₁(a)\,(K f)`, where `U₁(a)` is the rapidity-translation isometry `θ ↦ θ + a` on `L²(ℝ,dθ)`
(`K_boost_equivariant`, with `U₁ = boostUnitary`).

**(C3) Translation equivariance.**
`K (τ_b f)(θ) = e^{-iη(p_m(θ),b)}\,(K f)(θ) = M_b (K f)(θ)`, where `M_b` is the multiplication-by-unimodular-
phase isometry (`K_translate_equivariant`; the multiplier `multiplierIsometry`, proved a genuine
`LinearIsometry` via `multiplier_inner`, since `|e^{-iη}| = 1` makes the phase cancel in every inner
product — so the `θ`-dependent phase still preserves the entire complex Gram matrix).

**(C4) The Poincaré representation.**
`U(a,b) := M_b ∘ U₁(a)` (`poincareIsometry`); `K(τ_b β_a f) = U(a,b)(Kf)` (`K_poincare_equivariant`); and
the group law `U(a,b) ∘ U(a',b') = U(a+a', b + Λ_{-a}b')` (`poincareIsometry_comp`), built from the two
subgroup laws (`boostUnitary_comp`, `multiplierIsometry_comp`) and the semidirect intertwining
`U₁(a) ∘ M_b = M_{Λ_{-a}b} ∘ U₁(a)` (`boostUnitary_comp_multiplier`). Thus `(a,b) ↦ U(a,b)` is a unitary
representation of the connected Poincaré group of 1+1D Minkowski space, which boosts and translations
generate.

**(C5) The covariant typicality measure.**
For a pairwise-spacelike localized family `{K(region i)}` (microcausality supplied by (C1)), there is a
unique σ-additive probability measure `μ∞` on the history space `∏_i {±1}` whose finite marginals are the
Weyl-bit Born weights (`weylBitNet`, `weylBit_typicalityMeasure_exists`), and `μ∞` is invariant under each
of: a boost (`localized_typicality_boost_invariant`), a translation
(`localized_typicality_translation_invariant`), and an arbitrary connected-Poincaré element
(`localized_typicality_poincare_invariant`). Invariance is the isometry-invariance of the measure
(`weylBit_typicality_boost_invariant`): `μ∞` depends only on the family's Gram matrix, which `U(a,b)`
preserves.

**(C6) Non-triviality.**
`K` is not identically zero: `K_gaussian_ne_zero` (the Gaussian's localized amplitude
`2^{-1/2}π\,e^{-m^2\cosh(2θ)/4}` is everywhere strictly positive, hence not a.e. zero), and there is a
genuinely spacelike pair of localizable bumps for which (C1) is non-vacuous
(`localized_microcausality_nonvacuous`).

---

## 3. What we do NOT claim (the honest boundaries)

These are scope statements, not gaps in the proofs. Each is a place where a stronger-sounding sentence
would be unsupported.

1. **"Canonical," not "unique."** `μ∞` is the measure *canonically constructed* from the Born/Gram kernel
   and uniquely *extending its own finite-cylinder marginals* (Kolmogorov uniqueness). We do **not** prove
   it is the unique measure satisfying Born + covariance + microcausality; distinct measures can share
   one-bit marginals unless the full finite-dimensional law is part of the specification.

2. **Born-law scope.** The cylinder marginals are the *formalized Weyl-bit Born weights*
   `‖∏_{i∈J} A(u_i,σ_i)Ω‖²` for a commuting (spacelike, microcausal) family. We do **not** claim a joint law
   for non-commuting / sequential measurements; for incompatible observables no global classical selector
   measure exists (Fine/Bell), and we make commutativity an explicit hypothesis.

3. **Free / quasi-free, vacuum.** This is a vacuum (quasi-free) construction determined by the one-particle
   map `K`. We do **not** claim interacting fields or state-independence.

4. **Connected, proper-orthochronous only.** Covariance is under the connected Poincaré group generated by
   boosts and translations. We do **not** address parity, time reversal, or the full Poincaré group with its
   disconnected components.

5. **Global translation.** A Poincaré transformation translates spacetime *once*: the same `b` acts on the
   whole family. We do **not** claim (and it would be false to claim) invariance under independent
   per-region translations.

6. **Non-triviality is global.** `K(\text{Gaussian}) ≠ 0` establishes that `K` is not the zero map. We do
   **not** yet prove the strictly-local statement `∃ f ∈ C_c^∞(ℝ^{1,1}),\ Kf ≠ 0` (which would require a
   Paley–Wiener analyticity argument); the Gaussian is not compactly supported.

7. **Symplectic vanishing vs. operator commutator.** We prove `Im⟪Kf, Kg⟫ = 0`. The corresponding statement
   "the local Weyl operators commute" should be read as: *in any representation of the CCR, vanishing of the
   symplectic form implies* `W(Kf)W(Kg) = W(Kg)W(Kf)`. We do not expose a particular CCR phase convention in
   the headline.

8. **Dimension.** All of the above is 1+1-dimensional. The mass-shell rapidity parametrization that makes the
   boost a translation is special to 1+1D; higher dimensions are not addressed.

---

## 4. Axiom hygiene

The development introduces **no domain axioms** for any of the results in §2 and contains **no `sorry`**.
Every theorem named above depends only on Lean's three standard foundational axioms — `propext`,
`Classical.choice`, `Quot.sound` — as verified by the `#print axioms` block in `QIQTH/AxiomAudit.lean` and
the repository's axiom-budget check. (The project as a whole carries 33 clearly-labelled interface axioms
used *elsewhere*, in unrelated continuum/operator-algebra modules; **none** is used by the construction
described here.)
