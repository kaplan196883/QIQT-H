# Born Rule Derivation from `P_Q` — Sketch

**Status:** Commitment for QIQT-H foundations paper. Born rule will be a *theorem*, not an axiom (A7 is downgraded).

## Setup

Let `ρ` be a density operator on a separable Hilbert space `H` with `dim(H) ≥ 3`. By the spectral theorem,

```tex
\rho = \sum_i \lambda_i\, |\psi_i\rangle\langle\psi_i|,\quad \lambda_i \ge 0,\quad \sum_i \lambda_i = 1.
```

Define the **effective dimension**:

```tex
d_{\rm eff}(\rho) \;=\; \frac{1}{\mathrm{Tr}(\rho^2)} \;=\; \frac{1}{\sum_i \lambda_i^2}.
```

QIQT-H **axiom A2** asserts a local capacity:

```tex
d_{\rm eff}(\rho_R) \;\le\; 2^{Q_R}.
```

## Definition of `P_Q`

When a measurement interaction drives `d_{\rm eff}(\rho)` toward `2^{Q_R}`, the informational projection operates:

```tex
\mathcal P_Q : \rho \;\longmapsto\; |\psi_k\rangle\langle\psi_k|\quad\text{for some } k,
```

i.e., `P_Q` maps `ρ` to one of its spectral eigenvectors. The choice of `k` is the **outcome**.

This is the *only* role `P_Q` plays operationally: it discards multi-eigenvector superposition once capacity is exhausted, leaving a single pure state.

## The outcome distribution must be a probability measure on the projection lattice

Let `p_k(ρ)` denote the probability that `P_Q` selects eigenvector `|ψ_k⟩` from `ρ`. By the structural axioms:

**(i) Spectral support.** If `λ_k = 0`, then `|ψ_k⟩` is not in the spectral support of `ρ`, and `p_k = 0`.

**(ii) Frame independence.** `P_Q` cannot depend on a basis chosen outside the framework. The probabilities must depend only on the operator pair `(ρ, |ψ_k⟩⟨ψ_k|)`.

**(iii) σ-additivity over orthogonal projections.** For any orthogonal projections `Π_1, Π_2` with `Π_1 Π_2 = 0`, the probability of "outcome in image of `Π_1` or in image of `Π_2`" equals the sum of the two probabilities. This is forced by the fact that `P_Q` produces a single eigenvector (mutually exclusive outcomes).

**(iv) Normalization.** `Σ_k p_k = 1`.

Therefore the map `f_ρ : Π ↦ p(\text{outcome} \in \mathrm{image}(Π))` defined on the projection lattice `P(H)` satisfies:

- `f_ρ(0) = 0`
- `f_ρ(I) = 1`
- `f_ρ(Π_1 + Π_2) = f_ρ(Π_1) + f_ρ(Π_2)` for orthogonal `Π_i`

## Apply Gleason's theorem

**Gleason (1957).** *For a separable Hilbert space `H` with `dim(H) ≥ 3`, every σ-additive probability measure `f` on the lattice of projection operators `P(H)` is of the form `f(Π) = Tr(σ Π)` for some unique density operator `σ` on `H`.*

Applying Gleason to `f_ρ`: there exists a unique density operator `σ_ρ` on `H` such that

```tex
p_k(\rho) \;=\; f_\rho(|\psi_k\rangle\langle\psi_k|) \;=\; \mathrm{Tr}(\sigma_\rho\, |\psi_k\rangle\langle\psi_k|) \;=\; \langle\psi_k|\,\sigma_\rho\,|\psi_k\rangle.
```

## Identification of `σ_ρ` with `ρ`

We now argue `σ_ρ = ρ`.

By spectral-support condition (i): for any `k` with `λ_k = 0`, `p_k = ⟨ψ_k|σ_ρ|ψ_k⟩ = 0`. So `σ_ρ` has the same null space as `ρ`.

By frame independence (ii): `σ_ρ` is determined by `ρ` alone, and must commute with `ρ` (otherwise it would introduce a preferred basis not present in `ρ`). Hence `σ_ρ` is diagonal in the eigenbasis of `ρ`.

By normalization (iv) and the requirement that `P_Q` preserves expectation values for observables compatible with `ρ`'s spectral decomposition (a minimal physical consistency condition), the diagonal entries of `σ_ρ` in `ρ`'s eigenbasis must equal `λ_k`. Hence

```tex
\sigma_\rho \;=\; \rho.
```

## Conclusion — Born rule emerges

```tex
\boxed{\;p_k(\rho) \;=\; \langle\psi_k|\,\rho\,|\psi_k\rangle \;=\; \lambda_k\;}
```

For a general POVM `{E_i}` (e.g., the measurement basis when the apparatus has not yet diagonalized `ρ`), the same argument applied to `P_Q` acting on the system-apparatus joint state yields

```tex
p_i \;=\; \mathrm{Tr}(\rho\, E_i),
```

which is the standard Born rule for POVMs.

## What this derivation buys QIQT-H

1. **A7 is no longer an axiom.** It is a theorem in the framework `A1–A6 + Gleason`.
2. **Matches RaQM's "Born rule derived, not postulated" claim.** Palmer derives Born from bit-string counting; QIQT-H derives it from spectral-truncation `P_Q` + Gleason. QIQT-H's derivation is basis-independent and does not require the discretized Riemann Sphere.
3. **Forces `dim(H) ≥ 3`** as a precondition. For genuinely 2-dimensional qubit systems, Born rule still needs a separate argument (Gleason fails for `dim = 2`). This is a known feature of Gleason-based derivations, not a defect specific to QIQT-H. The paper should flag it explicitly and cite the standard work-arounds (e.g., Busch's POVM extension of Gleason, which restores `dim = 2`).

## Subtleties to address in the paper

1. **Why does `P_Q` pick *the spectral basis* of `ρ` rather than some other basis?** Answer: because the joint system-apparatus state already has a preferred basis from the apparatus interaction; `ρ` here is the joint state, and its spectral basis approximately coincides with the pointer basis after decoherence. So `P_Q` does not select the pointer basis — *decoherence* selects it, and `P_Q` operates within it.
2. **Stochasticity.** `P_Q` is stochastic in the sense that it produces one outcome from a distribution. But this stochasticity is not a new physical postulate beyond Gleason — it is the unique probability assignment compatible with the framework.
3. **Compatibility with the no-collapse-within-patch axiom A4.** `P_Q` acts at *capacity saturation*, which is the boundary of the coherence patch. A4 applies *within* the patch. There is no contradiction: the patch boundary is exactly where coherent unitary description ceases to be sustainable.

## Open technical questions for the paper

- Make precise the condition "drives `d_eff` toward `2^{Q_R}`" — is it `d_eff ≥ 2^{Q_R}`, or `d_eff > (1−ε)·2^{Q_R}` for some `ε`, or a continuous saturation function?
- The Busch extension of Gleason for `dim = 2` should be cited and verified compatible.
- Is `P_Q` instantaneous, or does it have a finite timescale? If finite, what sets the timescale (and does it leave room for the neutrino-decoherence prediction)?
