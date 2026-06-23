# Empirical Signature — QIQT-H Neutrino Decoherence

**Commitment:** the paper's primary falsifiable prediction is a `Q_R`-dependent additional decoherence in neutrino oscillations over long baselines, testable at IceCube, KM3NeT, and successor neutrino observatories.

## Standard oscillation (the baseline)

Production of flavor eigenstate `|ν_α⟩` and detection in flavor `|ν_β⟩` over baseline `L` and neutrino energy `E`:

```tex
P_{\alpha\to\beta}^{\rm QM}(L,E)
= \sum_{i,j} U_{\alpha i}^* U_{\beta i} U_{\alpha j} U_{\beta j}^*
\exp\!\left[-i\frac{\Delta m_{ij}^2\, L}{2E}\right]
```

where `U_{αi}` is the PMNS matrix and `Δm²_{ij} = m_i² − m_j²`.

## QIQT-H modification

Each off-diagonal `(i ≠ j)` interference term picks up an extra decoherence factor:

```tex
P_{\alpha\to\beta}^{\rm QIQT-H}(L,E)
= \sum_{i,j} U_{\alpha i}^* U_{\beta i} U_{\alpha j} U_{\beta j}^*
\exp\!\left[-i\frac{\Delta m_{ij}^2\, L}{2E}\right]
\exp\!\left[-\Gamma_Q^{(ij)}(L, E)\, L\right].
```

The diagonal terms `(i = j)` are unaffected. The full QM oscillation pattern is recovered when `Γ_Q L → 0`.

## Origin of `Γ_Q` in QIQT-H

The two mass eigenstates `|ν_i⟩, |ν_j⟩` must maintain phase coherence over the propagation distance `L`. The phase accumulated is `Φ_{ij}(L) = Δm²_{ij} L / 2E`. Representing this phase to sufficient precision requires a number of coherent bits

```tex
n_{ij}(L,E) \;\sim\; \log_2\!\left(\frac{\Phi_{ij}(L)}{\delta\Phi_{\min}}\right)
\;\sim\; \log_2\!\left(\frac{\Delta m_{ij}^2\, L}{2E\,\delta\Phi_{\min}}\right)
```

where `δΦ_min` is the minimum resolvable phase difference (set by experimental sensitivity or, more fundamentally, by `Q_R` itself).

When `n_{ij}` approaches the coherent-information capacity available to the propagating neutrino pair, the relative phase becomes irretrievable and the off-diagonal term decoheres.

A natural first-order ansatz (Lindblad form, energy-scaling motivated by `Φ ∝ Δm² L / E` and `n ∝ log(LΔm²/E)`):

```tex
\Gamma_Q^{(ij)}(L,E) \;\sim\; \frac{c_\nu\, E}{Q_\nu^{\rm eff}(R_{\rm prop})}
\quad\text{or, with explicit dimensional scaling,}\quad
\Gamma_Q^{(ij)} \;\sim\; \frac{1}{\hbar c}\, \frac{E_\nu}{Q_\nu^{\rm eff}}
```

with `Q_ν^eff(R_prop)` the local coherent-information capacity along the propagation region. `c_ν` is an `O(1)` dimensionless constant the paper should attempt to fix from `P_Q`.

This is the simplest QIQT-H-flavored form. The paper should derive it more carefully from `P_Q` acting on the joint pair-state, not just dimensional-analyze it.

## Comparison with existing QG-decoherence ansätze

The neutrino-decoherence literature considers `Γ ∝ E^n` with `n ∈ {0, 1, 2}` ("type I/II/III" decoherence). QIQT-H's `Γ ∝ E¹` (linear) places it in the **type-II** class. This is significant because:

- IceCube and Super-Kamiokande searches typically report bounds on `γ₀` for each `n` separately
- Linear-in-E (`n = 1`) is one of the most-constrained channels — bounds are tight
- A specific microphysical origin for `n = 1` (rather than being a phenomenological choice) is a positive feature for QIQT-H

## Empirical bounds and predictions

Current IceCube atmospheric-neutrino bounds on linear-in-E decoherence (Stuttard & Jensen 2020; IceCube 2024 analyses):

```tex
\Gamma_Q / E \;\lesssim\; 10^{-32}\ \text{GeV}^{-1}
```

(approximate; specific limit depends on basis and decoherence model assumed)

This translates to a lower bound on the relevant `Q_ν^eff`:

```tex
Q_\nu^{\rm eff} \;\gtrsim\; \frac{c_\nu}{\hbar c}\cdot 10^{32}\ \text{GeV}^{-1}\cdot 1\,\text{GeV}
\;\sim\; \mathcal O(10^{22}\text{–}10^{28})\ \text{bits}
```

depending on `c_ν` and the energy range probed. This matches the order-of-magnitude estimate in the source QIQT-H.md (sec. 13).

## Discriminating predictions

QIQT-H predicts:

1. **Linear-in-E decoherence** for atmospheric and astrophysical neutrinos.
2. **`L`-independent `Γ_Q`** to first order (modulo `Q_ν^eff(R_prop)` slowly varying along the path).
3. **Cosmic neutrinos** (Gpc baselines) should show stronger decoherence than atmospheric neutrinos (km baselines) at the same `E`, by a factor of `L_cosmic / L_atm`.
4. **High-energy astrophysical neutrinos** (TeV–PeV, IceCube–KM3NeT) provide the tightest test. If `Q_ν^eff` is in the `10²²–10²⁸` range, the predicted decoherence is just at or below current sensitivity.
5. **Energy spectrum modification** for flavor ratios of astrophysical neutrinos: standard expectation `νₑ:ν_μ:ν_τ ≈ 1:1:1` after oscillation; QIQT-H predicts this ratio is approached *faster* than QM with increasing `L·E`.

## Falsification criteria

QIQT-H is **excluded** if:

- Future cosmic-neutrino flavor measurements show standard QM oscillation with sensitivity to `Q_ν^eff ≥ 10^{30}` bits, **or**
- The energy-scaling of decoherence is firmly *not* linear (`n ≠ 1`) — this would rule out the natural `Γ ∝ E / Q` form, **or**
- The decoherence rate is *zero* to sensitivity far below the natural QIQT-H scale derived from cosmological `Q_dS ~ 10^{123}` divided by horizon-scale `L`.

## Concrete deliverable for the paper

The QIQT-H paper should include:

- A short technical section deriving `Γ_Q ∝ E_ν / Q_ν^eff` from `P_Q` acting on the neutrino mass-eigenstate superposition. (One subsection, ~600 words.)
- A figure showing predicted decoherence as a function of `(L, E)` overlaid on current IceCube bounds.
- A table comparing QIQT-H predictions for IceCube, KM3NeT, IceCube-Gen2, and the proposed P-ONE detector.

## Why this signature, not others

Alternative candidate signatures considered and deferred:

- **Wigner's-friend coherence bounds** (nested-observer experiments). Conceptually pure but not currently achievable at relevant scales.
- **Quantum-computer fidelity scaling à la Palmer**. Would compete with RaQM directly on its strongest empirical territory; the QIQT-H story would be `Q_R`-dependent rather than global `N_max`, but the differentiation is technical and hard to demonstrate cleanly.
- **Optomechanical decoherence**. Constrained tightly by CSL bounds; QIQT-H's no-in-patch-noise commitment means it predicts *nothing* here, which is a non-result rather than a discriminating signature.
- **Cosmological CMB-mode coherence**. Interesting but speculative and far from current data.

**Neutrino decoherence wins** because:
1. The QIQT-H natural scale `Q_ν ~ 10^{22}–10^{28}` is *exactly the current IceCube sensitivity*. The next decade will test it.
2. The `Γ ∝ E` form is microphysically motivated by QIQT-H rather than chosen phenomenologically.
3. KM3NeT and IceCube-Gen2 will narrow the window within the paper's likely review timescale.
4. Negative results so far don't kill QIQT-H but constrain `Q_ν^eff` — turning a null result into a measurement.
