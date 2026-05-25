# Conversation transcript — QIQT-H, RaQM, \(Q_{\max}\), fractal information dimension

Date of record: 2026-05-23  
Language of original conversation: Polish

> Note: this file is a working transcript of the conversation in the form of structured Markdown. Early parts of the conversation about quantum mechanics, measurement, decoherence, Schrödinger's cat and the center of mass of the Earth were partially shortened by the interface as "skipped" in the available history. Where verbatim text is not available, the substantive content has been preserved in the form of a summary.

---

## 1. Starting point: the measurement problem in quantum mechanics

The conversation began with the question:

> If in quantum mechanics observation is needed for the wave function to "become concrete", then what happens for example in the Earth's core, or on a planet that no one is observing?

In the course of the conversation, the following were separated:

- unitary evolution of the quantum state,
- decoherence,
- the Born rule,
- collapse as a postulate or as an update of the description,
- the problem of a single measurement outcome.

Key formula:

```tex
|\Psi\rangle = \sum_i c_i |s_i\rangle |A_i\rangle |O_i\rangle
```

where:

- \(S\) — the measured system,
- \(A\) — the apparatus,
- \(O\) — the observer,
- \(|O_i\rangle\) — the observer has recorded the outcome \(i\).

In purely unitary QM there is no rule selecting a single \(i\). Decoherence removes interference between branches, but on its own it does not select a single outcome.

---

## 2. Empirical completeness vs. ontological incompleteness

The following distinction was established:

### Empirical completeness

The theory predicts all measurable statistics:

```tex
P(\omega|P,M)=\mathrm{Tr}(\rho E_\omega)
```

where:

- \(P\) — preparation procedure,
- \(M\) — measurement procedure,
- \(E_\omega\) — POVM element.

### Ontological incompleteness

The theory does not say which single fact "really" occurred in one run, unless we add an extra postulate.

In the language of model theory:

```tex
\mathcal T_{\rm QM} \nvdash \varphi_i
```

where \(\varphi_i\) denotes the sentence:

> the observer is in the state \(|O_i\rangle\).

---

## 3. Proposal of bounded information: \(Q\)

The following hypothesis appeared:

> Not all amplitudes / probabilities can have infinite physical precision. There is a finite bound on coherent information.

Working form:

```tex
Q < \infty
```

Initially \(Q\) was treated as a global cutoff, later it was refined that it should be local and depend on the region and the system:

```tex
Q \to Q_R
```

or even more precisely:

```tex
Q_{\rm coh}(R, S, E, T, \text{couplings})
```

---

## 4. QIQT — Quantized Information Quantum Theory

The working theory was named:

```tex
\textbf{QIQT}
```

Its basic intuition:

> Microevolution remains unitary quantum mechanics, but the physically accessible coherent information is finite.

### Working axioms of QIQT

#### A1. State

```tex
\rho \in \mathcal B(\mathcal H)
```

#### A2. Finite coherent information

```tex
d_{\rm eff}(\rho)=\frac{1}{\mathrm{Tr}(\rho^2)}\le 2^{Q_R}
```

#### A3. Composition

```tex
\mathcal H_{AB}=\mathcal H_A\otimes\mathcal H_B
```

but the coherent information is subadditive:

```tex
Q_{AB}\le Q_A+Q_B
```

#### A4. Microdynamics

```tex
\rho(t)=U(t)\rho(0)U^\dagger(t)
```

#### A5. Informational projection

```tex
\mathcal P_Q:\rho\mapsto[\rho]_Q
```

#### A6. Measurement as interaction

```tex
\rho_S\otimes\rho_A \to U(\rho_S\otimes\rho_A)U^\dagger
```

#### A7. Born rule

```tex
p_i=\mathrm{Tr}(\rho E_i)
```

---

## 5. QIQT-H — adding holography and thermodynamics

So that QIQT could asymptotically yield GR, a holographic-thermodynamic element was added.

### Local holographic bound

```tex
Q_R^{\rm coh}\le Q_R^{\rm holo}=\frac{A(\partial R)}{4l_P^2\ln2}
```

### Informational entropy

```tex
S_Q=k_B\ln2\, Q_R
```

### Local horizon condition

```tex
\delta E=T\,\delta S_Q
```

Then, analogously to Jacobson's derivation, in the IR limit one can recover the Einstein equations:

```tex
G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G T_{\mu\nu}
```

---

## 6. Wald entropy

For modified theories of gravity, the simple area formula should be replaced by the Wald entropy:

```tex
Q_{\max}^{\rm Wald}=\frac{S_{\rm Wald}}{k_B\ln2}
```

In general:

```tex
S_{\rm Wald}
= -2\pi k_B
\int_{\mathcal H} d^{D-2}x\,\sqrt{h}\,
\frac{\partial L}{\partial R_{\mu\nu\rho\sigma}}
\epsilon_{\mu\nu}\epsilon_{\rho\sigma}
```

Therefore:

```tex
Q_{\rm holo}^{\rm Wald}
= -\frac{2\pi}{\ln2}
\int_{\mathcal H} d^{D-2}x\,\sqrt{h}\,
\frac{\partial L}{\partial R_{\mu\nu\rho\sigma}}
\epsilon_{\mu\nu}\epsilon_{\rho\sigma}
```

For \(f(R)\):

```tex
Q_{\max}^{f(R)}
=\frac{A}{4l_P^2\ln2}f'(R)
```

---

## 7. Cosmological constant and cosmic \(Q_{\max}\)

For positive \(\Lambda\) we have the de Sitter horizon:

```tex
R_{\rm dS}=\sqrt{\frac{3}{\Lambda}}
```

```tex
A_{\rm dS}=4\pi R_{\rm dS}^2=\frac{12\pi}{\Lambda}
```

In GR:

```tex
Q_{\max}^{\rm dS}=\frac{3\pi}{\Lambda l_P^2\ln2}
```

After taking Wald into account:

```tex
Q_{\max}^{\rm Wald+\Lambda}
=\mathcal W(\Lambda_{\rm eff})
\frac{3\pi}{\Lambda_{\rm eff}l_P^2\ln2}
```

where:

```tex
\mathcal W=\frac{S_{\rm Wald}}{S_{\rm BH}}
```

For pure GR:

```tex
\mathcal W=1
```

---

## 8. Computation of the cosmic \(Q_{\max}\)

Using the values:

```tex
\Lambda \approx 1.1056\times10^{-52}\ {\rm m^{-2}}
```

and:

```tex
l_P=1.616255\times10^{-35}\ {\rm m}
```

we obtained:

```tex
R_{\rm dS}\approx1.65\times10^{26}\ {\rm m}
```

that is:

```tex
R_{\rm dS}\approx17.4\ {\rm Gly}
```

and:

```tex
Q_{\max}\approx4.7\times10^{122}\ {\rm bits}
```

so order-of-magnitude:

```tex
Q_{\max}\sim10^{123}
```

---

## 9. Local limit from \(R\)

For a sphere of radius \(R\):

```tex
Q_{\rm local}(R)
=\mathcal W(R)\frac{\pi R^2}{l_P^2\ln2}
```

Taking the cosmic limit into account:

```tex
Q_{\max}(R)
=
\min\left[
\mathcal W(R)\frac{\pi R^2}{l_P^2\ln2},
\mathcal W_{\rm dS}
\frac{3\pi}{\Lambda_{\rm eff}l_P^2\ln2}
\right]
```

Later the hard `min` was removed via a saturating function.

---

## 10. Version without `min`

Instead of:

```tex
Q_{\rm Wald}^{\Lambda}(R)=\min(Q_{\rm local},Q_{\rm dS})
```

the following was proposed:

```tex
Q_{\rm Wald}^{\Lambda}(R)
=
Q_{\rm dS}
\left(1-e^{-Q_{\rm local}(R)/Q_{\rm dS}}\right)
```

where:

```tex
Q_{\rm local}(R)=\mathcal W(R)\frac{\pi R^2}{l_P^2\ln2}
```

```tex
Q_{\rm dS}=\mathcal W_{\rm dS}
\frac{3\pi}{\Lambda_{\rm eff}l_P^2\ln2}
```

Furthermore:

```tex
Q_{\rm phys}(R,S)
=
Q_{\rm Wald}^{\Lambda}(R)
\left[
\chi(R)
+(1-\chi(R))
\left(1-e^{-\frac{q_0N_{\rm eff}(S)}{Q_{\rm Wald}^{\Lambda}(R)}}\right)
\right]
```

where:

- \(q_0\sim10\) bits per elementary carrier,
- \(N_{\rm eff}\) — number of effective carriers,
- \(\chi(R)\) — geometric/horizon activity.

---

## 11. Q for particles and cosmology

In order to have simultaneously:

```tex
Q_{\rm particle}\sim10
```

and:

```tex
Q_{\rm universe}\sim10^{123}
```

the following was proposed:

```tex
Q_{\rm total}
=\min\left[Q_{\rm Wald},q_0N_{\rm eff}+\chi Q_{\rm Wald}\right]
```

or a smooth version of the above.

For a single particle:

```tex
N_{\rm eff}=1,\quad \chi=0
```

```tex
Q_{\rm phys}\approx q_0\sim10
```

For a horizon:

```tex
\chi=1
```

```tex
Q_{\rm phys}=Q_{\rm Wald}^{\Lambda}
```

---

## 12. QIQT-H and the Standard Model

The Standard Model remains as local microphysics:

```tex
\mathcal L_{\rm SM}
=\mathcal L_{\rm gauge}
+\mathcal L_{\rm fermion}
+\mathcal L_{\rm Higgs}
+\mathcal L_{\rm Yukawa}
```

QIQT-H composes with it as an EFT:

```tex
\mathcal L_{\rm QIQT-H}
=
\mathcal L_{\rm SM}
+\mathcal L_{\rm EH}
+\sum_k \frac{c_k}{Q_R^{\Delta_k}}\mathcal O_k^{\rm SM}
+\mathcal L_{\rm info}
```

Requirements:

- preservation of \(SU(3)_c\times SU(2)_L\times U(1)_Y\),
- no anomaly violations,
- locality and Lorentz covariance in known regimes,
- no change to precision results of QED/QCD/electroweak.

---

## 13. Neutrinos as a test

Neutrino oscillations require phase coherence:

```tex
|\nu_\alpha\rangle=\sum_i U_{\alpha i}|\nu_i\rangle
```

If QIQT-H were to provide additional decoherence:

```tex
P_{\alpha\to\beta}=P_{\alpha\to\beta}^{\rm QM}\cdot e^{-\Gamma_Q L}
```

then the data force:

```tex
\Gamma_Q L\ll1
```

With a simple ansatz:

```tex
\Gamma_Q\sim\frac{E}{Q}
```

IceCube/KM3NeT data suggest very large sector-dependent lower bounds:

```tex
Q_{\nu}^{\rm propagation}\gtrsim10^{22}-10^{28}
```

depending on energy and model.

---

## 14. Galaxies and \(Q\)

In the standard picture:

```tex
g_N(r)=\frac{GM_b(r)}{r^2}
```

For flat rotation curves:

```tex
v(r)\approx const
```

```tex
g(r)=\frac{v^2}{r}
```

In QIQT-H a factor was introduced:

```tex
\Xi(r)
=\frac{dS_Q/dr}{dS_{\rm Wald}/dr}
=\frac{dQ_{\rm gal}/dr}{dQ_{\rm Wald}/dr}
```

Modified Poisson equation:

```tex
\nabla\cdot[\Xi(r)\nabla\Phi]=4\pi G\rho_b
```

For a spherical galaxy:

```tex
\Xi(r)g(r)=g_N(r)
```

```tex
g(r)=\frac{g_N(r)}{\Xi(r)}
```

For flat rotation curves:

```tex
\Xi(r)\propto\frac1r
```

which means:

```tex
Q_{\rm gal}(r)\propto r
```

instead of:

```tex
Q_{\rm Wald}(r)\propto r^2
```

---

## 15. Effective information dimension

The following was proposed:

```tex
D_Q(r)=\frac{d\ln Q}{d\ln r}
```

Hypothesis:

```tex
D_Q(r): 3\to2\to1\to0
```

Interpretation:

| Scale | \(D_Q\) | Meaning |
|---|---:|---|
| micro | 3 | local volumetric degrees of freedom |
| holography / normal horizons | 2 | area law / Wald |
| galaxies | 1 | active radial information, flat rotation curves |
| cosmology | 0 | saturation by the de Sitter horizon |

An important distinction:

```tex
D_{\rm matter}(r)\neq D_Q(r)
```

The distribution of matter on large scales may tend toward dimension 3, while the information available in a causal patch saturates to dimension 0.

---

## 16. Mathematical constructions similar to \(D_Q(r)\)

Known constructions were pointed out:

### Scale-dependent fractal dimension

```tex
D(r)=\frac{d\ln N(r)}{d\ln r}
```

### Multifractals

```tex
\mu(B_r(x))\sim r^{\alpha(x)}
```

### Spectral dimension

```tex
d_S(\sigma)=-2\frac{d\ln P(\sigma)}{d\ln\sigma}
```

### Dimensional flow

Known in approaches to quantum gravity, e.g. causal dynamical triangulations and multiscale spacetimes.

For QIQT-H the best notation is:

```tex
D_Q(r,x)=\frac{d\ln Q(r,x)}{d\ln r}
```

---

## 17. One-parameter \(\beta\) model

An attempt:

```tex
D_Q(r)=3\left[
1-
\left(
\frac{\ln(r/l_P)}{\ln(R_\Lambda/l_P)}
\right)^\beta
\right]
```

```tex
Q(r)=Q(l_P)
\exp\left[\int_{l_P}^{r}D_Q(u)d\ln u\right]
```

From the cosmological condition:

```tex
Q(R_\Lambda)=Q_{\rm dS}
```

we obtained:

- for \(Q(l_P)=1\):

```tex
\beta\approx2.03
```

- for \(Q(l_P)\approx4.53\):

```tex
\beta=2
```

- for \(Q(l_P)=10\):

```tex
\beta\approx1.98
```

So naturally:

```tex
\beta\simeq2
```

---

## 18. Problem with \(\beta=2\)

For \(\beta=2\):

```tex
D_Q=1
```

falls around:

```tex
r\sim7000\ {\rm AU}
```

that is, on the scale of wide binary systems / outer Solar System, not on galactic scales.

On galactic scales:

```tex
D_Q\sim0.4-0.6
```

which does not give a simple MOND-like \(D_Q\sim1\) for kpc.

Conclusion:

> \(\beta=2\) is natural cosmologically, but cannot by itself directly represent a full modification of gravity on all scales. An activation/screening function would be needed.

---

## 19. RaQM / Palmer

QIQT-H was compared with Palmer's RaQM.

### RaQM / IST

- rejects the full continuous Hilbert space as fundamental,
- admits only rationally bounded states/bases,
- preserves the Schrödinger equation,
- bounds the number of qubits of full coherence,
- is connected with the fractal geometry of the invariant set.

### Invariant set

The set \(I_U\) is dynamically invariant:

```tex
F(I_U)=I_U
```

Interpretation:

> The universe moves on a fractal subset of state space, and most formal Hilbert states do not exist physically.

### Relation to QIQT-H

The most honest hierarchy:

```tex
\text{RaQM/IST}
\to
\text{QIQT-H as an EFT of information}
\to
\text{standard QM/QFT for small systems}
```

QIQT-H is simpler operationally, RaQM is deeper ontologically.

---

## 20. Comparisons

### QIQT-H vs RaQM

| Criterion | QIQT-H | RaQM / IST |
|---|---|---|
| Hilbert space | formally used, operationally bounded | not fundamental |
| \(Q\) | informational cutoff | result of arithmetic/geometry of the invariant set |
| Standard Model | easier as an EFT | harder |
| Gravity | thermodynamic-informational | more deeply geometric |
| Tests | optomechanics, neutrinos, GHZ, galaxies | limits on quantum computers, Bell, state arithmetic |

### QIQT-H vs CSL / DP / Bohm

- CSL/DP change the dynamics or introduce collapse.
- Bohm adds an ontology of trajectories.
- QIQT-H changes the bounds on physically accessible information.

---

## 21. Most important final formulas

### Local Wald + \(\Lambda\) limit

```tex
Q_{\rm Wald}^{\Lambda}(R)
=
Q_{\rm dS}
\left(1-e^{-Q_{\rm local}(R)/Q_{\rm dS}}\right)
```

```tex
Q_{\rm local}(R)=
\mathcal W(R)
\frac{\pi R^2}{l_P^2\ln2}
```

```tex
Q_{\rm dS}=
\mathcal W_{\rm dS}
\frac{3\pi}{\Lambda_{\rm eff}l_P^2\ln2}
```

### Physical \(Q\)

```tex
Q_{\rm phys}(R,S)
=
Q_{\rm Wald}^{\Lambda}(R)
\left[
\chi(R)
+(1-\chi(R))
\left(
1-e^{-\frac{q_0N_{\rm eff}(S)}
{Q_{\rm Wald}^{\Lambda}(R)}}
\right)
\right]
```

### Information dimension

```tex
D_Q(r)=\frac{d\ln Q}{d\ln r}
```

### Fractal information measure

```tex
Q(r)=Q(r_0)\exp\left(\int_{r_0}^{r}D_Q(u)d\ln u\right)
```

### Galactic QIQT-H equation

```tex
\nabla\cdot[\Xi(r)\nabla\Phi]
=
4\pi G\rho_b
```

```tex
\Xi(r)=\frac{dQ_{\rm gal}/dr}{dQ_{\rm Wald}/dr}
```

---

## 22. Most honest status of the theory

QIQT-H is not a confirmed theory.

It is a hypothesis / phenomenological skeleton that tries to tie together:

- quantum mechanics without physical collapse,
- finite information,
- holography,
- Wald entropy,
- the cosmological constant,
- the Standard Model as local microphysics,
- GR as a thermodynamic limit,
- galactic anomalies as a change of the active dimension of information.

The current data are consistent with it only because the theory still has free elements:

- \(\chi(R)\),
- \(N_{\rm eff}\),
- \(\mathcal W(R)\),
- the function \(D_Q(r,x)\),
- a screening/activation mechanism.

The most important condition for further development:

> one must derive a concrete function \(D_Q(r,x)\) or \(\chi\) from a deeper fractal / RaQM / information-theoretic structure, rather than fitting it phenomenologically.

---

## 23. Possible next steps

1. Build an explicit model of \(D_Q(r,x)\) as a multifractal measure.
2. Check whether \(\beta=2\) and a low-acceleration activation function are consistent with Gaia DR3.
3. Fit QIQT-H to the radial acceleration relation.
4. Recompute predictions for wide binary systems.
5. Compare with Palmer's RaQM as a possible microtheory.
6. Write a preprint:
   - definitions,
   - axioms,
   - theorems,
   - falsifying experiments.

---

# Short final version

QIQT-H can be summarized in one sentence:

> Microevolution remains unitary QM, but the physically accessible coherent information is finite, locally bounded by the Wald entropy and by the cosmological horizon; effective information dimensions can flow with scale as \(3\to2\to1\to0\), giving classicality, GR, galactic anomalies and a finite cosmic budget of bits.
