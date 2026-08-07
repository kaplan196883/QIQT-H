---
layout: ../layouts/Deep.astro
title: Realisations of QIQT-H — runnable toy models
eyebrow: What a "realisation" is, made executable
description: QIQT-H is a boundary theory; a realisation is a generative model that fits it. Two SymPy-verified toys — a finite realisation (one CAR mode in a microstate memory) and the continuum realisation where the Einstein equations actually appear (a free field on a pp-wave) — draw the exact line between the two.
---

QIQT-H is best read as a **boundary theory**: a small postulate core (the $(\Phi,\lambda)$ ontology,
quantum equilibrium, and *finite regional capacity*) plus a family of *necessary conditions* on the record
structure of any quantum theory. A **realisation** is then a generative model — a constructive field theory,
the Standard Model, a quantum-spacetime construction — whose regional data, encoded into the finite-capacity
microstate space, satisfies those conditions. (See [the theory](/theory) and [the formalization](/formalization).)

The cleanest way to see what that *means* is to build the smallest realisations and **check the boundary
conditions exactly**. Two short, fully runnable SymPy scripts do precisely that. Together they draw the exact
line between what a *finite* realisation gives you and what the **Einstein field equations** actually require.

## The minimal finite realisation

`scripts/qiqth_minimal_realisation.py` — **one fermionic CAR mode (a qubit code $C=\mathbb{C}^2$)
isometrically embedded, $V:\mathbb{C}^2\hookrightarrow\mathbb{C}^N$, into a finite microstate memory
$\mathcal{H}_R=\mathbb{C}^N$.** It is the smallest object that exercises *every* boundary condition — and,
being one exact-CAR mode, it fits a finite sector perfectly. The script constructs the objects and verifies,
symbolically and exactly, each condition (each tagged with its machine-checked Lean theorem):

- **CAR fits exactly** — $\{a,a^\dagger\}=1$ on $\mathbb{C}^2$ (a fermion is finite; a boson cannot be).
- **The corner, and the tripwire** — $P=VV^\dagger$ is an orthogonal projector, and the encoding is unital
  *onto the corner*: $\iota_V(1)=P\neq 1_{\mathcal{H}_R}$, never the ambient identity.
- **Faithful read-back** — $\operatorname{Tr}\big((V\rho V^\dagger)(VOV^\dagger)\big)=\operatorname{Tr}(\rho O)$.
- **CAR in the corner** — $\{\iota_V(a),\iota_V(a^\dagger)\}=P$.
- **Born from typicality** — the equiprobable measure over an equal-amplitude orthonormal fine-graining
  reproduces the Born weights $|c_k|^2$ (the toy returns $\{0:\tfrac12,\,1:\tfrac13,\,2:\tfrac16\}$).
- **The area floor** — $S_{\mathrm{vN}}(\rho)\le\log\dim C\le\log\dim\mathcal{H}_R=\text{area}$.
- **Photon honesty** — a truncated bosonic mode necessarily carries the explicit defect
  $[a,a^\dagger]=1-N\,|N{-}1\rangle\langle N{-}1|$ (exact CCR is impossible in finite dimension).

Three composition checks confirm the program stays consistent under combination:

- **(a) Locality** — disjoint regions' observables commute, and the corner encoding *preserves* it:
  $[\iota_V(O_A),\iota_V(O_B)]=\iota_V([O_A,O_B])=0$ (because the encoding is a $\star$-homomorphism).
- **(b) Tensor-network RT** — a $3$-node weighted graph whose **cut is the area primitive**: purity
  $S(A)=S(A^c)$, subadditivity, the RT inequality $S_{\mathrm{vN}}(\rho_A)\le\mathrm{cut}(A)$, and min-cut
  *violating* the triangle inequality ($\lambda_{02}=5>4=\lambda_{01}+\lambda_{12}$) — so it is an **area,
  never a distance**.
- **(c) The thermal half** — a finite modular/Gibbs state with a *genuine temperature* (finite KMS), the
  exact entanglement first law $\delta S=\delta\langle K\rangle$, and — with the modular Hamiltonian
  $\propto$ area — the entropy–area variation $\delta S=\eta\,\delta A$.

That is as far as a *finite* realisation reaches: it carries the kinematic **and** the thermal boundary
conditions — including $\delta S=\eta\,\delta A$ — but it yields **no Einstein equations**.

<div class="note">

<strong>From one mode to the free Standard Model.</strong> The single CAR mode is only the smallest case. In
the Lean development (`FreeFieldCorner.lean`) the full <em>free</em> Standard-Model content — Dirac fermions,
gauge bosons, and the Higgs — is <em>transported</em> into the same capacity-bounded corner $P=VV^\dagger$,
with the graded (anti)commutation brackets preserved. This is <strong>transport, not construction</strong>:
the interacting dynamics (the actual Standard-Model couplings) are a cited frontier, and everything stays
<em>free / linearized / flat</em>-background — a substrate, not quantum gravity.

</div>

## The minimal *gravitational* realisation — where GR appears

`scripts/qiqth_gr_realisation.py` — the continuum object that *does* reach GR: **the free Klein–Gordon
field on a pp-wave background,** $ds^2=H(u,x,y)\,du^2+2\,du\,dv+dx^2+dy^2$ (matching the Lean capstone
`qiqt_gr_ppwave_showcase`). The script verifies Jacobson's "Einstein equation as an equation of state",
symbolically and end to end:

1. **Geometry** — Christoffel $\to$ Ricci $\to$ Einstein tensor: $R=0$, $G_{uu}=-\tfrac12\nabla^2_\perp H$,
   all other $G_{\mu\nu}=0$.
2. **Conservation** — the contracted Bianchi identity $\nabla^\mu G_{\mu\nu}=0$ (what fixes $\Lambda$ and
   lets a *local* Clausius relation become a *field* equation).
3. **The null-cone lemma** — a symmetric $S$ with $S_{\mu\nu}k^\mu k^\nu=0$ for all null $k$ must be
   $S=f\,g$ (verified on Minkowski with nine null directions). This is what turns the per-direction
   Clausius relation into a *tensor* equation.
4. **The equation of state** — $\delta Q=T\,\delta S$, with the QIQT-H inputs that *are* theorems
   ($\delta S=\eta\,\delta A$ from `DifferentialAreaLaw`, the $1/4$ from `SakharovRatio`) and the Unruh
   temperature *discharged* for the free field (`Fock.OneParticleBW`), closes to the explicit Einstein
   equation:

$$ -\tfrac12\,\nabla^2_\perp H \;=\; 8\pi G\,(\partial_u\phi)^2 . $$

So **GR is a property of the *continuum* realisation** — the one that supplies the smooth metric and the
Raychaudhuri area derivative $\delta A\leftrightarrow R_{kk}$ that no finite toy contains. It is a
*conditional* derivation: the labelled residuals (the matter equation of motion, the capacity postulate
(P4), the localization map, the reference-state identification, and the **value** of $G$) remain inputs.

## What the two toys show together

- A **finite** realisation realises the kinematic + thermal boundary conditions — Born weights, the area
  floor, locality, the RT inequality, a finite temperature, and even $\delta S=\eta\,\delta A$.
- The **Einstein field equations** are *not* a boundary condition every realisation must satisfy. They are a
  property of the *richer continuum* realisation, which additionally supplies the smooth-background geometry
  (Raychaudhuri) and the Bisognano–Wichmann/Unruh temperature.

> **QIQT-H says what must hold of any region's records; a realisation is what makes it hold — and a
> *gravitational* realisation is one that also carries the continuum structure from which the Einstein
> equations follow.**

Both scripts are exact-symbolic (no floating point) and run to completion with every check passing. They
live in [`scripts/`](https://github.com/kaplan196883/QIQT-H/tree/main/scripts) alongside the
[machine-checked Lean substrate](/formalization).
