---
layout: ../layouts/Deep.astro
title: Formalization in Lean 4 / Mathlib
eyebrow: Machine-checked substrate
description: The QIQT-H deductive substrate is machine-verified in Lean 4 / Mathlib — bounded Tomita–Takesaki modular theory and coherent-state Araki relative entropy, with a reproducible build and theorem index.
---

The modular and relative-entropy *calculus* underlying the regional cost functional $\chi_R$ is
machine-verified for the free-field coherent-state sector. The development carries no `sorry` and, as
reported by `#print axioms`, depends only on the standard classical foundations of Lean/Mathlib
(`propext`, `Classical.choice`, `Quot.sound`). At present the corpus spans roughly **409 files and ~4,400
theorems** (over 5,300 declarations including definitions) with a verified **axiom budget of 0** (every project-specific interface axiom has been discharged
to a concrete proof or a typeclass instance; what remains is carried as explicit, clearly-labelled hypotheses,
never as Lean axioms).

<div class="note">

<strong>Scope.</strong> The verified, axiom-free corpus now covers both the borrowed
mathematics (Tomita–Takesaki modular theory and Araki = CGP relative entropy, free-field coherent sector) and
the program's own results: the covariant σ-additive <em>consistent</em> Born measure on the record net, the
Born-from-typicality reduction (to a state-supervenience premise, with a no-go), λ's
covariance/contextuality structure, and the <em>metaselector</em> layer — a machine-checked no-go trilogy
(neither capacity, nor symmetry, nor the state Φ selects the record framework) with the positive answer
(einselection, Zurek's commutativity criterion), plus a category-error-proof record/area "contract" resting
on Born-from-projectors. A second, self-contained thread formalizes <strong>emergent gravity</strong> —
Jacobson's "Einstein equation of state" route to the Einstein field equations, with the thermodynamic input
grounded in QIQT-H's own capacity bound, as a <em>conditional</em> axiom-free chain (see below). What it does
<strong>not</strong> establish: the holographic axiom (FQ),
λ's <em>dynamical</em> law, or the continuum (Type III₁); and the gravity thread is conditional on three
clearly-labelled physics inputs (it is <em>not</em> "general relativity from nothing"). It does not close the
<a href="/open-problems">open problems</a>. (The original Macroscopic Definiteness Conjecture is
<a href="/open-problems">retired</a> as a category error, not a pending verification target.)

</div>

## The headline result

The coherent-state Araki relative entropy equals the one-particle Casini–Grillo–Pontello entropy, as a
literal machine-checked derivative theorem:

$$
\frac{d}{dt}\Big|_{0}\,\big\langle\Omega,\ \Delta_{W(f)\Omega\,\mid\,\Omega}^{\,it}\,\Omega\big\rangle = -\,i\,S_{\mathrm{CGP}}(f),
$$

so that

$$
S_{\mathrm{Araki}}\big(\omega_{W(f)\Omega}\,\Vert\,\omega_\Omega\big) = S_{\mathrm{CGP}}(f) \ge 0.
$$

## The free-field modular-energy bound (the honest core of "deriving holography")

A related, self-contained axiom-free development formalizes the **modular-energy bound** — the derivable content
of the JLMS route to the area law. Along *this modular route* the $A/4G$ area term is **not** free-field-derivable
(the free scalar has no Newton constant $G$, no geometric area operator, a scheme-dependent cutoff coefficient, and
the $\delta A/4G = 2\pi\!\int\!\delta T_{kk}$ step needs the Einstein equations) — so *here* the $A/4G$
identification stays a *gravitational input*, not a theorem. (This concerns the JLMS *modular route only*: the
Bekenstein–Hawking $\mathbf{1/4}$ ratio **is** derived — as a machine-checked theorem — but through the separate
**Sakharov / induced-gravity bridge**, `SakharovRatio.sakharov_ratio` (the **P4-MICRO** story) — a re-derivation
of the standard induced-gravity ratio, not unique to finiteness (any local relativistic QFT with the same UV
coefficient yields it); what *neither* derives is the **value of $G$**.) What **is**
machine-checked (`QIQTH/ModularEnergyBound.lean`) is that the
entropy variation is controlled by the modular-energy variation, which under one-particle Bisognano–Wichmann
$K_\sigma = 2\pi B_{\rm boost}$ is the Unruh bound $\Delta S \le 2\pi\,\Delta\langle B_{\rm boost}\rangle$:

| theorem | statement |
| --- | --- |
| `modular_relEnt_identity` | Umegaki: $D(\rho\Vert\sigma) = (\langle K_\sigma\rangle_\rho-\langle K_\sigma\rangle_\sigma) - (S(\rho)-S(\sigma))$, $K_\sigma=-\log\sigma$ |
| `modular_casini_bound` | $S(\rho)-S(\sigma) \le \langle K_\sigma\rangle_\rho-\langle K_\sigma\rangle_\sigma$ (from Klein positivity) |
| `finiteCorner_wedge_Casini_BW` | with $K_\sigma=2\pi K_{\rm boost}+c$ (BW identification, **explicit** hypothesis): $\Delta S \le 2\pi\,\Delta\langle K_{\rm boost}\rangle$ |
| `finiteCorner_firstLaw` | the first law $\delta S = \delta\langle K_\sigma\rangle$ at the reference (relative-entropy stationarity) |
| `finiteCorner_firstLaw_boostEnergy` | the explicit first law $\delta S = 2\pi\,\delta\langle K_{\rm boost}\rangle$ |
| `finiteCorner_wedge_saturation_BW` | **rigidity**: $\Delta S = 2\pi\,\Delta\langle K_{\rm boost}\rangle \iff \rho=\sigma$ (tight only at the reference) |
| `freeField_modularEnergyBound_finiteCorner_BW` | **capstone**: bound $\wedge$ exact deficit $2\pi\Delta\langle K_{\rm boost}\rangle-\Delta S=D(\rho\Vert\sigma)$ $\wedge$ rigidity |

This upgrades the *modular* pieces of the carried `Phase5Master` hypothesis from an assumption to derived
results. It is **formalized modular QFT — not a derivation of the holographic $A/4G$ bound**; the continuum
Type III$_1\!\to$II crossed-product dual-weight trace where $A/4G$ would live remains a multi-year cited frontier.

Relatedly, `InducedNewtonConstant.lean` (the granularity reframing) delivers `G = 1/(N Λ_s²)` — `G` promoted from
carried to derived (the *relation*; the numerical value still needs the species accounting) — and
`HolographicBridge.lean` machine-checks the **correspondence** that, with this induced `G`, the AdS/CFT boundary
Cardy microstate count of a BTZ horizon *equals* QIQT-H's bulk capacity exponent `(A/4)N Λ_s²`
(`btz_cardy_eq_qiqth_capacity`; the AdS radius cancels). This is a *correspondence* (the two holographic
bookkeepings agree under the shared `G`), **not** an import of a boundary CFT, the Cardy formula, or AdS/CFT's
cross-check — QIQT-H's capacity stays postulated/granularity-reframed.

## Emergent gravity: the Einstein equations as a machine-checked equation of state

A second, self-contained axiom-free development formalizes **Jacobson's "Einstein equation of state"** route
to general relativity — with the thermodynamic input now *grounded in QIQT-H* rather than assumed. The result
is a single **conditional** theorem:

> `qiqt_gr_from_wedge_kms` — the **Einstein field equations** $a\,T_{\mu\nu} = G_{\mu\nu} + \Lambda\,g_{\mu\nu}$
> (with a genuine Einstein tensor and a *constant* $\Lambda$) follow from QIQT-H's holographic **capacity bound**
> $S \le \eta A$ together with **Klein positivity** $S(\rho\Vert\sigma)\ge 0$, modulo **exactly three
> clearly-labelled, well-motivated physics inputs**: the wedge **KMS property**, **matter conservation**
> $\nabla^\mu T_{\mu\nu}=0$, and standard **structural regularity**.

What is genuinely *derived* inside the chain (no hypothesis smuggles in the conclusion):

- the **differential area law** $\delta S = \eta\,\delta A$ — from the capacity *bound* + saturation at the
  reference + Klein positivity (no hypothesis asserts $S=\eta A$; the inequality side is QIQT-H's own theorem);
- the **boost-charge** content of input #1 — the wedge modular flow *is* the geometric Lorentz boost
  (one-particle Bisognano–Wichmann), and the boost-energy derivative is purely imaginary, $i\cdot(\text{real})$,
  from the explicit boost generator together with unitarity;
- the **focusing** content of input #3 — at a stationary horizon the Raychaudhuri equation collapses to pure
  Ricci focusing $\,\mathrm{d}\theta/\mathrm{d}\lambda = -R_{kk}$;
- all the **differential geometry** — the Bianchi identities, $\nabla^\mu G_{\mu\nu}=0$, the
  null-cone $\Rightarrow$ tensor step, and the constancy of $\Lambda$.

| theorem | statement |
| --- | --- |
| `qiqt_gr_from_wedge_kms` | $a\,T = G + \Lambda g$ from the QIQT-H capacity bound + Klein, modulo three labelled inputs |
| `differential_area_law_of_relEntropy` | $\delta S = \eta\,\delta A$ derived from the bound + saturation + Klein positivity |
| `oneParticleBW_wedge` | the wedge modular flow equals the geometric Lorentz boost (one-particle Bisognano–Wichmann) |
| `hasDerivAt_inner_boostUnitary_imaginary` | the boost-charge derivative is $i\cdot$(boost energy) — boost generator + unitarity |
| `raychaudhuri_focusing_at_equilibrium` | Raychaudhuri $\Rightarrow \mathrm{d}\theta/\mathrm{d}\lambda=-R_{kk}$ at a stationary horizon |
| `einsteinTensor_divergence_zero` | $\nabla^\mu G_{\mu\nu}=0$ (twice-contracted Bianchi) |
| `jacobson_einstein_equation_of_state` | the null-cone tensor relation $\Rightarrow$ Einstein's equations with constant $\Lambda$ |

### The instantiated showcase — the floor laid bare

The development since has been *drained* further: the chain is now machine-checked for an **explicit free
Klein–Gordon field on a curved pp-wave spacetime**, the one-particle **Bisognano–Wichmann theorem is now a
fully unconditional Lean theorem** (no longer a cited input), matter conservation $\nabla^\mu T_{\mu\nu}=0$ is
*derived* for the KG stress tensor, and the entropy/area *derivatives* are derived from smoothness of the
record law. The capstone of that effort is a single theorem that **discharges every geometric and analytic
premise** and exhibits exactly what GR rests on:

> `qiqt_gr_ppwave_showcase` — the **Einstein field equations** $a\,T_{\mu\nu}=G_{\mu\nu}+\Lambda g_{\mu\nu}$ for
> the explicit **pp-wave** spacetime, with the metric/tetrad, the **area derivative** (Raychaudhuri area-rate,
> via an expansion-free congruence), and the **entropy bound** $S\le\eta A$ (Shannon's maximum at the
> holographic capacity) **all discharged inside the theorem** — leaving as hypotheses *exactly the irreducible
> floor*.

| what the showcase discharges | how |
| --- | --- |
| pp-wave metric + tetrad (symmetry, inverse, smoothness, frame congruence) | the explicit pp-wave geometry |
| `hA` — the area derivative | `area_hasDerivAt_of_covConst`: an expansion-free congruence has zero expansion $\Rightarrow$ constant area |
| `hbound` — the entropy bound $S\le\eta A$ | `shannon_le_log_card`: the area is set to the holographic capacity $\eta\,c=\log\lvert R\rvert$ |

| what it carries — *exactly the floor* | meaning |
| --- | --- |
| `hKG` | the matter **equation of motion** (Klein–Gordon on the pp-wave background) |
| `hcap` ($\eta\,c=\log\lvert R\rvert$) | the **finite-capacity** input (P4-MICRO: *finiteness* is the postulate; the area form $Q_R=A/4\ell_P^2$ is itself *derived* via the Sakharov bridge, and $G$ is carried — or itself *derived* as $G=1/(N\Lambda_s^2)$ under the granularity reframing, `InducedNewtonConstant`) |
| `hS`, `hK` | the **localization map** — the field-coupled record law whose entropy rate equals the stress flux $2\pi/\hbar\cdot T_{kk}$ |

The localization map is **provably not** dischargeable by analysis: at the uniform reference the Shannon
entropy is *stationary* ($\sum p'=0$), so the *value* of the heat rate is forced to be the stress flux — i.e.
the field-coupled record law, the irreducible Gap-2 input. So the showcase is the cleanest honest statement of
the result: **the Einstein equations for the pp-wave spacetime follow from the matter equation of motion + the
holographic capacity (P4) + the localization map** — every geometric, curvature, area-kinematic, and
entropy-bound step machine-checked and discharged.

<div class="note">

<strong>Honest scope — a conditional formalization milestone, not "GR from nothing."</strong> This is a
rigorous, axiom-free, <em>conditional</em> derivation: the chain rests on labelled inputs kept as explicit
hypotheses and <strong>never</strong> as Lean axioms. For the explicit free Klein–Gordon showcase these reduce
to <strong>three</strong>: the matter <strong>equation of motion</strong> (Klein–Gordon on the background), the
holographic <strong>capacity</strong> (P4, $Q_R=A/4\ell_P^2$), and the <strong>localization map</strong> (the
field-coupled record law — Gap 2). The wedge-modular-flow$=$boost story is <em>no longer</em> among them: the
one-particle Bisognano–Wichmann is now a fully unconditional Lean theorem, Raychaudhuri focusing is a theorem,
and matter conservation $\nabla^\mu T_{\mu\nu}=0$ is <em>derived</em> for the KG stress tensor — the modular and
geometric content has been <em>drained into theorems</em> for the free field. (The <em>algebraic</em> wedge-KMS
package — KMS-uniqueness, the strip property, standardness — remains cited rather than formalized only for the
<strong>general interacting</strong> algebra, where a Lean proof would require operator-algebra infrastructure —
unbounded Tomita–Takesaki theory, Hardy-strip methods — that Mathlib does not yet have; a substantial separate
undertaking, not an impossibility.) What QIQT-H supplies as <em>theorems</em> is the inequality side of the area
law; what makes the output <em>general relativity</em> is Jacobson's argument, here machine-checked end to end.
It is a verified <em>formalization</em> result — not a new physical prediction, and it does not by itself
establish that our universe's gravity <em>is</em> emergent.

</div>

## The quantized graviton and the linearized bridge

Two further axiom-free developments (2026-07) extend the substrate from the scalar field to **gravity's own
quantum** and assemble the **entanglement → linearized-Einstein bridge** from machine-checked parts.

### The free graviton, end to end

The linearized graviton is now formalized from kinematics through canonical quantization — standard free-field
physics, machine-checked (every theorem axiom-free, standard 3):

| theorem | statement |
| --- | --- |
| `tt_decomposition` + `polarizations_not_gauge` | the physical polarization space (TT modulo gauge) is **exactly 2-dimensional** — the $D(D-3)/2=2$ count via the explicit gauge quotient |
| `eR_helicity` / `eL_helicity` | the circular polarizations $e_\pm = e_+ \pm i e_\times$ are eigenvectors of rotation with eigenvalue $e^{\mp 2i\theta}$ — **helicity ±2 as explicit eigenvalues** |
| `kUp_null`, `physProj_*` | masslessness $k^2=0$ and the **physical-state projector** (the harmonic-gauge propagator numerator: idempotent, kills gauge and trace, extracts the helicity content) |
| `graviton_null_wave` | null profiles $f(t-z)$ solve the wave equation $\partial_t^2 h = \partial_z^2 h$ — the graviton propagates at $c$ (genuine calculus) |
| `ccr` | canonical quantization: $[a_i, a_j^\dagger]=\delta_{ij}$ for the two helicity modes on the Bargmann–Fock space $\mathbb{C}[X_0,X_1]$ |
| `numberOp_pow`, `hamiltonian_vacuum` | bosonic occupation spectrum $\mathbb{N}$; the Hamiltonian $\omega(N_0+N_1+1)$ with **zero-point energy** $H\lvert 0
angle=\omega\lvert 0
angle$ |
| `helicityOp_plus/minus`, `annih_coherent`, `twoPoint` | one-graviton states carry helicity ±2; coherent states $a\lvertlpha
angle=lpha\lvertlpha
angle$ (the classical bridge); the two-point function $\langle 0ert a_i a_j^\daggerert 0
angle=\delta_{ij}$ (the propagator residue) |

### The bridge: entanglement first law ⟺ linearized Einstein, assembled from real parts

The FGHMVR/Jacobson template (*entanglement first law at every ball ⟺ linearized Einstein*) is assembled in
nine increments — every derived step a theorem, every physical input an **explicit hypothesis** (never a Lean
axiom):

| theorem | statement |
| --- | --- |
| `graviton_solves_linearized_einstein`, `einstein_iff_dispersion` | the quantized graviton's polarization content solves linearized vacuum Einstein — and conversely $\delta G = 0 \Leftrightarrow k^2 = 0$: **Einstein forces light-cone propagation** |
| `bianchi_einsteinSymbol` | the linearized **Bianchi identity** $k^\mu(\delta G)_{\mu
u}=0$, identically |
| `couple_gauge_invariant_iff_conserved` | gauge invariance of the matter coupling $\int h_{\mu
u}T^{\mu
u}$ **⟺** stress-energy conservation |
| `soft_gauge_invariant_iff_ward`, `equivalence_principle` | longitudinal decoupling of the soft graviton ⟺ the Weinberg sum rule; for generic momenta **all couplings equal** — the **equivalence principle** at the algebraic level |
| `boost_flux_unique`, `ball_flux_unique` | the wedge and per-ball Clausius data $\delta\langle K
angle = -\delta S$ are **forced** (given the carried BW/CHM identifications), riding the derived modular flow |
| `chmWeight_edge_slope`, `cke_*` | the CHM ball kernel meets the entangling surface with **unit slope** (the wedge↔ball $2\pi$ consistency) and generates a conformal symmetry (Killing equation by real calculus) |
| `area_probes_separate` | geometric **area probes separate** symmetric perturbations — the separating-family hypothesis of the skeleton becomes a *theorem* |
| `bridge_firstLaw_iff_einstein`, `bridge_conditional` | **the capstone**: given the carried Clausius/area law $\delta S = \delta A/4G$, Iyer–Wald, and BW/CHM, the first law at every probe **⟺** the emergent perturbation satisfies linearized vacuum Einstein |

<div class="note">

<strong>Honest scope.</strong> The graviton development is standard <em>free-field</em> QFT (linearized, flat
background, no interactions), machine-checked — not a claim of quantum gravity. The bridge is a
<em>conditional linearized assembly</em>: the Clausius/area law $\delta S=\delta A/4G$, the Iyer–Wald identity,
the Bisognano–Wichmann/CHM identifications, scattering genericity, and the value of $G$ are carried as explicit
hypotheses. Background independence, the nonlinear completion, and the area law from microstate counting remain
the cited open frontier — the quantum-gravity problem itself.

</div>

### The microtheory earns its gravity (E1–E5)

A follow-on campaign of **joins between held theorems** upgrades the bridge from *assembled* to *earned in-model*
(all axiom-free, standard 3):

| theorem | statement |
| --- | --- |
| `freeFieldWedgePackage`, `freeField_clausius_unconditional` | **BW discharged**: the wedge Clausius datum δ⟨K⟩ = −δS forced with *no external Bisognano–Wichmann premise* (wired from the unconditional one-particle BW theorem; free field) |
| `reconstruct`, `reconstruct_areaVar` | **the metric is a function of the code's own area data** — the explicit decoder h<sub>ii</sub> = 2A(e<sub>i</sub>), h<sub>ij</sub> = A(e<sub>i</sub>+e<sub>j</sub>)−A(e<sub>i</sub>)−A(e<sub>j</sub>) inverts the emergence map (pointwise, basis-level, symmetric sector) |
| `calibrated_entanglement_cut_area_law`, `uniform_realizes_area_law` | **count = induced area / 4G**: with the area *induced* from the calibrated entanglement cut (no separate area label), log #microstates = screenArea/(4G) under the single named calibration log D<sub>e</sub> = w<sub>Ent</sub>(e), realized exactly by the maximum-entropy record |
| `rayFamily_firstLaw`, `code_equilibrium_einstein` | **code equilibrium ⟹ Einstein**: per-ray relative-entropy stationarity forces the first law at every probe, hence linearized vacuum Einstein — Jacobson's equation of state with the state the code's equilibrium (explicit K ↦ −K sign adapter) |
| `gravStress_conserved`, `deser_selfcoupling_consistent` | **the Deser rung**: the graviton's own radiation stress is conserved on-shell (masslessness ⟹ conservation), so its self-coupling is gauge-consistent — bootstrap order one toward nonlinear GR |

<div class="note">

<strong>Honest scope.</strong> Every derived step is a theorem; every physical input is a named carried
hypothesis — the calibration log D<sub>e</sub> = w<sub>Ent</sub>(e) (the physics of the area law), the per-ray
BW/analytic data, Iyer–Wald, and G. The full Deser iteration, the continuum Type II trace, background
independence, and the value of G remain the open walls — this is the strongest in-model statement of emergent
gravity, <em>not</em> quantum gravity.

</div>

### The wall: the Type II dual-weight trace on the crossed-product core (W1–W4)

The Chandrasekaran–Penington–Witten dual-weight trace — the object whose renormalized entropy underlies the
Type II capacity story — constructed on an honest algebraic core with its three defining laws **exact** (all
axiom-free, standard 3):

| theorem | statement |
| --- | --- |
| `dualAction_matter`, `dualAction_clock` | the **Takesaki dual action** θ<sub>s</sub> on the crossed product: fixes the matter π(a), phases the clock θ<sub>s</sub>(λ<sub>t</sub>) = e<sup>ist</sup>λ<sub>t</sub> — the vector-valued Weyl relation |
| `Iexp_dualShift` | the **log-clock density scales exactly**: I<sub>exp</sub>(f(·+s)) = e<sup>−s</sup>·I<sub>exp</sub>(f) — the τ∘θ<sub>s</sub> = e<sup>−s</sup>τ mechanism (density on the log-clock variable, the verifier's binding correction) |
| `zWeight_shift_quasiInvariant`, `zWeight_dualCircle_invariant` | the ℤ-clock regression: the e<sup>−1</sup> scaling belongs to the **shift**; the true dual (circle) action leaves the weight **invariant** — the distinction machine-checked |
| `tauMonomial_dual` | the trace on normal-ordered monomials π(a)λ<sub>t</sub>f(L): **τ₀∘θ<sub>s</sub> = e<sup>−s</sup>·τ₀ exactly**, no regularization |
| `eigen_tau_trace` | **traciality** τ₀(xy) = τ₀(yx): the matter KMS factor e<sup>κ</sup> cancels exactly against the ∫e<sup>x</sup> change of variables — **a KMS state becomes a trace under the log-clock dressing**, the Type II mechanism as a theorem |
| `eigen_tau_star_mul_nonneg` | **positivity** τ₀(x*x) ≥ 0 — the x*x symbol collapses to a pointwise norm-square |
| `phase5_from_core_trace`, `traceCapacity_from_core` | the capacity interfaces **instantiated by the constructed trace**: the JLMS remainder realized as τ₀(r*r), the bound S<sub>ren</sub> ≤ Q proven rather than assumed |

<div class="note">

<strong>Honest scope — the wall is not crossed.</strong> The trace exists with exact laws on the
<em>algebraic core</em>; the matter-side KMS-eigen and positivity inputs are carried (provable for the finite
corner); the von Neumann closure is the carried <code>DualWeightTraceExtension</code> typeclass (normal
weights/affiliated operators — the genuine remaining frontier, a named hypothesis, never an axiom); the
continuum count and black-hole matching remain cited. Not quantum gravity.

</div>

## Index of machine-checked results

For the **exact theorem statements**, machine-translated from the Lean source to readable math
(notation only, content verbatim), see the [**machine-rendered statements**](/statements) page.

Toolchain `leanprover/lean4:v4.30.0` · verified in `QIQTH/AxiomAudit.lean`.

### Finite Araki relative entropy

| theorem | statement |
| --- | --- |
| `arakiEntropy_eq_relEntropy` | $S_{\mathrm{Araki}}(\rho\Vert\sigma)=\operatorname{tr}\rho(\log\rho-\log\sigma)$ (Umegaki) |

### Operator convexity → Lieb's concavity → DPI → strong subadditivity

A complete, axiom-free, finite-dimensional formalization of the Carlen DPI–Lieb tower — operator-convexity
machinery that Mathlib does **not** have — built bottom-up, every result standard-3. This is an
independently-useful contribution to formalized mathematics, and it is what *discharged* the program's former
entropy-interface axioms (Donald, DPI, ArakiInterface, EntropyBridge) outright.

| theorem | statement |
| --- | --- |
| `peierls_inequality` | Peierls (Carlen 2.9): $\sum_j f(B_{jj}) \le \operatorname{tr} f(B)$, convex $f$ |
| `trace_function_convex` | $A \mapsto \operatorname{tr} f(A)$ convex for convex $f$ (2.10) |
| `matrix_sqrt_le_sqrt` | Löwner–Heinz: $0\le A\le B \Rightarrow \sqrt A\le\sqrt B$ |
| `star_inv_subadditive` | Ando's joint convexity of $(A,B)\mapsto B^\ast A^{-1}B$ |
| `gmean_superadditive` | joint concavity of the operator geometric mean $A\#B$ |
| `lieb_superadditive` | **Lieb's concavity theorem** — $(A,B)\mapsto\operatorname{tr}(K^\ast A^{1-t}K\,B^t)$ jointly concave |
| `relEntropy_subadditive` | joint convexity of quantum relative entropy |
| `dpi_mixed_unitary`, `partial_trace_dpi` | the **data-processing inequality** $D(\Phi\rho\Vert\Phi\sigma)\le D(\rho\Vert\sigma)$ |
| `strong_subadditivity` | **strong subadditivity** $S(\rho_{ABC})+S(\rho_B)\le S(\rho_{AB})+S(\rho_{BC})$ |
| `condMutualInfo_nonneg` | conditional mutual information $I(A{:}C\mid B)\ge 0$ |

### Bounded Tomita–Takesaki (standard subspace)

| theorem | statement |
| --- | --- |
| `modConj_rvdRC_modConj` | $JRJ=2-R$ |
| `modConj_rvdT_of_mem_K` | $J(T\xi)=(2-R)\xi$ for $\xi\in\mathcal{K}$ |
| `modUnitary` | $\Delta^{it}$: group law, unitarity, strong continuity |

### One-particle CGP relative entropy

| theorem | statement |
| --- | --- |
| `cgpEntropy` | $S(\xi)=-\!\int\log((2-r)/r)\,d\mu^R_\xi$ |
| `rvdSpec_balance` | the CGP spectral balance |
| `cgpEntropy_nonneg` | $S(\xi)\ge 0$ for localized $\xi\in\mathcal{K}$ |

### Free-field (Fock) modular flow

| theorem | statement |
| --- | --- |
| `secondQuantModFlowH` | $\Gamma(\Delta^{it})$: one-parameter group, vacuum-fixing, strongly continuous on coherent vectors |
| `secondQuantModFlowH_weylH` | $\sigma_t(W(u))=W(\Delta^{it}u)$ |

### Coherent-state relative modular operator and reduction

| theorem | statement |
| --- | --- |
| `relModFlowH` | $\Delta^{it}_{W(f)\Omega\mid\Omega}=W(f)\,\Gamma(\Delta^{it})\,W(f)^{*}$ |
| `connesCocycleH_chain` | $[D\omega_{W(f)\Omega}:D\omega_\Omega]_t=W(f)W(-\Delta^{it}f)$ + chain rule |
| `hasDerivAt_relModFlow_vacuum` | $S_{\mathrm{Araki}}(\omega_{W(f)\Omega}\Vert\omega_\Omega)=S_{\mathrm{CGP}}(f)$ |

### Free-field Born measure & decoherent-histories consistency

A genuine (non-deterministic) Born probability measure on the continuum free field, its Lorentz-covariance,
and the decoherent-histories *consistency* (sum-rule) conditions. Born is the **input** weight
$\mu_\Phi(\alpha)=\lVert C_\alpha\Phi\rVert^2$; these theorems establish that it is a *consistent*,
$\sigma$-additive, covariant probability — not a derivation of Born.

| theorem | statement |
| --- | --- |
| `weylBit_typicalityMeasure_exists` | a $\sigma$-additive Born probability measure $\mu_\infty$ exists (finite-fiber Kolmogorov extension; the finiteness is the capacity bound) |
| `weylBit_typicality_lorentzBoost_invariant` | $\mu_\infty$ is the same in every Lorentz frame (covariant *as a law*) |
| `weak_decoherence_bit` | $\mathrm{Re}\,D(\alpha,\beta)=0$ — weak decoherence / consistency (the Born sum-rule condition), exact |
| `weak_decoherence_context` | the same for every single-bit coarse-graining: the whole projective family is a consistent set |
| `bell_two_bit_strong_decoherence` | for orthogonal records $\langle u,v\rangle=0$, full $D=0$ (incl. the maximally-different Bell pair) |
| `bitOp_vac_expVec_cross_eq` | exact overlap correction $\tfrac12 e^{-\lVert v\rVert^2/2}\sinh\langle v,w\rangle$; vanishes iff $\langle v,w\rangle=0$ |
| `strong_decoherence_needs_orthogonality` | witnessed countermodel: overlapping records are *not* strongly decoherent |
| `offdiagonal_tendsto_zero` | SBS / Quantum-Darwinism: redundancy $N\to\infty$ drives the joint off-diagonal $\to 0$ |
| `realm_unique_of_einselection` | given the einselected pointer family the realm is unique… |
| `capacity_underdetermines_realm` | …but capacity *alone* does not pin it (a no-go: distinct capacity-maximal realms) |

### The metaselector — what fixes the record framework

The choice of abelian record framework $\{P_\alpha\}$ resolved as a **no-go trilogy** (neither capacity, nor
symmetry, nor the state $\Phi$ selects it) **plus a positive selector** (einselection), with a
category-error-proof record/area "contract." Verified scaffold, not new physics: $\lambda$ stays inert, so the
scheme remains operationally Everett (an ontological reading, with no formal-content claim attached).

| theorem | statement |
| --- | --- |
| `SymmetryNoGo.unitary_invariant_score_constant` | the unitary group acts **transitively** on frameworks (orthonormal bases), so any unitarily-invariant typicality score is constant — symmetry selects *no* framework |
| `StateAloneNoGo.state_records_trivial` | a single projection $P=\lvert\Phi\rangle\langle\Phi\rvert$ generates only the trivial framework $\{0,P,1-P,1\}$ — the state alone selects nothing finer (Bub–Clifton) |
| `MetaselectorSelection.pointer_commutes` | Zurek's criterion: a record commuting with the monitored $A$ commutes with the interaction $A\otimes B$ — einselected (decoherence-free) |
| `MetaselectorSelection.pointer_invariant` | an $A$-eigenstate stays a *product* under the $A\otimes B$ coupling: pointer states do not decohere |
| `BornProjBridge.bornRecordLaw` | Born-from-projectors: for a finite orthogonal PVM and normalized $\Phi$, $\mu(r)=\lVert P_r\Phi\rVert^2=\langle\Phi,P_r\Phi\rangle$ is a genuine record law |
| `RecordContract.shannon_le_log_card` | the record information bound $H(R)\le\log\lvert R\rvert$ (Jensen) — the entropy/capacity bridges thread the postulated Bousso bound |
| `MetaselectorSelection.finite_budget_forces_overlap` | a $D$-dim record space cannot hold $M>D$ orthonormal records — a finite holographic budget forces a residual-interference floor |

<div class="note">

<strong>Terminology (Gell-Mann–Hartle).</strong> <em>Re D = 0</em> is <em>weak</em>
decoherence / consistency (it is what makes the Born weights obey the probability sum rules); full
<em>D = 0</em> is <em>medium</em>, and with orthogonal record states also <em>strong</em>. The Weyl-bit
operators <em>A(u,s) = (I + sW(u))/2</em> are <em>effects</em>, not projectors, so this is a
generalized-measurement history; the projector/Boolean-record content is separate. These are exact algebraic
consistency results for the free/coherent sector — not a proof of macroscopic classicality.

</div>

### Born from typicality — the symmetry / state-supervenience reduction

The Born weights reduced from typicality to a single state-supervenience premise (with a no-go that *some*
premise is unavoidable). Born is **input**, not derived; these establish what it reduces to.

| theorem | statement |
| --- | --- |
| `RedundancyCompressible.card_redundantCodewords` | $R$ redundant copies of a record are distinguishable in $\lvert X\rvert$ ways, not $\lvert X\rvert^R$ — redundancy is compressible (the category-error core) |
| `RedundancyCompressible.naive_overcounts` | the naive $R\log\lvert X\rvert$ strictly exceeds the true $\log\lvert X\rvert$ |
| `EnvarianceJustification.envariance_swap_invariant` | the system swap, undone by the environment counter-swap, fixes the state **iff** the swapped amplitudes are equal (Zurek envariance, *proved* not assumed) |
| `BornEquiprobable.born_from_equiprobability` | for an equal-amplitude orthonormal fine-graining, the Born weight $=$ the equiprobable branch-count fraction (the amplitude→count bridge) |
| `StateSupervenience.NaturalTypicality.envariance_equiprob` | naturality $+$ a state-fixing symmetry $\Rightarrow$ equal-amplitude outcomes are equiprobable |

### λ's selection schema: covariance & contextuality (OP3b)

| theorem | statement |
| --- | --- |
| `CovariantGluing.no_covariant_selector` | no equivariant $\Phi\mapsto\lambda$ selector when the symmetric state's histories form a nontrivial orbit (the S² obstruction) — so $\lambda$ is a symmetry-breaking *sample* of the covariant law, not a covariant function |
| `ContextualitySafe.contextuality_safe` | a quantum/record correlation $>2$ (Tsirelson) has **no** global value-map — assigning values only to the actual context is forced |
| `Fock.bell_no_signaling_state` | no-signaling is **state-independent**: for *any* (entangled) global state, summing Bob's record outcome leaves Alice's marginal independent of Bob's setting |

### λ's selection schema: the finite Takesaki criterion + modular invariance

The finite (Type I) shadow of λ's kinematic-and-dynamical law. λ is **Type-III-native** — the records it selects
come from a chosen abelian *pointer* subalgebra 𝔄 (which exists already inside a Type III₁ factor), and the
Born weights are the algebraic state value $\omega(P_\alpha)$, needing no trace. These theorems make precise
*which* 𝔄 is consistent, that the decoherence map is the conditional expectation onto it, and that the
selection is stable under the modular dynamics.

| theorem | statement |
| --- | --- |
| `LambdaPointer.modAut_fixes_iff_commute` | **Takesaki criterion**: the modular flow fixes a pointer projection $\sigma(P)=P$ **iff** $[\rho,P]=0$ — i.e. iff the state has no coherence between pointer sectors (exact decoherence selects 𝔄) |
| `LambdaPointer.bornWeights_sum` | the algebraic Born weights $\omega(P_\alpha)=\operatorname{tr}(\rho P_\alpha)$ of a resolution of unity sum to $\operatorname{tr}\rho$ — a genuine probability |
| `LambdaPointer.dephase_preserves_state` | the decoherence map $E(x)=\sum_\alpha P_\alpha x P_\alpha$ is the unital, $\omega$-preserving **conditional expectation** onto 𝔄 (exactly when the criterion holds) |
| `LambdaPointer.dephase_sigmaDiag_commute` | **modular-invariance, $\forall t$**: $E$ commutes with the real-time modular flow $\sigma_t(x)=\rho^{it}x\rho^{-it}$ — a consistency fact (the modular flow is *not* physical time, so this is not physical no-recoherence) |
| `LambdaPointer.dephase_sigmaDiag_commute_diagonal` | in the einselected (density-eigenbasis) pointer basis the modular-invariance is **unconditional** for all $t$ |
| `LambdaPointer.modAut_fixes_pointer` / `bornWeight_modAut_invariant` | each selected record is a **fixed point** of the flow, and the Born weights are **constants of the modular motion** |
| `SelectionEvent.selects_exists_unique` | the **selection event**: an inverse-CDF selector from an actuality seed $s\in[0,1)$ picks **exactly one** record per seed (totality + uniqueness — single-world consistency) |
| `SelectionEvent.volume_selects` | the uniform seed measure of record $k$ equals its Born weight $p_k$ — the *single-shot* seed measure of record $k$ = its Born weight $p_k$ (the seed is λ; an across-run *frequency* needs the separate LLN; the selector is order-dependent, not equivariant, as the no-covariant-selector result requires) |

### λ's selection schema in the continuum (free-field / standard-subspace sector)

The finite schema above, lifted onto the **genuine continuum modular flow** $\Delta^{it}$ (the Rieffel–Van Daele
bounded `modUnitary` of a standard subspace) — axiom-free. The local algebra's Type III₁-ness (Buchholz–Wichmann)
is cited; the residual walls are the Haagerup natural-cone existence in Mathlib and the interacting case.

| theorem | statement |
| --- | --- |
| `ContinuumLambda.modAutOp_add` / `_mul` / `_star` | the modular automorphism $\sigma_t=\mathrm{Ad}(\Delta^{it})$ is a one-parameter group of unital $\star$-automorphisms |
| `ContinuumLambda.modAutOp_fixes_iff_commute` | **continuum Takesaki criterion**: $\sigma_t(A)=A \Leftrightarrow A$ commutes with $\Delta^{it}$ |
| `ContinuumLambda.dephaseOp_specProj_commute` | **continuum modular-invariance**: the decoherence map commutes with $\sigma_t$ for **every $t$** (unconditional for spectral pointer projections) — a consistency fact, *not* physical persistence (modular flow ≠ physical time) |
| `NaturalConeBorn.bornWeights_sum` | the **Type-independent algebraic Born rule**: the scalar spectral measure of a finite pointer partition sums to $\lVert\xi\rVert^2$ (a genuine probability, no trace) |
| `ContinuumSelection.continuum_selects_exists_unique` | the **Type-blind selection event**: exactly one record per actuality seed, driven by the continuum Born weights |
| `ContinuumSelection.continuum_volume_selects` | the uniform seed measure of record $k$ equals its continuum Born weight — the *single-shot* seed measure = its continuum Born weight (across-run frequency needs the separate LLN) |

And the **whole schema lifted to the second-quantized free field**: $\Gamma(\Delta^{it})$ as a unitary one-parameter
group of bounded operators on the Fock Hilbert space, with the field-level automorphism, modular-invariance, Born rule
(on the genuine Fock vacuum state) and selection event.

| theorem | statement |
| --- | --- |
| `secondQuantModCLM_unitary` | $\Gamma(\Delta^{it})$ is **unitary** on the Fock Hilbert space ($\Gamma^\star=\Gamma(-t)$) — the free-field modular unitary group |
| `dephaseFock_modAutFock_commute` | **field-level modular-invariance**: the decoherence map commutes with $\sigma_t=\mathrm{Ad}(\Gamma(\Delta^{it}))$ for every $t$ (a consistency fact, not physical persistence) |
| `vacuumState_povm_sum` / `vacuumState_weylBit_sum` | **field-level Born rule**: vacuum-state weights of a POVM are a probability; the Weyl-bit record gives $(1\pm e^{-\lVert u\rVert^2/2})/2$ |
| `field_selects_exists_unique` / `field_volume_selects` | the **free-field selection event**: exactly one Weyl-bit record per actuality seed, single-shot seed-measure = the Fock-vacuum-state Born weight |

<div class="note">

<strong>What these add (and don't).</strong> They pin down λ's <em>selection schema</em>, not a
law: Born reduces to state-supervenience (not capacity, not a counting rule); the covariance + contextuality
structure is verified (covariant measure, no covariant point-selector; no global value-map; state-independent
no-signaling — operationally weaker than Bell local causality); the Takesaki criterion fixes which record
context is consistent; and the dephasing map is <em>modular-invariant</em>. That last is a consistency fact,
<strong>not</strong> physical persistence — the modular flow is not the physical Hamiltonian evolution. The
inverse-CDF selection is a sampling representation (single-shot seed-measure = Born weight), <em>not</em> a
mechanism or an across-run frequency. So the single outcome is λ's by stipulation; the holographic bound is the
finite record <em>stage</em> only; and the scheme is operationally equivalent to standard QM. The honest
residual: the seed's <em>origin</em> (a primitive), an across-run <em>frequency</em> theorem, a <em>global
decoherent-history</em> selector, and the continuum walls (Haagerup natural-cone existence; interacting case).

</div>

## The joins — hypothesis deletion (J1–J4)

A dedicated campaign shrinking the carried inputs of the landed results by connecting held theorems. The
ledger, entry by entry (each says which named hypothesis became a theorem or shrank):

- **J1 — the finite corner discharges the eigen-core matter inputs** (`finiteCorner_tau_trace`,
  `finiteCorner_tau_pos`): the constructed Type II trace's traciality and positivity hold on the concrete
  corner (ρ = diag p, matrix units, κ<sub>ij</sub> = log p<sub>i</sub> − log p<sub>j</sub>) with **no matter
  hypotheses** — the KMS-eigen law, frequency conservation (automatic from the matrix-unit index loop) and
  positivity are theorems. *Deleted (for this model): hkms, hfreq, hpos.*
- **J2 — the CHM kernel probe + bridge refactor** (`chmRadialMass3_eq` = 4πR⁴/15,
  `CHMSymbolProbe3_eq`, `bridge_conditional_probe`): the mass-normalized CHM kernel pairing **equals** the
  ray area probe (one-variable calculus), and the bridge consumes the derivable probe. *The Iyer–Wald input
  factors; the residual is one stated identification (`hDeficit`).*
- **J3 — the abstract CHM transport theorem** (`hCHM_of_conformal_transport`, `toBallModularFamily`): the
  per-ball CHM identification is a theorem of ONE carried massless wedge-BW datum + conformal conjugacy +
  the modular transport in its weakest form (the m &gt; 0 BW theorem is never instantiated at m = 0).
  *hCHM (per-ball physics) shrunk to a wedge datum + functoriality + geometry — and the functoriality (`hmodVac`) has since been DELETED by the grounding campaign below.*
- **J4 — the formal Deser system** (`next_source_conserved`, `extend_of_solver`, `einsteinDeserSystem`):
  all-order consistency **propagation** — the next source's conservation is *derived* from a solving tower
  (harmonics at their correct momenta n·k; the Bianchi identity proven at every harmonic); no tower positing
  conservation per order. *Order 2 stays the concrete Deser theorem; nonlinear coefficients = frontier.*

## The Lorentz stress-test gates (CPSUV → diamond tip → state level)

Three falsification gates on the finite-capacity postulate itself — numerics validated against closed
forms, the decisive constants and limits machine-checked (`QIQTH/QG/CpsuvGate.lean`,
`LatticeDispersionBound.lean`, `DiamondTipGate.lean`, `StateLevelLVGate.lean`;
scripts `lorentz_stress_test.py`, `diamond_tip_test.py`; results docs under `docs/qg_roadmap/`).

- **Gate 1 — CPSUV.** A preferred-frame spatial cutoff in interacting Yukawa theory generates the one-loop
  speed splitting Δc² → g²/12π² — an **unsuppressed constant** (`cpsuv_gate_sharp_fails`: the closed form's
  nonzero limit is a Lean theorem; quadrature matched to 2·10⁻¹⁸); any O(4)-invariant regulator gives
  Δc² = 0 by symmetry (`covariantSplit_eq_zero`). *The naive mode-cutoff reading of finite capacity is
  falsified; the free-field lattice pass (|E<sub>a</sub>² − (m²+p²)| ≤ a²p⁴/12, also a theorem) is
  certified NOT decisive.*
- **Gate 2 — the diamond tip.** A causal diamond's tip vector u<sup>μ</sup><sub>D</sub> **does** reach the
  effective action: within the anisotropic family the splitting vanishes **iff** the regulator is isotropic
  (`tipSplit_eq_zero_iff`), with first-order sensitivity −2C ≠ 0; and the rapidity-average escape fails
  provably — the boost-averaged cutoff's null channel equals W/12 exactly (`boostAvg_log_channel`,
  `boostAvg_diverges`): linear growth, not a regulator. *There is no local Lorentz-invariant
  finite-capacity cutoff; frame-averaging cannot manufacture one.*
- **Gate 3 — the state level.** The surviving reading — Q<sub>D</sub> bounds the **entropy of the diamond
  algebra in the covariant vacuum** — makes **no low-energy LV prediction**: the admissible set is
  frame-free (`admissible_smul_iff`, `constraintSet_invariant`), the constraint touches no propagator
  (`stateLevel_noDeltaC2`: Δc² = 0 identically), and the only reopening channels are named theorems —
  non-invariant prepared states (`operationalLV_iff_not_invariant`), background-selecting saturation
  (`conditioned_invariant_iff_orbit_constant`), a **non-equivariant enforcement mechanism**
  (`equivariant_enforcement_preserves_invariance`), or a biased selector (closed by the held
  `upvm_covariant_probability`). Genuine finite instance: `permutationCapacity`.

<div class="note">

<strong>The arc's verdict, honestly.</strong> Every <em>regulator</em> reading of Q<sub>R</sub> = A/4ℓ<sub>P</sub>²
is dead — pixels pick a frame, diamond clocks leak, and averaging over the noncompact boost family is not a
regulator. The <em>entropy</em> reading is provably frame-free and is exactly what the Lean core already
formalizes (capacity = entropy, not a count). The <strong>dynamical-realization gap</strong> — what physical
mechanism enforces the bound — is now also the <em>sole remaining Lorentz door</em>: LV re-enters iff the
enforcer is non-equivariant. Consistent with the covariant-entropy-bound literature (Bousso, Casini, QNEC).
The loop integrals are numerically validated (closed forms to ≤0.16%), not formalized; NOT quantum gravity.

</div>

## The operator emergence map — "graviton = quantized area fluctuation," theorem-shaped (Q1–Q5)

The classical area→metric decoder promoted to an **operator map** on the polynomial Bargmann–Fock carrier
(`Module.End` of ℂ[X₀,X₁]; the completion is never used as an operator domain). Two honesty rules are
machine-enforced by design: equal-time quantized areas **commute** (the naive noncommutativity claim was cut
at consult time), and the finite code can never carry exact CCR (the trace obstruction) — the code join is
expectation-level, permanently.

- **Q1 — `reconstruct_hHat`**: the decoder inverts the QUANTIZED area map at operator level — the metric
  operator ĥ is a function of its own area-fluctuation observables, entrywise in End(Fock).
- **Q2 — `comm_area_mom`, `vacuum_area_pair`**: the honest quantum structure — the canonical pair
  [Â(Σ), Π̂(Σ′)] = i·areaPair·1 and the vacuum fluctuation ⟨0|Â(Σ)Â(Σ′)|0⟩ = areaPair(Σ,Σ′);
  equal-time areas commute (`comm_area_area = 0`).
- **Q3 — `coherent_hHat`, `coherent_area`**: the **classical bridge is the coherent shadow** —
  ⟨α|ĥ|α⟩ = h(α) = Σ<sub>λ</sub> 2Re(α<sub>λ</sub>)·pol<sup>λ</sup> and ⟨α|Â(Σ)|α⟩ = δA<sub>Σ</sub>(h(α)):
  exactly the δA input the assembled first-law ⟺ Einstein skeleton consumes.
- **Q4 — `heis_q`, `hHatT_wave`, `comm_areaT`**: the Heisenberg flow **derived** from the explicit monomial
  scaling (no Stone theorem), the operator **wave equation** ḧ + ω²ĥ = 0 (coefficientwise), and the
  time-separated area commutator 2i·sin(ω(s−t))·areaPair·1 — the causal structure of quantized areas.
- **Q5 — `code_count_eq_fock_area_expect`** (THE JOIN): with the held calibration and ONE named carried
  input `hJoin` (induced screen area = coherent total-area expectation, Â<sub>tot</sub> = A₀·1 + Â),
  **log #microstates = ⟨α|Â<sub>tot</sub>(Σ)|α⟩ / 4G** — the screen code's counting and the graviton's
  area operator agree as two computations of one number.

<div class="note">

<strong>Honest scope.</strong> The carried residue is three named inputs: <code>hJoin</code> (the
emergence-map identification, stated once), the calibration log D<sub>e</sub> = w<sub>Ent</sub>(e), and the
Bargmann-adjointness grounding of the coherent v-rule. The code Hilbert space is <strong>not</strong> Fock
and never will be (the CCR-isometry obstruction is a theorem-level fact); fixed momentum, two polarizations,
linearized, free. NOT quantum gravity — the genuine microstate count (deriving the calibration via the
Type II trace) and the von Neumann closure remain the frontier.

</div>

## The grounding campaign — carried hinges deleted at once (G1–G5)

Two files, four increments; every deletion names its residue.

- **G1 — the Bargmann adjointness** (`bargmann_adjoint`, `coeffFamilyPair_cohCoeff`, `cohPair_X_mul`):
  creation is adjoint to annihilation on the polynomial Bargmann–Fock space
  (⟨p, X<sub>l</sub>·q⟩<sub>B</sub> = ⟨∂<sub>l</sub>p, q⟩<sub>B</sub>), with the coherent reproducing rule
  ⟨coh α, p⟩<sub>B</sub> = p(ᾱ). *The operator-emergence coherent v-rule — previously cited — is now a
  polynomial-level theorem; the completion-level identification stays cited.*
- **G2 — the RvD operator transports** (`rvdRC_transport`): R<sub>S′</sub> = U R<sub>S</sub> U⁻¹ from
  orthogonal-projection uniqueness under the ℝ-isometry; i𝒦 transports automatically by ℂ-linearity.
- **G3 — the unitary covariance of the spectral theorem and Borel calculus** (`cfc_conjU`,
  `specMeasure_conjU`, `specProj_conjU`, **`borelFC_conjU`**): the continuous calculus, the Riesz–Markov
  scalar measures (as pushforwards, with Tietze-extended ambient tests), the spectral projections, and the
  bounded Borel calculus — f(UTU⁻¹) = U·(f∘e)(T)·U⁻¹ — all transport. *New spectral-tower infrastructure,
  independent of this campaign's payoffs.*
- **G4 — the modular flow transports; three payoffs** (`modUnitary_transport`): Δ<sup>it</sup> conjugates
  under carrier conjugacy. **J3's `hmodVac` carried field is DELETED** (the ball-transport package builds
  from geometric carrier conjugacy alone — residue: the geometry + the massless wedge BW); **Gate 3's
  covariance hinge is fed by the derived `modUnitary_inner_cov`**; **the ball-Clausius per-ball modular
  input is replaced by per-ball geometry**.

<div class="note">

<strong>The honest ledger after this campaign.</strong> Of the named carried inputs across the landed
results, the following remain: <code>hJoin</code> + the calibration (the emergence-map identifications —
deletable only by the genuine count via the vN closure), the massless wedge BW, the nonlinear Einstein
coefficients, symbol-level Iyer–Wald (<code>hDeficit</code>), and the geometric carrier-conjugacy data.
Everything else that was carried at the start of the joins/grounding arc is now a theorem. NOT quantum
gravity; the von Neumann closure and the count remain the frontier. <em>(Two later campaigns moved this
ledger: the keystone delivered the count in the finite branch — the calibration is a theorem there for
trace-defined weights — and the join instance below then deleted <code>hJoin</code> itself by
construction, merging the code and graviton towers at the finite level; the vN closure and the continuum
limit remain the named walls.)</em>

</div>

## The keystone — THE COUNT (K0–K6): the holographic count as a theorem in the finite branch

The campaign derives, rather than posits, that a diamond/screen algebra's entropy against the
**constructed** crossed-product trace τ₀ equals induced area/4G — deleting, in the finite branch, the
Clausius input, the geometric input, the calibration log D<sub>e</sub> = w<sub>Ent</sub>(e), and the
emergence join at once (`QIQTH/Keystone.lean`, `KeystoneOperator.lean`; axiom-free, std-3).

- **K0 — the entropy substrate** (`vonNeumannEntropy_maxMixed`, `vonNeumannEntropy_le_log_card`):
  S(maximally mixed) = log N against the UNNORMALIZED counting trace, with the Gibbs/Jensen guard
  S(ρ) ≤ log N for *every* density — the count equality is claimed only where it holds.
- **K2a — the standalone finite count** (`K2a_count_capstone`): link dimensions D<sub>e</sub>, microstates
  N<sub>C</sub> = Π D<sub>e</sub>, the diamond matrix algebra with τ(**1**) = N<sub>C</sub>, record
  projections with τ(P<sub>R</sub>) = |R| (the trace COUNTS records), and
  S = Σ<sub>e</sub> log D<sub>e</sub> = A<sub>τ</sub>(C)/4G as a theorem — G entering only through the
  normalization. The boundary is itself a theorem: `count_matches_external_weights_iff` — matching
  EXTERNAL geometric weights *is* the old calibration, never counted as deleted.
- **K2b — THE COUNT IN THE HELD CORE** (`tauMonomial_uniform_eq_tauCount`, `wEntTau_eq_log_tau0Dim`,
  `K2b_tau0_capstone`): **the counting trace IS the restriction of the constructed crossed-product trace
  τ₀** — the held monomial-trace formula at the uniform matter state and a mass-N<sub>C</sub> clock window
  reproduces Tr x exactly, so the count is not a new postulate; and **the calibration is a theorem**
  because the weight is trace-defined (the link weight IS the log of the link fiber's τ₀-dimension).
  Capstone: S(record corner) = log dim<sub>τ₀</sub>(𝒟<sub>C</sub>) = A<sub>τ</sub>(C)/4G.
- **K5 — the covariance checks** (`tauCount_conj`, `K5_dual_covariant_count`): trace-preserving code
  unitaries preserve the count; the dual action SCALES it exactly — S(θ<sub>s</sub>·) = S(·) − s, the
  honest transported-area covariance law (never naive invariance).
- **K1 — the operator packaging** (`clockMul`, `clockTransl_clockMul`, `repMonomial`): bounded-symbol
  clock multiplication operators on L²(ℝ; H), the product law, the **Weyl covariance**
  λ<sub>t</sub>∘M<sub>g</sub> = M<sub>g(·+t)</sub>∘λ<sub>t</sub>, and the represented core monomial
  π(a)·λ<sub>t</sub>·M<sub>F</sub> as a genuine continuous operator.
- **K3 — finite closure hygiene + a soundness find** (`tauCount_norm_le_sum_diag`): the counting trace is
  bounded on the finite corner; and the carried vN-extension interface (`DualWeightTraceExtension`) was
  found VACUOUS — an abelian collapse witness (M = ℂ) satisfied it for any algebra — and strengthened
  with a multiplicative-embedding requirement that provably kills the witness. No fake finite instance
  was shipped; the genuine σ-weak/normal-weight extension stays a named wall, now carried non-vacuously.

<div class="note">

<strong>The K6 checkpoint — the two honest sentences.</strong> HAVE: "every finite code screen realized
as a finite record corner of the constructed crossed-product core has
S<sub>τ₀</sub> = log dim<sub>τ₀</sub>(𝒟<sub>C</sub>) = Σ<sub>e</sub> log dim<sub>τ₀</sub>(P<sub>e</sub>)
= A<sub>τ</sub>(C)/4G; in the code instance dim<sub>τ₀</sub>(P<sub>e</sub>) = D<sub>e</sub>, so the
calibration is a theorem (trace-defined weight) and the count-built area operator gives the join by
construction — no hClausius/hGeom/hCalib/hJoin carried in this branch." HAVE NOT (Walls 1–5, named):
continuum QFT diamond algebras ARE these corners; external geometric area = count-built area;
Type III₁/II<sub>∞</sub> continuum structure in Lean; σ-weak/normal weights; the value of G.
NOT quantum gravity solved; no wall crossed.

</div>

## The join instance — `hJoin` deleted by construction (JI1–JI7): the two towers merged

The screen-code tower (the keystone count) and the graviton tower (Q1–Q5) joined into ONE object at the
finite level: the dictionary instance — links = screen elements, code weights defined FROM the geometry —
makes the Q5 carried hypothesis `hJoin` a **theorem** (`QIQTH/JoinInstance.lean`; axiom-free, std-3).
Two-level construction per the consult verdict: generic-exact with REAL trace-dimensions; integer codes
only under a named realizability datum.

- **JI1 — the local area decomposition** (`sum_localArea`, `A0Split`): the per-element shares
  β<sub>a</sub> + δA<sub>a</sub> reassemble A₀ + δA<sub>Σ</sub>(h), with the background apportionment
  carried as NAMED data (no canonical per-link split of a global constant exists; the uniform split is
  an optional policy, never pretended-derived).
- **JI2 — the carried `hJoin` is a THEOREM** (`hJoin_tau`, `hcal_tau`): with
  w<sub>Ent</sub>(a) := A<sup>loc</sup><sub>a</sub>/4G and D<sup>τ</sup><sub>a</sub> := e<sup>w</sup> (a
  positive REAL — trace-dimensions need not be integers), the exact Q5 hypothesis shape is supplied by
  construction, and the calibration is `Real.log_exp`. Geometry → code: no smuggling.
- **JI3 — the dictionary lives in the held core** (`exists_tau0_corner_of_posReal`): every positive real
  is a *realized* τ₀ corner value with the clock-window witness explicit (the free window mass — never
  subcorners of one fixed fiber+window, which are provably rank-quantized).
- **JI4 — the generic exact replacement** (`Stau_eq_area_over_4G`): the instance's count
  S<sub>τ</sub>(J) = Σ<sub>a</sub> w<sub>Ent</sub>(a) = A<sub>J</sub>/4G for ARBITRARY graviton data —
  count and geometry as two computations of one number, nothing carried.
- **JI5 — the old Q5 capstone with NO `hJoin` hypothesis**
  (`code_count_eq_fock_area_expect_noJoin`): for a nat-realizable geometry (`NatRealizable` — the named
  integer-dimension datum, where D<sup>τ</sup><sub>a</sub> = D<sub>a</sub>),
  log #microstates = ⟨α|Â<sub>tot</sub>(Σ)|α⟩/4G with the join supplied by `hJoin_tau`.
- **JI6 — the two normalizations are one formula** (`Stau_eq_capacity_primitives`): with the DERIVED
  G = 1/(N·Λ<sub>s</sub>²), the count is S<sub>τ</sub>(J) = (A<sub>J</sub>/4)·N·Λ<sub>s</sub>² — the
  count-built and induced-Newton normalizations meet in {area, species, granularity}; per-link capacity,
  the patch bound, and the area costs: **one nat of link entropy costs 4/(N·Λ<sub>s</sub>²) of area; one
  qubit costs 4·log 2/(N·Λ<sub>s</sub>²)**.

<div class="note">

<strong>The JI7 checkpoint — the two honest sentences.</strong> HAVE: "after JI1–JI6, <code>hJoin</code>
is no longer a hypothesis for the constructed τ join or for nat-realizable finite-code joins, and the
count normalization rewrites to (A<sub>J</sub>/4)·N·Λ<sub>s</sub>² with local capacity corollaries."
HAVE NOT: "no theorem says arbitrary external real geometry has exact natural link dimensions, no
asymptotic approximation is included, and no canonical A₀ split is asserted beyond the named
apportionment data/policy." The CCR-isometry obstruction is permanent (the join is expectation-level
forever); NOT quantum gravity solved; no wall crossed.

</div>

## The embedding — the truncated field diamond IS a counted record corner (EM1–EM7): the finite-level bridge closed

The matter-side dictionary. The key observation is definitional: the keystone's microstate space
`Micro = Π_k Fin(D_k)` IS a multi-mode truncated Fock basis (joint occupation numbers
n<sub>k</sub> &lt; D<sub>k</sub>) — no new Hilbert space is built; the campaign gives the
already-counted diamond algebra its FIELD structure and the mode↔link semantics
(`QIQTH/Embedding.lean`; axiom-free, std-3). With THE COUNT, THE JOIN INSTANCE, and THE EMBEDDING
complete, the finite-level bridge is closed end to end: a truncated free field in a diamond IS a
counted record corner, its records ARE occupation pointer states, its count IS the area over 4G, and
that same number IS the graviton's coherent area expectation — one object, one theorem chain.

- **EM1 — the dictionary** (`ModeAssignment`, `truncated_field_diamond_entropy`): a LINK IS A FIELD
  MODE (dimension = truncation cutoff, named finite data); the keystone count reads verbatim as the
  truncated field diamond's entropy S = Σ<sub>k</sub> log D<sub>k</sub> = A<sub>τ</sub>(C)/4G.
- **EM2 — the coordinate embedding** (`modeOp` + transport package): direct-entry (A on fiber k,
  delta elsewhere — never Kronecker), unital/additive/multiplicative/⋆/injective via a reusable
  fiber-sum lemma — each single-mode oscillator algebra genuinely embeds.
- **EM3 — the per-mode oscillators** (`mode_ladder_commutator`): the HONEST transported defect
  [a<sub>k</sub>, a<sub>k</sub>†] = 1 − D<sub>k</sub>·P<sub>top,k</sub> (exact CCR permanently
  impossible — stated, not hidden); the finite spectrum reading; [N<sub>k</sub>, a<sub>k</sub>] =
  −a<sub>k</sub>.
- **EM4 — the cross-mode algebra** (`modeOp_commute_of_ne`): ONE generic theorem, all cross
  commutators as corollaries — the bosonic sector (fermionic CAR needs the held graded layer).
- **EM5 — records** (`recordProj_eq_sum_occupationProj`, `encoded_mode_ladder_commutator`):
  RECORDS ARE OCCUPATION POINTER-BASIS SUBSETS as a theorem (welding the record ontology to the
  field ontology); the record trace through the constructed τ₀; corner transport with the honest
  unit P = VVᴴ, never the ambient 1.
- **EM6 — capacity** (`field_entropy_le_area_of_capacity`): CAPACITY IS A CONSTRAINT, NOT A
  GENERATOR — Σ log D<sub>k</sub> ≤ A/4G selects admissible assignments and implies S ≤ A/4G;
  each mode occupies 4G·log D<sub>k</sub> of area; ≤ A/(4G·log 2) two-level modes per diamond.
- **EM7 — the capstone** (`truncated_field_count_eq_fock_area_expect_noJoin`): **the finite-level
  bridge end to end** — log #(truncated Fock basis) = ⟨α|Â<sub>tot</sub>(Σ)|α⟩/(4G), composing
  field → corner → count → area → graviton on ONE object with no join hypothesis;
  `LocalizedModeFrame` certifies (never constructs) localization.

<div class="note">

<strong>The EM7 checkpoint — the two honest sentences.</strong> HAVE: "the N-mode truncated
free-field diamond algebra IS a counted record corner — the occupation basis is Micro, the per-mode
truncated oscillators embed with their honest defect ([a,a†] = 1 − D·P<sub>top</sub>), records are
occupation projectors, the count S = Σ log D<sub>k</sub> = A/4G reads as the truncated field
diamond's entropy, capacity bounds/saturates the cutoffs as a constraint, and the mode dictionary
composes with the join instance end-to-end (field → corner → count → area → graviton expectation)."
HAVE NOT: "no exact finite CCR (the truncation defect is permanent); no Type III₁ finite corner (the
cutoff→continuum limit is THE wall, never claimed); no construction of continuum-localized modes from
the standard subspace (mode membership is named finite data, at most CERTIFIED by a supplied
localization witness); capacity is a constraint, not a generator." NOT quantum gravity solved; no
wall crossed.

</div>

## The dynamics — the code's time evolution, the independent cross-check, and the conjecture (DY1–DY7)

The microscopic side gets what a definition of a theory requires — a time evolution — and the
campaign closes with the QIQT-H analogue of the Brown–Henneaux = Cardy check in its honest finite
form, plus the sharp continuum conjecture stated (never assumed) in Lean (`QIQTH/Dynamics.lean`,
`CrossCheck.lean`, `Conjectures.lean`; axiom-free, std-3).

- **DY1 — the diagonal dynamics** (`alpha`, the entry formula): H = Σ<sub>k</sub> ω<sub>k</sub>N<sub>k</sub>
  with its Heisenberg flow via explicit phase unitaries (no Stone theorem, no matrix exponential) —
  a one-parameter group of ⋆-automorphisms under which **records are stationary** (the honesty
  point: H is a function of the N<sub>k</sub>, so what λ selects among does not move) while the
  ladders rotate, α<sub>t</sub>(a<sub>k</sub>) = e<sup>−iω_k t</sup>a<sub>k</sub>.
- **DY2 — the explicit thermal state** (`gibbsDensity`): a product diagonal density (per-mode
  Boltzmann weights), a genuine density for every β, stationary under the flow.
- **DY3 — the KMS bridge** (`sigmaDiag_gibbs_eq_alpha_rescale`): **the Gibbs state's modular flow
  IS the rescaled physical flow**, σ<sub>s</sub><sup>ρ_β</sup> = α<sub>−βs</sub> (the partition
  function cancels; the flow is never *defined* by modular theory — the bridge runs from the
  independent dynamics to the KMS certificate); at β = 0 the Gibbs state IS the keystone's
  maximally mixed counting state.
- **DY4–DY5 — regions and their entropy** (`marginal_gibbsWeight`, `entropy_gibbs_region`):
  regions = subsets of mode labels (no spatial-entanglement claims); the Gibbs marginal is again
  Gibbs; S(ρ<sub>β,R</sub>) = Σ<sub>k∈R</sub> s<sub>k</sub>(βω<sub>k</sub>), saturating at
  Σ log D<sub>k</sub> with the all-β Gibbs bound.
- **DY6 — the saturated conditional Sakharov cross-check, CALIBRATION-FREE**
  (`S_micro_zero_eq_inducedQuarterG`): the code dynamics' region entropy at saturation equals the
  induced area over 4G<sub>ind</sub> — the microscopic side computed from the Hamiltonian, the
  macroscopic side supplied by independent Sakharov/species/cell data (with the derived
  G<sub>ind</sub> = 1/(N<sub>eff</sub>·Λ<sub>s</sub>²) only the species/cell matching remains
  input), and the proofs referencing NONE of the keystone calibration (grep-verified). Equality at
  saturation ONLY; the arbitrary-β equality is false and never claimed.
- **DY7 — the conjecture** (`FlatSpaceRecordGravityCorrespondence`): **the flat-space
  record-code/gravity correspondence, stated sharp** — in the continuum limit the capacity-bounded
  record code with diagonal dynamics equals free QFT + linearized gravity: for every region, micro
  record entropy = one-loop conical entropy = area/4G<sub>ind</sub>, with G<sub>ind</sub> the
  Sakharov constant of the SAME field content (one microscopic system computing both the states
  and G). The DY1–DY6 evidence is bundled and PROVEN (`finiteEvidence_holds`); the continuum claim
  carries NO proof field, NO axiom, NO instance — stated, never assumed.

<div class="note">

<strong>The DY7 checkpoint — the two honest sentences.</strong> HAVE: "a finite, axiom-free
diagonal code dynamics, explicit Gibbs/KMS states, product-mode reductions, and a saturated
conditional induced-gravity cross-check whose proof does not use the trace/wEnt area calibration."
HAVE NOT: "a finite proof of a continuum one-loop heat-kernel area law or an equality between
finite thermal entropy at arbitrary β and an induced geometric area; that remains the named
continuum frontier/conjecture." NOT quantum gravity solved; no wall crossed.

</div>

## The decoupling shadow — the finite forced core of the dictionary (DS1–DS7)

Prompted by a primary-source re-reading of Maldacena (hep-th/9711200), whose deepest structural
feature is that the dual sides are two SURVIVING DESCRIPTIONS of one parent construction under one
limit: this campaign delivers the honest finite shadow of that structure — the word "constructed"
is deleted from every part of QIQT-H's dictionary where deleting it is mathematically true, and
what remains is named parent data (`QIQTH/Decoupling/`, `QIQTH/Rigidity/`; axiom-free, std-3).

- **DS1 — the free sector forced, operator level** (`commutator_eventually_exact`): at fixed
  occupations the truncated ladder matrix elements are D-independent and the commutator entries
  stabilize to the exact-CCR values — the truncation defect lives only at the top level, which
  bounded occupations eventually never see.
- **DS2 — the first genuine limit theorems** (`tendsto_meanN`, `tendsto_defectExpect`): at fixed
  βω &gt; 0 the truncated occupation converges to the PLANCK value q/(1−q) and the defect
  expectation dies — the state-level decoupling half, bridged to the code's own thermal states.
- **DS3 — THE REGIME-SEPARATION GUARD** (`guard_entropy_saturates`, `guard_defect_survives`):
  along ANY schedule x<sub>D</sub>·D → 0, capacity saturates BUT the defect expectation tends to
  **1**, not 0 — exact saturated capacity is provably NOT the positive-temperature free-oscillator
  limit. The two halves of the shadow live in different regimes, as a theorem: the formalization
  itself forbids merging the count and the field limit into a fake continuum claim.
- **DS4 — the finite-product lifts** (`tendsto_productEntropy`): entropies, defects, and fixed
  occupations' Gibbs weights of finite mode sets all converge to the free-field values.
- **DS5 — the Cauchy rigidity** (`monotone_logValuation`): monotone additive on ℝ is linear
  (proved by hand); a monotone product-to-sum valuation on ℝ&gt;0 is κ·log.
- **DS6 — THE FORCED WEIGHT** (`finiteCorner_valuation_rigidity`, `forced_weight_product`,
  `nu2_counterexample`): a monoidal valuation monotone under ALL isometric embeddings is forced to
  be κ·log n — hence on product record corners A = κ·Σ log D<sub>k</sub>: the local weight of the
  keystone/join/embedding dictionaries is the UNIQUE refinement-natural valuation, no longer a
  constructed choice (κ is the one free normalization — where 4G lives, input). Necessity is
  machine-checked: ν₂ is additive and divisibility-monotone yet not ∝ log — the strong hypotheses
  cannot be weakened.
- **DS7 — the shadow package** (`decouplingShadow_holds`, `saturated_entropy_eq_forced_area`):
  the parent tower with its three theorems — the free sector survives the cutoff limit; every
  refinement-natural valuation is κ·Σ log D<sub>k</sub>; given the normalization, the saturated
  area law survives (the code's β = 0 entropy = the forced area over κ).

<div class="note">

<strong>The DS7 checkpoint — the two honest sentences.</strong> HAVE: "The capacity-limit theorem
forces the oscillator/free-field sector only in the bounded-occupation or positive-temperature
sense; it does not force the screen geometry or Newton constant." HAVE NOT: "The tower-rigidity
theorem forces the logarithmic capacity weight only under monoidal, monotone refinement
naturality; without those hypotheses there are explicit finite counterexamples." NOT a full
decoupling derivation — the join incidence geometry, the species/cell match, and the value of G
remain parent data; NOT quantum gravity solved; no wall crossed.

</div>


## The tower (T1–T8): the first machine-checked contact with the Type III₁ wall

Phase A of the continuum-definition attack, via the ITPFI/Araki–Woods route: the capacity code
tower with its Gibbs product states IS Araki–Woods input data, and its arithmetic invariant is
machine-verified to be the III₁ one — at the level of the wall's *fingerprint*, never the wall
itself (`QIQTH/Tower/`; axiom-free, std-3).

- **T1 — the fingerprint predicates** (`IsTailModularExponent`, `AWFingerprintIII1`): the named
  witness form of the Araki–Woods asymptotic-ratio invariant, additive in the modular exponent κ,
  with a load-bearing tail quantifier and uniform weight floor (drifting-frequency and
  vanishing-weight counterexamples documented), the EXACT per-mode ratio λ₁/λ₀ = e^{−x} (the
  partition function cancels), and the bridges to the held `kappaOf` eigenvalue law.
- **T2 — Kronecker density**: two reals at irrational ratio generate a dense additive subgroup
  (`AddSubgroup.dense_or_cyclic`; the cyclic case forces a rational ratio).
- **T3 — THE CENTERPIECE** (`gibbsTower_awFingerprint_III₁`): two frequencies occurring
  infinitely often at irrational ratio, uniform bounds 0 &lt; a ≤ βω<sub>k</sub> ≤ b, cutoffs
  D<sub>k</sub> ≥ 2 ⟹ the tower's eigenvalue family satisfies the III₁ fingerprint — PLUS the
  hypothesis-free alternating {1, √2} qubit instance via `irrational_sqrt_two`. The operator
  reading rests on three facts cited verbatim and never proved (Araki–Woods 1968; Connes 1973);
  no von Neumann algebra is constructed anywhere in the development.
- **T4 — the Powers guard** (`gibbsTower_constant_not_fingerprint`): a constant-frequency tower
  provably FAILS the fingerprint (every tail exponent lies in sℤ — the arithmetic fingerprint of
  the Powers factor III<sub>e^{−s}</sub>, cited). The separation theorem: the predicate is
  neither vacuous nor universal.
- **T5 — the state limit** (`gibbsLimitMeasure`): the σ-additive infinite-mode Gibbs measure on
  occupation configurations — the unique projective limit of the dynamics campaign's own thermal
  marginals through the held Kolmogorov/product machinery, whose finite marginals ARE the code's
  DY Gibbs weights.
- **T6 — non-atomicity** (`gibbsLimitMeasure_noAtoms`): under the uniform frequency bound every
  singleton configuration is null (the cylinder squeeze) — so no diagonal-density quantum reading
  of the limit exists: FALSE, not deferred; the Type-I shortcut is provably closed. The
  vacuum-atom dichotomy is cited, never proved.
- **T7 — the finite operator tower** (`cornerEmbed`): for nested corners C ⊆ C′ the inclusion is
  a unital ⋆-homomorphism, mode-compatible, state-compatible (φ<sub>C′</sub>∘ι = φ<sub>C</sub>),
  and modular-flow equivariant (σ<sub>s</sub><sup>C′</sup>∘ι = ι∘σ<sub>s</sub><sup>C</sup>, via
  the `kappaOf` eigen-law) — a family of finite-dimensional maps only: exactly the ITPFI tower
  DATA, its classification never performed.

<div class="note">

<strong>The T8 checkpoint — the two honest sentences.</strong> HAVE: "the machine-checked
arithmetic content of the Araki–Woods III₁ criterion for the code's Gibbs tower, including a
hypothesis-free concrete instance, the Powers-guard separation, the σ-additive infinite-mode
Gibbs measure with its non-atomicity, and the state-compatible modular-equivariant finite
refinement tower; the inference to an actual III₁ factor is cited (Araki–Woods 1968; Connes
1973), never proved." HAVE NOT: "the ITPFI von Neumann algebra, its ratio set, its type, any
inductive limit or weak closure, any quantum state on the infinite system, or any
continuum-limit completion — none are constructed or classified here." NOT the continuum done;
no wall crossed — this is the wall's fingerprint.

</div>


## The closure (C1–C11): the von Neumann double-commutant theorem

The convergent blocker of the continuum program — the missing lemma that four separately-named
frontiers all reduce to — is now a machine-checked theorem, in Mathlib-styleable form: Mathlib
defines `VonNeumannAlgebra` by the bicommutant property but has **no bicommutant theorem**; this
campaign closes that gap (`QIQTH/VonNeumann/`; axiom-free, std-3; all eleven increments landed,
the stretch included).

- **THE CENTERPIECE** (`vonNeumann_double_commutant`, green first try): for every unital
  ⋆-subalgebra A of the bounded operators on a complex Hilbert space, **the double centralizer
  A″ equals the set of operators approximable from A in norm on every finite tuple of vectors**
  — the SOT closure, stated concretely (`SOTApprox`; one approximant per tuple, the load-bearing
  quantifier order). Forward: the classical amplification argument fully verified — the
  cyclic-subspace projection in the commutant (⋆-closure load-bearing, upper-triangular
  counterexample), single-vector density (unitality load-bearing, A = {0} counterexample), the
  frozen PiLp amplification interface (ι† = π), the two minimal matrix-commutant lemmas (never
  Mₙ(A′)), n-vector density. Converse: the (x, Sx) two-vector estimate — single-vector
  approximability is provably insufficient.
- **The WOT stretch** (`wotClosure_image_eq_image_bicommutant`, shipped): the weak-operator
  closure IS the bicommutant, wholly inside Mathlib's WOT type copy (separate continuity only —
  joint WOT continuity of multiplication is false). With the centerpiece: **WOT closure = SOT
  closure = A″** — the full classical statement.
- **`VonNeumannAlgebra.generatedBy`** — the vN algebra generated by any operator set (double
  centralizer + minimality + the Galois lemma), proven to BE the SOT closure of the generated
  ⋆-algebra (`generatedBy_carrier_eq`).
- **The two payoffs, honestly scoped**: `crossedProductVN` — the crossed product M⋊<sub>σ</sub>ℝ
  packaged as a genuine `VonNeumannAlgebra` on L²(ℝ;H) with the membership characterization
  (packaging only; the dual-weight trace is NOT claimed to extend to the weak closure); and
  `limitVN` — the directed-union limit algebra for any hypothesized common representation (the
  refinement-tower limit; the code tower's own instantiation awaits the tower-GNS campaign).

<div class="note">

<strong>The C11 checkpoint — the two honest sentences.</strong> HAVE: "We have the von Neumann
double-commutant theorem as an axiom-free Lean theorem over current Mathlib — for every unital
⋆-subalgebra A of the bounded operators on a complex Hilbert space, the double centralizer A″
equals the set of operators approximable from A in norm on every finite tuple of vectors (and,
in the shipped WOT increment, the weak-operator closure) — packaged as
`VonNeumannAlgebra.generatedBy` with membership lemmas, and instantiated to present the
project's crossed-product representation and any commonly-represented refinement tower as
genuine `VonNeumannAlgebra`s." HAVE NOT: "We do not have Kaplansky density, normal states,
preduals or the σ-weak topology, type classification, or the inductive-limit (tower-GNS)
Hilbert space — the ITPFI tower's limit algebra is packaged only relative to a hypothesized
common representation, and the crossed-product dual-weight trace is not claimed to extend from
the algebraic core to the weak closure." The gate to the continuum, not the wall crossed.

</div>


## The representation (R1–R9): the tower's limit von Neumann algebra exists

The GNS construction of the compatible Gibbs family: the corner tower — previously a family of
finite matrix algebras related by embeddings — now acts on ONE Hilbert space, and its
directed-union limit von Neumann algebra is an actual, named, axiom-free object
(`QIQTH/TowerGNS/`; the first genuinely infinite-dimensional quantum object of the development).

- **The Hilbert space `TowerGNS`** — the completion of the direct sum of ALL finite corners
  under the stabilized Gibbs pairing, which is *deliberately semidefinite*: the null directions
  are exactly the direct-limit gluing, and the metric completion performs the identification
  (**`towerGerm`**) — no quotient is ever taken. Instance architecture = Mathlib's own
  `GelfandNaimarkSegal.lean`, verbatim.
- **The representation `towerRep`** — every corner algebra acts as a unital ⋆-algebra
  homomorphism (bounded via an elementary Frobenius estimate — honest scope: bounded, NOT
  claimed contractive), with the algebra laws holding ONLY in the completion (provably false at
  the pre-level — the stages differ; the germ reconciles). CAPSTONE **`towerRep_cornerEmbed`**:
  π<sub>C′</sub> ∘ ι = π<sub>C</sub> — the tower acts coherently through every stage.
- **The cyclic vector Ω** — implements EVERY corner Gibbs state as a vector state
  (⟪Ω, π<sub>C</sub>(a)Ω⟫ = φ<sub>C</sub>(a)) and its orbit is dense. Ω is NOT shown separating.
- ★ **`towerLimitVN`** ★ — the directed-union limit von Neumann algebra of the representation
  images (the double-commutant campaign's `limitVN`, instantiated), with membership characterized
  by SOT-approximation from the finite stages, and the ℕ-instantiation `freqTowerLimitVN` for
  the code's frequency tower. The object THE TOWER and THE CLOSURE campaigns were built for.

<div class="note">

<strong>The R9 checkpoint — the two honest sentences.</strong> HAVE: "One Hilbert space — the
completion of the semidefinite Gibbs-GNS pre-space on the direct sum of all finite corners —
carrying compatible unital ⋆-representations of every corner algebra (π_{C′} ∘ cornerEmbed =
π_C for all C ⊆ C′), a unit cyclic vector Ω implementing every corner Gibbs state as a vector
state (⟪Ω, π_C(a)Ω⟫ = φ_C(a)), and the directed-union limit von Neumann algebra towerLimitVN =
limitVN of the representation images, with membership characterized by SOT-approximation from
the finite stages — all axiom-free." HAVE NOT: "The type of towerLimitVN is not classified — no
factor, no ITPFI identification, no III₁ claim is made or proved (the T3 fingerprint stays
arithmetic; Araki–Woods 1968 and Connes 1973 stay cited, never invoked); Ω is not shown
separating, the modular theory of the limit state on the completion is not constructed, and the
representations are not shown isometric." The continuum is not done — but for the first time it
has an inhabitant.

</div>


## The transport + the accounting: dynamics for the limit algebra; the species form forced

Two tracks, one campaign (all axiom-free, std-3, budget 0).

- **THE MODULAR TRANSPORT** — the per-corner Gibbs modular flows transported to **`towerFlow`**,
  a *strongly continuous one-parameter unitary group* U<sub>t</sub> on the tower GNS space:
  U₀ = 1, the group law, U<sub>t</sub>* = U<sub>−t</sub>, **U<sub>t</sub>Ω = Ω**, THE
  IMPLEMENTATION THEOREM U<sub>t</sub> π<sub>C</sub>(a) U<sub>−t</sub> = π<sub>C</sub>(σ<sub>t</sub>a)
  at every finite stage (the covariance is exact already at the pre-level), and
  **`towerLimitVN` invariant under conjugation by the flow**. The finite-stage boundary KMS
  identity is displayed on the limit space (honestly bannered: not strip analyticity, not a KMS
  state of the limit algebra). HAVE NOT: no Tomita Δ/J, Ω not shown separating, no Stone
  generator (the named next hook), no type classified — U<sub>t</sub> is defined by *transport*.
- **THE ACCOUNTING** — the honest maximal species upgrade: **the regulator rigidity theorem**
  (any positive, species-additive, monotone, rescaling-covariant family is *forced* to the
  Sakharov/Dvali form 1/G = N<sub>eff</sub>·Λ², the exponent an output, with a counterexample
  showing weakened covariance breaks it); **the first derived — not cited — heat-kernel
  coefficient** in the repository (1/√(4πt) from Mathlib's Gaussian integral); and **the
  mixed-species consistency chain** — one shared species datum feeds both the entanglement
  entropy and the induced 1/G, with the mixed-content 1/4 and S = A/4G as theorems (the entire
  species sum cancelling), chained through the BTZ Cardy count. HAVE NOT: the numerical value of
  G is not derived; the c<sub>i</sub> stay cited Seeley–DeWitt data — a consistency chain over
  one shared cited datum, NOT an independent cross-check.


## The generator: the self-adjoint Hamiltonian of the limit dynamics, computed

`towerGen := stoneGen (towerFlow)` — the transported flow's genuine **self-adjoint unbounded
generator** (K = K†), instantiating the held Stone theorem with the five flow facts (two adapter
lemmas; every increment green on first or second build). With it:

- **The zero-mode** — Ω ∈ dom(K) and **KΩ = 0**: the cyclic vector is annihilated because the
  flow fixes it exactly.
- **The explicit core** — on every pure component, **K ↑(of<sub>C</sub> a) =
  ↑(of<sub>C</sub> [H<sub>C</sub>, a])** with H<sub>C</sub> = diagonal(log gibbsWeight): the
  finite-stage modular Hamiltonian acts by *commutator*; the generator is COMPUTED, not just
  certified, on a **constructively dense** domain (no Gårding mollification).
- **Flow covariance** — U<sub>s</sub> preserves dom(K) and K U<sub>s</sub> = U<sub>s</sub> K.

<div class="note">

<strong>Honest scope (the checkpoint, verbatim).</strong> "towerGen is NOT constructed from, and
NOT claimed equal to, a Tomita modular Hamiltonian log Δ of the limit state — no Δ, J, S,
separating property, KMS-at-the-limit, or von Neumann type is claimed. No spectral resolution
(PVM) of the unbounded towerGen is claimed, and no exponential-recovery identity
towerFlow t = exp(it·towerGen) is claimed — the recovery wall is open by design and the campaign
does not cross it."

</div>


## The separation: Ω is cyclic AND separating — the standard form

The limit algebra reaches the **standard-form hypothesis pair of Tomita–Takesaki theory**,
axiom-free (`RightMul.lean`, `Separation.lean`):

- **The weight exchange + half-power intertwining** — T7's modular-frequency lemma
  exponentiated gives ι(a)·√ρ<sub>K</sub> = √ρ<sub>K</sub>·ι(rightConj a), so RIGHT
  multiplication is *bounded* with the weighted Frobenius constant
  Σ‖a<sub>nm</sub>‖²(w<sub>m</sub>/w<sub>n</sub>) (never claimed contractive).
- **The commutant facts** — left and right actions commute (deep-stage double germ; no Finset
  equality ever stated), and every element of `towerLimitVN` commutes with every right
  multiplication by *pure bicommutant algebra* (double-centralizer membership is definitional).
- ★ **`towerCyclicVec_separating`** ★ — T ∈ towerLimitVN, TΩ = 0 ⟹ T = 0: T kills the right
  orbit of Ω, which IS the left orbit, and that orbit spans densely. With the held cyclicity:
  **Ω is CYCLIC AND SEPARATING for the tower limit von Neumann algebra.** Plus
  `towerLimitVN_eq_of_apply_cyclicVec` — the well-definedness germ of a future Tomita S₀.

<div class="note">

<strong>Honest scope (checkpoint, verbatim).</strong> "No Tomita operator S₀, no modular
operator Δ, no conjugation J, no KMS condition at the limit, and no type classification is
constructed or claimed here — separation is the HYPOTHESIS for that theory, not the theory."

</div>


## The Tomita operator: S₀, computed and closable

Modular theory proper begins: **`towerTomita₀`** — the Tomita operator of the tower limit state
on its classical orbit domain, as a genuine conjugate-linear (σ-semilinear) partial operator:

- **Well-defined because Ω is separating** (the previous campaign's capstone doing its job);
  involutive; densely defined; **S₀Ω = Ω**; and the **computed core action
  S₀ ↑(of<sub>C</sub> a) = ↑(of<sub>C</sub> aᴴ)** — the Tomita involution is conjugate-transpose
  on pure components.
- **The finite σ₋ᵢ, computed** — the commutant-side right multiplications carry the exact
  adjoint **R<sub>a</sub>† = R<sub>ρaᴴρ⁻¹</sub>** (the engine squared + the modAut bridge): the
  honest finite-tower substitute for KMS analyticity, a theorem rather than an analytic
  continuation.
- **The classical pairing** ⟪T*Ω, R<sub>a</sub>Ω⟫ = ⟪R<sub>a</sub>†Ω, TΩ⟫ on a dense family,
  and **closability** in the graph-limit sense (T<sub>n</sub>Ω → 0 ∧ T<sub>n</sub>*Ω → v ⟹
  v = 0).

<div class="note">

<strong>Honest scope (checkpoint, verbatim).</strong> "The closure S̄ is not constructed as an
object, and no polar decomposition, no modular operator Δ, no modular conjugation J, no KMS
condition of the limit state, and no von Neumann type classification is constructed or claimed;
Mathlib's LinearPMap closure and adjoint theories cover only ℂ-linear (identity ring-hom)
partial maps, and a conjugate-linear closure theory is not built here."

</div>


## The conjugate closure: S̄ as an object — and a new slice of Mathlib

The closure of the Tomita operator exists, built by the **ℝ-reduction** (a conjugate-linear map
IS ℝ-linear; Mathlib's closure theory applies verbatim through the global complexToReal
instances — no local instances anywhere):

- **Four new abstract theorems** (Mathlib-only imports — upstream-gap contributions): the
  ℝ-restriction view of a conjugate-linear partial map; the **sequence-closability bridge**
  (`isClosable_of_seq` — absent from Mathlib even for ordinary linear maps); and the transfer
  theorems — conjugate-homogeneity and the involution *survive closure* (no adjoint anywhere).
- **`towerTomitaBar`** — S̄: closed, extending S₀ with the orbit domain as a core, S̄Ω = Ω,
  conjugate-transpose on pure components, twist-guarded conjugate-homogeneous, and **fully
  involutive** with trivial kernel and range = domain.

<div class="note">

<strong>Honest scope (checkpoint, verbatim).</strong> "The modular operator Δ, the conjugation
J, and the polar decomposition are not constructed (the documented Δ contract … is the named
next campaign); no σ-semilinear graph or closure theory is contributed to Mathlib here (the
ℝ-reduction sidesteps it; the σ-graph remains Mathlib's own open TODO); no KMS condition of the
limit state and no von Neumann type is claimed."

</div>


## The modular operator: Δ, computed as the modular automorphism

The campaign after the conjugate closure delivers Tomita–Takesaki's central object for the tower
limit state:

- **Tomita's F with no Riesz machinery** — the conjugate-linear adjoint of S̄, built on the
  ∃-Riesz domain {y : ∃ w, ∀ x, ⟪S̄x, y⟫ = ⟪w, x⟫}: no real inner product, no dual-space
  machinery, no completeness argument anywhere. The abstract `conjAdjoint` (closed in the
  sequence sense, with the core-extension equalizer lemma) is itself a Mathlib-gap contribution.
- **Δ := F∘S̄** — a ℂ-linear densely defined partial operator (the two conjugations cancel):
  **symmetric** (IsFormalAdjoint Δ Δ), **positive** (⟪Δx, x⟫ = ‖S̄x‖² ≥ 0), **closable**
  (Δ ≤ Δ† with Δ† closed), fixing Ω.
- **The computation** — on the dense pure-component core,
  **Δ ↑(of<sub>C</sub> a) = ↑(of<sub>C</sub> (modAut<sub>ρ<sub>C</sub></sub> a))**: the continuum
  modular operator *acts as* the finite modular automorphism ρaρ⁻¹, stage by stage — the modular
  operator of the physics, computed rather than postulated.

<div class="note">

<strong>Honest scope (checkpoint, verbatim).</strong> "Full self-adjointness Δ† = Δ is not
proved — it is von Neumann's S̄*S̄ theorem, absent from Mathlib and named as the next target; no
polar decomposition, no J, no Δ^{1/2} or Δ^{it} (no unbounded positive square-root or spectral
theory for partial operators exists in the pin), no KMS condition of the limit state, and no von
Neumann type is constructed or claimed."

</div>


## The von Neumann campaign: Δ† = Δ — and von Neumann's theorem itself

One campaign later, the modular operator is genuinely **self-adjoint** (six increments in a
single session, four consecutive first-try greens):

- **Three abstract Mathlib-gap files** (RCLike-generic, Mathlib-only imports): the
  self-adjointness kernel (symmetric + ran(1+A) = ⊤ ⟹ A† = A); the von Neumann graph
  orthogonal decomposition of a closed partial operator in ℓ²(E×E) (no adjoint anywhere); and
  **von Neumann's theorem itself** — T†T densely defined and self-adjoint for closed densely
  defined T, over any RCLike field. None exists in Mathlib at the pin.
- **The i-twist** — conjugate-homogeneity upgrades the real graph-orthogonality pairing to the
  full complex pairing, which lands *verbatim* in the ∃-Riesz F-domain membership:
  **ran(1+Δ) = ⊤**.
- **The headline** — **Δ† = Δ** (`towerModularOp_isSelfAdjoint`): the tower modular operator
  is a genuinely self-adjoint, positive, closed, densely defined operator fixing Ω and
  computed as the finite modular automorphism on the dense core; with kernel triviality and
  the resolvent bound ‖x‖ ≤ ‖x + Δx‖.

<div class="note">

<strong>Honest scope (checkpoint, verbatim).</strong> "Δ^{1/2} and the polar decomposition
S̄ = JΔ^{1/2} are not constructed (so J is still not an object); the spectral resolution of the
unbounded Δ is not built; Δ^{it} and the KMS property of the limit state are not proved — in
particular NO claim that the transported dynamics equals the modular flow of Δ; no Tomita
theorem at the algebra level; no von Neumann type statement."

</div>


## The resolvent campaign: Δ^{it} exists

The modular unitary group of the tower limit state is constructed (seven increments, every one
first-try green):

- **The resolvent** — R := (1+Δ)⁻¹, an everywhere-defined self-adjoint contraction with
  0 ≤ R ≤ 1, trivial kernel, dense range = dom Δ, spectrum in [0,1], RΩ = ½Ω, and the exact
  identity **Δ∘R = 1−R** — Δ is a function of a single bounded self-adjoint operator.
- **The abstract PVM supplement** (reusable) — the operator-level spectral theorem T = ∫λ dE;
  the **kernel-atom lemma** (injective self-adjoint T forces E({0}) = 0 — not automatic from
  kernel triviality); the eigenvector calculus f(T)x = f(r)x.
- **The headline** — **Δ^{it} := towerModUnitary**, the bounded Borel calculus of R under the
  symbol ((1−r)/r)^{it}: a **strongly continuous one-parameter unitary group** (U₀ = 1,
  U_{s+t} = U_sU_t, U_t⋆ = U_{−t}) fixing the cyclic vector (U_tΩ = Ω), commuting with Δ on
  its whole domain, with E({0}) = 0 certifying the group genuinely represents δ^{it} on the
  spectrum.

<div class="note">

<strong>Honest scope (checkpoint, verbatim).</strong> "No claim that towerModUnitary equals
the transported towerFlow (equivalently towerGen = log Δ): two strongly continuous unitary
groups now coexist on the tower space and their identification — the exponential-recovery
wall — is the named next campaign, not crossed here. No KMS condition of the limit state is
proved; Tomita's theorem is not proved — U_t is not shown to implement automorphisms of the
limit algebra; Δ^{1/2}, J, and the polar decomposition are still not constructed; no von
Neumann type statement."

</div>


## The identification: the exponential-recovery wall, crossed — and Tomita I

The campaign after the resolvent identifies the two unitary groups (five increments, every
one first-try green):

- **The eigenvector route** — the Gibbs density is *diagonal by construction*, so matrix
  units are simultaneous eigenvectors of the finite modular automorphism
  (modAut ρ (e<sub>nm</sub>) = (w<sub>n</sub>/w<sub>m</sub>)e<sub>nm</sub>), of Δ, of the
  resolvent, and — through the eigenvector calculus — of Δ^{it}, with the *same* explicit
  scalar e^{it(log w<sub>n</sub> − log w<sub>m</sub>)} the transported physical flow
  carries. No spectral theorem, no Stone uniqueness, no log Δ needed anywhere.
- **The identification** — **towerFlow = Δ^{it} as operators** (`towerModUnitary_eq_towerFlow`):
  the transported physical dynamics of the tower limit state IS the spectral modular flow of
  its modular operator; corollary, towerGen IS the Stone generator of Δ^{it}.
- **Tomita's theorem, first half** — Δ^{it} implements the modular automorphisms
  (Δ^{it} π(a) Δ^{−it} = π(σ_t a)) and preserves the limit algebra:
  **Δ^{it} towerLimitVN Δ^{−it} = towerLimitVN** — the modular theory of the physics equals
  the modular theory of the state.

<div class="note">

<strong>Honest scope (checkpoint, verbatim).</strong> "J and the polar decomposition
S̄ = JΔ^{1/2} are still not constructed (so JMJ = M′, the second half of Tomita's theorem,
stays open — the natural next campaign: J on matrix units is also explicit, so the same
eigenbasis method applies); no analytic strip-KMS of the limit state (only the boundary
identity); no von Neumann type classification; and everything remains the finite-stage Gibbs
inductive-limit state — the free-field/Type-III continuum objects are untouched."

</div>

## Reproduce the verification

```bash
~/.elan/bin/lake build QIQTH
~/.elan/bin/lake build QIQTH.AxiomAudit   # emits #print axioms for every theorem
```

Each theorem reports `depends on axioms: [propext, Classical.choice, Quot.sound]`. The full
statement-level index lives in the repository; a companion formalization paper is in preparation.

A note on wording: "no axioms" here means no *project* axioms. `propext`, `Classical.choice`, and
`Quot.sound` are the standard classical foundations every ordinary Mathlib proof uses; we keep them and
add nothing of our own.
