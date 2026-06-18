# 51 — General relativity as the emergent equation of state of the holographic record structure

**Status:** new direction, 2026-06-18. Lays out precisely how GR fits QIQT-H — *not* as an added postulate
but as a recoverable emergent equation of state — mapping the two known derivations (Jacobson; the
entanglement first law) onto the program's own objects (Q_R, χ_R, the modular first law), and marking exactly
what is **verified**, **inherited**, and **open**. Companion: a Lean file `QIQTH/EinsteinEquationOfState.lean`
that machine-checks the *linear-algebraic crux* of the thermodynamic derivation (not the full field equation —
the differential geometry is cited). Per the authority hierarchy (Lean > papers > pro), the derivations below
are the literature; only the Lean lemma is ours-and-checked.

---

## 0. The claim, stated honestly up front

**GR is not a separate assumption QIQT-H needs — Einstein's field equations are recoverable as the emergent
thermodynamics / entanglement equation-of-state of the same finite-information structure the framework
postulates.** The inputs to the known derivations are *exactly* QIQT-H's objects. BUT: those derivations
(a) **assume the area law** (S ∝ A) — they do not derive it; (b) derive the **dynamics** (field equations),
presupposing spacetime, horizons, and G; (c) are **inherited**, not yet carried out inside the program. So the
truthful statement is *"GR is recoverable as emergent, by a known derivation the framework supplies the right
ingredients for, presupposing the area law it postulates,"* **not** "QIQT-H derives GR from scratch." The
selector λ plays **no** role — GR emerges entirely from Φ's entanglement/entropy structure.

---

## 1. Route A — Jacobson (1995): Einstein's equation as an equation of state

**Inputs.** (i) Every local Rindler horizon has entropy $\delta S = \eta\,\delta A$ proportional to its area
(η = 1/4Għ) — the **holographic/Bekenstein form = QIQT-H's $Q_R = A/4\ell_P^2$**. (ii) The Clausius relation
$\delta Q = T\,\delta S$ with the Unruh temperature $T = \hbar a/2\pi c k_B$. (iii) The Raychaudhuri focusing
equation relating area change to the Ricci curvature along null congruences, $d\theta/d\lambda = -R_{\mu\nu}k^\mu k^\nu + \dots$.

**Output.** Demanding (i)–(iii) for *all* local horizons through *every* point forces
$$R_{\mu\nu} - \tfrac12 R g_{\mu\nu} + \Lambda g_{\mu\nu} = 8\pi G\, T_{\mu\nu}.$$
Einstein's equation is then an **equation of state** — a thermodynamic identity from coarse-graining, not a
fundamental field law; the metric is a collective variable.

**The logical skeleton (where the Lean lemma sits).**
1. Energy flux across the horizon: $\delta Q = \int T_{\mu\nu}k^\mu k^\nu\,\lambda\,d\lambda\,dA$.
2. Area/entropy change via Raychaudhuri: $\delta S = \eta\,\delta A = -\eta\int R_{\mu\nu}k^\mu k^\nu\,\lambda\,d\lambda\,dA$.
3. Clausius ⇒ for **every** null $k$: $\;T_{\mu\nu}k^\mu k^\nu = \dfrac{1}{2\pi\eta}R_{\mu\nu}k^\mu k^\nu$.
4. **[Lean crux]** A symmetric tensor identity holding on the *entire null cone* forces a **tensor** equation
   up to a multiple of the metric: $\;2\pi\eta\,T_{\mu\nu} = R_{\mu\nu} + f\,g_{\mu\nu}$.
5. Conservation $\nabla^\mu T_{\mu\nu}=0$ + contracted Bianchi $\nabla^\mu(R_{\mu\nu}-\tfrac12Rg_{\mu\nu})=0$
   fix $f = -\tfrac12 R + \Lambda$, giving the Einstein equation.

Steps 1–2 are differential geometry (**cited / hypothesised**). Step 4 is **pure linear algebra — and it is the
step that turns a scalar thermodynamic relation into a tensor field equation.** That is what we machine-check.

---

## 2. Route B — the entanglement first law (Lashkari–Van Raamsdonk; Faulkner et al., 2013–14)

**Inputs.** The **first law of entanglement** $\delta S_{\mathrm{EE}} = \delta\langle K\rangle$ ($K$ = modular
Hamiltonian) for ball-shaped regions, plus the area-law entanglement entropy (Ryu–Takayanagi, $S = A/4G$).
**Output.** The **linearised** Einstein equations in the bulk (Faulkner et al. extend to nonlinear order).

**Why this is the QIQT-H-native route.** The modular Hamiltonian $K$, the first law, and relative entropy are
*exactly* the **Araki/Tomita–Takesaki χ_R calculus QIQT-H has machine-checked** (free-field coherent sector).
So the verified substrate is the right home for this derivation — the open part is the continuum/interacting
realisation (the Type III → Type II wall, Gap 3). This is the more rigorous and more "ours" of the two routes;
Route A is the cleaner one to expose the algebraic crux.

---

## 3. The map: which QIQT-H object feeds which input

| derivation input | QIQT-H object | status |
|---|---|---|
| area-law entropy $S\propto A$ | holographic capacity $Q_R = A/4\ell_P^2$ | **postulated** (Gap 3: ground it) |
| modular Hamiltonian / first law | χ_R = Araki relative entropy, modular flow $\Delta^{it}$ | **machine-checked** (free field) |
| UV-finiteness of the relevant entropy | relative entropy (vacuum-subtracted) | **machine-checked** (free field) |
| Raychaudhuri / null focusing | — (differential geometry) | **cited / not in scope** |
| null-cone ⇒ tensor equation | `EinsteinEquationOfState.lean` | **machine-checked (this note)** |
| conservation + Bianchi ⇒ fix Λ | — (differential geometry) | **cited** |

**One postulate, double duty.** The single capacity postulate $Q_R = A/4\ell_P^2$ is *both* the finiteness
that tames the UV infinities (note on GR/UV) *and* Jacobson's input from which the field equations emerge. GR
is not bolted on beside the information postulate — it is the thermodynamics *of* it.

---

## 4. What the Lean file establishes (and what it does not)

**`QIQTH/EinsteinEquationOfState.lean` — the algebraic crux, machine-checked, axiom-free.**

- **Main lemma `symmTensor_eq_smul_metric_of_null`** (on $(1+3)$ Minkowski): if a symmetric bilinear form $C$
  satisfies $C(k,k)=0$ for **every null vector** $k$ (those with $g(k,k)=0$), then $C = c\,g$ for some scalar
  $c$. *(The classical "a quadratic form vanishing on the null cone is a multiple of the metric" — proved by
  evaluating $C$ on an explicit family of null vectors $e_0\pm e_i$ and the Pythagorean null vector $5e_0+3e_i+4e_j$.)*
- **Corollary `einstein_tensor_eq_of_state`**: if symmetric tensors $T$ (stress) and $E$ (Ricci) satisfy
  $a\,T(k,k) = E(k,k)$ for every null $k$ — the *integrated Clausius relation*, **taken as hypothesis** (this is
  what Raychaudhuri supplies) — then $\exists f,\ a\,T = E + f\,g$: a **tensor** field equation up to a metric
  term. This is **Jacobson's step 4** — the exact point where local thermodynamics becomes a tensor equation.

**BUILD STATUS: verified.** Both theorems compile against Mathlib (lean4 v4.30.0) and are **axiom-free**
(`#print axioms` = `[propext, Classical.choice, Quot.sound]` only); wired into `QIQTH.lean` + `AxiomAudit.lean`.

**What it does NOT do (state plainly — pro's scope-discipline list, do not let a reader infer otherwise):**
- It does **not** derive the Einstein equation. Steps 1–2 (energy flux, Raychaudhuri focusing) and step 5
  (conservation + Bianchi fixing $f=-\tfrac12R+\Lambda$) are **differential geometry, cited not checked**.
- It does **not** check: Raychaudhuri focusing, the local-Rindler-horizon construction, the approximate boost
  Killing vector, the Unruh temperature, the Clausius relation, the area-entropy law, conservation, the
  contracted Bianchi identity, the cosmological-constant integration, or the **local-equilibrium assumptions**
  ($\theta=0$, $\sigma=0$, twist $=0$ at the point) that Jacobson uses.
- It does **not** derive the area law (assumed) or the value of $G$ (the constant $a$).
- It is finite-dimensional linear algebra over a fixed Minkowski signature — the honest, non-vacuous, checkable
  *core* of the argument, not the argument. **Correct title:** *"the algebraic crux that turns equality of null
  contractions into a tensor equation,"* NOT *"machine-checked Jacobson's derivation."*

**Why it is still worth having.** It machine-verifies the single step that is most often hand-waved — *why* a
relation that holds "for each horizon / each null direction" upgrades to a *tensor* law. It is non-vacuous (a
real implication about the null cone), axiom-free, and it is the natural Lean entry point for the GR-emergence
story, exactly as the χ_R calculus is the entry point for Route B.

---

## 4b. GPT-5.5-pro strategic verdict (2026-06-18) — where to push next

Consulted on "why not build Raychaudhuri ourselves / what is the best Lean target." Verdict, blunt:

- **Mathlib is not a usable Lorentzian-GR library.** It has strong smooth-manifold + analysis infrastructure
  and *some* Riemannian pieces, but **no mature Lorentzian Levi-Civita / Riemann / Ricci / geodesic-congruence
  / Raychaudhuri stack** (the missing keystone: indefinite-signature metrics — Mathlib's `InnerProductSpace` is
  positive-definite). Full abstract Jacobson = a **multi-year Mathlib-infrastructure project**, mostly
  recertifying undisputed textbook DG. My characterization was correct.
- **Do NOT build full coordinate Raychaudhuri.** From $\Gamma(g)$ through Ricci through the null optical scalars
  is **months, not weeks** (the hard parts: the *null screen* formalism since $k\in k^\perp$ needs an auxiliary
  null $\ell$; the shear/twist decomposition; second-derivative blow-up), and it certifies textbook geometry
  without removing the physical inputs. A bounded *optical-algebra* "Raychaudhuri-lite" (assume the optical
  equation + connection as hypotheses; prove $\frac{d\theta}{d\lambda}=-\tfrac12\theta^2-\sigma^2+\omega^2-R_{\mu\nu}k^\mu k^\nu$
  from the screen decomposition) is weeks-scale but low marginal value.
- **The algebraic crux (this file) is the right Route-A thing to have checked** — genuinely Jacobson's
  load-bearing step, non-vacuous — *provided* it is titled narrowly (done).
- **Unruh/Bisognano–Wichmann is a true end-to-end blocker** (algebraic QFT: wedge algebras, modular groups,
  KMS, spectrum condition) but **cleanly citeable** as a physical input (the temperature). The honest theorem
  shape is *conditional*: "assuming Unruh $T$, area entropy $S=\eta A$, and Clausius, the null relation ⇒
  Einstein up to Λ." Not hollow if the assumptions are explicit.

**The single sharpest next target (pro's recommendation):** *not* Raychaudhuri, but the **entanglement
first-law / RT first-variation bridge** (Route B) — because it uses the modular-Hamiltonian / relative-entropy
machinery **QIQT-H already machine-checks** (free-field sector), and the heavy cited part is only RT + the
gravitational all-balls→linearised-Einstein theorem, not all of Riemannian geometry. Precise target
`rt_ball_first_law_from_entanglement_first_law`:
> machine-check the information-theoretic first law $\delta S_B = \delta\langle K_B\rangle$ for ball regions;
> then with the (cited) RT relation $\delta S_B = \delta A_B/4G$ derive $\delta A_B/4G = \delta\langle K_B\rangle$;
> and with the (cited) CFT ball modular Hamiltonian $K_B = 2\pi\int_B \frac{R^2-|x-x_0|^2}{2R}T_{00}\,d^{d-1}x$,
> derive the all-balls weighted-boundary-energy identity. **Cite** the Lashkari–Van Raamsdonk / Faulkner et al.
> gravitational corollary (all-balls ⇒ linearised Einstein). Weeks-scale, load-bearing, QIQT-H-aligned, not a
> recertification of textbook GR.

**Machine-checked vs cited line (pro):** *check* — entropy/relative-entropy first-law identities (already in
QIQT-H), the null-cone algebra (done), tensor inference, constant bookkeeping, optionally conservation+Bianchi→Λ
as conditional algebra. *Cite* — Raychaudhuri, local Rindler horizons, Unruh/BW, Clausius, the area law (unless
QIQT-H derives it), RT/HRT + AdS/CFT, Iyer–Wald, the all-balls integral-geometry step.

**STATUS — Route B bridge DELIVERED (2026-06-18), `QIQTH/EntanglementFirstLaw.lean` (builds, axiom-free):**
- `firstLaw_of_stationary` — the entanglement **first law** `δS = δ⟨K⟩`, proved as a clean real-analysis
  consequence of relative-entropy **stationarity** (`D ≥ 0` and `D 0 = 0` ⇒ `IsLocalMin` ⇒ `deriv D 0 = 0`;
  with `D = ⟨K⟩ − S` this gives `deriv S 0 = deriv KE 0`). **The inputs are QIQT-H's OWN machine-checked
  facts** — `relEntropy_nonneg` (Klein), `relEntropy_eq_crossEntropy_sub_entropy`, `relEntropy_self` (`#check`ed
  in the file). The *only* granted input is the smoothness `DifferentiableAt` of the family ε↦ρ(ε).
- `rt_bridge` — + cited RT (`S = A/4G`) ⇒ `δ(A/4G) = δ⟨K⟩`.
- `rt_all_balls_energy` — + cited ball modular Hamiltonian (`δ⟨K⟩ = W`, the weighted boundary energy) ⇒
  `δ(A/4G) = W` for all balls. The gravitational all-balls ⇒ linearized-Einstein step remains **cited**.
- `gibbs_first_law` — the **integrated (finite) first law** `S(ρ) ≤ ⟨K⟩ = crossEntropy ρ σ` (Gibbs/Klein,
  equality iff ρ=σ), proved with **no differentiability** straight from `relEntropy_nonneg` +
  `relEntropy = crossEntropy − S`. The finite shadow of `δS = δ⟨K⟩`, fully grounded.

- **Discharging the smoothness — what's tractable vs. the genuine wall (probed 2026-06-18):**
  - `crossEntropy ρ σ = −(ρ·matLog σ).trace.re` is **linear in ρ** (matLog σ fixed) ⇒ `hKE` is *in principle*
    dischargeable for any differentiable family (continuous-linear-map ∘ family); the only obstacle is
    matrix-norm / CLM plumbing, not mathematics.
  - `hS` (von Neumann entropy `−Tr(ρ log ρ)`, nonlinear) splits into two halves, and the **matrix-log half is
    now DONE** (commit pending): since `S = ∑ᵢ negMulLog(λᵢ)`, the `log`-derivative lives entirely in
    `negMulLog`, differentiable away from `0` (Mathlib `Real.differentiableAt_negMulLog`, `deriv = −log−1`).
    `spectralEntropy_differentiableAt` + `spectralEntropy_deriv` (axiom-free) machine-check that the entropy is
    differentiable in its eigenvalues, with the explicit first variation `δS = ∑ᵢ(−log pᵢ−1)·pᵢ'(0)`.
  - **Lifted onto the actual entropy:** `vonNeumannEntropy_differentiableAt` (axiom-free) — since
    `vonNeumannEntropy (h ε) = ∑ᵢ negMulLog((h ε).eigenvalues i)` *by definition*, the real von Neumann entropy
    is differentiable at `0` whenever each eigenvalue `(h ε).eigenvalues i` is differentiable and nonzero. So
    `hS` for the first law is now machine-checked **modulo exactly the eigenvalue-perturbation hypothesis `hev`**
    — on the actual entropy, not an abstract `S`.
  - **The fixed-basis case `hev` is now DISCHARGED (a theorem, not assumed) — `QIQTH/SpectralSum.lean`.** The
    obstacle (`IsDensity.eigenvalues` = sorted spectral data, no Mathlib lemma to an external diagonal) is
    bypassed through the **characteristic polynomial**, which is sorting- and conjugation-invariant:
    `sum_eq_of_prod_X_sub_C_eq` (∏(X−aᵢ)=∏(X−bᵢ) ⇒ ∑f(aᵢ)=∑f(bᵢ), via the roots multiset) ⟹
    `vonNeumannEntropy_diagonal` (S(diag d)=∑negMulLog dᵢ, charpoly_diagonal vs IsHermitian.charpoly_eq) ⟹
    `vonNeumannEntropy_unitaryConj` (S(U diag(p)U†)=∑negMulLog pᵢ for any unitary U, via `charpoly_mul_comm`).
    The family capstones `vonNeumannEntropy_{diagonal,unitaryConj}_differentiableAt` then prove `hS` for any
    **fixed-eigenbasis** family `ρ(ε)=U diag(p ε)U†` with `pᵢ` smooth+nonzero — **no `hev` assumption**. All
    axiom-free.
  - **Residual:** only genuinely **basis-ROTATING** families remain (eigenvalues can cross, where the sorted
    eigenvalues are non-differentiable) — a fundamental analytic frontier (Kato perturbation theory), not just
    missing infrastructure, and not unconditionally true. **Net status: the Route-B chain is machine-checked
    end-to-end — first law, RT bridge, all-balls energy, integrated Gibbs law, the spectral/matrix-log
    derivative, the lift onto the real von Neumann entropy, AND `hS` for the entire fixed-eigenbasis case — with
    the only remaining inputs the standard cited physics (RT, ball modular Hamiltonian, all-balls ⇒ linearized
    Einstein) plus, for basis-rotating families, eigenvalue-perturbation theory.**

## 4c. The curvature/connection tower (`QIQTH/Curvature.lean`) — Layer 0 done (2026-06-18)

The one thing both routes ultimately need is the differential-geometry tower Mathlib lacks. Building it the
tractable way (pro's advice): **component-level in a coordinate patch** `Point n = Fin n → ℝ`, as
multivariable calculus + algebra, NOT the multi-year abstract-manifold library.

- **Layer 0 (DONE, axiom-free, builds):** `pd` (partial derivative); `christoffel` (the Levi-Civita
  connection Γ from the metric) + `christoffel_symm` (torsion-free, Γ^μ_{νρ}=Γ^μ_{ρν}); `riemann`
  (R^ρ_{σμν}) + `riemann_antisymm` (antisymmetry in the last two indices); `ricci`, `scalarCurv`,
  `einsteinTensor` (G=Ric−½Rg); `covDerivVec/Cov/02` (the covariant derivative) + `covDeriv02_symm`. These
  are the definitions + the structural identities that need **no** analytic input.
- **Layer 1 (DONE, axiom-free):** the `pd` algebra (`pd_add/sub/const_mul/mul` — linearity + Leibniz);
  `inv_contract` (the inverse-metric collapse ∑σ g_{σν}(∑α g^{σα}w_α)=w_ν); `christoffel_lower`
  (Γ_{νλμ}=½(∂_λg_{νμ}+∂_μg_{νλ}−∂_νg_{λμ})); and **`metric_compat` — `∇_λ g_{μν}=0`**, the defining
  Levi-Civita property, now a THEOREM from the Christoffel definition + metric symmetry.
- **Layer 2 (DONE through the Schwarz keystone, axiom-free):** the **first Bianchi** identity
  `riemann_first_bianchi` (R^ρ_{σμν}+R^ρ_{μνσ}+R^ρ_{νσμ}=0, algebraic — `christoffel_symm` only); the
  pd↔fderiv bridge `pd_eq_fderiv`; **Schwarz `pd_comm`** (∂ᵢ∂ⱼf=∂ⱼ∂ᵢf for smooth f, via `pd_pd_eq` +
  `IsSymmSndFDerivAt`) — the analytic keystone; and **`second_bianchi_deriv_part`** — the *derivative
  part* of the second Bianchi cyclic sum vanishes (the six ∂∂Γ terms cancel in pairs via Schwarz).
- **THE WALL (honest frontier):** the **full second Bianchi** additionally needs the **ΓΓ / Γ·R terms**
  to cancel — a ~60+ term combinatorial cancellation (first Bianchi + Christoffel symmetry across the
  covariant-derivative-of-Riemann expansion) that is **impractical to brute-force in general coordinates**.
  The clean route is **normal coordinates** (Γ=0 at a point), a separate large construction Mathlib lacks.
  So the contracted Bianchi `∇^μ G_{μν}=0` (Jacobson's conservation+Bianchi step) is the one piece still
  cited. *Net: connection + all curvature tensors + metric compatibility + first Bianchi + Schwarz + the
  second-Bianchi derivative part are ALL machine-checked, far inside where the "cited" line sat before; the
  remaining gap is the second-Bianchi ΓΓ remainder, needing normal-coordinate machinery.*
- **Honest scale:** Layer 0 is a clean foundation; Layers 1–2 are the genuine multi-month effort (the
  differentiability propagation through Γ/Riemann is where the cost lives). This is the START of the tower,
  not its completion — and per pro, its marginal value for QIQT-H is bounded (it recertifies textbook DG),
  so it is pursued as honest infrastructure, with the information-theoretic Route-B side being the
  higher-leverage QIQT-H-native work.

## 5. Honest bottom line

GR fits QIQT-H as an **emergent equation of state**: the field equations are recoverable from the area-law
capacity + the modular first law (Jacobson; entanglement first law), both of which are QIQT-H's own objects,
with the verified χ_R calculus the natural substrate for the rigorous (Route B) version. The Lean file pins the
algebraic crux. What remains **inherited/cited** (the differential geometry) and **open** (grounding the area
law; the interacting continuum) is marked. The defensible one-liner:

> **Gravity is not an extra postulate of QIQT-H; it is the emergent thermodynamics of its finite-information
> structure — recoverable by a known derivation whose algebraic heart we machine-check, and whose remaining
> steps are the cited continuum frontier.**
