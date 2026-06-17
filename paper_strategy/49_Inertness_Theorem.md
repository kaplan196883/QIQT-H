# 49 — The Holographic Inertness Theorem (the substantive core, made precise)

**Status:** new direction, 2026-06-18. Outcome of the "where is the substance / how to make it work"
investigation + a GPT-5.5-pro consult. The honest verdict: QIQT-H has **no laboratory deviation** from QM
(finite information is empirically inert below horizon saturation), but that inertness is itself a **clean,
provable, publishable theorem**, and — together with the **no-covariant-selector** structural result and the
verified **χ_R** calculus — is the program's genuine substance. This note states the theorem precisely so it
can be proved/written up. Per the authority hierarchy (Lean > papers > pro), pro's reasoning here is a
consultant's sketch to be checked against the literature and, where possible, Lean.

---

## 0. An honesty correction (propagate everywhere)

The earlier framing "finite Q_R ⇒ an **amplitude floor** ε ~ 2^(−Q_R)" is **an overclaim** and is retired.
Finite Hilbert-space **dimension does not discretize amplitudes** — a single qubit already has a continuum of
pure states. The correct statement is **resource-bounded operational indistinguishability** (Thm 1 below):
to *detect* a dimension cap D ~ e^{Q_R} you need entropy ~Q_R, spectral resolution ~e^{−Q_R}, or
sample/time resources exponential in Q_R. The "amplitude floor" was conflating finite-dim with discretization.
(The paper's *separate* finite-resolution-amplitude postulate, if retained, must be stated as its own
hypothesis and is itself subject to the e^{2Q} sampling wall — not derived from finite-dimensionality.)

---

## 1. Theorem 1 — Holographic operational inertness (the headline)

**Setup.** Let $\mathcal H_\infty$ be the QFT Hilbert space of a region $R$; let $P$ project onto an
operationally accessible subspace (states below energy $E$ / particle number $N$ / bandwidth $\Lambda$), with
$\operatorname{rank}P = d_{\mathrm{eff}}\le e^{S_{\mathrm{eff}}}$. Let the finite holographic model have
$\dim\mathcal H_Q = e^{Q_R}$, $Q_R = A/4\ell_P^2$, and suppose $S_{\mathrm{eff}}\ll Q_R$ (so $d_{\mathrm{eff}}\le e^{Q_R}$
and an isometric embedding $V:P\mathcal H_\infty\hookrightarrow\mathcal H_Q$ exists).

**Claim.** For any protocol of length $T$ with instruments $\{\mathcal M_t\}$ and states $\rho_t$ obeying a
leakage bound $\operatorname{Tr}[(I-P)\rho_t]\le\eta$ at each step, the transcript distributions satisfy
$$\lVert p_\infty - p_Q\rVert_{\mathrm{TV}} \;\le\; C\,T\,\sqrt{\eta}.$$

**Key lemma (gentle measurement / projection).**
$$\Big\lVert \rho - \tfrac{P\rho P}{\operatorname{Tr}(P\rho)}\Big\rVert_1 \;\le\; 2\sqrt{\operatorname{Tr}[(I-P)\rho]}.$$
Propagate through the protocol by a hybrid / diamond-norm accumulation argument (energy-constrained diamond
norm for the infinite-dim legs).

**Where holography enters (the load-bearing physical input).** For weakly-gravitating matter the maximal
realizable entropy before black-hole formation is the ’t Hooft bound
$$S_{\mathrm{matter}}(R)\ \lesssim\ (A/\ell_P^2)^{3/4}\ \ll\ A/4\ell_P^2 = Q_R,$$
so all laboratory QFT lives in a subspace parametrically below the cap ⇒ the cap is inactive. It "bites" only
when $S_{\mathrm{eff}}\sim Q_R$ (black holes, de Sitter), or under $T\gtrsim e^{Q_R}$ / $N_{\mathrm{samples}}\gtrsim e^{2Q_R}$.

**Literature status (to verify before claiming novelty).** Ingredients exist and must be cited: gentle-
measurement lemma (Winter; Ogawa–Nagaoka), Fannes–Audenaert / Alicki–Fannes continuity, energy-constrained
diamond norms (Shirokov, Winter), Hamiltonian truncation, and the Bekenstein / ’t Hooft / Bousso bounds. Pro's
assessment: **no single theorem currently states "finite holographic information is empirically inert below
saturation"** — so the *synthesis* is the contribution. Confirm against the literature.

---

## 2. Corollary (computed) — Modular inertness on the verified χ_R object

Done concretely in `scripts/bekenstein_modular_inertness.py`. For a ball region $R$ and a coherent excitation
of energy $E$, the CHM modular Hamiltonian gives $\langle\Delta K\rangle \le 2\pi RE/\hbar c$, so by positivity
of relative entropy / the first law,
$$\frac{\chi_R}{Q_R} \;=\; \frac{S(\omega\Vert\omega_0)}{Q_R}\;\le\;\frac{2\pi RE/\hbar c}{\pi R^2/\ell_P^2}\;=\;\frac{2GE/c^4}{R}\;=\;\frac{R_s}{R}.$$
The finite-$Q_R$ correction to the **Araki/modular relative entropy QIQT-H already machine-checks (free-field
coherent sector)** is therefore **$O(R_s/R)$-suppressed** — i.e. suppressed by the **compactness** — and reaches
order one **only at $R_s/R\sim1$ (horizon formation)**. Numerical ladder (atom $6\times10^{-43}$ → Earth
$1.4\times10^{-9}$ → Sun $4\times10^{-6}$ → neutron star $0.35$ → black hole $1.0$). This converts the slogan
into a sharp bound *on the object the program actually verifies*, and is the cleanest "substance" deliverable.

**Optional sharper computation (pro):** mutual information $I_Q(A:B)$ between two separated balls (UV-finite,
the cleanest place a modification could show). Expected $I_Q - I_{\mathrm{QFT}}\sim e^{-Q_R}$ (door closes) or a
Planck-power $(\ell_P/L)^n$ (inaccessible EFT-type). Worth doing to close the entanglement door explicitly.

---

## 3. Theorem 2 — No covariant selector (the structural gem; narrow it)

Already machine-checked in spirit (the S² obstruction). State as: **there exists a Lorentz-covariant,
σ-additive, no-signaling Born measure $\mu_\Phi$ on the decoherent record/history space, and NO deterministic
Lorentz-equivariant selector $F:\Phi\mapsto\lambda$** — so single-outcome actualization is necessarily a
**symmetry-breaking sample** from a covariant *law*, not an equivariant *function* of the state. Pro: this
cleanly separates "covariant distribution" from "non-covariant individual sample," a distinction usually
blurred — and is publishable foundations/math-physics.

**Narrowing (mandatory, to avoid the referee):**
- Do **not** claim "solves what Everett/Bohm/CSL cannot." Everett needs no selected branch; Bohm has serious
  foliation/multi-time approaches; Tumulka's rGRWf is a relativistic flash collapse. Correct framing:
  *"QIQT-H avoids the dynamical-relativistic problems of collapse and Bohm because λ is non-dynamical and inert
  — the price is empirical equivalence and epiphenomenality."*
- σ-additivity is **trivial on a finite net**; the nontrivial content is **compatibility/covariance/no-signaling
  under the continuum / inverse-limit construction**. Say which you mean.
- No-signaling is a **verified property** of the measure, **not** a new physical mechanism.

---

## 4. Referee defense map (pre-empt)

1. **Epiphenomenal λ** ("Everett + an unobservable label") — *accept it*; it is an empirically conservative
   modal/Everettian interpretation with a covariant single-outcome measure. Do not fight this.
2. **Finite local algebras vs Type III / Reeh–Schlieder** — answer: **only the record net is finite; the
   underlying Φ evolves as standard QFT/Everett.** (Key defensive move — keeps us inside algebraic QFT.)
3. **Exact vs approximate decoherence** — the Lean theorem is exact-in-the-idealized-net; flag the gap to
   approximate physical implementation (Dowker–Kent residual).
4. **"You proved a theorem about your formal object — why is it the ontology?"** — the central vulnerability;
   answer with the inertness theorem (the formal object reproduces all QM phenomenology) + parsimony, not proof.

---

## 5. The four-condition no-go (why there is no lab effect, stated cleanly)

If (i) Φ evolves exactly unitarily, (ii) λ has no back-reaction, (iii) λ is Born-distributed in every context,
and (iv) observers access only λ-selected records — then operational predictions are **exactly QM**. Any
testable route must break one: collapse/back-reaction (→ DP/CSL, see `bekenstein_collapse_rate.py`,
`collapse_scaling_factor.py`; R_0 is atomic not holographic, `QR_derive_R0.py`), non-Born λ (→ Valentini
nonequilibrium, signaling), a final boundary condition $E_f\neq I$ (→ testable temporal correlations but
unconstrained without new physics), or measurement-context dependence (→ superdeterminism, not QIQT-H). **No
free lunch** — confirmed by pro.

---

## 6. The concrete to-do (what "making it work" means)

1. **Prove Theorem 1** (resource-bounded inertness) cleanly; cite the gentle-measurement/continuity machinery;
   verify no single theorem already states the holographic synthesis. → a standalone foundations result.
2. **Corollary 2 done** (`bekenstein_modular_inertness.py`); optionally add the $I_Q(A:B)$ mutual-information
   computation to close the entanglement door explicitly.
3. **Write up Theorem 2** (no covariant selector), narrowed per §3, leaning on the machine-checked S² obstruction.

These are **structural / mathematical** substance, not phenomenology. They predict **no** deviation; they make
precise *why* none is observable below saturation and *what* the single-world construction rigorously buys.
The honest one-line thesis: **finite holographic information is operationally invisible below saturation; the
nontrivial content is covariant σ-additive Born typicality + the no-covariant-selector theorem + the verified
χ_R calculus — not laboratory phenomenology.**
