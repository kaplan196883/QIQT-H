---
layout: ../layouts/Deep.astro
title: The theory
eyebrow: The mathematics
description: The finite-information axiom (FQ) as a record stage, the regional cost functional χ_R as Araki relative entropy, Type II regional algebras, the retirement of the H2 conjecture, and single outcomes by λ-selection.
---

The framework has three moving parts: a capacity axiom (the finite record *stage*), a cost functional for
regional information, and a non-dynamical actuality selector λ that draws the single-world conclusion. (A
fourth, earlier part — a conjecture tying *two actual records* to a capacity *overflow* — has been withdrawn
as a category error; see below. Capacity bounds the *number* of records, not whether two can be actual.)
Only the cost functional's underlying calculus is [machine-verified](/formalization); the rest is stated
honestly as postulate or open.

## 1. Finite regional capacity (FQ)

A bounded region $R$ with boundary area $A$ carries a finite information capacity

$$ Q_R \;=\; \frac{A}{4\ell_P^2}, $$

the holographic / Bekenstein–Hawking bound, with $A$ the boundary area of the region and $Q_R$ in natural
entropy units (divide by $\ln 2$ for bits). In QIQT-H this enters as a **postulate** about physically
instantiable content, not merely about thermodynamic entropy: the renormalized information of any state the
region actually realizes obeys $S_{\mathrm{ren}} \le Q_R$. Grounding this bound from a more primitive
principle, and stating it cleanly in the continuum, is one of the [open problems](/open-problems).

## 2. The cost of regional content: $\chi_R$

To compare "how much information" two regional states carry, QIQT-H uses the **Araki relative entropy**
$S(\omega \,\|\, \omega_0)$ of a state $\omega$ against a reference $\omega_0$ (the local vacuum). For a
bounded region the local algebra is not the familiar Type I factor of ordinary quantum mechanics; in
relativistic field theory it is a **Type III$_1$** von Neumann algebra. Araki relative entropy is already
well defined there. The **Type II** "dressed" algebras — which carry a trace-like *generalized* entropy —
come from the gravitational crossed-product construction of Chandrasekaran–Penington–Witten and Witten;
QIQT-H borrows that picture as motivation, it is not something established here. The regional cost
functional is

$$ \chi_R(\omega) \;=\; S\big(\omega \,\|\, \omega_0\big), $$

computed through Tomita–Takesaki modular theory: the modular operator $\Delta$, the modular conjugation
$J$, and the modular flow $\Delta^{it}$ of the reference state. (Identifying this vacuum-relative
distinguishability functional with the *cost to instantiate* regional content is itself part of the
QIQT-H hypothesis, not a theorem.) For coherent excitations $W(f)\Omega$ of a free field this reduces to an
explicit one-particle expression, the Casini–Grillo–Pontello entropy $S_{\mathrm{CGP}}(f)$, and **this
coherent-state reduction is what the Lean development checks**, end to end, from the bounded modular
operators to the entropy-reduction identity.

<div class="note">

<strong>Scope.</strong> What is verified is the modular and relative-entropy
<em>calculus</em> for the free-field coherent sector, the bookkeeping machine for <em>χ<sub>R</sub></em>. The verified
part does <strong>not</strong> include the Type&nbsp;II regional construction itself, the (FQ) axiom, or
the conjecture below.

</div>

## 3. The retired conjecture: macroscopic definiteness (H2)

The program's original load-bearing claim — the **Macroscopic Definiteness Conjecture** — was that two or
more distinct macroscopic records being *actual* together in a region would have joint cost exceeding the
capacity $Q_R$, so finite capacity itself forces a single outcome. **This is now retired as a category
error** (2026-06-15), and we record the retirement plainly rather than keep it as "the crux."

Why it fails: a holographic bound counts *independent* degrees of freedom (joint entropy / code dimension),
**not** a sum of redundant classical records — $R$ redundant copies of one fact carry joint entropy $H(X)$,
not $R\,H(X)$ (machine-checked). Ordinary, weakly-gravitating record entropy is moreover capped at
$\sim(A/\ell_P^2)^{3/4}$, parametrically *below* $A/4\ell_P^2$ (only a black hole saturates $A/4$, and it has
no records); for the observable universe that is $\sim 10^{91}$ against $\sim 10^{122}$ — a permanent ~31-order
gap, and the universe runs at $\sim 10^{-18}$ of its holographic capacity. And the $\log 2$ data-processing
estimate confirms two records cost about *one bit* more than one, not an area-scale $Q_R$. Finally, by exact
unitary linearity, finite capacity can neither forbid a superposition nor select a branch. So $Q_R$ does
**not** do the single-outcome work; it is the finite record *stage* (a cardinality bound). The single
outcome is supplied by $\lambda$ — the next section.

## 4. Single record — by selection, not by capacity

After decoherence has stabilized and proliferated the macroscopic records (making them non-interfering and
redundantly objective), the content the region *realizes* is one definite macroscopic world — while $\Phi$
keeps all branches and evolves exactly unitarily, with no collapse term. **The single record is supplied by
the non-dynamical selector $\lambda$**, an Everett-like selection among the unitarily-evolved alternatives.

<div class="note">

<strong>Where the exclusion really comes from.</strong> Since capacity does not forbid two
records (§3), what makes a region's <em>actual</em> content single-valued is just that a classical carrier
holds <em>one</em> value — local single-valuedness — and which value is the actual one is supplied by λ. The
Lean development machine-checks a finite, additive-cost <em>counting</em> bound (at most one member of a
saturating family), an honest <em>finite stage</em>; it does <strong>not</strong> derive that capacity
overflows on two macroscopic records.

</div>

This is worth stating carefully, because "one outcome" and "unitary evolution" sound contradictory. The
global wave function evolves unitarily throughout; the single *actual* record is a [selection](/selection)
by λ among the unitarily-evolved alternatives, not a dynamical modification of the Schrödinger equation — the
[(Φ, λ) account](/selection). Making that selection precise, and deriving its statistics, is the
dynamical-realization and Born problem below. Q<sub>max</sub>'s role is the finite record *stage* (how many
distinguishable records exist), not the selection.

Recent progress has made λ's *selection schema* precise where it can be — machine-checked, axiom-free, at the
**finite**, the **one-particle continuum** (the bounded modular flow $\Delta^{it}$), *and* the
**second-quantized free-field** ($\Gamma(\Delta^{it})$, a unitary group) levels. (We say *schema*, not *law*:
"axiom-free in Lean" means no extra Lean axioms, not no physical postulates — those are the hypotheses below.)
The records come from a chosen abelian coarse-graining *associated with* the Type&nbsp;III$_1$ algebra (it has
no atoms), and **Takesaki's criterion** fixes which record context is consistent — the modular flow fixes a
projection iff it commutes with the (faithful, reduced) state, $[\rho,P]=0$, *exact decoherence*. The dephasing
map is then the state-preserving conditional expectation onto the (generally nonabelian) block-diagonal algebra,
and the Born weights $\omega(P_\alpha)$ are a genuine probability (on the Fock vacuum state the single-mode
Weyl-bit effect gives $(1\pm e^{-\lVert u\rVert^2/2})/2$). One *consistency* result: the dephasing map commutes
with the modular flow $\sigma_t$ for every $t$ — no *modular* recoherence in the chosen invariant algebra. But
the modular flow is **not** the physical Hamiltonian evolution (they agree only in special KMS /
Bisognano–Wichmann cases), so this is modular-invariance, *not* a proof that real records never recohere under
the actual dynamics.

The **selection event** has an explicit constructor too (`SelectionEvent.lean`): an **inverse-CDF** selector
from an "actuality seed" $s\in[0,1)$ picks **exactly one** record per seed (totality + uniqueness of a sampling
map), and the *single-shot* seed measure of record $k$ equals its Born weight $p_k$. It adds no actualization
*mechanism*, and a single-shot measure is *not yet* an across-run frequency (that needs a product measure + a
law of large numbers). The selector is order-dependent, not equivariant (as the no-covariant-selector result
requires); the seed measure is order-blind.

Two honest caveats remain — now in their *irreducible* form. First, the construction reduces the whole selection
to one datum: *which seed is actual*. The seed **is** λ — the one primitive a non-dynamical single-world theory
must take as given; its origin is not, and arguably cannot be, derived. Second, the weights enter as an input
here; deriving them as across-run **frequencies** rests on a premise the Born no-go proves unremovable.

## 5. Born statistics

That outcome $k$ occurs across runs with frequency $|c_k|^2$ is the **Born rule**. QIQT-H recovers it from
typicality: over the measure of microscopic initial conditions compatible with a given preparation, the
realized single-record outcome has frequency $|c_k|^2$ for *typical* initial data. Substantial progress is now
machine-checked (axiom-free): a Lorentz-covariant, σ-additive, decoherent-histories-*consistent* Born measure
on the free-field record net **exists and is verified**, and Born is **reduced** to a single
*state-supervenience* premise — via the Zurek envariance symmetry (proved) and an orthonormality bridge — with
a [no-go](/born) showing some such premise is unavoidable (naturality alone is not enough; refinement-additivity
is what fixes the square). What remains: justifying that premise as *forced* rather than merely motivated, and
the continuum/interacting realization. Born is an honest *reduction*, not yet a derivation from nothing.

---

The status, at a glance: **(FQ)** postulate · **$\chi_R$ calculus** machine-verified · **H2** *retired*
(category error — capacity does not forbid records) · **single record** supplied by λ (selection postulate;
covariance + contextuality + no-signaling machine-checked; dynamical-realization gap open) · **Born** reduced
(axiom-free) to a state-supervenience premise. The whole development is **axiom-free**. The
[formalization](/formalization) page documents exactly which pieces are checked; the
[open problems](/open-problems) page lays out the remaining frontier (λ's law, the continuum).
