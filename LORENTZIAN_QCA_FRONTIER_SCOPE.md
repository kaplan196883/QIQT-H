# Scoping the Lorentzian finite-capacity substrate frontier

**Status:** SCOPE (2026-06-30), grounded in a GPT-5.5-pro consult. **Origin:** the QG campaign
(`QG_CAMPAIGN_PLAN.md`) closed with **I4 = FAIL (CPSUV)** — a naive "finite capacity = Lorentz-violating hard
spatial cutoff" radiatively generates unsuppressed dim-4 Lorentz violation `Δc² → (4/3)·g²/16π²`. The named next
frontier was "a Lorentzian QCA substrate that shows `Δc²(Λ) → 0`." This scope is honest about whether that is a
real prospect.

## Bottom line (blunt)

> **A regular local quantum cellular automaton (QCA) is an excellent FREE emergent-Dirac substrate, but it is
> NOT a credible standalone escape from CPSUV.** A finite-range QCA has a preferred lattice/foliation frame, so
> the marginal Lorentz-violating kinetic operators are symmetry-allowed and will be generated at `O(g²/16π²)`
> under interactions — exactly like the cutoff — *unless an actual protecting symmetry or a covariant/nonlocal
> regulator forbids them.* No interacting 3+1D finite-local-Hilbert QCA is known for which a one-loop `Δc²` has
> been shown to vanish without tuning. So the "Lorentzian QCA" frontier splits into two very different things:
> **(A) a decisive falsification experiment** (expected to FAIL — and that failure is informative), and **(B) the
> real QIQT-H route: covariant *holographic/nonlocal* finite capacity**, where the I4 kill — of the *local-cutoff
> strawman* — may simply not apply. (B) is a research program, not a QCA simulation.

---

## 0. Why this frontier exists (what the campaign fixed)

- **I3** (free): a free lattice/QCA dispersion's Lorentz defect is `O((ap)²)`, α=2, **no rapidity floor** — free
  Lorentz emergence is easy and real.
- **I4** (interacting, decisive): with a *preferred-frame* regulator, interactions drive `Δc² = Z_s/Z_t − 1` to a
  nonzero `O(g²/16π²)` constant (CPSUV). The free pass does **not** survive interactions.

So the binding question is **dynamical/radiative**: can a finite-capacity *Lorentzian* substrate keep `Δc²`
suppressed at the interacting/loop level? This scope answers "how would we test it, and where does the real
answer live."

---

## 1. The free substrate base — the Dirac/Weyl QCA *(mature; days–weeks)*

**1+1D Dirac walk** (two components `R,L`, exact local unitarity), the cleanest to simulate:
```
ψ_R(t+τ, x) = n·ψ_R(t, x−a) − i m·ψ_L(t, x)
ψ_L(t+τ, x) = n·ψ_L(t, x+a) − i m·ψ_R(t, x) ,   n = √(1−m²)
```
Momentum-space step `U(k) = n cos(ka) I − i(m σ_x + n sin(ka) σ_z)`, dispersion `cos(ωτ) = n cos(ka)` ⟹
`E² = M² + c²p² + O(a²p⁴)` — matches I3 (α=2, no floor).

**3+1D Weyl/Dirac walk:** conditional shifts `S_i(k) = cos(k_i a) I − i sin(k_i a) σ_i`, `A(k)=S_x S_y S_z`;
Dirac couples two Weyl sectors via a local mass coin, `cos(ωτ) = n_m d(k)`. The raw chiral walk has a leading
*anisotropic* tree defect `O(a p_x p_y p_z)`; use the **parity/time-reversal-symmetric split-step (Strang)
Dirac walk** to get a genuine `O((ap)²)` free defect (`H_eff = α·p + βM + O(a²p³)`). For simulation the
symmetric split-step / collide-stream form is cleaner than the axiomatic BCC construction.

*Refs:* Bialynicki-Birula PRD 49 (1994); Meyer JSP 85 (1996); Strauch PRA 73 (2006); D'Ariano–Perinotti PRA 90
(2014); Bisio–D'Ariano–Perinotti–Tosini FoP 45 (2015); Arrighi, Nat. Comp. 18 (2019).

**Increment F (buildable now):** implement the symmetric split-step 3+1D Dirac QCA; verify its free dispersion's
Lorentz defect is `O((ap)²)` with no floor — the QCA confirmation of I3. *Days.*

---

## 2. The decisive QCA experiment — the interacting one-loop `Δc²` *(weeks–months; expected FAIL)*

**Model (minimal, marginal coupling — NOT a 3+1D four-fermion contact, which is irrelevant and gives false
comfort):** a symmetric split-step Dirac QCA `Ψ` + a scalar quantum walk `Φ` + a **local Yukawa kick**
`U_int = exp[−i g τ ∑_x Φ_x Ψ̄_x Ψ_x]`, assembled as a symmetric Floquet step `U = U₀^{1/2} U_int U₀^{1/2}`.
(For strict finite local Hilbert, truncate the scalar oscillator / use a hard-core boson and check truncation
stability.)

**Observable:** extract the dressed one-particle pole `E_X²(p) = M_X² + c_X²|p|² + O(p⁴)` for each species and
form `Δc² = c_ψ²/c_φ² − 1`. **Tune the free speeds equal at `g=0`, then turn on `g` — do NOT retune a velocity
counterterm at each `a`** (that would make the test vacuous).

**Method — QCA/Floquet lattice perturbation theory** (cleaner than exact diagonalization, which sees no radiative
dressing in a number-conserving one-particle sector — it needs the virtual multiparticle/Floquet-vacuum
sectors): discrete propagator `G₀⁻¹(ω,k) = I − e^{iωτ} U(k)`, `ω ∈ (−π/τ, π/τ]`; one-loop self-energy
`Σ = g² ∫_{BZ} (dΩ d³q) Γ G₀(ω−Ω, p−q) Γ D₀(Ω,q)`; project `δZ_t ~ Tr[γ⁰ ∂Σ/∂ω]₀`,
`δZ_s ~ −⅓ ∑_i Tr[γⁱ ∂Σ/∂p_i]₀`. Plot `K(a) = (16π²/g²)·Δc²(a)` as `a→0` at fixed physical renormalization point.

**Validation gate (mandatory, before trusting the QCA number):** reproduce **K = 0** for a Lorentz-covariant
regulator and **K = O(1)** for a hard preferred-frame cutoff (i.e. re-derive I4 in this code). Only then evaluate
the QCA.

- **PASS:** `Δc²(a) ~ (aμ)^α` or `= 0` *by an identifiable Ward identity*. (One-loop `K=0` alone is NOT a pass —
  accidental cancellation is not protection; must identify the symmetry and test other interactions / two loops.)
- **FAIL (expected):** `Δc²(a) → K·g²/16π²`, `K ≠ 0`. QCA-ness itself is then **not** protection.

**Increment Q (the decisive experiment):** the above. *Weeks–months.* Its value is **falsification**: a clean
FAIL (the likely outcome) rigorously closes the "unprotected QCA escape" and forces QIQT-H to §3.

---

## 3. The real route — covariant holographic/nonlocal finite capacity *(research program; where the answer lives)*

The I4/CPSUV kill is specifically a kill of the **local-cutoff strawman**: independent Planck cells, a local
spatial-`|k|` cutoff, a preferred frame. It does **not** prove that *every* finite regional/holographic
Hilbert-space theory radiatively violates Lorentz invariance. QIQT-H's capacity is **regional/holographic**, not
a local UV lattice — so a genuinely holographic finite capacity would not regulate loops by cutting spatial
modes in a preferred frame, and the dim-4 LV operators could simply be **absent**.

**But this is a burden, not a slogan.** To be more than hope, QIQT-H must establish at least one of:
1. **No preferred `n^μ`** in the low-energy effective action (the finite capacity leaves no frame vector), or
2. **Ward identities forcing `Z_t = Z_s`** (an exact Lorentz/diffeomorphism symmetry of the UV completion), or
3. **Covariant low-energy amplitudes** after the holographic UV completion (computed, not assumed).

This is the honest frontier. Concrete (research-grade) sub-questions: does the regional capacity bound, imposed
*covariantly* (per causal diamond, à la Bousso/CEB — not per spatial cell), avoid sourcing a preferred frame? Do
the edge/gauge/code degrees of freedom carry the Lorentz Ward identity? This is where the crossed-product /
modular-flow machinery (which IS covariant) plausibly reconnects — modular flow has no preferred lab frame.

---

## 4. Branch logic (what each outcome forces)

| Outcome | Consequence |
|---|---|
| Increment Q **FAILs** (`K≠0`, expected) | The unprotected Lorentzian QCA is dead. Finite capacity is **not** a local Lorentzian substrate. QIQT-H must commit to §3 (covariant holographic) — or concede finite capacity cannot be dynamically Lorentzian. |
| Increment Q **PASSes** (`K=0`) | Not yet a win — must identify the protecting Ward identity (§3.2) and test other interactions / two loops. A real but surprising result that would redirect effort to *why*. |
| §3 burden met (a Ward identity / covariant amplitudes) | The genuine escape — finite *holographic* capacity is Lorentz-safe. This is the prize, and the hardest part. |

---

## 5. Protection-mechanism ledger (viability for a finite-capacity theory)

- **(a) Exact/enhanced symmetry, SUSY-like cancellation** — *real* mechanism (Groot Nibbelink–Pospelov PRL 94
  (2005): exact SUSY forbids dim≤4 LV; soft breaking reintroduces it only `~(m_soft/M_UV)²`). **No** buildable
  3+1D finite-local-Hilbert QCA with realistic SUSY + chiral matter + proven suppression exists.
- **(b) RG irrelevance** — **NO** (generic): the LV operator is *marginal*; CPSUV = irrelevant-UV-LV feeds
  marginal-IR-LV. Only special critical/strongly-coupled fixed points drive speeds together (Chadha–Nielsen NPB
  217 (1983); Anber–Donoghue PRD 83 (2011); Bednik–Pujolàs–Sibiryakov JHEP 2013) — too slow (logarithmic) in
  weakly-coupled 3+1D.
- **(c) Lorentz-invariant discreteness (causal sets)** — a *real conceptual* route (Poisson sprinkling is
  Lorentz-invariant in distribution; Bombelli–Lee–Meyer–Sorkin PRL 59 (1987)) but **NOT a lattice QCA** (no fixed
  tensor factorization, no synchronous local update; needs nonlocal d'Alembertians; interacting radiative
  stability unsettled). "Lorentzian QCA" with a regular lattice is in tension with exact Lorentz invariance.
- **(d) Nonlocality / holographic regional capacity** — **the plausible QIQT-H escape** (§3). Real *iff* the
  covariance burden is discharged; otherwise it is hope.

---

## 6. Honest difficulty + the first increment + the kill criterion

- Free QCA (Increment F): **days**.
- Clean 1+1D interacting toy: **weeks** (not decisive for CPSUV).
- 3+1D one-loop Floquet/QCA Yukawa `Δc²` (Increment Q): **weeks–months**.
- Strict nonperturbative finite-local-Hilbert 3+1D QCA with controlled continuum limit: **years**.
- Covariant holographic finite-capacity construction (§3): **a research program**.

**First increment (most informative): Increment Q** — the one-loop Floquet `Δc²` on the Yukawa-coupled
split-step Dirac+scalar QCA, *validated* against I4 (K=0 covariant, K=O(1) cutoff). **Kill criterion:** a clean
`Δc²(a) → K·g²/16π²`, `K≠0` — combined with the EFT fact that the marginal LV operator is symmetry-allowed — is
enough to close the unprotected-QCA branch (no need to test every QCA). That negative result then makes §3
(covariant holographic) the *only* live route, or forces the honest concession that finite capacity cannot be a
local Lorentzian substrate.

**Net:** the value of building Increment Q is a decisive falsification; the value of QIQT-H's distinctive bet is
entirely in §3 (covariant holographic capacity). Never claim QG or the value of `G`; the `1/4` *ratio* is derived
(`SakharovRatio.lean`).

---

## 7. Key references

Collins–Perez–Sudarsky–Urrutia–Vucetich PRL 93 191301 (2004); Groot Nibbelink–Pospelov PRL 94 081601 (2005);
Bolokhov–Groot Nibbelink–Pospelov PRD 72 015013 (2005); Karsch NPB 205 (1982); Klassen NPB 533 (1998);
Chadha–Nielsen NPB 217 (1983); Anber–Donoghue PRD 83 (2011); Bednik–Pujolàs–Sibiryakov JHEP 2013;
Bialynicki-Birula PRD 49 (1994); Meyer JSP 85 (1996); Strauch PRA 73 (2006); D'Ariano–Perinotti PRA 90 (2014);
Bisio–D'Ariano–Perinotti–Tosini FoP 45 (2015); Arrighi Nat. Comp. 18 (2019); Bombelli–Lee–Meyer–Sorkin PRL 59
(1987); Benincasa–Dowker PRL 104 (2010).
