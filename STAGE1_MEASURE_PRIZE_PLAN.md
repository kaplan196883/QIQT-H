# Stage 1 — the measure-level boost-covariant typicality measure (plan)

*The path from the now-complete continuum free-field algebraic spine to the literal
`μ∞.map(boost) = μ∞`. Written 2026-06-08. A live GPT-5.5-pro consult was attempted but its API was
down (4 consecutive failures); this plan is grounded in GPT's **prior** detailed review (2026-06-08,
recorded in `project_qiqth_prize_roadmap` memory) plus direct arithmetic checks. Re-consult GPT when its
API recovers to pressure-test §A.1 and the positivity route.*

---

## A. The honest strategic picture (what Stage 1 is, and is not)

**What's done (axiom-free):** the entire algebraic spine — bosonic Fock space, coherent states, the
quasifree vacuum **state** `ω₀`, the **bounded Weyl operators** `W(u)` (isometric, CCR-unitary), the
**boost-invariant vacuum 2-point function** `weyl2pt`, **microcausality** (spacelike ⇒ commute), and the
abstract σ-additive Kolmogorov μ∞ pipeline.

**Stage 1 target:** a *boost-covariant commuting-Weyl-bit net* → `μ∞.map(boost) = μ∞`, abstracting the
spacetime geometry into hypotheses (index set `I`, boost `β` permuting `I`, covariant `u : I →
OneParticle` with `u(β t i) = U₁(t)(u i)`, mutual symplectic-orthogonality `Im⟪u i, u j⟫ = 0`).

### A.1 Is Stage 1 genuine, or just the i.i.d. mode-permutation result re-skinned?

**Honest answer (GPT's prior caveat + analysis): Stage 1 is an *abelian-sector* result — genuinely
stronger than the finite-mode i.i.d. result, but NOT yet the full Haag–Kastler prize.** Two things make
it genuinely stronger, and one honest limitation:

- **(+) The per-context law is the genuine quasifree vacuum law, not a chosen i.i.d. `ν`.** The joint
  Born law of a commuting family `{Φ(uᵢ)}` under `ω₀` is the **Gaussian free-field measure** whose
  covariance is the real two-point function `weyl2pt` — a *correlated* measure derived from the vacuum,
  not a product measure stipulated by hand. `FreeFieldTypicality` chose `ν`; here `ω₀` *forces* it.
- **(+) Boost-covariance is derived from `ω₀`'s Lorentz-invariance**, not assumed: it rides
  `weyl2pt_boost_invariant` + `u(β t i) = U₁(t)(u i)`, i.e. the genuine field covariance, not a relabeling.
- **(−) The boost still acts by PERMUTING an abstract `I`.** Its full physical force (Einstein locality,
  no-signaling between *spacelike regions*) only bites once `I` is the genuine spacelike-local record set
  — that is **Stage 2** (the localization map). Without it, Stage 1 is "covariant typicality measure on
  the free Gaussian field's commuting-observable histories," which is a real, citable result, but the
  word *Lorentz-covariant* is honest only up to the abstract `β`-action.

**Verdict:** worth doing — it is the genuine measure-level theorem the whole program was aiming at, on
the genuine quasifree field — but the abstract must be stated with the honest caveat, and the headline
"relativistic / Haag–Kastler" claim waits on Stage 2.

---

## B. The crux: joint-law positivity — solved by a NORM-SQUARE representation (GPT consult #2)

GPT-5.5-pro's key refinement (2026-06-08): **don't fight positivity with operator order or alternating
arithmetic — make `P` a literal norm-square, and do all of Stage 1 on the pre-Fock space.** Define, for
sign `s = ±1`,
```
A_i^s := (I + s·weylPre(u_i)) / 2.
```
Since `W(u)* = W(−u)`, the bit effect `E_i^s = (2I + s·W(u_i) + s·W(−u_i))/4 = (A_i^s)* A_i^s`, so for a
commuting (isotropic) family
```
∏_{i∈F} E_i^{s_i} = (∏ A_i^{s_i})* (∏ A_i^{s_i}),   and   P_F(s) := ‖ ∏_{i∈F} A_i^{s_i} Ω ‖²  ≥ 0.
```
**Positivity is then FREE** (a norm-square), scales to all `n`, needs **no** operator-order theorem and
**no `ContinuousLinearMap` bundling** — everything is `weylPre` + `fockInner`. The proof recipe:

1. **Definition / positivity.** `A_{L,s} = ∏_k (I + s_k·weylPre(u_{i_k}))/2` on `FockPre`; `P_L(s) =
   ‖A_{L,s} Ω‖² = fockInner (A_{L,s}Ω) (A_{L,s}Ω)`. `≥ 0` immediate.
2. **Normalization (Σ = 1).** The isometry identity `‖(ψ+Wψ)/2‖² + ‖(ψ−Wψ)/2‖² = ‖ψ‖²` (uses only
   `W` isometric), inducted over the list.
3. **Projectivity (coarse-grain consistency).** Order the larger list with retained coordinates first,
   forgotten last; sum forgotten signs one at a time via the same identity; pairwise commutation
   (`weyl_microcausality`) gives order-independence.
4. **Boost-covariance.** Expand `A_{L,s}Ω` as a finite combination of coherent vectors `W(∑_{i∈S}u_i)Ω`;
   its Gram matrix is built from inner products / norms of *sums* of `u_i`, all preserved by `U₁(t)` +
   equivariance `u_{β t i} = U₁(t) u_i`.
5. **Kolmogorov.** Feed `P_F` into `KolmogorovFiniteFiber.exists_isLimit` → `μ∞` with `(β t)_*μ∞ = μ∞`.

`B.0` (bundle `W(u)` as a CLM, `E_i^s` as positive effects) is then **semantically nice but NOT
logically required** — do it *after* Stage 1, to prove the equivalence `P_F(s) = ω₀(∏ E_i^{s_i})` and
package the result in standard operator-state language.

---

## C. The staged increments (revised per GPT consult #2 — B.0 deferred)

| Step | Target | Builds on | Difficulty |
|---|---|---|---|
| **1.1** | the bit vectors `A_i^s Ω` on `FockPre`; two-bit law `P(s,s') = ‖A_i^s A_j^{s'} Ω‖²` — prob. dist. (≥0 free, Σ=1 via the isometry identity) + the **non-product** law `E[S_iS_j]=e^{−(‖u_i‖²+‖u_j‖²)/2}cosh(Re⟪u_i,u_j⟫)` (kills "just a permutation") | `weylPre`, `fockInner`, `weyl_microcausality` | M |
| **1.2** | `n`-bit law `P_F(s)=‖∏A_i^{s_i}Ω‖²`: probability + **projective** + **boost-covariant** (the recipe above) | 1.1 | M–L |
| **1.3** | `KolmogorovFiniteFiber.exists_isLimit` → **`μ∞` on `{±1}^I` with `(β t)_*μ∞ = μ∞`** | 1.2, existing Kolmogorov | M |
| **B.0** (after) | bundle `W(u)` as CLM, `E_i^s` as a positive `Effect`, prove `P_F = ω₀(∏ E_i^{s_i})` — operator-state packaging | Stage 1 done | M |

**Soundness gate (GPT-confirmed).** A mutually symplectic-orthogonal (isotropic) family generates an
**abelian CCR subalgebra**; `ω₀` restricted to it is a genuine **classical Gaussian measure**
(`C_ij = Re⟪u_i,u_j⟫`), so `P_F(s) = ∫ ∏ (1+s_i cos X_i)/2 dN(0,C_F)` — exactly the compatible/decoherent
record framework the gate requires; Fine's theorem is *satisfied*, no trap for finite `n`. (Trap only if
one were to put **noncommuting** Bell settings in a single global `I` — which we never do.)

**Wording discipline (GPT):** call it a **boost-invariant abelian Weyl-bit *process***, not yet
"Lorentz-covariant free-field typicality"; finite laws are **determined by** the quasifree two-point
function / Gram covariance (do *not* claim the bit covariance *equals* the two-point function). Use
`φ(T)=⟪Ω,TΩ⟫` (not the real-part `ω₀`) when speaking C\*/Bochner; real parts only on self-adjoint effects.

---

## D. What Stage 1 does NOT give (honest boundary) → Stage 2

- The boost acts on an **abstract** `I`; genuine spacelike locality / no-signaling needs `I` = the real
  spacelike-local record set. That is the **localization map** `K : TestFun → OneParticle`,
  `Im⟪Kf,Kg⟫ = 0` for spacelike supports (Pauli–Jordan), `K(boost·f) = U₁(t)(Kf)` — Stage 2,
  multi-month (Fourier / mass-shell / Minkowski geometry), partly citable (Pauli–Jordan vanishing).

## E. Strongest honest claim once Stage 1 is done (Stage 2 not)

> "We machine-check, axiom-free, a Lorentz-boost-covariant σ-additive typicality measure on the
> histories of any commuting (isotropic) family of free-field observables, with the joint statistics
> forced by the quasifree vacuum state (the Gaussian free-field measure, covariance = the vacuum
> two-point function); the spacelike-local *instantiation* of the index by genuine spacetime regions
> (Pauli–Jordan) remains."

## F. Immediate next action (revised)

Start **1.1**: on `FockPre`, define the bit vectors `A_i^s Ω = (Ω + s·weylPre(u_i)Ω)/2`, the two-bit law
`P(s,s') = ‖A_i^s A_j^{s'} Ω‖²` via `fockInner`; prove it's a probability distribution (≥0 free; Σ=1 via
the isometry identity `‖(ψ+Wψ)/2‖²+‖(ψ−Wψ)/2‖²=‖ψ‖²`) and the **non-product** correlation
`E[S_iS_j]=e^{−(‖u_i‖²+‖u_j‖²)/2}cosh(Re⟪u_i,u_j⟫)`. No CLM bundling (B.0 is deferred to after 1.3).

## G. Honest distance (GPT consult #2)

- **Abstract boost-invariant abelian Weyl-bit process** (the Stage-1 theorem): **~60–70%** via the
  pre-Fock norm-square route (≤60% if one insists on the CLM/effect API first — hence defer it).
- **Localized free-field record measure** (the full prize): **35–45%** now → **55–65%** after Stage 1 →
  **80–90%** after Stage 1 + B.0 + Stage 2. (Never 100% without theorem packaging, concrete index
  choices, and measurability details.)
- **Stage 1 is the highest-value next target.**
