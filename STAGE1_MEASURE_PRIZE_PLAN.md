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

## B. The crux: joint-law positivity, and the enabler it forces

The one genuinely hard sub-step is `P(a) = ω₀(∏ᵢ Bit(uᵢ, aᵢ)) ≥ 0`. Two routes:

- **(a) Operator positivity (clean, recommended).** Each `Bit(u,a)` is a **positive contraction**
  (`0 ≤ Bit ≤ I`): `Bit(u,T) = (2I + W(u) + W(−u))/4`, and `(W(u)+W(−u))/2 = Re W(u)` is self-adjoint
  with norm ≤ 1, so `Bit(u,T) ∈ [0,I]`. For symplectically-orthogonal `u,v` the bits **commute**
  (`weyl_microcausality`), so the product of commuting positives is positive, and `ω₀` is positive
  (`vacuumState_nonneg`) ⇒ `P ≥ 0`. *This needs `W(u)` as a genuine bounded operator with self-adjoint
  real part and an order/positivity API.*
- **(b) Explicit arithmetic.** Expand `P(a)` into vacuum amplitudes (`weyl2pt`, vacuum values — all real
  exponentials when `Im = 0`) and prove `≥ 0` directly. Direct check: `P(T,T) = (1/16)[4 + 4e^{−½‖v‖²} +
  4e^{−½‖u‖²} + 4e^{−½‖u‖²−½‖v‖²}cosh⟪u,v⟫]` — manifestly positive. But `P(T,F) = weylBitWeight u −
  P(T,T)` etc. need the marginal-dominates-joint inequalities, which get unwieldy for `n` bits.

**Decision: route (a).** It scales to `n` bits and is the conceptually correct argument (state on a
commutative subalgebra). It forces the **enabler**:

### B.0 (enabler) — `W(u)` as a bounded operator + `Bit(u,a)` as a positive effect

Currently `weylH u` is a *function* (`Completion.map`) + an isometry; `weylPre u` is a `LinearMap` on
the dense pre-space. For route (a) I need:
- `W(u)` (or at least `Re W(u)`) as a **`Fock H →L[ℂ] Fock H`** (bundle `Completion.map`'s linearity —
  the additive/`ℝ`-linear extension is standard; or build `weylH` as a `LinearIsometryEquiv` directly).
- `Bit(u,a) : Fock H →L Fock H`, with `IsSelfAdjoint`, `0 ≤ Bit`, `Bit ≤ 1` (a custom `Effect` structure
  via quadratic-form inequalities `0 ≤ re⟪x, Bit x⟫ ≤ ‖x‖²` — GPT's suggested shortcut to dodge the
  missing `StarOrderedRing (B(H))` C\*-order API).
- `commute (Bit u a) (Bit v b)` from `weyl_microcausality` (lifted to `weylH`).
- `0 ≤ ω₀(Bit(u,a) Bit(v,b))` from "product of commuting positives is positive" + `vacuumState_nonneg`.

This is the real next increment and the gateway to the whole of Stage 1.

---

## C. The staged increments

| Step | Target | Builds on | Difficulty |
|---|---|---|---|
| **B.0** | `W(u)`/`Re W(u)` as a bounded `CLM`; `Bit(u,a)` as a positive `Effect`; commutation lifted; `ω₀(Bit·Bit) ≥ 0` | `weylH`, `weyl_microcausality`, `vacuumState_nonneg` | M (Completion linearity + a custom `Effect` struct) |
| **1.1** | two-bit joint Born law `P(a,b) = ω₀(Bit(u,a)Bit(v,b))`: probability distribution (≥0, Σ=1) + **boost-covariant** | B.0, `weyl2pt_boost_invariant` | M |
| **1.2** | `n`-bit joint law over a mutually-isotropic family; **projective** (coarse-grain consistent) + boost-covariant; the *compatible record framework* (Fine/Bell satisfied since all commute) | 1.1 | M–L |
| **1.3** | feed the boost-covariant projective family into `KolmogorovFiniteFiber.exists_isLimit` → **`μ∞` with `μ∞.map(historyBoost β t) = μ∞`** | 1.2, existing Kolmogorov | M |

**1.2 soundness note (the Fine/Bell gate).** A *mutually symplectic-orthogonal* family is an **isotropic
subspace** of the one-particle space; the Weyl observables `{Φ(uᵢ)}` mutually commute, generating an
**abelian CCR subalgebra**, on which `ω₀` restricts to a genuine **classical (Gaussian) probability
measure** (Gelfand/Bochner). This is exactly the "single compatible/decoherent record framework" the
soundness gate requires — Fine's theorem is *satisfied*, not violated, because there is no incompatibility
in an isotropic family. (Cross-check this framing with GPT when reachable.)

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

## F. Immediate next action

Start **B.0**: bundle `W(u)`/`Re W(u)` as a bounded operator on `Fock H` and define `Bit(u,a)` as a
positive `Effect`, with `ω₀(Bit(u,a)Bit(v,b)) ≥ 0` for commuting bits. Then **1.1**.
