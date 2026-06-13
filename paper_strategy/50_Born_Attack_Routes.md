# 50 — Born Exponent: Attack Routes (GPT-5.5-pro consult, 2026-06-13)

This document records the three attack routes on the Born **exponent** (why `p_k ∝ w_k` and not
`w_k^α`), GPT-5.5-pro's assessment, the new routes it surfaced, and which pieces are now
machine-checked (`QIQTH/BornRoutes.lean`, axiom-free).

## The single open problem (restated)

Everything up to the exponent is machine-checked (records ⇒ definiteness; refinement-additivity ⇔
Born; no-signaling ⇔ Born; uniform typicality + weight-encoding ⇒ Born). The α-family
`f(w)=w^α` (α≠1) satisfies **every** Born-free structural premise yet is **not** Born — it is the
proven countermodel (`RefinementBorn.alphaSq_ne_born`). So closing Born = supplying exactly one
extra premise that **breaks the α-symmetry**. The whole question is: *can that premise be derived
from QIQT-H dynamics rather than assumed?*

## The three routes written down

- **Route A — capacity counting / MaxEnt.** Maximise entropy of the outcome distribution subject to a
  capacity/cost constraint; hope Born falls out. **Pro's verdict: obstruction, not a closure.** A flat
  MaxEnt gives uniform (dimension counting), not Born; any *additive* per-branch cost reproduces the
  whole `w^α` family (α = the cost's exponent). Best repurposed as a **no-go**: "no symmetric additive
  cost singles out α=1."

- **Route B — uniqueness of the equivariant measure.** Argue the only dynamics-invariant typicality
  measure is `|Ψ|²`. **Pro's verdict: only closes with Bohm-grade extra structure** (a guidance
  current + locality). For a bare finite deterministic selector, α-equivariant measures exist, so
  uniqueness fails without that structure. Best repurposed as a **guardrail/impossibility** (the
  `SelectionDynamics.uniformModel` honest-risk note).

- **Route C — no-signaling + capacity (count level).** *The closest positive route.* If every remote
  record split is a μ-preserving dynamics that leaves the local coarse basin invariant (remote-split
  **no-signaling**), the count functional `F` is forced additive: `F(a+b)=F(a)+F(b)`, hence
  `F(n)=n·F(1)`, hence `P_F(i)=n_i/M = w_i` — **Born on the rational grid**. ✅ The load-bearing
  `additive ⇒ linear` step is machine-checked: `BornRoutes.additive_nat_linear`.
  **Honest caveat (pro):** stating "F additive" *directly* is just refinement-naturality (already
  proven, `RefinementBorn.refinementNatural_additive`). The genuine new content is the **dynamical
  lemma** that every Bob-local split is implemented by a μ-preserving remote dynamics — that is the
  Born-strength input and remains open.

## New routes pro surfaced

- **Martingale / optional-stopping (pro's "best missing dynamical bridge").** If the squared branch
  weight `W_k(t)` is a μ-**martingale** (μ-expected squared weight conserved) with the final record
  **absorbing** (`W_k(T)∈{0,1}`) and initial value `w_k`, then by optional stopping
  `μ(outcome k) = E_μ[W_k(T)] = E_μ[W_k(0)] = w_k` — **Born**. This is exactly why GRW/CSL collapse
  models recover Born. ✅ Machine-checked: `BornRoutes.born_from_martingale`. The Born-strength premise
  is the martingale conservation; deriving it from QIQT-H unitary dynamics is the open step. This is a
  genuinely **different** Born-strength input from refinement/fine-graining — physically the most
  appealing (it is a conservation law), and the most promising frontier target.

- **Meta no-go (Lean-friendly).** "If a structural constraint set Γ is satisfied by every power-rule
  model `Fα(n)=n^α`, and `F₂` violates Born on some finite context, then Γ does **not** entail Born."
  ✅ Machine-checked witness: `BornRoutes.sqRule_refinement_signals` — counts `[2,2]` vs the
  refinement `[1,1,2]`: Born gives `1/2` either way; the α=2 rule gives `1/2` coarse but `1/3` fine,
  i.e. it **signals under refinement**. So no premise the whole power-family obeys can force Born —
  the formal statement of *why the exponent cannot be pinned for free*.

## Pro's ranking

1. **Route C** — best positive route (count-level additivity; Born on the grid). ✅ core checked.
2. **Martingale** — best missing dynamical bridge (conservation-law Born). ✅ implication checked.
3. **Route B α-no-go** — best guardrail/impossibility.
4. **Route A MaxEnt no-go** — obstruction theorem.

## What is now machine-checked (this round, `QIQTH/BornRoutes.lean`, axiom-free)

| theorem | content |
|---|---|
| `additive_nat_linear` | Route C core: additive count `F` ⇒ `F(n)=n·F(1)` ⇒ Born weights `n_i/M`. |
| `born_from_martingale` | Martingale + absorbing 0/1 + initial `w_k` ⇒ `μ(outcome k)=w_k`. |
| `sqRule_refinement_signals` | Meta no-go witness: α=2 signals under `[2,2]→[1,1,2]` (1/2 vs 1/3); Born invariant. |
| `SelectionModel.expectation_conserved` | **Bridge**: equivariance ⇒ `E_μ[W∘R]=E_μ[W]` for every `W` — the martingale-increment condition, *derived* not assumed in the equivariant model. |

### The bridge that unifies the routes

`SelectionModel.expectation_conserved` (in `SelectionDynamics.lean`) shows the **martingale conservation
and the equivariance condition are the same thing**: for an equivariant typicality measure, the
μ-expectation of every observable is conserved under the selection step `R`. This discharges
`born_from_martingale`'s Born-strength premise (`hmart`) *inside the equivariant model class* — so the
no-signaling route (equivariance) and the martingale route are two faces of one condition. The entire
open problem then collapses to a single physical claim: **the actual `(Φ,λ)` dynamics preserves a
Born-agnostic typicality measure `μ`** (the Valentini-style relaxation hope, vs. the circularity risk
that the only equivariant `μ` is `|Ψ|²` itself).

## Honest status

These are **conditional theorems**: each makes its one Born-strength premise fully explicit and
machine-checks the implication to Born, and the meta no-go proves no Born-free premise can replace
it. The remaining genuine research frontier is unchanged and now sharply localised: **derive one of
{remote-split no-signaling on counts, squared-weight martingale conservation, equivariance} from the
actual (Φ,λ) dynamics.** The martingale route is the recommended next target — a conservation law is
the most natural thing to seek a dynamical proof of.
