# A finite-information actuality selector λ — worked out

**Status (2026-06-16):** worked out, with the load-bearing core machine-checked, axiom-free
(`lean/mathlib/QIQTH/FiniteInfoLambda.lean`). This is the honest route to giving *finite information*
a load-bearing role in QIQT-H — after the session's findings that (a) the holographic bound is not the
single-outcome mechanism (H2 retired), and (b) λ as currently formalized requires *no* finite information
(infinite-dim Fock space, continuum seed). The move here: **bound the selector's resolving power**, not Φ.

## 1. The problem it fixes

QIQT-H is named for finite/quantized information, but the load-bearing content (λ + modular/algebraic record
structure) turned out to be information-capacity-agnostic. The retired **H2** wrongly applied the capacity
bound to **Φ's records** (the joint cost of two records "exceeding" Q_R — a category error: a holographic
bound counts independent d.o.f., not redundant copies). The clean alternative is to apply finiteness to the
**selector λ**, not to Φ.

## 2. The model

- Φ stays infinite-dimensional and exactly unitary. Born weights `p_α = ω(P_α)` on a finite record family
  come from Φ as usual.
- **λ has finite resolving power**: per region R it can distinguish among at most `N ≤ e^{Q_R}` equal
  *actuality cells* (`log₂ N` bits, capped by the regional holographic capacity). The finite-information seed
  is `j ∈ {0,…,N−1}` (value `j/N`); record α is selected iff its Born cell `[lo_α, lo_α+p_α)` contains `j/N`.
- The cell count and quantized weight:
  ```
  gridCount(α) = #{ j<N : lo_α ≤ j/N < lo_α+p_α } = ⌈N·lo_{α+1}⌉ − ⌈N·lo_α⌉
  gridWeight(α) = gridCount(α) / N
  ```

## 3. The forcing — why N ≤ e^{Q_R} (principled, not a bare postulate)

λ_R is the actuality fact for region R, and it must be **physically instantiable** — realized within the
region's degrees of freedom (the "observer is the wavefunction" thesis). By (FQ) the region holds ≤ Q_R
nats, so λ_R cannot carry more than Q_R nats of *pointer* information — hence it resolves among ≤ e^{Q_R}
records. This is a self-consistency requirement, not a free postulate. (Distinguish the *pointer* — ≤ Q_R
bits saying which record is actual — from the *records* themselves, the content; no circularity if the
selector indexes, rather than duplicates, the records.)

## 4. What is DERIVED (machine-checked, axiom-free)

| result | Lean theorem |
|---|---|
| Every actuality seed selects exactly one record: Σ gridCount = N (the cells partition the seeds) | `gridCount_sum` |
| The finite-information weights are a genuine probability over a **finite, uniform** seed measure | `gridWeight_sum` |
| **Born up to the resolution**: `\|gridWeight(α) − p_α\| < 1/N` | `gridWeight_near_born` |
| **Exact Born is the N→∞ (infinite-capacity) limit** | `gridWeight_tendsto_born` |
| **A minimum actualizable weight**: a positive-weight record below the resolution gets ZERO cells | `resolution_floor` |

Two structural consequences (informal): finite λ **forces contextuality** (it lacks the bits to be a global
noncontextual value-map over infinitely many counterfactual contexts — so it can only fix the actual one),
and it **derives outcome discreteness** (≤ N ≤ e^{Q_R} actualizable records, as a consequence of bounded λ
rather than an assumption).

## 5. The payoff — a candidate distinction from Everett

This is the program's first concrete candidate for being *more than* "Everett with an actuality tag":

- **A smallest grain of actuality.** With finite resolution, records of Born weight below ~`2^{−Q_R}` are
  *never actualized* (`resolution_floor`). In Everett every branch is real (just low-measure). So finite-λ
  carries a genuine ontological structure Everett lacks.
- **A calculable, capacity-controlled deviation from exact Born.** `gridWeight` differs from Born by `< 1/N`
  (`gridWeight_near_born`), recovering exact Born only as `N → ∞`. At the true holographic scale
  (`N ~ e^{10^{122}}`) this is unobservable — *consistent with all data* — but it is an **in-principle**
  deviation, and with a small **effective** capacity `N^eff` (the free parameter the foundations paper already
  flags for its conditional phenomenology) it becomes **testable** (a maximum-superposition-scale / minimum-
  actualizable-probability signature). Finite-λ is the mechanism those conditional predictions ride on.
- **The seed becomes finite.** The typicality measure is now uniform over `N` seeds — a *finite*-information
  prior — resolving the earlier awkwardness that the continuum seed `s∈[0,1)` carried infinite information.

## 6. Postulated vs derived (honest accounting)

- **Postulated:** (FQ) the region holds ≤ Q_R information; λ instantiated within the region (so `N ≤ e^{Q_R}`);
  the uniform measure on the N seeds (typicality).
- **Derived (axiom-free):** §4 above — exactly-one selection, finite probability, Born-up-to-1/N, the N→∞
  limit, the resolution floor.

## 7. Honest caveats / what remains

- "Finite-information λ" is here pinned as a **bit-bound on the seed (N cells)**; alternative formalizations
  (a complexity bound, a bound on distinguishable selections) would have different fine consequences.
- The deviation is *unobservable* at the true holographic N; the empirical content lives entirely in the
  conditional `N^eff` regime, where `N^eff` is currently a free parameter (deriving it non-circularly is the
  same open problem the paper flags).
- The **global-history** problem stands: finite-per-region λ is the infinite product of finite local
  selectors (matching the finite-fiber record net), but one *coherent* actual world (consistency across
  overlapping regions/times) is still the open global-history target.
- The forcing argument's circularity (λ instantiated within the records it selects) needs a fully rigorous
  treatment.

## 8. Bottom line

Forcing λ to be information-limited is the one move that simultaneously (i) gives **finite information /
holography a genuine load-bearing role** — on the *selector*, where it is clean, not on Φ where it was a
category error; (ii) **derives** outcome discreteness and contextuality; and (iii) supplies a **candidate
empirical/ontological distinction from Everett** (a grain of actuality, a tunable Born deviation). The
load-bearing arithmetic is machine-checked, axiom-free. It is a research lead, not a finished result — but
unlike the natural-cone / interacting walls, it could change what the theory *is*.
