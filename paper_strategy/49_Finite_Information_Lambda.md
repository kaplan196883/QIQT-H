# A finite-information actuality selector λ — worked out, then retracted

**Status (2026-06-16): NEGATIVE RESULT.** The idea was worked out and the load-bearing arithmetic
machine-checked (`lean/mathlib/QIQTH/FiniteInfoLambda.lean`, axiom-free), then **red-teamed (GPT-5.5-pro,
verified by direct computation)**. The conceptual payoffs **do not survive**, and the specific construction
**contradicts two of QIQT-H's own machine-checked results**. This note records the idea, what is actually
true, and why it fails — so the mistake is not repeated.

## 1. The idea (as proposed)

After finding that (a) holographic capacity is *not* the single-outcome mechanism (H2 retired) and (b) λ as
formalized needs *no* finite information, the proposal was: apply finiteness to the **selector**. Bound λ's
resolving power per region to `N ≤ e^{Q_R}` equal "actuality cells"; the seed is `j ∈ {0,…,N−1}`; record α is
selected iff its Born cell `[lo_α, lo_α+p_α)` contains `j/N`, giving
`gridCount(α) = ⌈N·lo_{α+1}⌉ − ⌈N·lo_α⌉`, `gridWeight = gridCount/N`.

## 2. What is actually true (machine-checked, axiom-free)

These are **correct**, but they are facts about **one particular finite inverse-CDF sampler**, not about
"finite information":

- `gridCount_sum`/`gridWeight_sum` — the N cells partition the seeds; grid weights are a probability on the
  lattice `k/N`.
- `gridWeight_near_born` — `|gridWeight − p_α| < 1/N` (the rounding error of the `k/N` lattice).
- `gridWeight_tendsto_born` — `gridWeight → p_α` as `N → ∞`.
- `resolution_floor` — for **some** ordering and N, a positive-weight record gets 0 cells.

## 3. Why the payoffs FAIL (red-team, verified)

**(i) "Finite information ⇒ this grid" is false.** A finite-*valued* selector `λ ∈ {1,…,M}` with the *exact*
Born law `μ(α) = p_α` carries only `log M ≤ Q_R` realized bits and reproduces **Born exactly** — no deviation,
no floor. The deviation is an artifact of the extra "uniform-seed + deterministic-CDF" assumption, which
finite information does **not** force. (Dithering the grid restores exact Born in expectation.) So finiteness
constrains λ's *value space*, not its *probability law*.

**(ii) The "grain of actuality / minimum actualizable weight" is ordering-dependent, not physical.**
Same Born `(3/4, 1/4)` at `N=2`: ordering `(3/4,1/4) → (1,0)` (the `1/4` record excluded); ordering
`(1/4,3/4) → (1/2,1/2)` (not excluded). The only honest statement is "nonzero grid weight is a multiple of
`1/N`" — a property of the *selector measure*, not a Born threshold.

**(iii) The grid CONTRADICTS QIQT-H's own machine-checked results.** Two internal inconsistencies:
- **Envariance.** Equal-weight records get unequal grid weights: `(1/3,1/3,1/3), N=2 → (1/2,1/2,0)`. But
  QIQT-H *machine-checks* Zurek envariance (equal amplitudes ⇒ equiprobable) as the backbone of its Born
  reduction. The grid breaks the very symmetry the Born derivation rests on.
- **No-signaling.** Rounding *joint* records makes a remote marginal depend on the correlation: correlated
  `(1/2,0,0,1/2), N=3 →` Bob-marginal `2/3`; anticorrelated `(0,1/2,1/2,0), N=3 →` Bob-marginal `1/3` (both
  with exact Born marginal `1/2`) — an order-`1/N` signal. QIQT-H machine-checks *state-independent
  no-signaling*; the grid breaks it.

**(iv) "Finite-λ forces contextuality" is false.** Contextuality is forced by Kochen–Specker/Bell (the
algebraic impossibility of a global value-map), not by a bit budget; finite precision can even *weaken* KS
(Meyer–Kent–Clifton).

**(v) The forcing argument is incoherent.** A dilemma: if λ is non-dynamical and not a physical record, why is
it counted by `Q_R`? If it *is* physically instantiated in R, it is a new record with dynamics, breaking the
non-dynamical/no-collapse posit. And "which record (of M)" costs `log M` bits only relative to a *codebook*
whose ordering carries the infinite information — so the construction relocates infinite info, it doesn't
eliminate it. (Also a unit slip: `Q_R` in nats gives a threshold `e^{−Q_R}`, not `2^{−Q_R}`, and only under
saturation `N ≈ e^{Q_R}`.)

## 4. The salvageable core (real, but gives nothing new)

> If a uniform `N`-seed were physically mandatory, exact Born would be impossible for all contexts (weights on
> the lattice `k/N`).

That is genuine mathematics. But turning it into physics would require a **canonical** quantizer independent of
ordering / `[0,1)`-parameterization, that is **Lorentz-covariant**, **no-signaling-preserving**,
**envariance-respecting**, **projectively consistent** across regions, and yields an **across-run LLN** — none
of which exists, and the obvious candidate (this grid) fails all of them. A finite-*valued* λ with the exact
Born law has none of these problems but also no deviation, hence **no distinction from Everett**.

## 5. Lesson

"Finite information" constrains the *value space* of λ, not its *probability law*; a finite-valued λ reproduces
Born exactly. The deviation-bearing version requires an arbitrary uniform-seed-plus-grid that is not forced,
is ordering/frame-dependent, and breaks the program's own verified envariance and no-signaling. **It is not a
route to distinguishing QIQT-H from Everett.** The Lean module is retained as correct arithmetic about a
specific sampler, clearly relabeled; the physical interpretation is withdrawn.
