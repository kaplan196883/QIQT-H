# The finite-information λ that survives: a finite *index*, exact Born

**Status (2026-06-16): POSITIVE result, machine-checked (axiom-free), red-teamed and survived.**
This is the constructive complement to the negative result of `49_Finite_Information_Lambda.md` (the grid).
The lesson of the failure — *finiteness must not touch λ's probability law* — has a clean resolution.

## 1. The dividing line

Where the finiteness lives decides everything:

- **Finiteness in the probability LAW** (the retracted grid: a uniform-`N`-cell inverse-CDF that *rounds*
  the weights) is **fatal** — ordering-dependent, and it breaks the program's own machine-checked envariance
  and operational no-signaling.
- **Finiteness in the actuality DOMAIN** survives: λ is a finite **index** `α ∈ {0,…,M−1}` into a finite set
  of distinguishable record-histories, with the **exact** Born law `Pr(λ=α) = ‖C_α Φ‖²` (a real, computed
  from Φ, *not* rounded). The "finite encoding of λ" is then just the finite **cardinality** of the index
  space (`M ≤ 2^B`, i.e. `log₂ M` bits).

## 2. Machine-checked (axiom-free): `QIQTH/FiniteIndexLambda.lean`

The dividing line is now a theorem set:

- `indexWeight_marginal` / `indexWeight_envariant` — the finite-index law (= exact Born `p`) **preserves
  marginals** (no-signaling-transparent) and **equal weights** (envariance-transparent), by definition.
- `grid_breaks_envariance` — the grid law gives `(1/3,1/3,1/3)` at `N=2` the weights `(1/2,1/2,0)`: equal
  Born weights, **unequal** grid weights. Contradicts the machine-checked Zurek envariance.
- `grid_breaks_no_signaling` — two joint Born distributions, correlated `(1/2,0,0,1/2)` and anticorrelated
  `(0,1/2,1/2,0)`, have the **same** Born marginal `1/2` for one party but **different** grid marginals
  (`2/3` vs `1/3`) at `N=3` — an order-`1/N` **signal**. Contradicts the machine-checked state-independent
  no-signaling.

So: finiteness in the law is provably fatal; finiteness in the index is provably Born-transparent.

## 3. The holographic budget, without the register dilemma (mutual-information)

The bit-budget for λ can be the horizon entropy **without** making λ a new dynamical beable. The escape
(pro-confirmed) is the mutual-information identity. If λ adds *no distinction beyond the physical record* it
indexes (`H(λ|R)=0`), then
```
H(λ) = I(λ;R) + H(λ|R) = I(λ;R) ≤ H(R) ≤ S_horizon.
```
λ's information *is* the record information it indexes — bounded by the (holographically bounded) record
entropy. No stored register, no extra beable. The holographic bound thus constrains **how many distinguishable
record-histories there are** (`log|Ω_rec| ≤ S_horizon`), not Φ's superpositions (the retired H2 error) and not
the probability resolution (the retired grid error). This is the clean, load-bearing role for finite
information.

## 4. The forced consequence (refined)

A finite-bit λ over **infinitely many** positive-entropy Born events is **impossible** (Levin–Schnorr: a
finite computable seed can't be Martin-Löf-random for a positive-entropy Born measure; `H(X₁:ₙ) ≤ H(λ) ≤ B`
vs Born's `~n·h`). So a finite-bit λ forces **finite total independent record information** (finitely many
distinguishable histories — *not* literally finitely many event tokens; a 1-bit λ can pick between two
infinite simple histories). Born then holds as **finite-sample typicality** (Hoeffding/Chernoff;
`QIQTH.BornConcentration`), i.e. with high Born measure for large finite samples — not certainty.

## 5. Postulated vs derived

- **Postulated:** Φ supplies the exact Born weights; the record-history space is finite (`log|Ω_rec| ≤ S`,
  from a covariant horizon/Bousso bound — a physics input); λ adds no distinctions beyond the records
  (`H(λ|R)=0`); the typicality measure is the exact Born measure on histories.
- **Derived (machine-checked):** the index law is Born-transparent (marginals + equal-weights); the grid law
  is not (envariance + no-signaling counterexamples); Born-as-finite-sample (`BornConcentration`).

## 6. Honest limits

- **Born-transparent ⇒ operationally equivalent to Everett.** No new prediction; the distinction is
  ontological (one actual finite history vs. all finite branches), plus a cosmological commitment (finitely
  many distinguishable actual records ever) that Everett needn't make but can accept.
- The horizon-entropy identification needs a **covariant** record-history space (causal diamond / Bousso
  light-sheet), and inherits quantum-gravity uncertainty about de Sitter entropy (a bound on distinguishable
  states, not obviously a time-integrated event count; a global λ for an infinite FRW universe is *not*
  bounded by one horizon).
- This is **not** a derivation of Born and **not** an empirical distinction from Everett.

## 7. Bottom line

> **Finite information lives coherently in (Φ,λ) — as a holographic bound on the finite record-history
> *index* λ (via `I(λ;R) ≤ S_horizon`, no new beable), with the Born measure left exact.** The dividing line
> is machine-checked: the index is Born-transparent; the grid (finiteness in the law) provably breaks
> envariance and no-signaling. It re-earns "Quantized Information" honestly — the actual record-history is a
> finite object — but it is **ontological, not empirical**: it does not distinguish QIQT-H from Everett by
> any experiment.
