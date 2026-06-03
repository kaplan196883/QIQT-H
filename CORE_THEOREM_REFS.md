# Supporting arXiv literature for the QIQT-H core theorem

Collected 2026-06 (via Playwright/arXiv) while drafting `QIQTH/CoreNoCollapse.lean`.
TeX sources downloaded to `refs/arxiv_sources/<id>/` (tarballs git-ignored; extract
with `tar xzf <id>.tar.gz`). All are open-access arXiv preprints.

Per the GPT-5.5-pro strategic review (2026-06): the **Tomita–Takesaki / Type-III
tower is NOT the load-bearing part** of the "finite Q_max removes collapse" claim.
The load-bearing content is the finite-capacity exclusion + selector + Born/typicality
+ collapse-as-conditionalization, formalized in `QIQTH/CoreNoCollapse.lean`. These
references ground each block.

## Tier 1 — directly grounds the finite-capacity / record-exclusion core

- **arXiv:2601.19703** — Strasberg, Schindler, Wang, Winter, *Approximate
  Decoherence, Recoherence and Records in Isolated Quantum Systems* (Jan 2026).
  **THE anchor.** Decoherent-histories framework; proves (geometric, robust,
  Hilbert-space fact) that a family of N almost-orthogonal history vectors cannot be
  approximated by orthogonal record vectors once N → D, so the number of *identifiable*
  records `N_detectable ≪ D ≪ N_max`. They name the open **"branch selection problem"**:
  *how does the multiverse select the few branches that have observers aware of their
  history?* — which is **exactly** the question QIQT-H's `(Q_max, λ)` answers. Our
  `coactual_subsingleton` is the (cleaner, exact) capacity-exclusion fact; QIQT-H is a
  proposed resolution of their problem. Use for: motivation of the capacity bound, and
  the honest statement that single-outcome needs a *selection* principle beyond decoherence.

- **arXiv:2509.17775** — *Functional Information in Quantum Darwinism: An Operational
  Measure of Objectivity* (2026). Capacity-aware framework: adequacy predicate via the
  **Holevo bound**, capacity-limited plateaus `FI ≲ log₂ N`. Use for: a concrete
  information-theoretic `cost`/`Q_max` model justifying the saturation premise
  `cost > Q_max/2` (the one genuinely physical input of our core theorem).

## Tier 2 — Born rule / typicality (the across-run frequency layer)

- **arXiv:1910.08049** — *Typicality in the foundations of statistical physics and
  Born's rule*. Grounds the typicality measure μ over runs (cf. `QIQTH.BornTypicality`,
  `BornConcentration`).
- **arXiv:2302.02086** — *The Born Rule — Axiom or Result?* Born from a single
  non-contextuality assumption (Gleason-flavored; cf. `QIQTH.GleasonSelector`).
- **arXiv:1308.5384** — *Derivation of the Born rule based on the minimal set of
  assumptions* (entanglement-first route).

## Tier 3 — collapse-as-conditionalization / retrospective Born

- **arXiv:2010.15101** — *Observations of wavefunction collapse and the retrospective
  application of the Born rule*. Grounds `QMRecords.joint_eq_weight_mul_cond`
  (sequential Born = weight × conditional; collapse recovered by conditioning).
- **arXiv:1601.01214** — *Scheme of a Derivation of Collapse from Quantum Dynamics*
  (Born as a consequence of dynamics).
- **arXiv:1702.01845** — *Updating the Born rule* (a rule subsuming Born + collapse,
  knowledge-based).

## Tier 4 — decoherence does NOT by itself give single outcomes (the gap we fill)

- **arXiv:1308.4055** — *Why decoherence solves the measurement problem* (and the
  standard counter-view). Use for: framing why a *separate* selection/capacity
  principle is needed — decoherence kills interference, not multiplicity.

## How each maps to `CoreNoCollapse.lean`

| Block | Lean object | Reference |
|---|---|---|
| finite-capacity exclusion (core) | `coactual_subsingleton`, `RecordContext.cost_gt_half` | 2601.19703, 2509.17775 |
| single outcome (no collapse) | `exactly_one_actual`, `qiqth_single_outcome_no_collapse` | 2601.19703 (branch selection) |
| Born weights / typicality | `QMRecords.weight`; `GleasonSelector`/`BornTypicality` | 1910.08049, 2302.02086 |
| collapse = conditionalization | `QMRecords.joint_eq_weight_mul_cond` | 2010.15101, 1702.01845 |
| why decoherence is insufficient | (motivation for `Selection`/`λ`) | 1308.4055 |

## Open physical input (NOT a Lean theorem)

The saturation premise `cost r > Q_max/2` (each complete macroscopic record consumes
> half the capacity ⇒ at most one fits) is the genuine physical content. Justifying it
from a concrete capacity model (holographic/Bekenstein, modular nuclearity, or the
Holevo/functional-information bounds of 2509.17775) is the next research target — this
is exactly where the Strasberg–Winter "branch selection problem" locates the open
question.
