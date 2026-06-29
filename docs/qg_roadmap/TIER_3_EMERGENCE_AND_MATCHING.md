# Tier 3 — Emergence and matching (derive the Tier-1 skeleton FROM the Tier-2 substrate)

> **Goal.** Take the finite-capacity substrate built in Tier 2 (no geometry assumed) and **derive**
> the semiclassical geometric-code skeleton catalogued in Tier 1 (geometry assumed): a reconstructed
> metric / causal structure, an RT/HRT-type law (or its replacement), JLMS, CPW/Type II as the
> *effective continuum* algebra, a propagating graviton, the semiclassical Einstein equations, and
> ultimately their nonlinear form. **This is the step that turns "emergent gravity" into "quantum
> gravity."** Almost all of it is category **(c)** — this is the mountain.

**The whole point of the recut lives here.** Tier 1 *assumes* geometry; Tier 3 *produces* it. The
matching condition is the deliverable: *the structures Tier 1 took as input must come out of Tier 2 as
output.* Any time we are tempted to "use CPW/RT/fixed-area to get geometry," that is the Tier-1→Tier-3
circularity — Tier 3's job is to make those structures **theorems about the substrate**, with the
geometry on the *output* side.

---

## 3.1 Metric / causal-structure reconstruction  *(category (c); the first emergence deliverable)*

**Claim to establish.** From the Tier-2 substrate's entanglement data, reconstruct a metric and causal
structure: **entanglement → distance** (the "ER=EPR / entanglement builds geometry" mechanism,
Van Raamsdonk), and operational signalling order → causal/light-cone structure. In a holographic code
this is the bulk-geometry-from-boundary-entanglement map; QIQT-H's distinctive demand is that it work
from a **finite** substrate with bounded error.

> ⚠️ **Correction (2026-06-29, GPT-5.5-pro audit) — min-cut is NOT a metric.** An earlier draft of this
> section said "min-cut → distance" and listed "min-cut metric properties" as the Lean core. That is
> **false**: min-cut (equivalently the RT/entanglement *area*) does **not** satisfy the triangle
> inequality, so it is not a distance. Counterexample: on a weighted graph with `c(x,y)=c(y,z)=1`,
> `c(x,z)=4`, the pairwise min-cuts are `λ(x,y)=λ(y,z)=2` but `λ(x,z)=5 > 2+2`. Min-cut is an
> **area / capacity / entropy** primitive, not a distance primitive — it belongs in §3.2 (RT) and in the
> Tier-2 capacity skeleton, *not* in the metric reconstruction. The distance must be built by a
> reconstruction rule that **is** a metric: a **shortest-path / graph-geodesic** distance, a **cut-cone /
> L¹** embedding distance, a **`−log`(similarity)** distance under a multiplicative-triangle hypothesis,
> or the **variation-of-information** metric `VI(X,Y)=H(X|Y)+H(Y|X)` on record partitions. See the
> Corrections log at the end of this file.

**First concrete deliverable (highest-value for Tier 3).** In the §2.1 toy substrate, compute an emergent
**distance** from the entanglement data via a reconstruction rule that is provably a metric (shortest-path
/ cut-cone-L¹ / `−log`-similarity / variation-of-information), show it satisfies the metric axioms
(non-negativity, symmetry, triangle inequality) up to controlled error, and match it against the Tier-1
geometry; keep **min-cut** in its correct role as the *area/entropy* quantity (§3.2 / Tier-2 capacity).
Formalize in Lean **two** finite-combinatorial cores: (i) the guard theorem `minCut_not_metric` (min-cut
violates the triangle inequality — the counterexample above), and (ii) the chosen reconstruction's metric
axioms (`ApproxMetric ε`). The "this is *the* spacetime metric" identification remains a physics claim,
tagged by error bound.

**Honest status (c):** doing this for a substrate that *also* recovers QFT+GR is the central
emergent-spacetime problem; doing it in the toy is **(b)** and is the right first step.

---

## 3.2 RT/HRT (or replacement) as a substrate theorem  *(category (c))*

Re-derive the Ryu–Takayanagi / HRT entropy law — `S = area/4G + bulk` — as a **consequence** of the
substrate's code structure, *not* as an assumed holographic input (which is how Tier 1 §1.1 used it).
In holographic codes this is Harlow's "RT from QEC," but there it is *within* an assumed geometric
code. Tier 3 must produce the code (and hence the area operator) from Tier 2 first. The matching test:
the Tier-3-derived `L_A` equals the Tier-1-assumed central area operator.

---

## 3.3 CPW/Type II as the effective continuum algebra  *(category (c), conditional)*

Show that the large-capacity limit of the finite substrate's subregion algebras **flows to** the
CPW/Witten Type II crossed-product algebra (Type III local algebra + the gravitational dressing /
clock that tames the divergence). This is the *correct, non-circular* use of CPW: it appears as the
**effective description of the emergent semiclassical phase**, derived as a limit — not as the engine
of emergence. Requires the continuum Tomita–Takesaki / crossed-product infrastructure
(`TOMITA_TAKESAKI_ROADMAP.md`, `STONE_THEOREM_PLAN.md`); until then it is `OPEN`/`CITED`.

---

## 3.4 First-principles linearized Einstein, then nonlinear  *(category (c))*

- **Linearized.** Re-derive the entanglement first law `δS = δ⟨K⟩ ⇒` linearized Einstein
  (Faulkner–Lashkari–Van Raamsdonk) but **without assuming holography** — from the Tier-2 substrate's
  emergent geometry (§3.1) + emergent area law (§3.2). This is the first-principles version of Tier 1
  §1.4. The current QIQT-H δS=ηδA Lean theorem and the Jacobson `qiqt_gr_freefield` capstone are the
  *background-dependent, conditional* shadow of this; Tier 3 must lift them to emergent geometry.
- **Nonlinear.** Push linearized-from-entanglement to the **full nonlinear operator** Einstein
  equations. This is **essentially full quantum gravity** — flagged `(c)`, no timeline.

---

## 3.5 The graviton, the constraints, and the problem of time  *(category (c); MISSING-from-program items)*

For this tier to be quantum *gravity* and not just emergent classical dynamics, it must also produce:
- a **propagating spin-2 graviton** in the weak-field limit, with **universal coupling to
  stress-energy**, correct soft-graviton behaviour, and unitarity/positivity;
- the **constraint algebra / diffeomorphism invariance** as emergent symmetries of the substrate
  dynamics (the Tier-2 §2.3 structure realized);
- a resolution of the **problem of time**: when geometry fluctuates, "record," "region," and "time"
  are dynamical/relational, so the foundational selector `λ` and the Born measure `μ` must be
  reformulated as a measure over **diffeomorphism-equivalence classes of decoherent histories**, not
  records on a fixed slice. **This is where the foundational axis (Φ, λ, μ) and the gravity axis
  finally have to merge** — and it is genuinely open in *every* approach, not just QIQT-H.

**Why this is its own section.** These are the items GPT-5.5-pro flagged as *missing entirely* from the
original ladder. They are not optional polish; without them "quantum gravity" is not earned. Listing
them honestly here is itself part of the deliverable.

---

## 3.6 The Born measure μ under dynamical geometry  *(category (c); the foundations/gravity merge)*

QIQT-H's `λ` selects one record label; `μ` (P5, primitive) gives Born weights; the no-go says no
*invariant selector* exists. When geometry is dynamical and slices are gauge, the open OP3b "covariant
typicality measure" becomes "covariant-over-histories typicality measure." Tier 3 must show that the
emergent semiclassical phase admits a `μ` consistent with (i) Born statistics, (ii) no-signalling, and
(iii) diffeomorphism invariance — or honestly characterize the obstruction (a history-space analogue of
`no_covariant_selector`). This closes the loop with the Tier-0 §0.3 selector obstruction.

---

## Tier 3 honest scale

This tier **is** quantum gravity. With the possible exception of the toy-level metric reconstruction
(§3.1, which is **(b)**), every sub-item is **(c)**: no existing program has derived emergent dynamical
spacetime + graviton + constraints + Einstein (nonlinear) + a consistent measure from a finite
substrate. The honest framing for any external communication: *Tier 3 is the goal, not a plan with a
schedule.* Progress is real and reportable at the toy/matching level (§3.1–3.2); the full tier is the
open problem.

**First concrete move:** §3.1 — emergent-distance reconstruction in the Tier-2 toy substrate via a
**metric-valid** rule (shortest-path / cut-cone-L¹ / `−log`-similarity / variation-of-information — NOT
raw min-cut, which is the *area* primitive, see the §3.1 correction), matched against the Tier-1 RT
skeleton, with the finite-combinatorial core in Lean (the `minCut_not_metric` guard + the reconstruction's
`ApproxMetric` axioms).

**Exit criterion:** the Tier-1 skeleton (metric, area operator, RT, JLMS, Type II, linearized
Einstein) is **derived from** the Tier-2 substrate with controlled error, a spin-2 graviton with
universal coupling emerges, the constraint algebra and a diffeomorphism-invariant `μ` are in hand, and
the nonlinear Einstein equations hold as operator equations in the appropriate limit. **Only when Tier
2 + Tier 3 are both met is "quantum gravity" an honest word for QIQT-H.**

---

## Corrections log

- **2026-06-29 (GPT-5.5-pro emergent-spacetime scope audit) — §3.1 min-cut ≠ metric.** Earlier drafts of
  §3.1 (and the §3 "first concrete move" + the Tier-3 line of `README.md`) specified the emergent-distance
  reconstruction as "min-cut → distance" with "min-cut metric properties" as the Lean core. This was a
  **mathematical error**: the min-cut (= RT/entanglement *area* across a bipartition) does **not** obey the
  triangle inequality and is therefore not a distance. Counterexample: weighted graph `c(x,y)=c(y,z)=1`,
  `c(x,z)=4` gives `λ(x,y)=λ(y,z)=2`, `λ(x,z)=5 > 4`. Nothing built in Lean depended on this (it was a
  *planned* deliverable, not a proved theorem), so no proof is affected — but the recipe was mis-specified.
  **Fix:** min-cut is retained in its correct role as the *area/capacity/entropy* primitive (§3.2 RT and the
  Tier-2 capacity skeleton); the *distance* is now reconstructed by a rule that is provably a metric
  (shortest-path / cut-cone-L¹ / `−log`-similarity / variation-of-information), and the planned Lean core is
  split into (i) the guard `minCut_not_metric` and (ii) the reconstruction's `ApproxMetric ε` axioms. This
  also sharpens the Tier-1/Tier-3 boundary: area-from-entanglement (RT) and distance-from-entanglement
  (geodesic) are *different* reconstructions and must not be conflated.
