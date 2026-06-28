# Tier 2 — The finite Quantized-Information substrate (the real QIQT-H novelty)

> **Goal.** Build the **actual microscopic theory**: a finite-capacity quantum-information substrate
> with an explicit Hilbert spectrum, composition/inclusion maps, dynamics, constraint/gauge structure,
> and a *controlled continuum/RG limit* — and show it can reproduce approximate QFT **without
> immediately breaking locality, unitarity, or Lorentz covariance beyond bounded error.** This is
> where QIQT-H stops being "a formal-verification wrapper around standard it-from-qubit" and becomes a
> distinctive theory. It is also where the central quantum-gravity difficulty lives: **most of Tier 2
> is category (c).**

**Why this is the pivot.** GPT-5.5-pro's blunt strategic verdict: the strongest move is **not** "jump
to CPW Type II and call it quantum geometry." It is *"prove the finite-dimensional edge/JLMS/fixed-area
skeleton rigorously (Tier 0–1), then build a finite-capacity code/substrate whose continuum limit
reproduces that skeleton."* Tier 2 **is** that substrate. Everything before it is scaffolding;
everything after it (Tier 3–4) is *consequences* of it.

**The distinctive angle from FINITENESS.** Standard it-from-qubit is continuum / large-`N` /
Type-III-adjacent, built on *infinite* entanglement regulated by gravity. QIQT-H's postulate is
**finite regional capacity**. That points *away* from pure continuum Type III and *toward* a finite
substrate whose Type III behaviour is only **approximate** in the large-capacity limit. Natural arenas:
- finite-dimensional **holographic quantum error-correcting codes** (HaPPY-type, random tensor networks),
- **finite causal-diamond Hilbert spaces**,
- **quantum cellular automata** with emergent Lorentz symmetry,
- **finite-factor approximations** to Type III local algebras (hyperfinite II/III limits from finite
  matrix algebras).

**The defining tension to confront head-on.** An *exact* finite cutoff generically conflicts with
*exact* Lorentz invariance and *exact* continuum locality. A finite-capacity theory must therefore
explain how Lorentz covariance and microcausality emerge **approximately / relationally**, with
quantified error scaling. This is the single hardest internal-consistency demand on the whole program.

---

## 2.1 Minimal finite-capacity toy substrate with a continuum/RG knob  *(category (b) for the toy; (c) for the real thing — THE de-risking deliverable)*

**Deliverable.** Do **not** start with 3+1D gravity. Build a controlled toy with:
- finite Hilbert spaces per region,
- explicit regional **inclusion maps** (how small-region algebras sit inside larger ones),
- **unitary dynamics**,
- an **area/min-cut capacity law** built in by construction (e.g. a hyperbolic tensor network where
  entanglement across a cut is bounded by the min-cut ≈ "area"),
- a **tunable continuum limit** (bond dimension / refinement parameter),
- **quantified Lorentz-violation / error scaling** as the knob is turned.

**The one question it must answer:**
> *Can finite record capacity coexist with an approximate continuum QFT limit without immediately
> breaking locality, unitarity, or Lorentz covariance beyond an acceptable, quantified error?*

Concretely: a **HaPPY-like / random-tensor-network code**, or a **finite spin-chain → CFT** model, is
enough as a first benchmark. Measure: emergent two-point functions vs. CFT prediction; Lorentz/boost
covariance violation vs. refinement; locality (commutator decay) vs. distance; unitarity of the coarse
dynamics.

**Why this de-risks the program more than anything else.** Every continuum-entropy manipulation we
could do instead *assumes* the limit exists. This benchmark *tests* it. If finite capacity is
fundamentally incompatible with approximate Lorentz QFT, we need to know now — and if it is
compatible, we have the first concrete object on which Tier 3 emergence can be demonstrated.

**Artifact.** A simulation + short paper (`docs/qg_roadmap/tier2_toy/`), with the entanglement /
min-cut / Lorentz-error data; the *structural* claims (min-cut = capacity bound; code = exact QEC)
formalized in Lean where finite-dimensional.

---

## 2.2 The capacity-is-area law, derived FROM the substrate  *(category (c))*

This is where the mis-tiered "A2" actually belongs. Finiteness alone gives a **volume** law (Tier 0
§0.2). Area capacity must **emerge** from the substrate's structure — the inclusion maps and code
redundancy must make the *distinguishable-record* capacity of a region scale with its boundary, not
its volume. In a holographic code this is the **min-cut / bulk-to-boundary** structure; the area law
becomes a theorem *about the code*, not about bare finiteness.

**Honest status.** A first-principles maximum-distinguishable-record area law is **(c)** — it is, in
effect, "why is the world holographic," one of the central QG questions. The toy substrate (§2.1) lets
us *exhibit* it in a model; promoting it to a derivation for a substrate that also recovers QFT+GR is
the open core.

**Deliverable.** In the §2.1 toy: `mincut_bounds_distinguishable_records` (Lean, finite) — the
distinguishable-record capacity across a cut ≤ min-cut "area." Then the *physics* claim "this min-cut
is the geometric area" is a Tier-3 matching result, tagged `OPEN` until then.

---

## 2.3 Constraint / gauge / diffeomorphism structure  *(category (c); currently MISSING from the program)*

Quantum gravity is not "metric fluctuations" — it is **constrained** dynamics. The substrate must
ultimately carry (an emergent or built-in analogue of):
- the **Hamiltonian & momentum constraints** `H[N] ≈ 0`, `D[ξ] ≈ 0` with an anomaly-free
  hypersurface-deformation algebra (or a covariant/path-integral equivalent),
- **diffeomorphism invariance / gravitational dressing**: in gravity, local bulk operators are *not*
  gauge-invariant, subregion factorization *fails*, and edge modes / centers / relational observables
  are central, not optional. This directly affects Gap-2 (Tier 0/1), the area operator, and the
  Born/record story.

**Honest status.** This is a known gap in the *current* QIQT-H formulation (which lives on a fixed
slice with clean tensor factorization). It is **(c)**. The deliverable for Tier 2 is *modest and
honest*: identify, in the toy substrate, what plays the role of the constraints and the
gauge/dressing, and whether subregion factorization survives or must be replaced by a
center/edge-mode algebra. Even a negative result (factorization fails as expected) is progress,
because it tells Tier 3 what "regions" and "records" can mean when geometry is dynamical.

---

## 2.4 Fixing the value of G  *(category (c))*

Also mis-tiered originally (was "A3b"). Sakharov induced gravity gives `1/G` as a sum over species +
regulator; without a UV completion the cutoff, the bare counterterm, and the full species spectrum are
unknown. **Cross-species universality** (all matter couples to the *same* emergent geometric equation)
is a plausible frontier result and worth proving — but it does **not** fix the *observed value* of `G`.
The value of `G` is determined only once the finite substrate's spectrum and cutoff are pinned. Ledger
tag stays `OPEN` through Tier 2; only a concrete §2.1-class substrate with a fixed spectrum could
close it. **Never claim the value of G is derived.**

---

## 2.5 RG / continuum-limit control  *(category (c))*

The substrate must demonstrably yield, in its continuum limit: emergent Lorentz symmetry, emergent
locality, the correct low-energy QFT, **suppression of Lorentz-violating operators**, and the
renormalization of `G, Λ`, and higher-curvature terms. This is where most discrete/finite programs
(causal sets, naive lattices, some CA models) historically struggle — Lorentz-violation suppression is
the recurring killer. The §2.1 toy's "quantified Lorentz-error scaling" is the first, smallest probe
of this; full control is **(c)**.

---

## Tier 2 honest scale

This is the **core quantum-gravity tier**. The toy benchmark (§2.1) is genuinely buildable now and is
the highest-leverage de-risking experiment in the entire roadmap — but the *real* substrate that
recovers SM+GR with controlled Lorentz emergence (§2.2–2.5) is **(c): the central QG problem no
existing program has solved.** Be ruthlessly honest: progress here is measured in "we built a toy that
exhibits X with error scaling Y," not in "we derived quantum gravity."

**First concrete move:** §2.1 — the finite-capacity toy substrate (HaPPY/random-tensor-network or
spin-chain→CFT) with a continuum knob and quantified Lorentz/locality/unitarity error, plus the Lean
`mincut_bounds_distinguishable_records` finite theorem.

**Exit criterion (full):** a finite-capacity substrate with explicit dynamics + constraints whose
continuum limit provably reproduces an approximate Lorentz-invariant local QFT with bounded, suppressed
violation — i.e., the object Tier 3 can grow geometry out of. Reaching this *is* most of "solving
quantum gravity," and should be described that way.
