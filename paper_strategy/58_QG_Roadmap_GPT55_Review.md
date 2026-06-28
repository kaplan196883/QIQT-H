# 58 — GPT-5.5-pro review of the QIQT-H → Quantum Gravity roadmap

**Date:** 2026-06-28. **Reviewer:** GPT-5.5-pro (reasoning_effort high), via OpenAI MCP.
**Subject:** a skeptical review of the proposed "from where we are to actual quantum gravity"
roadmap. **Outcome:** the original 4-tier ladder (A→B→C→D) was **recut** into the dependency-ordered
Tier 0–4 used in `docs/qg_roadmap/`. This file archives the review's load-bearing findings so the
roadmap's claims are traceable.

## Verdict (one line)
The ladder was directionally sensible as a *list of themes* but **wrong as a dependency order**: it
conflated (1) conditional thermodynamic gravity on a background, (2) the semiclassical
holographic/algebraic description once geometry exists, and (3) the microscopic finite-capacity
theory whose continuum limit *produces* geometry. The original Tier B mixed (2) and (3).

## The two structural errors caught
1. **A2 mis-tiered.** "Derive `log N_R ∝ A` from finiteness" is **not** Tier-A cleanup. Finiteness
   alone gives a **volume** law (finite lattice: `log dim 𝓗_R = n·log d ∝ Vol`). Area capacity needs
   something that breaks tensor-factor independence (gravitational constraints, holographic QEC
   redundancy, finite causal-diamond Hilbert spaces, a screen postulate) → Tier-C-hard. The Sakharov
   bridge derives the area *form* **conditionally** (local QFT on smooth background + covariant
   cutoff), NOT from bare finiteness.
2. **CPW/Witten Type II is circular as an emergence engine.** The crossed product presupposes a
   semiclassical bulk background (a `1/N`, `G→0` gravitational dressing of an existing QFT in curved
   spacetime). It **describes** subregion algebras once geometry exists; it cannot be the **source**
   of emergent spacetime. So old-B4 (reconstruct geometry) and old-B5 (crossed-product area operator)
   were in tension. Correct, non-circular use: CPW Type II appears as the **effective continuum limit**
   of the substrate's subregion algebras (Tier 3 §3.3), derived, not assumed.

## The recut (→ `docs/qg_roadmap/`)
- **Tier 0** — assumption ledger + finite-dim obstruction theorems (Gap-2 KMS/capacity iff;
  finiteness↛area). Category (a).
- **Tier 1** — semiclassical geometric-code skeleton (fixed-area, JLMS, edge/bulk, finite Type II,
  RT⇒linearized-Einstein), **conditional, geometry assumed**. Category (b).
- **Tier 2** — the finite QI substrate (the real novelty): finite Hilbert spectrum, inclusion maps,
  dynamics, constraints/gauge, continuum/RG limit, quantified Lorentz-error. Mostly (c); the toy
  benchmark is (b) and is the top de-risking deliverable.
- **Tier 3** — derive Tier-1 *from* Tier 2 (metric reconstruction, RT, JLMS, CPW-as-limit, graviton,
  constraints, linearized→nonlinear Einstein, diffeo-invariant μ). Mostly (c).
- **Tier 4** — black-hole microstates, Page curve, singularity, cosmology (all (c)); + a near-term
  parameterized-phenomenology bounds paper ((a)).

## Missing-from-the-original-ladder items (now folded into Tiers 2–3)
Hamiltonian/constraint structure & problem of time; diffeomorphism invariance / gravitational dressing
(subregion factorization fails); matter beyond scalars (fermions, gauge fields, anomalies, SM);
RG/continuum-limit control (Lorentz-violation suppression — the recurring killer for discrete
programs); the spin-2 graviton with universal coupling, soft theorems, unitarity; the cosmological
constant & higher-curvature suppression; black-hole microstate counting is **not** replaced by the
`1/4` ratio; the Born μ must become a measure over **diffeo-equivalence classes of histories** once
geometry fluctuates.

## Category legend
(a) near-term formal/analytic; (b) hard but plausibly tractable frontier; (c) "this is the central QG
problem — no existing program has done it." `(c)` ≠ "don't attempt"; it = "don't call it cleanup,
don't promise a timeline."

## Per-tier highest-value first deliverable (de-risking order)
0. Gap-2 KMS–capacity compatibility/obstruction theorem (Lean).
1. Finite-dim JLMS/QEC theorem with central area operator `L_A`, `K_A = L_A + K_bulk` (Lean).
2. Minimal finite-capacity toy substrate (HaPPY/random-tensor-network or spin-chain→CFT) with a
   continuum knob + quantified Lorentz/locality/unitarity error. **Top de-risking experiment.**
3. Emergent-distance (min-cut/mutual-information) metric reconstruction in the toy, matched to RT.
4. Parameterized finite-capacity/decoherence **bounds** paper (CP + no-signalling + approx-Lorentz).

## Blunt strategic takeaway (verbatim sense)
The strongest move is **not** "jump to CPW Type II and call it quantum geometry." It is: *prove the
finite-dimensional edge/JLMS/fixed-area skeleton rigorously, then build a finite-capacity code/substrate
whose continuum limit reproduces that skeleton.* That gives QIQT-H a distinctive identity instead of
being a formal-verification wrapper around existing it-from-qubit ideas. QIQT-H's genuine current
strengths: clean assumption isolation, the finite-capacity entropy theorem, formal-verification
discipline, conditional Sakharov/Jacobson coefficient matching, and the explicit selector-cannot-be-
invariant no-go.
