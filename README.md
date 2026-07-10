# QIQT-H — One Wave Function, One World

**A single-world, holographic formulation of quantum mechanics — with the entire deductive substrate machine-verified in Lean 4, so you can re-run every proof yourself.**

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20837905.svg)](https://doi.org/10.5281/zenodo.20837905) &nbsp;·&nbsp; **Site:** [qiqt.org](https://qiqt.org) &nbsp;·&nbsp; **Author:** Pawel Kaplanski

---

## Verify it yourself

Foundations claims are cheap. This one ships a **verification capsule**. On your own machine, with minimal trust in the author, it wipes the compiled proofs and rebuilds them from source (the Lean kernel re-checks every step), replays an independent kernel checker, and audits that the *complete* transitive dependency set is only Lean's three standard axioms — no `sorry`, no hidden axiom, no `native_decide`.

```bash
git clone https://github.com/kaplan196883/QIQT-H && cd QIQT-H
bash verify/verify.sh   # → verify/out/claim_card.md
```

It prints a **claim card**: the exact formal statement, the complete trusted base, and a ledger of every *physical* assumption still assumed rather than proven. See a real one at **[qiqt.org/claim-card](https://qiqt.org/claim-card)**. All mechanical trust collapses to three things: the Lean kernel, your reading of the rendered statement, and the explicitly-listed physical inputs. *(Needs the Lean toolchain via [elan](https://github.com/leanprover/elan); the clean-room build takes a while — that is the point.)*

Prefer not to run a shell script? A pinned **Docker** recipe rebuilds the whole stack — Lean, Mathlib, the project — from source and runs the capsule: `docker build -t qiqt-verify -f verify/Dockerfile . && docker run --rm qiqt-verify`. **Reproduced the build?** Please add a line to [`REPRODUCED.md`](REPRODUCED.md) — the public reproduction log.

## What this is

QIQT-H's ontology is **Φ-monism**: there is one substance — the universal wave function Φ, evolving exactly unitarily — of which observers are macroscopic patterns; a non-dynamical selector **λ** marks exactly one decohered record actual per run. No collapse, no branching, no fundamental probability. It rests on five postulates; the genuinely irreducible new physics is **(P4) finite holographic capacity + (P5) quantum equilibrium**, on the **(P1) (Φ,λ) ontology** — (P2)–(P3) being the standard quantum-relativistic arena.

- **Measurement problem** — dissolved without collapse: decoherence supplies the records, λ makes exactly one actual. Single outcomes are λ's work, *never* the capacity bound (the earlier "capacity forbids records" reading is retired as a category error).
- **Born rule** — not a primitive: *reduced*, by a battery of machine-checked no-go theorems, to the single quantum-equilibrium postulate P5.
- **Gravity** — finite regional **entropy** (Q_R bounds the von Neumann entropy S(ρ_R) of Φ, *not* a finite matter Hilbert dimension) feeds a conditional, Lean-checked Jacobson-style derivation of an **Einstein-form equation** for the free field. The area *floor* is a derived theorem; the area *form* and the 1/4 are a conditional Sakharov re-derivation; the numerical value of G is a named frontier.

## What is machine-checked

Over **5,000 theorems across ~490 files**, axiom-free (Lean's standard three only; project axiom budget 0, CI-guarded). Formalization firsts — to our knowledge, in any proof assistant:

- The **first complete Tomita–Takesaki modular theory** for an inductive-limit (GNS) state — the modular operator Δ, the flow Δ^it, the conjugation J with polar decomposition S̄ = J∘Δ^½, both halves of Tomita's theorem (Δ^it M Δ^−it = M and J M J ⊆ M′), and a genuine non-tracial KMS state.
- An **unbounded Stone theorem** + PVM spectral theorem + bounded Borel functional calculus — beyond current Mathlib.
- The **von Neumann double-commutant theorem** (A″ = SOT = WOT closure).
- The **holographic count as a theorem** (S = Σ log D = A/4G) and the Araki–Woods III₁ fingerprint of the capacity tower.
- **Einstein's equations** from the capacity bound — a conditional Jacobson chain for the free field, end to end.

Full scope for every claim: **[qiqt.org/formalization](https://qiqt.org/formalization)**.

## What this is **not**

Stated plainly, because conflating these is what lets a skeptic dismiss the work:

- **Not** a proof that general relativity or this interpretation is true of our universe.
- **Not** a claim that quantum gravity is solved — the gravity chain is *conditional* on named, shrinking inputs (the Clausius/area law where not yet discharged, the trace-to-geometry match, the value of G, the continuum Type III₁ limit, interacting matter).
- **Not** a claim that the Lean definitions *faithfully model* the physics — that **adequacy** judgment is left to you, via the rendered claim card. The capsule certifies a *conditional mathematical entailment*, not a physical truth.

It is a research program with its open problems named (**[qiqt.org/open-problems](https://qiqt.org/open-problems)**), not a completed theory.

## Repository structure

- `verify/` — the verification capsule (`verify.sh`, `README.md`, the axiom audit, the claim card).
- `lean/mathlib/QIQTH/` — the Lean 4 / Mathlib formalization; `AxiomAudit.lean` is the per-theorem `#print axioms` audit.
- `QIQT_Foundations_Paper.md` — the foundations paper (canonical source; `build/` holds the generated `.tex` + PDF).
- `ABSTRACT.md` — the canonical abstract and the alignment guardrails all public copy tracks.
- `LEAN_RESULTS_INVENTORY.md` — the honest ground-truth inventory of what is proven and under exactly what conditions.
- `website/` — the [qiqt.org](https://qiqt.org) source (Astro).

## Cite

Pawel Kaplanski, *One Wave Function, One World: Φ-Monism, a Holographic Entropy Bound, and a Machine-Verified Path Toward Emergent Gravity* (2026). Zenodo concept DOI **[10.5281/zenodo.20837905](https://doi.org/10.5281/zenodo.20837905)** (resolves to the latest release). Companion methods paper: [10.5281/zenodo.20837809](https://doi.org/10.5281/zenodo.20837809).
