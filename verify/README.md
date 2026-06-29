# `verify/` — the QIQT-H verification capsule

A self-contained harness that lets **anyone, on their own machine, with minimal trust
in the authors**, re-establish what the QIQT-H → GR formalization actually proves — and
see exactly what it still assumes.

```bash
bash verify/verify.sh
# -> verify/out/claim_card.md
```

## What it certifies (and what it cannot)

This capsule produces a **mathematical certificate**, not a physical proof. Be precise
about the difference, because conflating them is what lets a skeptic dismiss the work:

- ✅ **Certified:** *In the build on your machine, the Lean kernel accepts each capstone
  theorem, and its **complete** transitive dependency set is only `propext`,
  `Classical.choice`, `Quot.sound` — no `sorry`, no project axiom, no `native_decide`.*
  Together with the **full hypothesis ledger** (every assumption the statement still makes).
- ❌ **Not certified — and no proof script can:**
  1. that GR is physically true of our universe;
  2. that the Lean definitions *faithfully model* QIQT-H and GR (the **adequacy** gap — a
     human, domain-expert judgment; the capsule *minimizes* it by rendering the exact
     statement, but cannot mechanize agreement);
  3. that the **labelled physical inputs** (the residue in the ledger — e.g. the FQ
     capacity bound, the Clausius/area floor) hold in nature. Those are scientific
     arguments made in the paper, not theorems.

The capsule's value is collapsing all *mechanical* trust to near-zero, so the only things
a reader must weigh are (a) the Lean kernel, (b) their reading of the rendered statement,
and (c) the explicitly-listed physical inputs.

## The stages

| Stage | What it removes from your trust | How |
|------|----------------------------------|-----|
| **1** clean-room rebuild | trust in the authors' cached build artifacts | wipes the project's `.olean`s and rebuilds `QIQTH` from source; the kernel re-checks every project proof |
| **2** independent re-check | trust in Lean's *elaborator* | `leanchecker` (built into the toolchain) replays each capstone's import closure through the kernel logic alone (catches `unsafe` / `@[implemented_by]` escapes) |
| **3** axiom / soundness audit | trust in the authors' axiom accounting | `Lean.collectAxioms` over each capstone; **fail-closed** if the transitive set leaves `{propext, Classical.choice, Quot.sound}` or contains a forbidden axiom (`sorryAx`, `Lean.ofReduceBool`) |
| **card** | trust in the authors' description of the claim | renders the *exact* formal statement + the *complete* hypothesis ledger, flagging the load-bearing physical inputs |

What the kernel checks during Stage 1 is the small, audited type-theory core (~the de
Bruijn criterion); Stage 2 makes that check independent of the much larger elaborator.

## Configuration — `config.json`

- `capstones` — the theorems to certify (name + informal claim + honest scope note).
- `standard_axioms` / `forbidden_axioms` — the Stage-3 whitelist / blacklist.
- `input_notes` — human annotations for hypothesis binders (by exact name or prefix),
  tagging the **`physical-input`** residue versus routine regularity/setup. Editing this
  changes only the *card's prose*; it can never relax the axiom audit.

## Outputs — `verify/out/` (git-ignored)

- `claim_card.md` — the human-facing certificate: verdict, formal statement, complete
  trusted base, full hypothesis ledger, scope.
- `axioms.json` — the raw `collectAxioms` facts per capstone.

## Stage 2: `leanchecker`

The independent re-checker is **built into the Lean toolchain** as `leanchecker` (since
v4.28; the old standalone `lean4checker` repo is deprecated). Because it ships with the
toolchain, its version always matches the oleans and **nothing needs installing** —
`lake env leanchecker <module>` just works. Stage 2 re-checks the import closure of each
capstone's module (which covers every declaration the certified proof touches); this
replays the kernel over Mathlib too, so it can take many minutes. If `leanchecker` is
somehow absent (a pre-v4.28 toolchain), Stage 2 is **skipped with a loud warning** and the
certificate is marked incomplete.

## Gold standard: full from-source clean room (optional)

`verify.sh` Stage 1 rebuilds the *project's* modules; its dependencies (Mathlib, …) are
pinned by `lake-manifest.json` but not rebuilt each run. For a maximally hostile reviewer,
run the whole stack — Lean, Mathlib, the project — from source in a pinned container:

```dockerfile
# sketch — pin EXACTLY the lean-toolchain + lake-manifest revs in this repo
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y curl git build-essential
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
COPY . /qiqt
WORKDIR /qiqt/lean/mathlib
RUN ~/.elan/bin/lake build QIQTH            # builds Mathlib + project from source (slow)
RUN bash /qiqt/verify/verify.sh
```

Then nothing but the base image, the pinned source, and your CPU is trusted.
