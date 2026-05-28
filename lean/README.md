# QIQT-H Lean formalizations

A pilot Lean 4 formalization of selected QIQT-H theorems. Two parallel
variants:

- **Standalone** (this directory's `*.lean`) — self-contained, no
  Mathlib dependency, verifies in ~3 s per file with bare `lean`.
  Trust base: Lean kernel + 6 axiomatized real-arithmetic facts.
- **Mathlib-rooted** (`mathlib/QIQTH/*.lean`) — same theorems, all
  arithmetic discharged against `Mathlib.Data.Real.Basic`. Trust
  base: Lean kernel + Mathlib. Continuous-form Theorem 3.

## Files

### Standalone (this directory)

- `Theorem7.lean` — No-signaling from AQFT microcausality + locality.
- `Theorem6.lean` — Effective Macroscopic Definiteness (inner chain:
  Donald's identity + holographic bound ⇒ Holevo info ≤ capacity ⇒
  bound on H_ε).
- `Resolution.lean` — Lemma 1 (near-extreme indistinguishability) +
  Theorem 3 (finite Q ⇒ positive resolution floor). Discrete form.
- `lean-toolchain` — Pins Lean to `v4.30.0` for reproducibility.

### Mathlib-rooted (`mathlib/`)

See `mathlib/README.md`. Lake project; `lake build` compiles the
QIQTH library against precompiled Mathlib.

## Verifying

**Standalone** — with [elan](https://github.com/leanprover/elan) installed:

```bash
lean Theorem7.lean
lean Theorem6.lean
lean Resolution.lean
```

A clean compile (no output, exit 0) means the proofs check.

**Mathlib variant** — one-time `lake exe cache get` (~5 GB download
of precompiled Mathlib), then `lake build`. See `mathlib/README.md`.

## Scope

| Theorem | Status | Notes |
|---|---|---|
| Theorem 7 (No-signaling) | ✅ Proved | Locality axiomatized; reducing it to microcausality requires Mathlib `StarSubalgebra` + a vN-algebra commutant lemma not yet in the library. |
| Theorem 6 (Effective definiteness) | ✅ Inner chain proved | Donald → I_Hol ≤ C step is rigorous. Real arithmetic axiomatized (5 facts). Holevo + Fano + experimental-slack passed as hypotheses. |
| Lemma 1 (Near-extreme indistinguishability) | ✅ Proved | Discrete-bin formalization; transitive equality on quantization bins. |
| Theorem 3 (Positive resolution floor) | ✅ Proved | `numBins Q = 2^Q > 0` for finite Q : ℕ. |
| Theorems 1, 4 (Single-record per-run) | ⏸ Out of scope | Mixes FQ with decoherence dynamics. |
| Theorem 2 (Proper subclass) | ⏸ Tautological once FQ formalized as a predicate. |
| Theorem 5 (Born from typicality) | ⏸ Schematic / open problem | The paper itself flags as not yet proved. |
| Trilemma (Position paper) | ⏸ Meta-claim | Requires formal theory-of-theories machinery. |

## Re-deriving the real-arithmetic axioms

`Theorem6.lean` axiomatizes a tiny ordered-real fragment (5 facts). To
re-derive them against `Mathlib.Data.Real.Basic`:

| Axiom in this file | Mathlib lemma |
|---|---|
| `RealQ.le_refl` | `le_refl` |
| `RealQ.le_trans` | `le_trans` |
| `RealQ.add_le_add_right` | `add_le_add_right` |
| `RealQ.sub_le_self_of_nonneg` | `sub_le_self` (with `0 ≤ b`) |
| `RealQ.eq_sub_of_sum` | `eq_sub_of_add_eq'` |

See the paper-side text in `../QIQT_Foundations_Paper.md` §7 for the
informal statements and proofs.
