# QIQT-H Lean formalizations — Mathlib variant

Mathlib-rooted proofs of QIQT-H Theorems 6, 7, Lemma 1, Theorem 3.

The standalone counterparts in `../*.lean` axiomatize the arithmetic
facts they consume.  This variant discharges those axioms against
`Mathlib.Data.Real.Basic`, so the trust base is `Mathlib + Lean kernel`
(no custom axioms).

## Files

| Lake module | Source |
|---|---|
| `QIQTH.Theorem6` | `QIQTH/Theorem6.lean` |
| `QIQTH.Theorem7` | `QIQTH/Theorem7.lean` |
| `QIQTH.Resolution` | `QIQTH/Resolution.lean` |
| `QIQTH.UnitarityLocality` | `QIQTH/UnitarityLocality.lean` — closes the microcausality ⇒ locality gap for Theorem 7 (unitary-dilation case) |
| `QIQTH.Donald` | `QIQTH/Donald.lean` — derives Donald's identity from three primitive relative-entropy axioms (A1, A2, A3) |
| `QIQTH.DoubleSlit` | `QIQTH/DoubleSlit.lean` — worked instance: single-spot saturation collapses Theorem 6 to determinacy |
| `QIQTH.StateLevelNoSignaling` | Lifts T7 from probabilities to states; closure of Alice-fixing under composition and convex mixtures |
| `QIQTH.KrausLocality` | Generalizes `UnitarityLocality` to arbitrary finite-Kraus Bob channels (POVMs, projective measurements) |
| `QIQTH.ResolutionExt` | Monotonicity `Q₁ ≤ Q₂ ⇒ ε(Q₂) ≤ ε(Q₁)`, bits/nats conversion, complement lemmas |
| `QIQTH.CapacityPacking` | `N · I_0 ≤ Q_R ⇒ N ≤ ⌊Q_R / I_0⌋` + Markov-style suppression bounds |
| `QIQTH.RelEntPositivity` | `D(ρ ‖ σ) ≥ 0` (Klein, axiomatized) + convexity of `D` in first argument (derived from Donald) |
| `QIQTH.HolevoCoarseGraining` | Donald deficit formula + saturation rigidity + coarse-graining inequality |
| `QIQTH.DPI` | Data Processing Inequality interface + regional monotonicity + composition |
| `QIQTH.ShannonFano` | Finite Shannon entropy + single-record certainty bridge from `H_ε ≤ 0` |
| `QIQTH.BellMarginal` | Algebraic Bell/POVM marginalization identity |
| `QIQTH.Bell` | **CHSH-LHV bound** `\|chsh\| ≤ 2` for any local-hidden-variable model + **QIQT-H corollary** (no LHV model reproduces QIQT-H's quantum-level CHSH violations, yet QIQT-H still satisfies no-signaling) |
| `QIQTH` (root, re-exports) | `QIQTH.lean` |

## What Mathlib gives us

| Standalone axiom | Mathlib replacement |
|---|---|
| `RealQ.le_refl` | `le_refl` |
| `RealQ.le_trans` | `le_trans` |
| `RealQ.add_le_add_right` | `add_le_add_right` |
| `RealQ.sub_le_self_of_nonneg` | `sub_le_self_of_nonneg` (via `linarith`) |
| `RealQ.eq_sub_of_sum` | `eq_sub_of_add_eq'` (via `linarith`) |

All five real-arithmetic axioms collapse to a single `linarith` call.

`Resolution.lean` additionally gets the **continuous form** of
Theorem 3:  `eps Q := (1/2 : ℝ)^Q` with `eps_pos` proven by
`positivity`. The standalone variant only carries the discrete
`numBins Q > 0`.

## Verifying

```bash
cd lean/mathlib
lake exe cache get   # one-time, fetches precompiled Mathlib (~5 GB)
lake build           # compiles QIQTH/*.lean (~30 s on warm cache)
```

A clean `lake build` (exit 0, no error lines) means the proofs check.

## Setup notes

- Lean toolchain: `leanprover/lean4:v4.30.0` (pinned in `lean-toolchain`).
- Mathlib pinned at `v4.30.0` tag (declared in `lakefile.lean`).
- `lake exe cache get` fetches precompiled `.olean` files from
  `leanprover-community/mathlib4` Azure cache — much faster than
  building Mathlib from source (which would take hours).
- First-run `lake update` fetches ~10 transitive dependencies
  (Mathlib + plausible + Aesop + Qq + batteries + Cli + …).
