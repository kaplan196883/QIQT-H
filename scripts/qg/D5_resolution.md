# D5 — the resolution: what QIQT-H is, after the full adversarial stress-test

**Date:** 2026-06-30. **Plan:** `FINITE_MATTER_OR_ENTROPY_PLAN.md` D5 (final). Synthesizes D1–D4 and two
adversarial GPT-5.5-pro red-teams. **This is the honest endpoint of the finite-capacity-vs-Lorentz campaign.**

## The chain (machine-checked where noted)

- **D1** — QIQT-H's load-bearing capacity bound is a von Neumann **entropy** bound (`area_floor_vonNeumann`:
  `S_vN(ρ_R) ≤ A/4ℓ_P²`); the postulate's own header disclaims the matter reading ("operational capacity, NOT
  Hilbert-space dimension"; "type-III local algebra"); finite cardinality lives on the decoherent **records**,
  the finite-dim models are **proxies**. ⟹ Fork A, not Fork B.
- **D2** (Lean, axiom-free) — finite-dim matter + exact `[K,P]=iH`, `[K,H]=iP`, `H⪰0` ⟹ `H=0` *and* `P=0`. Fork
  B (literal finite matter) is untenable for exact Lorentz.
- **D3** (Lean, axiom-free) — a uniform `N`-atom record state with trace weights `e^Q/N` has entropy `=Q` for all
  `N` ⟹ `S_τ ≤ Q_D ⇏ card ≤ e^{Q_D}`. Fork A's capacity is **entropy**, not a state count.
- **D4** — on Fork A the distinctive content is an *interpretation* (single-world (Φ,λ) + machine-checked
  Born-from-typicality + the algebraic regional-content reframing).

## The verdict (two adversarial red-teams, no charity)

> **QIQT-H, after D1–D4, is standard Lorentz-covariant QFT + decoherence + a single-world λ-selector + a
> Born-typicality axiom (P5), decorated with an assumed Bousso-style holographic *entropy* bound and standard
> induced-gravity / Jacobson material. Classification: (b) — a competent repackaging of known interpretation
> machinery, known holography, and known induced gravity, with useful formal cleanup. The distinctive "finite
> quantized information as fundamental physical capacity" did NOT survive.**

The four load-bearing concessions, stated plainly:

1. **"Finite capacity" is not load-bearing — it is branding.** The (Φ,λ) ontology and the Born-typicality theorem
   both hold over ordinary infinite-dimensional QFT with **no** holographic capacity bound. Delete the entropy
   bound and the interpretation is intact. So "finite capacity" is decorative *for the interpretation*; the
   finite record cardinality, where it appears, is a *separate selection-rule assumption* (`LorentzSelection.
   card_le`), **not** a holographic consequence (D3).
2. **The holographic entropy bound is the Bousso/covariant entropy bound under QIQT-H branding** — or, if
   implemented in QFT, a regulator-sensitive renormalized-entropy statement. Not a new principle.
3. **Born-from-typicality is a *conditional reduction*, not a probability-free derivation.** It reduces Born to
   P5 (the canonicity of the equiprobable/envariant measure) — which *carries the empirical content* (it is the
   quantum-equilibrium postulate for λ, the same disputed bridge principle as Deutsch–Wallace / Zurek envariance
   / typicality programs). The program already concedes this (P5 is the named open premise); it is progress
   *only if* P5 is independently motivated rather than Born in disguise — which is unsettled.
4. **The 1/4 ratio and the conditional Einstein equation are re-derivations of standard Sakharov/Jacobson**, in
   QIQT-H notation. Fork A abandons finite matter, so QIQT-H cannot even use "finite Hilbert capacity" as the
   Sakharov UV regulator; it inherits the standard species/regulator/`G`-renormalization problems. "QIQT-H's own
   derivation" is defensible only weakly ("re-derived a known result in our notation").

## What honestly survives (fair calibration)

The verdict is (b), but not nothing:
- **A clean, machine-checked single-world interpretation.** Exact unitarity + a non-dynamical selector + Born as
  across-run typicality, with the measurement problem reframed algebraically. Most interpretations are *not*
  machine-checked; this one's deductive core is axiom-free (budget 0). That rigor is real and unusual.
- **A clean Born *reduction* to one named premise (P5)** — useful even though it is not a derivation from
  unitarity alone.
- **Honest discipline already in the program** — the H2 retirement, the "cited frontiers," P5 as the open
  premise, and now this retraction. The program has been honest; the failure is the *branding* ("finite quantized
  information"), not hidden dishonesty.

## The one thing needed to be more than (b)

> **Derive a regulator-independent, Lorentz/diffeomorphism-covariant finite *operational record-capacity* bound
> with the `A/4G` coefficient FROM QIQT-H's own ontology — not by assuming Bousso/Jacobson/P5 — and make that
> bound INDISPENSABLE for a result not already available in standard QFT + holography.** Until then, "finite
> capacity" is branding, not load-bearing.

## Punch-list: align papers / site / memory with "finite *entropy*, not finite *matter*"

These are **recommended edits for the author's approval** (a public-framing reframe of the program's headline
claim should be the inventor's call; the internal record and the honest frontier notes are already updated):

- **Paper (`QIQT_Foundations_Paper.md`).** (1) Abstract/§1.1: state that "finite capacity (FQ)" is a holographic
  *entropy* bound over covariant Type III₁ matter, NOT a finite matter Hilbert space, and that it is **not
  load-bearing** for the (Φ,λ) interpretation (which holds without it). (2) Born: keep the honest "conditional on
  P5" framing; do not call it a probability-free derivation. (3) 1/4/Einstein: frame explicitly as a
  re-derivation of Sakharov/Jacobson, not a unique consequence of finiteness. (The Lorentz-naturalness frontier
  paragraph, §1.1a, is already added.)
- **Website.** Homepage/`idea`/`theory` pages that headline "finite quantized information / finite capacity":
  add the scope (finite *entropy*, an interpretation), or demote the finiteness from the headline. (`open-problems`
  Gap 4 is already added.)
- **Memory.** Record the final (b) verdict + "finite capacity not load-bearing" (done with this increment).

## Campaign status: COMPLETE

The fork is resolved: **QIQT-H is Fork A — a typicality-based single-world interpretation + an algebraic reframing
+ an assumed holographic entropy bound + standard induced gravity. The distinctive finite-information claim is
branding, not load-bearing physics.** Honest, machine-checked, and now on the public record. Never claim QG or
the value of `G`; the `1/4` ratio is derived (`SakharovRatio.lean`) — but it is a re-derivation, not unique.
