# J2 — local-symbol audit of QIQT-H's actual capacity: VERDICT

**Date:** 2026-06-30. **Plan:** `COVARIANT_CAPACITY_CPSUV_PLAN.md` J2 (the decisive conceptual increment).
**Question:** is QIQT-H's actual per-causal-diamond capacity a **mode / modular-energy truncation** (a
frame-picking UV symbol `F_D = f((u_D·k)², k_⊥²)` ⟹ CPSUV-class, FAIL) or a **nonlocal / algebraic state-count
constraint** (no frame-picking UV symbol ⟹ escape-class)? J1 showed the answer is decided entirely by which class
the regulator is in.

## What QIQT-H's capacity actually IS (from the code)

`QIQTH/LorentzSelection.lean`, `structure RecordedHistoryNet`:

```lean
P    : RecordPresheaf Diam                                   -- bulk record-sector presheaf
fin  : ∀ D, Fintype (P.X D)                                  -- each diamond's record fibre is FINITE
N    : Diam → ℕ                                              -- holographic atom budget  N D ≈ ⌊exp Q_D⌋
card_le : ∀ D, Fintype.card (P.X D) ≤ N D                    -- ★ THE CAPACITY BOUND
ω    : ∀ D, P.X D → ℝ                                        -- decoherence-functional weights ω_Φ(P_i^D)
ω_nonneg, ω_norm, ω_marg                                     -- ω is a no-signaling probability measure
```

with (docstring, lines 356–359, 381–384) the explicit reading

> `#Atoms(B_Φ(D)) ≤ N D` — the discrete form of `log #Atoms ≤ Q_D = A(∂D)/4ℓ_P²`.

So the capacity is **`Fintype.card (P.X D) ≤ exp(Q_D)`**: a **cardinality bound on the record-sector fibre** —
the number of *distinguishable macroscopic record atoms* (the decoherent pointer sectors, carrying the
decoherence measure `ω`) in a causal diamond `D` is at most `exp(A(∂D)/4ℓ_P²)`.

## Verdict: class (b) — an algebraic state-COUNT, NOT a mode truncation

The bound is on **`Fintype.card (P.X D)`** — the *cardinality of a finite set of records*. It is:
- **NOT** a cutoff on matter-field momentum modes `|k| < Λ` (there is no field momentum anywhere in the
  structure — `P.X D` is an abstract finite record-sector type, not a mode space);
- **NOT** a modular-energy (`K_D`-spectral) truncation (no modular Hamiltonian, no spectral cutoff — the only
  per-diamond datum is the integer budget `N D` and the probability weights `ω`);
- a **nonlocal / algebraic counting constraint** on the decoherent record content per diamond — class **(b)**.

The record atoms `P.X D` are the *coarse-grained classical pointer sectors* (equipped with the decoherence
functional `ω`), which are exponentially *fewer* than the underlying field microstates and have no momentum
labels at all. So QIQT-H's capacity has **no matter-field UV symbol `F_D(x,k)`** in the sense J1 tested — it does
not regulate matter loops.

## Consequence — honest, two-sided

**(+) It dodges the direct CPSUV kill.** The I4/J1 FAIL is specifically of a matter-field UV regulator with a
frame-picking symbol (a mode / `K_D`-spectral truncation, class (a)). QIQT-H's capacity is **not** such a
regulator — it is an algebraic record-count with no local UV symbol — so the CPSUV kill **does not apply to it as
coded.** QIQT-H's capacity is *not* in the FAIL class. (This vindicates the earlier point that the I4 kill is of
the *local-cutoff strawman*, not QIQT-H's actual construction — see `qiqth_lorentz_two_threads`.)

**(−) But it does NOT, by itself, ESCAPE either.** Precisely *because* the capacity is a record-count and not a
matter-field regulator, **it is silent on the matter-field UV regularization.** The matter QFT on which the
records form still needs *some* UV completion, and whether that completion is Lorentz-scalar (escape, `Δc²=0`) or
frame-picking (FAIL, `Δc²≠0`) is a **separate question the capacity does not answer.** Imposing
`#Atoms ≤ exp(Q_D)` constrains how many records a diamond can hold; it says nothing about the matter propagator's
short-distance symbol.

## Where this leaves the decisive question

QIQT-H's capacity is **class (b)** — exactly the kind a genuine escape needs (a nonlocal/algebraic state-count,
not a mode truncation). But the escape is **not yet achieved**, because the capacity must be **paired with a
Lorentz-scalar matter UV kernel** (proper-time / □ / Pauli–Villars) for the *matter* loops to be covariant. That
pairing — a covariant UV kernel + the algebraic record-count capacity, both inside the (frame-free) crossed-
product / modular structure — is **plan J6, QIQT-H's real construction problem** (months–years).

**Net (matches the plan's anticipated outcome, stated plainly):** the CPSUV kill applies to the *mode-truncation
misreading* of finite capacity; QIQT-H's *actual* capacity (an algebraic record-count) escapes that kill but does
not supply the matter UV regulator, so a full escape requires J6 (a covariant kernel + the algebraic capacity).
The honest status is therefore **"not FAIL, not yet ESCAPE — silent on the matter UV, which must be supplied
covariantly."** Never claim QG or the value of `G`; the `1/4` ratio is derived (`SakharovRatio.lean`).
