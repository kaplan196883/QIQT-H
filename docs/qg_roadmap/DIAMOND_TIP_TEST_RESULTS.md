# The DIAMOND-TIP test: RESULTS (2026-07-02)

**The named residual danger of the covariant branch has been TESTED — and it is real.** Follow-on to
`LORENTZ_STRESS_TEST_RESULTS.md` (which killed preferred-frame cutoffs and left the OP3b covariant-diamond
architecture as sole survivor, with the caveat that a diamond's tips define a timelike `u^μ_D`).
Design GPT-5.5-pro (2026-07-02, two rounds — the second correcting the closed form for the both-lines
scheme against my numerics); script `scripts/diamond_tip_test.py`.

## Part 1 — the tip vector DOES reach the effective action (single diamond)

The CHM modular-energy truncation of a diamond is LOCALLY a rest-frame cutoff (`ξ_D ≈ (L/2)u_D` near the
center; boundary corrections `O((LΛ)⁻¹)` cannot remove a dimension-4 LV operator). The honest one-loop proxy:
the anisotropic line form factor `R = exp(−(a k₄² + b|k|²)/Λ²)` on both lines, `χ = a/b` (χ=1 is the O(4)
point; the χ-deformation IS the tip vector: `q² = b[k_E² + (χ−1)(k_E·u_E)²]`). Exact closed form (validated):

```
Δc²(χ) = 2C·H_both(χ),   H_both = (1−s)(3s²+9s+4)/(4(1+s)²),   s = √χ,   C = 1/(12π²)
H_both(0) = 1,   H_both(1) = 0,   dH_both/ds|₁ = −1   (⟹ dΔc²/dχ|₁ = −C·g²)
```

| χ | exact | numeric (Λ=240) | rel |
|---|---|---|---|
| →0 (spatial endpoint) | `2C = 1.68856·10⁻²` | `1.65603·10⁻²` | 1.9% (extreme-anisotropy grid limit) |
| 1/9 (`11/16·2C`) | `+1.160972·10⁻²` | `+1.160134·10⁻²` | 0.07% |
| 1/4 (`37/72·2C`) | `+8.677972·10⁻³` | `+8.670964·10⁻³` | 0.08% |
| 1 (O(4)) | `0` | `−9·10⁻¹³` | exact |
| 4 (`−17/18·2C`) | `−1.594870·10⁻²` | `−1.592327·10⁻²` | 0.16% |

**Verdict:** `Δc² = 0 ⟺ χ = 1` (within the family), with **first-order** sensitivity `−C·g²` at the
symmetric point. Any tip-anchored truncation — including the local limit of the CHM modular cutoff on a
SINGLE diamond — generates unsuppressed percent-level×g² Lorentz violation. The tip vector survives.

## Part 2 — the rapidity average does NOT rescue it

The candidate escape "the theory has ALL boosted diamonds with an invariant measure; average" fails twice:

- **Averaging the generated LV operator:** `⟨(u⁰)²⟩_W = 1/2 + sinh(2W)/(4W)` — grows like `e^{2W}/8W`.
  There is no Lorentz-invariant finite limit (validated exactly).
- **Averaging the regulator before the loop:** on a null ray the boosted sharp cutoff has support up to
  `Λe^W` with `R_W(E) = (W − log(E/Λ))/(2W)`, and the logarithmic kinetic channel gives
  `∫ dE/E R_W² = W/12` **exactly** (validated to machine precision at W = 2,4,8,16) — LINEAR growth in W.
  The pointwise `1/W` suppression is defeated by the exponentially expanding boosted support: **the boost
  average of frame cutoffs is not a regulator at all.** The noncompactness of the boost group is fatal at
  the regulator level.

## Part 3 — the forced conclusion (the structural theorem)

There is **no local Lorentz-invariant finite-capacity momentum cutoff**: an invariant symbol can depend only
on `k²`, and sets like `|k²| < Λ²` have infinite rapidity volume (arbitrarily energetic near-null modes) —
a Lorentz-invariant bandlimit is not a finite local capacity. A finite local mode truncation NECESSARILY
introduces a timelike `u^μ` — unless the construction is **nonlocal/state-level covariant**.

**What this means for QIQT-H (honest, and constructive):**

1. Any reading of `Q_D = A/4ℓ_P²` as a *mode-counting cutoff in the diamond's rest frame* is **falsified**
   (Part 1) and cannot be repaired by summing over diamonds (Part 2).
2. The consistent reading — the one the Lean formalization ALREADY uses — is **algebraic/state-level**:
   `Q_D` bounds the *entropy of the diamond algebra in the covariant vacuum state* (the modular/Type-II
   trace bookkeeping), with covariance built in BEFORE any loop is computed (the boost-invariant `μ`,
   per-diamond modular data — the OP3b architecture; cf. `EntropyNotCardinality.entropy_bound_not_
   cardinality_bound`: capacity is entropy, NOT a count). This branch makes NO preferred-frame prediction
   at one loop because it never introduces a frame regulator.
3. The sharpened open question is therefore no longer "is there a covariant regulator?" (answer: no, locally)
   but: **does the state-level capacity constraint have any low-energy LV signature at all, and does the
   entropy-not-count reading suffice for the microstate side of the wall?** That is the next decisive item.

## Lean certification (`QIQTH/QG/DiamondTipGate.lean`, axiom-free std-3)

- `anisoH_eq_zero_iff` — within the family, `Δc² = 0 ⟺ s = 1` (the O(4) point): the tip deformation
  generically fails, machine-checked at the closed-form level;
- `anisoH_hasDerivAt_one` — first-order sensitivity `dH/ds|₁ = −1` (`tipSplit_hasDerivAt`: slope `−2C ≠ 0`);
- `anisoH_zero` — the spatial endpoint `H_both(0) = 1` (consistency with the executed CPSUV gate);
- `boostAvg_log_channel` — `∫₀^W ((W−t)/2W)² dt = W/12` exactly; `boostAvg_diverges` — it tends to
  infinity: the boost-averaged cutoff has NO regulator limit (the no-rescue certificate);
- `u0sq_avg_diverges` — `1/2 + sinh(2W)/4W → ∞` (via `sinh x ≥ x + x³/6`): no invariant average of the
  generated operator.

⚠ NOT QG; the loop integrals are numerically validated (closed forms to ≤0.16%), not formalized; the
positive follow-on (a low-energy signature bound for the state-level capacity) is open.
