# Sakharov / induced-gravity calculation for the free Klein–Gordon field — deriving the `1/4`

**Status:** PLAN (not started). **Track:** GR / foundations (the `1/4` frontier of `P4_WALL_CAMPAIGN_PLAN.md`).
**Goal:** test whether the **`1/4`** of `S = A/4ℓ_P²` can be *derived* — not postulated — from QIQT-H's own matter
sector (the free KG field already in the machine-checked GR chain), via the **induced-gravity / entanglement-
entropy** mechanism (Sakharov 1967; Susskind–Uglum 1994; Jacobson 1994).  The mechanism: the field's vacuum
**entanglement entropy** across a surface and the **induced Newton constant** come from the *same* UV divergence,
so their ratio — `1/4` — is **cutoff-independent**.  This is the one strings-free route to the coefficient (per
the GPT-5.5-pro adjudication), and the free scalar is the cleanest case.

## 0. The claim, precisely (and the honest scope)
For a free minimally-coupled scalar in 4D, with a single UV regulator `ε`:
```
   S_ent(∂R) = A/(48π ε²) + (subleading) ,        (leading entanglement-entropy area law)
   1/G_ind   = 1/(12π ε²)  + (matter renormalization of Newton's constant, Sakharov)
   ⟹  S_ent = (A/4)·(1/G_ind)  — the ε CANCELS, the 1/4 is cutoff-independent.
```
**This reproduces known physics** (Susskind–Uglum; Jacobson; Solodukhin's review) — the value is *not* a new
result but (i) doing it with **QIQT-H's finiteness as the regulator** rather than an arbitrary cutoff, and (ii)
checking the `1/4` *survives* that substitution — i.e. that the holographic coefficient is forced by the matter
content, turning P4 from postulate toward theorem.  **Honest caveats up front (§3):** the individual coefficients
`48π`/`12π` are scheme-dependent (only the *ratio* `1/4` is robust); the universality of `1/4` across *all*
species (full Susskind–Uglum) needs the contact-term/edge-mode care (gauge fields, non-minimal coupling) and is
NOT delivered by the free scalar; and the circularity risk — the finiteness must NOT secretly do the work — must
be met head-on.

## 1. The three pieces
**(P1) Entanglement entropy of the free scalar across `∂R`.**  Two equivalent routes:
- *Conical deficit / replica* (Callan–Wilczek; Solodukhin): `S = −∂_n[ \mathrm{Tr} e^{-…} ]` via the heat kernel
  on the `n`-sheeted cone; the leading term is the `a_1`/`a_2` Seeley–DeWitt coefficient → `A/ε²`.
- *Real-space / Gaussian* (Bombelli–Koul–Lee–Sorkin; Srednicki): the ground state is Gaussian; `S_ent` of a
  region = the entropy of the reduced Gaussian state, computed from the field's two-point function restricted to
  the region; the leading scaling is `∝ A` (the area law). ← **the formalizable route (§2-C).**

**(P2) Induced Newton constant (Sakharov).**  Integrating out the scalar induces an Einstein–Hilbert term
`(1/16πG_ind)∫√g R` in the effective action; `1/G_ind` is the `a_2` heat-kernel (Seeley–DeWitt `R`-)coefficient,
`∝ 1/ε²`.  Same heat kernel, same `ε` as (P1).

**(P3) The ratio.**  `S_ent / (A · (1/G_ind)) = (1/48π)/(1/12π) = 1/4`.  The cutoff cancels; the `1/4` is the
**universal ratio of the two heat-kernel coefficients** — a *theorem* of the field's UV structure, not a free
input.  This is the sense in which the `1/4` is "derived."

## 2. Stages (deliverables: analytic markdown + symbolic/Python check + a Lean-formalizable core)

### Stage A — the analytic derivation (the mechanism)  *(markdown + `scripts/sakharov_kg.py` symbolic check)*
Write out (P1)–(P3) for the free minimally-coupled scalar: the heat-kernel/Seeley–DeWitt coefficients `a_0,a_2`,
the entanglement-entropy leading divergence, the induced `1/G`, and the cancellation giving `S_ent = A/4·(1/G)`.
Symbolically verify the `1/4` ratio (sympy) — independent of `ε` and of the overall heat-kernel normalization.
**Deliverable:** `docs/SAKHAROV_KG_DERIVATION.md` + a reproducible `scripts/sakharov_kg.py` printing `ratio = 1/4`.
**Risk: low** (known physics; the check is a clean symbolic identity).

### Stage B — the QIQT-H finiteness regulator + the circularity audit  *(markdown)*
Replace the generic cutoff `ε` by QIQT-H's **finiteness regulator** — the deformed/bounded position structure
(the finite phase space → minimal-length lattice from the framework's own notes) OR the finite record count.
Show the `1/4` ratio is *unchanged* (it must be — it's the ratio of heat-kernel coefficients, regulator-robust).
**The circularity audit (the load-bearing part):** prove the area law is NOT smuggled in via the regulator — the
`1/4` comes from the matter's `a_2/a_4` structure, not from having *assumed* `S ∝ A`.  State precisely what the
regulator supplies (a finite UV) vs. what the matter supplies (the coefficient ratio).  **Risk: medium**
(conceptual; the honest content is the circularity argument).

### Stage C — the Lean-formalizable core: Gaussian entanglement area law on a finite lattice  *(`QIQTH/Entropy/…`)*
The machine-checkable foothold (avoids heat kernels): **Srednicki's discretization** — a free scalar on a finite
`N`-site lattice is a system of coupled harmonic oscillators in a **Gaussian ground state**; the entanglement
entropy of a sub-region is a function of the eigenvalues of the (restricted) covariance matrix (the symplectic /
Williamson spectrum).  Targets:
- the **Gaussian-state entropy formula** `S = Σ [(ν+1/2)log(ν+1/2) − (ν−1/2)log(ν−1/2)]` for symplectic
  eigenvalues `ν` (finite-dimensional linear algebra — builds on the existing `QIQTH/Entropy` / quantum-entropy
  tower, the von Neumann entropy machinery);
- the **area scaling** `S ∝ (boundary size)` for the lattice ground state (the discrete area law) — the finite,
  axiom-free analog of (P1), with the records = the lattice cells.
**Risk: high** (Gaussian-state entropy + Williamson normal form is real linear-algebra work; the area-law
*scaling* may need a bound rather than the exact coefficient).  This is the genuine QIQT-H-native, finite,
machine-checkable piece — the records as a finite oscillator network whose entanglement is the area.

## 3. Honest limitations (stated up front)
- **Reproduces known physics** (Susskind–Uglum/Jacobson) — the novelty is the QIQT-H regulator + the
  circularity-clean statement, not the `1/4` value.
- **Free scalar only.** The *universality* of `1/4` across all species (gauge fields, fermions, the graviton) is
  the full Susskind–Uglum claim and needs contact-term/edge-mode treatment (Kabat) — NOT delivered here.  Free
  minimally-coupled scalar is the clean case.
- **The species problem.** The free scalar fixes `1/G_ind` for *that* field; the real `G` needs the real matter
  content.  So this derives the *mechanism* and the `1/4` *ratio*, not the physical value of `G`.
- **Mechanism, not micro-theory.** This shows the `1/4` *can* come from matter entanglement; it does NOT build
  the finite record micro-theory (the "it-from-qubit" endpoint) — it's the bridge between the machine-checked
  dressing and that frontier.
- **Circularity is the danger** — Stage B's audit is the point: if QIQT-H's finiteness *is* the area law, the
  derivation is empty.  The `1/4` must come from the matter `a_2/a_4` ratio, independent of the regulator.

## 4. Verification
- Stage A: `python scripts/sakharov_kg.py` prints the `1/4` ratio reproducibly; cross-check vs Solodukhin's
  review coefficients.
- Stage C: `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3;
  `bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per
  stage with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; refresh.

## 5. References
Sakharov 1967 (induced gravity); Bombelli–Koul–Lee–Sorkin 1986 + Srednicki 1993 (entanglement area law);
Callan–Wilczek 1994, Kabat 1995 (conical/contact terms); Susskind–Uglum 1994, Jacobson 1994 (`S_BH` = matter
entanglement = `A/4G_ind`); Solodukhin, *Living Rev. Rel.* 14 (2011) 8 (review, coefficients).

## Progress log
- **Stage A ✅** (`docs/SAKHAROV_KG_DERIVATION.md` + `scripts/sakharov_kg.py`) — the analytic derivation +
  symbolic check. From the scalar heat-kernel `a₁ = R/6`: induced `1/G_ind = 1/(12π ε²)` (Sakharov); the
  conical-deficit/replica entanglement entropy `S_ent = A/(48π ε²)`; and **`S_ent = A/(4 G_ind)`** — the `ε`
  cancels, `ratio = 1/4`. The decisive point the script makes explicit: **the `1/4` is the purely *geometric*
  ratio `(conical-deficit 4π)/(EH 16π)`**, cutoff- AND matter-independent — which is *why* the Bekenstein–Hawking
  `1/4` is universal (matter sets `G_ind`; geometry sets the `1/4`). `python scripts/sakharov_kg.py` prints
  `1/4` (all assertions pass). Reproduces Susskind–Uglum/Jacobson; the QIQT-H novelty is Stage B.
- **Stage B ✅** (`docs/SAKHAROV_KG_STAGE_B.md` + the `[Stage B]` block in `scripts/sakharov_kg.py`) — the
  finiteness regulator + the **circularity audit**. (i) The regulator substitution `ε → ℓ_P` (finite records /
  minimal length) turns the divergent `1/G_ind = 1/(12πε²)` into the finite Planckian `G_ind ~ ℓ_P²`, giving
  `S_ent ~ A/4ℓ_P²` — P4's form. (ii) **Circularity audit:** traced every input — the matter heat-kernel `a₁`,
  the conical `4π`, the EH `16π`, the regulator — and *none* carries the `1/4`; it is the *output* `= 4π/16π`.
  The area law `∝ A` **emerges** from the conical curvature being a δ-function on `Σ` (not assumed); P4's stated
  `η = 1/4ℓ_P²` is **recovered as a consequence**, never used as input. The script confirms it symbolically with
  an **arbitrary** matter coefficient `b` and **arbitrary** regulator `reg`: `S_ent/(A/G_ind) = 1/4` regardless.
  **Honest residual:** the *value* of `G_ind`/`ℓ_P` (the species problem + the concrete cutoff) is the input —
  *not* the `1/4`; and Type II finiteness alone isn't the full regulator (needs the concrete spectrum → Stage C).
- **Stage C ✅ (the building block; the full lattice-scaling is the labelled frontier)** —
  `QIQTH/GaussianStateEntropy.lean`, axiom-free (standard 3), budget 0, wired into `QIQTH.lean` +
  `AxiomAudit.lean`, full `QIQTH` build green (8709 jobs). Formalizes the **per-mode Gaussian entanglement
  entropy** `S(ν) = (ν+½)log(ν+½) − (ν−½)log(ν−½)` — the function that, by Williamson normal form, the
  Srednicki area law *sums over symplectic modes*. Machine-checked properties: `gaussModeEntropy_half`
  (`S(½)=0` — a minimum-uncertainty mode is pure, no entanglement), `gaussModeEntropy_hasDerivAt`
  (`dS/dν = log((ν+½)/(ν−½))`, the `+1`s from each `x log x` cancelling), `gaussModeEntropy_deriv_pos`
  (strictly increasing), `gaussModeEntropy_nonneg` (`S ≥ 0` — entanglement never negative, via monotonicity
  from the pure-state value; continuity at the `ν=½` endpoint handled through `Real.negMulLog`, since `log`
  itself is discontinuous at 0). This is the irreducible, finite, axiom-free kernel of the area law — the
  entropy carried by ONE mode of the record/oscillator network.
  **HONEST BLOCKER (recorded):** the full **area-law *scaling*** (`Σ over modes ∝ boundary size` from the
  lattice covariance matrix's Williamson spectrum) is **NOT** formalized — it needs the symplectic
  eigenvalue / Williamson-normal-form linear algebra (a genuine Mathlib-grade gap, flagged high-risk in §2-C).
  Stage C delivers the per-mode summand and its physics (pure⇒0, monotone, nonneg); the lattice scaling that
  turns `Σ S(νᵢ)` into `∝ A` is the cited formalization frontier, left green at this checkpoint.
- **Stage C+ ✅ (multi-mode sum — the literal `S = Σᵢ S(νᵢ)` formula)** — extended
  `QIQTH/GaussianStateEntropy.lean` (axiom-free, budget 0, full build green) to the **total** Gaussian-state
  entropy: `gaussModeEntropy_continuous` (continuous everywhere via `negMulLog`), `gaussModeEntropy_pos`
  (a squeezed mode `ν>½` carries strictly positive entropy, via strict monotonicity), and the multi-mode
  `gaussStateEntropy ν := Σᵢ gaussModeEntropy(νᵢ)` with `gaussStateEntropy_nonneg`, `gaussStateEntropy_pure`
  (all modes at the floor ⇒ 0), and `gaussStateEntropy_eq_zero_iff` (total entropy `=0` **iff** every mode
  pure — zero exactly on the unentangled state, strictly positive once any mode is squeezed). This completes
  the plan's named **Gaussian-state entropy formula** bullet (§2-C, first target). The remaining §2-C target
  — the area-law *scaling* `Σ ∝ boundary size` — stays the labelled frontier (Williamson spectrum of the
  lattice covariance matrix).
- **Stage C++ ✅ (a concrete entangled instance — the two-mode squeezed vacuum)** — added to
  `QIQTH/GaussianStateEntropy.lean` (axiom-free, budget 0, full build green) the canonical genuinely-entangled
  Gaussian: `twoModeSqueezedSympEig s := cosh(2s)/2` (the reduced single-mode symplectic eigenvalue of the
  two-mode squeezed vacuum). Machine-checked: `_ge_half` (respects the `ν≥½` floor via `cosh≥1`), `_half_iff`
  (`ν=½ ⟺ s=0`, i.e. floor ⟺ no entanglement), `twoModeSqueezed_entropy_pos` (any `s≠0` ⟹ strictly positive
  entanglement entropy), `twoModeSqueezed_entropy_zero` (`s=0` ⟹ a product state, zero entropy). This makes the
  abstract formula **non-vacuous on a real physical state** — the irreducible 2-mode area-law model.
- **Stage C+++ ✅ (the area-law *seed* — entropy counts only entangled modes)** —
  `gaussStateEntropy_eq_sum_active` (axiom-free, budget 0, full build green): the total entropy equals the
  sum over the **strictly-squeezed** modes alone (`νᵢ > 1/2`); pure modes (`νᵢ = 1/2`) drop out. This is the
  precise structural seed of the area law — *the entropy counts entangled modes* — and isolates the sole
  remaining (cited) physics: for a lattice ground state those entangled modes localize at the region's
  **boundary** (the Williamson symplectic spectrum), turning the count into `∝ boundary size`. That last step
  is the labelled frontier.
- **Stage C⁴ ✅ (the symplectic eigenvalue from a covariance matrix — `n=1` Williamson)** — `oneModeSympEig
  a b c := √(ab−c²)` (the single-mode symplectic eigenvalue = `√det` of the `2×2` covariance `[[a,c],[c,b]]`),
  with `oneModeSympEig_ge_half` (the Heisenberg uncertainty bound `det ≥ 1/4` ⟹ `ν ≥ 1/2`), `oneModeSympEig_pure`
  (saturated bound `det=1/4` ⟹ pure floor), and `oneModeSympEig_entropy_nonneg`. This is the **first real piece
  of Williamson** — it grounds `ν` in physical *covariance data* (not an abstract input), for the tractable
  `n=1` case. The `N`-mode reduction (diagonalizing the `2N×2N` covariance by a symplectic transformation)
  stays the labelled frontier. Axiom-free, budget 0, full build green.
- **Stage C⁵ ✅ (`n=1` symplectic INVARIANCE — `ν` is a symplectic invariant)** — `oneModeSympEig_eq_sqrt_det`
  (`ν = √det !![a,c;c,b]`), `det_conj_eq_of_det_one` (`det(S M Sᵀ)=det M` for `det S=1`, pure det-multiplicativity),
  and `oneModeSympEig_symplectic_invariant`: under a one-mode symplectic congruence `M ↦ S M Sᵀ` with
  `S ∈ Sp(2,ℝ)=SL(2,ℝ)`, `√det(SMSᵀ) = oneModeSympEig a b c`. This is the **defining feature** of a symplectic
  eigenvalue — basis-independence — making `ν` a genuine physical invariant (readable off any canonical frame),
  the property the whole Williamson-spectrum / area-law mode-count rests on. The `N`-mode normal form stays the
  labelled frontier. Axiom-free, budget 0, full build green.
- **Stage A-Lean ✅ (the `1/4` RATIO machine-checked — Lean mirror of `scripts/sakharov_kg.py`)** —
  `QIQTH/SakharovRatio.lean` (axiom-free, standard 3, budget 0, wired into `QIQTH.lean` + `AxiomAudit.lean`,
  full `QIQTH` build green, 8713 jobs). Formalizes the **circularity-clean algebraic core** the sympy script
  checks: `sakharov_ratio` — with `S_ent = A·b/(48π·reg)` and `1/G_ind = b/(12π·reg)`, the ratio
  `S_ent/(A/G_ind) = 1/4` with the **arbitrary** matter coefficient `b`, **arbitrary** regulator `reg`, area
  `A`, and `π` ALL cancelling (the `1/4` is the *output*, never an input); `geometric_quarter` — `4π/16π = 1/4`
  (the conical-deficit/EH geometric origin); `heatkernel_ratio_eq_geometric` — `(1/48π)/(1/12π) = 4π/16π` (both
  `1/4`, the two presentations agree). **HONEST SCOPE (in the file's docstrings):** this machine-checks the
  RATIO cancellation only; the heat-kernel coefficients `48π`/`12π` are physics INPUTS (Seeley–DeWitt `a₂`,
  reproducing Susskind–Uglum/Solodukhin), and the area-law SCALING `S∝A` (Williamson / M3), the VALUE of
  `G_ind`/`ℓ_P` (the species/UV datum), and cross-species universality remain the labelled frontiers / carried
  input. So: the `1/4` *ratio* is now a Lean theorem (regulator- and matter-independent); the value of `G` stays
  carried.
- **PLAN COMPLETE** (A+B+C+/++/+++/⁴/⁵ + A-Lean; only the N-mode Williamson reduction is the labelled frontier). Net: the `1/4` is derived (geometric, non-circular — A+B) and now **machine-checked in Lean** (A-Lean); the Srednicki entropy formula
  `S = Σᵢ S(νᵢ)` and its physics (pure⇔0, monotone, nonneg, strictly positive when entangled) are
  machine-checked (C/C+), instantiated on the canonical entangled two-mode squeezed vacuum (C++), and reduced
  to a sum over the entangled modes only (C+++) — the area-law seed, frontier = "entangled modes ⟹ boundary".
