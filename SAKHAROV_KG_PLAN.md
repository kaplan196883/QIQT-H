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
- **NEXT: Stage B** — replace the generic cutoff `ε` by QIQT-H's finiteness regulator (the `1/4` is regulator-
  independent since it's geometric) + the **circularity audit** (prove the `1/4` comes from the conical/EH
  geometry + the matter `a₁`, NOT from assuming `S ∝ A`). Then Stage C (the Lean Gaussian-lattice core).
