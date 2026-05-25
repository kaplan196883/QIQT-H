# Research Gap Analysis — QIQT-H Foundations Paper

## Method
Concept-mapping + problem-solution analysis applied to the 28-paper literature base. Each gap is verified by three pieces of evidence showing the gap is real and not already addressed under different terminology.

## Concept × Approach map (white-space view)

|                           | Computational/abstract cutoff | Stochastic dynamics | Rational/CA discretization | **Holographic/Wald-derived bound** |
|---------------------------|:---:|:---:|:---:|:---:|
| Reconstructs QM structure | —   | —   | —   | — |
| Bounds Hilbert dim        | Srikanth 03 | — | Palmer 25, ’t Hooft 14 | Banks 25, Bousso 02 |
| Modifies Schrödinger      | (Srikanth) | CSL, DP, Pearle | — | — |
| Selects single outcome    | Srikanth 03 | CSL, DP, Penrose OR | — | ★ **GAP** |
| Locally varying cutoff    | — | — | — | ★ **GAP** |
| Composes additively over subsystems | — | — | — | ★ **GAP** |

The three starred cells are the openings QIQT-H targets.

---

## Gap 1 — Holographic grounding of the information cutoff that produces collapse

### Type
Complete gap.

### Definition
No existing framework derives the information cutoff responsible for measurement-outcome selection from the holographic area-law / Wald entropy bound. Existing finite-information collapse proposals (Srikanth 2003, 't Hooft 2014, Palmer 2025) treat the cutoff as an abstract postulate; existing holographic-finite-dimension arguments (Bekenstein 1981, Bousso 2002, Banks 2025) do not address measurement at all.

### Evidence
1. **Srikanth (2003), quant-ph/0302160.** Postulates "finite fine-graining" as a primitive; no geometric or holographic justification. The cutoff sits at the Planck scale by assumption, not derivation.
2. **Banks (2025), arXiv:2509.17856.** Argues finite entropy in QG implies finite Hilbert dimension for subsystems — but the entire paper is silent on the measurement problem and collapse phenomenology. Explicit complement to Gap 1.
3. **Palmer (2025), arXiv:2510.02877; IST canon (Palmer 2009, 2016).** RaQM/IST introduces `N_max` from rational-number constraints attributed to gravity. *Correction to earlier draft:* Palmer's framework is not silent on outcome selection — it commits to a **superdeterministic, hidden-variable** resolution (outcomes predetermined by hidden ξ on the fractal invariant subset `I_U`; the appearance of randomness is epistemic; Statistical Independence is formally violated). The relevant gap is not "Palmer leaves outcomes open"; it is "no published finite-information account derives the bound holographically *and* delivers single-outcome selection *without* recourse to hidden variables or superdeterminism."

### Significance: **HIGH**
The measurement problem is the central open problem in QM foundations; the holographic bound is the best-established candidate for a finite information capacity in nature. Connecting them is a structural step nobody has taken.

### Feasibility
High. QIQT-H axiom A2 plus the Jacobson/Wald construction in §5–6 already provides the technical link. The paper need only formalize it cleanly.

---

## Gap 2 — Locally varying, system-dependent capacity `Q_R(R,S,…)`

### Type
Partial gap.

### Definition
All published finite-information collapse mechanisms use a single global parameter (Srikanth's fine-graining; Palmer's `N_max`; CSL's λ; Penrose's gravitational decoherence rate set by mass-energy distribution but not by region geometry). No proposal carries a coherent-information capacity that depends jointly on region geometry `R`, system `S`, environment `E`, and effective dimension count.

### Evidence
1. **CSL/Diósi-Penrose family** (Bassi-Ghirardi 2003; LISA Pathfinder bounds 2025, arXiv:2501.08971). The collapse rate λ in CSL is a universal constant; experimental bounds constrain it but do not allow regional variation.
2. **'t Hooft CA (2014), arXiv:1405.1548.** The information cell is Planck-scale and translation-invariant — no system-dependent structure.
3. **Palmer RaQM (2025), arXiv:2510.02877.** `N_max` is a global qubit capacity (~200–1000), not a region-dependent function.

### Significance: **MEDIUM-HIGH**
A region-dependent bound is *necessary* if the cutoff is to derive from local horizon area, and it is exactly what enables QIQT-H to make different quantitative claims for laboratory systems vs. cosmological scales.

### Feasibility
High. QIQT-H section 9–11 of the source document already sketches the local `Q_max(R)` and the smooth interpolation `Q_dS(1 − e^{−Q_local/Q_dS})`.

---

## Gap 3 — Single-outcome selection *without* modifying Schrödinger dynamics within a coherence patch

### Type
Controversy gap (active competition between MWI, RQM, CSL, OR — none satisfy this exact criterion).

### Definition
Existing approaches split into two camps: (i) those that modify Schrödinger evolution to obtain single outcomes (GRW, CSL, DP, Penrose OR); (ii) those that keep unitary dynamics but deny single outcomes are needed (MWI, decoherent histories, RQM/QBism's epistemic reading). No framework keeps Schrödinger unmodified *within* the coherence patch and produces an objective single outcome *at the patch boundary* via informational saturation.

### Evidence
1. **Bassi-Dorato-Ulbricht (2025), arXiv:2502.19278.** The current review explicitly catalogs (i) and (ii) above as the two recognized strategies; the QIQT-H position is absent.
2. **Palmer (2025), arXiv:2510.02877.** "The Schrödinger equation is not modified in RaQM, even during measurement" — yet Palmer makes no claim to select single outcomes; he punts on the question.
3. **'t Hooft (2014), arXiv:1405.1548.** Chooses the superdeterministic horn — denies superposition is fundamental — rather than keeping unitary dynamics and adding a separate information-saturation mechanism.

### Significance: **HIGH**
This is the architecturally novel feature of QIQT-H: a clean partition between *within-patch unitarity* (A4) and *at-boundary informational projection* (A5). Most reviewers will recognize it as a distinct position.

### Feasibility
High *if* QIQT-H can give a formally rigorous account of `P_Q: ρ ↦ [ρ]_Q`. The current QIQT-H.md leaves this projection schematic — this is the **highest-priority technical work** for the paper.

---

## Gap 4 — Quantitative composition rule for coherent information across nested subsystems

### Type
Partial gap.

### Definition
Bekenstein and Bousso bounds give upper limits on the entropy of a region, but no published proposal couples these bounds with an explicit *subadditivity rule* for coherent information that composes across nested subsystems (i.e., `Q_{AB} ≤ Q_A + Q_B` with operational meaning). Existing finite-info accounts treat the cutoff as a global ceiling, not as a structural rule on composition.

### Evidence
1. **Bousso (2002), Rev. Mod. Phys. 74:825.** Covariant entropy bound is a single inequality on a region; composition behavior across overlapping/nested regions is not given.
2. **Tilloy (2019), arXiv:1910.03278.** Studies collapse dynamics on finite-D Hilbert spaces but does not formalize a composition axiom for coherent information across joined systems.
3. **Banks (2025), arXiv:2509.17856.** Argues finite dim for subsystems; does not formalize a subadditive rule for composing capacities.

### Significance: **MEDIUM**
A composition rule is essential if the framework is to apply to nested measurement (system + apparatus + observer + environment). The QIQT-H A3 axiom (`Q_{AB} ≤ Q_A + Q_B`) is a candidate; the paper should defend and explore its consequences.

### Feasibility
High. The subadditivity axiom is already in QIQT-H.md; needs formal grounding (e.g., consistency with strong subadditivity of von Neumann entropy).

---

## Summary
- **4 gaps identified**, all with ≥3 pieces of evidence.
- At least one high-significance gap (Gap 1, Gap 3 — actually two).
- **Quality Gate 2 (gap portion): PASS.**
