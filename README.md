# QIQT-H Foundations of Quantum Mechanics

A three-paper foundational program in quantum mechanics by Paweł Kapłański (2026), combining the Chandrasekaran-Penington-Witten Type II crossed-product algebra construction with a literal physical-instantiation reading of the Bekenstein-Bousso holographic information bound.

## Two facts, one world

**1. Only $\Phi$ is dynamical — and it carries no probability.** $\Phi$ is the whole *dynamical* content of physical reality, evolving by one exactly-unitary law: no collapse, no branches-as-substances, no observer standing outside it, and no probability built into it. What we call the Born rule is an *across-run frequency*, not a number the world assigns to a single run. A run also contains exactly one *non-dynamical* fact: the actuality selector $\lambda$ — *which* of $\Phi$'s macroscopic realizations is the actual one. $\lambda$ is not a substance, not an observer, and not a probability; it is actuality, nothing more. (So "there is only the wave function" is true at the level of *constitution and law*; the complete per-run ontology is the pair $(\Phi, \lambda)$.)

**2. Information is limited by surface area.** Every bounded region $R$ can hold only $Q_R = A(\partial R)/4\ell_P^2$ worth of physical information (Bekenstein–Bousso, read literally). A region can instantiate only *finitely many distinguishable records.*

From these two facts, with decoherence, the measurement problem is *decomposed* — not by adding a mechanism, but by separating what each ingredient does: **the binary, definite outcomes we observe are a feature of macroscopic record-structures (which are area-limited and einselected), not of the wave function.** We measure in $0/1$ because *we* are macroscopic; the binary is the texture of our scale, not of the world. The honest division of labor: decoherence + einselection furnish *stable, robust, effectively Boolean* records (robustness, not uniqueness); the surface-area bound makes the set of distinguishable records *finite* (cardinality, not selection); and the non-dynamical fact $\lambda$ supplies *which* record is actual. The framework therefore **decomposes the measurement problem into a robustness part, a finiteness part, and two clearly-stated primitives ($\lambda$ actuality, and a typicality measure $\mu$ for Born statistics — itself an open problem); it does not claim to derive single outcomes from the area bound alone** (see the Central claim and the Macroscopic Definiteness Conjecture below).

## The trilogy

1. **`QIQT_Position_Paper.md`** — accessible position statement: *One Wave Function, One World: How the Holographic Information Bound Selects the Macroscopic World*

2. **`QIQT_Foundations_Paper.md`** — rigorous technical framework with Type II algebras, theorems, hidden-inconsistency framing, the Bell stance (keep free settings; violate Parameter Independence at the ontic level; operational no-signaling), the Macroscopic Definiteness Conjecture: *One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from Holographic Constraint*

3. **`QIQT_Math.md`** — end-to-end worked example on the double-slit experiment: *The QIQT-H Framework in Action: A Worked Mathematical Account of the Double-Slit Experiment*

## Central claim

The framework is **weak-ψ-monist** (the wave function $\Phi$ is the sole *dynamical* ontology; the complete per-run state is the pair $(\Phi, \lambda)$ with $\lambda$ a non-dynamical run-index selecting the realized record — ψ-ontic, weak-ψ-monist, formal-ψ-incomplete) with a finite-information axiom (FQ) constraining the instantiable regional content per bounded region of spacetime:

$$S_{\rm ren}(\omega_\Psi) \le Q_R := \frac{A(\partial R)}{4\ell_P^2}$$

The division of labor is explicit. **Continuous, conserved amplitude:** the weights $|c_k|^2$ are continuous and conserved under unitary evolution — decoherence never drives them to $0$ or $1$ (formally: `NoConcentration`). **Decoherence + einselection** make macroscopic *records* stable, redundant, and effectively Boolean — this is why a macroscopic system (apparatus, brain, AI) can only register a definite result; it explains the *stability and classicality* of outcomes, not their uniqueness. **The holographic bound** caps *how many* distinguishable records a region can hold (its genuine, non-redundant role). **$\lambda$** supplies *which* single record is actual. Schrödinger / Heisenberg evolution of the underlying field algebra is preserved exactly; no collapse, no hidden particles, no branching ontology, no modal value-rules are added.

## Central conjecture (open theorem)

**Macroscopic Definiteness Conjecture** (foundations paper §7.6). *Revised statement.* A naive reading — "two macroscopic records cost twice the information, so a two-record content exceeds $Q_R$" — does **not** follow from the Bekenstein–Bousso bound, which limits *entropy* (the number of mutually **distinguishable** records, $\#\le e^{Q_R}$), not *superposition*: a redundant cat state $\alpha\,|0\rangle^{\otimes N} + \beta\,|1\rangle^{\otimes N}$ encodes two macroscopically distinct records, fits in $N$ qubits, and is a pure state of zero entropy, violating no bound. By linearity, if $|R_0\rangle$ and $|R_1\rangle$ are each instantiable in $R$, so is their superposition — unless a superselection-type principle is added, which would stand in tension with the exact unitary linearity the framework preserves. We therefore **do not claim** the holographic bound forbids multi-record content; its genuine role is to bound the *number and redundancy* of distinguishable records, and the **uniqueness of the actual record is supplied by $\lambda$**, not derived from $Q_R$. The conjecture is restated as the open question of whether finite capacity plus einselection can be strengthened into a genuine macroscopic superselection rule consistent with unitarity — flagged as the framework's central unresolved problem, on equal footing with the Born-typicality measure, and candidly noted as currently implausible in its strong "forbids superposition" form. The framework's single-outcome content rests on $\lambda$ regardless of its fate.

## Mathematical status

- **Rigorous scaffolding (borrowed)**: Type II crossed-product algebras (Witten 2022; Chandrasekaran-Penington-Witten 2022; Chandrasekaran-Longo-Penington-Witten 2022; Jensen-Sorce-Speranza 2023)
- **Foundational axiom (our postulate)**: (FQ) literal physical-instantiation reading of Bekenstein-Bousso bound
- **Qualitative consequences worked out**: finite physical resolution; decoherence + (FQ) → stable, finite, effectively Boolean record structure (the *stage*); single-record actuality supplied by $\lambda$
- **Open problems explicitly identified**: explicit closed-form $\epsilon(R)$; whether finite capacity + einselection strengthen into a genuine macroscopic superselection rule consistent with unitarity (the revised Macroscopic Definiteness Conjecture — its strong "forbids superposition" form is currently implausible); Born-typicality measure over $\lambda$-histories analogous to Bohmian $|\psi|^2$-equivariance

The framework is presented as a research program with rigorous scaffolding + clearly identified open theorems — not a completed mathematical theory.

## Machine-checked finite core (Lean 4 / Mathlib)

The load-bearing *finite* content is formalized **axiom-free** (only Lean's standard
`propext, Classical.choice, Quot.sound`; project axiom budget **33**, all of them continuum /
operator-algebra interface axioms — none in the finite core). The headline machine-checked
result is a **finite no-collapse Born representation theorem**:

> A finite information-capacity bound forces a **unique actual pointer value** per run (no
> collapse map); a **non-contextual** outcome assignment is **forced** by finite effect-Gleason
> to be the Born weight $\mathrm{tr}(\rho P_a)$ of a density matrix; **product preparation**
> gives independent trials; and the actual-value histories then carry the **Born product law**
> and are **Chebyshev-typical**. Born statistics are *not assumed* — only non-contextuality and
> product preparation are; the world-measure is shown to carry no observable freedom.

This is a *conditional representation theorem*, not a derivation of Born from $Q_R$ alone (two
GPT-5.5-pro verification passes; honest scope and the full claim→theorem map are in
**`FINITE_BORN_REPRESENTATION.md`**). It is the realized finite portion of the program; the
**continuum, Lorentz-covariant** construction (the breakthrough μ) remains open
(`PRIZE_ROADMAP.md`, `PROGRAM_STATUS.md`).

## Repository structure

- `QIQT_Position_Paper.md`, `QIQT_Foundations_Paper.md`, `QIQT_Math.md` — the three papers
- `PROGRAM_STATUS.md` — living honest status map (what's done, the prize, must-fix set)
- `FINITE_RESULT.md` — **paper-ready master consolidation** of the whole finite, axiom-free formalization (claim→theorem map, honest ledger, suggested paper)
- `FINITE_BORN_REPRESENTATION.md` — scope + claim→theorem map for the no-collapse Born representation
- `PRIZE_EXECUTION_PLAN.md` — staged plan to the continuum prize (Stages 1–3; finite stages done)
- `PRIZE_ROADMAP.md`, `AXIOM_CONTRACTS.md`, `CORE_THEOREM_REFS.md` — roadmap, axiom audit, references
- `lean/mathlib/QIQTH/` — the Lean 4 / Mathlib formalization (axiom-free finite core; `AxiomAudit.lean`)
- `QIQT-H.md`, `QIQT-H_zapis_rozmowy.md` — original notes (Polish and English)
- `paper_strategy/` — strategy documents and GPT-5.5 review rounds
- `*.pdf` — source materials (Palmer 2025 PNAS supplement; original ChatGPT conversation)

## Author

Paweł Kapłański, 2026
