# Literature Review Report — QIQT-H Foundations Paper

## Literature coverage
- **Papers in core literature base:** 28
- **Time span:** 1986–2026
- **Disciplines:** quantum foundations (quant-ph), gravity/holography (gr-qc, hep-th), philosophy of physics
- **Core concepts covered:** finite information / Hilbert dimension, holographic bound, collapse mechanisms, informational reconstruction, thermodynamic gravity, measurement problem, single-outcome selection

## A. Direct precursors — finite-information accounts of measurement

1. **Srikanth, R. (2003).** *A Computational Model for Quantum Measurement.* Quantum Inf. Process. 2(3): 153–199. [arXiv:quant-ph/0302160]. **★ Critical precursor.** Assumes finite fine-graining of Hilbert space; argues that when measurement-entanglement exceeds this capacity, unitary evolution becomes "computationally unstable" and the system suffers an "information transition" — exactly the QIQT-H A2+A5 mechanism, but cast in computational rather than geometric language. Provides a "probabilistic complement to decoherence". 23 years old, modestly cited.
2. **Mayburov, S. (2010, rev. 2025).** *Information Constraints in Quantum Measurements.* [arXiv:1005.3691]. Derives Born rule from constraints on measuring apparatus's ability to distinguish pure vs. mixed ensembles. Different mechanism (apparatus epistemic constraint) but same general spirit.
3. **Hamid, E. I. B. (2025).** *The Emergence of Objective Classicality: A Computational First-Principles Study of Observer-Induced Decoherence.* [arXiv:2509.12280]. Demonstrates classicality from purely unitary dynamics with observer-as-subsystem. Does not invoke an info bound; complementary baseline.

## B. Objective collapse models (the main empirical rivals)

4. **Ghirardi, Rimini & Weber (1986).** *Unified dynamics for microscopic and macroscopic systems.* Phys. Rev. D 34: 470. Foundational GRW collapse model.
5. **Pearle, P. (1989).** Continuous Spontaneous Localization (CSL).
6. **Diósi, L. (1989).** Gravitationally-induced collapse.
7. **Penrose, R. (1996).** *On gravity's role in quantum state reduction.* Gen. Rel. Grav. 28: 581. (Penrose OR.)
8. **Bassi, A. & Ghirardi, G. (2003).** *Dynamical reduction models.* Phys. Rep. 379: 257.
9. **Tilloy, A. (2019).** *Continuous collapse models on finite dimensional Hilbert spaces.* [arXiv:1910.03278]. Technical baseline for the finite-D limit.
10. **Carlesso et al. (2025).** *Improved bounds on collapse models from LISA Pathfinder.* Phys. Rev. A 111: L020203. [arXiv:2501.08971]. Current state-of-the-art empirical bounds on CSL — any rival mechanism must clear these.
11. **Bassi, Dorato, Ulbricht (2025).** *The Quantum Measurement Problem: A Review of Recent Trends.* [arXiv:2502.19278]. Most recent comprehensive review.
12. **(Review article) (2025).** *Spontaneous Collapse Models.* [arXiv:2508.18822]. Companion review.

## C. Holographic / finite-dimension-in-QG line

13. **Bekenstein, J. D. (1981).** *Universal upper bound on the entropy-to-energy ratio.* Phys. Rev. D 23: 287.
14. **'t Hooft, G. (1993).** *Dimensional reduction in quantum gravity.* [arXiv:gr-qc/9310026].
15. **Bousso, R. (2002).** *The holographic principle.* Rev. Mod. Phys. 74: 825. [arXiv:hep-th/0203101]. Canonical covariant entropy bound reference.
16. **Wald, R. M. (1993).** *Black hole entropy is the Noether charge.* Phys. Rev. D 48: R3427. (Wald entropy formula used in QIQT-H §6.)
17. **Buoninfante, Lambiase, Petruzziello (2020).** *Bekenstein bound from the Pauli principle.* [arXiv:2005.13973]. Alternative derivation.
18. **Banks, T. (2025).** *Finite Entropy Implies Finite Dimension in Quantum Gravity.* [arXiv:2509.17856]. **★ Important ally.** Argues that black-hole-physics intuition requires finite-D Hilbert spaces for subsystems with finite entropy. *Does not address measurement* — this is precisely the gap QIQT-H fills.

## D. Informational reconstructions of QM

19. **Hardy, L. (2001).** *Quantum Theory From Five Reasonable Axioms.* [arXiv:quant-ph/0101012]. Pioneering informational axiomatization.
20. **Chiribella, D'Ariano, Perinotti (2011).** *Informational derivation of quantum theory.* Phys. Rev. A 84: 012311.
21. **Masanes, L. & Müller, M. (2011).** *A derivation of quantum theory from physical requirements.* New J. Phys. 13: 063001.
22. **Berghofer, P. (2024).** *Defending the Quantum Reconstruction Program.* Eur. J. Phil. Sci. [arXiv:2410.21152]. Recent philosophical defense.
23. **(2025).** *Systematizing the Interpretation of Quantum Theory via Reconstruction.* [arXiv:2512.18002]. Recent meta-review.

## E. Finite-state / deterministic alternatives

24. **'t Hooft, G. (2014/2016).** *The Cellular Automaton Interpretation of Quantum Mechanics.* [arXiv:1405.1548]; Springer. Superdeterministic CA interpretation.
25. **Palmer, T. (2009).** *The Invariant Set Postulate.* Proc. Roy. Soc. A 465: 3165. [arXiv:0812.1148]. IST foundational paper.
26. **Palmer, T. (2016).** *Invariant Set Theory.* [arXiv:1605.01051].
27. **Palmer, T. (2025).** *Rational Quantum Mechanics: Testing Quantum Theory with Quantum Computers.* [arXiv:2510.02877]. **★ Critical contemporary.** RaQM keeps Schrödinger unmodified; introduces finite qubit capacity `N_max ≈ 200–1000` from rational-number constraints attributed to gravity; predicts quantum-advantage saturation at ~1000 qubits. *Does not address single-outcome selection.*

## F. Thermodynamic / emergent gravity (used by QIQT-H§5)

28. **Jacobson, T. (1995).** *Thermodynamics of spacetime: The Einstein equation of state.* Phys. Rev. Lett. 75: 1260. [arXiv:gr-qc/9504004]. Original derivation `δQ = TdS ⇒ G_{μν} = 8πGT_{μν}`. QIQT-H reuses this construction. Cite, do not reprove.

## Organization by theme

- **Same thesis as QIQT-H** (collapse from info bound): Srikanth 2003, Mayburov 2010, partially 't Hooft CA, partially Penrose OR.
- **Same holographic premise** (finite Hilbert dim from area law): Bekenstein 1981, 't Hooft 1993, Bousso 2002, Banks 2025. None of these connect to measurement.
- **Same axiomatic style**: Hardy 2001, Chiribella et al. 2011, Masanes-Müller 2011. None of these address measurement collapse.
- **Empirical bar to clear**: GRW, CSL, DP, Penrose OR — all give *some* falsifiable signature. QIQT-H needs at least one analogous signature.
- **Closest contemporary** (must engage directly): Palmer RaQM 2025 — same era, related claims, leaves the same gap QIQT-H proposes to fill.

## Quality Gate 2 check
- ✓ Core papers ≥20 (have 28)
- ✓ Keywords coverage complete (finite info, holography, collapse, axiomatization, gravity)
- ✓ Time span adequate (40 years + recent)
- ✓ Multiple disciplines covered (quant-ph, gr-qc, hep-th, philosophy)
- ✓ Both proponents and rival approaches included
- **PASS** — proceed to gap analysis.
