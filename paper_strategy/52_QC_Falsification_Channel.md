# 52 — Can Shor / scaling quantum computers falsify QIQT-H? (2026-06-13)

**Idea (Pawel).** Shor's algorithm / large-scale coherent quantum computation needs a huge coherent
superposition; finite `Q_max` might cap it ⇒ a falsifiable ceiling. Stress-tested (consult, checked against
the experimental record and our own Lean results per the Lean > papers > pro authority order).

## Verdict by version

**(1) As a consequence of QIQT-H's capacity bound — NO ceiling.**
Holographic capacity bounds `log₂(dim H_R) ≤ A/4ℓ_P² ~ 10⁶⁶ bits`, i.e. the *qubit count* `N`. So the region
has headroom for ~10⁶⁶ qubits; Shor on RSA-2048 needs ~4000 logical qubits — 10⁶⁶ ⋙ 4000. Moreover a QC's
computational superposition is microscopic and *non-broadcast*, so the Macroscopic Definiteness Conjecture
(about decohered macroscopic records) is silent on it. **QIQT-H predicts Shor succeeds, identical to standard
QM.** (Same lesson as `RankCountNoGo` and the `Q^eff` failure in `51`: the bound is kinematic and is the *log*
of Hilbert dimension.)

**(2) As a "branch-count cost" postulate (cost = #amplitudes `2^N`, ceiling `2^N ≤ Q_max` ⇒ N~220) — ALREADY
EXCLUDED.** `|+⟩^⊗N` is a *product* state with `2^N` computational-basis branches but zero entanglement, and
coherent product superpositions of **thousands** of atoms are routine (optical-lattice clocks, Ramsey
interferometry, spin-squeezed ensembles; N ~ 10³–10⁶). A literal branch-count ceiling would forbid these; it
doesn't. Also: branch-count is *basis-dependent* (a 60-qubit GHZ has 2 computational branches; `H^⊗N|0⟩` has
`2^N`), so it is ill-defined without a preferred basis. And branch-counting is exactly the reading our
`RankCountNoGo` proved wrong. **Dead.**

**(3) As a basis-independent complexity/entanglement ceiling (≈ Kalai's conjecture) — consistent-but-
soon-falsifiable, but it is an ADDED postulate, not QIQT-H.** A ceiling on entanglement entropy / Schmidt rank
/ circuit complexity / magic near `N_eff ~ 220` coherent logical qubits is consistent with ALL current data —
Sycamore 53–70 qubits (`2^70~10²¹`), GHZ ~60, Borealis 216 modes (`2^216~10⁶⁵`, numerically close but lossy /
non-universal), surface-code `d=7` at ~100 physical qubits — because none reach ~220 genuinely-coherent
logical qubits. This is operationally **Gil Kalai's "scalable fault-tolerant QC is impossible"** conjecture
(correlated/complexity-dependent noise floor). Strong Kalai claims ("QEC can't reduce error with distance")
are already in tension with Google's 2024 below-threshold surface-code results; the weak version (fails at
large scale) is not yet killed.

## Cleanest near-term signature (to discriminate from standard QM + local decoherence)

An **abrupt, global, complexity-threshold fidelity collapse** that (i) no local-noise model `F~e^{−εG}` can
fit, (ii) does not improve with better isolation, and (iii) does NOT decrease under QEC code-distance
scaling once the global state crosses the threshold. Decisive kill: a high-fidelity error-corrected
computation past ~220 genuinely-coherent logical qubits with logical error continuing to scale as local-noise
threshold theory predicts. Verification challenge: classical checking of >220-qubit random circuits is
impossible, so the clean route is fault-tolerant *logical* scaling, not raw RCS.

## Honest bottom line

Scaling QC is the **sharpest near-term falsification frontier** for any finite-capacity/collapse theory —
better than the neutrino channel. BUT:
- QIQT-H *as an interpretation* predicts Shor works (no ceiling from the kinematic bound).
- The naive branch-count ceiling is *already excluded*.
- The only live version is a complexity-ceiling **added postulate** = Kalai's conjecture, which would have to
  **override the log-dim counting our own `RankCountNoGo` proved correct**. It is consistent with current data,
  falsifiable within ~a decade if made quantitatively precise (else it retreats into unfalsifiability), and is
  being squeezed by below-threshold QEC progress.

So QC does not falsify QIQT-H-as-it-stands; it sharply tests a *specific committed extension* (complexity
ceiling / Kalai), which the framework's own results argue against. Consistent with `51` and the empirical-
equivalence verdict in `PROGRAM_STATUS`/`08`/`PUBLICATION_STRATEGY`/qiqt.org/idea.
