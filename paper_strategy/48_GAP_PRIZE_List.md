# QIQT-H — GAP / PRIZE list (the build-on document)

**Status as of:** 2026-06-12. **Verified by:** GPT-5.5-pro (assessment verification, this date) +
machine-checked Lean corpus (commit `4720763a7b59`). This is the canonical, honest map of what is DONE,
what is MISSING, and what closing each gap BUYS ("the prize"). Use it to plan the next builds.

**One-line thesis:** bounded regions hold only finite physical information (holography), so a region cannot
*instantiate* a wave function carrying ≥2 macroscopic records — so after decoherence the per-run state is
*already* single-record, with global unitarity exactly intact (no collapse, no MWI, no Bohm, no modal rule).

**The argument is a 5-link chain. Two links are postulates, one is conditional, one is open, one is the
verified substrate:**

| Link | Claim | Status |
|---|---|---|
| 1 | Holography ⟹ region `R` has finite capacity `Q_R=A(∂R)/4ℓ_P²` | **Postulate (FQ)** |
| 2 | Regional content = state on dressed Type II `Â(R)`, cost `χ_R`=Araki rel. entropy to `σ_R` | **Calculus verified** (not the framework) |
| 3 | A ≥2-record content has `χ_R > Q_R` | **GAP 1 — conjecture (H2)** |
| 4 | ∴ ≥2-record states not instantiable ⟹ single-record (Thm 6, given H1∧H2∧H3) | **Conditional + GAP 2 (dynamical)** |
| 5 | Born probabilities from typicality of microscopic ICs | **GAP 3 — open** |

---

## ✅ WHAT IS DONE (the verified floor — do not over-credit it)

**A. The modular / relative-entropy CALCULUS (free-field coherent sector), machine-checked, no `sorry`,
only standard classical Lean axioms.** This is the *calculus that link 2 uses* — **NOT** the dressed Type II
regional content map, the CPW crossed product, gravitational dressing, or the capacity inequality.
- finite Araki = Umegaki (`arakiEntropy_eq_relEntropy`); bounded Tomita–Takesaki (`JRJ=2−R`, `Δ^{it}`,
  strong continuity); CGP one-particle relative entropy + **positivity** `S(ξ)≥0` for localized `ξ∈𝒦`
  (`cgpEntropy_nonneg`); free-field modular flow `Γ(Δ^{it})`, `σ_t(W(u))=W(Δ^{it}u)`; relative modular
  operator + Connes cocycle + chain rule; the **entropy reduction** `S(ω_{W(f)Ω}‖ω_Ω)=cgpEntropy(f)`
  (`hasDerivAt_relModFlow_vacuum`). Full index: `paper_strategy/45_Theorem_Paper_Index.md`.
- *Scope caveats (per GPT-5.5-pro):* `log((2−r)/r)` is bounded only in the regular regime `σ(R)⊆[a,2−a]`
  (the achievement is "no unbounded `log Δ` is built", not a bounded integrand); the relative-modular
  formula `Δ_{uΩ|Ω}=uΔu*` needs `W(f)∈M` (`f` in the real standard subspace) and a stated slot convention.

**B. Finite no-collapse layer (finite-dim), machine-checked:** the finite Born representation
(`FINITE_BORN_REPRESENTATION`, `EffectGleason.finite_effect_gleason`, `BornJoin*`), the finite typicality
skeleton (`BornTypicalityFinite`: finite weak LLN / Chebyshev), the finite Type-I modular flow, and the
record-net evaluation-equivariance skeleton (`DiamondSwapNet`, `covariant_selection_of_net`). These are the
finite *shadows* of the continuum mechanism.

**C. A subspace-invariance piece relevant to GAP 2:** `modUnitary_mapsTo_K` (`U_t 𝒦 ⊆ 𝒦`, the modular flow
preserves the standard subspace) — a fragment of dynamical invariance.

---

## 🎯 THE GAPS (load-bearing order) + PRIZES

### GAP 1 — H2 / Macroscopic Definiteness (THE CRUX)
- **Claim to establish:** a regional content with ≥2 operationally-distinct macroscopic records has
  `χ_R > Q_R`.
- **Why decisive:** the no-collapse conclusion has *zero* bite until this holds. *Finite capacity alone does
  NOT forbid 2-record superpositions* — a finite-dim Hilbert space contains superpositions of many
  distinguishable vectors. H2 is the nonstandard *extra* claim that physically *instantiating* a 2-record
  state costs more than `Q_R`.
- **PRIZE:** turns the thesis from a conditional program into a genuine no-collapse *result*. The headline.
- **Done toward it:** essentially nothing direct. The CGP calculus gives a *calculable* cost for coherent
  excitations but **no macroscopic lower bound**. A DPI/readout-channel route gives only ~`log 2`
  (order-one classical info), **not** an area-scale violation.
- **Needed (subtasks):** (i) operationally define "macroscopic record" inside the algebra; (ii) a
  *quantitative model* of the `χ_R` cost to instantiate one record; (iii) a robust lower bound showing TWO
  records force `χ_R > Q_R` — robust to compressed / error-corrected / degenerate / non-coherent encodings;
  (iv) tie the bound to the area law `Q_R`.
- **Difficulty:** HARD (genuine new physics). **Formalizable?** only after a concrete model exists; the
  fundamentally-different argument needed is likely a distinguishability-volume / modular-Hamiltonian
  estimate, not DPI.

### GAP 2 — Dynamical realization (static exclusion → single-outcome evolution)
- **Claim to establish:** even granting H2, actual *unitary* measurement evolution produces **exactly one**
  admissible record (not zero), and the admissible-state space is **invariant under the dynamics**.
- **Why it matters:** Theorem 6 is a *static exclusion* theorem. It rules out 2-record states; it does NOT
  show measurement dynamics *lands on* a single-record state, nor that one (not zero) records appears, nor
  that a concrete interaction maps microscopic ICs → single record.
- **PRIZE:** closes the loop from *constraint* to *mechanism* — makes "no collapse" a dynamical statement,
  not just a kinematic exclusion.
- **Done toward it:** the finite no-collapse representation + record-net skeleton (B) is the finite shadow;
  `modUnitary_mapsTo_K` (`U_t 𝒦⊆𝒦`) is a continuum invariance fragment.
- **Needed:** existence of an admissible post-measurement state; exactly-one-not-zero; dynamical invariance
  of the admissible space under the field/measurement dynamics; a concrete measurement model ICs→record.
- **Difficulty:** MEDIUM–HARD. Partly **formalizable in finite dimensions now** (good near-term Lean target).

### GAP 3 — Born from typicality (the probabilities)
- **Claim to establish:** among admissible microscopic ICs, the outcome-`i` subset carries Born weight
  `|c_i|² = ω_Φ(P_i)`.
- **Why it matters:** H2 + GAP 2 give *single outcomes* but no *statistics* → not empirically adequate.
  Logically independent of H2 (single-outcome exclusion does not need Born), but mandatory for predictions.
- **PRIZE:** makes the theory predictive. The prize-aligned track is **OP3b: the covariant typicality
  measure**.
- **Done toward it:** finite typicality skeleton (`BornTypicalityFinite`) + finite Born representation,
  machine-checked; the record-net evaluation-equivariance skeleton. *But the bare existence of a
  `RecordedHistoryNet` is trivially true — the genuine open problem is the REALIZATION.*
- **Needed (OP3b realization):** a measure `μ` that is (a) extracted from a *fixed* relativistic QFT +
  geometry (area law `N(D)=⌊e^{Q_D}⌋`, boundary algebra fixed externally), (b) **Born-pinned** to `ω_Φ(P_i)`
  of an actual global state `Φ`, (c) equivariant under a *genuine Poincaré group action* (current
  `PoincareAction` is a single order-automorphism, not a representation), (d) σ-additive / Lorentz-invariant.
- **Difficulty:** HARD (continuum). Finite track DONE; continuum = OP3b, the cited prize frontier.

### GAP 4 — FQ grounding + continuum / general-state realization
- **Claim(s):** (a) ground `S_ren ≤ Q_R` rather than postulate it; (b) extend the modular/entropy results to
  *general* (non-coherent) states and the Type III→II continuum.
- **Why it matters:** FQ is postulated (CPW give the Type II *entropy*, not the *bound*); the formalization
  is free-field/coherent only.
- **PRIZE:** weakens the central assumption; the Type III / unbounded-modular formalization is a
  Mathlib-grade contribution in its own right.
- **Done toward it:** the bounded coherent-state modular theory + entropy reduction (A); free-field `σ_t`.
- **Needed:** general two-state relative modular operator (**needs unbounded GNS — the Mathlib gap**); Type
  III classification; the CPW crossed product; a holographic/quantum-gravity grounding of FQ.
- **Difficulty:** VERY HARD (unbounded operator theory Mathlib lacks). The cited frontier; not a blocker for
  the (conditional) paper.

---

## DEPENDENCY / BUILD ORDER

- **GAP 1 (H2)** is independent and decisive — attack the *concept* first (a quantitative cost model). It
  does not wait on the others.
- **GAP 2 (dynamical)** partly rides the finite-dim no-collapse work already done → best **near-term Lean**
  target.
- **GAP 3 (Born)** has a finite track DONE + the OP3b continuum track (the prize).
- **GAP 4 (continuum/general)** is the deep Mathlib frontier — defer; chip at finite/semifinite analogues.

## CONCRETE NEXT LEAN BUILD-ON TARGETS (mapped to gaps)

1. **(GAP 1 support, NOT a proof of H2)** finite-dim / semifinite **Donald's identity + Fano + the
   conditional no-multi-record theorem under H1–H3** — directly supports the paper's Theorem 6 and is the
   highest-value formalization closer to the load-bearing claim.
2. **(GAP 2)** finite-dim **dynamical single-outcome**: `U_t`-invariance of the admissible (≤capacity)
   subspace + existence/uniqueness of the single-record post-measurement state. Tractable now.
3. **(GAP 3)** OP3b realization steps: externalize the geometry spec, replace the single automorphism by a
   genuine **group action** with equivariant weights, tie `ω` to the formalized Born functional.
4. **(GAP 4)** general two-state relative entropy → blocked on unbounded operators (Mathlib); revisit only
   after upstream support.

---

## ONE-PARAGRAPH HONEST SUMMARY (for any external doc)

QIQT-H is a logically coherent, conditional research program whose *mathematical substrate* (the
modular / relative-entropy calculus underlying the regional cost `χ_R`) is machine-checked for the
finite and free-field coherent sectors. The program becomes a *theory* only when (1) **H2** — that a ≥2-record
regional content exceeds the holographic capacity — is quantitatively established, (2) the **dynamical
realization** connects that static exclusion to actual single-outcome unitary evolution, and (3) **Born
statistics** are derived from typicality. The formalization strengthens the floor; it closes none of these.
