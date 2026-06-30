# Toward quantum gravity — the honest campaign

**Status:** ACTIVE PLAN (2026-06-30). **Verdict it operationalizes:** QIQT-H is **not** quantum gravity — it is a
finite-information foundation + a semiclassical/thermodynamic route to *classical* Einstein on an assumed
background + a finite proto-geometry scaffold. Genuine QG needs **Tier 2** (a finite-capacity substrate with a
controlled continuum/RG limit recovering approximate Lorentz QFT) **and Tier 3** (derive metric/RT/JLMS/Type-II/
linearized→nonlinear Einstein/graviton/constraints/diff-invariant Born measure *from* that substrate). Both are
category **(c)** — the open problem. See `docs/qg_roadmap/`.

> **This plan does not promise QG.** It sequences the *de-risking experiments* and *buildable Lean cores* that
> either keep the finiteness bet alive or kill a branch, and it names the frontier honestly. Progress is measured
> in *"we built a toy that exhibits X with error scaling Y"* and *"we proved no-go Z,"* never *"we derived QG."*

---

## 0. Honest invariants (enforced every increment)

- **Never claim QG, the value of `G`, or the `1/4` coefficient.** The `1/4` *ratio* is derived (`SakharovRatio`);
  the value of `G` and the area normalization `⟨A_edge⟩ = A(∂R)` are the carried UV datum.
- **Finiteness is a BET to be tested, not assumed.** The central tension (GPT-5.5-pro, 2026-06-30): an *exact*
  finite cutoff conflicts with *exact* Lorentz invariance. The campaign's first job is to *measure* whether
  finite capacity coexists with **bounded, suppressed** Lorentz violation — not to assume it does.
- **Ship green increments; checkpoint frontiers.** Each Lean increment: `lake build` green, `#print axioms` =
  std-3, `axiom_budget_check.sh` budget 0, one commit, push. Each simulation: a reproducible script + the data.
- **Distinguish (b) buildable from (c) open.** Tag every deliverable. Most of Tier 2/3 is (c); say so.

---

## 1. The bottleneck and the de-risking centerpiece

Per the GPT-5.5-pro QG audit ([[qiqth_qg_lorentz_cutoff_verdict]]), the bottleneck is **not** more finite RT
lemmas — it is the **Lorentz / RG naturalness of finite capacity**. The single highest-leverage move is the
**Lorentz-Cutoff Stress Test**: build one finite-capacity toy, measure its low-energy Lorentz defect, and run the
**one-loop speed-splitting test** `Δc² := Z_s/Z_t − 1`. If interactions drive `Δc²` to a nonzero `O(g²/16π²)`
constant as `Λ→∞`, the naive finite-cutoff branch hits the **Collins–Perez–Sudarsky–Urrutia–Vucetich** obstruction
(PRL 93, 191301, 2004) and must be abandoned or protected by a symmetry. That single number is the campaign's
decisive pass/fail.

---

## 2. The increments — most-tractable-first

### Phase A — buildable-now no-gos that honestly bound the finite claims *(Lean, (b))*

- **I1 — Finite Poincaré trace no-go (gate B).** On a finite-dim Hilbert space, `[K,P]=i·H` with `H ⪰ 0` forces
  `H = 0` (trace of a commutator is 0; PSD + trace 0 ⟹ 0). So an *exact* finite-region Poincaré algebra forces a
  trivial Hamiltonian — finite capacity can carry boosts only **approximately**. `QIQTH/QG/FinitePoincareNoGo.lean`.
  **Tractable now.**
- **I2 — BW-recurrence bound (gate C).** Finite modular flow has discrete spectrum + recurrences, so it cannot
  exactly realize continuum Bisognano–Wichmann modular flow for *all* boost times. A theorem to this effect forces
  our finite modular/spectral results to be honestly *finite-time / low-energy approximate*. `QIQTH/QG/`. **Tractable.**

### Phase B — the Lorentz-cutoff stress test *(Lean dispersion bound + Python loop test, (b))*

- **I3 — free dispersion Lorentz-defect bound.** For the lattice/QCA dispersion `E_a(p)² = m² + (4/a²)sin²(ap/2)`,
  prove `|E_a(p)² − (m²+p²)| ≤ a²p⁴/12` — the cheap, known pass: defect `~(ap)²`, `α=2`, **no rapidity-independent
  floor**. Lean theorem. (Cheap pass — not yet decisive.)
- **I4 — the decisive one-loop `Δc²` naturalness test.** A free-fermion chain / QCA Dirac toy: extract `Γ⁽²⁾`,
  compute `Δc² = Z_s/Z_t − 1` at one loop. **PASS** if `Δc² ~ (E/Λ)^α` (suppressed); **FAIL** if it tends to a
  nonzero `O(g²/16π²)` constant (CPSUV). Python/numerics + a short note. **This is the campaign's pass/fail gate.**

### Phase C — Lean cores toward Tier 2/3 *(Lean, (b) in the toy / (c) for the real thing)*

- **I5 — T1 crossed-product finite trace** (`CrossedProductFiniteTrace.lean`, see
  `CROSSED_PRODUCT_TYPE_II_SCOPE.md` §3): a non-vacuous `Phase5Master` instance from a finite trace ⟹ P4's
  holographic floor unconditional in a concrete model. The Tier-2 §2.2 "area law from the substrate" direction.
- **I6 — exact finite RT** (the hard half of max-flow=min-cut): upgrade `flow_weak_duality` to the equality in a
  finite holographic code — the Tier-3 §3.2 "RT as a substrate theorem" core. (Mathlib may lack max-flow=min-cut;
  build the LP/Menger direction or checkpoint.)

### Phase D — the finite-capacity toy substrate *(Python sim + Lean structural cores, (b) toy / (c) real)*

- **I7 — HaPPY / random-tensor-network substrate** (Tier-2 §2.1): a finite holographic code; measure emergent
  two-point functions vs CFT, commutator decay (locality), boost-covariance violation vs refinement, coarse
  unitarity. Lean: `mincut_bounds_distinguishable_records` (finite). The QG roadmap's highest-leverage substrate.

---

## 3. Falsification gates (what negative result forces retreat)

A universal "finite capacity forbids approx Lorentz" theorem is **false** (critical chains/QCAs are
counterexamples), so kills are branch-specific:
- **A. one-loop `Δc²` naturalness (I4) — the best.** Nonzero `O(g²/16π²)` ⟹ naive finite-cutoff branch dead.
- **B. finite Poincaré trace no-go (I1).** Kills *exact* finite Poincaré (not approximate).
- **C. BW-recurrence (I2).** Forces finite modular results to finite-time/approximate.
- **D. tensor-network anisotropy.** Fixed bounded-degree graphs ⟹ crystalline/Finsler anisotropy; an `O(1)`
  lower bound kills those as continuum geometry unless Crofton-averaged.
- **E. Weinberg–Witten gate.** Any Tier-3 composite graviton must explicitly evade W–W (no massless spin-2 with a
  gauge-invariant local stress tensor) via diffeo redundancy / holography / nonlocality.

---

## 4. The frontier (category (c) — checkpoint, do not fake)

Tier-3 summit, open in **every** approach: a propagating spin-2 **graviton** with universal coupling; the
**constraint algebra / diffeomorphism invariance** as emergent symmetries; **nonlinear operator Einstein**; and
the **problem of time** — reformulating the selector `λ` and the Born measure `μ` as a measure over
diffeomorphism-classes of decoherent histories (where the foundational and gravity axes finally merge). These are
named, not scheduled.

---

## 5. Protocol & verification

Per Lean increment: `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = std-3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit with the
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; update the Progress log.
Per simulation: a reproducible `scripts/qg/` script + the measured error-scaling data + a short honest note.

---

## 6. Progress log

- **2026-06-30** — plan created.
- **2026-06-30 — I1 ✅ DONE** (`QIQTH/QG/FinitePoincareNoGo.lean`, gate B): `trace_commutator` (tr of a
  commutator = 0), `trace_eq_zero_of_boost_relation` ([K,P]=i·H ⟹ tr H=0), `no_exact_finite_boost` (+ H ⪰ 0 ⟹
  H=0, via `Matrix.PosSemidef.trace_eq_zero_iff`), and the contrapositive `no_boost_of_pos_ne_zero`. Axiom-free
  (std 3), full `QIQTH` build green (8876 jobs), budget 0; wired into `QIQTH.lean` + `AxiomAudit.lean`. Finite
  capacity carries boosts only approximately — the finite modular/spectral claims are finite-time/low-energy.
- **2026-06-30 — I2 ✅ DONE** (`QIQTH/QG/FiniteModularRecurrence.lean`, gate C): `modHam_spectrum_finite` /
  `modHam_real_spectrum_finite` (a finite modular Hamiltonian `K=log Δ` has finite spectrum, via
  `Matrix.finite_real_spectrum`), `exists_energy_outside_finite_spectrum` (it MISSES real energies — `ℝ` is
  infinite), `finite_modular_spectrum_ne_real_line` (`spectrum ℝ K ≠ ℝ`). The continuum BW generator (the boost)
  has spectrum all of `ℝ` (a.c., mixing) ⟹ no finite modular flow equals it; finite modular flow is
  almost-periodic/recurrent — a finite-time/low-energy shadow. Axiom-free (std 3), full `QIQTH` green, budget 0;
  wired into `QIQTH.lean` + `AxiomAudit.lean`.
- **NEXT → Phase B (the de-risking centerpiece):** I3 (free-dispersion Lorentz-defect bound, Lean), then **I4**
  (the decisive one-loop Δc² naturalness test, Python).
