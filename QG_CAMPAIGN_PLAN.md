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
- **2026-06-30 — I3 ✅ DONE** (`QIQTH/QG/LatticeDispersion.lean`, Phase B cheap pass): for the lattice/QCA
  dispersion `E_a(p)²=m²+(4/a²)sin²(ap/2)`, `latticeDispSq_le_contDispSq` (`E_a(p)² ≤ m²+p²` everywhere) and
  `latticeDisp_lorentz_defect` (`|E_a(p)²−(m²+p²)| ≤ a²p⁴/8` in the sub-cutoff regime `a·p ≤ 2`), via the core
  `abs_sin_sq_sub_sq_le` (`|sin²x−x²|≤x⁴/2` on `[0,1]`, from `sin_sq_le_sq` + `sin_gt_sub_cube`). Defect ~(ap)²,
  vanishes as a→0 — **NO rapidity-independent floor (α=2)**. Constant 1/8 = honest Mathlib value (optimal 1/12).
  Axiom-free (std 3), full `QIQTH` green, budget 0; wired in. The cheap/known pass — NOT yet decisive.
- **2026-06-30 — I4 ✅ DONE — THE DECISIVE TEST, result = FAIL (CPSUV)** (`scripts/qg/cpsuv_speed_splitting.py`,
  `scripts/qg/I4_cpsuv_result.md`). One-loop Yukawa speed splitting under a preferred-frame hard spatial cutoff:
  **Δc² → (4/3)·g²/16π² ≠ 0**, an UNSUPPRESSED O(g²/16π²) plateau (not power- or log-suppressed). Closed form
  `Δc²=(g²/12π²)(2u⁵−u³)`; numerics reproduce it to 6e-16, sympy verifies the antiderivative, and the O(4)
  Lorentz-invariant regulator gives 0 (root cause = regulator frame-dependence, computed not assumed). **A naive
  finite-capacity-as-LV-hard-cutoff is DEAD** — ordinary interactions radiatively generate experimentally-excluded
  dim-4 Lorentz violation. Finite capacity survives ONLY with a protection mechanism (exact symmetry / SUSY-like
  cancellation / deformed-statistical Lorentz invariance / nonlocal-holographic substrate). This sharpens Tier-2
  §2.5 into a HARD criterion: any substrate (I7) must show Δc²(Λ)→0 parametrically, not merely small at tree level.
- **2026-06-30 — I5 ✅ DONE** (`QIQTH/QG/FiniteTracePhase5.lean`, Phase C / T1): a **non-vacuous `Phase5Master`
  instance from a finite trace** — `phase5_of_finite_trace` discharges the certificate (to which P4's floor was
  reduced) in a concrete finite density-matrix model: `ξ=0` (`cgpEntropy_zero`), `areaTerm=log|n|` the DERIVED
  capacity, `remainder=log|n|−S_vN` the genuine entropy deficit proved ≥0 by `vonNeumannEntropy_le_log_card`
  (Jensen) — NOT `Phase5Master.of_le` on an assumed inequality. `finiteTrace_area_floor`: P4's floor obtained
  THROUGH the interface. Type I/II₁ shadow (continuum Type II_∞ dual-weight trace = the §4 / scope-doc frontier);
  1/4 & G never asserted. Axiom-free (std 3), full `QIQTH` green, budget 0; wired in.
- **2026-06-30 — I6 ✅ DONE** (`QIQTH/QG/ExactRT.lean`, Phase C / Tier-3 §3.2): exact finite RT via the
  **optimality certificate** — `exact_rt_of_saturating`: a saturating witness (`flowValue f s = cutCapacity
  cap C`) certifies `max-flow = min-cut` (`f` maximizes flow, `C` minimizes cut, both from Track C
  `flow_weak_duality`); `saturating_flow_isMax`, `saturated_cut_isMin`, and `minCut_attained` (the min-cut is
  achieved — finitely many cuts). Reduces exact RT to producing a saturating witness; the witness existence
  (Ford–Fulkerson / Menger) is the cited Mathlib-gap frontier (no max-flow theorem in Mathlib), honestly
  checkpointed. Axiom-free (std 3), full `QIQTH` green, budget 0; wired in.
- **2026-06-30 — I7 ✅ DONE** (`QIQTH/QG/MinCutRecords.lean` + `scripts/qg/rtn_rt_substrate.py` +
  `I7_rtn_result.md`, Phase D / Tier-2 §2.1–§2.2): the finite-capacity toy substrate. **Lean:**
  `mincut_bounds_distinguishable_records` (`log #records ≤ cut`, the area-not-volume capacity law) +
  `record_count_le_exp_cut`. **Sim:** a random tensor network on a ring — `S(A)/(min-cut·log D)` rises
  monotonically toward 1 FROM BELOW (0.50→0.98 m=1, 0.42→0.87 m=2 over D=2→12), never exceeding 1, i.e.
  saturating the RT bound `S ≤ min-cut·log D` (= the Lean theorem). RT / capacity-is-area holds **kinematically**.
  **Honest checkpoint:** a static RTN has NO Lorentzian dynamics, so the I4 Δc² mandate is NOT testable here —
  it requires a LORENTZIAN QCA substrate (the next frontier); the RTN's RT success must not be read as passing
  I4. Axiom-free (std 3), full `QIQTH` green, budget 0; wired in.

---

## CAMPAIGN COMPLETE (planned increments I1–I7, 2026-06-30)

All seven planned increments landed axiom-free (std-3, budget 0) / verified-reproducible. Honest summary:
- **I1–I2** (no-gos): finite capacity carries boosts only approximately (gate B) and finite modular flow has
  discrete spectrum ≠ continuum BW (gate C) — the finite claims are honestly fenced.
- **I3** (cheap pass): the free lattice dispersion's Lorentz defect is `O(a²p⁴)`, no rapidity floor (α=2).
- **I4 (THE DECISIVE TEST) = FAIL (CPSUV):** one-loop Δc² → (4/3)·g²/16π² ≠ 0 — a naive finite-capacity-as-LV-
  hard-cutoff is dead; finite capacity survives only with a protection mechanism. The pivotal result.
- **I5** (P4 thread): a non-vacuous `Phase5Master` instance from a finite trace — P4's floor grounded in a model.
- **I6** (RT): exact RT from an optimality certificate (Ford–Fulkerson the cited gap).
- **I7** (substrate): RTN exhibits RT/capacity-area kinematically; the dynamical Lorentz mandate is the frontier.

**Net verdict (unchanged, now evidenced):** QIQT-H is NOT quantum gravity. The campaign de-risked the finiteness
bet and found the real obstruction is **dynamical Lorentz naturalness** (I4), not the kinematics (I3/I6/I7 fine).
The single highest-leverage open frontier: a **Lorentzian finite-capacity substrate that demonstrably shows
`Δc²(Λ) → 0`** — without it, P4 cannot be realized as a local cutoff. Tier-3 (graviton, constraints, nonlinear
Einstein, diff-invariant μ) remains category (c), untouched. Never claimed QG / G / the 1/4.
