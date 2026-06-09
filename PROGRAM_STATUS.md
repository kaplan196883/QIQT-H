# QIQT-H — Program Status: where we are, and what the breakthrough would be

*Living status document. Last updated 2026-06-08 (operator-algebra infrastructure
note in §2a: bounded spectral theorem + continuum modular flow + RvD standard-subspace
objects now built & axiom-free, program at the Mathlib frontier). Prior substantive
revision 2026-06-06, after a multi-round GPT-5.5-pro
adversarial soundness review that produced a **strategic pivot** (§2a), a new
axiom-free **capacity-exclusion core** (§3c), and a new axiom-free **finite no-collapse
Born representation** joining the capacity core to the Born/typicality layer (§3d; full
scope map in `FINITE_BORN_REPRESENTATION.md`). This is the honest map: what is done,
what is the prize we are chasing, and what must be fixed before arXiv.*

> **Update 2026-06-06.** The project axiom budget is now **33** (all 33 are continuum /
> operator-algebra interface axioms; the entire finite core below is axiom-free —
> `propext, Classical.choice, Quot.sound` only). 37 → 35 via the Goldstein–Struyve Step-1 /
> Step-3 discharges; 35 → 33 by DELETING the two content-free placeholder axioms
> (`LLN_typicality_axiom`, `mackey_gleason_to_trace_density`), both superseded by axiom-free
> finite results. References to "37"/"35" elsewhere in this document predate these and read 33.
>
> **Update 2026-06-08 (the continuum Fock/CCR field foundation — built from scratch).** Mathlib
> has *zero* Fock-space / CCR theory; this session machine-checked, axiom-free (budget still 33),
> the entire operator/state apparatus of the continuum 1+1D bosonic free field (`QIQTH/Fock/*`,
> master write-up `WRITEUP.md` §6½, plan `FOCK_CCR_FOUNDATION_PLAN.md`):
> one-particle L²(ℝ) + the **Lorentz boost** as a one-parameter unitary group (rapidity);
> the **symmetric Fock space** via the positive-definite-kernel keystone `exp⟪f,g⟫`
> (Gram-PSD + Schur product theorem), with coherent vectors `e(f)`, vacuum `Ω`, `⟪e(f),e(g)⟫=exp⟪f,g⟫`;
> **second quantization** Γ and the boost as a **Hilbert-space isometry fixing the vacuum**
> (`boostFockH_vacuum`); the **quasifree vacuum state** `ω₀` (the `ω` `EffectStateNet` consumes);
> the **bounded Weyl operators** `W(u)` with their isometry/CCR-unitarity (`fockInner_weyl`); the
> **Lorentz-invariance of the vacuum state** (`weylCoeff_vacuum_boost_invariant`); the first
> **non-vacuous boost-covariance** — the vacuum two-point function `⟪Ω,W(u)W(v)Ω⟫` is boost-invariant
> (`weyl2pt_boost_invariant`); and **microcausality** — spacelike (symplectically orthogonal) Weyl
> observables COMMUTE (`weyl_microcausality`).  A GPT-5.5-pro review put the *literal* prize at ~20%
> and named the bounded Weyl operator as the keystone; that keystone and all three of its recommended
> increments (Weyl op, non-vacuous covariance, microcausality) are now done.  **The localization gap is
> now CLOSED (2026-06-10).** The concrete 1+1D mass-shell localization map `K : TestFun → L²(ℝ)` is
> built with: **(i)** Pauli–Jordan microcausality `Im⟪Kf,Kg⟫=0` for spacelike-separated supports
> (`K_im_inner_eq_zero_smooth`, via the oscillatory IBP keystone — non-vacuous witness); **(ii)** full
> connected-Poincaré equivariance `K(τ_b β_a f)=U(a,b)Kf` with `(a,b)↦U(a,b)=M_b∘U₁(a)` a genuine unitary
> **representation** of `ℝ^{1,1}⋊SO⁺(1,1)` (`poincareIsometry_comp`); **(iii)** non-triviality
> (`K_gaussian_ne_zero`).  Hence the σ-additive `μ∞` is invariant under the WHOLE connected Poincaré group
> (`localized_typicality_poincare_invariant`), and the bounded-operator/POVM bundling on the completed
> Hilbert space (`weylCLM`, `jointEffectCLM_complete`) is done.  Per GPT-5.5-pro the scoped mathematical
> prize is now closed (~98–99%); the residual is honest *scope* wording (free/quasi-free vacuum sector,
> connected proper-orthochronous group, 1+1D, no Type III₁ net) — no unformalized analytic input, no
> `sorry`.  See `ARXIV_NOTE_WeylBit.md` and `SCOPE_STATEMENT.md`.

---

## 1. One-paragraph honest verdict

QIQT-H is **not (yet) a breakthrough solution to the measurement problem.** In
its honest current form it is:

> exactly-unitary global wavefunction Φ  +  a primitive **actuality selector λ**
> (which macroscopic realization is the actual one)  +  an **unconstructed
> typicality measure μ** (meant to deliver Born)  +  a **holographic
> finite-record bound** Q_R = A(∂R)/4ℓ_P².

That is a **legitimate, publishable research-program architecture**. What is
*missing* is the one object that would make it a genuine breakthrough: a
**canonical, Lorentz-covariant construction of μ / λ-selection** that yields the
Born rule and operational no-signaling *without fiat*. Until μ is constructed,
this is an interpretation/architecture, not a derivation.

---

## 2. THE BREAKTHROUGH WE ARE LOOKING FOR (the prize)

**A canonical, Lorentz-covariant law assigning to each unitary global Φ a measure
μ over actuality selectors (λ / history valuations) such that:**

1. Born weights are recovered for **all** decoherent record partitions;
2. independent experiments **tensor-factorize** correctly;
3. **LLN / frequency** behaviour follows (typical λ-histories show Born frequencies);
4. **operational no-signaling** holds after μ-averaging;
5. **free settings / measurement independence** are preserved (no superdeterminism);
6. the construction is **covariant** — no hidden foliation;
7. μ is **derived** (from finite-record covariance + noncontextuality + tensor
   multiplicativity + locality), **not** "choose the Born measure by hand."

If (1)–(7) are achieved, QIQT-H becomes a genuine breakthrough. **Caveat (honest):**
this may be a restatement of the measurement problem itself — every single-world
program (Everett, Bohm, modal, Kent) owes essentially this same object. So the
prize is real, hard, and shared; sharply *stating* it is itself a contribution.

**Attack plan: see `PRIZE_ROADMAP.md`** (GPT-5.5-pro "be bold" consultation, 2026-06).
The committed route is **Effect-Gleason + Kolmogorov** (NOT the raw decoherence
functional): finite records ⇒ POVM effects ⇒ Busch/Bunce–Wright Mackey-Gleason
uniqueness ⇒ Born ⇒ projective cylinders ⇒ unique covariant μ. The make-or-break
sub-claim is the **Covariant Record-Completeness Lemma** (records functorially = effects,
rich enough for Gleason); the uniqueness spine is Busch-Gleason + record-certainty (which
kills the maximally-mixed alternative) + Kolmogorov. Staged: **Stage 1 (finite-dim) is the
minimal breakthrough** and is mostly done — `GleasonSelector.positive_ray_certain_forces_
born` is the single-state core; the new gaps (tensor multiplicativity + decoherent
partition additivity) are being built in `RecordGleason.lean`.

**The single sharpening that would most raise the contribution short of the full
prize — the "Record Quotient Theorem":**
> For every internal observer in a finite causal region R at distinguishability
> scale ε, every reportable proposition factors through a *finite Boolean record
> algebra* B_{R,ε} whose atoms are einselected, redundantly encoded,
> ε-distinguishable records, with |At(B_{R,ε})| ≤ e^{Q_R}; actual reports are
> valuations selected by λ.

This is what makes "we measure in 0/1 because we are macroscopic" precise: not
"the world is binary," but "internal macroscopic reports are finite-valued
elements of a finite record quotient." Proving this is the most tractable real
contribution on the path.

---

## 2a. STRATEGIC PIVOT (2026-06) — what is actually load-bearing

A multi-round GPT-5.5-pro soundness review settled a question that had been
quietly distorting the priorities: **the Tomita–Takesaki / Type-III tower is
infrastructure, not the load-bearing part of "finite Q_max removes the need for
the collapse postulate."** Type III does not imply finite capacity, and modular
flow is reversible — neither delivers the single-outcome content. The spectral /
crossed-product machinery is a correct and reusable mathematical home, but
it is *not* where the breakthrough claim is discharged.

> **Infrastructure progress note (2026-06-08).** That said, the infrastructure is now
> substantially built and axiom-free: the **bounded spectral theorem** (`PVM_of_selfAdjoint`,
> `T=∫λ dE`), the **bounded Borel functional calculus** (`borelFC`), the **continuum modular
> flow** `Δ^{it}` as a strongly-continuous unitary group with its modular automorphism `*`-group
> `σ_t`, state-invariance, and the **complex-time/entire-analytic flow** are complete in
> `QIQTH/Spectral/SpectralTheorem.lean`; the **Rieffel–Van Daele standard-subspace** modular
> objects are complete up to the analytic square root in `QIQTH/StandardSubspaceModular.lean`
> (`0≤R≤2`, `R` ℂ-linear/positive `Rℂ`, `D=P−Q` conjugate-linear ⇒ `J` antiunitary). The program
> has reached the operator-algebra **infrastructure frontier of Mathlib v4.30**; the three live
> walls (operator square root / `StarOrderedRing (B(H))`, unbounded antilinear Tomita `S`, genuine
> KMS) are detailed in `TOMITA_TAKESAKI_ROADMAP.md` §"CURRENT STATUS". All axiom-free; budget 33.

> **Update 2026-06-08 — the continuum covariant typicality measure μ is now machine-checked.** The
> "XL step" (`XL_STEP_PLAN.md`) is complete: a σ-additive, unique, Born-marginal, covariant,
> no-signaling measure μ∞ over histories/λ for the **correlated/entangled** case (`FiniteMarginals` +
> finite-fiber Kolmogorov extension `KolmogorovFiniteFiber.exists_isLimit`), shown **state-agnostic** —
> μ∞ exists for ANY normal state on a compatible net (`StateNetMeasure.EffectStateNet`, with a
> non-vacuity witness). Axiom-free, budget 33, Fine/Bell contextuality enforced. The sole remaining
> gap is the *physical* input (a normal state on a **Type III₁** QFT net), now itself **planned** in
> `PHASE_B_INFRASTRUCTURE_PLAN.md` — Part A (predual/normal states of `B(H)`: bounded, Mathlib-grade,
> the only piece μ needs) + Part B (Type III₁ / Buchholz–Wichmann: research-grade, not needed for μ).
> This does not change §1's verdict: the continuum is now *constructed* given a normal state, with the
> QFT-state existence the honest cited/planned frontier.

The load-bearing content is, instead, the chain **finite-capacity exclusion →
actuality selector λ → Born/typicality → collapse-as-conditionalization**, plus a
concrete *mechanism* that makes the capacity threshold non-circular. That chain is
now machine-checked, axiom-free, in three new files (§3c). The pivot is recorded so
the program does not again sink effort into Type-III analysis as if it were the
prize; it is a tool, available when the continuum realization (Open Problem 3b) is
attacked, not the source of the single-world result.

---

## 3. WHERE WE ARE — what is genuinely done / novel (publishable)

- **Division-of-labor clarity** (cleaner than most "decoherence solves outcomes"
  arguments): decoherence conserves weights · einselection ⇒ robust Boolean
  records · holography ⇒ finitely many distinguishable records · λ ⇒ which is
  actual · μ ⇒ Born frequencies.
- **Lean formalization + assumption audit** (*the strongest original component*):
  no-signaling, CHSH→Tsirelson 2√2 with rigorous singlet, microcausality,
  Donald's identity, `NoConcentration` (decoherence conserves |c_k|²),
  support-preservation ≠ Born-equivariance, structural audits. **33 project
  axioms** (down from 57; all continuum/operator-algebra interface). Publishable
  **as a formal dependency analysis**, NOT
  as a completed Born derivation. Recent discharges (all machine-checked,
  standard Lean axioms only):
  - **Gleason/Born:** `GleasonSelector` is now **axiom-free** — Born is *derived
    from positivity* + normalization + ray-certainty (`positive_ray_certain_
    forces_born`); the earlier FALSE Gleason axiom was retired with a
    counterexample, and both residual linear-algebra axioms discharged.
  - **Lorentz (OP3b) finite interface:** `LorentzSelection`(+`Strong`) is
    **axiom-free** — the four opaque AQFT axioms retired for an explicit
    `RecordedHistoryNet`; measure covariance **derived from unitarity**
    (`ubornω_covariant`, no longer assumed); a genuine **group action on Γ(X)**
    proved (`actSection_mul`); PVM positivity + completeness preserved under
    transport; and **non-trivial models built** (`LorentzWitness` A/B) refuting
    vacuity. Continuum Type III₁ realization remains open.
  - **Infra (OP6/OP9):** the finite-classical axioms `KL_classical_nonneg`
    (Gibbs), `H_bound_imp_max_lb` (Rényi-∞ ≤ Shannon, the Fano step), and
    `H_zero_imp_dirac` are now **proved**; `ShannonFano` is axiom-free.
- **Finite distinguishable-record quotient** M_ε(R) ≤ e^{Q_R} — potentially
  interesting if made precise (→ Record Quotient Theorem above).

## 3b. What holography's REAL (narrow) job is

Q_R does **non-redundant** work *only* as: "for a finite causal region at scale
ε, the empirically accessible record algebra is a finite Boolean quotient with
≤ e^{Q_R} atoms." It does **NOT**: select an outcome · forbid the cat state
α|0⟩^N+β|1⟩^N · derive Born · produce collapse · create exact superselection.
Sell it as the former (defensible); never as the latter (fails).

## 3c. THE CAPACITY-EXCLUSION CORE — new axiom-free mechanism (2026-06)

The pivot (§2a) was accompanied by *building* the load-bearing chain as a
machine-checked, axiom-free conditional theorem. Three new modules (standard Lean
axioms only — `propext`, `Classical.choice`, `Quot.sound`; in the project budget
of 33; verified by `AxiomAudit.lean`):

- **`QIQTH/CoreNoCollapse.lean`** — the conditional representation theorem.
  Finite-capacity exclusion (`coactual_subsingleton`: a region whose record cost
  exceeds half its capacity can hold at most one active record) **plus** the
  actuality selector λ (`Selection`) ⇒ **exactly one** actual record
  (`exactly_one_actual`, `qiqth_single_outcome_no_collapse`). A *genuine* PVM
  (`FinPVM`: self-adjoint, idempotent, orthogonal, complete) with Born
  normalization (`weight_sum_eq_one`: ∑‖Eψ‖²=1) and collapse-as-conditionalization
  (`condProb_eq_born_postState`, `joint_eq_weight_mul_cond`: sequential Born =
  weight × conditional, so "collapse" is recovered as Bayesian updating, not a
  dynamical event).
- **`QIQTH/CapacityModel.lean`** — *derives* the capacity bound from orthonormality:
  records as an orthonormal pointer family in a finite register force ∑ⱼ recDim ≤ D
  (`capacity_total`), so at most one record can occupy > D/2 (`macroscopic_subsingleton`,
  `capacity_exactly_one`). The saturation premise of `CoreNoCollapse` is here a
  *theorem*, not a stipulation.
- **`QIQTH/SBSBridge.lean`** (Tier B) — the bridge that makes the threshold a
  *physical* fact rather than a ">half the register" fiat. An **objective record**
  (Zurek/Korbicz Spectrum Broadcast Structure) of an n-outcome pointer broadcast to
  R environment fragments forces a broadcast support of Hilbert dimension ≥ nᴿ
  (tensor product — dims multiply: `broadcast_finrank_ge`), i.e. **information cost
  ≥ R·log n** (`redundancy_le_logStorage`). With finite information capacity Q_max,
  "macroscopic = large redundancy R" ⇒ cost > Q_max/2 ⇒ at most one
  (`sbs_single_outcome`). The chain is robust to *approximate* decoherence (a
  near-orthonormal family with pairwise overlap < 1/(n−1) is still linearly
  independent ⇒ dim ≥ n: `fragment_finrank_ge_approx`) and includes the
  amplification fact that weak per-collision monitoring compounds to reliable
  records (block overlap ≤ γ^L → 0 for γ<1: `block_overlap_tendsto_zero`).

**Machine-checked ladder (all axiom-free):** distinguishability ⇒ dim ≥ n;
*approximate* distinguishability ⇒ dim ≥ n; R fragments ⇒ storage ≥ R·log n; **toy
Hamiltonian `H_int = g σ_z⊗σ_x` ⇒ per-collision overlap `cos 2θ`, so `γ<1` derived**;
weak overlap γ<1 ⇒ block overlap → 0 (amplification); objectivity witness ⇒ macroscopic
storage; finite additive capacity ⇒ ≤ 1 objective record active (small records
coexist — the bound is honest, not a by-fiat "exactly one for everything"); Born
normalization + collapse-as-conditionalization.

**Honest standing (GPT-5.5-pro, seven review passes).** Unified rank **(b+)** with
an **(a)-grade mechanized mathematical core**. The mechanized-theorem fraction of
the central claim rose from ~25% to **~50% mechanized theorem / ~45% explicit
physical-modeling premise / ~5% residual (mostly wording risk)**. Referee judgment
for a Lean-formalization-of-physics paper: **accept / weak-accept** *with conditional
framing*; **major revision** if it claims an unconditional solution of the
measurement problem.

**The single isolated physical input — now DISCHARGED for a toy Hamiltonian (2026-06).**
The premise was: derive a *stable, factorized, branch-dependent scattering model with
uniform per-collision distinguishability γ<1 from a concrete Hamiltonian.* This is now a
machine-checked, axiom-free theorem for the standard Zurek collisional/QND monitor
`H_int = g·σ_z^S ⊗ σ_x^E` (`QIQTH/CollisionalGamma.lean`): the branch-conditioned
environment records overlap by `⟨E_+|E_-⟩ = cos 2θ` (`branch_overlap`), so the
per-collision distinguishability `γ = |cos 2θ| < 1` for generic coupling
(`gamma_lt_one`) — *derived*, not assumed; the propagator `U_s(θ) = exp(-iθ s A)` is a
verified one-parameter unitary group (`collisionU_group`) with self-adjoint generator
(`hamiltonian_isSymmetric`); and over `L` independent collisions the overlap factorizes
to `γ^L → 0` (`collisional_overlap_tendsto_zero`), feeding the existing
`overlap_amplifies` chain. A concrete `σ_x`-on-ℂ² witness refutes vacuity
(`sigmaX_branch_overlap`). Everything downstream of the premise
(amplification → redundancy → storage bound → single-record exclusion) was already
machine-checked, so the toy-model chain is now end-to-end mechanized.
**Residual (genuinely open):** the *field-theoretic* version — deriving uniform `γ<1`
(and the QND/factorized, no-recoherence structure itself) from a realistic
system–environment Hamiltonian rather than positing the collisional form. The remaining
modeling choices (finite Q_max, additive capacity for disjoint substrates, tensor
factorization, no-recoherence, reading low-overlap branch states as records) are
transparent, not hidden. Full SBS with mixed fragment
states + von-Neumann-entropy cost, the SBS uniqueness theorem, and the
non-commuting-basis (objectivity einselects the basis) result are deferred
multi-session research — and constitute a *constructive* answer to the
Strasberg–Winter "branch selection problem" (arXiv:2601.19703).

**Guardrail (do not violate in any abstract or claim).** Do **not** write "We prove
in Lean that finite Q_max alone eliminates the collapse postulate and solves the
measurement problem." The defensible statement is: *a conditional capacity theorem —
under finite additive storage and a scattering model with uniform per-collision
distinguishability, repeated interactions amplify small overlaps into redundant
record states requiring macroscopic storage, while deriving the scattering premise
from a Hamiltonian remains open.*

Design notes, the block→reference map, and the closing assessment are in
`CORE_THEOREM_REFS.md`; arXiv TeX sources in `refs/arxiv_sources/` (git-ignored).

---

## 3d. THE FINITE NO-COLLAPSE BORN REPRESENTATION — capacity core joined to Born (2026-06)

The capacity-exclusion core (§3c) delivers *unique outcomes*; the Gleason/typicality work
delivers *Born statistics*; they were proved in separate towers. This session **joined them**
into a single finite, axiom-free representation theorem and then reduced its assumptions as far
as is honestly possible. Full claim→theorem map and the GPT-5.5-pro-verified scope caveats are
in **`FINITE_BORN_REPRESENTATION.md`**; the one-paragraph version:

> A finite information-capacity bound forces a **unique actual pointer value** per run, with no
> collapse map (`CoreNoCollapse` → `PointerValue.existsUnique_actualValue`); a **non-contextual**
> outcome assignment is **forced** to be the Born weight `tr(ρ Pₐ)` of a density matrix by finite
> effect-Gleason (`OneSiteGleason.oneSite_forced`; converse `traceEffectMeasure`); **product
> preparation** yields independent trials (`BornTypicalityFinite.w_history_factorizes`); and the
> actual-value histories then carry the **Born product law** and are **Chebyshev-typical**
> (`BornJoin.finite_noCollapseBornRepresentation`, `BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality`).
> The world-measure carries **no observable freedom** (`history_law_unique`). Born statistics are
> **not assumed** — only non-contextuality and product preparation are.

**Two GPT-5.5-pro verification passes (folded in, honest):** the join is *formally sound,
non-vacuous, axiom-free*, but it is a **conditional representation theorem, not a derivation of
Born from capacity.** Genuinely reduced: the single-trial Born **weights** are now a real
effect-Gleason consequence of non-contextuality (not a bare assumption), and the **factorization**
follows from product preparation. Honestly **not** removed: non-contextuality and product
preparation are genuine (motivated, strong) inputs; the `ActualEnsemble` interface still names
`oneSite`/`indep`; the trace-path theorem is an interface (circular as a standalone derivation);
the no-collapse value-uniqueness is, relative to the probability layer, a wrapper. All docstrings
carry these caveats. **Guardrail:** never write "Born derived from `Q_max`/from nothing"; the
defensible headline is *"Born weights + factorization derived from non-contextuality + product
preparation; world-measure shown observationally free; finite, axiom-free, machine-checked."*

New axiom-free modules: `BornTypicalityFinite`, `BornTypicalityQuantum`, `BornMeasureUniqueness`,
`ValueSelection`, `OneSiteBorn`, `OneSiteGleason`, `BornJoin`, `BornJoinGleason`,
`OrthogonalCapacity` (all standard-three; budget 33).

**Prize finite stages (1–3) also done (2026-06-06), all axiom-free:** the covariant
recorded-history architecture — `FreeFieldNet` (non-toy net + product-Born no-signaling theorem),
`DiamondSwapNet` (genuine diamond-permuting covariant action; the unified net `diamondBornNet`),
`QubitIC` (informationally-complete record POVM — finite Covariant Record-Completeness),
`SheafSection` (global selectors exist + classified, gluing unobstructed), `SpectralPVM` (finite
spectral theorem as a PVM), and `FiniteModularTheory.modAut_stateOf_invariant` (finite Tomita
state-invariance).  The continuum (Type III₁ / bounded spectral theorem / Tomita–Takesaki / Bunce–
Wright) is the open infrastructure problem (`PRIZE_EXECUTION_PLAN.md` Stage 3).  **The complete
finite result is consolidated, paper-ready, in `FINITE_RESULT.md`** (full claim→theorem map, honest
derived/assumed ledger, suggested paper structure and abstract).

---

## 4. GAP RANKING (severity for publishability)

Status legend: ✅ DONE (committed) · ◻ OPEN (research agenda).

| # | Gap | Severity | Status / Fix |
|---|-----|----------|-----|
| 1 | **Bell: PI-vs-measurement-dependence contradiction** | was **FATAL** | ✅ DONE — committed to PI-violation horn; §6.9/Position/Tutorial rewritten; Palmer reframed as opposite horn |
| 2 | **Unconstructed μ + no-signaling/fine-tuning** | Fatal to *breakthrough*; OK as flagged open problem | ◻ OPEN — = the prize (§2); Open Problem 1 |
| 3 | **Lorentz covariance of A_R[Φ,λ]** | Fatal to *"relativistic completion"* claims; OK as open problem | ◧ PARTIAL — the **finite conditional interface is fully discharged & axiom-free** (`LorentzSelection`+`Strong`: covariance derived from unitarity, a real group action on Γ(X), full-PVM preservation) and **non-trivially instantiated** (`LorentzWitness` A/B); the **continuum Type III₁ realization is OPEN** (Open Problem 3b, §4a + paper §11.4) |
| 4 | **λ = "microscopic initial conditions"** | was MUST-FIX | ✅ DONE — relabeled "atemporal global actuality selector" across 4 papers + Lean docstrings + memory |
| 5 | **Born interface axioms in Lean** | Non-fatal *if transparent* | ✅ adequate — AxiomAudit.lean enumerates; abstract states it is conditional |
| 6 | **MDC strong form** | Non-fatal; already demoted | ✅ DONE — strong "forbids superposition" form disavowed (cat-state) in §7.6 + README; the **number-bound (≤ 1 record) form is now a conditional axiom-free theorem** in the finite SBS / capacity model (§3c, `SBSBridge.sbs_single_outcome`), conditional on the scattering premise |

**As of HEAD (2026-06): the one load-bearing inconsistency (#1) is resolved and the must-fix calibration set is committed. #3 (Lorentz) has had its entire *finite conditional interface* discharged, made axiom-free, and instantiated by non-trivial models; #2 (μ) has its finite Gleason core (Born from positivity) discharged axiom-free; and the single-outcome *mechanism* (#6, number-bound) is now a machine-checked conditional theorem via the capacity-exclusion core (§3c). What remains for #2 and #3 is the same *continuum* operator-algebra wall (Type III₁ / Tomita–Takesaki, beyond current Mathlib), and for the §3c core the one isolated physical input (Hamiltonian origin of the γ<1 scattering premise) — the genuine research agenda, honest open problems, not contradictions.**

---

## 4a. OPEN PROBLEM 3b — Lorentz covariance of the selection structure (detail)

Equal in rank to the Born/μ problem; the relativistic counterpart of it. **Not** secured by operational no-signaling (no-signaling ≠ Lorentz invariance of the beable). QIQT-H is structurally *better placed* than Bohm — Φ's dynamics is exactly-unitary and already covariant, and λ is non-dynamical (no collapse/guidance event to time-order, so nothing needs a "now") — but that is "better placed," not "proved." Five requirements, increasing difficulty:

1. **λ as a genuinely 4D object** — defined geometrically over the whole spacetime history (a globally consistent decoherent history / bundle section), Poincaré acting geometrically, NO Cauchy slice. "Initial data on Σ₀" reintroduces a preferred frame and fails. (Definitional; discipline.)
2. **Covariant region structure** — $Q_R$, ε(R) on **causal diamonds** via the **Bousso light-sheet** bound, not spatial slices (slice-area is frame-dependent). CPW/Witten scaffolding is already diamond-based + microcausal, so scaffolding is covariant; burden is λ and $A_R$. *Concrete, fixable now — do first.*
3. **The covariance identity (core theorem)** — prove $A_{gR}[U_g\Phi,\, g\!\cdot\!\lambda] = g\cdot A_R[\Phi,\lambda]$ for every Poincaré $g$ ("every frame agrees on the facts"). OPEN.
4. **Foliation-free global consistency** — the family $\{C_R\}$ restriction-compatible on nested diamonds and jointly consistent on spacelike diamonds, with the consistency condition statable in the **causal partial order alone** (no global time function). Operational no-signaling is its observable shadow; the ontic statement must be proved. OPEN.
5. **Poincaré-*equivariant* typicality** — μ over λ must satisfy $g_*\mu_\Phi = \mu_{U_g\Phi}$ (equivariance, NOT strict invariance $\mu(g\cdot S)=\mu(S)$ — too strong, since Born depends on Φ; invariance is the special case of Poincaré-invariant Φ). **Couples to Open Problem 1**: an equivariant μ_Φ is strictly harder than a single-frame μ; relativistic analogue of Bohm's $|\psi|^2$-equilibrium frame-dependence. HARDEST. OPEN.

Honest riders: 3–5 are genuine open theorems; the Lorentz-friendliness is *bought with* an atemporal / all-at-once (block, mildly retrocausal-flavored) reading of λ (owned, not hidden); this places QIQT-H in the Kent / Wharton–Sutherland family rather than the foliation-bound Bohm/GRW family — a structural advantage that is, as yet, a promissory note.

**Proposed construction (intended line of attack; paper §11.4):**
- **Dirac, not Schrödinger.** Φ is a relativistic quantum field (Dirac field for matter), with a genuine Poincaré action U_g via the spinor rep S(Λ). Required, not cosmetic: req-3's identity A_{gR}[U_gΦ,g·λ]=g·A_R is only statable with a covariant U_g, which Galilean Schrödinger lacks. Also: the Dirac field is the natural matter content of the CPW/Witten AQFT algebras — this just names the QFT the scaffolding already presupposes. (Carrier is the field, not the one-particle Dirac eq, which has Klein/negative-energy pathologies.)
- **λ = holographic boundary data on causal-diamond screens.** C_D = A_D[Φ,λ] reconstructed from λ|_{∂D}. Forcing motivation: the capacity Q_R = A(∂R)/4ℓ_P² is itself a boundary quantity, so the fact that spends it should live on the boundary. Discharges three requirements at once: (1) ∂D is a covariant slice-free object (boundary data ≠ Cauchy data); (2) Q_R and λ share the screen; (4) boundary data on nested/overlapping diamonds glues by edge-agreement → order-theoretic gluing, no global time.
- **Honest status:** "boundary data fixes the bulk record" = holographic bulk reconstruction (HKLL / entanglement-wedge), subtle and non-literal even in AdS/CFT, open for general causal diamonds. So the proposal *relocates* req 3–4 to the sharper theorem "does holographic screen data on a causal diamond uniquely + covariantly fix the λ-selected bulk record?" — not yet solved, but λ now has a concrete covariant home and Φ a covariant U_g.

**GPT-5.5-pro sharpening (paper §11.4 has the full version):**
- **Correction A — gluing is over BULK OVERLAPS, not screen intersections.** For K⊂D, ∂K ⊄ ∂D, so "edge agreement" is too weak. Correct condition: ρ_{D,L}(C_D)=ρ_{E,L}(C_E) ∀ L⊂D∩E. Formally: X_Φ(D)=Stone(B_Φ(D)) a presheaf on the causal-diamond poset; λ = a GLOBAL SECTION λ∈Γ(X_Φ)=lim X_Φ(D). Req 4 = "a global section exists."
- **Correction B — obstruction is ROBERTS NET COHOMOLOGY, not plain topology.** Gluing cocycle [g_{ij}]∈Ȟ¹(Aut(X_Φ)) (→H² gerbe if projective); same machinery that classifies DHR superselection sectors. Split property + Haag duality HELP (finite pointer algebras, causal complements) but do NOT trivialize it — the split inclusion is non-canonical, breaks covariance unless a Poincaré-natural split is proved. Kochen–Specker: λ selects ONE realm, not a global valuation.
- **Correction C — req 5 is EQUIVARIANCE not invariance** (folded into req 5 above).
- **Req 3 becomes automatic** from equivariant naturality: build X_Φ naturally from the covariant net over Diam⋊G (G = Poincaré / its spin cover ISpin(1,3) for Dirac), λ an equivariant global section, then A_{gD}[U_gΦ,gλ]=γ_g(λ_D)=g·A_D[Φ,λ] in one line. BW/Borchers give modular covariance. Breaks if: non-canonical pointer basis / split, frame-dependent ε(D), gauge/edge modes, tie-breaking.
- **The measure: the DECOHERENCE FUNCTIONAL is the answer.** μ_Φ(Cyl(α))=D_Φ(α,α)=⟨Φ|C_α†C_α|Φ⟩=τ_D(h_{Φ,D}P_α), extended by Kolmogorov–Carathéodory. Covariant via C_{gα}=U_gC_αU_g⁻¹ ⇒ equivariance; Born by construction. Type II trace τ_D is only a CARRIER (writes local Born weights, doesn't pin μ); BW/KMS geometric only for wedges/CFT-diamonds.
- **No-signaling survives conditional on a SCREEN-LOCAL MARGINAL LEMMA**: μ-pushforward of λ to any local instrument = AQFT Born state, independent of spacelike settings. Forced reformulation: if λ is the whole history (incl. settings), Bell MI ρ(λ|a,b)=ρ(λ) is ill-posed → restate MI for the PAST/common-cause component of λ.
- **7 repairs to borrow Gell-Mann–Hartle/Isham-HPO wholesale:** (1) realm-selection / Dowker–Kent; (2) contrary inferences → recorded histories only; (3) frame-dependent time-ordered class operators → Schwinger–Keldysh / Tomonaga–Schwinger; (4) Type III₁ exact-projection obstruction; (5) approximate decoherence needs ε(D) stable under gluing; (6) **holographic capacity log#Atoms(B_Φ(D))≤Q_D is NOT automatic in GMH — QIQT-H's new ingredient**; (7) the MI reformulation.

**THE LINCHPIN — Poincaré-equivariant holographic recorded-history sheaf theorem (paper §11.4):** for a covariant Haag–Kastler net (locality, isotony, time-slice, Haag duality, split/nuclearity, BW covariance) and every admissible Φ, ∃ finite Boolean record algebras B_Φ(D) with log#Atoms≤Q_D and DecErr≤ε(D), boundary reconstruction B_{Φ,∂}(D)≅B_Φ(D), a sheaf X_Φ over Diam, a nonempty Γ(X_Φ), a Born/decoherence-functional measure μ_Φ with Kolmogorov consistency, Poincaré equivariance, and no-signaling marginals. Then A_D[Φ,λ]=λ_D (mere evaluation) and req-3 covariance is immediate. **This is the real target of OP3b**; proving it even for FREE FIELDS first would convert the Lorentz promissory note into a result.

**Lean formalization target — DONE for the finite conditional layer (HEAD 2026-06).** The poset/sheaf layer is built and **axiom-free**: `LorentzSelection` (Diam poset, presheaf X_Φ with functorial restriction, global section λ, evaluation-gives-covariance PROVED) and `LorentzSelectionStrong`, which goes well beyond the original target:
- the four opaque AQFT axioms (record algebras + holographic bound, boundary reconstruction, decoherence measure, no-signaling marginal) were **retired** and replaced by an explicit `RecordedHistoryNet` structure — interface-as-hypothesis, not opaque axiom;
- **measure covariance is DERIVED, not assumed**: `born_unitary_invariant` ⇒ `ubornω_covariant` (the old `hcov` is now a theorem from unitary state/effect transport);
- `actSection` is a **genuine group action on Γ(X)** (`actSection_one`/`actSection_mul`, the section-object law, no `HEq` hacks);
- the boosted effects are a **full PVM** (`E_cov_preserves_proj` + `unitary_preserves_resolution`) and the weights a **covariant probability distribution** (`upvm_covariant_probability`);
- **non-trivial models exist** (`LorentzWitness` A: a spread 2-outcome Born distribution refuting the one-point net; B: a non-trivial group permuting two diamonds), settling vacuity.

All machine-checked, standard Lean axioms only, project axiom budget 33. Reviewed across seven GPT-5.5-pro rounds (Red → "Green for the finite conditional interface"). **What remains is exactly the continuum:** producing such a `RecordedHistoryNet` *with its unitary Poincaré transport* from an actual relativistic Type III₁ QFT (Tomita–Takesaki / Haagerup-L^p, beyond current Mathlib) — the genuine, untouched hard problem. Proving the linchpin even for FREE FIELDS first remains the next real target.

---

## 5. MUST-FIX SET BEFORE arXiv (the checklist)

- [ ] **(0)** Fix manifesto overclaim "There is only Φ" → "Only Φ is *dynamical*;
      a run also contains the non-dynamical actuality fact λ." (README + §1.0a)
- [ ] **(1)** **Bell → PI horn**: rewrite §6.9 + README Bell line; delete
      measurement-dependence-as-our-position; recommend keeping Palmer only as a
      *contrasting* sister program, not as QIQT-H's stance. State: keep free
      settings + outcome-definiteness ⇒ deny **Parameter Independence** at the
      ontic level; operational no-signaling holds after μ-averaging.
- [ ] **(2)** **λ relabel**: "microscopic initial conditions" → "atemporal global
      actuality/history selector" across all four papers + Lean docstrings + memory.
- [ ] **(3)** **Claim calibration**: "solves/dissolves the measurement problem" →
      "decomposes the problem; λ and μ are the remaining primitive/open structures."
- [ ] **(4)** **μ status**: explicitly "unconstructed / interface-level"; do not
      claim Born is derived.
- [ ] **(5)** **Holography status**: "Q_R bounds distinguishable-record capacity
      only; does not exclude superpositions or select outcomes."
- [ ] **(6)** **Lean**: theorem-dependency table separating machine-verified
      results from project/interface axioms (largely exists — surface it).

**Submission gate:** item (1) is the one *load-bearing inconsistency* — do NOT
submit with it unresolved. The rest are honesty/calibration; with them done, the
paper is defensible as a research-program / foundations-architecture paper.

**Status update (2026-06):** items (0)–(6) are all COMMITTED. The load-bearing
inconsistency (1) is resolved. What remains is the genuine research agenda — the
two breakthrough-defining open problems (μ construction; Lorentz covariance,
Open Problem 3b §4a) plus the supporting open problems (ε(R) form, recoherence
stability). These are honest gaps in a research-program paper, not blockers.

---

## 6. What critics will say if we DON'T fix it

> "This is Everett plus a primitive actual-world index and an unspecified Born
> measure, with internally inconsistent Bell language."

The fixes above convert that into the accurate, defensible:

> "An exactly-unitary single-world architecture that *decomposes* the measurement
> problem into a robustness part (decoherence), a finiteness part (holography),
> and two clearly-stated primitives (λ actuality, μ typicality), with a
> machine-checked dependency audit and a sharply-posed open problem (covariant μ)."
