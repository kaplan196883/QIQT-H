# QIQT-H — Roadmap to the prize (the canonical covariant typicality measure μ)

*Battle plan from the GPT-5.5-pro "be bold" consultation (2026-06), recorded as the
working program for Open Problem 1. The prize = a canonical, Lorentz-covariant
typicality measure μ over λ with Born marginals, consistent under coarse-graining and
composition, with NO per-measurement stipulation — the object that turns QIQT-H from a
(b+) conditional program into a genuine breakthrough.*

## 0a. Status (2026-06-06) — the FINITE portion of this route is realized, axiom-free

The **finite-dimensional** stage of the Effect-Gleason route below is now machine-checked,
axiom-free (budget 33, standard-three only). Built and joined this session: finite effect-Gleason
(`EffectGleason.finite_effect_gleason` — Born from positivity+additivity); the single-trial Born
law **forced from non-contextuality** (`OneSiteGleason.oneSite_forced`) with its converse
(`traceEffectMeasure`); product-preparation independence (`BornTypicalityFinite.w_history_factorizes`);
finite typicality (Chebyshev/union); product-measure uniqueness (`BornMeasureUniqueness`); and the
**finite no-collapse Born representation** joining the capacity core to all of the above
(`BornJoin.finite_noCollapseBornRepresentation`, `BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality`).
Two GPT-5.5-pro verification passes: *sound, non-vacuous, but a CONDITIONAL representation theorem*
— Born **weights** + **factorization** are derived from non-contextuality + product preparation,
NOT from `Q_max` alone. Full claim→theorem map + honest scope: **`FINITE_BORN_REPRESENTATION.md`**.

**What this route's PRIZE still needs (continuum):** Stages 3–5 below — the Covariant
Record-Completeness Lemma and the AQFT localization producing a single **Lorentz-covariant** μ.
The 33 remaining axioms are exactly this continuum / Type III₁ interface (beyond current Mathlib).

**A concrete, Lean-grounded staged execution plan** (free-field finite-mode instance → sheaf /
global-section / cohomology layer → continuum analytic infrastructure), with per-item difficulty,
dependencies, what already exists, and kill-criteria, is in **`PRIZE_EXECUTION_PLAN.md`**. Headline:
Stages 1–2 (free fields, finite-mode) are the next concrete builds and would already convert the
Lorentz promissory note into a result; Stage 3 (Type III₁ / Tomita–Takesaki) is the long pole.

## 0a′. Status update (2026-06-08) — Stage-3 infrastructure built to the Mathlib frontier; honest distance-to-prize

A full re-inspection of all 67 Lean files (axiom-ledger + four cluster audits) plus a session of
continuum work updates the picture. The headline: **the "long pole" (Stage 3 operator-algebra
infrastructure) is now substantially built and axiom-free** — it no longer sits at zero, but at three
*named Mathlib-infrastructure walls*. The distance to the prize, by layer:

- **Layer A — the no-collapse mechanism ("finite Q_max ⇒ single outcome, no collapse"): DONE.**
  Axiom-free, non-vacuous, *derived* (not assumed): the capacity bound is a theorem from
  orthonormality/dimension (`CapacityModel`, `OrthogonalCapacity`); saturation is derived from SBS
  redundancy (`SBSBridge`); the one physical input γ<1 is derived from a toy QND Hamiltonian
  (`CollisionalGamma`). `qiqth_single_outcome_no_collapse`, `ValueSelection`. **Distance ≈ 0.**
- **Layer B — Born: a CONDITIONAL representation theorem, not "Born from nothing."**
  Genuinely proved axiom-free: `EffectGleason.finite_effect_gleason` (finite Busch),
  `GleasonSelector.born_is_forced` (Born from positivity + ray-certainty), tensor-multiplicativity,
  Chebyshev typicality. **But** the load-bearing premises — non-contextuality, ray-support/positivity,
  product independence, **measure equivariance** — are *assumed*, each *proved necessary* by
  countermodels (`EquivarianceGap`, `NoBornFromNothing`, `BornMinimalityTable`) but not *forced* from
  Q_max/holography alone. Honest claim: *"Born is the unique admissible measure given a named minimal
  set of independent postulates."* **Distance = reduce those premises to first principles — a shared
  open problem of every single-world program, not a coding gap.**
- **Layer C — the covariant μ (OP3b, the prize proper): finite skeleton DONE & RIGID; continuum OPEN.**
  `LorentzSelectionStrong` is axiom-free and rigid (external geometry, a *real* Poincaré group action
  with consumed group laws, **covariance derived from unitarity**, normalization derived), with
  non-trivial models incl. `DiamondSwapNet` (a genuine geometry-moving swap over a real orbit) and
  `FreeFieldNet` (no-signaling *derived* from the product Born measure). The continuum **Type III₁
  realization is open** — pinning geometry/Born-weights/dynamics to an actual relativistic QFT + the
  N→∞ limit.
- **Layer D — Stage-3 operator-algebra infrastructure (feeds Layer C): built to the frontier.**
  NEW since the 2026-06-06 status: the **bounded spectral theorem** (`PVM_of_selfAdjoint`, `T=∫λ dE`)
  and **bounded Borel FC** are COMPLETE (`QIQTH/Spectral/SpectralTheorem.lean`), superseding the
  "Spectral/PVM lacks the analytic spectral theorem" line of the old inventory; the **continuum
  modular flow** `Δ^{it}` is a strongly-continuous unitary group with its modular automorphism
  `*`-group `σ_t`, state-invariance, and an entire complex-time flow; the **Rieffel–Van Daele
  standard-subspace** objects are complete up to the analytic square root
  (`QIQTH/StandardSubspaceModular.lean`: `0≤R≤2`, `R` ℂ-linear/positive `Rℂ`, `D=P−Q`
  conjugate-linear ⇒ `J` antiunitary). **Three live walls remain**, each an independent upstream
  Mathlib contribution: (1) the operator square root / `StarOrderedRing (B(H))` (circular with the
  sqrt it would unlock — Mathlib-flagged future work); (2) unbounded antilinear Tomita `S`;
  (3) genuine KMS (the identity is *false* for an arbitrary generator, so not claimed). Details:
  `TOMITA_TAKESAKI_ROADMAP.md` §"CURRENT STATUS". All axiom-free; **budget held at 33** (all 33 are
  honest named entropy/modular interface inputs — audit found no vacuous/illegitimate axiom).

**Bottom line.** The *mechanism* (Layer A) is in hand and machine-checked. The two genuine open
frontiers are the *unconditional* Born derivation (Layer B — discharge the named premises to deeper
principles) and the *continuum* covariant μ (Layer C) — the latter gated on Layer-D infrastructure
now built right up to three specific Mathlib walls. Nothing here is faked; the budget confirms it.

**Update (2026-06-08) — the continuum covariant μ is now MACHINE-CHECKED end-to-end** (the "XL step",
`XL_STEP_PLAN.md`): the σ-additive, unique, Born-marginal, covariant, no-signaling typicality measure
μ∞ over histories/λ is built for the **correlated/entangled** case (Phase A: `FiniteMarginals`,
`KolmogorovFiniteFiber.exists_isLimit` via a finite-fiber Kolmogorov extension I proved from
compactness), and the construction is **state-agnostic** — μ∞ exists for ANY normal state on a
compatible net (Phase B core: `StateNetMeasure.EffectStateNet`, with a non-vacuity witness). All
axiom-free, budget 33, Fine/Bell contextuality constraint enforced. The SOLE remaining gap is the
*physical* input — a **normal state on a Type III₁ QFT net** — whose construction is now itself
**planned** in `PHASE_B_INFRASTRUCTURE_PLAN.md`: **Part A** (predual / trace-class / normal states of
`B(H)` — bounded, Mathlib-contributable, the only piece μ needs) and **Part B** (Type III₁ /
Buchholz–Wichmann — research-grade, multi-year, NOT needed for μ; characterizes the algebra type).

**Update (2026-06-08b) — Phase-B Part A STARTED, the loop is CLOSED on `B(H)`, and a free-field
covariant μ∞ is built (all axiom-free, budget 33).**
- **Genuine normal state on infinite-dim `B(H)`** (`QIQTH/NormalState.lean`): the diagonal density
  operator `ω(x)=Tr(ρ x)=∑ pₙ⟨bₙ,x bₙ⟩` — positive, normalized, additive (`diagStateHom`), bypassing
  the (unbuilt) general Schatten theory.
- **LOOP CLOSED end-to-end on `B(H)`** (`QIQTH/BHTypicalityMeasure.lean`, `bh_typicalityMeasure_exists`):
  a real normal state on `B(H)` → `EffectStateNet` → finite-fiber Kolmogorov extension → a unique
  σ-additive probability typicality measure μ∞ — the first fully **infinite-dimensional** instance of
  the whole pipeline.
- **General trace-class foundation** (`QIQTH/AbsoluteValue.lean`): the operator absolute value
  `|T|=√(T⋆T)` (Simon §1.1) via `cfc` on the nonneg spectrum of `T⋆T` (`spectrum_star_mul_self_nonneg`
  — sidesteps the missing `StarOrderedRing (B(H))`), with `|T|·|T|=T⋆T`, `‖|T|x‖=‖Tx‖`.
- **FREE-FIELD covariant typicality measure** (`QIQTH/FreeFieldTypicality.lean`,
  `freeFieldMeasure_boost_invariant`): the pipeline run on genuine free-field occupation sectors
  `m → Bool`, with μ∞ **invariant under the geometry-moving mode-permutation boost** (the finite-mode
  Lorentz action) — genuine covariance of the typicality measure, instantiated by field structure.

So the entire measure / state / covariance apparatus is machine-checked AND now runs on a genuine
**free-field net with a real boost symmetry** — at **finite mode number (Type I)**.  The one genuinely
remaining frontier for the *continuum* (Type III₁) prize is the **Fock / CCR / quasifree-vacuum field
infrastructure** (real symplectic test space → Weyl algebra → quasifree vacuum → Fock → local net →
explicit second-quantized boost): a separate **multi-year, build-from-scratch** program (Mathlib has
none of it), but **wall-free** — that route bypasses the Tomita/Type-III machinery (never forms `Δ^{1/2}`)
— and **every downstream piece is already proven**, so it is "build the field net," not "redo the measure
theory."

## 0. The route we commit to (and what we reject)

**Effect-Gleason + Kolmogorov — NOT the raw decoherence functional.**

    finite records ⇒ effects/POVMs ⇒ Busch / Bunce–Wright–Christensen–Yeadon
    Mackey–Gleason uniqueness ⇒ Born weights ⇒ projective cylinder family
    ⇒ Kolmogorov/Riesz unique covariant μ.

We do **not** start from `μ_Φ(Cyl α) := D_Φ(α,α) = ⟨Φ|C_α†C_α|Φ⟩`. That formula is
correct *as a corollary* but fatal *as a definition*: it is not Kolmogorov-additive on
non-decoherent families and it looks **chosen**. The decoherence functional re-enters
only as the theorem's output, on recorded/decoherent Boolean contexts. Envariance
(Zurek) and decision theory (Deutsch–Wallace) are **optional explanatory add-ons, not
the proof core** — the DW circularity charge is sidestepped by using operator-algebraic
probability uniqueness instead of decision theory.

## 1. The make-or-break sub-claim

**Covariant Record-Completeness Lemma.** Every finite objective-record protocol in the
AQFT net determines, functorially and foliation-independently, a finite POVM `{E_i}`,
*and* the class of record protocols is rich enough to tomographically separate all finite
effects Gleason needs. **Prove this and the rest is theorem-chasing.** (Finite-dim it is
near-trivial — records *are* POVMs; the depth is the AQFT localization, Stages 3–5.)

## 2. The central theorem (whose proof IS the breakthrough)

**QIQT-H Covariant Record Representation Theorem.** Let `𝒜 : Diam → vNAlg` be a
Haag–Kastler net (isotony, Einstein causality, Poincaré covariance `U_g 𝒜(O) U_g⁻¹ =
𝒜(gO)`, split property, no type-I₂ obstruction); `Φ` the exact unitary universal state
with local normal state `ω_Φ(A) = ⟨Φ,AΦ⟩`. A *finite record protocol* `π` = localized
instruments in finitely many causal diamonds with finite outcome set `Ω_π` and Heisenberg
effects `E^π_r ∈ 𝒜(O_π)`, `0 ≤ E^π_r ≤ 1`, `∑_r E^π_r = 1` (for a closed projective
history, `E^π_α = C_α† C_α`). A *QIQT-H typicality assignment* `T` satisfies:
(i) finite additivity / coarse-graining; (ii) effect noncontextuality (same effect ⇒ same
probability); (iii) finite-record covariance + **record certainty** (an occupied sharp
pointer re-reads as certain); (iv) tensor multiplicativity on split products;
(v) Einstein locality (spacelike ops commute); (vi) Poincaré covariance
`T^{gπ}_{U_gΦ}(gr) = T^π_Φ(r)`; (vii) normality / continuity.

**Conclusion A (Born/effect):** for every finite record protocol
`T^π_Φ(r) = ω_Φ(E^π_r) = ⟨Φ, E^π_r Φ⟩`; for every exactly-decoherent recorded family
`{C_α}`, `D_Φ(α,β) = ⟨Φ, C_β† C_α Φ⟩`, `= 0` for `α≠β`, and
`T_Φ(α) = D_Φ(α,α) = ⟨Φ, C_α† C_α Φ⟩`; on a finite/Type-II record carrier `D` with trace
`τ_D`, `T_Φ(α) = τ_D(h_{Φ,D} P_α)`, `h_{Φ,D}` the unique Radon–Nikodym density of
`ω_Φ|_D`.

**Conclusion B (global measure):** with `X_Φ` the recorded-history sheaf over `Diam⋊𝒫↑₊`
(finite Stone-space fibers) and `Γ(X_Φ) = lim_π Ω_π` the compatible global record sections
`λ`, there is a **unique** regular probability measure `μ_Φ` with
`μ_Φ(Cyl_π(S)) = ∑_{r∈S} ω_Φ(E^π_r)`.

**Conclusion C (covariance/product/LLN/no-signaling):** `g_* μ_Φ = μ_{U_gΦ}`;
`μ_{Φ⊗Ψ} = μ_Φ ⊗ μ_Ψ`; iid ⇒ strong law `μ_Φ(lim_N (1/N)#{k:r_k=i} = p_i) = 1` with
`p_i = ω_Φ(E_i)`; for spacelike Bell protocols `p(a,b|x,y) = ω_Φ(E^A_{a|x} F^B_{b|y})`
with `[E^A,F^B]=0` ⇒ `∑_b p = ω_Φ(E^A_{a|x})` independent of `y` (no-signaling after
μ-averaging); free settings = independent setting record factors `ν_X(x)ν_Y(y)μ_S(λ_S)`
with arbitrary `ν_X,ν_Y` (no superdeterminism).

## 3. Why μ is FORCED, not chosen (requirement 7 — the uniqueness skeleton)

1. **Effect functional.** `f_Φ(E) := T_Φ(record realizing E)` is well-defined by (ii);
   coarse-graining ⇒ `f_Φ(E+F) = f_Φ(E)+f_Φ(F)` for `E,F ≥ 0`, `E+F ≤ 1`; `f_Φ(1)=1`.
   By **Busch-Gleason (POVMs)** / **Bunce–Wright / Christensen–Yeadon Mackey-Gleason**
   (vN algebras with no type-I₂ summand), `f_Φ` extends uniquely to a normal state
   `f_Φ(E) = ρ_Φ(E)`; on finite/Type-II carriers `= τ(h_Φ E)`.
2. **Record certainty pins the vector state.** The certainty/repeatability clause kills
   the maximally-mixed alternative `tr(E)/d` (which satisfies positivity, normalization,
   covariance, tensor multiplicativity, locality but ignores `ψ`). It forces
   `ρ_ψ = |ψ⟩⟨ψ|`, i.e. `f_ψ(E) = ⟨ψ,Eψ⟩`. **Record certainty is the semantic content of
   "objective record" — not optional; without it uniqueness is FALSE.**
3. **Cylinder uniqueness.** All finite cylinder probabilities fixed ⇒ Kolmogorov /
   Riesz–Markov gives a unique measure on the inverse limit of finite record spaces; any
   `μ'` with the same finite-record axioms agrees on the generating cylinder algebra.

Strongest spine: **Busch / Bunce–Wright Gleason + Kolmogorov uniqueness.**

## 4. Landmines and defusals

| Landmine | Defusal |
|---|---|
| Type III₁ local algebras have no trace | Don't make trace fundamental — use normal states on III; `τ_D(hP)` lives only on finite/Type-II record carriers / split inclusions / Falcone–Takesaki core. |
| Decoherence functional not additive on arbitrary histories | Extend only over recorded/decoherent Boolean contexts (where `D(α,α)` is a genuine classical measure). |
| Kochen–Specker contextuality | λ is a global section of *actual recorded* Boolean algebras (incl. settings), NOT a valuation of all projections. |
| Bell / free settings | QIQT-H is not local-deterministic HV; free settings = independence from *source-section* variables under split products, not from the whole λ (which includes settings). |
| Deutsch–Wallace circularity | Avoid decision theory; use operator-algebraic probability uniqueness. |
| Qubit/Gleason loophole | Use POVM/effect Gleason (Busch), or tensor a qubit with a finite record ancilla. |
| Crossed product depends on a reference state (breaks covariance) | Use the **Falcone–Takesaki canonical core** (functorial under automorphisms), not a state-dependent crossed product. |
| No strict local projectors (Reeh–Schlieder / Hegerfeldt) | Records live in localized detector/probe algebras (Fewster–Verch / BFV measurement schemes), not vacuum-annihilating field projectors. |
| Hidden foliation in class operators | Define protocols over the causal partial order; spacelike products commute ⇒ any linear extension gives the same effect. |
| Roberts/DHR gluing obstruction | Twisted sheaves; vacuum/neutral sector ⇒ obstruction vanishes; general ⇒ `μ = ∑_ρ q_ρ μ_ρ` over sector weights. |
| Only approximate decoherence | Prove the exact theorem first; then robustness: `|D(α,β)| ≤ ε ⇒` additivity fails by `O(n²ε)`. The QND `γ^N` result (`CollisionalGamma`) supplies the decay. |

## 5. Staging (the de-risking ladder)

- **Stage 1 — finite-dimensional (THE MINIMAL BREAKTHROUGH).** Finite Record
  Effect-Gleason Theorem: any effect-probability assignment satisfying coarse-graining +
  effect noncontextuality + finite-record covariance + tensor multiplicativity + record
  certainty equals `⟨ψ,Eψ⟩`; then `∑_α C_α†C_α = 1`, `p(α) = ⟨Φ,C_α†C_αΦ⟩`, decoherent
  coarse-graining additive. *Status: the single-state core is DONE axiom-free
  (`GleasonSelector.positive_ray_certain_forces_born`); the NEW gaps are tensor
  multiplicativity + decoherent partition additivity — see `RecordGleason.lean`.*
- **Stage 2 — finite causal poset.** Spacelike order-independence, covariance, Bell
  no-signaling, free-setting factorization, iid LLN. De-risks (2)–(6).
- **Stage 3 — single AQFT causal diamond.** Split inclusion `𝒜(O₁) ⊂ N ⊂ 𝒜(O₂)`,
  `N` type-I / finite-record carrier; finite detector records implement finite effects.
  First serious Type-III defusal.
- **Stage 4 — free fields.** Massive scalar / Weyl net (Poincaré covariance + split known;
  Fewster–Verch detector schemes); construct `μ_Φ` for finite detector networks.
- **Stage 5 — full sheaf/DHR.** `X_Φ` over `Diam⋊G`; Roberts cohomology (twisted sections;
  `μ = ∑_ρ q_ρ μ_ρ`).

## 6. Lean vs pen-and-paper

**Formalize in Lean (axiom-free) first:** finite effects/POVMs; the finite Effect-Gleason
proof (additivity ⇒ positive linear functional ⇒ density ⇒ ray-certainty ⇒ rank-one);
class operators + `∑ C_α†C_α = I` + decoherent additivity; tensor/product probabilities;
no-signaling marginals; weak LLN (Chebyshev — `BornConcentration`); finite inverse-limit
cylinder uniqueness.

**Stay pen-and-paper (named imported hypotheses, beyond Mathlib):** Bunce–Wright /
Christensen–Yeadon Mackey-Gleason; Type-III AQFT; split property; Fewster–Verch
measurement theory; Roberts/DHR cohomology; Falcone–Takesaki core.

## 7. Kill-criteria (pivot if…)

1. A non-Born assignment satisfies the **exact** finite axioms *including record certainty*.
2. Record certainty turns out disallowed (⇒ maximally-mixed survives, uniqueness false).
3. Record protocols are not effect-complete (Born underdetermined).
4. Overlapping recorded partitions cannot form a consistent cylinder system (no global μ).
5. Finite records cannot be localized in diamonds without foliation dependence (req 6 fails).
6. Even the restricted *recorded* sheaf has no sector-twisted global sections (drop λ-as-section).
7. Normality cannot be justified (singular finitely-additive states spoil uniqueness).

## Bottom line (GPT-5.5-pro)

> "The prize is reachable on this route. The decisive theorem is the Covariant
> Record-Completeness + Effect-Gleason Representation Theorem. Once finite records are
> functorially identified with effects and the record category is rich enough, Born
> weights and the global Lorentz-covariant μ are forced, not stipulated."

Even so, the result would be a **λ-augmented / modal no-collapse** derivation (Φ + λ),
not a ψ-only one. The breakthrough is "μ derived, not chosen" — it removes the largest
probability-theoretic debt; it does not eliminate λ.
