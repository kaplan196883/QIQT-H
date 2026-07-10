# Boundary-dynamics candidates — enumerated and VERIFIED against the Lean sources

## STATUS UPDATE (2026-07-10, same day): RC1 LANDED — candidate 6's first brick is a theorem
`QIQTH/RecordChannel.lean` (commit `73fd89c4`, 57 declarations, [AF] std-3, budget 0): the
record-dephasing semigroup `Tsem s = e^{−s}·id + (1−e^{−s})·dephase` — a genuine one-parameter
semigroup of trace-preserving, unital, density-preserving channels COMMUTING with the held free flow;
fixed points = EXACTLY the record-diagonal states; exponential convergence of every state to its
record readout (`tendsto_Tsem_dephase` — decoherence/einselection as a semigroup theorem, the
dynamical upgrade of `alpha_diagonal`); entropy production (`entropy_Tsem_ge`, sign-flip-unitary
`dephase_matLog` crux); the Lyapunov theorem (`relEntropy_Tsem_le`, Gibbs instance
`relEntropy_Tsem_gibbs_le`); capacity respected with maxMixed the saturating fixed point
(`saturation_fixed`); record-relabeling equivariance (`Tsem_perm`). The boundary side is now an OPEN
QUANTUM SYSTEM with dynamics, not a ledger. HONEST: pointer basis an INPUT; PosDef carried per held
conventions; CP in prose; finite corner; E4/K2a/Gate-3 cited; NOT the strong principle, NOT QG.
Next bricks: the E4 join (semigroup equilibria feed `code_equilibrium_einstein`'s hypotheses) and
the candidate-3 unraveling (the jump chain + path measure via `CoarseGrainNaturality`).

## STATUS UPDATE 2: RC2 + RC3 LANDED (same day) — RC CAMPAIGN COMPLETE (`RC_CAMPAIGN_PLAN.md`)
- **RC2** `ef64ea39` `RecordEquilibrium.lean`: the second law WITH RIGIDITY (production zero ⟺
  record) + the E4 join `boundary_dynamics_equilibria_are_geometry` (stationary ∧ Lyapunov-stable ∧
  linearized-Einstein). Candidate 6's equilibria are now dynamically characterized, stable, and
  geometric.
- **RC3** `a63c9b73` `RecordUnraveling.lean`: `unraveling_exact` — candidate 6 = E_λ[candidate 3] AS
  A THEOREM (λ = jump time + Born-selected record; single-world actuality = one sample path);
  Chapman–Kolmogorov; the Born reading via the held `bornW`; **BORN FORCED**
  (`unraveling_weights_unique`) — the finite answer to candidate 3's named circularity risk (forced
  GIVEN the channel; why-this-channel = the remaining einselection input).
- Candidates 6 and 3 have thus moved from "toolkit complete / scaffold" to FIRST BRICKS LANDED; the
  6⟷3 unraveling subsection below is now theorem-backed end-to-end at the finite level. The open
  ends: the interacting (record-creating-from-coupling) upgrade of the channel, the continuum path
  measure (T5 machinery), and the why-this-basis einselection question.

**Date:** 2026-07-10. **Question:** what dynamics could run on QIQT-H's boundary side (the record/code
ledger), turning the machine-checked *dictionary* (`ADSCFT_GAP_ANALYSIS.md`) into a *duality*? Seven
candidates, each checked against the actual Lean theorems (grep sweep of `lean/mathlib/QIQTH/`,
2026-07-10). All cited results are [AF] std-3 unless noted.

## 0. The headline the sweep found: a free boundary dynamics ALREADY EXISTS (DY1–DY7 COMPLETE)

`QIQTH/Dynamics.lean` + `CrossCheck.lean` + `Conjectures.lean` — **the code has a time evolution**:
- `Hcode = Σ_k ω_k N_k` (the diagonal code Hamiltonian) with the Heisenberg flow `alpha` a genuine
  one-parameter group of ⋆-automorphisms (`alpha_add/mul/star`, entry formula — no Stone needed);
- explicit Gibbs/KMS states (`gibbs_isDensity`, `gibbs_kms_condition`), region reductions
  (`reduced_gibbsDensity_eq`), the region entropy formula (`entropy_gibbs_region`), saturation
  `Smicro_zero = Σ log D_k`;
- **`sigmaDiag_gibbs_eq_alpha_rescale`** — the Gibbs state's MODULAR flow IS the rescaled PHYSICAL
  flow (`σ_s^{ρ_β} = α_{−βs}`): candidates 1 and "physical Hamiltonian" provably coincide on thermal
  states;
- **DY6 `S_micro_zero_eq_inducedQuarterG`** — the saturated Sakharov cross-check, CALIBRATION-FREE:
  the micro side computed from the code Hamiltonian, the macro side supplied independently;
- **DY7 `FlatSpaceRecordGravityCorrespondence`** — the named conjecture Prop: micro record entropy =
  one-loop conical entropy = A/4G_ind with G_ind the Sakharov constant of the SAME field content —
  **one microscopic system computing both states and G** (exactly the single-theory cross-check
  `AdSCFTComparison.lean` identifies as AdS/CFT's remaining advantage); `finiteEvidence_holds`
  (DY1–DY6 bundled, every field a landed theorem); `continuumClaim` stated, never assumed.

**And the honesty theorem that defines the whole problem:** **`alpha_diagonal`/`alpha_recordProj` —
UNDER THE FREE DYNAMICS, EVERY RECORD IS STATIONARY** (H is a function of the N_k; the record algebra
is FIXED by the flow; only the ladders rotate). This is the Lean-precise statement of the
dynamical-source wall: **the free boundary dynamics exists and freezes the records; the dynamics that
CREATES records must be interacting (off-diagonal).** The missing boundary dynamics = interaction
terms, constrained by the no-gos below.

## The machine-checked no-gos that constrain EVERY candidate

- **`FQDynamicsNoGo.connected_finite_range_subsingleton`** — a literally finite invariant state set +
  continuous evolution ⟹ trivial dynamics. The boundary state space must be *operationally* finite
  (bounded entropy), never an exact finite grid.
- **Gate C `finite_modular_spectrum_ne_real_line`** (`QG/FiniteModularRecurrence.lean`) — a finite
  modular Hamiltonian has finite spectrum; the continuum BW boost has spectrum ℝ. Finite realizations
  of modular/clock dynamics are finite-time/low-energy approximations; the genuine flow needs the
  limit algebra (the Tower/Closure ladder).
- **L2 `causal_no_go`** (`MinkowskiDiamond.lean`) — deterministic structure growth carries a frame;
  a record-accretion process must be random or equivariant.
- **Gate 3 `equivariant_enforcement_preserves_invariance`/`safe_enforced_step`**
  (`QG/StateLevelLVGate.lean`) — the capacity-enforcement half of any dynamics must be equivariant;
  a non-equivariant enforcer is the (sole) Lorentz-violation door, pre-falsified.

## The seven candidates, with verified Lean status

1. **Modular dynamics (thermal time; H = −log Δ).** *Status: BUILT at the free/finite level; the
   continuum generator is the active ladder.* Held: `sigmaDiag`/`sigmaDiag_comp`
   (`FiniteModularTheory`), `towerGen = log Δ` (ID5), the modular-equivariant refinement tower
   (`cornerEmbed_sigmaDiag`), CHM ball flows, and — decisively — `sigmaDiag_gibbs_eq_alpha_rescale`
   (modular = physical on Gibbs states, so this candidate and DY's free Hamiltonian AGREE where both
   are defined). Constraint: Gate C (finite recurrence). Missing: which state; locality; interaction.
2. **Crossed-product clock dynamics (CLPW/Witten observer route).** *Status: structurally FAR ALONG.*
   Held: `clockTransl_stronglyContinuous` + the clock generator via `stoneGen`
   (`CrossedProductGenerator.lean`), the covariance relation (`CrossedProductCovariance.lean`),
   `fiberModFlow_comm_clockTransl`, Weyl covariance (K1), and the entropy law of the dual flow
   `K5_dual_covariant_count` (`S(θ_s·) = S(·) − s` — a dynamics that provably rescales capacity).
   Missing: matter–clock coupling; normal weights (Wall 4).
3. **Stochastic record accretion — the (Φ,λ) process as dynamics.** *Status: SCAFFOLD EXISTS.*
   Held: `SelectionDynamics.lean` (the `SelectionModel` structure — microstates, Born-agnostic
   typicality measure, deterministic readout, remote action, DGZ-style equivariance condition; a
   non-vacuous uniform-measure instance giving the remote no-signaling half WITHOUT assuming Born),
   `CoarseGrainNaturality` (Kolmogorov consistency of the Born measures — exactly the projective
   system a stochastic process needs), the σ-additive infinite Gibbs measure (T5),
   `BornConcentration` (Chebyshev frequency bounds). Named honest risk (in the file header): if the
   only equivariant μ is |Ψ|² the construction is circular; the non-circular hope is Valentini-style
   relaxation. Constraints: L2 (randomness), Gate 3 (equivariant enforcement). Unique payoff: would
   answer single-outcome selection AND the dynamical source in one object.
4. **Random-circuit / random-tensor-network dynamics on the screen code.** *Status: GERM ONLY.*
   Held: the discrete-Weyl 1-design engine (`Entropy/WeylDesign.lean` character orthogonality; the
   clock-twirl) and `dpi_mixed_unitary` — depolarization realized as an AVERAGE OF UNITARY
   CONJUGATIONS (the repo's one genuine random-unitary-average theorem); unconditional exact RT
   (`maxFlow_min_cut` → `exact_rt_unconditional`) as the pattern such dynamics must produce. Missing:
   any Haar/typicality machinery; finite k-design dynamics is the tractable entry.
5. **Refinement/RG flow — scale as the time (radial) direction.** *Status: CATEGORY-LEVEL ONLY.*
   Held: `cornerEmbed` (state-compatible, modular-equivariant embeddings — the ITPFI tower data),
   `EdgeRefinement`/`refinement_preserves_area_and_capacity` (G4 toy background independence),
   `forced_weight_product` (the flow's rigid invariant), `LambdaRG_invariant` (dimensional
   transmutation). Missing: a generator/semigroup — a flow equation, not a diagram. Payoff if built:
   gap 4 (emergent radial dimension) and the dynamics gap become one object.
6. **Dissipative capacity-respecting channel dynamics (Lindblad-type).** *Status: TOOLKIT COMPLETE,
   DYNAMICS ABSENT — and the TARGET THEOREM ALREADY EXISTS.* Held: the full DPI/Lieb tower
   (`dpi_mixed_unitary`, `partial_trace_dpi`, `strong_subadditivity` — entropy monotonicity under
   channels, DONE), the explicit Gibbs equilibria (DY2/DS2), and **`code_equilibrium_einstein`**
   (E4: code equilibrium ⟹ first law at every ray ⟹ linearized vacuum Einstein). Missing: the
   semigroup itself. **The most Lean-tractable first brick in this whole document:** define a
   one-parameter family of capacity-respecting channels on the held finite code, prove entropy
   monotonicity from the held DPI, and show its fixed points are exactly the E4 equilibria — the
   first machine-checked "the boundary dynamics' equilibria ARE geometry."
7. **Constraint enforcement as dynamics (saturation as attractor).** *Status: the CONSTRAINT side is
   complete; not a standalone candidate.* Held: Gate 3's `admissible_smul_iff`/
   `constraintSet_invariant`/`safe_enforced_step`, and `uniform_realizes_area_law` (max-entropy
   realizes the count — the saturation regime is where the area law lives). Every other candidate
   must satisfy this one.

## 6 ⟷ 3: the unraveling relationship (why the channel brick is also candidate 3's first brick)

Candidates 6 and 3 are ONE physical process at two levels of description — the standard quantum-
trajectories (GKSL ⟷ jump-process) relationship: **candidate 6 is candidate 3 with λ integrated out;
candidate 3 is candidate 6 with λ put back in.**

The dictionary:
- each Lindblad/Kraus **jump operator** of the channel = one **record-formation event** of the
  accretion process (a capacity-respecting channel = one whose Kraus operators write into the record
  factor without exceeding Q_D — einselection);
- the channel's **jump rates** = the accretion chain's **transition probabilities**;
- the channel state = the **λ-average over accretion paths**: (6) = E_λ[(3)];
- the compatibility condition — the path process's one-point marginals evolve by the channel — **is
  already a theorem**: `born_coarse_grain`/`CoarseGrainNaturality` (Kolmogorov consistency of the Born
  measures under context refinement) is exactly what makes the σ-additive PATH measure constructible,
  and T5's `Measure.infinitePi` machinery is the constructor.

How the held theorems distribute across the two levels:

| Channel level (candidate 6)                              | Path level (candidate 3)                    |
|----------------------------------------------------------|---------------------------------------------|
| DPI (`dpi_mixed_unitary`, `partial_trace_dpi`) — entropy monotone | the arrow of accretion: record formation only loses distinguishability |
| Gate 3 equivariance (`safe_enforced_step`)                | the DGZ condition `(R)_*μ = μ` in `SelectionModel` |
| Gibbs fixed points (DY2) / E4 equilibria (`code_equilibrium_einstein`) | detailed balance of the jump chain; SATURATION = where accretion stalls against capacity (the horizon as the stationary regime) |
| Born weights of outcomes (`bornW`)                        | path frequencies — `BornConcentration`'s Chebyshev bound |

Two QIQT-H-specific payoffs of building the semigroup (6) first:
1. **Gate 3 transfers downward** — channel-level equivariance constrains the path measure's
   equivariance, so the covariance requirement on the accretion process (L2: random-or-equivariant)
   is inherited, not re-proven.
2. **The circularity risk named in `SelectionDynamics.lean` becomes DECIDABLE**: with a concrete jump
   chain, "is the stationary/consistent path measure forced to be the Born weights?" is a finite
   fixed-point question. Forced-by-necessity = the non-circular Born derivation (the Valentini-style
   relaxation hope, as a theorem); forced-by-assumption-only = the circularity exposed. Either
   outcome is progress, and it is exactly the kind of finite statement the repo proves well.

So the sequencing is: build (6) — the generator, the entropy monotone from held DPI, fixed points =
the E4 equilibria; then unravel to (3) — the finite Markov jump chain on the record ledger, the path
measure via `CoarseGrainNaturality` + `Measure.infinitePi`, and the equivariance/Born fixed-point
question posed as a theorem. The ensemble half is lawlike and gate-safe; the path half carries
QIQT-H's distinctive single-world content.

## Synthesis

The natural composite — and structurally what "a CFT" is from the holographic side — is: modular/clock
flow (1+2) as the time direction, refinement flow (5) as the radial direction, stochastic accretion or
random circuits (3/4) as the microscopic process, channel dynamics (6) as its coarse-grained
description, and (7) as the consistency constraint. The Lean sweep shows the repo has: the free time
direction BUILT (DY), the clock structurally built (2), the equilibrium⟹Einstein target theorem built
(6/E4), the constraint side built (7), scaffolds for the selection process (3), and germs for
randomness (4) and RG flow (5).

**The three checks any candidate must pass (all theorem-shaped in the repo):** (a) equivariance (the
gates); (b) it must FORCE the correlation patterns the geometry-as-output program currently inserts —
in Lean terms: it must make records NON-stationary in exactly the pattern that decodes to geometry
(the interacting upgrade of `alpha_diagonal`); (c) the strong half of decoupling — the geometry/G side
must survive the same capacity limit that already provably forces the free matter sector (DS7's named
gap), i.e. prove `continuumClaim` of `FlatSpaceRecordGravityCorrespondence` or its finite shadow.

⚠ Scope firewall: an enumeration of candidate mechanisms with verified formal status — no candidate is
claimed correct; no new physics; NOT QG.
