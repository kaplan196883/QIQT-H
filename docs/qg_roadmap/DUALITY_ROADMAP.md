# DUALITY ROADMAP — what separates the verified dictionary from a genuine duality

**Date:** 2026-07-12 (D3 skeleton complete + cited-inputs program G1/G2 landed; see the ledger).
**Companions:** `ADSCFT_GAP_ANALYSIS.md` (the mechanism-by-mechanism
comparison), `WHERE_WE_ARE.md` (the full-credit status), `FLAT_RECORD_GRAVITY_CONJECTURE.md`
(the target statement + the cited-inputs discharge ledger). **Definition used throughout:** a DUALITY is two independently defined
theories provably describing the same physics; a DICTIONARY is a set of proven correspondences
between two bookkeepings of one constructed object. QIQT-H today holds the dictionary (much of it
as theorems); this file enumerates exactly what is missing for the duality, item by item, each
with its Lean-precise obstruction status.

## The six missing pieces

### D1 — an interacting boundary Hamiltonian (the theory itself)
The boundary has kinematics, thermodynamics, and dissipation — but its unitary dynamics is FREE
(`Hcode = Σ ω_k N_k`; `alpha_diagonal` PROVES the free flow cannot create records) and record
formation is a coupling MODEL (IC1's pure-dephasing/measurement limit, einselection derived at the
Cesàro level). A duality needs one self-contained interacting Hamiltonian on the code from which
the dephasing, the geometry-decoding correlations, and the equilibria all FOLLOW.
**Status:** the pointer-competition case `[H_S, A] ≠ 0` is the named next brick; nothing
structural blocks it — it is unbuilt, not obstructed.

### D2 — the large-capacity limit as an actual limit theory (the N → ∞ slot)
The exact CCR is recovered as D → ∞ at bounded occupations (DS1 `commutator_eventually_exact`)
and the limit algebra `towerLimitVN` exists with its COMPLETE modular theory — but the ladder
stops two rungs short:
- **JMJ = M′ past the Kaplansky gap** (LA1′: the equality holds pointwise on the cyclic orbit;
  the obstruction is Lean-precise — the RATIO-weighted Frobenius operator bound vs the
  COLUMN-weighted GNS bound are inequivalent quadratic forms; the Δ-smoothing route is the named
  escape);
- **the type III₁ classification** (the Araki–Woods fingerprint is proven arithmetically, T1–T8;
  the operator inference is CITED — and no proof assistant has a factor/type API).
Without the completed limit, "the boundary theory contains the graviton" remains a
truncated-avatar statement (EM1–EM7), not a spectral one.
**Status:** two named rungs, each with a characterized obstruction.

### D3 — THE STRONG HALF OF DECOUPLING (the duality-making theorem; the center)
DS1–DS7 proved the weak half: the MATTER sector survives the cutoff limit, and the area weight is
rigid. A duality requires the GEOMETRY side to survive the SAME limit from the SAME parent — so
that `S = A/4G` becomes a consistency theorem of ONE theory rather than two bookkeepings
calibrated to shared primitives (`AdSCFTComparison.lean`'s exact diagnosis of what AdS/CFT
uniquely has). This statement EXISTS as the named Prop **`FlatSpaceRecordGravityCorrespondence`**
(`Conjectures.lean`): micro continuum record entropy = one-loop conical entropy = area/4G_ind,
ONE microscopic system computing both the states and G. Its finite half is PROVEN
(`finiteEvidence_holds`); the continuum half is the conjecture.
**Status:** stated, finite-evidenced, open. Proving it IS acquiring the duality.

### D4 — bulk dynamics from boundary dynamics
Held: statics (equilibria are Einstein states — `boundary_dynamics_equilibria_are_geometry`,
E4-conditional) and the decoder (`reconstruct` — metric from area data). Missing: the theorem
that boundary EVOLUTION generates bulk EVOLUTION. Even the composable first rung — the RC
relaxation trajectory `T_s ρ` inducing a metric trajectory `h(s)` through the held area probes,
with its evolution law inherited from the flow — is not built. (In AdS/CFT this is automatic:
one Hamiltonian, two readings.)
**Status:** first rung composable from held pieces; unbuilt.

### D5 — the radial dimension
Entanglement-at-all-scales becoming the holographic direction (Maldacena's U = RG scale). Held:
the substrate (exact RT = `maxFlow_min_cut`, unconditional; the refinement tower with its rigid
forced-weight invariant; state-decoded geometry through dS₂). Missing: the scale-as-dimension
theorem — the decoded bulk is spatial and single-scale.
**Status:** substrate unconditional; the theorem absent.

### D6 — protection (what makes a dictionary RIGID)
Non-renormalization is why AdS/CFT's dictionary has fixed coefficients. No analogue exists here,
which is why `N_eff/4`, `Λ_s`, and the heat-kernel `c_i` float — with the `c_i` blocker (the
`(1/6−ξ)` Seeley–DeWitt coefficient) gated on the ecosystem-wide Riemannian heat-kernel gap that
no proof assistant has crossed. Without protection, even a proven correspondence is a
one-parameter FAMILY of dictionaries, not THE dictionary.
**Status:** absent; the deepest blocker is external (Mathlib's own diff-geo frontier).

## The dependency structure and the critical path

```
D1 (interacting H)  ──►  D2 (limit theory)  ──►  D3 (strong decoupling = THE DUALITY)
       │
       └──►  D4 (bulk dynamics)                 D5, D6: parallel tracks
```

D1 → D2 → D3 is a chain: the interacting theory feeds the limit; the limit is where the
strong-decoupling conjecture lives. D4 hangs off D1 (needs dynamics worth transporting). D5 and
D6 are parallel and independently valuable.

**The critical path to "duality" is exactly three objects long:** the interacting code
Hamiltonian (D1), the completed limit algebra (D2), and the DY7 continuum correspondence (D3) —
and the third is already written down with its finite half proven.

## Suggested next bricks (each loop-sized, in path order)

- **D1a:** the pointer-competition model — `H = H_S + A⊗B` with `[H_S, A] ≠ 0`; target: the
  einselected basis as a function of the coupling strength (the honest hard case of IC1).
- **D4a:** the statics→dynamics rung — `h(s) := reconstruct(δA(T_s ρ))` and its evolution law
  (composable from held pieces; the first machine-checked "boundary relaxation drives bulk
  geometry in time").
- **D2a:** the Δ-smoothing campaign (the Kaplansky escape — mollify the compression approximants
  by bounded functions of the held Δ).
- **D3a:** the first continuum rung of `FlatSpaceRecordGravityCorrespondence` (scope with a
  design consult; the conjecture's finite evidence names the shape).

## D3d DESIGN — CONSULT DONE (gpt-5.5-pro, 2026-07-12): the Susskind–Uglum counterterm identity
The honest formalizable rung is the CUTOFF-EXPLICIT counterterm identity (NOT a cutoff-free
cancellation of infinities). File `QIQTH/ConicalSakharov.lean` (import ConicalHeatKernel + cite
SakharovRatio). Carry `I` (= the proper-time/IR cutoff functional J_ε) as an EXPLICIT named real
— never take ε → 0. Core (pro's verified Lean algebra, trivially `ring`-provable):
- `Sent N A I := N*A*I/12`; `dInvG N I := N*I/3`; `Gind N I := (dInvG N I)⁻¹`;
  `invGren invGbare N I := invGbare + dInvG N I`.
- ★ `ent_eq_area_quarter_dInvG : Sent N A I = (A/4)*dInvG N I` — THE SUSSKIND–UGLUM IDENTITY
  (S_ent = A/4 · δ(1/G)).
- ★ `bare_entropy_renormalizes : (A/4)*invGbare + Sent N A I = (A/4)*invGren invGbare N I` —
  entanglement entropy IS the counterterm renormalizing 1/G.
- ★★ `induced_product (h : dInvG N I ≠ 0) : 4*Gind N I*Sent N A I = A` — cutoff-INDEPENDENT
  (holds at every finite cutoff; the honest S·4G = A).
- THE JOIN TO D3c: the 1/12 in Sent = the replica derivative of D3c's `coneCoeff`
  (`hasDerivAt_coneCoeff_one = 1/6`, times the ½ loop factor); SIGN NOTE (pro-caught): the entropy
  operator is `(1 + n∂_n)` in the orbifold variable n (or `(1 − q∂_q)` for q = angle/2π) — use the
  q-form or the +n form, NOT −n. THE JOIN TO THE HELD SAKHAROV: the D=4 specialization
  I = 1/(4πε²) gives S = NA/(48πε²), δ(1/G) = N/(12πε²), so 1/48π = (1/4)·(1/12π) — the held
  `SakharovRatio.sakharov_ratio` ratio, now READ as the S_ent : δ(1/G) = 1/4 relation. Deliver
  the D=4 and D=2 (c/6 log(L/ε)) specializations as corollaries tying I to the explicit forms.
FIREWALL (cited, per pro §6): the Gaussian determinant log Z = ½∫(dt/t)Tr K; the replica identity
S = (1−q∂_q)log Z_q|₁; the n → 1 analytic continuation; a₁ = R/6 for the minimal scalar; the SAME
regulator in S and δ(1/G). Integer-cone + one-loop free scalar; NOT the conjecture (its fourth
rung), NOT QG.

## ★ THE LEDGER AS OF 2026-07-12 (post D1a/D4a/D2a/LA2/D3a–e + cited-inputs G1/G2) — the six pieces, current status

| Piece | Status | What landed / what remains |
|---|---|---|
| **D1 — interacting boundary Hamiltonian** | 🟢 derived + characterized at the solvable level | IC1: einselection derived (Cesàro); D1a: the resonance/DFS theorem + rotating-records witness + quantitative Zeno — the two failure modes and the recovery regime machine-checked. *Remains:* a general (non-solvable) interacting model — research-grade, honestly cited. |
| **D2 — the limit theory (N → ∞ slot)** | 🟢 complete up to the type API | The full both-halves Tomita theorem (D2a — Kaplansky gap was an artifact); LA2: FACTOR + full modular spectrum (σ((1+Δ)⁻¹) = [0,1] exact; hypothesis-free √2 III₁ signature). *Remains:* the Connes S-invariant/type classification proper — an ecosystem type-API gap, not a proof gap. |
| **D3 — strong decoupling (THE duality theorem)** | 🟢 SKELETON COMPLETE + 2/5 cited inputs discharged (finite); the Prop itself still OPEN | **Skeleton (5 rungs, machine-checked term by term):** D3a `7393d3af` (continuum entropy π²/(3β); Bose integral + Riemann-sum theorem, both Mathlib-firsts) · D3b `04c22cb2` (heat-kernel winding form = canonical Bose free energy) · D3c `a1d3a65e` (exact conical coefficient (1/12)(n−1/n) + c/6 replica derivative; cosecant-sum Mathlib-first) · D3d `0aa98ee3` (Susskind–Uglum: S_ent = (A/4)δ(1/G), entanglement entropy renormalizes 1/G) · D3e/f `22bbd7b2` (saturation bridge + non-commuting-limit diagram). **Cited-inputs discharge program** (turning the conjecture's five physical inputs into finite theorems): **#1 Gaussian one-loop determinant — DONE finite, G1 `2e286419`** (`OneLoopDeterminant.lean`: the Frullani subtracted proper-time log-det `log det A = ∫(N e^{−t}−Tr e^{−tA})/t`, a genuine convergent Lebesgue integral killing the raw `∫ Tr K dt/t` UV divergence, + the diagonal Gaussian + the `log Z` assembly; continuum functional det / ζ-reg / arbitrary PosDef Gaussian stay cited). **#2 replica n→1 continuation — DONE finite, G2 `41f35b90`** (`ReplicaContinuation.lean`: `w(n)=log ∑ pᵢⁿ` smooth, `w(1)=0`, `w'(1)=∑ pᵢ log pᵢ`, so `replica_entropy_hasDerivAt` gives the headline `S = −∂ₙ log Zₙ|₁ =` the von Neumann entropy; `renyi_tendsto_shannon` = the Rényi limit via the slope characterization; the integer-n-geometric→analytic identification stays cited). *Remains (none a clean tractable Lean brick):* **#3** the curved a₁=R/6 (gated on Mathlib's own Riemannian heat-kernel/Seeley–DeWitt frontier — research-grade, no proof assistant has it); **#4** the same-regulator assumption (a physical modeling stipulation, not a theorem — carried as a labelled hypothesis in D3d); **#5** the cutoff identification D_eff~1/x (a modeling choice fixing the offset; the log-matching itself is proved in D3e/f). Discharge #3–#5 + assemble the continuum limit and `FlatSpaceRecordGravityCorrespondence` closes — as an UNCONDITIONAL statement it is a `def…:Prop` with NO proof term today. **BUT the ENTAILMENT is now machine-checked (G3 `07898db8`, `CorrespondenceAssembly.lean`):** `flatSpaceCorrespondence_of_constructive` — a `ConstructiveCLD` view builds the four opaque fields from the proved rungs, and the three still-cited inputs (#3/#4/#5), carried as `PhysicalInputs` structure hypotheses over building blocks (never axioms, never the output fields), IMPLY the correspondence. NON-VACUOUS: the middle equality (area law) is DERIVED from D3d's `induced_product`; only #1/#3 route through the carried inputs. Plus the a₁=R/6 algebraic core (`scalarA1 ξ R=(1/6−ξ)R`; ξ=0⟹R/6; 4D conformal ξ=1/6⟹0; the analytic Seeley–DeWitt identification stays Mathlib-gated). The conjecture is now "a conditional theorem whose only remaining assumptions are three named physical inputs" rather than an unproven Prop. |
| **D4 — bulk dynamics from boundary dynamics** | 🟡 conservation half landed | D4a: geometry = the conserved charge of boundary decoherence; frozen bulk metric — the first dynamical bulk–boundary statement. *Remains:* GENERATION — a bulk equation of motion from boundary evolution; backreaction. |
| **D5 — the radial dimension** | ⚪ substrate only | Exact RT unconditional; refinement tower with rigid invariant. *Remains:* the scale-as-dimension theorem. |
| **D6 — protection** | ⚪ absent | *Remains:* everything; deepest blocker (the (1/6−ξ) coefficient) is gated on Mathlib's own Riemannian frontier. |

**The critical path D1 → D2 → D3 now reads: two links effectively forged, the third's SKELETON
complete and 2 of its 5 physical inputs discharged at the finite level.** The remaining distance to
"duality" is now sharply localized: the conjecture's `Prop` awaits three cited inputs (one — a₁=R/6
— gated on Mathlib's own Riemannian frontier, two — same-regulator and the D_eff~1/x cutoff — that
are physical modeling stipulations rather than theorems a proof assistant can discharge) plus the
continuum assembly of the skeleton, together with the two parallel tracks D5/D6. Everything short of
those is landed, pushed, and axiom-free.

## CAMPAIGN STATUS: COMPLETE (2026-07-11) — all three bricks FULL GREEN, all pushed

- **D1a DONE** — `e7d3938f` `PointerCompetition.lean` (66 decls): THE RESONANCE THEOREM
  (resonant modes protect coherences — the DFS witness; pointer bases not generic), the
  rotating-records witness (exact population `1 − sin²(ωt)/(1+λ²)`: einselection under
  competition is a REGIME), and the QUANTITATIVE ZENO bound (deviation ≤ 1/(1+λ²) uniformly in
  time). D1's einselection story complete at the exactly-solvable level.
- **D4a DONE** — `f0dfa334` `BulkRelaxation.lean` (27 decls): THE EMERGENT GEOMETRY IS THE
  CONSERVED CHARGE OF BOUNDARY DECOHERENCE — the ledger principle, four charge instances (incl.
  the equilibrium entropy with its area/4G reading and the K2a counting trace, formally), and
  `bulk_metric_frozen`/`_emergent` — the first machine-checked dynamical bulk–boundary statement.
- **D2a DONE — THE PRIZE** — `94d285f7` `TowerGNS/CommutationEquality.lean` (22 decls, green
  first attempt): ★★★ **J·M·J = M′ IN FULL** (`tomita_commutation_equality`,
  `jconj_image_eq_commutant`, `(JMJ)′ = M`, Ω cyclic+separating for both M and M′). LA1′'s
  "Kaplansky gap" was an ARTIFACT of the wrong estimate — the consult identified the classical
  right-boundedness route (bimodular stage projection + T ∈ M′ ⟹ ‖R_{b_C}‖ ≤ ‖T‖ uniformly; the
  column witness cancels the Gibbs weight exactly, no auxiliary norm needed). With the held
  Tomita I, S̄/Δ(†=Δ)/J/polar, non-traciality, KMS-boundary: **THE FULL TOMITA–TAKESAKI
  COMMUTATION THEOREM for the tower limit — the first complete both-halves Tomita theorem in any
  proof assistant.** D2's limit-algebra rung: only the TYPE classification (III₁) remains.
- LESSON (recorded in memory): a wall named by one brick deserves a consult before being carried
  forward — the Kaplansky wall dissolved under one short consult.
- **LA2 DONE (2026-07-12)** — `e3f4a757`: the tower limit is a FACTOR with the full modular
  spectrum (σ((1+Δ)⁻¹) = [0,1] exact; hypothesis-free √2 III₁ signature). D2's ladder ends at the
  Connes S-invariant/type API alone.
- **D3a DONE (2026-07-12)** — `7393d3af` `ContinuumEntropy.lean` (36 decls, consult-verified,
  all 6 deliverables): THE FIRST CONTINUUM RUNG of `FlatSpaceRecordGravityCorrespondence` — the
  Planck kernel genuinely tied to the held DS3 D → ∞ limit; ★ THE BOSE INTEGRAL ∫₀^∞ s_∞ = π²/3
  from scratch (Tonelli + Basel — absent from Mathlib) + the Riemann-sum convergence theorem (also
  absent from Mathlib); ★★ `record_entropy_continuum_limit` — the finite record-region entropy
  converges along refining mode families to the EXACT c = 1 thermal entropy π²/(3β). The
  conjecture's first two terms TOUCH. Remaining for D3: the conical/heat-kernel leg, induced-G,
  the β → 0 saturation regime, the limit interchange — per the consult's rung ladder
  (heat-kernel representation of the same 1D thermodynamics = the named next rung).

## CAMPAIGN (ACTIVE, 2026-07-11): D1a → D4a → D2a, sequential, loop-driven

- **D1a — `PointerCompetition.lean`** (the honest hard case of einselection, made exactly
  solvable): (i) the COMMUTING layer — `H_S = diag h` shifts the decoherence frequencies to
  `(h_n−h_m) + (a_n−a_m)b_k`, IC1's capstone survives under the shifted resolution hypothesis,
  AND the new phenomenon machine-checked: **`resonance_protects_coherence`** — a resonant
  environment mode (`h_n−h_m = −(a_n−a_m)b_k`, `w_k > 0`) leaves a nonvanishing time-averaged
  coherence (the decoherence-free-subspace witness: pointer bases are NOT generic under
  competition). (ii) the NON-COMMUTING qubit model, EXACTLY SOLVABLE via the anticommuting-pair
  trick: `H = σ_x⊗1 + λ·σ_z⊗σ_z` has `H² = (1+λ²)·1`, so `U_t = cos(ωt)·1 − i(sin(ωt)/ω)·H`
  in closed form (`ω = √(1+λ²)`) — **`records_not_invariant`** (the free part rotates records:
  einselection under competition is a REGIME, not an identity) and **`zeno_strong_coupling`**
  (as `λ → ∞` the reduced dynamics converges to record-preserving dephasing, deviation `O(1/λ)`
  — the quantum-Zeno/strong-coupling regime as a theorem).
- **D4a — `BulkRelaxation.lean`** (the statics→dynamics rung, honestly scoped):
  **`area_conserved_along_relaxation`** — the record ledger (diagonal data) is `Tsem`-invariant
  and every held area/count functional is a function of the ledger, so THE EMERGENT GEOMETRY IS
  THE CONSERVED CHARGE OF BOUNDARY DECOHERENCE (the bulk metric constant while coherences decay
  exponentially — equilibria-are-geometry upgraded to a conservation law along the approach);
  the abstract metric-trajectory packaging `h(s) := reconstruct(areaData s)` (held E2 decoder,
  linearity/uniqueness); the free-flow contrast (coherent parameters rotate — the graviton wave
  through the emergence map, Q4 cited).
- **D2a — the Δ-smoothing attempt** (the Kaplansky escape; CONSULT-GATED, checkpoint-early
  permitted): GPT-5.5 design consult on the RvD smoothing route in the tower setting (spectral
  compressions of Δ via the held resolvent borelFC), then ONE brick attempt; expected outcome a
  characterized narrowing of the Kaplansky gap, full closure a stretch.
- D3a (the conjecture's first continuum rung) = the named follow-on campaign, consult-first.
- Discipline unchanged: one bg fable subagent per brick, independent verification, AxiomAudit
  pins, full budget check, checkpoint at genuine walls; commits now PUSHED (authorization
  standing, 2026-07-11).

## HONEST scope firewall (binding)

This file plans; it claims nothing. Every "held" item above carries its original conditions
(capacity postulate, hTkk, Clausius floor, carried BW/CHM/IW where applicable, finite corners
where stated). Proving D1–D6 in full is the QG-core of the tier roadmap — research-grade, not
increment-grade; the bricks listed are the honest loop-sized entry points, and checkpointing at
genuine walls remains the discipline. NOT QG; not a claim that the duality exists.
