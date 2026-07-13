# DUALITY ROADMAP — what separates the verified dictionary from a genuine duality

**Date:** 2026-07-13 (D3 skeleton + G1/G2 + G3 conditional theorem + D4b/D4c bulk dynamics + D5a radial
+ the Seeley–DeWitt interface; see the ledger). The conjecture is a CONDITIONAL theorem, not an
unproven `Prop`. **Companions:** `ADSCFT_GAP_ANALYSIS.md` (the mechanism-by-mechanism
comparison), `WHERE_WE_ARE.md` (the full-credit status), `FLAT_RECORD_GRAVITY_CONJECTURE.md`
(the target statement + the cited-inputs discharge ledger), `HEAT_KERNEL_GAP_PLAN.md` (the deferred
curvature wall).

## ★ STATE OF CLOSE (2026-07-13) — the tractable program is closed; the residue is three external walls

Every TRACTABLE item in this roadmap is now either a theorem or a cleanly-carried conditional (with its
hypothesis a labelled structure/argument field, never a Lean `axiom`). The **entire remaining residue is
three EXTERNAL walls**, none QIQT-H-specific, each documented and deferred:

1. **The Riemannian heat-kernel / Seeley–DeWitt theory** — surfaces 3× (D3 input #3 `a₁=R/6`, D5 warp,
   D6 curvature). Absent from every proof assistant; deferred with a phased plan
   (`HEAT_KERNEL_GAP_PLAN.md`); `a₁=R/6` carried via the `SeeleyDeWittData` interface. Its Phase 1
   (curvature) IS the live Mathlib effort (Gouëzel's Riemannian manifolds; Massot–Rothgang's
   Levi-Civita PR) — track/contribute upstream, do not fork.
2. **The von Neumann factor / type-III₁ classification API** (D2) — the Connes S-invariant / type
   classification proper; absent from every proof assistant (the tower's III₁ *signature* — σ((1+Δ)⁻¹)
   = [0,1] — is already proved; only the abstract type API is missing).
3. **General interacting matter** (D1) — a non-solvable interacting boundary Hamiltonian; research-grade,
   contains a Clay-type problem.

Everything short of those three is landed, pushed, axiom-free, budget 0. The duality/DY7 conjecture is
NOT proved — it is conditional on the carried inputs; closing the tractable work does not change that,
it makes the remaining distance exactly these three named external walls. **Definition used throughout:** a DUALITY is two independently defined
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
(`finiteEvidence_holds`); its continuum SKELETON is now machine-checked term by term (D3a–D3e/f); its
two tractable physical inputs are finite theorems (G1/G2); and its ENTAILMENT is a conditional
theorem (G3 — the three still-cited inputs, as labelled hypotheses, imply it). The UNCONDITIONAL
continuum statement remains the conjecture.
**Status:** skeleton complete · 2/5 inputs discharged · entailment machine-checked · the
unconditional Prop still open (see the ledger row). Closing it IS acquiring the duality.

### D4 — bulk dynamics from boundary dynamics
Held: statics (equilibria are Einstein states — `boundary_dynamics_equilibria_are_geometry`,
E4-conditional) and the decoder (`reconstruct` — metric from area data). D4a delivered the
CONSERVATION half (RC dephasing freezes the metric — geometry = conserved charge); **D4b delivered
the GENERATION half** (`BulkGeneration.lean`, `250210e7`): a boundary Markov population-transfer
generator Q moves the ledger, and the bulk metric velocity is the LINEAR decoder pushforward of the
rate equation `p' = Q·p` — the first machine-checked "boundary evolution generates bulk evolution."
**D4c delivered the AUTONOMY** (`BulkAutonomy.lean`, `ccb5825d`): when `ker(decoder)` is
`Q`-invariant (the intertwiner `D∘Q = Qbar∘D`), the metric velocity descends to a function of the
metric `h(s)` alone — the autonomous bulk law `HasDerivAt h (Qbar (h s)) s` — and the no-go
`no_descend_of_bad_kernel` proves the condition is necessary, not decorative. So the bulk-dynamics
KINEMATICS is complete (conservation + generation + autonomy). What remains — backreaction and the
Einstein/curved dynamical content — is the heat-kernel-gated D5-warp/D6-curvature wall (deferred),
not a separate D4 gap. (In AdS/CFT the autonomy is automatic: one Hamiltonian, two readings.)
**Status:** all three kinematic halves landed; the curved/Einstein dynamical content is the shared
heat-kernel wall, deferred.

### D5 — the radial dimension
Entanglement-at-all-scales becoming the holographic direction (Maldacena's U = RG scale). Held:
the substrate (exact RT = `maxFlow_min_cut`, unconditional; the refinement tower with its rigid
forced-weight invariant; state-decoded geometry through dS₂). **D5a delivered the scale-as-dimension
theorem** (`ScaleDimension.lean`, `ef52d8f7`): the tower's log-additive forced-weight invariant
`Λ(k) = ∑_{n<k} forcedWeight n` supplies a radial coordinate, and the held single-scale cut metric
`weightedCutDist` extends to a bulk pseudometric on `X × ℕ` (site × scale) whose SLICES are the
boundary metric and whose FIBERS are additive RG-depth geodesics — "entanglement at scale k = bulk
radial depth k" as a finite kinematic theorem. Missing: the metric content of that radial axis — an
AdS warp factor / curvature, not a chosen L¹ no-warp product.
**Status:** the radial coordinate is a KINEMATIC theorem; the warp/curvature (the geometry OF the
radial direction) remains — and its coefficient is the same `(1/6−ξ)` heat-kernel gate as D6.

### D6 — protection (what makes a dictionary RIGID)
Non-renormalization is why AdS/CFT's dictionary has fixed coefficients. No analogue exists here,
which is why `N_eff/4`, `Λ_s`, and the heat-kernel `c_i` float. The `c_i` blocker (the `(1/6−ξ)`
Seeley–DeWitt coefficient) is now HALF-crossed: its ALGEBRAIC content is a theorem (G3
`CorrespondenceAssembly.lean` — `scalarA1 ξ R = (1/6−ξ)R`, minimal scalar `⟹ R/6`, 4D conformal
`⟹ 0`), but the ANALYTIC identification `heatTraceCoeff₁ = ∫(R/6+trE)` stays gated on the
ecosystem-wide Riemannian heat-kernel gap that no proof assistant has crossed. **DECISION
(2026-07-13): the analytic derivation is DEFERRED (phased fill = `HEAT_KERNEL_GAP_PLAN.md`); until
then `a₁ = R/6` is carried via option (b) as a NAMED INTERFACE, not an ad-hoc hypothesis** —
`SeeleyDeWittInterface.lean` (`9dc0ad19`) bundles `a₀=1, a₁=R/6+trE` as a `SeeleyDeWittData` structure
(never an axiom) and sources G3's input #3 from it, so the eventual Phase-7 discharge is a SINGLE
instance; `HeatTraceAsymptotics.lean` (`3d03943a`) adds the carried short-time trace shape and PROVES
the coefficient extraction (normalized trace `→ 1`; subleading slope `→ R/6+trE`), showing the
interface is non-vacuous and isolating exactly what Phase 4 must supply. Without protection, even a
proven correspondence is a one-parameter FAMILY of dictionaries, not THE dictionary.
**Status:** absent as a mechanism; the coefficient's algebraic half is proved and its assumption is
now a clean named interface (option (b)); the analytic half's deepest blocker is external (Mathlib's
own diff-geo frontier), deferred with a plan.

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

The 2026-07-11/12 campaign bricks (D1a · D4a · D2a · LA2 · D3a–e · G1 · G2 · G3) all LANDED — see
the ledger and the campaign logs below. The current frontier, in decreasing tractability:

- **D4b — the GENERATION half of bulk dynamics** (the D4 remainder; likely the next tractable
  brick): a bulk equation of motion from boundary evolution — `h(s) := reconstruct(δA(T_s ρ))` given
  a genuine EVOLUTION law (not just D4a's conservation/frozen metric). Composable from held pieces;
  no external gate. Consult-first on the honest evolution-law statement.
- **D5a — the scale-as-dimension rung** (the D5 remainder): entanglement-at-all-scales → the
  holographic radial direction, on the held refinement tower + exact RT. The decoded bulk is
  currently spatial/single-scale; the theorem is absent, not obstructed.
- **The a₁ = R/6 ANALYTIC identification** (the D3 input #3 / D6 `c_i` remainder): the algebraic
  half is proved (G3); the analytic `heatTraceCoeff₁ = ∫(R/6+trE)` is GATED on Mathlib's absent
  Riemannian heat-kernel theory — research-grade, a Mathlib contribution, NOT increment-grade.
- **Encoding #4/#5 as physical postulates** (optional, honesty-of-record): the same-regulator and
  cutoff-identification inputs are modeling stipulations, not theorems; they are already carried as
  `PhysicalInputs` hypotheses in G3's conditional theorem — no further Lean work discharges them.

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

## ★ THE LEDGER AS OF 2026-07-13 (post D1a/D4a/D2a/LA2/D3a–e + G1/G2 + G3 + D4b + D5a + the Seeley–DeWitt interface / heat-trace-shape layer) — the six pieces, current status

| Piece | Status | What landed / what remains |
|---|---|---|
| **D1 — interacting boundary Hamiltonian** | 🟢 derived + characterized at the solvable level | IC1: einselection derived (Cesàro); D1a: the resonance/DFS theorem + rotating-records witness + quantitative Zeno — the two failure modes and the recovery regime machine-checked. *Remains:* a general (non-solvable) interacting model — research-grade, honestly cited. |
| **D2 — the limit theory (N → ∞ slot)** | 🟢 complete up to the type API | The full both-halves Tomita theorem (D2a — Kaplansky gap was an artifact); LA2: FACTOR + full modular spectrum (σ((1+Δ)⁻¹) = [0,1] exact; hypothesis-free √2 III₁ signature). *Remains:* the Connes S-invariant/type classification proper — an ecosystem type-API gap, not a proof gap. |
| **D3 — strong decoupling (THE duality theorem)** | 🟢 SKELETON COMPLETE + 2/5 cited inputs discharged (finite); the Prop itself still OPEN | **Skeleton (5 rungs, machine-checked term by term):** D3a `7393d3af` (continuum entropy π²/(3β); Bose integral + Riemann-sum theorem, both Mathlib-firsts) · D3b `04c22cb2` (heat-kernel winding form = canonical Bose free energy) · D3c `a1d3a65e` (exact conical coefficient (1/12)(n−1/n) + c/6 replica derivative; cosecant-sum Mathlib-first) · D3d `0aa98ee3` (Susskind–Uglum: S_ent = (A/4)δ(1/G), entanglement entropy renormalizes 1/G) · D3e/f `22bbd7b2` (saturation bridge + non-commuting-limit diagram). **Cited-inputs discharge program** (turning the conjecture's five physical inputs into finite theorems): **#1 Gaussian one-loop determinant — DONE finite, G1 `2e286419`** (`OneLoopDeterminant.lean`: the Frullani subtracted proper-time log-det `log det A = ∫(N e^{−t}−Tr e^{−tA})/t`, a genuine convergent Lebesgue integral killing the raw `∫ Tr K dt/t` UV divergence, + the diagonal Gaussian + the `log Z` assembly; continuum functional det / ζ-reg / arbitrary PosDef Gaussian stay cited). **#2 replica n→1 continuation — DONE finite, G2 `41f35b90`** (`ReplicaContinuation.lean`: `w(n)=log ∑ pᵢⁿ` smooth, `w(1)=0`, `w'(1)=∑ pᵢ log pᵢ`, so `replica_entropy_hasDerivAt` gives the headline `S = −∂ₙ log Zₙ|₁ =` the von Neumann entropy; `renyi_tendsto_shannon` = the Rényi limit via the slope characterization; the integer-n-geometric→analytic identification stays cited). *Remains (none a clean tractable Lean brick):* **#3** the curved a₁=R/6 (gated on Mathlib's own Riemannian heat-kernel/Seeley–DeWitt frontier — research-grade, no proof assistant has it); **#4** the same-regulator assumption (a physical modeling stipulation, not a theorem — carried as a labelled hypothesis in D3d); **#5** the cutoff identification D_eff~1/x (a modeling choice fixing the offset; the log-matching itself is proved in D3e/f). Discharge #3–#5 + assemble the continuum limit and `FlatSpaceRecordGravityCorrespondence` closes — as an UNCONDITIONAL statement it is a `def…:Prop` with NO proof term today. **BUT the ENTAILMENT is now machine-checked (G3 `07898db8`, `CorrespondenceAssembly.lean`):** `flatSpaceCorrespondence_of_constructive` — a `ConstructiveCLD` view builds the four opaque fields from the proved rungs, and the three still-cited inputs (#3/#4/#5), carried as `PhysicalInputs` structure hypotheses over building blocks (never axioms, never the output fields), IMPLY the correspondence. NON-VACUOUS: the middle equality (area law) is DERIVED from D3d's `induced_product`; only #1/#3 route through the carried inputs. Plus the a₁=R/6 algebraic core (`scalarA1 ξ R=(1/6−ξ)R`; ξ=0⟹R/6; 4D conformal ξ=1/6⟹0; the analytic Seeley–DeWitt identification stays Mathlib-gated). The conjecture is now "a conditional theorem whose only remaining assumptions are three named physical inputs" rather than an unproven Prop. |
| **D4 — bulk dynamics from boundary dynamics** | 🟢 all three: conservation + generation + AUTONOMY (conditional) | D4a: geometry = the conserved charge of boundary decoherence; frozen bulk metric. **D4b `250210e7`: the GENERATION half** — a boundary Markov (col-sums-zero) generator Q MOVES the ledger, and the bulk metric velocity = the LINEAR decoder pushforward of `p'=Q·p` (`bulk_eom`; `pExp` trajectory + `hasDerivAt_pExp`; grounded in the held `AreaMap.reconstruct`). **D4c `ccb5825d` `BulkAutonomy.lean`: the AUTONOMY** — when `ker(decoder)` is `Q`-invariant (intertwiner `D∘Q = Qbar∘D`), the metric velocity DESCENDS to a function of the metric `h(s)` alone: `HasDerivAt h (Qbar (h s)) s` (`autonomous_descend_at_clm`) — and the necessity no-go `no_descend_of_bad_kernel` proves the condition is required (kernel not Q-invariant ⟹ no descended velocity field). *Remains:* backreaction + the Einstein/curved dynamical content — that is the heat-kernel-gated D5-warp/D6-curvature wall (deferred), NOT a separate D4 gap. The bulk-dynamics KINEMATICS is now complete. |
| **D5 — the radial dimension** | 🟡 radial coordinate landed (kinematic) | Exact RT unconditional; refinement tower with rigid invariant. **D5a `ef52d8f7` `ScaleDimension.lean`:** the log-additive forced-weight invariant supplies a radial axis; `weightedCutDist` extends to a bulk pseudometric on `X × ℕ` (slices = boundary metric, fibers = additive RG-depth geodesics) — the scale-as-dimension theorem. *Remains:* the warp/curvature OF the radial direction (a chosen no-warp L¹ product here) — its coefficient is the same `(1/6−ξ)` heat-kernel gate as D6. |
| **D6 — protection** | ⚪ absent as a mechanism; the coefficient's algebraic half proved, its assumption now a clean interface | *Remains:* the non-renormalization mechanism. The `(1/6−ξ)` Seeley–DeWitt coefficient's ALGEBRAIC content is a theorem (G3 `CorrespondenceAssembly.lean`); its ANALYTIC identification (`heatTraceCoeff₁ = ∫(R/6+trE)`) is the deepest blocker — gated on Mathlib's own Riemannian heat-kernel frontier: the heat semigroup kernel, the small-`t` asymptotic expansion, the normal-coordinate parametrix, and the conical/distributional version are ALL absent from every proof assistant. This is the a₁=R/6 analytic wall (input #3 of the conjecture); a WALL, not increment-grade. **DEFERRED with a phased fill (`HEAT_KERNEL_GAP_PLAN.md`, decision 2026-07-13); option (b) now BUILT as a named interface: `SeeleyDeWittInterface.lean` (`9dc0ad19`) carries `a₁=R/6+trE` as a `SeeleyDeWittData` structure sourcing G3's input #3 (Phase-7 discharge = a single instance, not a refactor), and `HeatTraceAsymptotics.lean` (`3d03943a`) carries the short-time trace shape + proves the coefficient extraction (non-vacuous; Phase-4 obligation isolated). `a₁=R/6` CARRIED, never an axiom, never claimed derived.** |

**The critical path D1 → D2 → D3 now reads: two links effectively forged, the third's SKELETON
complete, 2 of its 5 physical inputs discharged at the finite level, and its ENTAILMENT machine-checked
(G3 — inputs ⟹ correspondence).** The remaining distance to "duality" is now sharply localized: the
conjecture's UNCONDITIONAL `Prop` awaits three cited inputs (one — a₁=R/6 — whose algebraic half is
proved and whose analytic half is gated on Mathlib's own Riemannian frontier; two — same-regulator and
the D_eff~1/x cutoff — that are physical modeling stipulations rather than theorems a proof assistant
can discharge), together with the two parallel tracks D5/D6. Everything short of those is landed,
pushed, and axiom-free — and the conjecture is now a conditional theorem, not an unproven Prop.

**Update 2026-07-13 (the frontier-bricks pass):** D4 is now BOTH halves (D4b `250210e7` — boundary
Markov flow drives the bulk metric via the linear-decoder pushforward), and D5 has its radial
coordinate (D5a `ef52d8f7` — the scale-as-dimension pseudometric on `X × ℕ`, kinematic). The
campaign then hit the SAME wall from three sides: the AUTONOMOUS bulk EOM (D4), the WARP/curvature of
the radial axis (D5), and the a₁=R/6 ANALYTIC coefficient (D6 / conjecture input #3) all reduce to
the missing Riemannian heat-kernel / Seeley–DeWitt theory — absent from every proof assistant. That
is the honest single remaining obstruction on this front: **the geometry OF the emergent directions
(their curvature), gated on Mathlib's own differential-geometry frontier.** The kinematics — where
the directions are, how entanglement lays them out, how boundary flow moves them — is machine-checked.

**Update 2026-07-13 (the wall, parked cleanly):** rather than force the wall, it is DEFERRED with a
phased fill plan (`HEAT_KERNEL_GAP_PLAN.md`) and the `a₁ = R/6` assumption is now carried the clean
way — option (b) as a NAMED INTERFACE: `SeeleyDeWittInterface.lean` (`9dc0ad19`) makes `a₁=R/6+trE` a
`SeeleyDeWittData` structure feeding G3's conditional theorem, so the eventual discharge is a single
instance; `HeatTraceAsymptotics.lean` (`3d03943a`) carries the short-time trace shape and proves the
coefficient extraction (non-vacuous; the Phase-4 obligation isolated). Nothing is claimed derived —
`a₁=R/6` is a labelled interface field, never an axiom. The wall is documented, the assumption is
named, and the derivation waits behind the plan until the rest of the program closes.

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
