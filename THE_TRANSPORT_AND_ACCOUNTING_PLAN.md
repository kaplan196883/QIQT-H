# THE TRANSPORT + THE ACCOUNTING (B1–B8 · A1–A4): two tracks, one campaign

**Status:** ACTIVE (2026-07-06). **FABLE-5-CONSULT-VERIFIED (self-consult, high reasoning; all held
APIs read, all Mathlib names verified against the pin).** **Track B (THE MODULAR TRANSPORT):** the
per-corner Gibbs modular flows transported to one one-parameter unitary group U_t on TowerGNS —
towerLimitVN gets its dynamics. **Track A (THE ACCOUNTING):** the honest maximal species upgrade —
the regulator RIGIDITY theorem (the Sakharov/Dvali FORM 1/G = N_eff·Λ² forced), the first DERIVED
heat-kernel coefficient (1D Gaussian, from Mathlib's integral), and the mixed-species consistency
chain over ONE shared datum. Order: B first (de-risks the novel construction), then A, then B7
stretch + checkpoints.

## Binding verdict (never violate)

- **B-1:** pre-level flow = `of C x ↦ of C (σ_t^C x)` at each stage's own Gibbs weights. ⋆-auto +
  φ-invariance are ONE-LINE corollaries of `sigmaDiag_gibbs_eq_alpha_rescale` + held
  `alpha_mul`/`alpha_star`/`gibbs_stationary` — NEVER touch `Complex.cpow`/`diagPow` directly
  (route entries through held `sigmaDiag_entry` + `gibbsWeight_pos`). Do NOT use
  `modAut_stateOf_invariant` (imaginary-time translate — wrong object).
- **B-2:** extension vehicle = `LinearMap.mkContinuous _ 1` + `ContinuousLinearMap.completion`
  (NO LinearIsometry.extend in the pin) — the R6→R7 recipe verbatim, incl. the induction
  incantations and `eq_adjoint_iff`. Unitarity packaged as `adjoint (U t) = U (−t)` + two-sided
  inverses + `unitary.mem_iff`.
- **B-3:** covariance `flowRaw ∘ leftMulRaw = leftMulRaw (σ_t a) ∘ flowRaw` holds EXACTLY at the
  pre-level (both sides at stage C ⊔ C'; `cornerEmbed_sigmaDiag` twice + `sigmaDiag_mul` at the
  big stage) — no germ needed.
- **B-4:** towerLimitVN invariance via `mem_towerLimitVN_iff` + a general `SOTApprox` conjugation
  lemma (‖(UTU⁻¹−UaU⁻¹)ξ‖ = ‖(T−a)(U⁻¹ξ)‖; stages map ONTO stages since σ_t bijective).
- **B-5 CUTS:** Tomita S/J/Δ of the limit; Ω-separating; analytic (strip) KMS at the limit (the
  finite-stage BOUNDARY identity IS included, docstring: "NOT strip analyticity, NOT a KMS state
  of the limit algebra"); Stone generator (B7 strong continuity = stretch, CUT-ELIGIBLE); type
  claims. Names: `towerFlow`/`flowRaw`/`flowPre`; docstring "defined by TRANSPORT, not constructed
  from a Tomita operator of the limit state". FORBIDDEN tokens: III₁/factor/ITPFI.
- **A-1 (candidate b, PRIMARY):** regulator rigidity — positive + species-additive + monotone +
  rescaling-covariant ⟹ 1/G = N_eff·Λ^κ, κ = 2 by ONE dimensional calibration; via
  `A(x) := log(F x/F 1)` + held DS5 `monotone_logValuation`. Covariance hypothesis quantifies over
  an UNKNOWN g (κ an OUTPUT — vacuity guard); ship the non-vacuity instance (effSpeciesN toy) +
  the dyadic counterexample (`Λ²(1+ε sin(2π log₂ Λ))`) in the same increment.
- **A-2 (candidate a, provable fragment ONLY):** the 1D momentum heat coefficient
  (1/2π)∫e^{−tk²}dk = 1/√(4πt) from `integral_gaussian` + the cutoff moment ∫₀^Λ 2k = Λ² from
  `integral_id`, wired into `inducedInvG`. Lattice a₁ asymptotics — CUT (no Laplace/theta in pin).
- **A-3 (candidate c):** ONE shared `SpeciesContent` feeding BOTH S_ent = A·(Σnᵢcᵢ)Λ²/48π AND
  1/G = (Σnᵢcᵢ)Λ²/12π; mixed-content 1/4 + `speciesEntropy_eq_capacity` (= A/(4G)) as theorems.
- **A-4 (candidate d, miniature Strominger–Vafa):** CUT — any 5–8-increment version is a
  manufactured equality.
- **A-5 NAMING (binding):** the c_i are "cited one-loop Seeley–DeWitt heat-kernel coefficients
  (Susskind–Uglum/Solodukhin normalization), hand-entered". No `derived_G`/`numerical_G`/bare
  `cross_check` names. Honest claim: the FORM is forced; the bookkeeping wired end-to-end from one
  shared datum; the NUMBERS stay cited.

## Increments (in order; per-increment discipline below)

- [x] **B1 — `QIQTH/TowerGNS/FlowPre.lean`** ✅ DONE: `sigmaDiag_gibbs_mul`/`_star`/`_one`,
  `stateOf_sigmaDiag_gibbs`, capstone `gnsInner_sigmaDiag` (⟪σx,σy⟫_K = ⟪x,y⟫_K) — all through
  the rescale bridge. Risk LOW.
- [x] **B2 — same file** ✅ DONE: `flowRaw t` (toModule; component = per-stage σ_t), `flowRaw_of`,
  `rawInner_flowRaw` (isometry — double DirectSum.induction_on, pure case = pairInner_embed +
  cornerEmbed_sigmaDiag both slots + gnsInner_sigmaDiag), `flowPre := mkContinuous _ 1`. Risk MED.
- [x] **B3 — `QIQTH/TowerGNS/Flow.lean`** ✅ DONE: `towerFlow t := (flowPre t).completion`, `_coe`,
  `towerFlow_zero`, `towerFlow_comp` (group law via sigmaDiag_comp + gibbsWeight_pos),
  `towerFlow_inner`, `towerFlow_adjoint` (= U_{−t}), `towerFlow_mem_unitary`. Risk LOW-MED.
- [x] **B4 — same file** ✅ DONE: `towerFlow_cyclicVec` (U_tΩ = Ω), `towerFlow_vectorState`,
  `towerState_kms_boundary` (finite-stage boundary identity, honest docstring). Risk LOW.
- [x] **B5 — `QIQTH/TowerGNS/FlowCovariance.lean`** ✅ DONE: pre `flowRaw_leftMulRaw` (EXACT),
  **`towerFlow_conj_towerRep`** (U_t π_C(a) U_{−t} = π_C(σ_t a)) — THE IMPLEMENTATION THEOREM.
  Risk LOW-MED.
- [x] **B6 — same file** ✅ DONE: `SOTApprox_conj_isometric`, `towerStageAlg_flow_invariant`, capstone
  **`towerLimitVN_flow_invariant`**. Risk LOW-MED.
- [x] **A1 — `QIQTH/Rigidity/RegulatorRigidity.lean`** ✅ DONE: `regulator_forced_power`,
  `regulator_dimension_calibration` (κ = 2), **`speciesRegulator_forced`** (the FORM forced),
  `dyadic_covariance_insufficient` witness, non-vacuity instance. Risk LOW-MED (drop the
  counterexample's monotonicity conjunct if it fights).
- [x] **A2 — `QIQTH/HeatKernelOneD.lean`** ✅ DONE: `heatDensity_oneD` (= 1/√(4πt)), `cutoff_moment`
  (= Λ²), `inducedInvG_as_integral`. Risk LOW.
- [x] **A3 — `QIQTH/SpeciesCrossCheck.lean`** ✅ DONE: `speciesEntropy`, `species_sakharov_ratio`
  (mixed-content 1/4), capstone **`speciesEntropy_eq_capacity`**; optional BTZ chain. Risk LOW.
- [x] **B7 (STRETCH, CUT-ELIGIBLE) — `QIQTH/TowerGNS/FlowContinuity.lean`** ✅ DONE (SHIPPED — cut not needed): the explicit
  weighted-sum formula for ‖(U_t−U_s)(of C a)‖², `continuous_towerFlow_of`, capstone
  `continuous_towerFlow_apply` (ε/3 + density + ‖U‖ ≤ 1). Stay norm-free on matrices. Risk HIGH;
  cut after one genuinely failed session without shame.
- [ ] **B8/A4 — checkpoints**: both HAVE/HAVE-NOT pairs VERBATIM (below) into
  `TowerGNS/Checkpoint.lean` (Track B stanza) + a Track A checkpoint comment in
  SpeciesCrossCheck.lean + LEAN_RESULTS_INVENTORY.md; plan → COMPLETE; delete the loop; stop.
  (If B7 cut: delete nothing from HAVE-B — it already hedges "unless the stretch increment
  lands"; keep the hedge only if B7 shipped, else state "no strong continuity is claimed".)

## Checkpoint sentences (verbatim at B8/A4)

TRACK A HAVE: "We have the regulator rigidity theorem — any positive, species-additive, monotone
family covariant under rescalings is forced to the Sakharov/Dvali form 1/G = N_eff·Λ^κ, with κ = 2
fixed by a single dimensional calibration and an explicit witness that weakened covariance breaks
the conclusion — together with the first derived (not cited) heat-kernel coefficient in the
repository (the 1D Gaussian a₀ = 1/√(4πt), from Mathlib's Gaussian integral) and the
mixed-field-content Sakharov consistency chain: one shared species datum feeds both the
entanglement entropy and the induced 1/G, and their ratio being 1/4 — and the entropy equalling
A/4G — are theorems with the entire species sum cancelling."

TRACK A HAVE NOT: "We do not have the numerical value of G, and we have not derived the
per-species coefficients: the c_i remain cited one-loop Seeley–DeWitt heat-kernel data,
hand-entered; no lattice area-law scaling, no one-loop integral, and no independent microstate
count is formalized — the consistency chain certifies that one shared cited datum is wired
coherently through both bookkeepings, not that either side is independently computed."

TRACK B HAVE: "We have the transported Gibbs modular flow as a one-parameter unitary group on the
tower GNS space — U_t obtained by isometric extension of the per-corner flows through the
completion, with U_0 = 1, the group law U_t U_s = U_{t+s}, adjoint U_t* = U_{−t}, invariance of
the cyclic vector U_t Ω = Ω, the implementation theorem U_t π_C(a) U_{−t} = π_C(σ_t a) at every
finite stage, and invariance of the limit von Neumann algebra towerLimitVN under conjugation by
the flow — all axiom-free."

TRACK B HAVE NOT: "We do not have the modular theory of the limit: no Tomita operator, Δ, or J on
the completion is constructed, Ω is not shown separating, no analytic (strip) KMS condition for
the limit state is proved — only the finite-stage boundary identity is displayed — no strong
continuity or Stone generator is claimed unless the stretch increment lands, and no type is
classified; U_t is defined by transport of the finite corner flows, not derived from the limit
state."

## Top-5 failure modes (mitigations binding)

1. Synonym instance mismatch → ALL working lemmas at raw ⨁; synonym crossed in application
   position only (copy LeftMul/Representation layout literally).
2. cpow side-conditions → never touch diagPow/cpow; the rescale bridge + alpha_* + sigmaDiag_entry.
3. fun_prop stalls on adjoint-mixed goals → only the two green Representation.lean shapes; derive
   adjoint from towerFlow_inner if needed.
4. B7 rabbit-hole → norm-free weighted sums; ε/3 hand-rolled; cut-eligible.
5. Track A vacuity → covariance over UNKNOWN g (κ output); non-vacuity instance + dyadic witness
   shipped in A1 itself; vacuity read before checkpoint.

## Discipline (every increment)

`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<Mod>` green; #print axioms std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit on
main + trailer `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log AND
LEAN_RESULTS_INVENTORY.md. NO sorry; carried inputs as hypotheses NEVER axioms; NEVER claim G
derived numerically, KMS of the limit, Ω separating, a type, or the continuum done; NEVER claim an
increment too hard (attempt, iterate; checkpoint only after a genuine failed attempt with the
error shown); check sibling jobs before each increment; explicit git paths only. Subagent
authoring (fable) permitted per increment with discipline kept in the main loop. Consults: Agent
tool (fable) high reasoning or mcp__OpenAI__ask gpt-5.5-pro (never expose keys).

## Progress log

- **2026-07-06** — Campaign scoped; consult verified (key discoveries: σ's ⋆-auto/φ-invariance are
  free via the rescale bridge; covariance EXACT at pre-level, no germ; no LinearIsometry.extend in
  pin → mkContinuous-1 + CLM.completion; Track A candidate (d) cut as manufactured; (a) cut to its
  provable Gaussian fragment). Loop armed.

- **2026-07-06** — **B1 LANDED, GREEN FIRST TRY** (`QIQTH/TowerGNS/FlowPre.lean`, axiom-free
  std-3, budget 0; fable subagent): `cornerFlow` (the per-corner Gibbs modular flow) with the
  FULL law kit — zero/mul/star/one/add/smul/comp, `stateOf_cornerFlow` (state invariance via
  gibbs_stationary), CAPSTONE **`gnsInner_cornerFlow`** (the GNS form is flow-invariant — the
  isometry seed for B2) and **`cornerFlow_cornerEmbed`** (T7's equivariance reoriented). Route
  compliance verified: no cpow/diagPow entry facts anywhere — everything through the rescale
  bridge + held alpha_*; add/smul by distributivity over the opaque conjugators. NEXT → B2
  (flowRaw + isometry + flowPre, same file).

- **2026-07-06** — **B2 LANDED, GREEN FIRST TRY** (FlowPre.lean extended, axiom-free std-3,
  budget 0; fable subagent): `cornerFlowₗ` (linear bundling), `flowRaw` (same-stage componentwise
  flow via toModule — NO stage shift, simpler than leftMulRaw) + `flowRaw_of`; CAPSTONE
  **`rawInner_flowRaw`** — the flow is an ISOMETRY of the pre-space (double induction; pure case
  = cornerFlow_cornerEmbed in both pairInner slots + gnsInner_cornerFlow); `flowPreₗ` +
  **`flowPre := mkContinuous _ 1`** with `flowPre_norm_eq` (‖U_t x‖ = ‖x‖ via Real.sqrt_sq).
  NEXT → B3 (Flow.lean: towerFlow on the completion).

- **2026-07-06** — **B3+B4 LANDED** (`QIQTH/TowerGNS/Flow.lean`, axiom-free std-3, budget 0;
  fable subagent, one fix — `Unitary.mem_iff` capitalized in the pin): **`towerFlow t :=
  (flowPre t).completion`** — THE ONE-PARAMETER UNITARY GROUP on TowerGNS: U_0 = 1, group law,
  isometry, **U_t† = U_{−t}** (eq_adjoint_iff + the raw neg-relation), CAPSTONE
  **`towerFlow_mem_unitary`**. Transport disclaimer in every docstring. B4:
  **`towerFlow_cyclicVec`** (U_tΩ = Ω via cornerFlow_one), `towerFlow_vectorState` (the Ω vector
  state is conjugation-invariant via adjoint_inner_left), **`towerState_kms_boundary`** — the
  finite-stage boundary KMS identity displayed through towerRep_inner_cyclicVec (honest banner:
  NOT strip analyticity, NOT a KMS state of the limit). NEXT → B5 (FlowCovariance — THE
  IMPLEMENTATION THEOREM).

- **2026-07-06** — **B5+B6 LANDED — TRACK B CORE COMPLETE** (`QIQTH/TowerGNS/FlowCovariance.lean`,
  axiom-free std-3, budget 0; fable subagent, green first build): `flowRaw_leftMulRaw` (covariance
  EXACT at pre-level — no germ, as the verdict predicted); CAPSTONE **`towerFlow_conj_towerRep`**
  — THE IMPLEMENTATION THEOREM U_t π_C(a) U_{−t} = π_C(σ_t a); `SOTApprox.conj` (general
  conjugation transport in the VonNeumann namespace); `towerFlow_norm_eq`;
  `towerStageAlg_flow_conj` (stages ONTO stages); CAPSTONE **`towerLimitVN_flow_invariant`** (+
  iff form) — THE LIMIT ALGEBRA IS INVARIANT UNDER ITS TRANSPORTED DYNAMICS. towerLimitVN now has
  its dynamics. NEXT → A1 (RegulatorRigidity — Track A begins).

- **2026-07-06** — **A1 LANDED — THE REGULATOR RIGIDITY THEOREM** (`QIQTH/Rigidity/
  RegulatorRigidity.lean`, axiom-free std-3, budget 0; fable subagent, green first build):
  `RegulatorFamily` (pos + covariance over an UNKNOWN g + mono — κ an OUTPUT, the vacuity
  guard); **`regulator_forced_power`** (F Λ = F 1·Λ^κ, via A := log F − log F 1 discharged by
  DS5's `monotone_logValuation`); `regulator_dimension_calibration` (ONE point pins κ = 2, no
  rpow-injectivity needed — log route); CAPSTONE **`speciesRegulator_forced`** — the
  Sakharov/Dvali FORM Σᵢ Fᵢ Λ = N_eff·Λ² FORCED for a shared-g family calibrated at a single
  species; **`dyadic_covariance_insufficient`** (Λ²·(2+sin(2π log₂ Λ)): dyadic covariance +
  positivity do NOT force the power form — Λ₀ = 2^{1/4} witness; monotonicity conjunct dropped
  per plan); `toyRegulator` + `toyRegulator_realizes_inducedInvG` (non-vacuity BY RFL against
  the held inducedInvG). The numbers stay cited. NEXT → A2 (HeatKernelOneD).

- **2026-07-06** — **A2 LANDED** (`QIQTH/HeatKernelOneD.lean`, axiom-free std-3, budget 0; fable
  subagent, green first build): **`heatDensity_oneD`** — (1/2π)∫e^{−tk²}dk = 1/√(4πt), DERIVED
  from Mathlib's `integral_gaussian` — THE FIRST DERIVED (not cited) HEAT-KERNEL-TYPE COEFFICIENT
  in the repository; `cutoff_moment` (∫₀^Λ 2k = Λ² via integral_id); `inducedInvG_as_integral`
  (the held Λ² realized as a momentum integral — defeq + cutoff_moment). Honest scope in the
  docstring: 1D/free/Gaussian; the 4D c_i stay CITED; no numerical-G claim. NEXT → A3
  (SpeciesCrossCheck).

- **2026-07-06** — **A3 LANDED — TRACK A COMPLETE** (`QIQTH/SpeciesCrossCheck.lean`, axiom-free
  std-3, budget 0; fable subagent, green first try): `speciesEntropy` (raw 1/48π physics form);
  **`species_sakharov_ratio`** — the MIXED-CONTENT 1/4 (the entire species sum cancels);
  CAPSTONE **`speciesEntropy_eq_capacity`** — S_ent = A/(4G) with ONE shared species datum
  feeding both sides; BONUS `btz_cardy_eq_species_entropy` (the BTZ chain cooperated). Track A
  checkpoint sentences VERBATIM in the file. NEXT → B7 (FlowContinuity stretch; cut-eligible).

- **2026-07-06** — **B7 LANDED — THE STRETCH SHIPPED** (`QIQTH/TowerGNS/FlowContinuity.lean`,
  axiom-free std-3, budget 0; fable subagent, two cycles): `cornerFlow_entry` (via the HELD
  sigmaDiag_entry — entry access only, no cpow); `norm_flowRaw_sub_of_sq` (the COLLAPSED closed
  form — re(2⟪a,a⟫ − ⟪a,σ_{−t+s}a⟫ − ⟪a,σ_{−s+t}a⟫) — instead of the raw weighted sum, per
  "pick what closes"); tendsto on pure components + pre-vectors (tendsto_finsetSum); CAPSTONE
  **`continuous_towerFlow_apply`** — ε/3 + Completion.denseRange_coe + the uniform isometry:
  **THE TRANSPORTED FLOW IS A STRONGLY CONTINUOUS ONE-PARAMETER UNITARY GROUP** on TowerGNS.
  The door to the held Spectral/Stone tower is open (the generator NOT claimed — post-campaign).
  The HAVE-B sentence keeps its stretch hedge as SHIPPED. NEXT → B8/A4 (checkpoints; delete
  loop; stop).
