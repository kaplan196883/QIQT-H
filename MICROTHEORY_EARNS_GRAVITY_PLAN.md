# MICROTHEORY EARNS GRAVITY — the campaign (joins between theorems we already hold)

**Status:** ACTIVE (2026-07-02). **Goal:** make the QIQT-H microtheory *earn* its gravity: discharge BW for the
free field (E1), reconstruct the graviton FROM the code's area data (E2), derive the in-model area law from
entanglement counting (E3), and land the first dynamics rung — code equilibrium ⟹ first law ⟹ Einstein (E4).
Code-audited 2026-07-02: each increment is a JOIN between existing theorems (listed per increment), not a
from-scratch build. Deser self-sourcing (E5) follows.

## Honest labels (scope, not difficulty)
Free field · linearized · flat background · finite/model level. E3 moves the calibration from an area LABEL to
ENTANGLEMENT weights — the local calibration stays an explicit hypothesis (deleting it entirely = the continuum
Type II trace + background independence, out of scope here). NEVER claim QG solved. All increments: NO sorry,
std-3, budget 0, one commit each, honest labels.

## Increments

- [x] **E1 ✅ LANDED (`QIQTH/FreeFieldWedgePackage.lean`, [AF] std-3, wired+pinned, budget 0) — BW discharged into the bridge (the free-field wedge package).**
  HELD: `oneParticleBW_niceWedge_unconditional` (Fock/CyclicWitness:701) — `∀ t, modUnitary S t = V t` at the
  OPERATOR level for the free-field nice wedge (`V t = boostUnitary (2πt)`); `WedgeBoostPackage` (WedgeBoostClausius)
  needs only the statewise `hBW`.
  BUILD: `freeFieldWedgePackage (hm : 0 < m) ξ : WedgeBoostPackage (niceWedgeStandardSubspace …) ξ` with
  `boost := V`, `hBW := fun t => by rw [oneParticleBW_niceWedge_unconditional …]`; corollary
  `freeField_clausius_unconditional` — the wedge Clausius datum `δ⟨K_boost⟩ = −δS` FORCED with **no BW
  hypothesis** (only the domain/spectral conditions). One carried input of the bridge deleted for the free field.
- [x] **E2 ✅ LANDED (`QIQTH/AreaDecoder.lean`, [AF] std-3, wired+pinned, budget 0) — the graviton reconstructed from the code's area data (invert A2).**
  HELD: `area_probes_separate` (injectivity), `areaVar_ray` (`δA_ray(v) = ½ h(v,v)`), the G2 decoder frame
  `eq_zero_of_decoder`/`separating_of_decoder` (EmergentDynamics:67 — built to receive exactly this instance).
  BUILD: the explicit decoder — `reconstruct (A : (Fin 4 → ℝ) → ℝ) : Matrix (Fin 4) (Fin 4) ℝ` with
  `h_ii = 2·A(e_i)`, `h_ij = A(e_i+e_j) − A(e_i) − A(e_j)`; theorems `reconstruct_areaVar` —
  `reconstruct (fun v => areaVar (raySurf v) h) = h` for symmetric `h` (THE METRIC IS A FUNCTION OF THE CODE'S
  AREA DATA — the A2 map inverted), and `reconstruct_unique` (via `area_probes_separate`). The emergent `h` is
  then *defined* from area measurements; A1 (`einsteinSymbol`) applies to it verbatim.
- [x] **E3 ✅ LANDED (`QIQTH/CalibratedAreaLaw.lean`, [AF] std-3, wired+pinned, budget 0) — the in-model area law from entanglement counting (the join).**
  HELD: count side `shannon_le_log_card`/`vonNeumannEntropy_le_log_card` (+ max-entropy equality at uniform);
  geometry side Track C `cut` + `entropy_le_cut` (EmergentSpacetime:214, the finite RT `S_vN ≤ cut`);
  code side `area_law_of_packing`/`area_law_saturation` (equality in the tight sector); coefficient
  `sakharov_ratio`.
  BUILD: the identification theorem — for a screen whose links carry ENTANGLEMENT weights `w` (Track C data, not
  an `areaWt` label), under the local calibration `logDim e = w e/(4G)` (the packing saturation stated on
  entanglement weights): `log #microstates = cut(w, S)/(4G)` — max-entropy count = entanglement min-cut over 4G,
  with the uniform-state witness realizing the count (the equality case of `shannon_le_log_card`). Plus the
  strict version: without calibration the count is unbounded at fixed cut (ride
  `codeCap_unbounded_at_fixed_area`). The Strominger-shape move: count and geometry as two computations, agreeing
  under the stated local calibration — the calibration now lives on entanglement data, not an area label.
- [x] **E4 ✅ LANDED (`QIQTH/CodeEquilibrium.lean`, [AF] std-3, wired+pinned, budget 0) — dynamics rung one: code equilibrium ⟹ first law ⟹ Einstein.**
  HELD: `finiteCorner_firstLaw` (ModularEnergyBound:128 — first law `δS = δ⟨K⟩` AS relative-entropy stationarity
  `D′ = 0`), `relEntropy_eq_zero` rigidity, `bridge_firstLaw_iff_einstein` (ASM — waits for exactly this input).
  BUILD: a concrete update rule — `evolve : ℝ → Matrix n n ℂ` a state path with `D(ρ_t‖σ)` non-increasing and
  stationary at `ρ_0 = σ` (e.g. the explicit interpolation path already used in B4); theorem
  `equilibrium_firstLaw` — at a stationary point of the relative-entropy flow the first law holds
  (`finiteCorner_firstLaw` instantiated on the concrete path); capstone `code_equilibrium_einstein` — chaining
  into `bridge_firstLaw_iff_einstein`: a code family at relative-entropy equilibrium at every probe satisfies
  linearized Einstein (the other ASM inputs carried as before).
- [ ] **E5 (follow-on) — the Deser rung:** the graviton's own stress symbol (quadratic in `h`, from the A1
  symbols) sourced back through the B1 coupling — second-order self-consistency, first order of the bootstrap.

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0; AxiomAudit
pins; wire `QIQTH.lean` for new modules; ONE commit on main + `Co-Authored-By: Claude Opus 4.8
<noreply@anthropic.com>`; push schannel; update this checklist + `LEAN_RESULTS_INVENTORY.md`. Consults:
`mcp__OpenAI__ask` model `gpt-5.5-pro`.

## Progress log
- **2026-07-02** — plan created from the code audit. **GPT-5.5-pro verification: RECOMMEND IMPLEMENTATION**
  (E1/E2 ready; E2 math confirmed). REQUIRED EDITS (all binding):
  (E1) "no BW hypothesis" = no external BW premise; domain/regularity premises remain; check boost sign.
  (E2) vector-indexed probes (raySurf is vector-level — OK); REQUIRE symmetry; label = pointwise tensor
  reconstruction in a basis, NOT a smooth global metric.
  (E3) **the wEnt formulation**: calibration `logDim e = wEnt e` (Track C entropy weights); DEFINE
  `screenArea := 4G·cut(wEnt,S)` (area INDUCED from calibrated entanglement capacity); conclude
  `log #microstates = screenArea/(4G)`. Name it `calibrated_entanglement_cut_area_law` — genuine formal progress
  (one weight family does both jobs; the separate areaWt label deleted) but NOT a derivation of area from
  entanglement (the calibration carries the physics). Require `G > 0`, finite nonempty state spaces, the
  cut-indexing lemma (no double count), classical uniform witness (`shannon_le_log_card` equality), keep the
  no-calibration guard.
  (E4) ONE path is NOT enough: build `RayPathFamilyRealizes h` (a per-ray state-path family, each stationary at
  its reference, realizing the ray-probe first-law datum) ⟹ `FirstLawAtEveryRay h` ⟹
  `bridge_firstLaw_iff_einstein.mp`. Add the EXPLICIT sign adapter between `δS = δ⟨K_σ⟩`
  (`finiteCorner_firstLaw`) and the Clausius form `δ⟨K⟩ = −δS` (K_boost = −K_σ orientation) — never implicit.
  E3/E4 capstone claims BLOCKED until the scaling + universal-ray/sign edits are in the code.
- **2026-07-02 — E1 ✅ LANDED**: freeFieldWedgePackage (hBW = theorem via oneParticleBW_niceWedge_unconditional) + freeField_clausius_unconditional (Clausius datum forced, NO BW premise). NEXT → E2.
- **2026-07-02 — E2 ✅ LANDED**: the explicit decoder (reconstruct: h_ii=2A(e_i), h_ij=A(e_i+e_j)−A(e_i)−A(e_j)); reconstruct_areaVar (the metric IS a function of the code's area data, A2 inverted) + reconstruct_unique. Pointwise, basis-level, symmetry required (verifier labels). NEXT → E3.
- **2026-07-02 — E3 ✅ LANDED**: calibrated_entanglement_cut_area_law (wEnt formulation per the verifier: screen_cut_eq cut-indexing lemma; inducedScreenArea := 4G·cut(wEnt,S); log #microstates = screenArea/4G under the carried calibration log D_e = wEnt e; uniform_realizes_area_law equilibrium witness; guard kept). NEXT → E4.
- **2026-07-02 — E4 ✅ LANDED**: RayPathFamilyRealizes (per-ray equilibrium family, one path per ray) ⟹ rayFamily_firstLaw (B4′ stationarity at every probe) ⟹ code_equilibrium_einstein (bridge_firstLaw_iff_einstein.mp); clausius_sign_adapter explicit (K↦−K). NEXT → E5 (Deser rung).
