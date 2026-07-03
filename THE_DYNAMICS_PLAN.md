# THE DYNAMICS (DY1–DY7): the code's time evolution + the independent cross-check + the conjecture

**Status:** ACTIVE (2026-07-03). **GPT-5.5-pro-VERIFIED** (binding verdict below). **Goal:** give the
microscopic side (the capacity-bounded record code = the truncated field diamond, THE EMBEDDING's
object) a TIME EVOLUTION — the diagonal code Hamiltonian `H = Σ_k ω_k N_k`, its Heisenberg flow,
explicit Gibbs/KMS states, mode-region entropies — with the declared destination the INDEPENDENT
CROSS-CHECK (the QIQT-H analogue of Brown–Henneaux = Cardy: the saturated region entropy equals the
induced-gravity area/4G with the proof NOT using the trace/wEnt calibration), and the sharp
flat-space record-code/gravity correspondence packaged as a named Lean `Prop` (never an axiom).
Files: `lean/mathlib/QIQTH/Dynamics.lean` (DY1–DY5), `QIQTH/CrossCheck.lean` (DY6, calibration-free),
`QIQTH/Conjectures.lean` (DY7).

## Binding verdict (from the consult — never violate)
- **Diagonal Hamiltonian route, NOT transported modAut**: the physical flow must be
  state-independent (modular flow depends on ρ_β and trivializes at β = 0); `modAut` is only the KMS
  certificate AFTER the Gibbs density is built. Define `energy n = Σ ω_k n_k`,
  `phaseUnitary t = diag e^{itE(n)}`, `alpha t A = U_t A U_{−t}` — no Stone, no unbounded operators,
  no Matrix.exp, no spectral calculus. Everything via the ENTRY FORMULA
  `α_t(A)(n,m) = e^{it(E(n)−E(m))} A(n,m)`.
- **The honesty point on dynamics**: H is a function of the N_k, so the diagonal record algebra is
  FIXED by the flow (records are stationary); the nontrivial dynamics lives on the off-diagonal
  coherences and ladders (`α_t(a_k) = e^{−iω_k t} a_k`).
- **Gibbs = explicit product diagonal density** (per-mode `Z_k`, `p_k`, entrywise product); KMS via
  the BRIDGE `σ_s^{ρ_β} = α_{−βs}` into the held FiniteModularTheory (never defining α by modAut);
  β = 0 is the tracial case (cyclicity).
- **Region = subset of MODE labels** (not a spatial subregion — say so); the reduced Gibbs state
  factorizes; `S_micro(R,β) = Σ_{k∈R} s_{D_k}(βω_k)`; at β = 0 it is Σ log D_k with the ≤ bound for
  all β. NO claim of spatial area-law entanglement (the Gibbs product state has none).
- **The cross-check verdict: option (ii)** — the SATURATED CONDITIONAL SAKHAROV CHECK, with the β→0
  recovery as a lemma and the continuum one-loop equality as the named frontier. `InducedCrossCheckData`
  (Aind, Neff, Λs, Gind + `quarterG_eq_primitives` + `speciesCellMatch`) supplies the macro side
  INDEPENDENTLY; prove `S_micro(R,β) ≤ Aind/4Gind` and `S_micro(R,0) = Aind/4Gind`. The PROOF may
  import Dynamics + InducedNewtonConstant + SakharovRatio and must NOT reference `wEntTau`, `cutTau`,
  `inducedScreenAreaTau`, `tauMonomial`, or `hJoin` (the keystone calibration = the shared-calibration
  trap; the type-level import of Micro/DiamondAlg is unavoidable — the ban is on the CALIBRATION
  identifiers, enforced by grep + module docstring). NO arbitrary-β equality claim (false as β→∞).
- **The conjecture packaging**: a `QIQTH.Conjectures` namespace — `FlatRecordGravityFiniteEvidence`
  (a Prop structure bundling the finite evidence), `FlatSpaceRecordGravityCorrespondence` (the
  continuum claim as a def/Prop over `ContinuumLimitData`), and a package whose `continuumClaim` is a
  Prop-valued FIELD-FREE def — NO proof field, NO axiom, NO typeclass instance, mirrored verbatim in
  docs.
- **CUT**: transported-modular-flow-as-definition; Stone/unbounded/Matrix.exp/spectral FC;
  interacting or mode-mixing Hamiltonians; spatial-entanglement claims for the Gibbs product state;
  arbitrary-β equality with A/4G_ind; deriving heat-kernel coefficients in the finite file; keystone
  calibration identifiers in the cross-check proof; closed-form geometric-series Z unless trivial;
  PROVING the correspondence conjecture; conjecture-as-instance/axiom.

## Increments
- [x] **DY1 — the diagonal dynamics core** ✅ DONE (`QIQTH/Dynamics.lean`): `energy`, `Hcode` (with
  `Hcode_apply_diag`), `phaseUnitary` (group law), `alpha` with the ENTRY FORMULA `alpha_entry`;
  `alpha_zero`/`alpha_add`/`alpha_mul`/`alpha_star`; the actions — `alpha_diagonal` (records/number
  operators/occupation projectors STATIONARY) and `alpha_modeLowering`/`alpha_modeRaising`
  (`α_t(a_k) = e^{−iω_k t}·a_k`, `α_t(a_k†) = e^{iω_k t}·a_k†` — the nontrivial dynamics).
- [x] **DY2 — the explicit Gibbs product density** ✅ DONE: `ZMode` (positivity), `pMode` (normalization),
  `gibbsDensity` (entrywise product diagonal); `gibbs_isDensity`; `gibbs_stationary`
  (α_t-invariance).
- [x] **DY3 — the finite KMS bridge** ✅ DONE: `sigmaDiag_gibbs_eq_alpha_rescale` (σ_s^{ρ_β} = α_{−βs}, up
  to the held sign convention) ⟹ `gibbs_kms_condition` from FiniteModularTheory; the tracial β = 0
  lemma separately.
- [x] **DY4 — the mode-region reduction** ✅ DONE: reduction to `R : Finset Mode` (finite
  marginalization); the reduced Gibbs density is diagonal and product over `k ∈ R`.
- [x] **DY5 — the region entropy formula** ✅ DONE: diagonal-vN = Shannon for these densities; product
  additivity; `thermalModeEntropy` + `S_micro_eq_sum_mode`; `S_micro_zero` (= Σ log D_k) +
  `S_micro_le_count` (≤, all β).
- [x] **DY6 — the saturated induced cross-check** ✅ DONE (`QIQTH/CrossCheck.lean`, CALIBRATION-FREE):
  `InducedCrossCheckData` (the macro side as independent Sakharov/species/cell data);
  **`S_micro_le_inducedQuarterG`** (all β) + **`S_micro_zero_eq_inducedQuarterG`** (saturation) —
  the proofs referencing NO keystone calibration identifier (grep-checked).
- [ ] **DY7 — the conjecture package + checkpoint** (`QIQTH/Conjectures.lean`):
  `FlatRecordGravityFiniteEvidence`, `FlatSpaceRecordGravityCorrespondence`,
  `FlatRecordGravityPackage.continuumClaim` (no proof field, no axiom); the docs mirror. Then the
  checkpoint (the two honest sentences, VERBATIM in the module docstring + inventory): HAVE: "a
  finite, axiom-free diagonal code dynamics, explicit Gibbs/KMS states, product-mode reductions, and
  a saturated conditional induced-gravity cross-check whose proof does not use the trace/wEnt area
  calibration." HAVE NOT: "a finite proof of a continuum one-loop heat-kernel area law or an
  equality between finite thermal entropy at arbitrary β and an induced geometric area; that remains
  the named continuum frontier/conjecture." Delete the loop; paper/website sync on request.

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0;
AxiomAudit pins; wire `QIQTH.lean`; ONE commit + `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`;
push schannel; update this checklist + `LEAN_RESULTS_INVENTORY.md`. HONESTY: records are stationary
under this flow (say so); region = mode subset, no spatial entanglement claims; the cross-check is
CONDITIONAL and SATURATED (β = 0), never arbitrary-β; the continuum one-loop law is the named
frontier; NEVER claim QG solved or a wall crossed. NEVER claim an increment too hard — attempt,
iterate, checkpoint only after a genuine failed attempt with the error shown. Check for sibling jobs
before each increment. Consults: `mcp__OpenAI__ask` gpt-5.5-pro (do NOT expose the key).

## Progress log
- **2026-07-03** — plan created from the GPT-5.5-pro dynamics consult (diagonal-H route, entry-formula
  proofs, explicit Gibbs products, KMS via bridge, region = mode subset, the saturated conditional
  cross-check in a calibration-free module, the conjecture as a named Prop package; the cut list;
  ordering DY1→DY7). NEXT → DY1.

- **2026-07-03** — **DY1 LANDED** (`QIQTH/Dynamics.lean`, axiom-free std-3, budget 0): energy/Hcode
  (Hcode_apply_diag — H diagonal with entry E(n) = Σ ω_k n_k); phaseUnitary (group law) + alpha with
  THE ENTRY FORMULA alpha_entry (e^{it(E(n)−E(m))}·A(n,m) — no Stone, no Matrix.exp);
  alpha_zero/add/mul/star (a one-parameter group of ⋆-automorphisms); alpha_diagonal — RECORDS ARE
  STATIONARY (H a function of the N_k, the honesty point stated); CAPSTONE
  alpha_modeLowering/Raising — the nontrivial dynamics: α_t(a_k) = e^{−iω_k t}·a_k,
  α_t(a_k†) = e^{iω_k t}·a_k†. NEXT → DY2 (the Gibbs product density).

- **2026-07-03** — **DY2 LANDED** (axiom-free std-3, budget 0): ZMode (positive per-mode partition
  function); pMode (normalized Boltzmann weights); gibbsWeight (the product weight — positive,
  normalized via the product-sum interchange Fintype.piFinset_univ + Finset.prod_univ_sum);
  gibbsDensity (explicit product diagonal — NO matrix exponential); CAPSTONE gibbs_isDensity (PSD +
  unit trace); gibbs_stationary (tr(ρ_β·α_t(A)) = tr(ρ_β·A) — the flow preserves the diagonal and
  ρ_β is diagonal). NEXT → DY3 (the finite KMS bridge).

- **2026-07-03** — **DY3 LANDED** (axiom-free std-3, budget 0): sigmaDiag_entry (the diagonal modular
  flow's entry formula at a positive weight, via cpow → exp/log); log_gibbsWeight
  (log w = −βE − Σ log Z); CAPSTONE sigmaDiag_gibbs_eq_alpha_rescale — σ_s^{ρ_β} = α_{−βs} (the
  partition function CANCELS between the two diagonal conjugations; only the energy differences
  survive — the flow is never defined by modAut, per the verdict); gibbsInvertible (explicit diagonal
  inverse) + gibbs_kms_condition (the held finite Tomita–Takesaki KMS applied to the explicit
  density); gibbsDensity_zero_eq_maxMixed (the tracial β = 0 case: the thermal tower and the keystone
  counting tower share their ground floor). NEXT → DY4 (the mode-region reduction).

- **2026-07-03** — **DY4 LANDED** (axiom-free std-3, budget 0): restrictMicro + marginalWeight
  (region = subset of MODE labels; everything diagonal ⟹ reduction = CLASSICAL marginalization, no
  operator partial trace); CAPSTONE marginal_gibbsWeight — THE GIBBS MARGINAL IS AGAIN GIBBS (the
  complement modes sum to 1 mode-by-mode; proof via a named-f product-sum interchange over the
  occupation basis); reduced_gibbsDensity_eq (the reduced density IS the region's own Gibbs
  density — diagonal and product over k ∈ R). NEXT → DY5 (the region entropy formula).

- **2026-07-03** — **DY5 LANDED** (axiom-free std-3, budget 0, no sorry): eigenvalues_sum_diagonal
  (NEW reusable — eigenvalue sums of a real diagonal matrix are entry sums, via
  Matrix.charpoly_diagonal + roots_multiset_prod_X_sub_C) + vonNeumannEntropy_diagonal (diagonal vN
  = Shannon of the weights); modeEntropy/Smicro; shannon_gibbsWeight (product-state additivity via
  the named-kernel interchange — one log factor per mode, complement modes sum to 1); CAPSTONE
  entropy_gibbs_region — S(ρ_{β,R}) = S_micro(R,β) = Σ_k s_k(βω_k); Smicro_zero (SATURATION at
  β = 0: = Σ log D_k) + Smicro_le_count (the all-β bound via the held Shannon/Gibbs bound; NO
  arbitrary-β area equality claimed). NEXT → DY6 (the saturated induced cross-check —
  calibration-free).

- **2026-07-03** — **DY6 LANDED** (`QIQTH/CrossCheck.lean`, axiom-free std-3, budget 0,
  CALIBRATION-FREE grep-verified — the only wEntTau/cutTau/tauMonomial/hJoin mentions are the header
  documenting the ban): InducedCrossCheckData (the macro side as independent Sakharov/species/cell
  data, structure fields never axioms); ofSpecies (with the DERIVED G_ind = 1/(N_eff·Λs²) the
  quarter-G identity is the held capacity_exponent THEOREM — only species/cell matching remains
  input); S_micro_le_inducedQuarterG (all β); CAPSTONE S_micro_zero_eq_inducedQuarterG — THE
  SATURATED CONDITIONAL SAKHAROV CROSS-CHECK: S_micro(R,0) = A_ind/4G_ind, micro side from the
  Hamiltonian (DY1–DY5), macro side independent; equality at SATURATION ONLY. NEXT → DY7 (the
  conjecture package + checkpoint).
