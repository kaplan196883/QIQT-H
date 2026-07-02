# THE KEYSTONE — THE COUNT (K0–K6): the remaining QG-shaped problem, laddered honestly

**Status:** ACTIVE (2026-07-03). **GPT-5.5-pro-VERIFIED** (recut binding below). **Goal:** derive, rather
than posit, that a diamond/screen algebra's renormalized entropy against the CONSTRUCTED Type II trace τ₀
equals induced area/4G — deleting, in the finite branch, `hClausius`/`hGeom`, the calibration
`log D_e = wEnt e`, and the emergence join `hJoin` at once. The reachable core is the FINITE RECORD CORNER
OF THE HELD CROSSED-PRODUCT CORE; the continuum walls are named, permanent parts of the plan.

## Binding corrections (from the verdict — never violate)
- **The calibration deletes ONLY trace-defined:** the theorem is for `wEntτ e := Real.log (τdim τ₀ P_e)`
  (then `τdim P_e = D_e` is PROVEN in the code instance). An EXTERNAL geometric `wEnt` matching `log D_e`
  is the old calibration — never count it as deleted; state `count_matches_external_weights_iff` honestly.
- **`hJoin` deletes ONLY for the count-built area operator** (`areaTotOpτ` built from τ₀ dimensions — the
  join by construction). Matching the EXTERNAL `areaTotOp` of Q5 remains a genuine wall (Wall 1).
- **UNNORMALIZED counting trace** (`τ(1) = N_C = Π D_e`) — a normalized trace kills the count.
- **The dual action SCALES the count**: the honest K5 covariance is `S_{τ₀}(θ_s P) = S_{τ₀}(P) − s`
  (transported area), invariance only for trace-PRESERVING code/Lorentz unitaries.
- **CUT from the critical path:** a truncated/discretized clock (the continuous log-clock has exact `Iexp`
  masses); any finite-Type-II factor-classification claim (the count needs the TRACE, not classification);
  exact count for arbitrary real external weights (false without realizability `e^{w} ∈ ℕ` — an asymptotic
  block-code approximation is a separate later campaign); σ-weak/vN normal weights; external-area matching;
  the value of G (enters only as the area normalization — permanent).
- **Ordering:** K0 → K2a → K2b → K5 → K1 → K3(finite only) → K4(walls doc). K1 must NOT block K2.

## Increments
- [x] **K0 — the finite trace-entropy lemmas** ✅ DONE (`QIQTH/Keystone.lean`): the generic `Sren` over a trace
  functional; **`Sren_maxMixedOn_projection`** (`S(maxMixed on P) = log τ(P)`); the maximality bound
  `Sren_le_log_tau_support` and the equality-iff (prevents claiming equality for non-maximal states).
- [ ] **K2a — the standalone finite count**: `LinkDims`/`Micro`/`card_micro` (`= Π D_e`); `DiamondAlg` =
  matrix algebra on microstates; the UNNORMALIZED `tauCount = Matrix.trace`; `recordProj` with
  `tau_recordProj = R.card` and `tau_top = N_C`; `wEntτ e := log D_e` (trace-defined); `log_N_eq_cutτ`;
  **`K2a_count_capstone`**: `Sren tauCount (maxMixed) = inducedScreenAreaτ/(4G)` — the count as a THEOREM
  with `G` entering only through the normalization.
- [ ] **K2b — the τ₀ realization (THE COUNT in the held core)**: the clock cutoff
  `clockCutOfMass r := 1_{(−∞, log r]}` with **`Iexp_clockCutOfMass = r`** (`∫_{−∞}^{log r} e^x dx = r`);
  the core embedding `coreEmbed x := π(x)·q_{N_C}(L)` (t = 0 monomials, uniform matter state
  `ω = Tr/N_C`); **`tau0_coreEmbed_eq_tauCount`** (`τ₀(π(x)q_C(L)) = Tr x` — the counting trace IS the
  restriction of the constructed τ₀, not a new postulate); `tau0_core_recordProj_eq_card`;
  **`K2b_tau0_capstone`**: `S_{τ₀}(record corner) = inducedScreenAreaτ/(4G)`; `link_tauDim_eq_D` +
  `wEntτ_eq_log_tauDim` — **the calibration is a theorem because the weight is trace-defined**; the
  honest `count_matches_external_weights_iff` for external weights.
- [ ] **K5 — the covariance checks**: `TracePreservingUnitary` + `Sren_cov_tracePreserving` +
  `tauCount_unitary_conj` (code unitaries preserve the count — Gate-3's finite instantiation); the
  DUAL-SCALING law `tau0_dual_scaled_dim` (`τ₀(θ_s P) = e^{−s}τ₀(P)`, from the held exact scaling) +
  **`K5_dual_covariant_count`** (`S(θ_s·) = S(·) − s` — covariance with transported area, NOT naive
  invariance).
- [ ] **K1 — the operator packaging** (do not block K2): clock cutoffs as OPERATORS via the held
  boundedFC on the clock representation (`fL`), `fL_indicator`, the covariance via held `borelFC_conjU`;
  the operator-level monomial trace `tau0_monomial_operator`; the dense-core functional
  (linear + tracial + positive) — restrict to the normal-form corner if quotienting fights back.
- [ ] **K3 — finite closure hygiene ONLY**: bounded tracial functionals extend to norm closures of finite
  corners; the finite-corner `DualWeightTraceExtension` instance. NOT the vN/normal-weight tower.
- [ ] **K6 — checkpoint (the two honest sentences, verbatim in the module docstring + inventory):**
  HAVE: "every finite code screen realized as a finite record corner of the constructed crossed-product
  core has S_{τ₀} = log dim_{τ₀}(𝒟_C) = Σ_e log dim_{τ₀}(P_e) = A_τ(C)/4G; in the code instance
  dim_{τ₀}(P_e) = D_e, so the calibration is a theorem (trace-defined weight) and the count-built area
  operator gives the join by construction — no hClausius/hGeom/hCalib/hJoin carried in this branch."
  HAVE NOT (Walls 1–5, named): continuum QFT diamond algebras ARE these corners; external geometric
  area = count-built area; Type III₁/II_∞ continuum structure in Lean; σ-weak/normal weights; the value
  of G. Delete the loop; paper/website sync on request.

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0;
AxiomAudit pins; wire `QIQTH.lean`; ONE commit + `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`;
push schannel; update this checklist + `LEAN_RESULTS_INVENTORY.md`. HONESTY: the deletions hold in the
FINITE BRANCH exactly as scoped; the walls stay named; NEVER claim QG solved or the continuum count done.
NEVER claim an increment too hard — attempt, iterate, checkpoint only after a genuine failed attempt with
the error shown. Check for sibling jobs before each increment. Consults: `mcp__OpenAI__ask` gpt-5.5-pro
(do NOT expose the key).

## Progress log
- **2026-07-03** — plan created from the GPT-5.5-pro keystone consult (K2 recut: trace-defined weights or
  nothing; unnormalized trace; dual action SCALES the count; the cut list; ordering K0→K2a→K2b→K5→K1→K3;
  the two-sentence honest checkpoint fixed verbatim). NEXT → K0.
- **2026-07-03** — **K0 LANDED** (`QIQTH/Keystone.lean`, axiom-free std-3, budget 0): `maxMixed = N⁻¹·1`
  (unnormalized counting trace) with `maxMixed_isDensity`; `maxMixed_eigenvalues` (constant spectrum via
  the eigenvector-basis relation); CAPSTONES `vonNeumannEntropy_maxMixed` (S = log N — the entropy half
  of the count) + `vonNeumannEntropy_le_log_card` (the Gibbs guard: equality only at maximal mixing,
  riding the held classical bound). NEXT → K2a (the standalone finite count).
