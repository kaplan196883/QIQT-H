# THE GROUNDING CAMPAIGN — Bargmann adjointness + hmodVac from the RvD tower (G1–G4)

**Status:** ✅ COMPLETE (2026-07-03, G1–G5). **GPT-5.5-pro-VERIFIED.** **Goal:** delete carried hinges in MULTIPLE landed
results at once: G1 grounds the operator-emergence coherent v-rule as a theorem (Bargmann adjointness on
polynomials); G2–G4 derive the modular transport from the RvD tower — deleting J3's `hmodVac` carried field,
instantiating Gate 3's trace-transport hinge, and replacing the ball-Clausius modular input.

## Binding corrections (from the verdict — never violate)
- **G1:** prove `bargmann_adjoint` by MONOMIAL-LINEARITY in `q` (induction_on_monomial), NOT a global support
  reindex; define `bargmann` summing over `q.support` (right-support) + the superset lemma
  (`Finset.sum_subset`); wrap `coeff_pderiv` locally with our exact orientation
  (`coeff m (pderiv l p) = (m l + 1)·coeff (m + single l 1) p` — prove from `pderiv_monomial` if absent);
  the factorial identity `multiFact (m + single l 1) = multiFact m·(m l + 1)` via `Nat.factorial_succ` +
  product split at `l`. Coherent grounding stays POLYNOMIAL-LEVEL: `coeffFamilyPair (cohCoeff α) p =
  cohPair α p = eval (conj∘α) p` + `cohPair_X_mul` — NO theorem about `⟨coh α, X·coh α⟩` without the
  completed space (summability).
- **G2 (the crux):** the generic `borelFC_conjU` via the SCALAR-MEASURE/RMK route — CFC conjugation
  covariance (`cfc g (UTU⁻¹) = U (cfc g T) U⁻¹`, Mathlib functoriality or a local uniqueness proof) ⟹
  `scalarMeasure_conjU` (test against continuous g; diagonal first, polarize if needed) ⟹ bounded Borel `f`
  via the `inner_borelFC` calc chain ⟹ operator equality. NO generator-uniqueness shortcut (domain/strong-
  continuity obligations — riskier). Spectrum subtypes: NO dependent rewrites — use ambient symbols where
  possible; else the `spectrumConjHomeomorph` with `simp` val lemma (our `modChar` symbol is ambient, so the
  transported symbol is extensionally identical).
- **Structure:** the `conjU` wrapper with `conjU_apply_U`/`conjU_comp_U` simp lemmas ONCE; projection
  transport by the uniqueness characterization of the real orthogonal projection under the ℝ-isometry;
  caller-friendly `..._of_carrier_eq` variants (hypothesis `S'.K = S.K.map U`) so payoff sites never build
  `S.map U` explicitly.

## Increments (verified order)
- [x] **G1 — the Bargmann adjointness** ✅ DONE (`QIQTH/BargmannPairing.lean`): `multiFact`; `bargmann` (right-support)
  + superset lemma + linearity/`bargmann_conj_symm`; `multiFact_add_single`; `coeff_pderiv_shift` (local
  wrapper); `bargmann_monomial_right`; **`bargmann_adjoint`** (`⟨p, X_l·q⟩_B = ⟨∂_l p, q⟩_B` — creation is
  adjoint to annihilation ON POLYNOMIALS, the v-rule ground); `cohCoeff`/`coeffFamilyPair`/`cohPair` +
  **`coeffFamilyPair_cohCoeff`** (`= eval (conj∘α) p`, the reproducing rule) + **`cohPair_X_mul`**
  (`= conj(α_l)·cohPair` — the coherent creation rule, grounded). Update the Q3 docstrings: v-rule cited →
  v-rule GROUNDED (polynomial level).
- [x] **G2 — projection/operator transport** ✅ DONE (`QIQTH/ModularTransport.lean`): `conjU` + simp lemmas;
  `projK_map` (real orthogonal projection under ℝ-isometry, uniqueness route); `rvdRC_map` +
  `rvdRC_transport_of_carrier_eq`.
- [x] **G3 — the Borel-FC covariance (the crux). ✅ COMPLETE** (G3a cfc_conjU; G3b(i) specMeasure_conjU; G3b(ii) specProj/PVM/diagInt/bilinDiag transport + CAPSTONE `borelFC_conjU`) (in `ModularTransport.lean`: `conjUStarAlgHom` continuous star-hom, `spectrum_conjU`, `conjU_isSelfAdjoint`, `cfc_conjU` — the CONTINUOUS FC covariance via Mathlib `map_cfc`). **G3b remaining:** CFC conjugation covariance (Mathlib functoriality name or
  local uniqueness proof); `scalarMeasure_conjU` (RMK uniqueness against continuous tests);
  **`borelFC_conjU`** (the calc chain through `inner_borelFC`); spectrum handling per the binding correction.
- [x] **G4 — the payoffs. ✅ DONE** (in `ModularTransport.lean`): **`modUnitary_map`** (`modUnitary (S.map U) t = conjU U (modUnitary S t)` — one
  line from G2+G3); `modUnitary_intertwine_of_carrier_eq` + `modUnitary_apply_of_carrier_eq`; corollaries:
  **J3 hmodVac DELETED** (`J3_hmodVac_of_unitary_transport` discharging `CHMTransportData.hmodVac` given
  carrier conjugacy + state transport), **Gate-3 hinge instantiated** (`Sren_cov_of_traceCovariant` fed by
  the derived transport), **ball family** (`ball_modUnitary_cov`/`ball_hmodVac` given the geometric carrier
  covariance). Update J3/Gate-3/inventory honestly: which named input became a THEOREM, which residue
  remains (the geometric carrier covariance data itself).
- [x] **G5 — checkpoint. ✅ CAMPAIGN COMPLETE** (loop deleted; sync on request). Inventory; plan COMPLETE; delete the loop; paper/website sync on request.

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0; AxiomAudit
pins; wire `QIQTH.lean`; ONE commit + `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push
schannel; update this checklist + `LEAN_RESULTS_INVENTORY.md`. Honesty: hypothesis deletion = the named input
becomes a theorem or shrinks — say which, every time; the coherent grounding is polynomial-level (the
completion stays cited); NOT QG. NEVER claim an increment too hard — attempt, iterate, checkpoint only after
a genuine failed attempt with the error shown. Check for sibling jobs before each increment. Consults:
`mcp__OpenAI__ask` gpt-5.5-pro (do NOT expose the key).

## Progress log
- **2026-07-03** — plan created from the GPT-5.5-pro consult (G1 monomial-linearity route, right-support
  bargmann, polynomial-level coherent grounding; G2–G4 conjU wrapper → projK/rvdRC transport → borelFC_conjU
  via CFC covariance + RMK uniqueness → modUnitary_map + the three payoff corollaries; generator-uniqueness
  shortcut REJECTED). NEXT → G1.
- **2026-07-03** — **G1 LANDED** (`BargmannPairing.lean`, axiom-free std-3, budget 0): the Bargmann pairing
  (right-support, superset lemma, linearity, conj-symmetry); multiFact_add_single; CAPSTONE
  `bargmann_adjoint` — creation IS adjoint to annihilation on polynomials (monomial-linearity route);
  the coherent layer at polynomial level: `coeffFamilyPair_cohCoeff` (the reproducing rule) +
  `cohPair_X_mul` (the coherent creation rule). HYPOTHESIS GROUNDED: the Q3 coherent v-rule (docstrings
  updated cited → GROUNDED; the completion-level identification stays cited). NEXT → G2.
- **2026-07-03** — **G2 LANDED** (`ModularTransport.lean`, axiom-free std-3, budget 0): conjU wrapper;
  `starProj_transport` (the core — real orthogonal projections transport along membership-level carrier
  conjugacy, by the uniqueness characterization under the ℝ-isometry); `carrierMap_mulI` (i𝒦 transports
  automatically — ℂ-linearity commutes with the I-scaling); projK/projIK/rvdR transport; CAPSTONE
  `rvdRC_transport` — R_{S′} = U R_S U⁻¹. NEXT → G3 (the crux: borelFC_conjU).
- **2026-07-03** — **G3a LANDED** (appended to `ModularTransport.lean`, axiom-free std-3, budget 0):

  `unitOfLIE` + `spectrum_conjU` (conjugation preserves the ℝ-spectrum); `conjU_continuous` (compL);

  `conjUStarAlgHom` (the continuous star-hom; map_star via the adjoint inner characterization);

  `conjU_isSelfAdjoint`; CAPSTONE `cfc_conjU` — the CONTINUOUS functional-calculus covariance

  cfc f (U T U⁻¹) = U (cfc f T) U⁻¹ (ambient real symbols, Mathlib map_cfc). NEXT → G3b (the

  scalar-measure/RMK lift to the bounded Borel calculus: specMeasure_conjU via the spectrum

  homeomorph + Tietze test functions, then borelFC_conjU by the inner_borelFC calc chain).

- **2026-07-03** — **G3b(i) LANDED** (appended to `ModularTransport.lean`, axiom-free std-3,

  budget 0): `specHomeo` (value-preserving spectrum homeomorphism) + CAPSTONE `specMeasure_conjU` —

  the RMK scalar measure transports as a pushforward, μ^{UTU⁻¹}_{Ux} = (specHomeo)_* μ^T_x (ext

  against C_c tests, Tietze-extended to ambient symbols, riding cfc_conjU). NEXT → G3b(ii): the

  specProj/PVM transport + borelFC_conjU via the inner_borelFC calc chain, then G4.

- **2026-07-03** — **G3b(ii) LANDED — G3 (THE CRUX) COMPLETE** (axiom-free std-3, budget 0):

  qForm/cForm transport (polarization, U ℂ-linear); `specProj_conjU` (E′(s′) = U E(e⁻¹s′) U⁻¹,

  inner ext); `pvmScalarMeasure_conjU` (pushforward); `diagInt_conjU`; `bilinDiag_conjU`;

  CAPSTONE **`borelFC_conjU`** — f(UTU⁻¹) = U·(f∘e)(T)·U⁻¹ for bounded measurable symbols.

  NEXT → G4 (modUnitary_map one line + the three payoffs).

- **2026-07-03** — **G4 LANDED — CAMPAIGN COMPLETE (G1–G5).** `modUnitary_transport`
  (Δ^{it}_{S′} = U Δ^{it}_S U⁻¹ — one congruence + the crux; the dependent-type obstacle solved by
  the subst-based borelFC_congr_op + defeq trans steps); `modUnitary_apply_transport`. PAYOFFS:
  `CHMTransportDataOfCarrierMap` — **J3's hmodVac carried field DELETED** (geometric carrier
  conjugacy alone builds the transport data; residue = the geometry itself);
  `modUnitary_inner_cov` — **Gate 3's covariance hinge fed by a derived theorem**;
  `ball_modUnitary_cov` — the ball-Clausius per-ball modular input replaced by geometry.
  LEDGER (G1–G4): the Q3 coherent v-rule GROUNDED (Bargmann adjointness); the RvD operator,
  spectral projections, PVM measures, and bounded Borel calculus all TRANSPORT under unitary
  conjugacy (the named follow-on of J3 AND Gate 3, built); hmodVac DELETED. Loop deleted.
