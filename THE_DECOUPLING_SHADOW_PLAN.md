# THE DECOUPLING SHADOW (DS1–DS7): the finite forced core of the dictionary

**Status:** ACTIVE (2026-07-03). **GPT-5.5-pro-VERIFIED** (binding verdict below). **Goal:** the
finite shadow of Maldacena's decoupling-limit structure (one parent, one limit, two surviving
descriptions) — replacing "constructed weight dictionary" by "RIGID under the finite
decoupling-shadow hypotheses": (a) THE CAPACITY LIMIT — genuine `Filter.Tendsto` theorems forcing
the free-oscillator sector in the cutoff limit (bounded-occupation CCR recovery; Gibbs
correlations/entropy → the Planck/free values; the high-T capacity saturation; the
REGIME-SEPARATION GUARD); (c) REFINEMENT RIGIDITY — a monoidal, monotone, refinement-natural area
valuation is FORCED to be `κ·log dim = κ·Σ log D_k` (with the explicit counterexample showing
weaker hypotheses fail). Files under `lean/mathlib/QIQTH/Decoupling/` + `QIQTH/Rigidity/`.

## Binding verdict (from the consult — never violate)
- **NO full Maldacena analogue**: QIQT-H cannot honestly force the join incidence geometry, the
  species/cell match, or the value of G from a finite limit — those remain parent data /
  normalization input. The honest deletion: "local weight = log capacity" becomes RIGID/FORCED
  under refinement naturality; "truncated mode = free oscillator mode in the limit" becomes FORCED
  by the cutoff limit. NEVER sell this as a full decoupling derivation.
- **(b) dual scaling is NOT the campaign** — e^{−s}τ(p) → 0 without renormalization, chosen answer
  with it: the Type III wall restated. At most sanity lemmas, no campaign.
- **The REGIME-SEPARATION GUARD is load-bearing honesty**: capacity saturation (x_D·D → 0 ⟹
  S_D − log D → 0) and thermal CCR recovery (fixed x > 0 ⟹ defect expectation D·q^{D−1}/Z_D → 0)
  are DIFFERENT regimes — in the saturation regime the defect expectation tends to 1, NOT 0. Exact
  saturated capacity is not simultaneously the positive-temperature free-oscillator limit. State
  the guard as a theorem.
- **Rigidity needs the STRONG hypotheses**: additivity alone is FALSE (the 2-adic valuation
  ν₂(n) is additive and divisibility-monotone but not ∝ log). The theorem: A(1) = 0 +
  A(mn) = A(m)+A(n) + (m ≤ n ⟹ A(m) ≤ A(n), i.e. monotone under ALL isometric embeddings)
  ⟹ ∃ κ ≥ 0, A(n) = κ·log n. Proof route: A(n^r) = r·A(n); m^r ≤ n^s ⟹ r·A(m) ≤ s·A(n);
  s := ⌈r·log m/log n⌉, r → ∞ ⟹ A(m)/log m ≤ A(n)/log n; swap. Include the ν₂ counterexample.
- **Single-mode analysis first, explicit formulas**: Z_D(q) = (1−q^D)/(1−q); ⟨N⟩_D → q/(1−q);
  S_D(x) → −log(1−e^{−x}) + x/(e^x−1) (fixed x > 0); defect D·q^{D−1}/Z_D → 0. Matrix
  elements/finite support ONLY — no operator norms, no unbounded operators.
- **CUT**: operator-norm limits; unbounded operators; continuum Riemann sums; the Type III limit;
  path integrals; any claim that the rigidity forces the join adjacency/screen incidence; any
  claim capacity saturation = the free-field state limit; claiming G or the species match forced.

## Increments
- [x] **DS1 — bounded-sector CCR recovery** ✅ DONE (`QIQTH/Decoupling/TruncatedCCR.lean`): the ladder
  matrix elements at FIXED occupations are D-independent once D is large enough
  (`lowering_matrixElement_stable`); the commutator entries STABILIZE to the exact-CCR values —
  `[a_D, a_D†](m,n) = δ_{mn}` for m+1, n+1 < D (via the held defect theorem: the top projector
  vanishes at bounded occupations) + the `∀ᶠ D in atTop` eventually-form. The finite analogue of
  "the parent contains the free sector".
- [x] **DS2 — the single-mode Gibbs limit** ✅ DONE (`QIQTH/Decoupling/GibbsSingleMode.lean`): for
  0 ≤ q < 1: `Z_D q → 1/(1−q)`, `⟨N⟩_D → q/(1−q)` (genuine Filter.Tendsto — QIQT-H's first limit
  theorems), and the DEFECT EXPECTATION `D·q^{D−1}/Z_D → 0` (fixed βω > 0 only).
- [x] **DS3 — entropy regimes + the guard** ✅ DONE (`QIQTH/Decoupling/EntropyRegimes.lean`):
  `S_D(x) → −log(1−e^{−x}) + x/(e^x−1)` (fixed x > 0); the high-T saturation `S_D(x) → log D` as
  x → 0⁺; THE REGIME-SEPARATION GUARD — along x_D·D → 0: S_D(x_D) − log D → 0 BUT the defect
  expectation → 1 (saturation ≠ the free-oscillator limit, as a theorem).
- [x] **DS4 — finite products** ✅ DONE (`QIQTH/Decoupling/ProductModes.lean`): the single-mode limits
  lifted to finite mode sets by `Finset.sum`/`Tendsto` algebra (S_prod = Σ S_{D_k}(βω_k)
  converging modewise; bounded-word convergence for H = Σ ω_k N_k). Finite mode sets ONLY.
- [x] **DS5 — real log-valuation rigidity** ✅ DONE (`QIQTH/Rigidity/LogValuationReal.lean`): a monotone
  additive A on positive reals is `κ·log` (g(t) := A(e^t) monotone additive Cauchy rigidity).
- [ ] **DS6 — the finite-corner valuation rigidity** (`QIQTH/Rigidity/FiniteCornerValuation.lean`):
  A : ℕ+ → ℝ with A(mn) = A(m)+A(n) and m ≤ n ⟹ A(m) ≤ A(n) is `κ·log n` (the ⌈r log m/log n⌉
  squeeze); hence on product records A = κ·Σ log D_k — THE FORCED WEIGHT DICTIONARY; PLUS the ν₂
  counterexample (additive + divisibility-monotone but NOT ∝ log — the strong hypotheses are
  necessary).
- [ ] **DS7 — the shadow package + checkpoint** (`QIQTH/Decoupling/DecouplingShadow.lean`): the
  parent tower packaged (truncated corner + oscillators + records + refinement-natural valuation)
  with the three theorems (free sector survives the cutoff limit; the valuation is κ·Σ log D_k;
  given the normalization the saturated area law survives). Then the checkpoint (the two honest
  sentences, VERBATIM in the module docstring + inventory): "The capacity-limit theorem forces
  the oscillator/free-field sector only in the bounded-occupation or positive-temperature sense;
  it does not force the screen geometry or Newton constant." AND "The tower-rigidity theorem
  forces the logarithmic capacity weight only under monoidal, monotone refinement naturality;
  without those hypotheses there are explicit finite counterexamples." Delete the loop;
  paper/website sync on request.

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0;
AxiomAudit pins; wire `QIQTH.lean`; ONE commit + `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`;
push schannel; update this checklist + `LEAN_RESULTS_INVENTORY.md`. HONESTY: not a full decoupling
derivation — the forced core is the WEIGHT dictionary and the free sector, never the join geometry
/ species match / G; the regime guard stays a theorem; NEVER claim QG solved or a wall crossed.
NEVER claim an increment too hard — attempt, iterate, checkpoint only after a genuine failed
attempt with the error shown. Check for sibling jobs before each increment. Consults:
`mcp__OpenAI__ask` gpt-5.5-pro (do NOT expose the key).

## Progress log
- **2026-07-03** — plan created from the GPT-5.5-pro decoupling-shadow consult (verdicts: (a) YES
  with sharp scope, (b) NO — the wall restated, (c) YES with strengthened hypotheses + the ν₂
  counterexample, (d) rejected as too strong; the regime-separation guard; the cut list; ordering
  DS1→DS7; the two checkpoint sentences fixed verbatim). NEXT → DS1.

- **2026-07-03** — **DS1 LANDED** (`QIQTH/Decoupling/TruncatedCCR.lean`, axiom-free std-3,
  budget 0): lowering_matrixElement_stable (ladder entries at fixed occupations are D-INDEPENDENT
  — rfl-level); commutator_matrixElement_stabilizes (⟨m|[a_D,a_D†]|n⟩ = δ_mn below the top level —
  the truncation defect invisible at bounded occupations); CAPSTONE commutator_eventually_exact
  (the ∀ᶠ D in atTop form — the free-oscillator sector FORCED by the cutoff limit; the weak half
  of the decoupling argument in its honest finite form). NEXT → DS2 (the single-mode Gibbs limit).

- **2026-07-03** — **DS2 LANDED** (`QIQTH/Decoupling/GibbsSingleMode.lean`, axiom-free std-3,
  budget 0): QIQT-H's first GENUINE LIMIT THEOREMS (Filter.Tendsto) — tendsto_Zgeom (Z_D →
  1/(1−q)); tendsto_meanN (⟨N⟩_D → q/(1−q), the PLANCK value; riding
  hasSum_coe_mul_geometric_of_norm_lt_one); CAPSTONE tendsto_defectExpect (D·q^{D−1}/Z_D → 0 at
  fixed βω > 0 — the state-level decoupling half; the n·qⁿ → 0 shift trick via
  tendsto_add_atTop_iff_nat); ZMode_eq_Zgeom (the bridge: the DY2 code partition function IS the
  truncated geometric sum at q = e^{−βω}). NEXT → DS3 (entropy regimes + the guard).

- **2026-07-03** — **DS3 LANDED** (`QIQTH/Decoupling/EntropyRegimes.lean`, axiom-free std-3,
  budget 0, no sorry): thermalEntropy (S_D = log Z + x·⟨N⟩) with the elementary bound toolkit
  (1 ≤ Z ≤ D, D·q^{D−1} ≤ Z, 0 ≤ ⟨N⟩ ≤ D); tendsto_thermalEntropy_planck (fixed x > 0: S_D → the
  free Planck oscillator entropy; planck_form gives x/(e^x−1)); tendsto_thermalEntropy_saturation
  (fixed D: S_D → log D as x → 0⁺, by continuity at 0); CAPSTONES guard_entropy_saturates +
  guard_defect_survives — THE REGIME-SEPARATION GUARD: along ANY schedule x_D·D → 0, capacity
  saturates (squeeze |S − log D| ≤ x_D·D) BUT the defect expectation tends to 1 (squeeze
  e^{−x_D·D} ≤ defect ≤ 1) — saturated capacity is provably NOT the free-oscillator limit.
  NEXT → DS4 (finite products).

- **2026-07-03** — **DS4 LANDED** (`QIQTH/Decoupling/ProductModes.lean`, axiom-free std-3,
  budget 0): planckEntropy + productEntropy; CAPSTONE tendsto_productEntropy
  (Σ_k S_{D_j(k)}(βω_k) → Σ_k s_Planck(βω_k) along any schedule growing at every mode — by
  tendsto_finset_sum over the DS3 single-mode limit); tendsto_totalDefect (the total defect
  expectation dies); tendsto_gibbsWeight_fixedOccupation (every fixed occupation's Gibbs weight →
  the free-field Boltzmann weight Π q^n(1−q) — the state-level product decoupling). Finite mode
  sets only. NEXT → DS5 (real log-valuation rigidity).

- **2026-07-03** — **DS5 LANDED** (`QIQTH/Rigidity/LogValuationReal.lean`, axiom-free std-3,
  budget 0, no sorry): the classical monotone-additive Cauchy rigidity DONE BY HAND —
  monotone_additive_eq_smul (ℚ-linearity by ℕ-induction/negation/denominator-clearing, then the
  rational squeeze via exists_rat_btwn + le_of_forall_pos_le_add); CAPSTONE monotone_logValuation
  — a monotone product-to-sum valuation on ℝ>0 is κ·log with κ ≥ 0 (via g(t) = A(e^t)). The
  positive-real half of the forced weight dictionary. NEXT → DS6 (the finite-corner valuation
  rigidity + the ν₂ counterexample).
