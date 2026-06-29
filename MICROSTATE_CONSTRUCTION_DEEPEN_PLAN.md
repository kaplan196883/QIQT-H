# Deepening the microstate construction — electrons & photons (axiom-free Lean)

> **Provenance.** This plan operationalizes the GPT-5.5-pro audit (2026-06-29) of "how much deeper
> the field-from-microstates construction can honestly go." It extends the **code-capacity bridge**
> (`QIQTH/CodeCapacityBridge.lean`, M0–M7) and the unifying theorem `records_born_and_area_bounded`.

---

## §0 — Honest scope (the line we do NOT cross)

The construction is about **how a field/particle's RECORDS are STORED and READ BACK** in a
finite, capacity-bounded microstate memory — NOT about deriving the field's existence or dynamics
from capacity.

- **Capacity is a CONSTRAINT, never a generator.** We never claim "the holographic bound derives
  the electron/photon." We never claim the value of `G` or the `1/4` ratio (matter-renormalization
  UV data).
- **Code space `C_R` and microstate space `𝓗_R` stay SEPARATE**, connected only by an isometry
  `V : C_R ↪ᵢ 𝓗_R`. They are never identified.
- **THE AUDIT TRIPWIRE (from GPT-5.5-pro).** Everything transported by `A ↦ V A Vᴴ`, `ρ ↦ VρVᴴ`
  lands in the **corner** `P · End(𝓗_R) · P` where `P := V Vᴴ` is the code projector. Any theorem
  that silently replaces `P` by the ambient identity `1_𝓗` (without a hypothesis forcing `P = 1`)
  is the overclaim to catch. **Every increment below must respect the corner.**
- **What the whole program WOULD establish (the honest slogan):**
  > *Finite field-code fragments, when encoded into capacity-bounded microstate spaces, appear as
  > Born-weighted, dynamically-faithful, area-bounded record structures — for both the electron
  > (fermionic CAR) and the photon (truncated bosonic).*
- **What it would NOT establish:** emergence of field dynamics, exact continuum CCR/Type-III modular
  theory, full Lorentz covariance from capacity, or a derived (non-postulated) area coefficient.
- **Discipline:** no `sorry`; every theorem `#print axioms` = standard 3 (`propext`,
  `Classical.choice`, `Quot.sound`); `bash scripts/axiom_budget_check.sh` budget 0; one green commit
  per increment with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via
  schannel; checkpoint honestly at each frontier (leave green, record the blocker, move on).

---

## §1 — Module layout

New file **`lean/mathlib/QIQTH/CornerConstruction.lean`** (the deepening tower), importing
`QIQTH.CodeCapacityBridge`, `QIQTH.BornEquiprobable`, `QIQTH.FQBoundMicro`, and (where available)
PhysLean CAR/Wick (`Physlib`). Wire every new theorem into `QIQTH.lean` + `QIQTH/AxiomAudit.lean`.
Electron-specific lemmas may go in a `section Electron`, photon-specific in `section Photon`,
sharing the corner core.

---

## §2 — Increments (most-tractable-first; ranked by value × tractability)

Each increment is a self-contained, axiom-free, green-building checkpoint. **D1 is the backbone**
that makes the corner honest for everything after it; build it first.

### D1 — Corner ⋆-algebra equivalence + n-point preservation  *(days; ⭐ backbone)*

The rigorous statement of "storing then reading back doesn't distort anything."

- `codeProjector (V : C_R ↪ᵢ 𝓗_R) : End 𝓗_R := V ∘ Vᴴ` with `codeProjector_isIdempotent`,
  `codeProjector_isSelfAdjoint` (`P† = P`, `P*P = P`), and `Vᴴ ∘ V = 1_{C_R}` (isometry).
- `encode (A : End C_R) : End 𝓗_R := V ∘ A ∘ Vᴴ` (the corner map `ι_V`).
- **`encode_starHom`**: `encode (A*B) = encode A * encode B`, `encode Aᴴ = (encode A)ᴴ`,
  `encode 1 = P` (NOT `1_𝓗` — the corner unit). Bundle as a `⋆`-algebra map onto `Corner P`.
- **`encoded_npoint`**: `Tr (VρVᴴ * encode A₁ * … * encode Aₙ) = Tr (ρ * A₁ * … * Aₙ)`
  (generalizes the existing M2 `encoded_record_expectation` to n factors via `encode_starHom`
  + trace cyclicity + `Vᴴ V = 1`).
- **Rides:** Mathlib f.d. `Matrix`/`End`, `conjTranspose`, `trace_mul_comm`; existing M1/M2.
  **Gap:** a small `Corner P` API if not already present.
- **Scope:** faithful *encoding/read-back*, NOT emergence of dynamics.
- **Covers electron & photon:** dimension-agnostic — `C_R` is later instantiated to CAR Fock
  (`Fin (2^n)`) for the electron and truncated Fock (`Fin ((d+N).choose N)`) for the photon.

### D2 — Sharp-record Born entropy ≤ area  *(days–2wk)*

Upgrade `record_log_card_le_area` from a **cardinality** bound to a real **Shannon-entropy** bound.

- For an orthogonal PVM record `{P_k}` on `C_R` (`∑ P_k = 1`, pairwise orthogonal) and density `ρ`,
  set `p k := Tr (ρ * P_k)`.
- **`sharp_record_born_entropy_le_area`**: `shannonEntropy p ≤ areaTerm`, via
  `H(p) ≤ log #{k | P_k ≠ 0} ≤ log (finrank C_R) ≤ log (finrank 𝓗_R) ≤ areaTerm`.
- **Layer-C corollary `born_readout_entropy_le_area`**: with `sec : I → K`, `p = pushforward`
  of uniform-`I` along `sec`, and `log|I| ≤ areaTerm`, conclude `shannonEntropy p ≤ areaTerm`.
  This connects the Born readout (Layer C) directly to an entropy–area statement.
- **Rides:** finite probabilities, `Real.log`, rank/cardinality. **Gap:** finite Shannon entropy
  `H(p) ≤ log|supp p|` — check Mathlib; build a tiny finite-entropy lemma if absent.
- **Scope:** bounds **orthogonal stored** records; does NOT bound arbitrary POVM-label entropy
  (a POVM can inject external randomness unless the apparatus is in the capacity budget — say so).
- **Covers electron & photon:** instantiate `I` at `Fin (2^n)` / `Fin ((d+N).choose N)`.

### D3 — Finite-Weyl / CCR no-go companion  *(days)*

Sharpen `no_finiteDim_CCR` with the operational obstruction (high honesty, cheap).

- **`finite_weyl_qpow_eq_one`**: invertible `U V = q • V U` on dimension `n` ⟹ `q^n = 1`
  (take determinants). So continuous Weyl CCR cannot hold in finite dimension for generic phase.
- **`truncated_oscillator_commutator`** (photon honesty): for the `N`-level lowering operator
  `a_N e_k = √k • e_{k-1}`, prove `[a_N, a_N†] = 1 - N • |top⟩⟨top|`, hence
  `Tr (ρ * [a_N, a_N†]) = 1 - N * ρ_top` (the honest low-occupation approximation error).
- **Rides:** `Matrix (Fin n)`, `det`, `trace`, finite sums. **Gap:** none significant.
- **Scope:** establishes that the **photon** on finite microstates is necessarily truncated/approximate
  (exact bosonic CCR is impossible) — the bosonic counterpart of the exact fermionic fit.

### D4 — CAR operators in the corner (ELECTRON)  *(corner: days; full: weeks)*

The electron's field operators, honestly transported.

- Assume a finite CAR representation on `C_R` (or reuse PhysLean's): `{a f, a† g} = ⟪f,g⟫ • 1`,
  `{a f, a g} = 0`, `{a† f, a† g} = 0`.
- **`encoded_CAR_corner`**: `{encode (a f), encode (a† g)} = ⟪f,g⟫ • P` (the corner unit `P`,
  NOT `1_𝓗`).
- **`encoded_CAR_full_iff_surjective`** (the no-overclaim guard): if
  `{encode (a f), encode (a† f)} = ⟪f,f⟫ • 1_𝓗` for some `f` with `⟪f,f⟫ ≠ 0`, then `P = 1_𝓗`
  (i.e. compressed CAR operators satisfy ambient-identity CAR ONLY when the code fills `𝓗_R`).
- **`fermion_modes_le_area`**: `finrank ℂ (FermionicFock h) = 2 ^ finrank ℂ h`, so under
  `V : FermionicFock h ↪ᵢ 𝓗_R` + capacity, `finrank ℂ h * log 2 ≤ areaTerm` (electron mode count
  is area-bounded).
- **Locality:** CAR subalgebras for orthogonal mode subspaces commute (transport via D1).
- **Rides:** PhysLean CAR/Wick + exterior-algebra Fock; D1's `encode_starHom`. **Gap:** if PhysLean's
  CAR isn't directly usable, assume a CAR rep as a typeclass and prove transport first.
- **Scope:** exact for **finite fermionic modes**; NOT full Lorentz/Poincaré covariance from capacity
  (only supplied finite/compact symmetries transport).

### D5 — Truncated-Fock operators in the corner (PHOTON)  *(days–1wk)*

The photon counterpart of D4, honest about truncation (builds on D3).

- Use the `N`-level truncated oscillator per mode; photon code space = truncated Fock
  `⊗ Fin(N+1)` with `card ≤ (d+N).choose N`.
- **`encoded_truncated_ladder_corner`**: `encode (a_N) `, `encode (a_N†)` satisfy the truncated
  commutator transported into the corner: `[encode a_N, encode a_N†] = encode (1 - N|top⟩⟨top|)`
  `= P - N • encode|top⟩⟨top|`.
- **`photon_modes_le_area`**: under `V : TruncFock ↪ᵢ 𝓗_R` + capacity,
  `log ((d+N).choose N) ≤ areaTerm` (already have `photon_entropy_le_area`; restate as a mode/occupation
  ceiling and connect to D2's entropy bound).
- **Scope:** **approximate** photon (finite occupation cutoff `N`); the truncation error is the D3
  `N·ρ_top` term — quantified, not hidden.

### D6 — Finite modular flow + KMS on the code; conditional BW descent  *(1–3wk / research at the BW step)*

- **`finite_modular_flow`**: `σ_ρ t A := ρ^{it} * A * ρ^{-it}` for faithful finite density `ρ`
  on `C_R`, with the group law and **finite KMS** `φ (A * σ_ρ(i) B) = φ (B * A)`, `φ A := Tr(ρ A)`.
- **`encoded_modular_flow_corner`**: `encode (σ_ρ t A) = σ^{corner}_{VρVᴴ} t (encode A)`
  (modular flow commutes with encoding, using the corner/support of `VρVᴴ`).
- **`modular_eq_BW_if_invariant`** (CONDITIONAL, honest): if `P` commutes with the one-particle BW
  generator `K_BW` and `ρ_C = Z⁻¹ exp(-2π K_BW|_C)`, then `σ_{ρ_C} t = ` boost flow on `C`.
  Otherwise compression and modular flow do NOT commute — state this as the explicit hypothesis.
- **Rides:** the existing Stone/spectral/bounded-FC tower; trace cyclicity. **Gap:** clean complex
  powers/logs of positive matrices + KMS analytic-continuation convention.
- **Scope:** finite KMS is **real**; automatic descent of one-particle BW flow to finite records is
  **NOT** — exact wedge modular theory is type-III/continuum. Checkpoint here if the BW step resists.
- **Covers both:** electron (CAR Gibbs) and photon (truncated-oscillator Gibbs).

### D7 — Dynamics preservation under intertwining  *(days–wks)*

The honest "fragment of dynamics" — **preservation, not generation**.

- Given supplied code dynamics `U_t` and ambient `W_t` with `W_t ∘ V = V ∘ U_t`:
  **`encoded_npoint_of_intertwining`**: encoded Heisenberg n-point functions equal the code ones.
- **`decoherence_functional_preserved`**: the decoherence functional `D_enc(h,h') = D_code(h,h')`
  for sequential record histories.
- **Optional `finite_gibbs_detailed_balance`**: `G_A(-ω) = exp(-βω) G_{A†}(ω)` for a finite Gibbs
  state; at `β = 2π` with `K = K_BW` this is an Unruh-type finite fragment.
- **Scope:** λ-selection + Φ-runtime **preserve** supplied dynamics/correlators/histories; they do
  NOT generate field dynamics. Reeh–Schlieder on a finite code is a Schmidt-rank toy, not continuum RS.

### D8 — P5 isolation (envariance uniqueness)  *(days)*

Cannot remove P5, but can isolate it cleanly.

- **`uniform_of_permInvariant`**: a permutation-invariant probability `μ` on finite `I` is uniform
  `μ i = 1/|I|`.
- Optional **`envariance_equalAmplitude`**: `(U_σ ⊗ U_{σ⁻¹}) Ψ = Ψ` for equal-amplitude Schmidt `Ψ`.
- **Scope:** uniqueness of the uniform measure **under symmetry**; the physical premise "λ respects
  envariant symmetries" remains an explicit assumption (P5 is isolated, not discharged).

### D9 — (Frontier, do NOT overclaim) Gaussian/Williamson entropy  *(research-grade)*

- Honest target: for a finite cutoff bosonic Gaussian state,
  `S(ρ_Gaussian) = ∑_j g(ν_j)` (symplectic eigenvalues), after formalizing Williamson normal form.
- **Gap:** real symplectic linear algebra + Williamson + Gaussian covariance — **mostly absent from
  Mathlib**. **Scope:** a cutoff Gaussian entropy formula, NOT an area law; the coefficient is
  cutoff/model-dependent, NOT the holographic `1/4`. **Checkpoint as the cited frontier; do not grind.**

---

## §3 — Build / commit protocol (per increment)

1. `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.CornerConstruction` → green.
2. Add `#print axioms` entries to `QIQTH/AxiomAudit.lean`; rebuild `QIQTH QIQTH.AxiomAudit` green;
   confirm each new theorem depends only on `[propext, Classical.choice, Quot.sound]`.
3. `bash scripts/axiom_budget_check.sh` → raw axiom count 0, OK.
4. Wire the module into `QIQTH.lean` (import) if newly created.
5. Update §4 Progress log below.
6. ONE commit on `main` with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer;
   push via `git -c http.sslBackend=schannel push origin main`.
7. Report when an increment lands OR a frontier is honestly checkpointed.

---

## §4 — Progress log

- 2026-06-29 — Plan written from the GPT-5.5-pro deepening audit. Backbone = D1 (corner ⋆-algebra
  equivalence). Order: D1 → D2 → D3 → D4 (electron) → D5 (photon) → D6 → D7 → D8; D9 is the cited
  frontier.
- 2026-06-29 — **D1 DONE** (axiom-free standard-3, budget 0, full QIQTH green 8874 jobs). New module
  `QIQTH/CornerConstruction.lean`: `codeProjector V = V Vᴴ` (`_mul_self` idempotent, `_conjTranspose`
  self-adjoint); `encode V A = V A Vᴴ` with the `⋆`-homomorphism laws `encode_mul`
  (`ι_V(AB)=ι_V(A)ι_V(B)`), `encode_conjTranspose` (`ι_V(Aᴴ)=ι_V(A)ᴴ`); **the tripwire made explicit**
  `encode_one` (`ι_V(1) = P`, the corner unit, NOT `1_𝓗`) + `codeProjector_eq_one_iff_encode_one`
  (ambient-unital ⟺ code fills `𝓗_R`); `encode_prod` (nonempty product hom); and the backbone
  **`encoded_npoint`** — `Tr((VρVᴴ)·ι_V(A₁)···ι_V(Aₙ)) = Tr(ρ·A₁···Aₙ)` (storing the field and reading
  back any product of records reproduces the bare statistics; generalizes M2 to a full n-point
  correlator), with `encoded_twopoint` as the physically central corollary. Dimension-agnostic →
  covers electron & photon uniformly. Honest: faithful encoding / read-back, NOT emergence of the
  field or its dynamics. Wired into `QIQTH.lean` + `AxiomAudit.lean`. _Next: D2 (sharp-record Born
  entropy ≤ area)._
- 2026-06-29 — **D2 DONE** (axiom-free standard-3, budget 0, full QIQTH green 8874 jobs). The **entropy
  upgrade of M7** in `CornerConstruction.lean` (`section Records`): `born_record_entropy_le_area` — the
  actual **Shannon entropy** of a Born record distribution `p : K → ℝ` obeys the area floor once the
  records fit the microstate space, `H(p) ≤ log(card K) ≤ log(card 𝓗) ≤ A/4ℓ_P²` (rides the existing
  Gibbs/Jensen `RecordContract.shannon_le_log_card` + the bridge's fitting+capacity chain). Layer-C tie
  **`born_readout_entropy_le_area`** — the *actual* Born readout `(sectorAmp k)² = |c_k|²` of the unifying
  theorem has area-bounded entropy (joins the typicality-derived Born weights to the capacity layer in
  entropy form), with helper `sum_uniform_outcomeMarginal` (the uniform measure's marginals sum to 1).
  So M7's "log #records ≤ area" is sharpened to "the *information* in the Born-weighted records ≤ area."
  Honest scope unchanged: about the field's records; does not remove P5 or the capacity postulate. Wired
  into `AxiomAudit.lean`. _Next: D3 (finite-Weyl/CCR no-go + truncated-oscillator commutator)._
