# CODE–CAPACITY BRIDGE — connect the free-field substrate to QIQT-H's finite microstates

**Goal.** Make "electron/photon ↔ QIQT-H microstates" a **real machine-checked connection**, not a slogan —
without overclaiming. Build the **code-subspace encoding bridge** linking the free-field regional sector
(CAR `⋀h` / truncated symmetric Fock) to the finite-microstate / holographic-capacity layer
(`log dim 𝓗_R ≤ A(∂R)/4ℓ_P²`), plus the one genuine "reverse" statement with teeth: the **CAR/CCR finite-
capacity statistics dichotomy**. (GPT-5.5-pro consult, 2026-06-29.)

## §0. HONEST SCOPE (read first — do not drift)

- **Capacity is a CONSTRAINT / admissibility principle, NOT a generator.** The finite-microstate postulate
  `log dim 𝓗_R ≤ A/4ℓ_P²` does **not** determine Dirac-vs-Maxwell, spin, mass, gauge group, charge, the gamma
  matrices, or the Lorentz rep. Every finite quantum system under the same dimension budget satisfies it. **Do
  NOT claim "capacity derives the electron/photon."** The honest arrow is `capacity ⟹ upper bound on admissible
  code dimension`, never `capacity ⟹ electron/photon`.
- **The only honest "reverse" content with teeth:** exact finite **CAR** sectors exist (`⋀h ≅ M_{2ⁿ}`); exact
  finite **CCR** sectors are impossible (`0 = Tr[a,a†] = Tr I = dim H`). So fermions fit finite capacity exactly;
  bosons (the photon) need a number/energy cutoff or the Type-II renormalized route. Spin-statistics PROPER still
  needs locality/Poincaré/positive-energy — **NOT** capacity; do not claim otherwise.
- **`K̃` self-adjoint (Increment 1c, done) is NECESSARY but NOT SUFFICIENT** for microstate counting: it gives
  spectral calculus / modular flow / `e^{itK̃}` but **not** a trace, density matrix, or `log` of an effective
  microstate dimension. The genuine "renormalized entropy = log effective microstate dim" is the **Type-II /
  dual-weight trace theorem (Phase 5 of `P4_WALL_CAMPAIGN_PLAN.md`)** and needs the trace — out of scope here.
- Per-increment protocol (same as ELECTRON/PHOTON plans): `cd lean/mathlib && ~/.elan/bin/lake build
  QIQTH.<module>` green; `#print axioms` = standard 3 (`propext`/`Classical.choice`/`Quot.sound`); `bash
  scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; ONE commit on main with the
  `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via `git -c http.sslBackend=schannel
  push origin main`; update the §3 Progress log below. No `sorry`. Never claim the value of `G`; the 1/4 ratio is
  matter-renormalization-dependent.

## §1. New module: `QIQTH/CodeCapacityBridge.lean`

Keep the field's **code space** `C_R` and the **microstate space** `𝓗_R` SEPARATE (do NOT identify them — that
is the slogan). Connect by an **isometry** `V : C_R ↪ 𝓗_R`. Reuse existing dims: `Fock/Dirac/CAR.finrank_CARFock`
(`dim ⋀h = 2ⁿ`), `Fock/Photon/PhotonFock.truncFockDim_eq_choose` (`dim Sym^{≤N}h = C(d+N,N)`), and the existing
`QuantumEntropy.vonNeumannEntropy` / `IsDensity` + `SpectralSum.vonNeumannEntropy_diagonal` +
`shannon_le_log_card` / `vonNeumannEntropy_le_log_card`.

## §2. The theorem package (ordered, most-tractable-first)

**M0 — `no_finiteDim_CCR` (START HERE; the gem).** On a nonzero finite-dimensional ℂ-space `H` there are no
operators `a, a†` with `a*a† − a†*a = 1`. Proof: `Tr(a a† − a† a) = 0` (trace of a commutator) but `Tr(1) =
dim H ≠ 0`. So **exact finite CCR is impossible** — the photon's bosonic mode cannot live in a finite-capacity
sector without a cutoff (contrast the CAR fermion, which fits exactly: `⋀h` finite). Mathlib: `Matrix.trace_mul_
comm` / `Matrix.trace_one` / `Fintype.card`. *(~5–15 lines; the single most honest "physics from capacity".)*

**M1 — code/microstate admissibility `code_fits_iff_finrank_le`.** For finite-dim ℂ-spaces `C_R`, `𝓗_R`:
`(∃ V : C_R →ₗᵢ[ℂ] 𝓗_R) ↔ finrank C_R ≤ finrank 𝓗_R`. (Mathlib `LinearIsometry` exists ⟺ finrank ≤; via
`LinearMap.exists_...`/orthonormal-basis extension, or the finrank-monotone-under-injective direction + a
constructed isometry on a subspace.) *(Statement of "the field sector fits holographically iff its code dim
fits".)*

**M2 — encoding preserves entropy & records.** For an isometry `V : C_R →ₗᵢ 𝓗_R` and a density `ρ` on `C_R`:
(a) `vonNeumannEntropy (V ρ V†) = vonNeumannEntropy ρ` (`entropy_conj_isometry_eq` — spectrum preserved);
(b) `Tr_{𝓗_R}(VρV† · VOV†) = Tr_{C_R}(ρ O)` (`encoded_expectation_eq` — record expectations match). So encoding
into the microstate space changes neither the field entropy nor its record statistics.

**M3 — `entropy_le_log_rank_support` / effective microstate dimension.** For a finite-dim density `ρ`:
`vonNeumannEntropy ρ ≤ log (rank (support ρ)) ≤ log (finrank C_R)`. Define `D_eff(ρ) := exp(S_vN ρ)`;
`D_eff ρ ≤ finrank C_R`. (Largely reuses `vonNeumannEntropy_le_log_card`.)

**M4 — `encoded_field_entropy_le_area` (the chained bridge, the payoff).** Given `V : C_R ↪ 𝓗_R` and the
P4-MICRO holographic bound `log (finrank 𝓗_R) ≤ A/4ℓ_P²` (the `HolographicCapacityBound`/`MicrostatePostulate`
typeclass from `FQBoundMicro.lean`): for any density `ρ` on `C_R`,
`S_vN ρ ≤ log (finrank C_R) ≤ log (finrank 𝓗_R) ≤ A/4ℓ_P²`. **The free field's regional entropy obeys the area
capacity once its code sector admissibly encodes into the microstate space.**

**M5 — field instantiations.** Specialize M4 to the actual fields using the existing dims:
- electron: `finrank (CARFock 𝕜 h_R) = 2^{finrank h_R}` ⟹ `S_vN ≤ n_F·log 2 ≤ A/4ℓ_P²` when `2^{n_F} ≤ finrank
  𝓗_R`.
- photon: `truncFockDim d N = C(d+N,N)` ⟹ `S_vN ≤ log C(d+N,N) ≤ A/4ℓ_P²` when `C(d+N,N) ≤ finrank 𝓗_R`. Tie to
  the existing `photon_capacity_bound`.

**M6 — record-capacity corollary.** For a family of perfectly distinguishable record projections `{P_i}` on
`C_R` (orthogonal nonzero), `|I| ≤ finrank C_R`, hence after encoding `log |I| ≤ A/4ℓ_P²`. Applies to the even/
parity records (electron) and gauge-invariant records (photon). (`card_orthogonal_nonzero_projections_le_finrank`.)

**M7 — bundle + honest README theorem.** One capstone statement: *finite free-field code fits in the holographic
microspace ⟹ all encoded field entropies/records obey the area capacity*, PLUS the obstruction *exact untruncated
CCR photon sector cannot fit finite capacity* (`no_finiteDim_CCR`). Wire the capstone into `AxiomAudit.lean` with
the honest-scope note from §0.

## §3. Progress log

- 2026-06-29 — plan opened (GPT-5.5-pro consult). Honest scope fixed: capacity = constraint, not generator;
  CAR-fits / CCR-doesn't is the only reverse content with teeth; the renormalized-entropy = log-microstate-dim
  link needs the Phase-5 trace (out of scope).
- 2026-06-29 — **M0 DONE** (`QIQTH/CodeCapacityBridge.lean`, axiom-free standard-3, budget 0, full QIQTH green
  8873 jobs). **`no_finiteDim_CCR`**: on a nonzero finite-dim space, no `a,a†` satisfy `[a,a†]=a a†−a† a=1`
  (`trace([a,a†])=0` via `trace_mul_comm`, but `trace 1 = Fintype.card n ≠ 0`). So the photon's bosonic mode
  CANNOT live in a finite-microstate sector without a cutoff — the CAR fermion's `⋀h` fits exactly; the single
  genuine "reverse" content of capacity. Wired into `QIQTH.lean`+`AxiomAudit.lean`. Next: **M1
  `code_fits_iff_finrank_le`**.
