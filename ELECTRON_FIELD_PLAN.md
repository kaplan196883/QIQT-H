# ELECTRON_FIELD_PLAN — the free Dirac electron in QIQT-H

**Status:** active plan (opened 2026-06-28). **Scope:** the **free** massive charged Dirac field —
the first concrete instance of "matter beyond scalars" in the QG roadmap (`docs/qg_roadmap/` Tier 1
§1.2, Tier 2 §2.3). **Out of scope (cited, not formalized):** interacting QED, gauge dressing,
Gauss-law edge modes, infraparticles, the photon, the full Standard Model.

**GPT-5.5-pro-vetted (2026-06-28; thread archived conceptually in
`memory/qiqth_electron_field_requirements.md`).**

---

## 0. The crux, stated first (do not bury it)

The QIQT-H substrate is **entirely bosonic**: `QIQTH/Fock/` is a Weyl/CCR algebra + Glauber coherent
states + one-particle Bisognano–Wichmann + boost-KMS. **There is no Dirac/spinor/CAR anything.** So
"specify the electron" means **building a parallel free-Dirac (CAR / quasi-free) substrate**, not
tweaking the scalar.

**The conceptual crux is NOT "the boost picks up a fermionic sign."** The Rindler modular flow
`Δ_W^{it}` stays *exactly* the geometric boost `U(Λ_W(−2πt))`, KMS at `β=2π` (same Unruh temperature).
The fermionic sign lives in **graded locality + twisted modular duality**:

> The free Dirac field is a **Z₂-graded CAR field net**. With parity `Γ=(−1)^F` and the **Klein twist**
> `Z = (1+iΓ)/(1+i)`, the modular conjugation sends a wedge algebra to the *Klein-twisted* opposite
> wedge: **`𝓕(W)' = Z 𝓕(W') Z*`**, `J_W = Z·J_geom`, and homogeneous fields **graded-commute**
> `F₁F₂ = (−1)^{|F₁||F₂|} F₂F₁` at spacelike separation. This is the AQFT form of spin–statistics
> (Bisognano–Wichmann + Araki CAR duality + Guido–Longo modular spin-statistics).

**The load-bearing consequence for QIQT-H specifically:** fermionic subregion factorization needs a
**graded tensor product** `CAR(h_A⊕h_B) ≅ CAR(h_A) ⊗̂_{Z₂} CAR(h_B)` (odd operators across regions
**anticommute**). So QIQT-H must **decide which algebra "records per region" / the capacity bound
attach to**:
1. the full graded field algebra `𝓕(O)`,
2. the **even** (parity-preserving) subalgebra `𝓕(O)_+`, or
3. the U(1)-invariant **observable** algebra `𝒜(O) = 𝓕(O)^{U(1)}`.

**This plan adopts (2)/(3): records and operations are EVEN observables.** Classical/decoherent
variables become **even bilinears** — charge density `j^μ = ψ̄γ^μψ`, stress tensor `T_μν`, occupation
number, spin density — **not** c-number field amplitudes. Consequently the **bosonic χ_R
coherent-sector calculus does NOT transfer** (a real substrate cost, handled in E8).

---

## 1. What carries over, what changes (the work list in one table)

| Ingredient | Free scalar (have) | Free Dirac electron (build) | Cat. |
|---|---|---|---|
| One-particle space | KG modes, scalar | Dirac solution space, spinor; **Wigner** unitary rep (the `(½,0)⊕(0,½)` spinor rep is only the finite-dim index action) | (a)/(b) |
| Causal kernel | Pauli–Jordan `Δ_m` | Dirac `S_D = (iγ·∂+m)Δ_m`, **anti**commutator | (a) |
| Algebra | Weyl/CCR (commutators) | **CAR** (anticommutators), antisymmetric Fock = exterior algebra | (b) |
| Classical sector | Glauber coherent states (χ_R) | **quasi-free CAR states via covariance matrix `C`**; no Hilbert-space coherent states | (b) |
| Locality | local | **graded-local + twisted duality** (the crux) | (b) |
| Modular flow `Δ^{it}` | boost (`OneParticleBW`,`BoostKMS`) | **same boost**, β=2π | (a) |
| Modular conj. `J` | geometric | **`J_W = Z·J_geom`** (Klein twist) | (b) |
| Unruh occupation | Bose `1/(e^{2πω}−1)` | **Fermi–Dirac `1/(e^{2πω}+1)`** | (a) |
| Entropy | bosonic | **`S = −Tr[C log C + (1−C)log(1−C)]`** (clean) | (a) |
| Capacity bound | `S_vN ≤ log N_R` | **`S_R ≤ dim(h_R)·log2 = log dim(∧h_R)`** on graded regional algebra | (a) |
| Rel. entropy | Klein/Araki | **Araki CAR** rel-entropy (clean closed form) | (a)/(b) |
| Records / no-signaling | Weyl-based | **even-observable** re-derivation; graded tensor product | (b) |
| Charge | neutral | global U(1); local algebras still **factors** (no center in continuum) | (b) |
| Jacobson hook | scalar `T_μν` | **Dirac (Belinfante) `T_μν`** in `2π K_boost` | (b) |

`1/G`/area note: adding Dirac shifts **both** the matter entanglement divergence **and** `1/G`; the
`1/4` ratio is stable **only after `G` is renormalized/capacity-defined** — it is **NOT** "untouched by
matter." Never claim the value of `G` is derived.

---

## 2. Phases (Lean-concrete, ship-green-increments). New modules under `QIQTH/Fock/Dirac/`.

Each phase is an axiom-free green checkpoint (`#print axioms` = standard 3; budget 0; wire into
`QIQTH.lean` + `AxiomAudit.lean`). Order is most-tractable-first; the finite-dim entropy/capacity core
(E3, E7) is front-loaded because it is independently valuable and lands fastest.

### E3 — Quasi-free fermionic entropy + the capacity bound  *(category (a); START HERE — sharpest, most self-contained)*
`QIQTH/Fock/Dirac/QuasiFreeEntropy.lean`.
- `binaryEntropy c := −c·log c − (1−c)·log(1−c)`; `binaryEntropy_le_log_two : binaryEntropy c ≤ log 2`
  for `c ∈ [0,1]` (the one genuinely new analytic lemma; maximum at `c=1/2`).
- `fermionicGaussianEntropy C := ∑ over eigenvalues c of (−c log c − (1−c)log(1−c))` for a Hermitian
  correlation matrix `C` with `0 ≤ C ≤ 1` (reuse `IsHermitian.cfc` / spectral sum, mirror
  `GaussianStateEntropy.lean`/`QuantumEntropy`).
- **`fermionicGaussianEntropy_le_log_card : fermionicGaussianEntropy C ≤ (Fintype.card ι) • log 2`** —
  the fermionic capacity bound. Note `(card ι)·log 2 = log (2 ^ card ι) = log dim(∧ h_R)` (exterior
  algebra dimension), so this is **`S_R ≤ log dim(∧ h_R)`**: the CAR mirror of `shannon_le_log_card`.
- Optional: `fermionicGaussianRelEntropy C D = Tr[C(log C−log D)+(1−C)(log(1−C)−log(1−D))] ≥ 0`
  (Araki CAR rel-entropy positivity, finite-dim) — mirrors `relEntropy_nonneg` (Klein).

### E2 — CAR algebra + antisymmetric Fock  *(category (b))*
`QIQTH/Fock/Dirac/CAR.lean`. Build on Mathlib `ExteriorAlgebra` / `CliffordAlgebra` (antisymmetric
Fock = `⋀ h`). Creation/annihilation `a(f), a†(g)` with `{a(f),a†(g)} = ⟪f,g⟫`, `{a(f),a(g)}=0`;
parity `Γ=(−1)^F` as the `ℤ₂`-grading involution; `dim (⋀ h) = 2 ^ dim h`.

### E1 — Dirac one-particle structure  *(category (a)/(b))*
`QIQTH/Fock/Dirac/OneParticleDirac.lean`. Spinor space + gamma matrices (Mathlib `CliffordAlgebra` of
the Minkowski form, or an explicit 4×4 rep); positive/negative-energy projection; charge conjugation;
Dirac inner product; the **Wigner** one-particle unitary Poincaré rep (spinor indices ride the
covariant wavefunction). `S_D = (iγ·∂+m)Δ_m` as the causal anticommutator kernel; spacelike vanishing
from `supp Δ_m`.

### E4 — Klein twist + Z₂-graded net + twisted duality  *(category (b); THE CRUX)*
`QIQTH/Fock/Dirac/KleinTwist.lean`. `Γ=(−1)^F`, `Z = (1+iΓ)/(1+i)` (unitary; `Z² = Γ` up to phase);
graded commutation `F₁F₂ = (−1)^{|F₁||F₂|} F₂F₁`; the abstract **twisted-duality** statement
`𝓡(H(W))' = Z 𝓡(H(W')) Z*`; even subalgebra `𝓡_+` obeys ordinary spacelike commutativity
`[𝓕(A)_+, 𝓕(B)_+] = 0`.

### E5 — CAR second quantization of one-particle BW data  *(category (b); the sharpest physics theorem)*
`QIQTH/Fock/Dirac/OneParticleBWFermi.lean`. **The fermionic mirror of `OneParticleBW`.** Given
one-particle modular data `δ_W^{it}=u(Λ_W(−2πt))`, `j_W=u(r_W)` (wedge reflection/PCT incl. charge
conjugation + spinor transf.), the Fock modular objects satisfy
**`Δ_W^{it}=Expₐ(δ_W^{it})=U(Λ_W(−2πt))`** and **`J_W = Z·Expₐ(j_W)`** with twisted duality
`𝓡(H(W))'=Z𝓡(H(W'))Z*`. Consequences bundled: modular flow = boost; J carries the twist; even
observables spacelike-commute.

### E6 — Boost-KMS β=2π + Fermi–Dirac occupation  *(category (a); mirror of `BoostKMS`)*
`QIQTH/Fock/Dirac/BoostKMSFermi.lean`. Vacuum restricted to the wedge is boost-KMS at `β=2π`; for a
Rindler mode `b_ω`, `α_t(b_ω)=e^{−iωt}b_ω`, and KMS + CAR ⇒ **`n_ω = 1/(e^{2πω}+1)`** (Fermi–Dirac;
the `+1` is the CAR signature, vs Bose `−1`).

### E7 — Graded regional capacity + the which-algebra decision  *(category (b); the QIQT-H integration point)*
`QIQTH/Fock/Dirac/GradedCapacity.lean`. State regional capacity for the **even / U(1)-invariant**
algebra; finite block form `𝒜_R ≃ ⊕_q M_{n_q}(ℂ)` ⇒ `S(ρ_R) = H(p_q) + ∑_q p_q S(ρ_q)`; combine with
E3 to get the regional bound on the chosen algebra. Document explicitly (docstring + ledger) that the
bound is for the chosen algebra, **not** a naive bosonic tensor factor.

### E8 — Even-observable records + no-signaling  *(category (b))*
`QIQTH/Fock/Dirac/EvenObservables.lean`. Re-derive the records/decoherence/no-signaling lemmas for
**even** local operations (graded tensor product); records built from even bilinears (`j^μ`, `T_μν`,
number, spin density). The CAR replacement for the χ_R coherent-sector decoherence story.

### E9 — Dirac stress tensor → Jacobson hook  *(category (b))*
`QIQTH/Fock/Dirac/DiracStressTensor.lean`. Belinfante `T_μν = (i/4)ψ̄(γ_μ∂↔_ν+γ_ν∂↔_μ)ψ`; the boost
modular Hamiltonian `2π K_boost = 2π ∫_{x¹>0} x¹ T_00`. Feed the fermionic `T_μν` into the existing
`qiqt_gr_freefield` / `QiqtToGR` slots, so the conditional Einstein-form chain runs for Dirac matter
(still conditional, still background-dependent, still classical — just no longer scalar-only).

---

## 3. Mathlib foundations to build on
- `Mathlib/LinearAlgebra/ExteriorAlgebra/*`, `CliffordAlgebra/*` (antisymmetric Fock; gamma matrices).
- `IsHermitian.cfc`, matrix functional calculus (E3 entropy via spectral sum).
- `Matrix.Order` Loewner order (`0 ≤ C ≤ 1` for the correlation matrix).
- Existing QIQT-H: `QuantumRelativeEntropy.lean` (`relEntropy`, Klein), `RecordContract.lean`
  (`shannon_le_log_card` — the bosonic mirror to imitate), `GaussianStateEntropy.lean`,
  `FiniteModularTheory.lean` (`modAut`, `kms_condition`), `SpectralPVM.lean`.
- The scalar templates to mirror: `Fock/OneParticleBW.lean`, `Fock/BoostKMS.lean`,
  `Fock/SecondQuant.lean`, `Fock/PauliJordan.lean`.

## 4. Verification (per increment)
- `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.Fock.Dirac.<Module>` green; full `lake build QIQTH`
  green.
- `#print axioms <thm>` = `propext, Classical.choice, Quot.sound` only; `bash scripts/axiom_budget_check.sh`
  budget 0.
- Wire into `QIQTH.lean` (import) + `AxiomAudit.lean` (`#print axioms`).
- ONE commit per increment on `main`, `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`, push
  via `git -c http.sslBackend=schannel push origin main`; update the Progress log below.

## 5. Honest scale
Free-Dirac one-particle / CAR quasi-free / Araki CAR rel-entropy / BW-for-fermions / twisted duality /
Rindler-KMS-FD are all **known/clean** physics → genuine near-term Lean work. The QIQT-H-specific
integration (graded regional capacity, even-observable no-signaling, replacing χ_R, Dirac-`T_μν` in
Jacobson) is **frontier-but-tractable**. **Actual QED** (gauge dressing, Gauss-law edge modes,
infraparticles, soft photons, nonperturbative 4D interacting construction) is **interacting-QFT-hard**
and stays **cited, not formalized**. No `sorry`; never claim the value of `G`; the `1/4` ratio is
matter-renormalization-dependent; defer DHR/edge-modes/QED; leave green and checkpoint honestly at each
frontier.

## 6. Progress log
- 2026-06-28 — plan opened (GPT-5.5-pro-vetted). Crux = Z₂-graded CAR net + twisted duality; records on
  even/observable algebra.
- 2026-06-28 — **E3 DONE** (`QIQTH/Fock/Dirac/QuasiFreeEntropy.lean`, axiom-free, budget 0). The CAR
  capacity bound: `binaryEntropy c = negMulLog c + negMulLog(1−c)`, `binaryEntropy_le_log_two`
  (≤ log 2, via concavity of `negMulLog` — Jensen at `c, 1−c`, max at `c=1/2`), `binaryEntropy_half`
  (= log 2), `binaryEntropy_nonneg`; `fermionicGaussianEntropy c = ∑ binaryEntropy(c i)`,
  `fermionicGaussianEntropy_nonneg`, **`fermionicGaussianEntropy_le_card_log_two`** (≤ n·log 2) and
  **`fermionicGaussianEntropy_le_log_dim`** (≤ log(2ⁿ) = log dim(⋀ h_R)) — the fermionic mirror of
  `shannon_le_log_card`, i.e. `S_vN ≤ log N_R` survives bosons → fermions. Wired into `QIQTH.lean` +
  `AxiomAudit.lean` (both theorems standard-3). Build green (`lake build QIQTH.AxiomAudit`, 8729 jobs);
  `axiom_budget_check.sh` raw count 0.
- 2026-06-28 — **E2 (dimension) DONE** (`QIQTH/Fock/Dirac/CAR.lean`, axiom-free, budget 0). The
  antisymmetric (CAR) Fock space = the exterior algebra `CARFock 𝕜 M := ExteriorAlgebra 𝕜 M`.
  **`finrank_CARFock : dim(⋀ M) = 2 ^ finrank M`** (each mode is a qubit; via Mathlib
  `Module.Basis.ExteriorAlgebra` indexed by `Finset I`, `card = 2^card I`). **`fermionicGaussianEntropy_le_log_carFockDim`**
  combines it with E3 so the bound reads `S_vN ≤ log N_R` with `N_R = dim(CARFock 𝕜 h_R)` the **literal**
  Fock dimension — closing the E3↔Fock loop. Wired into `QIQTH.lean` + `AxiomAudit.lean` (both
  standard-3); `lake build QIQTH.Fock.Dirac.CAR` green (2399 jobs); budget 0. **Deferred E2 sub-item**
  (checkpointed, not blocked): the full CAR operator algebra `a(f),a†(g)` with `{a(f),a†(g)}=⟪f,g⟫`,
  `{a(f),a(g)}=0` + parity `Γ=(−1)^F` from the existing Mathlib grading
  `DirectSum.Decomposition (fun n ↦ ⋀[𝕜]^n M)`. Next: **E1** (Dirac one-particle + `S_D` kernel) or the
  E2 operator-algebra sub-item; then **E4** (Klein twist / twisted duality — the crux).
- 2026-06-28 — **E2 parity / E4-seed DONE** (`QIQTH/Fock/Dirac/Parity.lean`, axiom-free, budget 0). The
  fermion parity `Γ=(−1)^F` as the grade involution on `⋀ M`: **`parity 𝕜 M : ⋀M →ₐ ⋀M`** built via the
  exterior-algebra universal property (`lift (−ι)`, the mirror of Mathlib `CliffordAlgebra.involute`);
  `parity_ι : Γ(ι m) = −ι m` (one-particle/odd → eigenvalue −1), `parity_one : Γ1 = 1` (vacuum even,
  +1), `parity_comp_parity`/`parity_involutive`/`parity_parity` (`Γ∘Γ=id`), and `parityEquiv` (Γ as an
  `AlgEquiv`, the form E4 consumes). This is the **seed of the E4 crux** (Klein twist `Z=(1+iΓ)/(1+i)`
  needs Γ) and of the even/observable algebra (E7/E8). Wired into `QIQTH.lean` + `AxiomAudit.lean`
  (both standard-3); `lake build QIQTH.Fock.Dirac.Parity` green (2400 jobs); budget 0. Next: **E4**
  (the even/odd ±1 eigenspace decomposition `⋀M = (⋀M)₊⊕(⋀M)₋`, then the Klein twist `Z` over `𝕜=ℂ`
  and the abstract twisted-duality statement `𝓕(W)'=Z𝓕(W')Z*`), or **E1** (Dirac one-particle).
