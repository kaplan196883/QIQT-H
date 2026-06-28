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
- 2026-06-28 — **E4 crux (Klein-twist algebra) DONE** (`QIQTH/Fock/Dirac/KleinTwist.lean`, axiom-free,
  budget 0). The **Klein twist** `kleinTwist γ = (1+iγ)/(1+i)` for an involution `γ` in a ℂ-algebra, with
  its defining identity **`kleinTwist_sq : Z² = γ`** (proof: expand, push central ℂ-scalars through `γ`,
  collapse `γ·γ=1`, and the two ℂ-scalar facts `α²+β²=0`, `2αβ=1` with `α=(1+i)⁻¹`, `β=i(1+i)⁻¹`) and
  **`kleinTwist_sq_sq : Z⁴ = 1`**. For `γ=Γ=(−1)^F` (Parity.lean) this is the Klein twist whose twisted
  duality `𝓕(W)'=Z𝓕(W')Z*` is the AQFT spin–statistics form for the electron — the crux that the
  modular flow stays the geometric boost (no sign) while the **commutant/J carries the twist**. Wired
  into `QIQTH.lean` + `AxiomAudit.lean` (both standard-3); `lake build QIQTH.Fock.Dirac.KleinTwist` green
  (2401 jobs); budget 0. **Checkpointed (next, not blocked):** Z unitary `Z*Z=1` (needs `StarRing`, `γ`
  self-adjoint); the operator-algebra twisted-duality theorem + instantiating `γ` as the second-quantized
  parity unitary `u_Γ` on the CAR inner-product space (**E5** — needs the inner product / GNS, the
  genuine operator-algebra frontier). Next: **E5/E6** (one-particle BW data → `Δ_W^it`=boost, `J_W=Z·Expₐ(j_W)`,
  boost-KMS β=2π, Fermi–Dirac), or **E1** (Dirac one-particle + `S_D` kernel).
- 2026-06-28 — **E6 (Fermi–Dirac Unruh occupation) DONE** (`QIQTH/Fock/Dirac/FermiDirac.lean`,
  axiom-free, budget 0). The CAR `+1` vs Bose `−1` thermal signature: `fermiDirac β ω = 1/(e^{βω}+1)`,
  **`fermiDirac_kms_balance : n = e^{−βω}(1−n)`** (KMS thermal condition + CAR `bb†=1−b†b`),
  **`fermiDirac_unique`** (the balance's unique solution is Fermi–Dirac), `fermiDirac_mem_Ioo` (`0<n<1`,
  Pauli — at most singly occupied), and **`boseEinstein_kms_balance`** (the CCR sign `aa†=1+a†a` gives
  `n=e^{−βω}(1+n) → 1/(e^{βω}−1)`: same Unruh temperature, denominator sign `−1` vs CAR `+1` — the
  spin–statistics signature at the occupation level); `rindlerOccupationFermi ω = fermiDirac (2π) ω`
  (Unruh `β=2π`). Wired into `QIQTH.lean` + `AxiomAudit.lean` (all standard-3); `lake build
  QIQTH.Fock.Dirac.FermiDirac` green (1913 jobs); budget 0. **Honest:** the *balance relation* is the
  KMS+CAR input (presupposes the modular/KMS state — cited E5 machinery); derived here is the occupation
  FROM the balance. Next: **E5** (CAR 2nd-quant of one-particle BW data — the operator-algebra frontier:
  `Δ_W^it`=boost, `J_W=Z·Expₐ(j_W)`, twisted duality; needs inner product/GNS), or **E1** (Dirac
  one-particle + `S_D` kernel), or the **Z-unitary** checkpoint from E4.
- 2026-06-28 — **E7/E8-seed (even/observable algebra) DONE** (`QIQTH/Fock/Dirac/EvenObservables.lean`,
  axiom-free, budget 0). The §0 "which algebra" decision, formalized: `IsEven a := parity a = a` (the
  Γ-fixed, eigenvalue-`+1` observables); closure (`isEven_one/zero/add/mul/smul/algebraMap`); and the
  bundled **`evenSubalgebra 𝕜 M : Subalgebra`** — the Γ-fixed subalgebra to which records/capacity
  attach. The load-bearing physical fact **`isEven_ι_mul_ι`**: a product of two one-particle (odd)
  generators is EVEN, so **fermion bilinears (ψ̄ψ, j^μ, T_μν) are Γ-fixed even observables** (the
  records), while one-particle states are odd (`parity_one_particle : Γ(ι m)=−ι m`) — exactly why
  records = even bilinears and the χ_R c-number calculus does not transfer. Wired into `QIQTH.lean` +
  `AxiomAudit.lean` (both standard-3); `lake build QIQTH.Fock.Dirac.EvenObservables` green (2401 jobs);
  budget 0. Next E7/E8: graded regional capacity block decomposition `S(ρ_R)=H(p_q)+Σp_q S(ρ_q)` +
  even-observable no-signaling. Remaining frontier (checkpointed): **E5** (operator-algebra BW data /
  twisted-duality theorem / GNS), **E1** (Dirac one-particle + `S_D`), E4 **Z-unitary** (`StarRing`).
- 2026-06-28 — **E7 (graded regional capacity) DONE** (`QIQTH/Fock/Dirac/GradedCapacity.lean`,
  axiom-free, budget 0). The charge/parity block decomposition for the graded regional algebra
  `𝒜_R ≃ ⊕_q M_{n_q}`: **`gradedShannon_chain_rule`** — the record entropy decomposes as
  `S = H(p) + Σ_q p_q S(w_q)` (sector mixing entropy + average within-sector entropy), via the entropy
  chain identity `Real.negMulLog_mul`; and **`gradedShannon_capacity_le`** — each block contributes
  `≤ log n_q` (per-sector `RecordContract.shannon_le_log_card` / the E3 CAR `S ≤ log dim`), so
  `S(ρ_R) ≤ H(p) + Σ_q p_q log n_q`: **the finite-capacity bound passes to the graded regional algebra**
  to which (§0) records/capacity attach. Wired into `QIQTH.lean` + `AxiomAudit.lean` (both standard-3);
  `lake build QIQTH.Fock.Dirac.GradedCapacity` green (3055 jobs); budget 0. **Honest:** the further
  collapse to a single `log(Σ_q n_q) = log dim(⊕M_{n_q})` needs a Jensen/log-sum step over the sector
  weights (next E7 sub-item). Remaining frontier (checkpointed): **E5** (operator-algebra BW data /
  twisted-duality theorem / GNS), **E1** (Dirac one-particle + `S_D`), E4 **Z-unitary** (`StarRing`),
  **E8** (even-observable no-signaling), **E9** (Dirac `T_μν` → Jacobson hook).
- 2026-06-28 — **E7 completion (full graded capacity) DONE** (added to `GradedCapacity.lean`,
  axiom-free, budget 0). The Gibbs/log-sum collapse closing E7: **`entropy_add_avgLogCard_le`** —
  `H(p) + Σ_q p_q log n_q ≤ log(Σ_q n_q)` (via `log x ≤ x−1` per sector; equality at the maximally-mixed
  `p_q ∝ n_q`), and **`gradedShannon_le_log_total`** — chaining chain-rule + per-sector capacity +
  collapse to the **headline `S(ρ_R) ≤ log(Σ_q n_q) = log dim(⊕_q M_{n_q})`**: the fermionic
  `S_vN ≤ log N_R` on the charge/parity-graded (even/observable) regional algebra. Wired into
  `AxiomAudit.lean` (both standard-3); `lake build QIQTH.Fock.Dirac.GradedCapacity` green (3055 jobs);
  budget 0. **E7 now complete** (chain rule → per-block bound → total `log dim`). Remaining frontier
  (checkpointed): **E5** (operator-algebra BW data / twisted-duality theorem / GNS), **E1** (Dirac
  one-particle + `S_D`), E4 **Z-unitary** (`StarRing`), **E8** (even-observable no-signaling), **E9**
  (Dirac `T_μν` → Jacobson hook).
- 2026-06-28 — **E6→E5 bridge (per-mode modular Hamiltonian) DONE** (added to `FermiDirac.lean`,
  axiom-free, budget 0). **`fermiDirac_logit`** — for a fermionic mode with occupation
  `n = fermiDirac β ω`, the modular energy is the logit `log((1−n)/n) = βω`. This is the **single-mode
  form of the fermionic modular Hamiltonian `K = log((1−C)/C)`** (the quasi-free modular generator of
  `QuasiFreeEntropy`): the logit of the occupation IS the inverse-temperature-scaled mode energy,
  linking the E6 occupation to the modular generator `Δ^{it}=e^{−itK}` (the E5 target). Wired into
  `AxiomAudit.lean` (standard-3); `lake build QIQTH.Fock.Dirac.FermiDirac` green (1925 jobs); budget 0.
  Remaining frontier (checkpointed): **E5** (full operator-algebra BW data / twisted-duality theorem /
  GNS), **E1** (Dirac one-particle + `S_D`), E4 **Z-unitary** (star-algebra), **E8** (even-observable
  no-signaling), **E9** (Dirac `T_μν` → Jacobson hook).
- 2026-06-28 — **E4 Z-unitary (crux completion) DONE** (`QIQTH/Fock/Dirac/KleinTwistUnitary.lean`,
  axiom-free, budget 0). **`kleinTwist_star_mul_self`** — for a self-adjoint involution `γ`
  (`star γ = γ`, `γ·γ=1`) in a ℂ-*-algebra, **`Z*Z = 1`**: the Klein twist is **unitary**. With
  `kleinTwist_sq` (`Z²=Γ`) this makes `Z` a unitary of order 4 (a unitary fourth root of the parity `Γ`)
  — the genuine intertwiner the twisted modular duality `𝓕(W)'=Z𝓕(W')Z*` requires. Proof = the
  `kleinTwist_sq` expansion with conjugate scalars `ᾱ,β̄` and the identities `ᾱα+β̄β=1`, `ᾱβ+β̄α=0`
  (`α=(1+i)⁻¹`, `β=i(1+i)⁻¹`). **The Klein-twist ALGEBRA is now complete: `Z²=Γ`, `Z⁴=1`, `Z*Z=1`.**
  Wired into `QIQTH.lean` + `AxiomAudit.lean` (standard-3); `lake build QIQTH.Fock.Dirac.KleinTwistUnitary`
  green (2402 jobs); budget 0. Remaining frontier (checkpointed): **E5** (full operator-algebra BW data /
  twisted-duality theorem / GNS — instantiating `γ` = second-quantized parity unitary on the CAR
  inner-product space), **E1** (Dirac one-particle + `S_D`), **E8** (even-observable no-signaling),
  **E9** (Dirac `T_μν` → Jacobson hook).
- 2026-06-28 — **E8 seed (even records commute with field operators) DONE** (added to
  `EvenObservables.lean`, axiom-free, budget 0). The no-signaling kernel: **`ι_mul_ι_swap`** — the
  one-particle (odd) generators anticommute `ι a·ι b = −ι b·ι a` (from `ι v·ι v = 0` on `a+b`); hence
  **`ι_mul_ι_comm_ι`** — a fermion bilinear `ι a·ι b` (an even observable/record, `isEven_ι_mul_ι`)
  **commutes** with a field operator `ι c`: `(ι a·ι b)·ι c = ι c·(ι a·ι b)`. So the electron's records
  (even bilinears `j^μ`, `T_μν`) commute with the odd field operators — a record measurement cannot
  signal through the field algebra. (Both depend only on `[propext, Quot.sound]`.) Wired into
  `AxiomAudit.lean`; `lake build QIQTH.Fock.Dirac.EvenObservables` green (2401 jobs); budget 0. **Honest:**
  this is the single-algebra generator-level kernel; the full bipartite no-signaling (graded tensor
  product across spacelike-separated regions) is the next E8 sub-item. Remaining frontier (checkpointed):
  **E5** (operator-algebra BW data / twisted-duality theorem / GNS), **E1** (Dirac one-particle + `S_D`),
  **E8 bipartite** (graded tensor product), **E9** (Dirac `T_μν` → Jacobson hook).
- 2026-06-28 — **E1 spinor core (Dirac gamma / Clifford algebra) DONE**
  (`QIQTH/Fock/Dirac/DiracGamma.lean`, axiom-free, budget 0). The electron is a Dirac spinor; its
  spin/Lorentz structure is the Clifford algebra of the metric. `diracGamma Q v` = the gamma operator in
  direction `v` (Clifford generator `ι Q v`; for an orthonormal Minkowski basis `γ_μ = diracGamma Q e_μ`).
  **`diracGamma_sq`** : `γ(v)² = Q v` (`γ_μ²=η_μμ`); **`diracGamma_anticomm`** : `{γ_a,γ_b} = polar Q a b
  = 2η(a,b)` — THE defining Dirac/Clifford relation `{γ^μ,γ^ν}=2η^{μν}`; `diracGamma_anticomm_ortho` /
  `diracGamma_swap_ortho` : `{γ_μ,γ_ν}=0`, `γ_μγ_ν=−γ_νγ_μ` for `μ≠ν`. The spinor-representation core of
  E1, on Mathlib's `CliffordAlgebra`. Wired into `QIQTH.lean` + `AxiomAudit.lean` (standard-3);
  `lake build QIQTH.Fock.Dirac.DiracGamma` green (1766 jobs); budget 0. **Honest:** the full Dirac
  one-particle Hilbert space (±energy splitting, Dirac inner product, Wigner Poincaré rep) + the causal
  kernel `S_D=(iγ·∂+m)Δ_m` (need the field in momentum space) remain the E1 frontier (checkpointed).
  Remaining: **E5** (operator-algebra BW data / twisted-duality theorem / GNS), **E1 field** (one-particle
  space + `S_D`), **E8 bipartite** (graded tensor product), **E9** (Dirac `T_μν` → Jacobson hook).
- 2026-06-28 — **E1 Clifford ℤ₂-grading (Lorentz generators are even) DONE** (added to `DiracGamma.lean`,
  axiom-free, budget 0). The Clifford algebra carries a `ℤ₂`-grading `evenOdd Q i` parallel to the CAR
  parity `Γ=(−1)^F`: **`diracGamma_mem_odd`** (a single gamma `γ_μ` is **odd**, grade 1),
  **`diracGamma_mul_mem_even`** (a product of two gammas is **even**, grade 0), `diracSigma a b =
  γ_aγ_b−γ_bγ_a` (the **Lorentz generator** `σ_μν=(i/4)[γ_μ,γ_ν]`), and **`diracSigma_mem_even`**
  (`σ_ab ∈ evenOdd Q 0` — the spinor representation of the Lorentz group sits in the **even** Clifford
  subalgebra). This is the gamma-side parallel of the CAR parity grading — both axes (Clifford spin /
  CAR statistics) carry the same `ℤ₂` even/odd structure that is the crux. Wired into `AxiomAudit.lean`
  (standard-3); `lake build QIQTH.Fock.Dirac.DiracGamma` green (1774 jobs); budget 0. Remaining frontier
  (checkpointed): **E5** (operator-algebra BW data / twisted-duality theorem / GNS), **E1 field**
  (one-particle space + `S_D` in momentum space), **E8 bipartite** (graded tensor product), **E9**
  (Dirac `T_μν` → Jacobson hook). These need GNS / momentum-space field operators / graded tensor
  products — the operator-algebra/QFT-construction tier beyond the self-contained algebraic spine.
- 2026-06-28 — **E8 (even records pairwise commute) DONE** (added to `EvenObservables.lean`, axiom-free,
  budget 0). **`evenBilinear_comm`** — two fermion bilinears commute,
  `(ι a·ι b)·(ι c·ι d) = (ι c·ι d)·(ι a·ι b)`: the electron's even records (`j^μ`, `T_μν`) pairwise
  commute, so they are jointly measurable and cannot signal between one another — the no-signaling
  statement for the even records themselves (a step beyond `ι_mul_ι_comm_ι`). Proof = the bilinear
  commutes with each generator, moved through twice. Wired into `AxiomAudit.lean` (`[propext,
  Quot.sound]`); `lake build QIQTH.Fock.Dirac.EvenObservables` green (2401 jobs); budget 0. Remaining
  frontier (checkpointed): **E5** (GNS / twisted-duality theorem), **E1 field** (`S_D` momentum space),
  **E8 bipartite** (graded tensor product assigning records to spacelike regions), **E9** (Dirac `T_μν`).
- 2026-06-28 — **E3 (CAR / Araki relative entropy positivity) DONE** (added to `QuasiFreeEntropy.lean`,
  axiom-free, budget 0). The fermionic relative entropy (the optional E3 item): `fermionicBinaryRelEntropy
  c d = c·log(c/d) + (1−c)·log((1−c)/(1−d))` (binary KL divergence), **`fermionicBinaryRelEntropy_nonneg`**
  (`0 ≤ D(c‖d)` via Gibbs `log x ≤ x−1` — the fermionic mirror of Klein's inequality
  `QuantumRelativeEntropy.relEntropy_nonneg`), and **`fermionicGaussianRelEntropy_nonneg`** (`S(ρ_C‖ρ_D) ≥ 0`,
  the CAR/Araki relative entropy positivity, summed over modes). Relative entropy — not the bare vN
  entropy — controls the modular / entanglement-first-law side of the area law, so this is the fermionic
  input to that route. Wired into `AxiomAudit.lean` (standard-3); `lake build QIQTH.Fock.Dirac.QuasiFreeEntropy`
  green (2179 jobs); budget 0. Remaining frontier (checkpointed): **E5** (GNS / modular flow theorem —
  unbuilt in any proof assistant), **E1 field** (`S_D` momentum space), **E8 bipartite** (graded tensor
  product), **E9** (Dirac `T_μν`). NOTE (web search 2026-06-28): PhysLean has fermionic CAR/Wick
  second-quantization — leverage it for the E2-full/E5 operator layer rather than rebuild.
- 2026-06-28 — **E6 (particle–hole symmetry) DONE** (added to `FermiDirac.lean`, axiom-free, budget 0).
  **`fermiDirac_particle_hole`** — `n(βω) + n(−βω) = 1`: flipping the sign of the mode energy
  (particle ↔ hole / charge conjugation) sends `n ↦ 1−n`. The distribution-level shadow of the
  electron's particle/antiparticle (Dirac-sea) structure — a hole at `+ω` is a particle at `−ω`. Wired
  into `AxiomAudit.lean` (standard-3); `lake build QIQTH.Fock.Dirac.FermiDirac` green (1925 jobs); budget
  0. **The self-contained algebraic/analytic layer of the electron substrate is now exhaustively covered;
  further genuine progress requires PhysLean integration (CAR operator layer) or the modular-theory
  frontier (Tomita–Takesaki, unbuilt in any proof assistant).**

## 7. PhysLean integration (2026-06-28)

The remaining E2-full / E5 operator tier (fermionic CAR creation/annihilation operators, Wick algebra)
is already formalized in **PhysLean** (HEPLean). Rather than rebuild it, QIQT-H now **depends on
PhysLean**:

- **Pinned to commit `d0ee4af6f490`** (the last PhysLean commit on Lean v4.30.0), whose Mathlib pin
  `c5ea00351c28 @ v4.30.0` **exactly matches** QIQT-H's — so the existing Mathlib build is reused,
  **no v4.31 bump / multi-hour rebuild**. `lake update PhysLean` resolved to a single Mathlib; PhysLean's
  `FieldStatistics.Basic` builds green in QIQT-H (41 s, reusing cache).
- **Bridge module `QIQTH/Fock/Dirac/PhysLeanBridge.lean`** fuses PhysLean's `ℤ₂` `FieldStatistic` group
  with the substrate's parity/Clifford gradings: `electron_pair_bosonic` (`fermionic·fermionic=bosonic`
  ↔ `isEven_ι_mul_ι`), `statParity : FieldStatistic →+ ℤ₂` (the shared grading hom, `statParity_mul`),
  `electron_statParity = 1` (the electron is odd). Axiom-free; budget 0; full QIQTH build green with
  PhysLean in the graph.
- **Available for the follow-on E2-full/E5 work:** `Physlib.QFT.PerturbationTheory.{CreateAnnihilate,
  FieldSpecification.CrAnFieldOp, WickAlgebra.Basic, WickAlgebra.SuperCommute}` — the fermionic CAR
  a/a† operators + the graded (super)commutator that is the QIQT-H crux.

This closes the "build vs reuse" decision for the operator layer: **reuse PhysLean**. The other frontier
(E5 modular flow / Tomita–Takesaki) remains unbuilt in any proof assistant.
- 2026-06-28 — **PhysLean bridge increment: electron exchange sign = −1** (added to
  `PhysLeanBridge.lean`, axiom-free, budget 0). **`electron_exchangeSign`** — `𝓢(fermionic, fermionic)
  = −1` (PhysLean `exchangeSign`): exactly the graded-commutation sign `(−1)^{|F₁||F₂|}` of the crux
  `F₁F₂ = (−1)^{|F₁||F₂|}F₂F₁` for two fermions, the **same `−1`** as the substrate's
  `ι_mul_ι_swap : ι a·ι b = −(ι b·ι a)`. PhysLean's exchange-sign machinery and the QIQT-H CAR
  anticommutation carry the identical Pauli sign — the first substantive use of PhysLean inside the
  substrate. `lake build QIQTH.Fock.Dirac.PhysLeanBridge` green (2097 jobs); standard-3; budget 0. Next:
  build the CAR a/a† operators on Physlib `CrAnFieldOp`/`WickAlgebra`/`SuperCommute` (E2-full/E5).
