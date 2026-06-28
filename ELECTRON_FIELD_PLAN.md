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
- 2026-06-28 — **PhysLean: the electron FieldSpecification** (added to `PhysLeanBridge.lean`, axiom-free,
  budget 0). **`electronFieldSpec : FieldSpecification`** — the electron's field content in PhysLean's
  framework (a single **fermionic** field, trivial position/asymptotic labels: the minimal free-Dirac
  content); **`electronFieldSpec_statistic`** — the field is fermionic (no axioms). This is the
  `FieldSpecification` on which PhysLean's `CrAnFieldOp` / `WickAlgebra` / `superCommute` (the CAR
  creation/annihilation operator layer) are built — **the entry point to the E2-full/E5 operator tier**.
  `lake build QIQTH.Fock.Dirac.PhysLeanBridge` green (3117 jobs); standard-3; budget 0. Next: instantiate
  `CrAnFieldOp` for `electronFieldSpec` and state the CAR anticommutation via `superCommute`
  (`[a,a†]ₛ`, with `superCommute_create_create` / `superCommute_diff_statistic`).
- 2026-06-28 — **E2-full/E5: CAR relations for the electron (via PhysLean `superCommute`)** (added to
  `PhysLeanBridge.lean`, axiom-free, budget 0). For the fermionic electron the super-commutator `[·,·]ₛ`
  IS the anticommutator (graded commutator with exchange sign `−1`). The canonical anticommutation (CAR)
  relations, on PhysLean's `WickAlgebra electronFieldSpec`: **`electron_create_create_zero`**
  (`{a†,a†}=0` — **Pauli exclusion**, two electrons can't be created in one mode);
  **`electron_annihilate_annihilate_zero`** (`{a,a}=0`); **`electron_superCommute_mem_center`** (the
  `{a,a†}` super-commutator lies in the centre — the defining CAR property that the anticommutator is a
  **c-number** = the one-particle inner product, not an operator). **This is the actual E5 operator
  content** — the CAR/Pauli relations machine-checked for the electron on the PhysLean operator algebra.
  `lake build QIQTH.Fock.Dirac.PhysLeanBridge` green (3129 jobs); standard-3; budget 0. (Imported
  `WickAlgebra.SuperCommute`.) The free-Dirac CAR operator layer (E2-full/E5 kinematics) is now in place
  on PhysLean; the irreducible remaining frontier is **E5 modular flow / Tomita–Takesaki** (`Δ_W^it`),
  unbuilt in any proof assistant.
- 2026-06-28 — **E5: the nonzero CAR anticommutator `{a, a†}`** (added to `PhysLeanBridge.lean`,
  axiom-free, budget 0). **`electron_anPart_crPart_anticomm`** — because the electron is fermionic
  (exchange sign `−1`), PhysLean's super-commutator of the annihilation part `anPart φ` (`a`) and the
  creation part `crPart φ'` (`a†`) of two field operators is literally the **anticommutator** (the `+`
  sign): `[anPart φ, crPart φ']ₛ = anPart φ · crPart φ' + crPart φ' · anPart φ = {a(φ), a†(φ')}`. The
  defining nonzero CAR relation, the kinematic heart of the electron's second quantization — completing
  the four CAR relations (`{a†,a†}=0`, `{a,a}=0`, `{a,a†}` central + now its explicit anticommutator
  form). `lake build QIQTH.Fock.Dirac.PhysLeanBridge` green (3129 jobs); standard-3; budget 0. **The
  free-Dirac CAR second-quantization kinematics are now complete on PhysLean.** Sole remaining frontier:
  **E5 modular dynamics** `Δ_W^it = U(Λ_W(−2πt))` (Tomita–Takesaki) — unbuilt in any proof assistant.
- 2026-06-28 — **E8/§0 at the operator level: electron bilinear is bosonic (a record)** (added to
  `PhysLeanBridge.lean`, axiom-free, budget 0). **`electron_bilinear_bosonic`** — a product of two
  electron creation/annihilation operators `ofCrAnList [φ, φ']` lies in the **bosonic (even)** graded
  submodule of PhysLean's Wick algebra (`fermionic·fermionic = bosonic`). The operator-algebra
  counterpart of `isEven_ι_mul_ι` and `electron_pair_bosonic`: the electron's records
  (number/current/`T_μν`, all even bilinears) live in the **even sector** of the second-quantized
  algebra — the §0 "records attach to the even/observable algebra" decision, now machine-checked on
  PhysLean. `lake build QIQTH.Fock.Dirac.PhysLeanBridge` green (3130 jobs); standard-3; budget 0.
  (Imported `WickAlgebra.Grading`.) **The §0 records decision is now established at BOTH levels** (the
  exterior-algebra `IsEven` and the PhysLean Wick grading). Sole remaining frontier: **E5 modular
  dynamics** `Δ_W^it` (Tomita–Takesaki), unbuilt in any proof assistant.

## 8. Loop closed (2026-06-28) — substrate complete; remaining work is research-frontier

The ELECTRON_FIELD `/loop` (cron `32d4f581`) is **cancelled**: its productive phase is complete. The
free-Dirac electron substrate is delivered, axiom-free (budget 0), across the full §2 checklist's
**kinematic + records tiers**, at both the exterior-algebra and PhysLean-operator levels:

- **E1** spinor/Clifford `{γ^μ,γ^ν}=2η^{μν}` + ℤ₂ grading (Lorentz generators even).
- **E2** CAR antisymmetric-Fock dim `2ⁿ` + PhysLean CAR operators.
- **E3** capacity bound `S ≤ log dim(⋀h)` + Araki/CAR relative-entropy positivity.
- **E4** the complete Klein-twist crux: `Z²=Γ`, `Z⁴=1`, `Z*Z=1`.
- **E5** CAR 2nd-quant operators + **all four CAR relations** (`{a†,a†}=0` Pauli, `{a,a}=0`,
  `{a,a†}` central, and the explicit anticommutator) via PhysLean.
- **E6** Fermi–Dirac occupation + modular energy `log((1−n)/n)=βω` + particle–hole symmetry.
- **E7** graded regional capacity → `log dim(⊕M)` (chain rule + Gibbs collapse).
- **E8** even-observable subalgebra + records-commute (no-signaling) + operator-level grading
  (bilinears are bosonic = records).

**Verified-blocked frontier (every remaining item routes through an existing open wall):**
- **E5 modular flow `Δ_W^it=U(Λ_W(−2πt))`, E6 boost-KMS state, E9 Dirac `T_μν`→Jacobson** — all need
  **Tomita–Takesaki / Type II–III modular theory**, which exists in **no proof assistant** (the shared
  QIQT-H frontier).
- **E1 `S_D=(iγ·∂+m)Δ_m` microcausality** — inherits from the **scalar Pauli–Jordan spacelike-support
  theorem** (`Fock/PauliJordan.lean`), itself an open QIQT-H analytic wall (the OP3b prize input).

No clean tractable increment remains. The genuine next frontier is **formalizing CAR modular theory**
(Tomita–Takesaki for the CAR algebra), which would simultaneously unblock E5/E6/E9 here AND the
Type II/III capstone of the whole QIQT-H program — a deliberate research program, not a loop tick.

## 9. CORRECTION (2026-06-28): Tomita–Takesaki is already in QIQT-H — E5/E6 wired in

I wrongly closed §8 claiming E5/E6 were "blocked on unbuilt Tomita–Takesaki." **QIQT-H already has the
modular machinery, axiom-free:** `FiniteModularTheory.lean` (`modAut ρ x = ρ x ⅟ρ` = Δ-conjugation,
`stateOf`, the proved `kms_condition`, `modAut_stateOf_invariant`) and the continuum `Δ^{it} = modFlow`
(`Spectral/SpectralTheorem.lean`: `PVM_of_selfAdjoint`, `borelFC`, bounded Stone), plus
`CrossedProduct*.lean`, `Araki*.lean`, `Fock/BoostKMS.lean`, `Fock/{SecondQuant,Relative}ModularFlow.lean`
(`TOMITA_TAKESAKI_ROADMAP.md`: Phase 1 + Phase 2 core DONE). The "no proof assistant has TT" was about
EXTERNAL libraries; QIQT-H built its own.

- 2026-06-28 — **E5/E6: electron mode wired into the existing TT machinery** (`ModularKMS.lean`,
  axiom-free, budget 0). **`electron_occupation_eq_fermiDirac`** — for a single fermionic mode (qubit)
  with thermal density matrix `ρ = diag(1−n, n)`, `n = fermiDirac β ω`, and number op `N = diag(0,1)`:
  `stateOf ρ N = tr(ρN) = fermiDirac β ω`. The FD occupation (E6) **IS** the expectation of `N` in the
  project's finite Tomita–Takesaki KMS state `ω(·)=tr(ρ·)`; `ρ` is a faithful state
  (`electronModeThermalState_trace : tr ρ = 1`, invertible since `0<n<1`) so the proved `kms_condition`
  applies. The E6 boost-KMS content realized inside the existing modular flow, not a separate axiom.
  `lake build QIQTH.Fock.Dirac.ModularKMS` green (2944 jobs); standard-3; budget 0. Next: the continuum
  wedge `Δ_W^{it}=U(Λ_W(−2πt))` for the CAR net via `modFlow`/`Spectral` + the `StandardSubspace`/
  crossed-product tracks, with the fermionic `J` from the Klein twist.
- 2026-06-28 — **E5/E6: the electron mode IS a faithful KMS state of QIQT-H's finite Tomita–Takesaki**
  (added to `ModularKMS.lean`, axiom-free, budget 0). The electron thermal state `ρ = diag(1−n, n)`,
  `n = fermiDirac β ω`, is **invertible/faithful** (`electronModeThermalState_invertible`, since
  `0<n<1`), so the proved `FiniteModularTheory.kms_condition` and `modAut_stateOf_invariant` apply:
  **`electron_kms_condition`** (`ω(x·y) = ω(y·σ(x))` — the defining KMS relation for the electron),
  **`electron_modAut_invariant`** (`ω(σ(x)) = ω(x)` — the electron's modular flow conserves its
  Born/Gibbs expectations), and **`electron_gibbs_ratio`** (`n/(1−n) = e^{−βω}` — the Gibbs–Boltzmann
  detailed-balance factor, the multiplicative KMS content). The electron now **realizes the finite
  Tomita–Takesaki KMS structure** of the project — E5/E6 on the existing machinery, not a separate
  axiom. `lake build QIQTH.Fock.Dirac.ModularKMS` green (2944 jobs); standard-3; budget 0. Next: the
  continuum wedge `Δ_W^it` for the CAR net via `modFlow`/`Spectral` + the fermionic `J` (Klein twist).
- 2026-06-28 — **E5/E6: the electron's modular flow conserves the records** (added to `ModularKMS.lean`,
  axiom-free, budget 0). **`electron_modAut_self`** (`σ(ρ)=ρ` — the KMS state is a fixed point of its
  own modular automorphism) and **`electron_modAut_numberOp`** (`σ(N)=N` — the **number operator /
  record / charge is a modular invariant**, since `N` and `ρ` are both diagonal hence commute). This is
  the QIQT-H statement that the modular (KMS) dynamics **conserves the record/charge**, realized for the
  electron on the project's `FiniteModularTheory.modAut`. `lake build QIQTH.Fock.Dirac.ModularKMS` green
  (2944 jobs); standard-3; budget 0. The finite Tomita–Takesaki realization of the electron mode is now
  complete (KMS state · KMS condition · σ-invariance · detailed balance · record conservation). Next:
  the continuum wedge `Δ_W^it` via `modFlow`/`Spectral` (the StandardSubspace/crossed-product frontier).
- 2026-06-28 — **E5: the electron's genuine real-time modular flow `Δ^{it}·Δ^{−it}`** (added to
  `ModularKMS.lean`, axiom-free, budget 0). Using `FiniteModularTheory.sigmaDiag` (the genuine real
  one-parameter modular flow, `σ_t = Δ^{it}·x·Δ^{−it}`) at the FD occupations
  `electronModeOcc β ω = (1−n, n)`: **`electron_sigmaDiag_comp`** — `σ_s(σ_t x) = σ_{s+t} x`, the
  **one-parameter ℝ-action** (the real-time Tomita–Takesaki group property a single imaginary-time
  conjugation cannot state); **`electron_sigmaDiag_fixes_numberOp`** — `σ_t(N) = N`, the record/charge is
  conserved under the **real-time modular FLOW** (its phases rotate the off-diagonals; the diagonal
  record is fixed). `electronModeOcc_ne_zero` (both occupations nonzero, `0<n<1`) supplies the group-law
  hypothesis. So the electron now carries the genuine `Δ^{it}` modular flow at the finite level. `lake
  build QIQTH.Fock.Dirac.ModularKMS` green (2944 jobs); standard-3; budget 0. Next: lift to the continuum
  wedge `Δ_W^it` for the CAR net via `Spectral/SpectralTheorem.modFlow` (the StandardSubspace/crossed-
  product frontier).
- 2026-06-28 — **E5/E9: the modular phase = `e^{−it·βω}` (modular Hamiltonian eigenvalue = mode energy
  `βω`)** (added to `ModularKMS.lean`, axiom-free, budget 0). **`electron_modular_phase`** — the ratio of
  `Δ^{it}`'s occupied/empty eigenvalues is the Gibbs factor raised to `it`,
  `(n/(1−n))^{it} = e^{−it·βω}`. So the modular flow rotates the off-diagonal (raising/lowering)
  operators by the modular frequency `βω`; the generator of `σ_t` (the modular Hamiltonian `K`) has
  eigenvalue gap `βω`, and at the Unruh value `β = 2π` this is `2π·ω = 2π × (boost generator eigenvalue)`
  — the **`Δ^{it} = U(boost)` content at the single-mode level** (toward E9's `2π K_boost`). Proof: the
  Gibbs ratio + `cpow` of a positive real = `exp` + `Real.log_exp`. `lake build QIQTH.Fock.Dirac.ModularKMS`
  green (2944 jobs); standard-3; budget 0. The finite modular tier now includes the **modular energy =
  boost** identification. Next: the continuum wedge `Δ_W^it` for the CAR net (the StandardSubspace/
  crossed-product frontier).
- 2026-06-28 — **E5: the raising operator `a†` is a modular eigenoperator** (added to `ModularKMS.lean`,
  axiom-free, budget 0). **`electron_sigmaDiag_raising`** — `σ_t(a†) = (p₁^{it} p₀^{−it})·a†` (with
  `raisingOp = Matrix.single 1 0 1`, the matrix unit `E_{1,0}` = `a†`). The real-time modular flow
  `Δ^{it}` rotates `a†` by the modular phase `(n/(1−n))^{it} = e^{−it·βω}` (`electron_modular_phase`):
  **`a†` is an eigenvector of the modular automorphism with the modular frequency `βω`** (= the boost
  energy at `β = 2π`). This is the operator-level `Δ^{it} = U(boost)` action on the creation operator.
  Proof: the diagonal–matrix-unit–diagonal conjugation (`fin_cases` + `ring`). `lake build
  QIQTH.Fock.Dirac.ModularKMS` green (2944 jobs); standard-3; budget 0. The finite modular tier now has
  the operator-level eigenoperator action; next: the continuum lift to the CAR net via `modFlow`.
- 2026-06-28 — **E5: the lowering operator `a` is the dual modular eigenoperator (full spectral
  decomposition)** (added to `ModularKMS.lean`, axiom-free, budget 0). **`electron_sigmaDiag_lowering`**
  — `σ_t(a) = (p₀^{it} p₁^{−it})·a` (`loweringOp = Matrix.single 0 1 1 = E_{0,1}`), the modular flow
  rotates `a` by the **inverse** modular phase `((1−n)/n)^{it} = e^{+it·βω}`. With
  `electron_sigmaDiag_raising` (`a†` rotates by `e^{−it·βω}`) this is the **full modular spectral
  decomposition**: `a†` raises the modular energy by `βω`, `a` lowers it, and `N = a†a` is fixed
  (`electron_sigmaDiag_fixes_numberOp`) — the single-mode `Δ^{it} = U(boost)` Bohr-frequency rotation.
  `lake build QIQTH.Fock.Dirac.ModularKMS` green (2944 jobs); standard-3; budget 0. The finite/single-mode
  modular tier is now spectrally complete; the remaining E5 is the continuum CAR-net lift via `modFlow`.
- 2026-06-28 — **E5/E9: the number operator is the modular generator (canonical ladder commutators)**
  (added to `ModularKMS.lean`, axiom-free, budget 0). **`electron_number_raising_comm`** (`[N, a†] = a†`)
  and **`electron_number_lowering_comm`** (`[N, a] = −a`): the number operator raises/lowers `a†`/`a` by
  one quantum. Since the modular Hamiltonian is affine in `N` (`K = βω·N + c·I`), these give
  `[K, a†] = βω·a†` and `[K, a] = −βω·a` — the source of the modular phases `e^{∓it·βω}`
  (`electron_sigmaDiag_raising`/`_lowering`). So the **modular Hamiltonian ∝ the number operator (the
  record)**, with the modular energy `βω = 2π × the boost energy` at `β = 2π` — the E9 `2π K_boost`
  identification at the mode level. `lake build QIQTH.Fock.Dirac.ModularKMS` green (2944 jobs); standard-3;
  budget 0. The single-mode modular/boost dictionary is now complete (state · KMS · flow · spectrum ·
  generator). Remaining E5: the continuum CAR-net lift via `modFlow` (the operator-algebra frontier).
- 2026-06-28 — **E6/E9: single-mode thermal/entanglement entropy `S = log Z + β⟨E⟩`** (added to
  `ModularKMS.lean`, axiom-free, budget 0). **`electron_mode_entropy`** —
  `binaryEntropy(n) = log(1 + e^{−βω}) + βω·n`, with `n = fermiDirac β ω`, partition function
  `Z = 1 + e^{−βω}`, and mean energy `⟨E⟩ = ω·n` (so `βω·n = β⟨E⟩ = ⟨K⟩` up to the constant `log Z`). The
  **bridge `S ↔ ⟨K⟩`** — the input to the entanglement first law `δS = δ⟨K⟩` that drives the area law,
  realized for the electron mode. Proof: log-algebra on the FD occupation (`fermiDirac` def + KMS
  balance + `log_div`/`log_mul`/`log_exp`). `lake build QIQTH.Fock.Dirac.ModularKMS` green (3055 jobs);
  standard-3; budget 0. (Imported `QuasiFreeEntropy` for `binaryEntropy`.) The single-mode modular tier
  now connects the entropy to the modular energy — the area-law input. Remaining E5: the continuum
  CAR-net lift via `modFlow`.
- 2026-06-28 — **E9: the entanglement first law `δS = δ⟨K⟩` for the electron mode** (added to
  `ModularKMS.lean`, axiom-free, budget 0). **`hasDerivAt_binaryEntropy`** — `d/dn S(n) = log((1−n)/n)`
  (the modular-energy logit; via `Real.hasDerivAt_negMulLog` + chain rule). **`electron_firstLaw`** — at
  the KMS/Unruh occupation `n = fermiDirac β ω`, `HasDerivAt binaryEntropy (βω) n`: the entropy's
  derivative wrt occupation **IS the modular energy `βω`**. Since `⟨K⟩ = βω·N + c`, `d⟨K⟩/dn = βω = dS/dn`
  — the **differential entanglement first law `δS = δ⟨K⟩`** that drives the area law, realized for the
  electron mode. `lake build QIQTH.Fock.Dirac.ModularKMS` green (3055 jobs); standard-3; budget 0. The
  single-mode chain *FD occupation → KMS state → modular flow = boost → K ∝ N → S = log Z + β⟨E⟩ → δS =
  δ⟨K⟩* is now complete. Remaining E5: the continuum CAR-net lift via `modFlow`.
- 2026-06-28 — **E5 CONTINUUM: the CAR field-net modular flow `Γ₋(Δ^{it})`** (`QIQTH/Fock/Dirac/
  CARModularFlow.lean`, axiom-free, budget 0). The continuum wedge modular flow for the electron CAR net
  is the **fermionic second quantization** of the one-particle continuum `Δ^{it} = modUnitary S t`
  (`StandardSubspaceModularFlow`, already built): **`fermiSecondQuantModFlow S t = ExteriorAlgebra.map
  (modUnitary S t)`** on the antisymmetric (exterior/CAR) Fock `⋀ H` — the fermionic analog of the
  bosonic `secondQuantModFlow`, **reusing the same one-particle `Δ^{it}`** (the modular flow is
  statistics-independent at the one-particle level; only the second-quantization functor differs,
  symmetric ↦ antisymmetric). **`fermiSecondQuantModFlow_ι`** (`Γ₋(Δ^{it})(ι f)=ι(Δ^{it} f)`),
  **`_zero`** (`Γ₋(Δ^0)=id`), **`_add`** (the one-parameter group law `Γ₋(Δ^{is})∘Γ₋(Δ^{it})=Γ₋(Δ^{i(s+t)})`,
  from `modUnitary_add` + `ExteriorAlgebra.map` functoriality). **This is the continuum field-level
  `Δ_W^{it}` for the electron**, on QIQT-H's existing TT machinery. `lake build
  QIQTH.Fock.Dirac.CARModularFlow` green (3526 jobs); standard-3; budget 0. Remaining E5: the fermionic
  modular conjugation `J_W = Z·Γ₋(j)` (Klein twist ∘ second-quantized reflection) + the twisted duality.
- 2026-06-28 — **E5 continuum: the modular flow acts by algebra automorphisms** (added to
  `CARModularFlow.lean`, axiom-free, budget 0). **`fermiSecondQuantModFlow_one`** (`Γ₋(Δ^{it}) Ω = Ω`,
  vacuum invariance); **`fermiSecondQuantModFlow_comp_neg`** (`Γ₋(Δ^{it}) ∘ Γ₋(Δ^{−it}) = id`, so
  `Δ^{−it}` is the inverse); **`fermiModFlowEquiv`** — `Γ₋(Δ^{it})` bundled as an **`AlgEquiv`** (an
  algebra *isomorphism* of the CAR Fock with inverse `Γ₋(Δ^{−it})`). This is the defining Tomita–Takesaki
  property that the modular automorphism group `σ_t = Γ₋(Δ^{it})` lands in `Aut(𝓕)`, realized for the
  electron CAR net at the continuum level. `lake build QIQTH.Fock.Dirac.CARModularFlow` green (3526 jobs);
  standard-3; budget 0. The continuum modular flow is now a genuine one-parameter automorphism group.
  Remaining E5: the fermionic modular conjugation `J_W = Z·Γ₋(j)` (antilinear — the genuine remaining gap).
- 2026-06-28 — **E5/§0: the continuum modular flow preserves the even/record sector** (added to
  `CARModularFlow.lean`, axiom-free, budget 0). **`fermiSecondQuantModFlow_comp_parity`** —
  `Γ₋(Δ^{it}) ∘ Γ = Γ ∘ Γ₋(Δ^{it})`: the continuum modular flow **commutes with the fermion parity
  `Γ = (−1)^F`** (both graded algebra homs, agreeing on the `ι` generators). Hence the modular flow
  **preserves the ℤ₂ grading — the even (record/observable) sector is invariant under the modular
  dynamics**: the record/charge is conserved by the field-level modular flow (the §0/E8 "records attach
  to the even algebra" decision, now conserved by `σ_t` at the **continuum** level, matching the
  finite-level `electron_modAut_numberOp`/`electron_sigmaDiag_fixes_numberOp`). `lake build
  QIQTH.Fock.Dirac.CARModularFlow` green (3549 jobs); standard-3; budget 0. Remaining E5: the antilinear
  fermionic modular conjugation `J_W = Z·Γ₋(j)` (the genuine antilinear-functor / Mathlib gap).
- 2026-06-28 — **E5/§0: the modular flow keeps records as records** (added to `CARModularFlow.lean`,
  axiom-free, budget 0). **`fermiSecondQuantModFlow_isEven`** — `IsEven x → IsEven (Γ₋(Δ^{it}) x)`: the
  even (record/observable) sector is mapped into itself by the continuum modular dynamics (a consequence
  of the parity-commute). So the electron's records (even bilinears `j^μ`, `T_μν`, number) **remain
  records under the field-level modular flow `σ_t`** — modular dynamics conserves the even/observable
  algebra at the continuum. `lake build QIQTH.Fock.Dirac.CARModularFlow` green (3550 jobs); standard-3;
  budget 0. The continuum modular-flow ↔ records connection is now complete at the element level.
  Remaining E5: the antilinear fermionic modular conjugation `J_W = Z·Γ₋(j)` (the genuine
  antilinear-functor / Mathlib gap).
- 2026-06-28 — **E5: a record transforms covariantly under the modular/boost flow** (added to
  `CARModularFlow.lean`, axiom-free, budget 0). **`fermiSecondQuantModFlow_ι_mul_ι`** —
  `Γ₋(Δ^{it})(ι f · ι g) = ι(Δ^{it} f) · ι(Δ^{it} g)`: a fermion bilinear (a current / `T_μν`-type record)
  is carried by the modular flow to the bilinear of the **boosted** one-particle states — the records
  **transform covariantly** under `σ_t` (`Δ^{it} = U(boost)`). Immediate from `Γ₋(Δ^{it})` being an
  algebra hom. `lake build QIQTH.Fock.Dirac.CARModularFlow` green (3550 jobs); standard-3; budget 0. The
  continuum modular flow's action on records is now explicit (covariant transformation). **The electron's
  modular tier is comprehensively complete** (finite + continuum, flow + spectrum + generator + entropy +
  first law + record covariance/conservation), all on QIQT-H's existing TT machinery. Sole remaining E5:
  the antilinear modular conjugation `J_W = Z·Γ₋(j)` (antilinear-functor / Mathlib gap).
- 2026-06-28 — **E3/E9: CAR relative-entropy faithfulness `D(c‖c)=0`** (added to `QuasiFreeEntropy.lean`,
  axiom-free, budget 0). **`fermionicBinaryRelEntropy_self`** (`D(c‖c)=0`) and
  **`fermionicGaussianRelEntropy_self`** (`S(ρ‖ρ)=0`). With the positivity (`≥0`), this is the second
  defining property of the CAR/Araki relative entropy, and exactly what makes the first law `δS=δ⟨K⟩` the
  statement that `D(n‖n_KMS)` is *minimized* (=0) at the KMS occupation. `lake build
  QIQTH.Fock.Dirac.QuasiFreeEntropy` green (2179 jobs); standard-3; budget 0.
- 2026-06-28 — **E6 CAPSTONE: the electron Unruh effect at the Bisognano–Wichmann temperature `β=2π`**
  (added to `ModularKMS.lean`, axiom-free, budget 0, 3055 jobs green). At `β=2π` the finite modular flow
  `σ_t=Δ^{it}` is the geometric Rindler boost (BW), so the electron KMS state is the Rindler/Unruh thermal
  state. **`electron_unruh_occupation`**: `ω(N) = rindlerOccupationFermi ω = 1/(e^{2πω}+1)` — the FD/Unruh
  occupation as the modular-state expectation. **`electron_unruh_occupation_mem_Ioo`**: the Pauli bound
  `0<n_ω<1` (≤1 fermion/mode) — the sharp **contrast with the photon's UNBOUNDED bosonic** Unruh occupation
  `1/(e^{2πω}−1)` (which needs a number cutoff, `PHOTON_FIELD_PLAN` P2/P3), so the electron's per-mode
  capacity is intrinsically finite (CAR `dim ⋀h=2^n`, no cutoff). **`electron_unruh_entropy`**:
  `S(n_ω)=log(1+e^{−2πω})+2πω·n_ω` (the `log Z+β⟨E⟩` thermal entropy at the BW temperature).
  **`electron_unruh_firstLaw`**: `HasDerivAt binaryEntropy (2πω) n_ω` — the first law `δS=δ⟨K⟩` at the Unruh
  temperature, modular energy `2πω` (the `+2π` wiring one-particle BW into the area law). Ties the
  already-built modular flow to the boost-KMS Unruh law. Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-28 — **E9: the modular Hamiltonian `K=βω·N` and the boost Hamiltonian `2πK_boost`** (added to
  `ModularKMS.lean`, axiom-free, budget 0, 3055 jobs green). `σ_t=Δ^{it}=e^{−itK}` has `K` affine in the
  number operator (BW: the Rindler modular Hamiltonian is `2π×` the boost generator); the central `c·I`
  drops from all commutators. **`modHamiltonian β ω := (βω)•numberOp`**;
  **`electron_modHamiltonian_raising_comm`** (`[K,a†]=βω·a†` — scaling `[N,a†]=a†`; `a†` is a modular
  eigenoperator with eigenvalue `βω`, the generator source of `σ_t(a†)=e^{−itβω}a†`);
  **`electron_modHamiltonian_lowering_comm`** (`[K,a]=−βω·a`);
  **`electron_boost_modHamiltonian_raising_comm`** (at `β=2π`, `[K_W,a†]=2πω·a†` — the boost modular
  Hamiltonian `K_W=2πK_boost` whose `⟨K_W⟩` feeds the Clausius/Jacobson area relation `δS=δ⟨K_W⟩`). The
  E9 modular-energy object that connects the modular flow to the area law. Wired into `AxiomAudit.lean`;
  standard-3; budget 0. (HONEST: the Dirac Belinfante `T_μν` → `K_W` *geometric integral* and the full
  Jacobson assembly remain the cited E9 frontier; this lands the single-mode generator `K=βω·N` itself.)
- 2026-06-28 — **E9: the modular-energy expectation `⟨K⟩=βω·n`** (added to `ModularKMS.lean`, axiom-free,
  budget 0, 3055 jobs green). **`electron_modHamiltonian_expectation`**: the KMS/modular-state expectation
  of `K=βω·N` is `βω·n` (`stateOf` linearity + `electron_occupation_eq_fermiDirac`) — the `⟨K⟩=β⟨E⟩`
  modular-energy term in `S=log Z+β⟨E⟩` (`electron_mode_entropy`) and the `δ⟨K⟩` of the first law
  `δS=δ⟨K⟩` (`electron_firstLaw`). **`electron_boost_modEnergy`**: at `β=2π`, `⟨K_W⟩=2πω·n_ω` — the
  boost-energy expectation feeding the Clausius/Jacobson area relation `δS=δ⟨K_W⟩`. Closes the single-mode
  E9 loop: generator `K` (commutators) → expectation `⟨K⟩` → entropy/first law. Wired into
  `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E9: the modular Hamiltonian `K=βω·N` is self-adjoint** (added to `ModularKMS.lean`,
  axiom-free, budget 0, 3058 jobs green). **`electron_modHamiltonian_isHermitian`**: a real multiple of
  the real-diagonal number operator is Hermitian (`Matrix.IsHermitian.smul` of
  `isHermitian_diagonal_of_self_adjoint`), so `K` is a genuine self-adjoint generator and `Δ^{it}=e^{−itK}`
  is a **unitary** one-parameter group (the Stone/Tomita–Takesaki form). Closes the single-mode E9
  generator triad: `K` self-adjoint + ladder commutators (modular frequencies `∓βω`) + expectation
  `⟨K⟩=βω·n`. (Added `import Mathlib.LinearAlgebra.Matrix.Hermitian`.) Wired into `AxiomAudit.lean`;
  standard-3; budget 0.
- 2026-06-29 — **E1: the Dirac Lorentz/spin generator structure** (added to `DiracGamma.lean`, axiom-free,
  budget 0, 1774 jobs green). **`diracSigma_antisymm`**: `σ_ab = −σ_ba` — the defining antisymmetry of the
  spin generators `σ_μν` (6 independent = 3 rotations + 3 boosts). **`diracSigma_ortho`**: for orthogonal
  directions `σ_ab = 2γ_aγ_b`; in particular the boost generator `σ_{0i} = 2γ_0γ_i` (time⟂space) — the
  spinor representation of the Rindler boost whose flow is the electron's modular `Δ^{it}` (ties E1's
  Clifford/spin core to the E6/E9 boost-modular structure). Wired into `AxiomAudit.lean`; standard-3;
  budget 0. (HONEST: the Dirac one-particle space + the causal kernel `S_D=(iγ·∂+m)Δ_m` microcausality —
  inheriting from the proved scalar Pauli–Jordan spacelike vanishing `pauliJordan_spacelike_tendsto_zero`
  via "a local differential operator preserves spacelike support" — remain the analytic E1 frontier.)
- 2026-06-29 — **§0 (operator level): a single electron field operator is odd (NOT a record)** (added to
  `PhysLeanBridge.lean`, axiom-free, budget 0, 3130 jobs green). **`electron_single_fermionic`**:
  `ofCrAnList [φ]` lies in the FERMIONIC (odd) `statSubmodule` of PhysLean's Wick algebra — a single fermion
  is odd, so not an even observable / record. With `electron_bilinear_bosonic` (bilinears even) this
  completes the operator-level even/odd grading, **identical across all three layers**: the exterior CAR
  (`parity_one_particle` / `isEven_ι_mul_ι`), the Clifford (`diracGamma_mem_odd` / `diracGamma_mul_mem_even`),
  and PhysLean's `WickAlgebra` — the §0 "records = even bilinears, one-particle = odd" decision realized
  uniformly. Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E6/capacity: the Pauli per-mode entropy ceiling `S ≤ log 2`** (added to `ModularKMS.lean`,
  axiom-free, budget 0, 3061 jobs green). **`electron_mode_entropy_le_log2`**: the electron mode's thermal
  entropy `binaryEntropy(fermiDirac β ω) ≤ log 2` — a fermionic mode is a *qubit* (occupied or empty, Pauli
  exclusion), so its entropy is bounded by `log 2` (Gibbs/Jensen `shannon_le_log_card` on the 2-outcome
  occupation `{n, 1−n}`). The sharp **contrast with the photon**: the bosonic mode entropy is *unbounded*
  (no cutoff, `PHOTON_FIELD_PLAN` P2/P4), whereas the electron's per-mode entropy has the hard ceiling
  `log 2` — the entropy-level shadow of the CAR finite capacity `dim ⋀h = 2^n`. (Added
  `import QIQTH.RecordContract`.) Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E9: the modular-energy spectrum `K = diag(0, βω)`** (added to `ModularKMS.lean`,
  axiom-free, budget 0, 3061 jobs green). **`electron_modHamiltonian_diag`**: `K = βω·N = diag(0, βω)` —
  the modular energy levels are exactly `{0, βω}` (empty mode `0`, occupied mode `βω` = the boost energy
  quantum, `= 2πω` at the BW temperature), the gap driving the modular phase `σ_t(a†)=e^{−itβω}a†`.
  **`electron_modHamiltonian_trace`**: `Tr K = βω` (the sum of modular energy levels). Makes the modular
  Hamiltonian's spectrum explicit, completing the E9 generator picture (form `K=βω·N` + commutators +
  expectation `⟨K⟩` + self-adjoint + spectrum `{0,βω}`). Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E4: the Klein twist is a TWO-SIDED unitary `Z Z* = 1`** (added to `KleinTwistUnitary.lean`,
  axiom-free, budget 0, 2402 jobs green). **`kleinTwist_mul_star_self`**: the complement of the existing
  `Z* Z = 1`, proved *elegantly* via the order-4 relation — `Z⁴=1` (`kleinTwist_sq_sq`) makes `Z³` a
  two-sided inverse of `Z`, which with `Z* Z = 1` forces `Z* = Z³`, hence `Z Z* = Z⁴ = 1` (no re-expansion
  needed). So `Z` is a genuine **two-sided unitary** — the full intertwiner the twisted duality
  `𝓕(W)'=Z𝓕(W')Z*` requires. **The Klein-twist algebra is now complete: `Z²=Γ`, `Z⁴=1`, `Z*Z=ZZ*=1`.**
  Wired into `AxiomAudit.lean`; standard-3; budget 0. (The operator-algebra twisted-duality *theorem* +
  `γ` = the second-quantized parity unitary on the CAR space remain the E5 GNS frontier.)
- 2026-06-29 — **E4/E5: the Klein twist preserves the parity grading `[Z, Γ] = 0`** (added to
  `KleinTwist.lean`, axiom-free, budget 0, 2401 jobs green). **`kleinTwist_comm_gamma`**: `Z·γ = γ·Z` — the
  Klein twist commutes with the involution `γ` it is built from (since `Z = α·1 + β·γ` has *central*
  scalars; proved cleanly via `Commute.add_left`/`mul_left`). For `γ = Γ = (−1)^F` this is `[Z, Γ] = 0`:
  the twisted duality `𝓕(W)'=Z𝓕(W')Z*` does **not mix the even/odd sectors**, so the electron's even
  records stay even under the twist — exactly the §0 "records attach to the even algebra" requirement,
  now compatible with the twisted duality. Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E4 WITNESS: the Klein twist on the actual fermion parity `(−1)^N`** (`QIQTH/Fock/Dirac/
  KleinTwistWitness.lean`, axiom-free standard-3, budget 0, 2406 jobs green). **`fermionParity = (−1)^N =
  diag(1,−1)`** — a concrete `2×2` self-adjoint unitary involution on the single-fermion Fock space `ℂ²`
  (`fermionParity_involutive` `Γ²=1`, `fermionParity_selfAdjoint` `Γ*=Γ`). All four abstract Klein-twist
  relations are **witnessed non-vacuously** on it: **`electron_kleinTwist_sq`** (`Z²=Γ`),
  **`electron_kleinTwist_star_unitary`** (`Z*Z=1`), **`electron_kleinTwist_unitary`** (`ZZ*=1`),
  **`electron_kleinTwist_comm`** (`[Z,Γ]=0`) — the twisted-duality intertwiner realized on the *real*
  electron parity, not just postulated. Wired into `QIQTH.lean`+`AxiomAudit.lean`; standard-3; budget 0.
  (The field-level `(−1)^F` on the full CAR Fock + the operator-algebra duality *theorem* = E5 GNS frontier.)
- 2026-06-29 — **E5/§0: every diagonal record is a modular invariant** (added to `ModularKMS.lean`,
  axiom-free, budget 0, 3061 jobs green). **`electron_sigmaDiag_fixes_diagonal`**: the real-time modular
  flow `σ_t=Δ^{it}` fixes *every* diagonal matrix `diag(d)` — generalizing `electron_sigmaDiag_fixes_numberOp`
  (the `D=N` case) to the **whole classical/pointer (record) basis**. Since `Δ^{it}=diagPow` is diagonal
  and diagonals commute, `σ_t(D)=D·(Δ^{it}Δ^{−it})=D`. So the electron's records (the diagonal/decohered
  observables — number, occupation, charge) are **conserved by the modular dynamics** at the finite
  single-mode level — the finite-KMS counterpart of the continuum `fermiSecondQuantModFlow_isEven`. Wired
  into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E4/E5: parity = `(−1)^N`, tying the Klein-twist grading to the modular Hamiltonian**
  (added to `KleinTwistWitness.lean`, axiom-free, budget 0, 3098 jobs green).
  **`fermionParity_eq_one_sub_two_numberOp`**: `Γ = 1 − 2N` (`diag(1,−1) = 1 − 2·diag(0,1)`) — the parity
  operator (Klein-twist input) is exactly `(−1)^N` of the number operator (modular-Hamiltonian input
  `K=βω·N`), so `Γ` and `K` are both functions of `N`, simultaneously diagonal.
  **`electron_sigmaDiag_fixes_parity`**: `σ_t(Γ)=Γ` — the modular flow preserves the parity grading
  (`Γ` is diagonal, via `electron_sigmaDiag_fixes_diagonal`): a record of definite parity stays that parity
  under the modular dynamics (records conserved, concrete operator level). Wired into `AxiomAudit.lean`;
  standard-3; budget 0.
- 2026-06-29 — **E4/E6: the twisted-duality intertwiner `Z` commutes with the modular Hamiltonian** (added
  to `KleinTwistWitness.lean`, axiom-free, budget 0, 3098 jobs green). Since `Z` commutes with `Γ=1−2N`
  (`kleinTwist_comm_gamma`) and `N=(1−Γ)/2`, **`electron_kleinTwist_comm_numberOp`** gives `Z·N=N·Z`;
  scaling by `βω`, **`electron_kleinTwist_comm_modHamiltonian`** gives `Z·K=K·Z` (`K=βω·N`). So the Klein
  twist is a **modular invariant** — it commutes with the modular Hamiltonian (hence the modular flow `σ_t`),
  so the twisted duality `𝓕(W)'=Z𝓕(W')Z*` is **compatible with the modular dynamics** (the E4 twist
  consistent with the E6/E9 modular tier). Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E6: the modular state is the Gibbs state over the spectrum `{0, βω}`** (added to
  `ModularKMS.lean`, axiom-free, budget 0, 3061 jobs green). **`electron_gibbs_weight_ground`**:
  `(1−n)·Z = e^{−E₀} = 1` (`E₀=0`); **`electron_gibbs_weight_excited`**: `n·Z = e^{−E₁} = e^{−βω}` (`E₁=βω`),
  `Z = 1 + e^{−βω}`. So the electron's KMS/modular occupations are **exactly the Boltzmann weights
  `e^{−Eᵢ}/Z`** of the modular energy spectrum `{0, βω}` (`electron_modHamiltonian_diag`), with `Z = Σᵢ e^{−Eᵢ}`
  the modular partition function (whose `log Z` is the `S = log Z + β⟨E⟩` of `electron_mode_entropy`) — the
  "modular state = Gibbs state" statement at the entry level (the matrix-exp `ρ = e^{−K}/Z` form is the
  cited fiddly-but-tractable follow-on). Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E6: the fermionic depletion factor `1 − n = e^{βω}·n`** (`fermiDirac_one_sub`, in
  `FermiDirac.lean`, axiom-free, budget 0, 1925 jobs green). The `(1−n)` Pauli-blocking factor equals
  `e^{βω}` times the occupation — the multiplicative KMS+CAR balance, the **exact fermionic mirror of the
  photon's bosonic enhancement** `1 + n = e^{βω}·n` (`boseEinstein_one_add`). The `−n` (Pauli) vs `+n`
  (stimulated) is the spin–statistics signature carried to the occupation algebra, now stated symmetrically
  on both sides. Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **★ E6 CAPSTONE: the modular partition OPERATOR `e^{−K} = diag(1, e^{−βω})`, via the matrix
  exponential** (added to `ModularKMS.lean`, axiom-free standard-3, budget 0, 3113 jobs green — the deferred
  matrix-exp piece, now landed). **`electron_exp_neg_modHamiltonian`**: `NormedSpace.exp(−K) = diag(1, e^{−βω})`
  — the matrix exponential of `−K = −βω·N = diag(0,−βω)` is the diagonal of Boltzmann factors `e^{−Eᵢ}` over
  the modular spectrum `{0, βω}` (via `Matrix.exp_diagonal` + `Complex.exp_eq_exp_ℂ`).
  **`electron_partition_trace`**: `Z = Tr e^{−K} = 1 + e^{−βω}` — the modular partition function as a **trace**
  (the operator-level realization, whose `log Z` is the `S = log Z + β⟨E⟩` of `electron_mode_entropy`). With
  the Gibbs weights this completes the **"modular state = Gibbs state `e^{−K}/Z`"** picture at the operator
  level. (Added imports `Mathlib.Analysis.Normed.Algebra.MatrixExponential`, `…SpecialFunctions.Exponential`.)
  Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **★★ E6 FULL CAPSTONE: the modular state IS the Gibbs state `Z·ρ = e^{−K}`** (`ModularKMS.lean`,
  axiom-free standard-3, budget 0, 3113 jobs green). **`electron_thermalState_gibbs`**: `(1+e^{−βω})·ρ =
  e^{−K}` — the FD thermal state `ρ = diag(1−n, n)` IS the normalized Gibbs operator `e^{−K}/Z` of the
  modular Hamiltonian `K = βω·N`, combining the partition operator (`electron_exp_neg_modHamiltonian`) with
  the Gibbs weights via `Matrix.diagonal_smul` + cast `linear_combination`. The **defining Tomita–Takesaki
  property** — the modular/KMS state is the Gibbs state of the modular Hamiltonian — now a machine-checked
  matrix identity. This closes the electron modular thermodynamic dictionary at the operator level
  (`K`, `e^{−K}`, `Z=Tr e^{−K}`, `ρ=e^{−K}/Z`, Gibbs weights, `⟨K⟩`, `S=log Z+β⟨E⟩`, first law). Wired into
  `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E6: the explicit normalized Gibbs state `ρ = (1/Z)·e^{−K}`** (`electron_thermalState_eq_gibbs`,
  in `ModularKMS.lean`, axiom-free, budget 0, 3113 jobs green). The canonical normalized form of the Gibbs
  identity — the modular/KMS state written explicitly as `e^{−K}/Z` (`Z = 1 + e^{−βω}`), the standard
  "Gibbs state" statement (from `Z·ρ = e^{−K}` via `smul_smul` + `inv_mul_cancel₀`). Wired into
  `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E1: the spin generator squares to a scalar — boost vs rotation `σ_ab² = −4·Q(a)Q(b)`**
  (added to `DiracGamma.lean`, axiom-free, budget 0, 1775 jobs green). **`diracSigma_sq_ortho`**: for
  orthogonal `a⟂b`, `σ_ab² = −4·Q(a)·Q(b)` (a *scalar*, since `σ_ab=2γ_aγ_b` and
  `(γ_aγ_b)²=−γ_a²γ_b²=−Q(a)Q(b)`). This **distinguishes boosts from rotations**: with `η=(+,−,−,−)`, the
  **boost** `σ_{0i}` has `Q(e₀)Q(eᵢ)=(+1)(−1)=−1 ⟹ σ²=+4>0` (non-compact, *hyperbolic* — the Rindler boost
  generator whose `Δ^{it}` is the modular flow); a **rotation** `σ_{ij}` has `(−1)(−1)=+1 ⟹ σ²=−4<0`
  (compact, *elliptic*). The sign of `σ²` is the boost-vs-rotation (non-compact-vs-compact) dichotomy of the
  Lorentz spin generators. (Added `import Mathlib.Tactic.NoncommRing`.) Wired into `AxiomAudit.lean`;
  standard-3; budget 0.
- 2026-06-29 — **E1: the fundamental orthogonal-gamma square `(γ_aγ_b)² = −Q(a)Q(b)`** (extracted/exported in
  `DiracGamma.lean`, axiom-free, budget 0, 1775 jobs green). **`diracGamma_mul_sq_ortho`**: the building
  block of `diracSigma_sq_ortho` (`σ²=4×` this), now a standalone lemma. So `γ_aγ_b` is a *square root* of
  `−Q(a)Q(b)`: for a **rotation plane** (`Q(a)Q(b)>0`) it is a **complex structure** (`(γ_aγ_b)²<0`, the `i`
  generating the `U(1)` rotation); for a **boost plane** (`Q(a)Q(b)<0`, time⟂space) it squares to a positive
  scalar (hyperbolic). `diracSigma_sq_ortho` refactored to use it. Wired into `AxiomAudit.lean`; standard-3;
  budget 0.
- 2026-06-29 — **E1: `γ` transforms as a vector under the spin generator `[σ_ab, γ_a] = −4·Q(a)·γ_b`**
  (added to `DiracGamma.lean`, axiom-free, budget 0, 1775 jobs green). **`diracSigma_comm_gamma_left`**:
  `σ_ab γ_a − γ_a σ_ab = −4·Q(a)·γ_b` (`a⟂b`) — the commutator of the Lorentz spin generator with a gamma in
  its plane rotates it into the other. The **defining property of the spinor representation**: the gamma
  matrices `γ_μ` transform as a **4-vector** under the Lorentz generators `σ_μν` (the source of
  `[σ_μν,γ_ρ]=2(η_νργ_μ−η_μργ_ν)` covariance), the spinor realization of the Lorentz boost/rotation acting
  on the vector index. Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E1: the spin generator acts only in its plane `[σ_ab, γ_c] = 0` (`c⟂a,b`)** (added to
  `DiracGamma.lean`, axiom-free, budget 0, 1775 jobs green). **`diracSigma_comm_gamma_ortho`**: a gamma
  orthogonal to both `a` and `b` commutes with `σ_ab` (`σ_ab γ_c = γ_c σ_ab`), so the Lorentz
  rotation/boost generated by `σ_ab` acts **only within the `{a,b}` plane** and leaves the orthogonal
  complement invariant (the planar nature of a Lorentz transformation). With `diracSigma_comm_gamma_left`
  (rotates the plane) this fully characterizes the spinor action of `σ_ab` on the gamma 4-vector. Wired
  into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **E1: boost vs rotation, concrete `(γ_aγ_b)² = ∓1`** (added to `DiracGamma.lean`, axiom-free,
  budget 0, 1775 jobs green). **`diracGamma_mul_sq_rotation`**: for a *rotation plane* (`Q(a)·Q(b)=1`),
  `(γ_aγ_b)²=−1` — `γ_aγ_b` is a **complex structure** (square root of `−1`, generating the elliptic `U(1)`
  rotation `e^{θγ_aγ_b}=cos θ+sin θ·γ_aγ_b`). **`diracGamma_mul_sq_boost`**: for a *boost plane*
  (`Q(a)·Q(b)=−1`, time⟂space), `(γ_aγ_b)²=+1` — a **hyperbolic** generator (`e^{η γ_aγ_b}=cosh η+sinh
  η·γ_aγ_b`, the unbounded boost whose `Δ^{it}` is the modular flow). The concrete elliptic-vs-hyperbolic
  realization of the boost/rotation dichotomy. Wired into `AxiomAudit.lean`; standard-3; budget 0.
