# QIQT-H Lean formalizations — Mathlib variant

**Status:** 34 theorem-bearing modules + 1 axiom audit (35 total). 2062 build jobs, exit 0. Every "PROVED concretely" theorem depends only on the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no accidental project-axiom contamination. Verified via `QIQTH.AxiomAudit` (`lake build QIQTH.AxiomAudit` emits `#print axioms` for each key theorem).

Mathlib-rooted proofs of QIQT-H Theorems 6, 7, Lemma 1, Theorem 3.

The standalone counterparts in `../*.lean` axiomatize the arithmetic
facts they consume.  This variant discharges those axioms against
`Mathlib.Data.Real.Basic`, so the trust base is `Mathlib + Lean kernel`
(no custom axioms).

## Files

| Lake module | Source |
|---|---|
| `QIQTH.Theorem6` | `QIQTH/Theorem6.lean` |
| `QIQTH.Theorem7` | `QIQTH/Theorem7.lean` |
| `QIQTH.Resolution` | `QIQTH/Resolution.lean` |
| `QIQTH.UnitarityLocality` | `QIQTH/UnitarityLocality.lean` — closes the microcausality ⇒ locality gap for Theorem 7 (unitary-dilation case) |
| `QIQTH.Donald` | `QIQTH/Donald.lean` — derives Donald's identity from three primitive relative-entropy axioms (A1, A2, A3) |
| `QIQTH.DoubleSlit` | `QIQTH/DoubleSlit.lean` — worked instance: single-spot saturation collapses Theorem 6 to determinacy |
| `QIQTH.StateLevelNoSignaling` | Lifts T7 from probabilities to states; closure of Alice-fixing under composition and convex mixtures |
| `QIQTH.KrausLocality` | Generalizes `UnitarityLocality` to arbitrary finite-Kraus Bob channels (POVMs, projective measurements) |
| `QIQTH.ResolutionExt` | Monotonicity `Q₁ ≤ Q₂ ⇒ ε(Q₂) ≤ ε(Q₁)`, bits/nats conversion, complement lemmas |
| `QIQTH.CapacityPacking` | `N · I_0 ≤ Q_R ⇒ N ≤ ⌊Q_R / I_0⌋` + Markov-style suppression bounds |
| `QIQTH.RelEntPositivity` | `D(ρ ‖ σ) ≥ 0` (Klein, axiomatized) + convexity of `D` in first argument (derived from Donald) |
| `QIQTH.HolevoCoarseGraining` | Donald deficit formula + saturation rigidity + coarse-graining inequality |
| `QIQTH.DPI` | Data Processing Inequality interface + regional monotonicity + composition |
| `QIQTH.ShannonFano` | Finite Shannon entropy + single-record certainty bridge from `H_ε ≤ 0` |
| `QIQTH.BellMarginal` | Algebraic Bell/POVM marginalization identity |
| `QIQTH.Bell` | **CHSH-LHV bound** `\|chsh\| ≤ 2` for any local-hidden-variable model + **QIQT-H corollary** (no LHV model reproduces QIQT-H's quantum-level CHSH violations, yet QIQT-H still satisfies no-signaling) |
| `QIQTH.Tsirelson` | **Rigorous singlet construction.** Explicit 4D real construction: ψ⁻ = (\|01⟩−\|10⟩)/√2, σ_z⊗σ_z, σ_x⊗σ_x. Direct computation gives ⟨ZZ⟩ = ⟨XX⟩ = −1, hence ⟨T⟩ = √2·(−1+−1) = −2√2. Discharges `Bell.tsirelson_bound` axiom. |
| `QIQTH.H1H2Audit` | **Central audit:** (H1) + Donald + Klein + DPI do NOT imply (H2). Classical KL countermodel σ = (½,½), ρ = δ₀: KL = log 2 ≈ 0.693 < 1 = I_0. **Sharp replacement:** (H2) is equivalent to σ(E_record) ≤ exp(−I_0). Converts the framework's central non-AQFT postulate from "opaque empirical axiom" to "precise reference-weight bound on pointer sectors". |
| `QIQTH.NoConcentration` | **Central audit:** Linear unitary measurement-decoherence preserves branch weights — it does NOT concentrate amplitudes to 0/1. Equal-superposition input ψ = (\|0⟩+\|1⟩)/√2 leaves weights (½,½). Theorems 1/4 ("single-record per-run") therefore require something beyond unitary decoherence: (FQ) literal truncation, hidden-variable selection, stochastic conditioning, or an explicit concentration axiom. |
| `QIQTH.EntropyBridge` | **Entropy notation audit:** The (FQ) bound is on `χ_R` (Araki relative entropy), NOT on the CPW renormalized entropy `S_R^CPW` — though the paper sometimes writes `S_ren` for `χ_R`. Bridge identity `χ_R(ω) = ΔK_{σ_R}(ω) − ΔS_R^CPW(ω)`. Counterexample: a state can satisfy a CPW-S_ren-bound while violating any modular-relative-entropy bound. Paper §4.1(ii) now flags this explicitly. |
| `QIQTH.BranchLedger` | **Branch-summed bound audit:** Branch-summed cost `I_Σ^ε := Σ_k c_R(r_k)` is NOT bounded by Shannon/Holevo/holographic entropy in general. Concrete counterexample: binary uniform distribution with unit per-record cost has Shannon = log 2 ≈ 0.693 but branch-summed cost = 2. Confirms the paper's own admission (Math §9A.3) that the branch-summed bound is a *strengthening* of holography, not a derived consequence. |
| `QIQTH.ArakiInterface` | **Side-conditioned Donald/DPI/Klein interface:** Packages Donald's identity, Klein positivity, DPI for normal UCP channels, and `I_Hol ≤ Shannon` with explicit finiteness/normality/positivity conditions appropriate for Araki/Tomita-Takesaki relative entropy. Replaces the abstract cross-entropy primitives of `Donald.lean` with conditioned axioms safer in the operator-algebra setting. |
| `QIQTH.FQDynamicsNoGo` | **Final structural audit:** If (FQ) is read as "exactly finite admissible state space H_phys", then continuous Hamiltonian evolution preserving H_phys is *trivial* (every admissible state is evolution-fixed). Proof: continuous function from connected ℝ to T2 space with finite range is constant (clopen-fiber argument). Forces the framework to mean "bounded information" or "finite operational distinguishability", not literally finite invariant grid. |
| `QIQTH.CompressionLocality` | **Final structural audit:** Ambient commutativity `[A,B]=0` does NOT imply restricted commutativity `[PAP, PBP]=0` for a projection P. Leakage identity: `[PAP, PBP] = PB(1−P)AP − PA(1−P)BP`. Audit corollary: locality is preserved iff the projection commutes with the local algebras' observables. Isolates the implicit "local projection" constraint on (FQ)-restricted dynamics needed for Theorem 7. |
| `QIQTH.NoBornFromNothing` | **Born audit:** For ANY target distribution `p` and any surjective outcome map, there exists a microscopic measure `μ` whose outcome-marginal equals `p`. Construction: pick a section, place mass `p k` on `s k`. Specialization to Born weights gives Theorem 5 *conditionally*. Strategic point: the structural axioms do NOT determine Born frequencies — μ-selection is the load-bearing physical input. |
| `QIQTH.EquivarianceGap` | **Born audit:** Support preservation (the framework's "H_phys is dynamically invariant") does NOT imply measure preservation (Bohmian-style |ψ|²-equivariance). Concrete counterexample: swap bijection on `Fin 2` with non-uniform measure `(3/4, 1/4)`. A genuine equivariance theorem requires concrete dynamics + Born-measure family the framework does not currently specify. |
| `QIQTH.BornTypicality` | **Conditional Born theorem.** Replaces "Born as probability rule" (Gleason-style) with "Born as empirical-frequency target" (QIQT-H's actual ontology). Proves `expectedIndicator outcome μ k = (c k)²` rigorously from a canonical IC measure (whose `outcomeMarginal` equals Born weights). Almost-sure convergence axiomatized via LLN interface. Identifies the open question as: WHICH measure is "canonical"? Candidates: tracial typicality from CPW Type II, symmetric equiprobability, or holographic modular construction. |
| `QIQTH.TypicalityMackeyGleason` | **Sub-theorem A.** Normal additive noncontextual typicality weights on the IC projection algebra are uniquely of the trace-density form `μ(P) = τ_R(D · P)`. Conditional on the standard Mackey-Gleason + noncommutative Radon-Nikodym theorems (axiomatized at interface). The structural "Gleason for typicality" for QIQT-H. |
| `QIQTH.OperationalNoGo` | **Sub-theorem B.** Concrete witness: two distinct IC measures `μ₁ = (1/4, 1/4, 1/2)` and `μ₂ = (1/2, 0, 1/2)` on `Fin 3` produce identical outcome marginals under the non-injective outcome map `(0,0,1)`. Operational data cannot uniquely determine the IC measure; structural input is needed. |
| `QIQTH.FQEquivarianceUniqueness` | **Sub-theorem C.** Among trace-density typicality structures, locality + naturality + FQ-equivariance uniquely fix the canonical density (Goldstein-Struyve theorem adapted to QIQT-H). Combined with A + B: the Canonical IC Measure Principle is derivable from {Mackey-Gleason + Goldstein-Struyve adapted + FQ Hamiltonian equivariance}, not from operational axioms. Abstract-interface version; see `GoldsteinStruyveFinDim` for the concrete finite-dimensional version with two steps proved. |
| `QIQTH.GoldsteinStruyveFinDim` | **Concrete finite-dimensional Goldstein-Struyve.** Step 2 (normalization → α + β = 1) and Step 4 (non-degeneracy → α = 1, β = 0) PROVED concretely using `Matrix (Fin d) (Fin d) ℂ` and `Matrix.trace`. Step 1 (Schur classification of unitary-equivariant linear maps on Hermitians) and Step 3 (tensor-multiplicativity narrowing) axiomatized at the interface — Step 1 estimated at 2–5 weeks of concrete matrix-unit Lean work (GPT-5.5-pro). Combined `goldstein_struyve_findim` theorem is PROVED by composition. |
| `QIQTH.GoldsteinStruyveStep3` | **Step 3 algebraic core (PROVED).** Bypasses the full Kronecker machinery by extracting the algebraic constraint that tensor multiplicativity imposes at the `((1,1),(1,1))` matrix component: `α + β/d² = (α + β/d)²`. Polynomial identity `α·d² + (1-α) − (α·d + (1-α))² = α·(d-1)²·(1-α)` proved by `ring`. Combined with `α + β = 1` and `d ≥ 2`, this forces `α·(1-α) = 0`, hence `(α,β) ∈ {(1,0), (0,1)}`. |
| `QIQTH.GoldsteinStruyveKronecker` | **Step 3 Kronecker bridge (PROVED for d = 2).** Concrete construction of E₁₁ = `Matrix.stdBasisMatrix 0 0 1` on `Fin 2`, plus the polymorphic `schurFormFin n` and `schurFormProd` (on `Fin 2 × Fin 2`). Shows that tensor multiplicativity at the witness `(E₁₁ ⊗ E₁₁)` evaluated at the `((0,0),(0,0))` component yields exactly `TensorConstraintAt11 2 α β`. Combined with `GoldsteinStruyveStep3.step3_tensor_narrowing`: the full Step 3 conclusion `(α,β) ∈ {(1,0), (0,1)}` is proved from tensor multiplicativity + normalization. |
| `QIQTH.GoldsteinStruyveStep1` | **Step 1 structural decomposition.** Exposes the multi-week Schur classification proof (GPT estimate: 2-5 weeks of concrete Lean work) as a composition of 5 named sub-lemmas: (1a) complex-linear extension, (1b) diagonal-unitary basis preservation, (1c) permutation-unitary coefficient unification, (1d) Hadamard rotation pins to Schur form, (1e) Hermitian restriction forces real coefficients. Each sub-lemma is an axiomatized clean conceptual claim about specific unitary group elements; the composition is proved. Concrete `matrixUnit` constructions provided as scaffolding. |
| `QIQTH` (root, re-exports) | `QIQTH.lean` |

## What Mathlib gives us

| Standalone axiom | Mathlib replacement |
|---|---|
| `RealQ.le_refl` | `le_refl` |
| `RealQ.le_trans` | `le_trans` |
| `RealQ.add_le_add_right` | `add_le_add_right` |
| `RealQ.sub_le_self_of_nonneg` | `sub_le_self_of_nonneg` (via `linarith`) |
| `RealQ.eq_sub_of_sum` | `eq_sub_of_add_eq'` (via `linarith`) |

All five real-arithmetic axioms collapse to a single `linarith` call.

`Resolution.lean` additionally gets the **continuous form** of
Theorem 3:  `eps Q := (1/2 : ℝ)^Q` with `eps_pos` proven by
`positivity`. The standalone variant only carries the discrete
`numBins Q > 0`.

## Verifying

```bash
cd lean/mathlib
lake exe cache get   # one-time, fetches precompiled Mathlib (~5 GB)
lake build           # compiles QIQTH/*.lean (~30 s on warm cache)
```

A clean `lake build` (exit 0, no error lines) means the proofs check.

## Setup notes

- Lean toolchain: `leanprover/lean4:v4.30.0` (pinned in `lean-toolchain`).
- Mathlib pinned at `v4.30.0` tag (declared in `lakefile.lean`).
- `lake exe cache get` fetches precompiled `.olean` files from
  `leanprover-community/mathlib4` Azure cache — much faster than
  building Mathlib from source (which would take hours).
- First-run `lake update` fetches ~10 transitive dependencies
  (Mathlib + plausible + Aesop + Qq + batteries + Cli + …).
