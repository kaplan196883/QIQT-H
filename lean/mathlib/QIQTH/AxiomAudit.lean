/-
  Axiom dependency audit — `#print axioms` over every "PROVED
  concretely" theorem in the project.

  GPT-5.5-pro's closing recommendation: verify that theorems advertised
  as proved concretely have no accidental dependency on project-specific
  interface axioms (Mackey-Gleason, Goldstein-Struyve Step 1/3 axioms,
  LLN_typicality_axiom, sorryAx, etc.).

  Build this module with `lake build QIQTH.AxiomAudit`; the
  `#print axioms` directives emit the dependency lists to the build
  log.  Each expected entry is annotated with what should appear:

    "no project axioms"  ⇒ should show only `Classical.choice`,
                            `propext`, `Quot.sound` (standard Lean/
                            Mathlib axioms).

    "project axioms: X"  ⇒ should additionally show X (acceptable
                            interface axioms documented in the
                            module).
-/

import QIQTH

namespace QIQTH.AxiomAudit

-- ── Core deductive (all should have NO project axioms) ─────────────

#print axioms QIQTH.Theorem6.BranchData.holevo_le_capacity
-- expected: standard Lean/Mathlib axioms only
#print axioms QIQTH.Theorem6.effective_definiteness
-- expected: standard Lean/Mathlib axioms only

#print axioms QIQTH.Theorem7.Setup.no_signaling
-- expected: standard only

#print axioms QIQTH.Resolution.eps_pos
-- expected: standard only (positivity of (1/2)^Q)

#print axioms QIQTH.UnitarityLocality.locality_of_conjugation
-- expected: standard only (StarRing arithmetic)

-- ── Bell + Tsirelson (Tsirelson should fully discharge) ────────────

#print axioms QIQTH.Tsirelson.tsirelson_rigorous
-- expected: standard only — concrete singlet construction

#print axioms QIQTH.Tsirelson.singlet_chsh_abs_gt_two
-- expected: standard only

#print axioms QIQTH.Bell.LHVModel.chsh_le_two
-- expected: standard only (finite probability + ±1 algebra)

-- ── H1/H2 audit (PROVED concretely) ───────────────────────────────

#print axioms QIQTH.H1H2Audit.H1_does_not_imply_H2
-- expected: standard only

#print axioms QIQTH.H1H2Audit.H2_iff_reference_weight
-- expected: standard only

-- ── NoConcentration audit (PROVED concretely) ─────────────────────

#print axioms QIQTH.NoConcentration.decoherence_does_not_concentrate
-- expected: standard only

#print axioms QIQTH.NoConcentration.audit_conclusion
-- expected: standard only

-- ── Born audits ───────────────────────────────────────────────────

#print axioms QIQTH.NoBornFromNothing.exists_probability_realizing
-- expected: standard only — concrete section-based construction

#print axioms QIQTH.NoBornFromNothing.any_anti_born_realizable
-- expected: standard only

#print axioms QIQTH.EquivarianceGap.support_preservation_does_not_imply_measure_preservation
-- expected: standard only — concrete Fin 2 counterexample

#print axioms QIQTH.BornTypicality.born_mean_conditional
-- expected: standard only (the LLN axiom is used only in the
-- almost-sure form, not in the mean form)

-- ── Operational no-go (PROVED concretely) ─────────────────────────

#print axioms QIQTH.OperationalNoGo.operational_data_insufficient
-- expected: standard only — concrete Fin 3 witness

-- ── Final structural audits ───────────────────────────────────────

#print axioms QIQTH.FQDynamicsNoGo.finite_admissible_flow_fixed
-- expected: standard only — topology of preconnected→T2 with finite range

#print axioms QIQTH.CompressionLocality.compressed_commutator_with_commute
-- expected: standard only — noncommutative ring manipulation

-- ── Goldstein-Struyve finite-dim ──────────────────────────────────

#print axioms QIQTH.GoldsteinStruyveFinDim.step2_normalization
-- expected: standard only — concrete Matrix.trace computation

#print axioms QIQTH.GoldsteinStruyveStep1.schur_classification_real
-- expected: standard only — step1 Schur classification, FULLY PROVED (axiom retired 2026-06)

#print axioms QIQTH.GoldsteinStruyveFinDim.step3_tensor_multiplicativity
-- expected: standard only — traceless-Z (diag 1,−1) Kronecker entry computation
-- (formerly an axiom; PROVED 2026-06, retiring it: budget 37→36)

#print axioms QIQTH.GoldsteinStruyveFinDim.step4_nondegeneracy
-- expected: standard only

#print axioms QIQTH.GoldsteinStruyveStep3.step3_algebraic_core
-- expected: standard only — polynomial identity + real arithmetic

#print axioms QIQTH.GoldsteinStruyveStep3.step3_tensor_narrowing
-- expected: standard only

#print axioms QIQTH.GoldsteinStruyveKronecker.step3_kronecker_bridge
-- expected: standard only — concrete matrix-entry computation

#print axioms QIQTH.GoldsteinStruyveKronecker.step3_tensor_narrowing_via_kronecker
-- expected: standard only

-- ── Combined theorems (KNOWN to use interface axioms) ─────────────
-- These SHOULD show their interface dependencies; that is expected.

#print axioms QIQTH.GoldsteinStruyveFinDim.goldstein_struyve_findim
-- expected: standard only — step1 now takes the Schur form as a supplied hypothesis
-- (no axiom); step3 is also proved.  (Callers discharge step1 via schur_classification_real.)

#print axioms QIQTH.GoldsteinStruyveFinDim.step3_tensor_narrowing
-- expected: standard only — honest tensor narrowing (independent composite coefficient α')

-- ── Regression suite (non-vacuity + countermodels) ────────────────
#print axioms QIQTH.GoldsteinStruyveModels.canonical_principle_nonvacuous
-- expected: standard only — identity witnesses ALL hypotheses of the flagship (non-vacuous)
#print axioms QIQTH.GoldsteinStruyveModels.imaginaryId_not_hermitianPreserving
-- expected: standard only — i·id rejected by IsHermitianPreserving
#print axioms QIQTH.GoldsteinStruyveModels.depolarizing_not_nonDegenerate
-- expected: standard only — trace-depolarizing rejected by IsNonDegenerate
#print axioms QIQTH.GoldsteinStruyveModels.conjTranspose_not_isLinear
-- expected: standard only — conjugate-transpose rejected by IsLinear (certifies ℂ-linearity)

-- ── Finite Born-typicality (genuine, non-vacuous; replaces LLN placeholder) ──
#print axioms QIQTH.BornTypicalityFinite.sum_w_eq_one
-- expected: standard only — the canonical product weight is a probability distribution
#print axioms QIQTH.BornTypicalityFinite.expectation_count
-- expected: standard only — E[#{t: ω t = k}] = N·p k  (frequencies unbiased for Born weights)
#print axioms QIQTH.BornTypicalityFinite.markov_le
-- expected: standard only — finite Markov inequality for the product measure
#print axioms QIQTH.BornTypicalityFinite.chebyshev_count
-- expected: standard only — Chebyshev concentration: P((count−Np)² ≥ (Nε)²) ≤ E[(count−Np)²]/(Nε)²
#print axioms QIQTH.BornTypicalityFinite.marginal2
-- expected: standard only — two-coordinate marginal (covariance structure; p k if s=s', p k² else)
#print axioms QIQTH.BornTypicalityFinite.variance_count
-- expected: standard only — Var = N·p k·(1−p k) (binomial variance)
#print axioms QIQTH.BornTypicalityFinite.chebyshev_freq
-- expected: standard only — CLEAN typicality bound: P(|freq−p k| ≥ ε) ≤ p k(1−p k)/(Nε²)
#print axioms QIQTH.BornTypicalityQuantum.trace_kronN_mul
-- expected: standard only — product trace factorization tr((⊗ρ)(⊗E)) = ∏ tr(ρ E) (no independence smuggled)
#print axioms QIQTH.BornTypicalityQuantum.quantumWeight_eq_w
-- expected: standard only — quantum N-copy product weight = classical product weight of Born vector
#print axioms QIQTH.BornTypicalityQuantum.quantum_chebyshev_freq
-- expected: standard only — END-TO-END quantum Born-typicality: bad-frequency event weight ≤ p(1−p)/(nε²)
#print axioms QIQTH.BornTypicalityQuantum.trace_eventEffect_eq_sum
-- expected: standard only — tr(ρ^⊗ⁿ · F_S) = ∑ quantumWeight (POVM effects ADD; no amplitude interference)
#print axioms QIQTH.BornTypicalityQuantum.quantum_chebyshev_freq_event
-- expected: standard only — event-effect form: tr(ρ^⊗ⁿ · F_bad).re ≤ p(1−p)/(nε²)
#print axioms QIQTH.BornTypicalityQuantum.bornProb_sum
-- expected: standard only — ∑ₖ bornProb = 1 from POVM completeness + unit trace
#print axioms QIQTH.BornTypicalityQuantum.trace_vecMulVec_mul_eq
-- expected: standard only — rank-one trace as quadratic form tr(vv*·E) = v*·(E v)
#print axioms QIQTH.BornTypicalityQuantum.trace_mul_nonneg
-- expected: standard only — 0 ≤ tr(ρ·E) for PSD ρ, E (via vecMulVec decomposition)
#print axioms QIQTH.BornTypicalityQuantum.bornProb_nonneg
-- expected: standard only — 0 ≤ bornProb for PSD ρ + PSD effects
#print axioms QIQTH.BornTypicalityQuantum.quantum_chebyshev_freq_density
-- expected: standard only — density/POVM wrapper (Hermiticity + nonneg + ∑=1 ALL derived; no residual)
#print axioms QIQTH.BornTypicalityFinite.chebyshev_freq_union
-- expected: standard only — union bound over outcomes (∑ₖ p(1−p)/(Nε²))
#print axioms QIQTH.BornTypicalityFinite.chebyshev_freq_union_le
-- expected: standard only — global joint-typicality bound ≤ 1/(Nε²)
#print axioms QIQTH.BornTypicalityFinite.w_history_factorizes
-- expected: standard only — product preparation ⇒ trial independence (the principle behind indep)
#print axioms QIQTH.BornTypicalityQuantum.quantum_chebyshev_freq_union
-- expected: standard only — quantum lift of the outcome union bound
#print axioms QIQTH.BornTypicalityQuantum.quantum_chebyshev_freq_union_le
-- expected: standard only — quantum global joint typicality ≤ 1/(nε²)
#print axioms QIQTH.BornTypicalityQuantum.quantum_chebyshev_freq_union_density
-- expected: standard only — density/POVM global joint typicality (all hyps derived)

#print axioms QIQTH.BornMeasureUniqueness.eventEffect_univ
-- expected: standard only — product-history effects are a POVM (∑_ω F_ω = 1)
#print axioms QIQTH.BornMeasureUniqueness.measure_unique_of_additive
-- expected: standard only — additive measures agreeing on singletons are equal
#print axioms QIQTH.BornMeasureUniqueness.bornMeasure_eq_trace
-- expected: standard only — λ(S) = tr(ρ^⊗ⁿ · F_S).re
#print axioms QIQTH.BornMeasureUniqueness.product_born_measure_unique
-- expected: standard only — λ-IDENTIFICATION: product Born measure forced = trace functional
#print axioms QIQTH.BornMeasureUniqueness.bornMeasure_satisfies_hyps
-- expected: standard only — non-vacuity witness for the λ-identification
#print axioms QIQTH.BornTypicalityQuantum.kronN_conjTranspose
-- expected: standard only — (⊗ₜ A)ᴴ = ⊗ₜ Aᴴ
#print axioms QIQTH.BornTypicalityQuantum.kronN_isHermitian
-- expected: standard only — tensor of Hermitian is Hermitian
#print axioms QIQTH.BornMeasureUniqueness.bornMeasure_nonneg
-- expected: standard only — 0 ≤ λ(S) (measure positivity from bornProb_nonneg)
#print axioms QIQTH.BornMeasureUniqueness.eventEffect_isHermitian
-- expected: standard only — product-history event effects are self-adjoint
#print axioms QIQTH.BornMeasureUniqueness.hpt_of_cylinder_independence
-- expected: standard only — product marginals DERIVED from explicit cylinder independence
#print axioms QIQTH.BornMeasureUniqueness.product_born_measure_unique_of_independent_trials
-- expected: standard only — λ-identification with independence made an explicit named input

#print axioms QIQTH.FQEquivarianceUniqueness.canonical_ic_measure_principle
-- expected: standard + 4 acknowledged sub-axioms

#print axioms QIQTH.GoldsteinStruyveStep1.step1_via_sub_lemmas
-- expected: standard + 5 sub-axioms + the abstract Step 1 axiom

-- ── A1/A2/A4/A6 strengthening pass (PROVED concretely) ──────────────
-- All of these should depend only on standard Lean/Mathlib axioms.

-- A1: marginal locality from equivariance + local dynamics
#print axioms QIQTH.MarginalLocality.pushforward_marginal_local
-- expected: standard only — pure pushforward, NO equivariance assumption
#print axioms QIQTH.MarginalLocality.marginal_invariant_of_local_dynamics
-- expected: standard only
#print axioms QIQTH.MarginalLocality.alice_marginal_unchanged_by_bob_dynamics
-- expected: standard only

-- General bipartite no-signaling for an ARBITRARY (entangled) state (P0 of the GPT-5.5-pro plan)
#print axioms QIQTH.NoSignalingGeneral.bipartite_no_signaling
-- expected: standard only — ∑_b tr(ρ(E⊗F_b)) = tr(ρ(E⊗1)); no separability assumption on ρ.
#print axioms QIQTH.NoSignalingGeneral.local_marginal_indep_remote
-- expected: standard only — local marginal independent of remote POVM choice (genuine no-signaling).

-- P1: coarse-graining naturality — Born measures Kolmogorov-consistent under refinement
#print axioms QIQTH.CoarseGrainNaturality.born_coarse_grain
-- expected: standard only — bornW ρ (E a) = (π_* (bornW ρ ∘ E')) a when E a = ∑_{π b=a} E' b.
#print axioms QIQTH.CoarseGrainNaturality.born_total_coarse
-- expected: standard only — coarse Born measure sums to the fine one (normalization preserved).
#print axioms QIQTH.CoarseGrainNaturality.coarse_povm_complete
-- expected: standard only — a coarse-graining of a POVM is a POVM (∑E=1 preserved).
-- P2: covariance of the Born kernel under a unitary symmetry
#print axioms QIQTH.CoarseGrainNaturality.bornW_unitary_invariant
-- expected: standard only — bornW (UρUᴴ)(UEUᴴ)=bornW ρ E (trace cyclicity + UᴴU=1).
#print axioms QIQTH.CoarseGrainNaturality.bornW_context_covariant
-- expected: standard only — whole Born vector covariant under unitary transport of state+effects.
#print axioms QIQTH.CoarseGrainNaturality.sum_pushforward_eq
-- expected: standard only — ∑_{a∈A}(π_*μ)(a)=∑_{π b∈A}μ b (cylinder event = preimage measure).
-- P3: cylinder typicality (pre)measure on a directed projective system (canonical finite-record μ)
#print axioms QIQTH.CylinderTypicality.BornProjSystem.consistent
-- expected: standard only — Kolmogorov consistency μ_i = (π)_* μ_j (projective system).
#print axioms QIQTH.CylinderTypicality.BornProjSystem.μ_total
-- expected: standard only — ∑_a μ_i(a) = 1 (each stage a probability measure; uses tr ρ=1).
#print axioms QIQTH.CylinderTypicality.BornProjSystem.μ_nonneg
-- expected: standard only — 0 ≤ μ_i(a) (PSD state + PSD effects).
#print axioms QIQTH.CylinderTypicality.BornProjSystem.cylinder_refine
-- expected: standard only — cylinder measure stage-independent (premeasure well-defined).
#print axioms QIQTH.CylinderTypicality.BornProjSystem.cylinder_common_refine
-- expected: standard only — global consistency via directedness (common refinement).
#print axioms QIQTH.CylinderTypicality.BornProjSystem.μ_covariant
-- expected: standard only — typicality measure invariant under a unitary symmetry of the system.

-- XL-step Phase A smoke test: Finset ι projective family + i.i.d. σ-additive limit via infinitePi
#print axioms QIQTH.HistoryMeasure.productMarginals_isProjectiveLimit
-- expected: standard only — the i.i.d. family's projective-limit measure exists (Mathlib infinitePi).
#print axioms QIQTH.HistoryMeasure.productMarginals_marginal
-- expected: standard only — limit restricts to the product Born marginal at every finite context.
#print axioms QIQTH.HistoryMeasure.FiniteMarginals.limit_unique
-- expected: standard only — the projective-limit typicality measure is unique (determined by marginals).
-- XL Phase A: A3/A4/A5 properties of the history measure μ∞ (conditional on a limit)
#print axioms QIQTH.HistoryMeasure.isLimit_marginal
-- expected: standard only — A3: μ∞ restricts to the Born measure at every finite context.
#print axioms QIQTH.HistoryMeasure.isLimit_marginal_mono
-- expected: standard only — A5: local marginal = restriction of any larger-context marginal (no-signaling).
#print axioms QIQTH.HistoryMeasure.isLimit_map_eq
-- expected: standard only — A4: a marginal-preserving symmetry of the history space is measure-preserving.
-- XL Phase A, A0: matrix Born law → PMF → i.i.d. quantum continuum history measure
#print axioms QIQTH.QuantumHistoryMeasure.bornPMF
-- expected: standard only — the single-measurement Born weights form a PMF (nonneg + sum 1).
#print axioms QIQTH.QuantumHistoryMeasure.quantumHistoryMeasure_marginal
-- expected: standard only — the i.i.d. quantum history measure restricts to the Born product marginal.
-- XL Phase A, A2b: general (correlated) finite-fiber Kolmogorov extension
#print axioms QIQTH.KolmogorovFiniteFiber.projectiveFamilyContent_tendsto_zero
-- expected: standard only — the analytic crux: antitone cylinders, empty ⋂ ⇒ content→0 (compactness/FIP).
#print axioms QIQTH.KolmogorovFiniteFiber.kolmogorovMeasure_isProjectiveLimit
-- expected: standard only — the Kolmogorov measure IS the projective limit (correlated case, no product).
#print axioms QIQTH.KolmogorovFiniteFiber.exists_isLimit
-- expected: standard only — EXISTENCE: every finite-fiber FiniteMarginals family has a σ-additive μ∞.
-- XL Phase B (formalizable core): the typicality measure is STATE-AGNOSTIC
#print axioms QIQTH.StateNetMeasure.EffectStateNet.toFiniteMarginals
-- expected: standard only — B1: any state ω on a net of compatible effects ⇒ Kolmogorov-consistent Born family.
#print axioms QIQTH.StateNetMeasure.EffectStateNet.exists_typicalityMeasure
-- expected: standard only — μ∞ exists for ANY EffectStateNet (Type III₁ QFT realization of ω is the cited frontier).
#print axioms QIQTH.StateNetMeasure.EffectStateNet.diracNet_exists_typicalityMeasure
-- expected: standard only — NON-VACUITY: a concrete deterministic net fires the whole state→μ∞ pipeline
-- (the EffectStateNet hypotheses are jointly satisfiable; no soundness/vacuity hole).

-- Phase B Part A (first brick): a genuine infinite-dim normal state on B(H) (diagonal density operator)
#print axioms QIQTH.NormalState.diagState_add
-- expected: standard only — ω(x+y)=ω(x)+ω(y): the diagonal state is additive (bundled diagStateHom).
#print axioms QIQTH.NormalState.diagState_nonneg
-- expected: standard only — 0 ≤ ω(x) for x ≥ 0 (positivity on positive operators).
#print axioms QIQTH.NormalState.diagState_one
-- expected: standard only — ω(1)=∑ pᵢ (=1 for a density operator): normalization. So ω is a state.
-- Phase B Part A — closing the loop on B(H): the normal state drives the EffectStateNet → μ∞ pipeline
#print axioms QIQTH.BHTypicalityMeasure.bh_typicalityMeasure_exists
-- expected: standard only — END TO END on infinite-dim B(H): a genuine normal state ω=Tr(ρ·) yields a
-- unique σ-additive probability typicality measure μ∞ on histories (via EffectStateNet + Kolmogorov ext).
-- Phase B Part A — general trace-class step (Simon §1.1): operator absolute value |T|=√(T⋆T)
#print axioms QIQTH.AbsoluteValue.absOp_mul_self
-- expected: standard only — |T|·|T|=T⋆T (√x·√x=x on the nonneg spectrum of T⋆T; no StarOrderedRing needed).
#print axioms QIQTH.AbsoluteValue.norm_absOp_apply
-- expected: standard only — ‖|T|x‖=‖Tx‖ (the defining isometry property of the absolute value).
-- Toward the prize: free-field (finite-mode) covariant typicality measure
#print axioms QIQTH.FreeFieldTypicality.freeFieldMeasure_marginal
-- expected: standard only — the free-field history measure restricts to the product Born marginal.
#print axioms QIQTH.FreeFieldTypicality.freeFieldMeasure_boost_invariant
-- expected: standard only — μ∞ INVARIANT under the geometry-moving mode-permutation boost (covariance,
-- finite-mode Lorentz action) when the per-region state is boost-invariant.

-- F1 (Fock/CCR foundation): the one-particle space and the continuum boost UNITARY GROUP.
#print axioms QIQTH.Fock.OneParticle.MPFlow.unitary_apply
-- expected: standard only — the measure-preserving flow acts on L² by the unitary ψ ↦ ψ∘χ_{-t}.
#print axioms QIQTH.Fock.OneParticle.MPFlow.unitary_add_apply
-- expected: standard only — one-parameter group law U(s+t)=U(s)∘U(t) for the abstract flow unitary.
#print axioms QIQTH.Fock.OneParticle.boostUnitary_add_apply
-- expected: standard only — the 1+1D massive Lorentz boost (rapidity=translation on L²(ℝ)) is a
-- one-parameter unitary GROUP: the genuine continuum replacement for the finite mode-permutation boost.
#print axioms QIQTH.Fock.OneParticle.boostUnitary_zero_apply
-- expected: standard only — boost at rapidity 0 is the identity.

-- F2 keystone: the exponential kernel exp⟪f,g⟫ is positive semidefinite (builds the bosonic Fock space).
#print axioms QIQTH.Fock.ExpKernel.hPow_posSemidef
-- expected: standard only — entrywise (Hadamard) powers of a PSD matrix are PSD (Schur, iterated).
#print axioms QIQTH.Fock.ExpKernel.expKernel_isHermitian
-- expected: standard only — the exponential kernel is Hermitian.
#print axioms QIQTH.Fock.ExpKernel.expKernel_posSemidef
-- expected: standard only — KEYSTONE: exp⟪f,g⟫ is a positive-definite kernel (Gram PSD + Schur product
-- theorem + exp = ∑ₖ ·ᵏ/k! with 1/k!≥0).  This is what RKHS.OfKernel turns into the symmetric Fock
-- space whose kernel functions are the exponential vectors e(f) with ⟪e(f),e(g)⟫ = exp⟪f,g⟫.
#print axioms QIQTH.Fock.ExpKernel.expKernel_posSemidef'
-- expected: standard only — the INFINITE-index keystone (arbitrary, possibly inf-dim family), via
-- support-restriction to the finite case.  The form the exponential-vector inner product consumes.

-- F2c: the symmetric (bosonic) Fock space, pre-Hilbert structure (exponential vectors).
#print axioms QIQTH.Fock.fockInner_self_nonneg
-- expected: standard only — ⟪φ,φ⟫ ≥ 0 (= the keystone expKernel_posSemidef').
#print axioms QIQTH.Fock.FockPre.instCore
-- expected: standard only — PreInnerProductSpace.Core ℂ on the exponential-vector pre-space: the
-- pre-Hilbert symmetric Fock space (positive-semidefinite Hermitian inner product, conj-linear).
#print axioms QIQTH.Fock.FockPre.inner_expVec
-- expected: standard only — the DEFINING coherent-state identity ⟪e(f),e(g)⟫ = exp⟪f,g⟫.
-- F2c completion: the actual Fock HILBERT space (completion), vacuum, coherent-state identity.
#print axioms QIQTH.Fock.Fock.inner_expVec
-- expected: standard only — ⟪e(f),e(g)⟫ = exp⟪f,g⟫ in the completed Fock space (genuine Hilbert space).
#print axioms QIQTH.Fock.Fock.inner_vacuum
-- expected: standard only — the vacuum Ω = e(0) is a unit vector ⟪Ω,Ω⟫ = 1.
-- F3 (part): the quasifree vacuum STATE ω₀(T)=Re⟪Ω,TΩ⟫ on B(Fock) — the ω that EffectStateNet consumes.
#print axioms QIQTH.Fock.vacuumState_nonneg
-- expected: standard only — ω₀ ≥ 0 on positive operators.
#print axioms QIQTH.Fock.vacuumState_one
-- expected: standard only — ω₀(1) = 1 (vacuum is a unit vector); so ω₀ is a genuine state on B(Fock).
-- F3 (part): the Weyl/CCR algebraic core on exponential vectors.
#print axioms QIQTH.Fock.Weyl.weyl_isometry
-- expected: standard only — W(u) preserves the coherent-state inner product (CCR unitarity core).
#print axioms QIQTH.Fock.Weyl.weylCoeff_vacuum
-- expected: standard only — ⟪Ω,W(u)Ω⟫ = exp(−½‖u‖²): the defining value of the quasifree vacuum state.
-- F6 (first increment): the prize pipeline runs on the genuine continuum Fock space + vacuum state.
#print axioms QIQTH.Fock.fock_typicalityMeasure_exists
-- expected: standard only — END-TO-END: the quasifree vacuum state ω₀ on B(Fock H) drives a unique
-- σ-additive probability typicality measure μ∞ (via EffectStateNet + the Kolmogorov extension), on the
-- genuine continuum free-field Fock space.  The continuum analogue of bh_typicalityMeasure_exists.

-- F2-Γ: second quantization Γ(A)e(f)=e(Af) and the Lorentz boost on the Fock space.
#print axioms QIQTH.Fock.secondQuantPre_expVec
-- expected: standard only — Γ(A) e(f) = e(A f) (the pushforward Finsupp.mapDomain A).
#print axioms QIQTH.Fock.fockInner_secondQuant
-- expected: standard only — Γ(A) preserves the coherent-state inner product (A isometric) → Γ(A) isometric.
#print axioms QIQTH.Fock.secondQuantPre_comp
-- expected: standard only — functoriality Γ(A)∘Γ(B) = Γ(A∘B).
#print axioms QIQTH.Fock.boostFock_vacuum
-- expected: standard only — VACUUM INVARIANCE Γ(U₁(t))Ω = Ω: the boost fixes the Fock vacuum — the key
-- input to boost-covariance of μ∞ (the full F6 prize).
-- The Lorentz boost as a genuine isometry of the completed Fock HILBERT space, fixing the vacuum.
#print axioms QIQTH.Fock.boostFockH_isometry
-- expected: standard only — Γ(U₁(t)) is an isometry of Fock(L²(ℝ)) (completion of the pre-level boost).
#print axioms QIQTH.Fock.boostFockH_vacuum
-- expected: standard only — Γ(U₁(t)) Ω = Ω in the completed Fock Hilbert space.
-- Boost-invariance of the QUASIFREE VACUUM STATE on the Weyl observables (vacuum covariance).
#print axioms QIQTH.Fock.Weyl.weylCoeff_vacuum_isometry_invariant
-- expected: standard only — ⟪Ω,W(A u)Ω⟫ = ⟪Ω,W(u)Ω⟫ for any one-particle isometry A (depends only on ‖u‖²).
#print axioms QIQTH.Fock.weylCoeff_vacuum_boost_invariant
-- expected: standard only — ⟪Ω,W(U₁(t)u)Ω⟫ = ⟪Ω,W(u)Ω⟫: the quasifree vacuum state is LORENTZ-BOOST
-- INVARIANT (the boost preserves ‖u‖) — the physical heart of boost-covariance.
-- The bounded WEYL OPERATOR W(u) on Fock (GPT-flagged keystone): W(u)e(g)=c·e(g+u), isometric, unitary.
#print axioms QIQTH.Fock.weylPre_expVec
-- expected: standard only — W(u) e(g) = weylCoeff u g · e(g+u) (the coherent-vector action).
#print axioms QIQTH.Fock.fockInner_weyl
-- expected: standard only — W(u) preserves the coherent-state inner product (= weyl_isometry summed) →
-- W(u) is an ISOMETRY of the Fock space; the algebraic content making W(u) unitary.
#print axioms QIQTH.Fock.Weyl.weylCoeff_adjoint
-- expected: standard only — the coefficient-level adjoint identity conj(c_g)·exp⟪g+u,h⟫=exp⟪g,h−u⟫·c'_h.
#print axioms QIQTH.Fock.fockInner_weyl_adjoint
-- expected: standard only — W(u)* = W(−u): ⟪W(u)φ,ψ⟫=⟪φ,W(−u)ψ⟫ (weylCoeff_adjoint summed). W(u) is
-- UNITARY (isometry + inverse W(−u)); the keystone for the Weyl-bit effects E(u,s)=A(u,s)*A(u,s).
#print axioms QIQTH.Fock.weylPre_neg_cancel
-- expected: standard only — W(−u) W(u) = id (weylCoeff_neg_cancel: the two exponents cancel), so W(−u) is
-- the EXACT two-sided inverse of W(u) (not up to a phase); W(u) is invertible + unitary.
#print axioms QIQTH.Fock.effOp_sum_eq_id
-- expected: standard only — POVM COMPLETENESS E(u,+1)+E(u,−1)=I: {E(u,+1),E(u,−1)} is a genuine
-- operator-valued POVM (resolution of identity via W(−u)W(u)=I), not just positive effects.
#print axioms QIQTH.Fock.weylPre_zero
-- expected: standard only — W(0) = id.
#print axioms QIQTH.Fock.weylH_isometry
-- expected: standard only — W(u) extends to a genuine isometry of the completed Fock Hilbert space.
#print axioms QIQTH.Fock.fockInner_vacuum_weyl
-- expected: standard only — ⟪Ω,W(u)Ω⟫ = exp(−½‖u‖²): the quasifree value, as an actual operator m.e.
-- GPT Increment 2: the first NON-VACUOUS continuum boost-covariance (vacuum two-point Weyl function).
#print axioms QIQTH.Fock.weyl2pt_eq
-- expected: standard only — ⟪Ω,W(u)W(v)Ω⟫ = weylCoeff v 0 · weylCoeff u v (depends only on inner products).
#print axioms QIQTH.Fock.weyl2pt_boost_invariant
-- expected: standard only — ⟪Ω,W(U₁(t)u)W(U₁(t)v)Ω⟫ = ⟪Ω,W(u)W(v)Ω⟫: the vacuum two-point function is
-- LORENTZ-BOOST INVARIANT — a genuinely non-vacuous continuum boost-covariance (tests quasifree
-- correlations, unlike the deterministic typicality net).
#print axioms QIQTH.Fock.weylBitWeight_mem_Ioo
-- expected: standard only — the Weyl-bit Born weight (1+exp(−½‖u‖²))/2 ∈ (0,1) for u≠0: the would-be
-- Weyl-bit POVM is a genuine non-degenerate effect (the non-vacuity the deterministic Fock net lacked).
-- GPT Increment 3 core: MICROCAUSALITY (locality / no-signaling mechanism of the free field).
#print axioms QIQTH.Fock.weylPre_comp_expVec
-- expected: standard only — W(u)W(v) e(g) = c·e(g+v+u) (the composite on a coherent vector).
#print axioms QIQTH.Fock.weyl_microcausality
-- expected: standard only — W(u)∘W(v) = W(v)∘W(u) when Im⟪u,v⟫=0 (symplectic orthogonality, as
-- spacelike-separated smearings give): spacelike Weyl observables COMMUTE — Einstein causality.
-- Stage 1.1 (measure prize): the Weyl-bit norm-square Born law (positivity free, normalization).
#print axioms QIQTH.Fock.bit_normSq_sum
-- expected: standard only — ‖A(u,1)ψ‖²+‖A(u,−1)ψ‖²=‖ψ‖² (parallelogram + W isometric): the normalization
-- engine. A(u,s)=(I+s·W(u))/2, the Weyl bit; E(u,s)=A(u,s)*A(u,s) so Born weights are norm-squares (≥0 free).
#print axioms QIQTH.Fock.two_bit_normalization
-- expected: standard only — the four two-bit Weyl-bit Born weights sum to 1 (a probability distribution).
#print axioms QIQTH.Fock.totalWeight_vac
-- expected: standard only — the n-bit Weyl-bit Born weights of any finite family sum to 1 (telescoping).
-- Stage 1.2: boost-covariance — every Weyl-bit joint Born weight is Lorentz-invariant.
#print axioms QIQTH.Fock.weylPre_secondQuant_comm
-- expected: standard only — intertwining W(Au)∘Γ(A)=Γ(A)∘W(u) (from weylCoeff_isometry_invariant).
#print axioms QIQTH.Fock.histVec_boost
-- expected: standard only — histVec(A·family) = Γ(A)(histVec family) (boost equivariance of the history vector).
#print axioms QIQTH.Fock.bornWeight_boost_invariant
-- expected: standard only — ‖∏A(U₁(t)uᵢ,sᵢ)Ω‖² = ‖∏A(uᵢ,sᵢ)Ω‖²: every Weyl-bit joint Born weight is
-- LORENTZ-BOOST INVARIANT on the continuum free field — the per-outcome measure-level covariance.
#print axioms QIQTH.Fock.histVec_marginal
-- expected: standard only — PROJECTIVITY: marginalizing a bit gives the smaller-family weight. Together
-- with positivity (free), normalization (totalWeight_vac) and boost-covariance, the four Kolmogorov
-- ingredients for the σ-additive boost-covariant μ∞ are now all proven.

-- Stage 1.3: the Finset-context Born weight and its NORMALIZATION over an arbitrary finite context.
#print axioms QIQTH.Fock.bornVecTot_insert
-- expected: standard only — the order-independent history product ∏_{i∈J} A(uᵢ,sᵢ)Ω (Finset.noncommProd
-- over the COMMUTING bit operators, bitOp_commute from microcausality); insert prepends a bit.
#print axioms QIQTH.Fock.bornWeight_insert
-- expected: standard only — the Finset Born weight ‖∏_{i∈J} A(uᵢ,σᵢ)Ω‖² factors a bit off the head.
#print axioms QIQTH.Fock.bornWeight_total
-- expected: standard only — NORMALIZATION over an arbitrary finite context: ∑_σ bornWeight J σ = 1, by
-- induction on J (the explicit bit-splitting equiv insertBoolSplit reduces the inductive step to
-- bit_normSq_sum). The σ-additive μ∞'s `total` Kolmogorov obligation, now proven for any finite J.
#print axioms QIQTH.Fock.bornWeight_marginal
-- expected: standard only — PROJECTIVITY (single-mode marginal): summing the free bit at a head mode a∉J'
-- collapses bornWeight (insert a J') to bornWeight J' (bit_normSq_sum on the Finset Born weight). The
-- inductive step for the general coarse-graining consistency of the joint Born law.
#print axioms QIQTH.Fock.bornWeight_erase_marginal
-- expected: standard only — projectivity peeling the free bit at ANY a∈J (erase form), via bornVecTot_erase.
#print axioms QIQTH.Fock.bornWeight_coarse
-- expected: standard only — COARSE-GRAINING CONSISTENCY (Kolmogorov projectivity) of the joint Weyl-bit
-- Born law: for any I⊆J, bornWeight I y = ∑_{x↾I=y} bornWeight J x. Strong induction on J peeling one
-- FREE mode a∈J\I at a time (bornWeight_erase_marginal). The `coarse` obligation of EffectStateNet —
-- the last ingredient (with pos, total, boost-covariance) for the σ-additive boost-covariant μ∞.
#print axioms QIQTH.Fock.weylBit_typicalityMeasure_exists
-- expected: standard only — THE FIRST NON-DETERMINISTIC TYPICALITY MEASURE on the continuum free field:
-- the genuine Weyl-bit EffectStateNet (Born weights forming an actual 2^|J| probability distribution, not
-- a point mass) yields a σ-additive probability μ∞ on the history space via the Kolmogorov extension.
#print axioms QIQTH.Fock.bornWeight_isometry_invariant
-- expected: standard only — the joint Born weight is invariant under boosting every mode uᵢ↦A uᵢ by a
-- one-particle isometry A (Γ(A) push-through bornVecTot_secondQuant + Γ(A) unitary).
#print axioms QIQTH.Fock.weylBit_marginals_boost_invariant
-- expected: standard only — the ENTIRE projective family of finite Weyl-bit Born marginals is unchanged
-- under boosting the modes by a one-particle isometry (the measure-level Lorentz-covariance statement).
#print axioms QIQTH.Fock.weylBit_typicality_boost_invariant
-- expected: standard only — THE PRIZE: the σ-additive typicality measure μ∞ on the continuum free field is
-- LORENTZ-BOOST-COVARIANT. μ for modes u and ν for boosted modes A∘u realize the SAME projective family
-- (weylBit_marginals_boost_invariant), so μ=ν by uniqueness of the Kolmogorov limit. Axiom-free (the
-- standard three). The literal Open-Problem-3b deliverable on the relativistic free field, machine-checked.
#print axioms QIQTH.Fock.weylBit_typicality_lorentzBoost_invariant
-- expected: standard only — THE PRIZE specialized to the F1 Lorentz boost U₁(t) on L²(ℝ): the Weyl-bit
-- typicality measure μ∞ is invariant under U₁(t) (boostUnitary_preserves_isotropy supplies the boosted
-- microcausality). The typicality measure is the same in every Lorentz frame.

-- B.0: the Weyl-bit EFFECTS — Born weights are genuine vacuum-state POVM expectations.
#print axioms QIQTH.Fock.bitOp_adjoint_inner
-- expected: standard only — A(u,s) and A(u,s)*=(I+s̄W(−u))/2 are adjoint (from W(u)*=W(−u)).
#print axioms QIQTH.Fock.bit_effect_expectation
-- expected: standard only — ⟪ψ,E(u,s)ψ⟫ = ‖A(u,s)ψ‖²: the norm-square Born weight IS the vacuum/state
-- expectation of the POSITIVE effect E(u,s)=A(u,s)*A(u,s) (positivity = norm-square, manifestly T*T).
#print axioms QIQTH.Fock.bornWeight_singleton_eq_effect
-- expected: standard only — the single-mode Weyl-bit Born weight = ⟪Ω,E(uᵢ,±)Ω⟫, a genuine two-outcome
-- POVM {E(uᵢ,+1),E(uᵢ,−1)} expectation in the quasifree vacuum (the operational reading of the prize).
#print axioms QIQTH.Fock.bornVecTot_adjoint_inner
-- expected: standard only — ⟪∏A(uᵢ,sᵢ)Ω,ψ⟫=⟪Ω,∏A(uᵢ,sᵢ)*ψ⟫ (product adjoint, induction peeling one bit
-- via bitOp_adjoint_inner + commuting the head adjoint through the rest, bitAdj_commute/microcausality).
#print axioms QIQTH.Fock.bornWeight_eq_joint_effect
-- expected: standard only — THE JOINT POVM expectation: the full multi-mode Born weight bornWeight J σ =
-- ⟪Ω, E_σ Ω⟫ with E_σ = (∏A(uᵢ,σᵢ))*(∏A(uᵢ,σᵢ)) the positive joint effect. Every joint Born weight on the
-- continuum free field is a genuine vacuum-state expectation of a positive bounded effect (B.0 complete).

-- Increment 1: the abstract GEOMETRIC covariance interface (relabeling = boost via equivariance).
#print axioms QIQTH.Fock.GeoCovariantModes.bornWeight_relabel
-- expected: standard only — Born weight of the relabeled modes u∘π = Born weight of u (relabel = boost
-- via equivariance u(πi)=A(ui), then Γ(A) isometric).
#print axioms QIQTH.Fock.GeoCovariantModes.typicality_invariant
-- expected: standard only — GEOMETRIC COVARIANCE OF μ∞: the typicality measure for the geometrically
-- relabeled mode family u∘π equals the one for u. Abstract local-net covariance interface (GeoCovariantModes:
-- π relabeling, A one-particle symmetry, equivariance, microcausality) — the obligations a concrete
-- spacetime localization K would supply; specializes to Lorentz-boost frame-independence.

-- Increment 2: the LITERAL single-measure pushforward (the noncommProd reindex-by-bijection Mathlib lacks).
#print axioms QIQTH.Fock.bornVecTot_map
-- expected: standard only — Born history vector reindexed by an index bijection π (∏ over J.map π of v's
-- bits = ∏ over J of (v∘π)'s bits), by induction on the context.
#print axioms QIQTH.Fock.bornWeight_map
-- expected: standard only — Born weight reindexed by π: bornWeight v (J.map π) (outReindex σ) =
-- bornWeight (v∘π) J σ (signExt congruence on the relabeled context).
#print axioms QIQTH.Fock.GeoCovariantModes.typicality_pushforward_invariant
-- expected: standard only — THE LITERAL PUSHFORWARD COVARIANCE: (historyAct π)_* μ∞ = μ∞ as a single
-- measure (strengthens typicality_invariant). Pushforward marginal = μ-marginal on J.map π reindexed back
-- (singleton set identity) + π-invariance of Born weights ⇒ same projective family ⇒ uniqueness.

-- Stage 2 skeleton: the spacetime-localization interface (K + Pauli-Jordan + Poincare equivariance).
#print axioms QIQTH.Fock.SpacetimeLocalization.toGeoCovariantModes
-- expected: standard only — a localization datum (K:TestFun→H, region/boostT/relabel, equivariance,
-- Pauli-Jordan microcausality) yields a GeoCovariantModes datum (modes uᵢ=K(region i), isotropy from
-- pauli_jordan + distinct_spacelike, equivariance from K_equivariant + region_equivariant).
#print axioms QIQTH.Fock.SpacetimeLocalization.localized_typicality_exists
-- expected: standard only — the σ-additive Weyl-bit μ∞ over the spacelike-local field records exists.
#print axioms QIQTH.Fock.SpacetimeLocalization.localized_typicality_pushforward_invariant
-- expected: standard only — THE LOCALIZED PRIZE (skeleton): (historyAct π)_* μ∞ = μ∞ for the local field,
-- modulo the CITED concrete K (Pauli-Jordan/Wightman construction = the multi-month physics frontier).
#print axioms QIQTH.Fock.trivialLocalization
-- expected: standard only — non-vacuity witness: SpacetimeLocalization is inhabited (degenerate zero-mode
-- instance; nontrivial K = cited physics program), certifying the interface hypotheses are satisfiable.

-- The completed-Fock / CLM lift: bounded Weyl operators on the Fock Hilbert space + Born weight as a
-- genuine vacuum C*-state expectation of a bounded POVM effect.
#print axioms QIQTH.Fock.clmLift_coe
-- expected: standard only — bundled lift of a bounded FockPre operator to a CLM on Fock H (via
-- ContinuousLinearMap.extend along the dense isometric embedding toComplL), agreeing on the dense subspace.
#print axioms QIQTH.Fock.weylCLM_neg_cancel
-- expected: standard only — CCR-unitarity W(-u)W(u)=1 of the bounded Weyl operator on the Fock Hilbert space.
#print axioms QIQTH.Fock.weylCLM_vacuum_inner
-- expected: standard only — the genuine vacuum two-point matrix element ⟪Ω,W(u)Ω⟫=exp(-½⟪u,u⟫) ON THE
-- completed Hilbert space (GPT's single load-bearing operator-level theorem).
#print axioms QIQTH.Fock.weylBitEffectCLM_complete
-- expected: standard only — operator POVM completeness E(u,+1)+E(u,-1)=1 of bounded effects on Fock H.
#print axioms QIQTH.Fock.vacuumState_weylBitEffectCLM_true
-- expected: standard only — the single-mode Weyl-bit Born weight IS a genuine vacuum C*-state expectation
-- of a bounded positive effect: vacuumState(E(u,+1)) = (1+exp(-½‖u‖²))/2 = weylBitWeight u.

-- Concrete non-degenerate boost-orbit instance (GPT's minimal pushforward-invariant K milestone).
#print axioms QIQTH.Fock.boostOrbitModes
-- expected: standard only — discrete boost orbit uₙ=U₁(nτ)u₀ on L²(ℝ) as a GeoCovariantModes: boost of
-- rapidity τ acts by the shift n↦n+1 (equivariance from the boostUnitary group law), microcausality reduced
-- to the single seed condition hiso0 (Im⟪u₀,U₁(kτ)u₀⟫=0, k≠0 — the residual Pauli-Jordan input).
#print axioms QIQTH.Fock.boostOrbit_typicality_pushforward_invariant
-- expected: standard only — μ∞ over the boost orbit is fixed by the boost-induced shift n↦n+1 on the
-- history space ∏_{n:ℤ}{±1}: a non-degenerate continuum realization of the pushforward covariance.

-- Joint multi-mode effect lift (closing the pre-Hilbert gap) + sharp single-mode range.
#print axioms QIQTH.Fock.weylBitWeight_mem_Ioo_half
-- expected: standard only — sharp non-degeneracy: weylBitWeight u ∈ (1/2,1) for u≠0 (tightens (0,1)).
#print axioms QIQTH.Fock.jointEffectCLM_isPositive
-- expected: standard only — the joint Weyl-bit effect E_σ=(∏A)*(∏A) is a positive bounded operator on Fock H.
#print axioms QIQTH.Fock.vacuumState_jointEffectCLM
-- expected: standard only — the FULL multi-mode Born weight is a genuine vacuum C*-state expectation of a
-- bounded positive Hilbert-space effect: vacuumState(E_σ)=bornWeight u J σ (closes the pre-Hilbert gap).
#print axioms QIQTH.Fock.jointEffectCLM_complete
-- expected: standard only — JOINT POVM COMPLETENESS ∑_σ E_σ = 1 as an OPERATOR identity on Fock H (via the
-- generalized ∑_σ‖(∏A)φ‖²=‖φ‖² lifted by density + inner_map_self_eq_zero). With _isPositive and
-- vacuumState_jointEffectCLM, {E_σ} is a genuine operator POVM with vacuum Born weights — earns "POVM".

-- K-localization Phase 0: 1+1D Minkowski geometry (convention lock for the concrete localization map K).
#print axioms QIQTH.Fock.Localization.massShell_boost
-- expected: standard only — the rapidity-a boost shifts the mass shell, Λa(p_m θ)=p_m(θ+a) (cosh/sinh add).
#print axioms QIQTH.Fock.Localization.minkowskiDot_boost
-- expected: standard only — the Minkowski pairing is boost-invariant, η(Λp,Λx)=η(p,x) (cosh²−sinh²=1).
#print axioms QIQTH.Fock.Localization.det_lorentzBoost
-- expected: standard only — the boost is unimodular, det Λa = cosh²a−sinh²a = 1 (unit Jacobian for the
-- Fourier change of variables; via Matrix.toLin' + det_fin_two).
#print axioms QIQTH.Fock.Localization.measurePreserving_lorentzBoost
-- expected: standard only — the Lorentz boost preserves the Lebesgue volume on ℝ² (unit Jacobian, via
-- map_linearMap_addHaar_eq_smul_addHaar + det = 1) — the measure-preservation for the Fourier change of
-- variables in boost-equivariance. Phase 1b foundation.
#print axioms QIQTH.Fock.Localization.measurableEmbedding_lorentzBoost
-- expected: standard only — the boost is a measurable embedding (continuous linear equivalence Λa, inverse
-- Λ(-a)).
#print axioms QIQTH.Fock.Localization.minkowskiFourier_boost
-- expected: standard only — PHASE 1c KEYSTONE: boost-equivariance of the localization (Minkowski-Fourier)
-- map, (β_a f)^_M(p) = f̂_M(Λa p), via the change of variables y=Λa x (MeasurePreserving.integral_comp +
-- measurable embedding) + Minkowski-pairing boost-invariance. The localization intertwines the spacetime
-- boost with the one-particle (rapidity-translation) action.
#print axioms QIQTH.Fock.Localization.Krep_boost
-- expected: standard only — the localized rapidity amplitude (K f)(θ)=2^{-1/2}f̂_M(p_m θ) is boost-covariant:
-- (K(β_a f))(θ)=(K f)(θ+a), i.e. the Lorentz boost acts as the rapidity translation θ↦θ+a (the boostUnitary
-- action). From minkowskiFourier_boost + massShell_boost. Phase 2a.
#print axioms QIQTH.Fock.Localization.minkowskiFourier_conj
-- expected: standard only — reality/both-frequencies: conj(f̂_M(p)) = (conj f)^_M(−p); for real f this gives
-- conj(f̂_M(p))=f̂_M(−p), the relation making the full (both-frequency) Pauli–Jordan symplectic form emerge
-- from the positive-mass-shell amplitude (Phase 2b foundation; soundness traps #4/#6).
#print axioms QIQTH.Fock.Localization.Kform_im_antisymm
-- expected: standard only — the localized symplectic form Im⟨Kf,Kg⟩ is ANTISYMMETRIC (= −Im⟨Kg,Kf⟩), the
-- defining property of the Pauli–Jordan commutator form (NOT the symmetric Wightman 2-pt function; trap #6).
-- Via Hermitian symmetry conj⟨Kf,Kg⟩=⟨Kg,Kf⟩ (Kform_conj, integral_conj + conj_conj).
#print axioms QIQTH.Fock.Localization.K
-- expected: standard only — the L²-valued localization map K : LocalTest → L²(ℝ) (the one-particle-Hilbert-
-- space-valued localization; K L = the L² class of the rapidity amplitude Krep m L.f). The memLp domain
-- condition is a structure field; the Schwartz⟹memLp proof is the isolated analytic refinement.
#print axioms QIQTH.Fock.Localization.trivialLocalTest
-- expected: standard only — non-vacuity: the localizable-test class is inhabited (degenerately, f=0).
#print axioms QIQTH.Fock.Localization.minkowskiFourier_continuous
-- expected: standard only — Fourier transform of an integrable function is continuous (Riemann–Lebesgue,
-- dominated convergence + |exp|=1).
#print axioms QIQTH.Fock.Localization.Krep_aestronglyMeasurable
-- expected: standard only — part (a) of the boundedness MemLp: the localized amplitude Krep m f is
-- continuous (hence AEStronglyMeasurable) for integrable f. Part (b) (the L² bound from Schwartz–Fourier
-- mass-shell decay) is the isolated multi-week analytic core, carried as the LocalTest.memLp domain field.
#print axioms QIQTH.Fock.Localization.one_add_sq_le_cosh_sq
-- expected: standard only — 1+θ² ≤ cosh²θ (cosh²=1+sinh², sinh²θ≥θ²).
#print axioms QIQTH.Fock.Localization.memLp_cosh_inv
-- expected: standard only — 1/cosh ∈ L²(ℝ): cosh⁻² dominated by the Cauchy density (1+θ²)⁻¹
-- (integrable_inv_one_add_sq), the comparison function for the localized-amplitude boundedness.
#print axioms QIQTH.Fock.Localization.Krep_memLp_of_decay
-- expected: standard only — BOUNDEDNESS REDUCED TO A DECAY BOUND: if ‖(K f)(θ)‖ ≤ C/cosh θ then K f ∈ L²
-- (MemLp.of_le_mul against memLp_cosh_inv). All integrability discharged; the remaining obligation is the
-- sharp pointwise Fourier-decay estimate (the Fourier transform of a smooth test decays on the mass shell).
#print axioms QIQTH.Fock.Localization.two_sq_le_cosh_two_mul
-- expected: standard only — 2θ² ≤ cosh(2θ) (cosh(2θ)=1+2sinh²θ, sinh²θ≥θ²).
#print axioms QIQTH.Fock.Localization.integrable_exp_neg_cosh_two_mul
-- expected: standard only — exp(−c·cosh 2θ) integrable on ℝ (c>0), dominated by the Gaussian exp(−2cθ²) —
-- the integrability of the Gaussian test's |Krep|², toward a concrete non-degenerate LocalTest.
#print axioms QIQTH.Fock.Localization.minkowskiFourier_gaussian
-- expected: standard only — EXPLICIT Minkowski-Fourier transform of the 2D Gaussian: a separable product of
-- two 1D complex Gaussian Fourier integrals (Fubini via integral_fintype_prod_volume_eq_prod +
-- fourierIntegral_gaussian). The crown-jewel computation toward a concrete non-degenerate Krep_memLp.
#print axioms QIQTH.Fock.Localization.gaussian_Krep_memLp
-- expected: standard only — ★ THE BOUNDEDNESS CLOSED for a concrete physical test: the Gaussian's
-- localized amplitude is in L²(ℝ). ‖(K f)(θ)‖²=(π²/2)exp(−(m²/2)cosh 2θ), integrable. Krep_gaussian_eq
-- (real-cast value via cpow_add + ofReal_exp + cosh_two_mul) + integrable_exp_neg_cosh_two_mul.
#print axioms QIQTH.Fock.Localization.gaussianLocalTest
-- expected: standard only — a GENUINELY NON-DEGENERATE LocalTest (the Gaussian, m≠0): the boundedness
-- obligation of LocalTest is satisfied non-trivially (vs the f=0 trivialLocalTest), machine-checked.

-- K-localization: GENERAL SCHWARTZ 1/cosh decay (GPT-5.5-pro next-step #1 — widens the admissible
-- test class from Gaussian-only to ALL Schwartz functions, the honest "local test class").
#print axioms QIQTH.Fock.Localization.minkBilin_apply
-- expected: standard only — the rescaled Minkowski bilinear form L v w = (v₀w₀−v₁w₁)/(2π).
#print axioms QIQTH.Fock.Localization.minkowskiFourier_eq_fourierIntegral
-- expected: standard only — ★ BRIDGE: the bespoke (no-2π Minkowski) transform IS a
-- VectorFourier.fourierIntegral for L, importing Mathlib's Fourier-decay machinery.
#print axioms QIQTH.Fock.Localization.abs_sinh_le_cosh
-- expected: standard only — |sinh θ| ≤ cosh θ.
#print axioms QIQTH.Fock.Localization.schwartz_Krep_memLp
-- expected: standard only — ★ THE GENERAL DECAY: for ANY Schwartz f and m≠0, ‖Krep m f θ‖ ≤ C·(cosh θ)⁻¹
-- via the test vector v=(p₀,−p₁) extracting L v p=(p₀²+p₁²)/(2π) and p₀²+p₁²≥m²cosh²θ on the shell;
-- hence Krep m f ∈ L²(ℝ).  Closes GPT's prerequisite for "K is L²-bounded" as an operator statement.
#print axioms QIQTH.Fock.Localization.schwartzLocalTest
-- expected: standard only — every Schwartz spacetime test function is an L²-admissible LocalTest.

-- K-localization: PAULI–JORDAN BACKBONE (toward the single remaining input for the literal prize).
#print axioms QIQTH.Fock.Localization.Kform_boost_invariant
-- expected: standard only — ★ the localized symplectic (commutator) form is Lorentz-boost invariant:
-- Kform m (β_a f)(β_a g) = Kform m f g.  Microcausality is a boost-invariant statement.
#print axioms QIQTH.Fock.Localization.minkowskiDot_massShell
-- expected: standard only — the mass-shell phase η(p_m θ, z) = m(z₀ cosh θ − z₁ sinh θ).
#print axioms QIQTH.Fock.Localization.minkowskiDot_massShell_spacelike
-- expected: standard only — ★ the hyperbolic reparametrization: for spacelike z, η(p_m θ,z)=c·sinh(θ−φ),
-- so the kernel sin(η) is ODD in θ−φ (the source of the Pauli–Jordan cancellation).
#print axioms QIQTH.Fock.Localization.pauliJordan_trunc_equalTime_zero
-- expected: standard only — ★ the EXACT equal-time vanishing: ∫_{−R}^{R} sin(η(p_m θ,z))dθ = 0 for every
-- R when z₀=0 (odd integrand).  Microcausality cancellation in cleanest form.
#print axioms QIQTH.Fock.Localization.integral_sinh_div_cosh_sq
-- expected: standard only — ∫_a^b sinh x/cosh²x dx = (cosh a)⁻¹ − (cosh b)⁻¹ (FTC, antiderivative −1/cosh).
#print axioms QIQTH.Fock.Localization.abs_integral_sin_sinh_le
-- expected: standard only — ★★ THE OSCILLATORY KEYSTONE (GPT-5.5-pro's flagged wall): for 0≤a≤b,
-- |∫_a^b sin(c·sinh u)du| ≤ 3/(|c|·cosh a) — the oscillatory integral is controlled by 1/cosh a despite
-- the integrand never decaying.  Integration by parts (u=(c cosh)⁻¹, v=−cos(c sinh)) + the FTC remainder.
#print axioms QIQTH.Fock.Localization.integral_sin_sinh_symm_zero
-- expected: standard only — ∫_{−T}^{T} sin(c·sinh u)du = 0 (odd integrand, exact).
#print axioms QIQTH.Fock.Localization.abs_integral_shifted_le
-- expected: standard only — the shifted-tail bound |∫_{R−φ}^{R+φ}| ≤ 3/(|c|·cosh(R−|φ|)).
#print axioms QIQTH.Fock.Localization.tendsto_inv_cosh_atTop
-- expected: standard only — (cosh ·)⁻¹ → 0 at +∞.
#print axioms QIQTH.Fock.Localization.pauliJordan_spacelike_tendsto_zero
-- expected: standard only — ★★★ THE SPACELIKE VANISHING OF Δ_m: for spacelike z,
-- lim_R ∫_{−R}^{R} sin(η(p_m θ,z))dθ = 0.  The heart of microcausality, pointwise, machine-checked:
-- reparametrization (odd kernel) + symmetric cancellation + the IBP keystone tail bound, squeezed to 0.
#print axioms QIQTH.Fock.Localization.reflect_integral_sin_sinh
-- expected: standard only — kernel reflection ∫_{−q}^{−p} sin(c·sinh) = −∫_p^q sin(c·sinh).
#print axioms QIQTH.Fock.Localization.abs_integral_sin_sinh_le_uniform
-- expected: standard only — ★ the UNIFORM bound |∫_a^b sin(c·sinh u)du| ≤ 6/|c| (all a,b): the dominating
-- function for the dominated-convergence step of the bilinear assembly (5c).
#print axioms QIQTH.Fock.Localization.exists_pos_lower_bound_slSq
-- expected: standard only — ★ the r₀>0 compactness bound: on compact spacelike-separated K,L the spacelike
-- interval (x−y)₁²−(x−y)₀² ≥ ε>0 uniformly (extreme value theorem) — the 2nd ingredient for 5c's DCT.
#print axioms QIQTH.Fock.Localization.symm_intervalIntegral_tendsto_integral
-- expected: standard only — the symmetric truncation limit ∫_{−R}^R G → ∫_ℝ G (integrable G) — reduces
-- the localized form to the R→∞ limit of finite-R truncations (5c ingredient).
#print axioms QIQTH.Fock.Localization.im_exp_mul_of_real
-- expected: standard only — Im(exp(iα)·w) = sin α · Re w when Im w = 0.
#print axioms QIQTH.Fock.Localization.abs_pauliJordan_trunc_le
-- expected: standard only — uniform-in-R bound |∫_{−R}^R sin(η(p_mθ,z))dθ| ≤ 6/(|m|√(z₁²−z₀²)) for
-- spacelike z (reparam c²=m²(z₁²−z₀²) + the uniform oscillatory bound) — the per-point DCT dominating bound.
#print axioms QIQTH.Fock.Localization.Kform_im_trunc_tendsto_zero
-- expected: standard only — ★★ part (d) of the bilinear assembly (5c): the DOMINATED-CONVERGENCE step.
-- ∫∫ (f x·g y).re·(∫_{−R}^R sin(η(p_mθ,x−y))dθ) → 0 for real compact-support spacelike-separated f,g.
-- DCT over V×V: dominating C·‖f‖‖g‖ (C=6/(|m|√ε), exists_pos_lower_bound_slSq), per-point bound
-- abs_pauliJordan_trunc_le, pointwise limit pauliJordan_spacelike_tendsto_zero.
#print axioms QIQTH.Fock.Localization.Kform_im_trunc_eq
-- expected: standard only — ★★ part (c) of the bilinear assembly (5c): the finite-R MIXED FUBINI.
-- ∫_{−R}^R Im(conj(K f θ)·K g θ)dθ = ½∫∫ (f x·g y).re·(∫_{−R}^R sin(η)) — interval×product-measure swap
-- (integral_integral_swap) valid at finite R (kernel bounded by integrable ‖f‖‖g‖ over the finite measure).
#print axioms QIQTH.Fock.Localization.Kform_eq_inner
-- expected: standard only — the interface bridge: ⟪K Lf, K Lg⟫_{L²} = Kform m Lf.f Lg.f (L2.inner_def +
-- toLp coercion + RCLike.inner_apply').  Connects the integral-level form to the Hilbert inner product.
#print axioms QIQTH.Fock.Localization.K_im_inner_eq_zero_of_spacelike
-- expected: standard only — ★ Im⟪K Lf, K Lg⟫_{L²}=0 for spacelike-separated real compact-support tests:
-- LITERALLY the SpacetimeLocalization.pauli_jordan hypothesis field, discharged for the concrete K.
#print axioms QIQTH.Fock.Localization.localized_typicality_boost_invariant
-- expected: standard only — ★★ BOOST-COVARIANCE of the localized typicality measure, RESOLVING the
-- orbit/spacelike tension: for a pairwise-spacelike (NOT boost-closed) localized family {K(region i)},
-- μ∞ for {K(region i)} = μ∞ for {U₁(a)·K(region i)} = μ∞ for {K(boost_a·region i)}. The measure depends
-- only on the Gram matrix (isometry-invariance, weylBit_typicality_boost_invariant) — no orbit needed.
#print axioms QIQTH.Fock.Localization.localized_hiso_of_spacelike
-- expected: standard only — a pairwise-spacelike regular region family gives microcausal localized modes.
#print axioms QIQTH.Fock.Localization.localized_microcausality_nonvacuous
-- expected: standard only — ★★★ NON-VACUITY WITNESS: two GENUINELY spacelike-separated localizable tests
-- (smooth compact-support real bumps at (0,±5)) have Im⟪K Lf, K Lg⟫=0 — a non-vacuous pauli_jordan instance
-- (NOT f=0). Every analytic hypothesis discharged: Krep∈L² (schwartz_Krep_memLp via toSchwartzMap), hKint
-- (Cauchy–Schwarz MemLp.integrable_mul), spacelike supports (bump boxes, (Δx)²≥36>16≥(Δt)²). Seals the prize.
#print axioms QIQTH.Fock.Localization.bumps_spacelike
-- expected: standard only — the two bump record regions at (0,±5) are genuinely spacelike-separated.
#print axioms QIQTH.Fock.Localization.K_boost_equivariant
-- expected: standard only — ★ K(boost_a·f)=U₁(a)(K f): Poincaré equivariance, the SECOND physics input
-- of the SpacetimeLocalization interface (K_equivariant), discharged for the concrete K. The Lorentz boost
-- of rapidity a is the L²(ℝ) translation isometry boostUnitary a (Lp.compMeasurePreservingₗᵢ ℂ (·+a)).
#print axioms QIQTH.Fock.Localization.Kform_im_eq_zero_of_spacelike
-- expected: standard only — ★★★ THE PAULI–JORDAN MICROCAUSALITY OF K: Im⟨Kf,Kg⟩=(Kform m f g).im=0 for
-- real continuous compact-support f,g with spacelike-separated supports (m≠0, hKint convergence).
-- The literal Einstein-causality / microcausality input the SpacetimeLocalization interface isolates,
-- now machine-checked. Im∘∫ + truncation + finite-R Fubini (Kform_im_trunc_eq) + DCT
-- (Kform_im_trunc_tendsto_zero) + uniqueness of limits.
#print axioms QIQTH.Fock.Localization.Krep_prod_im
-- expected: standard only — ★★ part (a) of the bilinear assembly (5c): the fixed-θ DOUBLE-INTEGRAL
-- representation Im(conj(K f θ)·K g θ) = ½∫∫ sin(η(p_mθ,x−y))·(f x·g y).re ∂(vol×vol), for real
-- (conj f=f, conj g=g) continuous compact-support tests. Exposes the Pauli–Jordan kernel sin(η).
-- Route: conj-real + integral_prod_mul (product=double integral) + integral_comp_comm (Im∘∫) + the
-- pointwise im_exp_mul_of_real.
#print axioms QIQTH.Fock.Localization.K_im_inner_eq_zero_smooth
-- expected: standard only — ★★ hKint-FREE top-level microcausality export: for smooth compact-support real
-- tests with spacelike supports, Im⟨K Lf, K Lg⟩=0. The hKint convergence hypothesis is DISCHARGED internally
-- (smooth_hKint via Cauchy–Schwarz on Schwartz L² amplitudes), so the statement has the exact intended scope
-- with no analytic side-condition for the caller.
#print axioms QIQTH.Fock.Localization.K_gaussian_ne_zero
-- expected: standard only — ★★ NON-TRIVIALITY of the localization: K(gaussianLocalTest)≠0. The amplitude
-- Krep m gaussianTest θ = 2^{−1/2}π·exp(−m²cosh(2θ)/4) is everywhere strictly positive (Continuous +
-- ae_eq_iff_eq vs everywhere-positive ⇒ not a.e. 0), so the localized Weyl-bit Born outcome is genuinely
-- non-deterministic, not the trivial 0 mode. Closes the "modes could be zero" honesty gap.

-- A1d: FULL CONNECTED-POINCARÉ covariance — translations (the second generator) + the combined group
#print axioms QIQTH.Fock.Localization.Krep_translate
-- expected: standard only — the amplitude-level translation multiplier: K(τ_b f)(θ)=e^{−iη(p_mθ,b)}·Kf(θ).
-- A change of variables (translation is volume-preserving) + additivity of the Minkowski pairing. The
-- θ-DEPENDENT but UNIMODULAR phase that makes translations act as an L²(ℝ,dθ) multiplication isometry.
#print axioms QIQTH.Fock.Localization.K_translate_equivariant
-- expected: standard only — ★ K(τ_b f)=M_b(K f): translation equivariance, the SECOND Poincaré generator.
-- M_b is the multiplication-by-e^{−iη(p_mθ,b)} isometry on L²(ℝ) (multiplierIsometry; isometry because the
-- phase has modulus 1, multiplier_inner). Counterpart of K_boost_equivariant (the boost generator).
#print axioms QIQTH.Fock.Localization.localized_typicality_translation_invariant
-- expected: standard only — ★★ TRANSLATION-covariance of the localized typicality measure μ∞: the measure
-- for {K(region i)} equals that for the translated family {M_b·K(region i)}={K(τ_b·region i)}. Same
-- Gram-matrix/isometry-invariance route as the boost case (multiplier is unitary, |phase|=1).
#print axioms QIQTH.Fock.Localization.K_poincare_equivariant
-- expected: standard only — ★★★ FULL connected-Poincaré equivariance: K(τ_b·β_a·f)=U(a,b)(K f) with
-- U(a,b)=M_b∘U₁(a). Boosts ∘ translations generate the connected Poincaré group of 1+1D Minkowski space.
#print axioms QIQTH.Fock.Localization.localized_typicality_poincare_invariant
-- expected: standard only — ★★★ THE FULL-POINCARÉ PRIZE: μ∞ is invariant under the WHOLE connected Poincaré
-- group (boost a + translation b, U(a,b)=M_b∘U₁(a)), for a pairwise-spacelike microcausal localized family.
-- Lorentz-covariant + translation-covariant + microcausal σ-additive typicality measure on the 1+1D free
-- field — the literal Open-Problem-3b deliverable, axiom-free.
#print axioms QIQTH.Fock.Localization.boostUnitary_comp_multiplier
-- expected: standard only — ★★ the nonabelian semidirect-product relation U₁(a)∘M_b=M_{Λ_{−a}b}∘U₁(a):
-- boosting commutes a translation past it into the boosted translation. The heart of the Poincaré group law.
#print axioms QIQTH.Fock.Localization.poincareIsometry_comp
-- expected: standard only — ★★★ THE CONNECTED-POINCARÉ GROUP LAW: U(a,b)∘U(a',b')=U(a+a', b+Λ_{−a}b'), the
-- semidirect-product composition of ℝ^{1,1}⋊SO⁺(1,1). With K_poincare_equivariant this makes (a,b)↦U(a,b) a
-- genuine REPRESENTATION of the connected Poincaré group — not merely a parameterized family of isometries.
-- Closes GPT-5.5-pro's last rigor item (group-homomorphism packaging). From the two subgroup laws +
-- the intertwining boostUnitary_comp_multiplier.

-- A2: Goldstein-Struyve Step 1 — concrete sub-lemma proofs
#print axioms QIQTH.GoldsteinStruyveStep1.permutation_conj_matrixUnit
-- expected: standard only — direct matrix-entry computation
#print axioms QIQTH.GoldsteinStruyveStep1.diagonalU_conj_matrixUnit
-- expected: standard only — diagonal-character conjugation identity
#print axioms QIQTH.GoldsteinStruyveStep1.step1c_collapse_of_perm_symmetric
-- expected: standard only — Equiv.swap transitivity argument
#print axioms QIQTH.GoldsteinStruyveStep1.permMatrix_unitary
-- expected: standard only
#print axioms QIQTH.GoldsteinStruyveStep1.diagonalU_unitary
-- expected: standard only
#print axioms QIQTH.GoldsteinStruyveStep1.phase_separation
-- expected: standard only — {1, I} marker diagonal, Complex.exp-free
#print axioms QIQTH.GoldsteinStruyveStep1.offdiag_support_of_unitary_equivariant
-- expected: standard only — diagonal-character support step (GS step 1b core)
#print axioms QIQTH.GoldsteinStruyveStep1.offdiag_eq_smul
-- expected: standard only
#print axioms QIQTH.GoldsteinStruyveStep1.diag_support_of_unitary_equivariant
-- expected: standard only — E_ii maps to a diagonal matrix
#print axioms QIQTH.GoldsteinStruyveStep1.coeff_perm_symmetric
-- expected: standard only — permutation symmetry of D(E_ij) i j
#print axioms QIQTH.GoldsteinStruyveStep1.coeff_collapse
-- expected: standard only — off-diagonal/diagonal coefficients each collapse to one scalar
#print axioms QIQTH.GoldsteinStruyveStep1.diag_coeff_perm_symmetric
-- expected: standard only
#print axioms QIQTH.GoldsteinStruyveStep1.diag_coeff_collapse
-- expected: standard only — D(E_ii) diagonal entries collapse to c_diag (at i,i) and c_rest
#print axioms QIQTH.GoldsteinStruyveStep1.hadamardU_mul_self
-- expected: standard only — H·H = 1 (2s²=1 normalization)
#print axioms QIQTH.GoldsteinStruyveStep1.hadamardU_conj_Eaa
-- expected: standard only — H·E_aa·H* = ½(E_aa+E_ab+E_ba+E_bb)
#print axioms QIQTH.GoldsteinStruyveStep1.hadamardU_conj_entry_ab
-- expected: standard only — general (a,b)-entry of H·M·H*
#print axioms QIQTH.GoldsteinStruyveStep1.hadamard_relation
-- expected: standard only — c_off = c_diag − c_rest (Hadamard step 1d)

-- A4: Chebyshev concentration
#print axioms QIQTH.BornConcentration.chebyshev_finite
-- expected: standard only — finite sum manipulation
#print axioms QIQTH.BornConcentration.chebyshev_tail_bound
-- expected: standard only
#print axioms QIQTH.BornConcentration.bernoulli_variance
-- expected: standard only — single sum + ring identity
#print axioms QIQTH.BornConcentration.born_chebyshev_single_trial
-- expected: standard only
#print axioms QIQTH.BornConcentration.centered_first_moment_zero
-- expected: standard only — centered first moment vanishes
#print axioms QIQTH.BornConcentration.variance_add_of_product
-- expected: standard only — variance adds for independent variables
#print axioms QIQTH.BornConcentration.two_trial_bernoulli_variance
-- expected: standard only — 2·p(1−p) via variance-addition

-- A6: minimality / independence package
#print axioms QIQTH.BornMinimalityTable.P1_canonical_measure_necessary
-- expected: standard only (re-export of NoBornFromNothing)
#print axioms QIQTH.BornMinimalityTable.P2_measure_equivariance_necessary
-- expected: standard only (re-export of EquivarianceGap)
#print axioms QIQTH.BornMinimalityTable.P3_operational_sufficiency_necessary
-- expected: standard only (re-export of OperationalNoGo)
#print axioms QIQTH.BornMinimalityTable.P4_locality_reducible_to_equivariance
-- expected: standard only (re-export of MarginalLocality)

-- Open Problem 3b: Lorentz-covariance discrete skeleton
#print axioms QIQTH.LorentzSelection.bulk_overlap_agreement
-- expected: NO axioms at all (pure rewrite by GlobalSection.consistent)
#print axioms QIQTH.LorentzSelection.evaluation_covariance
-- expected: standard axioms ONLY (propext, Quot.sound).  CRUCIALLY *not* any
-- of the (now-RETIRED) 4 deferred AQFT axioms, AND no longer
-- `actSection_consistent` (eliminated by the OrderIso upgrade — proved theorem).
#print axioms QIQTH.LorentzSelection.actSection_consistent
-- expected: standard only — the pushed-forward section's consistency, PROVED
-- (was an axiom; now a theorem via act : ≃o and restrict_cast).
-- DISCHARGE PASS: the four opaque `axiom _ : Prop` AQFT placeholders
-- (record_presheaf_exists, boundary_reconstruction,
-- decoherence_functional_measure, screen_local_marginal) have been RETIRED and
-- replaced by the explicit `RecordedHistoryNet` structure + conditional
-- theorems.  The module now adds ZERO project axioms; the open content is the
-- single written-down existence question, not an assumed axiom.
#print axioms QIQTH.LorentzSelection.net_no_signaling
-- expected: standard only — no-signaling is now a THEOREM about any net.
#print axioms QIQTH.LorentzSelection.covariant_selection_of_net
-- expected: standard only — covariance over the full (hypothesized) net.
#print axioms QIQTH.LorentzSelection.covariant_selection_exists
-- expected: standard only — IF a net exists, a covariant selector exists.

-- STRENGTHENED Lorentz layer (GPT-5.5-pro A–G): makes the conditional interface
-- RIGID (externalized geometry) and CONNECTED (Born link), with theorems that
-- genuinely CONSUME the analytic fields.  All standard axioms only; ZERO project
-- axioms.
#print axioms QIQTH.LorentzSelectionStrong.card_le_of_le
-- expected: standard only — holographic bound propagates (uses N_mono).
#print axioms QIQTH.LorentzSelectionStrong.reconSection
-- expected: standard only — screen-encoded history is a consistent boundary
-- section (uses recon_nat).
#print axioms QIQTH.LorentzSelectionStrong.group_evaluation_covariance
-- expected: standard only — covariance for EVERY group element.
#print axioms QIQTH.LorentzSelectionStrong.act_mul_diam
-- expected: standard only — group composition law on diamonds (uses act_mul).
#print axioms QIQTH.LorentzSelectionStrong.measure_pushforward_total
-- expected: standard only — g-covariant weight ⇒ g-invariant total mass
-- (CONSUMES the covariance hypothesis, unlike covariant_selection_of_net).
#print axioms QIQTH.LorentzSelectionStrong.bornω_sum_one
-- expected: standard only — NORMALIZATION DERIVED from the Born functional
-- (born_sum/born_one), tying the Lorentz strand to the axiom-free Gleason strand.
#print axioms QIQTH.LorentzSelectionStrong.bornωRe_sum_one
-- expected: standard only — real probability normalization derived.
-- Second strengthening pass (γ-cocycle + per-cell measure + PVM positivity):
#print axioms QIQTH.LorentzSelectionStrong.γ_cocycle_apply
-- expected: standard only — pointwise group cocycle on fibres (CONSUMES IsRepMul).
#print axioms QIQTH.LorentzSelectionStrong.measure_pushforward_cell
-- expected: standard only — per-cell (not just total) measure covariance.
#print axioms QIQTH.LorentzSelectionStrong.born_posSemidef_nonneg
-- expected: standard only — ⟨ψ|E|ψ⟩ ≥ 0 for PSD E (matrix-adjoint positivity).
#print axioms QIQTH.LorentzSelectionStrong.pvm_bornωRe_nonneg
-- expected: standard only — PVM Born weights are nonnegative.
#print axioms QIQTH.LorentzSelectionStrong.pvm_isProbability
-- expected: standard only — PVM weights are a genuine probability distribution
-- (nonneg ∧ sum = 1) — closes the affine-vs-probability gap.
-- Third pass: measure covariance DERIVED from unitarity (hcov now a theorem).
#print axioms QIQTH.LorentzSelectionStrong.born_unitary_invariant
-- expected: standard only — UNCONDITIONAL: ⟨Uψ|U E Uᴴ|Uψ⟩ = ⟨ψ|E|ψ⟩.
#print axioms QIQTH.LorentzSelectionStrong.ubornω_covariant
-- expected: standard only — measure covariance DERIVED from unitary transport
-- (the previously-assumed hcov is now a consequence).
#print axioms QIQTH.LorentzSelectionStrong.ubornω_pushforward_cell
-- expected: standard only — per-cell pushforward, now unconditional on hcov.
#print axioms QIQTH.LorentzSelectionStrong.ubornω_total_invariant
-- expected: standard only — total-mass invariance, now unconditional on hcov.
-- Fourth pass: γ-cocycle on the selection + unified covariant probability data.
#print axioms QIQTH.LorentzSelectionStrong.selection_cocycle
-- expected: standard only — selection transports as a cocycle (γ_{g₁g₂} via the
-- once-pushed section); consumes IsRepMul + group_evaluation_covariance.
#print axioms QIQTH.LorentzSelectionStrong.upvm_covariant_probability
-- expected: standard only — uniform PVM weights are a COVARIANT probability
-- distribution (nonneg ∧ sum=1 ∧ ω_{gD}(γx)=ω_D(x)); fuses positivity +
-- unitary covariance in one object.
-- Fifth pass: PVM coherence under transport + section eval API.
#print axioms QIQTH.LorentzSelection.actSection_val
-- expected: NO axioms — public spec of actSection (unblocks the section-object
-- group-action law; actVal is private).
#print axioms QIQTH.LorentzSelectionStrong.E_cov_preserves_proj
-- expected: standard only — boosted effects stay a PVM (coherence as a theorem;
-- the UnitaryCovariance + UniformPVMData structure is not over-determined).
#print axioms QIQTH.LorentzSelectionStrong.covariantProbability_of_unitaryPVM
-- expected: standard only — packaged covariant probability distribution.
-- Sixth pass: the SECTION-OBJECT group-action law + full-PVM preservation.
#print axioms QIQTH.LorentzSelectionStrong.actSection_one
-- expected: standard only — identity law 1·λ = λ (section-object level).
#print axioms QIQTH.LorentzSelectionStrong.actSection_mul
-- expected: standard only — composition law (g₁g₂)·λ = g₂·(g₁·λ); actSection is
-- a genuine G-action on Γ(X) (the section-object law, no longer just the
-- selector-level shadow selection_cocycle).
#print axioms QIQTH.LorentzSelectionStrong.unitary_preserves_resolution
-- expected: standard only — U preserves ∑E=1 (boosted effects are a full PVM).
-- CONCRETE NON-TRIVIAL MODEL (refutes "only the one-point net satisfies it"):
#print axioms QIQTH.LorentzWitness.witness_covariantProbability
-- expected: standard only — a concrete CovariantProbability instance exists.
#print axioms QIQTH.LorentzWitness.witness_nondegenerate
-- expected: standard only — its Born weights are 9/25, 16/25 ∈ (0,1): a genuine
-- spread 2-outcome distribution, not a point mass / one-point fibre.
-- Witness B: a NON-trivial group acting non-trivially on the diamond geometry.
#print axioms QIQTH.LorentzWitness.witness2_action_nontrivial
-- expected: standard only — the swap moves diamond d0 to d1 (non-trivial orbit).
#print axioms QIQTH.LorentzWitness.witness2_covariantProbability
-- expected: standard only — covariant probability over a non-trivial group orbit
-- (exercises the covariance machinery, not just the probability content).

-- PRIZE STAGE 1: non-toy recorded-history net with product-Born no-signaling.
#print axioms QIQTH.FreeFieldNet.bornNet
-- expected: standard only — non-toy net (genuine marginalizing restriction, product Born ω)
#print axioms QIQTH.FreeFieldNet.bornNet_no_signaling
-- expected: standard only — no-signaling marginal DERIVED from the product Born measure
#print axioms QIQTH.FreeFieldNet.bornNet_covariant_selection
-- expected: standard only — covariant single-outcome selector over the non-toy net
#print axioms QIQTH.BornTypicalityFinite.w_perm_invariant
-- expected: standard only — permutation-equivariance of the product Born typicality measure
#print axioms QIQTH.FreeFieldNet.Dω_swap_invariant
-- expected: standard only — mode-swap equivariance of the net's product Born measure
#print axioms QIQTH.QubitIC.qubitIC_sum
-- expected: standard only — the four qubit record effects are a POVM (∑ = 1)
#print axioms QIQTH.QubitIC.qubitIC_separating
-- expected: standard only — RECORD-COMPLETENESS: four record traces separate density matrices (IC)
#print axioms QIQTH.QubitIC.qubitIC_records_imply_all_effects
-- expected: standard only — record statistics determine all effect statistics (bridge to Gleason)
#print axioms QIQTH.DiamondSwapNet.swapIso
-- expected: standard only — left↔right swap is a genuine non-trivial diamond order-isomorphism
#print axioms QIQTH.DiamondSwapNet.swap_covariant_selection
-- expected: standard only — covariant selector over the diamond-permuting orbit (non-trivial action)
#print axioms QIQTH.DiamondSwapNet.diamondBornNet
-- expected: standard only — UNIFIED net: product Born ω + both no-signaling marginals + swap action
#print axioms QIQTH.DiamondSwapNet.diamond_unified
-- expected: standard only — Stage-1 capstone: net+section+action exist AND covariant over the orbit

-- PRIZE STAGE 2: global-section existence + classification (gluing unobstructed, finite case).
#print axioms QIQTH.SheafSection.topSection
-- expected: standard only — every top record extends to a global section (gluing unobstructed)
#print axioms QIQTH.SheafSection.globalSection_eq_top
-- expected: standard only — every global section is determined by its top value (classification)
#print axioms QIQTH.SheafSection.diamondSelector_classifies
-- expected: standard only — selectors over the diamond net = joint records (cohomology trivial)

-- Infrastructure finite-discharge pass (Open Problems 6 & 9): the finite-
-- classical axioms are now PROVED, not assumed.
#print axioms QIQTH.RelEntPositivity.KL_classical_nonneg
-- expected: standard only — Gibbs' inequality (finite relative-entropy ≥ 0).
#print axioms QIQTH.ShannonFano.H_bound_imp_max_lb
-- expected: standard only — Rényi-∞ ≤ Shannon (the Fano-step bound, OP6).
#print axioms QIQTH.ShannonFano.H_zero_imp_dirac
-- expected: standard only — zero entropy ⇒ a Dirac record.

-- Tomita–Takesaki roadmap, Phase 1: PVM / spectral-theorem keystone scaffold.
-- (Projection-valued CONTENT lemmas; the genuine `ProjectionValuedMeasure`
-- adds strong-operator σ-additivity — its scalar-measure theorem T1 is the next
-- target. Revised after GPT-5.5-pro consultation.)
#print axioms QIQTH.Spectral.PVContent.inner_E_self
-- expected: standard only — ⟪x, E s x⟫ = ‖E s x‖² (projection diagonal identity).
#print axioms QIQTH.Spectral.PVContent.E_compl
-- expected: standard only — E sᶜ = 1 - E s.
#print axioms QIQTH.Spectral.PVContent.mu_univ
-- expected: standard only — scalar set-function total mass ‖x‖².
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.scalarMeasure_univ
-- expected: standard only — Phase-1 target T1 PROVED: the scalar spectral
-- measure is a genuine MeasureTheory.Measure of total mass ‖x‖² (from strong-
-- operator σ-additivity via the bounded functional ⟪x,·⟫).
-- Phase-1 target T2 (bounded-Borel FC), homomorphism core on simple functions:
#print axioms QIQTH.Spectral.PVContent.integralSimple_mul
-- expected: standard only — FC multiplicativity ∫f·∫g=∫(fg) on a disjoint family.
#print axioms QIQTH.Spectral.PVContent.integralSimple_adjoint
-- expected: standard only — FC adjoint law ∫f̄ = (∫f)†.
#print axioms QIQTH.Spectral.PVContent.integralSimple_star_mul_self
-- expected: standard only — (∫f)⋆(∫f) = ∫|f|² (positive T⋆T); step toward ‖·‖ bound.
#print axioms QIQTH.Spectral.PVContent.sum_E_biUnion
-- expected: standard only — ∑ᵢ E sᵢ = E(⋃ᵢ sᵢ) (finite additivity over a Finset).
#print axioms QIQTH.Spectral.PVContent.integralSimple_one
-- expected: standard only — ∫1 dE = 1 over a covering partition (FC unitality).
#print axioms QIQTH.Spectral.PVContent.E_nonneg
-- expected: standard only — 0 ≤ E s (self-adjoint idempotent is positive, Loewner).
#print axioms QIQTH.Spectral.PVContent.E_le_one
-- expected: standard only — E s ≤ 1 (subprojection of identity; 1-E s = E sᶜ ≥ 0).
#print axioms QIQTH.Spectral.PVContent.norm_sum_sq_of_orthogonal
-- expected: standard only — finite Pythagoras ‖∑gᵢ‖²=∑‖gᵢ‖² for orthogonal families.
#print axioms QIQTH.Spectral.PVContent.norm_E_apply_le
-- expected: standard only — projections are contractions (‖E s x‖ ≤ ‖x‖).
#print axioms QIQTH.Spectral.PVContent.integralSimple_opNorm_le
-- expected: standard only — the C*-NORM BOUND ‖∫f dE‖ ≤ ‖f‖∞ for the simple FC.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.inner_integralSimple_left
-- expected: standard only — sesquilinear form ⟪x,(∫f)y⟫ = ∑ᵢ cᵢ⟪x,E sᵢ y⟫.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.re_inner_integralSimple_self
-- expected: standard only — diagonal real form Re⟪x,(∫f)x⟫ = ∑ᵢ aᵢ‖E sᵢ x‖².
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.lintegral_indicatorSum_eq
-- expected: standard only — ∫⁻(∑aᵢ𝟙_{sᵢ}) dμ_x = ofReal(∑aᵢ‖E sᵢ x‖²).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.re_inner_integralSimple_eq_lintegral
-- expected: standard only — T2 BRIDGE ⟪x,(∫f dE)x⟫ = ∫ f dμ_x (genuine measure).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.inner_E_polarization
-- expected: standard only — sesquilinear polarization ⟪x,E s y⟫ via diagonal forms.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.inner_E_eq_polarization_measures
-- expected: standard only — μ_{x,y}(s) = ¼-combo of the four genuine measures μ_z.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.inner_integralSimple_eq_polarization
-- expected: standard only — simple sesquilinear form via genuine scalar measures.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.scalarMeasure_toReal
-- expected: standard only — (μ_x s).toReal = ‖E s x‖².
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.scalarMeasure_toReal_parallelogram
-- expected: standard only — parallelogram identity (seed of sesquilinearity, T2 ext).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.scalarMeasure_smul
-- expected: standard only — μ_{c·x} = ‖c‖²·μ_x (scaling at the measure level).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.scalarMeasure_parallelogram_measure
-- expected: standard only — μ_{x+y}+μ_{x−y} = 2μ_x+2μ_y (measure-level parallelogram).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.diagInt_smul
-- expected: standard only — E2a homogeneity D_f(c·x) = ‖c‖² D_f(x).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.diagInt_parallelogram
-- expected: standard only — E2a parallelogram D_f(x+y)+D_f(x−y)=2D_f(x)+2D_f(y).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_add_left
-- expected: standard only — E2b Jordan–von Neumann core: B_f additive in first slot.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_conj_symm
-- expected: standard only — E2b conjugate-symmetry conj(B_f(y,x)) = B_{f̄}(x,y).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_add_right
-- expected: standard only — E2b additivity in the second slot.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_I_smul_left
-- expected: standard only — E2b i-scaling B_f(i·x,y) = conj(i)·B_f(x,y).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.scalarMeasure_odd_measure
-- expected: standard only — odd measure identity (continuity-free real-homogeneity key).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.diagInt_odd
-- expected: standard only — D_f(r·x+y)−D_f(r·x−y) = r(D_f(x+y)−D_f(x−y)).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_real_smul_left
-- expected: standard only — E2b real homogeneity B_f(r·x,y) = r·B_f(x,y).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_smul_left
-- expected: standard only — E2b FULL conj-linearity B_f(c·x,y) = conj(c)·B_f(x,y).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_smul_right
-- expected: standard only — E2b linearity in second slot B_f(x,c·y) = c·B_f(x,y).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.diagInt_norm_le
-- expected: standard only — E2c diagonal bound ‖D_f x‖ ≤ C‖x‖².
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_norm_le
-- expected: standard only — E2c product bound ‖B_f(x,y)‖ ≤ 2C‖x‖‖y‖.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.inner_intBorel
-- expected: standard only — ⋆ THE BOUNDED-BOREL FC ∫f dE: ⟪(∫f dE)x,y⟫ = B_f(x,y).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.intBorel_norm_le
-- expected: standard only — operator norm bound ‖∫f dE‖ ≤ 2C.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_const
-- expected: standard only — B_(const c)(x,y) = c⟪x,y⟫ (polarization of ‖·‖²).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.intBorel_const
-- expected: standard only — orientation: intBorel(const c) = conj(c)•1 (the Riesz op is conjugated).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_const
-- expected: standard only — oriented FC is unital: boundedFC(const c) = c•1, so Φ(1)=1.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.diagInt_indicator_eq_inner
-- expected: standard only — diagonal of the indicator's form is ⟪z, E s z⟫ (= μ_z(s)).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_indicator
-- expected: standard only — indicator bridge (polarized): B_{𝟙_s}(x,y) = ⟪x, E s y⟫.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_indicator
-- expected: standard only — THE bounded-Borel FC of an indicator is the spectral
-- projection: Φ(𝟙_s) = E s.  Anchors the abstract Borel FC to its PVM (Phase 1.1).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_indicator_mul
-- expected: standard only — multiplicativity of the FC on indicators: Φ(𝟙_{s∩t}) = E s·E t
-- (the projection *-relation; Φ(f·g)=Φ(f)·Φ(g) on the generating subalgebra).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.tendsto_diagInt_of_dominated
-- expected: standard only — DCT for the diagonal functional D_f against finite μ_z.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.tendsto_inner_boundedFC_of_dominated
-- expected: standard only — bounded-convergence (WOT "normality") continuity of the FC:
-- fₙ→f ptwise bounded ⟹ ⟪x,Φ(fₙ)y⟫→⟪x,Φ(f)y⟫.  Engine for simple→bounded-Borel extension.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_norm_le
-- expected: standard only — ‖Φ(f)‖ ≤ 2‖f‖∞ (Φ = adjoint of Riesz op intBorel, an isometry);
-- the operator-norm estimate enabling the simple→bounded-Borel extension toward Φ(fg)=Φ(f)Φ(g).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_add
-- expected: standard only — additivity of the bounded-Borel FC in f: Φ(f+g)=Φ(f)+Φ(g).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_smul
-- expected: standard only — ℂ-homogeneity of the bounded-Borel FC in f: Φ(c·f)=c·Φ(f).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.diagInt_finsetSum
-- expected: standard only — D_{∑Fᵢ}=∑D_{Fᵢ} (bound-free finset linearity of the diagonal functional).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_finsetSum
-- expected: standard only — B_{∑Fᵢ}=∑B_{Fᵢ} (finset linearity of the polarized form).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_eq_integralSimple
-- expected: standard only — Φ(∑cᵢ𝟙_{sᵢ}) = ∑cᵢ E sᵢ = integralSimple: the Riesz-form FC
-- equals the constructive simple spectral integral on simple functions.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.integralSimple_mul_eq
-- expected: standard only — (∑aᵢ E Aᵢ)(∑bⱼ E Bⱼ) = ∑ᵢⱼ aᵢbⱼ E(Aᵢ∩Bⱼ): operator
-- multiplicativity core for simple functions (cross terms collapse by E_inter).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_congr
-- expected: standard only — Φ(f) depends only on f (value = B_f), not on the bound proof.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.integralSimple_product_eq
-- expected: standard only — integralSimple over t×ˢs = product of the two (sum_product).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_simple_mul
-- expected: standard only — MULTIPLICATIVITY ON SIMPLE FUNCTIONS: Φ((∑aᵢ𝟙_{Aᵢ})(∑bⱼ𝟙_{Bⱼ}))
-- = (∑aᵢ E Aᵢ)(∑bⱼ E Bⱼ).  The base case for the bounded-Borel multiplicativity capstone.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.simpleFunc_eq_sum
-- expected: standard only — φ a = ∑_{y∈φ.range} y·𝟙_{φ⁻¹{y}}(a): the bridge from Mathlib's
-- SimpleFunc (approxOn output) to the ∑cᵢ𝟙 form, for the bounded-Borel extension.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_simpleFunc
-- expected: standard only — Φ(⇑φ) = ∑_{y∈φ.range} y·E(φ⁻¹{y}) for a SimpleFunc φ.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_simpleFunc_mul
-- expected: standard only — Φ(⇑φ·⇑ψ)=Φ(⇑φ)·Φ(⇑ψ) for SimpleFuncs (multiplicativity, SimpleFunc form).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.tendsto_bilinDiag_of_dominated
-- expected: standard only — bound-free normality: B_{fₙ}→B_f under bounded ptwise convergence.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_mul_simpleFunc_left
-- expected: standard only — Stage 1: Φ(⇑φ·g)=Φ(⇑φ)·Φ(g) (SimpleFunc φ, bounded Borel g).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_mul
-- expected: standard only — ★ KEYSTONE: Φ(f·g)=Φ(f)·Φ(g) for ALL bounded measurable f,g.
-- The bounded-Borel functional calculus is a multiplicative (hence unital *-algebra) hom.
-- Closes Phase 1's multiplicativity; the analytic core unblocking PVM_of_selfAdjoint & Δ^it.

-- Stone M1 (the unbounded FC ∫f dE on a PVM): the DOMAIN D(∫f dE)={x:∫f²dμ_x<∞} as a ℂ-submodule.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.scalarMeasure_zero
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcEnergy_smul
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcEnergy_add_le
-- expected: standard only — energy ∫f²dμ_x is ‖c‖²-homogeneous + sub-additive (parallelogram μ_{x+y}≤2μ_x+2μ_y);
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcDomain
-- so the finite-energy set is a ℂ-submodule — the natural domain of the unbounded self-adjoint operator K=∫f dE.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.mem_fcDomain_of_bounded
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcDomain_eq_top_of_bounded
-- bounded symbol ⟹ full domain (∫f²dμ_x ≤ C²‖x‖²) — the bridge to boundedFC; K is unbounded only via log.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.mem_fcDomain_iff_integrable_sq
-- the FC domain IS the L²(μ_x) condition: x∈D(∫f dE) ↔ f square-integrable vs μ_x — opens L²/Cauchy-Schwarz
-- for the operator construction (Riesz rep of y ↦ ∫ f dμ_{x,y}).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.integrable_of_mem_fcDomain
-- on the domain f∈L¹(μ_x) (L²⊆L¹, μ_x finite) — the diagonal expectation ⟨x,(∫f dE)x⟩=∫f dμ_x converges.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_isSelfAdjoint
-- real symbol (f̄=f) ⟹ boundedFC f self-adjoint (via bilinDiag_conj_symm) — the symmetry seed for K and
-- half the norm identity ‖boundedFC g x‖²=∫|g|²dμ_x of the truncation route to the operator ∫f dE.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcTrunc_lintegral_sub_sq_tendsto
-- on the domain the bounded truncations fₙ=f·𝟙_{|f|≤n} converge to f in L²(μ_x): ∫|f−fₙ|²dμ_x→0 (dominated
-- convergence, dominated by f²∈L¹) — the L²-Cauchy engine making boundedFC(fₙ)x Cauchy (→ the operator).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_adjoint
-- (boundedFC g)† = boundedFC(conj∘g) — the bounded FC is a *-hom; with boundedFC_mul gives the norm
-- identity ‖boundedFC g x‖²=∫|g|²dμ_x.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag_self
-- the polarized form's diagonal is the original functional: B_g(x,x)=∫g dμ_x (= the diagonal expectation
-- ⟨x,(∫g dE)x⟩) — the last substrate piece for the norm identity.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.inner_boundedFC_self
-- the diagonal expectation ⟨x,(∫h dE)x⟩ = ∫ h dμ_x (the JLMS first-law ⟨K⟩ at the bounded level).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_adjoint_mul_self
-- T†T = boundedFC(ḡ·g) for T=boundedFC g (the *-algebra hom: adjoint + mul); diagonal gives ‖Tx‖²=∫|g|²dμ_x.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.norm_boundedFC_sq
-- ★ THE NORM IDENTITY ‖boundedFC g x‖² = ∫|g|²dμ_x — converts the truncation L²-convergence into
-- operator-image Cauchy-ness, defining the unbounded operator ∫f dE as the strong limit lim boundedFC(fₙ)x.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_sub
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.norm_boundedFC_sub_sq
-- boundedFC symbol-subtractive + the difference-norm ‖boundedFC g₁ x − boundedFC g₂ x‖²=∫|g₁−g₂|²dμ_x
-- (the concrete Cauchy bound for boundedFC(fₙ)x).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcTrunc_diff_sq_le
-- the Cauchy integrand bound (fₘ−fₙ)² ≤ 2(f−fₘ)²+2(f−fₙ)² — truncation L²-convergence controls the diff-norm.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcTrunc_integral_sub_sq_tendsto
-- Bochner form ∫|f−fₙ|²dμ_x → 0 (from the lintegral version via ∫g=(∫⁻ofReal g).toReal + toReal continuity).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcTrunc_diff_lintegral_le
-- the Cauchy bound at the ℝ≥0∞ level: ∫⁻ofReal((fₘ−fₙ)²) ≤ 2∫⁻ofReal((f−fₘ)²)+2∫⁻ofReal((f−fₙ)²) —
-- sidesteps the Bochner Integrable whnf blowup (lintegral over scalarMeasure elaborates cleanly).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcSeq_norm_sub_sq
-- the operator sequence fcSeq n x := boundedFC(fₙ)x; its diff-norm as a lintegral:
-- ‖fcSeq m x − fcSeq n x‖² = (∫⁻ ofReal((fₘ−fₙ)²) dμ_x).toReal — bridges to the ℝ≥0∞ Cauchy bound.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcSeq_norm_sub_sq_le
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcSeq_cauchySeq
-- ★ the approximating sequence boundedFC(fₙ)x is CAUCHY on the domain (‖fcSeq m x−fcSeq n x‖²≤2A_m+2A_n,
-- A_k→0) — so its strong limit exists (H complete): the unbounded operator (∫f dE)x.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcSeq_tendsto_fcOp
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcOp_add
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcOp_smul
-- ★ THE UNBOUNDED OPERATOR ∫f dE: fcOp hf x := limUnder (boundedFC(fₙ)x); boundedFC(fₙ)x→fcOp x on the
-- domain (fcSeq_tendsto_fcOp); additive (fcOp_add) and ℂ-homogeneous (fcOp_smul) — a linear operator on D(∫f dE).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcOp_neg
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_neg
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcTrunc_neg
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcEnergy_neg
-- ★ SYMBOL-LINEARITY completion: ∫(−f)dE = −∫f dE (fcOp_neg, via fcTrunc_neg + boundedFC_neg + fcEnergy_neg) —
-- the unbounded FC ∫·dE is linear in the integrand (add/smul/neg), Mathlib-quality completeness.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcOp_symmetric
-- ★ the operator is SYMMETRIC on the domain: ⟨(∫f dE)x, y⟩ = ⟨x, (∫f dE)y⟩ (f real ⟹ boundedFC(fₙ)
-- self-adjoint; pass to the limit by inner-product continuity) — the modular Hamiltonian's reality/symmetry.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcOp_eq_boundedFC
-- bounded-symbol compat: (∫f dE)x = boundedFC(↑f)x for bounded f — ties the unbounded FC to boundedFC
-- (so Δ^{it}=boundedFC(...) and its generator K=∫log(r/(2−r))dE_R share the same calculus). M1 COMPLETE.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_expSymbol_add
-- the FC-exponential group law: boundedFC(e^{i(s+t)f}) = boundedFC(e^{isf})·boundedFC(e^{itf}) (boundedFC_mul
-- + exp_add) — the bounded-operator content of exp(itK) being a one-parameter group (K=∫f dE), abstract PVM.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_expSymbol_adjoint_mul
-- FC-exponential UNITARITY: boundedFC(e^{itf})†·boundedFC(e^{itf}) = 1 (|e^{itf}|²=1 via boundedFC_adjoint_mul_self).
-- With the group law: exp(itK) is a one-parameter UNITARY group — full bounded content of Δ^{it}=e^{−itK}.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.boundedFC_expSymbol_zero
-- the group identity boundedFC(e^{i·0·f}) = 1 — completes the group axioms (id + compose + inverse) of exp(itK).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.expSymbol_sub_one_norm_sq
-- ★ STONE foundation: ‖boundedFC(e^{itf})x − x‖² = ∫|e^{itf}−1|²dμ_x — the flow's deviation from 1 is the L²
-- norm of the symbol's deviation; foundation for strong continuity (t→0) and the generator (d/dt|₀ = i·K).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_sub_one_le
-- ★ STONE domination: ‖e^{itf ω}−1‖ ≤ |t|·|f ω| (Real.norm_exp_I_mul_ofReal_sub_one_le) — so ‖(e^{itf}−1)/t‖
-- ≤ |f ω|, the uniform L² bound for the generator's difference-quotient convergence (e^{itf}−1)/t → if.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.hasDerivAt_expSymbol
-- ★ STONE ptwise derivative: d/dt e^{itc}|₀ = i·c — the pointwise input ((e^{itf}−1)/t → if) for the generator.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.expSymbol_slope_tendsto
-- ★ STONE slope: (e^{itc}−1)/t → ic as t→0 (𝓝[≠]0, via hasDerivAt_iff_tendsto_slope) — ptwise difference
-- quotient in the form the L² dominated-convergence step consumes.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.norm_expSymbol_sub_one_div_le
-- ★ STONE L²-domination: ‖(e^{itf ω}−1)/t‖ ≤ |f ω| for ALL t (incl t=0, z/0=0) — the uniform DCT bound.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.expSymbol_diffQuotient_lintegral_tendsto
-- ★★ STONE ANALYTIC HEART: ∫‖(e^{itf}−1)/t − if‖²dμ_x → 0 as t→0 — the L² convergence of the difference
-- quotient (sequential lintegral DCT, dodging the Bochner-over-scalarMeasure whnf wall; dominated by 4f²,
-- ptwise→0 from expSymbol_slope_tendsto). The genuine multi-fire core for Δ^{it}=e^{−itK} (M2) + abstract Stone (M4).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.complexSymbol_fcTrunc_lintegral_tendsto
-- ★ STONE operator-assembly step 1: ∫‖h − i·↑fcTrunc_m‖²dμ_x → ∫‖h − i·↑f‖²dμ_x (bounded symbol h) — the m→∞
-- truncation half of the distance identity ‖boundedFC(h)x − i·fcOp x‖² = ∫‖h−if‖² that makes the generator mechanical.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.dist_boundedFC_smul_fcOp_sq
-- ★★ STONE operator-assembly step 2 (CRUX): ‖boundedFC(h)x − i·(∫f dE)x‖² = ∫‖h − i·↑f‖²dμ_x (bounded symbol h) —
-- the operator distance to i·fcOp x EQUALS the L² symbol distance to i·f. Collapses the generator double-limit to a
-- single limit (limit-uniqueness: i·fcSeq→i·fcOp + norm_boundedFC_sub_sq + complexSymbol_fcTrunc_lintegral_tendsto).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.hasDerivAt_boundedFC_expSymbol
-- ★★★ STONE GENERATOR (M2/M4 CAPSTONE): d/dt(boundedFC(e^{itf})x)|₀ = i·(∫f dE)x — the strongly-continuous
-- one-parameter unitary group t↦boundedFC(e^{itf}) has generator i·K (K=∫f dE). The OPERATOR Δ^{it}=e^{−itK}.
-- Assembled axiom-free from the analytic heart + the distance identity: ‖slope−i·fcOp x‖²=(∫⁻‖(e^{itf}−1)/t−if‖²).toReal→0.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.continuousAt_boundedFC_expSymbol
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.continuousAt_boundedFC_expSymbol'
-- ★★ STRONG CONTINUITY of the FC-exponential group (the Stone hypothesis): t↦boundedFC(e^{itf})x continuous at 0
-- (free from the HasDerivAt capstone — differentiable⟹continuous) AND at every t₀ (group law U_{t₀+s}=U_{t₀}U_s).
-- Resolves the strong-continuity step the earlier Bochner-DCT route could not (the whnf wall); lintegral route delivers it.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.norm_boundedFC_expSymbol
-- ★ UNITARITY (norm-preservation) of the FC-exponential group: ‖boundedFC(e^{itf})x‖=‖x‖, from U⋆U=1
-- (boundedFC_expSymbol_adjoint_mul). Completes the unitary one-parameter group at the norm level.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.continuous_boundedFC_expSymbol
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.hasDerivAt_boundedFC_expSymbol'
-- ★ FLOW IS C¹ EVERYWHERE: t↦boundedFC(e^{itf})x is Continuous (continuous_boundedFC_expSymbol) AND differentiable
-- at every t₀ with d/dt|_{t₀} = U_{t₀}(i·∫f dE x) (hasDerivAt_boundedFC_expSymbol', via group law + comp_sub_const +
-- clm comp) — upgrades the generator from t=0 to the whole line: U_t' = i·U_t·K.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.hasDerivAt_inner_boundedFC_expSymbol
-- ★ INFINITESIMAL matrix element: d/dt⟪η,boundedFC(e^{itf})x⟫|₀ = ⟪η,i·(∫f dE)x⟫ (generator ∘ innerSL, HasDerivAt.inner).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcTrunc_integral_tendsto
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.fcOp_inner_self
-- ★ M2 operator-level first law: ⟨x,(∫f dE)x⟩ = ∫ f dμ_x (L¹ DCT tail-conv + inner continuity) — for
-- K=∫log(r/(2−r))dE_R this is the OPERATOR ⟨K⟩ = ∫ kFn dμ = cgpEntropy (JLMS Stage 1 at operator level).
-- M2 INSTANTIATION: the modular Hamiltonian K = modK S = ∫ kFn dE_R (E_R = PVM_of_selfAdjoint (rvdRC S)) as
-- a genuine operator, and the operator-level first law ⟨ξ,Kξ⟩ = cgpEntropy S ξ.
#print axioms QIQTH.StandardSubspaceModular.modK_inner_self
-- K is a genuine SYMMETRIC LINEAR operator: K=K† (modK_symmetric), additive (modK_add), ℂ-homog (modK_smul).
#print axioms QIQTH.StandardSubspaceModular.modK_symmetric
#print axioms QIQTH.StandardSubspaceModular.modK_add
#print axioms QIQTH.StandardSubspaceModular.modK_smul
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_modFlow
-- ★★★ MODULAR Δ^{it}=e^{−itK} (OPERATOR LEVEL, pinned to the genuine modular Hamiltonian K=modK): the modular flow
-- t↦boundedFC(e^{it·kFn}(R)) (= modChar(−t) = Δ^{−it} on the spectrum) has Stone generator i·modK = iK. Direct
-- specialization of the general PVM Stone reconstruction hasDerivAt_boundedFC_expSymbol. Discharges the operator
-- half of the documented Tomita–Takesaki Δ^{it}=e^{−itK} frontier for the RvD free-field modular Hamiltonian.
#print axioms QIQTH.StandardSubspaceModular.continuousAt_modFlow
-- ★ STRONG CONTINUITY of the modular flow (Stone hypothesis for Δ^{it}): t↦boundedFC(e^{it·kFn}(R))ξ continuous at
-- every t₀ (domain ξ). Specializes continuousAt_boundedFC_expSymbol'; with group law + unitarity = the full C₀-group.
#print axioms QIQTH.StandardSubspaceModular.norm_modFlow
-- ★ UNITARITY of the modular flow: ‖Δ^{it}ξ‖=‖ξ‖ (specializes norm_boundedFC_expSymbol). Completes Δ^{it} as a
-- genuine C₀ one-parameter UNITARY group: group law + generator iK + strong continuity + norm-preservation.
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_modFlow_inner
-- ★★ INFINITESIMAL JLMS FIRST LAW d/dt⟨Δ^{it}⟩|₀ = i·S: the derivative of the modular flow's diagonal matrix
-- element ⟪ξ,Δ^{−it}ξ⟫ at t=0 is i·cgpEntropy (generator iK + the operator first law ⟨K⟩=S, modK_inner_self).
-- Ties the C₀ modular-flow Stone package directly to the entanglement entropy.
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_modChar
-- ★ CANONICAL Δ^{it}=e^{−itK} (generator −iK): the flow boundedFC(e^{it·(−kFn)}(R)) = modChar(t) = Δ^{it} on the
-- spectrum has Stone generator −i·modK = −iK, i.e. Δ^{it}=e^{−itK} literally. Uses fcOp_neg (∫(−kFn)dE=−modK).
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_modFlow_inner_im
-- ★ REAL-VALUED (PHYSICAL) FIRST LAW d/dt Im⟪ξ,Δ^{−it}ξ⟫|₀ = S: the entropy is the t-derivative of the imaginary
-- part of the modular correlator (a real observable) — the operator first law in physical form (Re part stationary).
#print axioms QIQTH.StandardSubspaceModular.modUnitary_eq
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_modUnitary
-- ★★ UNIFICATION: the crossed-product modular unitary modUnitary S t = Δ^{it} (on which modularAut σ_t and M⋊_σℝ are
-- built) is borelFC(modChar t) = (PVM_R).boundedFC(e^{it·(−kFn)}) (modUnitary_eq: modSpecFun=expSymbol, modChar_eq_exp_neg_kFn),
-- so its Stone generator is −i·modK = −iK (hasDerivAt_modUnitary). Connects the unbounded-FC modular Hamiltonian K to the Wall.
#print axioms QIQTH.StandardSubspaceModular.continuousAt_modUnitary
-- ★ STRONG CONTINUITY of modUnitary (crossed-product Δ^{it}): t↦modUnitary S t ξ continuous at every t₀ (domain ξ).
-- Completes modUnitary's C₀-package: group law (modUnitary_add) + unitarity + generator −iK + strong continuity.
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_inner_modUnitary
-- ★★ GR-CHAIN LOCALIZATION IDENTITY DERIVED: d/dt⟪ξ,modUnitary S t ξ⟫|₀ = i·(−S) — EXACTLY the modular-correlation-
-- derivative hypothesis bundled in WedgeKMSToGR.WedgeKMSFlux (the Bekenstein→GR per-null localization input), now
-- derived from the modular machinery (generator −iK + first law ⟨K⟩=S). The GR heat-flux kd = −cgpEntropy (modular entropy).
#print axioms QIQTH.StandardSubspaceModular.continuous_modUnitary
-- ★ modUnitary is a strongly-continuous one-parameter unitary group (textbook C₀-group Continuous form).
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_modUnitary'
-- ★ modUnitary is C¹ EVERYWHERE: d/dt(modUnitary S t ξ)|_{t₀} = Δ^{it₀}(−iK ξ) at every t₀ (generalizes the t₀=0
-- generator hasDerivAt_modUnitary to the whole line, via hasDerivAt_boundedFC_expSymbol' + modUnitary_eq + fcOp_neg).
#print axioms QIQTH.Spectral.Multiplication.mulOp
#print axioms QIQTH.Spectral.Multiplication.mulOp_coeFn
-- ★ MULTIPLICATION OPERATOR M_φ on L²(μ): for bounded measurable φ (‖φ‖≤C), (M_φ f)(s)=φ s·f s is a ℂ-linear CLM
-- with ‖M_φ‖≤C (mulOp, via MemLp.of_le_mul + mkContinuous). First brick of the position/momentum PVM (boost generator,
-- WedgeKMSFlux #5, via Fourier conjugation) — the most concrete remaining frontier construction.
#print axioms QIQTH.Spectral.Multiplication.mulOp_mul
#print axioms QIQTH.Spectral.Multiplication.mulOp_const
#print axioms QIQTH.Spectral.Multiplication.indMul_idempotent
-- ★ MULTIPLICATION PVM brick 2 — the *-algebra: M_φ∘M_ψ=M_{φψ} (mulOp_mul), M_c=c·1 (mulOp_const), and the spectral
-- projection E(A)=M_{𝟙_A} is IDEMPOTENT E(A)²=E(A) (indMul_idempotent, since 𝟙_A·𝟙_A=𝟙_A) — the projection property.
#print axioms QIQTH.Spectral.Multiplication.mulOp_adjoint
#print axioms QIQTH.Spectral.Multiplication.indMul_isSelfAdjoint
-- ★ MULTIPLICATION PVM brick 3 — the *-structure: adjoint M_φ*=M_φ̄ (mulOp_adjoint, via the L² inner product
-- ⟪M_φ̄ f,g⟫=⟪f,M_φ g⟫) ⟹ E(A) is SELF-ADJOINT (indMul_isSelfAdjoint, 𝟙_A real). With idempotency, E(A) is an
-- ORTHOGONAL PROJECTION — the spectral projection of the position observable. Next: σ-additivity → scalarMeasure → PVM.
#print axioms QIQTH.Spectral.Multiplication.indMul_univ
#print axioms QIQTH.Spectral.Multiplication.indMul_empty
#print axioms QIQTH.Spectral.Multiplication.indMul_inter
-- ★ MULTIPLICATION PVM brick 4 — the projection-valued CONTENT: E(univ)=1, E(∅)=0, E(A)E(B)=E(A∩B) (commuting
-- orthogonal projections; disjoint ⟹ orthogonal). The finitely-additive PV-content of the position PVM.
#print axioms QIQTH.Spectral.Multiplication.indMul_inner_self
-- ★ MULTIPLICATION PVM brick 5 — the scalar spectral measure (diagonal): ⟪f,E(A)f⟫ = ∫_A conj(f)·f = ∫_A‖f‖² (the L²
-- mass of f on A; = ‖E(A)f‖²≥0 as E(A) is an orthogonal projection). As A varies this is μ_f, the scalar spectral
-- measure of the position PVM (via L2.inner_def). Next: σ-additivity (strong) → the genuine PVM; then Fourier.
#print axioms QIQTH.Spectral.Multiplication.mulOp_add
#print axioms QIQTH.Spectral.Multiplication.indMul_union_disjoint
-- ★ MULTIPLICATION PVM brick 6 — finite additivity: M_φ+M_ψ=M_{φ+ψ} (mulOp_add) ⟹ E(A⊔B)=E(A)+E(B) for disjoint A,B
-- (indMul_union_disjoint, via 𝟙_{A∪B}=𝟙_A+𝟙_B). The finitely-additive projection-valued measure. Next: σ-additivity.
#print axioms QIQTH.Spectral.Multiplication.mulOp_sub
#print axioms QIQTH.Spectral.Multiplication.mulOp_smul
-- ★ MULTIPLICATION PVM brick 7 — symbol-linearity complete: M_φ−M_ψ=M_{φ−ψ} (mulOp_sub), M_{c·φ}=c·M_φ (mulOp_smul).
-- With add/mul/const/adjoint/congr, M_· is a complete unital *-algebra hom (bounded measurable fns → CLM on L²).
#print axioms QIQTH.Spectral.Multiplication.norm_indMul_sq
-- ★ MULTIPLICATION PVM brick 8 — the scalar spectral measure as a real nonneg quantity: ‖E(A)f‖²=∫_A‖f‖² (the L²
-- mass of f on A; via inner_self_eq_norm_sq + L2.inner_def + integral_re). μ_f(A)=∫_A‖f‖² is the genuine scalar
-- spectral measure of the position PVM — the key input to σ-additivity (the tail ∫_{A_N}‖f‖²→0).
#print axioms QIQTH.Spectral.Multiplication.norm_indMul_tendsto_iInter
-- ★ MULTIPLICATION PVM brick 9 — σ-additivity (continuity from above) of the scalar spectral measure: for antitone
-- Bₙ, ‖E(Bₙ)f‖²=∫_{Bₙ}‖f‖² → ∫_{⋂Bₙ}‖f‖² (Bₙ↓∅ ⟹ ‖E(Bₙ)f‖→0). Via norm_indMul_sq + tendsto_setIntegral_of_antitone
-- (‖f‖²∈L¹). The measure-tail driving the position PVM's operator σ-additivity. Next: bundle the ProjectionValuedMeasure.
#print axioms QIQTH.Spectral.Multiplication.indMul_sdiff
-- ★ MULTIPLICATION PVM brick 10 — subtractivity E(B)=E(A)+E(B\A) for A⊆B (equivalently E(B)−E(A)=E(B\A)): the finite-
-- additive decomposition B=A⊔(B\A) at the operator level (via indSymbol_sdiff 𝟙_B=𝟙_A+𝟙_{B\A} + mulOp_add). The
-- difference operator that turns the scalar measure-tail (brick 9) into operator σ-additivity ‖E(Bₙ)f−E(⋃)f‖→0.
#print axioms QIQTH.Spectral.Multiplication.indMul_tendsto_iUnion
-- ★ MULTIPLICATION PVM brick 11 — OPERATOR σ-ADDITIVITY (continuity from below / strong convergence): for monotone
-- Bₙ↑⋃ₖBₖ, E(Bₙ)f → E(⋃ₖBₖ)f in L². Proof: ‖E(Bₙ)f−E(⋃)f‖²=‖E((⋃)\Bₙ)f‖²=∫_{(⋃)\Bₙ}‖f‖² (subtractivity brick 10
-- + brick 8), and (⋃)\Bₙ↓∅ ⟹ tail→∫_∅=0 (brick 9 engine), then ‖·‖²→0 ⟹ ‖·‖→0. THE genuine countable-additivity
-- property of the position PVM — the last structural brick before bundling the ProjectionValuedMeasure.
#print axioms QIQTH.Spectral.Multiplication.indMul_comp_disjoint
#print axioms QIQTH.Spectral.Multiplication.indMul_inner_orthogonal
-- ★ MULTIPLICATION PVM brick 12 — PAIRWISE ORTHOGONALITY of the spectral projections: for disjoint measurable A,B,
-- E(A)∘E(B)=0 (indMul_comp_disjoint, via E(A)E(B)=E(A∩B)=E(∅)=0) and ⟪E(A)x,E(B)x⟫=0 (indMul_inner_orthogonal, via
-- self-adjointness + the composition). The components live in orthogonal subspaces L²(A)⟂L²(B). This is the
-- orthogonality input to the UNCONDITIONAL (pairwise-disjoint) σ-additivity HasSum form the ProjectionValuedMeasure
-- record requires. Next: range-additivity ∑_{n<N}E(Aₙ)=E(⋃_{n<N}Aₙ) → Summable via OrthogonalFamily → bundle the PVM.
#print axioms QIQTH.Spectral.Multiplication.indMul_set_congr
#print axioms QIQTH.Spectral.Multiplication.indMul_biUnion_disjoint
-- ★ MULTIPLICATION PVM brick 13 — FINITE (RANGE) ADDITIVITY over a Finset: for pairwise-disjoint measurable A,
-- ∑_{i∈s}E(Aᵢ)=E(⋃_{i∈s}Aᵢ) (indMul_biUnion_disjoint, Finset induction via indMul_union_disjoint + set-congruence
-- indMul_set_congr, the projection depends only on the set / proof-irrelevant measurability). The discrete
-- additivity feeding the unconditional HasSum σ-additivity (partial sums = projection onto the partial union).
-- FRONTIER (recorded): the hasSum_iUnion bundle needs the Hilbert orthogonal-summability bridge — Summable from
-- ∑‖E(Aₙ)x‖²<∞ via OrthogonalFamily of the ranges L²(Aₙ) (brick 12 orthogonality) + identify limit (brick 11).
#print axioms QIQTH.Spectral.Multiplication.norm_sq_eq_integral
#print axioms QIQTH.Spectral.Multiplication.norm_indMul_le
#print axioms QIQTH.Spectral.Multiplication.indMul_inner_orthogonal'
-- ★ MULTIPLICATION PVM brick 14 — the remaining inputs to the orthogonal-summability bridge: norm_sq_eq_integral
-- (‖x‖²=∫‖x a‖², read off E(univ)=1), norm_indMul_le (‖E(A)x‖≤‖x‖ — the projection is contractive, via ∫_A≤∫;
-- gives the uniform bound ∑‖E(Aₙ)x‖²≤‖x‖²), and indMul_inner_orthogonal' (⟪E(A)x,E(B)y⟫=0 for ALL x,y on disjoint
-- A,B — the two-vector orthogonality the OrthogonalFamily of ranges L²(Aₙ) needs). With bricks 11–13 these are all
-- the inputs to hasSum_iUnion: next fire assembles OrthogonalFamily.summable_iff_norm_sq_summable → HasSum → bundle PVM.
#print axioms QIQTH.Spectral.Multiplication.summable_indMul
-- ★ MULTIPLICATION PVM brick 15 — SUMMABILITY of the spectral components (the analytic heart): for pairwise-disjoint
-- measurable A, Summable (fun n => E(Aₙ)x) in L². The vectors E(Aₙ)x live in the pairwise-ORTHOGONAL ranges L²(Aₙ)
-- (assembled as an OrthogonalFamily of submodule ranges via brick 14's two-vector orthogonality), and
-- ∑‖E(Aₙ)x‖²≤‖x‖² (finite partial sums = ‖E(⋃ᵢ₌₀ⁿAᵢ)x‖²≤‖x‖² by OrthogonalFamily.norm_sum Pythagoras + brick 13
-- range-additivity + brick 14 contractivity), so OrthogonalFamily.summable_iff_norm_sq_summable gives Summable.
-- The OrthogonalFamily bridge that the hasSum_iUnion bundle needed. Next: identify ∑'=E(⋃)x (brick 11) → bundle PVM.
#print axioms QIQTH.Spectral.Multiplication.hasSum_indMul_iUnion
#print axioms QIQTH.Spectral.Multiplication.positionPVM
-- ★ MULTIPLICATION PVM brick 16 — THE POSITION PVM BUNDLED (ProjectionValuedMeasure complete): hasSum_indMul_iUnion
-- (∑ₙE(Aₙ)x=E(⋃Aₙ)x in HasSum form — summable brick 15 + range partial sums E(⋃ᵢ₌₀ⁿAᵢ)x→E(⋃)x via brick 11
-- + uniqueness of limits) closes the last structure field. positionPVM : ProjectionValuedMeasure α (Lp ℂ 2 μ),
-- E(A)=M_{𝟙_A} on measurable A (0 otherwise): self-adjoint idempotents (bricks 2–3), E(∅)=0/E(univ)=1/E(A∩B)=E(A)E(B)
-- (brick 4), strong HasSum σ-additivity (bricks 8–15). The canonical position PVM — axiom-free, the Fourier-conjugate
-- of which is the momentum PVM (route to the boost generator / WedgeKMSFlux #5). Bricks 1–16 = the genuine spectral
-- measure of the position operator on L²(μ), Mathlib-contributable.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.conj
-- ★ PVM UNITARY CONJUGATION (the Fourier mechanism, unitary-generic): for any PVM P and unitary U : H ≃ₗᵢ[ℂ] H,
-- (P.conj U).E A = U ∘ P.E A ∘ U⁻¹ is again a genuine ProjectionValuedMeasure. All fields transport: self-adjoint
-- (U†=U⁻¹, E†=E), idempotent (U⁻¹U=1), ∅↦0, univ↦UU⁻¹=1, multiplicative, σ-additive (U continuous linear ⟹ HasSum
-- preserved via HasSum.mapL). THE general mechanism by which the Fourier–Plancherel transform carries the position
-- PVM to the MOMENTUM PVM (→ translation/boost generator, WedgeKMSFlux #5). Instantiating U = the L² Fourier
-- transform is the next (Mathlib-Fourier-gated) step; the conjugation construction itself is complete + reusable.
#print axioms QIQTH.Spectral.Multiplication.momentumPVM
#print axioms QIQTH.Spectral.Multiplication.momentumPVM_E
-- ★ THE MOMENTUM PVM on L²(ℝ) (Fourier–Plancherel conjugate of the position PVM): momentumPVM = positionPVM.conj
-- (Lp.fourierTransformₗᵢ ℝ ℂ), i.e. Ê(A)=ℱ E(A) ℱ⁻¹. A GENUINE ProjectionValuedMeasure ℝ (Lp ℂ 2 volume),
-- axiom-free (standard 3 — even through Mathlib's Plancherel), inherited with NO further work via the conjugation
-- construction. The spectral measure of the momentum operator P=ℱXℱ⁻¹ on L²(ℝ) — the route to the
-- translation/boost generator e^{itP} (WedgeKMSFlux #5). Built for E=ℝ (canonical 1D); generalizes to any
-- finite-dim real inner product space carried by fourierTransformₗᵢ. Extracting the unbounded generator P=∫k dÊ(k)
-- (Stone) is the remaining unbounded-FC frontier; the GR chain beyond #5 stays gated on the physical inputs #1/#3/#4.
#print axioms QIQTH.Spectral.Multiplication.positionPVM_norm_sq
#print axioms QIQTH.Spectral.Multiplication.positionPVM_scalarMeasure
-- ★ POSITION PVM SCALAR MEASURE = THE BORN |ψ|² POSITION DISTRIBUTION: positionPVM_norm_sq (‖E(A)x‖²=∫_A‖x‖²) and
-- positionPVM_scalarMeasure ((scalarMeasure x)(A)=ENNReal.ofReal(∫_A‖x‖²)). The position PVM's scalar spectral
-- measure IS the (unnormalized) position-probability distribution |ψ(a)|²dμ(a) of the state — the Born rule for
-- position read directly off the bundled ProjectionValuedMeasure. Axiom-free corollary of bricks 8 + 16.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.norm_conj_E
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.conj_scalarMeasure
#print axioms QIQTH.Spectral.Multiplication.momentumPVM_scalarMeasure
-- ★ SPECTRAL MEASURES TRANSFORM COVARIANTLY UNDER UNITARY CONJUGATION: norm_conj_E (‖(P.conj U).E A x‖=‖P.E A (U⁻¹x)‖,
-- U isometry) and conj_scalarMeasure ((P.conj U).scalarMeasure x = P.scalarMeasure (U⁻¹x)). Instance
-- momentumPVM_scalarMeasure: the momentum-space Born mass of x = the POSITION mass of ℱ⁻¹x, i.e. |x̂(k)|² is the
-- momentum-probability density — read off the Fourier-conjugated PVM. Axiom-free; the Born rule for momentum as the
-- Fourier image of the Born rule for position. Completes the position↔momentum PVM Born picture.
#print axioms QIQTH.Spectral.Multiplication.translationLp
#print axioms QIQTH.Spectral.Multiplication.coeFn_translationLp
#print axioms QIQTH.Spectral.Multiplication.translationLp_add
-- ★ THE TRANSLATION OPERATOR / ONE-PARAMETER GROUP on L²(ℝ): translationLp t ((τ_t f)(x)=f(x+t)) is a ℂ-linear
-- isometry (Lp.compMeasurePreservingₗᵢ + volume translation-invariance); coeFn_translationLp (pointwise action),
-- norm_translationLp (isometry), and translationLp_add (the GROUP LAW τ_s∘τ_t=τ_{s+t}, ae-composition via
-- QuasiMeasurePreserving.tendsto_ae.eventually). t↦τ_t is the one-parameter unitary group whose generator is the
-- momentum operator P (e^{itP}=τ_t) — the kinematic object behind WedgeKMSFlux #5. FRONTIER (recorded): strong
-- continuity + identifying the generator with the momentum PVM (P=∫k dÊ, Stone) is the M4 Stone/unbounded-FC frontier.
#print axioms QIQTH.Spectral.Multiplication.continuous_translationLp
-- ★ STRONG CONTINUITY of the translation group: t↦τ_t F continuous ℝ→L²(ℝ) for every F (continuous_translationLp,
-- via ContinuousMap.curry of the jointly-continuous (t,x)↦x+t + Continuous.compMeasurePreservingLp). With the group
-- law (translationLp_add) + unitarity (norm_translationLp), t↦τ_t is now a genuine STRONGLY-CONTINUOUS one-parameter
-- unitary group (C₀-group) — the full Stone hypothesis. ONLY REMAINING for #5: identify the generator with the
-- momentum PVM (P=∫k dÊ(k), Stone's theorem — the unbounded-FC frontier); the GR chain beyond #5 stays gated on #1/#3/#4.
#print axioms QIQTH.Spectral.Multiplication.translationLp_zero
#print axioms QIQTH.Spectral.Multiplication.translationUnitary
#print axioms QIQTH.Spectral.Multiplication.translationUnitary_symm_apply
-- ★ THE TRANSLATION UNITARY GROUP (≃ₗᵢ packaging): translationLp_zero (τ_0=id) + translationUnitary t (τ_t as a
-- genuine ≃ₗᵢ[ℂ] unitary, invertible with inverse τ_{-t} via LinearIsometryEquiv.ofSurjective + the group law),
-- with translationUnitary_apply/_symm_apply. Upgrades the isometry semigroup to a one-parameter UNITARY group —
-- the form the conjugation/modular machinery consumes (e.g. positionPVM.conj (translationUnitary t) = the
-- translation-covariance of the position observable). Axiom-free; the Stone generator (P) remains the frontier for #5.
#print axioms QIQTH.Spectral.Multiplication.translationUnitary_coe_apply
#print axioms QIQTH.Spectral.Multiplication.positionPVM_conj_translation_scalarMeasure
-- ★ TRANSLATION-COVARIANCE of the position observable (scalar level): positionPVM_conj_translation_scalarMeasure —
-- ((positionPVM.conj (τ_t)).scalarMeasure x)(A) = ∫_A ‖(τ_{-t}x)(a)‖² da. Conjugating the position PVM by
-- translation-by-t shifts the Born position distribution to that of the translated state τ_{-t}x — the covariance
-- that makes the translation generator (momentum) conjugate to position (via conj_scalarMeasure +
-- positionPVM_scalarMeasure + translationUnitary coe lemmas). Axiom-free.
#print axioms QIQTH.Spectral.Multiplication.positionPVM_conj_translationUnitary
-- ★ TRANSLATION-COVARIANCE of the position observable (OPERATOR form — the full Weyl covariance):
-- positionPVM_conj_translationUnitary — (positionPVM.conj (τ_t)).E A = positionPVM.E ((·+t)⁻¹A), i.e.
-- τ_t E(A) τ_t⁻¹ = E(A−t). Proof: τ_t M_{𝟙_A} τ_{-t} = M_{𝟙_{(·+t)⁻¹A}} via the indicator-shift
-- 𝟙_A(x+t)=𝟙_{(·+t)⁻¹A}(x) (preimage membership is defeq) + the three coeFn's of τ_{-t}, M_{𝟙_A}, τ_t composed
-- through the measure-preserving shift ·+t (QuasiMeasurePreserving.tendsto_ae.eventually). Axiom-free. This is the
-- kinematic backbone of WedgeKMSFlux #5: the position spectral projection transforms covariantly under translation,
-- exactly the relation making the translation generator (momentum P) canonically conjugate to position X.
#print axioms QIQTH.Spectral.Multiplication.norm_mulOp_sq
#print axioms QIQTH.Spectral.Multiplication.norm_mulOp_of_norm_one
-- ★ GENERAL MULTIPLICATION-OPERATOR NORM + UNIMODULAR ISOMETRY CRITERION: norm_mulOp_sq (‖M_φ f‖²=∫‖φ a‖²‖f a‖²,
-- generalizing brick 8's 𝟙_A case to any bounded measurable symbol) and norm_mulOp_of_norm_one (‖φ‖≡1 ⟹ ‖M_φ f‖=‖f‖,
-- the unitarity criterion). This is the foundation for the POSITION-side one-parameter unitary group e^{isX}
-- (modulation M_{e^{isx}}, |e^{isx}|=1 ⟹ unitary) — the dual of the translation group e^{itP}, completing the
-- canonical X–P pair toward the Weyl CCR. Axiom-free; the e^{isX} group + Weyl CCR is the teed-up next target.
#print axioms QIQTH.Spectral.Multiplication.norm_modulationLp
#print axioms QIQTH.Spectral.Multiplication.modulationLp_add
-- ★ THE MODULATION OPERATOR / e^{isX} UNITARY GROUP on L²(ℝ): modulationLp s = M_{e^{isx}} ((e^{isX}f)(x)=e^{isx}f(x)),
-- a one-parameter UNITARY group — norm_modulationLp (‖e^{isX}f‖=‖f‖, unitary since |e^{isx}|=1, via
-- norm_mulOp_of_norm_one), coeFn_modulationLp (pointwise action), and modulationLp_add (group law
-- e^{isX}∘e^{is'X}=e^{i(s+s')X} via mulOp_mul + Complex.exp_add). Generated by the POSITION operator X — the
-- Fourier-dual of the translation group e^{itP} (TranslationFlow). The canonical X–P pair is now both realized as
-- one-parameter unitary groups. Recorded next target: the Weyl CCR e^{itP}e^{isX}=e^{ist}e^{isX}e^{itP}.
#print axioms QIQTH.Spectral.Multiplication.modSymbol_add_right
#print axioms QIQTH.Spectral.Multiplication.weyl_relation
-- ★ THE WEYL CANONICAL COMMUTATION RELATION (integrated Heisenberg [X,P]=i): weyl_relation —
-- τ_t (e^{isX} f) = e^{ist} • (e^{isX} (τ_t f)), i.e. e^{itP} e^{isX} = e^{ist} · e^{isX} e^{itP}. The translation
-- group e^{itP} and the modulation group e^{isX} fail to commute by exactly the phase e^{ist} — the INTEGRATED
-- (Weyl) form of the canonical commutation relation [X,P]=i. Proof: both sides act a.e. as e^{is(x+t)}f(x+t), the
-- phase e^{ist} peeled via modSymbol_add_right (e^{is(x+t)}=e^{ist}e^{isx}). Axiom-free. The full kinematic algebra
-- of the position/momentum operators on L²(ℝ) — Born rules, covariance, AND the CCR — is now machine-checked; the
-- only remaining Lean step for #5 is the (unbounded) Stone generator, a genuine Mathlib gap.
#print axioms QIQTH.Spectral.Multiplication.modulationLp_zero
#print axioms QIQTH.Spectral.Multiplication.modulationLp_neg_comp
-- ★ MODULATION GROUP STRUCTURE (identity + inverses): modulationLp_zero (e^{i0X}=1, via mulOp_const) +
-- modulationLp_neg_comp/comp_neg (e^{∓isX}∘e^{±isX}=1, from the group law at (−s)+s=0). Completes s↦e^{isX} as a
-- genuine group homomorphism ℝ→unitaries (identity, composition, inverses) — the position-side one-parameter
-- unitary group is now a full group. Axiom-free. Recorded next target: strong continuity of e^{isX} (s↦e^{isX}f
-- continuous, via DCT) — making it a full C₀-group symmetric to e^{itP}; then the (unbounded) Stone generator X.
#print axioms QIQTH.Spectral.Multiplication.continuous_modulationLp
-- ★ STRONG CONTINUITY of the modulation group: s↦e^{isX}f continuous ℝ→L²(ℝ) for every f (continuous_modulationLp,
-- via DCT). Proof: ‖e^{isX}f−e^{is₀X}f‖²=∫|e^{isx}−e^{is₀x}|²|f|² (mulOp_sub + norm_mulOp_sq) →0 by
-- tendsto_integral_filter_of_dominated_convergence (integrand→0 ptwise as s→s₀, dominated by 4|f|²). With the group
-- law + unitarity + identity/inverses, e^{isX} is now a full STRONGLY-CONTINUOUS one-parameter UNITARY group
-- (C₀-group, generator = the position operator X) — SYMMETRIC to the translation group e^{itP}. Axiom-free. Both
-- legs of the canonical X–P pair are now complete C₀-groups; only the (unbounded) Stone generators X,P stay frontier.
#print axioms QIQTH.Spectral.Multiplication.modulationUnitary
#print axioms QIQTH.Spectral.Multiplication.modulationUnitary_symm_apply
-- ★ THE MODULATION UNITARY (≃ₗᵢ packaging): modulationUnitary s — e^{isX} as a genuine ≃ₗᵢ[ℂ] unitary, invertible
-- with inverse e^{-isX} (from modulationLp_neg_comp/comp_neg), with modulationUnitary_apply/_symm_apply. Parallels
-- translationUnitary; packages e^{isX} in the form the conjugation/modular machinery consumes (e.g.
-- momentumPVM.conj (modulationUnitary s) = the dual covariance of the momentum observable under position-modulation).
-- Axiom-free. Both X–P unitary groups are now ≃ₗᵢ-packaged; the (unbounded) Stone generators X,P stay frontier.
#print axioms QIQTH.Spectral.Multiplication.positionPVM_conj_modulationUnitary
-- ★ INVARIANCE OF THE POSITION OBSERVABLE UNDER MODULATION (the trivial leg of Weyl covariance):
-- positionPVM_conj_modulationUnitary — e^{isX} E(A) e^{-isX} = E(A). Modulation commutes with the position
-- spectral projection E(A)=M_{𝟙_A} (both multiplication operators): M_{e^{isx}}M_{𝟙_A}M_{e^{-isx}}=M_{𝟙_A} since
-- e^{isx}e^{-isx}=1 (mulOp_mul ×2 + mulOp_congr). So [e^{isX},E(A)]=0 — e^{isX} is a function of X and commutes
-- with all functions of X. CONTRAST the translation covariance where τ_t genuinely MOVES E(A). Axiom-free. The two
-- legs of the Weyl covariance are now both machine-checked: τ_t moves position (E(A−t)); e^{isX} leaves it (E(A)).
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.E_comm
-- ★ SPECTRAL PROJECTIONS OF ANY PVM COMMUTE: E_comm (E s * E t = E t * E s for measurable s,t, both = E(s∩t) via
-- E_inter + Set.inter_comm). A fundamental general property of any ProjectionValuedMeasure — the observable is a
-- commutative family of projections — applying at once to BOTH the position PVM and the momentum PVM (and the finite
-- spectral PVM). Axiom-free, general, Mathlib-contributable.
#print axioms QIQTH.Spectral.Multiplication.indMul_inner
-- ★ OFF-DIAGONAL MATRIX ELEMENT of the position spectral projection: indMul_inner — ⟪g,E(A)f⟫=∫_A conj(g)·f dμ, the
-- position-space transition amplitude between g and f restricted to A (the complex off-diagonal scalar spectral
-- measure μ_{g,f}, polarized form of the diagonal μ_f). Generalizes indMul_inner_self (g=f). Axiom-free; the matrix
-- elements ⟪g,f(X)g'⟫ of every bounded function of position integrate against it.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.conj_E_inner
#print axioms QIQTH.Spectral.Multiplication.momentumPVM_inner
-- ★ MATRIX ELEMENTS UNDER UNITARY CONJUGATION + THE MOMENTUM TRANSITION AMPLITUDE: conj_E_inner (general —
-- ⟪g,(P.conj U).E A f⟫=⟪U⁻¹g,P.E A (U⁻¹f)⟫, the off-diagonal companion of conj_scalarMeasure, via U isometry +
-- inner_map_map) and momentumPVM_inner (instance — ⟪g,Ê(B)f⟫=∫_B conj((ℱ⁻¹g)(a))·(ℱ⁻¹f)(a) da: the momentum-space
-- transition amplitude is the POSITION amplitude of the inverse-Fourier states). Axiom-free; completes the
-- position↔momentum off-diagonal Born/amplitude picture (diagonal = scalarMeasure, off-diagonal = these).
#print axioms QIQTH.Spectral.Multiplication.positionPVM_scalarMeasure_eq_withDensity
-- ★ POSITION SCALAR MEASURE = THE BORN |x|² DENSITY MEASURE: positionPVM_scalarMeasure_eq_withDensity —
-- scalarMeasure x = μ.withDensity (a ↦ ‖x a‖²), the position-probability distribution of x is the measure with
-- Radon–Nikodym density |x|² w.r.t. μ (the measure-level Born rule for position; the set-level
-- positionPVM_scalarMeasure promoted to a measure identity via withDensity_apply + ofReal_integral_eq_lintegral_ofReal).
-- Axiom-free. Recorded next target: the position Born EXPECTATION ⟨f(X)⟩=∫f|x|² (positionPVM.diagInt = ∫f·|x|²),
-- via integral_withDensity_eq_integral_smul₀ (NNReal weight) — the withDensity-integral step.
#print axioms QIQTH.Spectral.Multiplication.positionPVM_diagInt
-- ★ THE POSITION BORN EXPECTATION VALUE: positionPVM_diagInt — diagInt f x = ∫ f(a)·‖x a‖² dμ. The expectation
-- of any bounded function f of the position observable X in the (unnormalized) state x is ∫ f(a)|x(a)|² da — the
-- Born expectation rule for position, read off the spectral measure (diagInt = ∫ f d(scalarMeasure x) against the
-- |x|² density, via integral_withDensity_eq_integral_toReal_smul₀). Axiom-free. With the diagonal/off-diagonal
-- scalar measures + the expectation, the position observable's full Born statistics are machine-checked.
#print axioms QIQTH.Spectral.ProjectionValuedMeasure.conj_diagInt
#print axioms QIQTH.Spectral.Multiplication.momentumPVM_diagInt
-- ★ THE MOMENTUM BORN EXPECTATION VALUE (Fourier image of the position one): conj_scalarMeasure_eq +
-- conj_diagInt (general — (P.conj U).diagInt f x = P.diagInt f (U⁻¹x): the diagonal functional/expectation
-- transforms covariantly under conjugation) and momentumPVM_diagInt (instance — momentumPVM.diagInt f x =
-- ∫ f(a)·‖(ℱ⁻¹x)(a)‖² da: ⟨f(P)⟩ is the POSITION expectation of ℱ⁻¹x). Axiom-free. Both observables X,P now have
-- their FULL Born statistics machine-checked: probability density, transition amplitudes, AND expectation values.
#print axioms QIQTH.Spectral.Multiplication.momentumPVM_scalarMeasure_eq_withDensity
-- ★ MOMENTUM SCALAR MEASURE = THE BORN |ℱ⁻¹x|² DENSITY MEASURE: momentumPVM_scalarMeasure_eq_withDensity —
-- scalarMeasure x = volume.withDensity (a ↦ ‖(ℱ⁻¹x)(a)‖²): the momentum-probability distribution of x is the
-- measure with density |ℱ⁻¹x|² (the momentum-space |x̂|²), the Fourier image of the position density (conj_scalarMeasure_eq
-- + positionPVM_scalarMeasure_eq_withDensity). Axiom-free. Both observables now have the measure-level Born density.
#print axioms QIQTH.Spectral.Multiplication.fourier_integral_norm_sq
-- ★ PLANCHEREL / CONSERVATION OF TOTAL PROBABILITY: fourier_integral_norm_sq — ∫‖(ℱ⁻¹x)(a)‖² da = ‖x‖². The
-- Fourier transform is an L² isometry, so the momentum density |ℱ⁻¹x|² integrates to the same total mass ‖x‖² as
-- the position density |x|² — the Born total-probability is conserved between the position and momentum
-- representations (norm_sq_eq_integral + LinearIsometryEquiv.norm_map). Axiom-free.
#print axioms QIQTH.Spectral.stoneDomain
#print axioms QIQTH.Spectral.stoneGen
-- ★ STONE Phase 3.1 — THE INFINITESIMAL GENERATOR (the first brick of breaking the P4 wall / general Stone):
-- stoneDomain U = {x : t↦U_t x differentiable at 0} (a ℂ-submodule, since each U_t is ℂ-linear) and
-- stoneGen U : H →ₗ.[ℂ] H = the unbounded operator A x = −i·(d/dt U_t x)|₀ on that smooth domain (a genuine
-- LinearPMap; linearity from deriv_add/deriv_const_smul on the differentiable domain, no hypotheses on U needed).
-- For a strongly-continuous unitary group this IS the self-adjoint Stone generator. FRONTIER (recorded): essential
-- self-adjointness (Phase 3.2, Nelson analytic vectors) + the Cayley transform/unbounded spectral theorem (3.3)
-- are the genuine Mathlib-grade gaps; applying this to clockTransl ⟹ X=A_edge (P4-wall 4.3) is gated on them.
#print axioms QIQTH.Spectral.hasDerivAt_stoneGen
-- ★ STONE 3.1 cont. — the generator–derivative relation: hasDerivAt_stoneGen — for x in the smooth domain,
-- HasDerivAt (t↦U_t x) (i·A x) 0 (i.e. A x=−i·(d/dt U_t x)|₀, the HasDerivAt form). The foundational helper every
-- downstream Stone argument (symmetry ⟪Ax,y⟫=⟪x,Ay⟫, flow-invariance U_s·domain⊆domain, essential self-adjointness)
-- differentiates through. Axiom-free. NEXT sub-bricks: flow-invariance (group law + HasDerivAt.scomp/comp_hasDerivAt)
-- then symmetry (U_t unitary + HasDerivAt.inner) — the road to Phase 3.2.
#print axioms QIQTH.Spectral.hasDerivAt_stoneGen_flow
-- ★ STONE 3.1 cont. — the shifted-orbit derivative: hasDerivAt_stoneGen_flow — t↦U_t(U_s x) has derivative
-- i•U_s(A x) at 0 (group law + U_s a smooth CLM). The key derivative computation behind BOTH flow-invariance and
-- the commutation [A,U_s]=0; stoneDomain_apply_mem is now its .differentiableAt. Axiom-free.
#print axioms QIQTH.Spectral.stoneGen_comm_flow
-- ★ STONE 3.1 cont. — THE GENERATOR COMMUTES WITH THE FLOW [A,U_s]=0: stoneGen_comm_flow — stoneGen U (U_s x) =
-- U_s (stoneGen U x) on the smooth domain (from hasDerivAt_stoneGen_flow + generator-identification). The
-- U-invariance of A that makes the clock energy X=A_edge (Phase 4.3) compatible with the modular flow it is read
-- off from. Axiom-free.
#print axioms QIQTH.Spectral.stoneDomain_apply_mem
-- ★ STONE 3.1 cont. — FLOW-INVARIANCE OF THE SMOOTH DOMAIN: stoneDomain_apply_mem — for a one-parameter GROUP
-- (U(s+t)=U s∘L U t), U_s maps stoneDomain U into itself. (t↦U_t(U_s x)=U_{t+s}x is differentiable at 0 because
-- the orbit τ↦U_τ x is differentiable at s, via the group law U_τ=U_s∘U_{τ−s} + U_s a smooth CLM — chain rule
-- HasDerivAt.scomp_of_eq + HasFDerivAt.comp_hasDerivAt with restrictScalars ℝ for the ℂ-CLM over the ℝ-curve.)
-- The U-invariance of the smooth domain, a prerequisite for essential self-adjointness (Phase 3.2). Axiom-free.
-- NEXT: the symmetry ⟪Ax,y⟫=⟪x,Ay⟫ (U_t unitary + HasDerivAt.inner), then the Gårding-density/essential-s.a. wall.
#print axioms QIQTH.Spectral.hasDerivAt_stoneGen_neg
#print axioms QIQTH.Spectral.stoneGen_symmetric
-- ★ STONE 3.1 cont. — THE GENERATOR IS SYMMETRIC (first half of self-adjointness): hasDerivAt_stoneGen_neg
-- (backward flow t↦U_{−t}x has derivative −i·A x) and stoneGen_symmetric — ⟪A x, y⟫=⟪x, A y⟫ on the smooth domain
-- for a one-parameter UNITARY group (U group + U_t inner-preserving). Proof: the unitary relation
-- ⟪U_t x,y⟫=⟪x,U_{−t}y⟫ differentiated at 0 two ways (HasDerivAt.inner product rule) gives ⟪i·Ax,y⟫=⟪x,−i·Ay⟫, i.e.
-- −i⟪Ax,y⟫=−i⟪x,Ay⟫ (conj_I + inner_smul); cancel −i. The symmetry of A=−i(d/dt U_t) — the operator is Hermitian on
-- its domain. Axiom-free. REMAINING wall (Phase 3.2/3.3): Gårding density of the domain + essential self-adjointness
-- (Range(A±i) dense / Nelson analytic vectors) + the Cayley transform/unbounded spectral theorem — the genuine Mathlib gaps.
#print axioms QIQTH.Spectral.stoneGen_isFormalAdjoint_self
-- ★ STONE 3.1 cont. — the generator bundled as a SYMMETRIC unbounded operator in Mathlib's framework:
-- stoneGen_isFormalAdjoint_self — (stoneGen U).IsFormalAdjoint (stoneGen U) for a one-parameter unitary group
-- (direct from stoneGen_symmetric). This is Mathlib's LinearPMap.IsFormalAdjoint (T is a formal adjoint of itself
-- ⟺ symmetric), the precise A⊆A* entry point: once the domain is dense, stoneGen U ⊆ (stoneGen U)† (le_adjoint),
-- and self-adjointness is Ā=Ā*. Axiom-free. REMAINING wall: domain density (Gårding) + essential self-adjointness +
-- Cayley — the genuine Mathlib gaps.
#print axioms QIQTH.Spectral.stoneGen_eq_of_hasDerivAt
-- ★ STONE 3.1 cont. — generator IDENTIFICATION (uniqueness half of Stone's correspondence):
-- stoneGen_eq_of_hasDerivAt — if HasDerivAt (t↦U_t x) (i•v) 0 then stoneGen U x = v. The generator is pinned by
-- ANY witnessed derivative (via HasDerivAt.unique + smul cancel by i≠0). The bridge from the abstract stoneGen to a
-- concrete operator: to show stoneGen of a group = a known B, exhibit HasDerivAt (t↦U_t x) (i•B x) 0. No density. Axiom-free.
#print axioms QIQTH.Spectral.stoneGen_re_inner_smul_I
#print axioms QIQTH.Spectral.stoneGen_norm_add_smul_I_sq
#print axioms QIQTH.Spectral.stoneGen_norm_sub_smul_I_sq
-- ★ STONE 3.1 cont. — THE CAYLEY ESTIMATE (deficiency-index pair): for the symmetric generator,
-- ‖(A±i)x‖² = ‖Ax‖² + ‖x‖² (stoneGen_norm_add/sub_smul_I_sq). The cross term re⟪Ax,i•x⟫=0 (stoneGen_re_inner_smul_I
-- — ⟪Ax,x⟫ real by symmetry, ×i rotates to imaginary axis). So A±i are bounded below (‖(A±i)x‖≥‖x‖), hence
-- INJECTIVE — the entry point to the Cayley transform (A−i)(A+i)⁻¹ and the deficiency-index criterion for
-- essential self-adjointness (Phase 3.2/3.3). Axiom-free. (Surjectivity of A±i = the open Range-dense wall.)
#print axioms QIQTH.Spectral.stoneGen_norm_cayley_eq
#print axioms QIQTH.Spectral.stoneGen_norm_le_norm_add_smul_I
-- ★ STONE 3.1 cont. — CAYLEY ISOMETRY + bounded-below: stoneGen_norm_cayley_eq — ‖(A−i)x‖=‖(A+i)x‖ (both
-- =√(‖Ax‖²+‖x‖²)), so V:(A+i)x↦(A−i)x is norm-preserving — the defining property of the Cayley transform
-- V=(A−i)(A+i)⁻¹ (isometry Range(A+i)→Range(A−i); unitary ⟺ both ranges dense ⟺ A e.s.a.). And
-- stoneGen_norm_le_norm_add_smul_I — ‖x‖≤‖(A+i)x‖, so A+i injective. Axiom-free. (Range-density = open wall.)
#print axioms QIQTH.Spectral.stoneGen_le_adjoint
-- ★ STONE 3.1 cont. — the EXPLICIT A⊆A† containment, conditional on Gårding density:
-- stoneGen_le_adjoint — given hdense : Dense (stoneGen U).domain, stoneGen U ≤ (stoneGen U)† (via le_adjoint).
-- The symmetric-operator containment self-adjointness Ā=Ā† rests on. Density hypothesis left EXPLICIT and
-- undischarged — proving Dense (stoneGen U).domain for the concrete C₀ groups (Gårding/mollified vectors) is the
-- honestly-carried Mathlib-grade wall. Axiom-free.

-- Phase 1.3 (bounded spectral theorem): scalar-measure construction for PVM_of_selfAdjoint
#print axioms QIQTH.SpectralTheorem.re_inner_cfc_nonneg
-- expected: standard only — positivity bridge: f ≥ 0 on spectrum ⟹ 0 ≤ re⟪x, f(T) x⟫.
-- The positivity of the scalar functional Λ_x f = re⟪x, cfc f T x⟫ seeding μ_x (cfc_nonneg
-- in the C*-order of B(H), which coincides with the Loewner/IsPositive order).
#print axioms QIQTH.SpectralTheorem.integral_specMeasure
-- expected: standard only — defining property of the scalar spectral measure μ_x (Riesz–Markov):
-- ∫ f dμ_x = re⟪x, f(T) x⟫.  μ_x := rieszMeasure of the positive functional Λ_x = specPLM;
-- the scalar half of the bounded spectral theorem PVM_of_selfAdjoint.
#print axioms QIQTH.SpectralTheorem.specMeasure_real_univ
-- expected: standard only — total mass μ_x(univ) = ‖x‖² (scalar-level E(univ)=1): 1(T)=1,
-- re⟪x,x⟫=‖x‖². Uses the constant-1 C_c function (HasCompactSupport.of_compactSpace).
#print axioms QIQTH.SpectralTheorem.inner_cfcHom_polarization
-- expected: standard only — complex polarization bridge: the off-diagonal ⟪f(T) x, y⟫ is the
-- polarized combination of the diagonal scalar integrals ∫ f dμ_z (f(T) self-adjoint, diagonal
-- real). The bridge from the scalar measures μ_z to the projection-valued E(B).
#print axioms QIQTH.SpectralTheorem.specMeasure_real_le
-- expected: standard only — per-set bound μ_z(B) ≤ ‖z‖² (monotone vs total mass); feeds the
-- operator-norm bound on the spectral projections E(B).
#print axioms QIQTH.SpectralTheorem.specMeasure_smul
-- expected: standard only — scaling law μ_{c•x} = ‖c‖²·μ_x (positive-measure identity via
-- Riesz–Markov uniqueness Measure.ext_of_integral_eq_on_compactlySupported).
#print axioms QIQTH.SpectralTheorem.specMeasure_parallelogram
-- expected: standard only — parallelogram law μ_{x+y}+μ_{x−y} = 2μ_x+2μ_y (cross terms cancel);
-- the engine for sesquilinearity of the polarized form (x,y)↦μ_{x,y}(B) toward E(B).
#print axioms QIQTH.SpectralTheorem.specMeasure_add
-- expected: standard only — additivity engine: μ_{x+a+b}+μ_{x−a}+μ_{x−b} = μ_{x−a−b}+μ_{x+a}+μ_{x+b}
-- (both sides = 3q(x)+2q(a)+2q(b)+g(a,b)); gives additivity of the polarized form in y
-- (apply with (a,b)=(y₁,y₂) and (I·y₁,I·y₂)). Via Riesz–Markov uniqueness + quadratic-form ring.
#print axioms QIQTH.SpectralTheorem.qForm_smul
-- expected: standard only — q_s(c•z) = ‖c‖²·q_s(z) (diagonal quadratic form scaling).
#print axioms QIQTH.SpectralTheorem.qForm_parallelogram
-- expected: standard only — q_s parallelogram (specMeasure_parallelogram pushed through .real).
#print axioms QIQTH.SpectralTheorem.qForm_add
-- expected: standard only — q_s second-difference identity (specMeasure_add through .real).
#print axioms QIQTH.SpectralTheorem.bForm_self
-- expected: standard only — b_s(u,u) = q_s(u) (polarization diagonal).
#print axioms QIQTH.SpectralTheorem.bForm_add_right
-- expected: standard only — b_s additive in right arg; with bForm_comm/add_left ⟹ biadditive.
#print axioms QIQTH.SpectralTheorem.bForm_sq_le
-- expected: standard only — CAUCHY–SCHWARZ b_s(u,v)² ≤ q_s(u)·q_s(v). Since q_s ≥ 0, the
-- quadratic t↦q_s(u+t•v) is ≥0 on ℚ (ℚ-homog via bundled AddMonoidHom + map_ratCast_smul),
-- hence on ℝ (Rat.denseRange_cast.induction_on), so discrim ≤ 0 (discrim_le_zero). The keystone
-- delivering boundedness → continuity → ℝ-linearity → the spectral projection E(B).
#print axioms QIQTH.SpectralTheorem.bForm_abs_le
-- expected: standard only — boundedness |b_s(u,v)| ≤ ‖u‖·‖v‖ (CS + q_s(z)≤‖z‖²).
#print axioms QIQTH.SpectralTheorem.bForm_real_smul_right
-- expected: standard only — ℝ-homogeneity b_s(u,r•v)=r·b_s(u,v) (continuity + map_real_smul);
-- the Jordan–von Neumann analytic step, now discharged.
#print axioms QIQTH.SpectralTheorem.bForm_I_comm
-- expected: standard only — i-twist b_s(I•x,y) = −b_s(x,I•y) (from i-invariance of q_s).
#print axioms QIQTH.SpectralTheorem.cForm_add_right
-- expected: standard only — complex form c_s additive in y.
#print axioms QIQTH.SpectralTheorem.cForm_I_right
-- expected: standard only — c_s(x,I•y) = i·c_s(x,y); with ℝ-homog+additivity ⟹ ℂ-linear in y.
#print axioms QIQTH.SpectralTheorem.cForm_smul_right
-- expected: standard only — ℂ-homogeneity c_s(x,c•y)=c·c_s(x,y) (decompose c=re+im·i; combine
-- ℝ-homog, the i-twist, additivity). c_s(x,·) is now fully ℂ-linear in y.
#print axioms QIQTH.SpectralTheorem.cForm_conj_smul_left
-- expected: standard only — conjugate-linearity c_s(c•x,y)=conj(c)·c_s(x,y). With cForm_add_left,
-- c_s is now fully sesquilinear (conj-linear in x, ℂ-linear in y).
#print axioms QIQTH.SpectralTheorem.cForm_norm_le
-- expected: standard only — ‖c_s(x,y)‖ ≤ 2·‖x‖·‖y‖ (bounded sesquilinear form ⟹ E(s) via Riesz).
#print axioms QIQTH.SpectralTheorem.specProj
-- expected: standard only — THE SPECTRAL PROJECTION E(s):H→L[ℂ]H, Riesz rep of c_s via
-- continuousLinearMapOfBilin (bundled H→L⋆[ℂ]H→L[ℂ]ℂ from mkContinuous per slot).
#print axioms QIQTH.SpectralTheorem.inner_specProj
-- expected: standard only — defining identity ⟪E(s) x, y⟫ = c_s(x,y). The operator E(s) now
-- exists; remaining PVM laws (E_univ=1, E_inter, σ-additivity) build on this + the q/b engine.
#print axioms QIQTH.SpectralTheorem.specProj_empty
-- expected: standard only — E(∅) = 0.
#print axioms QIQTH.SpectralTheorem.specProj_isSelfAdjoint
-- expected: standard only — E(s) self-adjoint (Hermitian symmetry c_s(y,x)conj = c_s(x,y)).
#print axioms QIQTH.SpectralTheorem.specProj_univ
-- expected: standard only — E(univ) = 1 (c_univ(x,y)=⟪x,y⟫ via norm polarization + μ_x(univ)=‖x‖²).
#print axioms QIQTH.SpectralTheorem.specProj_isPositive
-- expected: standard only — 0 ≤ E(s) (re⟪E(s)x,x⟫ = q_s(x) ≥ 0).
#print axioms QIQTH.SpectralTheorem.specProj_union_disjoint
-- expected: standard only — finite additivity E(s∪t)=E(s)+E(t) on disjoint measurable sets
-- (measure additivity in the set argument).
#print axioms QIQTH.SpectralTheorem.specProj_le_one
-- expected: standard only — E(s) ≤ 1 (1−E(s) positive; re⟪(1−E(s))x,x⟫=‖x‖²−q_s(x)≥0).
#print axioms QIQTH.SpectralTheorem.norm_specProj_sq_le
-- expected: standard only — effect estimate ‖E(s)x‖²≤q_s(x) (E(s)²≤E(s) via Commute.mul_nonneg).
#print axioms QIQTH.SpectralTheorem.specProj_finset_sum
-- expected: standard only — finite Finset additivity ∑_{n∈F} E(A n) = E(⋃_{n∈F} A n) (induction
-- on F via specProj_union_disjoint). The base for σ-additivity (norm-tail + effect estimate).
#print axioms QIQTH.SpectralTheorem.specProj_hasSum
-- expected: standard only — σ-ADDITIVITY (strong/SOT): HasSum (E(A n) x) (E(⋃A) x) for disjoint
-- measurable A. Norm-tail: ‖∑_s E(A n)x − E(⋃A)x‖² ≤ q_{⋃A}(x)−∑_s q_{A n}(x) → 0 (effect
-- estimate + scalar measure σ-additivity via ENNReal.hasSum_toReal + squeeze_zero). E is now a
-- complete σ-additive normalized POVM (0≤E(s)≤1, E(∅)=0, E(univ)=1, self-adjoint, σ-additive).
#print axioms QIQTH.SpectralTheorem.inner_cfcHom_conj
-- expected: standard only — cfcHom-conjugation engine ⟪g(T)z, h(T)(g(T)z)⟫ = ⟪z, (h·g²)(T)z⟫
-- (self-adjointness + cfcHom multiplicativity g·h·g=h·g²). First brick toward E_inter (the
-- bounded-Borel-FC bridge: transport cfcHom multiplicativity to indicators via monotone class).
#print axioms QIQTH.SpectralTheorem.qfForm_smul
-- expected: standard only — q_f(c•z)=‖c‖²q_f(z) for the f-weighted form q_f(z):=∫f dμ_z.
#print axioms QIQTH.SpectralTheorem.qfForm_parallelogram
-- expected: standard only — parallelogram for q_f (descends from specMeasure_parallelogram).
#print axioms QIQTH.SpectralTheorem.qfForm_add
-- expected: standard only — additivity engine for q_f. The q-engine for the bounded Borel FC Φ(f):
-- replacing q_s=∫𝟙_s by q_f=∫f, transferred from the measure identities by integration.
#print axioms QIQTH.SpectralTheorem.inner_cfcHom_mul
-- expected: standard only — ⟪g(T)x,h(T)y⟫=⟪x,(g·h)(T)y⟫ (self-adj + cfcHom algebra hom). The clean
-- engine for the DIRECT E_inter route (off-diagonal identity ν_{g(T)x,y}=g·ν_{x,y}, no Φ/monotone class).
#print axioms QIQTH.SpectralTheorem.integral_specMeasure_cont
-- expected: standard only — ∫ h dμ_z = re⟪z, h(T)z⟫ for continuous h (C_c bridge on compact spectrum).
#print axioms QIQTH.SpectralTheorem.specMeasure_engine
-- expected: standard only — off-diagonal engine: ∫h dμ_{g(T)x+v}−∫h dμ_{g(T)x−v} = ∫(h·g)dμ_{x+v}−
-- ∫(h·g)dμ_{x−v} (both = 4·re⟪x,(h·g)(T)v⟫). The integral form of ν_{g(T)x,y}=g·ν_{x,y}; crux of E_inter.
#print axioms QIQTH.SpectralTheorem.specMeasure_engine_measure
-- expected: standard only — engine MEASURE form (g≥0): μ_{g(T)x+v}+μ_{x−v}·g = μ_{g(T)x−v}+μ_{x+v}·g
-- (·g = withDensity(ofReal g)), by Riesz–Markov uniqueness from specMeasure_engine
-- (integral_withDensity_eq_integral_toReal_smul + isFiniteMeasure_withDensity). E_inter step (a).
#print axioms QIQTH.SpectralTheorem.withDensity_real_setIntegral
-- expected: standard only — ((μ_z)·g).real s = ∫_s g dμ_z for g≥0 (withDensity_apply +
-- integral_eq_lintegral_of_nonneg_ae). The withDensity↔setIntegral bridge.
#print axioms QIQTH.SpectralTheorem.specMeasure_setEngine_nonneg
-- expected: standard only — set-level engine (g≥0): q_s(g(T)x+v)−q_s(g(T)x−v)=∫_s g dμ_{x+v}−
-- ∫_s g dμ_{x−v} (eval specMeasure_engine_measure at s via .real). E_inter step (b), g≥0 case.
#print axioms QIQTH.SpectralTheorem.specMeasure_setEngine
-- expected: standard only — set-level engine, GENERAL continuous g (signed): same identity,
-- via linearity (g=(g+‖g‖)−‖g‖; LHS=4·b_s(g(T)x,v) linear via bForm_add/sub_left+cfcHom, RHS by
-- integral_add). E_inter step (b) complete.
#print axioms QIQTH.SpectralTheorem.re_inner_cfcHom_specProj
-- expected: standard only — diagonal–E(s): re⟪x,h(T)(E(s)v)⟫ = b_s(h(T)x,v).
#print axioms QIQTH.SpectralTheorem.integral_specMeasure_polarization
-- expected: standard only — ∫f dμ_{w+u}−∫f dμ_{w−u} = 4·re⟪w,f(T)u⟫.
#print axioms QIQTH.SpectralTheorem.specProj_engine_measure
-- expected: standard only — final measure identity μ_{x+E(s)v}+(μ_{x−v})↾s = μ_{x−E(s)v}+(μ_{x+v})↾s
-- (RMK uniqueness; test reduces via polarization+re_inner_cfcHom_specProj+specMeasure_setEngine).
#print axioms QIQTH.SpectralTheorem.bForm_specProj
-- expected: standard only — b_t(x,E(s)v) = b_{s∩t}(x,v) (evaluate the final measure identity at t).
#print axioms QIQTH.SpectralTheorem.specProj_inter
-- expected: standard only — ★ E_INTER: E(s∩t)=E(s)·E(t), the projection/multiplicativity property.
-- The LAST ProjectionValuedMeasure field. E is now a genuine PVM ⟹ bounded spectral theorem.
#print axioms QIQTH.SpectralTheorem.PVM_of_selfAdjoint
-- expected: standard only — ★★ THE BOUNDED SPECTRAL THEOREM (PVM form): every bounded self-adjoint
-- T : H →L[ℂ] H induces a ProjectionValuedMeasure on spectrum ℝ T (E = specProj). All fields proved
-- axiom-free (isIdem from E_inter at s=t). THE Layer-1 keystone unlocking bounded Borel FC + Δ^it.
#print axioms QIQTH.SpectralTheorem.re_inner_T_eq_integral
-- expected: standard only — spectral representation (diagonal): ∫_{σ(T)} λ dμ_x(λ) = re⟪x,Tx⟫,
-- i.e. T = ∫λ dE on the diagonal (T recovered from its PVM). Via integral_specMeasure + cfcHom_id.

-- Layer 2 kickoff: the bounded Borel functional calculus of T (via PVM_of_selfAdjoint)
#print axioms QIQTH.SpectralTheorem.borelFC_mul
-- expected: standard only — (f·g)(T)=f(T)·g(T) for bounded measurable f,g (the bounded Borel FC of T
-- is multiplicative). Instantiates PVM.boundedFC_mul with PVM_of_selfAdjoint. Gateway to Δ^it.
#print axioms QIQTH.SpectralTheorem.borelFC_one
-- expected: standard only — bounded Borel FC unital ((fun _=>1)(T)=1).

-- Layer 2: the continuum one-parameter unitary group U(t)=exp(it·A)=Δ^it (modular flow)
#print axioms QIQTH.SpectralTheorem.modFlow_add
-- expected: standard only — one-parameter group law U(s+t)=U(s)·U(t) (commuting exponentials).
#print axioms QIQTH.SpectralTheorem.modFlow_unitary
-- expected: standard only — U(t)⋆·U(t)=1 (unitary), from U(t)⋆=U(−t) (star_exp + A self-adjoint).
-- The continuum modular flow Δ^it generalizing FiniteModularTheory.sigmaDiag to B(H).
#print axioms QIQTH.SpectralTheorem.modFlow_continuous
-- expected: standard only — t↦U(t) norm-continuous (exp_continuous). So U is a strongly-continuous
-- one-parameter unitary group — the bounded-generator Stone's theorem.
-- Layer 2: the modular automorphism group σ_t(x)=U(t)·x·U(t)⁻¹
#print axioms QIQTH.SpectralTheorem.modAut_comp
-- expected: standard only — σ_s∘σ_t = σ_{s+t} (one-parameter automorphism group law).
#print axioms QIQTH.SpectralTheorem.modAut_mul
-- expected: standard only — σ_t(x·y)=σ_t(x)·σ_t(y) (conjugation by a unitary is multiplicative).
#print axioms QIQTH.SpectralTheorem.modAut_star
-- expected: standard only — σ_t(x⋆)=σ_t(x)⋆ (A self-adjoint). σ_t is a *-automorphism group — the
-- continuum modular automorphism group, generalizing FiniteModularTheory.modAut to B(H).
-- Layer 2: modular invariance of the vector state ω_ξ(x)=⟪ξ,xξ⟫
#print axioms QIQTH.SpectralTheorem.modAut_vectorState_invariant
-- expected: standard only — ω_ξ(σ_t x)=ω_ξ(x) when Δ^{it}ξ=ξ (fixed cyclic-separating vector). The
-- first state-coupled continuum modular theorem; generalizes FiniteModularTheory.modAut_stateOf_invariant.
#print axioms QIQTH.SpectralTheorem.modFlow_apply_eq_self_of_generator
-- expected: standard only — A ξ=0 ⇒ U(t)ξ=ξ (generator fixes ⇒ flow fixes; exp series via map_tsum).
#print axioms QIQTH.SpectralTheorem.modAut_vectorState_invariant_of_generator
-- expected: standard only — A ξ=0 ⇒ ω_ξ(σ_t x)=ω_ξ(x). Checkable (infinitesimal) form of invariance.
-- Layer 2: complex-time (entire-analytic) modular flow σ_z = Δ^{iz}
#print axioms QIQTH.SpectralTheorem.modFlowC_add
-- expected: standard only — U(w+z)=U(w)U(z) for all complex w,z (analytic continuation; bounded gen).
#print axioms QIQTH.SpectralTheorem.modFlowC_continuous
-- expected: standard only — U(z) entire in z.
#print axioms QIQTH.SpectralTheorem.modAutC_comp
-- expected: standard only — σ_w∘σ_z=σ_{w+z} for complex w,z.
#print axioms QIQTH.SpectralTheorem.modAutC_neg_I
-- expected: standard only — σ_{-i}(x)=Δ·x·exp(-A): imaginary-time conjugation = conjugation by Δ.
-- (Honest: the analytic infrastructure; the KMS *identity* needs the genuine modular Δ — Phase 3.)

-- Phase 3′ (Track B): Rieffel–Van Daele bounded modular construction on StandardSubspace
#print axioms QIQTH.StandardSubspaceModular.projK_idem
-- expected: standard only — P = orthogonal projection onto 𝒦 is idempotent.
#print axioms QIQTH.StandardSubspaceModular.rvdR_inner_self
-- expected: standard only — RvD Prop 2.2(1): ⟪Rξ,ξ⟫ = ‖Pξ‖²+‖Qξ‖² (engine for R injective).
#print axioms QIQTH.StandardSubspaceModular.rvdR_inner_self_nonneg
-- expected: standard only — 0 ≤ ⟪Rξ,ξ⟫ (R is a positive operator, RvD 0 ≤ R ≤ 2).
#print axioms QIQTH.StandardSubspaceModular.rvdR_injective
-- expected: standard only — RvD Prop 2.2(1): R=P+Q injective (Pξ=Qξ=0 ⟹ ξ⊥𝒦+i𝒦 dense
-- ⟹ ξ=0, via IsCyclic).  Makes the modular operator well-defined.
#print axioms QIQTH.StandardSubspaceModular.rvdPmQ_sq
-- expected: standard only — RvD Prop 2.2(2): (P−Q)² = P+Q−(PQ+QP) = R(2−R) (idempotent
-- algebra); whence T = R^½(2−R)^½ for the polar decomposition JT = P−Q.
#print axioms QIQTH.StandardSubspaceModular.rvdR_inner_self_le
-- expected: standard only — RvD 0 ≤ R ≤ 2 (upper half): ⟪Rξ,ξ⟫ ≤ 2‖ξ‖² (P,Q contractions).
#print axioms QIQTH.StandardSubspaceModular.rvdR_inner_symm
-- expected: standard only — R symmetric: ⟪Rx,y⟫=⟪x,Ry⟫ (P,Q self-adjoint). (Operator-level
-- star R = R is rvdR_isSelfAdjoint below — H→L[ℝ]H DOES carry adjoint/Star via open ClosedSubmodule.)
-- Operator-level adjoint structure (unblocking the polar decomposition; open ClosedSubmodule
-- supplies InnerProductSpace ℝ H ⇒ H→L[ℝ]H has adjoint/Star after all):
#print axioms QIQTH.StandardSubspaceModular.projK_isSelfAdjoint
-- expected: standard only — P self-adjoint as a bounded operator (star P = P).
#print axioms QIQTH.StandardSubspaceModular.rvdR_isSelfAdjoint
-- expected: standard only — R = P+Q self-adjoint.
#print axioms QIQTH.StandardSubspaceModular.rvdR_isPositive
-- expected: standard only — R positive (0≤R), licensing the CFC square root R^{1/2} of the RvD
-- polar decomposition T = R^{1/2}(2−R)^{1/2}.
#print axioms QIQTH.StandardSubspaceModular.rvdPmQ_isSelfAdjoint
-- expected: standard only — P−Q self-adjoint.
#print axioms QIQTH.StandardSubspaceModular.rvdPmQ_injective
-- expected: standard only — ★ D=P−Q INJECTIVE (Dξ=0 ⟹ Pξ=Qξ∈𝒦∩i𝒦=⊥ ⟹ Rξ=0 ⟹ ξ=0). Kernel-free D
-- ⟹ the modular conjugation J (of D=J·T) is a FULL involution J²=1 (J foundation).
#print axioms QIQTH.StandardSubspaceModular.rvdPmQ_commute_A
-- expected: standard only — D commutes with A=R(2−R)=T² (trivial: A=D², D·D²=D²·D). The inductive
-- BASE for D·T=T·D (D·√A=√A·D), which lifts by the closed real-commutant argument
-- ({Y|D∘Y=Y∘D} closed ℝ-*-subalgebra ⊇ elemental ℝ A ∋ √A) — DONE (see rvdPmQ_commute_rvdT).
#print axioms QIQTH.StandardSubspaceModular.rvdT_injective
-- expected: standard only — T injective (T²=D² inj since D inj). ⟹ range T dense ⟹ J:Tξ↦Dξ extends
-- to all of H (the dense-extension prerequisite for the modular conjugation J).
#print axioms QIQTH.StandardSubspaceModular.rvdR_le_two
-- expected: standard only — 2·1−R positive (R≤2). With rvdR_isPositive: full RvD bound 0≤R≤2, so
-- both R^{1/2} and (2−R)^{1/2} exist (the polar-decomposition factors T=R^{1/2}(2−R)^{1/2}).
-- ℂ-linearity of R (gateway to repackaging R as H→L[ℂ]H for the complex CFC √):
#print axioms QIQTH.StandardSubspaceModular.projIK_smul_I
-- expected: standard only — conjugation identity Q(i·ξ)=i·(Pξ) (Q=J·P·J⁻¹, J=mult-by-i), via the
-- variational characterization + mult-by-i is a real-orthogonal isometry.
#print axioms QIQTH.StandardSubspaceModular.rvdR_smul_I
-- expected: standard only — R(i·ξ)=i·(Rξ): R=P+Q is ℂ-linear (commutes with mult-by-i).
-- Rℂ : H→L[ℂ]H — the complex-linear repackaging of R, and its positivity:
#print axioms QIQTH.StandardSubspaceModular.rvdR_smul_complex
-- expected: standard only — R(c·x)=c·(Rx) ∀c:ℂ (full ℂ-map_smul, via c=c.re+c.im·i).
#print axioms QIQTH.StandardSubspaceModular.rvdRC_isSymmetric
-- expected: standard only — Rℂ complex-symmetric (Re from rvdR_inner_symm, Im via i-twist).
#print axioms QIQTH.StandardSubspaceModular.rvdRC_isPositive
-- expected: standard only — Rℂ is a positive operator in the complex C*-algebra H→L[ℂ]H.
#print axioms QIQTH.StandardSubspaceModular.rvdRC_nonneg
-- expected: standard only — 0≤Rℂ (Loewner). The hypothesis CFC.sqrt will consume; the sqrt itself
-- is blocked only on the missing Mathlib instance StarOrderedRing (H→L[ℂ]H) (flagged future work).
#print axioms QIQTH.StandardSubspaceModular.rvdPmQ_smul_I
-- expected: standard only — D=P−Q is conjugate-linear: D(i·ξ)=−i·(Dξ). The structural reason the
-- modular conjugation J (of J·T=P−Q) is antiunitary, in contrast to the ℂ-linear R.
-- The RvD square roots — UNBLOCKED: StarOrderedRing/CStarAlgebra (H→L[ℂ]H) have landed in Mathlib,
-- so CFC.sqrt now applies to Rℂ. The polar-decomposition factors R^{1/2}, (2−R)^{1/2}, T, and the
-- RvD Prop 2.2(2) identity T²=R(2−R):
#print axioms QIQTH.StandardSubspaceModular.rvdTwoSubRC_isPositive
-- expected: standard only — 0≤2−R (R≤2), the second positive factor; positivity transfers from the
-- ℝ-side rvdR_le_two by defeq of reApplyInnerSelf.
#print axioms QIQTH.StandardSubspaceModular.rvdSqrtR_mul_self
-- expected: standard only — R^{1/2}·R^{1/2}=R (CFC.sqrt_mul_sqrt_self on the positive Rℂ).
#print axioms QIQTH.StandardSubspaceModular.rvdRC_injective
-- expected: standard only — R=rvdRC INJECTIVE (toward √R-range density, the ξ=√Rζ reconciliation): from R(2−R)
-- injective (rvdRC_mul_rvdTwoSubRC_injective) via commute. R inj ⟹ √R inj (rvdSqrtR_mul_self) ⟹ √R DENSE RANGE in H
-- — the structural basis of lifting GConstancy from ξ=√Rζ to all 𝒦 (remaining: the √R-vectors-in-𝒦 dense in 𝒦).
#print axioms QIQTH.StandardSubspaceModular.rvdTwoSubRC_injective
-- expected: standard only — 2−R INJECTIVE (companion to rvdRC_injective): from R(2−R) inj, (2−R)a=(2−R)b ⇒ R(2−R)a=
-- R(2−R)b ⇒ a=b. So 2 not eigenvalue ⇒ E({2})=0. With R inj (E({0})=0): PVM({0,2})=0 ⇒ deviceOpC(−i/2)=√(2−R) a.e.
-- (the device-character endpoint atoms vanish) — toward (a1-end) of the bottom-edge KMS reality.
#print axioms QIQTH.StandardSubspaceModular.rvdSqrtTwoSubR_mul_self
-- expected: standard only — (2−R)^{1/2}·(2−R)^{1/2}=2−R.
#print axioms QIQTH.StandardSubspaceModular.rvdSqrtR_commute_rvdSqrtTwoSubR
-- expected: standard only — √R and √(2−R) commute (both functions of R, via Commute.cfcₙ_nnreal).
#print axioms QIQTH.StandardSubspaceModular.rvdT_sq
-- expected: standard only — RvD Prop 2.2(2): T²=R(2−R) for T=R^{1/2}(2−R)^{1/2}. The analytic heart
-- of the bounded-operator construction of the modular objects J and Δ.
-- The modular conjugation J: polar decomposition D=J·T, via the isometry ‖Tξ‖=‖Dξ‖:
#print axioms QIQTH.StandardSubspaceModular.rvdT_nonneg
-- expected: standard only — T=√R·√(2−R)≥0 (product of commuting positives, Commute.mul_nonneg).
#print axioms QIQTH.StandardSubspaceModular.rvdT_isSelfAdjoint
-- expected: standard only — T self-adjoint (it is positive).
#print axioms QIQTH.StandardSubspaceModular.rvdRC_mul_rvdTwoSubRC_apply
-- expected: standard only — T²=D² as maps: (R(2−R))ξ=(P−Q)((P−Q)ξ), both = Pξ+Qξ−P(Qξ)−Q(Pξ).
#print axioms QIQTH.StandardSubspaceModular.rvdT_norm_eq
-- expected: standard only — ★ THE modular-conjugation isometry ‖Tξ‖=‖Dξ‖ (RvD polar decomp D=J·T).
-- D=P−Q is antilinear, T=|D| its positive modulus; J:Tξ↦Dξ is thus a well-defined antiunitary.
-- RvD intertwiners (engine for both J²=1 via D·T=T·D, and modular-flow invariance U_t𝒦=𝒦 via D·U_t=U_t·D):
#print axioms QIQTH.StandardSubspaceModular.rvdPmQ_mul_rvdR
-- expected: standard only — D·R = (2−R)·D  (pure idempotent algebra).
#print axioms QIQTH.StandardSubspaceModular.rvdR_mul_rvdPmQ
-- expected: standard only — R·D = D·(2−R).
#print axioms QIQTH.StandardSubspaceModular.rvdPmQ_anticommute_rvdR_sub_one
-- expected: standard only — D·(R−1) = −(R−1)·D (D ANTIcommutes with R−1). Engine for the covariance
-- [U_t,D]=0: D antilinear + this ⟹ D commutes with i(R−1); U_t=u_t(R) is a fn of i(R−1) with
-- conj(u_t(2−r))=u_t(r). (Full covariance needs the Borel/vN-SOT lift — U_t discontinuous, not norm-elemental.)
-- ★★ THE CONTINUUM MODULAR FLOW Δ^{it}=u_t(R) via bounded BOREL FC (continuous cfc cannot reach it):
#print axioms QIQTH.StandardSubspaceModular.modChar_norm
-- expected: standard only — ‖u_t(r)‖=1 (the modular character is unimodular).
#print axioms QIQTH.StandardSubspaceModular.borelFC_adjoint
-- expected: standard only — f(T)⋆=(conj f)(T) (adjoint of the bounded Borel FC, via bilinDiag_conj_symm).
#print axioms QIQTH.StandardSubspaceModular.modUnitary_zero
-- expected: standard only — U_0 = 1.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_add
-- expected: standard only — U_{s+t} = U_s·U_t (group law, via borelFC_mul + u_{s+t}=u_s·u_t).
#print axioms QIQTH.StandardSubspaceModular.modUnitary_adjoint
-- expected: standard only — U_t⋆ = U_{-t}.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_unitary
-- expected: standard only — ★ U_t is UNITARY: the continuum one-parameter modular unitary group
-- Δ^{it} of a standard subspace (one-particle level; NOT yet second-quantized free-field Γ(Δ^{it})).
#print axioms QIQTH.StandardSubspaceModular.modUnitary_norm
-- expected: standard only — U_t is an isometry (‖U_t ξ‖=‖ξ‖).
#print axioms QIQTH.StandardSubspaceModular.inner_modUnitary_modUnitary
-- expected: standard only — cocycle inner identity ⟪U_a ξ, U_b ξ⟫=⟪ξ, U_{b−a} ξ⟫.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_stronglyContinuous
-- expected: standard only — ★★ STRONG continuity t↦U_t ξ. So Δ^{it} is a STRONGLY CONTINUOUS
-- one-parameter unitary group — the full textbook modular flow (norm continuity fails near endpoints;
-- proved via sequential criterion + bounded-Borel-FC dominated convergence).
-- Toward U_t𝒦=𝒦: structural reduction P=½(R+D) ⟹ [U_t,P]=0 from [U_t,R]=0 ∧ [U_t,D]=0:
#print axioms QIQTH.StandardSubspaceModular.rvdR_add_rvdPmQ_eq
-- expected: standard only — R+D=2P (RvD P=½(R+D)), pure projection algebra.
#print axioms QIQTH.StandardSubspaceModular.mem_K_iff_projK
-- expected: standard only — ξ∈𝒦 ↔ Pξ=ξ.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_commute_projK_of
-- expected: standard only — [U_t,P]=0 reduced to [U_t,R]=0 ∧ [U_t,D]=0 via P=½(R+D).
#print axioms QIQTH.StandardSubspaceModular.modUnitary_mapsTo_K_of_commute
-- expected: standard only — CONDITIONAL U_t𝒦⊆𝒦 given the two commutators. The remaining obligations:
-- [U_t,R]=0 (reachable, R=borelFC(id) via polarizing inner_cfcHom_polarization) and the COVARIANCE
-- [U_t,D]=0 (D antilinear conjugates spec(R) by r↦2−r; the genuine frontier, no Mathlib infra).
#print axioms QIQTH.StandardSubspaceModular.modUnitary_commute_specProj
-- expected: standard only — ★ U_t commutes with EVERY spectral projection E(s) of R (both are
-- borelFC values; multiplicative + u_t·𝟙_s=𝟙_s·u_t). So Δ^{it} ∈ vN(R) — the operator-level statement
-- that the modular flow is a function of R (unconditional; [U_t,R]=0 then needs only R=∫λ dE).
#print axioms QIQTH.StandardSubspaceModular.scalarMeasure_eq_specMeasure
-- expected: standard only — bridge scalarMeasure(PVM_of_selfAdjoint)=specMeasure (‖E(s)x‖²=qForm via
-- E projection). Connects the bounded-Borel-FC layer (diagInt/bilinDiag) to re_inner_T_eq_integral;
-- the keystone toward R=∫λ dE (R=borelFC(id)) hence the literal pointwise [U_t,R]=0.
-- ★★ THE LITERAL [U_t,R]=0 — obligation (R) of 𝒦-invariance, FULLY DISCHARGED:
#print axioms QIQTH.StandardSubspaceModular.rvdRC_eq_borelFC
-- expected: standard only — R = borelFC(coord) = ∫λ dE, the OPERATOR spectral theorem for R, via
-- diagInt(coord)=⟪·,R·⟫ (the bridge) + the 4-term polarization.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_commute_rvdRC
-- expected: standard only — ★ [U_t,R]=0 operator form (U_t=Φ(u_t), R=Φ(coord), borelFC_comm).
#print axioms QIQTH.StandardSubspaceModular.modUnitary_commute_rvdR
-- expected: standard only — [U_t,R]=0 pointwise: U_t(Rξ)=R(U_t ξ).
#print axioms QIQTH.StandardSubspaceModular.modUnitary_mapsTo_K_of_commute_D
-- expected: standard only — ★ U_t𝒦⊆𝒦 now needs ONLY the covariance [U_t,D]=0 (obligation R discharged).
-- The single remaining gate to full standard-subspace invariance is the antilinear covariance.
-- ★★★ THE ANTILINEAR-CFC COMMUTATION D·T=T·D — the J²=1 keystone, FULLY PROVEN:
#print axioms QIQTH.StandardSubspaceModular.restrictScalars_star
-- expected: standard only — ℂ-adjoint-restricted = ℝ-adjoint (no Mathlib lemma; by ext_inner).
#print axioms QIQTH.StandardSubspaceModular.commute_of_mem_elemental
-- expected: standard only — D (self-adj ℝ-op) commuting with B commutes with all of elemental ℝ B
-- (the closed real *-subalgebra realCommutant, via StarAlgebra.elemental.le_of_mem).
#print axioms QIQTH.StandardSubspaceModular.sqrt_mem_elemental
-- expected: standard only — CFC.sqrt B ∈ elemental ℝ B (CFC.sqrt=cfcₙ Real.sqrt=cfc Real.sqrt).
#print axioms QIQTH.StandardSubspaceModular.rvdPmQ_commute_rvdT
-- expected: standard only — ★★★ D·T = T·D. The antilinear modular conjugation D commutes with the
-- positive modulus T=√(R(2−R)). Applied to A=T² (D·A=A·D trivial) ⟹ D commutes with √A=T. This is
-- THE keystone: J=D·T⁻¹ self-adjoint ⟹ J²=1; same machinery gives the covariance [U_t,D]=0.
-- ★ THE MODULAR CONJUGATION J — constructed as a bounded ℝ-linear isometry (J²=1 perf-blocked, see file):
#print axioms QIQTH.StandardSubspaceModular.rvdT_restrictScalars_denseRange
-- expected: standard only — range T dense ((range T)ᗮ=ker T=⊥, T inj self-adj).
#print axioms QIQTH.StandardSubspaceModular.modConj
-- expected: standard only — J = LinearMap.extendOfNorm of Tξ↦Dξ (the modular conjugation).
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdT
-- expected: standard only — J(Tξ) = Dξ (D = J·T, the polar decomposition).
#print axioms QIQTH.StandardSubspaceModular.modConj_norm
-- expected: standard only — ‖Jη‖=‖η‖ (J isometric, by density from ‖Tξ‖=‖Dξ‖).
#print axioms QIQTH.StandardSubspaceModular.modConj_inner_map
-- expected: standard only — ⟪Jη,Jζ⟫=⟪η,ζ⟫ (J inner-preserving).
#print axioms QIQTH.StandardSubspaceModular.modConj_isSelfAdjoint
-- expected: standard only — J self-adjoint ⟪Jη,ζ⟫=⟪η,Jζ⟫ (density from D·T=T·D; fast symmetry via
-- ℂ-self-adjoint+re for T and projection symmetry for D, avoiding the scoped-ℝ adjoint perf wall).
#print axioms QIQTH.StandardSubspaceModular.modConj_sq
-- expected: standard only — ★★ J² = 1. THE MODULAR CONJUGATION IS A FULL ANTIUNITARY INVOLUTION.
-- Tomita–Takesaki S=JΔ^{1/2} complete at the one-particle level: Δ^{it} (strongly cts unitary group)
-- + J (J²=1) both axiom-free for a standard subspace.
#print axioms QIQTH.StandardSubspaceModular.cfcΩ_intertwine
-- expected: standard only — ★ the antilinear continuous-FC Stone–Weierstrass intertwiner
-- D·f(R) = conj(f(2−·))(R)·D for EVERY continuous f. The heart of the covariance.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_commute_rvdPmQ
-- expected: standard only — ★★ the modular COVARIANCE [U_t, D] = 0 (U_t commutes with the antilinear
-- D=P−Q). Via the intertwiner at the θ-fixed damped fn hΩ=u_t·r(2−r), D·A=A·D, cancel A by dense range.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_mapsTo_K
-- expected: standard only — ★★★ FULL standard-subspace invariance U_t 𝒦 ⊆ 𝒦. Both obligations
-- ([U_t,R]=0 and [U_t,D]=0) discharged: the continuum modular flow preserves the standard subspace.
#print axioms QIQTH.StandardSubspaceModular.modConj_commute_modUnitary
-- expected: standard only — ★ J Δ^{it} = Δ^{it} J (modular conjugation commutes with the flow), a
-- canonical TT relation. UNBLOCKED by [U_t,D]=0: D=J·T, U_t commutes both D and T (via Commute.cfcₙ_nnreal),
-- so J commutes U_t on dense range T.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_mem_K_iff
-- expected: standard only — ★★★ Δ^{it} 𝒦 = 𝒦 (membership iff): the modular flow preserves the standard
-- subspace BOTH ways. Inclusion U_t𝒦⊆𝒦 + group law (U_{-t} inverse) ⟹ U_t ξ ∈ 𝒦 ↔ ξ ∈ 𝒦.

-- Finite-dimensional Tomita–Takesaki (the modular engine)
#print axioms QIQTH.FiniteModularTheory.modAut_mul
-- expected: standard only — σ_t is a *-endomorphism (⅟m * m cancels)
#print axioms QIQTH.FiniteModularTheory.modAut_comp
-- expected: standard only — one-parameter group law σ_s∘σ_t = σ_{s+t}
#print axioms QIQTH.FiniteModularTheory.kms_condition
-- expected: standard only — KMS boundary identity from trace cyclicity.
#print axioms QIQTH.FiniteModularTheory.modAut_stateOf_invariant
-- expected: standard only — modular flow preserves its state (finite Tomita; Stage 3.2 shadow).
#print axioms QIQTH.SpectralPVM.specProj_sum_eq_one
-- expected: standard only — spectral PVM resolution of identity (∑ eigenprojections = 1; Stage 3.1).
#print axioms QIQTH.SpectralPVM.specProj_orthogonal
-- expected: standard only — distinct spectral eigenprojections are orthogonal.
#print axioms QIQTH.FiniteModularTheory.sigmaDiag_comp
-- expected: standard only — the GENUINE real-time modular flow's
-- one-parameter group law σ_s∘σ_t=σ_{s+t} (diagonal case), via cpow_add.
#print axioms QIQTH.FiniteModularTheory.diagPow_mul
-- expected: standard only — (p i)^{is}·(p i)^{it} = (p i)^{i(s+t)}.

-- LambdaPointer.lean — λ's pointer law, finite (Type I) shadow of Takesaki's
-- conditional-expectation criterion (2026-06-15; the Type-III-native redirect).
#print axioms QIQTH.LambdaPointer.modAut_fixes_iff_commute
-- expected: standard only — finite Takesaki criterion σ(P)=P ⟺ [ρ,P]=0 (exact decoherence).
#print axioms QIQTH.LambdaPointer.bornWeights_sum
-- expected: standard only — algebraic Born weights ω(Pₐ)=tr(ρPₐ) sum to tr ρ (a probability).
#print axioms QIQTH.LambdaPointer.dephase_preserves_state
-- expected: standard only — dephasing E(x)=Σ Pₐ x Pₐ is the ω-preserving conditional expectation when [ρ,Pₐ]=0.
#print axioms QIQTH.LambdaPointer.dephase_one
-- expected: standard only — the dephasing conditional expectation is unital, E(1)=1.
#print axioms QIQTH.LambdaPointer.dephase_modAut_commute
-- expected: standard only — PERSISTENCE: E∘σ=σ∘E, the decoherence map commutes with the modular flow (static→dynamical).
#print axioms QIQTH.LambdaPointer.modAut_fixes_pointer
-- expected: standard only — each selected record is a fixed point of the modular flow.
#print axioms QIQTH.LambdaPointer.bornWeight_modAut_invariant
-- expected: standard only — Born weights are constants of the modular motion (KMS invariance).
#print axioms QIQTH.LambdaPointer.dephase_sigmaDiag_commute
-- expected: standard only — REAL-TIME persistence ∀t: E commutes with the genuine one-parameter modular flow σ_t.
#print axioms QIQTH.LambdaPointer.dephase_sigmaDiag_commute_diagonal
-- expected: standard only — unconditional real-time persistence in the einselected (diagonal) pointer basis, ∀t.

-- WeakStrongSplit.lean — weak/strong decomposition of state-supervenience (2026-06-15).
#print axioms QIQTH.WeakStrongSplit.weight_naturality
-- expected: standard only — WEAK premise (naturality) holds for every f, hence is f-blind: cannot force Born.
#print axioms QIQTH.WeakStrongSplit.weak_underdetermines_born
-- expected: standard only — the α-family (id vs (·)²) witnesses weak ⇏ Born (disagree at p=(3/4,1/4)).
#print axioms QIQTH.WeakStrongSplit.sq_not_refinementAdditive
-- expected: standard only — STRONG premise (refinement-additivity) discriminates Born from the α-family witness.
#print axioms QIQTH.WeakStrongSplit.refinementAdditive_nsmul
-- expected: standard only — refinement-additivity linearizes f(n·x)=n·f(x): the mechanism selecting Born.

-- SelectionEvent.lean — λ's selection-event constructor (inverse-CDF; 2026-06-15).
#print axioms QIQTH.SelectionEvent.selects_exists_unique
-- expected: standard only — EXACTLY ONE record per actuality seed (single-world: not zero, not two).
#print axioms QIQTH.SelectionEvent.volume_selects
-- expected: standard only — uniform seed measure of record k = its Born weight (selection realizes Born frequency).

-- FiniteInfoLambda.lean — ONE finite inverse-CDF sampler (correct arithmetic; physical interpretation RETRACTED, see header).
#print axioms QIQTH.FiniteInfoLambda.gridWeight_sum
-- expected: standard only — the grid weights are a probability on the k/N lattice.
#print axioms QIQTH.FiniteInfoLambda.gridWeight_near_born
-- expected: standard only — lattice rounding error |gridWeight − pₐ| < 1/N (not a physical Born deviation).
#print axioms QIQTH.FiniteInfoLambda.gridWeight_tendsto_born
-- expected: standard only — gridWeight → pₐ as N→∞.
#print axioms QIQTH.FiniteInfoLambda.resolution_floor
-- expected: standard only — for SOME ordering/N a positive-weight record gets 0 cells (ordering-dependent, not a threshold).

-- FiniteIndexLambda.lean — the SURVIVING finite-info λ (finite index, exact Born) + the dividing line.
#print axioms QIQTH.FiniteIndexLambda.indexWeight_marginal
-- expected: standard only — the finite-INDEX law preserves marginals (no-signaling-transparent).
#print axioms QIQTH.FiniteIndexLambda.grid_breaks_envariance
-- expected: standard only — the GRID law breaks envariance ((1/3,1/3,1/3) N=2 → (1/2,1/2,0)).
#print axioms QIQTH.FiniteIndexLambda.grid_breaks_no_signaling
-- expected: standard only — the GRID law breaks no-signaling (same Born marginal, different grid marginal: order-1/N signal).

-- TinyUniverse.lean — (Φ,λ) in a very limited information space (one-bit universe + statistical emergence).
#print axioms QIQTH.TinyUniverse.oneBit_grid_distorts
-- expected: standard only — one-bit universe: index keeps (1/3,2/3) exact; grid forces (1/2,1/2) at N=2.
#print axioms QIQTH.TinyUniverse.born_finite_sample_bound
-- expected: standard only — Born as finite-sample typicality: Pr(|p̂−p|≥ε) ≤ 1/(4Kε²).
#print axioms QIQTH.TinyUniverse.statistical_emergence
-- expected: standard only — the bound 1/(4Kε²) → 0 as K→∞ (statistical Born emerges in the large-info limit).
#print axioms QIQTH.TinyUniverse.qubitBorn_eq_oneBitBorn
-- expected: standard only — λ ENFORCES Φ: the single-bit weights are the squared amplitudes of a qubit (p = ‖Φ 0‖², not free).
#print axioms QIQTH.TinyUniverse.phi_eq_superposition
-- expected: standard only — the bit names the actual world: Φ = ∑ k, Φ k • e_k, λ selects one of the records composing Φ.

-- TwoBitUniverse.lean — (Φ,λ) at two bits: entanglement + marginal/no-signaling structure.
#print axioms QIQTH.TwoBitUniverse.product_independent
-- expected: standard only — product (unentangled) Φ: the two bits are independent, joint Born = product of marginals.
#print axioms QIQTH.TwoBitUniverse.bell_correlated
-- expected: standard only — entangled Bell Φ: uniform marginals (½) yet joint ≠ product (P(0,1)=0 ≠ ¼): genuine correlation.
#print axioms QIQTH.TwoBitUniverse.bell_perfect_correlation
-- expected: standard only — the Bell bits are never unequal (P(a,b)=0 for a≠b): knowing λ_A fixes λ_B.
#print axioms QIQTH.TwoBitUniverse.coarse_is_oneBit
-- expected: standard only — ONE bit in a two-qubit world: a binary coarse-graining; the coarse law IS a one-bit universe.
#print axioms QIQTH.TwoBitUniverse.bell_parity_zero
-- expected: standard only — entanglement makes the parity bit DEFINITE (2‖c‖²=1 on aligned block); a local bit on the same Φ is uniform.

-- ThreeQubitUniverse.lean — 8-record world with 1/2/3 bits: resolution hierarchy + GHZ entropy ceiling.
#print axioms QIQTH.ThreeQubitUniverse.blockBorn_full_eq_triBorn
-- expected: standard only — 3 bits = full resolution: the 2^k-block coarse law collapses to the per-record Born law.
#print axioms QIQTH.ThreeQubitUniverse.ghz_supported_on_diagonal
-- expected: standard only — GHZ lives in 8 records but only 2 carry weight (000/111): Born entropy 1 bit, not log(dim)=3.
#print axioms QIQTH.ThreeQubitUniverse.ghz_2bit_collapse
-- expected: standard only — 2 bits don't separate GHZ's A,B (the A≠B block has weight 0): extra budget is slack.

-- RecordContract.lean — the (Φ,λ) record/area CONTRACT (labeled scaffold; postulates as hypotheses, no axioms).
#print axioms QIQTH.RecordContract.coarsen_sum
-- expected: standard only — coarse-graining pushes the record law forward to a probability (blocks partition records).
#print axioms QIQTH.RecordContract.coarsen_card_le
-- expected: standard only — capacity non-increasing under coarse-graining: |coarse records| ≤ |fine records|.
#print axioms QIQTH.RecordContract.area_entropy_bridge
-- expected: standard only — area bridge (entropy version): I(λ;R) ≤ H(R) ≤ S_area threads the Bousso postulate.
#print axioms QIQTH.RecordContract.area_capacity_bridge
-- expected: standard only — area bridge (capacity version): I(λ;R) ≤ log|R| ≤ S_area, the STRONGER dim postulate (≠ Bousso).
#print axioms QIQTH.RecordContract.shannon_le_log_card
-- expected: standard only — the info bound H(R) ≤ log|R| (Gibbs/Jensen on concave negMulLog): discharges hinfo concretely.
#print axioms QIQTH.RecordContract.shannon_uniform_eq_log_card
#print axioms QIQTH.RecordContract.shannon_eq_area_at_saturation
-- expected: standard only — ★ CAPACITY SATURATION (the entropy-area EQUALITY). shannon_uniform_eq_log_card:
-- H(R)=log|R| at the uniform/maximally-mixed record (Jensen bound SATURATED; ∑negMulLog(1/n)=log n) — the
-- equilibrium regime Jacobson assumes. shannon_eq_area_at_saturation: + the holographic capacity postulate
-- log|R|=S_area (record dim = e^{area}, Q_R∝A) ⟹ H(R)=S_area. DECOMPOSES the area-law postulate into (i)
-- maximum-entropy/equilibrium — which QIQT-H's finite-record structure DERIVES (the saturation), and (ii)
-- capacity=area — the one genuinely-holographic input still postulated. So the entropy half of S=ηA is QIQT-H's
-- saturation; only log|R|=S_area is irreducibly assumed. Feeds the hAreaLaw premise of jacobson_einstein_from_area_law.

-- BornProjBridge.lean — Born FROM PROJECTORS: μ(r)=‖P_r Φ‖²=⟨Φ,P_rΦ⟩ is a RecordContract.RecordLaw.
#print axioms QIQTH.BornProjBridge.bornProj_sum
-- expected: standard only — ∑_r ‖P_r Φ‖² = ‖Φ‖² = 1 for a normalized Φ over a finite orthogonal PVM (∑ P_r = 1).
#print axioms QIQTH.BornProjBridge.bornRecordLaw
-- expected: standard only — the bridge: Born-from-projectors weights form a genuine RecordLaw (contract rests on Born-from-Φ).
#print axioms QIQTH.RecordContract.eventProb_le_one
-- expected: standard only — the selector's event measure IS the Born measure (a genuine probability ≤ 1): λ's whole empirical content.

-- SymmetryNoGo.lean — symmetry cannot select a preferred framework (the metaselector must be einselection).
#print axioms QIQTH.SymmetryNoGo.invariant_of_pretransitive_constant
-- expected: NO axioms at all — a transitive group action makes any invariant score constant (selects nothing).
#print axioms QIQTH.SymmetryNoGo.unitary_invariant_score_constant
-- expected: standard only — THE NO-GO: unitary group transitive on frameworks ⇒ any unitarily-invariant score is constant.
#print axioms QIQTH.SymmetryNoGo.exists_unitary_map
-- expected: standard only — any two orthonormal bases (frameworks) are related by a unitary: the framework space is one orbit.

-- MetaselectorSelection.lean — the POSITIVE selector (einselection) + the finite-budget overlap floor.
#print axioms QIQTH.MetaselectorSelection.pointer_commutes
-- expected: standard only — Zurek criterion: a record commuting with monitored A commutes with the interaction A⊗B (einselected).
#print axioms QIQTH.MetaselectorSelection.pointer_invariant
-- expected: standard only — an A-eigenstate stays a PRODUCT under A⊗B coupling: pointer states are decoherence-free.
#print axioms QIQTH.MetaselectorSelection.finite_budget_forces_overlap
-- expected: standard only — a D-dim record space cannot hold M>D orthonormal records: finite budget forces overlap (interference floor).

-- StateAloneNoGo.lean — a state alone selects only the trivial framework (completes the no-go trilogy).
#print axioms QIQTH.StateAloneNoGo.state_records_trivial
-- expected: standard only — a single projection P=|Φ⟩⟨Φ| generates only {0,P,1−P,1}: Φ alone selects no finer framework.

-- ContinuumLambda.lean — Stage 1 of the continuum λ-law (2026-06-15): on the genuine RvD Δ^{it} flow.
#print axioms QIQTH.ContinuumLambda.modAutOp_add
-- expected: standard only — modular automorphism σ_t = Ad(Δ^{it}) is a one-parameter group.
#print axioms QIQTH.ContinuumLambda.modAutOp_fixes_iff_commute
-- expected: standard only — continuum Takesaki criterion σ_t(A)=A ⟺ A commutes with Δ^{it}.
#print axioms QIQTH.ContinuumLambda.modAutOp_fixes_specProj
-- expected: standard only — spectral pointer projections are fixed by the continuum modular flow ∀t.
#print axioms QIQTH.ContinuumLambda.dephaseOp_specProj_commute
-- expected: standard only — CONTINUUM PERSISTENCE: decoherence map commutes with σ_t ∀t (spectral pointers, unconditional).

-- NaturalConeBorn.lean — Stage 2 of the continuum λ-law: the Type-independent algebraic Born rule.
#print axioms QIQTH.NaturalConeBorn.bornWeights_sum
-- expected: standard only — spectral-measure Born weights over a partition sum to ‖ξ‖² (a genuine probability, no trace).
#print axioms QIQTH.NaturalConeBorn.modBornWeights_sum_unit
-- expected: standard only — continuum modular pointer Born weights are a probability (unit state).

-- ContinuumSelection.lean — Stage 3 of the continuum λ-law: the (Type-blind) selection event.
#print axioms QIQTH.ContinuumSelection.continuum_selects_exists_unique
-- expected: standard only — exactly one record per seed, driven by the continuum Born weights.
#print axioms QIQTH.ContinuumSelection.continuum_volume_selects
-- expected: standard only — uniform seed measure of record k = its continuum Born weight (realizes Born).

-- ContinuumLambdaFock.lean — Stage 4 capstone foundation: Γ(Δ^{it}) at the Fock level.
#print axioms QIQTH.Fock.secondQuantModFlowH_bijective
-- expected: standard only — the free-field modular flow is a bijective isometry (vector-level unitarity).
#print axioms QIQTH.Fock.secondQuantModFlowH_weyl_fixed
-- expected: standard only — Γ-level persistence: Weyl records on modular-fixed modes commute with Γ(Δ^{it}).

-- SecondQuantCLM.lean — Γ(Δ^{it}) as a bounded operator (the field-level Ad-persistence substrate).
#print axioms QIQTH.Fock.secondQuantModCLM_apply
-- expected: standard only — the bounded operator Γ(Δ^{it}) agrees with the function secondQuantModFlowH.
#print axioms QIQTH.Fock.secondQuantModCLM_mul
-- expected: standard only — Γ(Δ^{it}) is a one-parameter group of bounded operators on Fock.
#print axioms QIQTH.Fock.secondQuantModCLM_adjoint
-- expected: standard only — Γ(Δ^{it})⋆ = Γ(Δ^{-it}) (the adjoint is the inverse flow).
#print axioms QIQTH.Fock.secondQuantModCLM_unitary
-- expected: standard only — Γ(Δ^{it}) is UNITARY on the Fock Hilbert space (the free-field modular unitary group).

-- ContinuumLambdaField.lean — the continuum λ-persistence at the genuine free-field level.
#print axioms QIQTH.Fock.modAutFock_fixes_iff_commute
-- expected: standard only — field-level Takesaki criterion: σ_t(A)=A ⟺ A commutes with Γ(Δ^{it}).
#print axioms QIQTH.Fock.dephaseFock_modAutFock_commute
-- expected: standard only — FIELD-LEVEL PERSISTENCE: decoherence map commutes with σ_t=Ad(Γ(Δ^{it})) ∀t.

-- FieldBorn.lean — the Born rule at the genuine free-field level (Fock vacuum state).
#print axioms QIQTH.Fock.vacuumState_povm_sum
-- expected: standard only — vacuum-state weights of a POVM sum to 1 (field-level Born probability).
#print axioms QIQTH.Fock.vacuumState_weylBit_sum
-- expected: standard only — the Weyl-bit record POVM's vacuum-state weights are a probability (free-field two-outcome Born).

-- FieldSelection.lean — the selection event at the genuine free-field level.
#print axioms QIQTH.Fock.field_selects_exists_unique
-- expected: standard only — exactly one Weyl-bit record per seed, driven by the Fock-vacuum-state Born weights.
#print axioms QIQTH.Fock.field_volume_selects
-- expected: standard only — uniform seed measure of a record = its free-field Born weight (realizes Born).

-- Free-field finite-mode instance (a, b, c)
#print axioms QIQTH.FreeFieldRecord.holographic_bound
-- expected: standard only — (a) N free-fermion modes ⇒ log₂ #Atoms = N ≤ Q_R
#print axioms QIQTH.FreeFieldRecord.decoherence_decay
-- expected: standard only — (b) Gaussian overlap e^{-cN} → 0 as N → ∞
#print axioms QIQTH.FreeFieldRecord.boost_comp
-- expected: standard only — (c) finite-mode Lorentz action group law
#print axioms QIQTH.FreeFieldRecord.boost_bijective
-- expected: standard only — (c) each boost is a record-sector bijection
#print axioms QIQTH.FreeFieldRecord.recordOverlap_le_pow
-- expected: standard only — (b′) the SUBSTANTIVE content: the factorized
-- environment overlap |⟨E_α|E_β⟩| = |∏ mode overlaps| ≤ q^(#differing modes).
#print axioms QIQTH.FreeFieldRecord.recordOverlap_tendsto_zero
-- expected: standard only — (b′) derived q^N → 0 decay from the mode product.

-- Gleason-route μ construction (Open Problem 1).  NOTE: the earlier FALSE
-- axiom `effect_gleason_representation` was RETIRED (2nd GPT-5.5-pro review);
-- this module now adds NO project axiom — every theorem below is standard-only.
#print axioms QIQTH.GleasonSelector.naive_gleason_premises_insufficient
-- expected: standard only — PROVED red-team: positivity-free premises do NOT
-- force Born (Fin 2 counterexample). Soundness check.
#print axioms QIQTH.GleasonSelector.rankOne_sandwich
-- expected: standard only — |ψ⟩⟨ψ| E |ψ⟩⟨ψ| = ⟨ψ|E|ψ⟩ • |ψ⟩⟨ψ| (no hψ).
#print axioms QIQTH.GleasonSelector.born_is_forced
-- expected: standard ONLY — Born FORCED from linearity + ray-support +
-- ray-certainty.  No project axiom (the false axiom is gone).
#print axioms QIQTH.GleasonSelector.positive_functional_hermitian
-- expected: standard ONLY — a positive functional is a *-functional, PROVED by
-- polarization (was a named axiom; now discharged).
#print axioms QIQTH.GleasonSelector.quadratic_nonneg_forall_linear_zero
-- expected: standard only — the real-quadratic null core (PROVED).
#print axioms QIQTH.GleasonSelector.psd_null_radical
-- expected: standard ONLY — Cauchy–Schwarz null-radical, PROVED (was an axiom;
-- now discharged via the real-quadratic discriminant at c=t and c=it).
#print axioms QIQTH.GleasonSelector.support_of_positive_certain
-- expected: standard ONLY — the genuine Gleason bridge: positivity + certainty
-- ⇒ ray-support, fully proved (no project axiom).
#print axioms QIQTH.GleasonSelector.positive_ray_certain_forces_born
-- expected: standard ONLY — THE CAPSTONE: Born follows from POSITIVITY +
-- normalization + ray-certainty, with NO project axiom. The finite-dim
-- Gleason result, complete.
#print axioms QIQTH.GleasonSelector.history_measure_is_born
-- expected: standard only — μ on a decoherent record family = Born weights.
#print axioms QIQTH.GleasonSelector.history_measure_total
-- expected: standard only — the record measure is normalized to 1.
#print axioms QIQTH.GleasonSelector.no_signaling_marginal
-- expected: standard ONLY — requirement (2) honest form: one functional gives
-- spacelike-marginal independence for all Bob settings (no per-experiment
-- tuning).

-- QIQT-H CORE: single-outcome-without-collapse (the load-bearing theorem).
#print axioms QIQTH.CoreNoCollapse.coactual_subsingleton
-- expected: standard only — finite capacity ⇒ ≤1 coactual record (NON-CIRCULAR core).
#print axioms QIQTH.CoreNoCollapse.exactly_one_actual
-- expected: standard only — capacity + selector ⇒ EXACTLY ONE actual record.
#print axioms QIQTH.CoreNoCollapse.qiqth_single_outcome_no_collapse
-- expected: standard only — ∃! actual record, no collapse postulate.
#print axioms QIQTH.CoreNoCollapse.active_macroscopic_subsingleton
-- expected: standard only — ≤1 MACROSCOPIC active record (small records may coexist; no fiat).
#print axioms QIQTH.SBSBridge.unique_objective_record
-- expected: standard only — honest form: ∃! OBJECTIVE (redundant) active record; small ones coexist.
#print axioms QIQTH.SBSBridge.ObjectivityWitness.storage_ge
-- expected: standard only — (E) operational objectivity ⇒ macroscopic storage (redundancy DERIVED).
#print axioms QIQTH.SBSBridge.overlap_amplifies
-- expected: standard only — (#5) block overlap = ∏ per-collision overlaps ≤ γ^L (amplification).
#print axioms QIQTH.SBSBridge.block_overlap_tendsto_zero
-- expected: standard only — γ<1 ⇒ γ^L → 0: distinguishability amplified exponentially.
#print axioms QIQTH.SBSBridge.overlap_block_zero
-- expected: standard only — one perfect collision ⇒ block branches orthogonal (exact record).
#print axioms QIQTH.SBSBridge.linearIndependent_of_near_orthonormal
-- expected: standard only — near-orthonormal (overlap < 1/(n-1)) ⇒ linearly independent.
#print axioms QIQTH.SBSBridge.fragment_finrank_ge_approx
-- expected: standard only — APPROXIMATE δ-decoding: imperfect distinguishability still ⇒ dim ≥ n.
#print axioms QIQTH.CoreNoCollapse.FinPVM.weight_sum_eq_one
-- expected: standard only — Born normalisation ∑‖E r ψ‖²=1 (genuine resolution of identity).
#print axioms QIQTH.CoreNoCollapse.FinPVM.condProb_eq_born_postState
-- expected: standard only — collapse=conditionalization: condProb = Born on Lüders post-state.
#print axioms QIQTH.CoreNoCollapse.FinPVM.joint_eq_weight_mul_cond
-- expected: standard only — sequential Born = weight × conditional (chain rule).
#print axioms QIQTH.CoreNoCollapse.pair_exceeds_of_cost_gt_half
-- expected: standard only — cost_gt_half ⇒ the honest exact premise Qmax < cost r + cost s.
#print axioms QIQTH.CoreNoCollapse.joint_coactual_subsingleton
-- expected: standard only — SUBADDITIVITY-robust exclusion (monotone jointCost + pairwise overflow)
#print axioms QIQTH.CoreNoCollapse.coactual_subsingleton_via_joint
-- expected: standard only — additive core reproduced from the subadditive one
#print axioms QIQTH.CoreNoCollapse.qiqth_single_outcome_joint
-- expected: standard only — single-outcome capstone with NO additivity assumed

-- QIQT-H CAPACITY MODEL: the finite-capacity bound DERIVED (not assumed).
#print axioms QIQTH.CapacityModel.orthonormal_card_le_finrank
-- expected: standard only — #records ≤ finrank (raw capacity fact, Strasberg).
#print axioms QIQTH.CapacityModel.capacity_total
-- expected: standard only — ∑ recDim ≤ D (capacity additive + bounded, DERIVED).
#print axioms QIQTH.CapacityModel.macroscopic_subsingleton
-- expected: standard only — ≤1 macroscopic record (saturation premise now a THEOREM).
#print axioms QIQTH.CapacityModel.capacity_exactly_one
-- expected: standard only — capacity + selector ⇒ EXACTLY ONE macroscopic record.

-- QIQT-H ORTHOGONAL CAPACITY: pairwise overflow DERIVED from orthogonality (subadditive).
#print axioms QIQTH.OrthogonalCapacity.jointCost_mono
-- expected: standard only — span-dimension joint cost is monotone
#print axioms QIQTH.OrthogonalCapacity.pair_exceeds
-- expected: standard only — pairwise overflow DERIVED from orthogonality + macroscopicity
#print axioms QIQTH.OrthogonalCapacity.orthogonal_single_outcome
-- expected: standard only — single-outcome with pair_exceeds grounded in distinguishability
#print axioms QIQTH.OrthogonalCapacity.witness
-- expected: standard only — concrete 2-record orthogonal witness (non-vacuity)

-- QIQT-H PRIZE BRIDGE C1: one actual RECORD → one actual VALUE.
#print axioms QIQTH.PointerValue.ValueSelection.active_value_eq
-- expected: standard only — all coactual records share one pointer value
#print axioms QIQTH.PointerValue.ValueSelection.existsUnique_actualValue
-- expected: standard only — EXACTLY ONE actual pointer value (value-level single outcome)
#print axioms QIQTH.PointerValue.existsUnique_actualHistory
-- expected: standard only — unique actual pointer-value history over n trials

-- QIQT-H PRIZE BRIDGE C2: one-site Born (vector valuation = Born weight).
#print axioms QIQTH.OneSiteBorn.vectorState_eq_weight
-- expected: standard only — ν_ψ(Eᵣ) = ‖Eᵣψ‖² = weight (one-site Born calibration)
#print axioms QIQTH.OneSiteBorn.bornVec_sum
-- expected: standard only — Born weights are a probability vector (sum = 1)

-- QIQT-H PRIZE (C3+C4): the JOIN — capacity-selected actual histories are Born.
#print axioms QIQTH.BornJoin.ActualEnsemble.pushforward_eq_w
-- expected: standard only — world-mass of a history = Born PRODUCT weight (from oneSite+indep)
#print axioms QIQTH.BornJoin.ActualEnsemble.actualHistory_typical
-- expected: standard only — atypical-frequency histories carry small total mass
#print axioms QIQTH.BornJoin.ActualEnsemble.actualHistory_typical_world
-- expected: standard only — world-mass form of typicality
#print axioms QIQTH.BornJoin.ActualEnsemble.finite_noCollapseBornRepresentation
-- expected: standard only — THE PRIZE: unique actual history + Born product law + typicality
#print axioms QIQTH.BornJoin.iidWitness
-- expected: standard only — concrete i.i.d. Born ensemble: oneSite+indep JOINTLY SATISFIABLE
#print axioms QIQTH.BornJoin.iid_oneSite
-- expected: standard only — single-trial marginal of the product Born weight is p (non-vacuity)
#print axioms QIQTH.BornJoin.ActualEnsemble.history_law_unique
-- expected: standard only — world-measure carries no observable freedom (outcome law forced)

-- TOWARD THE REAL PRIZE: single-trial Born law DERIVED from non-contextuality.
#print axioms QIQTH.OneSiteGleason.oneSite_forced
-- expected: standard only — non-contextual μ(Pₐ) = Re tr(ρ Pₐ) FORCED by effect-Gleason (not assumed)
#print axioms QIQTH.OneSiteGleason.forced_isProbVector
-- expected: standard only — the forced single-trial law is a probability vector
#print axioms QIQTH.BornJoinGleason.ensemble_p_isBorn
-- expected: standard only — non-contextual ensemble law p is FORCED Born (p = Re tr(ρ Pₐ))
#print axioms QIQTH.BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality
-- expected: standard only — full representation with the single-trial law DERIVED (not assumed)
#print axioms QIQTH.OneSiteGleason.traceEffectMeasure
-- expected: standard only — converse to Gleason: every density matrix IS a non-contextual EffectMeasure
#print axioms QIQTH.BornJoinGleason.finite_noCollapseBorn_trace
-- expected: standard only — representation with hcal DISCHARGED via the concrete trace measure

-- QIQT-H TIER B: the bridge theorem (Spectrum Broadcast Structures, information cost).
#print axioms QIQTH.SBSBridge.fragment_finrank_ge
-- expected: standard only — distinguishability ⇒ fragment dimension ≥ n (orthonormal).
#print axioms QIQTH.SBSBridge.broadcast_finrank_ge
-- expected: standard only — broadcasting tensors spaces: dims multiply (≥ n²).
#print axioms QIQTH.SBSBridge.redundancy_le_logStorage
-- expected: standard only — LOAD-BEARING: distinguishability ⇒ ∑log(finrank) ≥ R·log n.
#print axioms QIQTH.SBSBridge.euclidean_storage_bound
-- expected: standard only — non-vacuity: the storage bound holds for Euclidean fragments.
#print axioms QIQTH.SBSBridge.sbs_single_outcome
-- expected: standard only — Tier-B single outcome: saturation DERIVED from redundancy.
#print axioms QIQTH.SBSBridge.fragmented_single_outcome
-- expected: standard only — FULLY load-bearing: storageCost finrank-DEFINED, hstorage PROVED
-- (no free field); redundancy_le_logStorage is in the dependency graph.

-- QIQT-H COLLISIONAL γ: the per-collision distinguishability γ<1 DERIVED from a toy
-- Hamiltonian H_int = g σ_z^S ⊗ σ_x^E (discharges the one isolated physical input of the
-- SBS chain, GPT-5.5-pro).  All axiom-free (standard three only).
#print axioms QIQTH.CollisionalGamma.collisionU_group
-- expected: standard only — U_s is a one-parameter unitary group (exp(-iθ s A) homomorphism).
#print axioms QIQTH.CollisionalGamma.hamiltonian_isSymmetric
-- expected: standard only — H_s = s·A is self-adjoint (genuine observable / Stone).
#print axioms QIQTH.CollisionalGamma.branch_overlap
-- expected: standard only — ⟨E_+|E_-⟩ = cos²θ - sin²θ (the per-collision overlap, COMPUTED).
#print axioms QIQTH.CollisionalGamma.gamma_lt_one
-- expected: standard only — γ = |cos 2θ| < 1 for generic coupling (DERIVED, not assumed).
#print axioms QIQTH.CollisionalGamma.collisional_block_overlap
-- expected: standard only — factorized amplification: block overlap ≤ γ^|B| (feeds overlap_amplifies).
#print axioms QIQTH.CollisionalGamma.collisional_overlap_tendsto_zero
-- expected: standard only — γ^L → 0: weak monitoring amplified into reliable records.
#print axioms QIQTH.CollisionalGamma.sigmaX_branch_overlap
-- expected: standard only — non-vacuity: the σ_x model on ℂ² realizes ⟨E_+|E_-⟩ = cos 2θ.

-- QIQT-H STAGE 1 toward the PRIZE (Effect-Gleason route, PRIZE_ROADMAP.md): the two
-- gaps beyond the single-state Gleason core. All axiom-free (standard three only).
#print axioms QIQTH.RecordGleason.born_kron
-- expected: standard only — Born factorizes on tensor products (independent experiments).
#print axioms QIQTH.RecordGleason.decoherent_partition_additive
-- expected: standard only — Born for ALL decoherent partitions (cylinder-consistency seed).
#print axioms QIQTH.RecordGleason.born_complete_total
-- expected: standard only — complete record family ⇒ weights sum to 1 (a probability).
#print axioms QIQTH.RecordGleason.stage1_record_measure
-- expected: standard only — packaged Stage-1 minimal-breakthrough record measure.

-- QIQT-H EFFECT-GLEASON step G1 (GLEASON_SCOPE.md): finite-dim Busch/POVM Gleason
-- foundation. All axiom-free (standard three only).
#print axioms QIQTH.EffectGleason.isEffect_smul
-- expected: standard only — effects closed under scaling by t ∈ [0,1].
#print axioms QIQTH.EffectGleason.EffectMeasure.map_zero
-- expected: standard only — μ 0 = 0.
#print axioms QIQTH.EffectGleason.EffectMeasure.mono
-- expected: standard only — monotonicity (E ≤ F ⇒ μ E ≤ μ F).
#print axioms QIQTH.EffectGleason.EffectMeasure.map_smul_add
-- expected: standard only — scaling additivity (seed of homogeneity).
#print axioms QIQTH.EffectGleason.cauchy_unit_interval
-- expected: standard only — G1 CORE: additive + monotone on [0,1] ⇒ ℝ-linear (Cauchy squeeze).
#print axioms QIQTH.EffectGleason.EffectMeasure.map_smul
-- expected: standard only — G1: μ(t•E) = t·μ E (additive + bounded ⇒ ℝ-homogeneous).
#print axioms QIQTH.EffectGleason.quadForm_im_zero
-- expected: standard only — G2: Hermitian quadratic form ⟨x,Hx⟩ is real (im = 0).
#print axioms QIQTH.EffectGleason.posSemidef_sumNorm_sub_herm
-- expected: standard only — G2: Hermitian Löwner bound H ⪯ (∑‖Hᵢⱼ‖)•1 (absent from Mathlib).
#print axioms QIQTH.EffectGleason.exists_smul_one_sub_posSemidef
-- expected: standard only — G2 prereq (absent from Mathlib): PSD A ⪯ c•1 (Löwner bound).
#print axioms QIQTH.EffectGleason.isEffect_inv_smul
-- expected: standard only — G2: PSD A bounded by c•1 ⇒ (1/c)•A is an effect (cone-scaling).
#print axioms QIQTH.EffectGleason.EffectMeasure.coneExt_eq
-- expected: standard only — G2: cone extension ν A = c·μ((1/c)•A), bound-independent.
#print axioms QIQTH.EffectGleason.EffectMeasure.coneExt_one
-- expected: standard only — G2: ν 1 = 1.
#print axioms QIQTH.EffectGleason.EffectMeasure.coneExt_nonneg
-- expected: standard only — G2: ν ≥ 0 on PSD matrices.
#print axioms QIQTH.EffectGleason.posSemidef_smul_one_sub_mono
-- expected: standard only — G2: Löwner-bound monotonicity (A ⪯ a•1, a≤b ⇒ A ⪯ b•1).
#print axioms QIQTH.EffectGleason.EffectMeasure.coneExt_add
-- expected: standard only — G2: ν is additive on PSD (common-bound argument).
#print axioms QIQTH.EffectGleason.EffectMeasure.coneExt_smul_one
-- expected: standard only — G2: ν(a·1) = a for a ≥ 0.
#print axioms QIQTH.EffectGleason.EffectMeasure.hermExt_eq
-- expected: standard only — G2: Hermitian extension Λ H = ν(H+c·1) − c, bound-independent.
#print axioms QIQTH.EffectGleason.posSemidef_sumNorm_add_herm
-- expected: standard only — G2: lower Löwner bound (∑‖Aᵢⱼ‖)•1 + A PSD for Hermitian A.
#print axioms QIQTH.EffectGleason.EffectMeasure.hermExt_add
-- expected: standard only — G2: Λ additive on Hermitian matrices.
#print axioms QIQTH.EffectGleason.EffectMeasure.hermExt_nonneg
-- expected: standard only — G2: Λ ≥ 0 on PSD (= ν there).
#print axioms QIQTH.EffectGleason.EffectMeasure.coneExt_smul
-- expected: standard only — G2: ν(t•A) = t·ν A for t ≥ 0.
#print axioms QIQTH.EffectGleason.EffectMeasure.hermExt_smul
-- expected: standard only — G2: Λ(t•H) = t·Λ H for all t ∈ ℝ ⇒ Λ is ℝ-linear.
#print axioms QIQTH.EffectGleason.EffectMeasure.hermExt_eq_mu_of_isEffect
-- expected: standard only — G2: Λ E = μ E on effects (recovers μ; the capstone link).
#print axioms QIQTH.EffectGleason.hermDecomp
-- expected: standard only — G3: M = reHerm M + i·imHerm M (complexification decomposition).
#print axioms QIQTH.EffectGleason.EffectMeasure.cExt_add
-- expected: standard only — G3: Λ_ℂ additive.
#print axioms QIQTH.EffectGleason.EffectMeasure.cExt_smul
-- expected: standard only — G3: Λ_ℂ(c•M) = c·Λ_ℂ M ⇒ Λ_ℂ is ℂ-LINEAR on all matrices.
#print axioms QIQTH.EffectGleason.EffectMeasure.cExt_trace
-- expected: standard only — G3 Riesz: Λ_ℂ M = tr(ρM), ρ a b := Λ_ℂ(E_{ba}).
#print axioms QIQTH.EffectGleason.EffectMeasure.cExt_eq_mu_of_isEffect
-- expected: standard only — G4: Λ_ℂ E = ↑(μ E) on effects.
#print axioms QIQTH.EffectGleason.EffectMeasure.rho_trace
-- expected: standard only — G4: tr ρ = 1 (normalization).
#print axioms QIQTH.EffectGleason.EffectMeasure.rho_posSemidef
-- expected: standard only — G4: ρ PSD (rank-1 |x⟩⟨x| route + hermExt_nonneg).
#print axioms QIQTH.EffectGleason.EffectMeasure.finite_effect_gleason
-- expected: standard only — CAPSTONE: finite-dim effect (Busch) Gleason — μ E = tr(ρE),
-- ρ a density matrix. The Born rule from positivity + additivity, axiom-free.
#print axioms QIQTH.EffectGleason.trace_form_unique
-- expected: standard only — trace-form non-degeneracy on effects (uniqueness engine).
#print axioms QIQTH.EffectGleason.EffectMeasure.finite_effect_gleason_unique
-- expected: standard only — UNIQUENESS of the Gleason density (∃!).
#print axioms QIQTH.EffectGleason.EffectMeasure.mu_sum_of_povm
-- expected: standard only — POVM probabilities sum to 1.
#print axioms QIQTH.EffectGleason.maxMixed
-- expected: standard only — non-vacuity: maximally-mixed EffectMeasure (0 < d).

-- A3: Finite-dim quantum relative-entropy program (begins retiring the entropy axiom stack)
#print axioms QIQTH.QuantumEntropy.IsDensity.sum_eigenvalues
-- expected: standard only — eigenvalues of a finite density matrix sum to 1 (tr = ∑ eigenvalues).
#print axioms QIQTH.QuantumEntropy.IsDensity.eigenvalues_le_one
-- expected: standard only — each eigenvalue of a density matrix is ≤ 1 (bounded by the unit sum).
#print axioms QIQTH.QuantumEntropy.vonNeumannEntropy_nonneg
-- expected: standard only — ★ von Neumann entropy S(ρ)=∑ negMulLog(λᵢ) ≥ 0 for any density matrix:
-- the concrete finite-dim content of the (currently opaque) entropy object Donald.H. First step of the
-- program to replace the axiomatized quantum-entropy stack with theorems about concrete density matrices.
#print axioms QIQTH.QuantumEntropy.cfc_trace
-- expected: standard only — the trace workhorse tr(f(A))=∑ᵢ f(λᵢ) for the Hermitian functional calculus
-- (f(A)=U·diag(f∘λ)·U⋆, trace conjugation-invariant). Reduces entropy/relative-entropy to eigenvalue sums.
#print axioms QIQTH.QuantumEntropy.relEntropy_self
-- expected: standard only — D(ρ‖ρ)=0 for the concrete quantum relative entropy D(ρ‖σ)=tr(ρ(log ρ−log σ)),
-- built on the Hermitian matrix logarithm matLog := IsHermitian.cfc Real.log (the gating primitive Mathlib
-- lacked, now in hand). Concrete realization of the opaque Donald.D / ArakiInterface.AkRelEnt.
#print axioms QIQTH.QuantumEntropy.trace_mul_matLog
-- expected: standard only — Stage 1 toward Klein: tr(ρ·log ρ)=∑ᵢ λᵢ log λᵢ for positive-definite ρ
-- (ρ·log ρ = (x↦x log x)(ρ) via cfc_mul, then cfc_trace). The diagonal term of D(ρ‖σ).
#print axioms QIQTH.QuantumEntropy.crossTerm_trace
-- expected: standard only — Stage 2: the cross-term tr(ρ·log σ)=∑ᵢⱼ pᵢ Sᵢⱼ log qⱼ, S i j = normSq((U_ρ⋆U_σ)ᵢⱼ)
-- the overlap matrix. Trace cyclicity + the diag(p)·W·diag(l)·W⋆ index expansion.
#print axioms QIQTH.QuantumEntropy.relEntropy_nonneg
-- expected: standard only — ★★ KLEIN'S INEQUALITY: D(ρ‖σ)=tr(ρ(log ρ−log σ))≥0 for positive-definite density
-- matrices. The finite-dimensional content of the axiom RelEntPositivity.D_nonneg / ArakiInterface.Akre_nonneg.
-- Doubly-stochastic/Jensen proof: diagonal term (trace_mul_matLog) − cross term (crossTerm_trace), the overlap
-- matrix S doubly stochastic (row/col_sum_normSq), concavity of log (Jensen) ⇒ ≥ ∑pᵢlog(pᵢ/rᵢ)=KL(p‖r)≥0
-- (RelEntPositivity.KL_classical_nonneg). Now PROVED, not assumed, in finite dimensions — axiom-free.
#print axioms QIQTH.QuantumEntropy.vonNeumannEntropy_eq_neg_trace
-- expected: standard only — the entropy bridge S(ρ)=−tr(ρ log ρ) (spectral = operator form, via trace_mul_matLog).
#print axioms QIQTH.QuantumEntropy.relEntropy_eq_crossEntropy_sub_entropy
-- expected: standard only — Donald identity (A1) D(ρ‖σ)=crossEnt(ρ,σ)−H(ρ), concrete; content of Donald.D_eq_crossEnt_sub_H.
#print axioms QIQTH.QuantumEntropy.crossEntropy_self
-- expected: standard only — Donald identity (A3) crossEnt(ρ,ρ)=H(ρ), concrete; content of Donald.crossEnt_self.
#print axioms QIQTH.QuantumEntropy.crossEntropy_sum
-- expected: standard only — Donald identity (A2) crossEnt linear in first arg, crossEnt(∑pₖρₖ,σ)=∑pₖcrossEnt(ρₖ,σ);
-- concrete content of Donald.crossEnt_mixture. The three Donald structural identities now PROVED for the matrix model.
#print axioms QIQTH.Donald.donald_identity
-- expected: standard only — Donald's identity is now a THEOREM about any DonaldSystem typeclass (the former 8
-- opaque Donald axioms — State/D/H/crossEnt/mixture + the 3 identities — are now class fields, NOT axioms).
#print axioms QIQTH.QuantumEntropy.instDonaldSystemHermitianMat
-- expected: standard only — ★★ the concrete DISCHARGE: Hermitian matrices form a DonaldSystem, axiom-free.
-- D/H/crossEnt = the trace (Umegaki) forms; (A1),(A3) are rfl, (A2) is crossEntropy_sum (trace linearity).
-- This retires the 8 former Donald axioms (budget 29→21): they are now derived facts about a realizable
-- interface, with a genuine finite-dim model, rather than global assumptions.

-- A4: DPI / Lieb program (Carlen §2 toolkit), Phase 1 — toward retiring the DPI axioms
#print axioms QIQTH.Entropy.peierls_inequality
-- expected: standard only — ★ Peierls' inequality (Carlen Thm 2.9): ∑ⱼ f(Re Bⱼⱼ) ≤ ∑ᵢ f(λᵢ) for Hermitian B,
-- convex f. The diagonal entries are a doubly-stochastic average of eigenvalues (‖Vⱼₖ‖² overlap, row/col-
-- stochastic) → Jensen. Foundation of the §2 trace-convexity toolkit (the bottom of the Lieb/DPI tower).
#print axioms QIQTH.Entropy.eigenvalues_sum_conj_invariant
-- expected: standard only — eigenvalue sums ∑ᵢ f(λᵢ) are invariant under unitary conjugation A ↦ V⋆AV
-- (equal characteristic polynomials via charpoly_mul_comm ⇒ equal eigenvalue multisets via
-- roots_charpoly_eq_eigenvalues). The conjugation-invariance foundation for Carlen 2.10–2.12 (which apply
-- Peierls in the eigenbasis of (A+B)/2) and for the unitary invariance of relative entropy used in DPI.
#print axioms QIQTH.Entropy.trace_function_midpoint_convex
-- expected: standard only — ★ convexity of trace functions (Carlen Thm 2.10): Tr f((A+B)/2) ≤
-- (Tr f(A) + Tr f(B))/2 for convex f (eigenvalue-sum form). In M=(A+B)/2's eigenbasis the diagonal is
-- λ(M) = (Re A'ᵢᵢ + Re B'ᵢᵢ)/2; midpoint convexity termwise + Peierls + conjugation invariance.
#print axioms QIQTH.Entropy.trace_function_convex
-- expected: standard only — ★ convexity of trace functions (Carlen Thm 2.10, FULL two-point form):
-- Tr f(tA+(1−t)B) ≤ t·Tr f(A) + (1−t)·Tr f(B), t∈[0,1], convex f. The two §2 results the DPI/Lieb tower
-- needs from §2 (Peierls + this convexity) are now complete and axiom-free.

-- A4: DPI / Lieb program — Phase 2 kickoff (Carlen §2.1/§3 operator convexity, Loewner order)
#print axioms QIQTH.Entropy.conjTranspose_mul_mul_le
-- expected: standard only — congruence preserves the Loewner order: A ≤ B ⇒ V⋆AV ≤ V⋆BV (via
-- PosSemidef.conjTranspose_mul_mul_same on B−A). The order-congruence foundation of the Schur/Ando route
-- to Lieb's concavity (the deep Phase-2 crux). (Mathlib MatrixOrder: A ≤ B := (B−A).PosSemidef.)
#print axioms QIQTH.Entropy.fromBlocks_star_inv_posSemidef
-- expected: standard only — the block [[A,B],[B⋆,B⋆A⁻¹B]] is PSD for A PosDef (Carlen Lemma 3.2 via the
-- Schur complement Matrix.PosDef.fromBlocks₁₁, already in Mathlib). The minimality factorization.
#print axioms QIQTH.Entropy.star_inv_le_of_fromBlocks_posSemidef
-- expected: standard only — minimality: fromBlocks A B B⋆ D PSD (A PosDef) ⇒ B⋆A⁻¹B ≤ D. This is the
-- engine of Ando's joint convexity of (A,B)↦B⋆A⁻¹B (Carlen Thm 3.1, next toward Lieb).
#print axioms QIQTH.Entropy.star_inv_subadditive
-- expected: standard only — ★★ ANDO's joint convexity of (A,B)↦B⋆A⁻¹B (Carlen Thm 3.1, subadditive form):
-- (B₀+B₁)⋆(A₀+A₁)⁻¹(B₀+B₁) ≤ B₀⋆A₀⁻¹B₀ + B₁⋆A₁⁻¹B₁ for PosDef A₀,A₁. Sum of two PSD Schur blocks is the
-- combined block (fromBlocks_add), PSD; minimality (A₀+A₁ PosDef) gives the inequality. The key §3 result
-- feeding the operator-mean concavities and Lieb's concavity theorem.
#print axioms QIQTH.Entropy.parallel_sum_subadditive
-- expected: standard only — operator HARMONIC-MEAN concavity (Carlen §3.2): (A,B)↦B⋆(A+B)⁻¹B is jointly
-- convex (⟺ M₋₁(A,B)=2B−2B(A+B)⁻¹B concave), a direct corollary of Ando (star_inv_subadditive applied to
-- (A₀+B₀,B₀),(A₁+B₁,B₁)).
#print axioms QIQTH.Entropy.ofMatrix_le_iff
#print axioms QIQTH.Entropy.ofMatrix_nonneg_iff
#print axioms QIQTH.Entropy.ofMatrix_cfc
-- expected: standard only — CStarMatrix↔Matrix BRIDGE (transport engine for the Löwner–Heinz toolkit).
-- ofMatrix_le_iff/nonneg_iff: the Matrix Loewner order and CStarMatrix spectral order coincide across
-- ofMatrixStarAlgEquiv (a StarRingEquiv is automatically an OrderIsoClass). ofMatrix_cfc: e (cfc f A) =
-- cfc f (e A) (StarAlgHomClass.map_cfc, continuity from ofMatrixL). The bridge file ALSO supplies the three
-- CStarMatrix CFC instances Mathlib leaves un-synthesizable (FiniteDimensional + real-CFC + NonnegSpectrumClass),
-- which makes the ENTIRE Löwner–Heinz toolkit (concaveOn_rpow, sqrt_le_sqrt, …) fire on CStarMatrix and hence
-- transport to Matrix. Unblocks the geometric-mean / Lieb tower.
#print axioms QIQTH.Entropy.matrix_sqrt_le_sqrt
#print axioms QIQTH.Entropy.ofMatrix_sqrt
-- expected: standard only — OPERATOR MONOTONICITY of √ on Matrix n n ℂ (Löwner–Heinz p=1/2): 0≤A≤B ⟹ √A≤√B.
-- Transported from CFC.sqrt_le_sqrt across the CStarMatrix bridge (ofMatrix_sqrt = √ commutes with the equiv via
-- ℝ≥0 cfc-naturality; ofMatrix_le_iff carries the inequality back). The maximality ingredient for the operator
-- geometric mean (Carlen §3.3–3.5) → Lieb's concavity.
#print axioms QIQTH.Entropy.matrix_le_sqrt_of_sq_le
-- expected: standard only — maximality reduction Z²≤C ⟹ Z≤√C (Z Hermitian): Z ≤ |Z| = √(Z·Z) via
-- CFC.abs_sub_self (|Z|−Z = 2•Z⁻ ≥ 0), then √(Z·Z) ≤ √C by operator √-monotonicity. The engine of the
-- operator geometric-mean maximality.
#print axioms QIQTH.Entropy.gmean_mul_inv_mul_gmean
#print axioms QIQTH.Entropy.gmean_fromBlocks_posSemidef
#print axioms QIQTH.Entropy.le_gmean_of_fromBlocks_posSemidef
#print axioms QIQTH.Entropy.gmean_superadditive
-- expected: standard only — the OPERATOR GEOMETRIC MEAN A#B = √A·√(√A⁻¹ B √A⁻¹)·√A and its JOINT CONCAVITY
-- (Carlen Thm 3.5, Ando): achievability ([[A,A#B],[A#B,B]] PSD via Schur with (A#B)A⁻¹(A#B)=B) + maximality
-- ([[A,X],[X,B]] PSD ⟹ X ≤ A#B, via Z²≤C⟹Z≤√C after A^{-1/2}-conjugation) ⟹ superadditivity
-- A₀#B₀+A₁#B₁ ≤ (A₀+A₁)#(B₀+B₁). The operator-mean input to Lieb's concavity theorem.
#print axioms QIQTH.Entropy.posSemidef_mul_of_commute
#print axioms QIQTH.Entropy.sqrt_mul_of_commute
#print axioms QIQTH.Entropy.commute_rpow_dyadic
#print axioms QIQTH.Entropy.commute_rpow_mul
-- expected: standard only — ★★ COMMUTING-PRODUCT RPOW (the matrix fact Mathlib lacks, now PROVEN):
-- (P*Q)^t = P^t·Q^t for commuting PosDef P,Q and 0≤t. Chain: commuting √ (sqrt_mul_of_commute, via
-- sqrt_unique + commuting cfc) → 1/2ⁿ powers (commute_rpow_inv_two_pow, induction) → dyadic m/2ᵏ
-- (commute_rpow_dyadic, via Commute.mul_pow) → all t (continuity continuous_matrix_rpow + dyadic density
-- ⌊t·2ʲ⌋/2ʲ→t). This UNBLOCKS the tensor power (A⊗B)^t=A^t⊗B^t and the A^{1-t}⊗B^t form Lieb needs.
#print axioms QIQTH.Entropy.rpow_kronecker_one
#print axioms QIQTH.Entropy.rpow_one_kronecker
#print axioms QIQTH.Entropy.rpow_kronecker
#print axioms QIQTH.Entropy.wgmean_kronecker
#print axioms QIQTH.Entropy.tensor_rpow_superadditive
#print axioms QIQTH.Entropy.lieb_superadditive
-- expected: standard only — ★★★★ LIEB'S CONCAVITY THEOREM (Carlen 6.1, q+r=1): (A,B)↦Tr(Kᴴ·A^{1-t}·K·(Bᵗ)ᵀ)
-- jointly concave (superadditive), t∈[0,1]. The joint concavity of A^{1-t}⊗Bᵗ (tensor_rpow_superadditive)
-- read through the vec/trace identity Tr(Kᴴ·A·K·Bᵀ)=⟨vecK,(B⊗ₖA)vecK⟩ (kronecker_mulVec_vec +
-- star_vec_dotProduct_vec): the PSD operator inequality ⟹ scalar one since M↦⟨v,Mv⟩ is linear + monotone.
-- One of the deepest results in quantum information theory, machine-checked from scratch.
#print axioms QIQTH.Entropy.rpow_unitary_conj
-- expected: standard only — rpow commutes with unitary conjugation (u·M·u⋆)^t = u·M^t·u⋆, via CFC
-- naturality (map_cfc) under the inner ∗-automorphism conjStarAlgAut u. The basis-change engine
-- toward the no-transpose form of Lieb that the relative-entropy joint convexity consumes.
#print axioms QIQTH.Entropy.rpow_transpose
#print axioms QIQTH.Entropy.posDef_transpose
#print axioms QIQTH.Entropy.trace_rpow_concave
-- expected: standard only — rpow_transpose: (A^t)ᵀ=(Aᵀ)^t (transpose = entrywise conj is an
-- ℝ-star-alg-aut, map_cfc). trace_rpow_concave: ★★ the NO-TRANSPOSE Lieb (A,B)↦Tr(A^{1-t}·B^t)
-- jointly concave — Lieb at K=1 with the Bᵀ removed via rpow_transpose; THE relative-entropy input.
#print axioms QIQTH.Entropy.mul_matLog_eq
#print axioms QIQTH.Entropy.hasDerivAt_rpow_one_sub_zero
#print axioms QIQTH.Entropy.hasDerivAt_trace_rpow_mul
-- hasDerivAt_trace_rpow_mul: d/dt Tr(A^{1-t}·Bᵗ)|₀ = Tr(-(A·log A) + A·log B) = -D(A‖B). Product rule
-- (Frobenius normed ring) on the two factor derivatives + the continuous linear trace. THE derivative
-- whose negative real part is the Umegaki relative entropy — so D = lim_{t→0}(Tr A - Tr(A^{1-t}Bᵗ))/t.
#print axioms QIQTH.Entropy.relEntropy_eq_neg_deriv
#print axioms QIQTH.Entropy.tendsto_relEntropy
-- relEntropy_eq_neg_deriv: D(A‖B) = -Re d/dt Tr(A^{1-t}Bᵗ)|₀ (trace algebra). tendsto_relEntropy:
-- ★ D(A‖B) = lim_{t→0}(Tr A - Tr(A^{1-t}Bᵗ))/t — relative entropy AS the limit of Lieb's difference
-- quotient (hasDerivAt + slope). The quotient is jointly convex (trace_rpow_concave) ⟹ D jointly convex.
#print axioms QIQTH.Entropy.cfc_log_conj
#print axioms QIQTH.Entropy.matLog_conj
#print axioms QIQTH.Entropy.relEntropy_unitary_invariant
#print axioms QIQTH.Entropy.matLog_smul
#print axioms QIQTH.Entropy.relEntropy_smul
#print axioms QIQTH.Entropy.relEntropy_subadd_sum
-- relEntropy_subadd_sum: D(Σᵢ Aᵢ ‖ Σᵢ Bᵢ) ≤ Σᵢ D(Aᵢ‖Bᵢ) (finite subadditivity, induction on
-- relEntropy_subadditive). The 4th DPI ingredient: subadd + unitary inv + scaling ⟹ mixed-unitary DPI.
#print axioms QIQTH.Entropy.dpi_mixed_unitary
-- expected: standard only — ★★★★★ DATA-PROCESSING INEQUALITY (Lindblad–Uhlmann) for mixed-unitary
-- channels Φ(ρ)=Σₖ pₖ Uₖ ρ Uₖ⋆: D(Φρ‖Φσ) ≤ D(ρ‖σ). Proved from joint convexity via
-- subadd_sum → relEntropy_smul (scaling) → relEntropy_unitary_invariant → Σpₖ=1. The concrete DPI
-- that retires the abstract DPI axioms (see DPI.lean).
#print axioms QIQTH.DPI.DPI_inequality
-- expected: standard only — DPI_inequality is now a THEOREM (was an axiom): D(Φρ‖Φσ)≤D(ρ‖σ) for the
-- concrete MixedUnitaryChannel, = dpi_mixed_unitary. The 4 DPI axioms (Channel/pull/DPI_inequality/
-- restrict) RETIRED → budget 21→17. The DPI/Lieb tower is complete for the mixed-unitary class.
#print axioms QIQTH.Entropy.trace_partialTraceRight
#print axioms QIQTH.Entropy.partialTraceRight_isHermitian
#print axioms QIQTH.Entropy.partialTraceRight_quadForm
#print axioms QIQTH.Entropy.partialTraceRight_posSemidef
#print axioms QIQTH.Entropy.partialTraceRight_posDef
-- expected: standard only — PARTIAL TRACE Tr₂ + its structural properties (Carlen Thm 5.6), toward
-- FULLY-GENERAL CPTP DPI beyond the mixed-unitary class. (Tr₂ρ)_{ij}=Σ_a ρ_{(i,a)(j,a)} is trace-
-- preserving and positivity-preserving — the quadratic-form decomposition ⟨v,Tr₂ρ v⟩=Σ_a⟨w_a,ρ w_a⟩
-- (partialTraceRight_quadForm, w_a the a-slice of v) makes Tr₂ both PSD-preserving and (over a nonempty
-- traced factor) PosDef-preserving (each ⟨w_a,ρ w_a⟩>0 for v≠0) — the latter needed since the Umegaki
-- relative entropy D(·‖·) is PosDef-only. Hence Hermitian-preserving. The reusable foundation; the
-- discrete-Weyl 1-design realizing ρ↦(Tr₂ρ)⊗(I/m) as mixed-unitary + the DPI assembly are next. Axiom-free.
#print axioms QIQTH.Entropy.weyl_char_sum_eq_zero
#print axioms QIQTH.Entropy.weyl_char_sum
-- expected: standard only — CHARACTER ORTHOGONALITY, the arithmetic engine of the discrete-Weyl 1-design
-- (toward partial-trace DPI). Σ_{b<m} ω^{b·c} = m·[c=0] for ω a primitive m-th root: off-diagonal (c≠0)
-- vanishes since ω^c is an m-th root ≠1 so geom_sum_eq telescopes (ω^{cm}−1)/(ω^c−1)=0; diagonal (c=0)
-- sums m ones. Feeds the clock-twirl Σ_b Z^b M Z^{-b}=diag M → Weyl 1-design → ρ↦(Tr₂ρ)⊗(I/m). Axiom-free.
#print axioms QIQTH.Entropy.clock_mem_unitary
#print axioms QIQTH.Entropy.shift_mem_unitary
-- expected: standard only — THE CLOCK & SHIFT WEYL UNITARIES (toward partial-trace DPI). clock ω m =
-- diag(1,ω,…,ω^{m−1}) is unitary (diagonal of unit-modulus roots, conj·self=normSq=‖ω‖²=1); shift m =
-- (finRotate m).permMatrix is unitary (permutation matrix, via conjTranspose_permMatrix + permMatrix_mul
-- group cancellation). These are the conjugating unitaries of the clock-twirl / Weyl 1-design. Axiom-free.
#print axioms QIQTH.Entropy.geom_sum_root_eq_zero
#print axioms QIQTH.Entropy.clock_char_orthogonality
-- expected: standard only — CLOCK CHARACTER ORTHOGONALITY (the entrywise engine of the dephasing twirl).
-- Σ_b ω^{j·b}·conj(ω^{k·b}) = m·[j=k]: each summand factors as w^b with w=ω^j·conj(ω^k), an m-th root
-- of unity that is 1 iff j=k (primitive-root injectivity pow_inj). Diagonal → m; off-diagonal → 0
-- (geom_sum_root_eq_zero: m-th root ≠1 ⟹ geometric sum telescopes to 0). This is exactly what makes the
-- clock twirl (1/m)Σ_b Z^b M (Z^b)⋆ project M onto its diagonal (dephasing) → toward partial-trace DPI.
#print axioms QIQTH.Entropy.clock_pow
#print axioms QIQTH.Entropy.clock_twirl
-- expected: standard only — THE CLOCK TWIRL = DEPHASING CHANNEL: (1/m)Σ_b Z^b M (Z^b)⋆ = diag(M).
-- clock_pow: Z^k = diag(ω^{i·k}). clock_twirl assembles it entrywise: (Z^b M (Z^b)⋆)_{jk} =
-- ω^{j·b}M_{jk}conj(ω^{k·b}), summed over b and scaled by 1/m gives M_{jk}·[j=k] (clock_char_orthogonality
-- (1/m)·m=1 on diagonal, 0 off) = diag(M). A genuine mixed-unitary channel (uniform 1/m weights over the
-- clock unitaries Z^b) — the dephasing half of the Weyl twirl → ρ↦(Tr₂ρ)⊗(I/m) → partial-trace DPI. Axiom-free.
#print axioms QIQTH.Entropy.perm_conj_diagonal
-- expected: standard only — PERMUTATION CONJUGATION OF A DIAGONAL = relabeled diagonal: P_σ·diag d·P_σ⋆
-- = diag(d∘σ). Conjugating a diagonal by a permutation matrix permutes its diagonal entries — the
-- structural fact behind the shift twirl (X=P_{finRotate} conjugation keeps a diagonal diagonal, just
-- cyclically relabeled). Proved by reading the conjugation as a double submatrix relabeling of diag d
-- (PEquiv.toMatrix_toPEquiv_mul / mul_toMatrix_toPEquiv + submatrix_diagonal_equiv). General (any σ),
-- reusable. Remaining for shift_twirl: orbit sum Σ_{a:Fin m} d(σ^a j)=Σ_p d_p (cycle bijection). Axiom-free.
#print axioms QIQTH.Entropy.shift_orbit_sum
#print axioms QIQTH.Entropy.shift_twirl
-- expected: standard only — THE SHIFT TWIRL = MAXIMALLY-MIXING CHANNEL: (1/m)Σ_a X^a (diag d) (X^a)⋆ =
-- ((Σ_j d_j)/m)·I. shift_orbit_sum: since finRotate is an m-cycle, a↦σ^a j enumerates Fin m
-- (injective via IsCycle.pow_eq_pow_iff + pow_injOn_Iio_orderOf, orderOf=m=support card; m=1 subsingleton),
-- so Σ_{a:Fin m} d(σ^a j)=Σ_p d_p. shift_twirl: each conjugation relabels the diagonal cyclically
-- (perm_conj_diagonal), summing over the full cycle replaces every diagonal entry by the orbit sum =
-- maximally mixed. Composing clock_twirl (dephasing) ∘ shift_twirl (mixing) = complete depolarization
-- M↦(Tr M/m)·I = the full discrete-Weyl 1-design (mixed-unitary). → factor-2 lift → partial-trace DPI. Axiom-free.
#print axioms QIQTH.Entropy.weyl_depolarization
-- expected: standard only — THE COMPLETE DEPOLARIZING CHANNEL = Weyl twirl (clock dephasing ∘ shift
-- mixing): averaging M over conjugation by every Weyl unitary W_{a,b}=X^aZ^b maps M↦(Tr M/m)·I. Composes
-- clock_twirl (inner b-sum → diag M) then shift_twirl (outer a-sum of diag M → maximally mixed); the proof
-- is simp_rw[clock_twirl];rw[shift_twirl];rfl (M.trace=Σ_j M_jj defeq). The full discrete-Weyl 1-design as
-- a mixed-unitary channel — the single-factor depolarization underlying the factor-2 twirl
-- ρ↦(Tr₂ρ)⊗(I/m) of partial-trace DPI. Axiom-free.
#print axioms QIQTH.Entropy.weyl_depolarization_flat
-- expected: standard only — the FLAT Weyl-average form the mixed-unitary channel consumes:
-- Σ_{a,b} (1/m²)·W_{a,b} M W_{a,b}⋆ = (Tr M/m)·I, W_{a,b}=X^aZ^b (uniform 1/m² weights). Same content as
-- weyl_depolarization with the inner clock average pulled out of the shift conjugation
-- ((X^aZ^b)⋆=Z^b⋆X^a⋆, X^a·(–)·X^a⋆ through the b-sum). Feeds dpi_mixed_unitary. Axiom-free.
#print axioms QIQTH.Entropy.one_kron_mem_unitary
-- expected: standard only — I_n⊗W is UNITARY when W is (PartialTraceDPI.lean) — the conjugating unitaries
-- of the factor-2 Weyl twirl. Via Kronecker mixed-product (I⊗W)⋆(I⊗W)=(I⋆I)⊗(W⋆W)=I⊗I=I
-- (conjTranspose_kronecker + ← mul_kronecker_mul + one_kronecker_one). First brick of the factor-2 lift
-- ρ↦(Tr₂ρ)⊗(I/m) toward partial-trace DPI D(Tr₂ρ‖Tr₂σ)≤D(ρ‖σ) (Carlen §5.7). Axiom-free.
#print axioms QIQTH.Entropy.kron_conj_block
#print axioms QIQTH.Entropy.factor2_depolarization
-- expected: standard only — THE FACTOR-2 WEYL TWIRL = COMPLETE DEPOLARIZATION OF FACTOR 2:
-- Σ_{a,b}(1/N²)•((I⊗W_ab)ρ(I⊗W_ab)ᴴ)=(Tr₂ρ)⊗ₖ(I_N/N). kron_conj_block: ((I⊗W)ρ(I⊗W)ᴴ)_{(i,a')(j,b')}
-- =(W·blockᵢⱼρ·Wᴴ)_{a'b'} (entrywise Kronecker reduction — I on factor 1 selects the (i,j)-block, W
-- conjugates factor 2). factor2_depolarization: per-block weyl_depolarization_flat gives
-- (Tr(blockᵢⱼρ)/N)·[a'=b'], and Tr(blockᵢⱼρ)=(Tr₂ρ)ᵢⱼ (=partialTraceRight, defeq), = (Tr₂ρ)⊗(I/N). This is
-- a mixed-unitary channel (one_kron_mem_unitary) ⟹ dpi_mixed_unitary ⟹ partial-trace DPI. Axiom-free.
#print axioms QIQTH.Entropy.kronRightHom
#print axioms QIQTH.Entropy.matLog_kron_one
-- expected: standard only — MATRIX-LOG FACTORS THROUGH ⊗1: log(A⊗1_m)=(log A)⊗1_m. kronRightHom = the
-- two-type generalization of TensorPower.kroneckerRightHom (A↦A⊗ₖ1_p, unital ⋆-alg-hom
-- Matrix n n→⋆ₐ Matrix(n×p)(n×p)); matLog_kron_one = CFC naturality (IsHermitian.cfc_eq bridge +
-- StarAlgHomClass.map_cfc, same pattern as matLog_conj for unitary conjugation). Key infrastructure for
-- relative-entropy ⊗-additivity (maximally-mixed factor) → partial-trace DPI. Axiom-free.
#print axioms QIQTH.Entropy.partial_trace_dpi
-- expected: standard only — ★★★★★ PARTIAL-TRACE DATA PROCESSING: D(Tr₂ρ‖Tr₂σ) ≤ D(ρ‖σ). Tracing out a
-- subsystem can only DECREASE the quantum relative entropy — extends DPI from the mixed-unitary class to
-- the partial trace (the central CPTP map), exactly Carlen §6.4+§5.7, fully machine-checked & axiom-free.
-- The factor-2 Weyl twirl (I⊗W_ab, weights 1/N²) is mixed-unitary (dpi_mixed_unitary) and = (Tr₂ρ)⊗(I/N)
-- (factor2_depolarization); relEntropy_kron_one (N⁻¹·N=1) closes it. NOTE the IsHermitian of the
-- depolarized states is built DIRECTLY (isHermitian_kronecker) NOT via PosDef.kronecker — the latter's
-- Fintype.ofFinite blows up whnf. This completes the partial-trace DPI tower (Weyl 1-design from scratch).
#print axioms QIQTH.Entropy.relEntropy_kron_one
-- expected: standard only — RELATIVE-ENTROPY ⊗-ADDITIVITY (scalar-identity 2nd factor):
-- D(A⊗(c·1_m)‖B⊗(c·1_m))=(c·dim m)·D(A‖B). The common c·1 factor's log cancels in logρ−logσ=(logA−logB)⊗1
-- (matLog_smul+matLog_kron_one), and trace factors Tr((A(logA−logB))⊗(c·1))=Tr(A(logA−logB))·(c·dim m)
-- (trace_kronecker). For maximally-mixed c=1/dim m this is exactly D(A‖B) — the last step before the
-- partial-trace DPI assembly. Axiom-free.
#print axioms QIQTH.Entropy.perm_mem_unitary
-- expected: standard only — any permutation matrix is unitary (general form of shift_mem_unitary, for the
-- factor-2 Weyl unitaries X^a=((finRotate)^a).permMatrix in the partial-trace DPI capstone). Axiom-free.
#print axioms QIQTH.QuantumEntropy.relEntropy_eq_zero
-- expected: standard only — ★★★★★ KLEIN'S EQUALITY CASE: D(ρ‖σ)=0 ⟹ ρ=σ for density matrices. The
-- equality tracking of relEntropy_nonneg (doubly-stochastic/Jensen): KL(p‖r)=0⟹p=r (Gibbs, log x<x−1)
-- + strict-Jensen ∑Sᵢⱼlog qⱼ=log rᵢ (map_sum_eq_iff') ⟹ W·diag(q)=diag(p)·W ⟹ σ=ρ. The hard direction.
#print axioms QIQTH.ArakiInterface.Akre_nonneg
#print axioms QIQTH.ArakiInterface.donald_araki
#print axioms QIQTH.ArakiInterface.dpi_ucp
#print axioms QIQTH.ArakiInterface.AkRelEnt_self
#print axioms QIQTH.ArakiInterface.AkRelEnt_eq_zero_iff
-- AkRelEnt_eq_zero_iff is now a THEOREM (was an axiom): D=0 ↔ ρ=σ, = relEntropy_eq_zero + AkRelEnt_self.
#print axioms QIQTH.ArakiInterface.matLog_le
#print axioms QIQTH.ArakiInterface.IHol_le_Shannon
-- matLog_le: ★ OPERATOR MONOTONICITY OF log (A⪯B⟹log A⪯log B), via Mathlib CFC.log_le_log transported
-- through the CStarMatrix bridge. IHol_le_Shannon is now a THEOREM (was an axiom): ★★★★★ HOLEVO'S
-- BOUND χ=Σpᵢ D(ρᵢ‖ρ̄)≤H(p), pointwise via pᵢρᵢ⪯ρ̄ + log monotonicity. ALL 11 ArakiInterface axioms
-- now RETIRED → budget 7→6. Remaining 6 axioms: EntropyBridge (Tomita–Takesaki / Type II frontier).
-- expected: standard only — the former ArakiInterface AXIOMS, now THEOREMS in the finite-dim model
-- (NormalState=HermitianMat): Akre_nonneg=Klein (relEntropy_nonneg), donald_araki=Donald's identity,
-- dpi_ucp=DPI (DPI_inequality), AkRelEnt_self=relEntropy_self. 9 of 11 ArakiInterface axioms RETIRED
-- → budget 17→8. Remaining 8 axioms: ArakiInterface (Holevo + Klein-equality) 2 + EntropyBridge 6.
-- toward DPI §6.4: cfc_log_conj/matLog_conj (log(uMu⋆)=u·log M·u⋆ via map_cfc on conjStarAlgAut),
-- relEntropy_unitary_invariant (D(uρu⋆‖uσu⋆)=D(ρ‖σ)). matLog_smul (log(c·ρ)=(log c)·1+log ρ via
-- cfc_comp_smul+cfc_const_add) + relEntropy_smul (D(c·ρ‖c·σ)=c·D(ρ‖σ), the log c terms cancel).
-- With joint convexity these give DPI for mixed-unitary channels Φ(ρ)=Σₖ pₖ Uₖ ρ Uₖ⋆.
#print axioms QIQTH.Entropy.relEntropy_subadditive
-- expected: standard only — ★★★★★ JOINT CONVEXITY OF QUANTUM RELATIVE ENTROPY (Carlen Thm 6.3):
-- D(A₀+A₁‖B₀+B₁) ≤ D(A₀‖B₀)+D(A₁‖B₁). The t→0 limit of the subadditive Lieb quotients
-- (trace_rpow_concave + tendsto_relEntropy + le_of_tendsto on 𝓝[>]0). The §6.3 capstone — built
-- end to end from Lieb's concavity through the matrix-calculus derivative. The key DPI §6.4 input.
-- mul_matLog_eq: A·log A = U·diag(λᵢ log λᵢ)·Uᴴ (conjStarAlgAut multiplicativity).
-- hasDerivAt_rpow_one_sub_zero: d/dt(t↦A^{1-t})|₀ = -(A·log A). With hasDerivAt_rpow_zero these are
-- the two derivatives feeding the product+trace rule for d/dt Tr(A^{1-t}Bᵗ)|₀ = -relEntropy.
#print axioms QIQTH.Entropy.hasDerivAt_rpow_zero
-- expected: standard only — d/dt(t↦B^t)|₀ = log B (matLog), for PosDef B. Differentiate the
-- eigendecomposition B^t=U·diag(μᵢ^t)·Uᴴ (eigenvectors constant) → scalar deriv d/dt μ^t=μ^t log μ.
-- Needs `open scoped Matrix.Norms.Frobenius` (Matrix has no canonical norm; Frobenius = a consistent
-- NormedRing+NormedAlgebra so matrix-valued HasDerivAt composition + const_mul have aligned instances).
-- First step of the relative-entropy joint convexity (Carlen §6.3): D = lim_{t→0}(Tr A−Tr(A^{1-t}Bᵗ))/t.
-- expected: standard only — ★★★ THE LIEB INPUT: JOINT CONCAVITY of (A,B)↦A^{1-t}⊗B^t for t∈[0,1].
-- wgmean_kronecker: wgmean t (A⊗I)(I⊗B) = A^{1-t}⊗B^t (commuting tensor weighted mean, via rpow_kronecker +
-- final factor √A·(A⁻¹)^t·√A=A^{1-t} = sqrt_mul_rpow_inv_mul_sqrt with rpow_inv_eq (A⁻¹)^t=A^{-t}). Then
-- Ando's wgSuperadd_mem_Icc applied to (A⊗I,I⊗B) gives tensor_rpow_superadditive: A₀^{1-t}⊗B₀^t+A₁^{1-t}⊗B₁^t
-- ≤ (A₀+A₁)^{1-t}⊗(B₀+B₁)^t. With the vec/trace identity this yields Lieb's concavity theorem (Carlen §6.1).
-- expected: standard only — ★★ TENSOR POWER (A⊗ₖB)^t = A^t⊗ₖB^t for PosDef A,B and 0≤t. Factor identities
-- (A⊗1)^t=A^t⊗1 and (1⊗B)^t=1⊗B^t via the ·⊗1 / 1⊗· star-algebra homs + StarAlgHomClass.map_cfc; the general
-- product via A⊗B=(A⊗1)(1⊗B) (commuting) + commute_rpow_mul. THE tensor identity Lieb needs for A^{1-t}⊗B^t.
#print axioms QIQTH.Entropy.gmean_kronecker
#print axioms QIQTH.Entropy.tensor_sqrt_superadditive
-- expected: standard only — TENSOR LIFT of the geometric mean (first step of Ando's tensor argument to Lieb):
-- gmean(A⊗I)(I⊗B)=√A⊗√B (commuting tensor geometric mean, via sqrt_kronecker/inv_kronecker) ⟹
-- JOINT CONCAVITY of (A,B)↦√A⊗√B: √A₀⊗√B₀+√A₁⊗√B₁ ≤ √(A₀+A₁)⊗√(B₀+B₁) (the p=q=1/2 case of A^p⊗B^q
-- concavity, which with the vec/trace identity yields Lieb's concavity theorem, Carlen §6.1).
#print axioms QIQTH.Entropy.gmean_le_gmean_right
#print axioms QIQTH.Entropy.gmean_le_gmean_left
#print axioms QIQTH.Entropy.gmean_mono
#print axioms QIQTH.Entropy.fromBlocks_diag_posSemidef
-- expected: standard only — FULL JOINT MONOTONICITY of A#B: monotone in B (conjugation + √-monotone) and
-- in A (achievability block + positive block-diagonal [[A'-A,0],[0,0]] via fromBlocks_diag_posSemidef +
-- maximality) ⟹ gmean_mono (A≤A',B≤B' ⟹ A#B≤A'#B'). The monotonicity needed for the dyadic bisection.
#print axioms QIQTH.Entropy.gmean_nested_superadditive
-- expected: standard only — DYADIC LADDER toward the general A#ₜB (hence A^{1-t}⊗B^t) family:
-- gmean_le_gmean_right (monotonicity in 2nd arg, via conjugation + operator √-monotonicity) +
-- gmean_nested_superadditive (the t=1/4 weighted-mean concavity A₀#(A₀#B₀)+A₁#(A₁#B₁) ≤
-- (A₀+A₁)#((A₀+A₁)#(B₀+B₁)), from superadditivity ×2 + monotonicity). Iterating gives all dyadic
-- weights; continuity gives the full A#ₜB family feeding Lieb's concavity.
#print axioms QIQTH.Entropy.wgmean_half
#print axioms QIQTH.Entropy.wgmean_zero
#print axioms QIQTH.Entropy.wgmean_one
#print axioms QIQTH.Entropy.gmean_rpow
#print axioms QIQTH.Entropy.wgmean_midpoint
#print axioms QIQTH.Entropy.continuous_matrix_rpow
#print axioms QIQTH.Entropy.continuous_wgmean
-- expected: standard only — EXPONENT CONTINUITY (the one Mathlib gap, now closed): t ↦ A^t continuous for
-- PosDef A, via the spectral formula A^t = V·diag(λᵢ^t)·Vᴴ (IsHermitian.cfc + rpow_eq_cfc_real), reducing to
-- scalar Real.continuous_const_rpow (λᵢ>0). Hence continuous_wgmean: t ↦ A#ₜB continuous. The last analysis
-- ingredient for lifting dyadic concavity to all t∈[0,1] via matrix_le_of_tendsto.
#print axioms QIQTH.Entropy.wgSuperadd_zero
#print axioms QIQTH.Entropy.wgSuperadd_one
#print axioms QIQTH.Entropy.wgSuperadd_midpoint
#print axioms QIQTH.Entropy.wgSuperadd_of_tendsto
#print axioms QIQTH.Entropy.wgSuperadd_dyadic
#print axioms QIQTH.Entropy.wgSuperadd_mem_Icc
-- expected: standard only — ★★★ CONTINUITY ARGUMENT COMPLETE: joint concavity of the weighted geometric
-- mean A#ₜB at EVERY t∈[0,1] (wgSuperadd_mem_Icc). wgSuperadd_of_tendsto (closed under limits, via
-- continuous_wgmean + matrix_le_of_tendsto) + wgSuperadd_dyadic (concavity at all dyadics k/2ⁿ by bisection
-- induction) + density of dyadics (⌊t·2ʲ⌋/2ʲ→t). This is Ando's full result A#ₜB jointly concave ∀t — the
-- last structural input to Lieb's concavity theorem (Carlen §6.1).
-- expected: standard only — BISECTION to joint concavity at all dyadic weights. WgSuperadd t = the two-point
-- superadditivity of A#ₜB; wgSuperadd_zero/one (endpoints A#_0B=A, A#_1B=B), wgSuperadd_midpoint (concavity
-- at s,t ⟹ at (s+t)/2, via wgmean_midpoint + gmean_superadditive + gmean_mono + wgmean_posDef). Repeated
-- bisection from {0,1} gives concavity at every dyadic k/2ⁿ; matrix_le_of_tendsto + exponent-continuity lift
-- to all t∈[0,1] — the joint concavity of A^{1-t}⊗B^t feeding Lieb (Carlen §6.1).
-- expected: standard only — the WEIGHT-MIDPOINT IDENTITY (Ando), the structural key to dense dyadic weights:
-- gmean_rpow (gmean(Cˢ)(Cᵗ)=C^{(s+t)/2}, the commuting collapse via rpow_add) ⟹ wgmean_midpoint
-- ((A#ₛB)#½(A#ₜB)=A#_{(s+t)/2}B) via gmean_congr with M=√A. Bisecting {0,1} gives joint concavity at every
-- dyadic weight k/2ⁿ (dense); matrix_le_of_tendsto then lifts it to all t∈[0,1] — the route to Lieb.
-- expected: standard only — WEIGHTED operator geometric mean A#ₜB = A^{1/2}(A^{-1/2}BA^{-1/2})^t A^{1/2}
-- (matrix rpow): endpoints wgmean_zero (=A), wgmean_one (=B), and wgmean_half (=A#B, the geometric mean,
-- via sqrt_eq_rpow). The interpolating object whose weight-midpoint identity (from gmean_congr) gives the
-- dense dyadic weights for the continuity argument toward Lieb.
#print axioms QIQTH.Entropy.gmean_congr
-- expected: standard only — CONGRUENCE COVARIANCE of the operator geometric mean (Ando): for invertible M,
-- (M X Mᴴ)#(M Y Mᴴ) = M(X#Y)Mᴴ. Proved from the variational characterization by conjugating the 2×2 block
-- by diag(M,M) (fromBlocks_multiply) + achievability/maximality both directions + le_antisymm. This is the
-- transformer invariance underlying the weight-midpoint identity (A#ₛB)#½(A#ₜB)=A#_{(s+t)/2}B → dense dyadics.
#print axioms QIQTH.Entropy.nestGmean_superadditive
-- expected: standard only — JOINT CONCAVITY AT EVERY DYADIC WEIGHT t=1/2ᵏ (the general A#ₜB family,
-- inductively): nestGmean k A₀ B₀ + nestGmean k A₁ B₁ ≤ nestGmean k (A₀+A₁)(B₀+B₁), where
-- nestGmean k = A #_{1/2ᵏ} B is the k-fold nested geometric mean. Induction on k via superadditivity +
-- monotonicity-in-2nd-arg. Continuity in t then gives all t, i.e. A^{1-t}⊗B^t concavity → Lieb (§6.1).
#print axioms QIQTH.Entropy.matrix_le_of_tendsto
#print axioms QIQTH.Entropy.add_le_of_tendsto
-- expected: standard only — LIMIT-STABILITY of the Loewner order (the continuity step's analytical core):
-- fᵢ≤gᵢ, fᵢ→a, gᵢ→b ⟹ a≤b, and aᵢ+bᵢ≤cᵢ + tendsto ⟹ a+b≤c. Transferred from the OrderClosedTopology of
-- the C⋆-algebra CStarMatrix across the bridge (ofMatrix_le_iff + ofMatrixL homeomorphism). Lets joint
-- concavity at the dense dyadic weights extend to all t — the limit step of Ando's route to Lieb.

/-! ### ★ EntropyBridge RETIRED — the final 6 axioms discharged (budget 6 → 0) -/

#print axioms QIQTH.EntropyBridge.bBridge
-- expected: standard only — ★ the bridge identity χ = ΔK − (S_ren(ω)−S_ren(σ)) as a THEOREM for the
-- concrete model (= Donald A1: D(ρ‖σ)=crossEnt(ρ,σ)−H(ρ), a `ring` identity in the trace terms).
#print axioms QIQTH.EntropyBridge.instEntropyBridgeHermitianMat
-- expected: standard only — the concrete Hermitian-matrix EntropyBridgeSystem instance; the witness
-- discharging the former 6 EntropyBridge axioms (RState/Sren_CPW/chi_R/dK_modular/refState/bridge_identity).
#print axioms QIQTH.EntropyBridge.EntropyBridgeSystem.chi_bound_from_dK_and_Sren_lower
-- expected: standard only — the transfer lemma, now a theorem over any EntropyBridgeSystem.
#print axioms QIQTH.EntropyBridge.fq_ambiguity_counterexample
-- expected: standard only — the χ vs S_ren counterexample (already axiom-free).

-- ARAKI RELATIVE ENTROPY via the relative modular operator (genuine object, finite-dim instance).
#print axioms QIQTH.Araki.exp_Lmul
#print axioms QIQTH.Araki.exp_Rmul
-- expected: standard only — exp naturality of L/R: exp(L_A)=L_{exp A}, exp(R_A)=R_{exp A} (R via the
-- opposite algebra), the engine for the operator log.
#print axioms QIQTH.Araki.exp_matLog
-- expected: standard only — exp(matLog A)=A through the EIGENVALUE cfc (matLog_UDU + Matrix.exp_conj/
-- exp_diagonal), dodging the L2-operator-norm-vs-eigenvalue-CFC instance diamond on Matrix.
#print axioms QIQTH.Araki.log_relMod
-- expected: standard only — ★ the operator log identity log Δ_{σ|ρ} = L_{log σ} − R_{log ρ} for the
-- relative modular operator Δ = L_σ R_ρ⁻¹, via relMod = exp(L_{logσ}−R_{logρ}) + CFC.log_exp.
#print axioms QIQTH.Araki.arakiEntropy_eq_relEntropy
-- expected: standard only — ★★ CONVENTION LOCK: the genuine Araki relative entropy
-- S(ρ‖σ) = −⟪ρ^½, log Δ_{σ|ρ} ρ^½⟫ reduces to the finite Umegaki entropy tr(ρ(log ρ − log σ)).
-- Certifies the σ-numerator/ρ-denominator convention. (Finite-dim Type I instance; continuum is the frontier.)

-- ★★★ FINITE TOMITA–TAKESAKI + CONNES MODULAR THEORY (2026-06-20, all axiom-free / standard only).
-- The relative modular flow Δ^{it}, its algebra action, Tomita σ_t(M)=M & JMJ=M', the Connes cocycle,
-- KMS, and the modular automorphism group — the complete finite modular theory on Hilbert–Schmidt space.
#print axioms QIQTH.Araki.arakiEntropy_nonneg
#print axioms QIQTH.Araki.relModFlow_add
#print axioms QIQTH.Araki.hasDerivAt_relModFlow
#print axioms QIQTH.Araki.hasDerivAt_relModFlow'
#print axioms QIQTH.Araki.continuous_relModFlow
-- expected: standard only — STONE GENERATOR d/dt Δ^{it}|₀ = i·K + FLOW (Heisenberg) EQUATION
-- d/dt Δ^{it} = Δ^{it}·(i·K) ∀t (K=logΔ=relModGen the modular Hamiltonian). Axiom-free.
#print axioms QIQTH.Araki.relModFlow_mem_unitary
#print axioms QIQTH.Araki.relModFlow_apply
#print axioms QIQTH.Araki.relModFlow_fix_gns
#print axioms QIQTH.Araki.relModFlow_eq_Lmul_Rmul
#print axioms QIQTH.Araki.relModFlow_conj_Lmul
#print axioms QIQTH.Araki.relModFlow_conj_Rmul
#print axioms QIQTH.Araki.connesCocycle
#print axioms QIQTH.Araki.connesCocycle_chain
#print axioms QIQTH.Araki.J_involutive
#print axioms QIQTH.Araki.J_Lmul_J
#print axioms QIQTH.Araki.J_Rmul_J
#print axioms QIQTH.Araki.J_inner
#print axioms QIQTH.Araki.kms_condition
#print axioms QIQTH.Araki.modAut_one
#print axioms QIQTH.Araki.modAut_mul
#print axioms QIQTH.Araki.modAut_conjTranspose
#print axioms QIQTH.Araki.modAut_add
#print axioms QIQTH.Araki.modAut_fix
#print axioms QIQTH.Araki.modAut_state_invariant
#print axioms QIQTH.Araki.relEntropy_modAut_invariant
#print axioms QIQTH.Araki.relEntropy_eq_neg_modGen
-- expected (ALL): standard only [propext, Classical.choice, Quot.sound]. Δ^{it} one-param unitary group
-- + GNS-invariance + Δ^{it}=L_{σ^{it}}R_{ρ^{-it}} + Tomita σ_t(M)=M / σ_t(M')=M' / JMJ=M' (J antiunitary)
-- + Connes cocycle (Dσ:Dρ)_t + chain rule + KMS + σ_t *-automorphism group + S(ρ‖σ)=−⟪ξ_ρ,(logΔ)ξ_ρ⟫.
#print axioms QIQTH.Araki.relEntropy_add_vonNeumann
#print axioms QIQTH.Araki.vonNeumann_le_modEnergy
-- expected: standard only — FIRST LAW: S(ρ‖σ)+S(ρ)=⟪K_σ⟫_ρ (modular energy, K_σ=−logσ) and the
-- first-law inequality S(ρ)≤⟪K_σ⟫_ρ (von Neumann entropy ≤ modular energy, = at ρ=σ). Axiom-free.
#print axioms QIQTH.Araki.firstLaw_saturation
-- expected: standard only — FIRST-LAW RIGIDITY: S(ρ)=⟪K_σ⟫_ρ ⟹ ρ=σ (saturated iff equilibrium),
-- from the decomposition + relEntropy_eq_zero (faithfulness). Axiom-free.

-- MODULAR RELATIVE ENTROPY (Phase B): the continuum one-particle (standard-subspace) relative-entropy
-- functional, built from the bounded RvD operator R=P+Q (NO unbounded log Δ).
#print axioms QIQTH.modChar_eq_exp_entropyDensity
-- expected: standard only — entropyDensity g(r)=log((2−r)/r) IS the modular-flow generator:
-- u_t(r)=exp(i·t·g(r)) on the spectrum interior. Identifies g as the modular Hamiltonian.
#print axioms QIQTH.cgpEntropy_zero
#print axioms QIQTH.rvdSpecMeasure_univ
-- expected: standard only — the one-particle modular relative entropy S(ξ)=−∫log((2−r)/r)dμ^R_ξ
-- (cgpEntropy) over the scalar spectral measure of R; total mass ‖ξ‖²; vanishes at the vacuum ξ=0.
-- Genuine continuum object (one-particle); full vN-algebra relative entropy needs Γ(Δ^{it}) (cited frontier).
#print axioms QIQTH.rvdSpec_integral_eq_re_inner
-- expected: standard only — ★ OPERATOR-EXPECTATION BRIDGE: for bounded measurable modular observable f,
-- ∫f dμ^R_ξ = re⟪ξ, f(R)ξ⟫ (f(R) = bounded Borel FC). Makes the (regularized) modular relative entropy
-- a genuine quantum expectation −re⟪ξ, K ξ⟫ of a bounded self-adjoint modular Hamiltonian, via the
-- diagonal reduction bilinDiag_self + inner_borelFC + diagInt + integral_ofReal.
#print axioms QIQTH.hasDerivAt_modChar
#print axioms QIQTH.rvdSpec_modUnitary
-- expected: standard only — DERIVATIVE BRIDGE (toward S=cgpEntropy): hasDerivAt_modChar (∂_t u_t(r) =
-- i·entropyDensity(r)·u_t(r), r∈(0,2) — the modular Hamiltonian g=entropyDensity is the flow generator, via
-- modChar_eq_exp_entropyDensity + HasDerivAt.cexp) and rvdSpec_modUnitary (the complex operator-expectation
-- bridge ⟨ξ,U_t ξ⟩=∫u_t dμ^R_ξ, via inner_borelFC + bilinDiag_self + diagInt). These feed differentiation
-- under the spectral integral to land S(ω_{W(f)Ω}‖ω_Ω)=cgpEntropy(f).
#print axioms QIQTH.cgpEntropy_eq_neg_re_inner
-- expected: standard only — ★★ BOUNDED-SPECTRUM CASE: when σ(R) ⊆ [a,2−a] stays away from the endpoints
-- {0,2} (0<a≤1), the one-particle modular relative entropy IS the operator expectation
-- S(ξ) = −⟪ξ, g(R) ξ⟫ of the bounded self-adjoint modular Hamiltonian g(R)=log((2−R)/R). Via the bridge
-- + entropyDensity_abs_le (|log((2−r)/r)| ≤ log((2−a)/a) on [a,2−a], by log-monotonicity cross-mult).
#print axioms QIQTH.hasFiniteEntropy_of_mem_Icc
#print axioms QIQTH.hasFiniteEntropy_smul
-- expected: standard only — FINITE-ENTROPY REGIME: HasFiniteEntropy S ξ := Integrable g μ^R_ξ (g diverges
-- at the endpoints {0,2}, so finiteness ⟺ μ^R_ξ not concentrating there). Regular regime σ(R)⊆[a,2−a] ⟹
-- finite (bounded g on finite measure, Integrable.mono'); vacuum finite; scale-invariant in the wavefunction.
#print axioms QIQTH.entropyDensity_reflect
#print axioms QIQTH.cgpDensity_nonneg
-- expected: standard only — CGP SUM-RULE scalar skeleton: g(2−r)=−g(r) (reflection symmetry, spectral
-- shadow of JΔJ=Δ⁻¹) + the manifestly-nonnegative CGP density 1_{(0,1)}((2−r)/r−1)g. The full sum rule
-- cgpEntropy=∫cgpDensity≥0 (for ξ∈𝒦) is GATED on the spectral balance (JRJ=2−R + Tomita fixedness ξ=JΔ^½ξ).
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdRC_modConj
-- expected: standard only — ★ J R J = 2 − R: the modular conjugation REFLECTS R (bounded shadow of the
-- canonical Tomita relation JΔJ=Δ⁻¹). From D(R−1)=−(R−1)D ⟹ DR=(2−R)D, transported to J via J(Tξ)=Dξ on
-- the dense range of T (T,R commute). CGP spectral-balance prerequisite 1 of 2.
#print axioms QIQTH.StandardSubspaceModular.rvdPmQ_eq_of_mem_K
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdT_of_mem_K
-- expected: standard only — ★ BOUNDED TOMITA FIXEDNESS: for ξ∈𝒦 (Pξ=ξ), D ξ = (2−R) ξ (and J(Tξ)=(2−R)ξ).
-- The bounded encoding of the Tomita fixedness ξ=JΔ^{1/2}ξ (𝒦 = +1 eigenspace of S=JΔ^{1/2}), avoiding the
-- unbounded Δ^{1/2}: from R=P+Q, D=P−Q, Pξ=ξ ⟹ Qξ=Rξ−ξ ⟹ Dξ=2ξ−Rξ. CGP prerequisite 2 of 2 — BOTH NOW
-- DONE; the spectral balance ∫(2−r)²F dμ_ξ=∫r(2−r)F(2−r)dμ_ξ (then ÷r²) is now fully bounded.
#print axioms QIQTH.StandardSubspaceModular.modConj_cfcΩ
#print axioms QIQTH.StandardSubspaceModular.reInner_modConj_cfcΩ
-- expected: standard only — ★ CONTINUOUS J-CONJUGATION J·f(R)=(twΩ f)(R)·J (extends JRJ=2−R to the whole
-- continuous FC, via cfcΩ_intertwine D·f(R)=(twΩ f)(R)·D + J(Tξ)=Dξ on dense range T) and its inner-product
-- form ⟪Jη,f(R)Jη⟫_ℝ=⟪η,(twΩ f)(R)η⟫_ℝ (the SPECTRAL REFLECTION, = the measure reflection μ_{Jη}=(2−·)_*μ_η
-- at the real-bilinear level). The operator+inner-product engine of the CGP measure reflection.
#print axioms QIQTH.cfcΩ_reInner_eq_integral
#print axioms QIQTH.rvdSpec_reflect
-- expected: standard only — ★★ THE MEASURE REFLECTION μ^R_{Jη} = (2−·)_* μ^R_η: ∫F∘inclΩ dμ_{Jη} =
-- ∫F∘(2−·)∘inclΩ dμ_η for continuous F. Lifts the inner-product reflection (reInner_modConj_cfcΩ) to the
-- measure via the cfcΩ↔borelFC bridge (cfcΩ_eq_borelFC: cfcΩ is literally borelFC∘inclΩ, by cfcCont's
-- definition + bound-independence) + cfcΩ_reInner_eq_integral (re⟪ξ,f(R)ξ⟫=∫F∘inclΩ dμ, via the operator-
-- expectation bridge) + twΩ_ofRealΩ. The first measure-theoretic step of the CGP spectral balance.
#print axioms QIQTH.cfcΩ_weight
-- expected: standard only — ★ THE h(R)-WEIGHTING: ∫F dμ^R_{h(R)ξ} = ∫h²·F dμ^R_ξ for real continuous h,F
-- (spectral measure at h(R)ξ is h² times that at ξ). Via h(R) self-adjoint (cfcΩ_ofRealΩ_adjoint) +
-- adjoint_inner_right + multiplicativity h(R)F(R)h(R)=(h²F)(R) (cfcΩ_mul + ofRealΩ_mul). The second
-- measure ingredient of the CGP balance; with the reflection + (2−R)ξ=J(Tξ) ⟹ ∫(2−r)²F dμ=∫r(2−r)F(2−r)dμ.
#print axioms QIQTH.rvdSpec_twoSubR
#print axioms QIQTH.rvdSpec_T
#print axioms QIQTH.rvdSpec_balance
-- expected: standard only — ★★ THE CGP POLYNOMIAL SPECTRAL BALANCE for ξ∈𝒦: ∫(2−r)²F(r)dμ_ξ =
-- ∫r(2−r)F(2−r)dμ_ξ. The bounded (cleared-denominator) form of the Tomita spectral balance. Assembles the
-- two measure engines — μ_{(2−R)ξ}=(2−r)²μ_ξ (rvdSpec_twoSubR, the h(R)-weighting at h=2−R) and
-- μ_{Tξ}=r(2−r)μ_ξ (rvdSpec_T, via T self-adjoint + T²=R(2−R) by rvdT_sq, NO √-functional-calculus) —
-- with the measure reflection μ_{Jη}=(2−·)_*μ_η (rvdSpec_reflect) + bounded Tomita fixedness (2−R)ξ=J(Tξ)
-- (modConj_rvdT_of_mem_K). R, 2−R realized as cfcΩ-images of real coordinates (rvdRC_eq_cfcΩ,
-- rvdTwoSubRC_eq_cfcΩ). This is the heart of the CGP relative-entropy positivity for localized states.
#print axioms QIQTH.cgpEntropy_nonneg
-- expected: standard only — ★★★ THE CGP RELATIVE-ENTROPY POSITIVITY: 0 ≤ S(ξ) for ξ∈𝒦 (projK ξ = ξ) in
-- the regular regime σ(R)⊆[a,2−a]. The localized one-particle instance of S(ρ‖σ)≥0, axiom-free from RvD
-- bounded Tomita–Takesaki. From rvdSpec_balance at the clamped representative of g/(2−r)² (clampF) ⟹ divided
-- balance ∫g dμ = −∫((2−r)/r)g dμ ⟹ S(ξ)=∫((1−r)/r)·log((2−r)/r) dμ, integrand ≥0 on all of (0,2) (no
-- (0,1)-split). Localization essential (point mass at r<1 gives S<0). Full vN-algebra S(ρ‖σ) via Γ(Δ^{it})
-- second quantization = cited Phase C frontier.
#print axioms QIQTH.Fock.secondQuantModFlow_add
#print axioms QIQTH.Fock.secondQuantModFlowH_vacuum
#print axioms QIQTH.Fock.secondQuantModFlowH_add
-- expected: standard only — PHASE C: Γ(Δ^{it}) the SECOND-QUANTIZED MODULAR FLOW on Fock space. The
-- one-particle modular flow Δ^{it}=modUnitary S t (unitary, modUnitary_add group law) is second-quantized
-- via the generic functor secondQuantPre to Γ(Δ^{it}) on FockPre H and (by completion) the Fock HILBERT
-- space — a one-parameter group of isometries fixing the vacuum (secondQuantModFlowH_{add,zero,vacuum,
-- isometry}). The field-level modular automorphism group's implementing unitaries (Bisognano–Wichmann: the
-- free-field local algebra's modular op IS Γ(Δ) of the standard-subspace modular op). Full vN-algebra
-- relative ENTROPY additionally needs the relative modular operator for two states (CGP reduces it to the
-- one-particle cgpEntropy, already proved ≥0).
#print axioms QIQTH.Fock.secondQuantModFlow_weyl
#print axioms QIQTH.Fock.secondQuantModFlowH_weylH
-- expected: standard only — PHASE C: TOMITA'S THEOREM AT THE FIELD LEVEL. σ_t(W(u))=Γ(Δ^{it})W(u)Γ(Δ^{-it})=
-- W(Δ^{it}u): the second-quantized modular flow maps the CCR/Weyl algebra onto itself, transporting the test
-- function by the one-particle modular flow (σ_t(M)=M). Engine = weylCoeff_isometry_invariant (Γ(A)W(u)=
-- W(Au)Γ(A)) specialized to A=Δ^{it}. Both pre-Fock and Fock-Hilbert (via Completion.map_comp) levels.
#print axioms QIQTH.Fock.weylVacuum_modFlow_invariant
#print axioms QIQTH.Fock.secondQuantModFlowH_continuous_expVec
-- expected: standard only — PHASE C: (a) the VACUUM IS THE MODULAR STATE: ⟪Ω,W(Δ^{it}u)Ω⟫=⟪Ω,W(u)Ω⟫ (the
-- quasifree vacuum state is σ_t-invariant, since ⟪Ω,W(v)Ω⟫=exp(−½⟪v,v⟫) and Δ^{it} preserves ⟪v,v⟫); (b)
-- STRONG CONTINUITY of Γ(Δ^{it}) on coherent vectors: t↦Γ(Δ^{it})e(f) continuous = continuous_FockExpVec
-- (coherent map f↦e(f) continuous, from ⟪e(f),e(g)⟫=exp⟪f,g⟫) ∘ modUnitary_stronglyContinuous — the
-- second-quantized lift of the one-particle Stone generator. Γ(Δ^{it}) is a genuine modular flow.
#print axioms QIQTH.Fock.relModFlowH_zero
#print axioms QIQTH.Fock.connesCocycle_eq
-- expected: standard only — PHASE C: the RELATIVE MODULAR OPERATOR of a coherent state W(f)Ω relative to the
-- vacuum, Δ_{W(f)Ω|Ω}^{it}=W(f)Γ(Δ^{it})W(f)⋆ (relModFlowH, bounded Weyl conjugate — Araki Δ_{uΩ|Ω}=uΔ_Ω u⋆).
-- HEADLINE connesCocycle_eq: the Connes cocycle (Dω_{W(f)Ω}:Dω_Ω)_t = Δ_{rel}^{it}Δ_Ω^{-it} = W(f)W(−Δ^{it}f),
-- a PRODUCT OF WEYL OPERATORS — the Araki/Connes formula for a coherent excitation, immediate from the Tomita
-- covariance secondQuantModFlowH_weylH + group law. The full relative entropy S(ω_{W(f)Ω}‖ω_Ω) reduces (CGP)
-- to the one-particle cgpEntropy already proved ≥0. General two-state relative modular ops = unbounded-GNS frontier.
#print axioms QIQTH.Fock.relModFlowH_add
#print axioms QIQTH.Fock.connesCocycleH_chain
-- expected: standard only — PHASE C: the relative modular flow is a ONE-PARAMETER GROUP (relModFlowH_add:
-- Δ_rel^{is}Δ_rel^{it}=Δ_rel^{i(s+t)}, the inner W(f)⋆W(f) cancels), and the Connes cocycle satisfies the
-- CHAIN RULE u_{s+t}=u_s·σ_s(u_t) (σ_s=Ad Γ(Δ^{is}); Connes' Radon–Nikodym) — both immediate from the Tomita
-- covariance + group law. Confirms relModFlowH/connesCocycleH are GENUINE modular flow / Connes cocycle objects.
#print axioms QIQTH.Fock.relModFlow_vacuum_char
-- expected: standard only — PHASE C: THE VACUUM CHARACTERISTIC FUNCTION of the relative modular flow,
-- ⟨Ω,Δ_{W(f)Ω|Ω}^{it}Ω⟩ = exp(⟨f,Δ^{it}f⟩−⟨f,f⟩). The bounded generating function of the coherent-state
-- relative entropy: its t-derivative at 0 = i·cgpEntropy(f) (= ∫(u_t−1)dμ^R_f, d/dt|0 u_t = i·entropyDensity).
-- Proof: push relModFlowH to pre-Fock (map_coe) ⟹ coherent vector weylCoeff(−f,0)·weylCoeff(f,−Δ^{it}f)·
-- e(f−Δ^{it}f), then fockInner + Weyl-coeff collapse. The bounded bridge to cgpEntropy (deriv step = remaining).
#print axioms QIQTH.Fock.hasDerivAt_relModFlow_vacuum
-- expected: standard only — ★★★ THE ENTROPY REDUCTION (loop CLOSED): d/dt|₀ ⟨Ω,Δ_{W(f)Ω|Ω}^{it}Ω⟩ =
-- −i·cgpEntropy(f), so S(ω_{W(f)Ω}‖ω_Ω) = i·d/dt|₀⟨Ω,Δ_rel^{it}Ω⟩ = cgpEntropy(f) — the Fock-level coherent-
-- state Araki relative entropy IS the one-particle CGP entropy (proved ≥0). Chain rule on the characteristic
-- function (relModFlow_vacuum_char) + hasDerivAt_inner_modUnitary (differentiation under the spectral integral,
-- via Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le with constant dominating bound log((2−a)/a)) +
-- ∫entropyDensity dμ = −cgpEntropy. Regular regime σ(R)⊆[a,2−a]. Full coherent-state Araki entropy DONE.

-- ★ BORN — the exact missing premise (RefinementBorn.lean): records ⇏ Born; refinement additivity ⇒ Born.
#print axioms QIQTH.RefinementBorn.alphaSqMeasure_sum
-- expected: standard only — the α=2 record measure μ₂(k)=w_k²/Σw_j² is a genuine probability (sums to 1).
#print axioms QIQTH.RefinementBorn.alphaSq_ne_born
-- expected: standard only — ★ records ⇏ Born: μ₂ on (1/3,2/3) gives 1/5 ≠ 1/3 (Born). A rule meeting every
-- record fact (definite, redundant-agreeing, support/certainty, label-symmetric, product-independent) can be non-Born.
#print axioms QIQTH.RefinementBorn.sq_not_additive
-- expected: standard only — (·)² is not additive: the precise premise (refinement indifference) the α=2 rule violates.
#print axioms QIQTH.RefinementBorn.additive_fMeasure_eq_born
-- expected: standard only — ★ refinement additivity (f : ℝ →+ ℝ) ⇒ Born on rational weights. Additivity IS the
-- exponent-fixer; records do not supply it. Whether finite capacity/H2 motivates it is the open physics question.
#print axioms QIQTH.RefinementBorn.continuous_additive_fMeasure_eq_born
-- expected: standard only — ★ additivity + CONTINUITY ⇒ Born on ALL REAL weights (closes the "irrational |c_k|²"
-- residual). additive_fMeasure_eq_born only reaches RATIONAL weights — additivity forces f(x)=x·f(1) on ℚ alone
-- (pathological Hamel-basis additive fns disagree on irrationals). The physically-natural continuity premise
-- excludes them: a continuous additive f:ℝ→+ℝ is ℝ-linear (AddMonoidHom.toRealLinearMap), so f(x)=x·f(1) ∀x∈ℝ.
-- GOTCHA: hlin matches f at ANY arg incl f 1, so simp_rw[hlin] loops — use Finset.sum_congr + hlin(w j) instead.
#print axioms QIQTH.RefinementBorn.alphaSq_refinement_violation
-- expected: standard only — ★ the precise mechanism: refining (1/3,2/3)'s 2/3 outcome into two equal 1/3 sub-records
-- (uniform triple), coarse μ₂ = 4/5 but fine sum = 2/3; 4/5 ≠ 2/3 ⇒ α=2 violates refinement indifference exactly.

-- ★ BORN layer 1 — SBS ⇒ Boolean record algebra / objectivity, Born-free (SBSBoolean.lean):
#print axioms QIQTH.SBSBoolean.record_unique
-- expected: standard only — a nonzero state can't lie in two orthogonal pointer sectors (records unambiguous).
#print axioms QIQTH.SBSBoolean.fragments_co_referential
-- expected: standard only — ★ redundant SBS readouts agree ⇒ all functions of one classical pointer K₀
-- (definiteness, NO Born weights — only orthogonality/support, nothing Born-flavoured smuggled in).

-- ★ BORN route 4 — no-signaling under refinement ⇒ Born (RefinementBorn.lean, per GPT-5.5-pro):
#print axioms QIQTH.RefinementBorn.refinementNatural_additive
-- expected: standard only — ★ refinement-naturality (coarse prob = sum of fine probs; = no-signaling under
-- remote record refinement) + f>0 ⇒ f(x+y)=f x+f y. Compose with additive_fMeasure_eq_born ⇒ Born.
#print axioms QIQTH.RefinementBorn.id_refinementNatural
-- expected: standard only — Born (f=id) IS refinement-natural (easy direction; abstract counterpart of
-- bipartite_no_signaling / bornNet_no_signaling). With refinementNatural_additive: natural ⟺ Born (the iff).

-- ★ BORN selector (λ) layer — Gap 3 reduces to a Gap-2 bridge (SelectorRefinement.lean, per GPT-5.5-pro):
#print axioms QIQTH.SelectorRefinement.readout_invariant_marg
-- expected: standard only — Born-free bridge: remote refinement leaving the local readout unchanged
-- (XL∘R=XL, selector-level microcausality) ⇒ local marginal invariant (selector no-signaling). The Gap-2 input.
#print axioms QIQTH.SelectorRefinement.Countermodel.alphaSq_selector_signals
-- expected: standard only — ★ SEPARATION: a deterministic α=2 selector over a fixed uniform measure on 15
-- microstates has coarse cell 12 ≠ 5+5=10 merged fine cells ⇒ selector no-signaling FAILS while the trace
-- no-signaling theorem holds ⇒ existing microcausality does NOT force selector no-signaling (Gap 3 ⇏ closed).
-- BORN-A1 Stage 1: Actuality Projective Consistency — honest coarse-graining selectors satisfy APC automatically:
#print axioms QIQTH.BornActualityConsistency.marg_coarseGrain
-- BORN-A1 Stage 2: APC ⟺ additivity (the honest §4 equivalence — Born's premise reframed as selector no-signaling):
#print axioms QIQTH.BornActualityConsistency.apc_iff_positiveAdditive
-- BORN-C Stage 1: μ-selection — equivariance (quantum equilibrium) ⟹ selector no-signaling:
#print axioms QIQTH.BornMuSelection.equivariant_no_signaling
-- BORN-C Stage 2-3: equivariance ⟹ context-independent (non-contextual) marginals; martingale selection:
#print axioms QIQTH.BornMuSelection.equivariant_context_independent
#print axioms QIQTH.BornMuSelection.mu_selection_martingale
-- A1-ppwave Stage 1: the pp-wave metric, its inverse, symmetry and g·gi=I:
#print axioms QIQTH.Curvature.ppMetric_inv
-- A1-ppwave Stage 2-3: Γ^μ_{ν1}≡0 ⟹ ∂_v covariantly constant ⟹ hWgeo/hWequil on a CURVED metric:
#print axioms QIQTH.Curvature.christoffel_ppMetric_last_one
#print axioms QIQTH.Curvature.ppMetric_raychaudhuri_setup
-- A1-ppwave Stage 4 (partial): Γ^x_uu = −½∂_x H — the connection is H-dependent (full Ric≠0 documented frontier):
#print axioms QIQTH.Curvature.christoffel_ppMetric_x_uu
-- A1+A2 worked-example Stage 1: pp-wave metric/inverse smoothness (hCg/hCgi) for smooth H:
#print axioms QIQTH.Curvature.ppMetric_contDiff
-- A1+A2 Stage 2: explicit pp-wave tetrad — frame congruence hcong + invertibility hPP/hPP':
#print axioms QIQTH.Curvature.ppFrame_cong
-- A1+A2 worked example: QIQT→GR for the explicit pp-wave spacetime (all geometry discharged; FQ carried):
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_ppwave
-- The SHOWCASE: pp-wave QIQT→GR, floor laid bare — geometry + hA + hbound discharged; only EOM + P4 + localization:
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_ppwave_showcase
#print axioms QIQTH.SelectorRefinement.local_factor_remote_invariant
-- expected: standard only — Gap-2 milestone 1: selector-locality (local marginal factors through ρ_A) +
-- ρ_A-preservation under remote refinement ⇒ local marginal remote-invariant (the "remote" half of the bridge).
#print axioms QIQTH.SelectorRefinement.equivariant_marg_invariant
-- expected: standard only — ★ Gap-2 milestone 3a (equilibrium core): EQUIVARIANCE (μ-preserving remote
-- dynamics R) ⇒ every local marginal R-invariant = selector no-signaling, Bell-compatibly (no pointwise
-- locality, which Bell.chsh_lhv would cap at |CHSH|≤2). Isolates the load-bearing Gap-2 input: (R)_*μ=μ.

-- ★ BORN Gap-2 Phase 3c SCAFFOLD — the (Φ,λ) selection-dynamics model (SelectionDynamics.lean):
#print axioms QIQTH.SelectionDynamics.SelectionModel.no_signaling
-- expected: standard only — any equivariant SelectionModel has selector no-signaling (wires the model to 3a).
#print axioms QIQTH.SelectionDynamics.uniformModel_no_signaling
-- expected: standard only — Born-agnostic instance: uniform μ preserved by ANY bijective remote action ⇒
-- equivariant ⇒ no-signaling for free, with a measure assuming nothing about Born. Open core = Born marginals
-- + equivariance of the ACTUAL non-uniform dynamical μ (the Gap-2 frontier).
#print axioms QIQTH.SelectionDynamics.marg_uniform_eq_card
-- expected: standard only — over uniform μ the marginal of k = the number of fine microstates selecting k.
#print axioms QIQTH.SelectionDynamics.born_from_uniform
-- expected: standard only — ★★ UNIFORM TYPICALITY REPRODUCES BORN: a deterministic selector over the
-- Born-agnostic uniform measure with M·w_k microstates per outcome k has normalised marginal = w_k (Born).
-- The Zurek envariance route as a selection model; sole residual = the fine-graining encodes the weights
-- (= the refinement-additivity premise of RefinementBorn). Born-agnostic μ + that residual ⇒ Born.
#print axioms QIQTH.RefinementBorn.sq_not_refinementNatural
-- expected: standard only — the α=2 rule is NOT refinement-natural (it would signal); the α-family is
-- exactly excluded by no-signaling. So: no-signaling under refinement ⇒ Born; without it, every α survives.

-- BornRoutes.lean — GPT-5.5-pro 2026-06-13 attack routes (see paper_strategy/50_Born_Attack_Routes.md).
#print axioms QIQTH.BornRoutes.additive_nat_linear
-- expected: standard only — Route C core: additive count F ⇒ F(n)=n·F(1) ⇒ Born weights on the grid.
#print axioms QIQTH.BornRoutes.born_from_martingale
-- expected: standard only — martingale/optional-stopping Born: μ-conserved squared weight + absorbing
-- 0/1 record + initial w_k ⇒ μ(outcome k) = w_k. Born-strength premise = the martingale conservation.
#print axioms QIQTH.BornRoutes.sqRule_refinement_signals
-- expected: standard only — meta no-go witness: the α=2 rule signals under [2,2]→[1,1,2] refinement
-- (1/2 vs 1/3) while Born stays 1/2; so any premise the whole power-family obeys cannot entail Born.

#print axioms QIQTH.SelectionDynamics.SelectionModel.expectation_conserved
-- expected: standard only — equivariance ⇒ μ-expectation of every observable conserved under the
-- selection step (the martingale-increment condition); discharges born_from_martingale's hmart in the
-- equivariant model, collapsing the open content to "the (Φ,λ) dynamics preserves a Born-agnostic μ".

-- Envariance.lean — Zurek's equal-amplitude Born half (companion to born_from_uniform).
#print axioms QIQTH.Envariance.envariance_equal_marg
-- expected: standard only — a μ-preserving swap implementing the a↔b label swap ⇒ equal marginals
-- (equal-amplitude branches equiprobable), with no Born assumption.
#print axioms QIQTH.Envariance.envariance_forces_uniform
-- expected: standard only — total transposition-envariance ⇒ μ constant; DERIVES the uniform
-- Born-agnostic measure that born_from_uniform had to assume.

-- Relaxation.lean — the swing at the physics (GPT-5.5-pro 2026-06-13): derive measure-preservation
-- from reversibility, plus the circularity no-go.
#print axioms QIQTH.Relaxation.resetKernel_reaches
-- expected: standard only — NO-GO: any full-support ν is the unique attracting equilibrium of the
-- reset kernel, so relaxation alone does NOT select Born (the H-theorem circularity detector).
#print axioms QIQTH.Relaxation.inducedKernel_col
-- expected: standard only — THE ADVANCE: a reversible closed update F:S×E≃S×E over a uniform bath
-- induces a COLUMN-stochastic selector kernel; bistochasticity is derived from the bijection, not assumed.
#print axioms QIQTH.Relaxation.uniform_stationary_of_colStochastic
-- expected: standard only — column-stochastic ⇒ uniform (Born-counting) measure is stationary.
#print axioms QIQTH.Relaxation.doeblin_contraction
-- expected: standard only — ε-minorized kernel contracts ℓ¹ distance by (1−|Ω|ε): the relaxation half.
#print axioms QIQTH.Relaxation.relaxation_to_uniform
-- expected: standard only — reversibility (col-stochastic) + uniform bath + mixing (ε-minorization) ⇒
-- every μ relaxes geometrically to uniform = Born. The finite H-theorem, all premises explicit.

-- RankCountNoGo.lean — GPT-5.5 consult 2026-06-13: decoherence cannot encode the weights in record counts.
#print axioms QIQTH.RankCountNoGo.no_multiplicity_rule_is_born
-- expected: standard only — no amplitude-independent record-multiplicity rule equals Born (multiplicity is
-- state-independent, Born is state-dependent). Closes Path A; Born needs an irreducible Hilbert-typicality axiom.
#print axioms QIQTH.RankCountNoGo.multRule_ne_born_of_differs
-- expected: standard only — the core: a state-independent rule can't match Born across two differing states.

-- BornChain.lean — the Path-B capstone: Gleason makes the irreducible noncontextual-typicality axiom = Born.
#print axioms QIQTH.BornChain.noncontextual_forces_born
-- expected: standard only — a noncontextual probability assignment (EffectMeasure) is FORCED to the Born
-- trace form Re tr(ρE) on every effect (finite effect-Gleason). The Gleason-uniqueness link, forward.
#print axioms QIQTH.BornChain.born_is_noncontextual
-- expected: standard only — converse: every density matrix yields such a noncontextual assignment; so the
-- noncontextual functionals are exactly the Born functionals (the axiom pins Born uniquely).

-- RotationBorn.lean — GPT-5.5 consult 2026-06-13: why exponent 2 (Banach–Lamperti core).
#print axioms QIQTH.RotationBorn.rotation_invariant_iff_exponent_two
-- expected: standard only — Σ|c_k|^α is rotation- (mixing-) invariant iff α=2; the square is the unique
-- power-law normalization preserved by continuous unitary mixing.
#print axioms QIQTH.RotationBorn.lpow_rotation_invariant_forces_two
-- expected: standard only — the no-go half: α≠2 is broken by the explicit 45° rotation witness on (1,0).

-- SymmetrySquare.lean — GPT-5.5-pro consult 2026-06-13: bell curve = Born's square (Maxwell–Herschel) +
-- boost no-go.
#print axioms QIQTH.SymmetrySquare.gaussian_profile_from_rotation
-- expected: standard only — rotation/U(2)-product invariance ⇒ Gaussian profile with the |z|² quadratic =
-- the same square Born uses (the bell-curve↔Born bridge, integer radial values).
#print axioms QIQTH.SymmetrySquare.no_boost_invariant_positive_norm
-- expected: standard only — no boost-invariant positive probability norm exists (indefinite signature);
-- relativistic Born comes from the unitary (Wigner) rep, not spacetime-boost invariance.

-- WeylBitConsistency.lean — the free-field Born histories are a CONSISTENT SET (2026-06-15).
#print axioms QIQTH.Fock.weak_decoherence_bit
-- expected: standard only — the consistency atom: Re D(α,β)=0 for the two outcomes of one Weyl bit
-- (Gell-Mann–Hartle WEAK decoherence / consistency), proved EXACTLY (no N→∞), = bit_normSq_sum.
#print axioms QIQTH.Fock.weak_decoherence_context
-- expected: standard only — weak decoherence in any commuting context (single-bit coarse-graining):
-- the whole projective Born family μ∞ rests on a consistent set.
#print axioms QIQTH.Fock.bell_marginal_sum_rule
-- expected: standard only — the Bell two-record wing marginal obeys the Born sum rule (consistency
-- made operational: the marginal probability is well-defined).

-- WeylBitStrongDecoherence.lean — full D=0 (GMH medium; with orthogonal records, strong) (2026-06-15).
#print axioms QIQTH.Fock.vacuum_bit_strong_decoherence
-- expected: standard only — single Weyl bit on the vacuum is EXACTLY orthogonal (full D=0, not just
-- weak Re D=0), because the vacuum Weyl one-point function is real.
#print axioms QIQTH.Fock.bell_two_bit_strong_decoherence
-- expected: standard only — for orthogonal record modes ⟪u,v⟫=0, the maximally-different Bell history
-- vectors vec(+,+) and vec(−,−) are exactly orthogonal: closes the multi-bit-differing residual with
-- full D=0 (GMH medium + orthogonal records). NON-orthogonal modes give a nonzero overlap correction
-- (record-overlap term ∝ Re⟪u,v⟫, SBS-suppressed, cited).
#print axioms QIQTH.Fock.bitOp_vac_expVec_cross_eq
-- expected: standard only — the EXACT overlap-correction formula: cross term = weylCoeff(v,0)·
-- (exp⟪v,w⟫ − exp(−⟪v,w⟫))/4; vanishes iff ⟪v,w⟫=0 (the strong-decoherence orthogonality condition).
#print axioms QIQTH.Fock.strong_decoherence_needs_orthogonality
-- expected: standard only — witnessed countermodel over H=ℂ (v=w=1): the cross term is nonzero, so the
-- orthogonality hypothesis of bell_two_bit_strong_decoherence is NECESSARY (overlapping records ≠ strong).

-- BornEquiprobable.lean — Born from symmetric equiprobability (audit candidate ii) (2026-06-15).
#print axioms QIQTH.BornEquiprobable.norm_sum_orthonormal_sq
-- expected: standard only — ‖∑_{i∈s} fᵢ‖² = |s| for an orthonormal family (the amplitude↔count identity).
#print axioms QIQTH.BornEquiprobable.uniform_marginal_eq_sectorAmp_sq
-- expected: standard only — the Zurek amplitude→count bridge: uniform-measure outcome marginal = squared
-- sector amplitude (= Born weight); discharges the posited count=M·w_k of SelectionDynamics.born_from_uniform.
#print axioms QIQTH.BornEquiprobable.born_from_equiprobability
-- expected: standard only — symmetric equiprobability over an equal-amplitude orthonormal fine-graining gives
-- Born empirical frequencies; residual = envariance symmetry + existence of the fine-graining (both Born-free).

-- EnvarianceJustification.lean — the envariance symmetry is structurally forced for equal amplitudes (2026-06-15).
#print axioms QIQTH.EnvarianceJustification.joint_perm_coeff
-- expected: standard only — the joint permutation U_S⊗U_E relabels amplitudes by c ↦ c∘σ⁻¹ (so it fixes
-- the entangled state iff c is σ-invariant).
#print axioms QIQTH.EnvarianceJustification.envariance_swap_invariant
-- expected: standard only — the a↔b swap (undone by the environment counter-swap) fixes ψ iff c a = c b:
-- "equal amplitudes ⇒ envariant", with the symmetry exhibited as a unitary, not posited. Reduces the
-- envariance residual of BornEquiprobable to state-supervenience (probabilities depend only on the state).
#print axioms QIQTH.EnvarianceJustification.phase_perm_coeff
#print axioms QIQTH.EnvarianceJustification.envariance_phase_swap_invariant
#print axioms QIQTH.EnvarianceJustification.phase_compensation_unitary_iff
-- expected: standard only — ★ EQUAL-MODULUS ENVARIANCE (closes the named "only c_a=c_b, not |c_a|=|c_b|"
-- gap). phase_perm_coeff: phase-weighted env permutation UE(e_k)=φ_k•e_{σk} relabels-and-rephases
-- amplitudes by c_k↦c_{σ⁻¹k}·φ_{σ⁻¹k}. envariance_phase_swap_invariant: the PHASE-COMPENSATED swap
-- UE(e_a)=(c_b/c_a)•e_b, UE(e_b)=(c_a/c_b)•e_b fixes ψ for ANY non-zero c_a,c_b (the phases cancel the
-- mismatch) — generalising envariance_swap_invariant beyond the aligned case. phase_compensation_unitary_iff:
-- the phase factor c_b/c_a has modulus 1 (⇒ UE unitary on orthonormal records = a GENUINE symmetry) EXACTLY
-- when ‖c_a‖=‖c_b‖. HONEST: the fixing is algebraic; legitimacy (unitarity) holds iff equal modulus, so this
-- does NOT permit swapping unequal-probability branches. Closes Born envariance to equal-modulus (was: aligned).

-- StateSupervenience.lean — argument (a): the (Φ,λ) ontology forces state-supervenience (2026-06-15).
#print axioms QIQTH.StateSupervenience.NaturalTypicality.stabilizer_invariant
-- expected: standard only — a relabelling-natural typicality is invariant under state-fixing symmetries.
#print axioms QIQTH.StateSupervenience.NaturalTypicality.envariance_equiprob
-- expected: standard only — naturality + an envariance symmetry (g•Φ=Φ, g•a=b) ⇒ T Φ a = T Φ b. The SYMMETRY
-- fragment of Born; naturality is necessary but NOT sufficient (α-family T_q is natural+equiprob, non-Born) —
-- Born also needs refinement-additivity (RefinementBorn), equal-norm canonicity, continuity, independence.

-- HolographyScaffolding.lean — how much holography λ's law needs: only finiteness, not the area-bound (2026-06-15).
#print axioms QIQTH.HolographyScaffolding.measure_needs_only_finiteness
-- expected: standard only — λ's law (the σ-additive Born measure) exists for any finite-fiber net, with NO
-- area/ℓ_P/Q_R in hypothesis or proof; holography is sufficient grounding for the finiteness, not required.
#print axioms QIQTH.HolographyScaffolding.records_finite_of_holographic_bound
-- expected: standard only — the holographic count bound (inject into Fin ⌊e^{Q_R}⌋) ⇒ finiteness (sufficiency).

-- WeylBitBell.lean — OP3b concrete Bell embedding: no-signaling FROM the record measure (2026-06-15).
#print axioms QIQTH.Fock.bell_no_signaling_state
-- expected: standard only — no-signaling is STATE-INDEPENDENT: for ANY global state ψ (entangled included),
-- summing Bob's record outcome gives Alice's marginal ‖A(u,σ_A)ψ‖², independent of Bob's mode v. Causality
-- always; Bell-violation iff the state is entangled (state-dependent, via the abstract Tsirelson).
#print axioms QIQTH.Fock.bell_no_signaling_setting_indep
-- expected: standard only — operational no-signaling (any state): two Bob settings v,v' give the SAME Alice marginal.

-- ContextualitySafe.lean — OP3b Bell-marginal check: λ-measure is contextuality-safe (2026-06-15).
#print axioms QIQTH.ContextualitySafe.no_global_record_valuemap
-- expected: standard only — no global value-map (LHVModel over all 4 settings) reaches |CHSH|>2; so λ is not
-- a noncontextual value-map over incompatible settings.
#print axioms QIQTH.ContextualitySafe.contextuality_safe
-- expected: standard only — a quantum/record correlation >2 (Tsirelson) has no global value-map; combined
-- with per-context no-signaling (NoSignalingGeneral.bipartite_no_signaling), actual-context-only is forced
-- and consistent — dodging the Fine/Bell global-distribution obstruction without smuggling non-quantum input.

-- CovariantGluing.lean — OP3b: covariant MEASURE exists, covariant SELECTOR cannot (2026-06-15).
#print axioms QIQTH.CovariantGluing.no_covariant_selector
-- expected: NO axioms at all — no equivariant Φ↦λ selector exists when the symmetric state's actual histories
-- form a nontrivial orbit (the S² obstruction); so λ is a symmetry-breaking SAMPLE of the covariant law,
-- not a covariant function. The covariant MEASURE half is weylBit_typicality_lorentzBoost_invariant.
#print axioms QIQTH.CovariantGluing.bool_swap_no_selector
-- expected: NO axioms at all — finite S²-analog witness (Bool histories swapped, unique symmetric state):
-- no covariant selector, while the uniform measure is invariant (uniform_invariant). The dichotomy.

-- RedundancyCompressible.lean — redundant records are compressible: the category-error core (2026-06-15).
#print axioms QIQTH.RedundancyCompressible.card_redundantCodewords
-- expected: standard only — # distinguishable R-fold redundant records = |X| (R-independent), NOT |X|^R.
#print axioms QIQTH.RedundancyCompressible.naive_overcounts
-- expected: standard only — the naive "R copies cost R·log|X|" strictly exceeds the true log|X|: charging
-- a holographic bound per redundant imprint overcounts the same information R-fold (the category error).
#print axioms QIQTH.RedundancyCompressible.code_subspace_dim
-- expected: standard only — orthonormal redundant-copy states span a subspace of dim |X|, not exp(R).

-- SBSSuppression.lean — redundancy (Quantum Darwinism) restores strong decoherence in the limit (2026-06-15).
#print axioms QIQTH.SBSSuppression.offdiagonal_norm_le
-- expected: standard only — the exponential bound ‖∏ z k‖ ≤ rᴺ on the joint off-diagonal of N fragments.
#print axioms QIQTH.SBSSuppression.offdiagonal_tendsto_zero
-- expected: standard only — per-fragment overlap ≤ r < 1 ⇒ joint off-diagonal → 0 as redundancy N → ∞:
-- redundant broadcast drives FULL (strong) decoherence even when no single fragment fully resolves.

-- RealmSelection.lean — does Q_max select a unique realm? No alone; yes with einselection (2026-06-15).
#print axioms QIQTH.RealmSelection.capacity_underdetermines_realm
-- expected: standard only — the NO-GO: two distinct orthogonal 2-record realms in ℂ² (standard vs Hadamard),
-- both capacity-maximal ⇒ a capacity (cardinality) bound does NOT pick a unique realm.
#print axioms QIQTH.RealmSelection.realm_unique_of_einselection
-- expected: standard only — conditional: given the einselected pointer family, the realm is determined
-- (unique); Q_max then makes it finite + single-macroscopic (CapacityModel).

-- EinsteinEquationOfState.lean — the linear-algebraic crux of Jacobson's equation-of-state
-- derivation of GR (2026-06-18). NOT a derivation of the Einstein equation: the differential
-- geometry (Raychaudhuri focusing, local Rindler horizons, Unruh temperature, local-equilibrium
-- θ=σ=0) and the conservation+Bianchi step are CITED, not checked. Only the algebra is here.
#print axioms QIQTH.EinsteinEOS.symmTensor_eq_smul_metric_of_null
-- expected: standard only — a symmetric tensor vanishing on the entire null cone of Minkowski
-- is a scalar multiple of the metric (the step turning per-null-direction Clausius into a tensor eq).
#print axioms QIQTH.EinsteinEOS.QF_eq_BL
#print axioms QIQTH.EinsteinEOS.symmTensor_eq_smul_metric_of_null_general
-- expected: standard only — PHASE 3. The null-cone crux for a GENERAL Lorentzian metric (not just
-- Minkowski), via congruence reduction g=Pᵀ·η·P (Sylvester's law as a labeled hypothesis) to the
-- Minkowski lemma. This is the linear algebra that lets the per-null Clausius relation be stated in
-- each point's own local inertial frame and still yield a tensor field equation.
#print axioms QIQTH.EinsteinEOS.einstein_tensor_eq_of_state
-- expected: standard only — given a·T(k,k)=E(k,k) for all null k (Raychaudhuri supplies this, as
-- HYPOTHESIS), the tensors obey a·T = E + f·g; conservation+Bianchi fixing f=-½R+Λ is cited.

-- EntanglementFirstLaw.lean — Route B: the entanglement first law δS=δ⟨K⟩ from relative-entropy
-- stationarity, and the Ryu–Takayanagi bridge δ(A/4G)=δ⟨K⟩ (2026-06-18). The first-law INPUTS are
-- QIQT-H's own machine-checked relEntropy facts (nonneg=Klein; =cross−vN; self=0); RT, the ball
-- modular Hamiltonian, and the gravitational all-balls⇒linearized-Einstein step are CITED.
#print axioms QIQTH.EntanglementFirstLaw.firstLaw_of_stationary
-- expected: standard only — δS=δ⟨K⟩: relative entropy ≥0 and =0 at the reference ⇒ stationary ⇒
-- (via D=⟨K⟩−S) the first variations of entropy and modular energy agree.
#print axioms QIQTH.EntanglementFirstLaw.rt_bridge
-- expected: standard only — first law + (cited) RT S=A/4G ⇒ δ(A/4G)=δ⟨K⟩.
#print axioms QIQTH.EntanglementFirstLaw.rt_all_balls_energy
-- expected: standard only — + (cited) ball modular Hamiltonian ⇒ δ(A/4G)=W (weighted boundary energy).
#print axioms QIQTH.EntanglementFirstLaw.gibbs_first_law
-- expected: standard only — the INTEGRATED first law S(ρ)≤⟨K⟩ (Gibbs/Klein), no differentiability:
-- relEntropy≥0 (Klein) + relEntropy=crossEntropy−S. The finite shadow of δS=δ⟨K⟩.
#print axioms QIQTH.EntanglementFirstLaw.spectralEntropy_differentiableAt
-- expected: standard only — the MATRIX-LOG derivative at the spectral level: S=∑negMulLog(λᵢ) is
-- differentiable in its eigenvalues (negMulLog differentiable away from 0). Discharges hS once the
-- eigenvalues are smooth (trivial for fixed-basis families; eigenvalue perturbation is the deeper gap).
#print axioms QIQTH.EntanglementFirstLaw.spectralEntropy_deriv
-- expected: standard only — explicit δS = ∑ᵢ(−log pᵢ−1)·pᵢ'(0), the entropy first variation.
#print axioms QIQTH.EntanglementFirstLaw.vonNeumannEntropy_differentiableAt
-- expected: standard only — lifts the spectral lemma onto the ACTUAL von Neumann entropy:
-- S(ρ(ε)) = ∑negMulLog((h ε).eigenvalues i) by def, differentiable given eigenvalue-differentiability.
-- Reduces hS to exactly the eigenvalue-perturbation hypothesis (the cited Mathlib gap).

-- SpectralSum.lean — eigenvalue-perturbation infrastructure, DIAGONAL fixed-basis case (2026-06-18).
-- Closes hev/hS for diagonal families: the eigenvalue ORDERING is eliminated through the charpoly.
#print axioms QIQTH.SpectralSum.sum_eq_of_prod_X_sub_C_eq
-- expected: standard only — ∏(X−aᵢ)=∏(X−bᵢ) ⇒ ∑f(aᵢ)=∑f(bᵢ): symmetric sums are charpoly-determined
-- (roots multiset). The core that relates IsHermitian.eigenvalues to an external diagonal.
#print axioms QIQTH.SpectralSum.vonNeumannEntropy_diagonal
-- expected: standard only — S(diagonal d) = ∑ negMulLog(dᵢ) via charpoly_diagonal vs IsHermitian.charpoly_eq.
#print axioms QIQTH.EntanglementFirstLaw.vonNeumannEntropy_diagonal_differentiableAt
-- expected: standard only — hS DISCHARGED (a theorem, no hev) for a diagonal fixed-basis family:
-- S(ρ(ε))=∑negMulLog(pᵢ(ε)) differentiable. Closes the fixed-basis (U=I) eigenvalue-perturbation wall.
#print axioms QIQTH.SpectralSum.vonNeumannEntropy_unitaryConj
-- expected: standard only — S(U diag(p) U†)=∑negMulLog(pᵢ) for any unitary U: eigenvalues = permutation
-- of p via charpoly conjugation-invariance (charpoly_mul_comm). The GENERAL fixed-basis case.
#print axioms QIQTH.EntanglementFirstLaw.vonNeumannEntropy_unitaryConj_differentiableAt
-- expected: standard only — hS DISCHARGED (theorem, no hev) for ANY fixed-eigenbasis family
-- ρ(ε)=U diag(p ε) U†. Closes the ENTIRE fixed-basis eigenvalue-perturbation wall (residual: basis-rotating).

-- Curvature.lean — the connection/curvature tower, component-level in a coordinate patch (2026-06-18).
-- Layer 0: Christoffel / Riemann / Ricci / scalar / Einstein tensor + covariant derivative, with the
-- structural identities that need no analytic input. (Bianchi/conservation = later, need differentiability.)
#print axioms QIQTH.Curvature.christoffel_symm
-- expected: standard only — Γ^μ_{νρ}=Γ^μ_{ρν} (torsion-free), from the definition + metric symmetry.
#print axioms QIQTH.Curvature.christoffel_contracted
-- expected: standard only — CONTRACTED CHRISTOFFEL Γ^b_{ab}=½ g^{bα}∂_a g_{bα}: the two extra ∂g terms
-- cancel under b↔α relabelling (metric + inverse-metric symmetry, via Finset.sum_comm). This contracted
-- connection (=∂_a log√|g|) is the object whose closedness ∂_c(Γ^b_{ab})=∂_a(Γ^b_{cb}) underlies Ricci symmetry.
#print axioms QIQTH.Curvature.riemann_antisymm
-- expected: standard only — R^ρ_{σμν}=−R^ρ_{σνμ} (antisymmetry in the last two indices).
#print axioms QIQTH.Curvature.covDeriv02_symm
-- expected: standard only — ∇ preserves the lower-index symmetry of a (0,2) tensor.
-- Layer 1 (analytic): the partial-derivative algebra (linearity + Leibniz), the foundation for the
-- metric-compatibility and Bianchi identities.
#print axioms QIQTH.Curvature.pd_add
#print axioms QIQTH.Curvature.pd_sub
#print axioms QIQTH.Curvature.pd_const_mul
#print axioms QIQTH.Curvature.pd_mul
-- expected: standard only — ∂ᵢ(f+g)=∂ᵢf+∂ᵢg, ∂ᵢ(f−g), ∂ᵢ(c·f)=c·∂ᵢf, Leibniz ∂ᵢ(fg)=(∂ᵢf)g+f(∂ᵢg).
-- Layer 1: metric compatibility ∇g=0 (the defining Levi-Civita property).
#print axioms QIQTH.Curvature.inv_contract
-- expected: standard only — ∑σ g_{σν}(∑α g^{σα} w_α)=w_ν (inverse-metric collapse; double sum + δ).
#print axioms QIQTH.Curvature.christoffel_lower
-- expected: standard only — Γ_{νλμ}=½(∂_λg_{νμ}+∂_μg_{νλ}−∂_νg_{λμ}) (lowered Christoffel, via inv_contract).
#print axioms QIQTH.Curvature.metric_compat
-- expected: standard only — ∇_λ g_{μν}=0: the Levi-Civita defining property, a THEOREM from the
-- Christoffel definition + metric symmetry. (Closes a Layer-1 target feeding Jacobson's Bianchi step.)
#print axioms QIQTH.Curvature.riemann_first_bianchi
-- expected: standard only — first Bianchi R^ρ_{σμν}+R^ρ_{μνσ}+R^ρ_{νσμ}=0 (algebraic, christoffel_symm only).
-- The Schwarz keystone for the second Bianchi (mixed partials commute), via the pd↔fderiv bridge.
#print axioms QIQTH.Curvature.pd_eq_fderiv
-- expected: standard only — ∂ᵢg(x)=Dg(x)[eᵢ] (coordinate partial = directional fderiv, chain rule).
#print axioms QIQTH.Curvature.pd_comm
-- expected: standard only — Schwarz ∂ᵢ∂ⱼf=∂ⱼ∂ᵢf for smooth f (via IsSymmSndFDerivAt + pd_eq_fderiv).
#print axioms QIQTH.Curvature.second_bianchi_deriv_part
-- expected: standard only — the DERIVATIVE part of the second Bianchi cyclic sum vanishes: the six ∂∂Γ
-- terms cancel in pairs via Schwarz (pd_comm). (The full second Bianchi additionally needs the ΓΓ/Γ·R
-- cancellation — the long general-coordinate remainder; see note 51.)
-- Scaffolding for the FULL second Bianchi: ∂ commutes with sums, PdiffAt of smooth fields + products.
#print axioms QIQTH.Curvature.pd_sum
#print axioms QIQTH.Curvature.PdiffAt_of_contDiff
#print axioms QIQTH.Curvature.PdiffAt.mul
#print axioms QIQTH.Curvature.PdiffAt_pd
#print axioms QIQTH.Curvature.pd_riemann
-- expected: standard only — ∂_λR^ρ_{σμν} expanded (∂∂Γ terms + ∑_l Leibniz ∂Γ·Γ terms); the workhorse
-- for the full second Bianchi, with differentiability discharged by the PdiffAt_* helpers.

#print axioms QIQTH.Curvature.bianchi_extra_terms
-- expected: standard only — the (1,3) → matrix-form reduction (lower-index Γ·R terms cancel cyclically).
#print axioms QIQTH.Curvature.bianchi_GGG
-- expected: standard only — the cubic ΓΓΓ part = Jacobi identity ∑_cyclic[Γ_λ,[Γ_μ,Γ_ν]]=0 (κ↔e swap).
#print axioms QIQTH.Curvature.pd_riemannQuad
#print axioms QIQTH.Curvature.bianchi_dGamma
-- expected: standard only — the ∂Γ·Γ part cancels as identical sums up to renaming the contracted index.
#print axioms QIQTH.Curvature.second_bianchi
-- expected: standard only — the FULL second Bianchi identity ∇_λR^ρ_{σμν}+∇_μR^ρ_{σνλ}+∇_νR^ρ_{σλμ}=0,
-- assembled from the four cyclic-cancellation lemmas (∂∂Γ Schwarz + ∂Γ·Γ + ΓΓΓ Jacobi + extra terms).
-- The conservation identity behind ∇^μG_{μν}=0 (Jacobson's contracted-Bianchi step). Axiom-free.

#print axioms QIQTH.Curvature.PdiffAt_riemann
#print axioms QIQTH.Curvature.covDerivRiem_contract
-- expected: standard only — ∇ commutes with contraction: ∑_ρ ∇_λR^ρ_{σρν} = ∇_λ Ric_{σν} (the contracted
-- index pair's connection corrections cancel via sum_comm). The bridge from second Bianchi to ∇^μG_{μν}=0.

#print axioms QIQTH.Curvature.covDerivRiem_antisymm
-- expected: standard only — ∇R inherits Riemann's last-two-index antisymmetry (per-term via riemann_antisymm).
#print axioms QIQTH.Curvature.covDerivRiem_contract'
#print axioms QIQTH.Curvature.second_bianchi_contracted
-- expected: standard only — the ONCE-CONTRACTED Bianchi ∇_λR_{σν} − ∇_νR_{σλ} + ∇_ρR^ρ_{σνλ} = 0 (trace of
-- the second Bianchi over (ρ,μ)). One contraction with g^{μν} away from ∇^μG_{μν}=0. Axiom-free.

#print axioms QIQTH.Curvature.pd_const
#print axioms QIQTH.Curvature.inv_metric_compat
-- expected: standard only — ∇_λ g^{μρ}=0 (raised-index metric compatibility): differentiate the inverse
-- relation, substitute metric_compat, cancel connection terms, invert. Metric-raising tower, piece A.

#print axioms QIQTH.Curvature.lowered_riemann_eq
-- expected: standard only — g_{ρα}R^α_{σμν} = ∂Γ_lower − ΓΓ_lower (Riemann in terms of the metric).
#print axioms QIQTH.Curvature.lowered_riemann_antisymm
-- expected: standard only — first-pair antisymmetry R_{ρσμν}=−R_{σρμν} (∂∂g cancels by Schwarz, ΓΓ by the
-- symmetric pairing). Metric-raising tower piece B — the CRUX, needed for g^{σν}R^ρ_{σνλ} in ∇^μG_{μν}=0.

#print axioms QIQTH.Curvature.lowered_riemann_gi_trace
-- expected: standard only — ∑g^{σν}(g_{βρ}R^ρ_{σνλ}) = −Ric_{βλ} (metric trace of lowered Riemann → Ricci,
-- via piece B + the gi·g=δ collapse). Metric-raising tower piece C (core).

-- Twice-contracted Bianchi (Phase 1 of the "real derivation": discharges einstein_field_equation's `bianchi`).
#print axioms QIQTH.Curvature.ricci_gi_raise
#print axioms QIQTH.Curvature.gi_trace_covDeriv_ricci
#print axioms QIQTH.Curvature.gi_trace_covDerivRiem
#print axioms QIQTH.Curvature.gi_trace_covDerivRiem_ricci
#print axioms QIQTH.Curvature.divRiemann_trace_eq
#print axioms QIQTH.Curvature.twice_contracted_bianchi
-- expected: standard only — ∇^μ Ric_{μλ} = ½ ∂_λ R (the contracted Bianchi ∇^μG_{μλ}=0 in trace form),
-- by contracting second_bianchi_contracted with g^{σν}: ∂R (T1) − div02 (T2) − div02 (T3) = 0. Axiom-free.
#print axioms QIQTH.Curvature.einsteinTensor_divergence_zero
-- expected: standard only — ★ ∇^μ G_{μν} = 0: THE EINSTEIN TENSOR IS DIVERGENCE-FREE (the physically-famous
-- form of contracted Bianchi; the geometric ORIGIN of local energy-momentum conservation — why ∇^μ(a·T)=0 is
-- consistent with a·T=G+Λg). Writing G=Ric+(−½R)·g: div02(G)=twice_contracted_bianchi(½∂R)+div02_scalar_metric
-- (pd(−½R)=−½∂R)=0. Standalone named theorem (was only implicit inside einstein_field_equation). Axiom-free.
#print axioms QIQTH.Curvature.metric_contraction_trace
#print axioms QIQTH.Curvature.einstein_trace_eq
-- expected: standard only — metric_contraction_trace: g^{μν}g_{μν}=n (∑_μ δ^μ_μ, via hinv+gi symmetry).
-- ★ einstein_trace_eq: g^{μν}G_{μν}=(1−n/2)·R — THE TRACE OF THE EINSTEIN TENSOR (trace-reversed relation;
-- trace of a·T=G+Λg reads a·g^{μν}T_{μν}=(1−n/2)R+nΛ; in n=4 it is −R). From G=Ric−½R·g + g^{μν}g_{μν}=n
-- + the def R=g^{σν}R_{σν}. Axiom-free.

#print axioms QIQTH.Curvature.div02_scalar_metric
#print axioms QIQTH.Curvature.div02_add
#print axioms QIQTH.Curvature.einstein_field_equation
#print axioms QIQTH.Curvature.einstein_field_equation_real
-- expected: standard only — THE EINSTEIN FIELD EQUATION with the ACTUAL Einstein tensor (Ric=ricci,
-- R=scalarCurv), `bianchi` discharged by twice_contracted_bianchi. Only hypotheses = cited physics
-- (post-crux Clausius relation + conservation). Phase 2 of the real derivation. Axiom-free.
#print axioms QIQTH.Curvature.const_of_pd_zero
#print axioms QIQTH.Curvature.einstein_field_equation_real_global
-- expected: standard only — the field equation with a GENUINE cosmological constant Λ (true constant,
-- not just covariantly constant at a point), via const_of_pd_zero on connected Point n. Phase 4. Axiom-free.
#print axioms QIQTH.Curvature.crux_of_pernull
-- expected: standard only — PHASE 3 WIRING. DERIVES the tensor `crux` (a·T=R+f·g) from the genuinely
-- primitive per-null Clausius relation (a·T−R vanishes on the whole null cone of g x, in each point's
-- local inertial frame), via symmTensor_eq_smul_metric_of_null_general + pointwise congruence to
-- Minkowski. Closes the chain from Jacobson's heat premise to the field equation; f's smoothness is the
-- one honest analytic residual. Axiom-free.
-- expected: standard only — THE EINSTEIN FIELD EQUATION as equation of state: from the post-crux Clausius
-- relation a·T=R+f·g + conservation ∇^μ(aT)=0 + contracted Bianchi ∇^μR=½∂R + metric compat, derive
-- a·T_{μν}=G_{μν}+Λg_{μν} with Λ=f+½R covariantly constant (cosmological constant = integration constant).
-- Completes Jacobson's f-fixing step deferred by EinsteinEquationOfState.lean. Cited physics = labeled hyps.

-- ABSTRACT-MANIFOLD GR STACK (gap 3: lift off the single coordinate patch onto genuine manifolds).
#print axioms QIQTH.ManifoldGR.curvature_antisymm
#print axioms QIQTH.ManifoldGR.curvature_self
-- expected: standard only — the Riemann curvature endomorphism R(X,Y)σ = ∇_X∇_Yσ − ∇_Y∇_Xσ − ∇_[X,Y]σ
-- of an ARBITRARY covariant derivative on an ARBITRARY vector bundle over a manifold (Mathlib has the
-- 2025 CovariantDerivative + mlieBracket but NO curvature). Antisymmetry R(X,Y)=−R(Y,X) + R(X,X)=0.
-- First increment of the abstract-manifold stack. Axiom-free.
#print axioms QIQTH.ManifoldGR.curvature_smul_left
#print axioms QIQTH.ManifoldGR.curvature_smul_right
-- expected: standard only — TENSORIALITY: R(fX,Y)σ = f·R(X,Y)σ and R(X,fY)σ = f·R(X,Y)σ. The property
-- that makes the curvature a genuine TENSOR in the vector-field slots: the Leibniz term from ∇_{fX}=f∇_X
-- cancels exactly against the −(Yf)X term in the Lie-bracket product rule [fX,Y]=f[X,Y]−(Yf)X (both are
-- the same directional derivative d% f x (Y x)). Axiom-free.
#print axioms QIQTH.ManifoldGR.curvature_add_left
#print axioms QIQTH.ManifoldGR.curvature_add_right
-- expected: standard only — ADDITIVITY R(X+X',Y)σ=R(X,Y)σ+R(X',Y)σ and R(X,Y+Y')σ=R(X,Y)σ+R(X,Y')σ.
-- With tensoriality above, the curvature is bilinear+tensorial in its two vector-field slots. Axiom-free.
#print axioms QIQTH.ManifoldGR.curvature_add_section
-- expected: standard only — additivity in the SECTION slot R(X,Y)(σ+σ')=R(X,Y)σ+R(X,Y)σ' (funext+cov.add,
-- no germ-localisation). Curvature now additive in all three slots. Axiom-free.
#print axioms QIQTH.ManifoldGR.curvature_smul_section
-- expected: standard only — SECTION-SLOT TENSORIALITY R(X,Y)(fσ)=f·R(X,Y)σ, the deepest tensoriality
-- (makes R a genuine pointwise (1,3)-tensor in the section). Leibniz on the two ∇∇ terms leaves
-- (X(Yf)−Y(Xf))·σ and the bracket term gives −([X,Y]f)·σ; they cancel EXACTLY by the general-manifold
-- commutator mfderiv_apply_mlieBracket ([X,Y]f = X(Yf)−Y(Xf)). The concrete payoff of that commutator —
-- abstract-manifold Riemann curvature is now fully tensorial in all three slots. Axiom-free.
#print axioms QIQTH.ManifoldGR.first_bianchi
-- expected: standard only — FIRST (algebraic) BIANCHI on the tangent bundle: for a torsion-free
-- connection, R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0. Classical proof: torsion-freeness (∇_A B = ∇_B A + [A,B])
-- regroups the six ∇∇ terms by direction into ∇_X[Y,Z]+cyclic with opposite-order terms cancelling;
-- a second use turns ∇_X[Y,Z]−∇_{[Y,Z]}X into [X,[Y,Z]], cyclic sum = 0 by JACOBI. Mathlib has the
-- model-space Jacobi (leibniz_identity_lieBracket) but no mlieBracket version, so the manifold Jacobi is
-- a labeled hypothesis (its chart-transport is the remaining input). Companion def: `torsion`. Axiom-free.
#print axioms QIQTH.ManifoldGR.curvature_tensorialAt_left
#print axioms QIQTH.ManifoldGR.ricci
-- expected: standard only — THE RICCI TENSOR on an abstract manifold. curvature_tensorialAt_left:
-- X ↦ R(X,Y)σ is tensorial (curvature_smul_left + curvature_add_left → Mathlib TensorialAt). curvatureEndo:
-- the endomorphism v ↦ R(v,Y)Z : T_xM →L T_xM via mkHom. ricci: Ric(Y,Z) = LinearMap.trace of that
-- endomorphism = tr(v ↦ R(v,Y)Z). Needs [FiniteDimensional 𝕜 E][CompleteSpace 𝕜/E][IsManifold I 2 M];
-- hcovσ = connection-smoothness (∇_X Z smooth for smooth X). Feeds scalar curvature → Einstein. Axiom-free.
#print axioms QIQTH.ManifoldGR.mfderiv_apply_mlieBracket_model
-- expected: standard only — COMMUTATOR INFRASTRUCTURE (base case). The Lie bracket acts on a scalar as
-- the commutator of directional derivatives df([X,Y])=X(Yf)−Y(Xf), for the model-space manifold (M=E):
-- mfderiv→fderiv, mlieBracket→lieBracket, reduces to Mathlib's normed-space fderiv_apply_lieBracket. The
-- unblocker for section-tensoriality + Bianchi + Ricci; general-manifold case (charts) builds on it. Axiom-free.
#print axioms QIQTH.ManifoldGR.dirDeriv_add_vectorField
#print axioms QIQTH.ManifoldGR.dirDeriv_smul_vectorField
#print axioms QIQTH.ManifoldGR.dirDeriv_add_fun
-- expected: standard only — dirDeriv linearity (additive + 𝕜-homogeneous in the vector field, additive
-- in the function), the directional-derivative API the Bianchi cyclic sum / Ricci traces consume. Axiom-free.
#print axioms QIQTH.Curvature.pd_covDerivVec
#print axioms QIQTH.Curvature.ricci_identity
#print axioms QIQTH.Curvature.ricci_identity_contracted
-- ricci_identity_contracted: tracing the commutator on the upper index gives the Ricci tensor,
-- ∑_μ(∇_μ∇_ν−∇_ν∇_μ)V^μ = R_σν V^σ — the step that puts R_μν into the focusing. Axiom-free.
#print axioms QIQTH.Curvature.covDeriv2Vec_trace
#print axioms QIQTH.Curvature.raychaudhuri_focusing
-- covDeriv2Vec_trace: covariant derivative commutes with contraction, ∑_μ∇_ν∇_μV^μ = ∂_ν θ (geodesic-
-- direction Γ cancels by torsion-freeness). raychaudhuri_focusing: THE RAYCHAUDHURI FOCUSING EQUATION,
-- V^ν∂_νθ = Σ V^ν∇_μ∇_νV^μ − R_σν V^σV^ν — Jacobson's focusing step with the Ricci term −R_σνV^σV^ν
-- explicit. The GEOMETRY of Jacobson's front half is now machine-checked. Axiom-free.
#print axioms QIQTH.Curvature.geodesic_divergence_leibniz
-- geodesic_divergence_leibniz: for a geodesic field, the product-rule divergence of the acceleration
-- vanishes — the sub-step toward rewriting Σ V^ν∇_μ∇_νV^μ as −(∇_μV^ν)(∇_νV^μ) (the shear part Jacobson
-- neglects at the focusing point). Axiom-free.
#print axioms QIQTH.Curvature.geodesic_leibniz
#print axioms QIQTH.Curvature.raychaudhuri_geodesic
#print axioms QIQTH.Curvature.raychaudhuri_focusing_at_equilibrium
-- geodesic_leibniz: Σ V^ν∇_μ∇_νV^μ = −(∇_μV^ν)(∇_νV^μ) for a geodesic field (hP + geodesic T1=0 +
-- index-permutation T2=T3). raychaudhuri_geodesic: THE FULL RAYCHAUDHURI EQUATION in Jacobson's exact
-- form V^ν∂_νθ = −(∇_μV^ν)(∇_νV^μ) − R_σν V^σV^ν. The ENTIRE GEOMETRY of Jacobson's front half is now
-- machine-checked, axiom-free.
-- raychaudhuri_focusing_at_equilibrium: ★ at local equilibrium (θ=σ=ω=0 ⇒ shear-expansion quadratic
-- (∇V)(∇V)=0, Jacobson's stationary-horizon condition), Raychaudhuri collapses to PURE Ricci focusing
-- V^ν∂_νθ = −R_σν V^σV^ν (dθ/dλ=−R_kk). = the area-rate↔R_kk geometric content of hFocus (input #3 of
-- qiqt_gr_from_wedge_kms), DERIVED from raychaudhuri_geodesic; no Einstein presupposed. Only the abstract
-- area-rate↔expansion-θ identification remains modelling. Axiom-free.
-- expected: standard only — RAYCHAUDHURI FOCUSING (geometry of Jacobson's front half). pd_covDerivVec:
-- the product-rule expansion of ∂_μ(∇_ν V^ρ). ricci_identity: THE COMMUTATOR OF COVARIANT DERIVATIVES
-- IS THE RIEMANN TENSOR, (∇_μ∇_ν−∇_ν∇_μ)V^ρ=R^ρ_σμν V^σ — Bianchi-scale index computation (Schwarz
-- cancels ∂∂V; torsion-freeness cancels the geodesic Γ; ΓΓ reassembles into riemann via sum_comm). Its
-- ρ=μ contraction gives the −R_μν k^μ k^ν focusing term that enters Jacobson's δA. Axiom-free.
#print axioms QIQTH.ManifoldGR.dirDeriv_eq_chartAt
#print axioms QIQTH.ManifoldGR.dirDeriv_eq_chart
#print axioms QIQTH.ManifoldGR.dirDeriv_eventuallyEq_chart
-- dirDeriv_eq_chartAt: the FIXED-chart covariance (eval at nearby z ∈ source) — enables the SECOND
-- directional derivative; dirDeriv_eq_chart is the z=x₀ corollary. dirDeriv_eventuallyEq_chart: the
-- neighborhood form (Yf agrees as a FUNCTION near x with its chart rep) — the setup to differentiate it.
-- expected: standard only — GENERAL-MANIFOLD COMMUTATOR, foundational block. Directional-derivative
-- chart-covariance: (Yf)(x) on M = normed-space directional deriv of the chart rep f∘e⁻¹ along the
-- pushed-forward vector, via the chain rule for f=(f∘e⁻¹)∘e. The transport that lifts the model-space
-- commutator to general (boundaryless) manifolds. Axiom-free. (The 'wall' was Mathlib plumbing, not math.)
#print axioms QIQTH.ManifoldGR.PseudoRiemannianMetric.lower_injective
#print axioms QIQTH.ManifoldGR.PseudoRiemannianMetric.lower_symm
-- expected: standard only — P3 (Lorentzian metric, which Mathlib lacks — its metric infra is
-- positive-definite only). The pseudo-Riemannian metric structure (symmetric, nondegenerate bilinear
-- form field) + the index-lowering musical ♭ map, injective from nondegeneracy (first half of the
-- musical isomorphism). Foundation for Levi-Civita → Ricci → Einstein. Axiom-free.
#print axioms QIQTH.ManifoldGR.PseudoRiemannianMetric.raise_lower
#print axioms QIQTH.ManifoldGR.PseudoRiemannianMetric.lowerEquiv
-- expected: standard only — THE FULL MUSICAL ISOMORPHISM ♭ : TM ≅ T*M (with inverse ♯, index raising).
-- The metric carries ♯ (raise') + the right-inverse law (lower_raise') as data — standard for a
-- nondegenerate metric (a bundle iso T≅T*), avoiding a finite-dimensionality commitment; the left
-- inverse (raise_lower) follows from ♭-injectivity (nondeg'). lowerEquiv bundles it as a ≃L. This is
-- the index-raising iso the Levi-Civita Koszul formula needs to solve g(∇_X Y,·)=ω for ∇_X Y. Axiom-free.
#print axioms QIQTH.ManifoldGR.koszul_metric_compat
#print axioms QIQTH.ManifoldGR.koszul_torsion_free
-- expected: standard only — THE KOSZUL FORMULA + the two DEFINING Levi-Civita properties.
-- koszul = the RHS of 2g(∇_X Y,Z) = X·g(Y,Z)+Y·g(X,Z)−Z·g(X,Y)+g([X,Y],Z)−g([Y,Z],X)+g([Z,X],Y).
-- koszul_metric_compat: koszul X Y Z + koszul X Z Y = 2·X·g(Y,Z)  (≡ ∇g=0, metric compatibility).
-- koszul_torsion_free:  koszul X Y Z − koszul Y X Z = 2·g([X,Y],Z) (≡ ∇_X Y−∇_Y X=[X,Y], torsion-free).
-- Both are PURE ALGEBRA from metric symmetry + Lie-bracket antisymmetry — NO differentiability; the
-- dirDeriv terms cancel/merge and the bracket terms cancel via mlieBracket_swap (linear_combination, since
-- 𝕜 has no order so linarith is unavailable). The algebraic heart of Levi-Civita existence+uniqueness; the
-- remaining step is dualising koszul to ∇_X Y via the musical ♯ (lowerEquiv) + the connection axioms. Axiom-free.
#print axioms QIQTH.ManifoldGR.koszul_add_right_Z
-- expected: standard only — ADDITIVITY of koszul in the Z slot (koszul X Y (Z+Z') = koszul X Y Z +
-- koszul X Y Z'), half of the C∞-linearity that lets the Koszul RHS descend to a covector Z↦koszul X Y Z
-- (hence define ∇_X Y via ♯). dirDeriv terms split (additive in function via dirDeriv_add_fun, in field via
-- dirDeriv_add_vectorField); bracket terms via mlieBracket_add_left/right ([CompleteSpace E]); metric
-- bilinear. Needs [IsManifold I 2 M] + differentiability of the metric-paired functions/fields. Axiom-free.
#print axioms QIQTH.ManifoldGR.dirDeriv_mul
#print axioms QIQTH.ManifoldGR.koszul_smul_right_Z
-- expected: standard only — HOMOGENEITY of koszul in Z (koszul X Y (f•Z) = f·koszul X Y Z); with
-- additivity this is the FULL C∞-LINEARITY making koszul a covector in Z — hence ∇_X Y := ♯(½·koszul).
-- The Leibniz cross-terms (X·f)·g(Y,Z), (Y·f)·g(X,Z) (from dirDeriv_mul, product rule via HasMFDerivAt.mul)
-- cancel EXACTLY against −(X·f)·g(Z,Y), −(Y·f)·g(Z,X) (from mlieBracket_smul_left/right) by METRIC SYMMETRY
-- — the cancellation that makes Levi-Civita well-defined. Helpers: dirDeriv_mul (CLM-apply closed by defeq
-- rfl past the TangentSpace 𝓘(𝕜) codomain synonym), dirDeriv_smul_field. linear_combination (𝕜 unordered).
#print axioms QIQTH.ManifoldGR.dirDeriv_add_fun_at
#print axioms QIQTH.ManifoldGR.koszul_tensorialAt
-- expected: standard only — KOSZUL IS TENSORIAL IN Z. Packages the at-x additivity + homogeneity into
-- Mathlib's `TensorialAt` criterion (σ ↦ koszul X Y σ x is tensorial at x). By `TensorialAt.mkHom` this
-- defines the Koszul COVECTOR T_xM →L 𝕜, whose ♯-dual (lowerEquiv⁻¹) is the Levi-Civita ∇_X Y — Mathlib's
-- mkHom supplies the hard locality/bump-function step. The linearity lemmas were refactored to at-x hyps
-- (dirDeriv_add_fun_at = pointwise additivity via mfderiv_add) so TensorialAt's at-x fields are satisfied;
-- hsmooth = metric smoothness (a labeled hypothesis until a smooth-metric field is added). Axiom-free.
#print axioms QIQTH.ManifoldGR.koszulForm_apply
#print axioms QIQTH.ManifoldGR.leviCivita_koszul
-- expected: standard only — THE LEVI-CIVITA CONNECTION VECTOR exists on an abstract manifold and
-- satisfies the Koszul formula. koszulForm = the Koszul 1-form (covector T_xM→L𝕜) via TensorialAt.mkHom;
-- leviCivita ∇_X Y := ♯(½·koszulForm) (musical raise of half the Koszul form); leviCivita_koszul:
-- g(∇_X Y, Z) = ½·koszul X Y Z (the DEFINING equation realized) — via lower_raise (♭♯=id) + koszulForm_apply
-- (mkHom_apply). With koszul_metric_compat/koszul_torsion_free this certifies ∇ metric-compatible +
-- torsion-free. Needs [FiniteDimensional 𝕜 E][CompleteSpace 𝕜/E][IsManifold I 2 M]; hsmooth labeled. Axiom-free.
#print axioms QIQTH.ManifoldGR.scalarCurvature
#print axioms QIQTH.ManifoldGR.einsteinForm
-- expected: standard only — SCALAR CURVATURE + EINSTEIN TENSOR (bilinear-form level). scalarCurvature
-- R = g^{YZ}Ric(Y,Z) = LinearMap.trace of the Ricci operator ♯∘Ric (metric ♯=gm.raise composed with Ric).
-- einsteinForm G = Ric − ½·R·g, the combination whose covariant divergence vanishes and which equals the
-- stress-energy in Jacobson's eq of state. Takes the Ricci bilinear form as input; the bridge ricci(scalar)
-- → Ricci form (via mkHom₂) and the contracted Bianchi ∇^μG=0 are the remaining pieces. Axiom-free.

#print axioms QIQTH.ClausiusIntegral.integrand_eq_of_weighted_integral_eq
-- expected: standard only — THE INTEGRAND-MATCHING KERNEL of Jacobson's Clausius step (delivering part of
-- the per-null premise, gap "integral matching"). If ∫₀^ε λ·f = ∫₀^ε λ·g for every ε (as δQ=TδS forces
-- for the affine-weighted heat-flux and area-change integrands along every local horizon generator), then
-- f=g. Proof: FTC differentiates both integrals → ε·f(ε)=ε·g(ε), cancel ε≠0, extend to 0 by continuity
-- ({0}ᶜ dense). The bridge "Clausius integrals match" ⟹ "T_{kk} ∝ R_{kk} on the null cone"; the Sylvester
-- null-cone lemma then gives the pointwise tensor equation feeding jacobson_einstein_equation_of_state.
-- The remaining (horizon measure-theory + Unruh correlator) are the larger pieces. Axiom-free.

#print axioms QIQTH.Unruh.sinh_cosh_diff_sq
#print axioms QIQTH.Unruh.rindler_interval
-- expected: standard only — UNRUH EFFECT (geometric kernel; cited physics being formalized, plan 55).
-- The Lorentzian interval along a uniformly accelerated (Rindler) worldline is (Δt)²−(Δx)² =
-- (4/a²)sinh²(aΔτ/2). This sinh² is the entire reason the accelerated two-point function is thermal —
-- its imaginary-time periodicity (NEXT: complex KMS) is the KMS condition at β=2π/a, i.e. T=a/2π. Axiom-free.
#print axioms QIQTH.Unruh.sinh_sq_periodic
#print axioms QIQTH.Unruh.kms_periodicity
-- sinh_sq_periodic: THE KMS PERIODICITY (load-bearing complex analysis) — sinh² has imaginary period iπ,
-- sinh(w−iπ)²=sinh(w)². kms_periodicity: in proper time, 1/sinh²(aΔτ/2) is periodic under Δτ→Δτ−2πi/a.
-- This IS the KMS condition at β=2π/a ⟹ thermal at the Unruh temperature T=a/2π=ℏκ/2π. Axiom-free.

#print axioms QIQTH.Curvature.jacobson_einstein_equation_of_state
-- expected: standard only — THE END-TO-END THEOREM (plan 56). Composes the two halves —
-- crux_of_pernull (per-null Clausius relation ⟹ a·T=R+f·g, via the Sylvester null-cone lemma) and
-- einstein_field_equation_real_global (crux + conservation + contracted Bianchi ⟹ G+Λg=a·T) — into ONE
-- theorem: from Jacobson's per-null Clausius premise to the Einstein field equation with a genuine
-- constant Λ. All geometry discharged internally; cited residual = area law (gap 1), Clausius, the
-- free-field correlator form behind Unruh, and the integral matching bundled into `pernull`. Axiom-free.

#print axioms QIQTH.ClausiusIntegral.area_integral_div_sq_tendsto
#print axioms QIQTH.ClausiusIntegral.area_leadingCoeff_eq_neg_ricci
-- expected: standard only — JACOBSON'S SUBSTITUTION STEP (TeX 275-282, gr-qc/9504004 in refs/). The area
-- change δA(ε)=∫₀^ε θ dλ (Jacobson's δA=∫θ) has ε² leading coefficient ½θ'(0): (∫₀^ε θ)/ε²→θ'(0)/2 by
-- l'Hôpital (θ(ε)/(2ε)=½·slope(θ;0,ε)→½θ'(0)). At a local horizon θ(0)=σ(0)=0, so by the Raychaudhuri
-- rate θ'(0)=−R_kk(0), giving δA leading coeff −½R_kk(0) = the leading coeff of −∫₀^ε λR_kk (via
-- weighted_integral_div_sq_tendsto). That is EXACTLY Jacobson's "integration yields θ=−λR_kk, substituting
-- into δA gives δA=−∫λR_kk." Closes the area-integral half of the Clausius matching. Axiom-free.

#print axioms QIQTH.Curvature.BL_smul_sub
#print axioms QIQTH.Curvature.pernull_of_clausius_integral
#print axioms QIQTH.Curvature.jacobson_einstein_from_clausius_integral
-- expected: standard only — WIRING THE INTEGRAL CLAUSIUS STEP INTO THE END-TO-END THEOREM (plan 56,
-- ClausiusToPernull.lean). pernull_of_clausius_integral DERIVES the `pernull` premise of
-- jacobson_einstein_equation_of_state from Jacobson's RAW integral Clausius relation: given the affine-
-- weighted heat-flux integral ∫₀^ε λ·(a·T_{kk}) dλ = the area-change integral ∫₀^ε λ·R_{kk} dλ along every
-- local Rindler generator (= his eq. dQ = eq. dA, i.e. δQ=TδS with κ cancelled and a=2π/ℏη folded in), the
-- leading-ε² coefficients must match (value_at_zero_of_weighted_integral_proportional, FTC+l'Hôpital),
-- giving a·T_{kk}(0)=R_{kk}(0) per null direction = BL(a·T−Ric)v=0 (via BL_smul_sub). jacobson_einstein_
-- from_clausius_integral plugs this into the end-to-end theorem, so the premise is now LITERALLY Jacobson's
-- eq.(dQ)=eq.(dA) — the integral→point step is no longer an assumed gap. Cited residual now = exactly the
-- area law (gap 1), the Unruh temperature, and δQ=TδS. Axiom-free. Verified against gr-qc/9504004 in refs/.
#print axioms QIQTH.Curvature.clausius_integral_of_area_law
#print axioms QIQTH.Curvature.jacobson_einstein_from_area_law
-- expected: standard only — ★ THE AREA LAW ISOLATED AS A SINGLE POSTULATE. clausius_integral_of_area_law
-- DERIVES the bundled integral-Clausius premise ∫λ(a·T_kk)=∫λR_kk from its constituents presented as
-- SEPARATE labelled hypotheses: boost heat flux δQ=−κ∫λT_kk (hQ), Raychaudhuri δA=−∫λR_kk (hRay), the
-- ★ AREA LAW δS=ηδA (hAreaLaw — the QIQT-H holographic postulate), the ★ Unruh temperature T=ℏκ/2π (htemp),
-- and Clausius δQ=TδS (hClausius); with a=2π/ℏη the κ cancels (constant identity a·temp·η=κ, via field_simp)
-- and integral_const_mul pulls a out ⟹ the relation. jacobson_einstein_from_area_law then composes this with
-- jacobson_einstein_from_clausius_integral: the SINGLE axiom-free chain from the area-law postulate (+ Unruh,
-- Clausius, flux/Raychaudhuri integral forms, Lorentzian structure, conservation, f-regularity) to the genuine
-- Einstein field equation a·T=G+Λg with constant Λ. The area law now appears as ONE isolated, explicit premise.

#print axioms QIQTH.ManifoldGR.mpullbackWithin_extChartAt_symm_apply
#print axioms QIQTH.ManifoldGR.mpullbackWithin_extChartAt_symm_self
-- expected: standard only — abstract-manifold thread (gap 3). Field-side chart identification: the
-- chart pullback of a vector field X (the model representative used inside Mathlib's mlieBracket
-- I X Y x) evaluated at chart point e z equals the pushforward (de)_z (X z). _apply is the
-- NEIGHBORHOOD version (any z ∈ e.source, via (de⁻¹)⁻¹ = de from the chart-derivative composition
-- identities) — what the SECOND directional derivative in the commutator assembly needs; _self is the
-- base-point corollary (de_x = id ⟹ = X x). Field analogues of dirDeriv_eq_chart. Axiom-free.

#print axioms QIQTH.ManifoldGR.tangent_eq_zero_of_forall_mfderiv
-- expected: standard only — NON-DEGENERACY of the tangent–cotangent pairing: if df_x(v)=0 for every
-- scalar f, then v=0. Tested against f = ℓ∘extChartAt for ℓ in the dual; since de_x=id, df_x(v)=ℓ(v),
-- so all duals vanish on v ⟹ v=0 by Hahn–Banach (SeparatingDual 𝕜 E, e.g. 𝕜=ℝ). This upgrades
-- "holds against every function" identities to genuine vector-field identities — the device that turns
-- the functional Jacobi (a corollary of the commutator) into the vector Jacobi `first_bianchi` needs.
#print axioms QIQTH.ManifoldGR.dirDeriv_model_apply
#print axioms QIQTH.ManifoldGR.dirDeriv_dirDeriv_eq_chart
#print axioms QIQTH.ManifoldGR.mfderiv_apply_mlieBracket
-- expected: standard only — THE GENERAL-MANIFOLD COMMUTATOR (abstract-manifold thread, gap 3).
-- mfderiv_apply_mlieBracket: on any boundaryless C² manifold the Lie bracket acts on a scalar as the
-- commutator of directional derivatives, df([X,Y]) = X(Yf) − Y(Xf). This is the chart-free statement
-- whose Point-n component shadow is `ricci_identity`. Composes (a) bracket-side chart factorization
-- (dirDeriv_eq_chart at base, de_x=id), (b) function-side second-derivative transport
-- (dirDeriv_dirDeriv_eq_chart, the crux — manifold X(Yf) = model X̃(Ỹg) via dirDeriv_eventuallyEq_chart
-- + the neighborhood field identification), (c) the normed-space commutator mfderiv_apply_mlieBracket_model.
-- dirDeriv_model_apply: in the model, dirDeriv = fderiv-apply. All axiom-free.

-- NON-COMMUTATIVE MATRIX FUNCTION CALCULUS (QIQTH/MatrixFunctionCalculus.lean): the matrix
-- power/trace derivative that Mathlib lacks (its `hasFDerivAt_exp`/`log` are commutative-algebra only).
#print axioms QIQTH.MatrixCalculus.hasDerivAt_matrixPow
-- expected: standard only — THE MATRIX POWER RULE: d/dt (A+t·H)^m|₀ = Σ_{k<m} A^k·H·A^{m-1-k}, the
-- non-commutative Leibniz expansion along an affine path. By induction on m via HasDerivAt.mul (the
-- product rule), with the succ-case sum reindexed by Finset.sum_range_succ'. Axiom-free.
#print axioms QIQTH.MatrixCalculus.trace_leibniz_sum
-- expected: standard only — TRACE COLLAPSE: Tr(Σ_{k<m} A^k H A^{m-1-k}) = m·Tr(A^{m-1} H); by trace
-- cyclicity every term equals Tr(A^{m-1}H). The non-commutative sum becomes a scalar multiple.
#print axioms QIQTH.MatrixCalculus.hasDerivAt_trace_matrixPow
-- expected: standard only — ★ THE TRACE POWER RULE: d/dt Tr((A+t·H)^m)|₀ = m·Tr(A^{m-1} H), the
-- polynomial case of the trace-derivative d/dt Tr g(A+tH)|₀ = Tr(g'(A)H) underlying the first-order
-- entanglement first law δS=δ⟨K⟩. Composes hasDerivAt_matrixPow with the continuous-linear trace
-- (restrictScalars ℝ, via HasFDerivAt.comp_hasDerivAt_of_eq) and collapses via trace_leibniz_sum.
#print axioms QIQTH.MatrixCalculus.hasDerivAt_trace_sumPow
-- expected: standard only — THE TRACE POLYNOMIAL RULE (linearity lift): for any finite ℂ-combination
-- of powers p(M)=Σ_{m<N} c_m M^m (= any polynomial), d/dt Tr(p(A+t·H))|₀ = Σ_{m<N} c_m·m·Tr(A^{m-1}H)
-- = Tr(p'(A)H). From HasDerivAt.sum + const_smul over the trace power rule. Axiom-free.
#print axioms QIQTH.MatrixCalculus.hasDerivAt_trace_matrixPow_at
-- expected: standard only — THE TRACE POWER RULE AT A GENERAL BASE POINT: d/dt Tr((A+t·H)^m)|_{t=t₀}
-- = m·Tr((A+t₀·H)^{m-1} H) — holds everywhere, not just at 0, via the affine shift t↦t−t₀
-- (HasDerivAt.scomp_of_eq) reducing to the base-0 rule with A↦A+t₀·H. The form the entire-function
-- (power-series exp) case consumes via hasDerivAt_tsum. Axiom-free.
#print axioms QIQTH.MatrixCalculus.norm_entry_le_frobenius
#print axioms QIQTH.MatrixCalculus.norm_trace_le_card
-- expected: standard only — Frobenius bounds (the summability input for the entire-function trace-derivative).
-- norm_entry_le_frobenius: ‖M i j‖≤‖M‖ (entry ≤ Frobenius norm, single summand under the sqrt via
-- frobenius_norm_def + Real.rpow_le_rpow; Mathlib has this only for the sup norm). norm_trace_le_card:
-- ‖Tr M‖≤(card n)·‖M‖ (trace = sum of card diagonal entries, each ≤‖M‖). Axiom-free.

-- DIFFERENTIAL AREA LAW DERIVED (DifferentialAreaLaw.lean) — removing δS=ηδA as a bare assumption of the
-- QIQT-H⇒GR chain (GPT-5-pro architecture; the wedge-modular-bridge Phase 1).
#print axioms QIQTH.DifferentialAreaLaw.deriv_eq_of_le_of_eq
#print axioms QIQTH.DifferentialAreaLaw.differential_area_law
#print axioms QIQTH.DifferentialAreaLaw.differential_area_law_of_relEntropy
-- expected: standard only — ★ δS=ηδA DERIVED, not assumed. deriv_eq_of_le_of_eq: a bound f≤g near 0
-- saturated at 0 (f 0=g 0) forces EQUAL first variations f'=g' (0 is a local max of f−g ⇒ deriv=0) — WITHOUT
-- assuming f=g. differential_area_law: from the capacity BOUND S≤η·A (= QIQT-H's shannon_le_log_card, a
-- THEOREM) + saturation S 0=η·A 0 (shannon_uniform_eq_log_card) + entanglement first law IsLocalMin(KE−S) 0
-- + differentiability ⇒ δS=ηδA AND δ⟨K⟩=ηδA. differential_area_law_of_relEntropy: GROUNDS the first-law datum
-- hfl in QIQT's own theorem — IsLocalMin(KE−S) 0 IS relative-entropy positivity D=KE−S≥0, D 0=0 (Klein =
-- QuantumEntropy.relEntropy_nonneg + relEntropy_self), so the inputs reduce to {capacity bound, point-
-- saturation, Klein positivity, differentiability}. ANTI-CIRCULARITY: no hypothesis is S=ηA or δS=ηδA; the
-- INEQUALITY (QIQT's bound) + point-saturation + first law ENTAIL the area law, not presuppose it. Replaces the
-- bare hAreaLaw of jacobson_einstein_from_area_law (threading = follow-up; jacobson's chain only uses the
-- leading-ε² coefficient, so the derivative form suffices). Cited inputs (BW K=2πK_boost, boost-flux,
-- Raychaudhuri) stay as separate labelled hyps, NOT mixed into the area law.
#print axioms QIQTH.DifferentialAreaLaw.pernull_premise_of_modular
-- expected: standard only — PHASE B: the per-null premise from DERIVED modular relation + CITED AQFT inputs.
-- Chains the derived δ⟨K⟩=ηδA (k'=η·a') with hBWflux (Bisognano–Wichmann + boost heat flux: δ⟨K⟩=(2π/ℏ)F_T,
-- F_T=∫λT_kk) and hRay (Raychaudhuri leading order: δA=−G_R, G_R=∫λR_kk); with a=2π/(ℏη) these force the
-- per-null relation a·F_T=−G_R (boost-flux ∝ Ricci focusing) that pernull_of_clausius_integral consumes.
-- The modular relation is DERIVED from QIQT; ONLY hBWflux/hRay (the Type III₁ wedge-algebra + geometry
-- Mathlib lacks) are cited, kept SEPARATE — neither is the area law, neither presupposes Einstein. Axiom-free.
-- ASSEMBLY toward QIQT+Bekenstein⇒GR (QiqtToGR.lean):
#print axioms QIQTH.QiqtToGR.bl_pernull_of_modular
#print axioms QIQTH.QiqtToGR.hFocus_of_raychaudhuri
-- expected: standard only — ★ the hFocus input (#3) DERIVED from the machine-checked Raychaudhuri: given
-- equilibrium hequil (shear-expansion quadratic=0, Jacobson's horizon) + the modelling identification harea
-- (area rate = −V^ν∂_νθ), raychaudhuri_focusing_at_equilibrium gives ad=R_kk=BL(Ric)v (BL via Finset.sum_comm).
-- So hFocus's geometric content is machine-checked (null-congruence kinematics, no Einstein); only the area↔θ
-- identification harea stays labelled. Mirrors wedge_hBoostCharge_of_smooth for input #1. Axiom-free.
#print axioms QIQTH.QiqtToGR.bl_pernull_of_qiqt
-- expected: standard only — turns the derived modular relation into Jacobson's POINTWISE per-null premise
-- BL(a·T−Ric)v=0 (the exact `pernull` hyp of jacobson_einstein_equation_of_state), bypassing the affine-
-- integral layer. bl_pernull_of_modular: from k'=η·a' (DERIVED δ⟨K⟩=ηδA) + hFlux (BW boost flux
-- δ⟨K⟩=(2π/ℏ)BL(T)v) + hFocus (Raychaudhuri a'=BL(Ric)v) + a=2π/ℏη ⇒ a·BL(T)v=BL(Ric)v ⇒ BL(a·T−Ric)v=0
-- (via BL_smul_sub). bl_pernull_of_qiqt: COMPOSES differential_area_law_of_relEntropy (QIQT bound+sat+Klein
-- ⇒ k'=η·a') with it, so the per-null premise is DERIVED from QIQT content + ONLY the 2 cited inputs (hFlux,
-- hFocus). No hypothesis is the area law or the conclusion. Next: feed pernull into jacobson for the full
-- a·T=G+Λg. Axiom-free.
#print axioms QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr
-- expected: standard only — ★★★ THE END-TO-END THEOREM. Single theorem: along each null generator, QIQT-H's
-- capacity BOUND S≤η·A (shannon_le_log_card) + saturation (shannon_uniform_eq_log_card) + Klein positivity
#print axioms QIQTH.QiqtGrWitness.qiqt_bekenstein_gives_gr_satisfiable
-- expected: standard only — SATISFIABILITY WITNESS for the 23-hypothesis premise set of
-- qiqt_bekenstein_gives_gr. The flat/vacuum model (g=gi=const gm, identity frame, T=0, zero S/KE/A)
-- verifies all 23 hypotheses and the theorem yields its conclusion (vacuum Einstein eq), so the
-- premise set is jointly satisfiable and the headline theorem is NON-VACUOUS (not vacuously true).
-- ONE-PARTICLE BISOGNANO–WICHMANN — Phase 0 (OneParticleBW.lean): toward DERIVING hFlux (replacing the cited BW).
#print axioms QIQTH.Fock.OneParticleBW.modChar_fermi
#print axioms QIQTH.Fock.OneParticleBW.fermi_mem_Ioo
-- expected: standard only — the SCALAR spectral core of the one-particle BW (modular flow = boost). modChar_fermi:
-- modChar t (fermi x) = exp(i·t·2π x), where fermi x = 2/(1+e^{2π x}) is the spectral form of the wedge RvD R in
-- the boost-momentum (P=−i d/dθ) representation. Since g(r)=log((2−r)/r) and (2−fermi x)/fermi x = e^{2π x}, the
-- modular generator g(fermi x)=2π x — the pointwise core of modUnitary(t)=exp(i·t·2π P)=boostUnitary(−2π t).
-- GPT-5.5 Route C; the physical wedge subspace + standardness + operator identity rvdRC 𝒦=fermi(2π P) are the
-- genuinely analytic inputs (one-particle Reeh–Schlieder/strip-KMS), to be ISOLATED as labelled conditional
-- hypotheses (never axioms). This UPGRADES hFlux from cited toward derived (free field). Axiom-free.
#print axioms QIQTH.Fock.OneParticleBW.boostUnitary_KrepL2
-- expected: standard only — LAYER 1 foundation (GPT-5.5's first Layer-1 brick): L² boost-covariance
-- boostUnitary a (KrepL2 f) = KrepL2 (boostTest(−a) f). The geometric boost acts on the one-particle
-- wavefunction Krep f∈L²(rapidity) exactly as the spacetime boost boostTest(−a) on the test function —
-- the engine for boost-INVARIANCE of the physically-defined wedge subspace 𝒦 (NOT defined from modular
-- data, per the anti-circularity red-team). From Krep_boost + flow θ↦θ−a, via Lp.coeFn_compMeasurePreserving
-- + QuasiMeasurePreserving.tendsto_ae + Lp.ext. Axiom-free.
#print axioms QIQTH.Fock.OneParticleBW.mapsTo_closure_span
-- expected: standard only — INVARIANCE ENGINE: a continuous ℝ-linear L with MapsTo L W W also maps
-- closure(span ℝ W) into itself (span_induction for the span level + image_closure_subset_closure_image
-- + closure_mono for the closure). With L=boostUnitary a, W=boost-closed wedge generating set ⇒
-- boostUnitary a (𝒦_W) ⊆ 𝒦_W — the boost-invariance the GPT-5-pro KMS-uniqueness route needs (pro re-scope:
-- KMS route = days-weeks, vs R=fermi(P) = months; honest endpoint = conditional BW with ONE labelled strip/
-- KMS input Hyp_strip_Krep). Axiom-free.
#print axioms QIQTH.Fock.OneParticleBW.boostUnitary_mapsTo_closure_span
-- expected: standard only — Layer-1 invariance COMPLETE: if S (one-particle vectors) is boost-closed, then
-- 𝒦_W=closure(span ℝ S) is boost-invariant: boostUnitary a (𝒦_W)⊆𝒦_W. mapsTo_closure_span specialized to
-- boostUnitary via toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ. This is the V(a)𝒦=𝒦
-- the KMS-uniqueness route consumes. Axiom-free. (Remaining: KMS-uniqueness lemma [real functional analysis]
-- + wedge generating set + the labelled strip input Hyp_strip_Krep [irreducible AQFT, BGL §4].)
#print axioms QIQTH.Fock.OneParticleBW.lorentzBoost_mapsTo_rightWedge
-- expected: standard only — GEOMETRIC FOUNDATION: the right wedge W_R={z:z¹>|z⁰|} (light-cone form
-- z¹−z⁰>0 ∧ z¹+z⁰>0) in 1+1D Minkowski is BOOST-INVARIANT (lorentzBoost a maps W_R into itself). In
-- light-cone coords the boost scales z⁻↦e^{−a}z⁻, z⁺↦e^{a}z⁺ (cosh∓sinh=e^{∓a}), preserving positivity.
-- This is WHY the wedge generating set {KrepL2 f : supp f⊆W_R} is boost-closed ⇒ 𝒦_W boost-invariant. Axiom-free.
#print axioms QIQTH.Fock.OneParticleBW.boostUnitary_mapsTo_wedgeGenSet
#print axioms QIQTH.Fock.OneParticleBW.boostUnitary_mapsTo_wedgeSubspace
-- expected: standard only — ★ WEDGE-SUBSPACE BOOST-INVARIANCE COMPLETE (the V(a)𝒦=𝒦 the KMS route needs).
-- wedgeGenSet m = {KrepL2 f : f real (starRingEnd∘f=f), supp f⊆rightWedge, MemLp}; boost-closed via the sign
-- lemma + support_boostTest_subset + MemLp under translation (comp_measurePreserving). boostUnitary_mapsTo_
-- wedgeSubspace: boostUnitary a maps closure(span ℝ wedgeGenSet)=𝒦_W into itself — the PHYSICALLY-defined wedge
-- subspace (NOT from modular data), boost-invariant, axiom-free. Soft geometric layer of the one-particle BW
-- COMPLETE; remaining = KMS-uniqueness lemma (formalizable) + labelled strip input Hyp_strip_Krep (irreducible AQFT).
#print axioms QIQTH.Fock.OneParticleBW.stripKMS_trivial
-- expected: standard only — ★★★ SOUNDNESS AUDIT: StripKMS is TRIVIALLY satisfiable for ANY V (given Dense D)!
-- The witness F is only DifferentiableOn the OPEN strip with boundary VALUES imposed pointwise (no continuity
-- linking interior↔boundary), so F≡0 on the open strip + overriding the two boundary lines satisfies it. ⇒ the
-- labelled hStrip of oneParticleBW_of_kms/_wedge is VACUOUS, and the only real content (hUniq with trivial
-- StripKMS) asserts "invariance ⟹ V=Δ^{it}" — FALSE. The current StripKMS is mis-stated (too weak); the honest
-- fix is DiffContOnCl+bounded (now available via diffContOnCl_modCorrExt/modCorrExt_norm_le) + the Δ-WEIGHTED
-- top edge F(t+i)=∫modChar t·(ω/(2−ω))dμ (modCorrExt_kms_flip), NOT the plain flip. Defect recorded machine-checked.
#print axioms QIQTH.Fock.OneParticleBW.stripKMSrvd_real_midline
-- expected: standard only — ★★ RvD Prop 3.5 applied to StripKMSrvd: discharges the Prop-3.5 step of hUniq from
-- the CORRECT labelled KMS input. [CONVENTION CORRECTED 2026-06-21 to faithful RvD Def 3.4: f(t)=⟪η,V_tξ⟫ orbit in
-- LINEAR slot; Δ satisfies this on Im<0, removing a vacuity hole.] Top-edge flip f(t−i)=⟪V_tξ,η⟫ IS conj(f(t))
-- (⟪V_tξ,η⟫=conj⟪η,V_tξ⟫ by inner_conj_symm) ⇒ real_on_midline_of_conj_flip gives the half-strip
-- KMS form: bdd-holo f, f(t)=⟪η,V_tξ⟫, f(t−i/2) REAL. The reality input RvD Thm 3.8 consumes — axiom-free, the
-- genuine Prop-3.5 brick on the hUniq discharge spine (Thm 3.8's remaining g-pairing/device step still labelled).
#print axioms QIQTH.Fock.OneParticleBW.stripKMSrvd_halfStripReal
#print axioms QIQTH.Fock.OneParticleBW.oneParticleBW_of_stripKMSrvd
-- expected: standard only — ★★ NARROWED conditional BW (honest fix of the StripKMS soundness defect): uses the
-- CORRECT StripKMSrvd (RvD Def 3.4) instead of the vacuous StripKMS, and labels only the RvD Thm 3.8 CORE
-- hThm38 (HalfStripReal + 𝒦-invariance ⟹ modUnitary=V). The Prop-3.5 reduction StripKMSrvd⟹HalfStripReal is
-- DISCHARGED axiom-free (stripKMSrvd_halfStripReal = stripKMSrvd_real_midline per pair). So the unproven surface
-- shrinks from "all of Thm 3.8 + a vacuous StripKMS" to "just the Thm 3.8 g-function assembly". Strictly more honest.
#print axioms QIQTH.Fock.OneParticleBW.comparisonDatum_of_gConstancy
-- expected: standard only — ★★★ g-FUNCTION OUTPUT ⟹ ComparisonDatum (operator-algebra wrapper of RvD Thm 3.8).
-- GConstancy S V := ∀t η,ξ∈𝒦, ⟪V_tη,Δ^{it}Jξ⟫=⟪η,Jξ⟫ (analytic g-constancy output). ⟹ ComparisonDatum: for w⊥i𝒦
-- pick ξ=Δ^{−it}(Jw)∈𝒦; then Δ^{it}Jξ=w, Jξ=Δ^{−it}w (modConj_commute_modUnitary + group law), so ⟪V_tη,w⟫=
-- ⟪η,Δ^{−it}w⟫=⟪Δ^{it}η,w⟫ (modUnitary_adjoint) ⟹ conj ⟹ ⟪w,V_tη⟫=⟪w,Δ^{it}η⟫. ⟪η,Jξ⟫ RHS carries Δ-side
-- automatically. So the hUniq discharge now reduces to the SINGLE analytic step GConstancy; ALL algebra discharged.
#print axioms QIQTH.Fock.OneParticleBW.comparisonDatum_modUnitary
-- expected: standard only — NON-VACUITY CHECK: Δ^{it} (modUnitary S) satisfies ComparisonDatum trivially
-- (⟪w,Δ^{it}η⟫=⟪w,Δ^{it}η⟫, rfl). Confirms the narrowed conditional oneParticleBW_of_comparison is NOT a
-- vacuous-premise artifact — Δ is a model of hCompare's conclusion; the content is genuine UNIQUENESS.
#print axioms QIQTH.Fock.OneParticleBW.gTopEdge_real
-- expected: standard only — ★ g-FUNCTION TOP EDGE real (RvD Thm 3.8): g(t)=⟪V_tη, Δ^{it}Jξ⟫ is REAL for ξ,η∈𝒦,
-- V_tη∈𝒦. Δ^{it}Jξ=J(Δ^{it}ξ)∈(i𝒦)^⊥ (modConj_commute_modUnitary + Δ^{it}ξ∈𝒦 + J𝒦=(i𝒦)^⊥), so the 𝒦×(i𝒦)^⊥
-- pairing is real (inner_real_of_mem_K_perp_IK). GEOMETRIC, no analysis. The genuine device-vector g-function's
-- real-axis edge (2nd slot = z-varying Δ^{it}Jξ, NOT the discredited fixed Jξ of corrJ). Feeds GConstancy.
#print axioms QIQTH.Fock.OneParticleBW.gConstancy_of_inputs
-- expected: standard only — ★★★ FULL GConstancy from the 2 named RvD inputs: V-group + hKinv + h1 (bottom-edge KMS)
-- + hdense (√R-range density in 𝒦) ⇒ GConstancy S V. Chains gConstancy_eta_of_bottom (η) → gConstancy_xi_of_density (ξ).
#print axioms QIQTH.Fock.OneParticleBW.oneParticleBW_of_inputs
-- expected: standard only — ★★★★ COMPLETE DEVICE g-FUNCTION DISCHARGE of hUniq: modUnitary S t = V t from V-group +
-- hInv + hKMS(StripKMSrvd) + the 2 named RvD inputs (h1 bottom-edge mid-line KMS reality + hdense √R-range density in 𝒦).
-- gConstancy_of_inputs ⟹ comparisonDatum_of_gConstancy ⟹ oneParticleBW_of_comparison. EVERY analytic/constancy/density
-- step machine-checked axiom-free; labelled surface = exactly h1 + hdense (both RvD-structure facts). The un-garbled
-- g-function discharge END-TO-END.
#print axioms QIQTH.Fock.OneParticleBW.oneParticleBW_of_comparison
-- expected: standard only — ★★★ TIGHTEST honest labelling of the hUniq discharge. SOLE labelled hyp hCompare =
-- (HalfStripReal ⟹ ComparisonDatum), where ComparisonDatum = ∀t η∈𝒦 ∀w⊥i𝒦, ⟪w,V_tη⟫=⟪w,Δ^{it}η⟫ — the EXACT
-- output of RvD Thm 3.8's g-function. EVERYTHING else discharged axiom-free: Prop-3.5 reduction (stripKMSrvd_
-- halfStripReal), Δ-invariance (modUnitary_mapsTo_K), operator assembly (modUnitary_eq_of_orbit_compare:
-- IsSeparating⇒V_tη=Δ^{it}η on 𝒦, IsCyclic⇒V_t=Δ^{it}). So the ONLY unproven step is the source-garbled g-pairing/
-- Prop-3.7-device producing the comparison from the half-strip reality. Minimal honest "what remains".
#print axioms QIQTH.Fock.OneParticleBW.oneParticleBW_of_kms
-- expected: standard only — ★ CONDITIONAL ONE-PARTICLE BISOGNANO–WICHMANN (KMS-uniqueness route, gpt-5-pro
-- verdict: KMS-uniqueness is NOT provable in current Mathlib — needs unbounded Tomita/Hardy-strip, months —
-- so LABEL it, never a Lean axiom). modUnitary S t = V t from {hUniq: KMS-uniqueness for standard subspaces
-- (BGL §2, labelled HYPOTHESIS) + hStrip: StripKMS V D (the strip/KMS property, the single physical AQFT input
-- Hyp_strip_Krep, BGL §4, defined precisely via an ∃-quantified holomorphic extension on kmsStrip={0<Im z<1}
-- with KMS boundary flip — NO Hardy machinery) + hInv: V(t)𝒦⊆𝒦 (PROVED for the wedge via boostUnitary_mapsTo_
-- wedgeSubspace)}. Instantiated at 𝒦_W, V=boostUnitary(−2π·) ⇒ modUnitary 𝒦_W=boostUnitary(−2π·) ⇒ hFlux
-- DERIVED modulo exactly TWO labelled citable AQFT facts. AXIOM-FREE (the AQFT facts are hypotheses, not axioms);
-- genuine contribution = the invariance is DERIVED. This is the honest endpoint of the BW reduction.
#print axioms QIQTH.Fock.OneParticleBW.oneParticleBW_wedge
-- expected: standard only — ★ ONE-PARTICLE BW FOR THE WEDGE (invariance DISCHARGED from the proved lemma).
-- For S a StandardSubspace on the one-particle Lp whose real subspace is 𝒦_W=closure(span ℝ wedgeGenSet)
-- (hcarrier — the standardness of 𝒦_W = the one-particle Reeh–Schlieder input that makes S a StandardSubspace)
-- and V t=boostUnitary(−2πt) (hVboost): modUnitary S t=V t from {hUniq (KMS-uniqueness, BGL §2, labelled) +
-- hStrip (StripKMS, BGL §4, labelled)} — the boost-INVARIANCE oneParticleBW_of_kms needs is DISCHARGED here
-- from boostUnitary_mapsTo_wedgeSubspace (the proved geometric result) via hcarrier+hVboost. So the wedge
-- instance rests ONLY on the labelled AQFT facts, invariance derived. = modUnitary 𝒦_W=boostUnitary(−2π·),
-- the BW identification ⇒ hFlux. Axiom-free.
-- (relEntropy_nonneg) DERIVE the differential area law δS=ηδA, which with the two CITED inputs (hFlux=Bisognano–
-- Wichmann boost flux, hFocus=Raychaudhuri focusing) + structural (Lorentzian congruence g=PᵀηP, ∇·T=0,
-- f-regularity) ⇒ ∃Λ, a·T=G+Λg (genuine Einstein tensor, constant Λ) via jacobson_einstein_equation_of_state.
-- HONEST SCOPE: NOT from-nothing. QIQT supplies the INEQUALITY side as THEOREMS; δS=ηδA is DERIVED (no hyp is
-- S=ηA). CITED (Mathlib-unprovable, explicit labelled hyps NEVER axioms): hFlux (Type III₁ wedge-modular=boost,
-- BW) + hFocus (Raychaudhuri) + structural + per-generator path differentiability (modelling). All geometry
-- (Bianchi/∇·G=0/null-cone→tensor/Λ=const) machine-checked axiom-free. Verified: no sorry, no vacuous True hyps.
-- STRONG CONTINUITY of the boost group (first brick of the Stone-generator program toward grounding hBoostCharge):
#print axioms QIQTH.Fock.OneParticleBW.boostUnitary_eq_vadd
#print axioms QIQTH.Fock.OneParticleBW.continuous_boostUnitary_apply
#print axioms QIQTH.Fock.OneParticleBW.tendsto_boostUnitary_wedge
#print axioms QIQTH.Fock.OneParticleBW.continuous_inner_boostUnitary
-- expected: standard only — continuous_inner_boostUnitary: ★ matrix-element continuity t↦⟪η,boostUnitary t ξ⟫,
-- the real-axis boundary regularity of the correlation F_{η,ξ}(t) whose strip extension StripKMS asserts (a
-- derived ingredient of the wedge-KMS input) = scalar shadow of strong continuity ∘ continuous inner product.
#print axioms QIQTH.Fock.OneParticleBW.coeFn_boostUnitary
#print axioms QIQTH.Fock.OneParticleBW.inner_boostUnitary_toLp
-- expected: standard only — coeFn_boostUnitary: (boostUnitary a ξ)(θ)=ξ(θ−a) a.e. (the rapidity boost is the
-- spatial translation, from MPFlow.unitary_apply + pullback flow). inner_boostUnitary_toLp: ★ the boost matrix
-- coefficient ⟪f.toLp, boostUnitary s (f.toLp)⟫ = ∫ conj(f θ)·f(θ−s) dθ — the inner-product-to-integral bridge
-- (L2.inner_def + MemLp.coeFn_toLp + coeFn_boostUnitary + measure-preserving shift) turning the abstract boost
-- correlation into an analyzable cross-correlation integral. Setup for the boost-charge derivative (→ hBoostCharge).
#print axioms QIQTH.Fock.OneParticleBW.hasDerivAt_inner_boostUnitary_wedge
-- expected: standard only — ★★ THE BOOST-CHARGE DERIVATIVE (analytic core of hBoostCharge). For ξ=f.toLp with f
-- smooth enough (differentiable f', f & |f|² integrable, ‖f'‖≤B — all satisfied by any Schwartz/C¹-compact-support
-- f), d/dt⟪ξ,boostUnitary(−2πt)ξ⟫|₀ = 2π·∫conj(f)·f' = the RAPIDITY-MOMENTUM expectation 2π⟪ξ,−i∂_θξ⟫ (the boost
-- charge). Differentiation under the integral (hasDerivAt_integral_of_dominated_loc_of_deriv_le, dominating fn
-- 2π·B·|f|) on the bridge integral; chain rule via HasDerivAt.scomp (ℝ→ℂ). So hBoostCharge's ANALYTIC content is
-- DERIVED; with unitarity (derivative purely imaginary) it is hBoostCharge modulo only 2π⟪ξ,pξ⟫=(2π/ℏ)T_kk (stress
-- tensor). Mathlib has NO Stone's theorem for unitary groups (checked), so this direct H¹ route is the grounding.
#print axioms QIQTH.Fock.OneParticleBW.hasDerivAt_inner_boostUnitary_imaginary
-- expected: standard only — ★★★ hBoostCharge GROUNDED in its physical i·(real) form: d/dt⟪ξ,boostUnitary(−2πt)ξ⟫|₀
-- = Complex.I·((2π∫conj(f)f').im) — PURELY IMAGINARY (= i·boost energy), the exact shape of the labelled
-- hBoostCharge. Imaginarity forced by UNITARITY (GPT-5.5-pro): Re⟪ξ,U(t)ξ⟫≤‖ξ‖² (Complex.re_le_norm + Cauchy-
-- Schwarz norm_inner_le_norm + isometry LinearIsometryEquiv.norm_map), equality at 0 (inner_self_eq_norm_mul_norm)
-- ⇒ Re-correlation has a max at 0 ⇒ IsLocalMax.hasDerivAt_eq_zero ⇒ Re(deriv)=0 ⇒ deriv=I·(deriv.im). So
-- hBoostCharge is DERIVED for any smooth wedge state; only the stress-tensor identification 2π⟪ξ,pξ⟫=(2π/ℏ)T_kk stays labelled.
#print axioms QIQTH.Fock.OneParticleBW.wedge_hBoostCharge_of_smooth
-- expected: standard only — ★★★ the WedgeKMSFlux boost-charge SLOT derived: the bundle's hBoostCharge demand
-- HasDerivAt(⟪ξ,boostUnitary(−2πt)ξ⟫)(i·(2π/ℏ)T_kk) is, for any smooth wedge state ξ=f.toLp, exactly
-- hasDerivAt_inner_boostUnitary_imaginary modulo the SINGLE scalar identification hTkk:(2π/ℏ)T_kk=boost energy
-- (conserved boost Killing charge = stress-tensor flux). So the whole boost-charge slot reduces to ONE real
-- equation; everything operator/analytic is machine-checked. Pins the irreducible labelled remainder of input #1.
-- KMS STRIP-UNIQUENESS (StripUniqueness.lean): the analytic core of the labelled KMS-uniqueness (hUniq) — the
-- "Hardy-strip infrastructure Mathlib does not yet have," now assembled from Mathlib's Phragmén–Lindelöf.
#print axioms QIQTH.StripUniqueness.eqOn_of_bdd_holomorphic_strip
#print axioms QIQTH.StripUniqueness.kms_correlation_boundary_determined
#print axioms QIQTH.StripUniqueness.eqZero_of_im_zero_edge
-- expected: standard only — ★★★ ONE-EDGE BOUNDARY UNIQUENESS (Hadamard three-lines, the Schwarz-reflection-
-- free substitute Mathlib was thought to lack): f bounded-holomorphic on the KMS strip + f=0 on the BOTTOM
-- edge (Im=0) ⇒ f=0 on the closed strip. Rotate horizontal→vertical strip (w↦I·w) + Hadamard
-- norm_le_interp_of_mem_verticalClosedStrip' with edge bounds a=0,b=M ⇒ ‖f‖≤0^{1−θ}M^θ=0 interior;
-- Set.EqOn.of_subset_closure to the closure. THE step-5 matching tool — removes the perceived reflection wall.
#print axioms QIQTH.StripUniqueness.eqZero_of_im_zero_edge_halfStrip
-- expected: standard only — ★ CORRECT-STRIP analytic core: one-edge uniqueness on the HALF strip {−1/2≤Im≤0}
-- (the strip RvD Thm 3.8 / Prop 3.5 ACTUALLY use, lower edge Im=−1/2 = half-shift Δ^{½}=J). f bdd-holo +
-- f=0 on top edge Im=0 ⇒ f=0 (Hadamard three-lines, rotate to re⁻¹'[−1/2,0], zero edge u=0 ⇒ M^{1−θ}·0^θ=0).
-- Replaces the full-strip modeling the corrC framework got wrong (see FRAMEWORK CAVEAT above). Correct-
-- direction infrastructure; the faithful half-strip g-function rebuild still needs RvD's R^{−½} ζ-device.
#print axioms QIQTH.StripUniqueness.eqOn_of_im_zero_edge_halfStrip
-- expected: standard only — two bdd-holo F,G on {−1/2≤Im≤0} agreeing on the top edge Im=0 agree on the
-- half-strip (eqZero_of_im_zero_edge_halfStrip on F−G). The correct-strip matching step: orbit correlation
-- ⟨h(z),w⟩ and the KMS function share Im=0 values ⟨U_t ξ,η⟩ ⇒ coincide ⇒ KMS lower-edge (Im=−1/2) reality transfers.
#print axioms QIQTH.StripUniqueness.real_on_midline_of_conj_flip
-- expected: standard only — ★★★ RvD PROPOSITION 3.5 (reality on the mid-line): bdd-holo f on {−1<Im<0} with the
-- conjugate-flip f(t−i)=conj(f(t)) ⇒ Im f(t−i/2)=0. Reflection g(z)=conj(f(conj z−i)) is holo (DifferentiableAt.
-- conj_conj), bounded, =f on Im=0 (g(t)=conj(f(t−i))=conj(conj(f t))=f t by flip) ⇒ (eqOn_of_im_zero_edge_negStrip)
-- g=f on the strip ⇒ f(t−i/2)=conj(f(t−i/2)). The bridge from RvD Def 3.4's full-strip KMS to the half-strip
-- reality Thm 3.8 uses (Δ^{1/2}=J on the standard subspace). NON-GARBLED, faithful to the clean source.
#print axioms QIQTH.StripUniqueness.eqZero_of_im_zero_edge_negStrip
#print axioms QIQTH.StripUniqueness.eqOn_of_im_zero_edge_negStrip
-- expected: standard only — ★ UNIT-strip {−1≤Im≤0} one-edge uniqueness (full-width companion of the halfStrip
-- versions): bdd-holo + zero on top edge Im=0 ⇒ zero on the strip (Hadamard three-lines on re⁻¹'[−1,0]); two
-- such agreeing on Im=0 agree on the strip. This is the strip of RvD Def 3.4 (full-width KMS) — the uniqueness
-- RvD Prop 3.5's reflection argument invokes (full strip {−1≤Im≤0}, before Prop 3.5 folds to the half-strip).
#print axioms QIQTH.StripUniqueness.eqOn_of_im_zero_edge
-- expected: standard only — ★ one-edge determination: two bounded-holomorphic F,G agreeing on the bottom edge
-- (Im=0) agree on the closed strip (eqZero_of_im_zero_edge on F−G). RvD Thm 3.8 step-5 matching: the entire
-- orbit correlation ⟨h(z),b⟩ and the StripKMSrvd KMS function agree on the real axis ⇒ on the strip ⇒ the KMS
-- top-edge reality transfers to the orbit correlation (the Im=1 input of corrC_orbit_eq_of_edges_real).
#print axioms QIQTH.StripUniqueness.eqConst_of_im_zero_halfStrip
-- expected: standard only — ★★ HALF-STRIP two-edge constancy: bdd-holo g on {-1/2<Im<0} real on edges Im=0 & Im=-1/2
-- ⇒ g CONSTANT. Adapts eqConst_of_im_zero_strip ({0<Im<1}) via affine φ(w)=-w/2 ({0<Im w<1}→{-1/2<Im z<0}); G=g∘φ
-- bdd-holo real-on-edges ⇒ const, pull back. The constancy the RvD device g-function (real on Im=0 & Im=-1/2) consumes.
#print axioms QIQTH.StripUniqueness.eqConst_of_im_zero_strip
-- expected: standard only — ★★ bounded-holomorphic g with Im g=0 on BOTH strip edges ⇒ g CONSTANT. Combines
-- im_zero_on_strip (Im g=0 throughout) with AnalyticOnNhd.eq_const_of_re_eq_const (Re(i·g)=−Im g=0 const ⇒ i·g
-- const ⇒ g const). = RvD Theorem 3.8's "real on both edges ⇒ constant" conclusion, reflection-free.
#print axioms QIQTH.StripUniqueness.im_zero_on_strip
-- expected: standard only — ★ MAX-MODULUS on the strip: if g is bounded-holomorphic on the KMS strip
-- (DiffContOnCl+bound) and Im g=0 on BOTH edges, then Im g=0 throughout. Via |exp(±i·g)|=exp(∓Im g)=1 on the
-- edges ⇒ PhragmenLindelof.horizontal_strip ⇒ |exp(i·g)|≤1 and |exp(−i·g)|≤1 inside ⇒ Im g=0. The
-- REFLECTION-FREE substitute for RvD's "real on both edges ⇒ constant" step (the analytic crux of RvD Thm 3.8
-- KMS-uniqueness). Builds toward discharging hUniq via the bounded RvD route (Mathlib lacks Schwarz reflection,
-- so this routes through max-modulus + the already-built strip-uniqueness instead).
-- expected: standard only — eqOn_of_bdd_holomorphic_strip: ★ two bounded functions holomorphic on the open KMS
-- strip {0<Im<1}, continuous to the closure, AGREEING ON BOTH EDGES (Im=0 and Im=1), agree on the whole closed
-- strip — via PhragmenLindelof.eqOn_horizontal_strip (bounded ⇒ the sub-double-exp growth bound with c=0,B=0).
-- kms_correlation_boundary_determined: restated for the modular setting — a KMS two-point correlation is pinned
-- by its real-axis values F(t) and its KMS-flipped top-edge values F(t+i). This is the analytic heart of
-- one-particle KMS-uniqueness; the remaining hUniq discharge is the Borchers/Florig group-equality reduction.
-- MODULAR CHARACTER continuation (StandardSubspaceModularFlow.lean): the modular flow's OWN KMS strip seed.
#print axioms QIQTH.StandardSubspaceModular.modCharC_add
-- modCharC_add: u_{z+w}(r)=u_z(r)·u_w(r) (exp homomorphism in z; exp_add on (0,2), 1·1 off it). Drives the
-- device t-translation d_{(↑t)+z}=u_t·d_z ⇒ bottom-edge factorization deviceOpC(t−i/2)=Δ^{it}·deviceOpC(−i/2).
#print axioms QIQTH.StandardSubspaceModular.differentiable_modCharC
#print axioms QIQTH.StandardSubspaceModular.modCharC_kms_flip
#print axioms QIQTH.StandardSubspaceModular.modCharC_ofReal
-- expected: standard only — modCharC z r = exp(i·z·log((2−r)/r)) is the analytic continuation of the modular
-- character modChar to COMPLEX time z. differentiable_modCharC: entire in z (Complex.differentiable_exp).
-- modCharC_ofReal: matches modChar on the real axis (rfl). modCharC_kms_flip: ★ THE KMS BOUNDARY FLIP
-- u_{z+i}(r)=u_z(r)·(r/(2−r)) — shifting Im by β=1 multiplies by the modular weight exp(−log((2−r)/r)). This is
-- the scalar core of Δ^{it}'s own strip/KMS property, the regularity needed to enter the strip-uniqueness
-- comparison toward discharging hUniq. (Next: lift to the spectral-integral correlation ⟪ξ,Δ^{it}ξ⟫.)
-- ENTIRE-VECTOR construction (RvD Thm 3.8 operator half): Gaussian smearing into K.
#print axioms QIQTH.StandardSubspaceModular.gaussSmear_integrable
#print axioms QIQTH.StandardSubspaceModular.gaussSmear_mem_K
#print axioms QIQTH.StandardSubspaceModular.gaussSmear_smul_left
-- (gaussSmear_smul_left): V_s(gaussSmear V n η)=∫ e^{−n t²}•V_{s+t}η dt — V_s commutes with the Bochner integral
-- (integral_comp_comm) + the group law shifts the orbit; after u=s+t the integrand is e^{−n(u−s)²}•V_u η,
-- ENTIRE in s ⇒ gaussSmear is an entire vector for V (RvD's key property for Thm 3.8). Uses map_smul_of_tower
-- (ℂ-linear V_s commutes with the ℝ-scalar Gaussian weight).
#print axioms QIQTH.StandardSubspaceModular.gaussian_normalization
#print axioms QIQTH.StandardSubspaceModular.entireVec_mem_K
-- expected: standard only — gaussian_normalization: √(n/π)·∫e^{−n t²}=1 (integral_gaussian + sqrt algebra), so
-- √(n/π) is the approximate-identity constant. entireVec V n η = √(n/π)•gaussSmear V n η = RvD's normalised
-- dense entire vector; entireVec_mem_K: it lands in K (real-scalar smul of gaussSmear_mem_K).
#print axioms QIQTH.StandardSubspaceModular.entireVec_sub
-- expected: standard only — the mollifier error form η_n−η = √(n/π)•∫ e^{−n t²}•(V_t η−η) dt (subtract the
-- normalised constant η=√(n/π)•∫e^{−n t²}•η; integral_sub + integral_smul_const + the normalization). Setup for
-- the density η_n→η (Gaussian concentrates at t=0 where V_t η→η by strong continuity).
#print axioms QIQTH.StandardSubspaceModular.entireVec_sub_norm_le
-- expected: standard only — ‖η_n−η‖ ≤ √(n/π)·∫ e^{−n t²}·‖V_t η−η‖ dt (norm_integral_le_integral_norm on the
-- mollifier form), reducing the VECTOR density to a SCALAR Gaussian-mollifier limit of t↦‖V_t η−η‖ (bounded,
-- continuous, =0 at t=0). The convergence of that scalar mollifier is the remaining density brick.
#print axioms QIQTH.StandardSubspaceModular.gauss_mollifier_change_of_var
-- expected: standard only — change of variables u=√n·t: ∫ e^{−u²}·f(u/√n) du = √n·∫ e^{−n t²}·f(t) dt
-- (Measure.integral_comp_div + the exponent identity n·(u/√n)²=u²). Turns the CONCENTRATING Gaussian kernel into
-- a FIXED e^{−u²} against the rescaled f(u/√n), so the mollifier limit → f(0) follows by dominated convergence
-- (f(u/√n)→f(0)). Foundation for the scalar density convergence.
#print axioms QIQTH.StandardSubspaceModular.gauss_mollifier_integral_tendsto
-- expected: standard only — ★ the fixed-Gaussian mollifier LIMIT (dominated convergence): ∫e^{−u²}·f(u/√n)du →
-- ∫e^{−u²}·f(0)du as n→∞ for bounded continuous f. f(u/√n)→f(0) (u/√n→0 via Real.tendsto_sqrt_atTop + f cont),
-- dominated by e^{−u²}·M (tendsto_integral_filter_of_dominated_convergence). With change_of_var this gives
-- √(n/π)∫e^{−n t²}f → f(0) — the scalar density. Combined with entireVec_sub_norm_le ⇒ η_n → η (RvD density).
#print axioms QIQTH.StandardSubspaceModular.gauss_density_tendsto
-- expected: standard only — ★ the SCALAR Gaussian density √(n/π)·∫e^{−n t²}·f(t)dt → f(0) for bounded
-- continuous f. √(n/π)∫e^{−nt²}f = √(1/π)∫e^{−u²}f(u/√n) (change_of_var) → √(1/π)∫e^{−u²}f(0) = f(0)
-- (integral_gaussian: ∫e^{−u²}=√π, √(1/π)·√π=1). The mollifier limit, scalar form.
#print axioms QIQTH.StandardSubspaceModular.entireVec_tendsto
-- expected: standard only — ★★ RvD ENTIRE-VECTOR DENSITY η_n → η: the normalised entire vectors
-- η_n = √(n/π)∫e^{−n t²}V_t η converge to η (strongly-cont contraction V, V_0 η=η). Squeeze
-- 0 ≤ ‖η_n−η‖ ≤ √(n/π)∫e^{−nt²}‖V_t η−η‖ → ‖V_0 η−η‖=0 (entireVec_sub_norm_le + gauss_density_tendsto on
-- t↦‖V_t η−η‖, bounded by 2‖η‖). With entireVec_mem_K ⇒ entire vectors DENSE in K — the totality input
-- for RvD Theorem 3.8 KMS-uniqueness (hUniq). The analytic density backbone is now COMPLETE.
#print axioms QIQTH.StandardSubspaceModular.gaussSmearC_integrable
-- expected: standard only — the COMPLEX ORBIT gaussSmearC V n η z = ∫ e^{−n((u)−z)²}•V_u η du (H-valued,
-- complex time z) is Bochner-integrable ∀z: dominated by e^{n(Im z)²}·e^{−n(u−Re z)²}·‖η‖
-- (Re(−n(u−z)²)=−n(u−Re z)²+n(Im z)², shifted Gaussian via integrable_exp_neg_mul_sq.comp_sub_right).
#print axioms QIQTH.StandardSubspaceModular.gaussSmearC_ofReal
-- expected: standard only — ★ REAL-AXIS AGREEMENT gaussSmearC V n η ↑s = V_s(gaussSmear V n η): the complex
-- orbit restricted to ℝ is the genuine unitary-group orbit of the smeared vector (complex kernel collapses
-- to real e^{−n(u−s)²}, translation u=s+t via integral_add_left_eq_self + gaussSmear_smul_left). Anchors the
-- entire extension gaussSmearC to the actual flow V — toward the RvD Thm 3.8 operator assembly.
#print axioms QIQTH.StandardSubspaceModular.integrable_abs_add_mul_exp_neg_mul_sq
-- expected: standard only — LINEAR×GAUSSIAN integrability Integrable(u↦(|u|+c)·e^{−b u²}), b>0:
-- |u|·e^{−bu²} (= ‖u·e^{−bu²}‖, integrable_mul_exp_neg_mul_sq) + c·e^{−bu²}. The integrable DOMINATING
-- function for the holomorphy of gaussSmearC (bounds ‖2n(u−z)·e^{−n(u−z)²}‖ uniformly on a ball).
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_gaussSmearC
-- expected: standard only — ★★★ THE COMPLEX ORBIT IS ENTIRE (differentiation under the integral):
-- HasDerivAt (gaussSmearC V n η) (∫ 2n(u−z₀)·e^{−n(u−z₀)²}·V_u η) z₀. Derivative integrand dominated
-- uniformly on a unit ball by 2n·C₁·‖η‖·(|u−Re z₀|+|Im z₀|+2)·e^{−(n/2)(u−Re z₀)²}
-- (hasDerivAt_integral_of_dominated_loc_of_deriv_le; Re(−n(u−z)²)=−n(u−Re z)²+n(Im z)², AM-GM
-- (u−Re z)²≥(u−Re z₀)²/2−2, |Im z|≤|Im z₀|+1). The load-bearing RvD Thm 3.8 operator-assembly piece.
#print axioms QIQTH.StandardSubspaceModular.differentiable_gaussSmearC
-- expected: standard only — gaussSmearC V n η is Differentiable ℂ everywhere (entire). Composed with a
-- continuous-linear functional ⇒ the entire KMS correlation for the strip-uniqueness step of Thm 3.8.
#print axioms QIQTH.StandardSubspaceModular.differentiable_corrC
-- expected: standard only — ★ the KMS two-point CORRELATION corrC ξ V n η z = ⟨ξ,gaussSmearC V n η z⟩ is
-- ENTIRE (innerSL ℂ ξ ∘ the entire orbit). The analytic object the strip-uniqueness step compares between
-- two candidate modular flows.
#print axioms QIQTH.StandardSubspaceModular.corrC_ofReal
-- expected: standard only — real-axis value corrC ξ V n η ↑s = ⟨ξ,V_s(gaussSmear V n η)⟩: on ℝ the
-- correlation is the genuine matrix element of the flow (gaussSmearC_ofReal). Boundary data for Thm 3.8.
#print axioms QIQTH.StandardSubspaceModular.clm_eq_of_eqOn_K
-- expected: standard only — ★★ 𝒦→H CAPSTONE: two continuous ℂ-linear A,B agreeing on 𝒦 agree everywhere.
-- By ℂ-linearity also agree on i𝒦 (q∈i𝒦 ⇒ −i·q∈𝒦), hence on 𝒦+i𝒦 which is DENSE (IsCyclic 𝒦⊔i𝒦=⊤);
-- continuity (Continuous.ext_on). Lifts V_t η=Δ^{it}η on 𝒦 (eq_of_mem_K_of_inner_perp_IK) to V_t=Δ^{it}.
#print axioms QIQTH.StandardSubspaceModular.inner_modConj_smul_left
-- expected: standard only — J-CANCELLATION: ⟪J(c•v),w⟫=c•⟪Jv,w⟫ (ℂ-LINEAR in v). J antilinear (modConj_smul_conj)
-- ∘ inner conj-linear (inner_smul_left) = ℂ-linear (conj∘conj=id). Foundation of the J-twisted bilinear form.
#print axioms QIQTH.StandardSubspaceModular.modConjBilin
-- expected: standard only — ★★ J-TWISTED ℂ-BILINEAR FORM B(v,w)=⟪Jv,w⟫ : H →L[ℂ] H →L[ℂ] ℂ (mkContinuous₂; ℂ-linear
-- in v by J-cancellation, in w by inner; bound ‖v‖‖w‖ via modConj_norm). THE construction making the RvD g-function
-- g(z)=B(d_z(R)ζ, V_z η) HOLOMORPHIC (bounded bilinear of two holo curves) despite J's antilinearity.
#print axioms QIQTH.StandardSubspaceModular.modConj_smul_conj
-- expected: standard only — ★ J IS CONJUGATE-LINEAR: modConj(c•η)=conj(c)•modConj η. Extends antilinearity
-- (c=i) to all c via c=Re c+i·Im c + J's ℝ-linearity. Bundles J R^{½}J (J-sandwiches) as ℂ-linear — the
-- clean foundation for the B-bundling toward J R^{½}J=(2−R)^{½} (sqrt_unique).
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdSqrtR_modConj
-- expected: standard only — ★★★ SQRT-REFLECTION J R^{½}J=(2−R)^{½} (the "antilinear-CFC frontier", routed
-- around via CFC.sqrt_unique — NOT general antilinear CFC). Bundle B ξ=J(R^{½}(Jξ)) as ℂ-linear
-- (modConj_smul_conj×2), self-adjoint+positive (antiunitary modConj_inner_conj reduces ⟨Bx,y⟩ to
-- conj⟨R^{½}Jx,Jy⟩, R^{½}≥0), B·B=2−R (modConjSqrtR_sq) ⇒ sqrt_unique ⇒ B=(2−R)^{½}. Unblocks JPJ=1−Q ⇒ J𝒦=(i𝒦)^⊥.
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdSqrtTwoSubR_of_fixed
-- expected: standard only — BOTTOM-EDGE sqrt swap for J-fixed ζ: J(2−R)^{½}ζ=R^{½}ζ when Jζ=ζ (modConj_rvdSqrtTwoSubR_
-- modConj at Jζ=ζ). RvD's (2−R)^{½}ζ=Jξ device argument: the −i/2 device √(2−R) swaps to √R=ξ. Step (a1) of bottom edge.
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdSqrtTwoSubR_modConj
-- expected: standard only — symmetric sqrt-reflection J(2−R)^{½}J=R^{½}: immediate from J R^{½}J=(2−R)^{½}
-- by sandwiching with J + J²=1. Toward JTJ=T ⇒ [J,T]=0 ⇒ JDJ=D ⇒ JPJ=1−Q ⇒ J𝒦=(i𝒦)^⊥.
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdT_modConj
-- expected: standard only — ★ JTJ=T: J commutes with the polar radius T=R^{½}(2−R)^{½}. JTJ=(J R^{½}J)(J(2−R)^{½}J)
-- =(2−R)^{½}R^{½}=R^{½}(2−R)^{½}=T (both sqrt-reflections + sqrts commute). Keystone ⇒ [J,T]=0 ⇒ JDJ=D ⇒ JPJ=1−Q.
-- (modConj_rvdSqrtR = the "moved" reflection J R^{½}=(2−R)^{½}J used here.)
#print axioms QIQTH.StandardSubspaceModular.rvdT_modConj
-- expected: standard only — TJ=D: rvdT(modConj η)=rvdPmQ η. Combine [J,T]=0 (from JTJ=T) with JT=D (modConj_rvdT).
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdPmQ_modConj
-- expected: standard only — ★ JDJ=D: modConj(rvdPmQ(modConj ξ))=rvdPmQ ξ. From TJ=D: J(D(Jξ))=J(T ξ)=D ξ.
-- With JRJ=2−R this gives JPJ=(JRJ+JDJ)/2=((2−R)+D)/2=1−Q ⇒ J𝒦=(i𝒦)^⊥.
#print axioms QIQTH.StandardSubspaceModular.modConj_projIK_modConj
-- expected: standard only — ★ JQJ=1−P: modConj(projIK(modConj ξ))=ξ−projK ξ. =(JRJ−JDJ)/2=((2−R)−D)/2=1−P,
-- via 2•projIK=rvdR−rvdPmQ + JRJ=2−R + JDJ=D + smul_right_injective (cancel 2). RvD Prop 2.2(5).
#print axioms QIQTH.StandardSubspaceModular.projIK_modConj_eq_zero_of_mem_K
-- expected: standard only — ★★ J𝒦 ⊆ (i𝒦)^⊥ (RvD Prop 2.2(5)): ξ∈𝒦 (projK ξ=ξ) ⇒ projIK(modConj ξ)=0. From
-- JQJ=1−P: J(Q(Jξ))=ξ−Pξ=0, J injective (J²=1) ⇒ Q(Jξ)=0. PLACES the J-twisted w-vectors of Thm 3.8's
-- g-function in (i𝒦)^⊥ — the w-construction's subspace geometry COMPLETE. (antilinear-CFC "frontier" route done.)
#print axioms QIQTH.StandardSubspaceModular.modConj_projK_modConj
-- expected: standard only — JPJ=1−Q: modConj(projK(modConj ξ))=ξ−projIK ξ =(JRJ+JDJ)/2=((2−R)+D)/2=1−Q. Symmetric to JQJ=1−P.
#print axioms QIQTH.StandardSubspaceModular.projK_modConj_eq_self_of_perp_IK
-- expected: standard only — ★ (i𝒦)^⊥ ⊆ J𝒦 (reverse incl ⇒ J𝒦=(i𝒦)^⊥): w⊥i𝒦 ⇒ projK(modConj w)=modConj w
-- (Jw∈𝒦). From JPJ=1−Q: J(P(Jw))=w−Qw=w, J injective ⇒ P(Jw)=Jw. So the (i𝒦)^⊥ w-supply is EXACTLY J𝒦.
#print axioms QIQTH.StandardSubspaceModular.modConjSqrtR_sq
-- expected: standard only — ★ B·B=2−R for B=J R^{½}J: B(Bξ)=(2−R)ξ. Inner J²=1 collapses
-- J R^{½}(JJ)R^{½}J = J R^{½}R^{½}J = JRJ = 2−R (rvdSqrtR_mul_self + modConj_rvdRC_modConj). The b·b=a input
-- to CFC.sqrt_unique: with B bundled ℂ-linear + positive ⇒ J R^{½}J=(2−R)^{½} WITHOUT general antilinear CFC.
#print axioms QIQTH.StandardSubspaceModular.projIK_sub_projIK_self
-- expected: standard only — (i𝒦)^⊥ SUPPLY: projIK(ξ−Qξ)=0 (Q idempotent). Every ker(projIK)=(i𝒦)^⊥ element
-- is of this form, so the totality of (i𝒦)^⊥ against 𝒦 (eq_of_mem_K_of_inner_perp_IK) is fully populated.
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdPmQ
-- expected: standard only — J·D=T (dual of J·T=D): modConj(rvdPmQ ξ)=rvdT ξ. Apply J to J(Tξ)=Dξ + J²=1.
-- The bounded Tomita polar relation D=JT, T=JD, J²=1.
#print axioms QIQTH.StandardSubspaceModular.modConj_inner_conj
-- expected: standard only — ★ J IS ANTIUNITARY: ⟨Jη,Jζ⟩=conj⟨η,ζ⟩. Re part = modConj_inner_map (J real
-- isometry); Im part flips by antilinearity (modConj_smul_I): Im⟨Jη,Jζ⟩=⟨i·Jη,Jζ⟩_ℝ=−⟨J(i·η),Jζ⟩_ℝ=
-- −⟨i·η,ζ⟩_ℝ=−Im⟨η,ζ⟩. The full Tomita reality of J, engine behind J𝒦=(i𝒦)^⊥ (RvD Prop 2.2(5)).
#print axioms QIQTH.StandardSubspaceModular.modConj_smul_I
-- expected: standard only — ★ J IS ANTILINEAR: modConj(i·η)=−i·(modConj η). On the dense range of T (ℂ-linear):
-- J(i·T x)=J(T(i·x))=D(i·x)=(P−Q)(i·x)=i·(Q−P)x=−i·Dx=−i·J(Tx) (projK_smul_I/projIK_smul_I), continuity extends.
-- The antilinearity RvD use to place J𝒦 ⊆ (i𝒦)^⊥ (Prop 2.2(5)) — the source of the w⊥i𝒦 vectors of Thm 3.8.
#print axioms QIQTH.StandardSubspaceModular.eq_of_mem_K_of_inner_perp_IK
-- expected: standard only — ★★ TOTALITY/⊥-TO-EQUALITY (RvD Thm 3.8 closeout): a,b∈𝒦 with ⟨w,a⟩=⟨w,b⟩ ∀w⊥i𝒦
-- (projIK w=0) ⇒ a=b. d=a−b∈𝒦 ⊥ all (i𝒦)^⊥: w=d−Qd gives ‖d−Qd‖²=Re⟨w,d⟩=0 ⇒ d=Qd∈i𝒦; d∈𝒦⊓i𝒦=⊥
-- (IsSeparating). With orbit_inner_eq_of_entire for V and Δ^{it} (both ⟨w,·_t η⟩=⟨w,η⟩) ⇒ V_t η=Δ^{it}η on 𝒦.
#print axioms QIQTH.StandardSubspaceModular.corrC_real_on_axis
-- expected: standard only — ★ g REAL ON THE REAL AXIS (RvD Thm 3.8 step 4): with w⊥i𝒦 (projIK w=0) and the
-- orbit V_t(gaussSmear) staying in 𝒦, corrC w V n η ↑t = ⟨w,V_t(smear)⟩ is real ∀t (conj of the 𝒦–(i𝒦)^⊥
-- pairing, inner_real_of_mem_K_perp_IK). The real-axis-edge input to "real on both edges ⟹ constant".
#print axioms QIQTH.StandardSubspaceModular.inner_real_of_mem_K_perp_IK
-- expected: standard only — ★ RvD PROP 2.3 REALITY: x∈𝒦 (projK x=x) ∧ y⊥i𝒦 (projIK y=0) ⇒ ⟨x,y⟩_ℂ real
-- (Im⟨x,y⟩=⟨i·x,y⟩_ℝ, i·x∈i𝒦 ⊥ y). The reality making g(t)=⟨U_t η, J(2−R)^½R^{−½}ζ⟩ real on the strip
-- edges in RvD Thm 3.8 step 4 — input to "real on both edges ⟹ constant".
#print axioms QIQTH.StandardSubspaceModular.gaussSmearC_smul_left
-- expected: standard only — ★ GROUP FACTORIZATION V_t(gaussSmearC V n η z) = gaussSmearC V n η (z+t)
-- (RvD Thm 3.8's h(z+t)=U_t h(z) step). Pull V_t through the Bochner integral (← integral_comp_comm) +
-- group law V_t V_u = V_{t+u} + translation u↦u+t (integral_add_right_eq_self). Direct integral proof,
-- no identity theorem. The entire-function factorization driving the KMS boundary computation.
#print axioms QIQTH.StandardSubspaceModular.gaussSmearC_norm_le
-- expected: standard only — ★ GAUSSIAN BOUND ‖gaussSmearC V n η z‖ ≤ e^{n(Im z)²}·‖η‖·√(π/n): the complex
-- Gaussian modulus e^{−n(u−Re z)²+n(Im z)²} integrates (translation-invariant ∫e^{−n(u−Re z)²}=√(π/n)). On
-- the closed strip 0≤Im z≤1 this is the UNIFORM bound e^{n}·‖η‖·√(π/n).
#print axioms QIQTH.StandardSubspaceModular.corrC_norm_le
-- expected: standard only — ★ GAUSSIAN BOUND on the correlation |corrC ξ V n η z| ≤ ‖ξ‖·e^{n(Im z)²}·‖η‖·√(π/n)
-- (Cauchy–Schwarz over gaussSmearC_norm_le). On 0≤Im z≤1 uniformly bounded — the `bound` hypothesis of
-- StripUniqueness.eqOn_of_bdd_holomorphic_strip. corrC is now entire (differentiable_corrC) AND strip-bounded.
-- KMS CORRELATION ON THE STRIP (KMSCorrelation.lean): furnishing the strip-uniqueness hypotheses for corrC.
#print axioms QIQTH.StandardSubspaceModular.diffContOnCl_corrC
-- expected: standard only — corrC ξ V n η is DiffContOnCl on the open KMS strip (entire ⇒ diffContOnCl).
-- The first analytic hypothesis of kms_correlation_boundary_determined, now concrete for corrC.
#print axioms QIQTH.StandardSubspaceModular.corrC_bdd_strip
-- expected: standard only — uniform bound ‖corrC ξ V n η z‖ ≤ ‖ξ‖·e^n·‖η‖·√(π/n) on the OPEN strip
-- (corrC_norm_le + (Im z)²<1). The second analytic hypothesis of kms_correlation_boundary_determined.
#print axioms QIQTH.StandardSubspaceModular.corrC_eqOn_strip_of_boundary_eq
-- expected: standard only — ★★ STRIP-UNIQUENESS COMPARISON, the structural core of the hUniq discharge:
-- two contraction flows V,V' whose correlations corrC agree on the real axis AND the KMS top edge t+i have
-- EQUAL correlations on the whole closed KMS strip (kms_correlation_boundary_determined applied to the now-
-- furnished diffContOnCl_corrC + corrC_bdd_strip). With entireVec_tendsto density ⇒ V_t = V'_t.
#print axioms QIQTH.StandardSubspaceModular.gaussSmearC_zero
-- expected: standard only — h(0) = gaussSmear: the complex orbit at z=0 is the smeared vector η_n (complex
-- Gaussian e^{−n(u−0)²} collapses to real e^{−n u²}). Evaluation point g(0)=⟨w,η_n⟩ in RvD Thm 3.8.
#print axioms QIQTH.StandardSubspaceModular.corrC_eq_at_real_of_const
-- expected: standard only — ★ STEP 6b: g=corrC w constant on the strip ⇒ ⟨w,V_t(gaussSmear)⟩=⟨w,gaussSmear⟩
-- ∀t (evaluate g at t vs 0, gaussSmearC_zero). Same for Δ^{it} ⇒ ⟨w,V_t smear⟩=⟨w,Δ^{it} smear⟩; totality
-- of w + density ⇒ V_t=Δ^{it}. The constancy→operator-equality closeout of the KMS-uniqueness proof.
#print axioms QIQTH.StandardSubspaceModular.corrC_const_on_strip_of_edges
-- expected: standard only — ★ STEP 6a (to closed strip): Im(corrC w)=0 on BOTH edges (Im=0,Im=1) ⇒ corrC w
-- constant on the CLOSED kmsStrip. eqConst_of_im_zero_strip (Phragmén–Lindelöf) gives const on the open strip;
-- continuity of entire g propagates to closure (kmsStrip=closure kmsStripOpen, Set.EqOn.closure).
#print axioms QIQTH.StandardSubspaceModular.gConstancy_xi_of_density
-- expected: standard only — ★★ GConstancy ∀ξ∈𝒦 from √R-vector GConstancy + √R-density: hsqrt (GConstancy at √Rζ∈𝒦,
-- from gConstancy_eta_of_bottom) + hdense (√R-range dense in 𝒦: ∀ξ∈𝒦 ∃√Rζ_k∈𝒦→ξ) ⇒ GConstancy(η,ξ) ∀ξ∈𝒦 via
-- gConstancy_of_tendsto_xi. The ∀ξ∈𝒦 premise of comparisonDatum_of_gConstancy — ξ-reconciliation modulo √R-density.
#print axioms QIQTH.StandardSubspaceModular.gConstancy_of_tendsto_xi
-- expected: standard only — GConstancy CLOSED in ξ: GConstancy(η,ξ_k) for ξ_k→ξ ⇒ GConstancy(η,ξ). Both sides
-- ⟪V_t η,Δ^{it}(J·)⟫,⟪η,J·⟫ continuous in ξ (modConj+modUnitary+inner) ⇒ tendsto_nhds_unique. Lifts GConstancy from
-- ξ=√Rζ to closure(√R-range); √R dense range (R injective via rvdRC_mul_rvdTwoSubRC_injective) = the ξ=√Rζ reconciliation.
#print axioms QIQTH.StandardSubspaceModular.gConstancy_real_smul
-- expected: standard only — GConstancy real-scalar linear in vector: GConstancy(v) ⇒ GConstancy(c•v), c:ℝ (V_t ℂ-linear
-- + inner_smul_left, conj c=c). Bridges gaussSmear→entireVec=√(n/π)•gaussSmear.
#print axioms QIQTH.StandardSubspaceModular.gConstancy_eta_of_bottom
-- expected: standard only — ★★★ GCONSTANCY(η∈𝒦) REDUCED TO BOTTOM-EDGE KMS (full density+scaling closeout): ⟪V_t η,
-- Δ^{it}(Jξ)⟫=⟪η,Jξ⟫ (ξ=√Rζ) given geometric inputs + h1 (bottom-edge ∀ entire vec). Chains gConstancy_entire_of_bottom
-- → gConstancy_real_smul (scale to entireVec) → gConstancy_of_entireVec_limit (n→∞). FULL GConstancy(η) now rests ONLY
-- on the bottom-edge mid-line KMS reality — the single labelled RvD Thm 3.8 input. Remaining: h1(KMS) + ξ=√Rζ range.
#print axioms QIQTH.StandardSubspaceModular.gConstancy_of_entireVec_limit
-- expected: standard only — GCONSTANCY DENSITY: GConstancy(η) from GConstancy(entireVec V n η) ∀n>0. entireVec→η
-- (entireVec_tendsto) + ⟪V_t·,w⟫,⟪·,w⟫ continuous ⇒ constant equality passes to limit (tendsto_nhds_unique). Lifts the
-- entire-vector GConstancy to genuine η∈𝒦.
#print axioms QIQTH.StandardSubspaceModular.gConstancy_entire_of_bottom
-- expected: standard only — ★★★ GCONSTANCY(η_n) REDUCED TO BOTTOM-EDGE KMS: ⟪V_t η_n,Δ^{it}Jξ⟫=⟪η_n,Jξ⟫ given ONLY
-- the geometric inputs (ξ=√Rζ∈𝒦, orbit∈𝒦) + h1 (mid-line Im=-1/2 reality = the KMS input HalfStripReal). Top edge
-- auto (gFunction_top_edge_real_all). The ENTIRE analytic g-function argument now collapses to the single bottom-edge
-- KMS hypothesis — everything else machine-checked. Remaining to full hUniq: bottom-edge reality + density η_n→η + ξ range.
#print axioms QIQTH.StandardSubspaceModular.gFunction_top_edge_real_all
-- expected: standard only — TOP-EDGE reality ∀z form (h0 input): Im g(z)=0 on Im z=0 edge, for ξ=√Rζ∈𝒦 + orbit∈𝒦.
-- z with Im z=0 is real (z=↑z.re), so = gFunction_top_edge_real at z.re. Geometric, always-available top edge.
#print axioms QIQTH.StandardSubspaceModular.gConstancy_entire
-- expected: standard only — ★★★ GCONSTANCY for entire vectors (RvD Thm 3.8 output assembled): ⟪V_t η_n, Δ^{it}(Jξ)⟫=
-- ⟪η_n, Jξ⟫ (ξ=√R ζ, η_n=gaussSmear) from gFunction_eq_zero_const (g(t)=g(0)) + gFunction_real_eq (top) + gFunction_
-- zero (origin) + conj (inner_conj_symm). = GConstancy S V at (η_n, √R ζ), modulo the 2 edge-reality inputs h0,h1.
#print axioms QIQTH.StandardSubspaceModular.gFunction_eq_zero_const
-- expected: standard only — ★★★ DEVICE g-FUNCTION CONSTANCY (RvD Thm 3.8 analytic heart): g(z)=⟪J·d_z(R)ζ,V_z η⟫
-- real on BOTH half-strip edges (Im=0 & Im=-1/2) ⇒ g(t)=g(0) ∀t. diffContOnCl_gFunction + uniform bound
-- (gFunction_norm_le+gaussSmearC_norm_le, (Im z)²≤1/4) + eqConst_of_im_zero_halfStrip (2-edge Phragmén-Lindelöf)
-- ⇒ const on open half-strip; Set.EqOn.of_subset_closure (ContinuousOn closure) propagates to real axis. Top edge
-- geometric (gFunction_top_edge_real); BOTTOM edge Im=-1/2 = KMS input (HalfStripReal). ⇒ GConstancy(η_n).
#print axioms QIQTH.StandardSubspaceModular.corrC_orbit_eq_of_edges_real
-- expected: standard only — ★★ FULL STEP-6 CLOSEOUT CHAIN: g=corrC w real on both strip edges ⇒
-- ⟨w,V_t(gaussSmear)⟩=⟨w,gaussSmear⟩ ∀t (corrC_eq_at_real_of_const ∘ corrC_const_on_strip_of_edges). Edge
-- inputs: corrC_real_on_axis (Im=0, step 4) + KMS-flip top edge (Im=1, step 5/StripKMSrvd). Applied to V and
-- Δ^{it} ⇒ ⟨w,V_t smear⟩=⟨w,Δ^{it} smear⟩; totality of w + density ⇒ V=Δ. Only step 5 remains.
#print axioms QIQTH.StandardSubspaceModular.operator_ext_inner_dense
-- expected: standard only — ★ STEP 6e WIRING: continuous A,B with ⟨w,A x⟩=⟨w,B x⟩ for w in dense Dw + x in
-- dense Dx ⇒ A=B (ext_inner_left over dense Dw, then Continuous.ext_on over dense Dx). The final operator-
-- equality step: Dw=total {J(2−R)^½R^{−½}ζ}, Dx=dense entire vectors, equality=corrC_orbit_eq_of_edges_real.
#print axioms QIQTH.StandardSubspaceModular.corrC_bdd_closed_strip
-- expected: standard only — corrC closed-strip bound ‖corrC ξ z‖ ≤ ‖ξ‖·e^n·‖η‖·√(π/n) on kmsStrip (Im z∈[0,1]
-- ⇒ (Im z)²≤1). The bound hypothesis of eqOn_of_im_zero_edge.
#print axioms QIQTH.StandardSubspaceModular.corrC_bdd_halfStrip
-- expected: standard only — CORRECT-STRIP bound: ‖corrC ξ z‖ ≤ ‖ξ‖·e^{n/4}·‖η‖·√(π/n) on kmsHalfStrip
-- ({−1/2≤Im≤0}, (Im z)²≤1/4). The bounded-holomorphic input the correct half-strip g-function argument needs
-- (with diffContOnCl_corrC + eqOn_of_im_zero_edge_halfStrip). NOT part of the flawed full-strip chain above.
#print axioms QIQTH.StandardSubspaceModular.corrC_top_edge_real_of_kms_match
-- expected: standard only — ★★ STEP-5 REALITY TRANSFER: a KMS function f (from StripKMSrvd) bounded-holo on
-- the strip, agreeing with the orbit correlation g=corrC w on the REAL AXIS and with REAL top edge
-- (Im f(t+i)=0) ⇒ g's top edge is real (Im g(t+i)=0). Via eqOn_of_im_zero_edge (Hadamard one-edge): f=g on
-- the strip ⇒ g(t+i)=f(t+i) real. The last analytic input (h1) of corrC_orbit_eq_of_edges_real, from the KMS.
#print axioms QIQTH.StandardSubspaceModular.corrC_orbit_eq_of_kms_function
-- expected: standard only — ★★★ ANALYTIC CAPSTONE of RvD Thm 3.8: given the labelled KMS function f (the
-- StripKMSrvd output: bdd-holo, =g on real axis, real top edge) + geometric facts (w⊥i𝒦, orbit in 𝒦),
-- ⟨w,V_t(gaussSmear)⟩=⟨w,gaussSmear⟩ ∀t. Chains corrC_real_on_axis (bottom) + corrC_top_edge_real_of_kms_match
-- (top, Hadamard) ⟹ corrC_orbit_eq_of_edges_real. The ENTIRE analytic chain is now one axiom-free theorem;
-- only producing f from StripKMSrvd at the RvD vectors (the labelled physics input) remains for V=Δ.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_eq_of_orbit_inner
-- expected: standard only — ★★★ TOP-LEVEL RvD Thm 3.8 ASSEMBLY (hUniq discharge modulo orbit identities):
-- V and Δ^{it}=modUnitary both preserve 𝒦 AND both satisfy ⟨w,·_t η⟩=⟨w,η⟩ ∀η∈𝒦,∀w⊥i𝒦 ⇒ Δ^{it}=V_t.
-- ⟨w,Δ^{it}η⟩=⟨w,η⟩=⟨w,V_t η⟩ + both∈𝒦 ⇒ (eq_of_mem_K_of_inner_perp_IK, IsSeparating) Δ^{it}η=V_t η on 𝒦 ⇒
-- (clm_eq_of_eqOn_K, IsCyclic) Δ^{it}=V_t. Orbit identities = output of the KMS chain; 𝒦-inv = hUniq hyp.
-- ⚠ FRAMEWORK CAVEAT (2026-06-21, honest correction): these corrC FULL-strip "orbit-identity" lemmas
-- (corrC_orbit_eq_of_kms_function, corrC_orbit_eq_of_edges_real, corrC_eq_at_real_of_const,
-- modUnitary_eq_of_orbit_inner, orbit_inner_eq_of_entire) MIS-MODEL RvD Thm 3.8. They are individually-correct
-- CONDITIONAL theorems, but their top-edge hypothesis (corrC_top_edge_real_of_kms_match's "real top edge on
-- Im=1") is UNSATISFIABLE for nontrivial V: the chain's conclusion ⟨w,V_t smear⟩=⟨w,smear⟩ ∀w⊥i𝒦 forces
-- V_t=id (⊥(i𝒦)^⊥ ⇒ ∈i𝒦; ∈𝒦; 𝒦∩i𝒦=0), FALSE for Δ^{it}. RvD instead uses the HALF-strip {−1/2≤Im≤0} +
-- half-shift Δ^{1/2}=J (g(t−i/2)=⟨h,Jξ⟩, (2−R)^{½}ζ=Jξ) + KMS-matching that brings Δ in. So the hUniq
-- discharge does NOT go through via this chain; a faithful redo needs the half-strip + J-twisted w + R^{−½}
-- device. The J-algebra (J𝒦=(i𝒦)^⊥ etc.), entire vectors, Hadamard one-edge, StripUniqueness are UNAFFECTED.
#print axioms QIQTH.StandardSubspaceModular.modUnitary_eq_of_orbit_compare
-- expected: standard only — ★★★ CORRECTED TOP-LEVEL RvD Thm 3.8 ASSEMBLY (supersedes the vacuous
-- modUnitary_eq_of_orbit_inner above). Takes the FAITHFUL orbit datum: the U-vs-Δ comparison
-- ⟨w,V_t η⟩=⟨w,Δ^{it}η⟩ ∀η∈𝒦,∀w⊥i𝒦 (what RvD's g-fn constancy + KMS-matching against ⟨h,Δ^{it}ξ⟩ produce;
-- Δ genuinely enters since KMS is applied to the pair (η,Δ^{it}ξ) — it does NOT factor through ⟨w,η⟩, so this
-- premise is SATISFIABLE/non-vacuous, unlike orbit_inner's). Given it + both flows preserving 𝒦:
-- eq_of_mem_K_of_inner_perp_IK (IsSeparating) ⇒ V_t η=Δ^{it}η on 𝒦 ⇒ clm_eq_of_eqOn_K (IsCyclic) ⇒ Δ^{it}=V_t.
-- Remaining gap = producing the comparison datum from StripKMSrvd via the half-strip g-fn (RvD R^{−½} ζ-device,
-- Prop 3.7, garbled in the scan — NOT fabricated). This is the correct top-level structure of the discharge.
#print axioms QIQTH.StandardSubspaceModular.corrJ_real_on_axis
-- expected: standard only — ★★ FAITHFUL RvD g-function TOP EDGE (RvD Thm 3.8, p.198, clean PDF). The real
-- RvD half-strip function g(z)=⟨Jξ,h(z)⟩ uses the BOUNDED vector Jξ=modConj S ξ (ξ∈𝒦); RvD's written
-- (2−R)^{½}R^{−½}ξ EQUALS Jξ by their own sqrt-identity, so the unbounded R^{−½} is AVOIDED entirely. Top
-- edge real: Jξ⊥i𝒦 (projIK(Jξ)=0, projIK_modConj_eq_zero_of_mem_K) + V_t(smear)∈𝒦 ⇒ inner_real_of_mem_K_perp_IK.
-- The J-twisted faithful replacement for the discredited full-strip corrC_real_on_axis@generic-w. Resolves the
-- paradox: J𝒦=(i𝒦)^{⊥ℝ} is REAL-orthogonal, so ⟨v,Jξ⟩=0∀ξ does NOT give v∈i𝒦; consistent conclusion is the
-- U-vs-Δ comparison (modUnitary_eq_of_orbit_compare), shared constant ⟨η,Jξ⟩ cancelling between U and Δ sides.
#print axioms QIQTH.StandardSubspaceModular.clm_eq_of_inner_self_eq
-- expected: standard only — ★★ POLARIZATION BRIDGE (non-vacuous discharge closeout): over ℂ, ⟨Aξ,ξ⟩=⟨Bξ,ξ⟩ ∀ξ
-- ⇒ A=B. Apply inner_map_self_eq_zero to A−B (⟨(A−B)ξ,ξ⟩=0 ∀ξ ⇒ (A−B).toLinearMap=0). Converts the SCALAR
-- diagonal-correlation equality that strip-uniqueness (modCorrExt vs a KMS competitor) delivers into the
-- OPERATOR identity Δ^{it}=V_t. The correct, non-vacuous closeout (vs the discredited corrC(Jξ) constancy route).
#print axioms QIQTH.StandardSubspaceModular.modUnitary_eq_of_diag_corr
-- expected: standard only — ★ DIAGONAL-CORRELATION RvD Thm 3.8 CLOSEOUT: ⟨ξ,V ξ⟩=⟨ξ,Δ^{it}ξ⟩ ∀ξ ⇒ V=Δ^{it}
-- (modCorrExt convention, ξ first slot; conjugate both sides + clm_eq_of_inner_self_eq). The operator-level
-- target of modCorrExt_eq_of_boundary: once a KMS competitor's correlation is pinned to the Δ-side modCorrExt
-- on the strip (hence on the real axis ⟨ξ,V_tξ⟩=⟨ξ,Δ^{it}ξ⟩), this gives V_t=Δ^{it}.
#print axioms QIQTH.StandardSubspaceModular.corrW_bottom_edge_real_of_kms
-- expected: standard only — ★★ GENERAL bottom-edge reality transfer (RvD Thm 3.8, the genuine "apply KMS for
-- {U_t} to the pair (η,w)" step), ARBITRARY fixed 2nd-slot w. f bdd-holo on half-strip, =corrC(w) on real axis,
-- real lower edge ⇒ (eqOn_of_im_zero_edge_halfStrip) g(t−i/2) real. SATISFIABILITY DEPENDS ON w: for w=Δ^{it}ξ
-- (=modUnitary S t ξ, valid 𝒦-pair since Δ^{it}𝒦=𝒦) the KMS condition genuinely supplies f and the lower edge
-- IS real (V=Δ: ⟨Δ^{it}Jη,Δ^{it}ξ⟩=⟨Jη,ξ⟩, real). RvD's NON-CIRCULAR step — brings Δ in via a legit 𝒦-pair, not
-- by assuming ⟨ξ,U_tξ⟩=⟨ξ,Δ^{it}ξ⟩. For w=Jξ (corrJ instance) the premise is VACUOUS instead (see that lemma).
#print axioms QIQTH.StandardSubspaceModular.inner_mem_K_modConj_real
-- expected: standard only — ★ NON-VACUITY WITNESS: ξ,η∈𝒦 ⇒ ⟨ξ,Jη⟩ real (Jη∈(i𝒦)^⊥ + inner_real_of_mem_K_perp_IK).
-- The lower-edge value making the Δ-rotated-pair instance (w=Δ^{it}ξ) of corrW_bottom_edge_real_of_kms satisfiable.
#print axioms QIQTH.StandardSubspaceModular.corrJ_bottom_edge_real_of_kms
-- expected: standard only — ⚠⚠ VACUOUS PREMISE (honest correction 2026-06-21, total honesty). True conditional,
-- but its hypothesis (a bdd-holo f matching g=corrC(Jξ) on the real axis AND real on the bottom edge Im=−1/2)
-- is UNSATISFIABLE for the relevant flows, so it does NOT advance the hUniq discharge. RIGOROUS reason: g=⟨h(z),Jξ⟩
-- has a FIXED 2nd slot (needed for holomorphy). For V=Δ its TOP edge ⟨Δ^{it}η,Jξ⟩ is real (Δ^{it}η∈𝒦, Jξ∈(i𝒦)^⊥,
-- machine-checked reality). If the bottom edge were ALSO real then bdd+holo+real-both-edges ⟹ CONSTANT (Schwarz
-- reflection/Liouville) ⟹ ⟨Δ^{it}η,Jξ⟩=⟨η,Jξ⟩ ∀ξ∈𝒦; but Jξ EXHAUSTS {projIK=0} (projK_modConj_eq_self_of_perp_IK),
-- so the machine-checked eq_of_mem_K_of_inner_perp_IK forces Δ^{it}η=η ⇒ Δ=id, ABSURD. Hence g's bottom edge is
-- NOT real ⇒ no matching f exists ⇒ premise vacuous (same failure class as the full-strip corrC_top_edge flaw).
-- The GENUINE RvD g is NOT ⟨h(z),Jξ⟩: it is the Prop 3.7 device ⟨(2−R)^{iz}R^{−iz+1/2}[·],η⟩ with the VARYING
-- vector in the FIRST slot (BOUNDED on the half-strip by Lemma 3.6 — no unbounded R^{−1/2}), pairing the orbit
-- against η through the modular continuation. That is the correct target. corrJ_real_on_axis (TOP edge) is
-- UNAFFECTED — ⟨U_tη,Jξ⟩ real is genuinely true and remains valid.
#print axioms QIQTH.StandardSubspaceModular.orbit_inner_eq_of_entire
-- expected: standard only — ★★ DENSITY EXTENSION: ⟨w,V_t(gaussSmear V n η)⟩=⟨w,gaussSmear V n η⟩ ∀n>0 ⇒
-- ⟨w,V_t η⟩=⟨w,η⟩. Scale by √(n/π) to entireVec, entireVec_tendsto (→η) + continuity of V_t,⟨w,·⟩. Resolves
-- the V-vs-Δ smearing mismatch: both flows give ⟨w,·_t η⟩=⟨w,η⟩ on the SAME η ⇒ V_t η−Δ^{it}η ⊥ total{w}⊆(i𝒦)^⊥
-- ⇒ ∈i𝒦; both in 𝒦 + 𝒦∩i𝒦={0} ⇒ V_t η=Δ^{it}η. The comparison closes correctly.
#print axioms QIQTH.StandardSubspaceModular.modCorrExt_eq_of_boundary
-- expected: standard only — ★ Δ-SIDE comparison target: in the regular regime σ(R)⊆[a,2−a] the modular
-- correlation modCorrExt S ξ (=⟨ξ,Δ^{it}ξ⟩ continued) is bounded-holomorphic (diffContOnCl_modCorrExt +
-- modCorrExt_norm_le), so any competitor F bounded-holomorphic on the strip sharing its real-axis AND KMS
-- top-edge values coincides with it on the closed strip (kms_correlation_boundary_determined). The Δ-side
-- dual of corrC_eqOn_strip_of_boundary_eq — both correlation sides now pinned by their boundary data.
-- expected: standard only — gaussSmear V n η = ∫ e^{−n t²}•V_t η dt. gaussSmear_integrable: Bochner-integrable
-- (dominated by the Gaussian e^{−n t²}·‖η‖ via integrable_exp_neg_mul_sq, V_t norm-non-increasing + orbit
-- continuous). gaussSmear_mem_K: ★ the smeared vector lands in the real subspace K — the ℝ-linear projection
-- projK commutes with the Bochner integral (ContinuousLinearMap.integral_comp_comm) and fixes V_t η∈K. First
-- brick of RvD's dense-entire-vectors construction toward discharging hUniq (the operator/integral half).
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_modCharC
#print axioms QIQTH.StandardSubspaceModular.measurable_modCharC
#print axioms QIQTH.StandardSubspaceModular.abs_log_div_le
-- expected: standard only — the pointwise COMPLEX z-derivative d/dz u_z(r) = i·log((2−r)/r)·u_z(r) (via
-- HasDerivAt.cexp on exp(i·z·L)). measurable_modCharC: u_z Borel-measurable in r. abs_log_div_le: the modular
-- frequency |log((2−r)/r)|≤log((2−a)/a) on the regular window [a,2−a]. These dominate the integrand-derivative.
#print axioms QIQTH.hasDerivAt_modCorrExt
-- expected: standard only — ★★ HOLOMORPHY of the strip extension: in the regular regime σ(R)⊆[a,2−a] (0<a≤1),
-- at each interior z₀ (Im z₀∈(0,1)) F_ξ(z)=∫u_z dμ is ℂ-differentiable with derivative ∫i·log((2−ω)/ω)·u_{z₀} dμ
-- — differentiation under the spectral integral (hasDerivAt_integral_of_dominated_loc_of_deriv_le, 𝕜=ℂ; the
-- z-derivative bounded on the whole strip by log((2−a)/a)·(2−a)/a via abs_log_div_le + modCharC_norm_le). With
-- modCorrExt_ofReal/_kms_flip (the two edges) this is the bounded-holomorphic strip extension strip-uniqueness
-- consumes. Remaining for hUniq: continuity-to-closure (DiffContOnCl) + the Borchers group-equality reduction.
#print axioms QIQTH.differentiableOn_modCorrExt
#print axioms QIQTH.diffContOnCl_modCorrExt
-- expected: standard only — differentiableOn_modCorrExt: F_ξ differentiable on the OPEN strip (from
-- hasDerivAt_modCorrExt). diffContOnCl_modCorrExt: ★★ the FULL DiffContOnCl — differentiable on the open strip
-- AND continuous up to the closed strip {0≤Im≤1} (continuity via continuousOn_of_dominated: integrand
-- continuous in z, bounded by (2−a)/a on the closure; closure(im⁻¹'Ioo)=im⁻¹'Icc via Complex.closure_preimage_im).
-- This is the EXACT regularity QIQTH.StripUniqueness.eqOn_of_bdd_holomorphic_strip consumes — the bounded-
-- holomorphic strip extension of the modular correlation, fully assembled. Remaining for hUniq: the Borchers
-- group-equality reduction (V=Δ^{it} from boundary-value uniqueness) — the conceptual step, not yet started.
#print axioms QIQTH.modCorrExt_norm_le
-- expected: standard only — the uniform ‖·‖-bound ‖F_ξ(z)‖≤((2−a)/a)·‖ξ‖² on the closed strip (integrate
-- modCharC_norm_le against the finite spectral measure, μ^R_ξ(univ)=‖ξ‖²). The boundedness hypothesis that,
-- with diffContOnCl_modCorrExt, completes the input to strip-uniqueness. Analytic substrate for hUniq COMPLETE.
#print axioms QIQTH.StandardSubspaceModular.modCharC_norm
#print axioms QIQTH.StandardSubspaceModular.modCharC_norm_le
-- expected: standard only — modCharC_norm: EXACT modulus ‖u_z(r)‖=exp(−Im(z)·log((2−r)/r)) on (0,2) (=1 on the
-- real axis). modCharC_norm_le: in the REGULAR regime r∈[a,2−a] (0<a≤1) and z in the strip (0≤Im z≤1),
-- ‖u_z(r)‖≤(2−a)/a — the uniform BOUND that makes z↦∫u_z dμ^R_ξ a BOUNDED holomorphic strip extension of
-- ⟪ξ,Δ^{it}ξ⟫ (the hypothesis strip-uniqueness consumes). Boundedness seed for the spectral-integral lift.
#print axioms QIQTH.StandardSubspaceModular.rvdRC_spectrum_mem_Icc
-- expected: standard only — ★★ TIGHT spectrum location σ(R)⊆[0,2] (vs the loose norm-margin spectrum_subset_covΩ).
-- Lower 0≤ω: rvdRC_nonneg + StarOrderedRing.nonneg_iff_spectrum_nonneg. Upper ω≤2: 2−ω∈{2}−σ(R)=σ(2·1−R)
-- (spectrum.singleton_sub_eq) + rvdTwoSubRC_nonneg ⇒ 0≤2−ω. The spectral location the borelFC device-vector
-- construction (2−R)^{iz}R^{−iz+1/2}ζ=d_z(R)ζ consumes, paired with devChar_norm_le_Icc (d_z bounded on [0,2]).
#print axioms QIQTH.StandardSubspaceModular.devChar_norm_le
-- expected: standard only — ★★★ RvD Prop 3.7 DEVICE CHARACTER bound, NO regular window. d_z(r)=u_z(r)·√r =
-- ((2−r)/r)^{iz}·√r (=modCharC z r·√r). On the HALF strip {−1/2≤Im z≤0}: ‖d_z(r)‖≤√2 UNIFORMLY over ALL
-- r∈(0,2) — the √r factor (the +1/2 in R^{−iz+1/2}) EXACTLY cancels the r^{−iz} blow-up at r→0,2. Log form:
-- b·log(2−r)+(1/2−b)·log r ≤ (1/2)log2 (b=−Im z∈[0,1/2]; coeffs nonneg, sum 1/2; log(2−r),log r≤log2). This is
-- the scalar core of the genuine U-side continuation (2−R)^{iz}R^{−iz+1/2}ζ=d_z(R)ζ, bounded-holomorphic on
-- the half-strip for ANY standard subspace (unlike modCorrExt which needs σ(R)⊆[a,2−a]). devChar/measurable_devChar/
-- devChar_ofReal/differentiable_devChar: the device char is entire in z, Borel in r, =modChar t·√r on the axis.
#print axioms QIQTH.StandardSubspaceModular.devChar_norm_eq
-- expected: standard only — ‖d_z(r)‖=(2−r)^{−Im z}·r^{1/2+Im z} on (0,2) (rpow form, from modCharC_norm +
-- exp(c·log x)=x^c + div_rpow + rpow_sub). Exposes the two nonneg-exponent rpow factors for the domination.
#print axioms QIQTH.StandardSubspaceModular.devChar_deriv_norm_le
-- expected: standard only — ★★★ ASSEMBLED DEVICE-DERIVATIVE DOMINATION (no regular window): for −Im z=b∈[β₀,β₁]
-- ⊂(0,1/2), r∈(0,2), |log((2−r)/r)|·‖d_z(r)‖ ≤ √2·(2/β₀+log2)+√2·(2/(1/2−β₁)+log2) — a CONSTANT (r-uniform, slab-
-- uniform). devChar_norm_eq gives ‖d_z‖=(2−r)^b·r^{1/2−b}; split |log((2−r)/r)|≤|log(2−r)|+|log r|; rpow_mul_abs_
-- log_le on (2−r)^b·|log(2−r)| and r^{1/2−b}·|log r|, complementary rpow factors ≤√2. The integrable const dominator
-- hasDerivAt_integral_of_dominated_loc_of_deriv_le consumes for holomorphy of devCorrExt on the OPEN half-strip.
#print axioms QIQTH.StandardSubspaceModular.rpow_mul_abs_log_le
-- expected: standard only — ★★ POLYNOMIAL-BEATS-LOG bound (heart of the device-derivative domination): for
-- x∈(0,2], δ∈(0,1], x^δ·|log x| ≤ 2/δ + log2. (0,1]: log x⁻¹≤(x⁻¹)^{δ/2}/(δ/2) (Real.log_le_rpow_div) ⇒
-- x^δ·|log x|≤2·x^{δ/2}/δ≤2/δ. [1,2]: log x≤log2, x^δ≤2. Tames the log((2−r)/r) factor of the device z-derivative
-- against the r^{1/2±·} of ‖d_z‖ ⇒ the integrable CONSTANT dominator for holomorphy of devCorrExt.
#print axioms QIQTH.StandardSubspaceModular.devChar_zero
#print axioms QIQTH.StandardSubspaceModular.devChar_neg_half_I
-- expected: standard only — DEVICE interpolation endpoints (RvD Thm 3.8 g-function boundary values): d_0(r)=√r
-- (⇒ deviceOpC 0 = R^{1/2}=√R, so g(0)=⟨η,Jξ⟩) and d_{−i/2}(r)=√(2−r) on (0,2) (⇒ deviceOpC(−i/2)=(2−R)^{1/2},
-- the half-shift Δ^{1/2}=J on 𝒦). The device interpolates √R ↔ (2−R)^{1/2} across the half-strip — RvD Prop 3.7.
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_devChar_Icc
-- expected: standard only — ★ device z-derivative on CLOSED [0,2] (covers the spectrum endpoints σ(R)⊆[0,2]).
-- (0,2): hasDerivAt_devChar. r∈{0,2}: modCharC=1 ⇒ d_z(r)=√r z-constant (deriv 0), and the formula coefficient
-- vanishes since (2−r)/r=0 (2/0=0 at r=0, 0/2=0 at r=2) ⇒ log 0=0. The HasDerivAt form the differentiate-under-
-- the-spectral-integral holomorphy of devCorrExt needs (μ may give mass to the endpoints).
#print axioms QIQTH.StandardSubspaceModular.hasDerivAt_devChar
-- expected: standard only — ★ POINTWISE z-derivative of the device character: d/dz d_z(r)=i·log((2−r)/r)·d_z(r)
-- (same modular frequency as modCharC; √r is z-constant, so product rule via hasDerivAt_modCharC.mul_const).
-- The pointwise derivative feeding holomorphy of devCorrExt (differentiate under ∫, dominated on the open
-- half-strip where −Im z∈(0,1/2) keeps log·d_z bounded by the r^{1/2+Im z} taming).
#print axioms QIQTH.StandardSubspaceModular.devChar_norm_le_Icc
-- expected: standard only — ★★ DEVICE CHARACTER bound on CLOSED [0,2] (spectrum-ready strengthening). Interior
-- (0,2): devChar_norm_le. Endpoints r∈{0,2}: modCharC z r=1 (r∉(0,2)) ⇒ d_z(r)=√r, ‖·‖=√r≤√2; d_z(0)=0 (√r
-- kills the r→0 singularity). Since 0≤R≤2 (rvdRC_nonneg, rvdR_le_two) spectrum(R)⊆[0,2], so this is the bound
-- the borelFC construction of the operator device vector (2−R)^{iz}R^{−iz+1/2}ζ=d_z(R)ζ will consume.
#print axioms QIQTH.StandardSubspaceModular.differentiable_devChar
#print axioms QIQTH.StandardSubspaceModular.measurable_devChar
-- SPECTRAL-INTEGRAL STRIP EXTENSION (ModularRelativeEntropy.lean): F_ξ(z)=∫u_z dμ^R_ξ + its boundary data.
#print axioms QIQTH.modCorrExt_ofReal
#print axioms QIQTH.modCorrExt_kms_flip
-- expected: standard only — modCorrExt S ξ z = ∫ modCharC z ω.val dμ^R_ξ, the candidate bounded-holomorphic
-- strip extension of t↦⟪ξ,Δ^{it}ξ⟫. modCorrExt_ofReal: BOTTOM edge F_ξ(t)=⟪ξ,Δ^{it}ξ⟫ (modCharC_ofReal +
-- rvdSpec_modUnitary). modCorrExt_kms_flip: TOP edge F_ξ(t+i)=∫ modChar t (ω)·(ω/(2−ω)) dμ (the KMS weight),
-- in the regular regime σ(R)⊆(0,2). These are the two BOUNDARY conditions strip-uniqueness consumes — the
-- extension's edges now pinned. Remaining for hUniq: holomorphy under ∫ (boundedness done) + Borchers reduction.
#print axioms QIQTH.diffContOnCl_devCorrExt
-- expected: standard only — ★★ DEVICE bdd-HOLO on the CLOSED half-strip, NO regular window. DiffContOnCl =
-- differentiableOn (holomorphic) + continuousOn up to {−1/2≤Im≤0}. Edge continuity = dominated convergence under
-- ∫ (‖d_z‖≤√2 on the closed half-strip via devChar_norm_le_Icc+rvdRC_spectrum_mem_Icc; z↦d_z continuous, entire).
-- The exact DiffContOnCl input eqOn_of_im_zero_edge_halfStrip consumes — for EVERY standard subspace.
#print axioms QIQTH.StandardSubspaceModular.devCorrExt_eqOn_of_boundary
-- expected: standard only — ★★ DEVICE Δ-side STRIP-UNIQUENESS (no regular window): any bdd-holo F on the half-
-- strip agreeing with devCorrExt on the real axis Im=0 coincides with it on the whole closed half-strip
-- (eqOn_of_im_zero_edge_halfStrip + diffContOnCl_devCorrExt + devCorrExt_norm_le). The device analogue of
-- modCorrExt_eq_of_boundary, available for ANY standard subspace. Δ-side half of the strip-uniqueness comparison.
#print axioms QIQTH.deviceOpC
#print axioms QIQTH.deviceOpC_ofReal
-- expected: standard only — ★★ COMPLEX-z DEVICE OPERATOR d_z(R)=(2−R)^{iz}R^{−iz+1/2} for z in the half-strip
-- {−1/2≤Im z≤0} (borelFC of devChar z; ‖d_z‖≤√2 on σ(R)⊆[0,2], NO regular window). EXACTLY RvD Prop 3.7's
-- device (verified vs the rendered source). J·(d_z(R)ζ) is the anti-holo 2nd-slot vector of the Thm 3.8
-- g-function g(z)=⟨h(z),J d_z(R)ζ⟩. deviceOpC_ofReal: restricts to deviceOpReal (Δ^{it}√R) on Im z=0.
#print axioms QIQTH.deviceOpC_norm_le
-- deviceOpC_norm_le: ‖d_z(R)‖≤2√2 uniformly on the half-strip (borelFC norm ≤2·sup‖f‖, devChar bound √2).
#print axioms QIQTH.deviceOpC_bottomEdge_eq
-- expected: standard only — ★★ BOTTOM-EDGE t-translation: deviceOpC(t−i/2) = Δ^{it}·deviceOpC(−i/2) (bottom-edge
-- analogue of deviceOpReal_eq). devChar(↑t−i/2)=u_t·devChar(−i/2) EVERYWHERE (modCharC_add, no endpoint issue) ⇒
-- borelFC_mul ⇒ modUnitary t · deviceOpC(−i/2). So deviceVec(t−i/2)=Δ^{it}·deviceVec(−i/2): the modular flow
-- translates the fixed bottom-edge vector. Both g-function device edges now factor through Δ^{it}.
#print axioms QIQTH.deviceOpReal_eq
-- expected: standard only — ★★ DEVICE OPERATOR FACTORS as Δ^{it}·√R: deviceOpReal t = modUnitary t · rvdSqrtR
-- (general top-edge identity; deviceOpReal_zero is t=0). devChar(↑t)=u_t·√· ⇒ borelFC(devChar ↑t)=borelFC(u_t)·
-- borelFC(√·)=Δ^{it}·√R (borelFC_mul + modUnitary=borelFC(u_t) + borelFC(√·)=rvdSqrtR). So deviceVec(t)ζ=Δ^{it}(√R ζ)
-- =Δ^{it}ξ ⇒ g-function top edge g(t)=⟪U_tη,JΔ^{it}ξ⟫ (gTopEdge_real, real).
#print axioms QIQTH.deviceOpReal_zero
-- expected: standard only — ★★ DEVICE BOUNDARY OPERATOR IDENTITY: deviceOpReal 0 = √R (rvdSqrtR). devChar 0=√·
-- ⇒ deviceOpReal 0 = cfcCont(√·); (cfcCont√·)²=R (cfcCont_mul+cfcCont_coord, √ω·√ω=ω on σ(R)⊆[0,∞)) & ≥0
-- (=(cfcCont∜·)², self-adjoint square via cfcCont_star+star_mul_self_nonneg) ⇒ CFC.sqrt_unique ⇒ =CFC.sqrt R.
-- So deviceVec(0)=√R ζ=ξ, J·deviceVec(0)=Jξ ⇒ g-function value g(0)=⟪η,Jξ⟫ = the GConstancy RHS. The cfcCont↔CFC
-- bridge (borelFC of continuous fn = Mathlib CFC) realized via the sqrt-uniqueness pattern, no new axiom.
#print axioms QIQTH.devCorrExt_ofReal_inner
#print axioms QIQTH.deviceVecF_zero
-- expected: standard only — deviceVecF(0)=√R ζ (=ξ, the comparison point), from deviceVecF_real_eq t=0 + modUnitary_zero.
#print axioms QIQTH.gFunction_zero
-- expected: standard only — g(0)=⟪Jξ,η_n⟫ (ξ=√R ζ, η_n=gaussSmear): the Phragmén–Lindelöf comparison point. With g
-- const this = g(t). Via deviceVecF_zero + gaussSmearC_zero + modConjBilin_apply.
#print axioms QIQTH.deviceVecF_continuousOn
-- expected: standard only — DEVICE VECTOR CONTINUOUS on closed half-strip: ‖deviceVecF z−deviceVecF z₀‖=√(∫‖d_z−d_{z₀}
-- ‖²dμ)→0 (deviceOpC_diff_normSq+tendsto_integral_devChar_diff_sq+Real.sqrt_sq, congr' on self_mem_nhdsWithin).
#print axioms QIQTH.diffContOnCl_gFunction
-- expected: standard only — ★★ g-FUNCTION DiffContOnCl (full analytic regularity for Phragmén–Lindelöf): holo on open
-- half-strip (differentiableOn_gFunction) + continuous to closure {−1/2≤Im≤0} (modConjBilin bilinear ∘ deviceVecF_
-- continuousOn + gaussSmearC continuous, ContinuousOn.clm_apply). With gFunction_norm_le + edge realities ⇒ constancy.
#print axioms QIQTH.tendsto_integral_devChar_diff_sq
-- expected: standard only — DEVICE-CHAR L² CONTINUITY (dominated conv): ∫‖d_z−d_{z₀}‖²dμ^R_ζ→0 as z→z₀ in closed
-- half-strip. tendsto_integral_filter_of_dominated_convergence: integrand→0 ptwise (hasDerivAt_devChar_Icc.continuousAt)
-- + dominated by (√2+√2)²=8 (devChar_norm_le_Icc). With deviceOpC_diff_normSq ⇒ deviceVecF continuity ⇒ DiffContOnCl.
#print axioms QIQTH.deviceOpC_diff_normSq
-- expected: standard only — L² DIFFERENCE identity ‖deviceOpC(z)ζ−deviceOpC(z₀)ζ‖²=∫‖d_z−d_{z₀}‖²dμ^R_ζ (deviceOpC_sub
-- + borelFC_apply_norm_sq). Foundation of device-vector CONTINUITY (∫→0 by dominated conv) ⇒ DiffContOnCl half of g.
#print axioms QIQTH.deviceVecF_norm_le
-- expected: standard only — UNIFORM device-vector bound ‖deviceVecF z‖≤2√2‖ζ‖ ∀z (deviceOpC_norm_le applied to ζ; 0
-- off strip). The bounded device factor of g.
#print axioms QIQTH.gFunction_norm_le
-- expected: standard only — POINTWISE g-BOUND ‖g(z)‖≤2√2‖ζ‖·‖h(z)‖ (h=gaussSmearC): modConj_norm isometry +
-- deviceVecF_norm_le + norm_inner_le_norm. With the Gaussian bound on ‖h‖ ⇒ uniform strip bound for Phragmén–Lindelöf.
#print axioms QIQTH.modConj_deviceVecF_bottom
-- expected: standard only — DEVICE/J COMMUTE on bottom edge: J·deviceVecF(t−i/2)=Δ^{it}·(J·deviceOpC(−i/2)ζ) (deviceVecF_
-- bottom_eq + modConj_commute_modUnitary). With deviceOpC(−i/2)=√(2−R) + modConj_rvdSqrtTwoSubR_of_fixed ⇒ Δ^{it}·√R ζ=
-- Δ^{it}ξ, the 2nd slot of g(t−i/2). Step (a1) of the bottom-edge reality (RvD device argument).
#print axioms QIQTH.deviceVecF_bottom_eq
-- expected: standard only — BOTTOM-EDGE device value deviceVecF(t−i/2)=Δ^{it}·deviceOpC(−i/2)ζ (=√(2−R)ζ off {0,2}):
-- deviceVecF_eq_of_mem (mid-line Im=−1/2 in closed half-strip) + deviceOpC_bottomEdge_eq. The 2nd-slot device on the
-- g-function bottom edge; its reality is the KMS input (HalfStripReal) for the Phragmén–Lindelöf constancy.
#print axioms QIQTH.gFunction_top_edge_real
-- expected: standard only — ★★ TOP-EDGE REALITY of g (endgame piece 3a): g(t).im=0 for ξ=√R ζ∈𝒦 + orbit in 𝒦.
-- Δ^{it}(Jξ)=J(Δ^{it}ξ) (modConj_commute) with Δ^{it}ξ∈𝒦 (modUnitary_mapsTo_K) ⇒ ⊥i𝒦 (projIK_modConj_eq_zero_of_
-- mem_K, J𝒦=(i𝒦)^⊥); ⟪𝒦-vec V_t η_n, ⊥i𝒦⟫ REAL (inner_real_of_mem_K_perp_IK), g(t)=conj of that. Geometric.
#print axioms QIQTH.gFunction_real_eq
-- expected: standard only — g(t)=⟪Δ^{it}(Jξ), V_t η_n⟫ (top edge, ξ=√R ζ): deviceVecF_real_eq + gaussSmearC_ofReal +
-- modConj_commute_modUnitary(JΔ^{it}=Δ^{it}J). conj = GConstancy LHS ⟪V_t η_n, Δ^{it}Jξ⟫; reality ⇒ g(t)=that.
#print axioms QIQTH.differentiableOn_gFunction
-- expected: standard only — ★★★ G-FUNCTION HOLOMORPHIC (endgame piece 2): g(z)=⟪J·d_z(R)ζ, V_z η⟫=modConjBilin S
-- (deviceVecF S ζ z)(gaussSmearC V n η z) is DifferentiableOn the open half-strip. The continuous ℂ-bilinear
-- modConjBilin (=⟪J·,·⟫) applied to two HOLO curves: deviceVecF (differentiableOn_deviceVecF, strong holo) +
-- gaussSmearC (differentiable_gaussSmearC, entire V-orbit). Bilinear chain rule DifferentiableOn.clm_apply. The
-- holomorphic strip fn the Phragmén–Lindelöf constancy g(t)=g(0)⟹GConstancy consumes.
#print axioms QIQTH.deviceVecF_real_eq
-- expected: standard only — REAL-AXIS value deviceVecF(t)=Δ^{it}·√R ζ (g-function top-edge): via deviceVecF_eq_of_mem
-- + deviceOpC_ofReal + deviceOpReal_eq. With ξ=√R ζ, J·deviceVecF(t)=Δ^{it}(Jξ) = the second slot of g(t)=
-- ⟪V_t η, Δ^{it}Jξ⟫ (GConstancy's LHS). The g-function endgame top edge.
#print axioms QIQTH.differentiableOn_deviceVecF
-- expected: standard only — device vector HOLOMORPHIC (DifferentiableOn) on the open half-strip im⁻¹'Ioo(-1/2)0:
-- immediate from hasDerivAt_deviceVecF (slab β₀=-Im z₀/2, β₁=(1/2-Im z₀)/2 around z₀). The strong-holo half-strip
-- input the g-function Phragmén–Lindelöf constancy consumes.
#print axioms QIQTH.hasDerivAt_deviceVecF
-- expected: standard only — ★★★★ STRONG (FRÉCHET) HOLOMORPHY of the device vector (PIECE 4 COMPLETE, the holomorphy
-- wall DEFEATED): HasDerivAt (deviceVecF S ζ) (deviceDerivOpC z₀ ζ) z₀ at every interior z₀ of the open half-strip.
-- slope→deriv since ‖slope−deriv‖=√(remainder integral)→√0=0 (deviceOpC_slope_normSq + tendsto_integral_devChar_
-- remainder_sq + Real.sqrt continuity, via hasDerivAt_iff_tendsto_slope + tendsto_iff_norm_sub_tendsto_zero). NO
-- Mathlib Dunford (weak⟹strong) needed — the H-valued derivative is obtained from a SCALAR dominated-convergence
-- integral. ⇒ DifferentiableOn deviceVecF on the open strip ⇒ the g-function product rule ⇒ GConstancy ⇒ hUniq.
#print axioms QIQTH.deviceOpC_slope_normSq
-- expected: standard only — ★★★ OPERATOR-ALGEBRA HEART of piece 4: ‖(z−z₀)⁻¹·(deviceOpC(z)ζ−deviceOpC(z₀)ζ) −
-- deviceDerivOpC(z₀)ζ‖² = ∫‖Δ_z(ω)−∂d(ω)‖² dμ^R_ζ (= tendsto_integral_devChar_remainder_sq integrand). The slope−
-- deriv vector is ONE borelFC applied to ζ (deviceOpC_sub + borelFC_smul + borelFC_sub via CLM sub_apply/smul_apply),
-- so borelFC_apply_norm_sq turns ‖·‖² into ∫‖g_z‖²dμ. Bridges the H-valued slope to the proven scalar →0 integral.
#print axioms QIQTH.deviceOpC_sub
-- expected: standard only — device-op difference as single borelFC: deviceOpC(z)−deviceOpC(z₀)=borelFC(d_z−d_{z₀}),
-- = borelFC_sub.symm (deviceOpC is defeq a borelFC with √2 bound). First step of the slope operator-algebra.
#print axioms QIQTH.deviceDerivOpC
-- expected: standard only — CANDIDATE Fréchet derivative operator ∂_z d_{z₀}(R)=borelFC(ω↦i·log((2−ω)/ω)·d_{z₀}(ω)),
-- bounded by devCharDeriv_norm_le_slab const (slab-independent operator by borelFC_congr). Applied to ζ it is the
-- derivative of deviceVecF S ζ at z₀ (hasDerivAt_deviceVecF, pending the borelFC operator-algebra slope identity).
#print axioms QIQTH.deviceVecF_eq_of_mem
-- expected: standard only — TOTAL device-vector function deviceVecF (piece 4 of strong holo): dite-total ℂ→H,
-- = deviceOpC(z)ζ on closed half-strip {−1/2≤Im z≤0}, 0 outside. Sidesteps the deviceOpC-takes-proofs friction
-- so HasDerivAt (deviceVecF S ζ) is about a genuine ℂ→H function. deviceVecF_eq_of_mem = dif_pos (proof-irrel).
#print axioms QIQTH.devCharDeriv_norm_le_slab
-- expected: standard only — derivative-norm-on-slab bound ‖i·log·d_w(ω)‖≤C (companion to devChar_slope_norm_le):
-- bounds the candidate Fréchet derivative ∂d at slab points (devChar_deriv_norm_le on (0,2); 0 on {0,2}).
#print axioms QIQTH.tendsto_integral_devChar_remainder_sq
-- expected: standard only — ★★★ STRONG-HOLO DOMINATED CONVERGENCE (piece 3, the heart): the L² remainder of the
-- device-vector difference quotient vanishes, ∫‖(d_z(ω)−d_{z₀}(ω))/(z−z₀)−∂d_{z₀}(ω)‖²dμ^R_ζ→0 as z→z₀ (z≠z₀).
-- Lebesgue tendsto_integral_filter_of_dominated_convergence: integrand→0 ptwise (tendsto_devChar_slope, piece 1)
-- + dominated by const 4C² (devChar_slope_norm_le ‖Δ_z‖≤C + devCharDeriv_norm_le_slab ‖∂d‖≤C, piece 2), integrable
-- on finite μ^R_ζ. With borelFC_sub+borelFC_apply_norm_sq (‖slope−d‖²=∫‖Δ_z−∂d‖²dμ) ⇒ Fréchet deriv of z↦deviceOpC(z)ζ.
#print axioms QIQTH.devChar_slope_norm_le
-- expected: standard only — UNIFORM slope/Lipschitz bound (piece 2 of strong-holo dominated convergence): on the
-- slab {−β₁<Im z<−β₀}, ‖d_z(ω)−d_{z₀}(ω)‖ ≤ C·‖z−z₀‖, C=devChar_deriv_norm_le const, UNIFORM in ω. Via complex
-- MVT Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (hasDerivAt_devChar_Icc on convex slab + deriv bound;
-- ω∈{0,2}⇒deriv 0). Gives ‖Δ_z(ω)‖≤C uniformly ⇒ the dominating constant 4C² for dominated convergence.
#print axioms QIQTH.tendsto_devChar_slope
-- expected: standard only — POINTWISE diff-quotient convergence (piece 1 of strong-holo dominated convergence):
-- (d_z(ω)−d_{z₀}(ω))/(z−z₀) → i·log((2−ω)/ω)·d_{z₀}(ω) as z→z₀ (z≠z₀), from hasDerivAt_devChar_Icc via
-- hasDerivAt_iff_tendsto_slope + slope_def_field. Feeds tendsto_integral_filter_of_dominated_convergence ⇒
-- ∫‖Δ_z−∂d‖²dμ→0 ⇒ Fréchet deriv of z↦deviceOpC(z)ζ (with borelFC_sub + borelFC_apply_norm_sq).
#print axioms QIQTH.devCorrExt_inner
-- expected: standard only — DIAGONAL operator identification (general z in half-strip): D_ξ(z)=⟪ξ,deviceOpC(z)ξ⟫.
-- The scalar integral ∫d_z dμ^R_ξ IS the diagonal device-operator expectation (inner_borelFC+bilinDiag_self+diagInt).
-- Bridges the proven scalar holo (hasDerivAt_devCorrExt) to the device OPERATOR — prerequisite for the polarization
-- route to off-diagonal ⟪w,deviceOpC(z)ζ⟫ and the strong/Fréchet holo of z↦deviceOpC(z)ζ.
#print axioms QIQTH.StandardSubspaceModular.borelFC_sub
-- expected: standard only — borelFC LINEARITY (subtraction): (f−g)(T)=f(T)−g(T), from borelFC_add+borelFC_neg
-- (=borelFC_smul(−1)). Step (i) of the strong-holomorphy diff-quotient: deviceVec(z)−deviceVec(z₀) =
-- borelFC(devChar z − devChar z₀)ζ, so the slope = borelFC(Δ_z)ζ with Δ_z=(devChar z−devChar z₀)/(z−z₀).
#print axioms QIQTH.rvdSpec_borelFC_diag
-- expected: standard only — DIAGONAL of borelFC: ⟪x,f(R)x⟫=∫f dμ^R_x (inner_borelFC+bilinDiag_self+diagInt). Linear
-- companion to borelFC_inner_self; the bridge for borelFC_congr_ae.
#print axioms QIQTH.StandardSubspaceModular.borelFC_congr_ae
-- expected: standard only — ★★ borelFC a.e.-CONGRUENCE: f(R)=g(R) if f=ᵐ[μ^R_x] g ∀x. Via rvdSpec_borelFC_diag (diagonals
-- = ∫, integral_congr_ae) + clm_eq_of_inner_self_eq. THE tool for deviceOpC(−i/2)=√(2−R): d_{−i/2} & √(2−r) differ ONLY
-- on endpoints {0,2}, E-null once R,2−R injective. Remaining for (a1-end): scalarMeasure({0,2})=0 (E-atom, needs E=
-- boundedFC(ind) or R·E({λ})=λE({λ})).
#print axioms QIQTH.SpectralTheorem.borelFC_const
-- expected: standard only — QIQTH-layer wrapper of boundedFC_const: (fun _ => c)(T)=c•1.
#print axioms QIQTH.SpectralTheorem.borelFC_indicator
-- expected: standard only — QIQTH-layer wrapper of boundedFC_indicator: 𝟙_s(T)=E s (bounded Borel FC of a
-- level-set indicator = the spectral projection). The bridge from the FC down to the PVM projections E.
#print axioms QIQTH.StandardSubspaceModular.rvdRC_mul_E_levelSet
-- expected: standard only — ★ SPECTRAL-ATOM EIGEN-RELATION R·E({λ=c})=c·E({λ=c}): borelFC sends coord↦mult, so on
-- {λ=c} R acts as scalar c. Via R=borelFC(coord) (rvdRC_eq_borelFC), E(s)=borelFC(𝟙_s) (borelFC_indicator),
-- coord·𝟙_s=c·𝟙_s pointwise, borelFC_mul+borelFC_const. THE E-atom-vanishing engine (closes the borelFC_congr_ae gap).
#print axioms QIQTH.StandardSubspaceModular.rvdRC_E_zero_levelSet
-- expected: standard only — E({λ=0})=0 (no atom at 0): R·E({0})=0 (eigen-relation, c=0) + R injective (rvdRC_injective).
#print axioms QIQTH.StandardSubspaceModular.rvdRC_E_two_levelSet
-- expected: standard only — E({λ=2})=0 (no atom at 2): (2−R)·E({2})=0 (eigen-relation, c=2 ⇒ R·E=2E) + 2−R injective.
#print axioms QIQTH.rvdSpecMeasure_zero_levelSet
-- expected: standard only — μ^R_x({λ=0})=0 (scalarMeasure_apply + E({0})=0).
#print axioms QIQTH.rvdSpecMeasure_two_levelSet
-- expected: standard only — μ^R_x({λ=2})=0 (scalarMeasure_apply + E({2})=0).
#print axioms QIQTH.rvdSpecMeasure_endpoints
-- expected: standard only — ★★ μ^R_x({λ∈{0,2}})=0: the device-character ENDPOINTS are μ^R_x-null (measure_union_null
-- of the two atoms). EXACTLY the a.e. input borelFC_congr_ae needs for deviceOpC(−i/2)=√(2−R): d_{−i/2} & √(2−r)
-- differ only on {0,2}. (a1-end) E-atom-vanishing now CLOSED — next: feed into deviceOpC(−i/2)=√(2−R) + KMS reflection.
#print axioms QIQTH.cfcCont_sqrtTwoSub_eq
-- expected: standard only — CONTINUOUS half of deviceOpC(−i/2)=√(2−R): cfcCont(√(2−·))=rvdSqrtTwoSubR. Mirrors
-- deviceOpReal_zero (cfcCont(√·)=√R): square=2−R (cfcCont_mul + cfcCont(2−coord)=2−R via add/smul/one/coord),
-- positive (=(cfcCont ∜(2−·))²), CFC.sqrt_unique ⇒ CFC.sqrt(2−R).
#print axioms QIQTH.StandardSubspaceModular.deviceOpC_neg_half_eq
-- expected: standard only — ★★★ deviceOpC(−i/2)=√(2−R) (=rvdSqrtTwoSubR), the BOTTOM-EDGE device identity. devChar(−i/2)
-- =√(2−r) on (0,2) (devChar_neg_half_I) + cfcCont(√(2−·))=√(2−R) (cfcCont_sqrtTwoSub_eq); symbols differ ONLY at {0,2}
-- (modCharC=1 swaps), μ^R_x-null (rvdSpecMeasure_endpoints), so borelFC_congr_ae identifies the operators. Step (a1)
-- of the bottom-edge KMS reality (A) COMPLETE: J·deviceOpC(−i/2)ζ=J√(2−R)ζ=√Rζ=ξ. Remaining: (a2/a3) KMS reflection.
#print axioms QIQTH.StandardSubspaceModular.modConj_deviceOpC_neg_half
-- expected: standard only — J·deviceOpC(−i/2)ζ=√R(Jζ): deviceOpC_neg_half_eq + bottom-edge sqrt swap J√(2−R)=√R·J.
#print axioms QIQTH.StandardSubspaceModular.modConj_deviceVecF_bottom_eq
-- expected: standard only — bottom-edge g-VECTOR J·deviceVecF(t−i/2)=Δ^{it}·√R(Jζ) (modConj_deviceVecF_bottom +
-- modConj_deviceOpC_neg_half). First slot of the bottom g-function made explicit via deviceOpC(−i/2)=√(2−R).
#print axioms QIQTH.StandardSubspaceModular.modConj_deviceVecF_bottom_eq_fixed
-- expected: standard only — ★ Jζ=ζ case: J·deviceVecF(t−i/2)=Δ^{it}·√Rζ=Δ^{it}ξ (RvD (2−R)^½ζ=Jξ at vector level).
-- The bottom-edge g-vector IS Δ^{it}ξ; reality of ⟪Δ^{it}ξ,gaussSmearC(t−i/2)⟫ = the remaining KMS input h1 (a2/a3).
#print axioms QIQTH.StandardSubspaceModular.modConj_rvdSqrtTwoSubR
-- expected: standard only — J√(2−R)=√R·J (companion of modConj_rvdSqrtR), bottom-edge Tomita algebra.
#print axioms QIQTH.StandardSubspaceModular.rvdSqrtTwoSubR_injective
-- expected: standard only — √(2−R) injective (from √(2−R)²=2−R + rvdTwoSubRC_injective).
#print axioms QIQTH.StandardSubspaceModular.rvdSqrtR_modConj_of_mem_K
-- expected: standard only — ★ RvD Prop 3.7 (bounded Tomita on √R): ξ∈𝒦 ⟹ √R(Jξ)=√(2−R)ξ (bounded form of Δ^½ξ=Jξ).
-- From J(Tξ)=(2−R)ξ (modConj_rvdT_of_mem_K) + two sqrt reflections, cancel one √(2−R).
#print axioms QIQTH.StandardSubspaceModular.modConj_fixed_of_sqrtR_mem_K
-- expected: standard only — ★★ √Rζ∈𝒦 ⟹ Jζ=ζ: the bottom-edge condition reconciliation (resolves the
-- √Rζ∈𝒦-vs-Jζ=ζ gap). rvdSqrtR_modConj_of_mem_K at ξ=√Rζ + modConj_rvdSqrtR + commute, rvdT injective.
#print axioms QIQTH.StandardSubspaceModular.modConj_deviceVecF_bottom_eq_of_mem_K
-- expected: standard only — under √Rζ∈𝒦: J·deviceVecF(t−i/2)=Δ^{it}·√Rζ=Δ^{it}ξ (collapses √R(Jζ)→√Rζ via Jζ=ζ).
#print axioms QIQTH.StandardSubspaceModular.gFunction_bottom_eq_of_mem_K
-- expected: standard only — ★★★ bottom g-VALUE explicit (√Rζ∈𝒦): g(t−i/2)=⟪J·deviceVecF(t−i/2),w⟫=⟪Δ^{it}ξ,w⟫.
-- h1 NOW = Im⟪Δ^{it}ξ,gaussSmearC(t−i/2)⟫=0, ξ=√Rζ∈𝒦 — the clean a2/a3 KMS-reflection target (Δ^½=J + half-strip PL
-- from stripKMSrvd_real_midline). Bottom-edge g-vector AND value fully machine-checked; only the KMS reflection remains.
#print axioms QIQTH.StandardSubspaceModular.gFunction_bottom_real_of_perp_IK
-- expected: standard only — geometric SUFFICIENT condition (NOT the h1 route): under √Rζ∈𝒦, g(t−i/2)=⟪Δ^{it}ξ,
-- gaussSmearC(t−i/2)⟫ real IF projIK(gaussSmearC(t−i/2))=0. ⚠ that hypothesis is generally FALSE (mid-line orbit
-- has an i𝒦 component from the e^{−ni(u−t)} phase: −i·sin·V_uη ∈ i𝒦), so the bottom-edge reality is a GLOBAL
-- analytic fact (KMS f-transfer, RvD Thm 3.8 core), not pointwise ⊥. Lemma records the correct implication only.
#print axioms QIQTH.StandardSubspaceModular.gFunction_bottom_real_of_kms_match
-- expected: standard only — ★★★ THE CORRECT h1 ROUTE (RvD Thm 3.8 f-transfer). Freeze device at bottom-edge value
-- ξ_t=Δ^{it}ξ: g(t−i/2)=⟪ξ_t,gaussSmearC(t−i/2)⟫=corrC ξ_t V n η (t−i/2). corrC ξ_t entire (differentiable_corrC)
-- + bounded on half-strip (corrC_bdd_halfStrip); KMS f matches it on real axis with f(t−i/2) real ⟹ (half-strip
-- boundary uniqueness eqOn_of_im_zero_edge_halfStrip) corrC ξ_t=f ⟹ g(t−i/2)=f(t−i/2) real. hmatch IS satisfiable
-- (RvD's KMS for pair (η,Δ^{it}ξ) gives it) — remaining gap = the convention bridge from StripKMSrvd/HalfStripReal.
#print axioms QIQTH.StandardSubspaceModular.gFunction_bottom_real_of_faithful_kms
-- expected: standard only — ★★ h1 from the FAITHFUL-convention KMS witness. RvD Def 3.4 (read from source):
-- f(t)=⟨U_tξ,η⟩, RvD ⟨·,·⟩ LINEAR-FIRST (⟨h(z),Δ^{it}ξ⟩ entire) ⟹ Mathlib f(t)=inner ℂ η (V_t ξ) [orbit LINEAR slot].
-- For pair (gaussSmear,ξ_t): f(s)=⟪ξ_t,V_s gaussSmear⟫=corrC ξ_t s, f(t−i/2) real ⟹ gFunction_bottom_real_of_kms_match
-- ⟹ h1. VALIDATES the finding: codebase StripKMSrvd/HalfStripReal use inner ℂ (V_t ξ) η = CONJUGATE of RvD Def 3.4
-- (transfers reality to t+i/2 not t−i/2). Sole remaining h1 gap = convention fix StripKMSrvd ⟹ this faithful witness.
#print axioms QIQTH.Fock.OneParticleBW.h1_of_stripKMSrvd
-- expected: standard only — ★★★ h1 DISCHARGED from StripKMSrvd — RvD Thm 3.8 device g-function bottom edge COMPLETE.
-- For η∈𝒦 (orbit in 𝒦) + ξ=√Rζ∈𝒦: KMS (hKMS) at pair (gaussSmear,ξ_t=Δ^{it}ξ) [both ∈𝒦: gaussSmear_mem_K,
-- modUnitary_mapsTo_K] gives f bdd-holo, f(s)=⟪ξ_t,V_s gaussSmear⟫ (faithful Def 3.4), f(t−i/2) real (real_on_
-- midline_of_conj_flip). Restrict to half-strip (DiffContOnCl.mono) + gFunction_bottom_real_of_faithful_kms ⟹ h1.
-- The last analytic input of the g-function, NO LONGER LABELLED. Remaining for full hUniq: hdense (C', √R-range).
#print axioms QIQTH.Fock.OneParticleBW.oneParticleBW_of_stripKMSrvd_density
-- expected: standard only — ★★★ FULL hUniq DISCHARGE with h1 ELIMINATED: modUnitary S t = V t from V contraction
-- group + 𝒦-invariance + StripKMSrvd (RvD Def 3.4) + ONLY hdense (√R-range density in 𝒦). The bottom-edge KMS
-- reality h1 is derived from hKMS via h1_of_stripKMSrvd (RvD Thm 3.8 g-function f-transfer, machine-checked), no
-- longer labelled. The entire device g-function argument is axiom-free; the SOLE remaining named analytic input
-- is hdense (C', √R-range∩𝒦 dense in 𝒦). The convention is now the genuine RvD Def 3.4 (vacuity hole closed).
#print axioms QIQTH.StandardSubspaceModular.commute_projK_of_commute_R_D
-- expected: standard only — generic [A,P]=0 from [A,R]=[A,D]=0 (2P=R+D, rvdR_add_rvdPmQ_eq). Toward hdense.
#print axioms QIQTH.StandardSubspaceModular.mapsTo_K_of_commute_R_D
-- expected: standard only — generic 𝒦-invariance: A commuting with R(rvdR) and D(rvdPmQ) preserves 𝒦 (operator-
-- generic modUnitary_mapsTo_K_of_commute). The mechanism by which symmetric f(R) lands cutoffs in 𝒦 for hdense.
#print axioms QIQTH.StandardSubspaceModular.commute_rvdPmQ_of_commute_modConj_rvdT
-- expected: standard only — [A,D]=0 from [A,J]=[A,T]=0 (D=J·T, modConj_rvdT). For symmetric f, cfcCont f commutes
-- with J (modConj_cfcΩ/twΩ) and T (fn of R) ⟹ with D — the [·,D]=0 'frontier' step available for symmetric symbols.
#print axioms QIQTH.StandardSubspaceModular.cfcΩ_symm_mapsTo_K
-- expected: standard only — ★★ SYMMETRIC f(R) PRESERVES 𝒦: for twΩ f=f (conj(f(2−r))=f(r)), cfcΩ f maps 𝒦→𝒦.
-- cfcΩ f commutes with R (cfcΩ_commute_rvdRC), T (cfcΩ_commute_rvdT), J (modConj_cfcΩ + twΩ f=f) ⟹ with D=J·T
-- (commute_rvdPmQ_of_commute_modConj_rvdT) ⟹ with P=(R+D)/2 (mapsTo_K_of_commute_R_D). The hdense engine (step a):
-- symmetric spectral cutoffs land in 𝒦. Remaining: cutoff φ_k(R)ξ→ξ ∈range(√R) (step b) + assemble (step c).
#print axioms QIQTH.StandardSubspaceModular.rvdSqrtR_range_dense_in_K
-- expected: standard only — ★★★★ hdense PROVEN: √R-range dense in 𝒦 (RvD's ξ=√Rζ reconciliation, the LAST g-function
-- input). Via polar radius T=√R√(2−R): self-adjoint, DENSE RANGE in H (rvdT_restrictScalars_denseRange), commutes
-- with P (with R via rvdRC_commute_rvdT, with J via modConj_rvdT_modConj ⟹ with D ⟹ with P), and Tη=√R(√(2−R)η)∈
-- range(√R). For ξ∈𝒦: Tζ_k→ξ, T(Pζ_k)=P(Tζ_k)→Pξ=ξ ∈𝒦. ζ_k=√(2−R)(Pζ_k). hdense is now a THEOREM, not labelled.
#print axioms QIQTH.Fock.OneParticleBW.oneParticleBW_complete
-- expected: standard only — ★★★★★ hUniq FULLY DISCHARGED (RvD Theorem 3.8 COMPLETE, axiom-free). modUnitary S t=V t
-- for a strongly-continuous contraction group V with 𝒦-invariance + StripKMSrvd (RvD Def 3.4), NO remaining named
-- analytic input. Both g-function inputs are now THEOREMS: h1 (h1_of_stripKMSrvd, bottom-edge KMS reality via the
-- f-transfer) and hdense (rvdSqrtR_range_dense_in_K, √R-range density via the polar radius T). The un-garbled
-- device g-function discharge is end-to-end machine-checked. Rests only on the genuine KMS + contraction/invariance.
#print axioms QIQTH.StandardSubspaceModular.modCorr_midline_real
-- expected: standard only — ★★ MODULAR flow half-strip KMS reality is GEOMETRIC (toward RvD Prop 3.7, Δ is KMS /
-- non-vacuity of oneParticleBW_complete). For ξ=√Rζ∈𝒦, η∈𝒦: ⟪η,deviceVecF(t−i/2)⟫=⟪η,Δ^{it}Jξ⟫ real, since
-- deviceVecF(t−i/2)=J(Δ^{it}ξ) (modConj_deviceVecF_bottom_eq_of_mem_K + modConj_sq), Δ^{it}ξ∈𝒦 ⟹ J(Δ^{it}ξ)∈(i𝒦)^⊥
-- (projIK_modConj_eq_zero_of_mem_K), η∈𝒦 ⟹ inner_real_of_mem_K_perp_IK. NO circularity (the modular flow's device
-- vector IS Δ^{iz}ξ; Δ^½ξ=Jξ on 𝒦) — unlike the candidate V whose h1 needed the f-transfer.
#print axioms QIQTH.StandardSubspaceModular.modCorr_halfStripReal
-- expected: standard only — ★★ MODULAR flow satisfies RvD Prop 3.5 HALF-STRIP KMS form (at ξ=√Rζ∈𝒦): ∃f bdd-holo
-- on {−1/2<Im<0}, f(t)=⟪η,Δ^{it}ξ⟫, f(t−i/2) REAL. f(z)=⟪η,deviceVecF(z)⟫=⟪η,Δ^{iz}ξ⟫; bdd-holo via
-- differentiableOn_deviceVecF + deviceVecF_continuousOn; real-axis deviceVecF_real_eq; mid-line modCorr_midline_real
-- (geometric). Converse RvD Thm 3.8 (Δ is KMS) — non-vacuity of oneParticleBW_complete. Remaining: density + Prop 3.5 ⟸.
-- P4-derivation Stage 1: modular Hamiltonian K=−log Δ spectral function + generator identity Δ^{it}=e^{−itK}:
#print axioms QIQTH.StandardSubspaceModular.modChar_eq_exp_neg_kFn
#print axioms QIQTH.StandardSubspaceModular.kFn_nonpos_of_lt_one
#print axioms QIQTH.StandardSubspaceModular.kFn_nonneg_of_one_lt
-- P4-derivation Stage 2: the first law S = ⟨K⟩ — modular relative entropy = modular-energy expectation:
#print axioms QIQTH.StandardSubspaceModular.kFn_eq_neg_entropyDensity
#print axioms QIQTH.StandardSubspaceModular.cgpEntropy_eq_integral_kFn
-- Type II crossed product 1a-0: modular automorphism σ_t = one-param group of unital *-homs (action to cross):
#print axioms QIQTH.StandardSubspaceModular.modularAut_mul
#print axioms QIQTH.StandardSubspaceModular.modularAut_add
#print axioms QIQTH.StandardSubspaceModular.modularAut_star
-- The Wall Phase 1.1: the matter-rep fiber s↦σ_{-s}(a)(ξ s) is AEStronglyMeasurable on L²(ℝ;H):
#print axioms QIQTH.StandardSubspaceModular.aesm_matterFiber
-- The Wall Phase 1.2: π(a)ξ ∈ L²(ℝ;H) — the fiber is L² (contraction bound ‖σ_{-s}(a)v‖ ≤ ‖a‖‖v‖):
#print axioms QIQTH.StandardSubspaceModular.memLp_matterFiber
-- The Wall Phase 1.2/1.3: π(a) is a bounded operator (‖π(a)‖≤‖a‖) + a unital algebra homomorphism M→B(L²(ℝ;H)):
#print axioms QIQTH.StandardSubspaceModular.matterRep
#print axioms QIQTH.StandardSubspaceModular.matterRep_one
#print axioms QIQTH.StandardSubspaceModular.matterRep_mul
#print axioms QIQTH.StandardSubspaceModular.modularAut_adjoint
-- The Wall Phase 2: the clock translation unitary group λ_t on L²(ℝ;H) — λ_0=1, λ_{s+t}=λ_s λ_t, λ_t⁻¹=λ_{-t}, isometry:
#print axioms QIQTH.StandardSubspaceModular.clockTransl
#print axioms QIQTH.StandardSubspaceModular.clockTransl_coeFn
#print axioms QIQTH.StandardSubspaceModular.clockTransl_zero
#print axioms QIQTH.StandardSubspaceModular.clockTransl_add
#print axioms QIQTH.StandardSubspaceModular.clockTransl_comp_neg
#print axioms QIQTH.StandardSubspaceModular.clockTransl_neg_comp
-- The Wall Phase 3.1: the covariance λ_{-t} π(a) λ_t = π(σ_t a) — the defining crossed-product identity:
#print axioms QIQTH.StandardSubspaceModular.covariance
-- The Wall Phase 3.2: the (algebraic) crossed product M⋊_σℝ = ℂ-subalgebra generated by π(M) ∪ λ(ℝ):
#print axioms QIQTH.StandardSubspaceModular.matterRep_mem_crossedProduct
#print axioms QIQTH.StandardSubspaceModular.clockTransl_mem_crossedProduct
-- The Wall Phase 4.1: strong continuity of λ_t (the strongly-continuous one-parameter unitary group = Stone hypothesis):
#print axioms QIQTH.StandardSubspaceModular.clockTransl_stronglyContinuous
#print axioms QIQTH.StandardSubspaceModular.clockTransl_inner
-- ★ P4 WALL Phase 4.3 — the THIRD Stone hypothesis for the clock group: clockTransl_inner — ⟪λ_t a, λ_t b⟫=⟪a,b⟫
-- (λ_t a ℂ-linear isometry, via LinearIsometry.inner_map_map). The diamond-free UNITARY statement of the clock
-- group. With clockTransl_add (group law) + clockTransl_zero (λ_0=1), the three hypotheses of the general Stone
-- generator (QIQTH.Spectral.stoneGen) are now ALL in hand for clockTransl. Axiom-free.
#print axioms QIQTH.StandardSubspaceModular.clockEnergy_isFormalAdjoint_self
#print axioms QIQTH.StandardSubspaceModular.clockEnergy_norm_add_smul_I_sq
#print axioms QIQTH.StandardSubspaceModular.clockEnergy_norm_le_norm_add_smul_I
-- ★ P4 WALL Phase 4.3 — THE CLOCK ENERGY X AS A SYMMETRIC OPERATOR (concrete instantiation; Lp-wall CRACKED):
-- clockEnergy := stoneGen clockTransl = −i d/dt λ_t, the generator of the clock translation group on L²(ℝ;H), its
-- closure = A_edge. clockEnergy_isFormalAdjoint_self — X is symmetric (X⊆X† once dense); clockEnergy_norm_add_smul_I_sq
-- — Cayley estimate ‖(X+i)x‖²=‖Xx‖²+‖x‖²; clockEnergy_norm_le_norm_add_smul_I — X+i bounded below ⟹ injective.
-- All immediate instantiations of the general Stone lemmas (..._dom forms) for clockTransl_add/_zero/_inner. The
-- Lp-instance whnf divergence was DEFEATED via attribute [local irreducible] stoneGen stoneDomain + explicit ambient
-- (H := Lp H 2 volume). Axiom-free. (Essential self-adjointness = Range(X±i) dense = the carried analytic frontier.)
#print axioms QIQTH.Spectral.Multiplication.momentumOp_isFormalAdjoint_self
#print axioms QIQTH.Spectral.Multiplication.momentumOp_norm_add_smul_I_sq
#print axioms QIQTH.Spectral.Multiplication.momentumOp_norm_le_norm_add_smul_I
-- ★ P4 WALL — THE MOMENTUM OPERATOR P AS A SYMMETRIC OPERATOR (2nd of the 3 C₀ groups; same Lp-pattern):
-- momentumOp := stoneGen translationCLM = −i d/dt τ_t = −i d/dx, the generator of the L²(ℝ) translation group
-- e^{itP}. momentumOp_isFormalAdjoint_self — P symmetric; momentumOp_norm_add_smul_I_sq — Cayley estimate
-- ‖(P+i)x‖²=‖Px‖²+‖x‖²; momentumOp_norm_le_norm_add_smul_I — P+i bounded below ⟹ injective. Instantiations of the
-- general Stone lemmas for translationCLM_add/_zero/_inner (τ_t a ℂ-linear isometry). Lp-wall handled by the same
-- irreducible-stoneGen pattern. Axiom-free. (e.s.a. = Range(P±i) dense = the carried analytic frontier.)
#print axioms QIQTH.StandardSubspaceModular.modularGen_isFormalAdjoint_self
#print axioms QIQTH.StandardSubspaceModular.modularGen_norm_add_smul_I_sq
#print axioms QIQTH.StandardSubspaceModular.modularGen_norm_le_norm_add_smul_I
-- ★ P4 WALL — THE MODULAR HAMILTONIAN K AS A SYMMETRIC OPERATOR (3rd & last of the 3 C₀ groups):
-- modularGen := stoneGen (modUnitary S) = −i d/dt Δ^{it}, the generator of the one-particle modular flow Δ^{it},
-- = the K of JLMS K̃ = A_edge·(1/4ℓ_P²) + K_bulk. modularGen_isFormalAdjoint_self — K symmetric;
-- modularGen_norm_add_smul_I_sq — Cayley estimate ‖(K+i)x‖²=‖Kx‖²+‖x‖²; modularGen_norm_le_norm_add_smul_I — K+i
-- bounded below ⟹ injective. Instantiations of the general Stone lemmas for modUnitary_compL/_zero/inner_modUnitary_self
-- (the latter derived from modUnitary_adjoint). modUnitary lives on the ABSTRACT one-particle space (not Lp), so NO
-- irreducible/Lp workaround needed. Axiom-free. (e.s.a. = Range(K±i) dense = the carried analytic frontier.)
#print axioms QIQTH.Spectral.mollify_integrable
#print axioms QIQTH.Spectral.mollify_apply_flow
#print axioms QIQTH.Spectral.mollify_apply_flow_cov
-- mollify_apply_flow_cov — the orbit in DIFFERENTIATION-READY form: U_s x_φ = ∫ φ(u−s) U_u x du (change of
-- variables u=s+t, integral_add_right_eq_self). Now the s-dependence sits ENTIRELY in the smooth scalar φ(u−s);
-- the U_u x factor is s-independent ⟹ ready for differentiation under the integral (d/ds|₀ = −∫ φ'(u) U_u x du).
#print axioms QIQTH.Spectral.mollify_integrand_hasDerivAt
-- mollify_integrand_hasDerivAt — the CALCULUS CORE of the differentiation step (the h_diff hypothesis of
-- hasDerivAt_integral_of_dominated_loc_of_deriv_le): for φ∈C¹, σ↦φ(u−σ)•U_u x has derivative −φ'(u−σ₀)•U_u x at σ₀
-- (chain rule HasDerivAt.scomp on the inner u−σ, then HasDerivAt.smul_const by U_u x). Axiom-free.
#print axioms QIQTH.Spectral.mollify_shifted_aestronglyMeasurable
#print axioms QIQTH.Spectral.mollify_deriv_aestronglyMeasurable
#print axioms QIQTH.Spectral.mollify_neg_deriv_eq
-- the remaining (easy) differentiation hypotheses + the derivative-value identification:
-- mollify_shifted_aestronglyMeasurable (hF_meas, ∀σ) + mollify_deriv_aestronglyMeasurable (hF'_meas) — the
-- integrands are continuous ⟹ AEStronglyMeasurable. mollify_neg_deriv_eq — ∫(−φ'(u))•U_u x = −mollify U φ' x:
-- the would-be derivative of U_s x_φ is again a GÅRDING vector (−x_{φ'}), so the smooth subspace is closed under
-- the generator. Axiom-free. With mollify_integrable (hF_int) + mollify_integrand_hasDerivAt (h_diff), the ONLY
-- remaining hypothesis of hasDerivAt_integral_of_dominated_loc_of_deriv_le is the integrable dominating bound
-- supₛ|φ'(u−s)|·‖x‖ (compact support of φ' ⟹ indicator of a compact set) — the carried analytic gap.
#print axioms QIQTH.Spectral.exists_norm_le_of_compactSupport
#print axioms QIQTH.Spectral.exists_support_subset_of_compactSupport
-- the two compact-support consequences the dominating bound C·M·𝟙_K rests on: exists_norm_le_of_compactSupport —
-- φ' bounded (C=‖φ'‖_∞, via Continuous.bddAbove_range_of_hasCompactSupport); exists_support_subset_of_compactSupport
-- — φ' vanishes outside a ball {|y|≤ρ} (tsupport bounded + image_eq_zero_of_notMem_tsupport). Axiom-free.
-- Assembling bound := C·M·𝟙_{closedBall(ρ+nbhd)} (integrable: compact ⟹ finite measure) + applying the diff lemma
-- ⟹ x_φ ∈ stoneDomain U is the remaining step.
#print axioms QIQTH.Spectral.integrable_indicator_closedBall_const
#print axioms QIQTH.Spectral.mollify_orbit_hasDerivAt
#print axioms QIQTH.Spectral.mollify_mem_stoneDomain
-- ★★ P4 WALL MILESTONE — GÅRDING DIFFERENTIATION DONE ⟹ THE SMOOTH DOMAIN IS NONEMPTY:
-- integrable_indicator_closedBall_const — the dominating bound C·M·𝟙_{closedBall} is integrable (compact ⟹ finite
-- measure). mollify_orbit_hasDerivAt — the orbit s↦∫φ(u−s)U_u x du is differentiable at 0 with derivative
-- ∫(−φ'(u))U_u x du, via hasDerivAt_integral_of_dominated_loc_of_deriv_le with the bound C·M·𝟙_K (domination = case
-- split on |u|≤ρ+1; needs uniform ‖U_u x‖≤M). mollify_mem_stoneDomain — mollify U φ x ∈ stoneDomain U: the orbit
-- U_s x_φ = ∫φ(u−s)U_u x du (mollify_apply_flow_cov) is differentiable ⟹ x_φ in the smooth domain. THE SMOOTH
-- DOMAIN OF THE STONE GENERATOR IS NONEMPTY (contains every Gårding vector) — the hardest analytic step of e.s.a.
-- is done. Axiom-free. Remaining: DENSITY {x_φ} dense (φ→δ) ⟹ Range(A±i) dense ⟹ A essentially self-adjoint.
#print axioms QIQTH.Spectral.mollify_sub
#print axioms QIQTH.Spectral.norm_mollify_sub_le
-- ★ P4 WALL — the GÅRDING-APPROXIMATION identity (toward density of the smooth domain): mollify_sub —
-- x_φ − (∫φ)·x = ∫ φ(t)(U_t x − x) dt (subtract the constant field (∫φ)·x = ∫ φ(t)·x via integral_smul_const,
-- combine via integral_sub). norm_mollify_sub_le — ‖x_φ − (∫φ)·x‖ ≤ ∫ ‖φ(t)‖·‖U_t x − x‖ (norm_integral_le_integral_norm).
-- With ∫φ=1 and φ≥0 concentrated near 0, the bound → 0 by strong continuity (U_t x → x) ⟹ x_φ → x. Axiom-free.
-- Remaining: the Dirac-sequence limit + concluding {x_φ} dense (hence the smooth domain dense) ⟹ e.s.a.
#print axioms QIQTH.Spectral.norm_mollify_sub_le_uniform
-- ★ P4 WALL — the GÅRDING ε-BOUND: norm_mollify_sub_le_uniform — if ‖U_t x − x‖ ≤ ε wherever φ(t)≠0 (on supp φ),
-- then ‖x_φ − (∫φ)·x‖ ≤ ε·∫‖φ‖ (pointwise integrand bound ‖φ t‖·‖U_t x−x‖ ≤ ε·‖φ t‖ + integral_mono + integral_const_mul).
-- For a Dirac sequence (∫|φ|=1, φ supported near 0) this is ≤ ε → 0 by strong continuity ⟹ x_φ → x. Axiom-free.
-- Remaining: pick the bump sequence φₙ → δ + the limit ⟹ {x_φ} dense ⟹ smooth domain dense ⟹ e.s.a.
#print axioms QIQTH.Spectral.exists_mem_stoneDomain_norm_sub_le
-- ★ P4 WALL — the DENSITY ASSEMBLY: exists_mem_stoneDomain_norm_sub_le — combines mollify_mem_stoneDomain (Gårding
-- vector ∈ smooth domain) + norm_mollify_sub_le_uniform (the ε-bound): a normalized C¹_c mollifier φ averaging to x
-- ((∫φ)·x=x) and supported where ‖U_t x−x‖≤ε gives y=x_φ ∈ stoneDomain U with ‖y−x‖ ≤ ε·∫‖φ‖. With a Dirac bump
-- (∫‖φ‖=1, support shrinking) ⟹ for every x,ε a smooth-domain vector within ε ⟹ DENSITY of the smooth domain.
-- Axiom-free. Only missing piece: supplying the bump (Mathlib ContDiffBump.normed: C^∞, ∫=1, ≥0, compact support).
#print axioms QIQTH.Spectral.exists_delta_norm_sub_lt
#print axioms QIQTH.Spectral.stoneDomain_dense
-- ★★★ P4 WALL MILESTONE — THE SMOOTH DOMAIN OF THE STONE GENERATOR IS DENSE: stoneDomain_dense — for a contractive
-- strongly-continuous family (U_0=1, ‖U_t y‖≤‖y‖, t↦U_t y continuous), Dense (stoneDomain U). Proof: exists_delta_
-- norm_sub_lt (strong continuity ⟹ δ with ‖U_t x−x‖<r/2 for |t|<δ) + a normalized C^∞ bump (ContDiffBump.normed,
-- ℝ→ℂ coerced) supported in (−δ/2,δ/2) fed to exists_mem_stoneDomain_norm_sub_le ⟹ a Gårding vector x_φ ∈ stoneDomain
-- with ‖x_φ−x‖ ≤ (r/2)·1 < r. THE ENTIRE GÅRDING-DENSITY ARGUMENT IS NOW MACHINE-CHECKED, AXIOM-FREE. This
-- discharges the density hypothesis of stoneGen_le_adjoint — the last analytic input to essential self-adjointness
-- of the Stone generator (X=A_edge, P, K). Remaining: wire density+symmetry ⟹ IsSelfAdjoint closure ⟹ Stone (Cayley).
#print axioms QIQTH.Spectral.stoneGen_subset_adjoint
-- ★★ P4 WALL — A⊆A† UNCONDITIONAL: stoneGen_subset_adjoint — stoneGen U ≤ (stoneGen U)† for a contractive
-- one-parameter UNITARY group, combining stoneGen_le_adjoint (the conditional A⊆A†, needing smooth-domain density)
-- with stoneDomain_dense (which DISCHARGES that density). The symmetric densely-defined generator is contained in
-- its LinearPMap adjoint — the textbook "symmetric operator" with the density hypothesis no longer carried.
-- Axiom-free. Self-adjointness Ā=Ā† of the closure then follows from the Cayley/Range(A±i)-dense criterion.
#print axioms QIQTH.Spectral.stoneGen_isClosable
-- ★ P4 WALL — CLOSABILITY (the closure Ā exists): stoneGen_isClosable — (stoneGen U).IsClosable for a contractive
-- unitary group. The symmetric densely-defined generator has a closed extension — its adjoint A† (closed by
-- LinearPMap.adjoint_isClosed, given the smooth domain is dense via stoneDomain_dense) — and A⊆A†
-- (stoneGen_subset_adjoint), so A is closable (IsClosable.leIsClosable). Prerequisite for forming Ā = closure and
-- asking Ā=Ā† (self-adjointness). Axiom-free. Remaining: Range(A±i) dense ⟹ Ā=Ā† (the Cayley criterion, Mathlib gap).
#print axioms QIQTH.Spectral.resolvent_integrand_integrableOn
-- ★ P4 WALL — the RESOLVENT foundation (toward Range(A±i) dense): resolvent U x := ∫₀^∞ e^{−t} U_t x dt = (1−iA)⁻¹ x.
-- resolvent_integrand_integrableOn — the half-line integrand e^{−t} U_t x is IntegrableOn (0,∞): exp decay e^{−t}
-- dominates the bounded orbit (‖U_t x‖≤‖x‖) and ∫₀^∞ e^{−t}<∞ (exp_neg_integrableOn_Ioi + Integrable.mono'). Axiom-free.
-- Foundation of the Range-density witness: formally ∫₀^∞ e^{−t}e^{itA}dt = (1−iA)⁻¹ ⟹ −i(A+i) surjective ⟹ Range(A+i)=H.
-- Remaining (Mathlib-grade op-theory frontier): R x ∈ stoneDomain + the resolvent identity (A+i)(R x)=i x ⟹ Range dense.
#print axioms QIQTH.Spectral.norm_resolvent_le
-- ★ P4 WALL — the RESOLVENT IS A CONTRACTION: norm_resolvent_le — ‖R x‖ ≤ ‖x‖ (‖e^{−t}U_t x‖ ≤ e^{−t}‖x‖,
-- ∫₀^∞ e^{−t}=1 via integral_exp_neg_Ioi_zero + setIntegral_mono_on + norm_integral_le_integral_norm). R=(1−iA)⁻¹
-- is a bounded operator (norm ≤1) ⟹ 1−iA = −i(A+i) has a bounded right inverse, the step giving Range(A+i)=H. Axiom-free.
#print axioms QIQTH.Spectral.resolvent_apply_flow
-- ★ P4 WALL — the FLOW-ON-RESOLVENT identity: resolvent_apply_flow — U_s (R x) = ∫₀^∞ e^{−t} U_{s+t} x dt (U_s
-- through the set Bochner integral via integral_comp_comm + ContinuousLinearMap.map_smul_of_tower for the ℝ-smul +
-- group law). The algebraic core of the resolvent identity: after the change of variables u=s+t (giving
-- e^s ∫_s^∞ e^{−u}U_u x du), differentiating in s at 0 yields R x − x by the FTC ⟹ (A+i)(R x)=i x ⟹ Range(A+i)=H. Axiom-free.
#print axioms QIQTH.Spectral.resolvent_add
#print axioms QIQTH.Spectral.resolvent_smul
-- ★ P4 WALL — the RESOLVENT IS ℂ-LINEAR: resolvent_add (R(x+y)=Rx+Ry, integral_add + U_t linear) + resolvent_smul
-- (R(c•x)=c•Rx, integral_smul + map_smul + smul_comm). With norm_resolvent_le (‖Rx‖≤‖x‖), R = (1−iA)⁻¹ is a bounded
-- ℂ-linear operator. Axiom-free. Remaining: the resolvent identity (A+i)(R x)=i x (FTC differentiation) ⟹ Range(A+i)=H.
#print axioms QIQTH.Spectral.resolvent_comm_flow
-- ★ P4 WALL — the RESOLVENT COMMUTES WITH THE FLOW: resolvent_comm_flow — U_s (R x) = R (U_s x), from
-- resolvent_apply_flow (U_s(Rx)=∫₀^∞ e^{−t}U_{s+t}x) and R(U_s x)=∫₀^∞ e^{−t}U_t(U_s x)=∫₀^∞ e^{−t}U_{t+s}x (group
-- law), equal since U_{s+t}=U_{t+s}. So R commutes with U_s hence with the generator A — a resolvent/spectral
-- consistency property. Axiom-free.
#print axioms QIQTH.Spectral.resolvent_apply_flow_cov
-- ★ P4 WALL — the RESOLVENT ORBIT in DIFFERENTIATION-READY form: resolvent_apply_flow_cov —
-- U_s (R x) = e^s • ∫_s^∞ e^{−u} U_u x du. Change of variables u=s+t (MeasurePreserving.setIntegral_preimage_emb for
-- the translation, preimage (·+s)⁻¹(Ioi s)=Ioi 0, + integral_smul + the exponent algebra e^s·e^{−(t+s)}=e^{−t}).
-- Now the s-dependence sits in the smooth e^s factor and the integration LIMIT s only ⟹ the FTC for the improper
-- integral with variable lower limit gives d/ds|₀ = R x − x ⟹ R x ∈ stoneDomain + the resolvent identity (A+i)(R x)=i x. Axiom-free.
#print axioms QIQTH.Spectral.resolvent_integrand_integrableOn_Ioi
#print axioms QIQTH.Spectral.resolvent_halfline_hasDerivAt
-- ★ P4 WALL — the FTC for the resolvent's half-line integral: resolvent_halfline_hasDerivAt —
-- d/ds ∫_s^∞ e^{−u}U_u x du = −(e^{−s} U_s x). Via the splitting ∫_{Ioi s}=∫_{Ioi s₀}−∫_{s₀}^s
-- (intervalIntegral.integral_Ioi_sub_Ioi', needing resolvent_integrand_integrableOn_Ioi for any lower limit) + the
-- fundamental theorem of calculus (intervalIntegral.integral_hasDerivAt_right, integrand continuous) + HasDerivAt.congr.
-- The G'(s) feeding the product rule d/ds(e^s G(s))|₀ = R x − x ⟹ R x ∈ stoneDomain + (A+i)(R x)=i x. Axiom-free.
#print axioms QIQTH.Spectral.resolvent_orbit_hasDerivAt
#print axioms QIQTH.Spectral.resolvent_mem_stoneDomain
#print axioms QIQTH.Spectral.resolvent_stoneGen
-- ★★ P4 WALL MILESTONE — THE RESOLVENT IDENTITY (A+i)(R x)=i x: resolvent_orbit_hasDerivAt — d/ds U_s(R x)|₀ = R x − x
-- (product rule (Real.hasDerivAt_exp 0).smul on the e^s G(s) form + resolvent_apply_flow_cov + resolvent_halfline_hasDerivAt
-- + U_0=1). resolvent_mem_stoneDomain — R x ∈ stoneDomain U (orbit differentiable ⟹ the resolvent maps H INTO the
-- generator's domain). resolvent_stoneGen — stoneGen U (R x) = −i(R x − x) (generator identification), i.e.
-- (A+i)(R x)=i x ⟹ Range(A+i) ⊇ {i x}=H. The deficiency-index-zero fact that makes A essentially self-adjoint. Axiom-free.
#print axioms QIQTH.Spectral.stoneGen_add_I_surjective
-- ★★ P4 WALL — A+i IS SURJECTIVE (Range(A+i)=H): stoneGen_add_I_surjective — ∀ y, ∃ z ∈ stoneDomain, A z + i z = y,
-- witnessed by z := R(−i y): (A+i)(R(−i y)) = i(−i y) = y (resolvent_stoneGen + the i·(−i)=1 algebra). So the
-- deficiency subspace Range(A+i)^⊥ = ker(A†−i) = 0 — the essential-self-adjointness criterion (with the A−i mirror)
-- for the Stone generator. Axiom-free.
#print axioms QIQTH.Spectral.stoneGen_reversed_eq
#print axioms QIQTH.Spectral.stoneGen_sub_I_surjective
-- ★★ P4 WALL MILESTONE — BOTH DEFICIENCY INDICES ZERO (Range(A±i)=H): the reversed group t↦U_{−t} has generator −A
-- (stoneGen_reversed_eq, via hasDerivAt_stoneGen_neg + mem_stoneDomain_reversed/of_reversed); applying
-- stoneGen_add_I_surjective to it + the bridge gives stoneGen_sub_I_surjective — ∀ y, ∃ z ∈ stoneDomain, A z − i z = y,
-- i.e. Range(A−i)=H. With Range(A+i)=H (stoneGen_add_I_surjective), BOTH deficiency indices of the symmetric generator
-- A = stoneGen U vanish ⟹ the essential-self-adjointness criterion is met. Axiom-free. Remaining (Mathlib gap):
-- bundle the deficiency facts ⟹ Ā=Ā† (IsSelfAdjoint) ⟹ Cayley transform / unbounded spectral theorem ⟹ Stone.
#print axioms QIQTH.Spectral.deficiency_add_trivial
#print axioms QIQTH.Spectral.deficiency_sub_trivial
-- ★★ P4 WALL — the DEFICIENCY SUBSPACES ARE TRIVIAL (canonical inner-product form of n±=0): deficiency_add_trivial /
-- deficiency_sub_trivial — if ⟪(A±i)x, y⟫=0 ∀x∈domain (y ⊥ Range(A±i)) then y=0. From surjectivity (Range(A±i)=H):
-- y=(A±i)z ⟹ ⟪y,y⟫=0 ⟹ y=0 (inner_self_eq_zero). I.e. ker(A†∓i)=Range(A±i)^⊥=0 — the textbook essential-self-adjointness
-- criterion's content, now machine-checked. Axiom-free. Remaining (Mathlib gap): the criterion ⟹ Ā=Ā† (Cayley/spectral thm).
#print axioms QIQTH.Spectral.ker_adjoint_sub_I_trivial
#print axioms QIQTH.Spectral.ker_adjoint_add_I_trivial
-- ★★ P4 WALL — A† HAS NO ±i-EIGENVECTORS (the e.s.a. criterion in adjoint form): ker_adjoint_sub_I_trivial /
-- ker_adjoint_add_I_trivial — if (stoneGen U).adjoint ⟨w,hw⟩ = ±i•w then w=0. Via the formal-adjoint relation
-- ⟪A z, w⟫ = ⟪z, A† w⟫ (adjoint_isFormalAdjoint.symm), A†w=±iw gives ⟪(A∓i)z, w⟫=0 ∀z ⟹ w ⊥ Range(A∓i)=H ⟹ w=0
-- (deficiency_add/sub_trivial). So ker(A†∓i)=0 in Mathlib's LinearPMap.adjoint API — the EXACT hypothesis the
-- self-adjointness criterion (A⊆A† + ker(A†∓i)=0 ⟹ Ā=Ā†) consumes. Axiom-free. Remaining (Mathlib gap): the criterion
-- itself (Cayley transform) + the unbounded spectral theorem ⟹ Stone.
#print axioms QIQTH.Spectral.stoneGen_isSelfAdjoint
-- ★★★ P4 WALL MILESTONE — THE STONE GENERATOR IS SELF-ADJOINT: stoneGen_isSelfAdjoint — IsSelfAdjoint (stoneGen U),
-- i.e. (stoneGen U).adjoint = stoneGen U, for a contractive strongly-continuous one-parameter UNITARY group. The
-- BASIC criterion for self-adjointness (symmetric A⊆A† + Range(A±i)=H ⟹ A=A†, NO Cayley transform needed): A⊆A†
-- (stoneGen_subset_adjoint) + LinearPMap.eq_of_le_of_domain_eq, with the domain equality from surjectivity
-- (stoneGen_add_I_surjective) + ker(A†+i)=0 (ker_adjoint_add_I_trivial): for y∈dom(A†), ∃z∈dom(A) with (A+i)z=(A†+i)y,
-- then A†(y−z)=−i(y−z) ⟹ y=z∈dom(A). The generator of a unitary group is a GENUINE SELF-ADJOINT UNBOUNDED OPERATOR
-- — the spectral theorem's hypothesis, machine-checked. Axiom-free. Remaining (Mathlib gap): unbounded spectral
-- theorem (PVM via the now-self-adjoint A) ⟹ Stone U_t = exp(it A); applies to X=A_edge, P, K.
#print axioms QIQTH.StandardSubspaceModular.clockEnergy_isSelfAdjoint
#print axioms QIQTH.Spectral.Multiplication.momentumOp_isSelfAdjoint
#print axioms QIQTH.StandardSubspaceModular.modularGen_isSelfAdjoint
-- ★★★ P4 WALL — THE THREE NAMED GENERATORS ARE SELF-ADJOINT (concrete payoff of stoneGen_isSelfAdjoint):
-- clockEnergy_isSelfAdjoint — X = A_edge = stoneGen clockTransl (the clock energy, Lp ℂ²(ℝ;H), irreducible-stoneGen
-- pattern); momentumOp_isSelfAdjoint — P = stoneGen translationCLM = −i d/dx (L²(ℝ)); modularGen_isSelfAdjoint —
-- K = stoneGen (modUnitary S) = the JLMS modular Hamiltonian (abstract one-particle space). Each instantiates
-- stoneGen_isSelfAdjoint with the group's (∘L group law, U_0=1, unitarity, isometry/norm, strong continuity). All
-- three are GENUINE SELF-ADJOINT UNBOUNDED OPERATORS. Axiom-free. Remaining (Mathlib gap): unbounded spectral theorem.
#print axioms QIQTH.Spectral.Multiplication.translationCLM_norm_le
#print axioms QIQTH.Spectral.Multiplication.translationCLM_continuous
#print axioms QIQTH.Spectral.Multiplication.instNontrivialLp2
-- ★★★ P4 WALL — UPDATE: the "unbounded spectral theorem" gap above is now substantially addressed via the Cayley/cfc
-- route (QIQTH.Spectral.stoneGen_cfc_h_mul): the self-adjoint generators ALSO act as MULTIPLICATION BY THE SPECTRAL
-- VALUE c on the cfc core — the spectral content WITHOUT a PVM. translationCLM_norm_le/_continuous (the hUbd/hSC named
-- hypotheses) + instNontrivialLp2 (L²(ℝ) nontrivial) are the prerequisites for instantiating stoneGen_cfc_h_mul on
-- translationCLM (P = mult by c); the instantiation itself is checkpointed (Lp cfc-coercion plumbing, see
-- MomentumGenerator.lean). So X = A_edge (clockEnergy_isSelfAdjoint, self-adjoint) + the spectral action are BOTH done.
#print axioms QIQTH.Spectral.cayley_isStarNormal
#print axioms QIQTH.Spectral.nonneg_re_inner_nonneg
#print axioms QIQTH.Spectral.cayley_cfc_id
#print axioms QIQTH.Spectral.cayley_cfc_one
#print axioms QIQTH.Spectral.cayley_cfc_sq_re_inner_nonneg
#print axioms QIQTH.Spectral.cayley_cfc_re_inner_nonneg_of_nonneg
#print axioms QIQTH.Spectral.cayley_cfc_re_inner_add
#print axioms QIQTH.Spectral.cayley_cfc_re_inner_smul
#print axioms QIQTH.Spectral.expectationCLM
#print axioms QIQTH.Spectral.reExpectationCLM
#print axioms QIQTH.Spectral.cfcReExpectationCLM
#print axioms QIQTH.Spectral.realCfcReExpectationCLM
#print axioms QIQTH.Spectral.realCfcReExpectation_nonneg
#print axioms QIQTH.Spectral.cfcPLM
#print axioms QIQTH.Spectral.cfcPLMcc
#print axioms QIQTH.Spectral.cayleyScalarMeasure
#print axioms QIQTH.Spectral.cayleyScalarMeasure_integral
#print axioms QIQTH.Spectral.cayleyScalarMeasure_integral_C
#print axioms QIQTH.Spectral.integral_re_cfc_ofReal
-- ★★ P4 WALL — THE FUNCTION-FORM CFC↔MEASURE BRIDGE: integral_re_cfc_ofReal [Nontrivial H] —
-- re⟪x, cfc (↑∘r) V x⟫ = ∫ ω, r ω.1 dμ_x for r : ℂ→ℝ continuous on σ(V). Via cfc_eq_cfcL (cfc(↑∘r)V = cfcL ha
-- (restrict(↑∘r)) = cfcL ha (↑∘(r∘↑)), defeq) + cayleyScalarMeasure_integral_C. Bridges the function-form cfc
-- (operator-side identities) to the μ_x-integral (measure side) — the recurring dictionary entry, e.g. turns
-- cayley_cfc_sub_norm_sq into the genuine L² identity ‖cfc f V x − cfc g V x‖² = ∫|f−g|² dμ_x. Axiom-free.
-- ★ P4 WALL — INTEGRAL IDENTITY ON C(σV,ℝ) (compact-domain wrapper; CFC-bridge piece, GPT-5.5-pro recipe):
-- cayleyScalarMeasure_integral_C [Nontrivial H] — ∫ h dμ_x = re⟪x, cfcL ha (↑∘h) x⟫ for h : C(σV,ℝ) (continuous;
-- compact σV ⟹ compactly supported via continuousMapEquiv, so the C_c identity transports to C). Removes the C_c
-- plumbing from the function-form CFC bridge re⟪x, cfc g V x⟫ = ∫(g∘↑) dμ_x consumed by the Stone/Parseval build.
-- Axiom-free.
#print axioms QIQTH.Spectral.cayleyScalarMeasure_isFiniteMeasure
#print axioms QIQTH.Spectral.cayleyScalarMeasure_univ
#print axioms QIQTH.Spectral.cayleyScalarMeasure_isProbabilityMeasure
#print axioms QIQTH.Spectral.cayley_norm_cfc_le
#print axioms QIQTH.Spectral.cayley_cfc_isSelfAdjoint
#print axioms QIQTH.Spectral.cayley_cfc_inner_self_im_zero
#print axioms QIQTH.Spectral.cayley_norm_inner_cfc_le
#print axioms QIQTH.Spectral.cayley_cfc_inner_polarization
#print axioms QIQTH.Spectral.cayleyScalarMeasure_le_norm_sq
#print axioms QIQTH.Spectral.cayleyScalarMeasure_union
#print axioms QIQTH.Spectral.cayley_cfc_norm_sq
#print axioms QIQTH.Spectral.cayley_cfc_sub_norm_sq
#print axioms QIQTH.Spectral.cayley_cfc_sub_norm_sq_integral
#print axioms QIQTH.Spectral.cayley_cfc_norm_sq_integral
#print axioms QIQTH.Spectral.cayley_cfc_tendsto_zero_of_integral
#print axioms QIQTH.Spectral.cayley_cfc_cauchySeq_of_integral
#print axioms QIQTH.Spectral.cayley_defect_energy
#print axioms QIQTH.Spectral.cayleyCutoff_pos
#print axioms QIQTH.Spectral.cayleyCutoff_le_one
#print axioms QIQTH.Spectral.cayleyCutoff_continuous
#print axioms QIQTH.Spectral.cayleyCutoff_tendsto_zero_of_ne
#print axioms QIQTH.Spectral.cayleyCutoff_tendsto_indicator
#print axioms QIQTH.Spectral.cayleyCutoff_sq_mul_tendsto_zero
#print axioms QIQTH.Spectral.cayleyCutoff_integral_tendsto_atom
#print axioms QIQTH.Spectral.cayleyCutoff_defect_integral_tendsto_zero
#print axioms QIQTH.Spectral.cayleyCutoff_sub_indicator_sq_tendsto_zero
#print axioms QIQTH.Spectral.cayleyCutoff_L2_tendsto_zero
#print axioms QIQTH.Spectral.cayleyCutoff_cfc_cauchySeq
#print axioms QIQTH.Spectral.cayleyCutoff_cfc_tendsto_zero
#print axioms QIQTH.Spectral.cayleyScalarMeasure_atom_eq_zero
#print axioms QIQTH.Spectral.cayleyInv_continuousOn
#print axioms QIQTH.Spectral.cayleyInv_im_eq_zero
#print axioms QIQTH.Spectral.cayleyExp_continuousOn
#print axioms QIQTH.Spectral.cayleyExp_abs
#print axioms QIQTH.Spectral.cayleyExp_zero
#print axioms QIQTH.Spectral.cayleyExp_add
#print axioms QIQTH.Spectral.cayleyBump_continuous
#print axioms QIQTH.Spectral.cayleyBump_nonneg
#print axioms QIQTH.Spectral.cayleyBump_le_one
#print axioms QIQTH.Spectral.cayleyBump_tendsto_indicator
#print axioms QIQTH.Spectral.cayleyExp_abs_circle
#print axioms QIQTH.Spectral.cayleyExpBump_sub_norm
#print axioms QIQTH.Spectral.cayleyCutoff_sq_integral_tendsto_zero
#print axioms QIQTH.Spectral.cayleyExpBump_L2_tendsto_zero
#print axioms QIQTH.Spectral.cayleyExpBump_norm
#print axioms QIQTH.Spectral.cayleyExpBump_continuousOn
#print axioms QIQTH.Spectral.cayleyExpBump_cfc_cauchySeq
#print axioms QIQTH.Spectral.cayleyStoneU_tendsto
#print axioms QIQTH.Spectral.cayleyStoneU_add
#print axioms QIQTH.Spectral.cayleyStoneU_smul
#print axioms QIQTH.Spectral.cayleyStoneU_zero
#print axioms QIQTH.Spectral.cayleyBump_sq_integral_tendsto
#print axioms QIQTH.Spectral.cayleyStoneU_isometry
#print axioms QIQTH.Spectral.cayleyStoneLI
#print axioms QIQTH.Spectral.cayleyStoneCLM
#print axioms QIQTH.Spectral.cayleyStoneCLM_apply
#print axioms QIQTH.Spectral.cayleyStoneCLM_norm_map
#print axioms QIQTH.Spectral.cayleyExpBump_cfc_norm_le
#print axioms QIQTH.Spectral.cayleyExpBump_cfc_comp
#print axioms QIQTH.Spectral.cayleyProdSymbol_cfc_tendsto
#print axioms QIQTH.Spectral.cayleyStoneU_group
#print axioms QIQTH.Spectral.cayleyStoneU_neg_left
#print axioms QIQTH.Spectral.cayleyStoneU_neg_right
#print axioms QIQTH.Spectral.cayleyStoneLIE
#print axioms QIQTH.Spectral.cayleyStoneLIE_apply
#print axioms QIQTH.Spectral.cayleyStoneU_sub_norm_sq
#print axioms QIQTH.Spectral.cayleyExp_measurable
#print axioms QIQTH.Spectral.cayleyStoneU_continuous
#print axioms QIQTH.Spectral.cayleyStoneU_comm_cayleyUnitary
#print axioms QIQTH.Spectral.cayleyStoneU_cfc
#print axioms QIQTH.Spectral.cayleyExp_hasDerivAt_zero
#print axioms QIQTH.Spectral.cayleyExp_hasDerivAt
#print axioms QIQTH.Spectral.cayleyExp_slope_tendsto
#print axioms QIQTH.Spectral.cayleyExp_sub_one_norm_le
#print axioms QIQTH.Spectral.cayleyInv_measurable
#print axioms QIQTH.Spectral.cayleyExp_gen_integrand_tendsto
#print axioms QIQTH.Spectral.cayleyStoneU_slope_norm_sq
#print axioms QIQTH.Spectral.cayleyStoneU_cfc_hasDerivAt
#print axioms QIQTH.Spectral.cayleyStoneCLM_cfc_mem_stoneDomain
#print axioms QIQTH.Spectral.cayleyStoneCLM_stoneGen_cfc
#print axioms QIQTH.Spectral.cayleyBump_cfc_tendsto
#print axioms QIQTH.Spectral.cayleyStoneCLM_zero
#print axioms QIQTH.Spectral.cayleyStoneCLM_comp
#print axioms QIQTH.Spectral.cayleyStoneCLM_inner
#print axioms QIQTH.Spectral.cayleyStoneCLM_norm_le
#print axioms QIQTH.Spectral.cayleyStoneCLM_continuous
#print axioms QIQTH.Spectral.cayley_resolvent_symbol_cfc
#print axioms QIQTH.Spectral.cayleyUnitary_eq_sub_two_resolvent
#print axioms QIQTH.Spectral.resolvent_eq_cfc
#print axioms QIQTH.Spectral.cfc_h_mul_eq_resolvent
#print axioms QIQTH.Spectral.cfc_h_mul_mem_stoneDomain
#print axioms QIQTH.Spectral.stoneGen_cfc_h_mul
-- ★★★★★ P4 WALL — THE DIRECT GENERATOR IDENTITY (the ORIGINAL group's generator = mult by the spectral value c):
-- stoneGen_cfc_h_mul [Nontrivial H] — stoneGen U ⟨cfc(h·ψ)V z, _⟩ = cfc(i(1+ω)/2·ψ)V z for ψ∈C(σV), h(ω)=(1−ω)/2.
-- Every cfc-core symbol φ with c·φ∈C(σV) factors as φ=h·ψ, and c·φ=c·h·ψ=i(1+ω)/2·ψ (c·h=i(1+ω)/2), so this IS
-- stoneGen U (cfc φ V z)=cfc(c·φ)V z — the generator of the ORIGINAL C₀ group U is multiplication by the spectral
-- value c, derived DIRECTLY from resolvent_stoneGen (no recovery / essential-self-adjointness). Proof: cfc(h·ψ)V z=
-- R(cfc ψ V z) (cfc_h_mul_eq_resolvent), resolvent_stoneGen gives −i(R w−w), and cfc-linearity + the pointwise ring
-- identity −i((1−ω)/2·ψ−ψ)=i(1+ω)/2·ψ closes it. cfc_h_mul_mem_stoneDomain: the core vector is in the smooth domain.
-- THE GPT-5.5-pro ROUTE TO X=A_edge IS COMPLETE on the abstract C₀ group — instantiate clockTransl ⟹ X=A_edge. Axiom-free.
-- ★★★★ P4 WALL — RESOLVENT = cfc(h) V (the bridge to the direct generator identity): cayleyUnitary_eq_sub_two_-
-- resolvent — V y = y − 2·R y (V=1−2R; via cayleyEquiv.symm y = −i·R y, LinearPMap.map_smul + resolvent_stoneGen);
-- resolvent_eq_cfc — resolvent U y = cfc((1−ω)/2) V y (combine V=1−2R with cfc((1−ω)/2)V=½(1−V)). This turns the
-- resolvent generator formula resolvent_stoneGen (stoneGen U (R x)=−i(Rx−x), original group) into a cfc-of-V
-- statement; factoring a symbol φ=h·ψ then yields the DIRECT identity stoneGen U (cfc φ V z)=cfc(c·φ)V z — the
-- ORIGINAL group's generator = mult by the spectral value c, sidestepping the recovery / e.s.a. wall. Axiom-free.
-- ★★★★ P4 WALL — RESOLVENT SYMBOL cfc (GPT-5.5-pro direct-identity route): cayley_resolvent_symbol_cfc —
-- cfc((1−ω)/2) V = ½(1−V) (pure cfc linearity: cfc_const_mul + cfc_sub + cayley_cfc_one/_id). With the resolvent↔
-- Cayley relation R=½(1−V) (V=1−2R, next) ⟹ resolvent U = cfc(h)V, h=(1−ω)/2 — the bridge from resolvent_stoneGen
-- (stoneGen U (Rx)=−i(Rx−x)) to the DIRECT identity stoneGen U (cfc φ V z)=cfc(c·φ)V z (factor φ=h·ψ), identifying
-- the ORIGINAL group's generator with mult-by-c WITHOUT the recovery / essential-self-adjointness wall. Axiom-free.
-- ★★★★ P4 WALL — cayleyStoneCLM IS A C₀ UNITARY GROUP: the reconstructed Stone group satisfies the five abstract
-- C₀-group hypotheses — cayleyStoneCLM_zero (U_0=1), _comp (U_{s+t}=U_s∘U_t, group law), _inner (preserves inner
-- product, it's the LinearIsometryEquiv cayleyStoneLIE), _norm_le (‖U_t y‖≤‖y‖), _continuous (strong continuity). So
-- cayleyStoneCLM is a bona-fide input to the Gårding/stoneGen machinery (density, the recovery cayleyStoneCLM U = U),
-- and the whole Stone construction can be iterated/fed back on the reconstructed group. Axiom-free.
-- ★★★★ P4 WALL — THE cfc CORE IS DENSE (approximate identity): cayleyBump_cfc_tendsto — cfc(η_N)V z → z, η_N=cayleyBump.
-- Since η_N=1−ψ_N, cfc(η_N)V z = z − cfc(ψ_N)V z (cfc_sub + cayley_cfc_one), and the atom-killing cfc(ψ_N)V z→0
-- (cayleyCutoff_cfc_tendsto_zero, μ_z({1})=0) gives z. The η_N vanish quadratically at the excluded point 1, so the
-- bump vectors cfc(η_N)V z are genuine spectral-core vectors → the smooth domain of the Stone group is DENSE: every z
-- is a limit of core vectors on which the generator acts as multiplication by the spectral value c. Axiom-free.
-- ★★★★★ P4 WALL — STONE'S CORRESPONDENCE PACKAGED: the generator of the reconstructed unitary group IS multiplication
-- by the spectral value. cayleyStoneCLM_cfc_mem_stoneDomain — cfc φ V z ∈ stoneDomain(cayleyStoneCLM) (differentiable
-- ⟹ in the smooth domain, via cayleyStoneCLM_apply). cayleyStoneCLM_stoneGen_cfc — stoneGen(cayleyStoneCLM)⟨cfc φ V z⟩
-- = cfc(c·φ)V z, identifying A x=−i d/dt U_t x|₀ with the Cayley self-adjoint A=i(1+V)(1−V)⁻¹ = mult by c=cayleyInv on
-- the cfc core (wraps cayleyStoneU_cfc_hasDerivAt with stoneGen_eq_of_hasDerivAt). U_t=exp(itA) is the Stone group of
-- its own generator — Stone's theorem BOTH DIRECTIONS on the cfc core. Axiom-free, no PVM, no UV datum.
-- ★★★★★ P4 WALL — THE GENERATOR ON THE cfc CORE (Stone's CONVERSE): cayleyStoneU_cfc_hasDerivAt [Nontrivial H] —
-- HasDerivAt (t↦U_t(cfc φ V z)) (i·cfc(c·φ)V z) 0, for φ, e_r·φ, c·φ ContinuousOn σ(V). On the spectral core the Stone
-- group U_t=exp(itA) is DIFFERENTIABLE in t, with d/dt|₀ = i·(mult by the spectral value c=cayleyInv) — i.e. the
-- GENERATOR A is multiplication by c (= i(1+V)(1−V)⁻¹). Proof: U_t(cfc φ Vz)=cfc(e_tφ)Vz (cayleyStoneU_cfc);
-- hasDerivAt_iff_tendsto_slope, the slope−deriv has norm→0 since its SQUARE = ∫‖((e_τ−1)/τ−ic)φ‖²dμ_z
-- (cayleyStoneU_slope_norm_sq, the cfc-algebra+Parseval bridge) → 0 (cayleyExp_gen_integrand_tendsto, the scalar DCT),
-- via √-continuity. The converse half of Stone for the Cayley/cfc construction — the group is exp of its own generator
-- on a core. cayleyStoneU_slope_norm_sq is the operator norm²=∫DCT identity (cfc_sub/cfc_const_mul + Parseval). Axiom-free.
-- ★★★★★ P4 WALL — THE SCALAR GENERATOR DCT (the analytic heart of the generator): cayleyExp_gen_integrand_tendsto
-- [Nontrivial H] — ∫‖((e_τ−1)/τ − i·c)·φ‖²dμ_z → 0 as τ→0 (τ≠0), for φ, c·φ ContinuousOn σ(V). The squared L²-norm of
-- the gap between the symbol difference quotient (e_τ·φ−φ)/τ and its formal limit i·c·φ, → 0 by dominated convergence
-- on 𝓝[≠]0 (tendsto_integral_filter_of_dominated_convergence): integrand → 0 a.e. (cayleyExp_slope_tendsto),
-- dominated by 4‖c·φ‖² (integrable, c·φ∈C(σV) bounded) via ‖(e_τ−1)/τ‖≤‖c‖ (cayleyExp_sub_one_norm_le). With Parseval
-- + the cfc-algebra this gives HasDerivAt(t↦U_t(cfc φ V z)) (i·cfc(c·φ)V z) 0 = the generator on the cfc core. Axiom-free.
-- ★★★★ P4 WALL — THE TWO GENERATOR-DCT INPUTS: cayleyExp_slope_tendsto — (e_t(ω)−1)/t → i·c(ω) as t→0
-- (the pointwise difference-quotient convergence, from cayleyExp_hasDerivAt_zero via hasDerivAt_iff_tendsto_slope);
-- cayleyExp_sub_one_norm_le — ‖e_t(ω)−1‖ ≤ |t|·‖c(ω)‖ on σ(V)⊆S¹ (c real there by cayleyInv_im_eq_zero, so
-- e_t=exp(i↑(t·c.re)) and ‖exp(iθ)−1‖≤|θ| via Real.norm_exp_I_mul_ofReal_sub_one_le). These are exactly the pointwise
-- limit + t-independent domination the generator's dominated-convergence pass on the cfc core consumes. Axiom-free.
-- ★★★★ P4 WALL — THE STONE SYMBOL DERIVATIVE (the pointwise generator): cayleyExp_hasDerivAt_zero — d/dt e_t(ω)|₀ =
-- i·c(ω) (e_0=1, c=cayleyInv the spectral value); cayleyExp_hasDerivAt — d/dt e_t(ω)|ₛ = e_s(ω)·i·c(ω) everywhere
-- (each fibre solves f'=(i·c)f). Via HasDerivAt.cexp on exp(i·t·c) + Complex.ofRealCLM.hasDerivAt. The fibrewise
-- generator is multiplication by i·c(ω) = spectral form of i·A; on the cfc core (cayleyStoneU_cfc) this gives, formally,
-- d/dt U_t(cfc φ V z)|₀ = cfc(i·c·φ)V z. Transferring through cfc uniformly on σ(V) is the remaining wall. Axiom-free.
-- ★★★★ P4 WALL — THE SPECTRAL ACTION OF THE STONE GROUP ON THE cfc CORE: cayleyStoneU_cfc [Nontrivial H] —
-- U_t (cfc φ V z) = cfc(e_t·φ) V z, for φ and every e_r·φ ContinuousOn σ(V) (e.g. φ vanishing at the excluded point 1).
-- The abstract strong-limit U_t acts by multiplying the symbol by e_t(ω)=exp(it·c(ω)): cfc(g_{t,N})V(cfc φ V z)=
-- cfc(g_{t,N}·φ)V z (cfc_mul) → U_t(cfc φ V z) (cayleyStoneU_tendsto), and cfc(g_{t,N}·φ)V z → cfc(e_t·φ)V z since the
-- L²-defect ∫‖(g_{t,N}−e_t)φ‖²=∫ψ_N²|φ|²≤M²∫ψ_N²→0 (M=sup|φ| on compact σ(V)); uniqueness. Identifies U_t with the
-- bounded-Borel functional calculus cfc(e_t·) on a core — the gateway to the generator (differentiate t↦U_t(cfc φ V z)). Axiom-free.
-- ★★★★ P4 WALL — THE STONE GROUP IS A FUNCTION OF V: cayleyStoneU_comm_cayleyUnitary [Nontrivial H] —
-- U_t (V y) = V (U_t y). Each cutoff cfc(g_{t,N})V commutes with V (function of V, Commute.cfc); pass to the strong
-- limit (cayleyStoneU_tendsto + V continuous). So U_t = exp(itA) lies in the abelian von Neumann algebra generated by
-- the Cayley unitary V — the precise sense in which the modular flow is generated by its own spectral data. Axiom-free.
-- ★★★★★ P4 WALL — STRONG CONTINUITY of the Stone group: cayleyStoneU_continuous [Nontrivial H] — Continuous(t↦U_t x).
-- By the limit Parseval ‖U_t x−U_s x‖=√(∫‖e_t−e_s‖²dμ_x), and ∫‖e_t−e_s‖²→0 as t→s by dominated convergence on the
-- countably-generated filter 𝓝 s (tendsto_integral_filter_of_dominated_convergence): e_t=exp(i t·c(ω)) is cont. in t
-- so ‖e_t−e_s‖²→0 pointwise, dominated by 4 (‖e_r‖=1 on σ(V)⊆S¹), AEStronglyMeasurable via cayleyExp_measurable (e_t
-- Borel: built from continuous ops + a complex division). With linearity/isometry/U_0=1/group law/unitarity, t↦U_t is
-- a STRONGLY CONTINUOUS ONE-PARAMETER GROUP OF UNITARIES — the unitary-group side of Stone's theorem, complete. Axiom-free.
-- ★★★★★ P4 WALL — THE LIMIT PARSEVAL FOR THE STONE GROUP: cayleyStoneU_sub_norm_sq [Nontrivial H] —
-- ‖U_t x − U_s x‖² = ∫‖e_t − e_s‖²dμ_x (e_r=cayleyExp r the bounded-Borel Stone symbol). Transports the L²-isometry
-- through the strong limit: ‖cfc(g_{t,N})Vx − cfc(g_{s,N})Vx‖²=∫‖g_{t,N}−g_{s,N}‖² (cayley_cfc_sub_norm_sq_integral),
-- LHS→‖U_t x−U_s x‖² (norm cont. along cayleyStoneU_tendsto), RHS→∫‖e_t−e_s‖² by DCT (g_{t,N}−g_{s,N}=η_N(e_t−e_s),
-- η_N²→1 a.e. since μ_x({1})=0, dominated by 4); uniqueness. The bridge to strong continuity (RHS→0 as t→s, 2nd DCT). Axiom-free.
-- ★★★★★ P4 WALL — U_t IS A UNITARY H ≃ₗᵢ[ℂ] H: cayleyStoneU_neg_left/right (U_{-t} is a two-sided inverse of U_t,
-- from cayleyStoneU_group + cayleyStoneU_zero, (-t)+t=0) ⟹ cayleyStoneLIE := the LinearIsometryEquiv bundling U_t as
-- a genuine unitary (cayleyStoneLIE_apply: acts as cayleyStoneU). The continuum Stone exponential t↦U_t=exp(itA) is
-- now a one-parameter GROUP OF UNITARIES — no PVM, no UV datum; only strong continuity + generator remain for Stone.
-- ★★★★★ P4 WALL — THE ONE-PARAMETER GROUP LAW U_s U_t = U_{s+t} (cayleyStoneU_group [Nontrivial H]): the missing
-- multiplicative structure of the continuum Stone exponential. With A_N:=cfc(g_{s,N})V, y_N:=cfc(g_{t,N})V x, the
-- composite A_N y_N → U_s(U_t x) [operator-limit: contraction cayleyExpBump_cfc_norm_le + cayleyStoneU_tendsto via
-- A_N y_N − U_s(U_t x)=A_N(y_N−U_t x)+(A_N(U_t x)−U_s(U_t x)), squeeze_zero_norm] AND A_N y_N=cfc(e_{s+t}η_N²)V x →
-- U_{s+t}x [cayleyExpBump_cfc_comp + cayleyProdSymbol_cfc_tendsto, the latter via ‖cfc(e_r η_N²)Vx−cfc(g_{r,N})Vx‖²=
-- ∫η_N²ψ_N²≤∫ψ_N²→0]; uniqueness ⟹ U_s(U_t x)=U_{s+t}x. t↦U_t is now a one-parameter group of isometries. Axiom-free.
-- ★★★★ P4 WALL — GROUP-LAW PREREQUISITES (toward U_s U_t = U_{s+t}): cayleyExpBump_cfc_norm_le — the cutoff cfc
-- operators are CONTRACTIONS ‖cfc(g_{t,N})V z‖≤‖z‖ (Parseval ∫‖g_{t,N}‖²=∫η_N²≤∫1=‖z‖², since η_N≤1); the uniform
-- operator bound the group-law operator-limit step consumes. cayleyExpBump_cfc_comp — cfc MULTIPLICATIVITY:
-- cfc(g_{s,N})V (cfc(g_{t,N})V x) = cfc(e_{s+t}·η_N²)V x (cfc_mul + e_s·e_t=e_{s+t}); the algebraic half of the group
-- law. Remaining: pass N→∞ (operator-limit of contractions on the left, e_{s+t}η_N²→e_{s+t} in L² on the right). Axiom-free.
-- ★★★★ P4 WALL — U_t BUNDLED AS A BOUNDED OPERATOR H →L[ℂ] H: cayleyStoneLI (the ℂ-linear isometry H →ₗᵢ[ℂ] H from
-- cayleyStoneU_add/_smul/_isometry) → cayleyStoneCLM := cayleyStoneLI.toContinuousLinearMap (the H →L[ℂ] H packaging
-- Stone consumes; cayleyStoneCLM_apply: acts as cayleyStoneU; cayleyStoneCLM_norm_map: ‖U_t x‖=‖x‖ at the operator
-- level). The one-parameter group t↦U_t now lives in H →L[ℂ] H where U_s U_t=U_{s+t} is operator composition. Axiom-free.
-- ★★★★ P4 WALL — ‖U_t x‖ = ‖x‖, THE STONE EXPONENTIAL IS AN ISOMETRY (2nd of 3 remaining unitary-group bricks):
-- cayleyStoneU_isometry [Nontrivial H]. By Parseval (cayley_cfc_norm_sq_integral) ‖cfc(g_{t,N})V x‖²=∫‖g_{t,N}‖²dμ_x,
-- and on σ(V)⊆S¹ ‖g_{t,N}(ω)‖=η_N(ω) (cayleyExpBump_norm, ‖e_t‖=1) so =∫η_N²dμ_x → ‖x‖² (cayleyBump_sq_integral_-
-- tendsto: ∫η_N²=∫(1−ψ_N)²=μ_x(σV).toReal−2∫ψ_N+∫ψ_N² → ‖x‖²−0+0, via cayleyScalarMeasure_univ + the two atom-killing
-- limits cayleyCutoff_integral_tendsto_atom/cayleyCutoff_sq_integral_tendsto_zero). The same sequence → ‖U_t x‖²
-- (norm continuous along cayleyStoneU_tendsto), so ‖U_t x‖²=‖x‖² by uniqueness ⟹ ‖U_t x‖=‖x‖ (Real.sqrt_sq). Axiom-free.
-- ★★★★ P4 WALL — U_0 = id (Stone group identity): cayleyStoneU_zero [Nontrivial H] — U_0 x = x. At t=0 the symbol
-- is e_0 ≡ 1 (cayleyExp_zero), so g_{0,N}=η_N=1−ψ_N and cfc(g_{0,N})V x = x − cfc(ψ_N)V x; the atom-killing limit
-- cfc(ψ_N)V x → 0 (cayleyCutoff_cfc_tendsto_zero, μ_x({1})=0) gives x−0=x by uniqueness of strong limits. The first
-- of the three remaining unitary-group bricks (U_0=1 ✓, isometry ‖U_t x‖=‖x‖, group law U_s U_t=U_{s+t}). Axiom-free.
-- ★★★★ P4 WALL — THE CONTINUUM STONE EXPONENTIAL U_t IS DEFINED: cayleyStoneU [Nontrivial H] U ... t x :=
-- lim_N cfc(g_{t,N}) V x (the strong limit, exists by cayleyExpBump_cfc_cauchySeq + completeness). This IS
-- cfc(e_t) V x = exp(itA) x for the self-adjoint A=i(1+V)(1−V)⁻¹, built with NO PVM. cayleyStoneU_tendsto (the
-- defining strong-limit property) + cayleyStoneU_add (U_t(x+y)=U_t x+U_t y) + cayleyStoneU_smul (U_t(c•x)=c•U_t x)
-- ⟹ U_t is ℂ-LINEAR (map_add/map_smul of each cfc(g_{t,N})V + Tendsto.add/const_smul + tendsto_nhds_unique).
-- Toward U_t ∈ unitary(H), the one-parameter group law (cayleyExp_add/_zero), strong continuity, generator.
-- Axiom-free.
-- ★★★ P4 WALL — THE STONE-EXP CFC VECTORS FORM A CAUCHY SEQUENCE (the strong limit IS U_t x):
-- cayleyExpBump_cfc_cauchySeq [Nontrivial H] — cfc(g_{t,N}) V x is a CauchySeq in H (converges, H complete), whose
-- strong limit is the Stone unitary U_t x. g_{t,N}=e_t·η_N is ContinuousOn σ(V) (cayleyExpBump_continuousOn) and
-- → e_t in L²(μ_x) (cayleyExpBump_L2_tendsto_zero); L²-convergent ⟹ L²-Cauchy (quadratic triangle ‖g_m−g_n‖²≤
-- 2‖g_m−e_t‖²+2‖g_n−e_t‖² with c=e_t, integral_mono_of_nonneg; integrability via the a.e. equality to ψ_N²), then
-- cayley_cfc_cauchySeq_of_integral (the existence half). The continuum Stone exponential U_t=exp(itA) as a strong
-- limit of continuous functional calculi, NO PVM. Axiom-free.
-- ★★ P4 WALL — THE CUTOFF SYMBOL IS CONTINUOUS ON σ(V): cayleyExpBump t N ω := e_t(ω)·η_N(ω); cayleyExpBump_norm
-- (‖g_{t,N}(ω)‖=η_N(ω) on the circle) + cayleyExpBump_continuousOn [Nontrivial H] (ContinuousOn (g_{t,N}) σ(V)):
-- off the excluded point 1 a product of ContinuousAt fns (cayleyExp_continuousOn on the open {ω≠1} + bump cts);
-- AT 1 the value is g(1)=e_t(1)·0=0 and ‖g(ω)‖=η_N(ω)→η_N(1)=0 (cayleyExpBump_norm on σ(V)⊆S¹ + η_N cts +
-- eventuallyEq_nhdsWithin_of_eqOn + tendsto_zero_iff_norm_tendsto_zero) — the squeeze ⟹ ContinuousWithinAt. So
-- cfc(g_{t,N})V is well-defined (cfc needs ContinuousOn σ(V)), the operator whose strong limit is U_t. Axiom-free.
-- ★★ P4 WALL — THE CUTOFF SYMBOL CONVERGES TO THE SYMBOL IN L²(μ_x): cayleyExpBump_L2_tendsto_zero [Nontrivial H]
-- — ∫‖e_t·η_N − e_t‖² dμ_x → 0. Integrand = ψ_N(ω.1)² on σ(V)⊆S¹ (cayleyExpBump_sub_norm, integral_congr_ae) ⟹
-- = cayleyCutoff_sq_integral_tendsto_zero (∫ψ_N²→0): the squeeze 0≤∫ψ_N²≤∫ψ_N→μ_x({1})=0 (integral_mono_of_nonneg
-- ψ_N²≤ψ_N + DCT-1 + atom-killing + ENNReal.toReal_zero + squeeze_zero). The cutoff symbol → e_t in L²(μ_x), which
-- (with the L²-distance Parseval, via triangle) gives the L²-Cauchy condition for cfc(e_t·η_N)V x ⟹ strong limit
-- U_t x = lim cfc(e_t·η_N)V x. Axiom-free.
-- ★ P4 WALL — THE CUTOFF-SYMBOL L²-DEFECT (algebra toward the L²-convergence g_{t,N}→e_t): cayleyExp_abs_circle
-- (‖e_t(ω)‖=1 on the WHOLE circle incl. the junk point ω=1 where cayleyInv 1=i·2/0=0 ⟹ e_t(1)=exp 0=1) +
-- cayleyExpBump_sub_norm (‖e_t(ω)·η_N(ω) − e_t(ω)‖ = ψ_N(ω) on the circle: e_t·(η_N−1), ‖e_t‖=1, |η_N−1|=|−ψ_N|=ψ_N).
-- Hence ‖g_{t,N}−e_t‖²=ψ_N² ⟹ ∫‖g−e_t‖²dμ_x = ∫ψ_N²dμ_x ≤ ∫ψ_N dμ_x → μ_x({1})=0: the cutoff symbol → e_t in
-- L²(μ_x), the input to U_t = lim cfc(g_{t,N})V x. Axiom-free.
-- ★ P4 WALL — THE CONTINUOUS BUMP CUTOFF (the symbol's L²-approximation device): cayleyBump N ω := 1−cayleyCutoff N ω
-- — complementary to the rational cutoff. cayleyBump_continuous + _nonneg + _le_one (η_N∈[0,1] cts, the DCT
-- dominator) + _tendsto_indicator (η_N(ω)→ if ω=1 then 0 else 1, i.e. → indicator of ℂ∖{1}; from
-- cayleyCutoff_tendsto_indicator). η_N(1)=0 tames e_t's discontinuity at 1: the cutoff symbol e_t·η_N is cts on σ(V)
-- and → e_t in L²(μ_x) (μ_x({1})=0), so cfc(e_t·η_N)V x converges to define U_t x = strong-limit Stone exponential.
-- Axiom-free.
-- ★ P4 WALL — THE ONE-PARAMETER GROUP STRUCTURE OF THE SYMBOL: cayleyExp_zero (e_0(ω)=1, exp 0=1 — seed of U_0=1)
-- + cayleyExp_add (e_s(ω)·e_t(ω)=e_{s+t}(ω) via Complex.exp_add — the symbol-level seed of the Stone group law
-- U_s U_t = U_{s+t}: cfc(e_s)V·cfc(e_t)V = cfc(e_s·e_t)V = cfc(e_{s+t})V by cfc multiplicativity). Two of the three
-- Stone-group axioms at the symbol level (strong continuity t↦U_t x is the third). Axiom-free.
-- ★ P4 WALL — THE STONE-EXPONENTIAL SYMBOL: cayleyExp t ω := exp(i·t·cayleyInv ω) — the bounded Borel function
-- whose cfc cfc(e_t) V IS the Stone unitary U_t=exp(itA), A=cayleyInv(V). cayleyExp_continuousOn (cts off the
-- excluded point 1, exp∘cts) + cayleyExp_abs (modulus 1 on the circle off 1: ‖e_t(ω)‖=1 since cayleyInv ω real ⟹
-- i·t·c(ω) purely imaginary ⟹ ‖exp‖=exp((·).re)=exp 0=1, Complex.norm_exp). Bounded+cts off 1, and μ_x({1})=0, so
-- e_t is μ_x-a.e. cts/bounded — approximable in L²(μ_x), whose cfc-vectors converge (L²→strong bridge) to define
-- U_t x as a strong limit. Axiom-free.
-- ★ P4 WALL — THE INVERSE CAYLEY MAP (Stone-exp symbol foundation): cayleyInv ω := i(1+ω)/(1−ω) and
-- cayleyInv_continuousOn (continuous off the excluded point 1, denom 1−ω≠0) + cayleyInv_im_eq_zero (REAL on the
-- unit circle off 1: (c(ω)).im=0 for ‖ω‖=1, ω≠1 — i.e. A=i(1+V)(1−V)⁻¹ is self-adjoint, so exp(it·c(ω)) has
-- modulus 1; proof: conj ω=ω⁻¹ on the circle (RCLike.mul_conj) + div_eq_div_iff + linear_combination). The symbol
-- exp(it·cayleyInv(ω)) is continuous+bounded off ω=1, and μ_x({1})=0, so it is μ_x-a.e. defined — the data the
-- strong-limit Stone exponential U_t=exp(itA) consumes. Axiom-free.
-- ★★★★ P4 WALL — THE CAYLEY SPECTRAL ATOM VANISHES: cayleyScalarMeasure_atom_eq_zero [Nontrivial H] —
-- μ_x({1}) = 0, i.e. the scalar spectral measure of the Cayley unitary V puts NO mass on the exceptional point
-- 1 ∈ S¹ (image of ∞ under inverse Cayley). DCT-1 (∫ψ_N dμ→μ_x({1})) + ∫ψ_N dμ=re⟪x,cfc(ψ_N)V x⟫
-- (integral_re_cfc_ofReal) + cfc(ψ_N)V x→0 (cayleyCutoff_cfc_tendsto_zero, inner+re continuity) ⟹ ∫ψ_N→re⟪x,0⟫=0;
-- tendsto_nhds_unique ⟹ μ_x({1}).toReal=0 ⟹ μ_x({1})=0 (μ_x finite). CONSEQUENCE: the inverse-Cayley/Stone
-- exponential symbol exp(it·invCayley(ω)) (continuous+bounded off ω=1) is now μ_x-a.e. defined — the precondition
-- for the strong-limit Stone exponential U_t=exp(itA). Axiom-free.
-- ★★★ P4 WALL — THE CUTOFF CFC VECTORS TEND TO 0 (the operator heart of the atom-killing):
-- cayleyCutoff_cfc_tendsto_zero [Nontrivial H] — cfc(ψ_N) V x → 0 strongly in H. Assembles: (existence) the
-- CauchySeq converges to w (cauchySeq_tendsto_of_complete on cayleyCutoff_cfc_cauchySeq); ((V−1)w=0) the defect
-- (V−1)cfc(ψ_N)V x = cfc((z−1)ψ_N)V x → 0 (DCT-3 via cayley_cfc_tendsto_zero_of_integral, the convergence half)
-- and → (V−1)w by continuity, so tendsto_nhds_unique ⟹ (V−1)w=0; (w=0) ker(1−V)=0 (cayley_one_sub_injective).
-- The cfc(z−1)V=V−1 step is cfc_mul + cfc_sub + cayley_cfc_id/_one. With DCT-1 + inner-continuity this kills the
-- Cayley spectral atom μ_x({1})=0. Axiom-free.
-- ★★★ P4 WALL — THE CUTOFF CFC VECTORS FORM A CAUCHY SEQUENCE (the existence input): cayleyCutoff_cfc_cauchySeq
-- [Nontrivial H] — cfc(ψ_N) V x is a CauchySeq in H (hence converges, H complete). The cutoff sequence is
-- L²(μ_x)-Cauchy from DCT-2 (cayleyCutoff_L2_tendsto_zero) + the pointwise quadratic triangle ‖a−b‖²≤2‖a−c‖²+2‖b−c‖²
-- (c=1_{{1}}) integrated via integral_mono_of_nonneg: ∫‖ψ_m−ψ_n‖²≤2∫‖ψ_m−1_{{1}}‖²+2∫‖ψ_n−1_{{1}}‖²<ε. Then
-- cayley_cfc_cauchySeq_of_integral (the existence half of the L²→strong bridge) turns the L²-Cauchy condition into
-- a CauchySeq of operator-vectors. Axiom-free.
-- ★★ P4 WALL — THE SECOND DCT STEP (L²-Cauchy input): cayleyCutoff_L2_tendsto_zero [Nontrivial H] —
-- ∫ ‖ψ_N(ω) − 1_{{1}}(ω)‖² dμ_x → 0, i.e. the cutoff → the indicator of {1} in L²(μ_x). Dominated convergence:
-- integrand ‖ψ_N − 1_{{1}}‖² ≤ 4 (ψ_N≤1, ‖1_{{1}}‖≤1), AEStronglyMeasurable (continuous cutoff − indicator of the
-- measurable {1}), → 0 ptwise (cayleyCutoff_sub_indicator_sq_tendsto_zero, the helper). An L²-convergent sequence
-- is L²-Cauchy, so this feeds cayley_cfc_cauchySeq_of_integral (via the triangle ineq) ⟹ strong limit
-- w = lim cfc(ψ_N)V x (H complete) — the EXISTENCE input the atom-killing needs. Axiom-free.
-- ★★ P4 WALL — THE THIRD DCT STEP OF THE ATOM-KILLING: cayleyCutoff_defect_integral_tendsto_zero [Nontrivial H]
-- — ∫ ‖(ω−1)·ψ_N(ω)‖² dμ_x → 0. Dominated convergence with the (z−1)-weighted cutoff: integrand
-- ‖(ω−1)ψ_N‖²=‖ω−1‖²ψ_N² ≤ 4 (σ(V)⊆S¹ ⟹ ‖(ω:ℂ)‖=1 ⟹ ‖ω−1‖≤2; ψ_N≤1), continuous, → 0 ptwise
-- (cayleyCutoff_sq_mul_tendsto_zero). In the form ∫‖F_N ω.1‖²dμ_x→0 with F_N(z)=(z−1)ψ_N(z), feeds
-- cayley_cfc_tendsto_zero_of_integral ⟹ (V−1)cfc(ψ_N)V x=cfc((z−1)ψ_N)V x→0 ⟹ (V−1)w=0 ⟹ w=0 (ker(1−V)=0).
-- Axiom-free.
-- ★★ P4 WALL — THE FIRST DCT STEP OF THE ATOM-KILLING: cayleyCutoff_integral_tendsto_atom [Nontrivial H] —
-- ∫ ψ_N(ω) dμ_x → μ_x({1}) where {1} = {ω ∈ σ(V) | (ω:ℂ)=1}. Dominated convergence
-- (tendsto_integral_of_dominated_convergence) with the cutoff scaffolding: ψ_N∘↑ continuous, ≤1 (integrable
-- dominator, μ_x finite), → 1_{{1}} ptwise (cayleyCutoff_tendsto_indicator); limit ∫1_{{1}}dμ_x=μ_x({1})
-- (integral_indicator_one); {1} measurable via isClosed_eq. With ∫ψ_N dμ_x=re⟪x,cfc(ψ_N)V x⟫ this evaluates the
-- diagonal limit of the spectral projection toward 1 — the value lim cfc(ψ_N)V x must reproduce (forced to 0 by
-- ker(1−V)=0). Axiom-free.
-- ★ P4 WALL — THE RATIONAL CUTOFF SCAFFOLDING (toward μ_x({1})=0): cayleyCutoff N z := (1+(N+1)‖z−1‖²)⁻¹ and its
-- analytic properties — cayleyCutoff_pos (0<ψ_N), _le_one (ψ_N≤1, the DCT dominator), _continuous (each ψ_N cts),
-- _tendsto_zero_of_ne (z≠1 ⟹ ψ_N(z)→0, denom→∞ via inv_tendsto_atTop), _tendsto_indicator (ψ_N→1_{z=1} ptwise,
-- the DCT limit for ∫ψ_N dμ_x→μ_x({1})), _sq_mul_tendsto_zero (‖z−1‖²·ψ_N²→0, the integrand for ∫‖(ω−1)ψ_N‖²→0,
-- dominated by the defect-energy integrand). Pure real analysis, U-independent. Feeds the L²→strong bridge to kill
-- the Cayley atom μ_x({1})=0. Axiom-free.
-- ★★ P4 WALL — THE CAYLEY DEFECT-ENERGY IDENTITY: cayley_defect_energy [Nontrivial H] — ‖V x − x‖² =
-- ∫ ω, ‖(ω:ℂ)−1‖² dμ_x. The f=z−1 specialization of the Parseval f-isometry cayley_cfc_norm_sq_integral, using
-- cfc(z↦z−1)V = V−1 (cfc_sub + keystones cayley_cfc_id `cfc id V=V` & cayley_cfc_one `cfc 1 V=1`). Quantitatively
-- the spectral mass weighted by squared distance-to-1 = the Cayley defect ‖(V−1)x‖² — the integral witnessing
-- ker(1−V)=0 (cayley_one_sub_injective). The inverse-Cayley generator A=i(1+V)(1−V)⁻¹ is obstructed only by the
-- spectral ATOM μ_x({1}) (the next brick — vanishing via the L²→strong bridge + rational cutoffs). Axiom-free.
-- ★★ P4 WALL — THE EXISTENCE HALF OF THE OPERATOR-LIMIT TOOLKIT: cayley_cfc_cauchySeq_of_integral [Nontrivial H]
-- — if F n is Cauchy in L²(μ_x) (∀ε>0 ∃N ∀m,n≥N, ∫‖F m ω.1−F n ω.1‖²dμ_x<ε) then cfc(F n) V x is a CauchySeq in H
-- (hence converges, H complete). From the L²-distance Parseval cayley_cfc_sub_norm_sq_integral: L²-Cauchy at ε²
-- gives ‖·‖²<ε² ⟹ ‖·‖<ε (lt_of_pow_lt_pow_left₀). With cayley_cfc_tendsto_zero_of_integral (convergence half) this
-- is the FULL bridge L²(μ_x) continuous-fn limits ⟶ strong operator limits — makes cfc(ψ_N)V x converge (atom
-- μ_x({1})=0) and assembles U_t=exp(itA), no PVM (GPT-5.5-pro route 2026-06-27). Axiom-free.
-- ★★ P4 WALL — THE PARSEVAL / L²-ISOMETRY (integral form, f-version): cayley_cfc_norm_sq_integral [Nontrivial H]
-- — ‖cfc f V x‖² = ∫ ω, ‖f ω.1‖² dμ_x for f continuous on σ(V). The g=0 companion of cayley_cfc_sub_norm_sq_integral
-- (composes cayley_cfc_norm_sq with integral_re_cfc_ofReal at r z=‖f z‖², via star w·w=↑‖w‖²/RCLike.conj_mul). THE
-- Parseval identity: f↦cfc f V x is an L²(μ_x)→H isometry on continuous functions. Axiom-free.
-- ★★ P4 WALL — THE L² CONVERGENCE ENGINE (strong-limit Stone exp): cayley_cfc_tendsto_zero_of_integral
-- [Nontrivial H] — ∫‖F n ω.1‖² dμ_x → 0 ⟹ cfc(F n) V x → 0 strongly. From Parseval ‖cfc(F n)V x‖²=∫‖F n‖²dμ_x
-- (‖·‖²→0 ⟹ ‖·‖=√(‖·‖²)→0 ⟹ →0; tendsto_zero_iff_norm_tendsto_zero + Real.sqrt_sq). The convergence half of the
-- Cauchy/DCT machine turning L²(μ_x)-limits of continuous fns into strong operator limits — kills the Cayley atom
-- μ_x({1})=0 and assembles U_t=exp(itA), no PVM (GPT-5.5-pro route 2026-06-27). Axiom-free.
-- ★★★ P4 WALL — THE FULL PARSEVAL / L²-DISTANCE IDENTITY (integral form): cayley_cfc_sub_norm_sq_integral
-- [Nontrivial H] — ‖cfc f V x − cfc g V x‖² = ∫ ω, ‖f ω.1 − g ω.1‖² dμ_x for f,g continuous on σ(V). Capstone of the
-- CFC↔measure dictionary: composes cayley_cfc_sub_norm_sq (operator side: re⟪x, cfc(star(f−g)·(f−g))V x⟫) with the
-- function-form bridge integral_re_cfc_ofReal at r z=‖f z−g z‖², via the pointwise ℂ-identity star w·w=↑‖w‖²
-- (RCLike.conj_mul). This is the genuine Parseval/Cauchy estimate in MEASURE form: n↦cfc(e^{it·φₙ})V x is Cauchy
-- iff ∫‖e^{itφₙ}−e^{itφₘ}‖² dμ_x→0, which defines the Stone exponential U_t=exp(itA) without a PVM (GPT-5.5-pro
-- endorsed route 2026-06-27). Axiom-free; free scalar; no UV datum touched.
-- ★★ P4 WALL — L²-DISTANCE ESTIMATE (the Cauchy estimate for the strong-limit Stone exp): cayley_cfc_sub_norm_sq
-- [Nontrivial H] — ‖cfc f V x − cfc g V x‖² = re⟪x, cfc(|f−g|²) V x⟫ (cfc_sub ⟹ cfc f V − cfc g V = cfc(f−g)V, then
-- cayley_cfc_norm_sq at f−g). With the integral identity = ∫|f−g|² dμ_x — the Cauchy/dominated-convergence estimate
-- making n ↦ cfc(e^{it·φₙ})V x Cauchy, defining U_t=exp(itA) as a strong limit (no PVM). Axiom-free.
-- ★★ P4 WALL — L²-ISOMETRY OF THE FUNCTIONAL CALCULUS (operator side): cayley_cfc_norm_sq [Nontrivial H] —
-- ‖cfc f V x‖² = re⟪x, cfc(|f|²) V x⟫ (|f|²=conj f·f), via (cfc f V)⋆(cfc f V)=cfc(conj f·f)V (cfc_star+cfc_mul) +
-- adjoint_inner_right + inner_self_eq_norm_sq. With the integral identity (re⟪x,cfc(|f|²)V x⟫ = ∫|f|² dμ_x) this is
-- Parseval ‖cfc f V x‖² = ∫|f|² dμ_x — the L² estimate behind the dominated-convergence/Cauchy argument that builds
-- the Stone exponential U_t=exp(itA) as a strong limit of cfc(e^{it·φₙ})V x (GPT-5.5-pro recipe). Axiom-free.
-- ★ P4 WALL — FINITE ADDITIVITY OF THE SPECTRAL DISTRIBUTION: cayleyScalarMeasure_union [Nontrivial H] —
-- μ_x(S∪T) = μ_x(S)+μ_x(T) (toReal) for disjoint measurable S,T (measure_union + ENNReal.toReal_add, μ_x finite).
-- The diagonal shadow of the PVM additivity E(S∪T)=E(S)+E(T) and (normalized) the additivity of the Born
-- probabilities over disjoint spectral outcomes — refined to σ-additivity by the eventual PVM E. Axiom-free.
-- ★ P4 WALL — DIAGONAL SPECTRAL CONTENT BOUNDED: cayleyScalarMeasure_le_norm_sq [Nontrivial H] —
-- (cayleyScalarMeasure x S).toReal ≤ ‖x‖² for any S (μ_x finite, total mass ‖x‖², measure_mono + toReal_mono). This
-- is the bound the diagonal ⟪x, E(S) x⟫ = μ_x(S) of the spectral projection E(S) must satisfy (0 ≤ E(S) ≤ 1 on x),
-- controlling the Riesz representation of (x,y) ↦ ∫ 1_S dμ_{x,y} into E(S). Axiom-free.
-- ★★ P4 WALL — SPECTRAL POLARIZATION IDENTITY (off-diagonal via diagonals): cayley_cfc_inner_polarization
-- [Nontrivial H] — ⟪cfc f V y, x⟫ = (⟪cfc f V(x+y),x+y⟫ − ⟪cfc f V(x−y),x−y⟫ + I⟪cfc f V(x+Iy),x+Iy⟫ −
-- I⟪cfc f V(x−Iy),x−Iy⟫)/4 (inner_map_polarization of (cfc f V).toLinearMap). With the real diagonal
-- (cayley_cfc_inner_self_im_zero: ⟪cfc f V z,z⟫ = ↑(∫f dμ_z)) this expresses the FULL sesquilinear form via the
-- scalar measures μ_z — the formula that DEFINES the bounded-Borel operator f(V) and E(S)=1_S(V). Axiom-free.
-- ★★ P4 WALL — SPECTRAL SESQUILINEAR FORM IS BOUNDED (Riesz input for the Borel-FC operators): cayley_norm_inner_
-- cfc_le [Nontrivial H] — ‖⟪x, cfc f V y⟫‖ ≤ c·‖x‖·‖y‖ when ‖f z‖ ≤ c on σ(V) (Cauchy–Schwarz norm_inner_le_norm +
-- ContinuousLinearMap.le_opNorm + cayley_norm_cfc_le). The boundedness of (x,y)↦⟪x,cfc f V y⟫ that lets the form
-- (extended to bounded-Borel f via μ_{x,y}) be Riesz-represented by an operator f(V); for f=1_S this is E(S). Axiom-free.
-- ★ P4 WALL — EXPECTATION OF A REAL OBSERVABLE IS REAL: cayley_cfc_inner_self_im_zero [Nontrivial H] —
-- (⟪x, cfc f V x⟫).im = 0 for f real on σ(V), from cayley_cfc_isSelfAdjoint (cfc f V self-adjoint ⟹
-- conj⟪x,cfc f V x⟫ = ⟪cfc f V x, x⟫ = ⟪x,cfc f V x⟫ via adjoint_inner_left; Complex.conj_eq_iff_im). So
-- ⟪x,cfc f V x⟫ = ↑(∫f dμ_x) — the real scalar diagonal the polarization μ_{x,y} extends. Axiom-free.
-- ★★ P4 WALL — cfc OF A REAL FUNCTION IS SELF-ADJOINT (real observables → self-adjoint operators):
-- cayley_cfc_isSelfAdjoint [Nontrivial H] — (f z).im=0 on σ(V) ⟹ IsSelfAdjoint (cfc f V), via star(cfc f V) =
-- cfc(conj∘f)V = cfc f V (cfc_star + cfc_congr, conj(f z)=f z on σV). So spectral operators of real observables of V
-- are self-adjoint — the bridge making ⟪x,cfc f V x⟫ real (= ∫f dμ_x) and underlying the polarization μ_{x,y}
-- toward the PVM. Axiom-free.
-- ★★ P4 WALL — cfc OF V IS NORM-BOUNDED BY THE SUP-NORM (boundedness ⟹ Borel-FC extension): cayley_norm_cfc_le
-- [Nontrivial H] — ‖cfc f V‖ ≤ c when ‖f z‖ ≤ c on σ(V) (norm_cfc_le; the ℂ-normal CFC on H→L[ℂ]H is isometric,
-- IsStarNormal.instIsometricContinuousFunctionalCalculus, a global instance). This is the boundedness of f↦cfc f V
-- that lets the FC extend from continuous to bounded-Borel functions (approximation/dominated convergence over μ_x)
-- — the analytic input to the Borel FC and the PVM E(S). Axiom-free.
-- ★★ P4 WALL — μ_x IS A PROBABILITY MEASURE FOR ‖x‖=1 (Born/spectral distribution): cayleyScalarMeasure_isProbability
-- Measure [Nontrivial H] — ‖x‖=1 ⟹ IsProbabilityMeasure (cayleyScalarMeasure x). From cayleyScalarMeasure_univ
-- ((μ_x univ).toReal = ‖x‖²=1) + finiteness ⟹ μ_x univ = 1 (ENNReal.toReal_eq_one_iff). So μ_x is the Born/spectral
-- probability distribution of measuring (a function of) V in the normalized state x. Axiom-free.
-- ★★ P4 WALL — TOTAL MASS μ_x(σV) = ‖x‖²: cayleyScalarMeasure_univ [Nontrivial H] —
-- (cayleyScalarMeasure x Set.univ).toReal = ‖x‖^2. Integral identity at the const 1 (continuousMapEquiv on compact
-- σV): (μ_x univ).toReal = ∫1 dμ_x = re⟪x, cfc 1 V x⟫ = re⟪x,x⟫ = ‖x‖² (cfc 1 V=1 via map_one cfcHom;
-- inner_self_eq_norm_sq). So μ_x is the Born-like spectral distribution of the state x, total mass ‖x‖². Axiom-free.
-- ★ P4 WALL — μ_x IS A FINITE MEASURE: cayleyScalarMeasure_isFiniteMeasure [Nontrivial H] —
-- IsFiniteMeasure (cayleyScalarMeasure x) (RealRMK's CompactSpace instance, σ(V) compact). So μ_x is a genuine
-- finite spectral distribution of the state x (total mass ‖x‖²), and ∫ g dμ_x is defined for every bounded Borel g
-- — the extension beyond continuous functions underlying the Borel FC / the PVM E(S)=∫1_S dE. Axiom-free.
-- ★★★ P4 WALL — μ_x REPRESENTS THE FUNCTIONAL: cayleyScalarMeasure_integral [Nontrivial H] —
-- ∫ f dμ_x = re⟪x, cfc f V x⟫ for f : C_c(σV,ℝ) (RealRMK.integral_rieszMeasure for cfcPLMcc x). This PINS μ_x to V:
-- its moments are the expectations of functions of V in the state x (total mass ‖x‖², first moment re⟪x,Vx⟫). The
-- operator → scalar-spectral-measure half of the spectral theorem is now end-to-end machine-checked. Axiom-free.
-- ★★★ P4 WALL — THE SCALAR SPECTRAL MEASURE μ_x IS CONSTRUCTED: cayleyScalarMeasure [Nontrivial H] —
-- Measure (spectrum ℂ V) := RealRMK.rieszMeasure (cfcPLMcc x), the finite Borel measure on σ(V)⊆S¹ from the
-- Riesz–Markov–Kakutani theorem applied to the positive linear functional f↦re⟪x,cfc f V x⟫. (CompactSpace σ(V)
-- via spectrum.isCompact ⟹ the T2/MeasurableSpace/BorelSpace/LocallyCompactSpace instances all resolve.) By
-- RealRMK.integral_rieszMeasure, ∫f dμ_x = re⟪x,cfc f V x⟫ (total mass ‖x‖² from cfc 1 V=1; first moment re⟪x,Vx⟫
-- from cfc id V=V). The scalar component of V's PVM. Axiom-free. Remaining: assemble {μ_x} into the PVM E (Mathlib gap).
-- ★★★ P4 WALL — THE RMK INPUT C_c(σV,ℝ)→ₚ[ℝ]ℝ: cfcPLMcc [Nontrivial H] — f↦re⟪x,cfc f V x⟫ on the compactly-
-- supported functions = cfcPLM precomposed with the forgetful C_c(σV,ℝ)→C(σV,ℝ) (σV compact ⟹ bijection);
-- map_add'/map_smul' via map_add/map_smul of cfcPLM, monotone' via cfcPLM.monotone' ∘ (C_c→C order). This is EXACTLY
-- the type RealRMK.rieszMeasure consumes ⟹ feeding it gives the scalar spectral measure μ_x of V with
-- ∫f dμ_x = re⟪x,cfc f V x⟫. Axiom-free. Remaining: rieszMeasure ⟹ μ_x (Borel/LCH instances on σV), then the
-- PVM assembly (the genuine Mathlib gap).
-- ★★★ P4 WALL — THE POSITIVE LINEAR FUNCTIONAL C(σV,ℝ)→ₚ[ℝ]ℝ (the RMK input): cfcPLM [Nontrivial H] —
-- g↦re⟪x,cfc g V x⟫ bundled as a PositiveLinearMap, toLinearMap := (realCfcReExpectationCLM x).toLinearMap,
-- monotone' from realCfcReExpectation_nonneg (linear map monotone iff 0≤y⟹0≤f y, via f b−f a=f(b−a)≥0). This is
-- THE input RealRMK.rieszMeasure consumes: transported to C_c(σV,ℝ) (compact spectrum) it yields the scalar
-- spectral measure μ_x of V with ∫g dμ_x = re⟪x,cfc g V x⟫. Axiom-free. Remaining: C_c transport + rieszMeasure ⟹ μ_x,
-- then the PVM assembly (the genuine Mathlib gap).
-- ★★ P4 WALL — RMK FUNCTIONAL IS MONOTONE/POSITIVE (the →ₚ[ℝ] monotone' field): realCfcReExpectation_nonneg
-- [Nontrivial H] — 0 ≤ g ⟹ 0 ≤ realCfcReExpectationCLM x g for g : C(σ(V),ℝ). Bridge cfcL ha (↑∘g) = cfcHom ha (↑∘g)
-- = cfc (Function.extend Subtype.val (↑∘g) 0) V (cfcL_apply + cfcHom_eq_cfc_extend); the extend is ContinuousOn σ(V)
-- and real-≥0 there (= ↑(g ω) on the spectrum), so cayley_cfc_re_inner_nonneg_of_nonneg applies. With ℝ-linearity
-- (realCfcReExpectationCLM is a CLM) this is the →o/monotone' field upgrading it to C(σV,ℝ)→ₚ[ℝ]ℝ — the positive
-- linear functional RealRMK.rieszMeasure consumes to build μ_x. Axiom-free.
-- ★★ P4 WALL — RMK FUNCTIONAL ON THE REAL FUNCTIONS C(σV,ℝ) (ℝ↪ℂ restriction done): realCfcReExpectationCLM
-- [Nontrivial H] — C(spectrum ℂ V, ℝ) →L[ℝ] ℝ, g ↦ re⟪x, cfcHom V (↑∘g) x⟫ = (cfcReExpectationCLM x) ∘
-- (ContinuousLinearMap.compLeftContinuous ℝ σV Complex.ofRealCLM) (postcompose each real g with Complex.ofReal).
-- Since σ(V) is compact (cayley_spectrum_isCompact), C(σV,ℝ)=C_c(σV,ℝ); up to repackaging into →ₚ[ℝ] with the proven
-- positivity, this is the input RealRMK.rieszMeasure consumes to build μ_x. Axiom-free.
-- ★★ P4 WALL — RMK FUNCTIONAL ON C(σV,ℂ) (cfcHom precomposition done): cfcReExpectationCLM [Nontrivial H] —
-- C(spectrum ℂ V, ℂ) →L[ℝ] ℝ, φ ↦ re⟪x, cfcHom V φ x⟫ = (reExpectationCLM x) ∘ (cfcL V).restrictScalars ℝ, where
-- cfcL V : C(σV,ℂ) →L[ℂ] (H→L[ℂ]H) is the continuous functional calculus bundled as a CLM. Restricting the domain
-- to the real functions C_c(σV,ℝ) (ℝ↪ℂ embedding) gives the positive ℝ-linear functional RealRMK.rieszMeasure
-- turns into μ_x. Axiom-free.
-- ★ P4 WALL — BUNDLED EXPECTATION FUNCTIONALS (RMK-functional packaging): expectationCLM x : (H→L[ℂ]H)→L[ℂ]ℂ,
-- T↦⟪x,Tx⟫ = (innerSL ℂ x)∘(ContinuousLinearMap.apply ℂ H x). reExpectationCLM x : (H→L[ℂ]H)→L[ℝ]ℝ, T↦re⟪x,Tx⟫
-- = Complex.reCLM ∘ (expectationCLM x).restrictScalars ℝ. Precomposed with cfcHom V and restricted to C_c(σV,ℝ),
-- reExpectationCLM is the bundled Riesz–Markov functional whose positivity + ℝ-linearity are the proven →ₚ[ℝ] data
-- RealRMK.rieszMeasure consumes to build μ_x. Axiom-free.
-- ★★ P4 WALL — RMK FUNCTIONAL IS ℝ-LINEAR (completes positive LINEAR functional): cayley_cfc_re_inner_add
-- [Nontrivial H] — re⟪x,cfc(f+g)V x⟫ = re⟪x,cfc f V x⟫ + re⟪x,cfc g V x⟫ (cfc_add + inner_add_right + Complex.add_re).
-- cayley_cfc_re_inner_smul [Nontrivial H] — re⟪x,cfc(↑c·f)V x⟫ = c·re⟪x,cfc f V x⟫ for c:ℝ (cfc_const_mul +
-- inner_smul_right + Complex.re_ofReal_mul). With cayley_cfc_re_inner_nonneg_of_nonneg (positivity), g↦re⟪x,cfc g V x⟫
-- is a POSITIVE ℝ-LINEAR functional — every component RealRMK.rieszMeasure needs to produce μ_x. Axiom-free.
-- ★★ P4 WALL — RMK FUNCTIONAL POSITIVE ON THE WHOLE NONNEG CONE: cayley_cfc_re_inner_nonneg_of_nonneg
-- [Nontrivial H] — 0 ≤ re⟪x, cfc g V x⟫ for any g continuous on σ(V) that is real and ≥ 0 there. Reduce to the
-- square case via g = |√g|²: h z = √((g z).re) is continuous real, conj(h)·h = g on σ(V) (cfc_congr), so by
-- cayley_cfc_sq_re_inner_nonneg the expectation = ‖cfc h V x‖² ≥ 0 (closed via le_of_le_of_eq + congrArg to dodge
-- cfc proof-irrelevance). This is the exact positivity g↦re⟪x,cfc g V x⟫ needs to be a positive linear functional
-- C_c(σV,ℝ)→ₚ[ℝ]ℝ for RealRMK.rieszMeasure ⟹ μ_x. Axiom-free.
-- ★★ P4 WALL — SPECTRAL MOMENTS + RMK FUNCTIONAL POSITIVITY: cayley_cfc_one [Nontrivial H] — cfc 1 V = 1
-- (resolution of identity, ∫1 dE = 1; with cfc_id's ∫z dE = V these pin μ_x's total mass ‖x‖² and first moment).
-- cayley_cfc_sq_re_inner_nonneg [Nontrivial H] — 0 ≤ re⟪x, cfc(conj f·f) V x⟫ for f continuous on σ(V): since
-- cfc(conj f·f)V = cfc(star f)V * cfc f V = (cfc f V)⋆(cfc f V) ≥ 0 (cfc_mul + cfc_star + star_mul_self_nonneg),
-- the expectation = ‖cfc f V x‖² ≥ 0. As |f|² generate the nonneg cone of C(σV,ℝ), this is the POSITIVITY of the
-- Riesz–Markov functional g↦re⟪x,cfc g V x⟫ — the input RealRMK.rieszMeasure turns into μ_x. Axiom-free.
-- ★★ P4 WALL — cfc id V = V (the "V = ∫ z dE" continuous-FC shadow): cayley_cfc_id [Nontrivial H] —
-- cfc (id : ℂ→ℂ) (cayleyUnitary U ⋯) = cayleyUnitary U ⋯ (cfc_id ℂ _ cayley_isStarNormal). The coordinate function
-- z↦z applied to V through its continuous spectral data returns V — the C(σV)-level form of V = ∫_{S¹} z dE(z),
-- and the base case the scalar-measure construction integrates against. Resolves last fire's obstruction: the
-- ℂ-normal CFC local-instance theorem IS enableable via `attribute [local instance]` + importing CStarAlgebra.
-- ContinuousLinearMap (CStarAlgebra (H→L[ℂ]H)) + CFC.Basic + threading [Nontrivial H]. Axiom-free.
-- ★ P4 WALL — CFC PREDICATE + FUNCTIONAL POSITIVITY (RMK-input infrastructure): cayley_isStarNormal — IsStarNormal
-- (cayleyUnitary U ⋯) (isStarNormal_of_mem_unitary ∘ cayley_mem_unitary), the predicate the ℂ continuous functional
-- calculus requires. nonneg_re_inner_nonneg — 0 ≤ T (C*-order on H→L[ℂ]H) ⟹ 0 ≤ re⟪x,Tx⟫
-- (ContinuousLinearMap.nonneg_iff_isPositive + IsPositive.re_inner_nonneg_right): the functional-positivity step —
-- once cfc gives 0 ≤ cfc f V for f≥0 on σ(V), f↦re⟪x,cfc f V x⟫ is a positive functional, RMK→μ_x. Axiom-free.
-- NOTE (honest obstruction discovered): the ℂ-normal CFC is a *local-instance theorem* in Mathlib needing
-- [Nontrivial A] (nonempty spectrum); over abstract H the cfc-of-V route must thread Nontrivial H / work on the
-- concrete generators. The PVM keystone (μ_x via RMK → circle-PVM → transport → Stone) stays the genuine gap.
#print axioms QIQTH.Spectral.cayley_spectrum_isCompact
-- ★ P4 WALL — SPECTRUM OF V IS COMPACT (RMK precondition): cayley_spectrum_isCompact — IsCompact (spectrum ℂ
-- (cayleyUnitary U ⋯)) (spectrum.isCompact). With cayley_spectrum_subset_circle, σ(V) is a compact subset of S¹ —
-- the topological precondition the Riesz–Markov construction of the scalar spectral measures μ_x consumes:
-- on compact σ(V), C(σV)=C_c(σV), so f↦⟨x,cfc f V x⟩ (CFC in hand via V∈unitary; H→L[ℂ]H is a StarOrderedRing) gives
-- a finite Borel μ_x by RealRMK.rieszMeasure — the first rung of the operator→PVM keystone. Axiom-free.
#print axioms QIQTH.Spectral.cayley_one_sub
#print axioms QIQTH.Spectral.cayley_one_sub_injective
#print axioms QIQTH.Spectral.cayley_one_sub_denseRange
-- ★★ P4 WALL — 1−V HAS DENSE RANGE (V = Cayley transform of a DENSELY-DEFINED self-adjoint A): cayley_one_sub_
-- denseRange — DenseRange (fun y => y − V y). From cayley_one_sub (y−V y = 2i·(A+i)⁻¹y), ran(1−V) = 2i·dom(A) =
-- 2i·stoneDomain U, dense (stoneDomain_dense) since scaling by 2i≠0 is a homeomorphism (Homeomorph.smulOfNeZero).
-- With cayley_one_sub_injective (ker(1−V)=0) this is the FULL statement that V is the Cayley transform of a
-- densely-defined self-adjoint A=i(1+V)(1−V)⁻¹. Axiom-free. Remaining (Mathlib gap): Borel/PVM on S¹ ⟹ Stone.
-- ★★ P4 WALL — 1 IS NOT AN EIGENVALUE OF V (Cayley consistency): cayley_one_sub — y − V y = 2i·(A+i)⁻¹y (with
-- z=(A+i)⁻¹y: (Az+iz)−(Az−iz)=2iz). cayley_one_sub_injective — ker(1−V)=0, i.e. y↦y−V y injective (from the
-- formula + (A+i)⁻¹ injective + 2i≠0). This is the precise condition that V=(A−i)(A+i)⁻¹ is the Cayley transform of
-- a densely-defined self-adjoint A: the inverse Cayley A=i(1+V)(1−V)⁻¹ is well-defined on ran(1−V)=the smooth domain.
-- Axiom-free. Remaining (Mathlib gap): the Borel/PVM on S¹ for V + transport to A's unbounded PVM ⟹ Stone.
#print axioms QIQTH.Spectral.cayley_spectrum_subset_circle
-- ★★ P4 WALL — SPECTRUM OF THE CAYLEY UNITARY ON THE UNIT CIRCLE: cayley_spectrum_subset_circle —
-- spectrum ℂ (cayleyUnitary U ⋯ : H →L[ℂ] H) ⊆ Metric.sphere 0 1 (spectrum.subset_circle_of_unitary applied to
-- cayley_mem_unitary). The geometric foundation of V's spectral theorem: its (eventual) circle-PVM is supported on
-- S¹, and the inverse Cayley map z↦i(1+z)(1−z)⁻¹ pulls S¹∖{1} back to the real spectrum of A=stoneGen U. Axiom-free.
-- Remaining (Mathlib gap): the Borel/PVM functional calculus on S¹ for V + transport to A's unbounded PVM ⟹ Stone.
#print axioms QIQTH.Spectral.cayley_mem_unitary
#print axioms QIQTH.Spectral.cayleyUnitaryElt
-- ★★ P4 WALL — CAYLEY UNITARY IS A C*-ALGEBRA UNITARY ELEMENT (CFC doorway): cayley_mem_unitary —
-- (cayleyUnitary U ⋯ : H →L[ℂ] H) ∈ unitary (H →L[ℂ] H), i.e. star V * V = V * star V = 1 (via
-- LinearIsometryEquiv.star_eq_symm: star ↑V = ↑V.symm, and V.symm∘V=V∘V.symm=id). cayleyUnitaryElt — V bundled as
-- a unitary (H →L[ℂ] H) element. This unlocks Mathlib's continuous functional calculus: V is unitary/normal so
-- cfc f V exists and spectrum ℂ V ⊆ circle. Axiom-free. Remaining (Mathlib gap): the Borel/PVM functional calculus
-- (∫ z dE for V) + transport to the unbounded spectral theorem for A ⟹ Stone U_t = exp(itA).
#print axioms QIQTH.Spectral.cayley_add
#print axioms QIQTH.Spectral.cayley_smul
#print axioms QIQTH.Spectral.cayleyUnitary
-- ★★★ P4 WALL — THE CAYLEY TRANSFORM IS A UNITARY H ≃ₗᵢ[ℂ] H: cayleyEquiv_symm_add/_smul — (A+i)⁻¹ is ℂ-linear
-- (additive + homogeneous, by injectivity of A+i + LinearPMap.map_add/map_smul of A). cayley_add/cayley_smul —
-- V=(A−i)(A+i)⁻¹ is ℂ-linear. cayleyLM : H →ₗ[ℂ] H bundles V as a LinearMap; cayleyUnitary : H ≃ₗᵢ[ℂ] H bundles it
-- as a UNITARY = LinearEquiv.ofBijective cayleyLM cayley_bijective + norm_map' := norm_cayley. This is the bounded
-- unitary operator of the spectral theorem — the object whose bounded spectral measure, transported back through
-- the Cayley correspondence, yields the unbounded spectral theorem for the self-adjoint A=stoneGen U (X=A_edge, P,
-- K). Axiom-free. Remaining (Mathlib gap): the bounded-PVM spectral theorem for V + the transport + Stone exp.
#print axioms QIQTH.Spectral.stoneGen_sub_I_bijective
#print axioms QIQTH.Spectral.cayley_bijective
-- ★★ P4 WALL — THE CAYLEY TRANSFORM IS A UNITARY: stoneGen_sub_I_bijective — A−i : dom(A)→H is a bijection
-- (mirror of A+i: injective from ‖x‖≤‖(A−i)x‖=‖(A+i)x‖ via the Cayley isometry, surjective from
-- stoneGen_sub_I_surjective). cayley_bijective — V=(A−i)(A+i)⁻¹ is bijective, = (stoneGen_sub_I_bijective).comp
-- (cayleyEquiv).symm.bijective (composition of the bijection A−i with the bijection (A+i)⁻¹). With norm_cayley
-- (‖V y‖=‖y‖) this makes V a UNITARY operator. Axiom-free. Remaining (Mathlib gap): bundle V as a unitary CLM +
-- the bounded-PVM spectral theorem + transport to the unbounded spectral theorem for A ⟹ Stone U_t=exp(itA).
#print axioms QIQTH.Spectral.cayley
#print axioms QIQTH.Spectral.norm_cayley
-- ★★ P4 WALL — THE CAYLEY TRANSFORM IS AN ISOMETRY: cayley U ⋯ y := (A−i)((A+i)⁻¹ y) is the Cayley transform
-- V=(A−i)(A+i)⁻¹ of the self-adjoint generator A=stoneGen U (cayleyEquiv = the bijection A+i:dom(A)≃H from
-- stoneGen_add_I_bijective, its .symm = (A+i)⁻¹). norm_cayley — ‖V y‖=‖y‖: with z=(A+i)⁻¹y (so (A+i)z=y),
-- ‖V y‖=‖(A−i)z‖=‖(A+i)z‖ (the Cayley isometry stoneGen_norm_cayley_eq)=‖y‖. With surjectivity (A−i also
-- bijective) this makes V a UNITARY — the operator whose bounded spectral measure transports to the unbounded
-- spectral theorem for A. Axiom-free. Remaining (Mathlib gap): V as a unitary CLM + bounded-PVM + Stone exp.
-- ★★ P4 WALL — A+i IS A BIJECTION dom(A)→H (the Cayley-transform foundation): stoneGen_add_I_bijective —
-- Function.Bijective (fun z : stoneDomain U => stoneGen U z + i•(z:H)). Injective from the bounded-below estimate
-- ‖x‖≤‖(A+i)x‖ (stoneGen_norm_le_norm_add_smul_I + LinearPMap.map_sub), surjective from stoneGen_add_I_surjective.
-- So (A+i)⁻¹ : H→dom(A) exists — the building block of the Cayley transform V=(A−i)(A+i)⁻¹ (a unitary, by the
-- Cayley isometry ‖(A−i)x‖=‖(A+i)x‖), whose bounded spectral measure transports to the unbounded spectral theorem
-- for A ⟹ Stone. Axiom-free. Remaining (Mathlib gap): the Cayley operator + bounded-PVM transport + Stone exp.
-- ★ P4 WALL — GÅRDING MOLLIFIED VECTORS (entry to essential self-adjointness): mollify U φ x := ∫ φ(t) U_t x dt.
-- mollify_integrable — the integrand φ(t)U_t x is integrable (continuous × compact support, φ∈Cc, U strongly cont).
-- mollify_apply_flow — the FLOW-SHIFT identity U_s x_φ = ∫ φ(t) U_{s+t}x dt (U_s through the Bochner integral via
-- integral_comp_comm + the group law). The algebraic core of Gårding: differentiating its RHS in s (under the
-- integral) places x_φ in the smooth domain. Axiom-free. (The differentiation step + {x_φ} dense = the carried
-- analytic frontier — differentiation under the Bochner integral + approximate identity, the genuine Mathlib gap.)
#print axioms QIQTH.borelFC_apply_norm_sq
-- expected: standard only — L² ISOMETRY (real form): ‖f(R)ζ‖²=∫‖f(ω)‖²dμ^R_ζ. Real restatement of
-- borelFC_inner_self (⟪x,x⟫=↑‖x‖², conj(f)·f=↑‖f‖² via Complex.mul_conj+normSq_eq_norm_sq). The directly-usable
-- form for the strong-holomorphy diff-quotient ‖q_z−d‖²=∫‖Δ_z−∂d‖²dμ^R_ζ→0 (dominated convergence).
#print axioms QIQTH.borelFC_inner_self
-- expected: standard only — ★★★ L² LINCHPIN for strong holomorphy: ⟪f(R)ζ,f(R)ζ⟫=∫ conj(f)·f dμ^R_ζ (=∫|f|²,
-- so ‖f(R)ζ‖²=∫|f|²dμ^R_ζ). Via ⟪Aζ,Aζ⟫=⟪ζ,A*Aζ⟫ (adjoint_inner_right) + A*=borelFC(conj f) (borelFC_adjoint) +
-- A*A=borelFC(conj f·f) (borelFC_mul) + spectral bridge ⟪ζ,g(R)ζ⟫=∫g dμ (inner_borelFC). THE key for STRONG
-- (Fréchet) holo of z↦d_z(R)ζ: difference-quotient ‖q−d‖²=∫|Δ_z−∂d|²dμ^R_ζ→0 by dominated conv (no Mathlib Dunford).
#print axioms QIQTH.rvdSpec_deviceOpReal
-- expected: standard only — OPERATOR-FORM real-axis value: D_ξ(t)=⟪ξ,(Δ^{it}·√R)ξ⟫. deviceOpReal S t :=
-- borelFC(rvdRC)(devSpecReal) is the bounded real-axis device operator (devSpecReal ω=d_t(ω)=u_t·√ω, ‖·‖≤√2
-- on σ(R)⊆[0,2], NO regular window); rvdSpec_deviceOpReal = inner_borelFC bridge ⟪ξ,deviceOpReal ξ⟫=∫d_t dμ,
-- the device √R-regularized analogue of rvdSpec_modUnitary (⟪ξ,Δ^{it}ξ⟫=∫u_t dμ). Operator-level Δ-side edge.
#print axioms QIQTH.devCorrExt_ofReal
-- expected: standard only — REAL-AXIS value (scalar): D_ξ(t)=∫ u_t·√ω dμ^R_ξ (devChar_ofReal under ∫). The
-- √r-weighted modular correlation = ⟪ξ,Δ^{it}√R ξ⟫ as operator expectation (operator id needs borelFC↔CFC.sqrt
-- product bridge, deferred). The Δ-side device edge data; U-side pairing (RvD's ⟨U-orbit, R-device-vector⟩) open.
#print axioms QIQTH.hasDerivAt_devCorrExt
#print axioms QIQTH.differentiableOn_devCorrExt
-- expected: standard only — ★★★ DEVICE strip extension HOLOMORPHIC on the open half-strip, NO regular window.
-- At z₀ with Im z₀∈(−1/2,0): differentiate devCorrExt under the spectral integral (hasDerivAt_integral_of_
-- dominated_loc_of_deriv_le) ⇒ (devCorrExt)'(z₀)=∫ i·log((2−ω)/ω)·d_{z₀}(ω) dμ. Dominators = the device's
-- regular-window-FREE constants: F bound √2 (devChar_norm_le_Icc), F' bound the devChar_deriv_norm_le const,
-- uniform on a slab nbhd s={c<Im z<d}, [c,d]⊂(−1/2,0)∋Im z₀ (c=(z₀.im−1/2)/2, d=z₀.im/2). Spectrum endpoints
-- ω∈{0,2} handled by hasDerivAt_devChar_Icc (orbit z-constant there). Holomorphy half of the bdd-holo half-strip
-- extension strip-uniqueness consumes — available for EVERY standard subspace (the RvD Prop 3.7 device payoff).
#print axioms QIQTH.devCorrExt_norm_le
-- expected: standard only — ★★★ DEVICE strip extension bound, NO regular window. devCorrExt S ξ z = ∫ devChar z
-- dμ^R_ξ (RvD Prop 3.7 device analogue of modCorrExt). ‖D_ξ(z)‖ ≤ √2·‖ξ‖² for ALL z with −1/2≤Im z≤0, for ANY
-- standard subspace — the √r factor bounds devChar by √2 over the WHOLE σ(R)⊆[0,2] (devChar_norm_le_Icc +
-- rvdRC_spectrum_mem_Icc), integrated against the finite μ^R_ξ (univ=‖ξ‖²). DECISIVE advantage over modCorrExt
-- (which needs σ(R)⊆[a,2−a]): the bounded-holomorphic half-strip input exists for EVERY standard subspace.
-- expected: standard only — boostUnitary_eq_vadd: boostUnitary t = DomAddAct.mk(−t)+ᵥ· (the project boost group IS
-- Mathlib's canonical Lp domain-translation; unitary_apply precomposes with flow(−t) ⇒ ξ(x−t), matches mk(−t)+ᵥξ via
-- add_comm + Equiv.symm_apply_apply). continuous_boostUnitary_apply: ★ STRONG CONTINUITY t↦boostUnitary t ξ, from
-- Mathlib's Lp.instContinuousVAddDomAddAct (Lebesgue translation-invariant+locally-finite+inner-regular) + the adapter
-- (continuous_id.vadd const)∘(mkHomeomorph.continuous∘neg). tendsto_boostUnitary_wedge: boostUnitary(−2πt)ξ→ξ as t→0
-- — the strong-continuity premise a Stone-generator construction of the boost-charge derivative consumes. Axiom-free.
#print axioms QIQTH.Fock.OneParticleBW.modularEnergy_eq_stressFlux
-- expected: standard only — modular energy = (2π/ℏ)·T_kk at the Hilbert level: from BW (hasDerivAt_modularEnergy_of_
-- boost, modular energy = boost energy) + hBoostCharge (boost-charge=stress-flux). NOTE the derivative is i·(real):
-- for a unitary group d/dt⟪ξ,U(t)ξ⟫=i·⟨ξ,Kξ⟩ is PURELY IMAGINARY — stated correctly as Complex.I*((2π/ℏ·T_kk):ℂ),
-- so hBoostCharge is physically SATISFIABLE (non-vacuous). An earlier real-valued form was vacuous; fixed.
#print axioms QIQTH.Fock.OneParticleBW.oneParticle_hFlux
-- expected: standard only — ★★★ the one-particle hFlux fully assembled from labelled inputs: hcarrier/standardness
-- (Reeh–Schlieder), hUniq (KMS-uniqueness BGL §2), hStrip (wedge strip/KMS BGL §4), hBoostCharge (boost-charge=
-- stress-flux). Derives EVERYTHING modular inside: boost-invariance of 𝒦_W, modUnitary 𝒦_W=boostUnitary (BW), and
-- modular energy=boost energy ⇒ d/dt⟪ξ,Δ^{it}ξ⟫=i·(2π/ℏ)T_kk. = hFlux at the Hilbert level. Axiom-free.
#print axioms QIQTH.Fock.OneParticleBW.component_hFlux_of_wedgeKMS
-- expected: standard only — ★★★ the one-particle↔COMPONENT bridge: from the wedge-KMS inputs + hBoostCharge +
-- hbridge (the localization identity HasDerivAt(⟪ξ,Δ^{it}ξ⟫)(i·kd) — "the null-generator modular energy IS the
-- one-particle modular energy of ξ_{x,v}"), oneParticle_hFlux pins the SAME correlation's derivative to i·(2π/ℏ)T_kk;
-- HasDerivAt.unique + cancel I (Complex.I_ne_zero) + real-cast inj ⇒ kd=(2π/ℏ)T_kk — the chain's REAL component
-- hFlux, derived. So hFlux's whole modular surface (BW, modular=boost energy, real-coeff descent) is DERIVED. Axiom-free.
-- ★ WEDGE-KMS ⇒ GR (WedgeKMSToGR.lean): hFlux consolidated into the single labelled wedge KMS property.
#print axioms QIQTH.WedgeKMSToGR.hFlux_of_wedgeKMS
-- expected: standard only — the boost heat-flux hFlux DERIVED from WedgeKMSFlux (per null generator, unpack the
-- wedge-KMS bundle + feed component_hFlux_of_wedgeKMS) ⇒ kd=(2π/ℏ)BL(T x)v. hFlux is now derived from the labelled
-- wedge KMS property, not assumed. Axiom-free.
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_from_wedge_kms
-- expected: standard only — ★★★ THE GOAL THEOREM. Einstein's eqs from QIQT-H capacity postulate + Klein positivity
-- modulo EXACTLY THREE labelled physics inputs: (1) the wedge KMS property hKMS (WedgeKMSFlux — standardness +
-- KMS-uniqueness + strip + localized boost-charge=stress-flux + per-generator state), which DERIVES hFlux via
-- hFlux_of_wedgeKMS; (2) matter conservation conserv (∇·(a·T)=0); (3) standard structural regularity (Lorentzian
-- congruence g=PᵀηP, Raychaudhuri focusing hFocus = kinematics, f-regularity hreg, per-generator differentiability).
-- QIQT supplies bound+saturation+Klein as THEOREMS ⇒ δS=ηδA derived; all geometry axiom-free. = qiqt_bekenstein_
-- gives_gr with hFlux replaced by the derived wedge-KMS flux. Verified: no sorry, no vacuous True hyps. Axiom-free.
#print axioms QIQTH.Fock.OneParticleBW.oneParticleBW_wedge_complete
-- expected: standard only — wedge BW with KMS-UNIQUENESS DERIVED: modUnitary=boostUnitary(−2π·) from hcarrier +
-- V=boost + genuine StripKMSrvd, via oneParticleBW_complete (RvD Thm 3.8). Boost structural facts (isometry/group/
-- continuity/𝒦-inv) all derived from boostUnitary lemmas. Replaces the bundled opaque hUniq + vacuous StripKMS.
#print axioms QIQTH.Fock.StressTensor.hasDerivAt_inner_boost_rapidityMomentum
-- expected: standard only — ★ Stress-tensor Route B, Phase 0: the boost-charge derivative with its RHS NAMED.
-- d/dt⟪ξ,boostUnitary(−2πt)ξ⟫|₀ = i·2π·rapidityMomentum f f', where rapidityMomentum f f' = Im∫conj(f)·f' is the
-- boost energy ⟪f,(−i∂_θ)f⟫. Names the scalar that hTkk identifies with (2π/ℏ)·T_kk; Phases 1–3 (horizon field →
-- null stress flux → Mellin/Plancherel) will turn rapidityMomentum into a DEFINED stress flux, discharging hTkk.
#print axioms QIQTH.Fock.StressTensor.horizonField_boostTest
-- expected: standard only — ★ Stress-tensor Route B, Phase 1: boost↔dilation intertwining of the horizon field.
-- horizonField m f λ = ∫θ Krep m f θ·exp(−iλ·nullMom m θ) (the wedge mode restricted to the horizon, nullMom m θ
-- = (m/√2)e^{−θ}); horizonField m (boostTest a f) λ = horizonField m f (e^a·λ): the Lorentz boost acts on the
-- horizon as the DILATION λ↦e^aλ. The horizon-level Bisognano–Wichmann fact making modular flow = horizon dilation,
-- so K = ∫_H λ T_kk dλ (Phase 2–3). Proof: Krep_boost (boost = rapidity translation) + integral_add_right_eq_self.
#print axioms QIQTH.Fock.StressTensor.Tkk_boostTest
-- expected: standard only — ★ Stress-tensor Route B, Phase 2: the null stress component T_kk = ‖∂_λ φ_H‖² DEFINED,
-- and its scaling: Tkk[boostTest a f](λ) = (e^a)²·Tkk[f](e^a λ) (weight-2 conformal dim of ∂_λφ). horizonFieldDeriv
-- (= ∂_λ horizonField as an integral), Tkk := ‖horizonFieldDeriv‖², stressFluxKK := ∫_ℝ λ·Tkk (the two-sided modular/
-- boost charge K=∫_H λ T_kk dλ) are now DEFINED objects (T_kk no longer a label). Phase 3: stressFluxKK = −2π·rapidityMomentum.
#print axioms QIQTH.Fock.StressTensor.stressFluxKK_boostTest
-- expected: standard only — ★ Stress-tensor Route B, Phase 3a′ (unconditional half): DILATION-INVARIANCE of the FULL-LINE
-- horizon flux. stressFluxKK m (boostTest a f) = stressFluxKK m f — the boost charge K=∫_ℝ λ T_kk dλ is boost-invariant
-- (the Noether/KMS consistency: modular Hamiltonian commutes with the boost). Weight-2 scaling of Tkk cancels the weight-(−2)
-- Jacobian of the horizon dilation λ↦e^aλ. Proof: Tkk_boostTest + Measure.integral_comp_mul_left. NB: stressFluxKK is now
-- the FULL-LINE ∫_ℝ (was wrongly ∫_{λ>0}; GPT-5.5 consult — half-line ≠ const·rapidityMomentum). Phase 3b (now TRACTABLE,
-- no distributions): stressFluxKK = −2π·rapidityMomentum via the sesquilinear Fourier identity on the k-line.
#print axioms QIQTH.Fock.StressTensor.horizonFieldDeriv_eq_kIntegral
-- expected: standard only — ★ Stress-tensor Route B, Phase 3b-i: horizonFieldDeriv (=∂_λφ_H) IS a Fourier integral on the
-- null-momentum k-line. horizonFieldDeriv m f λ = ∫_{x>0} (−i·Krep m f(rapInv m x))·e^{−iλx}dx, via the change of variables
-- θ↦k=nullMom m θ=(m/√2)e^{−θ} (inverse rapInv m x=log(m/√2)−log x; Jacobian |dk/dθ|=k cancels the explicit nullMom factor).
-- Proof: integral_image_eq_integral_abs_deriv_smul + nullMom bijection ℝ→(0,∞) (rapInv_nullMom/nullMom_rapInv/injective/
-- image_univ/hasDerivAt). Entry point to the sesquilinear-Fourier evaluation (Phase 3b-ii ⟹ −2π·rapidityMomentum).
#print axioms QIQTH.Fock.StressTensor.fourierIntegral_exp_bridge
-- expected: standard only — ★ Stress-tensor Route B, Phase 3b-ii (convention bridge): 𝓕 g (λ/2π) = ∫ g(x)·e^{−iλx}dx.
-- Identifies the physicists' Fourier integral (from 3b-i) with Mathlib's 𝓕 (Real.fourierIntegral, whose convention carries
-- the 2π in the exponent), so the Fourier API / sesquilinear Parseval applies. Purely mechanical (fourier_real_eq_integral_
-- exp_smul + the 2π exponent cancellation); no analytic hypotheses. Remaining 3b-ii: ψ_H=𝓕[B] (IBP) + sesquilinear pairing + θ↔k.
#print axioms QIQTH.Fock.StressTensor.horizonFieldDeriv_eq_fourier
-- expected: standard only — ★ Stress-tensor Route B, Phase 3b-ii (consolidation): χ_H=∂_λφ_H IS a Mathlib Fourier transform.
-- horizonFieldDeriv m f λ = 𝓕 (horizonAmp m f)(λ/2π), horizonAmp := (Ioi 0).indicator (x↦−i·Krep m f(rapInv m x)). Combines
-- 3b-i (k-line integral) + the convention bridge + indicator-extension to ℝ. Makes the weak sesquilinear Parseval directly
-- applicable to χ_H. Next: the ψ_H=𝓕[B] partner (IBP) + the sesquilinear pairing ⟹ stressFluxKK = −2π·rapidityMomentum.
#print axioms QIQTH.Fock.StressTensor.inner_deriv_eq_I_mul_rapidityMomentum
-- expected: standard only — ★ Stress-tensor Route B, Phase 3b-ii: SELF-ADJOINTNESS of −i∂_θ. ∫conj(f)·f' = i·rapidityMomentum
-- f f' for smooth decaying f (Re∫conj(f)f'=0, the momentum operator is Hermitian). The piece that turns the Parseval output
-- ∫conj(A)B = i∫conj(K)K' into the REAL −2π·rapidityMomentum. Proof: ∫conj(f)f' + conj(∫conj(f)f') = ∫ d/dθ|f|² = 0 via the
-- full-line FTC integral_eq_zero_of_hasDerivAt_of_integrable + HasDerivAt.star. Generic (hyps: f differentiable + integrable f,f'·f).
#print axioms QIQTH.Fock.StressTensor.stressFluxKK_eq_of_flux
-- expected: standard only — ★★ Stress-tensor Route B, Phase 3b-ii ASSEMBLY: stressFluxKK m f = −2π·rapidityMomentum a a',
-- GIVEN hFlux (the Parseval/Fourier-deriv computation: ↑stressFluxKK = 2π·i·∫conj(a)a'). Combines hFlux with the proven
-- self-adjointness (∫conj(a)a'=i·rapidityMomentum): the two i factors give i²=−1 ⟹ the real −2π·rapidityMomentum. hFlux is
-- the ONE remaining deferred piece (weak sesquilinear Parseval on χ_H=𝓕(horizonAmp), ψ_H=𝓕(−iA'), + k↦θ change of vars) — a
-- genuine standard Mathlib-provable theorem (Fourier inversion + integral_sesq_fourierIntegral_eq_neg_flip), NOT vacuous/conjecture.
#print axioms QIQTH.Fock.StressTensor.real_fourier_mul_formula
-- expected: standard only — ★ Stress-tensor Route B, Phase 3b-ii: the multiplication formula ∫ 𝓕A·g = ∫ A·𝓕g (self-adjointness
-- of the real Fourier transform 𝓕). From Mathlib's VectorFourier.integral_fourierIntegral_smul_eq_flip + flip_innerₗ (real
-- inner product symmetric ⟹ L.flip=L, so NO Fourier inversion needed). The engine of the Parseval pairing ∫conj(𝓕A)·𝓕B =
-- ∫conj(A)·B that (with the Fourier-derivative ψ_H=𝓕[B] and k↦θ change of vars) discharges hFlux. Real progress on hFlux.
#print axioms QIQTH.Fock.StressTensor.fourier_conj_parseval
-- expected: standard only — ★★ Stress-tensor Route B, Phase 3b-ii: the PARSEVAL PAIRING ∫conj(𝓕A)·𝓕B = ∫conj(A)·B
-- (Plancherel, conjugate form). From Mathlib's sesquilinear VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip with
-- M=innerSL ℂ + Fourier inversion Continuous.fourierInv_fourier_eq (𝓕⁻(𝓕B)=B). Hyps: A integrable; B continuous+integrable,
-- 𝓕B integrable. This is the analytic HEART of hFlux — now PROVEN, not bundled. Remaining for hFlux: ψ_H=𝓕(−iA') (Fourier-deriv)
-- + k↦θ change of vars + Krep on-shell diff/decay; then χ_H=𝓕(horizonAmp) (done) + this Parseval ⟹ hFlux ⟹ stressFluxKK_eq_of_flux.
#print axioms QIQTH.Fock.StressTensor.fourier_parseval_deriv
-- expected: standard only — ★★ Stress-tensor Route B, Phase 3b-ii: ∫conj(𝓕A)·𝓕(deriv A) = i·rapidityMomentum A (deriv A).
-- Chains fourier_conj_parseval (B:=deriv A) with the self-adjointness inner_deriv_eq_I_mul_rapidityMomentum. The spectral-side
-- evaluation of the horizon flux: once Mathlib's fourier_deriv (𝓕(deriv A)=2πi·w·𝓕A) moves the affine weight λ into 𝓕(deriv A),
-- this gives the rapidity momentum. Remaining for hFlux: apply fourier_deriv + the λ=2πw rescale + horizonAmp instantiation + Krep regularity.
#print axioms QIQTH.Fock.StressTensor.fourier_weighted_pairing
-- expected: standard only — ★★ Stress-tensor Route B, Phase 3b-ii: the affine-weighted spectral pairing
-- ∫ w, conj(𝓕A w)·(w·𝓕A w) = (2π)⁻¹·rapidityMomentum A (deriv A). Mathlib's fourier_deriv (𝓕(deriv A)=2πi·w·𝓕A) moves the
-- weight w onto 𝓕(deriv A); fourier_parseval_deriv evaluates; the 2πi and the self-adjoint i combine to the real (2π)⁻¹. This
-- is the w-weighted norm of χ_H=𝓕A — the shape of stressFluxKK after the λ=2πw rescale. Remaining: ‖·‖² real cast + λ rescale + horizonAmp + Krep regularity.
#print axioms QIQTH.Fock.StressTensor.weighted_pairing_real
-- expected: standard only — ★★ Stress-tensor Route B, Phase 3b-ii: the REAL w-weighted Fourier norm ∫ w, w·‖𝓕A w‖² =
-- (2π)⁻¹·rapidityMomentum A (deriv A). The real form of fourier_weighted_pairing via conj(z)·z=‖z‖²
-- (Complex.normSq_eq_conj_mul_self + normSq_eq_norm_sq) + integral_ofReal. Remaining for hFlux: λ=2πw rescale (→stressFluxKK
-- = 2π·rapidityMomentum(horizonAmp)) + k↦θ change of vars (→rapidityMomentum(Krep)) + Krep on-shell diff/decay (Differentiable ℝ horizonAmp).
#print axioms QIQTH.Fock.StressTensor.flux_integral_eq
-- expected: standard only — ★★★ Stress-tensor Route B, Phase 3b-ii: the WHOLE generic spectral computation —
-- ∫ λ, λ·‖𝓕A(λ/2π)‖² = 2π·rapidityMomentum A (deriv A). The λ=2πw rescale (Measure.integral_comp_mul_left) puts the (2π)²
-- weight·Jacobian against weighted_pairing_real's (2π)⁻¹. This IS stressFluxKK m f once A=horizonAmp m f (horizonFieldDeriv_eq_fourier).
-- Remaining for hFlux: instantiate A=horizonAmp + k↦θ change of vars (rapidityMomentum(horizonAmp)↔rapidityMomentum(Krep)) + Krep regularity.
#print axioms QIQTH.Fock.StressTensor.stressFluxKK_eq_rapMom
-- expected: standard only — ★★★ Stress-tensor Route B, Phase 3b-ii: stressFluxKK m f = 2π·rapidityMomentum(horizonAmp m f)(deriv …).
-- flux_integral_eq instantiated at A=horizonAmp m f (via horizonFieldDeriv_eq_fourier: χ_H=𝓕 A). The horizon stress flux IS a rapidity
-- momentum. Hypotheses = the genuine on-shell regularity of horizonAmp (differentiable/integrable, its deriv, its 𝓕) — the gating
-- Krep-regularity, isolated as labeled hyps (true for nicely-decaying test fns). Remaining for hFlux: k↦θ change of vars (→∫conj(Krep)Krep', the sign).
#print axioms QIQTH.Fock.StressTensor.horizonAmp_hasDerivAt
-- expected: standard only — ★ Stress-tensor Route B, Phase 3b-ii: the horizon amplitude's derivative. For x>0,
-- HasDerivAt (horizonAmp m f) ((i/x)·kd(rapInv m x)) x where kd = the wedge mode's rapidity derivative (HasDerivAt Krep kd). Chain
-- rule for −i·Krep∘rapInv (Ioi 0 open ⟹ indicator locally smooth; rapInv'=−1/x). The explicit B=−iA' form, the input to the k↦θ
-- change of variables relating rapidityMomentum(horizonAmp) to ∫conj(Krep)·Krep'. Isolates the differentiation; needs HasDerivAt Krep.
#print axioms QIQTH.Fock.StressTensor.horizonAmp_inner_deriv
-- expected: standard only — ★★ Stress-tensor Route B, Phase 3b-ii: the k↦θ change of variables. ∫conj(horizonAmp m f)·deriv(horizonAmp m f)
-- = −∫conj(Krep m f)·kd (kd=Krep's rapidity deriv). Integrand vanishes x≤0 (indicator); for x>0, horizonAmp_hasDerivAt + conj(−iz)=i·conj z
-- give (−1/x)conj(Krep)·kd; integral_image_eq_integral_abs_deriv_smul (nullMom, |nullMom'|=nullMom cancels 1/x) + the k=e^{−θ} orientation flip → the minus.
#print axioms QIQTH.Fock.StressTensor.stressFluxKK_eq_neg_rapMom
-- expected: standard only — ★★★★ Stress-tensor Route B TARGET: stressFluxKK m f = −2π·rapidityMomentum(Krep m f)(Krep'). The DEFINED
-- free-field horizon null stress flux ∫_H λ T_kk dλ equals −2π·(rapidity-momentum boost charge of the one-particle wedge mode) — exactly
-- the scalar hTkk asserted. Combines stressFluxKK_eq_rapMom (=2π·rapidityMomentum(horizonAmp)) + horizonAmp_inner_deriv (k↦θ flip). Discharges
-- the scalar stress-flux identification hTkk of the QIQT→GR boost-charge=stress-flux input, modulo the genuine on-shell regularity of the wedge mode (labeled hyps).
#print axioms QIQTH.Fock.StressTensor.boostEnergy_eq_neg_stressFlux
-- expected: standard only — ★★★ Stress-tensor Route B → GR bridge: (2π·∫conj(Krep m f)·Krep').im = −stressFluxKK m f. The boost
-- energy in the EXACT form wedge_hBoostCharge_of_smooth's hTkk uses ((2π·∫conj(f)f').im) equals −stressFluxKK. So defining the GR
-- chain's T_kk := −(ℏ/2π)·stressFluxKK makes hTkk ((2π/ℏ)T_kk=(2π∫conj(f)f').im) hold by stressFluxKK_eq_neg_rapMom — the bundled
-- scalar T_kk is now the DEFINED, proven free-field horizon stress flux. Modulo the same on-shell regularity (labeled hyps).
#print axioms QIQTH.Fock.StressTensor.Krep_integrand_hasDerivAt
-- expected: standard only — ★ Stress-tensor Route B: pointwise θ-derivative of the Krep integrand (toward discharging the last
-- regularity gate, Krep differentiability). θ↦e^{−iη(p_m(θ),x)}·f(x) is differentiable with deriv e^{−iη}·(−i·m(x₀sinh θ−x₁cosh θ))·f(x),
-- since ∂_θ η(p_m(θ),x)=m(x₀sinh θ−x₁cosh θ) (minkowskiDot_massShell + cosh'=sinh,sinh'=cosh; HasDerivAt.ofReal_comp/cexp/mul_const). The
-- h_diff ingredient of Krep's rapidity differentiability; the full kd=Krep' adds the dominated-convergence bound (integrable for C_c^∞ f).
#print axioms QIQTH.Fock.StressTensor.Krep_deriv_norm_bound
-- expected: standard only — ★ Stress-tensor Route B: the domination bound (h_bound ingredient). For |θ|≤R, the Krep θ-derivative
-- integrand is ≤ m·cosh R·(|x₀|+|x₁|)·‖f x‖ (‖e^{iφ}‖=1 via Complex.norm_exp; |sinh θ|,|cosh θ|≤cosh R via abs_sinh/cosh_abs/cosh_le_cosh).
-- Continuous + compactly-supported in x for such f ⟹ integrable — the domination the differentiation-under-the-integral for kd=Krep' needs.
#print axioms QIQTH.Fock.StressTensor.Krep_bound_integrable
-- expected: standard only — ★ Stress-tensor Route B: bound_integrable ingredient. For continuous compactly-supported f, the bound
-- m·cosh R·(|x₀|+|x₁|)·‖f x‖ is continuous + compactly-supported (vanishes where f does) ⟹ integrable. With Krep_integrand_hasDerivAt
-- (h_diff) and Krep_deriv_norm_bound (h_bound), the differentiation-under-the-integral for HasDerivAt (Krep m f) kd is now assemblable.
#print axioms QIQTH.Fock.StressTensor.Krep_hasDerivAt
-- expected: standard only — ★★★ Stress-tensor Route B: Krep IS rapidity-differentiable (the HARD regularity gate discharged). For
-- continuous compactly-supported f, HasDerivAt (Krep m f) kd θ₀ with kd θ₀=(1/√2)∫ e^{−iη}·(−i·m(x₀sinh θ₀−x₁cosh θ₀))·f dx (=Krep').
-- Differentiation under the integral (hasDerivAt_integral_of_dominated_loc_of_deriv_le) via Krep_integrand_hasDerivAt (h_diff) +
-- Krep_deriv_norm_bound (h_bound) + Krep_bound_integrable. DISCHARGES the hkd hypothesis of stressFluxKK_eq_neg_rapMom/boostEnergy_eq_neg_stressFlux.
#print axioms QIQTH.Fock.StressTensor.stressFluxKK_eq_neg_rapMom_cptSupp
-- expected: standard only — ★★★★ Stress-tensor Route B, hkd DISCHARGED: for a continuous compactly-supported test function f,
-- ∃ kd (=Krep'), (∀θ HasDerivAt (Krep m f)(kd θ)θ) ∧ stressFluxKK m f = −2π·rapidityMomentum(Krep m f)(kd). Instantiates
-- stressFluxKK_eq_neg_rapMom with Krep_hasDerivAt, REMOVING the hardest regularity gate (Krep differentiability) from the labelled
-- inputs. Only the softer horizon-amplitude regularity (Differentiable ℝ horizonAmp + integrability) remains labelled (Schwartz-on-rapidity).
#print axioms QIQTH.Fock.Localization.schwartz_Krep_decay_sq
-- expected: standard only — ★★ Stress-tensor Route B (softer regularity, decay gate): for f Schwartz, m≠0,
-- ‖Krep m f θ‖ ≤ 16π²·(∫‖f‖+∫‖Df‖+∫‖D²f‖)/(√2 m²)·(cosh θ)⁻². The n=2 Fourier-decay estimate (one derivative more
-- than schwartz_Krep_memLp's n=1); test vector v=(p₀,−p₁) gives L v p=(p₀²+p₁²)/2π ≥ (m cosh θ)²/2π. Gates L¹/boundary-diff.
#print axioms QIQTH.Fock.StressTensor.integrable_inv_const_sq_add
-- expected: standard only — ★ Stress-tensor Route B: Integrable (fun x => (c²+x²)⁻¹) for c>0, via Mathlib
-- integrable_inv_one_add_sq + the domination (c²+x²)⁻¹ ≤ (min(c²,1))⁻¹(1+x²)⁻¹. The Cauchy dominator for ‖horizonAmp‖.
#print axioms QIQTH.Fock.StressTensor.horizonAmp_integrable
-- expected: standard only — ★★★ Stress-tensor Route B (softer regularity, INTEGRABILITY DISCHARGED): for f Schwartz, m>0,
-- Integrable (horizonAmp m f). The (cosh)⁻² Schwartz decay (schwartz_Krep_decay_sq) + the exact boundary map
-- cosh(rapInv x)=(c²+x²)/(2cx) (cosh_log, c=m/√2) dominate ‖horizonAmp x‖ ≤ 4Cc²(c²+x²)⁻¹ by the integrable Cauchy
-- kernel (integrable_inv_const_sq_add). Removes the L¹ half of the remaining horizon-amplitude regularity. Differentiable
-- ℝ horizonAmp (boundary at x=0, needs Krep' decay too) is the last labelled softer gate.
#print axioms QIQTH.Fock.StressTensor.horizonAmp_differentiable
-- expected: standard only — ★★★ Stress-tensor Route B (softer regularity, DIFFERENTIABILITY DISCHARGED): for f Schwartz,
-- m>0, given the wedge derivative kd (HasDerivAt Krep kd), Differentiable ℝ (horizonAmp m f). Three regions: x<0 locally
-- 0; x>0 via horizonAmp_hasDerivAt; x=0 the BIFURCATION SURFACE — the (cosh)⁻² Schwartz decay (schwartz_Krep_decay_sq) +
-- cosh(rapInv t)=(c²+t²)/(2ct) force the quadratic envelope ‖horizonAmp t‖≤K t², so slope→0 (squeeze_zero_norm) ⟹ deriv 0.
-- Discharges hAd. NOTE: the boundary case needs ONLY the cosh⁻² decay of Krep (the O(t²) envelope), NOT a Krep' decay.
#print axioms QIQTH.Fock.StressTensor.horizonAmp_norm_le
-- expected: standard only — Stress-tensor Route B: the pointwise Cauchy envelope ‖horizonAmp m f x‖ ≤ 4Cc²(c²+x²)⁻¹
-- (c=m/√2, C the cosh⁻² decay constant). The single bound feeding both L¹ (horizonAmp_integrable) and L² (hff).
#print axioms QIQTH.Fock.StressTensor.integrable_inv_const_sq_add_sq
-- expected: standard only — Stress-tensor Route B: Integrable ((c²+x²)⁻¹)² for c>0 (squared Cauchy dominator), via
-- integrable_inv_const_sq_add + ((c²+x²)⁻¹)² ≤ (c²)⁻¹(c²+x²)⁻¹. Bounds ‖horizonAmp‖².
#print axioms QIQTH.Fock.StressTensor.horizonAmp_sq_integrable
-- expected: standard only — ★★ Stress-tensor Route B (softer regularity, hff DISCHARGED): for f Schwartz, m>0,
-- Integrable (fun θ => conj(horizonAmp θ)·horizonAmp θ). ‖conj A·A‖=‖A‖² ≤ (4Cc²)²((c²+x²)⁻¹)² via horizonAmp_norm_le
-- + integrable_inv_const_sq_add_sq. Discharges hff (the A-self-pairing integrability). Uses only the cosh⁻² decay (no Krep').
#print axioms QIQTH.Fock.StressTensor.schwartz_Krep_hasDerivAt
-- expected: standard only — ★★★ Stress-tensor Route B (class unification): Krep IS rapidity-differentiable for a SCHWARTZ f
-- (companion of Krep_hasDerivAt, which needed compact support), same explicit kd=Krep'. Differentiation under the integral with
-- the two integrabilities from the Schwartz tail: F=e^{iη}·f is L¹ (‖e^{iη}‖=1, f integrable), bound m cosh R(|x₀|+|x₁|)‖f‖ is
-- L¹ ((|x₀|+|x₁|)≤2‖x‖, integrable_pow_mul). Lets hkd be discharged on the SAME Schwartz class as hA/hAd/hff. Provides kd for the
-- remaining deriv gates (hdA/hdAc/hFdA/h1/h2), whose closure needs the kd=Krep' DECAY (the next sub-campaign).
#print axioms QIQTH.Fock.Localization.coordMul_apply
-- expected: standard only — Stress-tensor Route B (Krep' decay foundation): coordMul j f = x_j·f as a SchwartzMap (coordinate
-- multiplication preserves Schwartz), via SchwartzMap.bilinLeftCLM with (z,r)↦r•z and the temperate-growth projection x↦x j.
#print axioms QIQTH.Fock.Localization.Krep_coordMul
-- expected: standard only — Stress-tensor Route B: Krep m (coordMul j f) θ = (1/√2)·minkowskiFourier(x_j f)(massShell m θ) —
-- bridges the cosh⁻² decay (schwartz_Krep_decay_sq on coordMul j f) into the Krep' moment decomposition.
#print axioms QIQTH.Fock.Localization.minkowskiFourier_coordMul_decay
-- expected: standard only — ★★ Stress-tensor Route B (Krep' decay input): ∃ C≥0, ∀θ ‖minkowskiFourier(x_j f)(massShell m θ)‖
-- ≤ C·(cosh θ)⁻². The (cosh)⁻² decay of the mass-shell FT of the moment x_j f (Schwartz), via Krep_coordMul + schwartz_Krep_decay_sq.
-- This is THE moment-decay input for the (cosh)⁻¹ decay of the rapidity derivative Krep' (kd), which unblocks hdA/hdAc/hFdA/h1/h2.
#print axioms QIQTH.Fock.Localization.kd_integral_eq_moments
-- expected: standard only — ★★ Stress-tensor Route B: the Krep' moment split — ∫ e^{iη}(−i m(x₀sinh−x₁cosh))f = −i m sinh θ·𝓕(x₀f)
-- + i m cosh θ·𝓕(x₁f) on the mass shell. Pointwise pull-out of real θ-constants (push_cast+ring) + integral linearity (each moment
-- integrand L¹ since ‖e^{iη}(x_j•f)‖=‖coordMul j f‖) separates the two mass-shell Fourier transforms.
#print axioms QIQTH.Fock.Localization.kd_norm_le
-- expected: standard only — ★★★ Stress-tensor Route B (THE Krep' DECAY): ∃C≥0,∀θ ‖(1/√2)∫e^{iη}(−i m(x₀sinh−x₁cosh))f‖ ≤ C·(cosh θ)⁻¹.
-- = ‖Krep'(θ)‖ ≤ C cosh⁻¹. Combines kd_integral_eq_moments (split) + minkowskiFourier_coordMul_decay (cosh⁻² moment decay) + |sinh|≤cosh
-- (abs_sinh_le_cosh): the m cosh θ prefactors meet cosh⁻² to leave cosh⁻¹. Since ∫cosh⁻¹=π this makes kd integrable — the analytic core
-- unblocking the remaining horizon-amplitude derivative gates hdA/hdAc/hFdA/h1/h2 (deriv horizonAmp = (i/x)kd(rapInv x) on x>0).
#print axioms QIQTH.Fock.StressTensor.Krep_deriv_norm_le
-- expected: standard only — ★★ Stress-tensor Route B: ‖deriv (Krep m f) θ‖ ≤ C·(cosh θ)⁻¹ (f Schwartz, m>0). Packages kd_norm_le
-- against the genuine deriv via schwartz_Krep_hasDerivAt.deriv, so kd:=deriv(Krep m f) is bounded AND measurable (measurable_deriv).
#print axioms QIQTH.Fock.StressTensor.horizonAmp_deriv_integrable
-- expected: standard only — ★★★ Stress-tensor Route B (hdA DISCHARGED): Integrable (deriv (horizonAmp m f)) for f Schwartz, m>0.
-- Off x=0 (null set, irrelevant): deriv = (i/x)·Krep'(rapInv x) on x>0, 0 on x<0; with cosh(rapInv x)=(c²+x²)/(2cx) + Krep_deriv_norm_le
-- the 1/x cancels ⟹ ‖deriv horizonAmp x‖ ≤ 2Cc(c²+x²)⁻¹, integrable (integrable_inv_const_sq_add). deriv measurable (measurable_deriv);
-- deriv horizonAmp =ᵐ derivH via {0} null (compl_mem_ae_iff). Discharges hdA — 5 of 9 regularity gates done.
#print axioms QIQTH.Fock.StressTensor.horizonAmp_deriv_le
-- expected: standard only — Stress-tensor Route B: shared aux — AEStronglyMeasurable (deriv horizonAmp) ∧ ∃D≥0, ‖deriv horizonAmp x‖
-- ≤ D(c²+x²)⁻¹ a.e. The Cauchy bound + measurability core feeding hdA/h1/h2.
#print axioms QIQTH.Fock.StressTensor.horizonAmp_deriv_mul_integrable
-- expected: standard only — ★★ Stress-tensor Route B (h1 DISCHARGED): Integrable (conj(deriv A)·A), A=horizonAmp m f (f Schwartz, m>0).
-- ‖conj A'·A‖=‖A'‖‖A‖ ≤ (2Cc(c²+x²)⁻¹)(B(c²+x²)⁻¹) via horizonAmp_deriv_le × horizonAmp_norm_le', squared dominator integrable_inv_const_sq_add_sq.
#print axioms QIQTH.Fock.StressTensor.horizonAmp_mul_deriv_integrable
-- expected: standard only — ★★ Stress-tensor Route B (h2 DISCHARGED): Integrable (conj(A)·deriv A). Same product bound as h1.
-- 7 of 9 regularity gates done (hkd hA hAd hff hdA h1 h2); remaining hdAc (needs super-exp Krep' decay) + hFdA (𝓕(deriv) integrable).
#print axioms QIQTH.Fock.StressTensor.horizonAmp_deriv_continuous
-- expected: standard only — ★★★ Stress-tensor Route B (hdAc DISCHARGED): Continuous (deriv (horizonAmp m f)), f Schwartz, m>0.
-- deriv horizonAmp = derivH globally (=(i/x)Krep'(rapInv x) on x>0, 0 on x≤0; x=0 via horizonAmp_hasDerivAt_zero). derivH continuous:
-- off 0 via Krep'∈C⁰ (schwartz_Krep_deriv_continuous) + rapInv/div continuity; at x=0 the SUPER-exp (cosh)⁻² decay (Krep_deriv_norm_le_sq)
-- + cosh(rapInv t)=(c²+t²)/(2ct) give ‖derivH t‖≤4Cc²|t|/(c²+t²)²→0 (squeeze_zero_norm). 8 of 9 gates done; only hFdA remains.
#print axioms QIQTH.Fock.StressTensor.stressFluxKK_eq_neg_rapMom_schwartz
-- expected: standard only — ★★★★ Stress-tensor Route B for the SCHWARTZ class, 8 of 9 gates: for f Schwartz, m>0,
-- stressFluxKK m f = −2π·rapidityMomentum(Krep)(Krep') with the ONLY remaining hypothesis hFdA : Integrable(𝓕(deriv(horizonAmp m f))).
-- Assembles the 8 axiom-free discharges (hkd hA hAd hff hdA h1 h2 hdAc) into stressFluxKK_eq_neg_rapMom. hFdA needs the C³ layer or an
-- L²-Plancherel (Lp.inner_fourier_eq) refactor of fourier_conj_parseval avoiding Fourier inversion. The single open technical gate of Route B.
#print axioms QIQTH.Fock.StressTensor.fourier_lp_ae_eq
-- expected: standard only — ★★★★ Stress-tensor Route B (hFdA UNBLOCK): the density-free L²-Plancherel coincidence. For g∈L¹∩L²,
-- ⇑(𝓕_{L²}(g.toLp 2)) =ᵐ 𝓕 g (classical Fourier integral). Proved WITHOUT density: both, as tempered distributions, pair with a
-- complex Schwartz Ψ by ∫(𝓕Ψ)·g = ∫Ψ·(𝓕g) (real_fourier_mul_formula = multiplication formula), so they agree as distributions,
-- and ae_eq_of_integral_contDiff_smul_eq (distribution injectivity) gives the a.e. equality. KEY: Lp.fourier_toTemperedDistribution_eq,
-- TemperedDistribution.fourier_apply, HasCompactSupport.toSchwartzMap (real Cc^∞ test → complex Schwartz). The bridge importing
-- Mathlib's L² Plancherel isometry (Lp.inner_fourier_eq) into the classical-𝓕 Parseval pairing — the route to discharging hFdA.
#print axioms QIQTH.Fock.StressTensor.fourier_conj_parseval_L2
-- expected: standard only — ★★★★ Stress-tensor Route B: inversion-free conjugate Parseval. For A,B∈L¹∩L², ∫conj(𝓕A)·𝓕B=∫conj(A)·B,
-- via Lp.inner_fourier_eq + fourier_lp_ae_eq + L2.inner_def. Needs only L¹∩L² membership, NOT Fourier inversion (no hFdA). Replaces fourier_conj_parseval.
#print axioms QIQTH.Fock.StressTensor.stressFluxKK_eq_neg_rapMom_schwartz_closed
-- expected: standard only — ★★★★★ ROUTE B FULLY CLOSED (Schwartz class): for ANY Schwartz f, m>0, stressFluxKK m f = −2π·rapidityMomentum(Krep)(Krep')
-- with NO remaining hypotheses. The last gate hFdA is GONE — the Parseval chain (fourier_parseval_deriv_L2 → … → stressFluxKK_eq_neg_rapMom_L2) uses
-- the L² Plancherel pairing (fourier_conj_parseval_L2), needing only horizonAmp,deriv∈L² (horizonAmp_memLp_two/horizonAmp_deriv_memLp_two). The
-- free-field horizon stress flux = boost momentum, UNCONDITIONALLY for Schwartz test functions, axiom-free.
#print axioms QIQTH.Fock.StressTensor.boostEnergy_eq_neg_stressFlux_schwartz_closed
-- expected: standard only — ★★★★★ The hTkk scalar FULLY CLOSED (Schwartz): (2π·∫conj(Krep)·Krep').im = −stressFluxKK m f for ANY Schwartz f, no
-- hypotheses. T_kk := −(ℏ/2π)·stressFluxKK makes the labelled hTkk an unconditional theorem — the bundled stress scalar IS the proven horizon stress flux.
#print axioms QIQTH.Fock.OneParticleBW.wedge_hbridge_of_smooth
-- expected: standard only — ★★ WedgeKMSFlux LOCALIZATION slot hbridge DERIVED for smooth wedge states: the modular-
-- energy deriv d/dt⟪ξ,Δ^{it}ξ⟫|₀ = i(2π/ℏ)T_kk via BW (oneParticleBW_wedge_complete: Δ=boost) reducing modular→boost,
-- then wedge_hBoostCharge_of_smooth. With wedge_hBoostCharge_of_smooth, BOTH WedgeKMSFlux derivative identities are now
-- derived from one smooth state ⟹ the bundled physics collapses to the SINGLE scalar hTkk:(2π/ℏ)T_kk=2π·Im∫f̄f' (the
-- free-field boost/modular energy = stress flux). All analytic/operator/modular machine-checked; only the scalar remains.
#print axioms QIQTH.Fock.StressTensor.wedge_boostCharge_eq_neg_stressFlux
-- expected: standard only — ★★★★★ ROUTE B WIRED INTO THE WEDGE BOOST CHARGE. For ANY Schwartz g, m>0, the boost/modular-energy
-- derivative of the free-field wedge mode Krep m g equals i·(−stressFluxKK m g) — the conserved boost Killing charge IS the
-- proven Route-B horizon stress flux, with NO hTkk hypothesis. Discharges hTkk of hasDerivAt_inner_boostUnitary_imaginary
-- (Tkk:=−(ℏ/2π)·stressFluxKK) via boostEnergy_eq_neg_stressFlux_schwartz_closed; all wedge-mode regularity supplied here
-- (schwartz_Krep_memLp, Krep_integrable, MemLp.star.integrable_mul, Krep_deriv_bounded, schwartz_Krep_hasDerivAt). The hTkk
-- scalar — the last labelled physics input of the localization slot — is now an UNCONDITIONAL theorem for the free field.
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_from_wedge_kms_raychaudhuri
-- expected: standard only — ★★★★ THE GOAL THEOREM with the FOCUSING input ALSO derived. Replaces raw hFocus
-- (ad=R_kk) with the kinematic Raychaudhuri data: a null geodesic congruence Vcong v per direction (hVC/hgeo/
-- hVval), at equilibrium (hequil), + the area↔θ modelling identification harea. The focusing step ad=BL(Ric)v
-- is DERIVED via hFocus_of_raychaudhuri (= axiom-free raychaudhuri_focusing_at_equilibrium). So BOTH the modular
-- side (RvD Thm 3.8, only WedgeKMSFlux_complete labelled) AND the focusing side (Raychaudhuri) are now derived;
-- the labelled surface shrinks to the area↔θ identification + the equilibrium/Clausius physics.
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_from_wedge_kms_complete
-- expected: standard only — ★★★★ THE GOAL THEOREM with KMS-uniqueness DERIVED. Identical to qiqt_gr_from_wedge_kms
-- but the wedge KMS input is the GENUINE non-vacuous WedgeKMSFlux_complete (bundling StripKMSrvd = RvD Def 3.4),
-- NOT the old opaque hUniq + trivially-satisfiable StripKMS. The BW identification modUnitary=boost is now DERIVED
-- from the machine-checked RvD Theorem 3.8 (oneParticleBW_complete) rather than assumed. Closes target #2 (GPT-5.5-pro
-- audit): the one remaining modular-theory ASSUMPTION of the GR chain is replaced by a theorem. Axiom-free, no sorry.

-- Item A (QIQT_GR_DISCHARGE_PLAN.md), Phase A1a — wedge-mode analytic continuation foundations:
#print axioms QIQTH.Fock.WedgeAnalyticity.KrepCont_ofReal
-- expected: standard only — ★★ A1a: the analytically continued localized amplitude KrepCont m f ζ agrees with
-- Krep m f θ on the real axis (ζ=↑θ). Foundation for the free-field Hardy proof of StripKMSrvd (boost-KMS / BW).
#print axioms QIQTH.Fock.WedgeAnalyticity.massShellℂ_add_pi_I
-- expected: standard only — ★★ the iπ-shift identity p_m(ζ+iπ)=−p_m(ζ) (cosh/sinh add-π-i), the analytic engine
-- of the boundary conjugation ψ_f(θ+iπ)=conj(ψ_f(θ)) that gives the KMS bottom edge.
#print axioms QIQTH.Fock.WedgeAnalyticity.norm_kernel_le_one
-- expected: standard only — ★★★ A1c: the WEDGE-DAMPING bound. ‖exp(−i·p_m(θ+iλ)·x)‖=exp(m sinλ(sinhθ x₀−coshθ x₁))≤1
-- for x in the right wedge (0<x₁−x₀, 0<x₁+x₀), 0≤λ≤π — the analytic engine that puts ψ_f in the Hardy strip H²(S_π).
#print axioms QIQTH.Fock.WedgeAnalyticity.hasDerivAt_kernel
-- expected: standard only — ★★ A1b (pointwise): the kernel ζ↦exp(−i·p_m(ζ)·x) is entire in rapidity, with
-- dK/dζ = K·(−i·(m sinhζ·x₀ − m coshζ·x₁)) (chain rule through exp). The per-x half of the holomorphy argument.
#print axioms QIQTH.Fock.WedgeAnalyticity.hasDerivAt_kernel_mul
-- expected: standard only — ★★ A1b-ii-α: the full integrand ζ↦K(ζ,x)·f(x) is complex-differentiable, deriv
-- kernelDeriv·f(x) — the h_diff ingredient for the dominated parametric-derivative assembly of KrepCont holomorphy.
#print axioms QIQTH.Fock.WedgeAnalyticity.continuous_kernel_in_x
-- expected: standard only — ★ A1b-ii: continuity of the kernel in x (measurability of the integrand).
#print axioms QIQTH.Fock.WedgeAnalyticity.differentiable_KrepCont
-- expected: standard only — ★★★★ A1b COMPLETE: KrepCont m f (the analytic continuation of the localized wedge
-- amplitude) is ENTIRE in rapidity for f continuous with compact support. Via hasDerivAt_KrepCont (dominated
-- parametric-derivative theorem over ℂ): per-x derivative hasDerivAt_kernel_mul + ball-domination from
-- norm_kernelDeriv_le (‖K'‖ ≤ exp(B)·B) and the compact bound ‖x‖≤M on tsupport f. The holomorphy half of the
-- free-field Hardy proof of StripKMSrvd (boost-KMS / Bisognano–Wichmann).
#print axioms QIQTH.Fock.WedgeAnalyticity.KrepCont_add_pi_I
-- expected: standard only — ★★★ A3: the iπ BOUNDARY CONJUGATION ψ_f(θ+iπ)=conj(ψ_f(θ))=conj(Krep m f θ) for
-- REAL f (via kernel_add_pi_I: K(θ+iπ,x)=conj K(θ,x), from p_m(θ+iπ)=−p_m(θ) + integral_conj). This is what
-- turns the KMS top edge ⟪η,V_t ξ⟫ into the bottom edge ⟪V_t ξ,η⟫ — the bottom-edge engine of StripKMSrvd.
#print axioms QIQTH.Fock.WedgeAnalyticity.norm_KrepCont_le
-- expected: standard only — ★★ A2 (sup-bound half): ‖KrepCont m f (θ+iλ)‖ ≤ (1/√2)·∫‖f‖ on the strip 0≤λ≤π for
-- wedge-supported f (from the damping ‖K(ζ,x)‖≤1 pushed through the integral). The L^∞-on-strip half of the
-- H²(S_π) bound; the L²-in-θ decay (strip extension of the cosh⁻² estimates) is the remaining analytic frontier.
#print axioms QIQTH.Fock.WedgeAnalyticity.integrable_exp_neg_const_mul_cosh
-- expected: standard only — ★ A2 decay building block: exp(−c·coshθ) integrable over ℝ (c>0), Gaussian
-- domination via coshθ≥θ²/8. The θ-integrability the interior-λ wedge-mode strip decay reduces to.
#print axioms QIQTH.Fock.WedgeAnalyticity.integrable_cosh_mul_exp_neg_const_mul_cosh
-- expected: standard only — ★ A2 derivative-decay block: cosh s·exp(−c·cosh s) integrable (c>0), via cosh s ≤
-- (1/c)exp((c/2)cosh s) (Real.two_mul_le_exp). The integrand-DERIVATIVE bound (cosh poly factor vs damping)
-- reduces to this — the integrability for the z-derivative domination of F's parametric holomorphy (DiffContOnCl).
#print axioms QIQTH.Fock.WedgeAnalyticity.exists_wedge_margin
-- expected: standard only — ★ A2: uniform wedge margin. tsupport f ⊆ open wedge (compact) ⟹ ∃δ>0,
-- δ≤x₁∓x₀ on tsupport f (continuous positive fn on compact attains positive min). Gives the uniform damping
-- rate coshθ·x₁−sinhθ·x₀ ≥ δ·coshθ powering the interior-λ L² decay (the pointwise route, sidestepping Minkowski).
#print axioms QIQTH.Fock.WedgeAnalyticity.norm_KrepCont_le_exp_decay
-- expected: standard only — ★★ A2 step 1: POINTWISE STRIP-DECAY. ‖KrepCont m f (θ+iλ)‖ ≤ (1/√2)(∫‖f‖)·exp(−(m sinλ δ)coshθ)
-- for wedge-supported f (margin δ), 0≤λ≤π. The double-exponential θ-decay (interior λ) making KrepCont(·+iλ)∈L².
-- Uses norm_kernel_eq (‖K‖=exp(m sinλ(sinhθ x₀−coshθ x₁))) + norm_kernel_le_exp_decay (margin ⟹ ≤exp(−c coshθ)).
#print axioms QIQTH.Fock.WedgeAnalyticity.memLp_KrepCont_strip
-- expected: standard only — ★★★ A2 step 2 (CORE): interior-λ L² MEMBERSHIP. For m>0, wedge-supported f,
-- λ∈(0,π), θ↦KrepCont m f (θ+iλ) ∈ L²(dθ). By POINTWISE domination ‖KrepCont(θ+iλ)‖≤C·exp(−c coshθ)
-- (norm_KrepCont_le_exp_decay) against the L² fn C·exp(−c cosh) (sq integrable via integrable_exp_neg_const_mul_cosh)
-- + MemLp.mono'. NO Minkowski integral inequality — the previously-flagged Mathlib gap is fully off the path.
#print axioms QIQTH.Fock.BoostKMS.inner_boostUnitary_KrepL2
-- expected: standard only — ★★ A4 (real-axis edge): ⟪KrepL2 g, boostUnitary a (KrepL2 f)⟫ = ∫ conj(Krep g θ)·Krep f(θ−a) dθ.
-- Bridges the abstract Lp ℂ 2 inner product (L2.inner_def) + boostUnitary action (boostUnitary_KrepL2, = rapidity
-- translation Krep_boost) to the concrete rapidity integral — the orbit correlation f(t)=⟪η,V_t ξ⟫ of StripKMSrvd.
#print axioms QIQTH.Fock.BoostKMS.symm_edge_eq_inner
-- expected: standard only — ★★ A4: the KMS TOP EDGE f(t)=⟪η,V_t ξ⟫ in symmetric (KMS-function) form. The
-- symmetric integral ∫ conj(Krep g(θ+πt))·Krep f(θ−πt) dθ (= t-real value of F(z)=∫conj(KrepCont g(θ+πz̄))·KrepCont f(θ−πz))
-- equals ⟪KrepL2 g, boostUnitary(2πt)(KrepL2 f)⟫, via symm_edge_eq_shifted (change of vars) + inner_boostUnitary_KrepL2.
#print axioms QIQTH.Fock.BoostKMS.kmsFun_ofReal_eq_inner
-- expected: standard only — ★★★ A4: the KMS FUNCTION F defined (kmsFun = ∫ conj(KrepCont g(conj(θ+πz)))·KrepCont f(θ−πz)),
-- and its REAL-AXIS (top-edge) value F(t) = ⟪KrepL2 g, boostUnitary(2πt)(KrepL2 f)⟫ (kmsFun_ofReal via KrepCont_ofReal,
-- then symm_edge_eq_inner). The StripKMSrvd witness F with its top edge discharged; bottom edge + DiffContOnCl remain.
#print axioms QIQTH.Fock.BoostKMS.kmsFun_sub_I
-- expected: standard only — ★★★ A4: the KMS BOTTOM EDGE F(t−i)=conj(F(t)) for real f,g. At z=t−i the iπ-shift puts
-- both KrepCont args at Im=+π, so KrepCont_add_pi_I (A3) collapses each to conj(Krep…): F(t−i)=∫Krep g(θ+πt)·conj(Krep f(θ−πt))
-- =conj(F(t)). With the top edge + ⟪V_t ξ,η⟫=conj⟪η,V_t ξ⟫, this is StripKMSrvd's bottom edge f(t−i)=⟪V_t ξ,η⟫.
-- BOTH KMS edges of the StripKMSrvd witness now proven; DiffContOnCl + boundedness + closedness-to-𝒦_W remain.
#print axioms QIQTH.Fock.BoostKMS.differentiable_reflKrepCont
-- expected: standard only — ★★ A4 (holomorphy ingredient): the reflected amplitude u↦conj(KrepCont g(conj u)) is
-- ENTIRE (Schwarz reflection conj∘F∘conj holo, via DifferentiableAt.star_conj + differentiable_KrepCont). The g-factor
-- H^# of the kmsFun integrand — confirms F's holomorphy is reachable (DiffContOnCl not blocked).
#print axioms QIQTH.Fock.BoostKMS.differentiable_kmsIntegrand
-- expected: standard only — ★★ A4: the kmsFun INTEGRAND is entire in z (g-factor = reflKrepCont∘affine,
-- f-factor = KrepCont∘affine, product differentiable). The per-θ h_diff ingredient for F's parametric-integral
-- holomorphy (DiffContOnCl). Remaining: the dominated z-derivative assembly + continuity-to-boundary + boundedness.
#print axioms QIQTH.Fock.BoostKMS.continuous_kmsIntegrand_in_theta
-- expected: standard only — ★ A4: the kmsFun integrand is continuous in θ (KrepCont continuous ∘ continuous
-- θ-maps + conj) — the hF_meas (measurability) ingredient for F's parametric-integral holomorphy.
#print axioms QIQTH.Fock.BoostKMS.stripKMSrvd_pair_of_regularity
-- expected: standard only — ★★★★ A4 CONSOLIDATION: StripKMSrvd for a wedge generator pair REDUCED TO the
-- analytic regularity of kmsFun. Given only hDCC (DiffContOnCl on the strip) + hbd (bounded), the ∃F witness
-- holds: F=kmsFun, top edge ⟪η,V_t ξ⟫ (kmsFun_ofReal_eq_inner), bottom edge ⟪V_t ξ,η⟫ (kmsFun_sub_I +
-- inner_conj_symm), V_t=boostUnitary(2πt). PRECISELY ISOLATES THE REMAINING FRONTIER: everything (F, both KMS
-- edges, Lp bridge, boost-orbit id) is DONE axiom-free; only DiffContOnCl+boundedness of one explicit function remains.

#print axioms QIQTH.Fock.BoostKMS.stripKMSrvd_pair
-- expected: standard only — ★★★★★ A4: StripKMSrvd (RvD Def 3.4) FULLY DISCHARGED for a wedge generator pair.
-- The θ-truncation+Hadamard three-lines+annular-difference route gives kmsFun_diffContOnCl + norm_kmsFun_le_closed,
-- feeding stripKMSrvd_pair_of_regularity. The banked citable result: the explicit free-field boost-KMS witness.
#print axioms QIQTH.Fock.BoostKMS.stripKMSrvd_closure
-- expected: standard only — ★★★★★ A4 (c3+c4): the KMS witness extended to the CLOSURE of the nice generators.
-- Nice approximants → bcf_cauchySeq → complete-space limit b in closedStrip→ᵇℂ → F (b on strip, 0 off). Holomorphy
-- via Weierstrass (TendstoLocallyUniformlyOn.differentiableOn); boundary via Filter.Tendsto.inner. NO density theorem.
#print axioms QIQTH.Fock.BoostKMS.stripKMSrvd_boostUnitary
-- expected: standard only — ★★★★★ A4: StripKMSrvd (fun t => boostUnitary(2πt)) (closure(niceWedgeGenSet m)) — the
-- free-field Bisognano–Wichmann KMS condition (RvD Def 3.4) as a THEOREM on the standard wedge subspace.
#print axioms QIQTH.Fock.BoostKMS.oneParticleBW_niceWedge
-- expected: standard only — ★★★★★ A4 DISCHARGE: modUnitary S t = boostUnitary(2πt) for S with carrier
-- closure(niceWedgeGenSet m), with EVERY labelled analytic input discharged (hKMS←stripKMSrvd_boostUnitary;
-- hInv←boostUnitary_mapsTo_niceWedgeGenSet+Set.MapsTo.closure; group structure←boost laws) via oneParticleBW_complete.
-- The labelled hKMS is ELIMINATED. Sign finding: StripKMSrvd holds for exactly one boost sign, and it is +2π.
#print axioms QIQTH.Fock.BoostKMS.oneParticleBW_niceWedge_of_standard
-- expected: standard only — ★ A4 FRONTIER ISOLATION: modUnitary = boost(2πt) for the nice-core wedge standard
-- subspace, conditional ONLY on hsep (separating) + hcyc (cyclic) — the niceWedgeStandardSubspace constructor over
-- the elementary carrier niceWedgeClosedSubmodule (= closure(niceWedgeGenSet)). The ENTIRE remaining gap to an
-- unconditional free-field one-particle BW is exactly those two Reeh–Schlieder lattice identities; all else is built.

#print axioms QIQTH.Fock.BoostKMS.niceWedge_isCyclic_of_dense
-- expected: standard only — ★ cyclic lattice identity hcyc ⟸ Dense(span_ℂ niceWedgeGenSet); the mulI instance-diamond
-- cracked via defeq-tolerant exact/refine. Engine: ClosedSubmodule_sup_mulI_eq_top_of_dense (general K + G⊆K).
#print axioms QIQTH.Fock.BoostKMS.niceWedge_dense_of_total
-- expected: standard only — ★ Dense(span_ℂ) ⟸ totality of {KrepL2 f}, via the COMPLEX orthogonal complement
-- (orthogonal_eq_bot_iff + topologicalClosure_eq_top_iff) — unambiguous InnerProductSpace ℂ, no diamond.
#print axioms QIQTH.Fock.BoostKMS.niceWedge_isSeparating_of_no_complex_line
-- expected: standard only — ★ separating hsep ⟸ "no complex line" (v∈K ∧ I•v∈K ⟹ v=0), DIRECT via the mulI
-- membership (closedSubmodule_smul_I_mem_of_mem_mulI, ℂ scalarSMulCLE) — bypasses the ᗮ ℝ-instance tangle entirely.
#print axioms QIQTH.Fock.BoostKMS.oneParticleBW_niceWedge_reehSchlieder
-- expected: standard only — ★★★★★ THE one-particle Bisognano–Wichmann reduced to its TWO analytic Reeh–Schlieder
-- inputs: modUnitary = boost(2πt) given ONLY (a) separating = no complex line (Pauli–Jordan symplectic non-degeneracy)
-- and (b) cyclic = wedge-totality ∫ conj(Krep f)·h=0 ∀ nice f ⟹ h=0 (Paley–Wiener). NO lattice/instance/KMS hypotheses;
-- every structural step machine-checked axiom-free. Item A's STRUCTURAL reduction COMPLETE.

-- ★★★★★★ THE TWO ANALYTIC REEH–SCHLIEDER INPUTS, BOTH NOW DISCHARGED (2026-06-23) — the frontier is CLOSED.
#print axioms QIQTH.Fock.CyclicWitness.niceWedgeCyclic_pos_mass
-- expected: standard only — ★ CYCLIC (wedge-totality) for ALL m>0: the complete L²-Wiener–Tauberian theorem
-- (boost_orbit_total_of_fourier_ne_zero) fed by a width-scaled wedge bump (R=π/(4m)) whose 1D amplitude is nonzero
-- by cos-positivity on the support. The Paley–Wiener input is now a THEOREM, no edge-of-the-wedge analyticity.
#print axioms QIQTH.Fock.CyclicWitness.strip_eqZero_of_top_edge_zero
-- expected: standard only — strip boundary-uniqueness: holomorphic on the open strip, continuous+bounded on the
-- closure, zero on the whole top edge ⟹ zero on the bottom edge. Asymmetric Hadamard three-lines (top const 0) +
-- continuity. The modular/KMS uniqueness engine of the separating proof.
#print axioms QIQTH.Fock.CyclicWitness.niceWedgeSeparating_pos_mass
-- expected: standard only — ★ SEPARATING (Pauli–Jordan symplectic non-degeneracy) for ALL m>0: PURE modular/KMS.
-- From stripKMSrvd_closure the boost-KMS witnesses F_vv (v,v) and F_c (iv,v); top edge F_c(t)=i·F_vv(t) ⟹ D:=F_c−i·F_vv
-- vanishes on the top edge ⟹ (strip_eqZero_of_top_edge_zero) on the bottom edge ⟹ −2i⟪U_t v,v⟫=0 ⟹ (t=0) ⟪v,v⟫=0 ⟹ v=0.
#print axioms QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional
-- expected: standard only — ★★★★★★ THE free-field one-particle Bisognano–Wichmann, FULLY UNCONDITIONAL: modUnitary S t
-- = boostUnitary(2πt) with NO Reeh–Schlieder hypotheses at all (both separating + cyclic discharged internally).
-- "modular flow = geometric boost" is a fully closed, axiom-free theorem — NO cited frontier on the one-particle level.
#print axioms QIQTH.Fock.hasDerivAt_modularEnergy_of_boost_pos
-- expected: standard only — sign-flipped (+2π) copy of hasDerivAt_modularEnergy_of_boost: given the SATISFIABLE BW
-- identification modUnitary S = boostUnitary(+2π·), the modular-energy derivative = the boost-energy derivative.
#print axioms QIQTH.Fock.freeField_modularEnergy_eq_boostCharge
-- expected: standard only — ★ FREE-FIELD modular-energy = stress-flux derivative with BW supplied INTERNALLY from
-- oneParticleBW_niceWedge_unconditional in the satisfiable +2π convention (no labelled hUniq/hStrip, no sign mismatch).
-- Phase 2 of QIQT_GR_FREEFIELD_COMPLETION_PLAN: only remaining input is the +2π boost-charge derivative (Phase 3).
#print axioms QIQTH.Fock.hasDerivAt_inner_boostUnitary_imaginary_pos
-- expected: standard only — the +2π boost-charge derivative (purely imaginary), by the t→−t reflection
-- (HasDerivAt.comp_const_sub) of the −2π hasDerivAt_inner_boostUnitary_imaginary; reuses the hard
-- dominated-convergence proof. d/dt ⟪ξ,boostUnitary(2πt)ξ⟫|₀ = i·((−(2π·∫conj(f)·f')).im).
#print axioms QIQTH.Fock.freeField_oneParticle_hFlux
-- expected: standard only — ★★★ THE free-field one-particle hFlux FULLY ASSEMBLED in the satisfiable +2π
-- convention: HasDerivAt(t↦⟪ξ,modUnitary S t ξ⟫)(i·(2π/ℏ·T_kk)) 0 for any smooth wedge state ξ=f.toLp, with the
-- BW identification AND the boost-charge derivative both supplied internally (axiom-free). Only labelled input is
-- the scalar physics identification hTkk: (2π/ℏ)·T_kk = (−(2π·∫conj(f)·f')).im. Phase 3 of the freefield plan.
#print axioms QIQTH.Fock.freeField_component_hFlux
-- expected: standard only — ★★★ free-field per-generator flux equation kd = (2π/ℏ)·T_kk, the +2π/nice-wedge analog
-- of component_hFlux_of_wedgeKMS_complete. Routes freeField_oneParticle_hFlux + derivative uniqueness into the EXACT
-- kd-conclusion qiqt_bekenstein_gives_gr consumes — bypassing the −2π/wedgeGenSet bundle. Only remaining inputs are
-- hbridge (kd = modular energy of localized mode) + hTkk (localization map, Gap 2). Phase 4 of the freefield plan.
#print axioms QIQTH.Fock.freeField_softData_nonvacuous
-- expected: standard only — NON-VACUITY of the localization datum's soft shell: the analytic hypotheses of
-- freeField_component_hFlux (MemLp/Integrable/measurable/HasDerivAt/bounded ‖f'‖) are simultaneously satisfiable,
-- witnessed by the Gaussian mode θ↦exp(−θ²), B=1 (2|x|≤x²+1≤exp(x²)). Only the modeling core (hbridge,hTkk) stays labelled.

-- ★★★★★★ THE `conserv` INPUT OF THE QIQT→GR DERIVATION, DISCHARGED for the explicit Klein–Gordon field (2026-06-23).
#print axioms QIQTH.Curvature.pd_gi_eq
-- expected: standard only — INVERSE-METRIC COMPATIBILITY ∇gi=0: ∂_ν gi^{λβ} = −∑σ Γ^λ_νσ gi^{σβ} − ∑σ Γ^β_νσ gi^{σλ}.
-- Contract the differentiated inverse relation pd_metric_inv_identity with gi^{λμ}; gi_g_delta + pd_g_eq + δ-contractions.
#print axioms QIQTH.Curvature.hHessGrad_eq
-- expected: standard only — the Hessian-gradient identity g^{μρ}∂_μφ(∇∇φ)_ρν = ½∂_ν(g^{αβ}∂_αφ∂_βφ): decompose
-- LHS=T1−T2, RHS=½(R1+R2+R3) (pd_gradSq_eq); T1=R2, R2=R3, T2=−½R1 (pd_gi_eq + christoffel_symm + gi-symmetry).
#print axioms QIQTH.Curvature.div02_kgStress_conserved_of_KG
-- expected: standard only — ∇^μ T_μν = 0 for the explicit free KG stress tensor T=kgStress, with hHessGrad supplied
-- internally; the ONLY remaining hypothesis is the equation of motion □φ=m²φ (genuine matter physics).
#print axioms QIQTH.Curvature.kg_conserv
-- expected: standard only — ★★★★★★ EXACTLY the `conserv : ∀ x ν, div02 g gi (fun y a' b => a·T y a' b) ν x = 0` input
-- consumed by WedgeKMSToGR/qiqt_gr_from_wedge_kms_complete, with T=kgStress: the coupling a scales out
-- (div02_const_smul) and the divergence vanishes. The matter-conservation input is now a drop-in theorem.
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg
-- expected: standard only — ★★★★★★★ THE END-TO-END QIQT→GR FOR THE EXPLICIT KG FIELD: a·kgStress_μν = G_μν + Λ·g_μν,
-- with T=kgStress concrete and conserv discharged internally (kg_conserv_of_contDiff) + hT_symm proved from metric
-- symmetry. No abstract matter T, no conserv hypothesis — the QIQT→GR matter sector is concrete and machine-checked.
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg_raychaudhuri
-- expected: standard only — the kinematic-Raychaudhuri form of the above: hFocus replaced by the null-congruence
-- Raychaudhuri data (hgeo/hequil/harea), still with T=kgStress concrete and conserv discharged internally.

-- Phases 4-5 of QIQT_GR_FREEFIELD_COMPLETION_PLAN: the FREE-FIELD QIQT→GR capstone.
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_from_flux_complete
-- expected: standard only — the GR theorem taking the per-generator flux EQUATION kd x v = (2π/ℏ)·BL(T x)v directly
-- (what qiqt_bekenstein_gives_gr consumes), instead of the WedgeKMSFlux_complete bundle. Convention-agnostic entry.
#print axioms QIQTH.WedgeKMSToGR.freeField_kd_conclusion
-- expected: standard only — the ∀-wrap of freeField_component_hFlux: per null generator the localization datum
-- (hbridge, hTkk) + freeField_oneParticle_hFlux gives kd x v = (2π/ℏ)·BL(T x)v. All modular/BW/boost machine-checked.
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_freefield
-- expected: standard only — ★★★★★★ THE FREE-FIELD QIQT→GR CAPSTONE: a·kgStress_μν = G_μν + Λ·g_μν with the wedge-KMS
-- modular flux supplied by the axiom-free +2π one-particle BW machinery (NOT a labelled WedgeKMSFlux_complete bundle).
-- Geometry hC/hric_symm/hreg + matter conserv + hT_symm all discharged internally for kgStress. Only labelled inputs:
-- the Clausius/area-saturation physics + the per-generator localization map (hbridge, hTkk) (Gap 2).
-- T3-3 localization ladder (hbridge/hFocus/hWarea discharged; hTkk transparent):
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_freefield_geom
-- T3-1: the four Clausius/area-law premises are theorems of the finite QIQT entropy model + area-capacity id:
#print axioms QIQTH.ClausiusFiniteWitness.clausius_package_from_finite_model
-- GR scaffolding: capstone hS/hK HasDerivAt facts derived from smoothness (Shannon/KL deriv; KL flat at equil):
#print axioms QIQTH.EntropyDeriv.shannon_hasDerivAt
#print axioms QIQTH.EntropyDeriv.KL_hasDerivAt_self
#print axioms QIQTH.EntropyDeriv.KE_hasDerivAt
-- A3: the witness packages hS/hK with the SAME rate (KL flat at equilibrium) — capstone derivs not independent:
#print axioms QIQTH.ClausiusFiniteWitness.clausius_deriv_package_from_finite_model
-- T3-1 Stage 2: thermo capstone — hsat/hDnn/hD0 discharged via the witness; only the dynamical bound labelled:
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_freefield_thermo
-- T3-3 continuum: per-generator hTkk from one universal mode calibration (ff = field-gradient · g₀):
#print axioms QIQTH.WedgeKMSToGR.localized_mode_hTkk
-- T3-3-C2: a concrete Gaussian wave packet satisfies the calibration (Im ∫ conj g₀ g₀' = −1/ℏ):
#print axioms QIQTH.WedgeKMSToGR.gaussMode_calibration
-- GR scaffolding C: the WHOLE width family hits the same 2π/ℏ calibration (not Gaussian-specific):
#print axioms QIQTH.WedgeKMSToGR.gaussModeA_calibration
-- GR scaffolding C3: the family's regularity block (hfd/hf'_meas/hB/hf2/hf_int for the capstone ff):
#print axioms QIQTH.WedgeKMSToGR.gaussModeA_hasDerivAt
#print axioms QIQTH.WedgeKMSToGR.gaussModeA'_norm_le
#print axioms QIQTH.WedgeKMSToGR.gaussModeA_memLp
#print axioms QIQTH.WedgeKMSToGR.gaussModeA_integrable_fn
-- T3-3-C3: free-field QIQT→GR with the localization mode CONSTRUCTED from φ — hTkk discharged:
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_freefield_gaussian
-- Maximally-discharged capstone: T3-1 (entropy from finite record) + T3-3-C3 (mode from φ) combined:
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_freefield_complete
-- T3-GR-Raychaudhuri: hWgeo/hWequil from W covariantly constant; flat-metric witness:
#print axioms QIQTH.Curvature.raychaudhuri_setup_of_covConst
#print axioms QIQTH.Curvature.covDerivVec_constMetric_const
-- GR scaffolding B: area-derivative hA from W covariantly constant (θ=0 ⟹ area-rate 0 ⟹ constant area):
#print axioms QIQTH.Curvature.expansion_eq_zero_of_covConst
#print axioms QIQTH.Curvature.area_hasDerivAt_of_covConst
-- complete capstone with hWgeo/hWequil collapsed to one covariant-constancy condition:
#print axioms QIQTH.WedgeKMSToGR.qiqt_gr_freefield_complete_covCong

-- Sakharov Stage C: per-mode Gaussian entanglement entropy (Srednicki building block of the area law).
#print axioms QIQTH.GaussianStateEntropy.gaussModeEntropy_half
#print axioms QIQTH.GaussianStateEntropy.gaussModeEntropy_hasDerivAt
#print axioms QIQTH.GaussianStateEntropy.gaussModeEntropy_deriv_pos
#print axioms QIQTH.GaussianStateEntropy.gaussModeEntropy_nonneg
#print axioms QIQTH.GaussianStateEntropy.gaussModeEntropy_continuous
#print axioms QIQTH.GaussianStateEntropy.gaussModeEntropy_pos
-- the multi-mode SUM (the literal Srednicki entropy formula S = Σᵢ S(νᵢ)); area-SCALING is the frontier.
#print axioms QIQTH.GaussianStateEntropy.gaussStateEntropy_nonneg
#print axioms QIQTH.GaussianStateEntropy.gaussStateEntropy_pure
#print axioms QIQTH.GaussianStateEntropy.gaussStateEntropy_eq_zero_iff
-- the area-law SEED: entropy is supported only on the entangled (supra-floor) modes; pure modes drop out.
#print axioms QIQTH.GaussianStateEntropy.gaussStateEntropy_eq_sum_active
-- concrete entangled instance: the two-mode squeezed vacuum (ν=cosh(2s)/2) realizes the entropy formula.
#print axioms QIQTH.GaussianStateEntropy.twoModeSqueezedSympEig_ge_half
#print axioms QIQTH.GaussianStateEntropy.twoModeSqueezedSympEig_half_iff
#print axioms QIQTH.GaussianStateEntropy.twoModeSqueezed_entropy_pos
#print axioms QIQTH.GaussianStateEntropy.twoModeSqueezed_entropy_zero
-- the n=1 Williamson case: symplectic eigenvalue ν=√det from a 2×2 covariance; uncertainty det≥1/4 ⟹ ν≥½.
#print axioms QIQTH.GaussianStateEntropy.oneModeSympEig_ge_half
#print axioms QIQTH.GaussianStateEntropy.oneModeSympEig_pure
#print axioms QIQTH.GaussianStateEntropy.oneModeSympEig_entropy_nonneg
#print axioms QIQTH.GaussianStateEntropy.oneModeSympEig_eq_sqrt_det
#print axioms QIQTH.GaussianStateEntropy.det_conj_eq_of_det_one
#print axioms QIQTH.GaussianStateEntropy.oneModeSympEig_symplectic_invariant
-- ★ WILLIAMSON n=1 symplectic INVARIANCE: ν=√det(cov) is unchanged under symplectic congruence M↦SMSᵀ (det S=1,
-- Sp(2,ℝ)=SL(2,ℝ)) — so ν is a basis-independent physical invariant (the defining feature of the Williamson
-- spectrum; lets ν be read off any canonical frame). The N-mode normal-form reduction stays the labelled frontier.
#print axioms QIQTH.Sakharov.sakharov_ratio
#print axioms QIQTH.Sakharov.geometric_quarter
#print axioms QIQTH.Sakharov.heatkernel_ratio_eq_geometric
-- ★ SAKHAROV 1/4 RATIO (Lean mirror of scripts/sakharov_kg.py, Stages A+B) — the circularity-clean algebraic core:
-- sakharov_ratio: S_ent=A·b/(48π·reg), 1/G_ind=b/(12π·reg) ⟹ S_ent/(A/G_ind)=1/4 with the matter coefficient b,
-- regulator reg, area A, and π ALL cancelling (the 1/4 is the OUTPUT, never an input). geometric_quarter: 4π/16π=1/4
-- (the conical-deficit/EH geometric origin). heatkernel_ratio_eq_geometric: (1/48π)/(1/12π)=4π/16π (both 1/4).
-- HONEST SCOPE: formalizes the RATIO cancellation only; the heat-kernel coefficients 48π/12π are physics INPUTS
-- (Seeley–DeWitt a₂, reproduces Susskind–Uglum/Solodukhin), and the area-law SCALING S∝A (Williamson, M3), the
-- VALUE of G_ind/ℓ_P (species/UV datum), and cross-species universality remain the labelled frontiers/carried input.

-- Tier A1 of QIQT_GR_DISCHARGEABLE_PLAN: discharge hric_symm.
#print axioms QIQTH.Curvature.ricci_symm
-- expected: standard only — Ricci symmetry R_σν=R_νσ via lowered-Riemann pair-symmetry (lowered_riemann_pair_symm:
-- the two antisymmetries + first Bianchi) + the gi-raised trace. Discharges the hric_symm hypothesis of the capstone.
-- Tier A5: discharge hC.
#print axioms QIQTH.Curvature.christoffel_contDiff
-- expected: standard only — Christoffel C^∞ from metric C^∞ (christoffel = ½∑gi·∂g; contDiff_pd: ∂ of C^∞ is C^∞).
-- Discharges the hC hypothesis of the capstone.

#print axioms QIQTH.FQBound.fq_bound_of_slack
#print axioms QIQTH.FQBound.fq_bound_of_jlms
#print axioms QIQTH.FQBound.fq_bound_area_only
#print axioms QIQTH.FQBound.fq_bound_of_slack_ennreal
-- ★★★ P4 WALL PHASE 6 — THE CONDITIONAL FQ BOUND (algebraic core; GPT-5.5-pro's highest-leverage increment):
-- fq_bound_of_slack — 0≤slack ∧ S+slack≤areaTerm ⟹ S≤areaTerm. fq_bound_of_jlms — JLMS first law S = ⟨A_edge⟩·c +
-- ⟨K_bulk⟩ − D with relative-entropy positivity 0≤D ⟹ S ≤ ⟨A_edge⟩·c + ⟨K_bulk⟩ (P4's BOUND, modulo the Phase-5
-- trace supplying areaExp/bulk/D/first-law). fq_bound_area_only — + bulk≤0 ⟹ S ≤ ⟨A_edge⟩·c (bare area floor).
-- fq_bound_of_slack_ennreal — ℝ≥0∞ form via le_self_add (no subtraction-with-∞). Hypotheses are theorem args, NOT
-- axioms; coefficient c (=1/4ℓ_P²) is the carried UV datum, never assigned; self-adjoint≠positive so area-positivity
-- is explicit where needed. Axiom-free (standard 3). The dual-weight trace (Phase 5) remains the genuine gap.

#print axioms QIQTH.fq_bound_cgp
#print axioms QIQTH.phase5_master_ineq
#print axioms QIQTH.Phase5Master.of_le
-- ★★★ P4 WALL PHASE 6 — THE Phase5Master INTERFACE IS EXACTLY THE JLMS MASTER INEQUALITY (minimality + non-vacuity):
-- Phase5Master.of_le — SvN + cgpEntropy S ξ ≤ areaTerm ⟹ Phase5Master S ξ SvN areaTerm (witness remainder =
-- areaTerm − SvN − cgpEntropy ≥ 0). The converse of phase5_master_ineq, so the certificate carries NEITHER MORE NOR
-- LESS than the single inequality SvN+cgpEntropy≤areaTerm: it is NON-VACUOUS (not instanceable for arbitrary SvN/
-- areaTerm) and MINIMAL (the dual-weight trace's ONLY obligation is that one inequality via the JLMS area first law).
-- Confirms the conditional FQ bound holographic_area_floor assumes exactly the trace's output, nothing more. Axiom-free.
#print axioms QIQTH.fq_bound_of_phase5
#print axioms QIQTH.holographic_area_floor
-- ★★★ P4 WALL — THE HOLOGRAPHIC AREA FLOOR IN MANIFEST FORM: holographic_area_floor [Phase5Master S ξ SvN
-- (edgeArea/(4*ellP^2))] — SvN ≤ edgeArea / (4*ellP^2), i.e. S ≤ A/4ℓ_P² in its physical shape (fq_bound_of_phase5
-- specialized to areaTerm = edgeArea/(4ℓ_P²)). edgeArea (= ⟨A_edge⟩ = A(∂R), the carried UV datum, never assigned)
-- and ellP (Planck length) explicit; the 1/4ℓ_P² coefficient is now manifest. Axiom-free, relative only to the
-- named Phase5Master certificate. The 1/4 ratio is derived (SakharovRatio); free scalar.
-- ★★★ P4 WALL PHASE 6 — THE Phase5Master CERTIFICATE (DonaldSystem-pattern; GPT-5.5-pro round-2 strategy):
-- class Phase5Master (S ξ) (SvN areaTerm : ℝ) bundles the JLMS balance SvN + cgpEntropy S ξ + remainder = areaTerm
-- with remainder_nonneg (the Phase-5 trace's positivity obligation). phase5_master_ineq derives the master
-- inequality SvN + cgpEntropy ≤ areaTerm. fq_bound_of_phase5 — P4's FQ bound SvN ≤ areaTerm UNCONDITIONAL RELATIVE
-- to the certificate (via fq_bound_cgp + cgpEntropy_nonneg). The holographic area floor is now a theorem modulo a
-- named, non-vacuous physics interface (Phase5Master), which the dual-weight trace will instance — NOT an axiom.
-- Axiom-free (standard 3). areaTerm coefficient (1/4ℓ_P²) is the carried UV datum, never assigned.
-- ★★★ P4 WALL PHASE 6 — FQ BOUND GROUNDED IN THE PROVED RELATIVE ENTROPY: fq_bound_cgp — discharges the 0≤slack
-- hypothesis of fq_bound_of_slack with the MACHINE-CHECKED cgpEntropy_nonneg (one-particle CGP modular relative
-- entropy ≥ 0). So the grounded FQ bound S_vN ≤ areaTerm holds whenever the JLMS master inequality
-- S_vN + cgpEntropy S ξ ≤ areaTerm holds (areaTerm = ⟨A_edge⟩/4ℓ_P², the Phase-5 trace's output) — the slack
-- positivity is no longer hypothesized, only the master inequality remains. Axiom-free (standard 3).
#print axioms QIQTH.area_floor_of_microstate
-- ★★★ P4-MICRO (Route 2 — the SHIPPABLE P4 endpoint; P4_MICRO_PLAN.md M-1): area_floor_of_microstate
-- [HolographicCapacityBound R areaTerm] — for any Born record law p on the finite microstate set R,
-- Shannon univ p ≤ areaTerm. P4's holographic area floor as a COROLLARY of the finite-microstate postulate:
-- shannon_le_log_card (axiom-free Jensen/Gibbs: S ≤ log|𝓗_R|) rewritten through the P4-MICRO capacity equation
-- log|𝓗_R| = areaTerm (= A/4ℓ_P²). P4 is no longer an independent postulate but a theorem conditional on the
-- framework's OWN finite-capacity postulate (the "QI" core) — the same finite-Q_max move that removes the collapse
-- postulate now retires the area-law postulate. HolographicCapacityBound is a TYPECLASS HYPOTHESIS, not a Lean axiom
-- (budget stays 0). The area coefficient is the carried UV datum, never assigned; the holographic input log|𝓗_R|∝A
-- stays the labelled frontier (the Type II dual-weight trace that would DERIVE it). Axiom-free (standard 3).
#print axioms QIQTH.holographic_area_floor_micro
-- ★★★ P4-MICRO (Route 2; P4_MICRO_PLAN.md M-2): holographic_area_floor_micro [HolographicCapacityBound R (edgeArea/(4·ellP²))] (edgeArea
-- ellP] — Shannon univ p ≤ edgeArea / (4*ellP^2), i.e. S ≤ A/(4ℓ_P²) in MANIFEST form (the 1/4ℓ_P² coefficient
-- explicit in the statement, not hidden in an abstract areaTerm). area_floor_of_microstate with the capacity
-- equation specialized to edgeArea/(4·ellP²). edgeArea (= ⟨A_edge⟩ = A(∂R), carried UV datum, never assigned)
-- and ellP (Planck length) are free reals; the 1/4 ratio is derived elsewhere (SakharovRatio). Still a typeclass
-- hypothesis, not a Lean axiom. Axiom-free (standard 3).
#print axioms QIQTH.area_floor_saturates
-- ★★★ P4-MICRO (Route 2; P4_MICRO_PLAN.md M-3): area_floor_saturates [HolographicCapacityExact R areaTerm] [Nonempty R]
-- — Shannon univ (fun _ => (card R)⁻¹) = areaTerm. The area floor is an EQUALITY (not just a bound) at the
-- maximally-mixed record p ≡ 1/|𝓗_R| — the equilibrium / horizon local-equilibrium regime — via the Jensen
-- saturation shannon_uniform_eq_log_card rewritten through the P4-MICRO capacity equation. So P4-MICRO delivers
-- both the bound (area_floor_of_microstate) AND its saturation. Area coefficient = carried UV datum, never
-- assigned. Axiom-free (standard 3).
#print axioms QIQTH.vonNeumannEntropy_le_log_card
#print axioms QIQTH.area_floor_vonNeumann
-- ★★★ P4-MICRO (Route 2; P4_MICRO_PLAN.md M-4, the GPT-5.5-pro C1 fix): the HONEST von Neumann form.
-- vonNeumannEntropy_le_log_card [IsDensity ρ] — S_vN(ρ) ≤ Real.log (Fintype.card n): the genuine max-entropy bound
-- S_vN = ∑ negMulLog(eigenvalues) (Shannon of the SPECTRUM — eigenvalues are a prob vector) fed into the axiom-free
-- shannon_le_log_card. NOT the record-law Shannon entropy of area_floor_of_microstate (dephasing only raises
-- entropy: S_vN ≤ H(record) one-way; a pure superposition has H=log d but S_vN=0). area_floor_vonNeumann
-- [HolographicCapacityBound n areaTerm] — S_vN(ρ) ≤ areaTerm: P4 for the genuine regional von Neumann entropy, via the
-- capacity equation. The correct object for P4. Area coefficient = carried UV datum; typeclass hypothesis, not a
-- Lean axiom. Axiom-free (standard 3).
#print axioms QIQTH.instCapacityBoundOfExact
-- ★★★ P4-MICRO (Route 2; P4_MICRO_PLAN.md M-5, the GPT-5.5-pro C2 split): the postulate is split into
-- HolographicCapacityBound (log|𝓗_R| ≤ areaTerm — all the FLOOR needs) and HolographicCapacityExact
-- (= areaTerm — only for saturation). instCapacityBoundOfExact : [HolographicCapacityExact] → HolographicCapacityBound
-- (= implies ≤), so every floor theorem fires from an exact postulate too. The floor theorems
-- (area_floor_of_microstate, holographic_area_floor_micro, area_floor_vonNeumann) now take the weaker Bound;
-- area_floor_saturates keeps Exact. Formerly the single =-form MicrostatePostulate. Axiom-free (standard 3).
#print axioms QIQTH.finCapacityExact
-- ★★★ P4-MICRO (Route 2; P4_MICRO_PLAN.md M-7, non-vacuity witness): finCapacityExact n : HolographicCapacityExact
-- (Fin n) (Real.log n) — a CONCRETE capacity postulate (card (Fin n) = n), proving the interface is INHABITED and
-- the floor non-vacuous (mirrors Phase5Master.of_le). A @[reducible] def, NOT a global instance — a deliberately
-- asserted physics witness, never auto-applied by typeclass resolution. The two `example`s in FQBoundMicro.lean fire
-- area_floor_of_microstate (bound form) and area_floor_saturates (exact form) on it. Axiom-free (standard 3).
#print axioms QIQTH.holographic_area_floor_micro_vonNeumann
-- ★★★ P4-MICRO (Route 2; P4_MICRO_PLAN.md M-8, the Route-1/Route-2 bridge): holographic_area_floor_micro_vonNeumann
-- [HolographicCapacityBound n (edgeArea/(4·ellP²))] — S_vN(ρ) ≤ edgeArea/(4·ellP²). The capacity-conditional
-- analogue of Route 1's FQBoundCGP.holographic_area_floor (= same conclusion ≤ edgeArea/(4·ellP²), but conditional
-- on HolographicCapacityBound = finite capacity, NOT on Phase5Master = the dual-weight trace). Route 2 (kinematic:
-- capacity⇒bound) vs Route 1 (dynamical: the modular trace that would DERIVE the capacity). Complementary, not
-- competing; both carry a named hypothesis (neither is "axiom-free area law"). Same carried UV datum. Axiom-free
-- (standard 3).
#print axioms QIQTH.GRFromMicro.hbound_hsat_of_capacity_family
#print axioms QIQTH.GRFromMicro.gr_from_p4micro
-- ★★★ P4-MICRO (Route 2; P4_MICRO_PLAN.md M-10, the GR bridge): gr_from_p4micro wires P4-MICRO into the
-- machine-checked Jacobson chain QiqtToGR.qiqt_bekenstein_gives_gr. hbound_hsat_of_capacity_family shows the two
-- ENTROPY slots are exactly P4-MICRO's outputs: from a finite-capacity family (a finite microstate type R x v t per
-- horizon patch with record law p, Shannon entropy = S, log-capacity log N = η·A) area_floor_of_microstate gives
-- hbound (S ≤ η·A) and area_floor_saturates gives hsat (S 0 = η·A 0). gr_from_p4micro plugs these in, leaving as the
-- HONEST residual: hDnn/hD0 (entanglement first law / Klein), hFlux (Bisognano–Wichmann / Unruh — the irreducibly
-- MODULAR thermal input a count cannot supply; GR-T1; derived for the free field via Fock.OneParticleBW, not by
-- P4-MICRO), hFocus (Raychaudhuri), hreg, conserv, + structural metric inputs. So "P4-MICRO fills the entropy slots;
-- the thermal slot is Route-1/BW" is now a CHECKABLE Lean dependency. NOT "P4-MICRO ⟹ GR" (false alone). The
-- capacity-tracks-area family (log N=η·A) + record-entropy = horizon-dS are the Gap-2 localization, carried as
-- explicit hypotheses; η (= 1/4ℓ_P²) is a free real (1/4 ratio derived via Sakharov, value of G never assigned);
-- the capacity is a typeclass hypothesis, not a Lean axiom. Axiom-free (standard 3).
#print axioms QIQTH.oneDensity_isDensity
-- ★★★ ELECTRON_FIELD_PLAN E3 (the free Dirac electron — first "matter beyond scalars"):
-- fermionicGaussianEntropy_le_log_dim — the CAR capacity bound. The von Neumann entropy of a quasi-free
-- (Gaussian) fermionic state, S = −Tr[C log C + (1−C)log(1−C)] = Σ binaryEntropy(eigenvalue), is bounded by
-- log(2^n) = log dim(⋀ h_R): each fermionic mode is a qubit (binaryEntropy_le_log_two, via concavity of negMulLog,
-- maximized log 2 at occupation 1/2). This is the fermionic mirror of shannon_le_log_card — the finite-capacity
-- bound S_vN ≤ log N_R survives the bosons → fermions transition. HONEST (ELECTRON_FIELD_PLAN §0): the crux for the
-- electron is the Z₂-graded CAR net + twisted modular duality (NOT a boost sign); WHICH regional algebra the
-- capacity attaches to (even / U(1)-invariant observables) is the E7 question; this E3 bound is the per-spectrum
-- kernel E7 consumes. Free Dirac only; QED/edge-modes/DHR deferred (cited). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermionicGaussianEntropy_le_log_dim
#print axioms QIQTH.Fock.Dirac.binaryEntropy_le_log_two
-- ★★★ ELECTRON_FIELD_PLAN E3 (CAR / Araki relative entropy positivity — fermionic Klein): the relative entropy of
-- two quasi-free fermionic states (mode spectra c,d∈(0,1)) is Σ over modes of the binary relative entropy / KL
-- divergence D(c‖d) = c·log(c/d) + (1−c)·log((1−c)/(1−d)). fermionicBinaryRelEntropy_nonneg: 0 ≤ D(c‖d) (Gibbs,
-- log x ≤ x−1 per term) — the fermionic mirror of Klein's inequality (QuantumRelativeEntropy.relEntropy_nonneg);
-- fermionicGaussianRelEntropy_nonneg: S(ρ_C‖ρ_D) ≥ 0, the CAR/Araki relative entropy positivity. Relative entropy
-- (not bare vN entropy) controls the modular / entanglement-first-law side of the area law. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermionicBinaryRelEntropy_nonneg
#print axioms QIQTH.Fock.Dirac.fermionicGaussianRelEntropy_nonneg
-- ELECTRON_FIELD E3/E9 (CAR relative-entropy FAITHFULNESS): fermionicBinaryRelEntropy_self D(c‖c)=0 and
-- fermionicGaussianRelEntropy_self S(ρ‖ρ)=0. With the positivity (≥0), this is the second defining property of the
-- CAR/Araki relative entropy; it is exactly what makes the first law δS=δ⟨K⟩ the statement that D(n‖n_KMS) is
-- minimized (=0) at the KMS occupation. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermionicBinaryRelEntropy_self
-- ★★★ ELECTRON_FIELD_PLAN E2 (antisymmetric/CAR Fock space): the fermionic (electron) Fock space is the
-- exterior algebra ⋀ M (CAR counterpart of the bosonic symmetric Fock space). finrank_CARFock: dim(⋀ M)=2^n for
-- an n-mode region — each fermionic mode is a qubit (Mathlib Module.Basis.ExteriorAlgebra indexed by Finset I,
-- card = 2^card I). fermionicGaussianEntropy_le_log_carFockDim combines this with E3 so the capacity bound reads
-- S_vN ≤ log N_R with N_R = dim(CARFock 𝕜 h_R) the LITERAL antisymmetric Fock dimension — the fermionic
-- S_vN ≤ log N_R. HONEST: this is the Fock DIMENSION; the full CAR a/a† anticommutator algebra + parity Γ=(−1)^F
-- grading + the Klein-twist/twisted-duality crux (E4) are the next sub-items. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.finrank_CARFock
#print axioms QIQTH.Fock.Dirac.fermionicGaussianEntropy_le_log_carFockDim
-- ★★★ ELECTRON_FIELD_PLAN E2/E4-seed (fermion parity Γ=(−1)^F): parity 𝕜 M — the grade involution on the CAR Fock
-- space ⋀ M (algebra automorphism negating each one-particle generator: parity_ι Γ(ι m)=−ι m; parity_one Γ1=1 —
-- vacuum even; parity_involutive Γ∘Γ=id). The exterior-algebra mirror of Mathlib CliffordAlgebra.involute, built via
-- the universal property (lift of −ι). This is the SEED of the E4 crux: the Klein twist Z=(1+iΓ)/(1+i) is built from
-- Γ, and the twisted modular duality 𝓕(W)'=Z𝓕(W')Z* is the AQFT spin–statistics form for the electron; Γ also
-- singles out the EVEN/observable subalgebra to which records/capacity attach (ELECTRON_FIELD_PLAN §0). Axiom-free
-- (standard 3).
#print axioms QIQTH.Fock.Dirac.parity_ι
#print axioms QIQTH.Fock.Dirac.parity_involutive
-- ★★★ ELECTRON_FIELD_PLAN E4 (THE CRUX — Z₂-graded twisted modular duality): kleinTwist γ = (1+iγ)/(1+i) for an
-- involution γ in a ℂ-algebra. kleinTwist_sq: Z² = γ — the DEFINING identity the twisted duality 𝓕(W)'=Z𝓕(W')Z*
-- rests on (applying the duality twice = parity Γ-conjugation); kleinTwist_sq_sq: Z⁴ = 1 (order-4, fourth root of
-- the parity involution). For γ = Γ=(−1)^F (Parity.lean) this is the Klein twist whose twisted duality is the AQFT
-- form of spin–statistics for the electron — the conceptual crux that the modular flow stays the geometric boost
-- (NOT a sign) while the COMMUTANT/J carries the fermionic twist. CHECKPOINTED (next increments, not blocked): Z
-- unitary Z*Z=1 (needs StarRing, γ self-adjoint); the operator-algebra twisted-duality theorem + instantiation of γ
-- as the second-quantized parity unitary (E5). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.kleinTwist_sq
#print axioms QIQTH.Fock.Dirac.kleinTwist_sq_sq
-- ★★★ ELECTRON_FIELD_PLAN E4 (crux completion — Z is UNITARY): kleinTwist_star_mul_self — for a self-adjoint
-- involution γ (star γ = γ, γ·γ = 1) in a ℂ-*-algebra, Z*Z = 1. With kleinTwist_sq (Z²=γ) this makes the Klein
-- twist a unitary of order 4 (a unitary fourth root of the parity Γ) — the genuine intertwiner the twisted modular
-- duality 𝓕(W)'=Z𝓕(W')Z* requires. Same expansion as kleinTwist_sq with conjugate scalars ᾱ,β̄ and the identities
-- ᾱα+β̄β=1, ᾱβ+β̄α=0. The Klein-twist ALGEBRA is now complete (Z²=Γ, Z⁴=1, Z*Z=1); the operator-algebra
-- twisted-duality theorem + γ = second-quantized parity unitary remain E5 (GNS frontier). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.kleinTwist_star_mul_self
-- ★★★ ELECTRON_FIELD_PLAN E4 (Z is a TWO-SIDED unitary): kleinTwist_mul_star_self — ZZ*=1, the complement of Z*Z=1.
-- Proved elegantly via the order-4 relation: Z⁴=1 (kleinTwist_sq_sq) makes Z³ a two-sided inverse, which with Z*Z=1
-- forces Z*=Z³, hence ZZ*=Z⁴=1. So Z is a genuine (two-sided) unitary — the full intertwiner the twisted duality
-- 𝓕(W)'=Z𝓕(W')Z* requires. The Klein-twist algebra is now complete: Z²=Γ, Z⁴=1, Z*Z=ZZ*=1. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.kleinTwist_mul_star_self
-- ELECTRON_FIELD E4/E5 (the Klein twist preserves the parity grading): kleinTwist_comm_gamma — Z·γ = γ·Z (Z commutes
-- with the involution γ it is built from, since Z=α·1+β·γ has central scalars). For γ=Γ=(−1)^F this is [Z,Γ]=0: the
-- twisted duality 𝓕(W)'=Z𝓕(W')Z* does not mix even/odd sectors, so the electron's even records stay even under the
-- twist (consistent with §0 "records attach to the even algebra"). Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.kleinTwist_comm_gamma
-- ELECTRON_FIELD E4 (witness — the Klein twist on the ACTUAL fermion parity): fermionParity = (−1)^N = diag(1,−1), a
-- concrete 2×2 self-adjoint unitary involution on the single-fermion Fock space ℂ² (fermionParity_involutive Γ²=1,
-- fermionParity_selfAdjoint Γ*=Γ). The four abstract Klein-twist relations are WITNESSED non-vacuously on it:
-- electron_kleinTwist_sq (Z²=Γ), electron_kleinTwist_star_unitary (Z*Z=1), electron_kleinTwist_unitary (ZZ*=1),
-- electron_kleinTwist_comm ([Z,Γ]=0) — the twisted-duality intertwiner realized on the real electron parity, not just
-- postulated. Axiom-free (standard 3); free Dirac. (Field-level (−1)^F + the operator duality theorem = E5 GNS frontier.)
#print axioms QIQTH.Fock.Dirac.fermionParity_involutive
#print axioms QIQTH.Fock.Dirac.fermionParity_selfAdjoint
#print axioms QIQTH.Fock.Dirac.electron_kleinTwist_sq
#print axioms QIQTH.Fock.Dirac.electron_kleinTwist_star_unitary
#print axioms QIQTH.Fock.Dirac.electron_kleinTwist_unitary
#print axioms QIQTH.Fock.Dirac.electron_kleinTwist_comm
-- ELECTRON_FIELD E4/E5 (parity = (−1)^N, tying the Klein-twist grading to the modular Hamiltonian): fermionParity_eq_
-- one_sub_two_numberOp — Γ = 1 − 2N (diag(1,−1) = 1 − 2·diag(0,1)): the parity operator (Klein-twist input) is exactly
-- (−1)^N of the number operator (modular-Hamiltonian input K=βω·N), so Γ and K are both functions of N, simultaneously
-- diagonal. electron_sigmaDiag_fixes_parity — σ_t(Γ)=Γ: the modular flow preserves the parity grading (Γ is diagonal),
-- so a record of definite parity stays that parity under the modular dynamics (records conserved, concrete level).
-- Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.fermionParity_eq_one_sub_two_numberOp
#print axioms QIQTH.Fock.Dirac.electron_sigmaDiag_fixes_parity
-- ELECTRON_FIELD E4/E6 (the twisted-duality intertwiner Z commutes with the modular Hamiltonian): since Z commutes with
-- Γ=1−2N (kleinTwist_comm_gamma) and N=(1−Γ)/2, electron_kleinTwist_comm_numberOp gives Z·N=N·Z; scaling by βω,
-- electron_kleinTwist_comm_modHamiltonian gives Z·K=K·Z (K=βω·N). So the Klein twist is a MODULAR INVARIANT — it
-- commutes with the modular Hamiltonian/flow, so the twisted duality 𝓕(W)'=Z𝓕(W')Z* is compatible with the modular
-- dynamics (the E4 twist consistent with the E6/E9 modular tier). Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.electron_kleinTwist_comm_numberOp
#print axioms QIQTH.Fock.Dirac.electron_kleinTwist_comm_modHamiltonian
-- ★★★ ELECTRON_FIELD_PLAN E6 (Fermi–Dirac Unruh occupation — the CAR +1 vs Bose −1 signature): for a Rindler mode
-- of the free Dirac field the vacuum is boost-KMS at β=2π (Unruh temperature, SAME as the scalar); the fermionic
-- difference is the occupation. fermiDirac β ω = 1/(e^{βω}+1); fermiDirac_kms_balance: n = e^{−βω}(1−n) (KMS thermal
-- condition + CAR anticommutator bb†=1−b†b); fermiDirac_unique: that balance has the Fermi–Dirac occupation as its
-- UNIQUE solution; fermiDirac_mem_Ioo: 0<n<1 (Pauli — at most singly occupied). boseEinstein_kms_balance shows the
-- CCR sign (aa†=1+a†a) gives n=e^{−βω}(1+n) → 1/(e^{βω}−1): same Unruh temperature, denominator sign −1 vs the CAR
-- +1 — the spin–statistics signature at the thermal occupation. rindlerOccupationFermi ω = fermiDirac (2π) ω.
-- HONEST (§0): the balance relation is the KMS+CAR input (presupposes the modular/KMS state, cited E5 machinery);
-- what is derived is the occupation FROM the balance (uniqueness, validity, Bose contrast). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermiDirac_kms_balance
#print axioms QIQTH.Fock.Dirac.fermiDirac_unique
#print axioms QIQTH.Fock.Dirac.boseEinstein_kms_balance
-- ELECTRON_FIELD/PHOTON_FIELD (the spin-statistics enhancement factors, symmetric pair): fermiDirac_one_sub —
-- 1−n = e^{βω}·n (the fermionic Pauli-blocking depletion factor); boseEinstein_one_add — 1+n = e^{βω}·n (the bosonic
-- spontaneous+stimulated enhancement). The −n (Pauli) vs +n (stimulated) is the spin-statistics signature carried to the
-- occupation algebra. Axiom-free (standard 3); free Dirac / free Maxwell.
#print axioms QIQTH.Fock.Dirac.fermiDirac_one_sub
#print axioms QIQTH.Fock.Photon.boseEinstein_one_add
-- PHOTON_FIELD_PLAN P4 (the bosonic Gibbs form): boseEinstein_gibbs_form — n = e^{−βω}/(1−e^{−βω}), the mean of the
-- geometric (Bose) distribution p_k=(1−x)x^k over number states k=0,1,2,…, Boltzmann factor x=e^{−βω}, single-mode
-- partition function Z=1/(1−x), n=x·Z. The bosonic 1−x denominator vs the fermionic 1+x (n=x/(1+x)) is the
-- geometric-vs-two-level spin-statistics signature. Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.boseEinstein_gibbs_form
-- PHOTON_FIELD_PLAN P4 (the Unruh photon occupation in Gibbs form): rindlerOccupationBose_gibbs_form — at β=2π,
-- n_ω = e^{−2πω}/(1−e^{−2πω}): the Rindler/Unruh photon occupation at the Bisognano–Wichmann temperature is the mean of
-- the geometric (Bose) distribution with Boltzmann factor e^{−2πω} (the β=2π specialization of boseEinstein_gibbs_form).
-- Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.rindlerOccupationBose_gibbs_form
-- PHOTON_FIELD_PLAN P4 (the bosonic partition function is n+1): boseEinstein_add_one_mul — (n+1)(1−e^{−βω})=1, i.e.
-- n+1 = 1/(1−e^{−βω}) = Z_bose = ∑_k e^{−βωk} (the geometric-series sum over number states). The (n+1) enhancement
-- factor IS the single-mode bosonic partition function. Contrast Z_fermi=1+e^{−βω} (two-level): geometric vs two-level
-- partition function is the spin-statistics signature at the partition level. Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.boseEinstein_add_one_mul
-- PHOTON_FIELD_PLAN P4 (the bosonic thermal entropy is non-negative): boseEntropy_nonneg — S_BE(n)=(1+n)log(1+n)−n log n
-- = log(1+n) + n·log((1+n)/n) ≥ 0 for n>0 (a sum of two nonneg terms: log(1+n)≥0 since 1+n≥1; n·log((1+n)/n)≥0 since
-- (1+n)/n≥1). The thermal/Unruh photon entropy is a genuine (nonneg) entropy. Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.boseEntropy_nonneg
-- PHOTON_FIELD_PLAN P1 (the photon helicity operator — spin-1, helicity ±1): helicityOp = (+1 on h_{+1}, −1 on h_{−1}),
-- the spin projection along the momentum. helicityOp_sq: Λ²=1 (eigenvalues ±1) — the photon is massless spin-1 with
-- exactly two helicities ±1 (never the longitudinal 0 of a massive vector). Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.helicityOp_sq
-- ★★★ ELECTRON_FIELD_PLAN E6→E5 bridge (per-mode modular Hamiltonian): fermiDirac_logit — for a fermionic mode with
-- occupation n = fermiDirac β ω, the modular energy is the logit log((1−n)/n) = βω. This is the single-mode form of
-- the fermionic modular Hamiltonian K = log((1−C)/C) (QuasiFreeEntropy / quasi-free modular generator): the logit of
-- the occupation IS the inverse-temperature-scaled mode energy, linking the E6 occupation to the modular generator
-- Δ^{it}=e^{−itK} (the E5 target). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermiDirac_logit
-- ★★★ ELECTRON_FIELD_PLAN E6 (particle–hole symmetry): fermiDirac_particle_hole — n(βω) + n(−βω) = 1. Flipping the
-- sign of the mode energy (particle ↔ hole / charge conjugation) sends n ↦ 1−n: the distribution-level shadow of
-- the electron's particle/antiparticle (Dirac-sea) structure — a hole at +ω is a particle at −ω. Axiom-free (std 3).
#print axioms QIQTH.Fock.Dirac.fermiDirac_particle_hole
-- ★★★ ELECTRON_FIELD_PLAN E7/E8-seed (the even/observable algebra — the §0 "which algebra" decision): for the
-- electron, records/capacity attach to the EVEN (parity-fixed) subalgebra, NOT the full graded field algebra.
-- IsEven a := parity a = a (Γ-eigenvalue +1); evenSubalgebra = the Γ-fixed Subalgebra (closed under +,*, contains
-- scalars). isEven_ι_mul_ι: a product of two one-particle (odd) generators is EVEN — so fermion bilinears (ψ̄ψ,
-- j^μ=ψ̄γ^μψ, T_μν) are Γ-fixed even observables (the physical records), while one-particle states are odd
-- (parity_one_particle Γ(ι m)=−ι m). This is why records = even bilinears and the χ_R coherent-sector c-number
-- calculus does NOT transfer (§0). Next E7/E8: graded regional capacity block decomposition + even-observable
-- no-signaling. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.isEven_ι_mul_ι
#print axioms QIQTH.Fock.Dirac.evenSubalgebra
-- ★★★ ELECTRON_FIELD_PLAN E8-seed (even records commute with field operators — the no-signaling kernel):
-- ι_mul_ι_swap — one-particle (odd) generators anticommute ι a·ι b = −ι b·ι a (from ι v·ι v = 0 on a+b);
-- ι_mul_ι_comm_ι — hence a fermion bilinear ι a·ι b (an even observable/record, isEven_ι_mul_ι) COMMUTES with a
-- field operator ι c: (ι a·ι b)·ι c = ι c·(ι a·ι b). This is the algebraic kernel of even-observable no-signaling:
-- the electron's records (even bilinears j^μ, T_μν) commute with the odd field operators, so a record measurement
-- cannot signal through the field algebra. The full bipartite statement (graded tensor product across spacelike
-- regions) is the next E8 sub-item. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.ι_mul_ι_swap
#print axioms QIQTH.Fock.Dirac.ι_mul_ι_comm_ι
-- ★★★ ELECTRON_FIELD_PLAN E8 (even records pairwise commute): evenBilinear_comm — two fermion bilinears
-- (ι a·ι b)·(ι c·ι d) = (ι c·ι d)·(ι a·ι b) commute. Commuting observables are jointly measurable and cannot
-- signal between one another, so this is the no-signaling statement for the electron's even records (j^μ, T_μν)
-- themselves — a step beyond ι_mul_ι_comm_ι. Axiom-free (standard 3 / fewer).
#print axioms QIQTH.Fock.Dirac.evenBilinear_comm
-- ★★★ ELECTRON_FIELD_PLAN E1 (spinor core — the Dirac gamma / Clifford algebra): the electron is a Dirac spinor;
-- its spin/Lorentz structure is the Clifford algebra of the metric. diracGamma Q v = the gamma operator in direction
-- v (Clifford generator ι Q v); for an orthonormal Minkowski basis γ_μ = diracGamma Q e_μ. diracGamma_sq: γ(v)²=Q v
-- (γ_μ²=η_μμ); diracGamma_anticomm: {γ_a,γ_b} = 2η(a,b) = polar Q a b (THE defining Dirac/Clifford relation
-- {γ^μ,γ^ν}=2η^{μν}); diracGamma_anticomm_ortho / diracGamma_swap_ortho: {γ_μ,γ_ν}=0, γ_μγ_ν=−γ_νγ_μ for μ≠ν. The
-- spinor-representation core of E1. HONEST: the full Dirac one-particle Hilbert space (±energy splitting, Dirac
-- inner product, Wigner Poincaré rep) + the S_D=(iγ·∂+m)Δ_m causal kernel remain the E1 frontier. Axiom-free.
#print axioms QIQTH.Fock.Dirac.diracGamma_anticomm
#print axioms QIQTH.Fock.Dirac.diracGamma_sq
-- ★★★ ELECTRON_FIELD_PLAN E1 (Clifford ℤ₂-grading — Lorentz generators are even): the Clifford algebra carries a
-- ℤ₂-grading evenOdd Q i parallel to the CAR parity Γ=(−1)^F. diracGamma_mem_odd: a single gamma γ_μ is ODD (grade
-- 1); diracGamma_mul_mem_even: a product of two gammas is EVEN (grade 0); diracSigma a b = γ_aγ_b−γ_bγ_a (the
-- Lorentz generator σ_μν=(i/4)[γ_μ,γ_ν]); diracSigma_mem_even: σ_ab ∈ evenOdd Q 0 — the spinor representation of the
-- Lorentz group sits in the EVEN Clifford subalgebra (the gamma-side parallel of the CAR parity grading). Axiom-free
-- (standard 3).
#print axioms QIQTH.Fock.Dirac.diracSigma_mem_even
#print axioms QIQTH.Fock.Dirac.diracGamma_mem_odd
-- ELECTRON_FIELD E1 (the Dirac Lorentz/spin generator structure): diracSigma_antisymm — σ_ab=−σ_ba, the defining
-- antisymmetry of the spin generators σ_μν (6 independent = 3 rotations + 3 boosts). diracSigma_ortho — for orthogonal
-- directions σ_ab=2γ_aγ_b; in particular the boost generator σ_{0i}=2γ_0γ_i (time⟂space), the spinor representation of
-- the Rindler boost whose flow is the electron's modular Δ^it (E1/E9). Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.diracSigma_antisymm
#print axioms QIQTH.Fock.Dirac.diracSigma_ortho
-- ELECTRON_FIELD E1 (the spin generator squares to a scalar — boost vs rotation): diracSigma_sq_ortho — for orthogonal
-- a⟂b, σ_ab² = −4·Q(a)·Q(b) (a SCALAR, since σ_ab=2γ_aγ_b and (γ_aγ_b)²=−γ_a²γ_b²=−Q(a)Q(b)). This distinguishes
-- BOOSTS from ROTATIONS: with η=(+,−,−,−), the boost σ_{0i} has Q(e₀)Q(eᵢ)=(+1)(−1)=−1 ⟹ σ²=+4>0 (non-compact,
-- hyperbolic — the Rindler boost generator whose Δ^it is the modular flow); a rotation σ_{ij} has (−1)(−1)=+1 ⟹ σ²=−4<0
-- (compact, elliptic). The sign of σ² is the boost-vs-rotation (non-compact-vs-compact) dichotomy. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.diracSigma_sq_ortho
-- ELECTRON_FIELD E1 (the fundamental orthogonal-gamma square): diracGamma_mul_sq_ortho — (γ_aγ_b)² = −Q(a)·Q(b) (a⟂b),
-- the building block of σ²=4× this. So γ_aγ_b is a square root of −Q(a)Q(b): for a rotation plane (Q(a)Q(b)>0) it is a
-- COMPLEX STRUCTURE ((γ_aγ_b)²<0, the i generating U(1)); for a boost plane (Q(a)Q(b)<0) it squares to a positive scalar
-- (hyperbolic). Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.diracGamma_mul_sq_ortho
-- ★★★ ELECTRON_FIELD_PLAN — PhysLean bridge (the CAR operator-layer dependency): QIQT-H now depends on PhysLean
-- (HEPLean, pinned to d0ee4af whose Mathlib pin c5ea00351c28 @ v4.30.0 matches QIQT-H's — no Mathlib bump), which
-- provides the fermionic CAR field-operator algebra (FieldStatistic, CreateAnnihilate, CrAnFieldOp, WickAlgebra,
-- SuperCommute) for E2-full/E5. electron_pair_bosonic: fermionic·fermionic = bosonic (PhysLean) ↔ isEven_ι_mul_ι
-- (two odd generators → even); statParity_mul: statParity : FieldStatistic →+ ℤ₂ is the grading hom shared by
-- PhysLean's FieldStatistic and the QIQT-H parity / Clifford evenOdd gradings; electron_statParity: the electron is
-- odd (grade 1). The dependency is live and the statistics align; building the CAR a/a† operators on PhysLean's
-- WickAlgebra is the follow-on E2-full/E5 work. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_pair_bosonic
#print axioms QIQTH.Fock.Dirac.statParity_mul
-- electron_exchangeSign: 𝓢(fermionic,fermionic) = −1 (PhysLean exchangeSign) — exactly the graded-commutation sign
-- (−1)^{|F₁||F₂|} of the crux F₁F₂=(−1)^{|F₁||F₂|}F₂F₁ for two fermions, the same −1 as the substrate's
-- ι_mul_ι_swap (ι a·ι b = −ι b·ι a). PhysLean's exchange sign and the QIQT-H CAR anticommutation carry the
-- identical Pauli sign. Axiom-free (standard 3 / fewer).
#print axioms QIQTH.Fock.Dirac.electron_exchangeSign
-- electronFieldSpec: the electron's PhysLean FieldSpecification (single fermionic field, trivial labels) — the
-- field-content structure on which PhysLean's CrAnFieldOp / WickAlgebra / superCommute (the CAR a/a† operator layer)
-- are built. electronFieldSpec_statistic: the electron field is fermionic. The entry point to the E2-full/E5
-- operator tier. Axiom-free (standard 3 / fewer).
#print axioms QIQTH.Fock.Dirac.electronFieldSpec_statistic
-- ★★★ ELECTRON_FIELD E2-full/E5 (CAR relations for the electron via PhysLean superCommute): for the fermionic
-- electron the super-commutator [·,·]ₛ IS the anticommutator (graded commutator with exchange sign −1). The CAR
-- relations: electron_create_create_zero {a†,a†}=0 (PAULI EXCLUSION — two electrons can't be created in one mode);
-- electron_annihilate_annihilate_zero {a,a}=0; electron_superCommute_mem_center — {a,a†} lies in the centre, the
-- defining CAR property that the anticommutator is a c-number (the one-particle inner product), not an operator.
-- The actual E5 operator content, machine-checked on PhysLean's WickAlgebra. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_create_create_zero
#print axioms QIQTH.Fock.Dirac.electron_superCommute_mem_center
-- ★★★ ELECTRON_FIELD E5 (the nonzero CAR anticommutator {a,a†}): electron_anPart_crPart_anticomm — because the
-- electron is fermionic (exchange sign −1), PhysLean's super-commutator of the annihilation part anPart φ (a) and
-- creation part crPart φ' (a†) of two field operators is literally the ANTICOMMUTATOR (+ sign):
-- [anPart φ, crPart φ']ₛ = anPart φ · crPart φ' + crPart φ' · anPart φ = {a(φ), a†(φ')}. The defining nonzero CAR
-- relation, the kinematic heart of the electron's second quantization. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_anPart_crPart_anticomm
-- ★★★ ELECTRON_FIELD E8/§0 at the operator level (records = even bilinears): electron_bilinear_bosonic — a product
-- of two electron creation/annihilation operators ofCrAnList [φ,φ'] lies in the BOSONIC (even) graded submodule of
-- PhysLean's Wick algebra (fermionic·fermionic = bosonic). The operator-algebra counterpart of isEven_ι_mul_ι and
-- electron_pair_bosonic: the electron's records (number/current/T_μν, even bilinears) live in the even sector of
-- the second-quantized algebra — the §0 "records attach to the even/observable algebra" decision, now on PhysLean.
-- Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_bilinear_bosonic
-- ELECTRON_FIELD §0 at the operator level (one-particle = odd, completing the even/odd grading): electron_single_fermionic
-- — a single field operator ofCrAnList [φ] is in the FERMIONIC (odd) submodule, so a single fermion is NOT a record;
-- with electron_bilinear_bosonic (bilinears even) this is the operator-level even/odd grading, identical to the Clifford
-- diracGamma_mem_odd and the exterior parity_one_particle across all three layers. Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.electron_single_fermionic
-- ★★★ ELECTRON_FIELD E5/E6 (electron mode wired into the EXISTING Tomita–Takesaki machinery): QIQT-H already has
-- the finite modular flow (FiniteModularTheory: modAut ρ x = ρ x ⅟ρ, stateOf, the proved kms_condition) and the
-- continuum Δ^it = modFlow (Spectral/SpectralTheorem). electron_occupation_eq_fermiDirac: for a single fermionic
-- mode (qubit) with thermal density matrix ρ = diag(1−n, n), n = fermiDirac β ω, and number op N = diag(0,1), the
-- KMS-state expectation stateOf ρ N = tr(ρN) = fermiDirac β ω — the FD occupation (E6) IS the expectation of N in
-- the project's finite Tomita–Takesaki KMS state; ρ is a faithful state (trace 1, invertible 0<n<1) so kms_condition
-- applies. The E6 boost-KMS content realized inside the existing modular flow, not a separate axiom. Axiom-free.
#print axioms QIQTH.Fock.Dirac.electron_occupation_eq_fermiDirac
-- ELECTRON_FIELD E5/E6 (electron mode IS a faithful KMS state of QIQT-H's finite Tomita–Takesaki): the electron
-- thermal state ρ = diag(1−n,n), n=fermiDirac β ω, is invertible (faithful, 0<n<1) so the PROVED
-- FiniteModularTheory.kms_condition and modAut_stateOf_invariant apply. electron_kms_condition: ω(x·y)=ω(y·σ(x)) for
-- the electron (the defining KMS relation); electron_modAut_invariant: ω(σ(x))=ω(x) (the electron's modular flow
-- conserves its Born/Gibbs expectations); electron_gibbs_ratio: n/(1−n)=e^{−βω} (the Gibbs–Boltzmann detailed-balance
-- factor, the multiplicative KMS content). The electron realizes the finite TT KMS structure. Axiom-free (std 3).
#print axioms QIQTH.Fock.Dirac.electron_kms_condition
#print axioms QIQTH.Fock.Dirac.electron_gibbs_ratio
-- ELECTRON_FIELD E5/E6 (the modular flow conserves the records): electron_modAut_self (σ(ρ)=ρ, the KMS state is a
-- fixed point of its modular automorphism); electron_modAut_numberOp (σ(N)=N — the number operator / record / charge
-- is a modular invariant, since N and ρ are both diagonal hence commute). The QIQT-H statement that the modular
-- (KMS) dynamics conserves the record/charge, for the electron. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_modAut_numberOp
-- ELECTRON_FIELD E5 (the electron's genuine real-time modular flow Δ^it·Δ^-it): electron_sigmaDiag_comp — the
-- electron mode's real one-parameter modular flow σ_t = sigmaDiag(electronModeOcc) (FiniteModularTheory's genuine
-- Δ^it conjugation at the FD occupations) is an ℝ-action, σ_s(σ_t x)=σ_{s+t}x — the one-parameter-group Tomita–
-- Takesaki property a single imaginary-time conjugation cannot state. electron_sigmaDiag_fixes_numberOp: σ_t(N)=N,
-- the record/charge is conserved under the real-time modular FLOW. The genuine continuum-style Δ^it for the electron
-- at the finite level. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_sigmaDiag_comp
#print axioms QIQTH.Fock.Dirac.electron_sigmaDiag_fixes_numberOp
-- ELECTRON_FIELD E5/E9 (modular phase = modular Hamiltonian eigenvalue = mode energy βω): electron_modular_phase —
-- the ratio of Δ^it's occupied/empty eigenvalues is the Gibbs factor^it, (n/(1−n))^{it} = e^{−it·βω}. So the modular
-- flow rotates the off-diagonal raising/lowering operators by the modular frequency βω; the generator of σ_t (the
-- modular Hamiltonian K) has eigenvalue gap βω, and at the Unruh value β=2π this is 2π·ω = 2π × (boost generator
-- eigenvalue) — the Δ^it = U(boost) content at the single-mode level (toward E9's 2π K_boost). Axiom-free (std 3).
#print axioms QIQTH.Fock.Dirac.electron_modular_phase
-- ELECTRON_FIELD E5 (the raising operator is a modular eigenoperator): electron_sigmaDiag_raising —
-- σ_t(a†) = (p₁^{it} p₀^{−it})·a† (raisingOp = the matrix unit E_{1,0}). The real-time modular flow Δ^it rotates a†
-- by the modular phase (n/(1−n))^{it} = e^{−it·βω} (electron_modular_phase); a† is an eigenvector of the modular
-- automorphism with the modular frequency βω (= the boost energy at β=2π). The operator-level Δ^it = U(boost)
-- action on the creation operator. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_sigmaDiag_raising
-- ELECTRON_FIELD E5 (the lowering operator is the dual modular eigenoperator — full spectral decomposition):
-- electron_sigmaDiag_lowering — σ_t(a) = (p₀^{it} p₁^{−it})·a, the modular flow rotates a by the INVERSE modular
-- phase ((1−n)/n)^{it} = e^{+it·βω}. With electron_sigmaDiag_raising (a† rotates by e^{−it·βω}) this is the full
-- modular spectral decomposition: a† raises the modular energy by βω, a lowers it, N=a†a fixed — the single-mode
-- Δ^it = U(boost) Bohr-frequency rotation. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_sigmaDiag_lowering
-- ELECTRON_FIELD E5/E9 (the number operator is the modular generator — canonical ladder commutators):
-- electron_number_raising_comm [N,a†]=a† and electron_number_lowering_comm [N,a]=−a. The number operator raises/
-- lowers a†/a by one quantum; since the modular Hamiltonian is affine in N (K = βω·N + c), [K,a†]=βω·a† and
-- [K,a]=−βω·a — the source of the modular phases e^{∓it·βω} (electron_sigmaDiag_raising/_lowering). The modular
-- Hamiltonian ∝ the number operator (the record), with the modular energy βω = 2π × the boost energy at β=2π.
-- Axiom-free (standard 3 / fewer).
#print axioms QIQTH.Fock.Dirac.electron_number_raising_comm
-- ELECTRON_FIELD E6/E9 (single-mode thermal/entanglement entropy S = log Z + β⟨E⟩): electron_mode_entropy —
-- binaryEntropy(n) = log(1+e^{−βω}) + βω·n, n=fermiDirac β ω, Z=1+e^{−βω}, mean energy ⟨E⟩=ω·n (so βω·n=β⟨E⟩=⟨K⟩
-- up to the constant log Z). The bridge S ↔ ⟨K⟩ — the input to the entanglement first law δS=δ⟨K⟩ that drives the
-- area law, for the electron mode. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_mode_entropy
-- ★★★ ELECTRON_FIELD E9 (the entanglement first law δS=δ⟨K⟩ for the electron mode): hasDerivAt_binaryEntropy —
-- d/dn binaryEntropy(n) = log((1−n)/n) (the modular-energy logit). electron_firstLaw: at the KMS/Unruh occupation
-- n=fermiDirac β ω, HasDerivAt binaryEntropy (βω) n — the entropy's derivative wrt occupation IS the modular energy
-- βω. Since ⟨K⟩=βω·n+c, d⟨K⟩/dn=βω=dS/dn: the differential entanglement first law δS=δ⟨K⟩ that drives the area law,
-- realized for the electron mode. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_firstLaw
-- ★★★ ELECTRON_FIELD E6 capstone (the electron Unruh effect at the Bisognano–Wichmann temperature β=2π): at β=2π the
-- finite modular flow σ_t=Δ^it is the geometric Rindler boost (BW), so the electron KMS state is the Rindler/Unruh
-- thermal state. electron_unruh_occupation: ω(N) = rindlerOccupationFermi ω = 1/(e^{2πω}+1) — the FD/Unruh occupation
-- as the modular-state expectation. electron_unruh_occupation_mem_Ioo: the Pauli bound 0<n_ω<1 (≤1 fermion/mode) — the
-- contrast with the photon's UNBOUNDED bosonic Unruh occupation 1/(e^{2πω}−1) (which needs a number cutoff, PHOTON P2/P3),
-- so the electron's per-mode capacity is intrinsically finite (CAR dim ⋀h=2^n, no cutoff). electron_unruh_entropy:
-- S(n_ω)=log(1+e^{−2πω})+2πω·n_ω (the log Z+β⟨E⟩ thermal entropy at the BW temperature). electron_unruh_firstLaw:
-- HasDerivAt binaryEntropy (2πω) n_ω — the first law δS=δ⟨K⟩ at the Unruh temperature, modular energy 2πω (the +2π
-- wiring one-particle BW into the area law). All axiom-free (standard 3); free Dirac; G never assigned.
#print axioms QIQTH.Fock.Dirac.electron_unruh_occupation
#print axioms QIQTH.Fock.Dirac.electron_unruh_occupation_mem_Ioo
#print axioms QIQTH.Fock.Dirac.electron_unruh_entropy
#print axioms QIQTH.Fock.Dirac.electron_unruh_firstLaw
-- ★★★ ELECTRON_FIELD E9 (the modular Hamiltonian K=βω·N and the boost Hamiltonian 2πK_boost): the modular
-- automorphism σ_t=Δ^it=e^{−itK} has K affine in the number operator (BW: the Rindler modular Hamiltonian is 2π× the
-- boost generator); the central constant c·I drops from all commutators. modHamiltonian β ω := (βω)•numberOp.
-- electron_modHamiltonian_raising_comm: [K,a†]=βω·a† (scaling [N,a†]=a† by βω) — a† is a modular eigenoperator with
-- eigenvalue βω, the generator source of σ_t(a†)=e^{−itβω}a†. electron_modHamiltonian_lowering_comm: [K,a]=−βω·a.
-- electron_boost_modHamiltonian_raising_comm: at β=2π, [K_W,a†]=2πω·a† — the boost modular Hamiltonian K_W=2πK_boost
-- whose ⟨K_W⟩ feeds the Clausius/Jacobson area relation δS=δ⟨K_W⟩ (the +2π wiring one-particle BW into the area law).
-- Axiom-free (standard 3); free Dirac; value of G never assigned.
#print axioms QIQTH.Fock.Dirac.electron_modHamiltonian_raising_comm
#print axioms QIQTH.Fock.Dirac.electron_modHamiltonian_lowering_comm
#print axioms QIQTH.Fock.Dirac.electron_boost_modHamiltonian_raising_comm
-- ELECTRON_FIELD E9 (the modular-energy expectation ⟨K⟩=βω·n): electron_modHamiltonian_expectation — the KMS-state
-- expectation of K=βω·N is βω times the FD occupation (stateOf linearity + electron_occupation_eq_fermiDirac); this
-- ⟨K⟩=β⟨E⟩ is the modular-energy term in S=log Z+β⟨E⟩ and the δ⟨K⟩ of the first law δS=δ⟨K⟩.
-- electron_boost_modEnergy: at β=2π, ⟨K_W⟩=2πω·n_ω — the boost-energy expectation feeding the Clausius/Jacobson area
-- relation. Axiom-free (standard 3); free Dirac; value of G never assigned.
#print axioms QIQTH.Fock.Dirac.electron_modHamiltonian_expectation
#print axioms QIQTH.Fock.Dirac.electron_boost_modEnergy
-- ELECTRON_FIELD E9 (the modular Hamiltonian K=βω·N is self-adjoint): electron_modHamiltonian_isHermitian — a real
-- multiple of the real-diagonal number operator is Hermitian, so K is a genuine self-adjoint generator and Δ^it=e^{−itK}
-- is a UNITARY one-parameter group (the Stone/Tomita–Takesaki form). Completes the single-mode E9 generator: K
-- self-adjoint + ladder commutators (modular frequencies ∓βω) + expectation ⟨K⟩=βω·n. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_modHamiltonian_isHermitian
-- ELECTRON_FIELD (the Pauli per-mode capacity ceiling): electron_mode_entropy_le_log2 — the electron mode's thermal
-- entropy ≤ log 2 (a fermionic mode is a qubit, Pauli exclusion: occupied or empty), via Gibbs/Jensen
-- (shannon_le_log_card) on the 2-outcome occupation distribution {n,1−n}. The sharp contrast with the photon: the bosonic
-- mode entropy is UNBOUNDED (no cutoff), whereas the electron's per-mode entropy has the hard ceiling log 2 — the
-- entropy-level shadow of the CAR finite capacity dim ⋀h=2^n. Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.electron_mode_entropy_le_log2
-- ELECTRON_FIELD E9 (the modular-energy spectrum): electron_modHamiltonian_diag — K=βω·N = diag(0, βω): the modular
-- energy levels are exactly {0, βω} (empty mode 0, occupied mode βω = the boost energy quantum, =2πω at the BW
-- temperature β=2π), the gap that drives the modular phase σ_t(a†)=e^{−itβω}a†. electron_modHamiltonian_trace: Tr K = βω
-- (the total/sum of modular energy levels). Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.electron_modHamiltonian_diag
#print axioms QIQTH.Fock.Dirac.electron_modHamiltonian_trace
-- ELECTRON_FIELD E5/§0 (every diagonal record is a modular invariant): electron_sigmaDiag_fixes_diagonal — the real-time
-- modular flow σ_t=Δ^it fixes EVERY diagonal matrix diag(d), generalizing electron_sigmaDiag_fixes_numberOp (the D=N
-- case) to the whole classical/pointer (record) basis. Since Δ^it=diagPow is diagonal and diagonals commute, σ_t(D)=D.
-- So the electron's records (the diagonal/decohered observables — number, occupation, charge) are CONSERVED by the
-- modular dynamics (finite-KMS counterpart of the continuum fermiSecondQuantModFlow_isEven). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.electron_sigmaDiag_fixes_diagonal
-- ELECTRON_FIELD E6 (the modular state as the Gibbs state over the spectrum {0,βω}): electron_gibbs_weight_ground —
-- (1−n)·Z = e^{−E₀} = 1 (E₀=0); electron_gibbs_weight_excited — n·Z = e^{−E₁} = e^{−βω} (E₁=βω), Z=1+e^{−βω}. So the
-- electron's KMS/modular occupations are EXACTLY the Boltzmann weights e^{−Eᵢ}/Z of the modular energy spectrum {0,βω}
-- (electron_modHamiltonian_diag), Z=Σᵢ e^{−Eᵢ} the modular partition function (whose log Z is the S=log Z+β⟨E⟩ of
-- electron_mode_entropy) — the modular state = Gibbs state, at the entry level. Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.electron_gibbs_weight_ground
#print axioms QIQTH.Fock.Dirac.electron_gibbs_weight_excited
-- ★★★ ELECTRON_FIELD E6 (the modular partition OPERATOR, via the matrix exponential): electron_exp_neg_modHamiltonian —
-- e^{−K} = NormedSpace.exp(−K) = diag(1, e^{−βω}), the matrix exp of −K=−βω·N=diag(0,−βω) is the diagonal of Boltzmann
-- factors e^{−Eᵢ} over the modular spectrum {0,βω} (Matrix.exp_diagonal + Complex.exp_eq_exp_ℂ). electron_partition_trace —
-- Z = Tr e^{−K} = 1 + e^{−βω}: the modular partition function as a TRACE (the operator-level realization, whose log Z is
-- the S=log Z+β⟨E⟩ of electron_mode_entropy). With the Gibbs weights this is the full "modular state = Gibbs state e^{−K}/Z"
-- picture at the operator level. Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.electron_exp_neg_modHamiltonian
#print axioms QIQTH.Fock.Dirac.electron_partition_trace
-- ★★★ ELECTRON_FIELD E6 (THE modular state = Gibbs state, full matrix identity): electron_thermalState_gibbs —
-- (1+e^{−βω})·ρ = e^{−K}, i.e. the FD thermal state ρ=diag(1−n,n) IS the normalized Gibbs operator e^{−K}/Z of the
-- modular Hamiltonian K=βω·N (combining electron_exp_neg_modHamiltonian with the Gibbs weights). The defining
-- Tomita–Takesaki property — the modular state is the Gibbs state of K — now a machine-checked matrix identity.
-- Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.electron_thermalState_gibbs
-- ELECTRON_FIELD E6 (the explicit normalized Gibbs state): electron_thermalState_eq_gibbs — ρ = (1/Z)·e^{−K}, the
-- canonical normalized form of the Gibbs identity (the modular state written explicitly as e^{−K}/Z, Z=1+e^{−βω}).
-- Axiom-free (standard 3); free Dirac.
#print axioms QIQTH.Fock.Dirac.electron_thermalState_eq_gibbs
-- ★★★ ELECTRON_FIELD E5 (CONTINUUM CAR-net modular flow Γ₋(Δ^it)): the continuum wedge modular flow for the electron
-- CAR net is the FERMIONIC second quantization of the one-particle continuum Δ^it = modUnitary S t
-- (StandardSubspaceModularFlow, already built). fermiSecondQuantModFlow S t = ExteriorAlgebra.map (modUnitary S t)
-- on the antisymmetric (exterior/CAR) Fock ⋀H — the fermionic analog of the bosonic secondQuantModFlow, reusing the
-- SAME one-particle Δ^it. fermiSecondQuantModFlow_ι: Γ₋(Δ^it)(ι f)=ι(Δ^it f); fermiSecondQuantModFlow_zero: Γ₋(Δ^0)=
-- id; fermiSecondQuantModFlow_add: Γ₋(Δ^is)∘Γ₋(Δ^it)=Γ₋(Δ^{i(s+t)}) (group law from modUnitary_add + ExteriorAlgebra
-- .map functoriality). The continuum field-level Δ_W^it for the electron, on QIQT-H's existing TT machinery.
-- Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermiSecondQuantModFlow_add
#print axioms QIQTH.Fock.Dirac.fermiSecondQuantModFlow_ι
-- ELECTRON_FIELD E5 (the continuum modular flow acts by ALGEBRA AUTOMORPHISMS): fermiSecondQuantModFlow_one
-- (Γ₋(Δ^it) Ω = Ω, vacuum invariance); fermiSecondQuantModFlow_comp_neg (Γ₋(Δ^it)∘Γ₋(Δ^-it)=id, so Δ^-it is the
-- inverse); fermiModFlowEquiv — Γ₋(Δ^it) bundled as an AlgEquiv (algebra ISOMORPHISM of the CAR Fock with inverse
-- Γ₋(Δ^-it)). The defining Tomita–Takesaki property that the modular automorphism group σ_t=Γ₋(Δ^it) lands in Aut(𝓕),
-- for the electron CAR net. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermiSecondQuantModFlow_comp_neg
#print axioms QIQTH.Fock.Dirac.fermiModFlowEquiv
-- ★★★ ELECTRON_FIELD E5/§0 (the continuum modular flow preserves the even/record sector):
-- fermiSecondQuantModFlow_comp_parity — Γ₋(Δ^it)∘Γ = Γ∘Γ₋(Δ^it), the continuum modular flow commutes with the
-- fermion parity Γ=(−1)^F (both graded algebra homs, agreeing on the ι generators). Hence the modular flow PRESERVES
-- the ℤ₂ grading — the even (record/observable) sector is invariant under the modular dynamics: the record/charge is
-- conserved by the field-level modular flow (the §0/E8 records decision, conserved by σ_t at the continuum level).
-- Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermiSecondQuantModFlow_comp_parity
-- ELECTRON_FIELD E5/§0 (the modular flow keeps records as records): fermiSecondQuantModFlow_isEven — IsEven x →
-- IsEven (Γ₋(Δ^it) x). The even (record/observable) sector is mapped into itself by the continuum modular dynamics
-- (a consequence of the parity-commute). The electron's records (even bilinears j^μ, T_μν, number) remain records
-- under the field-level modular flow σ_t — modular dynamics conserves the even/observable algebra at the continuum.
-- Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermiSecondQuantModFlow_isEven
-- ELECTRON_FIELD E5 (a record transforms covariantly under the modular/boost flow):
-- fermiSecondQuantModFlow_ι_mul_ι — Γ₋(Δ^it)(ι f · ι g) = ι(Δ^it f) · ι(Δ^it g). A fermion bilinear (current /
-- T_μν-type record) is carried by the modular flow to the bilinear of the boosted one-particle states — records
-- transform covariantly under σ_t (Δ^it = U(boost)). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.fermiSecondQuantModFlow_ι_mul_ι
-- ★★★ ELECTRON_FIELD_PLAN E7 (graded regional capacity — the charge/parity block decomposition): the electron's
-- even/U(1)-invariant regional algebra is graded 𝒜_R ≃ ⊕_q M_{n_q}. gradedShannon_chain_rule: the record entropy
-- decomposes as S = H(p) + Σ_q p_q S(w_q) (sector mixing entropy + average within-sector entropy), via the entropy
-- chain identity Real.negMulLog_mul. gradedShannon_capacity_le: each block contributes ≤ log n_q (per-sector
-- shannon_le_log_card / the CAR S≤log dim of E3), so S(ρ_R) ≤ H(p) + Σ_q p_q log n_q — the finite-capacity bound
-- passes to the graded regional algebra to which (per §0) records/capacity attach. HONEST: the further collapse to a
-- single log(Σ n_q) needs a Jensen/log-sum step over the sector weights (next E7 sub-item). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.gradedShannon_chain_rule
#print axioms QIQTH.Fock.Dirac.gradedShannon_capacity_le
-- ★★★ ELECTRON_FIELD_PLAN E7 (completion — full graded capacity S ≤ log dim(⊕M_{n_q})): entropy_add_avgLogCard_le
-- is the Gibbs/log-sum collapse H(p) + Σ_q p_q log n_q ≤ log(Σ_q n_q) (via log x ≤ x−1 per sector; equality at the
-- maximally-mixed p_q ∝ n_q). gradedShannon_le_log_total chains chain-rule + per-sector capacity + this collapse to
-- the headline S(ρ_R) ≤ log(Σ_q n_q) = log dim(⊕_q M_{n_q}) — the fermionic S_vN ≤ log N_R on the charge/parity-
-- graded (even/observable) regional algebra to which records attach (§0). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Dirac.entropy_add_avgLogCard_le
#print axioms QIQTH.Fock.Dirac.gradedShannon_le_log_total
-- ★★★ P4-MICRO (Route 2; P4_MICRO_PLAN.md M-11, von Neumann non-vacuity witness): oneDensity_isDensity —
-- IsDensity (1 : Matrix (Fin 1) (Fin 1) ℂ), the one-microstate pure state (1×1 identity), a genuine density
-- (PosSemidef.one + trace_one). Completes the witness story (M-7 only witnessed the record-law/Shannon floor): the
-- example in FQBoundMicro fires area_floor_vonNeumann (the honest M-4 von Neumann P4) on it — S_vN = 0 ≤ log 1 — so
-- the von Neumann floor is non-vacuous on a concrete density matrix. Axiom-free (standard 3).
-- ★★★ PHOTON_FIELD_PLAN P2 (the truncated bosonic Fock dimension — the analytic core of the photon capacity bound):
-- the photon is BOSONIC (symmetric Fock Γ_s), infinite-dim even for finite-dim one-particle h, so its regional
-- capacity is UNBOUNDED without a photon-number cutoff (the structural contrast with the electron's finite CAR
-- dim ⋀h = 2^(dim h)). truncFockDim d N := Σ_{k=0}^N multichoose(d,k) = dim Γ_s^{≤N}(h) for d = dim h. truncFockDim_succ:
-- the cutoff recurrence (+ multichoose(d,N+1) per added photon). truncFockDim_eq_choose: the closed form
-- dim Γ_s^{≤N}(h) = C(d+N, N) (induction + Pascal Nat.choose_succ_succ) — the FINITE dimension that exists only by the
-- number cutoff N; the bosonic mirror of the electron CAR S≤log dim, giving the photon bound S ≤ log C(dim h_γ+N, N) (P3).
-- truncFockDim_mono / truncFockDim_strictMono: dim is (weakly/strictly for d≥1) increasing in N — the finite-N shadow
-- of the photon's unbounded capacity (the "sup S = ∞ without a cutoff" corollary). Axiom-free (standard 3). Free Maxwell.
#print axioms QIQTH.Fock.Photon.truncFockDim_succ
#print axioms QIQTH.Fock.Photon.truncFockDim_eq_choose
#print axioms QIQTH.Fock.Photon.truncFockDim_mono
#print axioms QIQTH.Fock.Photon.truncFockDim_strictMono
-- ★★★ PHOTON_FIELD_PLAN P3 (the photon finite-capacity bound): photon_capacity_bound — for any density ρ on the
-- number-cutoff bosonic Fock Γ_s^{≤N}(h_γ) (dim = truncFockDim d N = C(d+N,N)), S_vN(ρ) ≤ log C(dim h_γ+N, N). The
-- bosonic mirror of the electron CAR S_vN ≤ log dim(⋀h_R) (vonNeumannEntropy_le_log_card on Fin (truncFockDim d N),
-- rewritten through Fintype.card_fin + the P2 closed form) — but FINITE only by the photon-number cutoff N (the
-- bosonic Fock is infinite-dim). photon_capacity_unbounded — for d≥1 the truncated dimension exceeds any B for large
-- N (truncFockDim_strictMono), so log dim → ∞: the photon capacity has no finite ceiling without the cutoff (the
-- "sup S=∞ without a cutoff" contrast with the electron). Axiom-free (standard 3). Free Maxwell; area coeff never set.
#print axioms QIQTH.Fock.Photon.photon_capacity_bound
#print axioms QIQTH.Fock.Photon.photon_capacity_unbounded
-- ★★★ PHOTON_FIELD_PLAN P4 (the Bose–Einstein photon Unruh occupation — the −1/CCR analog of the electron FD cluster):
-- the photon is bosonic so its Rindler/Unruh occupation is n_ω = 1/(e^{βω}−1) (the −1, vs the electron's +1).
-- boseEinstein_pos: 0 < n for βω>0. boseEinstein_unique: any n solving the CCR KMS balance n=e^{−βω}(1+n) equals the
-- Bose–Einstein occupation (the bosonic mirror of fermiDirac_unique). boseEinstein_gt_fermiDirac: n_BE > n_FD (more
-- occupation, and NO Pauli ceiling — the occupation-level reason the photon's regional capacity needs a number cutoff,
-- P2/P3, while the electron's CAR capacity is intrinsically finite). rindlerOccupationBose (=boseEinstein 2π ω) +
-- _balance + _pos: the photon Unruh occupation at the Bisognano–Wichmann temperature β=2π. Requires βω≠0 (the photon
-- zero-mode is the gauge/IR frontier P10). Axiom-free (standard 3). Free Maxwell only.
#print axioms QIQTH.Fock.Photon.boseEinstein_pos
#print axioms QIQTH.Fock.Photon.boseEinstein_unique
#print axioms QIQTH.Fock.Photon.boseEinstein_gt_fermiDirac
#print axioms QIQTH.Fock.Photon.rindlerOccupationBose_balance
#print axioms QIQTH.Fock.Photon.rindlerOccupationBose_pos
-- PHOTON_FIELD_PLAN P4 (the photon Unruh thermal entropy): photon_mode_entropy — for a bosonic photon mode with
-- Bose–Einstein occupation n=1/(e^{βω}−1), the mode entropy boseEntropy(n)=(1+n)log(1+n)−n log n equals the log
-- partition function −log(1−e^{−βω}) + βω·n (the bosonic mirror of electron_mode_entropy S=log Z+β⟨E⟩). UNBOUNDED: as
-- βω→0⁺, n→∞ and S→∞ — the entropy-level reason the photon needs a number cutoff (P2/P3), the sharp contrast with the
-- electron's Pauli ceiling S≤log 2 (electron_mode_entropy_le_log2). Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.photon_mode_entropy
-- PHOTON_FIELD_PLAN P4 (the Bose occupation decreases with mode energy): boseEinstein_le_of_le — for 0<βω₁≤βω₂,
-- n(βω₂) ≤ n(βω₁): higher-energy photon modes are thermally less occupied (1/(e^{βω}−1) is antitone in βω). The expected
-- monotone falloff of the thermal/Unruh photon spectrum with energy. Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.boseEinstein_le_of_le
-- PHOTON_FIELD_PLAN P4 (the photon entanglement first law δS=δ⟨K⟩): boseEinstein_logit — log((1+n)/n)=βω at the BE
-- occupation (the CCR analog of fermiDirac_logit). hasDerivAt_boseEntropy — d/dn S_BE = log((1+n)/n) (via
-- S_BE=negMulLog n − negMulLog(1+n)). photon_firstLaw — HasDerivAt boseEntropy (βω) (boseEinstein β ω): at the
-- Unruh occupation the bosonic mode entropy's derivative IS the modular energy βω (=2πω at the BW temperature), the
-- bosonic mirror of electron_firstLaw — the first law δS=δ⟨K⟩ that drives the area law. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Photon.boseEinstein_logit
#print axioms QIQTH.Fock.Photon.hasDerivAt_boseEntropy
#print axioms QIQTH.Fock.Photon.photon_firstLaw
-- ★★★ PHOTON_FIELD_PLAN P1/P5 (the photon continuum modular flow IS the bosonic Γ_s(Δ^it) — REUSE): the photon is
-- bosonic, so its field-level wedge modular flow Δ_γ^it = Γ_s(Δ^it) is EXACTLY the existing bosonic secondQuantModFlow
-- (vs the electron's fermionic Γ₋ = ExteriorAlgebra.map). Nothing new is built; this names the reuse in the photon
-- namespace. photonModFlow := secondQuantModFlow on the transverse helicity-±1 one-particle space; photonModFlow_expVec
-- (Γ_s(Δ^it)e(f)=e(Δ^it f)), _vacuum, _zero (=id), _add (the one-parameter group law), _isometric (preserves the Fock
-- inner product). photonModFlowH (Hilbert-space completion) + _isometry + _vacuum. So Δ_γ^it is a one-parameter
-- isometric automorphism group fixing the vacuum, reused wholesale. Axiom-free (standard 3). Free Maxwell only.
#print axioms QIQTH.Fock.Photon.photonModFlow_expVec
#print axioms QIQTH.Fock.Photon.photonModFlow_zero
#print axioms QIQTH.Fock.Photon.photonModFlow_add
#print axioms QIQTH.Fock.Photon.photonModFlow_isometric
#print axioms QIQTH.Fock.Photon.photonModFlowH_isometry
#print axioms QIQTH.Fock.Photon.photonModFlowH_vacuum
-- ★★★ PHOTON_FIELD_PLAN P6/P7 (the gauge-invariant observable algebra = the photon's records): per §0, records/capacity
-- attach to the GAUGE-INVARIANT observables (F_μν, T_μν, energy/helicity), NOT the raw potential A_μ — the photon
-- analogue of the electron's even (parity-fixed) subalgebra (EvenObservables). IsGaugeInvariant a := ∀ gauge transf
-- gaugeAct Λ, gaugeAct Λ a = a (the gauge-fixed points). gaugeInvariantSubalgebra: the records form a Subalgebra
-- (closed under +,*,scalars — isGaugeInvariant_{one,zero,add,mul,smul,algebraMap}). isGaugeInvariant_of_trivial: on the
-- positive physical (transverse) space the gauge action is trivial so EVERY physical observable is a record (why one
-- builds on F=dA, not indefinite A_μ). P7 isGaugeInvariant_map_of_comm: any algebra map commuting with the gauge action
-- (e.g. the modular flow photonModFlow, gauge-blind on the physical space) preserves records — the photon analogue of
-- fermiSecondQuantModFlow_isEven (modular dynamics keeps records as records). Axiom-free (standard 3). Free Maxwell.
#print axioms QIQTH.Fock.Photon.isGaugeInvariant_mul
#print axioms QIQTH.Fock.Photon.gaugeInvariantSubalgebra
#print axioms QIQTH.Fock.Photon.isGaugeInvariant_of_trivial
#print axioms QIQTH.Fock.Photon.isGaugeInvariant_map_of_comm
-- ★★★ PHOTON_FIELD_PLAN P8 (the centered edge-mode entropy decomposition): the photon's regional algebra is a CENTERED
-- flux-sector algebra ⊕_q 𝓑(𝓗_{R,q}) (Gauss-law constraint ⟹ boundary-flux center), so the entanglement entropy splits
-- S(ρ_R)=H(p_q)+Σ_q p_q S(ρ_{R,q}) — the edge-mode/Kabat contact-term structure, the SAME decomposition as the electron's
-- graded capacity with label = boundary flux (not parity). photon_edge_entropy_decomp (= gradedShannon_chain_rule
-- relabelled). photon_edge_term_nonneg: the boundary-flux Shannon term H(p_q)≥0 — at finite cutoff the edge modes add
-- POSITIVELY, vanishing iff the flux is definite (a factor, no center). photon_edge_capacity_le: S≤log(Σ_q dim 𝓗_{R,q})
-- (= gradedShannon_le_log_total). HONEST: the continuum Kabat contact-term SIGN is a renormalization subtlety beyond this
-- finite-cutoff positivity; the Gauss-law boundary algebra + heat-kernel determinant are deferred P10. Axiom-free (std 3).
#print axioms QIQTH.Fock.Photon.photon_edge_entropy_decomp
#print axioms QIQTH.Fock.Photon.photon_edge_term_nonneg
#print axioms QIQTH.Fock.Photon.photon_edge_capacity_le
-- ★★★ PHOTON_FIELD_PLAN P9 (abstract boundary-flux sectors — the edge-mode center): the Gauss-law constraint gives the
-- photon's regional algebra a CENTER generated by the boundary electric flux E_⊥|_{∂R}; its spectrum is the flux sectors
-- Q, and a state induces a classical distribution p over them (the edge-mode dof). fluxEntropy p = Σ_q negMulLog(p_q) =
-- H(p_q), the entropy of the central flux distribution (the edge-mode term of P8's split). photon_flux_entropy_nonneg:
-- H(p_q)≥0. photon_flux_entropy_le_log_card: H(p_q) ≤ log|Q| — the edge-mode/center capacity is bounded by the boundary
-- flux-sector COUNT (the "edge capacity ≤ boundary flux count" bound, via shannon_le_log_card). photon_centered_entropy_eq:
-- S = fluxEntropy p + Σ_q p_q S_q (P8 with the flux term named). The flux observables are CENTRAL records (P6). HONEST: the
-- continuum Gauss-law boundary algebra + Kabat contact determinant (sign) are deferred P10. Axiom-free (standard 3).
#print axioms QIQTH.Fock.Photon.photon_flux_entropy_nonneg
#print axioms QIQTH.Fock.Photon.photon_flux_entropy_le_log_card
#print axioms QIQTH.Fock.Photon.photon_centered_entropy_eq
-- PHOTON_FIELD_PLAN P6/P10 bridge (the field strength F=dA is gauge-invariant + the Bianchi identity, via d²=0):
-- fieldStrength_gauge_invariant — F=dA is unchanged by a gauge shift A↦A+dΛ (because the pure-gauge dΛ ∈ ker d_F, the
-- d²=0 cochain condition d_F∘d_gauge=0); the concrete reason the photon's records are the gauge-invariant F_μν, NOT the
-- gauge-variant A_μ (§0/P6). bianchi_identity — d_next(F)=0 for F=dA (d_next∘d_F=0): the homogeneous Maxwell eqs dF=0
-- (Bianchi). Both gauge-invariance and closedness of F are the two faces of d²=0. Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.fieldStrength_gauge_invariant
#print axioms QIQTH.Fock.Photon.bianchi_identity
-- PHOTON_FIELD_PLAN P6 (sharpest form — the field strength descends to the gauge quotient): fieldStrength_descends_to_
-- quotient — since range d_gauge ⊆ ker d_F (d²=0), F=dA factors as F̄∘mkQ through A ⧸ range d_gauge (Submodule.liftQ),
-- so the photon's physical observable is a function of the GAUGE-EQUIVALENCE CLASS, not the gauge representative — the
-- "records live on the physical (gauge-quotient) configuration space" thesis (§0/P6). Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.fieldStrength_descends_to_quotient
-- PHOTON_FIELD_PLAN P6/P9 bridge (the cohomological closed/exact structure): fieldStrength_eq_iff_sub_mem_ker — d_F a =
-- d_F a' ↔ a−a' ∈ ker d_F (the F-fibers are closed-element cosets). pureGauge_le_ker — range d_gauge ≤ ker d_F (d²=0 as a
-- submodule inclusion: exact ⊆ closed; a gauge shift never changes F). The quotient ker d_F ⧸ range d_gauge is the first
-- cohomology = the topological/boundary-flux sectors (closed-but-not-exact) — the algebraic home of the photon's edge-mode
-- center (P9 PhotonFluxSectors): nontrivial cohomology = nontrivial flux; trivial for a contractible region (factor, no
-- center). Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.fieldStrength_eq_iff_sub_mem_ker
#print axioms QIQTH.Fock.Photon.pureGauge_le_ker
-- PHOTON_FIELD_PLAN P6/P9 (trivial cohomology ⟹ F determines A up to gauge): fieldStrength_eq_iff_gauge_of_trivial_
-- cohomology — when ker d_F = range d_gauge (every closed is exact; a CONTRACTIBLE region, no flux sectors, the regional
-- algebra a factor), d_F a = d_F a' ↔ a−a' ∈ range d_gauge: the field-strength record F=dA is a COMPLETE invariant of the
-- physical (gauge) configuration. The honest §0/P9 caveat — the boundary-flux center exists only when the cohomology
-- (closed-mod-exact) is nontrivial. Axiom-free (standard 3); free Maxwell.
#print axioms QIQTH.Fock.Photon.fieldStrength_eq_iff_gauge_of_trivial_cohomology
-- PHOTON_FIELD_PLAN P1 (the transverse helicity-±1 one-particle space — 2 physical polarizations): the photon is massless
-- spin-1 with exactly 2 helicities ±1; model h_γ = h_{+1}⊕h_{−1}. photon_helicity_finrank: dim h_γ = dim h_+ + dim h_−.
-- photon_two_polarizations: dim(ℂ×ℂ)=2 — exactly 2 transverse polarizations per momentum (vs the 4 components of A_μ, 2
-- unphysical gauge/longitudinal modes excluded by working on the positive physical space). photon_capacity_helicity:
-- dim Γ_s^{≤N}(h_γ) = C(dim h_+ + dim h_− + N, N) — the cutoff bosonic capacity counts the 2 polarizations. Std 3; free Maxwell.
#print axioms QIQTH.Fock.Photon.photon_helicity_finrank
#print axioms QIQTH.Fock.Photon.photon_two_polarizations
#print axioms QIQTH.Fock.Photon.photon_capacity_helicity
-- PHOTON_FIELD_PLAN P1/P3 (the 2-polarization capacity): photon_capacity_two_helicity — for d modes per helicity the
-- photon capacity is C(2d+N, N) (the two transverse polarizations doubling the mode count). photon_capacity_helicity_ge:
-- truncFockDim d N ≤ truncFockDim (2d) N — the second polarization enlarges the capacity (the photon carries more
-- information than a single-component scalar-like field of the same per-helicity mode count). Axiom-free (standard 3).
#print axioms QIQTH.Fock.Photon.photon_capacity_two_helicity
#print axioms QIQTH.Fock.Photon.photon_capacity_helicity_ge

end QIQTH.AxiomAudit
