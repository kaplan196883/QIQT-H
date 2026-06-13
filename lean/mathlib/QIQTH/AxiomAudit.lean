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
#print axioms QIQTH.RefinementBorn.sq_not_refinementNatural
-- expected: standard only — the α=2 rule is NOT refinement-natural (it would signal); the α-family is
-- exactly excluded by no-signaling. So: no-signaling under refinement ⇒ Born; without it, every α survives.

end QIQTH.AxiomAudit
