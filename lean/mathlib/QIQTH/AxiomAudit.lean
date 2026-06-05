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

-- Finite-dimensional Tomita–Takesaki (the modular engine)
#print axioms QIQTH.FiniteModularTheory.modAut_mul
-- expected: standard only — σ_t is a *-endomorphism (⅟m * m cancels)
#print axioms QIQTH.FiniteModularTheory.modAut_comp
-- expected: standard only — one-parameter group law σ_s∘σ_t = σ_{s+t}
#print axioms QIQTH.FiniteModularTheory.kms_condition
-- expected: standard only — KMS boundary identity from trace cyclicity.
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

end QIQTH.AxiomAudit
