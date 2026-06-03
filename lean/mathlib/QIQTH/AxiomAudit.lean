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
-- expected: standard + step1_schur_classification + step3_tensor_multiplicativity
-- (the two acknowledged interface axioms)

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

end QIQTH.AxiomAudit
