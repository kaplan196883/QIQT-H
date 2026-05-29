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

end QIQTH.AxiomAudit
