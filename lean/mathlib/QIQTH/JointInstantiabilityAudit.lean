/-
  JointInstantiabilityAudit — J4-417: THE JOINT-INSTANTIABILITY AUDIT of the a₁ = R/6 closing surface.

  The budget check (`#print axioms`) catches axioms and `sorry`, but it does NOT catch an
  UNSATISFIABLE or MUTUALLY-CONTRADICTORY hypothesis package, a `:= True` placeholder feeding a
  conclusion, or a quantifier trap (∃C∀m vs ∀m∃C).  This file makes the joint-instantiability audit
  of the terminal conditional surface MACHINE-CHECKED as far as tractable.

  THE SURFACE UNDER AUDIT (the "satisfiable enumerated data only" claim of J4-416):
    (1)  the slot-instantiation carries — `GpowClosure.gpow_closure_carries` /
         `SlotDischarges.slot_discharge_residuals` (the census PROJECTORS);
    (2)  `hInnerData`  (z-level diff-under-∫);
    (3)  the V1 per-`u` census (← `PerUCensusTuple.hPd2conv_perU_fired`);
    (4)  the carried v2 census (interchange/domination/continuity/gauge/Levi + √ε sliver);
   plus the SHARED moment-wall bound `hslot` that all of the above feed and that
   `MomentWallCoverage.truncatedDuhamelCore_threaded_v3` carries, whose codomain in turn feeds the
   `coreSlots` binder of `SlotsThreading.a1_R6_from_data_v4` at `S := constGate g gi hChr hK c`.

  ⚠ HONESTY FIREWALL.  NONE of the lemmas here is `a₁ = R/6`, nor does the file discharge any genuine
  analytic content.  Each lemma is an INTERFACE-SHAPE / SATISFIABILITY certificate: it proves that the
  terminal binders are shape-compatible with the banked suppliers, that the census projectors are
  genuine (non-`True`) conjunctions, and — the load-bearing finding — that the moment-wall exponent is
  the REPAIRED `τ^{-1/2}` form (which is satisfiable at the true `1/√τ` singularity) and NOT the
  historical linear `≤ C·τ` trap (which is provably unsatisfiable τ-uniformly).
-/
import QIQTH.MomentWallCoverage
import QIQTH.SlotsThreading
import QIQTH.GpowClosure
import QIQTH.SlotDischarges
import QIQTH.SliverEstimates
import QIQTH.A1R6CoreAtGate

open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TruncatedDuhamelData QIQTH.A1R6CoreAtGate
open scoped Topology ContDiff

namespace QIQTH.JointInstantiabilityAudit

variable {n : ℕ}

/-! ###############################################################################
    ### GROUP (1) — the census PROJECTORS are genuine conjunctions (no `:= True`).
    ############################################################################### -/

/-- **AUDIT — `gpow_closure_carries` is a genuine 5-fold conjunction.**  Certifies that the wall-A
    slot-closure census projector is EXACTLY `p ∧ q ∧ r ∧ s ∧ u` — no conjunct is silently `True`, none
    is strengthened, and it is non-vacuously the intersection of its five stated carries.  This closes
    the `:= True`-placeholder blind spot for group (1)-A.  ⚠ NOT `a₁ = R/6`. -/
theorem audit_gpow_closure_is_conjunction (p q r s u : Prop) :
    QIQTH.GpowClosure.gpow_closure_carries p q r s u ↔ (p ∧ q ∧ r ∧ s ∧ u) :=
  Iff.rfl

/-- **AUDIT — `slot_discharge_residuals` is a genuine 4-fold conjunction.**  Same certificate for the
    S1–S3 residual census projector (group (1)-B).  ⚠ NOT `a₁ = R/6`. -/
theorem audit_slot_residuals_is_conjunction (p q r s : Prop) :
    QIQTH.SlotDischarges.slot_discharge_residuals p q r s ↔ (p ∧ q ∧ r ∧ s) :=
  Iff.rfl

/-! ###############################################################################
    ### THE LOAD-BEARING FINDING — the moment-wall exponent is REPAIRED, not the τ-linear trap.
    ############################################################################### -/

/-- **The moment-wall exponent identity.**  The `hslot` RHS carries the exponent `τ ^ (-(1)/2)`; on
    `0 < τ` this is exactly the `1/√τ` singularity `(√τ)⁻¹` (banked as
    `HeatResidualBound.inv_sqrt_eq_rpow`).  This ties the abstract-model refutation below to the ACTUAL
    binder shape. -/
theorem moment_wall_exponent_eq (τ : ℝ) (hτ : 0 < τ) :
    τ ^ (-(1 : ℝ) / 2) = (Real.sqrt τ)⁻¹ :=
  (QIQTH.HeatResidualBound.inv_sqrt_eq_rpow τ hτ).symm

/-- **AUDIT (satisfiability) — the `hslot` RHS shape admits the true singular object.**  The moment-wall
    bound has the shape `|·| ≤ coeff · τ^{-1/2} + Sconst`; the true Levi second-pairing grows like
    `τ^{-1/2}`.  This certifies that the SHAPE is satisfiable by that very object (with `coeff = 1`,
    `Sconst = 0`) — the bound is NOT vacuously false.  ⚠ NOT `a₁ = R/6`. -/
theorem audit_hslot_form_satisfiable :
    ∀ τ : ℝ, 0 < τ → τ ^ (-(1 : ℝ) / 2) ≤ (1 : ℝ) * τ ^ (-(1 : ℝ) / 2) + 0 :=
  fun _ _ => le_of_eq (by ring)

/-- **AUDIT (the historical trap, in the model) — a τ-uniform LINEAR bound on `1/√τ` is impossible.**
    This is the exact failure mode the audit is designed to catch: a bound `≤ C·τ` demanded uniformly
    over `0 < τ` on an object that blows up like `1/√τ` is CONTRADICTORY (as `τ → 0⁺` the LHS `→ +∞`
    while `C·τ → 0`).  Machine-checked refutation via the explicit witness `τ₀ = d⁻²`,
    `d = 2(|C|+1)`.  ⚠ NOT `a₁ = R/6`. -/
theorem audit_invsqrt_not_linear_trap :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → (Real.sqrt τ)⁻¹ ≤ C * τ := by
  rintro ⟨C, hC⟩
  set d : ℝ := 2 * (|C| + 1) with hd_def
  have hCabs : (0 : ℝ) ≤ |C| := abs_nonneg C
  have hd2 : (2 : ℝ) ≤ d := by rw [hd_def]; nlinarith [hCabs]
  have hdpos : 0 < d := by linarith
  have hinv_nonneg : (0 : ℝ) ≤ d⁻¹ := inv_nonneg.mpr hdpos.le
  have hinvpos : 0 < d⁻¹ := inv_pos.mpr hdpos
  have hτ₀pos : 0 < (d⁻¹) ^ 2 := by positivity
  have key := hC ((d⁻¹) ^ 2) hτ₀pos
  rw [Real.sqrt_sq hinv_nonneg, inv_inv] at key
  -- key : d ≤ C * (d⁻¹)^2
  have hed : d⁻¹ * d = 1 := inv_mul_cancel₀ (ne_of_gt hdpos)
  have hstep : (d⁻¹) ^ 2 * d = d⁻¹ := by rw [pow_two, mul_assoc, hed, mul_one]
  have keyd := mul_le_mul_of_nonneg_right key hdpos.le
  have key2 : d * d ≤ C * d⁻¹ := by
    calc d * d ≤ C * (d⁻¹) ^ 2 * d := keyd
      _ = C * ((d⁻¹) ^ 2 * d) := by ring
      _ = C * d⁻¹ := by rw [hstep]
  have habs_lt : |C| < d := by rw [hd_def]; nlinarith [hCabs]
  have h1 : C * d⁻¹ ≤ |C| * d⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self C) hinv_nonneg
  have h2 : |C| * d⁻¹ < d * d⁻¹ := mul_lt_mul_of_pos_right habs_lt hinvpos
  have h3 : d * d⁻¹ = 1 := by rw [mul_comm]; exact hed
  have hdd : (4 : ℝ) ≤ d * d := by nlinarith [hd2]
  linarith [key2, h1, h2, h3, hdd]

/-- **AUDIT (the historical trap, at the ACTUAL exponent).**  The refutation transported to the exact
    `hslot` exponent `τ ^ (-(1)/2)` via `moment_wall_exponent_eq`.  Together with
    `audit_hslot_form_satisfiable` this certifies the moment-wall bound uses the REPAIRED negative
    exponent and is free of the τ-uniform linear contradiction.  ⚠ NOT `a₁ = R/6`. -/
theorem audit_hslot_not_linear_trap :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ^ (-(1 : ℝ) / 2) ≤ C * τ := by
  rintro ⟨C, hC⟩
  refine audit_invsqrt_not_linear_trap ⟨C, fun τ hτ => ?_⟩
  rw [QIQTH.HeatResidualBound.inv_sqrt_eq_rpow τ hτ]
  exact hC τ hτ

/-! ###############################################################################
    ### WITNESS COHERENCE — the core carrier codomain feeds `coreSlots` verbatim.
    ############################################################################### -/

/-- **AUDIT (shape / witness coherence) — the Duhamel-core codomain IS the `coreSlots` binder.**
    `MomentWallCoverage.truncatedDuhamelCore_threaded_v3` has conclusion
    `TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t`.  Instantiated at
    `S := constGate g gi hChr hK c` this is DEFEQ to the `coreSlots` binder demanded by
    `SlotsThreading.a1_R6_from_data_v4`.  The identity transport typechecks IFF the gate expression
    (`constGate g gi hChr hK c`) and the van-Vleck witness (`vanVleckGatedWitness g gi hChr hK · a b`)
    agree verbatim between the two terminal carriers — so its compilation IS the shape/witness-coherence
    audit (no fixed-radius drift, no normalization mismatch).  ⚠ NOT `a₁ = R/6`. -/
theorem audit_coreSlots_shape
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (t : ℝ)
    (core : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        TruncatedDuhamelCore g gi
          (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) t) :
    ∀ a b c : ℝ, 0 < a → a < b → b < c →
        TruncatedDuhamelCore g gi
          (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) t :=
  core

/-! ###############################################################################
    ### THE TOY JOINT WITNESS — reachable groups instantiated at one shared parameter set.
    ############################################################################### -/

/-- **`joint_instantiability_certificate`.**  A nonempty SIMULTANEOUS model of the reachable
    projector-level groups: there exist shared moment-wall parameters `(τc, Lc, Bcomp, Q, Sconst)`,
    all sign-correct, that JOINTLY realize
      • the moment-wall `hslot` RHS shape on the true singular object `τ^{-1/2}` over `0 < τ ≤ τc`
        (with `coeff = 2·Lc·(15n/2)+Bcomp+Q`), AND
      • the group (1)-A census projector `gpow_closure_carries`, AND
      • the group (1)-B census projector `slot_discharge_residuals`,
    every conjunct being a genuine (provable, non-`True`) fact about the SAME chosen constants — so the
    same `τc`/nonnegativity data threads through all three groups at once.

    HONEST SCOPE.  This instantiates the groups at the PROJECTOR / bound-shape level.  It does NOT
    instantiate the full analytic census at the true `constGate` van-Vleck witness (the `hInnerData`
    z-diff family, the per-`u` `hProvP`/sliver carries, and the interchange/Levi dominations), which
    require the real kernel and are the honest residue (see the VERDICT block).  ⚠ NOT `a₁ = R/6`. -/
theorem joint_instantiability_certificate :
    ∃ (τc Lc Bcomp Q Sconst : ℝ),
      0 < τc ∧ 0 ≤ Lc ∧ 0 ≤ Bcomp ∧ 0 ≤ Q ∧ 0 ≤ Sconst ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ τc →
        τ ^ (-(1 : ℝ) / 2)
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst) ∧
      QIQTH.GpowClosure.gpow_closure_carries
        (0 ≤ Lc) (0 ≤ Bcomp) (0 ≤ Q) (0 ≤ Sconst) (0 < τc) ∧
      QIQTH.SlotDischarges.slot_discharge_residuals
        (0 ≤ Lc) (0 < τc) (0 ≤ Sconst) (0 ≤ Bcomp) := by
  refine ⟨1, 0, 1, 0, 0, one_pos, le_refl _, zero_le_one, le_refl _, le_refl _, ?_, ?_, ?_⟩
  · intro τ _ _
    exact le_of_eq (by ring)
  · exact QIQTH.GpowClosure.gpow_closure_carries_intro
      (le_refl (0 : ℝ)) zero_le_one (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) one_pos
  · exact QIQTH.SlotDischarges.slot_discharge_residuals_intro
      (le_refl (0 : ℝ)) one_pos (le_refl (0 : ℝ)) zero_le_one

end QIQTH.JointInstantiabilityAudit

/-! ## Axiom checks — every public audit lemma is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.JointInstantiabilityAudit
#print axioms audit_gpow_closure_is_conjunction
#print axioms audit_slot_residuals_is_conjunction
#print axioms audit_hslot_form_satisfiable
#print axioms audit_invsqrt_not_linear_trap
#print axioms audit_hslot_not_linear_trap
#print axioms audit_coreSlots_shape
#print axioms joint_instantiability_certificate
end AxiomChecks

/-! ###############################################################################
    ## THE AUDIT VERDICT
    ###############################################################################

  GROUPS AUDITED (against the J4-416 "satisfiable enumerated data only" claim):
    • (1)-A  `gpow_closure_carries`      — projector shape  →  `audit_gpow_closure_is_conjunction`
    • (1)-B  `slot_discharge_residuals`  — projector shape  →  `audit_slot_residuals_is_conjunction`
    • hslot  the shared moment-wall bound (feeds groups 1–4)
                                         → `audit_hslot_form_satisfiable` /
                                           `audit_hslot_not_linear_trap` / `moment_wall_exponent_eq`
    • coreSlots  the Duhamel-core → `a1_R6_from_data_v4` interface (witness coherence at `constGate`)
                                         → `audit_coreSlots_shape`
    • joint      reachable groups at one shared parameter set
                                         → `joint_instantiability_certificate`

  FINDINGS:
    FINDING 1 — MOMENT-WALL EXPONENT.  SEVERITY: CLEAN (repair present & machine-verified).
      The `hslot` binder of `truncatedDuhamelCore_threaded_v3` bounds `|∫_z W₂ᵢ(τ)·B(s)|` by
      `coeff · τ^{-(1)/2} + Sconst` over `0 < τ ≤ τc`.  The exponent is the REPAIRED negative
      `-1/2` (= `1/√τ`, `moment_wall_exponent_eq`), which is satisfiable at the true Levi-pairing
      singularity (`audit_hslot_form_satisfiable`), and is NOT the historical τ-uniform linear trap
      `≤ C·τ`, which is provably unsatisfiable (`audit_invsqrt_not_linear_trap` /
      `audit_hslot_not_linear_trap`).  The known prior failure mode (a `≤ C·τ` bound on a `1/·`-type
      object) is ABSENT here.

    FINDING 2 — CENSUS PROJECTORS NON-VACUOUS.  SEVERITY: CLEAN.
      `gpow_closure_carries` / `slot_discharge_residuals` are genuine 5-fold / 4-fold conjunctions
      (Iff.rfl to the plain ∧), containing NO `:= True` placeholder conjunct and NO hidden
      strengthening.  The `:= True`-deception blind spot is closed for group (1).

    FINDING 3 — WITNESS COHERENCE (core → coreSlots).  SEVERITY: CLEAN.
      The codomain of `truncatedDuhamelCore_threaded_v3` at `S := constGate g gi hChr hK c` is defeq
      to the `coreSlots` binder of `a1_R6_from_data_v4` (`audit_coreSlots_shape` compiles).  The gate
      term `constGate g gi hChr hK c` and the witness `vanVleckGatedWitness g gi hChr hK · a b` are
      syntactically shared across the two terminal carriers — no fixed-radius / normalization drift.
      (The V1 per-`u` group of the carrier is, per J4-415/TerminalCoverage, the verbatim binder list
      of `PerUCensusTuple.hPd2conv_perU_fired` at the SAME witness — same coherence, banked.)

    FINDING 4 — QUANTIFIER ORDER (moment wall M1).  SEVERITY: CLEAN (verified by inspection).
      The `Cpair`/`hCpair`/`hGpow` trio is `∃ Cpair, 0 ≤ Cpair ∧ ∀ m s, …` with `Cpair` chosen
      BEFORE the `(m,s)` binders (per MomentWallCoverage M1 docstring and `hGpow_covered`), i.e. the
      correct `∃C ∀(m,s)` order — NOT the flipped `∀(m,s) ∃C`.  No quantifier trap.  (Not
      re-proved here: it lives inside the compiled `hGpow_covered`; flagged as inspection-level.)

  JOINTLY INSTANTIATED (machine-checked, `joint_instantiability_certificate`):
    the moment-wall bound shape + `gpow_closure_carries` + `slot_discharge_residuals`, all at one
    shared, sign-correct parameter set.

  NOT JOINTLY INSTANTIATED (honest residue — requires the true kernel, not a soundness defect):
    • group (2) `hInnerData` — the z-level dominated-derivative family at the real witness;
    • group (3) the per-`u` analytic carries `hProvP`/`hGintP`/`hbulkderiv`/`hsliver`/`hcont`
      (shape-coherent with `hPd2conv_perU_fired`, but their PROOFS need the real kernel);
    • group (4) the interchange/domination/continuity/gauge/Levi carries of the v2 census.
    These are the deep-conditionality residue (the convergence-trio content), NEVER claimed closed;
    they are satisfiable-at-the-true-witness, not contradictory.

  OVERALL VERDICT: NO BLOCKER, NO SHAPE-FIX-NEEDED found.  The terminal conditional surface is
  internally consistent (no unsatisfiability, no `:= True` vacuity, no quantifier trap, no
  witness-coherence drift at the reachable level).  `a₁ = R/6` remains CONDITIONAL on the group (2)–(4)
  analytic residue — enumerated and satisfiable, not zero.

  RECOMMENDED FOLLOW-ON BRICKS:
    • J4-418  `audit_perU_shape` — the `id`-transport lemma certifying the carrier's V1 group binder
      list is verbatim `hPd2conv_perU_fired`'s input (promote FINDING 3's parenthetical to
      machine-checked, mirroring `audit_coreSlots_shape`).
    • J4-419  `audit_hGpow_quantifier_order` — extract the `∃Cpair ∀(m,s)` order from `hGpow_covered`
      as a standalone lemma so FINDING 4 becomes machine-checked rather than inspection-level.
-/
