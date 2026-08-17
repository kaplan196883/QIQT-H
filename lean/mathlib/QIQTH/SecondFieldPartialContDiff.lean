/-
  SecondFieldPartialContDiff — the step-2→3 BRIDGE of the `hCConv` transposition route: the concrete
  second field-partial `Φ = ∂ᵤ∂ᵥ[field slot] H` of a two-variable kernel `H : Point n × Point n → ℝ`
  is `ContDiffAt ℝ 1` at the origin AS SOON AS `H` is JOINTLY `ContDiffAt ℝ 3` there — which is exactly
  the hypothesis `WitnessTranspositionGeneralBound.general_transposition_sliver_of_contDiffAt` (J4-823)
  consumes.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is one
  regularity-collapse brick.  No `sorry`, no `:= True`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise.  std-3 only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT (JET4_TOWER_PLAN J4-823 → J4-828/829, plan `tranquil-stargazing-fox.md` Brick 3/4).

  The J4-818 transposition wall was dissolved by J4-823 into ONE joint-smoothness fact: for the
  witness's TWO-variable second field-partial `Φ : Point n × Point n → ℝ`, the transposition difference
  `Φ(0,z) − Φ(z,0)` is `O(√ε)` on the sliver window PROVIDED `Φ` is `ContDiffAt ℝ 1` at `(0,0)`
  (`general_transposition_sliver_of_contDiffAt`).  What was left explicit there was: EXHIBIT the
  concrete `Φ` (the second field-partial) and prove `ContDiffAt ℝ 1 Φ (0,0)`.

  ── THE COLLAPSE (this file).  Taking two FIELD-slot (first-component `p`) derivatives of `H` drops two
  regularity orders, and the field-slot derivatives depend `C¹` on the base slot `q` iff `H` is jointly
  one order higher — so `Φ ∈ C¹` at `(0,0)` follows from `H ∈ C³` JOINTLY at `(0,0)`.  Concretely, with

      `Φ = secondFieldPartial H v u := fun x => fderiv ℝ (fun y => fderiv ℝ H y (v,0)) x (u,0)`

  the second field-partial in field directions `v, u` (embedded in the `p`-slot as `(v,0)`, `(u,0)`):
    * `fderiv ℝ H` is `ContDiffAt ℝ 2` at `(0,0)` (`ContDiffAt.fderiv_right`, `2+1 ≤ 3`);
    * evaluating at the constant direction `(v,0)` keeps `ContDiffAt ℝ 2` (`ContDiffAt.clm_apply`);
    * `fderiv` of THAT is `ContDiffAt ℝ 1` (`ContDiffAt.fderiv_right`, `1+1 ≤ 2`);
    * evaluating at `(u,0)` keeps `ContDiffAt ℝ 1` (`ContDiffAt.clm_apply`).

  ── HONEST FIREWALL (binding).  This is a genuine, NON-VACUOUS reduction: the hypothesis
  `ContDiffAt ℝ 3 H (0,0)` is satisfiable (every `C^∞` kernel meets it) and is NOT the conclusion.  It
  turns the residual `hCConv` transposition wall from "`ContDiffAt ℝ 1` of an unspecified `Φ`" into the
  clean, standard-geometry statement "JOINT `ContDiffAt ℝ 3` of the witness kernel `H` at the origin"
  — whose SOLE missing ingredient is the mixed base-slot regularity `∂_q ∂²_p V` (sub-brick 3b,
  `ChartMixedThirdJetBasepoint`), whose abstract math is banked but whose weld to the concrete
  `.choose`-built `uniformFlowExp` needs second-order base regularity of that flow (`harem`/`hbrem`
  quadratic-in-`s` remainders) not yet in the tower.  The field-slot half is already discharged
  (`InverseChartFieldC3.witnessField_contDiffAt3_center`, sub-brick 3a).  This file does NOT supply the
  joint hypothesis for the concrete witness, does NOT wire into `kPrime_opNorm_sliver_bound.hcomp`, and
  does NOT close `hCConv`.  a₁ = R/6 remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import Mathlib
import QIQTH.WitnessTranspositionGeneralBound

open QIQTH.Curvature
open scoped Topology NNReal

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- **The concrete second field-partial** of a two-variable kernel `H : Point n × Point n → ℝ` in
    FIELD directions `v, u` (the first / `p` slot).  `∂ᵤ∂ᵥ[field] H` — both derivatives taken in the
    `p`-slot (directions embedded as `(v,0)`, `(u,0)`), the `q`-slot held as an honest parameter.  This
    is the exact object `general_transposition_sliver_of_contDiffAt`'s `Φ` denotes. -/
noncomputable def secondFieldPartial (H : Point n × Point n → ℝ) (v u : Point n) :
    Point n × Point n → ℝ :=
  fun x => fderiv ℝ (fun y => fderiv ℝ H y (v, (0 : Point n))) x (u, (0 : Point n))

/-- **★ THE COLLAPSE — joint `C³` ⟹ second field-partial `∈ C¹`.**  If `H : Point n × Point n → ℝ` is
    JOINTLY `ContDiffAt ℝ 3` at the origin `(0,0)`, then its second field-partial
    `secondFieldPartial H v u` (two `p`-slot derivatives) is `ContDiffAt ℝ 1` at `(0,0)` — exactly the
    hypothesis `general_transposition_sliver_of_contDiffAt` (J4-823) consumes.  Two applications of
    `ContDiffAt.fderiv_right` (each dropping one order) interleaved with `ContDiffAt.clm_apply`
    (evaluating at the constant field direction).  Non-vacuous (satisfiable by any `C^∞` kernel),
    NOT `a₁ = R/6`. -/
theorem secondFieldPartial_contDiffAt_one (H : Point n × Point n → ℝ) (v u : Point n)
    (hH : ContDiffAt ℝ 3 H ((0 : Point n), (0 : Point n))) :
    ContDiffAt ℝ 1 (secondFieldPartial H v u) ((0 : Point n), (0 : Point n)) := by
  -- `fderiv ℝ H` is `C²` at the origin (drops one order from `C³`).
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ H) ((0 : Point n), (0 : Point n)) :=
    hH.fderiv_right (by norm_num)
  -- evaluating at the constant field direction `(v,0)` keeps `C²`.
  have hg1 : ContDiffAt ℝ 2
      (fun y => fderiv ℝ H y (v, (0 : Point n))) ((0 : Point n), (0 : Point n)) :=
    h1.clm_apply contDiffAt_const
  -- `fderiv` of that scalar field is `C¹` (drops the second order).
  have h3 : ContDiffAt ℝ 1
      (fderiv ℝ (fun y => fderiv ℝ H y (v, (0 : Point n)))) ((0 : Point n), (0 : Point n)) :=
    hg1.fderiv_right (by norm_num)
  -- evaluating at `(u,0)` keeps `C¹` — this is `secondFieldPartial H v u`.
  have h4 : ContDiffAt ℝ 1
      (fun x => fderiv ℝ (fun y => fderiv ℝ H y (v, (0 : Point n))) x (u, (0 : Point n)))
      ((0 : Point n), (0 : Point n)) :=
    h3.clm_apply contDiffAt_const
  exact h4

/-- **★★ THE BRIDGE — joint `C³` ⟹ the J4-823 transposition sliver bound for the second field-partial.**
    Composing `secondFieldPartial_contDiffAt_one` with `general_transposition_sliver_of_contDiffAt`:
    for a kernel `H` jointly `ContDiffAt ℝ 3` at the origin, the transposition difference of its second
    field-partial obeys the closed `√ε` sliver rate.  This is the step-2→3 result the plan sequenced —
    the transposition wall's `ContDiffAt ℝ 1 Φ (0,0)` hypothesis is now discharged from JOINT `C³` of the
    kernel.  What remains for `hCConv` is joint `C³` of the CONCRETE witness at `(0,0)` (field half done
    via sub-brick 3a; mixed base half is sub-brick 3b's concrete weld) and the wiring into
    `kPrime_opNorm_sliver_bound.hcomp`.  NOT `a₁ = R/6`. -/
theorem secondFieldPartial_transposition_sliver (H : Point n × Point n → ℝ) (v u : Point n)
    (hH : ContDiffAt ℝ 3 H ((0 : Point n), (0 : Point n))) :
    ∃ (K : ℝ≥0) (r : ℝ), 0 < r ∧ ∀ (z : Point n) (ε : ℝ), ‖z‖ < r → ‖z‖ ≤ Real.sqrt ε →
      |secondFieldPartial H v u ((0 : Point n), z) - secondFieldPartial H v u (z, (0 : Point n))|
        ≤ (K : ℝ) * Real.sqrt ε :=
  general_transposition_sliver_of_contDiffAt (secondFieldPartial H v u)
    (secondFieldPartial_contDiffAt_one H v u hH)

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms secondFieldPartial_contDiffAt_one
#print axioms secondFieldPartial_transposition_sliver
end AxiomChecks
