/-
  CORRESPONDENCE ASSEMBLY — the conditional-Prop assembly of the DY7 conjecture together with the
  `a₁ = R/6` algebraic core (conjecture-input program, brick G3).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  MANDATORY FIREWALL (binding, honest scope).

  • This is a **CONDITIONAL THEOREM**, NOT a proof of `FlatSpaceRecordGravityCorrespondence`. The
    three still-cited physical inputs (#3 `a₁ = R/6`, #4 same-regulator, #5 cutoff identification)
    are carried as STRUCTURE HYPOTHESES (`PhysicalInputs`), NEVER as Lean `axiom`s; inputs #1 (G1)
    and #2 (G2) are the separately-proved finite determinant/replica bricks. The theorem proves the
    ENTAILMENT (inputs ⟹ correspondence), making precisely-auditable what physics is assumed — it
    does NOT discharge the inputs.

  • **NON-VACUITY.** The middle equality (loop = area/4G_ind) is DERIVED from D3d's proved
    `QIQTH.ConicalSakharov.induced_product`; the carried hypotheses reference only lower-level
    building blocks (regulators, curvature coefficient, record-side vs heat-kernel-side entropy),
    never the four opaque output fields of `ContinuumLimitData`. Hence the conditional theorem is
    not vacuously true.

  • **Part 1 (`a₁ = R/6`)** is the ALGEBRAIC coefficient once the local heat expansion is supplied.
    The ANALYTIC Seeley–DeWitt identification `heatTraceCoeff₁(P) = ∫ (R/6 + tr E)` needs Mathlib's
    absent Riemannian heat-kernel theory and stays CITED. Only the minimal-scalar (ξ=0 ⟹ a₁=R/6)
    and 4D-conformal (ξ=1/6 ⟹ a₁=0) specializations are proved here, purely algebraically.

  • NOT the conjecture, NOT the strong holographic principle, NOT quantum gravity. No axioms, no
    `sorry`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ConicalSakharov
import QIQTH.Conjectures

noncomputable section

namespace QIQTH.CorrespondenceAssembly

open QIQTH.ConicalSakharov QIQTH.Conjectures

/-! ### PART 1 — the `a₁ = R/6` algebraic core

The Seeley–DeWitt second heat-kernel coefficient for a Laplace-type operator `P = −(∇² + E)` is
`a₁ = R/6 + tr E`. This is the ALGEBRAIC coefficient given the local heat expansion; the analytic
`heatTraceCoeff₁(P) = ∫ (R/6 + tr E)` identification (Riemannian heat-kernel theory absent from
Mathlib) stays CITED. -/

/-- Laplace-type convention `P = −(∇² + E)`:  `a₁ = R/6 + tr E`. -/
def a1Laplace (R trE : ℝ) : ℝ := R / 6 + trE

/-- Scalar with `P = −∇² + ξR` ⟹ `E = −ξR` ⟹ `a₁ = (1/6 − ξ) R`. -/
def scalarA1 (ξ R : ℝ) : ℝ := (1 / 6 - ξ) * R

theorem a1_scalar_xi (R ξ : ℝ) : a1Laplace R (-ξ * R) = scalarA1 ξ R := by
  unfold a1Laplace scalarA1; ring

/-- **Minimal scalar** `ξ = 0` ⟹ `a₁ = R/6`. -/
theorem a1_minimal (R : ℝ) : scalarA1 0 R = R / 6 := by
  unfold scalarA1; ring

/-- The conformal coupling in dimension `d`:  `ξ_c = (d−2)/(4(d−1))`. -/
def xiConf (d : ℝ) : ℝ := (d - 2) / (4 * (d - 1))

theorem xiConf_four : xiConf 4 = (1 : ℝ) / 6 := by
  norm_num [xiConf]

/-- **4D conformal scalar** `ξ = 1/6` ⟹ `a₁ = 0`. -/
theorem a1_conformal_four (R : ℝ) : scalarA1 (xiConf 4) R = 0 := by
  rw [xiConf_four]; unfold scalarA1; ring

/-- **The `a₁` algebraic core, bundled**: minimal scalar gives `R/6`, 4D conformal gives `0`. -/
theorem a1_core (R : ℝ) : scalarA1 0 R = R / 6 ∧ scalarA1 (xiConf 4) R = 0 :=
  ⟨a1_minimal R, a1_conformal_four R⟩

/-! ### PART 2 — the conditional-Prop assembly

We build a constructive record whose fields are LOWER-LEVEL building blocks that the proved rungs
consume, DEFINE the four opaque `ContinuumLimitData` quantities from them, project to the opaque
data, and carry the three still-cited physical inputs (#3/#4/#5) as labelled hypotheses over the
building blocks only (the vacuity guard). -/

/-- The constructive continuum data: lower-level building blocks the rungs consume. The four opaque
    `ContinuumLimitData` fields are DEFINED from these, never stored directly. -/
structure ConstructiveCLD where
  /-- the continuum regions -/
  Region : Type
  /-- species / mode count -/
  N : ℝ
  /-- geometric area (the one genuinely-given datum) -/
  areaOf : Region → ℝ
  /-- the microscopic RECORD entropy value (DOS/record side — independent of the heat-kernel side) -/
  recEnt : Region → ℝ
  /-- the proper-time regulator functional `I` entering `S_ent` (heat-kernel side) -/
  entReg : ℝ
  /-- the regulator entering the induced `1/G` (Sakharov side) -/
  newtonReg : ℝ
  /-- scalar curvature `R` (for the `a₁` coefficient) -/
  curvR : ℝ
  /-- the supplied Seeley–DeWitt `a₁` coefficient -/
  a1coeff : ℝ
  /-- the Sakharov inverse Newton coefficient (independent expression) -/
  sakInvG : ℝ

namespace ConstructiveCLD

/-- micro entropy = the record-side value (NOT the heat-kernel side). -/
def microS (D : ConstructiveCLD) (R : D.Region) : ℝ := D.recEnt R

/-- one-loop conical entropy = the Susskind–Uglum `S_ent` from the heat-kernel side. -/
def loopS (D : ConstructiveCLD) (R : D.Region) : ℝ := Sent D.N (D.areaOf R) D.entReg

/-- induced Newton constant from the D3d `δ(1/G)`. -/
def GindV (D : ConstructiveCLD) : ℝ := Gind D.N D.entReg

/-- Sakharov induced Newton constant (independent). -/
def GsakV (D : ConstructiveCLD) : ℝ := (D.sakInvG)⁻¹

/-- Project the constructive data onto the opaque `ContinuumLimitData` the conjecture quantifies
    over. The four opaque fields are DEFINED here from the building blocks. -/
def toOpaque (D : ConstructiveCLD) : ContinuumLimitData where
  Region := D.Region
  microContinuumEntropy := D.microS
  oneLoopConicalEntropy := D.loopS
  area := D.areaOf
  Gind := D.GindV
  sakharovInducedNewtonConstant := D.GsakV

end ConstructiveCLD

/-- **THE PHYSICAL INPUTS (#3/#4/#5)** as labelled hypotheses over BUILDING BLOCKS ONLY — never the
    opaque `toOpaque` fields. This is the vacuity guard: the hypotheses relate independently-defined
    lower-level data, not the conjecture's output fields. -/
structure PhysicalInputs (D : ConstructiveCLD) : Prop where
  /-- #3 curved `a₁ = R/6` (minimal scalar): the supplied coefficient equals
      `scalarA1 0 (curvR) = R/6`. -/
  a1_eq_R_div_six : D.a1coeff = scalarA1 0 D.curvR
  /-- #5 cutoff identification `D_eff ~ 1/x`: the RECORD-side entropy equals the HEAT-KERNEL-side
      `S_ent` (the microscopic count from the DOS coincides with the one-loop conical entropy when
      the cutoffs are identified — a relation between two INDEPENDENTLY-defined blocks). -/
  cutoff_identifies : ∀ R, D.recEnt R = Sent D.N (D.areaOf R) D.entReg
  /-- #4 same-regulator: the induced-`1/G` regulator equals the `S_ent` regulator. -/
  same_regulator : D.newtonReg = D.entReg
  /-- the two induced Newton constants coincide (given #3+#4 the EH and Sakharov coefficients
      agree); stated at the inverse-coefficient building-block level. -/
  newton_matches : D.sakInvG = dInvG D.N D.entReg
  /-- nonzero guard for the area-law division. -/
  dInvG_ne : dInvG D.N D.entReg ≠ 0

/-- **★★ THE CONDITIONAL CORRESPONDENCE THEOREM.** Given the three cited physical inputs as
    hypotheses, the (constructed) continuum data satisfies the conjecture. NON-VACUOUS — the middle
    equality is DERIVED from D3d's proved `induced_product`; the hypotheses reference only building
    blocks. NOT a proof of the conjecture (its inputs stay assumed), but the ENTAILMENT is now
    machine-checked. -/
theorem flatSpaceCorrespondence_of_constructive
    (D : ConstructiveCLD) (h : PhysicalInputs D) :
    FlatSpaceRecordGravityCorrespondence D.toOpaque := by
  intro R
  refine ⟨?_, ?_, ?_⟩
  · -- micro = loop : from #5
    show D.microS R = D.loopS R
    simp only [ConstructiveCLD.microS, ConstructiveCLD.loopS]
    exact h.cutoff_identifies R
  · -- loop = area/(4·Gind) : DERIVED from D3d `induced_product` (the real content)
    show D.loopS R = D.toOpaque.area R / (4 * D.toOpaque.Gind)
    simp only [ConstructiveCLD.toOpaque, ConstructiveCLD.loopS, ConstructiveCLD.GindV]
    -- `induced_product`: 4 * Gind N entReg * Sent N (areaOf R) entReg = areaOf R.
    have hprod : 4 * Gind D.N D.entReg * Sent D.N (D.areaOf R) D.entReg = D.areaOf R :=
      induced_product D.N (D.areaOf R) D.entReg h.dInvG_ne
    -- `4 * Gind ≠ 0`, since Gind = (dInvG)⁻¹ and dInvG ≠ 0.
    have hGind : Gind D.N D.entReg ≠ 0 := by
      simp only [Gind]; exact inv_ne_zero h.dInvG_ne
    have hfour : (4 : ℝ) * Gind D.N D.entReg ≠ 0 :=
      mul_ne_zero (by norm_num) hGind
    -- From `(4*Gind) * Sent = area` conclude `Sent = area / (4*Gind)`.
    rw [eq_div_iff hfour]
    linear_combination hprod
  · -- Gind = Gsak : from #4 + newton_matches
    show D.toOpaque.Gind = D.toOpaque.sakharovInducedNewtonConstant
    simp only [ConstructiveCLD.toOpaque, ConstructiveCLD.GindV, ConstructiveCLD.GsakV]
    rw [Gind, h.newton_matches]

end QIQTH.CorrespondenceAssembly
