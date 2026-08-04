/-
  ImageSupportDischarge — J4-230: the hImg AUDIT + the discharge of the image-support fact for the
  CONCRETE flow-ball gate, and the precisely-named residual surjectivity wall of the AMPLITUDE guard.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It banks the
  final chart-side plumbing fact `hImg` (the image-support supplier of
  `RightInverseGeneral.hWG_of_regional_support`) for the concrete flow-ball gate, and isolates — as an
  explicit, satisfiable hypothesis — the ONE genuinely-open geometric residue (the off-image
  surjectivity `‖W q p‖ < b ⟹ p ∈ φ_q '' closedBall 0 ρ`).  No `sorry` (prose excepted), no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypotheses.

  ── THE hImg AUDIT VERDICT (what the guard `P` of the four gate-equation reps actually IS).
  In `GatedChartMeasAudit.tripleHEmeas_concrete_v3` (and `RightInverseGeneral.a1_R6_assembled_v6`) the
  `hWG` conjunct of each supplier existential carries the AMPLITUDE-SUPPORT guard, NOT S-membership:
    * τ rep   : `chartFieldAmp … ≠ 0 ∨ Cfield … ≠ 0`;
    * field-1 : `chartFieldAmp … ≠ 0 ∨ pd chartFieldAmp k … ≠ 0`;
    * field-2 : `chartFieldAmp … ≠ 0 ∨ pd_i … ≠ 0 ∨ pd_j … ≠ 0 ∨ pd_i pd_j … ≠ 0`.
  `chartFieldAmp = radialCutoff a b (W z p) · (vanVleck-cofactor)` carries NO gate factor for `p ∈ S z`;
  the S-membership `w.2.1 ∈ S w.2.2` lives only in the SEPARATE `hgate` conjunct (and only under
  `0 < w.1`).  So S-membership is **ABSENT** from the guard and **NOT derivable** from it: the amplitude
  support gives only `‖W z p‖ < b` (`radialCutoff` support), and from there the passage to image
  membership `p ∈ φ_z '' closedBall 0 ρ` is the off-image SURJECTIVITY — the wall the
  `RightInverseGeneral` header names ("the banked chart exposes only the LEFT-inverse germ … off the
  flow image `W` is the partial-homeomorph `symm` on junk, so `W q p` may be small WITHOUT `p` being a
  `φ_q`-image").

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; `std-3`).
    * `norm_lt_of_chartFieldAmp_ne_zero` — the AMPLITUDE-SUPPORT half, banked unconditionally:
        `chartFieldAmp g gi hC hK a b τ z p ≠ 0 → ‖uniformInverseChart g gi hC hK z p‖ < b`
      (`0 < a < b`), via `radialCutoff_eq_zero` (support) + `norm_le_rncRadial` + `rncRadial`/`√`.

    * `hImg_gate_of_radii` — the S-MEMBERSHIP-GUARD image support, FULLY CLOSED (pure radii, NO wall):
        for the concrete gate `S z = φ_z '' Metric.ball 0 c` with `c ≤ ρ`, membership in the gate implies
        membership in the flow image over `closedBall 0 ρ` (`Set.image_subset` of
        `ball 0 c ⊆ closedBall 0 ρ`).

    * `hWG_gate_concrete` — ★★ THE FLAGSHIP: the GUARDED chart agreement for the S-MEMBERSHIP guard,
      FULLY DISCHARGED on the concrete flow-ball gate.  A uniform radius `ρ > 0` and a globally
      measurable `Gc` (both from the J4-227 regional flow-inverse, a THEOREM) with, for every ball
      radius `c ≤ ρ`,
          `∀ w, w.2.2 ∈ K → w.2.1 ∈ φ_(w.2.2) '' ball 0 c → uniformInverseChart … = Gc (w.2.2, w.2.1)`.
      NO surjectivity wall — the S-membership guard makes `hImg` pure radii.  This is EXACTLY the `hWG`
      shape the reps consume, **for the S-membership guard**; the remaining gap to
      `tripleHEmeas_concrete_v3` is that its reps' guard is the AMPLITUDE disjunction, so bridging needs
      the reps' `hWG` guard STRENGTHENED to the S-membership conjunct they already carry in `hgate`
      (an edit to `GatedChartMeasAudit` — the documented NEXT BRICK).

    * `hImg_chartFieldAmp_of_surjectivity` / `hWG_chartFieldAmp_of_surjectivity` — the AMPLITUDE route,
      closed MODULO the explicitly-named residue.  Carrying the off-image surjectivity `hSurj` (the ONE
      open geometric fact) as a satisfiable hypothesis, the amplitude-support guard `chartFieldAmp ≠ 0`
      yields `hImg` and hence the guarded agreement.  `hSurj` is geometrically true on the actual chart
      but NOT provable from the exposed germ — it is the honest carry, never the conclusion.

  ── HONEST REMAINING SURFACE (the definitive distance to `a1_R6_of_geometry`).
    (i)  the OFF-IMAGE SURJECTIVITY `hSurj` (amplitude support ⊆ flow image) — the ONE geometric wall;
    (ii) STRENGTHENING the four `GatedChartMeasAudit` reps' `hWG` guard from the amplitude disjunction to
         the S-membership conjunct (would make (i) unnecessary, replacing it with pure radii) — an edit
         to `GatedChartMeasAudit`, out of this file's no-edit scope;
    (iii) the over-strong `∀ w …` `hgate` carriers of `tripleHEmeas_concrete_v3` (they demand
         `w.2.1 ∈ S w.2.2` for ALL field points, not the ae/eventually COVERAGE geometry of
         `ConcreteGateAssembly`) — a separate downstream instantiation concern, orthogonal to `hImg`.
  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import QIQTH.RightInverseGeneral
import QIQTH.RNCDecay

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.RadialDistance QIQTH.RightInverseGeneral
open scoped Topology

namespace QIQTH.ImageSupportDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the AMPLITUDE-SUPPORT half: `chartFieldAmp ≠ 0 ⟹ ‖W z p‖ < b`.
    ############################################################################### -/

/-- **★ `norm_lt_of_chartFieldAmp_ne_zero` — the amplitude-support extraction.**  For `0 < a < b`, if
    the chart amplitude `chartFieldAmp g gi hC hK a b τ z p` is nonzero at `(τ, z, p)`, then the inverse
    chart value `W z p := uniformInverseChart g gi hC hK z p` lies strictly inside the far radius:
        `‖uniformInverseChart g gi hC hK z p‖ < b`.
    Proof: `chartFieldAmp = radialCutoff a b (W z p) · cofactor`, so `chartFieldAmp ≠ 0` forces
    `radialCutoff a b (W z p) ≠ 0`, hence (contrapositive of `radialCutoff_eq_zero`)
    `rncRadialSq (W z p) < b²`; then `‖W z p‖ ≤ rncRadial (W z p) = √(rncRadialSq (W z p)) < √(b²) = b`.
    This is the geometric content of the `chartFieldAmp ≠ 0` guard — the support half of `hImg`.
    NOT `a₁ = R/6`. -/
theorem norm_lt_of_chartFieldAmp_ne_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (τ : ℝ) (z p : Point n)
    (h : chartFieldAmp g gi hC hK a b τ z p ≠ 0) :
    ‖uniformInverseChart g gi hC hK z p‖ < b := by
  set v := uniformInverseChart g gi hC hK z p with hvdef
  -- the radial cutoff factor is nonzero.
  have hrc : radialCutoff a b v ≠ 0 := by
    intro h0
    exact h (by simp only [chartFieldAmp, ← hvdef, h0, zero_mul])
  -- hence `rncRadialSq v < b²` (contrapositive of `radialCutoff_eq_zero`).
  have hlt : rncRadialSq v < b ^ 2 := by
    by_contra hge
    exact hrc (radialCutoff_eq_zero ha hab (not_lt.mp hge))
  -- `‖v‖ ≤ rncRadial v = √(rncRadialSq v) < √(b²) = b`.
  have hbnn : (0 : ℝ) ≤ b := le_of_lt (lt_trans ha hab)
  have hrb : rncRadial v < b := by
    rw [rncRadial]
    have hsqrt : Real.sqrt (rncRadialSq v) < Real.sqrt (b ^ 2) :=
      Real.sqrt_lt_sqrt (rncRadialSq_nonneg v) hlt
    rwa [Real.sqrt_sq hbnn] at hsqrt
  exact lt_of_le_of_lt (QIQTH.RNCDecay.norm_le_rncRadial v) hrb

/-! ###############################################################################
    ### §2 — the S-MEMBERSHIP-GUARD image support (pure radii, FULLY CLOSED).
    ############################################################################### -/

/-- **★ `gateBall_subset_flowImage_closedBall` — pure radii.**  For `c ≤ ρ` the concrete flow-ball gate
    `φ_z '' Metric.ball 0 c` sits inside the flow image over the closed ball `φ_z '' closedBall 0 ρ`,
    by `Set.image_subset` of `Metric.ball 0 c ⊆ Metric.closedBall 0 ρ`.  NOT `a₁ = R/6`. -/
theorem gateBall_subset_flowImage_closedBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (c ρ : ℝ) (hc : c ≤ ρ) :
    uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c
      ⊆ uniformFlowExp g gi hC hK z '' Metric.closedBall (0 : Point n) ρ :=
  Set.image_mono
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hc))

/-- **★ `hImg_gate_of_radii` — the image-support supplier for the S-membership guard.**  With the
    concrete gate `S z = φ_z '' Metric.ball 0 c` and `c ≤ ρ`, wherever the S-membership guard
    `P w := w.2.1 ∈ S w.2.2` holds at `w` over the base gate, the field point lies in the flow image
    over `closedBall 0 ρ` — EXACTLY the `hImg` slot of `hWG_of_regional_support`, with NO surjectivity
    wall (pure radii).  NOT `a₁ = R/6`. -/
theorem hImg_gate_of_radii (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c ρ : ℝ) (hc : c ≤ ρ) :
    ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
      w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c →
      w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.closedBall (0 : Point n) ρ :=
  fun w _ hP => gateBall_subset_flowImage_closedBall g gi hC hK w.2.2 c ρ hc hP

/-- **★★ `hWG_gate_concrete` — THE FLAGSHIP: the guarded chart agreement for the S-membership guard,
    FULLY DISCHARGED on the concrete flow-ball gate.**  A uniform radius `ρ > 0` and a globally
    measurable joint representative `Gc` (both from the J4-227 regional flow-inverse
    `ChartRepConstruction.flowInverse_jointMeasurable_regional`, a THEOREM) such that for EVERY ball
    radius `c ≤ ρ`, on the concrete gate `S z = φ_z '' Metric.ball 0 c`,
        `∀ w, w.2.2 ∈ K → w.2.1 ∈ φ_(w.2.2) '' Metric.ball 0 c →
              uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1)`.
    This is the `hWG` conjunct shape of `GatedChartMeasAudit`'s supplier existentials **for the
    S-membership guard**, with `Gc` internal and `hImg` discharged by pure radii (`hImg_gate_of_radii`)
    — NO surjectivity wall.  Composes `RightInverseGeneral.hWG_concrete` and `hWG_of_regional_support`.
    NOT `a₁ = R/6`. -/
theorem hWG_gate_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∃ Gc : Point n × Point n → Point n, Measurable Gc ∧
      ∀ c : ℝ, c ≤ ρ →
        ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
          w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c →
          uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1) := by
  obtain ⟨ρ, hρ, Gc, hGmeas, hagree⟩ := hWG_concrete g gi hC hK
  refine ⟨ρ, hρ, Gc, hGmeas, ?_⟩
  intro c hc
  exact hWG_of_regional_support g gi hC hK ρ Gc hagree
    (fun w => w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c)
    (hImg_gate_of_radii g gi hC hK c ρ hc)

/-! ###############################################################################
    ### §3 — the AMPLITUDE route, closed MODULO the precisely-named surjectivity wall.
    ############################################################################### -/

/-- **★ `hImg_chartFieldAmp_of_surjectivity` — the amplitude `hImg`, modulo the named wall.**  GIVEN the
    off-image surjectivity `hSurj` (the ONE open geometric residue: amplitude support `‖W q p‖ < b`
    implies image membership `p ∈ φ_q '' closedBall 0 ρ`), the amplitude-support guard
    `chartFieldAmp … ≠ 0` supplies the `hImg` image-support slot of `hWG_of_regional_support`.  Reduces
    the guard to `‖W q p‖ < b` (`norm_lt_of_chartFieldAmp_ne_zero`) then applies `hSurj`.  `hSurj` is
    geometrically true on the actual chart but NOT provable from the exposed left-inverse germ — the
    honest carry, never the conclusion.  NOT `a₁ = R/6`. -/
theorem hImg_chartFieldAmp_of_surjectivity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) (ρ : ℝ)
    (hSurj : ∀ q ∈ K, ∀ p : Point n,
        ‖uniformInverseChart g gi hC hK q p‖ < b →
        p ∈ uniformFlowExp g gi hC hK q '' Metric.closedBall (0 : Point n) ρ) :
    ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
      chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0 →
      w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.closedBall (0 : Point n) ρ :=
  fun w hzK hamp =>
    hSurj w.2.2 hzK w.2.1
      (norm_lt_of_chartFieldAmp_ne_zero g gi hC hK a b ha hab w.1 w.2.2 w.2.1 hamp)

/-- **★★ `hWG_chartFieldAmp_of_surjectivity` — the guarded agreement for the AMPLITUDE guard, modulo the
    named wall.**  A uniform radius `ρ > 0` and a globally measurable `Gc` (J4-227) such that GIVEN the
    off-image surjectivity `hSurj` at that `ρ`, the amplitude-support guard `chartFieldAmp … ≠ 0` yields
    the guarded chart agreement `uniformInverseChart … = Gc (…)`.  This is the amplitude analogue of
    `hWG_gate_concrete` — closed EXCEPT for the single explicit geometric residue `hSurj` (the off-image
    surjectivity), which is satisfiable (true on the actual chart) but not banked.  Composes
    `hWG_concrete`, `hImg_chartFieldAmp_of_surjectivity`, and `hWG_of_regional_support`.
    NOT `a₁ = R/6`. -/
theorem hWG_chartFieldAmp_of_surjectivity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ρ > (0 : ℝ), ∃ Gc : Point n × Point n → Point n, Measurable Gc ∧
      ((∀ q ∈ K, ∀ p : Point n,
          ‖uniformInverseChart g gi hC hK q p‖ < b →
          p ∈ uniformFlowExp g gi hC hK q '' Metric.closedBall (0 : Point n) ρ) →
      ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0 →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1)) := by
  obtain ⟨ρ, hρ, Gc, hGmeas, hagree⟩ := hWG_concrete g gi hC hK
  refine ⟨ρ, hρ, Gc, hGmeas, ?_⟩
  intro hSurj
  exact hWG_of_regional_support g gi hC hK ρ Gc hagree
    (fun w => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0)
    (hImg_chartFieldAmp_of_surjectivity g gi hC hK a b ha hab ρ hSurj)

end QIQTH.ImageSupportDischarge

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ImageSupportDischarge
#print axioms norm_lt_of_chartFieldAmp_ne_zero
#print axioms gateBall_subset_flowImage_closedBall
#print axioms hImg_gate_of_radii
#print axioms hWG_gate_concrete
#print axioms hImg_chartFieldAmp_of_surjectivity
#print axioms hWG_chartFieldAmp_of_surjectivity
end AxiomChecks
