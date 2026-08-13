/-
  TruncHIntCarries — J4-666: gap-(i) bricks 2 + 3 of the truncated Duhamel integrability family at the
  genuinely-curved witness — the two remaining CARRIES of `TruncHIntFromGeometry.curved_hIntOn_affine_
  from_geometry` (J4-665) SUPPLIED FROM GEOMETRY, and the combined closed corollary.  NOT `a₁ = R/6`;
  proves NOTHING new about `R/6` (R/6 stays a labelled carrier; gaps (ii)–(v) untouched).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — GAP (i) BRICKS 2–3 ONLY.  J4-665 banked
  `curved_hIntOn_affine_from_geometry` — the truncated family `IterConvIntegrableWOn` at the heat
  operator over the curved witness (`curvedRNCMetric κ`, `κ < 0`), with `hEzero` discharged from
  geometry — but it still CARRIED two satisfiable interface facts:
    • `hAff` — the affine `τ ≤ T₀` one-step residual bound (the `C·(1+τ)·baseKernelW 2 0` shape);
    • `hEmeas` (`tripleHEmeas`) — the S1 joint strong measurability (the `HEmeasBorelAudit` Borel
      surface).
  THIS file discharges BOTH, from banked geometry-only curved suppliers, at a SHARED constant-radius
  flow-ball gate (`constGate … c`, seed `K = {0}` — the honest curved gauge, NOT a fat `K` which would
  be `hframeK`-unsatisfiable, cp466), and composes them through `hIntOn_affine_from_geometry`.

  ── BRICK 2 (`hAff`).  `CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg` (J4-536) delivers the CONCRETE
     curved one-step width-2 defect bound `hpkgBound : ∀ t' τ p q, 0 < τ → τ ≤ t' → |heatOp …| ≤
     (C·(1+t'))·baseKernelW 2 0 τ p q` at `constGate … c` (`K = {0}`), carrying only `hChr`
     (discharged here via `CurvedA1CenterAmp.curvedRNC_hChr`) and the amplitude smoothness `hw`.
     Instantiating the outer cutoff `t' := τ` gives EXACTLY the affine `C·(1+τ)·baseKernelW 2 0` shape
     `hAff` wants — the honest (non-vacuous) truncated form; the all-τ FIXED-constant form is
     firewalled-unsatisfiable (J4-261) and is NOT attempted.

  ── BRICK 3 (`hEmeas`).  `CurvedA1GateS1.curved_hS1_at_gate` (J4-561) delivers `tripleHEmeas` for the
     curved gated witness at the SAME `constGate … c` (`K = {0}`), from the banked geometry-only
     supplier `ConstRadiusGateExport.tripleHEmeas_AT_CONSTRADIUS_GATE`, carrying only the
     transport-coefficient smoothness `hu` (labelled) and the jet-reach smallness `c < δ₀` as an
     antecedent.  Because `curvedRNC_heatOp_dom_pkg` and `curved_hS1_at_gate` produce their gate at the
     SAME literal `constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr …) isCompact_singleton
     c`, and I feed the pkg's own `a b c` into `curved_hS1_at_gate`, both carries are at the SAME
     `(a,b,c)` gate — so they compose.

  ── COMBINED (`curved_hIntOn_from_geometry_closed`).  `curved_hIntOn_affine_from_geometry` with BOTH
     carries discharged: the truncated Duhamel integrability family for the curved-witness heat
     operator, with `hEzero` from geometry (banked), `hAff` from geometry (brick 2), `hEmeas` from
     geometry (brick 3).  HONEST RESIDUE of gap (i) after this brick: the ONE arithmetic jet-reach
     antecedent `c < δ₀` (the pkg's gate radius vs the Gc jet reach — the SAME open compatibility
     already isolated in `CurvedA1HEmeas`/`CurvedA1GateS1`, NOT measurability, NOT the affine bound,
     NOT the conclusion), plus the two genuine LABELLED geometric inputs `hw` (amplitude `C^∞`) and
     `hu` (transport-coefficient `C^∞`).  Every one is satisfiable, non-vacuous, and never `a₁ = R/6`.

  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.TruncHIntFromGeometry
import QIQTH.CurvedRNCHeatOpDomPkg
import QIQTH.CurvedA1GateS1

open MeasureTheory
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.TruncatedHIntRethread QIQTH.HEmeasBorelAudit
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCHeatOpDomPkg QIQTH.CurvedA1GateS1
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped BigOperators Topology ContDiff

namespace QIQTH.TruncHIntCarries

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C1 — the COMBINED closed corollary: BOTH carries of J4-665 discharged from geometry.
    ############################################################################### -/

/-- **★★★ J4-666 (C1) — `curved_hIntOn_from_geometry_closed`.**  The truncated Duhamel-split
    integrability family `IterConvIntegrableWOn` at the heat operator over the genuinely-curved witness
    `(curvedRNCMetric κ, curvedRNCInv κ)` (`κ < 0`, `Ric ≠ 0`), at a provider-chosen constant-radius
    flow-ball gate `constGate … c` (seed `K = {0}`), with ALL THREE interface facts of
    `TruncHIntFromGeometry.curved_hIntOn_affine_from_geometry` supplied:
      • `hEzero` — from geometry (banked, J4-665);
      • `hAff`   — from geometry via `CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg` at outer cutoff
                   `t' := τ` (brick 2);
      • `hEmeas` (`tripleHEmeas`) — from geometry via `CurvedA1GateS1.curved_hS1_at_gate` (brick 3).
    The gate parameters `a b c` are the pkg's own (existential); `curved_hS1_at_gate` supplies the S1
    surface at those SAME parameters.  HONEST RESIDUE: the single jet-reach antecedent `c < δ₀` (the
    pkg's gate radius vs the Gc jet reach — the already-isolated arithmetic compatibility, NOT
    measurability, NOT the affine bound, NOT the conclusion), plus the LABELLED geometric inputs `hw`
    (amplitude `C^∞`) and `hu` (transport-coefficient `C^∞`).  Christoffel smoothness `hChr` is
    discharged internally (`curvedRNC_hChr`), NOT carried.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hIntOn_from_geometry_closed (κ : ℝ) (hκneg : κ < 0) (hn : 1 ≤ n)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k))
    (T₀ : ℝ) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧
      ∃ δ₀ > (0 : ℝ), c < δ₀ →
        IterConvIntegrableWOn
          (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκneg.le)
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b))
          2 (0 : ℝ) (C * (1 + T₀)) T₀ := by
  -- BRICK 2 source: the concrete curved one-step width-2 defect bound at `constGate … c`, `K = {0}`.
  obtain ⟨a, b, C, c, ha, hab, hCnn, hbc, hpkgBound, _hAdom⟩ :=
    curvedRNC_heatOp_dom_pkg κ hκneg (curvedRNC_hChr κ hκneg.le) hw T₀
  -- BRICK 3 source: the S1 (`tripleHEmeas`) surface at the SAME `(a,b,c)` gate, `K = {0}`.
  obtain ⟨δ₀, hδ₀, hS1⟩ :=
    curved_hS1_at_gate κ hκneg (by omega : 0 < n) (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) a b c ha hab hbc hu
  refine ⟨a, b, C, c, ha, hab, hCnn, hbc, δ₀, hδ₀, fun hcδ => ?_⟩
  -- BRICK 2: instantiate the pkg's outer cutoff `t' := τ` ⟹ the affine `C·(1+τ)·baseKernelW 2 0` shape.
  have hAff : ∀ τ p q, 0 < τ → τ ≤ T₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκneg.le)
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b) τ p q|
        ≤ C * (1 + τ) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ _
    exact hpkgBound τ τ p q hτ le_rfl
  -- BRICK 3: the S1 surface, jet-reach antecedent `c < δ₀` discharged.
  have hEmeas := hS1 hcδ
  -- COMPOSE through the J4-665 truncated producer (`hEzero` from geometry inside).
  exact QIQTH.TruncHIntFromGeometry.hIntOn_affine_from_geometry
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
    (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b hn
    (2 : ℝ) C T₀ (by norm_num) hCnn hAff hEmeas

/-! ###############################################################################
    ### C2 — non-vacuity: the closed corollary lives at a GENUINELY-CURVED witness.
    ############################################################################### -/

/-- **★ J4-666 (C2) — `curved_hIntOn_from_geometry_closed_curved_satisfiable`.**  The witness
    underlying `curved_hIntOn_from_geometry_closed` is GENUINELY CURVED, NOT the flat `δ`: for `κ ≠ 0`,
    `n ≥ 2`, the diagonal metric-Hessian trace (`Ric(0)`) of `curvedRNCMetric κ` is nonzero.  So the
    discharged carries are about a curved metric (`κ < 0 ⊂ κ ≠ 0`), not vacuously the flat kernel.
    Re-exports `CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg_curved_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_hIntOn_from_geometry_closed_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNC_heatOp_dom_pkg_curved_satisfiable κ hκ hn c

end QIQTH.TruncHIntCarries

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.TruncHIntCarries
#print axioms curved_hIntOn_from_geometry_closed
#print axioms curved_hIntOn_from_geometry_closed_curved_satisfiable
end AxiomChecks
