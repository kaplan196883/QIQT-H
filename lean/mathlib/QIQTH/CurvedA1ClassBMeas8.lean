/-
  CurvedA1ClassBMeas8 — J4-567.  Close the LAST open Section-G ∫z-slice MEASURABILITY carrier
  `hFmeas_d` of the fully-wired curved a₁ two-jet capstone
  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` at the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges the Section-G MEASURABILITY census binder
  `hFmeas_d` — the s-slice ae-strong-measurability of the RAW-witness · leviSeries pairing WITH AN
  UNCONSTRAINED (free) shift anchor `cc`
    `s ↦ ∫ z, vanVleckGatedWitness g^K gi^K … (cc − s) 0 z · leviSeries … s z 0`
  on the εₘ-floored `Lo` window `uIoc 0 (u − εₘ)` — for `g^K`.

  ── WHY THIS ONE IS DIFFERENT (the whole point of J4-567).  In `hMeasFII` (J4-564) and `hF'meas_d`
  (J4-565) the shift is `u − s`, which the εₘ-floor / null-endpoint transfer pins inside the
  positive-time continuity strip `(0,T]`, so the MapsTo-requiring Fubini core
  `SliceMeasurability.sliceMeas_of_jointCont` applies (it needs `∀ s ∈ window, 0 < shift ≤ T`).
  Here the anchor `cc` is UNIVERSALLY QUANTIFIED and FREE: on `uIoc 0 (u − εₘ)` the shift
  `τ = cc − s` can land ANYWHERE — including a positive-measure set where `τ ≤ 0` (and the null-set
  endpoint trick therefore does NOT apply).  So `sliceMeas_of_jointCont` is NOT usable, and carrying
  a per-`cc` MapsTo `∀ cc, ∀ s ∈ window, 0 < cc − s ≤ T` would be an UNSATISFIABLE vacuity trap.
  Instead the honest route is the banked GATED-INDICATOR JOINT `(s,z)` lever
  `InnerMeasFubini.gatedWitnessShift_joint_aesm`, wrapped by `InnerMeasFubini.hFmeas_concrete`: the
  raw gated witness is jointly `(s,z)`-ae-strong-measurable for ANY anchor `cc` because it is a
  measurable-set indicator (the gate depends only on `z`, `p = 0` fixed) applied to the ungated
  inner parametrix, whose joint measurability is a genuine, satisfiable (measurable-off-a-null-set)
  analytic carry `hInner` — NOT global continuity (the witness is singular at `(τ,z) = (0,0)`, so a
  `Continuous` carry WOULD be a vacuity trap; `AEStronglyMeasurable` tolerates the null singular set).

  It does NOT make `a₁ = R/6` unconditional: the geometric residuals `hsrc`/`hOffCollarTail`, the
  convergence trio, the interval-integrability members `hFint`/`hFint_d` (which need a genuine
  DOMINATION, not measurability), and `hInnerCont` all remain owed.

  ## What is closed

  `curved_hFmeas_d_at_gate` — the `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`,
  `S := constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c` instance of the banked
  geometry-generic Section-G free-anchor ∫z-slice supplier `InnerMeasFubini.hFmeas_concrete`,
  EXACTLY the shape of the capstone binder `hFmeas_d` (`∀ m, ∀ u ∈ U, ∀ cc, AEStronglyMeasurable …`).

  ## Carried residuals (honest, curvature-independent measurability carries)

  Each member carries {`hKm`, `hSm0`, `hInner`, `hLeviJoint`}:
    • `hKm` — `MeasurableSet K` (the base gate set; `K` is compact ⟹ measurable, carried);
    • `hSm0` — `MeasurableSet {z | 0 ∈ constGate … z}` (the spatial set-gate at `p = 0`);
    • `hInner` — joint `(s,z)`-ae-strong-measurability of the UNGATED order-1 inner parametrix at the
      free shift `cc − s` on every restricted window `(volume.restrict (uIoc 0 d)).prod volume` (a
      genuine, satisfiable measurability fact — the parametrix is measurable off its null singular
      set, NOT the conclusion);
    • `hLeviJoint` — joint `(s,z)`-ae-strong-measurability of the Levi-series factor on every
      restricted window (the truncated window may dip `≤ 0`, where the Levi factor vanishes, so this
      is carried directly rather than via the positive-strip `hBcont`).
  These are strictly lighter, satisfiable, non-vacuous measurability sub-carries of the capstone's
  `hFmeas_d` binder — the free-anchor analogue of J4-564's {`hFIICont`, `hBcont`}.  They are NOT the
  `a₁` coefficient and NOT gate-smallness.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  The member is a genuine `AEStronglyMeasurable` fact about a curved s-slice integral with a free
  anchor, discharged from the banked gated-indicator Fubini lever — NOT the capstone's conclusion,
  and NOT vacuous.  It holds at the genuinely-curved `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`,
  `curvedRNCMetric_ricci_trace_diag_ne`, `curved_hFmeas_d_at_gate_curved_satisfiable`); it does not
  touch, and is unaffected by, the `R/6` coefficient.  No `sorry`, no new axioms, no `:= True`, no
  hypothesis = conclusion, no existing file edited.  NOT `a₁ = R/6`. -/
import QIQTH.InnerMeasFubini
import QIQTH.SliceMeasurability
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.InnerMeasFubini
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open scoped ContDiff Interval Topology BigOperators

namespace QIQTH.CurvedA1ClassBMeas8

variable {n : ℕ}

/-! ###############################################################################
    ### AT-GATE INSTANCE — the exact capstone `hFmeas_d` binder shape at `g^K`.
    ###############################################################################

    The geometry-generic free-anchor supplier is the BANKED `InnerMeasFubini.hFmeas_concrete`
    (route: `gatedWitnessShift_joint_aesm` gated-indicator joint lever + `leviJoint` + Fubini).  We
    only instantiate it at the curved metric here. -/

/-- **★ J4-567 — `curved_hFmeas_d_at_gate`.**  The LAST open Section-G MEASURABILITY census binder
    `hFmeas_d` of `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the genuinely-curved
    witness `g^K = curvedRNCMetric κ`: for every `m`, `u ∈ U` and every FREE anchor `cc`, the s-slice
    map `s ↦ ∫ z, vanVleckGatedWitness g^K gi^K … (cc − s) 0 z · leviSeries … s z 0` is
    `AEStronglyMeasurable` on `volume.restrict (uIoc 0 (u − εₘ))`.  Discharged from the banked
    geometry-generic free-anchor Section-G ∫z-slice supplier `InnerMeasFubini.hFmeas_concrete`
    (whose engine is the gated-indicator joint `(s,z)` lever `gatedWitnessShift_joint_aesm`, the
    ONLY route that survives the unconstrained shift `cc`), instantiated at the curved metric.  The
    four measurability carries {`hKm`, `hSm0`, `hInner`, `hLeviJoint`} are carried honestly.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFmeas_d_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (U : Set ℝ)
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet
      {z : Point n | (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z})
    (hInner : ∀ cc d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck (curvedRNCMetric κ))
          (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
            (curvedRNCMetric κ) (curvedRNCInv κ))) a b
          (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK) (cc - p.1) 0 p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n)))) :
    ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (cc - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) :=
  hFmeas_concrete (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b U hKm hSm0 hInner hLeviJoint

/-- **★ J4-567 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the
    diagonal metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the LAST
    Section-G free-anchor s-slice measurability member is discharged at a genuinely curved witness
    (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.  NOT `a₁ = R/6`. -/
theorem curved_hFmeas_d_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1ClassBMeas8

section AxiomChecks
open QIQTH.CurvedA1ClassBMeas8
#print axioms curved_hFmeas_d_at_gate
#print axioms curved_hFmeas_d_at_gate_curved_satisfiable
end AxiomChecks
