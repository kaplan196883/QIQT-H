/-
  CurvedA1ClassBMeas4 — J4-563.  Close the W2 (differentiation-under-∫) MEASURABILITY carriers
  {`hFmeas`, `hF'meas`} of the fully-wired curved a₁ two-jet capstone
  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` at the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges TWO mechanical MEASURABILITY census
  binders of the W2 (differentiation-under-the-integral) family — the s-slice ae-strong-measurability
  of the `witnessFieldDeriv · leviSeries` pairing on the `Lo` window at an arbitrary field-slot shift
  `Function.update 0 i w` (`hFmeas`) and of the `witnessFieldDeriv2 · leviSeries` pairing on the `Lo`
  window at the field center `0` (`hF'meas`) — for `g^K`, from the banked geometry-generic s-slice
  Fubini core `SliceMeasurability.sliceMeas_of_jointCont` (J4-383).  It does NOT make `a₁ = R/6`
  unconditional: the geometric residuals `hsrc`/`hOffCollarTail`, the convergence trio, the
  interval-integrability member `hFint` (which needs a genuine DOMINATION, not measurability), the
  Section-G ∫z-slice family (`hMeasFII`/`hFmeas_d`/`hFint_d`/`hF'meas_d`), the leviSeries joint slices,
  and `hInnerCont` all remain owed.

  ## What is closed

  `hFmeas_slice`, `hFpmeas_slice` — the two geometry-generic s-slice W2 measurability suppliers (the
  `witnessFieldDeriv`/`witnessFieldDeriv2` analogues of `SliceMeasurability.hmeasLo_slice`), each a
  direct instantiation of the banked Fubini core `sliceMeas_of_jointCont` at the corresponding first
  factor.  `curved_hFmeas_at_gate`, `curved_hFpmeas_at_gate` — their `g := curvedRNCMetric κ`,
  `gi := curvedRNCInv κ`, `S := constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c` instances,
  exactly the shapes of the capstone binders `hFmeas`, `hF'meas`.

  ## Carried residuals (honest, curvature-independent analytic carries)

  Each member carries the four supplier carries {`hUT`, `hεU`, `hFieldCont`/`hField2Cont`, `hBcont`}:
    • `hUT`, `hεU` — the window bounds `u ≤ T`, `epsSeq m ≤ u` (satisfiable window bookkeeping);
    • `hFieldCont` — joint continuity of `(τ,z) ↦ witnessFieldDeriv g^K gi^K … i τ (update 0 i w) z`
      on the positive-time strip `Ioc 0 T ×ˢ univ`, per `i`, per `w`  (for `hFmeas`);
    • `hField2Cont` — joint continuity of `(τ,z) ↦ witnessFieldDeriv2 g^K gi^K … i τ 0 z` on the
      strip, per `i`  (for `hF'meas`);
    • `hBcont` — joint continuity of the Levi-series factor on the strip.
  These are genuine analytic facts about the curved witness on the positive-time strip, owed by the
  census and passed through here (not re-derived) — the exact measurability analogue of J4-562's
  carried {`hHeatCont`/`hSecCont`, `hBcont`}.  They are NOT the `a₁` coefficient and NOT gate-smallness.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  Each member is a genuine `AEStronglyMeasurable` fact about a curved s-slice integral, discharged from
  the banked Fubini core — NOT the capstone's conclusion, and NOT vacuous.  They hold at the
  genuinely-curved `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`, `curvedRNCMetric_ricci_trace_diag_ne`,
  `curved_hFmeas_at_gate_curved_satisfiable`); they do not touch, and are unaffected by, the `R/6`
  coefficient.  No `sorry`, no new axioms, no `:= True`, no hypothesis = conclusion, no existing file
  edited.  NOT `a₁ = R/6`. -/
import QIQTH.SliceMeasurability
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.EngineInstantiation

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.SliceMeasurability
open scoped ContDiff Interval Topology BigOperators

namespace QIQTH.CurvedA1ClassBMeas4

variable {n : ℕ}

/-! ###############################################################################
    ### GEOMETRY-GENERIC W2 SLICE SUPPLIERS — `witnessFieldDeriv`/`witnessFieldDeriv2` factors.
    ############################################################################### -/

/-- **★ `hFmeas_slice` — the geometry-generic W2 `hFmeas` supplier.**  s-slice
    ae-strong-measurability of the `witnessFieldDeriv · leviSeries` pairing at field slot
    `Function.update 0 i w` on the `Lo` window `uIoc 0 (u − εₘ)`, per `i`, per `w`.  On this window
    the shift `τ = u − s ∈ [εₘ, u) ⊆ (0,T]`, so the banked Fubini core `sliceMeas_of_jointCont`
    applies directly (the `witnessFieldDeriv` analogue of `hmeasLo_slice`).  Honest carries:
    {`hUT`, `hεU`, `hFieldCont`, `hBcont`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hFmeas_slice (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hFieldCont : ∀ (i : Fin n) (w : ℝ), ContinuousOn
      (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hChr hK S a b i p.1 (Function.update (0 : Point n) i w) p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m i u hu w
  have hεpos := epsSeq_pos m
  have hεu : epsSeq m ≤ u := hεU m u hu
  have huT : u ≤ T := hUT u hu
  have hIeq : Set.uIoc 0 (u - epsSeq m) = Set.Ioc 0 (u - epsSeq m) :=
    Set.uIoc_of_le (by linarith)
  rw [hIeq]
  have hmaps : ∀ s ∈ Set.Ioc (0 : ℝ) (u - epsSeq m), (0 : ℝ) < u - s ∧ u - s ≤ T := by
    intro s hs
    exact ⟨by linarith [hs.2, hεpos], by linarith [hs.1, huT]⟩
  have hsub : Set.Ioc (0 : ℝ) (u - epsSeq m) ⊆ Set.Ioc 0 T :=
    Set.Ioc_subset_Ioc_right (by linarith)
  exact sliceMeas_of_jointCont
    (fun τ z => witnessFieldDeriv g gi hChr hK S a b i τ (Function.update (0 : Point n) i w) z)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    T u (Set.Ioc 0 (u - epsSeq m)) measurableSet_Ioc hmaps hsub (hFieldCont i w) hBcont

/-- **★ `hFpmeas_slice` — the geometry-generic W2 `hF'meas` supplier.**  s-slice
    ae-strong-measurability of the `witnessFieldDeriv2 · leviSeries` pairing at the field center `0`
    on the `Lo` window `uIoc 0 (u − εₘ)`, per `i`.  Same `sliceMeas_of_jointCont` route, first factor
    replaced by the SECOND field-derivative kernel.  Honest carries: {`hUT`, `hεU`, `hField2Cont`,
    `hBcont`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hFpmeas_slice (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hField2Cont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        witnessFieldDeriv2 g gi hChr hK S a b i p.1 (0 : Point n) p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m i u hu
  have hεpos := epsSeq_pos m
  have hεu : epsSeq m ≤ u := hεU m u hu
  have huT : u ≤ T := hUT u hu
  have hIeq : Set.uIoc 0 (u - epsSeq m) = Set.Ioc 0 (u - epsSeq m) :=
    Set.uIoc_of_le (by linarith)
  rw [hIeq]
  have hmaps : ∀ s ∈ Set.Ioc (0 : ℝ) (u - epsSeq m), (0 : ℝ) < u - s ∧ u - s ≤ T := by
    intro s hs
    exact ⟨by linarith [hs.2, hεpos], by linarith [hs.1, huT]⟩
  have hsub : Set.Ioc (0 : ℝ) (u - epsSeq m) ⊆ Set.Ioc 0 T :=
    Set.Ioc_subset_Ioc_right (by linarith)
  exact sliceMeas_of_jointCont
    (fun τ z => witnessFieldDeriv2 g gi hChr hK S a b i τ (0 : Point n) z)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    T u (Set.Ioc 0 (u - epsSeq m)) measurableSet_Ioc hmaps hsub (hField2Cont i) hBcont

/-! ###############################################################################
    ### AT-GATE INSTANCES — the exact capstone `hFmeas`/`hF'meas` binder shapes at `g^K`.
    ############################################################################### -/

/-- **★ J4-563 — `curved_hFmeas_at_gate`.**  The W2 MEASURABILITY census binder `hFmeas` of
    `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the genuinely-curved witness
    `g^K = curvedRNCMetric κ`: for every `m`, `i`, `u ∈ U` and `w`, the s-slice map
    `s ↦ ∫ z, witnessFieldDeriv g^K gi^K … i (u−s) (update 0 i w) z · leviSeries … s z 0` is
    `AEStronglyMeasurable` on `volume.restrict (uIoc 0 (u − εₘ))`.  Discharged from the banked
    geometry-generic W2 slice supplier `hFmeas_slice`, instantiated at the curved metric.  The four
    supplier carries {`hUT`, `hεU`, `hFieldCont`, `hBcont`} are carried honestly.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFmeas_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c T : ℝ) (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hFieldCont : ∀ (i : Fin n) (w : ℝ), ContinuousOn
      (fun p : ℝ × Point n =>
        witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i p.1
          (Function.update (0 : Point n) i w) p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) :=
  hFmeas_slice (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUT hεU hFieldCont hBcont

/-- **★ J4-563 — `curved_hFpmeas_at_gate`.**  The W2 MEASURABILITY census binder `hF'meas` of
    `curved_a1_R6_fully_wired`, at `g^K = curvedRNCMetric κ`: for every `m`, `i`, `u ∈ U`, the
    s-slice map `s ↦ ∫ z, witnessFieldDeriv2 g^K gi^K … i (u−s) 0 z · leviSeries … s z 0` is
    `AEStronglyMeasurable` on `volume.restrict (uIoc 0 (u − εₘ))`.  Discharged from
    `hFpmeas_slice` instantiated at the curved metric.  Carries {`hUT`, `hεU`, `hField2Cont`,
    `hBcont`} honestly (the per-`i` second field-derivative continuity replaces `hFieldCont`).
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFpmeas_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c T : ℝ) (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hField2Cont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        witnessFieldDeriv2 (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i p.1 (0 : Point n) p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
              (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) :=
  hFpmeas_slice (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUT hεU hField2Cont hBcont

/-- **★ J4-563 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the two W2 s-slice
    measurability members are discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat
    `δ`.  NOT `a₁ = R/6`. -/
theorem curved_hFmeas_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1ClassBMeas4

section AxiomChecks
open QIQTH.CurvedA1ClassBMeas4
#print axioms hFmeas_slice
#print axioms hFpmeas_slice
#print axioms curved_hFmeas_at_gate
#print axioms curved_hFpmeas_at_gate
#print axioms curved_hFmeas_at_gate_curved_satisfiable
end AxiomChecks
