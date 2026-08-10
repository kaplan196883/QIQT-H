/-
  CurvedA1ClassBMeas5 — J4-564.  Close the Section-G error-kernel ∫z-slice MEASURABILITY carrier
  `hMeasFII` of the fully-wired curved a₁ two-jet capstone
  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` at the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges the Section-G MEASURABILITY census binder
  `hMeasFII` — the s-slice ae-strong-measurability of the RAW-witness · leviSeries pairing
  `s ↦ ∫ z, vanVleckGatedWitness g^K gi^K … (u−s) 0 z · leviSeries … s z 0` on the FULL error-kernel
  window `uIoc 0 u` — for `g^K`, from the banked geometry-generic s-slice Fubini core
  `SliceMeasurability.sliceMeas_of_jointCont` (J4-383).  The first factor here is the RAW gated
  witness `vanVleckGatedWitness … τ 0 z` (the error-kernel numerator), NOT the `heatOp`-transported
  `heatOp g gi (vanVleckGatedWitness …) τ 0 z` of `hmeasLo`/`hmeasHi` (J4-562), and the window is the
  full `uIoc 0 u` (no `εₘ` floor) whose single null endpoint `s = u` is handled by the same
  `Ioo → Ioc` transfer as `hmeasHi_slice`.  It does NOT make `a₁ = R/6` unconditional: the geometric
  residuals `hsrc`/`hOffCollarTail`, the convergence trio, the interval-integrability members
  `hFint`/`hFint_d` (which need a genuine DOMINATION, not measurability), the remaining Section-G
  ∫z-slice carriers (`hFmeas_d` with its unconstrained shift `cc`, `hF'meas_d` with its `deriv`
  first factor), the leviSeries joint slices (`hffro_meas`/`hfmov_meas`), and `hInnerCont` all remain
  owed.

  ## What is closed

  `hMeasFII_slice` — the geometry-generic Section-G ∫z-slice measurability supplier (the RAW-witness
  analogue of `SliceMeasurability.hmeasHi_slice`), a direct instantiation of the banked Fubini core
  `sliceMeas_of_jointCont` at the raw-witness first factor on the OPEN window `Ioo 0 u`, transferred to
  `uIoc 0 u` by `restrict_congr_set` (the null endpoint `s = u` is `volume`-null).
  `curved_hMeasFII_at_gate` — its `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`,
  `S := constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c` instance, exactly the shape of the
  capstone binder `hMeasFII`.

  ## Carried residuals (honest, curvature-independent analytic carries)

  Each member carries {`hUT`, `hU0`, `hFIICont`, `hBcont`}:
    • `hUT`, `hU0` — the window bounds `u ≤ T`, `0 ≤ u` (satisfiable window bookkeeping; `hU0` is the
      floor discharged at the wiring site from the capstone's `hUfloor`);
    • `hFIICont` — joint continuity of `(τ,z) ↦ vanVleckGatedWitness g^K gi^K … τ 0 z` on the
      positive-time strip `Ioc 0 T ×ˢ univ`  (the raw error-kernel numerator);
    • `hBcont` — joint continuity of the Levi-series factor on the strip.
  These are genuine analytic facts about the curved witness on the positive-time strip, owed by the
  census and passed through here (not re-derived) — the exact measurability analogue of J4-562's
  carried {`hHeatCont`/`hSecCont`, `hBcont`}.  They are NOT the `a₁` coefficient and NOT gate-smallness.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  The member is a genuine `AEStronglyMeasurable` fact about a curved s-slice integral, discharged from
  the banked Fubini core — NOT the capstone's conclusion, and NOT vacuous.  It holds at the
  genuinely-curved `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`, `curvedRNCMetric_ricci_trace_diag_ne`,
  `curved_hMeasFII_at_gate_curved_satisfiable`); it does not touch, and is unaffected by, the `R/6`
  coefficient.  No `sorry`, no new axioms, no `:= True`, no hypothesis = conclusion, no existing file
  edited.  NOT `a₁ = R/6`. -/
import QIQTH.SliceMeasurability
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.SliceMeasurability
open scoped ContDiff Interval Topology BigOperators

namespace QIQTH.CurvedA1ClassBMeas5

variable {n : ℕ}

/-! ###############################################################################
    ### GEOMETRY-GENERIC SECTION-G SLICE SUPPLIER — RAW-witness · leviSeries factor.
    ############################################################################### -/

/-- **★ `hMeasFII_slice` — the geometry-generic Section-G `hMeasFII` supplier.**  s-slice
    ae-strong-measurability of the RAW-witness · leviSeries pairing
    `s ↦ ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u−s) 0 z · leviSeries … s z 0` on the FULL
    error-kernel window `uIoc 0 u`.  The shift `τ = u − s` hits `0` at the single null endpoint
    `s = u`; we prove the fact on the OPEN window `Ioo 0 u` (where `τ ∈ (0, u) ⊆ (0,T]`) via the banked
    Fubini core `sliceMeas_of_jointCont`, then transfer to `uIoc 0 u` by `restrict_congr_set` (the RAW
    error-kernel analogue of `hmeasHi_slice`).  Honest carries: {`hUT`, `hU0`, `hFIICont`, `hBcont`}.
    ⚠ NOT `a₁ = R/6`. -/
theorem hMeasFII_slice (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hU0 : ∀ u ∈ U, 0 ≤ u)
    (hFIICont : ContinuousOn
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hChr hK S a b p.1 0 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 u)) := by
  intro u hu
  have huT : u ≤ T := hUT u hu
  have hu0 : 0 ≤ u := hU0 u hu
  have hmaps : ∀ s ∈ Set.Ioo (0 : ℝ) u, (0 : ℝ) < u - s ∧ u - s ≤ T := by
    intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1, huT]⟩
  have hsub : Set.Ioo (0 : ℝ) u ⊆ Set.Ioc 0 T := by
    intro s hs
    exact ⟨hs.1, by linarith [hs.2, huT]⟩
  have key := sliceMeas_of_jointCont
    (fun τ z => vanVleckGatedWitness g gi hChr hK S a b τ 0 z)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    T u (Set.Ioo 0 u) measurableSet_Ioo hmaps hsub hFIICont hBcont
  have hmeq : (volume : Measure ℝ).restrict (Set.uIoc 0 u)
      = (volume : Measure ℝ).restrict (Set.Ioo 0 u) := by
    rw [Set.uIoc_of_le hu0]
    exact (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  rw [hmeq]
  exact key

/-! ###############################################################################
    ### AT-GATE INSTANCE — the exact capstone `hMeasFII` binder shape at `g^K`.
    ############################################################################### -/

/-- **★ J4-564 — `curved_hMeasFII_at_gate`.**  The Section-G MEASURABILITY census binder `hMeasFII`
    of `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the genuinely-curved witness
    `g^K = curvedRNCMetric κ`: for every `u ∈ U`, the s-slice map
    `s ↦ ∫ z, vanVleckGatedWitness g^K gi^K … (u−s) 0 z · leviSeries … s z 0` is
    `AEStronglyMeasurable` on `volume.restrict (uIoc 0 u)`.  Discharged from the banked geometry-generic
    Section-G slice supplier `hMeasFII_slice`, instantiated at the curved metric.  The four supplier
    carries {`hUT`, `hU0`, `hFIICont`, `hBcont`} are carried honestly.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hMeasFII_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c T : ℝ) (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hU0 : ∀ u ∈ U, 0 ≤ u)
    (hFIICont : ContinuousOn
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b p.1 0 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 u)) :=
  hMeasFII_slice (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUT hU0 hFIICont hBcont

/-- **★ J4-564 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the Section-G s-slice
    measurability member is discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat
    `δ`.  NOT `a₁ = R/6`. -/
theorem curved_hMeasFII_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1ClassBMeas5

section AxiomChecks
open QIQTH.CurvedA1ClassBMeas5
#print axioms hMeasFII_slice
#print axioms curved_hMeasFII_at_gate
#print axioms curved_hMeasFII_at_gate_curved_satisfiable
end AxiomChecks
