/-
  WhiteHsolveFlowContraction — J4-720: the BANACH-FIXED-POINT SOLVER for the flow-gate
  null-frontier certificate `hsolveFlow`, plus the honest reduction of the SOLE surviving
  analytic residual of the whitened `hInnerCont` chain to ONE named base-varying-contraction input.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` stays a
  labelled carrier, untouched).  It targets the sole surviving analytic residual of
  `WhiteHnullFlowReduction.white_hInnerCont_closed_final7`, namely the Lipschitz-solvability
  certificate `hsolveFlow`, and reduces it — via a FULLY PROVEN Banach-fixed-point construction — to
  the honest base-varying-flow contraction data `hflowData`.  No `sorry`, no `admit`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no existing file edited, nothing committed,
  nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE W-REGULARITY VERDICT (scoping result, J4-720).
    The base-varying regularity of `w ↦ flowExp_w v` needed by the solver is NOT banked.  The banked
    base-point facts are all POINTWISE-at-the-centre first-order data:
      * `BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center` — `fderiv (Wbv) 0 = -id` for the
        base-slot INVERSE chart `Wbv z = uniformInverseChart … z 0`, from the base-`0` displacement bank;
      * `BasepointFDeriv.geodesicBasepoint_endpoint_hasFDerivAt_exists` — the base-point FIRST-order
        Fréchet derivative of the geodesic-flow endpoint AT the centre, with quadratic remainder;
      * `BaseVaryingIFTPackage.baseVaryingIFTPackage` — the full change-of-variables bundle, but only
        CONDITIONAL on the un-banked base-slot `C²` input `hbaseC2` (the recognized "J3 blocker").
    A UNIFORM-over-base-`w` Lipschitz-in-`w` bound with constant `< 1` on `w ↦ flowExp_w v − w` — the
    hypothesis the contraction-mapping solver needs — is exactly that missing base-varying regularity;
    it is neither banked nor cheaply derivable from the pointwise-at-centre data.  Per the sanctioned
    fallback we therefore BANK THE HONEST REDUCTION: the contraction data is carried as one named input
    `hflowData`, and everything downstream of it is PROVEN.

  ── WHAT IS FULLY PROVEN HERE (no residual, std-3 axioms).
    * `hsolveFlow_of_contractionData` — ★★ THE SOLVER.  For a flow family `Ψ : base → dir → point`,
      from the per-`z₀` contraction data (a uniform contraction constant `Kc < 1` making
      `w ↦ z₀ − Ψ w v + w` `ContractingWith Kc` for each sphere direction `v`, a uniform Lipschitz-in-`v`
      modulus `Cv`, and the frontier→sphere-image containment), the Lipschitz-solvability certificate
      `hsolveFlow` FOLLOWS.  `H v := ContractingWith.fixedPoint (w ↦ z₀ − Ψ w v + w)` solves
      `Ψ (H v) v = z₀`; `ContractingWith.fixedPoint_lipschitz_in_map` gives `H` Lipschitz on the sphere
      with constant `Cv / (1 − Kc)`; fixed-point uniqueness lands the bad base set in `H '' sphere`.
    * `white_hInnerCont_closed_final8` — ★★★ `final7` with the `hsolveFlow` residual REPLACED by the
      base-varying-contraction data `hflowData`; `hsolveFlow` is discharged internally by the solver.
      ZERO analytic residuals beyond the single honest `hflowData` input.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteHnullFlowReduction

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteAnnulus
open QIQTH.WhiteHJetCont QIQTH.WhiteHBaseExtend
open QIQTH.WhiteHInnerContLegADischarged
open QIQTH.WhiteHBaseGateCollarDischarge
open QIQTH.WhiteHnullFlowReduction
open scoped Topology ENNReal NNReal

namespace QIQTH.WhiteHsolveFlowContraction

variable {n : ℕ}

/-! ### §A — the Banach-fixed-point solver: `hsolveFlow` from base-varying contraction data. -/

/-- **★★ THE SOLVER.**  For any flow family `Ψ : Point n → Point n → Point n` (`Ψ w v` = the flow
image at base `w` in direction `v`) and gate family `S`, if for every observation point `z₀` there is
base-varying contraction data — a uniform constant `Kc < 1` making `w ↦ z₀ − Ψ w v + w`
`ContractingWith Kc` for each sphere direction `v`, a uniform Lipschitz-in-`v` modulus `Cv`, and the
frontier→sphere-image containment `{w | z₀ ∈ frontier (S w)} ⊆ {w | ∃ v ∈ sphere 0 c, Ψ w v = z₀}` —
then the Lipschitz-solvability certificate `hsolveFlow` holds.

Construction: `H v := ContractingWith.fixedPoint (fun w => z₀ − Ψ w v + w)`.  Its fixed-point equation
`z₀ − Ψ (H v) v + H v = H v` gives `Ψ (H v) v = z₀` (the SOLVER).  `fixedPoint_lipschitz_in_map`
(with `dist (Φ_v z) (Φ_{v'} z) = dist (Ψ z v) (Ψ z v') ≤ Cv · dist v v'`) makes `H` Lipschitz on the
sphere with constant `Cv / (1 − Kc)`.  For a bad base `w` (`∃ v ∈ sphere, Ψ w v = z₀`) the point `w`
is itself a fixed point of `Φ_v`, so `w = H v` by uniqueness — landing the bad set inside
`H '' sphere`.  FULLY PROVEN; no residual.  ⚠ NOT `a₁ = R/6`. -/
theorem hsolveFlow_of_contractionData {S : Point n → Set (Point n)} {c : ℝ}
    (Ψ : Point n → Point n → Point n)
    (hdata : ∀ z₀ : Point n, ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
        (∀ v ∈ Metric.sphere (0 : Point n) c,
          ContractingWith Kc (fun w => z₀ - Ψ w v + w)) ∧
        (∀ v ∈ Metric.sphere (0 : Point n) c, ∀ v' ∈ Metric.sphere (0 : Point n) c,
          ∀ w : Point n, dist (Ψ w v) (Ψ w v') ≤ (Cv : ℝ) * dist v v') ∧
        {w : Point n | z₀ ∈ frontier (S w)} ⊆
          {w : Point n | ∃ v ∈ Metric.sphere (0 : Point n) c, Ψ w v = z₀}) :
    ∀ z₀ : Point n, ∃ (H : Point n → Point n) (K : ℝ≥0),
        LipschitzOnWith K H (Metric.sphere 0 c) ∧
        {w : Point n | z₀ ∈ frontier (S w)} ⊆ H '' Metric.sphere (0 : Point n) c := by
  classical
  intro z₀
  obtain ⟨Kc, Cv, hKc1, hcontr, hvlip, hfront⟩ := hdata z₀
  set Φ : Point n → Point n → Point n := fun v w => z₀ - Ψ w v + w with hΦdef
  -- The total solver map: fixed point on the sphere, default `z₀` off it.
  set H : Point n → Point n := fun v =>
    if h : v ∈ Metric.sphere (0 : Point n) c then
      ContractingWith.fixedPoint (Φ v) (hcontr v h)
    else z₀ with hHdef
  -- The one-subtract-Kc positivity.
  have honesub : (0 : ℝ) < 1 - (Kc : ℝ) := by
    have hlt : (Kc : ℝ) < 1 := by exact_mod_cast hKc1
    linarith
  refine ⟨H, Cv / (1 - Kc), ?_, ?_⟩
  · -- Lipschitz on the sphere via `fixedPoint_lipschitz_in_map`.
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hHx : H x = ContractingWith.fixedPoint (Φ x) (hcontr x hx) := dif_pos hx
    have hHy : H y = ContractingWith.fixedPoint (Φ y) (hcontr y hy) := dif_pos hy
    -- uniform closeness of the two contraction maps.
    have hclose : ∀ z : Point n, dist (Φ x z) (Φ y z) ≤ (Cv : ℝ) * dist x y := by
      intro z
      have heq : dist (Φ x z) (Φ y z) = dist (Ψ z x) (Ψ z y) := by
        simp only [hΦdef]
        have hsub : (z₀ - Ψ z x + z) - (z₀ - Ψ z y + z) = Ψ z y - Ψ z x := by abel
        rw [dist_eq_norm, hsub, ← dist_eq_norm, dist_comm]
      rw [heq]; exact hvlip x hx y hy z
    have hdist := (hcontr x hx).fixedPoint_lipschitz_in_map (hcontr y hy) hclose
    rw [← hHx, ← hHy] at hdist
    -- rewrite the real constant `Cv/(1-Kc)` as the NNReal coercion.
    have hcoe : ((Cv / (1 - Kc) : ℝ≥0) : ℝ) = (Cv : ℝ) / (1 - (Kc : ℝ)) := by
      rw [NNReal.coe_div, NNReal.coe_sub hKc1.le, NNReal.coe_one]
    rw [hcoe]
    calc dist (H x) (H y)
        ≤ (Cv : ℝ) * dist x y / (1 - (Kc : ℝ)) := hdist
      _ = (Cv : ℝ) / (1 - (Kc : ℝ)) * dist x y := by ring
  · -- Containment: each bad base `w` is a fixed point, hence in `H '' sphere`.
    intro w hw
    obtain ⟨v, hv, hΨeq⟩ := hfront hw
    -- `w` is a fixed point of `Φ v`.
    have hfpw : Function.IsFixedPt (Φ v) w := by
      show z₀ - Ψ w v + w = w
      rw [hΨeq]; abel
    -- hence `w` equals the unique fixed point `H v`.
    have huniq : w = ContractingWith.fixedPoint (Φ v) (hcontr v hv) :=
      (hcontr v hv).fixedPoint_unique hfpw
    have hHvw : H v = w := by rw [hHdef]; simp only [dif_pos hv]; rw [← huniq]
    exact ⟨v, hv, hHvw⟩

end QIQTH.WhiteHsolveFlowContraction

/-! ### §B — the terminal feed: `final7` with `hsolveFlow` replaced by the contraction data. -/

namespace QIQTH.WhiteHsolveFlowContraction

open QIQTH.WhiteHnullFlowReduction

/-- **★★★ `white_hInnerCont_closed_final8` (THE TERMINAL FEED, `hsolveFlow` DISSOLVED).**  Identical
conclusion and hypotheses to `WhiteHnullFlowReduction.white_hInnerCont_closed_final7`, except the
Lipschitz-solvability residual `hsolveFlow` is REPLACED by the base-varying-flow contraction data
`hflowData`: for each `z₀`, a uniform contraction constant `Kc < 1` making
`w ↦ z₀ − flowExp_w v + w` `ContractingWith Kc` for each sphere direction `v`, a uniform
Lipschitz-in-`v` modulus `Cv`, and the frontier→sphere-image containment.  `hsolveFlow` is discharged
internally by `hsolveFlow_of_contractionData` (fully proven Banach fixed point).  This is the honest
single-input reduction: the base-varying flow regularity is carried as `hflowData` (see the file's
w-regularity verdict), everything downstream is PROVEN.  ⚠ NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final8 (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW (whiteLam κ hκ hKc) 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    (hWmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      whiteGatedWitness κ hκ hKc S a b w.1 w.2.1 w.2.2))
    (wA Cpre A₀ A₁ : ℝ) (hwA0 : 0 < wA) (hCpre0 : 0 ≤ Cpre) (hA₀0 : 0 ≤ A₀) (hA₁0 : 0 ≤ A₁)
    (hval : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |whiteGatedWitness κ hκ hKc S a b τ p q|
        ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q))
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (c δ₀ : ℝ) (hcδ : c < δ₀)
    -- B''. the BASE-VARYING-FLOW CONTRACTION data (replaces the `hsolveFlow` residual)
    (hflowData : ∀ z₀ : Point n, ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
        (∀ v ∈ Metric.sphere (0 : Point n) c,
          ContractingWith Kc (fun w => z₀ -
            uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v + w)) ∧
        (∀ v ∈ Metric.sphere (0 : Point n) c, ∀ v' ∈ Metric.sphere (0 : Point n) c,
          ∀ w : Point n,
            dist (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v)
              (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v')
              ≤ (Cv : ℝ) * dist v v') ∧
        {w : Point n | z₀ ∈ frontier (S w)} ⊆
          {w : Point n | ∃ v ∈ Metric.sphere (0 : Point n) c,
            uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v = z₀})
    (hSopen : ∀ w : Point n, w ∈ Kset → IsOpen (S w))
    (hSreach : ∀ w : Point n, w ∈ Kset →
        S w ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w ''
          Metric.ball (0 : Point n) c)
    (hspec : ∀ w : Point n, w ∈ Kset →
        (∀ v : Point n, ‖v‖ < δ₀ →
          (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc w z)) =ᶠ[nhds v] (fun z => z) ∧
          ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w)
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v)))
    (R : ℝ) (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    (C_D : ℝ) (hCD0 : 0 ≤ C_D)
    (hdisp0 : ∀ v : Point n, ‖v‖ ≤ c →
        ‖uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v - v‖
          ≤ C_D * ‖v‖ * ‖v‖)
    (hclosclause : closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc 0 '' Metric.ball 0 c)
      ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.closedBall 0 c)
    (hbR : b * (1 + C_D * c) < R)
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) :=
  white_hInnerCont_closed_final7 hn κ hκ hKc S a b ha hab C hC0 hpkg hEmeas hWmeas
    wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval Wg hagree c δ₀ hcδ
    (hsolveFlow_of_contractionData
      (S := S) (c := c)
      (fun w v => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v)
      hflowData)
    hSopen hSreach hspec R h0K hballS hballC C_D hCD0 hdisp0 hclosclause hbR Uwin hU1

end QIQTH.WhiteHsolveFlowContraction

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHsolveFlowContraction
#check @hsolveFlow_of_contractionData
#check @white_hInnerCont_closed_final8
#print axioms hsolveFlow_of_contractionData
#print axioms white_hInnerCont_closed_final8
end AxiomChecks
