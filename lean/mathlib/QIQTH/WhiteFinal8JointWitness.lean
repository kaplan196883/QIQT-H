/-
  WhiteFinal8JointWitness — J4-721: THE cp466 JOINT INHABITATION AUDIT of
  `WhiteHsolveFlowContraction.white_hInnerCont_closed_final8`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` stays a
  labelled carrier, untouched).  It is a cp466 antecedent-inhabitance audit of `final8`: at the ONE
  concrete genuinely-curved configuration `n = 2`, `κ = −1`, `Kset = closedBall 0 2`, it EXHIBITS
  concrete witnesses (proved) for EVERY hypothesis of `final8` EXCEPT the two genuine residues, and
  produces `final8`'s real `ContinuousOn` conclusion.  No `sorry`, no `admit`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no existing file edited, nothing committed,
  nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE AUDIT VERDICT (the joint co-instantiation, plus the honest residue).
    Of `final8`'s hypotheses, the following CO-INSTANTIATE concretely at the shared gate radius `c`
    (`c := min(δp,δS,δV,δW,δchart,ρ₀)/2`, the six supplier / geometry radii) with `a = c/4`, `b = c/2`:
      • the whole A-group `{C,hC0,hpkg,hEmeas,hWmeas,wA,Cpre,A₀,A₁,hval}` — from the four banked
        suppliers (`white_hpkgBound_at_radius`, `white_tripleHEmeas_uniform`,
        `white_witness_value_dom_at_radius`, `white_witness_value_concrete_uniform`);
      • `hagree` — reflexivity with `Wg := whiteInvChart`;
      • `hSopen`, `hspec`, `hclosclause` — the germ / C² / open-image / compact-closure clauses of
        `UniformChartRadius.uniformInverseChart_huniformChart` (K-uniform, `0 < c < δchart`);
      • `hSreach` — reflexivity (the gate IS the flow-image ball);
      • `hdisp0` — the base-`0` quadratic near-isometry `ExpMap.uniformFlowExp_displacement_bound`;
      • `h0K`, `hcδ` — trivial.
    THE TWO GENUINE RESIDUES that are CARRIED (not exhibited):
      • `hflowData` — the recognized J3 base-varying-flow contraction blocker (the sole surviving
        analytic input of the whitened `hInnerCont` chain);
      • the REACH TRIPLE `{R, hballS, hballC, hbR}` — `closedBall 0 R ⊆ flowExpₓ_0 '' ball 0 c` has NO
        banked producer.  ⚠ THE cp466 COUPLING FINDING: the value supplier
        `white_witness_value_dom_at_radius` HARDCODES the collar `a = c/4`, `b = c/2`, so `b = c/2` is
        FORCED; then `hbR : b·(1 + C_D·c) < R` forces `R > c/2` (`white_final8_forcedCollar_reach_gt`),
        whereas the only banked reach machinery (the crude `uniformFlowExp_approximatesLinearOn`
        surjectivity, constant `c_lin < 1`) delivers only `R ≤ (1 − c_lin)·(c/2) < c/2`.  So the reach
        is NOT a contradiction (the sharp reach `R ≈ c·(1 − C_D·c) > c/2` is geometrically true for
        small `c`) but it is NOT dischargeable from the banked crude reach; a SHARP reach lemma
        (`R > c/2`) is the missing brick.  Hence `{R,hballS,hballC,hbR}` is carried honestly.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `white_final8_joint_witness` — ★★★ the conditional joint witness: at the concrete config there
      ARE `S,a,b,c,δ₀,C_D` with `0<a<b<c<δ₀`, `0≤C_D`, such that — GIVEN ONLY the carried reach triple
      `{R,hballS,hballC,hbR}` and the base-varying flow blocker `hflowData` — `final8`'s interior-time
      continuity of the whitened inner pairing holds on `Ioo 0 u`, ∀ `u ∈ (0,1]`.  Every OTHER
      hypothesis is discharged internally (proved).
    * `white_final8_forcedCollar_reach_gt` — the PROVED cp466 coupling certificate: with the
      value-supplier-forced collar `b = c/2`, `hbR` forces `c/2 < R`.
-/
import Mathlib
import QIQTH.WhiteHInnerContClosed
import QIQTH.WhiteHsolveFlowContraction

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteAnnulus
open QIQTH.WhiteS1C QIQTH.WhiteHInnerContFinal QIQTH.WhiteLeviConvergenceTrio
open QIQTH.WhiteHsolveFlowContraction
open scoped Topology ENNReal NNReal BigOperators

namespace QIQTH.WhiteFinal8JointWitness

/-! ### The concrete genuinely-curved configuration: `n = 2`, `κ = −1`, `K = closedBall 0 2`. -/

/-- The fat compact base set `K = closedBall 0 2` in `Point 2`. -/
noncomputable def Kfat : Set (Point 2) := Metric.closedBall 0 2

theorem hKfat : IsCompact Kfat := isCompact_closedBall 0 2

theorem hkm : (-1 : ℝ) ≤ 0 := by norm_num

theorem h0Kfat : (0 : Point 2) ∈ Kfat := Metric.mem_closedBall_self (by norm_num)

theorem hKfat_sub : Kfat ⊆ Metric.closedBall (0 : Point 2) 2 := Set.Subset.rfl

/-! ### §A — the PROVED cp466 coupling certificate. -/

/-- **★ `white_final8_forcedCollar_reach_gt` — the cp466 coupling certificate.**  The value supplier
`white_witness_value_dom_at_radius` hardcodes the collar `a = c/4`, `b = c/2`, so once `hval` is
discharged the collar `b = c/2` is FORCED.  With that forced collar the reach side-condition
`hbR : b·(1 + C_D·c) < R` forces `c/2 < R`.  This is the exact reason the crude banked reach
(`uniformFlowExp_approximatesLinearOn`, constant `c_lin < 1`, giving `R ≤ (1 − c_lin)·(c/2) < c/2`)
CANNOT discharge `hballC`, and the reach triple must be carried.  NOT `a₁ = R/6`. -/
theorem white_final8_forcedCollar_reach_gt (c C_D R : ℝ) (hc : 0 < c) (hCD : 0 ≤ C_D)
    (hbR : (c / 2) * (1 + C_D * c) < R) : c / 2 < R := by
  have hexp : (c / 2) * (1 + C_D * c) = c / 2 + (c / 2) * (C_D * c) := by ring
  have hnn : 0 ≤ (c / 2) * (C_D * c) := mul_nonneg (by linarith) (mul_nonneg hCD hc.le)
  linarith

/-! ### §B — ★★★ the conditional joint witness of `final8`. -/

set_option maxHeartbeats 1600000 in
/-- **★★★ `white_final8_joint_witness` — the cp466 conditional joint inhabitation of `final8`.**
At `n = 2`, `κ = −1`, `Kset = closedBall 0 2`, there ARE a flow-ball gate `S`, radii `a,b,c,δ₀` and a
near-isometry constant `C_D` with `0 < a < b < c < δ₀`, `0 ≤ C_D`, such that — GIVEN ONLY the carried
reach triple `{R,hballS,hballC,hbR}` and the base-varying flow blocker `hflowData` — the whitened
inner-pairing interior-time continuity of `final8` holds on `Ioo 0 u`, ∀ `u ∈ (0,1]`.  Every OTHER
hypothesis of `final8` (the whole A-group, `hagree`, `hSopen`, `hSreach`, `hspec`, `hclosclause`,
`hdisp0`, `h0K`, `hcδ`) is EXHIBITED (proved) internally, certifying their joint inhabitance at ONE
concrete configuration.  ⚠ NOT `a₁ = R/6`. -/
theorem white_final8_joint_witness :
    ∃ (S : Point 2 → Set (Point 2)) (a b c δ₀ C_D : ℝ),
      0 < a ∧ a < b ∧ b < c ∧ c < δ₀ ∧ 0 ≤ C_D ∧
      ∀ (R : ℝ)
        (_hballS : Metric.closedBall (0 : Point 2) R ⊆ S 0)
        (_hballC : Metric.closedBall (0 : Point 2) R ⊆
          uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
            (curvedRNC_hChr (-1) hkm) hKfat 0 '' Metric.ball (0 : Point 2) c)
        (_hbR : b * (1 + C_D * c) < R)
        (_hflowData : ∀ z₀ : Point 2, ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
          (∀ v ∈ Metric.sphere (0 : Point 2) c,
            ContractingWith Kc (fun w => z₀ -
              uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
                (curvedRNC_hChr (-1) hkm) hKfat w v + w)) ∧
          (∀ v ∈ Metric.sphere (0 : Point 2) c, ∀ v' ∈ Metric.sphere (0 : Point 2) c,
            ∀ w : Point 2,
              dist (uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
                    (curvedRNC_hChr (-1) hkm) hKfat w v)
                (uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
                    (curvedRNC_hChr (-1) hkm) hKfat w v')
                ≤ (Cv : ℝ) * dist v v') ∧
          {w : Point 2 | z₀ ∈ frontier (S w)} ⊆
            {w : Point 2 | ∃ v ∈ Metric.sphere (0 : Point 2) c,
              uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
                (curvedRNC_hChr (-1) hkm) hKfat w v = z₀}),
        ∀ u ∈ Set.Ioc (0 : ℝ) 1, ContinuousOn
          (fun s => ∫ z, whiteGatedWitness (-1) hkm hKfat S a b (u - s) 0 z
            * leviSeries (whiteDefectKernel (-1) hkm hKfat S a b) s z 0)
          (Set.Ioo 0 u) := by
  classical
  have hn : 0 < 2 := by norm_num
  -- REPLAY the A-group obtain-chain at the shared radius `c`.
  obtain ⟨δp, hδp, hpkgc⟩ := white_hpkgBound_at_radius (-1) hkm hKfat 2 hKfat_sub
  obtain ⟨δS, hδS, hS1⟩ := white_tripleHEmeas_uniform hn (-1) hkm hKfat
  obtain ⟨δV, hδVpos, wA, Cpre, A₀, A₁, hwA0, hCpre0, hA₀0, hA₁0, hvalc⟩ :=
    white_witness_value_dom_at_radius (-1) hkm hKfat 2 hKfat_sub
  obtain ⟨δW, hδWpos, hWc⟩ := white_witness_value_concrete_uniform (-1) hkm hKfat
  -- the geometry radii: chart (germ/C²/open/closure) and near-isometry.
  obtain ⟨δchart, hδchart0, hchartspec⟩ :=
    uniformInverseChart_huniformChart (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) hkm) hKfat
  obtain ⟨ρ₀, hρ₀0, C_D, hCD0, hdisp⟩ :=
    uniformFlowExp_displacement_bound (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) hkm) hKfat
  -- the shared gate radius `c` below all six radii.
  set m : ℝ := min δp (min δS (min δV (min δW (min δchart ρ₀)))) with hmdef
  have hm0 : 0 < m := by
    rw [hmdef]
    exact lt_min hδp (lt_min hδS (lt_min hδVpos (lt_min hδWpos (lt_min hδchart0 hρ₀0))))
  set c : ℝ := m / 2 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hmp : m ≤ δp := by rw [hmdef]; exact min_le_left _ _
  have hmS : m ≤ δS := by rw [hmdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hmV : m ≤ δV := by
    rw [hmdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmW : m ≤ δW := by
    rw [hmdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hmchart : m ≤ δchart := by
    rw [hmdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hmρ : m ≤ ρ₀ := by
    rw [hmdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hcp : c < δp := by rw [hcdef]; linarith
  have hcS : c < δS := by rw [hcdef]; linarith
  have hcV : c < δV := by rw [hcdef]; linarith
  have hcW : c < δW := by rw [hcdef]; linarith
  have hcchart : c < δchart := by rw [hcdef]; linarith
  have hcρ : c < ρ₀ := by rw [hcdef]; linarith
  have ha : 0 < c / 4 := by linarith
  have hab : c / 4 < c / 2 := by linarith
  have hbc : c / 2 < c := by linarith
  -- the flow-ball gate.
  set S : Point 2 → Set (Point 2) :=
    fun z => uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) hkm) hKfat z '' Metric.ball (0 : Point 2) c with hSdef
  -- co-emit the A-group at this shared gate.
  obtain ⟨hfat, C, hC0, hpkg⟩ := hpkgc c hc0 hcp (c / 4) (c / 2) ha hab hbc
  have hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (whiteGatedWitness (-1) hkm hKfat S (c / 4) (c / 2)) :=
    hS1 c hc0 hcS (c / 4) (c / 2) ha hab hbc
  have hWmeas : StronglyMeasurable (fun w : ℝ × Point 2 × Point 2 =>
      whiteGatedWitness (-1) hkm hKfat S (c / 4) (c / 2) w.1 w.2.1 w.2.2) :=
    hWc c hc0 hcW (c / 4) (c / 2)
  have hval : ∀ τ : ℝ, 0 < τ → ∀ p q : Point 2,
      |whiteGatedWitness (-1) hkm hKfat S (c / 4) (c / 2) τ p q|
        ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q) := hvalc c hc0 hcV
  -- the geometry B-group: reflexive agreement, open, reach-refl, germ+C², closure, displacement.
  set Wg : Point 2 × Point 2 → Point 2 := fun p => whiteInvChart (-1) hkm hKfat p.1 p.2 with hWgdef
  have hagree : ∀ w : ℝ × Point 2 × Point 2, w.2.2 ∈ Kfat → w.2.1 ∈ S w.2.2 →
      whiteInvChart (-1) hkm hKfat w.2.2 w.2.1 = Wg (w.2.2, w.2.1) := fun _ _ _ => rfl
  have hSopen : ∀ w : Point 2, w ∈ Kfat → IsOpen (S w) :=
    fun w hw => ((hchartspec w hw).2 c hc0 hcchart).1
  have hSreach : ∀ w : Point 2, w ∈ Kfat →
      S w ⊆ uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
        (curvedRNC_hChr (-1) hkm) hKfat w '' Metric.ball (0 : Point 2) c :=
    fun _ _ => Set.Subset.rfl
  have hspec : ∀ w : Point 2, w ∈ Kfat →
      (∀ v : Point 2, ‖v‖ < δchart →
        (fun z => uniformInverseChart (curvedRNCMetric (-1)) (curvedRNCInv (-1))
            (curvedRNC_hChr (-1) hkm) hKfat w (uniformFlowExp (curvedRNCMetric (-1))
              (curvedRNCInv (-1)) (curvedRNC_hChr (-1) hkm) hKfat w z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric (-1)) (curvedRNCInv (-1))
          (curvedRNC_hChr (-1) hkm) hKfat w)
          (uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
            (curvedRNC_hChr (-1) hkm) hKfat w v)) :=
    fun w hw => (hchartspec w hw).1
  have hclosclause : closure (uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
        (curvedRNC_hChr (-1) hkm) hKfat 0 '' Metric.ball 0 c)
      ⊆ uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
          (curvedRNC_hChr (-1) hkm) hKfat 0 '' Metric.closedBall 0 c :=
    ((hchartspec 0 h0Kfat).2 c hc0 hcchart).2
  have hdisp0 : ∀ v : Point 2, ‖v‖ ≤ c →
      ‖uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
          (curvedRNC_hChr (-1) hkm) hKfat 0 v - v‖ ≤ C_D * ‖v‖ * ‖v‖ := by
    intro v hv
    have h := hdisp 0 h0Kfat v (lt_of_le_of_lt hv hcρ)
    simpa [sub_zero] using h
  -- assemble the witness; carry the reach triple + the flow blocker.
  refine ⟨S, c / 4, c / 2, c, δchart, C_D, ha, hab, hbc, hcchart, hCD0, ?_⟩
  intro R hballS hballC hbR hflowData
  exact white_hInnerCont_closed_final8 hn (-1) hkm hKfat S (c / 4) (c / 2) ha hab
    C hC0 hpkg hEmeas hWmeas wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval
    Wg hagree c δchart hcchart hflowData hSopen hSreach hspec
    R h0Kfat hballS hballC C_D hCD0 hdisp0 hclosclause hbR (Set.Ioc 0 1)
    (fun u hu => hu.2)

end QIQTH.WhiteFinal8JointWitness

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteFinal8JointWitness
#check @white_final8_joint_witness
#check @white_final8_forcedCollar_reach_gt
#print axioms white_final8_joint_witness
#print axioms white_final8_forcedCollar_reach_gt
end AxiomChecks
