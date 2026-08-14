/-
  WhiteFinal8SharpWitness — J4-722: THE REACH TRIPLE DISCHARGED, witness carrying ONLY `hflowData`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` stays a
  labelled carrier, untouched).  It STRENGTHENS the J4-721 joint witness of `final8` by DISCHARGING the
  reach triple `{R, hballS, hballC, hbR}` internally — using the sharp reach `WhiteSharpReach` — so the
  strengthened witness `white_final8_joint_witness_sharp` carries ONLY the recognized J3 blocker
  `hflowData`.  No `sorry`, no `admit`, no new axioms, no `:= True`, nothing committed / wired into
  `QIQTH.lean` / `AxiomAudit`.

  ── HOW THE TRIPLE IS DISCHARGED (at `n = 2`, `κ = −1`, `Kset = closedBall 0 2`).
    Set `R := (1 − C_L·c)·(3c/4)` with `C_L` the near-identity Jacobian constant of the sharp reach.
      • `hballC` — the sharp reach `uniformFlowExp_sharp_reach` at `q = 0` (`φ_0 0 = 0` via
        `uniformFlowExp_zero`) gives `closedBall 0 R ⊆ φ_0 '' ball 0 c` VERBATIM.
      • `hballS` — the gate `S 0 = φ_0 '' ball 0 c`, so `hballS = hballC`.
      • `hbR` — `(c/2)(1 + C_D·c) < R` from `sharp_reach_window_arith`, whose small-`c` premise
        `2·C_D·c + 3·C_L·c < 1` is FORCED by shrinking `c` below `1/(2C_D + 3C_L + 2)` (folded into the
        shared-radius `min`).  `C_D` = displacement const, `C_L` = near-identity const.
    Everything else is EXACTLY the J4-721 co-instantiation (the A-group + `hagree/hSopen/hSreach/hspec/
    hclosclause/hdisp0/h0K/hcδ`), replayed at the smaller shared radius.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `white_final8_joint_witness_sharp` — ★★★ the strengthened joint witness: at the concrete config
      there ARE `S,a,b,c,δ₀,C_D` with `0<a<b<c<δ₀`, `0≤C_D`, such that — GIVEN ONLY `hflowData` — the
      whitened inner-pairing interior-time continuity of `final8` holds on `Ioo 0 u`, ∀ `u ∈ (0,1]`.
      The reach triple is DISCHARGED internally.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.WhiteFinal8JointWitness
import QIQTH.WhiteSharpReach

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteAnnulus
open QIQTH.WhiteS1C QIQTH.WhiteHInnerContFinal QIQTH.WhiteLeviConvergenceTrio
open QIQTH.WhiteHsolveFlowContraction
open QIQTH.WhiteFinal8JointWitness QIQTH.WhiteSharpReach
open scoped Topology ENNReal NNReal BigOperators

namespace QIQTH.WhiteFinal8SharpWitness

set_option maxHeartbeats 1600000 in
/-- **★★★ `white_final8_joint_witness_sharp` — the reach-discharged joint witness of `final8`.**
At `n = 2`, `κ = −1`, `Kset = closedBall 0 2`, there ARE a flow-ball gate `S`, radii `a,b,c,δ₀` and a
near-isometry constant `C_D` with `0 < a < b < c < δ₀`, `0 ≤ C_D`, such that — GIVEN ONLY the
base-varying flow blocker `hflowData` — the whitened inner-pairing interior-time continuity of `final8`
holds on `Ioo 0 u`, ∀ `u ∈ (0,1]`.  The reach triple `{R,hballS,hballC,hbR}` (carried in J4-721) is now
DISCHARGED internally via the sharp reach `WhiteSharpReach.uniformFlowExp_sharp_reach` at the
small-`c` window.  ⚠ NOT `a₁ = R/6`. -/
theorem white_final8_joint_witness_sharp :
    ∃ (S : Point 2 → Set (Point 2)) (a b c δ₀ C_D : ℝ),
      0 < a ∧ a < b ∧ b < c ∧ c < δ₀ ∧ 0 ≤ C_D ∧
        (∀ (_hflowData : ∀ z₀ : Point 2, ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
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
          (Set.Ioo 0 u)) := by
  classical
  have hn : 0 < 2 := by norm_num
  -- REPLAY the A-group obtain-chain at the shared radius `c`.
  obtain ⟨δp, hδp, hpkgc⟩ := white_hpkgBound_at_radius (-1) hkm hKfat 2 hKfat_sub
  obtain ⟨δS, hδS, hS1⟩ := white_tripleHEmeas_uniform hn (-1) hkm hKfat
  obtain ⟨δV, hδVpos, wA, Cpre, A₀, A₁, hwA0, hCpre0, hA₀0, hA₁0, hvalc⟩ :=
    white_witness_value_dom_at_radius (-1) hkm hKfat 2 hKfat_sub
  obtain ⟨δW, hδWpos, hWc⟩ := white_witness_value_concrete_uniform (-1) hkm hKfat
  -- the geometry radii: chart (germ/C²/open/closure) and near-isometry displacement.
  obtain ⟨δchart, hδchart0, hchartspec⟩ :=
    uniformInverseChart_huniformChart (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) hkm) hKfat
  obtain ⟨ρ₀, hρ₀0, C_D, hCD0, hdisp⟩ :=
    uniformFlowExp_displacement_bound (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) hkm) hKfat
  -- ★ THE SHARP REACH data (near-identity constant `C_L`).
  obtain ⟨ρsharp, hρsharp0, C_L, hCL0, hreach⟩ :=
    uniformFlowExp_sharp_reach (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) hkm) hKfat
  -- the small-`c` window radius `ρwin := 1/(2C_D + 3C_L + 2)`.
  set ρwin : ℝ := 1 / (2 * C_D + 3 * C_L + 2) with hρwindef
  have hden : 0 < 2 * C_D + 3 * C_L + 2 := by linarith
  have hρwin0 : 0 < ρwin := by rw [hρwindef]; positivity
  -- the shared gate radius `c` below ALL radii (incl. sharp + window).
  set m : ℝ := min δp (min δS (min δV (min δW (min δchart (min ρ₀ (min ρsharp ρwin)))))) with hmdef
  have hm0 : 0 < m := by
    rw [hmdef]
    exact lt_min hδp (lt_min hδS (lt_min hδVpos (lt_min hδWpos (lt_min hδchart0
      (lt_min hρ₀0 (lt_min hρsharp0 hρwin0))))))
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
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hmsharp : m ≤ ρsharp := by
    rw [hmdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  have hmwin : m ≤ ρwin := by
    rw [hmdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
  have hcp : c < δp := by rw [hcdef]; linarith
  have hcS : c < δS := by rw [hcdef]; linarith
  have hcV : c < δV := by rw [hcdef]; linarith
  have hcW : c < δW := by rw [hcdef]; linarith
  have hcchart : c < δchart := by rw [hcdef]; linarith
  have hcρ : c < ρ₀ := by rw [hcdef]; linarith
  have hcsharp : c ≤ ρsharp := by rw [hcdef]; linarith
  have hcwin : c ≤ ρwin := by rw [hcdef]; linarith
  have ha : 0 < c / 4 := by linarith
  have hab : c / 4 < c / 2 := by linarith
  have hbc : c / 2 < c := by linarith
  -- THE small-`c` window inequality `2C_D c + 3C_L c < 1`.
  have hS2 : 0 ≤ 2 * C_D + 3 * C_L := by linarith
  have hwin : 2 * C_D * c + 3 * C_L * c < 1 := by
    have h1 : (2 * C_D + 3 * C_L) * c ≤ (2 * C_D + 3 * C_L) * ρwin :=
      mul_le_mul_of_nonneg_left hcwin hS2
    have h2 : (2 * C_D + 3 * C_L) * ρwin < 1 := by
      rw [hρwindef, mul_one_div, div_lt_one hden]; linarith
    nlinarith [h1, h2]
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
  -- the geometry B-group.
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
  -- ★ DISCHARGE THE REACH TRIPLE.
  set R : ℝ := (1 - C_L * c) * (3 * c / 4) with hRdef
  have hφ00 : uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) hkm) hKfat 0 0 = 0 :=
    uniformFlowExp_zero (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) hkm) hKfat 0 h0Kfat
  have hballC : Metric.closedBall (0 : Point 2) R ⊆
      uniformFlowExp (curvedRNCMetric (-1)) (curvedRNCInv (-1))
        (curvedRNC_hChr (-1) hkm) hKfat 0 '' Metric.ball (0 : Point 2) c := by
    have hr := hreach 0 h0Kfat c hc0 hcsharp
    rw [hφ00] at hr
    rw [hRdef]; exact hr
  have hballS : Metric.closedBall (0 : Point 2) R ⊆ S 0 := by rw [hSdef]; exact hballC
  have hbR : (c / 2) * (1 + C_D * c) < R := by
    rw [hRdef]; exact sharp_reach_window_arith c C_D C_L hc0 hwin
  -- assemble the witness; carry ONLY the flow blocker.
  refine ⟨S, c / 4, c / 2, c, δchart, C_D, ha, hab, hbc, hcchart, hCD0, ?_⟩
  intro hflowData
  exact white_hInnerCont_closed_final8 hn (-1) hkm hKfat S (c / 4) (c / 2) ha hab
    C hC0 hpkg hEmeas hWmeas wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval
    Wg hagree c δchart hcchart hflowData hSopen hSreach hspec
    R h0Kfat hballS hballC C_D hCD0 hdisp0 hclosclause hbR (Set.Ioc 0 1)
    (fun u hu => hu.2)

end QIQTH.WhiteFinal8SharpWitness

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteFinal8SharpWitness
#check @white_final8_joint_witness_sharp
#print axioms white_final8_joint_witness_sharp
end AxiomChecks
