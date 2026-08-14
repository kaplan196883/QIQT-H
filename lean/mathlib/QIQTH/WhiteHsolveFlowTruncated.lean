/-
  WhiteHsolveFlowTruncated — J4-732: THE TRUNCATED (z₀-DEPENDENT) BANACH SOLVER + the honest
  terminal feed of `hsolveFlow` from the SATISFIABLE truncated contraction data.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` (`R/6` stays a labelled carrier, untouched).
  It targets the sole surviving analytic residual `hsolveFlow` of the whitened `hInnerCont` chain
  (`WhiteHnullFlowReduction.white_hInnerCont_closed_final7`), and discharges it — via a FULLY PROVEN
  Banach-fixed-point construction on the TRUNCATED (clamped) solver map — from the base-varying-flow
  contraction data.  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE INTERFACE VERDICT (the pivot of J4-732).
    The banked abstract solver `WhiteHsolveFlowContraction.hsolveFlow_of_contractionData` takes a single
    z₀-INDEPENDENT flow family `Ψ` and, in `white_hInnerCont_closed_final8`, is fed `Ψ = uniformFlowExp`.
    Its `hflowData (i)` clause therefore demands a GLOBAL `ContractingWith Kc` of the UN-truncated true
    flow `w ↦ z₀ − uniformFlowExp w v + w` on ALL of `Point n`.  That is unprovable: the base-displacement
    Lipschitz bank (`baseDisplacement_windowed_lipschitz_concrete`) supplies contraction only on a WINDOW,
    and off the compact base set `K` the flow has no small-constant control.  The J3 truncation bricks
    (`coordClamp`, `truncatedSolverMap_contractingWith_solverShape`, `badSet_subset_closedBall`,
    `coordClamp_eq_self_of_mem_closedBall`) were built precisely to AVOID that global demand — but their
    contraction is for the z₀-DEPENDENT truncated map `Ψtrunc z₀ w v := φ (coordClamp z₀ r w) v −
    coordClamp z₀ r w + w`, whose clamp centre is z₀.  The z₀-independent-`Ψ` solver cannot express it.

    This file BUILDS THE MISSING KEYSTONE: the z₀-dependent truncated solver
    `hsolveFlow_of_truncatedContractionData`, which consumes exactly the SATISFIABLE truncated
    contraction data (window-local `ContractingWith`, uniform v-Lipschitz, true-flow frontier→sphere
    containment) and produces the same `hsolveFlow` output `final7` demands.  The bad-set localization
    (`badSet_subset_closedBall`) drives `coordClamp = id` on the frontier bad set, so the truncated map
    agrees with the true flow exactly where the containment leg (iii) lives; the Banach fixed point on the
    globally-contracting truncated map then lands the bad base inside a Lipschitz image of the sphere.

  ── WHAT IS FULLY PROVEN HERE (no residual, std-3 axioms).
    * `hsolveFlow_of_truncatedContractionData` — ★★ THE TRUNCATED SOLVER.  z₀-dependent, clamp-centred.
    * `white_hInnerCont_closed_final9` — ★★★ `final7` with the `hsolveFlow` residual REPLACED by the
      truncated (SATISFIABLE) contraction data + the gate reach `∀ w, S w ⊆ closedBall w ρ` (`ρ ≤ r`).
      ZERO analytic residuals beyond that honest data.  This is the CORRECT terminal feed the walled
      `final8` (global-contraction-of-true-flow) could not be.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteHnullFlowReduction
import QIQTH.BaseFlowGlobalContraction
import QIQTH.BaseFlowTruncationWindow

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
open QIQTH.BaseFlowGlobalContraction
open QIQTH.BaseFlowTruncationWindow
open scoped Topology ENNReal NNReal

namespace QIQTH.WhiteHsolveFlowTruncated

variable {n : ℕ}

/-! ### §A — the z₀-dependent TRUNCATED Banach-fixed-point solver. -/

/-- **★★ THE TRUNCATED SOLVER.**  For a true-flow family `φ : Point n → Point n → Point n`
(`φ w v` = the flow image at base `w`, direction `v`), a gate family `S` with uniform reach
`∀ w, S w ⊆ closedBall w ρ` and `ρ ≤ r`, and per-`z₀` truncated contraction data — a uniform
constant `Kc < 1` making the CLAMP-CENTRED truncated solver map
`w ↦ z₀ − (φ (coordClamp z₀ r w) v − coordClamp z₀ r w + w) + w` `ContractingWith Kc` for each sphere
direction `v`, a uniform Lipschitz-in-`v` modulus `Cv` of `v ↦ φ (coordClamp z₀ r w) v`, and the
TRUE-flow frontier→sphere-image containment `{w | z₀ ∈ frontier (S w)} ⊆ {w | ∃ v ∈ sphere 0 c, φ w v =
z₀}` — the Lipschitz-solvability certificate `hsolveFlow` holds.

Construction: `H v := ContractingWith.fixedPoint (Φ v)` with `Φ v w := z₀ − Ψtrunc w v + w`,
`Ψtrunc w v := φ (coordClamp z₀ r w) v − coordClamp z₀ r w + w`.  `fixedPoint_lipschitz_in_map` makes
`H` Lipschitz on the sphere with constant `Cv / (1 − Kc)`.  For a bad base `w` (`z₀ ∈ frontier (S w)`)
the localization `badSet_subset_closedBall` puts `w ∈ closedBall z₀ r`, so `coordClamp z₀ r w = w`
(`coordClamp_eq_self_of_mem_closedBall`); the truncated map then EQUALS the true flow there, and the
containment leg (iii) provides `v` with `φ w v = z₀`, making `w` a fixed point of `Φ v`; by uniqueness
`w = H v`, landing the bad set inside `H '' sphere`.  FULLY PROVEN.  ⚠ NOT `a₁ = R/6`. -/
theorem hsolveFlow_of_truncatedContractionData
    {S : Point n → Set (Point n)} {c r ρ : ℝ} (hρr : ρ ≤ r)
    (φ : Point n → Point n → Point n)
    (hreach : ∀ w : Point n, S w ⊆ Metric.closedBall w ρ)
    (hdata : ∀ z₀ : Point n, ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
        (∀ v ∈ Metric.sphere (0 : Point n) c,
          ContractingWith Kc
            (fun w => z₀ - (φ (coordClamp z₀ r w) v - coordClamp z₀ r w + w) + w)) ∧
        (∀ v ∈ Metric.sphere (0 : Point n) c, ∀ v' ∈ Metric.sphere (0 : Point n) c, ∀ w : Point n,
          dist (φ (coordClamp z₀ r w) v) (φ (coordClamp z₀ r w) v') ≤ (Cv : ℝ) * dist v v') ∧
        {w : Point n | z₀ ∈ frontier (S w)} ⊆
          {w : Point n | ∃ v ∈ Metric.sphere (0 : Point n) c, φ w v = z₀}) :
    ∀ z₀ : Point n, ∃ (H : Point n → Point n) (K : ℝ≥0),
        LipschitzOnWith K H (Metric.sphere 0 c) ∧
        {w : Point n | z₀ ∈ frontier (S w)} ⊆ H '' Metric.sphere (0 : Point n) c := by
  classical
  intro z₀
  obtain ⟨Kc, Cv, hKc1, hcontr, hvlip, hfront⟩ := hdata z₀
  -- The clamp-centred contraction map.
  set Φ : Point n → Point n → Point n :=
    fun v w => z₀ - (φ (coordClamp z₀ r w) v - coordClamp z₀ r w + w) + w with hΦdef
  -- The total solver map: fixed point on the sphere, default `z₀` off it.
  set H : Point n → Point n := fun v =>
    if h : v ∈ Metric.sphere (0 : Point n) c then
      ContractingWith.fixedPoint (Φ v) (hcontr v h)
    else z₀ with hHdef
  have honesub : (0 : ℝ) < 1 - (Kc : ℝ) := by
    have hlt : (Kc : ℝ) < 1 := by exact_mod_cast hKc1
    linarith
  refine ⟨H, Cv / (1 - Kc), ?_, ?_⟩
  · -- Lipschitz on the sphere via `fixedPoint_lipschitz_in_map`.
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hHx : H x = ContractingWith.fixedPoint (Φ x) (hcontr x hx) := dif_pos hx
    have hHy : H y = ContractingWith.fixedPoint (Φ y) (hcontr y hy) := dif_pos hy
    have hclose : ∀ z : Point n, dist (Φ x z) (Φ y z) ≤ (Cv : ℝ) * dist x y := by
      intro z
      have heq : dist (Φ x z) (Φ y z)
          = dist (φ (coordClamp z₀ r z) x) (φ (coordClamp z₀ r z) y) := by
        simp only [hΦdef]
        have hsub : (z₀ - (φ (coordClamp z₀ r z) x - coordClamp z₀ r z + z) + z)
              - (z₀ - (φ (coordClamp z₀ r z) y - coordClamp z₀ r z + z) + z)
            = φ (coordClamp z₀ r z) y - φ (coordClamp z₀ r z) x := by abel
        rw [dist_eq_norm, hsub, ← dist_eq_norm, dist_comm]
      rw [heq]; exact hvlip x hx y hy z
    have hdist := (hcontr x hx).fixedPoint_lipschitz_in_map (hcontr y hy) hclose
    rw [← hHx, ← hHy] at hdist
    have hcoe : ((Cv / (1 - Kc) : ℝ≥0) : ℝ) = (Cv : ℝ) / (1 - (Kc : ℝ)) := by
      rw [NNReal.coe_div, NNReal.coe_sub hKc1.le, NNReal.coe_one]
    rw [hcoe]
    calc dist (H x) (H y)
        ≤ (Cv : ℝ) * dist x y / (1 - (Kc : ℝ)) := hdist
      _ = (Cv : ℝ) / (1 - (Kc : ℝ)) * dist x y := by ring
  · -- Containment: each bad base `w` is a fixed point (via clamp = id on the window), hence in image.
    intro w hw
    -- localization: the bad base lands in the window, so the clamp is the identity there.
    have hwin : w ∈ Metric.closedBall z₀ r :=
      badSet_subset_closedBall z₀ r ρ hρr S hreach hw
    have hcc : coordClamp z₀ r w = w := coordClamp_eq_self_of_mem_closedBall z₀ r w hwin
    obtain ⟨v, hv, hφeq⟩ := hfront hw
    -- `w` is a fixed point of `Φ v` (truncated map = true flow at the window base).
    have hfpw : Function.IsFixedPt (Φ v) w := by
      show z₀ - (φ (coordClamp z₀ r w) v - coordClamp z₀ r w + w) + w = w
      rw [hcc, hφeq]; abel
    have huniq : w = ContractingWith.fixedPoint (Φ v) (hcontr v hv) :=
      (hcontr v hv).fixedPoint_unique hfpw
    have hHvw : H v = w := by rw [hHdef]; simp only [dif_pos hv]; rw [← huniq]
    exact ⟨v, hv, hHvw⟩

/-! ### §B — the terminal feed: `final7` with `hsolveFlow` from the truncated contraction data. -/

/-- **★★★ `white_hInnerCont_closed_final9` (THE CORRECT TERMINAL FEED, `hsolveFlow` DISSOLVED VIA
TRUNCATION).**  Identical conclusion and hypotheses to
`WhiteHnullFlowReduction.white_hInnerCont_closed_final7`, except the Lipschitz-solvability residual
`hsolveFlow` is REPLACED by the SATISFIABLE truncated base-varying-flow contraction data `hflowTrunc`
(clamp-centred `ContractingWith`, uniform v-Lipschitz, true-flow frontier→sphere containment) plus the
gate reach `hreach : ∀ w, S w ⊆ closedBall w ρ` with `ρ ≤ r`.  `hsolveFlow` is discharged internally by
`hsolveFlow_of_truncatedContractionData`.  Unlike the walled `final8` — which demanded an UNPROVABLE
global `ContractingWith` of the un-truncated `uniformFlowExp` — this feed carries only the window-local,
truncation-clamped contraction actually supplied by the J3 bricks.  ⚠ NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final9 (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
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
    -- B'''. the TRUNCATED (SATISFIABLE) base-varying-flow contraction data + the gate reach.
    (r ρ : ℝ) (hρr : ρ ≤ r)
    (hreach : ∀ w : Point n, S w ⊆ Metric.closedBall w ρ)
    (hflowTrunc : ∀ z₀ : Point n, ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
        (∀ v ∈ Metric.sphere (0 : Point n) c,
          ContractingWith Kc
            (fun w => z₀ -
              (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
                  (coordClamp z₀ r w) v - coordClamp z₀ r w + w) + w)) ∧
        (∀ v ∈ Metric.sphere (0 : Point n) c, ∀ v' ∈ Metric.sphere (0 : Point n) c, ∀ w : Point n,
          dist (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
                (coordClamp z₀ r w) v)
              (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
                (coordClamp z₀ r w) v')
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
    (hsolveFlow_of_truncatedContractionData (S := S) (c := c) (r := r) (ρ := ρ) hρr
      (fun w v => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v)
      hreach hflowTrunc)
    hSopen hSreach hspec R h0K hballS hballC C_D hCD0 hdisp0 hclosclause hbR Uwin hU1

end QIQTH.WhiteHsolveFlowTruncated

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHsolveFlowTruncated
#check @hsolveFlow_of_truncatedContractionData
#check @white_hInnerCont_closed_final9
#print axioms hsolveFlow_of_truncatedContractionData
#print axioms white_hInnerCont_closed_final9
end AxiomChecks
