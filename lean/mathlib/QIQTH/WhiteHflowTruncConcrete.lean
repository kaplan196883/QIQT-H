/-
  WhiteHflowTruncConcrete — J4-733: THE CONCRETE-WITNESS `hflowTrunc` CASE-SPLIT ASSEMBLY.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` (`R/6` stays a labelled carrier, untouched).
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE INTERFACE VERDICT (the pivot of J4-733).
    `WhiteHsolveFlowTruncated.white_hInnerCont_closed_final9` carries the truncated contraction data
    `hflowTrunc` as a hypothesis quantified over **ALL** base points `z₀ : Point n` — its clauses (i) the
    clamp-centred `ContractingWith` and (ii) the uniform v-Lipschitz are demanded for EVERY `z₀`, NOT only
    where the frontier bad set `{w | z₀ ∈ frontier (S w)}` is inhabited.  Those two clauses cannot be
    honestly supplied for a FAR `z₀` whose truncation window `closedBall z₀ r` lies outside the compact
    base set `K`: there the concrete flow `uniformFlowExp` has no confined geodesic tube, hence no
    window-uniform near-identity derivative and no small-constant base-displacement Lipschitz bound.  The
    supplier bricks `baseDisplacement_windowed_lipschitz_concrete` / `uniformFlowExp_vLipschitz_uniform`
    are, correctly, gated by an honest σ-interior-of-`K` window hypothesis (`hKσ`) that a far `z₀` cannot
    satisfy.  So discharging `hflowTrunc` verbatim (∀ `z₀`) is a category error — it would force an
    unsatisfiable ∀-`z₀` window hypothesis (the cp466 vacuity trap).

    THE CORRECT DISCHARGE IS THE CASE-SPLIT AT THE `hsolveFlow` (per-`z₀` `H`-existential) LEVEL, exactly
    as `final7` consumes it.  For each `z₀`:
      • if the bad set `{w | z₀ ∈ frontier (S w)}` is EMPTY (the far `z₀`), the containment conclusion
        `∅ ⊆ H '' sphere` is trivial for the DEGENERATE constant solver `H := fun _ => z₀` (`LipschitzOnWith
        0`) — no contraction data needed;
      • if the bad set is NONEMPTY (the near `z₀`), the truncated Banach solver runs on exactly the
        window-local, satisfiable contraction data — the SAME construction as
        `WhiteHsolveFlowTruncated.hsolveFlow_of_truncatedContractionData`, but the data is only ever
        required where the window IS in `K`'s σ-interior.

    This file BUILDS that case-split producer `white_hsolveFlow_of_truncNear` (near-only data ⟹ the full
    `hsolveFlow` output `final7` demands) and the corrected terminal feed
    `white_hInnerCont_closed_final10`.  The ∀-`z₀` window vacuity is dissolved: the truncated data is
    consumed ONLY on the inhabited bad set, where the σ-interior window is genuinely available.

  ── WHAT IS FULLY PROVEN HERE (no residual, std-3 axioms).
    * `white_hsolveFlow_of_truncNear` — ★★★ THE CASE-SPLIT PRODUCER.  Gate reach + `ρ ≤ r` + NEAR-ONLY
      truncated contraction data (the three clauses, required only when the bad set is inhabited) ⟹ the
      per-`z₀` Lipschitz-solvability certificate `hsolveFlow`.  Far `z₀` handled by the degenerate constant
      solver; near `z₀` by the clamp-centred Banach fixed point.  FULLY PROVEN.  ⚠ NOT `a₁ = R/6`.
    * `white_hInnerCont_closed_final10` — ★★★ `final7` with the `hsolveFlow` residual REPLACED by the
      NEAR-ONLY (satisfiable, non-vacuous) truncated contraction data + the gate reach.  The correct
      terminal feed the ∀-`z₀` `final9` could not honestly be.  ⚠ NOT `a₁ = R/6`.
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

namespace QIQTH.WhiteHflowTruncConcrete

variable {n : ℕ}

/-! ### §A — the case-split producer: near-only truncated data ⟹ `hsolveFlow`. -/

/-- **★★★ THE CASE-SPLIT PRODUCER.**  For a true-flow family `φ : Point n → Point n → Point n`, a gate
family `S` with uniform reach `∀ w, S w ⊆ closedBall w ρ` and `ρ ≤ r`, and per-`z₀` truncated contraction
data that is required **only where the frontier bad set is inhabited** (`hnear`) — a uniform constant
`Kc < 1` making the clamp-centred truncated solver map `ContractingWith Kc` for each sphere direction, a
uniform Lipschitz-in-`v` modulus `Cv`, and the true-flow frontier→sphere-image containment — the full
per-`z₀` Lipschitz-solvability certificate `hsolveFlow` holds.

Case split per `z₀`:
* bad set EMPTY (far `z₀`): the degenerate constant solver `H := fun _ => z₀` is `LipschitzOnWith 0`, and
  `∅ ⊆ H '' sphere` is trivial.  No contraction data is used here — this is why the ∀-`z₀` window
  hypothesis of `final9` was a category error.
* bad set NONEMPTY (near `z₀`): the clamp-centred Banach fixed point (verbatim the construction of
  `WhiteHsolveFlowTruncated.hsolveFlow_of_truncatedContractionData`), consuming the satisfiable
  window-local data supplied by `hnear`.  The bad-set localization `badSet_subset_closedBall` drives
  `coordClamp = id` on the frontier, so the truncated map equals the true flow there and the containment
  leg lands each bad base inside `H '' sphere`.

FULLY PROVEN.  ⚠ NOT `a₁ = R/6`. -/
theorem white_hsolveFlow_of_truncNear
    {S : Point n → Set (Point n)} {c r ρ : ℝ} (hρr : ρ ≤ r)
    (φ : Point n → Point n → Point n)
    (hreach : ∀ w : Point n, S w ⊆ Metric.closedBall w ρ)
    (hnear : ∀ z₀ : Point n, {w : Point n | z₀ ∈ frontier (S w)}.Nonempty →
        ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
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
  rcases Set.eq_empty_or_nonempty {w : Point n | z₀ ∈ frontier (S w)} with hempty | hne
  · -- FAR `z₀`: empty bad set, degenerate constant solver.
    refine ⟨fun _ => z₀, 0, ?_, ?_⟩
    · rw [lipschitzOnWith_iff_dist_le_mul]
      intro x _ y _
      simp
    · rw [hempty]; exact Set.empty_subset _
  · -- NEAR `z₀`: the clamp-centred Banach fixed point on the satisfiable window data.
    obtain ⟨Kc, Cv, hKc1, hcontr, hvlip, hfront⟩ := hnear z₀ hne
    set Φ : Point n → Point n → Point n :=
      fun v w => z₀ - (φ (coordClamp z₀ r w) v - coordClamp z₀ r w + w) + w with hΦdef
    set H : Point n → Point n := fun v =>
      if h : v ∈ Metric.sphere (0 : Point n) c then
        ContractingWith.fixedPoint (Φ v) (hcontr v h)
      else z₀ with hHdef
    have honesub : (0 : ℝ) < 1 - (Kc : ℝ) := by
      have hlt : (Kc : ℝ) < 1 := by exact_mod_cast hKc1
      linarith
    refine ⟨H, Cv / (1 - Kc), ?_, ?_⟩
    · rw [lipschitzOnWith_iff_dist_le_mul]
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
    · intro w hw
      have hwin : w ∈ Metric.closedBall z₀ r :=
        badSet_subset_closedBall z₀ r ρ hρr S hreach hw
      have hcc : coordClamp z₀ r w = w := coordClamp_eq_self_of_mem_closedBall z₀ r w hwin
      obtain ⟨v, hv, hφeq⟩ := hfront hw
      have hfpw : Function.IsFixedPt (Φ v) w := by
        show z₀ - (φ (coordClamp z₀ r w) v - coordClamp z₀ r w + w) + w = w
        rw [hcc, hφeq]; abel
      have huniq : w = ContractingWith.fixedPoint (Φ v) (hcontr v hv) :=
        (hcontr v hv).fixedPoint_unique hfpw
      have hHvw : H v = w := by rw [hHdef]; simp only [dif_pos hv]; rw [← huniq]
      exact ⟨v, hv, hHvw⟩

/-! ### §B — the corrected terminal feed: `final7` from the NEAR-ONLY truncated data. -/

/-- **★★★ `white_hInnerCont_closed_final10` (THE CORRECT TERMINAL FEED, `hsolveFlow` DISSOLVED VIA THE
NEAR-ONLY CASE-SPLIT).**  Identical conclusion and hypotheses to
`WhiteHnullFlowReduction.white_hInnerCont_closed_final7`, except the Lipschitz-solvability residual
`hsolveFlow` is REPLACED by the SATISFIABLE, NON-VACUOUS near-only truncated base-varying-flow contraction
data `hflowTruncNear` (the three clamp-centred clauses, required only where the frontier bad set is
inhabited) plus the gate reach `hreach : ∀ w, S w ⊆ closedBall w ρ` with `ρ ≤ r`.  `hsolveFlow` is
discharged internally by `white_hsolveFlow_of_truncNear`.  Unlike the ∀-`z₀` `final9` — whose `hflowTrunc`
demanded the clamp-centred contraction for FAR `z₀` too, forcing an unsatisfiable σ-interior window
hypothesis — this feed only ever requires the truncated data on the inhabited bad set, where the window IS
in `K`'s σ-interior.  ⚠ NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final10 (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
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
    -- B''''. the NEAR-ONLY (SATISFIABLE, NON-VACUOUS) base-varying-flow contraction data + the gate reach.
    (r ρ : ℝ) (hρr : ρ ≤ r)
    (hreach : ∀ w : Point n, S w ⊆ Metric.closedBall w ρ)
    (hflowTruncNear : ∀ z₀ : Point n, {w : Point n | z₀ ∈ frontier (S w)}.Nonempty →
        ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
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
    (white_hsolveFlow_of_truncNear (S := S) (c := c) (r := r) (ρ := ρ) hρr
      (fun w v => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v)
      hreach hflowTruncNear)
    hSopen hSreach hspec R h0K hballS hballC C_D hCD0 hdisp0 hclosclause hbR Uwin hU1

end QIQTH.WhiteHflowTruncConcrete

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHflowTruncConcrete
#check @white_hsolveFlow_of_truncNear
#check @white_hInnerCont_closed_final10
#print axioms white_hsolveFlow_of_truncNear
#print axioms white_hInnerCont_closed_final10
end AxiomChecks
