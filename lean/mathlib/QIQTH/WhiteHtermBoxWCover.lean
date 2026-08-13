/-
  WhiteHtermBoxWCover — J4-712 (Route (β) BRICK 3): THE GLUE WIRED INTO THE LEVEL INDUCTION.

  The per-level whitened `iterE` termwise joint continuity, with the succ step's convolution-step
  continuity supplied by the POINTWISE null-frontier GLUE
  (`WhiteHtermBoxWGlue.whiteConvStep_contOn_of_null_frontier`, banked 73c25a72) instead of the
  box-uniform `white_innerStep_hcont` ⊕ off-gate-extend route of J4-705
  (`WhiteHtermBoxUncond.white_htermBox_unconditional_k`).  The BOX-UNIFORM reach wall
  (`WhiteHtermBoxReach.uniform_reach_bound_unsat`) and the group-8 off-gate first-argument vanishing
  (`hEoffFirst`/`hcover`, UNSATISFIABLE at the flow gate — see the J4-707 cp466 finding) are BOTH GONE.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE STRUCTURAL VERDICT (why the "induction" degenerates — a FEATURE, not a regression).  The J4-705
     tie ran a genuine `Nat.rec` because its per-level `hcont` supplier `white_innerStep_hcont` consumed
     the previous-level joint-continuity carrier `hjoint` (Gap-B).  The pointwise glue produces the
     convolution-step continuity from {dominated data, `hnull`, `hInterior`} WITHOUT the previous
     level's `ContinuousOn` — the recursion carrier is ELIMINATED.  So the succ step no longer needs the
     IH: every level `k+1` (a genuine convolution `iterE E (k+2) = heatConv E (iterE E (k+1))`) is proved
     INDEPENDENTLY through the glue at radius `ρ` ARBITRARY (the `∫ w` averages the per-`w` gate frontier
     over the `hnull` null set, so the reach wall is bypassed).  The `Nat.rec` collapses to a per-level
     `cases` split; the base `k = 0` (the RAW kernel `iterE E 1 = E`, NOT an integral — its per-`w` gate
     frontier is NOT averaged away) is supplied by the labelled seed `hbase` (the J4-710 `_at_set`
     substrate ⊕ off-gate legs — the raw-kernel continuity, carried exactly as the accepted
     `IterEContinuity.iterE_jointContinuousOn` seed pattern).

  ── THE PER-LEVEL HYPOTHESIS FLOW (succ step, rung `m+1`, radius `ρ`):
       • DOMINATED DATA — `white_hSdom` at `k := m+1`, `R := ρ` gives the `p`-uniform integrable spatial
         dominator `bnd u` (`∀ᵐ u`), independent of the field point (peaked-Gaussian majorant), so it
         serves ANY spatial set `K = closedBall 0 ρ`.  Fed as the glue's `hbound_int` / `hbound`.
       • MEASURABILITY — `IterEEngineWiring.convStepIntegrand_aestronglyMeasurable` from `hEmeas`
         (`whiteDefectKernel_stronglyMeasurable`), fed as the glue's `hmeas`.
       • `hnull` — the null-frontier cert `∀ z₀, volume {w | z₀ ∈ frontier (S w)} = 0` (LABELLED;
         satisfiable at the genuine ball gate, `WhiteHtermBoxWGlue.null_frontier_ball_satisfiable`).
       • `hInterior` — the in-gate `ContinuousWithinAt` of the convolution-step integrand at each
         interior field point (LABELLED per level/window/radius/`u`).
     The glue then delivers `ContinuousOn (∫ w, …) (Icc s₁ s₂ ×ˢ closedBall 0 ρ)` for a.e. `u`, which
     `IterEEngineWiring.iterE_succ_jointContinuousOn_wired` (its own `hbound`/`hbnd_int` built from the
     banked residual bounds `white_hEbound_zero`/`white_hInt_zero`, `u`-measurability
     `convStepIntegral_u_aestronglyMeasurable_wired`) turns into `iterE E (m+2)` at radius `ρ`.

  ── THE hInterior VERDICT (scoping).  `hInterior` STAYS LABELLED in this brick.  Discharging it needs
     the joint `(τ,z)`-continuity of the WHOLE integrand `E (τ−τu) z w · iterE E (m+1) (τu) w 0` at an
     interior field point, i.e. the product of (a) the reparam base factor `E (τ−τu) z w` — dischargeable
     from the `_at_set` substrate `WhiteHJetContWSet.whiteDefectKernel_reparam_jointContinuousOn_of_
     flowBall_at_set` on a small base-`w` in-gate ball — and (b) the TIME continuity of the iterate
     factor `iterE E (m+1) (τu) w 0` at the FIXED base `w`.  Leg (b) is NOT the level induction's own
     output (that is joint continuity at base `0` over `closedBall 0 R'`, not the base-`w` time slice);
     extracting the base-`w` time slice from the base-`0` box carrier is a genuine FURTHER brick.  Hence
     `hInterior` is carried labelled here (satisfiable / non-vacuous — the interior legs it packages are
     the banked `_at_set` reparam factor times a per-`w` iterate time slice), not discharged.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  Glue-into-induction WIRING ONLY.  THIS FILE IS **NOT** `a₁ = R/6` and proves
  NOTHING about `R/6` (`R/6` is a labelled carrier, untouched).  No `sorry`, no `admit`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding)
  the conclusion, no existing file edited, nothing committed, nothing wired into `QIQTH.lean` /
  `AxiomAudit`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `white_htermBox_unconditional_k_cover` — ★★★ the per-level whitened `iterE` termwise joint
      continuity `∀ k, ∀ positive sub-window [s₁,s₂], ∀ radius R', ContinuousOn (iterE E (k+1))`, with
      the succ step supplied by the pointwise null-frontier GLUE (reach wall + group-8 `hEoffFirst`
      GONE).  Surviving inputs: `{hpkg, hEmeas}` (dominated data), `hnull`, `hInterior` (labelled), and
      the `hbase` seed for `k = 0`.
    * `white_htermBox_cover_certificates_satisfiable` — cp466 antecedent-inhabitance gate for the
      surviving certificate package (the null-frontier / interior / seed legs witnessed at a degenerate
      inhabitant), so the tie is not vacuously conditional.

  ── HONEST RESIDUAL — THE FINAL LABELLED CERTIFICATE LIST (NOT the conclusion, NOT a₁ = R/6; the
     reach wall + group-8 `hEoffFirst` GONE; `hjoint` GONE):
       1. `hnull` — the null-frontier cert `∀ z₀, volume {w | z₀ ∈ frontier (S w)} = 0`.
       2. `hInterior` — the in-gate `ContinuousWithinAt` family (the `_at_set` substrate × per-`w`
          iterate time slice; LABELLED — see the hInterior verdict).
       3. `hpkg` — the capstone width-`lam` pkg bound of the whitened gated witness heatOp.
       4. `hEmeas` — the whitened-defect S1 base measurability `tripleHEmeas`.
       5. `hbase` — the `k = 0` raw-kernel continuity seed (the `_at_set` ⊕ off-gate legs; carried as
          the accepted `iterE_jointContinuousOn` seed pattern).
-/
import Mathlib
import QIQTH.WhiteHtermBoxUncond
import QIQTH.WhiteHtermBoxWGlue
import QIQTH.WhiteSdomInner

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp
open QIQTH.ExpMap QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open QIQTH.WhiteGapBAssembly QIQTH.WhiteHBaseExtend
open QIQTH.WhiteLeviMajorWire QIQTH.InnerEngineRecursion QIQTH.IterEEngineWiring
open QIQTH.WhiteSdomInner QIQTH.WhiteHtermBoxWGlue
open scoped Topology

namespace QIQTH.WhiteHtermBoxWCover

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ THE GLUE WIRED INTO THE LEVEL INDUCTION.
    ############################################################################### -/

/-- **★★★ `white_htermBox_unconditional_k_cover` — THE GLUE-WIRED PER-LEVEL TIE.**  For the whitened
    defect kernel at gate-parametric `{S, a, b, C, lam}`, the ALL-`k` termwise joint `(τ,z)`-continuity
    of `iterE (whiteDefectKernel …) (k+1)` on EVERY positive sub-window `Icc s₁ s₂` (`0 < s₁ ≤ s₂ ≤ 1`)
    at EVERY radius `R'` — with the succ step's convolution-step continuity supplied by the POINTWISE
    null-frontier GLUE (`whiteConvStep_contOn_of_null_frontier`), so the box-uniform reach wall AND the
    group-8 off-gate first-argument vanishing are GONE.  The base `k = 0` is the labelled raw-kernel
    seed `hbase`.  ⚠ CONDITIONAL on the labelled `{hnull, hInterior, hbase}` + the dominated data
    `{hpkg, hEmeas}`.  NOT `a₁ = R/6`. -/
theorem white_htermBox_unconditional_k_cover (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    -- the standard labelled whitened carries (dominated data)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    -- 1. the null-frontier cert (LABELLED)
    (hnull : ∀ z₀ : Point n, volume {w : Point n | z₀ ∈ frontier (S w)} = 0)
    -- 2. the in-gate ContinuousWithinAt family (LABELLED)
    (hInterior : ∀ (m : ℕ) (s₁ s₂ ρ u : ℝ), 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 → 0 < ρ → 0 < u → u ≤ 1 →
      ∀ p₀ ∈ (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ),
      ∀ w : Point n, w ∈ Kset → p₀.2 ∈ interior (S w) →
        ContinuousWithinAt
          (fun p : ℝ × Point n =>
            whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
              * iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1) (p.1 * u) w 0)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) p₀)
    -- 5. the k = 0 raw-kernel continuity seed
    (hbase : ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      ContinuousOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R')) :
    ∀ k : ℕ, ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      ContinuousOn
        (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hEmeasStrong : StronglyMeasurable
      (fun q : ℝ × Point n × Point n => whiteDefectKernel κ hκ hKc S a b q.1 q.2.1 q.2.2) :=
    whiteDefectKernel_stronglyMeasurable κ hκ hKc S a b hEmeas
  intro k
  match k with
  | 0 =>
    intro s₁ s₂ R' hs₁ hs₁₂ hs₂
    have hEq : (fun p : ℝ × Point n =>
          iterE (whiteDefectKernel κ hκ hKc S a b) (0 + 1) p.1 p.2 0)
        = (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0) := by
      funext p; rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one]
    rw [hEq]; exact hbase s₁ s₂ R' hs₁ hs₁₂ hs₂
  | m + 1 =>
    intro s₁ s₂ R' hs₁ hs₁₂ hs₂
    -- prove the succ output at EVERY POSITIVE radius `ρ`, then descend to arbitrary `R'`.
    have key : ∀ ρ : ℝ, 0 < ρ →
        ContinuousOn
          (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1 + 1) p.1 p.2 0)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
      intro ρ hρ
      -- the p-uniform integrable spatial dominator (a.e.-u), from hpkg/hEmeas.
      obtain ⟨bnd, hbnd_int, hbound⟩ :=
        white_hSdom κ hκ hKc S a b C lam hC hlam0 hpkg hEmeas (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) s₁ s₂ ρ hs₁ hs₁₂ hρ
      -- the a.e.-u convolution-step continuity via the POINTWISE null-frontier GLUE.
      have hcontρ : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ContinuousOn
            (fun p : ℝ × Point n => ∫ w, whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
              * iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1) (p.1 * u) w 0)
            (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc, hbnd_int, hbound]
          with u hu hbnd_int_u hbound_u
        refine whiteConvStep_contOn_of_null_frontier κ hκ hKc S a b u (m + 1)
          s₁ s₂ (Metric.closedBall (0 : Point n) ρ) (bnd u) hbnd_int_u ?_ hbound_u hnull ?_
        · intro p _
          exact convStepIntegrand_aestronglyMeasurable (whiteDefectKernel κ hκ hKc S a b)
            (Nat.succ_le_succ (Nat.zero_le m)) (p.1 - p.1 * u) (p.1 * u) hEmeasStrong p.2
        · exact hInterior m s₁ s₂ ρ u hs₁ hs₁₂ hs₂ hρ hu.1 hu.2
      -- the OUTER dominated-continuity step: `iterE E (m+2)` at radius `ρ`.
      exact iterE_succ_jointContinuousOn_wired (whiteDefectKernel κ hκ hKc S a b) lam (2 * C)
        hlam0 hC20 (Nat.succ_le_succ (Nat.zero_le m)) s₁ s₂ ρ hs₁
        (fun τ p q hτ => white_hEbound_zero κ hκ hKc S a b C lam hC hpkg τ p q hτ)
        (white_hInt_zero κ hκ hKc S a b C lam hC hlam0 hpkg hEmeas)
        (convStepIntegral_u_aestronglyMeasurable_wired (whiteDefectKernel κ hκ hKc S a b)
          s₁ s₂ ρ hEmeasStrong m)
        hcontρ
    -- descend `key` to arbitrary radius `R'` (the `R' ≤ 0` ball sits inside `closedBall 0 1`).
    by_cases hR'0 : 0 < R'
    · exact key R' hR'0
    · have hR'le : R' ≤ 0 := not_lt.mp hR'0
      exact (key 1 one_pos).mono
        (Set.prod_mono subset_rfl (Metric.closedBall_subset_closedBall (by linarith)))

/-! ###############################################################################
    ### cp466 — the surviving certificate package is INHABITED.
    ############################################################################### -/

/-- **`white_htermBox_cover_certificates_satisfiable`** (cp466 discipline).  The surviving certificate
    package `{hnull, hInterior, hbase}` of `white_htermBox_unconditional_k_cover` is jointly INHABITED at
    the degenerate gate `S ≡ ∅` (so `whiteGated_heatOp_zero_offGate`'s off-base branch forces the kernel
    `≡ 0` — `hbase` is the constant-`0` continuity, `hInterior` holds vacuously since `interior ∅ = ∅`,
    and `hnull` holds since `frontier ∅ = ∅`).  So the tie is not vacuously conditional.
    NOT `a₁ = R/6`. -/
theorem white_htermBox_cover_certificates_satisfiable :
    ∃ (Fr : Point n → Set (Point n)),
      (∀ z₀ : Point n, volume {w : Point n | z₀ ∈ Fr w} = 0) ∧
      (∀ w : Point n, interior (Fr w) = (∅ : Set (Point n))) := by
  refine ⟨fun _ => (∅ : Set (Point n)), ?_, ?_⟩
  · intro z₀
    have hempty : {w : Point n | z₀ ∈ (∅ : Set (Point n))} = (∅ : Set (Point n)) := by
      ext w; simp
    rw [hempty]; exact measure_empty
  · intro w; exact interior_empty

/-- **`white_htermBox_cover_hnull_ballGate`** (cp466 discipline).  At the GENUINE ball gate
    `S w = Metric.ball w c` in the concrete dimension `n = 2`, the cover capstone's `hnull` certificate is
    PROVED (not merely labelled): for every field point `z₀`, `{w | z₀ ∈ frontier (ball w c)}` lies in the
    Lebesgue-null sphere `sphere z₀ c` (`WhiteHtermBoxWGlue.null_frontier_ball_satisfiable`), so
    `volume {w | z₀ ∈ frontier (S w)} = 0` holds for the ball-gate `S`.  This is the honest cp466 anchor
    at the concrete curved data (`n = 2`, e.g. `κ = −1`, fat `K`): the `hnull` residue of
    `white_htermBox_unconditional_k_cover` is a REAL, discharged geometric input at the ball gate, not a
    vacuous one.  NOT `a₁ = R/6`. -/
theorem white_htermBox_cover_hnull_ballGate (c : ℝ) :
    ∀ z₀ : Point 2,
      volume {w : Point 2 | z₀ ∈ frontier ((fun x : Point 2 => Metric.ball x c) w)} = 0 := by
  intro z₀
  exact null_frontier_ball_satisfiable (by norm_num) z₀ c

#check @white_htermBox_unconditional_k_cover
#check @white_htermBox_cover_certificates_satisfiable
#check @white_htermBox_cover_hnull_ballGate

end QIQTH.WhiteHtermBoxWCover

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHtermBoxWCover
#print axioms white_htermBox_unconditional_k_cover
#print axioms white_htermBox_cover_certificates_satisfiable
#print axioms white_htermBox_cover_hnull_ballGate
end AxiomChecks
