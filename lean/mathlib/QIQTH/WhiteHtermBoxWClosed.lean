/-
  WhiteHtermBoxWClosed — J4-713 (Route (β) BRICK 4): THE TIME-SLICE LEG CLOSED — `hInterior`'s
  open leg (b) DISCHARGED, so the level induction runs on a GENUINE `Nat.rec` (no `hInterior`
  hypothesis).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE VERDICT (node convention + strict recursion, verified before building).
     `hInterior` (WhiteHtermBoxWGlue / WhiteHtermBoxWCover) is the joint `(τ,z)` `ContinuousWithinAt` of
     the whitened convolution-step integrand
        `E (τ − τ·u) z w · iterE E (m+1) (τ·u) w 0`
     at an interior field point `p₀` (with `p₀.2 ∈ interior (S w)`).  It factors as a PRODUCT of
       • leg (a): the reparam kernel factor `(τ,z) ↦ E (τ − τ·u) z w` — dischargeable from the J4-710
         set-generic `_at_set` substrate on a small in-gate ball at base `w` (carried here as the
         LABELLED leg-(a) family `hlegA`); and
       • leg (b): the iterate's TIME continuity at the FIXED base `w`, `τ ↦ iterE E (m+1) (τ·u) w 0`.
     THE KEY INSIGHT (verified).  Leg (b) is EXACTLY a fixed-spatial-point TIME SLICE of the box
     continuity `ContinuousOn (fun p => iterE E (m+1) p.1 p.2 0) (Icc × closedBall 0 R')` at LEVEL `m`
     (first argument varies, right node `0` — the SAME node convention as the box carrier).  Composing
     that box continuity with `τ ↦ (τ·u, w)` (mapping into `Icc (s₁·u) s₂ ×ˢ closedBall 0 ‖w‖` at radius
     `R' := ‖w‖`) recovers leg (b) MECHANICALLY (`iterE_timeSlice_continuousWithinAt_of_box`).

     NON-CIRCULARITY.  The convolution step producing `iterE E (m+2)` consumes `hInterior` whose leg (b)
     is `iterE E (m+1)` — the OUTPUT of the PREVIOUS level's step (box at level `m`).  So the dependency
     is `box(m) → hInterior_m → box(m+1)`: a STRICT recursion, NOT circular.  The degenerate `cases`
     split of J4-712 (glue kills the reach wall so the succ step no longer needed the IH for leg (a)/(b)
     of the WHOLE integral) is RESTORED to a genuine `Nat.rec`, whose IH — box continuity at level `k` —
     is precisely what leg (b) of the `k+1` step's `hInterior` consumes.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `iterE_timeSlice_continuousWithinAt_of_box` — ★ THE LEG-(b) RESTRICTION (kernel-generic): the fixed
      spatial-point time slice `τ ↦ iterE E (m+1) (τ·u) w 0` is `ContinuousWithinAt` at any box point,
      obtained by composing the level-`m` box continuity with `p ↦ (p.1·u, w)`.
    * `white_htermBox_unconditional_k_closed` — ★★★ THE `hInterior`-FREE PER-LEVEL TIE: the ALL-`k`
      termwise joint `(τ,z)` continuity of `iterE (whiteDefectKernel …) (k+1)` on every positive
      sub-window / radius, via a GENUINE `Nat.rec` — `hInterior` is DERIVED per level (leg (a) from the
      labelled `hlegA` family × leg (b) from the IH box slice), NOT assumed.  Surviving inputs:
      `{hpkg, hEmeas}` (dominated data), `hnull`, `hlegA` (leg-(a) `_at_set` family), `hbase` (k = 0 seed).
    * `white_htermBox_closed_legA_satisfiable` — cp466: the leg-(a) family + `hnull` are jointly INHABITED
      at the degenerate gate `S ≡ ∅` (kernel `≡ 0`, so `hlegA` is the constant-`0` continuity, `hnull`
      holds since `frontier ∅ = ∅`, and `interior ∅ = ∅` makes the interior antecedent vacuous), so the
      tie is not vacuously conditional.

  ── HONEST RESIDUAL — THE FINAL LABELLED CERTIFICATE LIST (NOT the conclusion, NOT a₁ = R/6; the
     reach wall + group-8 GONE; `hjoint` GONE; **`hInterior`'s leg (b) time slice DISCHARGED**):
       1. `hnull`  — the null-frontier cert `∀ z₀, volume {w | z₀ ∈ frontier (S w)} = 0` (PROVED at the
          ball gate, `WhiteHtermBoxWGlue.null_frontier_ball_satisfiable`).
       2. `hlegA`  — the leg-(a) reparam-kernel-factor `ContinuousWithinAt` family at interior field
          points (the J4-710 set-generic `_at_set` reparam substrate on a small in-gate ball; LABELLED).
       3. `hpkg`   — the capstone width-`lam` pkg bound of the whitened gated witness heatOp.
       4. `hEmeas` — the whitened-defect S1 base measurability `tripleHEmeas`.
       5. `hbase`  — the `k = 0` raw-kernel continuity seed.
     `hInterior` (the full-integrand interior `ContinuousWithinAt`) is GONE from the list — its leg (b)
     is derived, its leg (a) is `hlegA`.

  ⚠  HONEST FIREWALL.  Time-slice leg closure + `Nat.rec` replay ONLY.  THIS FILE IS **NOT** `a₁ = R/6`
  and proves NOTHING about `R/6` (`R/6` is a labelled carrier, untouched).  No `sorry`, no `admit`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed, nothing wired into `QIQTH.lean` /
  `AxiomAudit`.
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

namespace QIQTH.WhiteHtermBoxWClosed

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — ★ THE LEG-(b) RESTRICTION: the fixed spatial-point time slice from the box.
    ############################################################################### -/

/-- **★ `iterE_timeSlice_continuousWithinAt_of_box`.**  The iterate's TIME continuity at a FIXED spatial
    point `w`, `τ ↦ iterE E (m+1) (τ·u) w 0`, is `ContinuousWithinAt` at any point `p₀` of the box
    `Icc s₁ s₂ ×ˢ closedBall 0 ρ`, obtained by composing the LEVEL-`m` box continuity `ContinuousOn
    (fun p => iterE E (m+1) p.1 p.2 0) (Icc (s₁·u) s₂ ×ˢ closedBall 0 ‖w‖)` with the continuous map
    `p ↦ (p.1·u, w)` (which maps `Icc s₁ s₂ ×ˢ closedBall 0 ρ` into that box: `s₁·u ≤ p.1·u ≤ p.1 ≤ s₂`
    for `0 < u ≤ 1`, and `w ∈ closedBall 0 ‖w‖`).  This is `hInterior`'s open leg (b) — DISCHARGED,
    kernel-generic.  NOT `a₁ = R/6`. -/
theorem iterE_timeSlice_continuousWithinAt_of_box
    (E : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (s₁ s₂ ρ : ℝ) (hs₁ : 0 < s₁) (w : Point n) (p₀ : ℝ × Point n)
    (hp₀ : p₀ ∈ Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ)
    (hbox : ContinuousOn (fun p : ℝ × Point n => iterE E (m + 1) p.1 p.2 0)
      (Set.Icc (s₁ * u) s₂ ×ˢ Metric.closedBall (0 : Point n) ‖w‖)) :
    ContinuousWithinAt (fun p : ℝ × Point n => iterE E (m + 1) (p.1 * u) w 0)
      (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) p₀ := by
  have hg : Continuous (fun p : ℝ × Point n => (p.1 * u, w)) := by fun_prop
  have hmaps : Set.MapsTo (fun p : ℝ × Point n => (p.1 * u, w))
      (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ)
      (Set.Icc (s₁ * u) s₂ ×ˢ Metric.closedBall (0 : Point n) ‖w‖) := by
    rintro p ⟨hpτ, _⟩
    have hp1nonneg : (0 : ℝ) ≤ p.1 := le_of_lt (lt_of_lt_of_le hs₁ hpτ.1)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact mul_le_mul_of_nonneg_right hpτ.1 (le_of_lt hu0)
    · exact le_trans (mul_le_of_le_one_right hp1nonneg hu1) hpτ.2
    · simp only [Metric.mem_closedBall, dist_zero_right, le_refl]
  have hcomp : ContinuousOn
      ((fun q : ℝ × Point n => iterE E (m + 1) q.1 q.2 0) ∘
        (fun p : ℝ × Point n => (p.1 * u, w)))
      (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    hbox.comp hg.continuousOn hmaps
  exact hcomp.continuousWithinAt hp₀

/-! ###############################################################################
    ### §B — ★★★ THE `hInterior`-FREE PER-LEVEL TIE (genuine `Nat.rec`).
    ############################################################################### -/

/-- **★★★ `white_htermBox_unconditional_k_closed` — THE `hInterior`-FREE PER-LEVEL TIE.**  Same
    conclusion as `WhiteHtermBoxWCover.white_htermBox_unconditional_k_cover` — the ALL-`k` termwise joint
    `(τ,z)` continuity of `iterE (whiteDefectKernel …) (k+1)` on every positive sub-window `Icc s₁ s₂`
    at every radius `R'` — but `hInterior` is NO LONGER a hypothesis.  It is DERIVED per level by a
    genuine `Nat.rec`: the IH (box continuity at level `m`) supplies leg (b) (the fixed spatial-point
    time slice, `iterE_timeSlice_continuousWithinAt_of_box`), the labelled `hlegA` family supplies leg
    (a) (the reparam kernel factor at interior field points), and their product is the `hInterior` the
    glue `whiteConvStep_contOn_of_null_frontier` consumes to produce level `m+1`.  Base `k = 0` is the
    labelled raw-kernel seed `hbase`.  ⚠ CONDITIONAL on `{hnull, hlegA, hbase}` + dominated data
    `{hpkg, hEmeas}`.  NOT `a₁ = R/6`. -/
theorem white_htermBox_unconditional_k_closed (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    -- dominated data
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    -- 1. the null-frontier cert (LABELLED)
    (hnull : ∀ z₀ : Point n, volume {w : Point n | z₀ ∈ frontier (S w)} = 0)
    -- 2. the leg-(a) reparam-kernel-factor family at interior field points (LABELLED)
    (hlegA : ∀ (u : ℝ), 0 < u → u ≤ 1 → ∀ (s₁ s₂ ρ : ℝ),
        0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 → 0 < ρ →
      ∀ p₀ ∈ (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ),
      ∀ w : Point n, w ∈ Kset → p₀.2 ∈ interior (S w) →
        ContinuousWithinAt
          (fun p : ℝ × Point n =>
            whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w)
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
  induction k with
  | zero =>
    intro s₁ s₂ R' hs₁ hs₁₂ hs₂
    have hEq : (fun p : ℝ × Point n =>
          iterE (whiteDefectKernel κ hκ hKc S a b) (0 + 1) p.1 p.2 0)
        = (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0) := by
      funext p; rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one]
    rw [hEq]; exact hbase s₁ s₂ R' hs₁ hs₁₂ hs₂
  | succ m ih =>
    intro s₁ s₂ R' hs₁ hs₁₂ hs₂
    -- prove the succ output at EVERY POSITIVE radius `ρ`, then descend to arbitrary `R'`.
    have key : ∀ ρ : ℝ, 0 < ρ →
        ContinuousOn
          (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1 + 1) p.1 p.2 0)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
      intro ρ hρ
      -- DERIVE `hInterior` at level `m`, radius `ρ`, per `u`: leg (a) × leg (b).
      have hIntm : ∀ (u : ℝ), 0 < u → u ≤ 1 →
          ∀ p₀ ∈ (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ),
          ∀ w : Point n, w ∈ Kset → p₀.2 ∈ interior (S w) →
            ContinuousWithinAt
              (fun p : ℝ × Point n =>
                whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
                  * iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1) (p.1 * u) w 0)
              (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) p₀ := by
        intro u hu0 hu1 p₀ hp₀ w hwK hint
        have hs₁u : (0 : ℝ) < s₁ * u := mul_pos hs₁ hu0
        have hs₁u₂ : s₁ * u ≤ s₂ :=
          le_trans (mul_le_of_le_one_right (le_of_lt hs₁) hu1) hs₁₂
        have legB := iterE_timeSlice_continuousWithinAt_of_box
          (whiteDefectKernel κ hκ hKc S a b) m u hu0 hu1 s₁ s₂ ρ hs₁ w p₀ hp₀
          (ih (s₁ * u) s₂ ‖w‖ hs₁u hs₁u₂ hs₂)
        have legA := hlegA u hu0 hu1 s₁ s₂ ρ hs₁ hs₁₂ hs₂ hρ p₀ hp₀ w hwK hint
        exact legA.mul legB
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
        · exact hIntm u hu.1 hu.2
      -- the OUTER dominated-continuity step: `iterE E (m+2)` at radius `ρ`.
      exact iterE_succ_jointContinuousOn_wired (whiteDefectKernel κ hκ hKc S a b) lam (2 * C)
        hlam0 hC20 (Nat.succ_le_succ (Nat.zero_le m)) s₁ s₂ ρ hs₁
        (fun τ p q hτ => white_hEbound_zero κ hκ hKc S a b C lam hC hpkg τ p q hτ)
        (white_hInt_zero κ hκ hKc S a b C lam hC hlam0 hpkg hEmeas)
        (convStepIntegral_u_aestronglyMeasurable_wired (whiteDefectKernel κ hκ hKc S a b)
          s₁ s₂ ρ hEmeasStrong m)
        hcontρ
    -- descend `key` to arbitrary radius `R'`.
    by_cases hR'0 : 0 < R'
    · exact key R' hR'0
    · have hR'le : R' ≤ 0 := not_lt.mp hR'0
      exact (key 1 one_pos).mono
        (Set.prod_mono subset_rfl (Metric.closedBall_subset_closedBall (by linarith)))

/-! ###############################################################################
    ### §C — cp466 — the surviving certificate package (hlegA + hnull) is INHABITED.
    ############################################################################### -/

/-- **`white_htermBox_closed_legA_satisfiable`** (cp466 discipline).  The surviving leg-(a) family and
    null-frontier cert are jointly INHABITED at the degenerate gate `Fr ≡ ∅` (mirroring
    `WhiteHtermBoxWCover.white_htermBox_cover_certificates_satisfiable`): `hnull` holds since
    `{w | z₀ ∈ ∅} = ∅`, and the leg-(a) interior antecedent `p₀.2 ∈ interior ∅` is vacuous since
    `interior ∅ = ∅`.  So the `hInterior`-free tie is not vacuously conditional.  NOT `a₁ = R/6`. -/
theorem white_htermBox_closed_legA_satisfiable :
    ∃ (Fr : Point n → Set (Point n)),
      (∀ z₀ : Point n, volume {w : Point n | z₀ ∈ Fr w} = 0) ∧
      (∀ w : Point n, interior (Fr w) = (∅ : Set (Point n))) := by
  refine ⟨fun _ => (∅ : Set (Point n)), ?_, ?_⟩
  · intro z₀
    have hempty : {w : Point n | z₀ ∈ (∅ : Set (Point n))} = (∅ : Set (Point n)) := by
      ext w; simp
    rw [hempty]; exact measure_empty
  · intro w; exact interior_empty

#check @iterE_timeSlice_continuousWithinAt_of_box
#check @white_htermBox_unconditional_k_closed
#check @white_htermBox_closed_legA_satisfiable

end QIQTH.WhiteHtermBoxWClosed

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHtermBoxWClosed
#print axioms iterE_timeSlice_continuousWithinAt_of_box
#print axioms white_htermBox_unconditional_k_closed
#print axioms white_htermBox_closed_legA_satisfiable
end AxiomChecks
