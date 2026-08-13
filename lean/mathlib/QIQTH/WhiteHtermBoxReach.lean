/-
  WhiteHtermBoxReach — J4-709: THE THREE-ROUTE SCOPING VERDICT + THE (α) PER-LEVEL STITCH.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE WALL (J4-708, e0c8050b).  `WhiteHtermBoxUncond.white_htermBox_unconditional_k` lifts the
     reach-`R` flow-ball box continuity of `iterE (whiteDefectKernel …) (k+1)` to ALL radii `R'` via
     the group-8 off-gate certificate `{U, hUopen, hEoffFirst (all-`w`), hcover}`.  J4-707/708 proved
     that group-8 is JOINTLY UNSATISFIABLE at the concrete flow gate: the succ branch applies
     `hEoffFirst τ z w = 0` at a GENERAL right node `w` (the integration variable), so it needs
     `whiteDefectKernel τ z w = 0` for `z ∈ U` at EVERY `w`, i.e. `U ∩ ⋃_w S w = ∅`; but `⋃_w S w`
     is unbounded at the flow gate, so no open `U` with `hcover : ∀ R', B̄ R' ⊆ B R ∪ U` exists.

  ── THE THREE-ROUTE SCOPING VERDICT (all three READ to their consumer use-sites).
     (γ) CONSUMER TOLERANCE — **DEAD / mismatch REAL.**  The `htermBox` chain
         `leviJoint_window_of_carries_width` → `leviSeries_stripContOn_width` →
         `JointContinuityAtoms.stripContOn_of_boxes` covers the Levi strip `Ioc 0 u ×ˢ univ`, and
         `stripContOn_of_boxes` (JointContinuityAtoms.lean:102) instantiates the box radius at
         `R := ‖p.2‖ + 1` for EVERY `p.2 ∈ univ` — UNBOUNDED.  The spatial `univ` is genuinely needed:
         the downstream `WhiteHcontWitnessFactor.leviTimeCont_of_jointStrip` extracts the `z`-slice
         time-continuity for a.e. `z` over ALL of `Point n` (the `∫ z` integration variable).  There is
         NO fixed radius `R₀`; the consumer uses `∀ R'`.  Route (γ) cannot drop group-8.
     (α) PER-LEVEL RADIUS — **DEAD at the concrete flow gate, but with a SATISFIABLE per-`k` stitch.**
         For FIXED `k`, `WhiteHtermBoxW0.whiteDefectKernel_leftNode_offGate_zero` gives
         `iterE E (k+1) τ p 0 = 0` for `M + k·ρ < ‖p‖` (bounded support, radius GROWING in `k`), from
         the SATISFIABLE certs `{S 0 ⊆ B̄(0,M), ∀ z, S z ⊆ B̄(z,ρ)}`.  Combined with reach-`R`
         flow-ball continuity, the all-radii lift closes via the open cover `{‖·‖ > M+k·ρ}` PROVIDED
         `M + k·ρ < R` (so the annulus `R < ‖p‖ ≤ M+k·ρ` is empty).  This is the SATISFIABLE replacement
         for group-8 — but only per-`k`: the UNIFORM `∀ k, M+k·ρ < R` is UNSATISFIABLE for `ρ > 0`,
         `R` bounded (`uniform_reach_bound_unsat` below).  At the concrete gate `R` is the bounded
         van-Vleck / injectivity reach, so the annulus is nonempty for `k > (R−M)/ρ`.  DEAD uniformly.
     (β) REACH EXTENSION — **the genuine route, deferred (multi-brick).**  Continuity at large `p`
         follows from a flow-ball at a DIFFERENT base `q` near `p` (the Gap-A geometry is base-`q`
         general); a finite subcover of the compact annulus `[R, M+k·ρ]` by base-`q` charts would supply
         the missing continuity.  But the per-level engine `white_innerStep_hcont` takes its `hbase` at a
         FIXED base/reach; a finite-cover continuity engine is a substantial multi-brick effort, not this
         brick.  NOTED, not built.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).  The (α) per-level stitch,
     replacing the UNSATISFIABLE group-8 by the SATISFIABLE support certs, and pinning the wall to a
     single explicit uniform reach bound:
    • `contOn_allRadii_of_supportRadius` — the GENERIC stitch: joint continuity on `Icc s₁ s₂ ×ˢ B̄ R`
      + `g ≡ 0` beyond a support radius `Msup < R` ⟹ joint continuity on `Icc s₁ s₂ ×ˢ B̄ R'` for ALL
      `R'` (the open cover `{‖·‖ > Msup}`, via the banked `contOn_prod_extend_of_zeroOn`).
    • `iterConvStep_leftNode_offGate_zero` — ★ the SUCC-BRANCH integrand vanishing (generic `E`):
      `∫ w, E (t−s) p w · iterE E (m+1) s w 0 = 0` for `M + (m+1)·ρ < ‖p‖`, from base support `M` +
      reach `ρ` — the reusable piece a future full support-brick re-induction needs in its succ branch
      (head `E` killed for `w` far, tail `iterE` killed by `iterE_leftNode_offGate_zero` for `w` near `p`).
    • `white_htermBox_perlevel_allRadii_of_reach` — ★★★ the (α) PER-LEVEL box continuity at ALL radii
      for FIXED `k`, from the reach-`R` base continuity `hbaseR` (labelled), the SATISFIABLE support
      certs `{S 0 ⊆ B̄ M, ∀ z S z ⊆ B̄(z,ρ)}`, and the per-`k` reach bound `M + k·ρ < R` — group-8 GONE,
      replaced by the satisfiable support certs.
    • `white_htermBox_perlevel_satisfiable` — cp466: the per-`k` package
      `{S 0 ⊆ B̄ M, ∀ z S z ⊆ B̄(z,ρ), M+k·ρ < R}` is jointly INHABITED (`S z = ball z 1`, `M=ρ=1`,
      `R = k+2`) — non-vacuous per `k`.
    • `uniform_reach_bound_unsat` — ★ THE WALL, PRECISELY: for `ρ > 0` the UNIFORM `∀ k, M+k·ρ < R` is
      UNSATISFIABLE (the support radius `M+k·ρ → ∞` overruns any bounded reach `R`).

  ⚠  HONEST FIREWALL.  Three-route scoping + the (α) per-level stitch + the exact wall lemma ONLY.
  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` is a labelled carrier,
  untouched).  The per-level statement is CONDITIONAL on the reach bound `M+k·ρ < R`, satisfiable per
  `k` but not uniformly at the bounded concrete reach — the mismatch is characterized, NOT papered
  over.  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  hypothesis equal to (or trivially yielding) the conclusion, no existing file edited, nothing
  committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.
-/
import Mathlib
import QIQTH.WhiteHtermBoxW0
import QIQTH.WhiteHtermBoxUncond

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open QIQTH.WhiteHtermBoxW0 QIQTH.WhiteHtermBoxUncond
open scoped Topology

namespace QIQTH.WhiteHtermBoxReach

variable {n : ℕ}

/-! ###############################################################################
    ### §A — the GENERIC bounded-support all-radii stitch.
    ############################################################################### -/

/-- **`contOn_allRadii_of_supportRadius`.**  If `g : ℝ × Point n → ℝ` is jointly `ContinuousOn`
    `Icc s₁ s₂ ×ˢ closedBall 0 R` and vanishes wherever the spatial coordinate has norm `> Msup` for
    some support radius `Msup < R`, then `g` is jointly `ContinuousOn Icc s₁ s₂ ×ˢ closedBall 0 R'`
    for EVERY `R'`.  The open cover is `U = {p | Msup < ‖p‖}` (the complement of `closedBall 0 Msup`):
    `Msup < R` makes `closedBall 0 R' ⊆ ball 0 R ∪ U`.  Via the banked
    `WhiteHtermBoxUncond.contOn_prod_extend_of_zeroOn`.  NOT `a₁ = R/6`. -/
theorem contOn_allRadii_of_supportRadius (g : ℝ × Point n → ℝ) (s₁ s₂ R Msup : ℝ)
    (hMsupR : Msup < R)
    (hzero : ∀ p : ℝ × Point n, Msup < ‖p.2‖ → g p = 0)
    (hR : ContinuousOn g (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ R' : ℝ, ContinuousOn g (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  intro R'
  refine contOn_prod_extend_of_zeroOn g s₁ s₂ R R' {p : Point n | Msup < ‖p‖}
    (isOpen_lt continuous_const continuous_norm) hzero hR ?_
  intro x hx
  by_cases hxR : ‖x‖ < R
  · exact Or.inl (by rw [Metric.mem_ball, dist_zero_right]; exact hxR)
  · exact Or.inr (by show Msup < ‖x‖; linarith [not_lt.mp hxR])

/-! ###############################################################################
    ### §B — ★ the succ-branch convolution-integrand vanishing (generic `E`).
    ############################################################################### -/

/-- **★ `iterConvStep_leftNode_offGate_zero`.**  The succ-branch Duhamel integrand of the left-node-`0`
    Levi iterate vanishes for the OUTER left node `p` far: given a right-node-`0` base support radius
    `M` (`E τ z 0 = 0` for `M < ‖z‖`) and a uniform gate reach `ρ` (`E τ p z = 0` for `‖z‖+ρ < ‖p‖`),
        `∫ w, E (t − s) p w · iterE E (m+1) s w 0 = 0`   whenever   `M + (m+1)·ρ < ‖p‖`.
    Per `w`: if `‖w‖ ≤ M + m·ρ` the head `E (t−s) p w` vanishes (`‖w‖+ρ ≤ M+(m+1)ρ < ‖p‖`, `reach`);
    else the tail `iterE E (m+1) s w 0` vanishes (`iterE_leftNode_offGate_zero`, `‖w‖ > M+m·ρ`).  So the
    integrand is identically `0` and `∫ w = 0` with NO integrability side conditions.  This is exactly
    the vanishing a future support-brick re-induction consumes in its succ off-gate extension (the
    SATISFIABLE replacement for the all-`w` group-8 `hEoffFirst`).  NOT `a₁ = R/6`. -/
theorem iterConvStep_leftNode_offGate_zero (E : ℝ → Point n → Point n → ℝ) (M ρ : ℝ)
    (hbase : ∀ (τ : ℝ) (z : Point n), M < ‖z‖ → E τ z 0 = 0)
    (hreach : ∀ (τ : ℝ) (p z : Point n), ‖z‖ + ρ < ‖p‖ → E τ p z = 0) :
    ∀ (m : ℕ) (t s : ℝ) (p : Point n), M + ((m : ℝ) + 1) * ρ < ‖p‖ →
      (∫ w, E (t - s) p w * iterE E (m + 1) s w 0) = 0 := by
  intro m t s p hp
  have hz0 : ∀ w : Point n, E (t - s) p w * iterE E (m + 1) s w 0 = 0 := by
    intro w
    by_cases hwle : ‖w‖ ≤ M + (m : ℝ) * ρ
    · have hpw : ‖w‖ + ρ < ‖p‖ := by
        have hsplit : M + ((m : ℝ) + 1) * ρ = M + (m : ℝ) * ρ + ρ := by ring
        rw [hsplit] at hp; linarith
      rw [hreach (t - s) p w hpw, zero_mul]
    · rw [iterE_leftNode_offGate_zero E M ρ hbase hreach m s w (not_le.mp hwle), mul_zero]
  simp only [hz0, MeasureTheory.integral_zero]

/-! ###############################################################################
    ### §C — ★★★ the (α) PER-LEVEL all-radii box continuity (group-8 replaced).
    ############################################################################### -/

/-- **★★★ `white_htermBox_perlevel_allRadii_of_reach` — THE (α) PER-LEVEL STITCH.**  For a FIXED level
    `k`, the whitened `iterE (whiteDefectKernel …) (k+1)` termwise box continuity extends from the
    reach-`R` flow-ball box `Icc s₁ s₂ ×ˢ B̄ R` (the labelled base continuity `hbaseR`) to ALL radii
    `R'`, using the SATISFIABLE support certificates
        `hMbound : S 0 ⊆ B̄(0,M)`   and   `hreach : ∀ z, S z ⊆ B̄(z,ρ)`
    (via `WhiteHtermBoxW0.whiteDefectKernel_leftNode_offGate_zero`, giving `iterE … (k+1) τ p 0 = 0`
    for `M+k·ρ < ‖p‖`) and the per-`k` reach bound `M + k·ρ < R`.  The group-8 off-gate certificate
    (`{U, hUopen, hEoffFirst (all-`w`), hcover}`, JOINTLY UNSATISFIABLE at the flow gate) is GONE,
    replaced by the satisfiable support certs.  ⚠ CONDITIONAL on the per-`k` reach bound `M+k·ρ < R`
    (satisfiable per `k`, NOT uniformly — `uniform_reach_bound_unsat`).  NOT `a₁ = R/6`. -/
theorem white_htermBox_perlevel_allRadii_of_reach (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b M ρ R : ℝ) (k : ℕ) (s₁ s₂ : ℝ)
    (hMbound : S 0 ⊆ Metric.closedBall (0 : Point n) M)
    (hreach : ∀ z : Point n, S z ⊆ Metric.closedBall z ρ)
    (hlt : M + (k : ℝ) * ρ < R)
    (hbaseR : ContinuousOn
        (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ R' : ℝ, ContinuousOn
        (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  refine contOn_allRadii_of_supportRadius _ s₁ s₂ R (M + (k : ℝ) * ρ) hlt ?_ hbaseR
  intro p hp2
  exact whiteDefectKernel_leftNode_offGate_zero κ hκ hKc S a b M ρ hMbound hreach k p.1 p.2 hp2

/-! ###############################################################################
    ### §D — cp466 satisfiability of the per-`k` package + THE WALL lemma.
    ############################################################################### -/

/-- **`white_htermBox_perlevel_satisfiable`** (cp466 discipline).  For EVERY fixed level `k`, the
    per-`k` stitch package `{S 0 ⊆ B̄(0,M), ∀ z, S z ⊆ B̄(z,ρ), M+k·ρ < R}` is jointly INHABITED —
    witnessed at the bounded gate `S z = ball z 1` (`M = ρ = 1`, `R = k+2`): `1 + k·1 = k+1 < k+2`.
    So the (α) per-level conditional is not vacuously conditional at any fixed `k`.  NOT `a₁ = R/6`. -/
theorem white_htermBox_perlevel_satisfiable (k : ℕ) :
    ∃ (S : Point n → Set (Point n)) (M ρ R : ℝ),
      S 0 ⊆ Metric.closedBall (0 : Point n) M ∧
      (∀ z : Point n, S z ⊆ Metric.closedBall z ρ) ∧
      M + (k : ℝ) * ρ < R := by
  refine ⟨fun z => Metric.ball z 1, 1, 1, (k : ℝ) + 2,
    Metric.ball_subset_closedBall, fun z => Metric.ball_subset_closedBall, ?_⟩
  rw [mul_one]; linarith

/-- **★ `uniform_reach_bound_unsat` — THE WALL, PRECISELY.**  For any `ρ > 0`, the UNIFORM reach bound
    `∀ k : ℕ, M + k·ρ < R` is UNSATISFIABLE: the growing support radius `M + k·ρ → ∞` overruns any
    bounded reach `R`.  This is the exact obstruction to promoting the (α) per-level stitch
    (`white_htermBox_perlevel_allRadii_of_reach`, satisfiable per `k`) to the uniform `∀ k` `htermBox`
    that the Levi consumer wants — the continuity-reach (bounded `R`) vs support-growth (`M+k·ρ`)
    mismatch, in one line.  NOT `a₁ = R/6`. -/
theorem uniform_reach_bound_unsat (M ρ R : ℝ) (hρ : 0 < ρ) :
    ¬ (∀ k : ℕ, M + (k : ℝ) * ρ < R) := by
  intro h
  obtain ⟨k, hk⟩ := exists_nat_gt ((R - M) / ρ)
  have h1 : M + (k : ℝ) * ρ < R := h k
  have h2 : R - M < (k : ℝ) * ρ := by rw [div_lt_iff₀ hρ] at hk; linarith
  linarith

#check @contOn_allRadii_of_supportRadius
#check @iterConvStep_leftNode_offGate_zero
#check @white_htermBox_perlevel_allRadii_of_reach
#check @white_htermBox_perlevel_satisfiable
#check @uniform_reach_bound_unsat

end QIQTH.WhiteHtermBoxReach

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHtermBoxReach
#print axioms contOn_allRadii_of_supportRadius
#print axioms iterConvStep_leftNode_offGate_zero
#print axioms white_htermBox_perlevel_allRadii_of_reach
#print axioms white_htermBox_perlevel_satisfiable
#print axioms uniform_reach_bound_unsat
end AxiomChecks
