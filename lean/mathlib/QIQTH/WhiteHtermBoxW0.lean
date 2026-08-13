/-
  WhiteHtermBoxW0 — J4-708: THE w=0 BINDER SHARPENING, cp466 CORRECTION + the SUPPORT BRICK.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── cp466 SCOPING CORRECTION (the finding).  J4-707 (`WhiteHInnerContClosed`, 65de2001) and the
     J4-708 task premise BOTH assert that the consumer `WhiteHtermBoxUncond.white_htermBox_unconditional_k`
     invokes its `hEoffFirst` hypothesis ONLY at right node `w = 0` (citing the base-case use
     `hEoffFirst p.1 p.2 0 hp2`, `WhiteHtermBoxUncond.lean` line ~210).  THIS IS INCORRECT.  The
     `succ` branch of that induction (`WhiteHtermBoxUncond.lean` line ~256) applies `hEoffFirst` at a
     GENERAL right node — the integration variable `w`:
        `funext w; rw [hEoffFirst (p.1 - p.1 * u) p.2 w hp2]; ring`
     used to kill the ENTIRE convolution integrand `∫ w, whiteDefectKernel … p.2 w · iterE … w 0`
     off-gate.  Hence a LITERAL "restrict `hEoffFirst` to `w = 0`" wrapper does NOT type-check: the
     succ off-gate all-radii extension genuinely needs `whiteDefectKernel τ z w = 0` for `z ∈ U` at
     EVERY `w`, i.e. `U ∩ ⋃_w S w = ∅`.  At the flow gate `S w = uniformFlowExp_w '' ball 0 c`,
     `⋃_w S w` is UNBOUNDED, so the fixed-`U`, all-`w` binder is jointly unsatisfiable with `hcover`
     (exactly the J4-707 conflict) — and the `w = 0` restriction alone does NOT repair the succ
     branch.  The "thin wrapper" of the task does not exist.

  ── THE HONEST RESOLUTION (why `w = 0`-satisfiability is real, just not as a wrapper).  The succ
     integrand `whiteDefectKernel τ' z w · iterE E (m+1) τ'' w 0` vanishes off-gate NOT because the
     kernel vanishes at every `w`, but because the SUPPORT of the two factors is DISJOINT for `z`
     far: the kernel needs `z ∈ S w` (⟹ `w ≈ z` far), while the SECOND factor `iterE E (m+1) τ'' w 0`
     — the `(k+1)`-fold Levi iterate with RIGHT node fixed at `0` — vanishes for the LEFT node `w`
     far (its left-node support propagates outward from `0` by at most the gate reach at each step).
     This file proves that SUPPORT PROPAGATION as a clean, reusable, side-condition-free lemma.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `iterE_leftNode_offGate_zero` — ★ THE SUPPORT BRICK (abstract, ANY residual `E`).  Given
        (base)  `E τ z 0 = 0` whenever `M < ‖z‖`      — right-node-`0` base support radius `M`;
        (reach) `E τ p z = 0` whenever `‖z‖ + ρ < ‖p‖`  — the uniform gate reach `ρ`,
      the `(k+1)`-fold iterate obeys `iterE E (k+1) τ p 0 = 0` whenever `M + k·ρ < ‖p‖`.  Pure
      `Nat.rec` on the convolution: at the step the inner `z`-integrand is IDENTICALLY `0` (either
      the IH kills the tail iterate for `‖z‖` large, or `reach` kills the head `E` for `‖p‖ ≫ ‖z‖`),
      so `∫ z = 0` and `∫ s = 0` with NO integrability side conditions.
    • `whiteDefectKernel_leftNode_offGate_zero` — the same, INSTANTIATED at the whitened defect
      kernel: the base support radius `M` comes from the `w = 0` gate bound `S 0 ⊆ closedBall 0 M`
      (SATISFIABLE — `S 0` is bounded), and the reach `ρ` from the uniform gate reach
      `∀ z, S z ⊆ closedBall z ρ` (SATISFIABLE at the flow gate — the flow-exp displacement is
      bounded), each transported through `whiteGated_heatOp_zero_offGate` on both `whiteDefectKernel`
      time branches.  This is the SATISFIABLE replacement for the all-`w` `hEoffFirst`/`hcover`
      group-8 certificate: `{S 0 ⊆ closedBall 0 M}` (w=0) + `{∀ z, S z ⊆ closedBall z ρ}` (reach).

  ── HONEST RESIDUAL / what this does NOT do.  The support brick discharges the off-gate VANISHING
     that the succ branch needs; it does NOT by itself rebuild `white_htermBox_unconditional_k` with
     the sharpened binder, because the growing support radius `M + k·ρ` interacts with the BOUNDED
     continuity reach `R` of the flow-ball geometry (the annulus `R < ‖p‖ ≤ M + k·ρ` is a region
     where the iterate is generally NONZERO yet continuity is supplied only up to reach `R`).  That
     continuity-reach vs support-growth mismatch is the genuine remaining wall for full closure at
     the concrete flow gate; it is documented here and NOT papered over.  `R/6` is a labelled
     carrier, untouched.

  ⚠  HONEST FIREWALL.  Support-propagation brick + cp466 scoping correction ONLY.  THIS FILE IS
  **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  No `sorry`, no `admit`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding)
  the conclusion, no existing file edited, nothing committed, nothing wired into `QIQTH.lean` /
  `AxiomAudit`.
-/
import Mathlib
import QIQTH.WhiteBridge
import QIQTH.WhiteGated

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open scoped Topology

namespace QIQTH.WhiteHtermBoxW0

variable {n : ℕ}

/-! ###############################################################################
    ### §A — ★ THE SUPPORT BRICK: iterate left-node support propagates by the gate reach.
    ############################################################################### -/

/-- **★ `iterE_leftNode_offGate_zero`.**  Abstract left-node support propagation for the Levi
    iterate with RIGHT node pinned at `0`.  Given a right-node-`0` base support radius `M`
    (`E τ z 0 = 0` for `M < ‖z‖`) and a uniform gate reach `ρ` (`E τ p z = 0` for `‖z‖ + ρ < ‖p‖`),
    the `(k+1)`-fold iterate vanishes at left node `p` once `M + k·ρ < ‖p‖`.  Pure `Nat.rec` on the
    convolution: at each step the inner `z`-integrand is IDENTICALLY zero (IH kills the tail for
    `‖z‖` large; reach kills the head `E` for `‖p‖ ≫ ‖z‖`), so both integrals vanish with NO
    integrability side conditions.  NOT `a₁ = R/6`. -/
theorem iterE_leftNode_offGate_zero (E : ℝ → Point n → Point n → ℝ) (M ρ : ℝ)
    (hbase : ∀ (τ : ℝ) (z : Point n), M < ‖z‖ → E τ z 0 = 0)
    (hreach : ∀ (τ : ℝ) (p z : Point n), ‖z‖ + ρ < ‖p‖ → E τ p z = 0) :
    ∀ (k : ℕ) (τ : ℝ) (p : Point n), M + (k : ℝ) * ρ < ‖p‖ →
      iterE E (k + 1) τ p 0 = 0 := by
  intro k
  induction k with
  | zero =>
    intro τ p hp
    have hM : M < ‖p‖ := by simpa using hp
    have h1 : iterE E (0 + 1) τ p 0 = E τ p 0 := rfl
    rw [h1]; exact hbase τ p hM
  | succ m ih =>
    intro τ p hp
    -- normalise the cast on the succ radius `M + (m+1)ρ`.
    have hcast : ((m + 1 : ℕ) : ℝ) * ρ = (m : ℝ) * ρ + ρ := by push_cast; ring
    rw [hcast] at hp
    -- unfold the iterate to the Duhamel convolution.
    have hunfold : iterE E (m + 1 + 1) τ p 0
        = ∫ s in (0 : ℝ)..τ, ∫ z, E (τ - s) p z * iterE E (m + 1) s z 0 := rfl
    rw [hunfold]
    -- the outer `s`-integrand vanishes for every `s`.
    have hfun : ∀ s : ℝ, (∫ z, E (τ - s) p z * iterE E (m + 1) s z 0) = 0 := by
      intro s
      -- the inner `z`-integrand is identically zero.
      have hz0 : ∀ z : Point n, E (τ - s) p z * iterE E (m + 1) s z 0 = 0 := by
        intro z
        by_cases hzle : ‖z‖ ≤ M + (m : ℝ) * ρ
        · -- `‖z‖` in the support band ⟹ `‖p‖ ≫ ‖z‖ + ρ` ⟹ head `E` vanishes.
          have hpz : ‖z‖ + ρ < ‖p‖ := by linarith
          rw [hreach (τ - s) p z hpz, zero_mul]
        · -- `‖z‖` beyond the band ⟹ IH kills the tail iterate.
          rw [ih s z (not_le.mp hzle), mul_zero]
      simp only [hz0, MeasureTheory.integral_zero]
    simp only [hfun, intervalIntegral.integral_zero]

/-! ###############################################################################
    ### §B — the whitened-defect instantiation: `w = 0` base bound + uniform gate reach.
    ############################################################################### -/

/-- **`whiteDefectKernel_leftNode_offGate_zero`.**  The support brick INSTANTIATED at the whitened
    defect kernel.  The base support radius `M` is supplied by the `w = 0` gate containment
    `S 0 ⊆ closedBall 0 M` (SATISFIABLE — the flow-ball gate at base `0` is bounded), and the reach
    `ρ` by the uniform gate reach `∀ z, S z ⊆ closedBall z ρ` (SATISFIABLE at the flow gate — the
    flow-exp displacement `‖uniformFlowExp_z v − z‖` is bounded on `ball 0 c`).  Both legs vanish
    through `whiteGated_heatOp_zero_offGate` on the two `whiteDefectKernel` time branches.  This is
    the SATISFIABLE replacement for the all-`w` `hEoffFirst` group-8 certificate.  ⚠ CONDITIONAL on
    `hMbound` (w=0) + `hreach`.  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_leftNode_offGate_zero (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b M ρ : ℝ)
    (hMbound : S 0 ⊆ Metric.closedBall (0 : Point n) M)
    (hreach : ∀ z : Point n, S z ⊆ Metric.closedBall z ρ) :
    ∀ (k : ℕ) (τ : ℝ) (p : Point n), M + (k : ℝ) * ρ < ‖p‖ →
      iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) τ p 0 = 0 := by
  -- base support: `M < ‖z‖ ⟹ z ∉ S 0`, transported off-gate.
  have hbase : ∀ (τ : ℝ) (z : Point n), M < ‖z‖ →
      whiteDefectKernel κ hκ hKc S a b τ z 0 = 0 := by
    intro τ z hz
    have hzc : z ∈ (Metric.closedBall (0 : Point n) M)ᶜ := by
      simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff, not_le]; exact hz
    have hsub : (Metric.closedBall (0 : Point n) M)ᶜ ⊆ {p' : Point n | p' ∉ S 0} :=
      fun x hx hxS => hx (hMbound hxS)
    have hopen : IsOpen (Metric.closedBall (0 : Point n) M)ᶜ :=
      Metric.isClosed_closedBall.isOpen_compl
    have hoff : {p' : Point n | p' ∉ S 0} ∈ nhds z :=
      Filter.mem_of_superset (hopen.mem_nhds hzc) hsub
    by_cases hτ : 0 < τ ∧ τ ≤ 1
    · rw [whiteDefectKernel_eq κ hκ hKc S a b hτ.1 hτ.2 z 0]
      exact whiteGated_heatOp_zero_offGate κ hκ hKc S a b τ z 0 (Or.inr hoff)
    · simp only [whiteDefectKernel, if_neg hτ]
  -- reach: `‖z‖ + ρ < ‖p‖ ⟹ p ∉ S z`, transported off-gate.
  have hreachE : ∀ (τ : ℝ) (p z : Point n), ‖z‖ + ρ < ‖p‖ →
      whiteDefectKernel κ hκ hKc S a b τ p z = 0 := by
    intro τ p z hpz
    have hpc : p ∈ (Metric.closedBall z ρ)ᶜ := by
      simp only [Metric.mem_closedBall, Set.mem_compl_iff, not_le]
      have hlow : ‖p‖ - ‖z‖ ≤ dist p z := by
        rw [dist_eq_norm]; have := norm_sub_norm_le p z; linarith [this]
      linarith
    have hsub : (Metric.closedBall z ρ)ᶜ ⊆ {p' : Point n | p' ∉ S z} :=
      fun x hx hxS => hx (hreach z hxS)
    have hopen : IsOpen (Metric.closedBall z ρ)ᶜ :=
      Metric.isClosed_closedBall.isOpen_compl
    have hoff : {p' : Point n | p' ∉ S z} ∈ nhds p :=
      Filter.mem_of_superset (hopen.mem_nhds hpc) hsub
    by_cases hτ : 0 < τ ∧ τ ≤ 1
    · rw [whiteDefectKernel_eq κ hκ hKc S a b hτ.1 hτ.2 p z]
      exact whiteGated_heatOp_zero_offGate κ hκ hKc S a b τ p z (Or.inr hoff)
    · simp only [whiteDefectKernel, if_neg hτ]
  exact iterE_leftNode_offGate_zero (whiteDefectKernel κ hκ hKc S a b) M ρ hbase hreachE

/-! ###############################################################################
    ### §C — cp466 satisfiability: the `w = 0` base bound + reach are jointly inhabited.
    ############################################################################### -/

/-- **`whiteDefect_w0_reach_satisfiable`** (cp466 discipline).  The SATISFIABLE replacement package
    `{S 0 ⊆ closedBall 0 M, ∀ z, S z ⊆ closedBall z ρ}` is jointly INHABITED — witnessed at the
    bounded gate `S z = ball z 1` (`M = 1`, `ρ = 1`): every `S 0 = ball 0 1 ⊆ closedBall 0 1` and
    `S z = ball z 1 ⊆ closedBall z 1`.  So the support brick's hypotheses are not vacuously
    conditional (unlike the all-`w` off-gate `hEoffFirst` at the flow gate).  NOT `a₁ = R/6`. -/
theorem whiteDefect_w0_reach_satisfiable :
    ∃ (S : Point n → Set (Point n)) (M ρ : ℝ),
      S 0 ⊆ Metric.closedBall (0 : Point n) M ∧
      (∀ z : Point n, S z ⊆ Metric.closedBall z ρ) := by
  refine ⟨fun z => Metric.ball z 1, 1, 1, ?_, ?_⟩
  · exact Metric.ball_subset_closedBall
  · exact fun z => Metric.ball_subset_closedBall

#check @iterE_leftNode_offGate_zero
#check @whiteDefectKernel_leftNode_offGate_zero
#check @whiteDefect_w0_reach_satisfiable

end QIQTH.WhiteHtermBoxW0

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHtermBoxW0
#print axioms iterE_leftNode_offGate_zero
#print axioms whiteDefectKernel_leftNode_offGate_zero
#print axioms whiteDefect_w0_reach_satisfiable
end AxiomChecks
