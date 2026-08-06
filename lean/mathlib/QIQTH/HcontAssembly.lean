/-
  HcontAssembly — J4-295: the `hcont` ASSEMBLY by STRONG INDUCTION.  The non-circular closure of the
  `iterE` termwise joint-continuity recursion.

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  The OUTER engine
  `IterEEngineWiring.iterE_succ_jointContinuousOn_wired` reduces one recursion rung
      `ContinuousOn (fun p => iterE E (k+1) p.1 p.2 0)  on  Icc t₁ t₂ ×ˢ closedBall 0 R`
  to two per-level carries `hmeas` (discharged from `hEmeas` by
  `InnerEngineRecursion.convStepIntegral_u_aestronglyMeasurable`) and `hcont` (the a.e.-`u` inner joint
  continuity), whose per-fibre content factors — via `InnerEngineRecursion.innerStep_cont_of_slots` — as
      (Gap-A) `E`'s continuity at the SECOND spatial argument `= w`  ·
      (Gap-B) `iterE E k`'s continuity at the FIRST spatial argument `= w`  ·
      (S-dom) a `p`-uniform integrable spatial dominator.
  Trying to feed the ALL-`k` `hcont` at once is CIRCULAR: Gap-B at rung `k` is exactly the level-`k`
  conclusion we are trying to prove.  This file breaks the circle with a plain (single-step) induction.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  regularity / recursion-structure brick.  No `sorry` (this header prose aside), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE INDEX ALIGNMENT (the load-bearing recon).  `iterE` (`QIQTH.LeviSeries.iterE`) is indexed
        `iterE E 0 = E`, `iterE E 1 = E`, `iterE E (k+2) = heatConvK E (iterE E (k+1))`,
     so the recursion step (`iterE_succ`, valid `k ≥ 1`) is `iterE E (k+1) = heatConvK E (iterE E k)`:
     producing rung `k+1` left-convolves `E` against the PREVIOUS term `iterE E k`.  Hence the inner
     integrand that `iterE_succ_jointContinuousOn_wired` (internal level `m`) consumes for output
     `iterE E (m+1)` is `w ↦ E (s−s·u) z w · iterE E m (s·u) w 0`, whose Gap-B factor is the continuity
     of `iterE E m` — i.e. the level-`m` conclusion.  So with the induction predicate
        `P k := ∀ t₁ t₂ R, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
                  ContinuousOn (fun p => iterE E (k+1) p.1 p.2 0) (Icc t₁ t₂ ×ˢ closedBall 0 R)`,
     the step is `P k ⟹ P (k+1)` via `iterE_succ_jointContinuousOn_wired` at internal level `m = k+1`
     (output `iterE E (k+2)`), whose `hcont` Gap-B factor is `iterE E (k+1)`'s continuity = `P k`.  The
     base `P 0` is `iterE E 1 = E`'s continuity (= the banked base slice `hbase`).  The `(t₁,t₂,R)` are
     INSIDE `P k` precisely so the step may re-instantiate `P k` on the SHRUNK time window
     `Icc (t₁·u) (t₂·u)` and on an ENLARGED ball `closedBall 0 (‖w‖+1)` containing the frozen base `w`.

  ── WHAT LANDS (all DERIVED / soundly WIRED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * `iterE_gapB_comp` — THE GAP-B COMPOSITION.  From the level-`m` joint continuity of
        `q ↦ iterE E m q.1 q.2 0` on the SHRUNK slab `Icc (t₁·u) (t₂·u) ×ˢ closedBall 0 R'`, and any
        frozen base `w ∈ closedBall 0 R'`, obtain the continuity of `p ↦ iterE E m (p.1·u) w 0` on
        `Icc t₁ t₂ ×ˢ closedBall 0 R` (for `0 ≤ u`).  Pure `ContinuousOn.comp` through the continuous,
        `MapsTo` affine section `p ↦ (p.1·u, w)`.  This is what turns the induction hypothesis into the
        engine's Gap-B (`hcontIter`) slot — NO extra carry.

    * `iterE_jointContinuousOn_strong` — THE STRONG-INDUCTION CLOSURE.  `∀ k, P k`, i.e. `∀ k, ∀ t₁ t₂ R,
        0 < t₁ → t₁ ≤ t₂ → 0 < R → ContinuousOn (fun p => iterE E (k+1) p.1 p.2 0)`, from ONLY the banked
        outer bounds (`hEbound`/`hInt`/`hEmeas`), the base slice `hbase` (= `P 0` = G1 at `w = 0`), and
        the two GENUINE per-rung analytic carries Gap-A (`hGapA`) + S-dom (`hSdom`).  Gap-B is discharged
        INTERNALLY from the induction hypothesis by `iterE_gapB_comp`; the `hmeas` slot is discharged
        from `hEmeas`.  Non-circular by construction.

    * `leviSlice_jointContinuousOn_of_strong` — (M-test stretch) the joint `(s,z)`-continuity of the
        FULL Levi `0`-slice `p ↦ leviSeries E p.1 p.2 0` on the compact, obtained by feeding the strong
        induction's per-`k` continuity (times the harmless `(-1)^(k+1)` scalar) as the `hterm` argument
        of `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise`, under a summable termwise
        envelope (`hu`/`hbound`).  This is the `hf_cont`-shaped capstone the assembly consumes.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
     The two GENUINE per-rung analytic carries of `iterE_jointContinuousOn_strong`, neither the
     conclusion and each satisfiable:
       • (Gap-A) `hGapA` — for a.e. `u`, a.e. `w`, the joint `(s,z)`-continuity of
         `(s,z) ↦ E (s−s·u) z w` — `E` evaluated at the GENERAL second spatial argument `w`
         (the integration variable, ranging over ALL of space).  Satisfiable: the frozen-base Gap-A
         cover `GapACoverGapB.heatOpWitness_fixedBase_originBall` (near `w`) /
         `heatOpWitness_fixedBase_originBall_far` (far `w`), composed through
         `GapACoverGapB.continuousOn_timeAffine_comp` for the `(s−s·u)` time argument — a ∀`w` active
         bank, NOT discharged here.
       • (S-dom) `hSdom` — for each rung `m` a `p`-uniform integrable spatial dominator of
         `w ↦ E (s−s·u) z w · iterE E m (s·u) w 0`.  Satisfiable: on the active region the residual's
         support is `‖z−w‖ ≤ √(3/2)·b` (`ZeroCollarLocalZero`), so `w ∈ closedBall 0 (R+√(3/2)·b)`; the
         fixed-`u` Gaussian majorant is bounded by its diagonal value (`gaussDdim_le_diagonal`), giving a
         constant · indicator dominator — NOT constructed here.
     The M-test feed additionally carries the summable termwise envelope (`hu`/`hbound`), satisfiable
     from the `iterConvW`/Gamma-ratio bound.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InnerEngineRecursion
import QIQTH.IterEEngineWiring
import QIQTH.MovingCorrAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.GaussianWidthTolerant QIQTH.InnerEngineRecursion QIQTH.IterEEngineWiring
open QIQTH.MovingCorrAssembly
open scoped Topology

namespace QIQTH.HcontAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## The Gap-B composition — the induction hypothesis becomes the engine's `hcontIter` slot.
    ############################################################################### -/

/-- **★★ `iterE_gapB_comp` — THE GAP-B COMPOSITION.**  Fix a level `m`, a reparametrization factor
    `0 ≤ u`, and a frozen base `w ∈ closedBall 0 R'`.  From the level-`m` JOINT continuity of
    `q ↦ iterE E m q.1 q.2 0` on the SHRUNK slab `Icc (t₁·u) (t₂·u) ×ˢ closedBall 0 R'`, obtain the
    continuity of the `z`-free, time-reparametrized slice `p ↦ iterE E m (p.1·u) w 0` on
    `Icc t₁ t₂ ×ˢ closedBall 0 R`.  The affine section `p ↦ (p.1·u, w)` is continuous and `MapsTo`
    (`t₁ ≤ p.1 ≤ t₂`, `0 ≤ u` gives `t₁·u ≤ p.1·u ≤ t₂·u`; the spatial slot is the constant `w ∈
    closedBall 0 R'`), so `ContinuousOn.comp` closes it.  This is EXACTLY the engine's Gap-B slot
    (`InnerEngineRecursion.innerStep_cont_of_slots`'s `hcontIter`) produced from the induction
    hypothesis — NO extra carry.  NOT `a₁ = R/6`. -/
theorem iterE_gapB_comp
    (E : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ) (hu : 0 ≤ u)
    {t₁ t₂ R R' : ℝ} (w : Point n) (hw : w ∈ Metric.closedBall (0 : Point n) R')
    (hIH : ContinuousOn (fun q : ℝ × Point n => iterE E m q.1 q.2 0)
      (Set.Icc (t₁ * u) (t₂ * u) ×ˢ Metric.closedBall (0 : Point n) R')) :
    ContinuousOn (fun p : ℝ × Point n => iterE E m (p.1 * u) w 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hcont : Continuous (fun p : ℝ × Point n => (p.1 * u, w)) :=
    (continuous_fst.mul continuous_const).prodMk continuous_const
  have hmaps : Set.MapsTo (fun p : ℝ × Point n => (p.1 * u, w))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)
      (Set.Icc (t₁ * u) (t₂ * u) ×ˢ Metric.closedBall (0 : Point n) R') := by
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
    obtain ⟨⟨h1, h2⟩, _hz⟩ := hp
    exact ⟨⟨mul_le_mul_of_nonneg_right h1 hu, mul_le_mul_of_nonneg_right h2 hu⟩, hw⟩
  exact hIH.comp hcont.continuousOn hmaps

/-! ###############################################################################
    ## The strong-induction closure — `∀ k, P k`, Gap-B discharged internally.
    ############################################################################### -/

/-- **★★★ `iterE_jointContinuousOn_strong` — THE STRONG-INDUCTION CLOSURE.**  For every level `k` and
    every positive-time compact `Icc t₁ t₂ ×ˢ closedBall 0 R`, the iterated residual slice
    `p ↦ iterE E (k+1) p.1 p.2 0` is jointly `ContinuousOn`, from ONLY:

    * the banked outer bounds `hEbound` (width-`κ` one-step residual bound), `hInt`
      (`IterConvIntegrableW`), `hEmeas` (base joint measurability);
    * `hbase` — the base slice `p ↦ E p.1 p.2 0` continuity on every positive-time compact (= `P 0`,
      the G1 cover at `w = 0`);
    * `hGapA` — (Gap-A) for a.e. `u`, a.e. `w`, `(s,z) ↦ E (s−s·u) z w` continuity;
    * `hSdom` — (S-dom) for each rung a `p`-uniform integrable spatial dominator.

    Gap-B (the engine's `hcontIter` slot) is discharged INTERNALLY from the induction hypothesis via
    `iterE_gapB_comp` (instantiated on the shrunk window `Icc (t₁·u) (t₂·u)` and the ball
    `closedBall 0 (‖w‖+1)` ∋ `w`); the `hmeas` slot from `hEmeas`
    (`convStepIntegral_u_aestronglyMeasurable`).  Plain single-step `Nat` induction — non-circular.
    None of `hGapA`/`hSdom` is the conclusion.  NOT `a₁ = R/6`. -/
theorem iterE_jointContinuousOn_strong
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW E κ 0 C)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (hbase : ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ContinuousOn (fun p : ℝ × Point n => E p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hGapA : ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
        ∀ᵐ w ∂volume, ContinuousOn
          (fun p : ℝ × Point n => E (p.1 - p.1 * u) p.2 w)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hSdom : ∀ (m : ℕ), 1 ≤ m → ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ∃ bnd : ℝ → Point n → ℝ,
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), Integrable (bnd u) volume) ∧
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
            ∀ᵐ w ∂volume,
              ‖E (p.1 - p.1 * u) p.2 w * iterE E m (p.1 * u) w 0‖ ≤ bnd u w)) :
    ∀ k : ℕ, ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro k
  induction k with
  | zero =>
      -- `iterE E (0+1) = iterE E 1 = E` (definitional); the base slice `hbase` = `P 0`.
      intro t₁ t₂ R h1 h2 h3
      exact hbase t₁ t₂ R h1 h2 h3
  | succ k ih =>
      -- Output `iterE E (k+2)` via the OUTER step at internal level `m = k+1`.
      intro t₁ t₂ R h1 h2 h3
      have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      obtain ⟨bnd, hbnd_int, hbound⟩ := hSdom (k + 1) hk1 t₁ t₂ R h1 h2 h3
      -- Gap-B: the a.e.-`u`, a.e.-`w` `hcontIter` slot, from the induction hypothesis `ih` (= `P k`).
      have hGapB : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ∀ᵐ w ∂volume, ContinuousOn
            (fun p : ℝ × Point n => iterE E (k + 1) (p.1 * u) w 0)
            (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        refine ae_of_all _ (fun w => ?_)
        have hu0 : 0 < u := hu.1
        have hwmem : w ∈ Metric.closedBall (0 : Point n) (‖w‖ + 1) := by
          rw [mem_closedBall_zero_iff]; linarith
        exact iterE_gapB_comp E (k + 1) u hu0.le w hwmem
          (ih (t₁ * u) (t₂ * u) (‖w‖ + 1) (mul_pos h1 hu0)
            (mul_le_mul_of_nonneg_right h2 hu0.le) (by positivity))
      -- Assemble the `hcont` slot per fibre and feed the OUTER step.
      refine iterE_succ_jointContinuousOn_wired E κ C hκ hC hk1 t₁ t₂ R h1 hEbound hInt
        (fun p _hp => convStepIntegral_u_aestronglyMeasurable E hk1 hEmeas p)
        (innerStep_cont_ae E hk1 t₁ t₂ R bnd hEmeas hbnd_int hbound
          (hGapA t₁ t₂ R h1 h2 h3) hGapB)

/-! ###############################################################################
    ## (M-test stretch) The full Levi `0`-slice joint continuity.
    ############################################################################### -/

/-- **★★ `leviSlice_jointContinuousOn_of_strong` — the `hf_cont`-shaped M-test capstone.**  The joint
    `(s,z)`-continuity of the FULL Levi `0`-slice `p ↦ leviSeries E p.1 p.2 0` on a positive-time
    compact, obtained by feeding the strong induction's per-`k` continuity (times the harmless
    `(-1)^(k+1)` sign) as the `hterm` argument of
    `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise`, under a summable termwise envelope
    (`hu`/`hbound`).  Carries the two per-rung analytic carries of the strong induction plus the
    summable envelope; none is the conclusion.  NOT `a₁ = R/6`. -/
theorem leviSlice_jointContinuousOn_of_strong
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) (hR : 0 < R)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW E κ 0 C)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (hbase : ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ContinuousOn (fun p : ℝ × Point n => E p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hGapA : ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
        ∀ᵐ w ∂volume, ContinuousOn
          (fun p : ℝ × Point n => E (p.1 - p.1 * u) p.2 w)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hSdom : ∀ (m : ℕ), 1 ≤ m → ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ∃ bnd : ℝ → Point n → ℝ,
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), Integrable (bnd u) volume) ∧
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
            ∀ᵐ w ∂volume,
              ‖E (p.1 - p.1 * u) p.2 w * iterE E m (p.1 * u) w 0‖ ≤ bnd u w))
    (env : ℕ → ℝ) (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0‖ ≤ env k) :
    ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hstrong := iterE_jointContinuousOn_strong E κ C hκ hC hEbound hInt hEmeas hbase hGapA hSdom
  have hterm : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × Point n => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    fun k => continuousOn_const.mul (hstrong k t₁ t₂ R ht₁ ht₁₂ hR)
  exact leviSlice_jointContinuousOn_of_termwise E t₁ t₂ R env hterm hu hbound

#check @iterE_gapB_comp
#check @iterE_jointContinuousOn_strong
#check @leviSlice_jointContinuousOn_of_strong

end QIQTH.HcontAssembly

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HcontAssembly
#print axioms iterE_gapB_comp
#print axioms iterE_jointContinuousOn_strong
#print axioms leviSlice_jointContinuousOn_of_strong
end AxiomChecks
