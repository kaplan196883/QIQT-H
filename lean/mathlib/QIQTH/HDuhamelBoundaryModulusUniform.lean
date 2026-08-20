/-
  HDuhamelBoundaryModulusUniform — discharge of the `hmod`, `hsup` and `hUfloor` census binders of the
  LIVE order-1 `hDuhamel` capstone (`HDuhamelLiveGateWired.hDuhamel_live_gate_wired`) via Heine–Cantor
  uniform continuity of the Levi `0`-slice.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure COMPOSITION / find-and-wire brick.  It discharges three census binders of the shared
  frozen/moving boundary-locally-uniform pile:

    • `hsup`   — the joint-`(u,z)` time-shift uniform convergence
        `∀ ε>0, ∀ᶠ m, ∀ u ∈ [ta,tb], ∀ z ∈ closedBall 0 ρ, |F (u − εₘ) z 0 − F u z 0| < ε`,
      obtained DIRECTLY from the banked Heine–Cantor provider
      `EnvelopeWiringLocUnif.heine_timeShift_sup_tendsto_tUniform` fed the Levi-`0`-slice joint
      continuity on the compact strip.

    • `hmod`   — the spatial modulus of continuity at `z = 0`, uniform over `u ∈ [ta,tb]`
        `∀ ε>0, ∃ δ>0, ∀ u ∈ [ta,tb], ∀ z ∈ ball 0 δ, |F u z 0 − F u 0 0| < ε`,
      obtained from the NEW general Heine–Cantor spatial-modulus lemma `heine_spatialModulus_at_zero`
      (built here, mirroring the banked time-shift proof) fed the SAME compact-strip slice continuity.

    • `hUfloor` — the positive window floor `∃ c>0, ∀ u ∈ U, c ≤ u`, which the LIVE census already
      carries VERBATIM as the sibling triple `⟨aT, haT, hUlb⟩` (`aT>0`, `∀ u∈U, aT ≤ u`).  This is the
      audit's `D` "trivial window fact" (`DataPileWitnessAudit.lean:47`); we bank the honest one-line
      implication `hUfloor_of_windowFloor`.

  Both `hmod` and `hsup` reduce to a SINGLE named satisfiable carrier — the Levi-`0`-slice joint
  continuity `ContinuousOn (fun p => F p.1 p.2 0) (Icc t₁ t₂ ×ˢ closedBall 0 R)` — and, at the concrete
  witness, that carrier is the banked `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise`
  (reducing further to `{termwise iterE joint continuity, summable envelope, envelope bound}`).  This is
  the exact find-and-wire pattern of J4-896..902.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.
  ⚠  STILL NOT `a₁ = R/6`.
-/
import QIQTH.EnvelopeWiringLocUnif
import QIQTH.MovingCorrAssembly
import QIQTH.ConvApproximants

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TrueHeatKernel QIQTH.LeviSeries
open QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.HDuhamelBoundaryModulusUniform

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The general Heine–Cantor spatial-modulus lemma (new content).
    ############################################################################### -/

/-- **★★ `heine_spatialModulus_at_zero`.**  From joint continuity of the `0`-slice
    `p ↦ F p.1 p.2 0` on the compact strip `Icc t₁ t₂ ×ˢ closedBall 0 R` (with `[ta,tb] ⊆ [t₁,t₂]`,
    `0 < R`), Heine–Cantor supplies a SINGLE `u`-free modulus `δ` witnessing the spatial modulus of
    continuity at `z = 0`, uniform over `u ∈ [ta,tb]`:
        `∀ ε>0, ∃ δ>0, ∀ u ∈ [ta,tb], ∀ z ∈ ball 0 δ, |F u z 0 − F u 0 0| < ε`.
    This is the EXACT `hmod` census-binder shape.  Route: uniform continuity on the compact strip gives
    a `u`- and `z`-free modulus `δ`; the shift distance `dist ((u,z),(u,0)) = ‖z‖` is `u`-free, so
    `‖z‖ < min δ R` closes it uniformly (the `min` keeps `z` inside the strip's spatial ball).
    Kernel-agnostic.  ⚠ NOT `a₁ = R/6`. -/
theorem heine_spatialModulus_at_zero
    (F : ℝ → Point n → Point n → ℝ) (t₁ t₂ R ta tb : ℝ)
    (hR : 0 < R) (ht₁ta : t₁ ≤ ta) (htab : ta ≤ tb) (htb₂ : tb ≤ t₂)
    (hcont : ContinuousOn (fun p : ℝ × Point n => F p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Set.Icc ta tb, ∀ z ∈ Metric.ball (0 : Point n) δ,
      |F u z 0 - F u 0 0| < ε := by
  have hs : IsCompact (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : Point n) R)
  have huc := hs.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδprop⟩ := huc ε hε
  refine ⟨min δ R, lt_min hδ hR, ?_⟩
  intro u hu z hz
  obtain ⟨hta, htb⟩ := Set.mem_Icc.mp hu
  have huIcc : u ∈ Set.Icc t₁ t₂ :=
    Set.mem_Icc.mpr ⟨le_trans ht₁ta hta, le_trans htb htb₂⟩
  have hzball : dist z (0 : Point n) < min δ R := by
    rw [← Metric.mem_ball]; exact hz
  have hzR : z ∈ Metric.closedBall (0 : Point n) R :=
    Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hzball (min_le_right _ _)))
  have h0R : (0 : Point n) ∈ Metric.closedBall (0 : Point n) R :=
    Metric.mem_closedBall.mpr (by simpa using hR.le)
  have hpmem : (u, z) ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R :=
    Set.mem_prod.mpr ⟨huIcc, hzR⟩
  have hqmem : (u, (0 : Point n)) ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R :=
    Set.mem_prod.mpr ⟨huIcc, h0R⟩
  have hdist : dist ((u, z) : ℝ × Point n) (u, (0 : Point n)) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact lt_of_lt_of_le hzball (min_le_left _ _)
  have hfin := hδprop (u, z) hpmem (u, (0 : Point n)) hqmem hdist
  rw [Real.dist_eq] at hfin
  exact hfin

/-! ###############################################################################
    ### The `hmod` / `hsup` census-binder discharges (abstract `F`).
    ############################################################################### -/

/-- **★★ `hmod_census_of_sliceContinuity`.**  The EXACT `hmod` census binder of
    `HDuhamelLiveGateWired.hDuhamel_live_gate_wired` (`:219-221`) and the shared
    `HDuhamelExportRethread`/`HDerivConvComposition` frozen/moving pile, for ABSTRACT `F`, reduced to
    the single Levi-`0`-slice joint continuity carrier via `heine_spatialModulus_at_zero`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hmod_census_of_sliceContinuity
    (F : ℝ → Point n → Point n → ℝ) (t₁ t₂ R ta tb : ℝ)
    (hR : 0 < R) (ht₁ta : t₁ ≤ ta) (htab : ta ≤ tb) (htb₂ : tb ≤ t₂)
    (hcont : ContinuousOn (fun p : ℝ × Point n => F p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
      ∀ z ∈ Metric.ball (0 : Point n) δ,
        |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε :=
  fun ε hε => heine_spatialModulus_at_zero F t₁ t₂ R ta tb hR ht₁ta htab htb₂ hcont ε hε

/-- **★★ `hsup_census_of_sliceContinuity`.**  The EXACT `hsup` census binder of
    `HDuhamelLiveGateWired.hDuhamel_live_gate_wired` (`:222-224`), for ABSTRACT `F`, obtained DIRECTLY
    from the banked `EnvelopeWiringLocUnif.heine_timeShift_sup_tendsto_tUniform` applied to the
    `0`-slice `fun s z => F s z 0`, fed the same compact-strip slice continuity.  ⚠ NOT `a₁ = R/6`. -/
theorem hsup_census_of_sliceContinuity
    (F : ℝ → Point n → Point n → ℝ) (t₁ t₂ R ρ ta tb : ℝ)
    (hρR : ρ ≤ R) (ht₁ta : t₁ < ta) (htab : ta ≤ tb) (htb₂ : tb ≤ t₂)
    (hcont : ContinuousOn (fun p : ℝ × Point n => F p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
      ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
        |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε :=
  fun ε hε =>
    QIQTH.EnvelopeWiringLocUnif.heine_timeShift_sup_tendsto_tUniform
      (fun s z => F s z 0) t₁ t₂ R ρ ta tb hρR ht₁ta htab htb₂ hcont ε hε

/-! ###############################################################################
    ### The `hUfloor` census-binder discharge (trivial sibling-redundant fact).
    ############################################################################### -/

/-- **`hUfloor_of_windowFloor`.**  The EXACT `hUfloor` census binder
    (`HDuhamelLiveGateWired.lean:176`, `∃ c>0, ∀ u∈U, c ≤ u`) is REDUNDANT with the sibling census
    binders `aT` (`:151`), `haT : 0 < aT` and `hUlb : ∀ u∈U, aT ≤ u` (`:152`), which the same theorem
    already carries.  This is the audit's `D` "trivial window fact" (`DataPileWitnessAudit.lean:47`).
    ⚠ NOT `a₁ = R/6`. -/
theorem hUfloor_of_windowFloor {U : Set ℝ} (aT : ℝ) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u) : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u :=
  ⟨aT, haT, hUlb⟩

/-! ###############################################################################
    ### The CONCRETE-witness discharge: reduce `hmod`/`hsup` to the banked termwise carrier.
    ############################################################################### -/

/-- **★★★ `hmod_hsup_at_witness`.**  BOTH the `hmod` and `hsup` census binders, at the LIVE order-1
    capstone's concrete Levi source `F := leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S
    a b))`, reduced to the banked `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise`
    ingredients `{hterm, hu, hbound}` (termwise `iterE` joint continuity + summable envelope + envelope
    bound) — the exact carriers the moving-correction/boundary assembly already stands on.  The Levi
    source is left ABSTRACT as `E`; instantiate `E := heatOp g gi (vanVleckGatedWitness …)` to hit the
    capstone's own `F` (via its `hFeq`).  ⚠ NOT `a₁ = R/6`. -/
theorem hmod_hsup_at_witness
    (E : ℝ → Point n → Point n → ℝ) (t₁ t₂ R ρ ta tb : ℝ)
    (hR : 0 < R) (hρR : ρ ≤ R) (ht₁ta : t₁ < ta) (htab : ta ≤ tb) (htb₂ : tb ≤ t₂)
    (env : ℕ → ℝ)
    (hterm : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × Point n => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0‖ ≤ env k) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |leviSeries E u z (0 : Point n) - leviSeries E u (0 : Point n) (0 : Point n)| < ε)
    ∧ (∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |leviSeries E (u - epsSeq m) z (0 : Point n) - leviSeries E u z (0 : Point n)| < ε) := by
  have hcont : ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    QIQTH.MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise E t₁ t₂ R env hterm hu hbound
  refine ⟨?_, ?_⟩
  · exact hmod_census_of_sliceContinuity (leviSeries E) t₁ t₂ R ta tb
      hR (le_of_lt ht₁ta) htab htb₂ hcont
  · exact hsup_census_of_sliceContinuity (leviSeries E) t₁ t₂ R ρ ta tb
      hρR ht₁ta htab htb₂ hcont

end QIQTH.HDuhamelBoundaryModulusUniform

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HDuhamelBoundaryModulusUniform
#print axioms heine_spatialModulus_at_zero
#print axioms hmod_census_of_sliceContinuity
#print axioms hsup_census_of_sliceContinuity
#print axioms hUfloor_of_windowFloor
#print axioms hmod_hsup_at_witness
end AxiomChecks
