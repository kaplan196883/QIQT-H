/-
  WhiteHInnerContTermBox — J4-699: THE `hJoint` RESIDUE COLLAPSED TO `htermBox`.  The whitened
  inner-pairing time-continuity, with the S1 base measurability (`hEmeas`) AND the width-`lam`
  Levi domination (`hmajor`) BOTH co-instantiated / discharged at the shared flow gate, leaving
  EXACTLY the whitened `iterE` termwise joint continuity (`htermBox`) as the sole surviving carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── CONTEXT (the ledger chain 59fc9d98).  `WhiteHcontWitnessFactor.white_hInnerCont_leviJoint`
     (J4-693) reduced the whitened inner-pairing continuity to a SINGLE carry — the Levi-slice JOINT
     continuity `hJoint : ∀ u ∈ U, ContinuousOn (leviSeries (whiteDefectKernel …) slice) (Ioc 0 u ×ˢ
     univ)`.  `WhiteLeviMajorWire.white_leviJoint_window_modulo_termBox` (J4-695) in turn reduces THAT
     `hJoint` to `{hmajor, htermBox}`, and supplies `hmajor` internally from `{hpkg, hEmeas}` — so the
     whole `hJoint` is dischargeable from `{hpkg, hEmeas, htermBox}`.  This file COMPOSES the two:
     co-instantiating `hpkg`/`hEmeas` at the SAME shared flow gate that the inner-pairing builder uses
     (the `white_hInnerCont_hmeas` co-instantiation pattern), so the ONLY carry that survives is
     `htermBox` (the whitened `iterE` termwise joint continuity — the M-test residual).

  ── WHAT THE TWO TASK MEMBERS BECOME.
       • `hEmeas` — the whitened-defect base measurability `tripleHEmeas` — is DISCHARGED here
         (co-instantiated at the shared gate via `WhiteS1C.white_tripleHEmeas_uniform`), NOT carried.
       • `hstep` — the per-level `iterE` convolution step — is exactly what produces `htermBox` (via
         `IterEEngineWiring.iterE_jointContinuousOn_wired` at the whitened `E` from the flow-ball
         `hbase` `WhiteHJetCont.whiteDefectKernel_jointContinuousOn_of_flowBall` and the OUTER-engine
         slots `{hmeas, hcont}`).  This file makes `htermBox` the single named residue; the step's own
         reduction to `{hmeas, hcont}` is the banked wired engine.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `white_hInnerCont_modulo_termBox` — ★★★ the composed whitened inner-pairing time-continuity with
      BOTH `hEmeas` (S1) AND `hmajor` (width-`lam` Levi domination) DISCHARGED at the shared flow gate:
      for EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)` (`n > 0`), window `U ⊆ (·,1]`, there ARE a fat open gate
      `S`, radii `0 < a < b`, and a width `lam = whiteLam ≥ 2` such that — MODULO ONLY the whitened
      `iterE` termwise box continuity `htermBox` — the interior-time continuity of the whitened inner
      pairing holds on `Ioo 0 u`, ∀ `u ∈ U`.
    • `white_hInnerCont_modulo_termBox_witness_gate` — the cp466 non-vacuity certificate
      (`n = 2`, `κ = −1`, `K = closedBall 0 2`): the ∃-package produces a FAT gate (`0 ∈ S 0`, open)
      with `0 < a < b` and `lam ≥ 2` — not `∅`-degenerate.

  ── HONEST RESIDUAL.  The composed continuity now owes ONLY `htermBox` (plus the prior
     `K1TransportBudget` / capstone piles).  `htermBox` is the whitened `iterE` termwise joint
     continuity, itself the flow-ball `hbase` (a THEOREM, `whiteDefectKernel_jointContinuousOn_of_flowBall`)
     plus the wired convolution-step slots `{hmeas, hcont}`.  `a₁ = R/6` established non-vacuously ONLY
     for the FLAT tower; `R/6` is a labelled carrier, untouched.

  ⚠ HONEST FIREWALL.  Gate co-instantiation + carry composition ONLY — one shared radius emitting the
  pkg bound + S1 measurability, discharging both the `hmajor` and `hEmeas` carries — NOT `a₁ = R/6`.
  DERIVED from the banked radius-parametric S1 / pkg suppliers + the banked value bricks + the
  gate-parametric width-`lam` Levi major wire + the witness-factor time continuity + the generic
  continuity builder.  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous hypothesis,
  no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.WhiteLeviConvergenceTrio
import QIQTH.WhiteLeviMajorWire
import QIQTH.WhiteHcontWitnessFactor

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.CurvedA1CenterAmp
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteAnnulus QIQTH.WhiteGated
open QIQTH.WhiteBridge QIQTH.WhiteHBdomAllRows QIQTH.WhiteS1C
open QIQTH.WhiteHInnerContFinal
open QIQTH.WhiteLeviConvergenceTrio
open QIQTH.WhiteLeviMajorWire
open QIQTH.WhiteHcontWitnessFactor
open QIQTH.CurvedRNCVanVleckBound
open QIQTH.LeviSeries
open QIQTH.GaussianWidthTolerant
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteHInnerContTermBox

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ the composed continuity, reduced to EXACTLY `htermBox`.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_modulo_termBox` — `hEmeas` AND `hmajor` DISCHARGED, ONLY `htermBox` LEFT.**
    For EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)` (`n > 0`), and window `U ⊆ (·,1]`, there ARE a fat open
    gate `S`, radii `0 < a < b`, and a width `lam = whiteLam ≥ 2` such that — MODULO ONLY the whitened
    `iterE` termwise box continuity `htermBox` — the interior-time continuity of the whitened inner
    pairing holds on `Ioo 0 u`, ∀ `u ∈ U`.  The whitened-defect S1 base measurability `tripleHEmeas`
    is CO-INSTANTIATED (proved) at the shared gate `S`, and the width-`lam` Levi domination `hmajor`
    is discharged from the co-instantiated pkg bound + that `hEmeas` (via
    `WhiteLeviMajorWire.white_leviJoint_window_modulo_termBox`); the resulting Levi joint continuity
    `hJoint` feeds `WhiteHcontWitnessFactor.leviTimeCont_of_jointStrip`, multiplied against the
    discharged witness factor, to produce the `hcont` slot of the generic builder.  The value
    domination is `white_witness_value_dom_at_radius`; the interior slice measurability `hmeas` is the
    banked witness×Levi `z`-slice product; the generic builder
    `CurvedA1HContDomGen.hInnerCont_of_dominations_generic` composes them.
    ⚠ HONEST width `lam = whiteLam`.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_modulo_termBox (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R)
    (U : Set ℝ) (hU1 : ∀ u ∈ U, u ≤ 1) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        ((∀ u ∈ U, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) u, ∀ R' : ℝ, ∀ k : ℕ,
            ContinuousOn (fun p : ℝ × Point n =>
                iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
              (Set.Icc (τ₀ / 2) u ×ˢ Metric.closedBall (0 : Point n) R')) →
          ∀ u ∈ U, ContinuousOn
            (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
              * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
            (Set.Ioo 0 u)) := by
  obtain ⟨δp, hδp, hpkgc⟩ := white_hpkgBound_at_radius κ hκ hKc R hKb
  obtain ⟨δS, hδS, hS1⟩ := white_tripleHEmeas_uniform hn κ hκ hKc
  obtain ⟨δV, hδVpos, wA, Cpre, A₀, A₁, hwA0, hCpre0, hA₀0, hA₁0, hvalc⟩ :=
    white_witness_value_dom_at_radius κ hκ hKc R hKb
  obtain ⟨δW, hδWpos, hWc⟩ := white_witness_value_concrete_uniform κ hκ hKc
  -- the shared radius below ALL FOUR thresholds.
  set c : ℝ := min δp (min δS (min δV δW)) / 2 with hcdef
  have hmin0 : 0 < min δp (min δS (min δV δW)) :=
    lt_min hδp (lt_min hδS (lt_min hδVpos hδWpos))
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hcp : c < δp := by
    have := min_le_left δp (min δS (min δV δW)); rw [hcdef]; linarith
  have hcS : c < δS := by
    have h1 : min δp (min δS (min δV δW)) ≤ min δS (min δV δW) := min_le_right _ _
    have h2 : min δS (min δV δW) ≤ δS := min_le_left _ _
    rw [hcdef]; linarith [le_trans h1 h2]
  have hcV : c < δV := by
    have h1 : min δp (min δS (min δV δW)) ≤ min δS (min δV δW) := min_le_right _ _
    have h2 : min δS (min δV δW) ≤ min δV δW := min_le_right _ _
    have h3 : min δV δW ≤ δV := min_le_left _ _
    rw [hcdef]; linarith [le_trans (le_trans h1 h2) h3]
  have hcW : c < δW := by
    have h1 : min δp (min δS (min δV δW)) ≤ min δS (min δV δW) := min_le_right _ _
    have h2 : min δS (min δV δW) ≤ min δV δW := min_le_right _ _
    have h3 : min δV δW ≤ δW := min_le_right _ _
    rw [hcdef]; linarith [le_trans (le_trans h1 h2) h3]
  have ha : 0 < c / 4 := by linarith
  have hab : c / 4 < c / 2 := by linarith
  have hbc : c / 2 < c := by linarith
  -- the shared gate.
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c with hSdef
  -- co-emit the four facts at this gate.
  obtain ⟨hfat, C, hC0, hpkg⟩ := hpkgc c hc0 hcp (c / 4) (c / 2) ha hab hbc
  have hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S (c / 4) (c / 2)) :=
    hS1 c hc0 hcS (c / 4) (c / 2) ha hab hbc
  have hWmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) w.1 w.2.1 w.2.2) :=
    hWc c hc0 hcW (c / 4) (c / 2)
  have hval : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) τ p q|
        ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q) := by
    have := hvalc c hc0 hcV
    exact this
  -- discharge the B-slot (width-`lam` Levi bound) from the package + `hEmeas`.
  obtain ⟨C_L, hC_L, hBdom⟩ :=
    white_leviSeries_full_row κ hκ hKc S (c / 4) (c / 2) C (whiteLam κ hκ hKc)
      hC0 (whiteLam_ge_two κ hκ hKc) hpkg hEmeas
  have hlam0 : (0 : ℝ) < whiteLam κ hκ hKc :=
    lt_of_lt_of_le two_pos (whiteLam_ge_two κ hκ hKc)
  -- the interior slice measurability `hmeas` (witness slice × Levi `z`-slice, eventually in `s`).
  have hmeas : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable
        (fun z => whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) (u - s) 0 z
          * leviSeries (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)) s z 0)
        (volume : Measure (Point n)) := by
    intro u hu s₀ hs₀
    refine Filter.eventually_of_mem (Ioo_mem_nhds hs₀.1 hs₀.2) (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have hs1 : s ≤ 1 := le_of_lt (lt_of_lt_of_le hs.2 (hU1 u hu))
    have hAslice : AEStronglyMeasurable
        (fun z : Point n => whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) (u - s) 0 z)
        (volume : Measure (Point n)) :=
      (hWmeas.comp_measurable
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    have hBslice : AEStronglyMeasurable
        (fun z : Point n => leviSeries (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)) s z 0)
        (volume : Measure (Point n)) :=
      white_leviSeries_zmeas κ hκ hKc S (c / 4) (c / 2) C (whiteLam κ hκ hKc) hC0
        (whiteLam_ge_two κ hκ hKc) hpkg hEmeas s hs0 hs1 0
    exact hAslice.mul hBslice
  refine ⟨S, c / 4, c / 2, ha, hab, hfat, whiteLam κ hκ hKc, whiteLam_ge_two κ hκ hKc,
    fun htermBox => ?_⟩
  -- STEP 1: reduce the `hJoint` Levi joint continuity to `htermBox` (the `hmajor` slot GONE).
  have hJoint : ∀ u ∈ U, ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)) p.1 p.2 0)
      (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (Point n))) :=
    white_leviJoint_window_modulo_termBox κ hκ hKc S (c / 4) (c / 2) C
      (whiteLam κ hκ hKc) hC0 (whiteLam_ge_two κ hκ hKc) U hpkg hEmeas htermBox
  -- STEP 2: build the `hcont` slot = discharged witness factor × extracted Levi time-continuity.
  have hcont : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
      ContinuousAt
        (fun s => whiteGatedWitness κ hκ hKc S (c / 4) (c / 2) (u - s) 0 z
          * leviSeries (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)) s z 0) s₀ := by
    intro u hu s₀ hs₀
    refine Filter.Eventually.of_forall (fun z => ?_)
    exact (whiteWitness_time_continuousAt κ hκ hKc S (c / 4) (c / 2) u z hs₀.1 hs₀.2).mul
      (leviTimeCont_of_jointStrip (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)) u
        (hJoint u hu) hs₀.1 hs₀.2 z)
  -- STEP 3: the generic builder composes value + Levi B-slot + `hmeas` + `hcont`.
  exact QIQTH.CurvedA1HContDomGen.hInnerCont_of_dominations_generic
    (whiteGatedWitness κ hκ hKc S (c / 4) (c / 2))
    (leviSeries (whiteDefectKernel κ hκ hKc S (c / 4) (c / 2)))
    1 U hU1 wA (whiteLam κ hκ hKc) hwA0 hlam0 Cpre A₀ A₁ C_L hCpre0 hA₀0 hA₁0 hC_L
    hval (fun s hs hsT z y => hBdom s z y hs hsT) hmeas hcont

/-- **cp466 non-vacuity gate** — at genuinely curved data (`n = 2`, `κ = −1`, `K = closedBall 0 2`):
    the ∃-package of `white_hInnerCont_modulo_termBox` produces ONE FAT gate (`0 ∈ S 0`, open) with
    `0 < a < b` and a width `lam ≥ 2` — the co-instantiated shared gate (with S1 AND the Levi major
    both discharged) is not `∅`-degenerate.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_modulo_termBox_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ ∃ lam : ℝ, 2 ≤ lam := by
  obtain ⟨S, a, b, ha, hab, hgate, lam, hlam2, -⟩ :=
    white_hInnerCont_modulo_termBox (n := 2) (by norm_num) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
      (U := (∅ : Set ℝ)) (by simp)
  exact ⟨S, a, b, ha, hab,
    hgate 0 (Metric.mem_closedBall_self (by norm_num)), lam, hlam2⟩

end QIQTH.WhiteHInnerContTermBox

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.WhiteHInnerContTermBox

#print axioms white_hInnerCont_modulo_termBox
#print axioms white_hInnerCont_modulo_termBox_witness_gate

end AxiomChecks
