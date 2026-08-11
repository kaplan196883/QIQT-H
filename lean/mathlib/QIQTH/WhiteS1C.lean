/-
  WhiteS1C — J4-632: S1-c — THE E3d ASSEMBLY AT THE WHITENED WITNESS
  (`white_tripleHEmeas`) + the UNCONDITIONAL whitened bridge feed
  (`white_tail_O_s_unconditional`), discharging the single carried S1/hEmeas residue of the
  J4-627 bridge feed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: `hlam8` (`lam = whiteLam ≤ 8`, opaque `C₀` — carried by the FROZEN-side bridge comparison)
  + `K1TransportBudget` + the fat-`K` carrier piles + the capstone co-instantiation at the
  whitened witness + the prior analytic piles.  This brick is the S1-c ASSEMBLY only.

  ── THE QUANTIFIER OBSTRUCTION AND ITS RESOLUTION.  The banked S1 suppliers (J4-628/629/630/631)
     take the cutoff radii `(a,b)` BEFORE their `∃ δ₀`; the banked pkg feed (J4-626,
     `white_hpkgBound_discharged`) hides its gate radius inside an opaque `∃ S a b`.  Co-instantiating
     the two at ONE gate therefore needs BOTH sides radius-PARAMETRIC with `(a,b)`-free `δ₀`.
     Inspection of every supplier proof shows the `(a,b)`-dependence of the radii is SPURIOUS —
     each `δ₀` comes from `(a,b)`-free geometry (`whiteChart_rep_concrete`, `hKSmeas_concrete`,
     `chartField_contDiffAt_reachable_uniform`, `uniformInverseChart_huniformChart`,
     `white_hann_bound`'s `r₀`, `whiteUnvel_norm_le`) — so §1–§4 re-derive the suppliers in the
     UNIFORM shape `∃ δ₀ > 0, ∀ c ∈ (0,δ₀), ∀ (a b) [∀ k/(i,j)], …` (same proofs, quantifiers
     reordered; the `∀ k`/`∀ i j` closures also come FREE — no `exists_forall_radius` finite-min
     is needed, the banked per-index radii being index-free at the source).

  ── DELIVERED:
     ▸ §1–§4 — uniform mirrors: `white_hDtau_uniform`, `whiteCut_locally_zero_offGate_uniform`
       (+ `white_hOffS_uniform` / `white_hOffS2_uniform`), `white_pdRep_uniform` /
       `white_hP1_uniform`, `white_pd2Rep_uniform` / `white_hP2_uniform`.
     ▸ §5 ★★ `white_tripleHEmeas_uniform` — S1-c: the E3d assembly
       `HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields` at `G := whiteGatedWitness`,
       concrete flow-ball gates, radii `0 < a < b < c < δ₀`, all five antecedents discharged
       (`hDτ`/`hP1 ∀k`/`hP2 ∀ij`/`hgi`/`hchr`) — the whitened `tripleHEmeas` is a THEOREM.
       + ★ `white_tripleHEmeas` — the supplier-shaped corollary (fixed `0 < a < b`, window
       `b < c < δ₀`).
     ▸ §6 ★ `white_hpkgBound_at_radius` — the J4-626 discharged pkg bound re-derived
       radius-PARAMETRICALLY (same proof, gate radius `c` and cutoff radii `(a,b)` free with
       `0 < a < b < c < δp`, `δp` opaque-but-positive and `(a,b,c)`-free) — needed because the
       banked `white_hpkgBound_discharged` hides its gate inside an opaque `∃`.
     ▸ §7 ★★ `white_tail_O_s_unconditional` — THE PAYOFF: for EVERY `κ ≤ 0`, compact
       `K ⊆ B̄(0,R)` (`n > 0`), there ARE a fat gate + radii + width `lam = whiteLam ≥ 2` such
       that the whitened k ≥ 2 tail obeys `C_os·s·G_{lam·s}` on `(0,1]` — UNCONDITIONALLY (the
       J4-627 `tripleHEmeas` antecedent is DISCHARGED at the co-instantiated gate).  Plus
       ★ `white_transport_bridge_hEmeas_discharged` — the bridge Prop feeder now carried modulo
       `lam ≤ 8` ONLY (the honest hlam8 width residue).
     ▸ §8 — non-vacuity gates (assembled `tripleHEmeas` inhabited at the genuinely curved fat
       witness `n = 2`, `κ = −1`, `K = B̄(0,2)`; underlying witness strictly positive; the
       unconditional feeder inhabited at the same data).

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteS1P2
import QIQTH.WhiteBridge

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.EquivProbe
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteS1
open QIQTH.WhiteS1P1 QIQTH.WhiteCollar QIQTH.WhiteS1P2 QIQTH.WhiteAnnulus
open QIQTH.GaussianWidthTolerant QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.WhiteBridge QIQTH.FrozenWire QIQTH.BridgeDefect QIQTH.CoInstSmoke
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace QIQTH.WhiteS1C

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the ∂_τ slot, radius-UNIFORM in the cutoff radii `(a,b)`.
    ############################################################################### -/

/-- **`white_hDtau_uniform`** — J4-628's `white_hDtau_concrete` with the cutoff radii `(a,b)`
    moved INSIDE the chart radius: the `δ₀` sources (`whiteChart_rep_concrete`,
    `hKSmeas_concrete`) are `(a,b)`-free, so the same proof gives the uniform shape.
    NOT `a₁ = R/6`. -/
theorem white_hDtau_uniform (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ a b : ℝ,
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          u w.2.1 w.2.2) w.1) := by
  obtain ⟨ρ, hρ, Wg, hWgMeas, hWagree⟩ := whiteChart_rep_concrete κ hκ hKc
  obtain ⟨δm, hδm, hδmspec⟩ :=
    QIQTH.ConcreteGateInstantiation.hKSmeas_concrete (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc
  refine ⟨min ρ δm, lt_min hρ hδm, ?_⟩
  intro c hc0 hcδ a b
  have hcρ : c ≤ ρ := le_of_lt (lt_of_lt_of_le hcδ (min_le_left _ _))
  have hcm : c < δm := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact white_hDtau_stronglyMeasurable hn κ hκ hKc _ a b Wg hWgMeas
    (hδmspec c hc0 hcm) (fun w hqK hpS => hWagree c hcρ w hqK hpS)

/-! ###############################################################################
    ### §2 — the whitened collar, radius-UNIFORM (J4-630 with `(a,b)` inside).
    ############################################################################### -/

/-- **`whiteCut_locally_zero_offGate_uniform`** — J4-630's collar with `(a,b)` moved inside the
    chart radius (`δ₀` = the banked uniform chart radius, `(a,b)`-free); same proof.
    NOT `a₁ = R/6`. -/
theorem whiteCut_locally_zero_offGate_uniform (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ a b : ℝ, 0 < a → a < b → b < c →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) →
        ∀ (τ : ℝ) (q : Point n), q ∈ Kset → ∀ p : Point n, p ∉ S q →
          (fun x => whiteGatedWitness κ hκ hKc S a b τ x q) =ᶠ[nhds p] (fun _ => 0) := by
  obtain ⟨δ₀, hδ₀pos, hspec⟩ := uniformInverseChart_huniformChart (curvedRNCMetric κ)
    (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hc0 hcδ a b ha hab hbc S hSeq τ q hq p hpS
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  have hbδ : b < δ₀ := lt_trans hbc hcδ
  obtain ⟨hgerm, hball⟩ := hspec q hq
  obtain ⟨_hOpenb, hclosb⟩ := hball b hb0 hbδ
  have hSq : S q = uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c := by rw [hSeq]
  have hsub : closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) b) ⊆ S q := by
    rw [hSq]
    exact hclosb.trans (Set.image_mono (Metric.closedBall_subset_ball hbc))
  set U := (closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) b))ᶜ with hUdef
  have hUopen : IsOpen U := isOpen_compl_iff.mpr isClosed_closure
  have hpU : p ∈ U := fun h => hpS (hsub h)
  refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) ?_
  intro x hxU
  have hxNotBall : x ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) b :=
    fun h => hxU (subset_closure h)
  show whiteGatedWitness κ hκ hKc S a b τ x q = 0
  show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ x q = 0
  by_cases hxS : x ∈ S q
  · rw [gatedKernel_apply_of_mem Kset S _ τ hq hxS]
    rw [hSq] at hxS
    obtain ⟨v, hv, hvx⟩ := hxS
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    have hWqv : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q v) = v := by
      have hh := ((hgerm v (lt_trans hvc hcδ)).1).eq_of_nhds
      simpa using hh
    have hWqx : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q x = v := by rw [← hvx]; exact hWqv
    have hval : whiteInvChart κ hκ hKc q x = whiteUnvel κ q v := by
      show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q x) = whiteUnvel κ q v
      rw [hWqx]
    have hcut0 : radialCutoff a b (whiteUnvel κ q v) = 0 := by
      by_contra hne
      have hlt : rncRadialSq (whiteUnvel κ q v) < b ^ 2 := by
        by_contra hge
        exact hne (radialCutoff_eq_zero ha hab (not_lt.mp hge))
      have hcontr : rncRadialSq v ≤ rncRadialSq (whiteUnvel κ q v) := by
        have h4 := whiteVel_radialSq_le κ hκ q (whiteUnvel κ q v)
        rwa [whiteVel_whiteUnvel κ hκ q v] at h4
      have hvb2 : rncRadialSq v < b ^ 2 := lt_of_le_of_lt hcontr hlt
      have hsqle : ‖v‖ * ‖v‖ ≤ rncRadial v * rncRadial v :=
        mul_le_mul (norm_le_rncRadial v) (norm_le_rncRadial v) (norm_nonneg v)
          (rncRadial_nonneg v)
      have hnv2 : ‖v‖ ^ 2 < b ^ 2 := by
        have hsq := rncRadial_sq v
        nlinarith [hsqle, hvb2, hsq]
      have hnvb : ‖v‖ < b := lt_of_pow_lt_pow_left₀ 2 hb0.le hnv2
      exact hxNotBall ⟨v, mem_ball_zero_iff.mpr hnvb, hvx⟩
    simp only [whiteCutKernel, hval, hcut0, zero_mul]
  · exact gatedKernel_apply_of_notMem Kset S _ τ x q (Or.inr hxS)

/-- **`white_hOffS_uniform`** — the `hOffS` shape, uniform in `(a,b,k)`.  NOT `a₁ = R/6`. -/
theorem white_hOffS_uniform (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ a b : ℝ, 0 < a → a < b → b < c →
      ∀ k : Fin n, ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
        w.2.1 ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
        pd (fun x : Point n => whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          w.1 x w.2.2) k w.2.1 = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar⟩ := whiteCut_locally_zero_offGate_uniform κ hκ hKc
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hc0 hcδ a b ha hab hbc k w hzK _hτ hpS
  have hEq := hcollar c hc0 hcδ a b ha hab hbc
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) rfl
    w.1 w.2.2 hzK w.2.1 hpS
  rw [pd_congr_of_eventuallyEq _ _ k w.2.1 hEq]
  exact pd_const 0 k w.2.1

/-- **`white_hOffS2_uniform`** — the mixed-second-`pd` `hOffS2` shape, uniform in `(a,b,i,j)`.
    NOT `a₁ = R/6`. -/
theorem white_hOffS2_uniform (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ a b : ℝ, 0 < a → a < b → b < c →
      ∀ i j : Fin n, ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
        w.2.1 ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
        pd (fun y : Point n => pd (fun x : Point n => whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          w.1 x w.2.2) j y) i w.2.1 = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar⟩ := whiteCut_locally_zero_offGate_uniform κ hκ hKc
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hc0 hcδ a b ha hab hbc i j w hzK _hτ hpS
  have hEq := hcollar c hc0 hcδ a b ha hab hbc
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) rfl
    w.1 w.2.2 hzK w.2.1 hpS
  have hEq2 : (fun y : Point n => pd (fun x : Point n => whiteGatedWitness κ hκ hKc
      (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
      w.1 x w.2.2) j y) =ᶠ[nhds w.2.1] (fun _ => 0) := by
    have hnest := (eventually_eventually_nhds (p := fun x =>
      (fun x : Point n => whiteGatedWitness κ hκ hKc
        (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
        w.1 x w.2.2) x = (fun _ => (0 : ℝ)) x)).mpr hEq
    filter_upwards [hnest] with y hy
    rw [pd_congr_of_eventuallyEq _ _ j y hy]
    exact pd_const 0 j y
  rw [pd_congr_of_eventuallyEq _ _ i w.2.1 hEq2]
  exact pd_const 0 i w.2.1

/-! ###############################################################################
    ### §3 — the first-`pd` slot, radius-UNIFORM.
    ############################################################################### -/

/-- **`white_pdRep_uniform`** — J4-629's `white_pdRep_concrete` with `(a,b,k)` moved inside the
    chart radius (all four `δ₀` sources are `(a,b,k)`-free); same proof.  NOT `a₁ = R/6`. -/
theorem white_pdRep_uniform (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ (a b : ℝ) (k : Fin n),
      ∃ Af : ℝ → Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => Af w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset →
            w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
            Af w.1 w.2.2 w.2.1
              = pd (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) k w.2.1) := by
  obtain ⟨ρ, hρ, Wg, hWgMeas, hWagree⟩ := whiteChart_rep_concrete κ hκ hKc
  obtain ⟨δm, hδm, hδmspec⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δr, hδr, hreach⟩ := QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨min (min ρ δm) (min δr δo), lt_min (lt_min hρ hδm) (lt_min hδr hδo), ?_⟩
  intro c hc0 hcδ a b k
  have hcρ : c ≤ ρ :=
    le_of_lt (lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδr : c < δr := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hAGmeas : Measurable (fun w : ℝ × Point n × Point n =>
      whiteCutKernelGc κ a b Wg (w.1, w.2.1, w.2.2)) := by
    simpa using whiteCutKernelGc_measurable κ a b Wg hWgMeas
  obtain ⟨Af, hAfMeas, hAfval⟩ := QIQTH.AmpPdComposition.measurable_dq_witness (K := Kset)
    (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc) c k
    (fun τ q p => whiteCutKernel κ hκ hKc a b τ p q)
    (fun τ q p => whiteCutKernelGc κ a b Wg (τ, p, q))
    hAGmeas
    (hδmspec c hc0 hcδm)
    (fun q hq => ((hopen q hq).2 c hc0 hcδo).1)
    (by
      intro w hqK hpImg
      obtain ⟨v, hv, hvp⟩ := hpImg
      have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
      have hC2 : ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w.2.2) w.2.1 := by
        rw [← hvp]
        exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
      exact whiteCut_pdiffAt_of_contDiffAt hn κ hκ hKc a b k w.1 w.2.2 w.2.1 hC2)
    (by
      intro w hqK p hpImg
      exact whiteCutKernel_eq_whiteCutKernelGc_of_agree κ hκ hKc a b Wg w.1 p w.2.2
        (hWagree c hcρ (w.1, p, w.2.2) hqK hpImg))
  exact ⟨Af, hAfMeas, fun w hqK hpS => hAfval w hqK hpS⟩

/-- **`white_hP1_uniform`** — the `hP1` E3d slot, radius-uniform with the collar discharged:
    `∃ δ₀ > 0, ∀ c ∈ (0,δ₀), ∀ 0 < a < b < c, ∀ k`, joint strong measurability.
    NOT `a₁ = R/6`. -/
theorem white_hP1_uniform (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ a b : ℝ, 0 < a → a < b → b < c →
      ∀ k : Fin n,
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        pd (fun x : Point n => whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          w.1 x w.2.2) k w.2.1) := by
  obtain ⟨δ₁, hδ₁, hrep⟩ := white_pdRep_uniform hn κ hκ hKc
  obtain ⟨δm, hδm, hδmspec⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δ₂, hδ₂, hOff⟩ := white_hOffS_uniform κ hκ hKc
  refine ⟨min (min δ₁ δ₂) (min δm δo), lt_min (lt_min hδ₁ hδ₂) (lt_min hδm hδo), ?_⟩
  intro c hc0 hcδ a b ha hab hbc k
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Af, hAfMeas, hAfval⟩ := hrep c hc0 hcδ₁ a b k
  exact white_hP1_stronglyMeasurable hn κ hκ hKc
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b k Af hAfMeas
    (hδmspec c hc0 hcδm)
    (fun q hq => ((hopen q hq).2 c hc0 hcδo).1)
    (fun w hq hp => hAfval w hq hp)
    (hOff c hc0 hcδ₂ a b ha hab hbc k)

/-! ###############################################################################
    ### §4 — the second-`pd` slot, radius-UNIFORM.
    ############################################################################### -/

/-- **`white_pd2Rep_uniform`** — J4-631's `white_pd2Rep_concrete` with `(a,b,i,j)` moved inside
    the chart radius; the second difference quotient on the §3 uniform first-`pd` witness.
    NOT `a₁ = R/6`. -/
theorem white_pd2Rep_uniform (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ (a b : ℝ) (i j : Fin n),
      ∃ Af2 : ℝ → Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => Af2 w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset →
            w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
            Af2 w.1 w.2.2 w.2.1
              = pd (fun y : Point n =>
                  pd (fun x : Point n =>
                    whiteCutKernel κ hκ hKc a b w.1 x w.2.2) j y) i w.2.1) := by
  obtain ⟨δ₁, hδ₁, hrep⟩ := white_pdRep_uniform hn κ hκ hKc
  obtain ⟨δm, hδm, hδmspec⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δr, hδr, hreach⟩ := QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨min (min δ₁ δm) (min δr δo), lt_min (lt_min hδ₁ hδm) (lt_min hδr hδo), ?_⟩
  intro c hc0 hcδ a b i j
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδr : c < δr := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Af, hAfMeas, hAfval⟩ := hrep c hc0 hcδ₁ a b j
  obtain ⟨Af2, hAf2Meas, hAf2val⟩ := QIQTH.AmpPdComposition.measurable_dq_witness (K := Kset)
    (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc) c i
    (fun τ q => fun y : Point n =>
      pd (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q) j y)
    Af
    hAfMeas
    (hδmspec c hc0 hcδm)
    (fun q hq => ((hopen q hq).2 c hc0 hcδo).1)
    (by
      intro w hqK hpImg
      obtain ⟨v, hv, hvp⟩ := hpImg
      have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
      have hC2 : ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w.2.2) w.2.1 := by
        rw [← hvp]
        exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
      have hK2 : ContDiffAt ℝ 2
          (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) w.2.1 :=
        whiteCut_contDiffAt_of_chartC2 κ hκ hKc a b w.1 w.2.2 w.2.1 hC2
      exact QIQTH.LaplaceBeltrami.PdiffAt_pd_of_contDiffAt
        (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) j i w.2.1 hK2)
    (by
      intro w hqK p hp
      exact (hAfval (w.1, p, w.2.2) hqK hp).symm)
  exact ⟨Af2, hAf2Meas, fun w hqK hpS => hAf2val w hqK hpS⟩

/-- **`white_hP2_uniform`** — the `hP2` E3d slot, radius-uniform with the order-2 collar
    discharged: `∃ δ₀ > 0, ∀ c ∈ (0,δ₀), ∀ 0 < a < b < c, ∀ i j`, joint strong measurability.
    NOT `a₁ = R/6`. -/
theorem white_hP2_uniform (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ a b : ℝ, 0 < a → a < b → b < c →
      ∀ i j : Fin n,
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        pd (fun y : Point n =>
          pd (fun x : Point n => whiteGatedWitness κ hκ hKc
            (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
            w.1 x w.2.2) j y) i w.2.1) := by
  obtain ⟨δ₁, hδ₁, hrep⟩ := white_pd2Rep_uniform hn κ hκ hKc
  obtain ⟨δm, hδm, hδmspec⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δ₂, hδ₂, hOff2⟩ := white_hOffS2_uniform κ hκ hKc
  refine ⟨min (min δ₁ δ₂) (min δm δo), lt_min (lt_min hδ₁ hδ₂) (lt_min hδm hδo), ?_⟩
  intro c hc0 hcδ a b ha hab hbc i j
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Af2, hAf2Meas, hAf2val⟩ := hrep c hc0 hcδ₁ a b i j
  exact white_hP2_stronglyMeasurable hn κ hκ hKc
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b i j Af2 hAf2Meas
    (hδmspec c hc0 hcδm)
    (fun q hq => ((hopen q hq).2 c hc0 hcδo).1)
    (fun w hq hp => hAf2val w hq hp)
    (hOff2 c hc0 hcδ₂ a b ha hab hbc i j)

/-! ###############################################################################
    ### §5 — ★★ S1-c: THE E3d ASSEMBLY — `tripleHEmeas` at the whitened witness.
    ############################################################################### -/

/-- **★★ `white_tripleHEmeas_uniform` — S1-c, the E3d assembly at the whitened witness.**  At
    the concrete flow-ball gates, radii `0 < a < b < c < δ₀` (single `(a,b)`-free chart radius),
    the whitened gated witness satisfies the base joint `(τ,p,q)` strong measurability
    `tripleHEmeas g^κ gi^κ (whiteGatedWitness S a b)` — the EXACT `hEmeas` slot of the J4-627
    bridge feed — via `triple_hEmeas_of_borel_deriv_fields` with ALL five antecedents
    discharged: `hDτ` (§1), `hP1 ∀k` (§3), `hP2 ∀ij` (§4), `hgi`/`hchr` (J4-628).
    The `∀k`/`∀ij` binder closures come free from the uniform mirrors (no finite-min radius
    reconciliation needed — the per-index radii are index-free at the source).
    NOT `a₁ = R/6`. -/
theorem white_tripleHEmeas_uniform (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ a b : ℝ, 0 < a → a < b → b < c →
      QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
        (whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b) := by
  obtain ⟨δD, hδD, hDτ⟩ := white_hDtau_uniform hn κ hκ hKc
  obtain ⟨δ1, hδ1, hP1⟩ := white_hP1_uniform hn κ hκ hKc
  obtain ⟨δ2, hδ2, hP2⟩ := white_hP2_uniform hn κ hκ hKc
  refine ⟨min δD (min δ1 δ2), lt_min hδD (lt_min hδ1 hδ2), ?_⟩
  intro c hc0 hcδ a b ha hab hbc
  have hcD : c < δD := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hc1 : c < δ1 := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc2 : c < δ2 := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  exact QIQTH.HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields
    (curvedRNCMetric κ) (curvedRNCInv κ)
    (whiteGatedWitness κ hκ hKc
      (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b)
    (hDτ c hc0 hcD a b)
    (fun k => hP1 c hc0 hc1 a b ha hab hbc k)
    (fun i j => hP2 c hc0 hc2 a b ha hab hbc i j)
    (fun i j => curvedRNCInv_entry_measurable κ hκ i j)
    (fun k i j => curvedRNC_christoffel_measurable κ hκ k i j)

/-- **★ `white_tripleHEmeas` — the supplier-shaped S1-c corollary** (fixed radii `0 < a < b`,
    window `b < c < δ₀` — the J4-630/631 collar-window discipline).  NOT `a₁ = R/6`. -/
theorem white_tripleHEmeas (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
        (whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b) := by
  obtain ⟨δ₀, hδ₀, h⟩ := white_tripleHEmeas_uniform hn κ hκ hKc
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ
  exact h c (lt_trans (lt_trans ha hab) hbc) hcδ a b ha hab hbc

/-! ###############################################################################
    ### §6 — the J4-626 pkg bound, radius-PARAMETRIC (the co-instantiation enabler).
    ############################################################################### -/

/-- **★ `white_hpkgBound_at_radius`** — the J4-626 `white_hpkgBound_discharged` re-derived
    radius-PARAMETRICALLY: a single `(a,b,c)`-free `δp > 0` such that for EVERY gate radius
    `c ∈ (0,δp)` and cutoff radii `0 < a < b < c`, the flow-ball gate is fat and the whitened
    gated witness obeys the full `∀ (p,q)` capstone-`hpkgBound` shape at width
    `lam = whiteLam`.  (The banked theorem hides its gate inside an opaque `∃`; this mirror
    exposes the radius so S1-c can be co-instantiated at the SAME gate.)  Same proof as J4-626:
    chart-certificate leg via `‖E_q⁻¹v‖ ≤ CE·‖v‖` (needs `(CE+1)·c < r₀`, folded into `δp`),
    frontier leg via the whitening expansion (`b < c` puts the frontier in the cutoff zero
    collar), hann leg via the `(a,b)`-parametric `white_hann_bound`.  NOT `a₁ = R/6`. -/
theorem white_hpkgBound_at_radius (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ δp > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δp → ∀ a b : ℝ, 0 < a → a < b → b < c →
      (∀ q ∈ Kset, q ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c
          ∧ IsOpen (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c))
      ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
          |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (whiteGatedWitness κ hκ hKc
                (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                  (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b) τ p q|
            ≤ (C * (1 + t'))
              * QIQTH.GaussianWidthTolerant.baseKernelW (whiteLam κ hκ hKc) 0 τ p q := by
  classical
  obtain ⟨δ₀, hδ₀0, hspec⟩ := uniformInverseChart_huniformChart (curvedRNCMetric κ)
    (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨rh, hrh0, hhann⟩ := white_hann_bound κ hκ hKc R hKb
  obtain ⟨rp, hrp0, Cp, hCp0, hprod⟩ := white_ambient_bound_displacement_lam κ hκ hKc R hKb
  obtain ⟨CE, hCE0, hCEle⟩ := whiteUnvel_norm_le κ hκ hKc
  set r₀ : ℝ := min rh rp with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hrh0 hrp0
  have hCE1 : (0 : ℝ) < CE + 1 := by linarith
  refine ⟨min δ₀ (r₀ / (CE + 1)), lt_min hδ₀0 (div_pos hr₀0 hCE1), ?_⟩
  intro c hc0 hcδp a b ha hab hbc
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  have hcδ : c < δ₀ := lt_of_lt_of_le hcδp (min_le_left _ _)
  have hcr : c < r₀ / (CE + 1) := lt_of_lt_of_le hcδp (min_le_right _ _)
  have hCEc : CE * c < r₀ := by
    have h1 : c * (CE + 1) < r₀ := (lt_div_iff₀ hCE1).mp hcr
    nlinarith
  -- the chart-certificate leg at the flow-ball gate.
  have key : ∀ q ∈ Kset, ∀ p ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c, ∃ w : Point n,
      p = whiteExp κ hκ hKc q w ∧ ‖w‖ < r₀ ∧ whiteInvChart κ hκ hKc q p = w
        ∧ ContinuousAt (fun p' => whiteInvChart κ hκ hKc q p') p := by
    intro q hq p hp
    obtain ⟨v, hvmem, hpv⟩ := hp
    have hv : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hvmem
    have hvδ : ‖v‖ < δ₀ := lt_trans hv hcδ
    have hVval : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q p = v := by
      rw [← hpv]
      exact (((hspec q hq).1 v hvδ).1).eq_of_nhds
    refine ⟨whiteUnvel κ q v, ?_, ?_, ?_, ?_⟩
    · rw [whiteExp_whiteUnvel κ hκ hKc q v]
      exact hpv.symm
    · calc ‖whiteUnvel κ q v‖ ≤ CE * ‖v‖ := hCEle q hq v
        _ ≤ CE * c := mul_le_mul_of_nonneg_left hv.le hCE0
        _ < r₀ := hCEc
    · show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q p) = whiteUnvel κ q v
      rw [hVval]
    · have hC2 := ((hspec q hq).1 v hvδ).2
      have hCV : ContinuousAt (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) p := by
        rw [← hpv]
        exact hC2.continuousAt
      exact ((whiteUnvel κ q).continuous.continuousAt).comp hCV
  -- leg (i): openness + fatness.
  have hSopen : ∀ q ∈ Kset, IsOpen (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c) :=
    fun q hq => ((hspec q hq).2 c hc0 hcδ).1
  have hfat : ∀ q ∈ Kset, q ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c
      ∧ IsOpen (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c) := by
    intro q hq
    refine ⟨⟨0, mem_ball_zero_iff.mpr (by rw [norm_zero]; exact hc0), ?_⟩, hSopen q hq⟩
    exact uniformFlowExp_zero (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
      hKc q hq
  -- leg (iii): the frontier — interior-off or the cutoff zero collar (b < c).
  have hfrontier : ∀ q ∈ Kset, ∀ p : Point n,
      p ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c →
      ({p' : Point n | p' ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c} ∈ nhds p)
      ∨ ({p' : Point n | b ^ 2
            ≤ rncRadialSq (whiteInvChart κ hκ hKc q p')} ∈ nhds p) := by
    intro q hq p hpS
    by_cases hcl : p ∈ closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c)
    · right
      have hsub := ((hspec q hq).2 c hc0 hcδ).2
      obtain ⟨v, hvmem, hpv⟩ := hsub hcl
      have hvle : ‖v‖ ≤ c := by rwa [Metric.mem_closedBall, dist_zero_right] at hvmem
      have hvδ : ‖v‖ < δ₀ := lt_of_le_of_lt hvle hcδ
      have hVval : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q p = v := by
        rw [← hpv]
        exact (((hspec q hq).1 v hvδ).1).eq_of_nhds
      have hval : whiteInvChart κ hκ hKc q p = whiteUnvel κ q v := by
        show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q p) = whiteUnvel κ q v
        rw [hVval]
      have hvc : ‖v‖ = c := by
        by_contra hne
        have hlt : ‖v‖ < c := lt_of_le_of_ne hvle hne
        exact hpS ⟨v, mem_ball_zero_iff.mpr hlt, hpv⟩
      have h3 : rncRadialSq v ≤ rncRadialSq (whiteUnvel κ q v) := by
        have h4 := whiteVel_radialSq_le κ hκ q (whiteUnvel κ q v)
        rw [whiteVel_whiteUnvel κ hκ q v] at h4
        exact h4
      have h5 : ‖v‖ ^ 2 ≤ rncRadialSq v := by
        have h6 := norm_le_rncRadial v
        have h7 : rncRadial v ^ 2 = rncRadialSq v := by
          rw [rncRadial, Real.sq_sqrt (rncRadialSq_nonneg _)]
        nlinarith [norm_nonneg v]
      have hgt : b ^ 2 < rncRadialSq (whiteInvChart κ hκ hKc q p) := by
        rw [hval]
        have h8 : c ^ 2 ≤ rncRadialSq (whiteUnvel κ q v) := by
          have h9 : ‖v‖ ^ 2 ≤ rncRadialSq (whiteUnvel κ q v) := le_trans h5 h3
          rw [hvc] at h9
          exact h9
        nlinarith [hb0, hbc]
      have hC2 := ((hspec q hq).1 v hvδ).2
      have hCV : ContinuousAt (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) p := by
        rw [← hpv]
        exact hC2.continuousAt
      have hVc : ContinuousAt (fun p' => whiteInvChart κ hκ hKc q p') p :=
        ((whiteUnvel κ q).continuous.continuousAt).comp hCV
      have hrc : ContinuousAt (fun p' => rncRadialSq (whiteInvChart κ hκ hKc q p')) p :=
        (rncRadialSq_contDiff.continuous.continuousAt).comp hVc
      have hopen : {p' : Point n | b ^ 2
          < rncRadialSq (whiteInvChart κ hκ hKc q p')} ∈ nhds p :=
        hrc.preimage_mem_nhds (Ioi_mem_nhds hgt)
      refine Filter.mem_of_superset hopen fun p' hp' => ?_
      exact le_of_lt (show b ^ 2
        < rncRadialSq (whiteInvChart κ hκ hKc q p') from hp')
    · left
      have hopen : (closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c))ᶜ ∈ nhds p :=
        (isClosed_closure.isOpen_compl).mem_nhds hcl
      exact Filter.mem_of_superset hopen
        (fun p' hp' hmem => hp' (subset_closure hmem))
  -- the (a,b)-instantiated hann + producer with the joint constant.
  obtain ⟨Ch, hCh0, hhann'⟩ := hhann a b ha hab
  have hCB0 : 0 ≤ max Cp Ch := le_trans hCp0 (le_max_left _ _)
  have hbd : ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ w : Point n, ‖w‖ < r₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ
          (whiteExp κ hκ hKc q w) q|
        ≤ max Cp Ch * gaussDdim (whiteLam κ hκ hKc * τ) (whiteExp κ hκ hKc q w - q) := by
    intro q hq τ hτ w hw
    refine (hprod q hq τ hτ w (lt_of_lt_of_le hw (min_le_right _ _))).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  have hann : ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ →
      ∀ p ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c,
      a ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p) →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteCutKernel κ hκ hKc a b) τ p q|
        ≤ max Cp Ch * gaussDdim (whiteLam κ hκ hKc * τ) (p - q) := by
    intro q hq τ hτ p hp hannp
    obtain ⟨w, hpw, hwr, hVw, _⟩ := key q hq p hp
    have hannw : a ^ 2 ≤ rncRadialSq w := by
      rw [← hVw]
      exact hannp
    have h := hhann' q hq τ hτ w (lt_of_lt_of_le hwr (min_le_left _ _)) hannw
    rw [hpw]
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  refine ⟨hfat, max Cp Ch, hCB0, ?_⟩
  exact white_hpkgBound_of_gatePackage κ hκ hKc
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c)
    ha hab hCB0 hbd hSopen key hfrontier hann

/-! ###############################################################################
    ### §7 — ★★ THE PAYOFF: the unconditional whitened bridge feed.
    ############################################################################### -/

/-- **★★ `white_tail_O_s_unconditional` — the J4-627 bridge feed with the S1/`hEmeas` residue
    DISCHARGED**: for EVERY `κ ≤ 0` and compact `K ⊆ B̄(0,R)` (`n > 0`) there ARE a fat open
    gate `S`, radii `0 < a < b`, and the width `lam = whiteLam ≥ 2` such that the whitened
    k ≥ 2 tail obeys `C_os·s·G_{lam·s}` on `(0,1]` — UNCONDITIONALLY (no `tripleHEmeas`
    antecedent left: the pkg bound and S1-c are co-instantiated at the SAME flow-ball gate
    `c = min(δp,δS1)/2`, radii `a = c/4 < b = c/2 < c`).  ⚠ HONEST WIDTH: the conclusion is at
    `G_{lam·s}` with `lam = whiteLam = 2(n·C₀²+1)` (opaque `C₀`), NOT at the frozen chain's
    `G_{8s}` — the `lam ≤ 8` (`hlam8`) width comparison remains the carried residue of the
    FROZEN-side bridge (see `white_transport_bridge_hEmeas_discharged`).  NOT `a₁ = R/6`. -/
theorem white_tail_O_s_unconditional (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset)
    (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        ∃ C_os : ℝ, 0 ≤ C_os ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
          |leviSeries (whiteDefectKernel κ hκ hKc S a b) s p 0
              + whiteDefectKernel κ hκ hKc S a b s p 0|
            ≤ C_os * (s * gaussDdim (lam * s) (p - 0)) := by
  obtain ⟨δp, hδp, hpkgc⟩ := white_hpkgBound_at_radius κ hκ hKc R hKb
  obtain ⟨δS, hδS, hS1⟩ := white_tripleHEmeas_uniform hn κ hκ hKc
  set c : ℝ := min δp δS / 2 with hcdef
  have hmin0 : 0 < min δp δS := lt_min hδp hδS
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hcp : c < δp := by
    have h1 : min δp δS ≤ δp := min_le_left _ _
    rw [hcdef]; linarith
  have hcS : c < δS := by
    have h1 : min δp δS ≤ δS := min_le_right _ _
    rw [hcdef]; linarith
  have ha : 0 < c / 4 := by linarith
  have hab : c / 4 < c / 2 := by linarith
  have hbc : c / 2 < c := by linarith
  obtain ⟨hfat, C, hC0, hpkg⟩ := hpkgc c hc0 hcp (c / 4) (c / 2) ha hab hbc
  have hEmeas := hS1 c hc0 hcS (c / 4) (c / 2) ha hab hbc
  exact ⟨(fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c),
    c / 4, c / 2, ha, hab, hfat, whiteLam κ hκ hKc, whiteLam_ge_two κ hκ hKc,
    white_tail_O_s κ hκ hKc _ (c / 4) (c / 2) C (whiteLam κ hκ hKc) hC0
      (whiteLam_ge_two κ hκ hKc) hpkg hEmeas⟩

/-- **★ `white_transport_bridge_hEmeas_discharged`** — the bridge Prop feeder with the S1 input
    DISCHARGED: the residue is `lam ≤ 8` (`hlam8`) ONLY — for every `κ ≤ 0`, compact
    `K ⊆ B̄(0,R)` (`n > 0`) and frozen data `(K₀, r)` there are a fat gate, radii and
    `lam = whiteLam ≥ 2` such that `lam ≤ 8` ALONE yields the
    `FrozenTransportBridge (whiteDefectKernel …) (frozenDefectKernel K₀ r)`.
    `lam ≤ 8 ↔ n·C₀² ≤ 3` (opaque `C₀`) is the honest carried width condition.
    NOT `a₁ = R/6`. -/
theorem white_transport_bridge_hEmeas_discharged (K₀ r : ℝ) (hK₀ : K₀ ≤ 0) (hr : 0 ≤ r)
    (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)} (hKc : IsCompact Kset)
    (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        (lam ≤ 8 →
          FrozenTransportBridge (whiteDefectKernel κ hκ hKc S a b)
            (frozenDefectKernel K₀ r)) := by
  obtain ⟨δp, hδp, hpkgc⟩ := white_hpkgBound_at_radius κ hκ hKc R hKb
  obtain ⟨δS, hδS, hS1⟩ := white_tripleHEmeas_uniform hn κ hκ hKc
  set c : ℝ := min δp δS / 2 with hcdef
  have hmin0 : 0 < min δp δS := lt_min hδp hδS
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hcp : c < δp := by
    have h1 : min δp δS ≤ δp := min_le_left _ _
    rw [hcdef]; linarith
  have hcS : c < δS := by
    have h1 : min δp δS ≤ δS := min_le_right _ _
    rw [hcdef]; linarith
  have ha : 0 < c / 4 := by linarith
  have hab : c / 4 < c / 2 := by linarith
  have hbc : c / 2 < c := by linarith
  obtain ⟨hfat, C, hC0, hpkg⟩ := hpkgc c hc0 hcp (c / 4) (c / 2) ha hab hbc
  have hEmeas := hS1 c hc0 hcS (c / 4) (c / 2) ha hab hbc
  refine ⟨(fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c),
    c / 4, c / 2, ha, hab, hfat, whiteLam κ hκ hKc, whiteLam_ge_two κ hκ hKc, ?_⟩
  intro hlam8
  exact white_transport_bridge K₀ r hK₀ hr κ hκ hKc _ (c / 4) (c / 2) C
    (whiteLam κ hκ hKc) hC0 (whiteLam_ge_two κ hκ hKc) hlam8 hpkg hEmeas

/-! ###############################################################################
    ### §8 — Non-vacuity / adversarial gates (cp466 discipline).
    ############################################################################### -/

/-- **Gate 1 — the assembled `tripleHEmeas` is INHABITED at the genuinely curved fat witness**
    (`n = 2`, `κ = −1`, `K = closedBall 0 2`): there are radii `0 < a < b < c` at which the
    whitened `tripleHEmeas` HOLDS — the S1-c antecedent system is satisfiable, not `∅`-gated.
    NOT `a₁ = R/6`. -/
theorem white_tripleHEmeas_witness :
    ∃ c a b : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
        (whiteGatedWitness (-1 : ℝ) (by norm_num) (isCompact_closedBall (0 : Point 2) 2)
          (fun z => uniformFlowExp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
            (curvedRNC_hChr (-1 : ℝ) (by norm_num))
            (isCompact_closedBall (0 : Point 2) 2) z '' Metric.ball (0 : Point 2) c) a b) := by
  obtain ⟨δ₀, hδ₀, h⟩ := white_tripleHEmeas_uniform (by norm_num) (-1 : ℝ) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2)
  exact ⟨δ₀ / 2, δ₀ / 8, δ₀ / 4, by linarith, by linarith, by linarith,
    h (δ₀ / 2) (by linarith) (by linarith) (δ₀ / 8) (δ₀ / 4)
      (by linarith) (by linarith) (by linarith)⟩

/-- **Gate 2 — the measured object is genuinely NONZERO at the curved fat witness**: the
    whitened gated witness whose `tripleHEmeas` is assembled here is strictly positive on the
    origin diagonal for every `τ > 0` (re-export of the J4-628 object gate) — S1-c is about a
    non-degenerate kernel, not `0`.  NOT `a₁ = R/6`. -/
theorem white_S1c_underlying_nonzero :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ →
      0 < whiteGatedWitness (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2)
        (fun z => uniformFlowExp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
          (curvedRNC_hChr (-1 : ℝ) (by norm_num))
          (isCompact_closedBall (0 : Point 2) 2) z '' Metric.ball (0 : Point 2) c)
        1 2 τ 0 0 :=
  QIQTH.WhiteS1P1.white_hP1_underlying_nonzero

/-- **Gate 3 — the UNCONDITIONAL feeder is inhabited at genuinely curved data** (`n = 2`,
    `κ = −1`, `K = closedBall 0 2`): the ∃-package of ★★ `white_tail_O_s_unconditional`
    delivers a fat gate at `0 ∈ K`, radii `0 < a < b`, width `lam ≥ 2` AND an actual tail
    constant `C_os ≥ 0` — no antecedent left to satisfy (contrast: the J4-627 feeder's
    witness gate could only exhibit the chain UP TO the S1 input).  NOT `a₁ = R/6`. -/
theorem white_unconditional_feed_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧ ∃ C_os : ℝ, 0 ≤ C_os := by
  obtain ⟨S, a, b, ha, hab, hfat, lam, hlam2, C_os, hC_os, -⟩ :=
    white_tail_O_s_unconditional (n := 2) (by norm_num) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
  exact ⟨S, a, b, ha, hab,
    hfat 0 (Metric.mem_closedBall_self (by norm_num)), lam, hlam2, C_os, hC_os⟩

/-- **Gate 4 — the radius window of the uniform mirrors is SATISFIABLE at every chart radius**
    (re-export of the J4-630 constraint-system gate): for every `δ₀ > 0` there are
    `0 < a < b < c < δ₀`.  In THIS brick the trap the gate guards against is moot: the radii
    are chosen AFTER the (a,b,c)-free `δ₀`s (`c = min(δp,δS1)/2`), which is exactly what the
    uniform mirrors enable.  NOT `a₁ = R/6`. -/
theorem white_S1c_radii_satisfiable :
    ∀ δ₀ : ℝ, 0 < δ₀ → ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧ c < δ₀ :=
  QIQTH.WhiteCollar.white_collar_radii_satisfiable

end QIQTH.WhiteS1C

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteS1C
#print axioms QIQTH.WhiteS1C.white_hDtau_uniform
#print axioms QIQTH.WhiteS1C.whiteCut_locally_zero_offGate_uniform
#print axioms QIQTH.WhiteS1C.white_hOffS_uniform
#print axioms QIQTH.WhiteS1C.white_hOffS2_uniform
#print axioms QIQTH.WhiteS1C.white_pdRep_uniform
#print axioms QIQTH.WhiteS1C.white_hP1_uniform
#print axioms QIQTH.WhiteS1C.white_pd2Rep_uniform
#print axioms QIQTH.WhiteS1C.white_hP2_uniform
#print axioms QIQTH.WhiteS1C.white_tripleHEmeas_uniform
#print axioms QIQTH.WhiteS1C.white_tripleHEmeas
#print axioms QIQTH.WhiteS1C.white_hpkgBound_at_radius
#print axioms QIQTH.WhiteS1C.white_tail_O_s_unconditional
#print axioms QIQTH.WhiteS1C.white_transport_bridge_hEmeas_discharged
#print axioms QIQTH.WhiteS1C.white_tripleHEmeas_witness
#print axioms QIQTH.WhiteS1C.white_S1c_underlying_nonzero
#print axioms QIQTH.WhiteS1C.white_unconditional_feed_witness_gate
#print axioms QIQTH.WhiteS1C.white_S1c_radii_satisfiable
end AxiomChecks
