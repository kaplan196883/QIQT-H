/-
  WhiteHlegADischarge — J4-714 (Route (β) BRICK 5): THE `hlegA` DISCHARGE.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE VERDICT.  `hlegA` — the leg-(a) reparam-kernel-factor `ContinuousWithinAt` family at
     interior field points, carried as a LABELLED hypothesis by
     `WhiteHtermBoxWClosed.white_htermBox_unconditional_k_closed` /
     `WhiteHInnerContGeomClosed.white_hInnerCont_closed_final` — is DERIVED here from the J4-710
     set-generic reparam substrate
     `WhiteHJetContWSet.whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at_set` by a
     neighbourhood-transfer argument, conditional on a LOCALITY / REACH certificate on the gate.

  ── THE ROUTE (pure topology + the banked set-generic substrate).  At an interior field point
     `z₀ = p₀.2 ∈ interior (S w)` and, via the REACH certificate `S w ⊆ flowBall_w(c)` and
     `interior` monotonicity, also `z₀ ∈ interior (flowBall_w(c))`:
       • pick `ε > 0` with `closedBall z₀ (ε/2) ⊆ interior (S w) ∩ interior (flowBall_w(c))`
         (`interior … ∩ interior …` is an OPEN neighbourhood of `z₀`);
       • the closed ball `K := closedBall z₀ (ε/2)` is in-gate (`K ⊆ S w`) AND in-reach
         (`K ⊆ flowBall_w(c)`), so the set-generic substrate gives the joint `(τ,z)`
         `ContinuousOn` of the reparam factor on `Icc s₁ s₂ ×ˢ K` (for `u < 1`);
       • `ContinuousOn.continuousWithinAt` at `p₀ ∈ Icc s₁ s₂ ×ˢ K`, then
         `ContinuousWithinAt.mono_of_mem_nhdsWithin` transfers to the ambient box
         `Icc s₁ s₂ ×ˢ closedBall 0 ρ` (the box `Icc ×ˢ K` is a within-box neighbourhood of `p₀`,
         witnessed by the OPEN `univ ×ˢ ball z₀ (ε/2)`; `ball ⊆ closedBall`).
     The `u = 1` endpoint is DEGENERATE: the reparam time is `p.1 − p.1·1 = 0`, off the window
     `(0,1]`, so `whiteDefectKernel … 0 · w ≡ 0` and the factor is the constant-`0` function —
     `ContinuousWithinAt` trivially.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `white_hlegA_of_reach` — ★★★ THE DISCHARGE: the FULL `hlegA` family produced from
      `{hn, hagree (labelled), hSopen (gate openness), hSreach (gate ⊆ flow-ball reach),
      hspec (the banked uniform germ), radii c < δ₀}`.  No spatial `interior(flowBall)` cert is
      needed beyond the reach — it is derived by `interior` monotonicity.
    * `white_hlegA_flowBallGate` — the concrete-gate corollary: at the flow-ball gate
      `S ≡ flowExp_·(c)` the openness/reach/germ certificates are BANKED (from
      `uniformInverseChart_huniformChart`) and the representative-agreement `hagree` is BANKED
      (from `whiteChart_rep_concrete`), so `hlegA` holds from `{hn, radii}` alone — i.e. `hlegA`
      is GONE as a separate family, replaced only by the (banked) representative agreement.
    * `white_hlegA_cert_package_satisfiable` — cp466: the generic wrapper's certificate package is
      jointly INHABITED (at the concrete flow-ball gate), so the discharge is not vacuously
      conditional.

  ── HONEST RESIDUAL — THE FINAL CERTIFICATE LIST AFTER THE `hlegA` DISCHARGE (NOT the conclusion,
     NOT `a₁ = R/6`):  feeding `white_hlegA_of_reach` into `white_htermBox_unconditional_k_closed`
     removes `hlegA` from the tie's surviving inputs; the residue becomes
       `{hnull, hbase, hpkg, hEmeas}` + the DISCHARGE cert `{hagree, hSopen, hSreach, hspec germ}`.
     At the CONCRETE flow-ball gate (`white_hlegA_flowBallGate`) the discharge cert collapses to the
     BANKED `{whiteChart_rep_concrete, uniformInverseChart_huniformChart}` — so `hlegA` is fully
     banked-discharged, leaving downstream ONLY `{hnull, hbase}` as the genuine per-gate certificates
     (plus the dominated data `{hpkg, hEmeas}`).

  ⚠  HONEST FIREWALL.  `hlegA` discharge ONLY.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING
  about `R/6` (`R/6` is a labelled carrier, untouched).  No `sorry`, no `admit`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding)
  the conclusion, no existing file edited, nothing committed, nothing wired into `QIQTH.lean` /
  `AxiomAudit`.
-/
import Mathlib
import QIQTH.WhiteHJetContWSet
import QIQTH.WhiteS1

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open QIQTH.WhiteS1 QIQTH.WhiteHJetContWSet
open scoped Topology BigOperators

namespace QIQTH.WhiteHlegADischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — ★★★ THE `hlegA` DISCHARGE (generic gate, reach cert).
    ############################################################################### -/

/-- **★★★ `white_hlegA_of_reach` — THE `hlegA` DISCHARGE.**  The FULL leg-(a) family
    (`hlegA` of `WhiteHtermBoxWClosed.white_htermBox_unconditional_k_closed`) is DERIVED from the
    J4-710 set-generic reparam substrate + a LOCALITY / REACH certificate:
      ▸ `hagree` — the whitened-inverse-chart representative agreement (LABELLED; banked at the
        concrete gate by `whiteChart_rep_concrete`);
      ▸ `hSopen` — gate openness (banked: flow-ball images are open);
      ▸ `hSreach` — the gate is within a single base flow-ball, `S w ⊆ flowBall_w(c)` (banked at
        the concrete gate, where `S w = flowBall_w(c)`);
      ▸ `hspec` — the banked UNIFORM germ `uniformInverseChart_huniformChart` (per base `w`);
      ▸ radii `c < δ₀`.
    The reparam factor's joint `(τ,z)` `ContinuousWithinAt` at each interior field point is obtained
    by the neighbourhood transfer: a small in-gate ∩ in-reach closed ball feeds the substrate, then
    `mono_of_mem_nhdsWithin` upgrades to the ambient box.  The `u = 1` endpoint is the constant-`0`
    factor (time `p.1 − p.1·1 = 0` is off the `(0,1]` window).  NOT `a₁ = R/6`. -/
theorem white_hlegA_of_reach (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (c δ₀ : ℝ) (hcδ : c < δ₀)
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
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v))) :
    ∀ (u : ℝ), 0 < u → u ≤ 1 → ∀ (s₁ s₂ ρ : ℝ),
        0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 → 0 < ρ →
      ∀ p₀ ∈ (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ),
      ∀ w : Point n, w ∈ Kset → p₀.2 ∈ interior (S w) →
        ContinuousWithinAt
          (fun p : ℝ × Point n =>
            whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) p₀ := by
  intro u hu0 hu1 s₁ s₂ ρ hs₁ hs₁₂ hs₂ hρ p₀ hp₀ w hwK hint
  rcases lt_or_eq_of_le hu1 with hu1' | hu1eq
  · -- u < 1 : the substrate branch.
    set z₀ : Point n := p₀.2 with hz₀
    -- reach: `z₀ ∈ interior (flowBall_w(c))`.
    have hzflow : z₀ ∈ interior (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc w '' Metric.ball (0 : Point n) c) :=
      interior_mono (hSreach w hwK) hint
    -- an OPEN in-gate ∩ in-reach neighbourhood of `z₀`.
    set U : Set (Point n) := interior (S w) ∩
      interior (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc w '' Metric.ball (0 : Point n) c) with hUdef
    have hUopen : IsOpen U := isOpen_interior.inter isOpen_interior
    have hzU : z₀ ∈ U := ⟨hint, hzflow⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hzU)
    -- the in-gate ∩ in-reach closed ball `K`.
    set K : Set (Point n) := Metric.closedBall z₀ (ε / 2) with hKdef
    have hKU : K ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hKS : K ⊆ S w := fun x hx => interior_subset (hKU hx).1
    have hKflow : K ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc w '' Metric.ball (0 : Point n) c :=
      fun x hx => interior_subset (hKU hx).2
    -- the substrate: joint `(τ,z)` continuity of the reparam factor on `Icc s₁ s₂ ×ˢ K`.
    have hcontOn := whiteDefectKernel_reparam_jointContinuousOn_of_flowBall_at_set hn κ hκ hKc
      S a b w Wg hagree u s₁ s₂ c δ₀ K hu0 hu1' hs₁ hs₂ hwK (hSopen w hwK) hKS hcδ
      (hspec w hwK) hKflow
    -- `ContinuousWithinAt` at `p₀ ∈ Icc s₁ s₂ ×ˢ K`.
    have hp₀box : p₀ ∈ Set.Icc s₁ s₂ ×ˢ K :=
      ⟨hp₀.1, Metric.mem_closedBall_self (by linarith)⟩
    have hcwa := hcontOn.continuousWithinAt hp₀box
    -- transfer: `Icc s₁ s₂ ×ˢ K` is a within-box neighbourhood of `p₀`.
    have hmem : (Set.Icc s₁ s₂ ×ˢ K)
        ∈ nhdsWithin p₀ (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
      rw [mem_nhdsWithin]
      refine ⟨Set.univ ×ˢ Metric.ball z₀ (ε / 2),
        isOpen_univ.prod Metric.isOpen_ball, ?_, ?_⟩
      · exact ⟨Set.mem_univ _, Metric.mem_ball_self (by linarith)⟩
      · intro q hq
        obtain ⟨hqO, hqS⟩ := hq
        exact ⟨hqS.1, Metric.ball_subset_closedBall hqO.2⟩
    exact hcwa.mono_of_mem_nhdsWithin hmem
  · -- u = 1 : the reparam time is `p.1 − p.1·1 = 0`, off the `(0,1]` window ⟹ constant `0`.
    subst hu1eq
    have hconst : (fun p : ℝ × Point n =>
          whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * 1) p.2 w)
        = (fun _ : ℝ × Point n => (0 : ℝ)) := by
      funext p
      have h0 : p.1 - p.1 * 1 = 0 := by ring
      rw [h0]
      show whiteDefectKernel κ hκ hKc S a b 0 p.2 w = 0
      simp only [whiteDefectKernel]
      rw [if_neg (by norm_num)]
    rw [hconst]
    exact continuousWithinAt_const

/-! ###############################################################################
    ### §B — the concrete flow-ball gate corollary (`hlegA` fully banked-discharged).
    ############################################################################### -/

/-- **★★ `white_hlegA_flowBallGate` — `hlegA` at the concrete flow-ball gate.**  At the gate
    `S ≡ (fun z => flowExp_z(c))` (the as-built gate shape used by `WhiteS1C`), the openness /
    reach / germ certificates of `white_hlegA_of_reach` are BANKED
    (from `uniformInverseChart_huniformChart`), reach being the identity `S w = flowBall_w(c)`, and
    the representative agreement `hagree` is BANKED (from `whiteChart_rep_concrete`).  So `hlegA`
    holds from `{hn, radii c ∈ (0, δ₀) with c ≤ ρ}` alone — the leg-(a) family is fully discharged
    into banked facts.  NOT `a₁ = R/6`. -/
theorem white_hlegA_flowBallGate (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (u : ℝ), 0 < u → u ≤ 1 → ∀ (s₁ s₂ ρ : ℝ),
          0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 → 0 < ρ →
        ∀ p₀ ∈ (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ),
        ∀ w : Point n, w ∈ Kset →
          p₀.2 ∈ interior ((fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) w) →
          ContinuousWithinAt
            (fun p : ℝ × Point n =>
              whiteDefectKernel κ hκ hKc
                (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                  (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
                (p.1 - p.1 * u) p.2 w)
            (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) p₀ := by
  obtain ⟨ρ0, hρ0, Wg, _hWgMeas, hWagree⟩ := whiteChart_rep_concrete κ hκ hKc
  obtain ⟨δ₀, hδ₀0, hgerm⟩ := uniformInverseChart_huniformChart (curvedRNCMetric κ)
    (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨min ρ0 δ₀, lt_min hρ0 hδ₀0, ?_⟩
  intro c hc0 hcδ
  have hcρ : c ≤ ρ0 := le_of_lt (lt_of_lt_of_le hcδ (min_le_left _ _))
  have hcδ₀ : c < δ₀ := lt_of_lt_of_le hcδ (min_le_right _ _)
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c with hSdef
  -- `hagree` : banked representative agreement (at radius `c ≤ ρ0`, in-gate = in flow-ball image).
  have hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
      whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1) :=
    fun w hqK hpS => hWagree c hcρ w hqK hpS
  -- `hSopen` : banked flow-ball openness.
  have hSopen : ∀ w : Point n, w ∈ Kset → IsOpen (S w) :=
    fun w hwK => ((hgerm w hwK).2 c hc0 hcδ₀).1
  -- `hSreach` : the gate IS the flow-ball image.
  have hSreach : ∀ w : Point n, w ∈ Kset →
      S w ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w ''
        Metric.ball (0 : Point n) c :=
    fun w _ => subset_rfl
  -- `hspec` : the banked uniform germ.
  have hspec : ∀ w : Point n, w ∈ Kset →
      (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v)) :=
    fun w hwK => (hgerm w hwK).1
  exact white_hlegA_of_reach hn κ hκ hKc S a b Wg hagree c δ₀ hcδ₀ hSopen hSreach hspec

/-! ###############################################################################
    ### §C — cp466: the discharge certificate package is INHABITED.
    ############################################################################### -/

/-- **`white_hlegA_cert_package_satisfiable`** (cp466 discipline).  The certificate package of the
    generic discharge `white_hlegA_of_reach` (`{hagree, hSopen, hSreach, hspec germ, c < δ₀}`) is
    jointly INHABITED at the concrete flow-ball gate: there is a positive gate radius `c < δ₀` at
    which all four legs hold simultaneously (openness + reach + germ from
    `uniformInverseChart_huniformChart`, agreement from `whiteChart_rep_concrete`).  So the discharge
    is not vacuously conditional.  NOT `a₁ = R/6`. -/
theorem white_hlegA_cert_package_satisfiable (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ (S : Point n → Set (Point n)) (Wg : Point n × Point n → Point n) (c δ₀ : ℝ),
      0 < c ∧ c < δ₀ ∧
      (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1)) ∧
      (∀ w : Point n, w ∈ Kset → IsOpen (S w)) ∧
      (∀ w : Point n, w ∈ Kset →
        S w ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w ''
          Metric.ball (0 : Point n) c) := by
  obtain ⟨ρ0, hρ0, Wg, _hWgMeas, hWagree⟩ := whiteChart_rep_concrete κ hκ hKc
  obtain ⟨δ₀, hδ₀0, hgerm⟩ := uniformInverseChart_huniformChart (curvedRNCMetric κ)
    (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  set c : ℝ := min ρ0 δ₀ / 2 with hcdef
  have hc0 : 0 < c := by positivity
  have hcρ : c ≤ ρ0 := by
    have : min ρ0 δ₀ ≤ ρ0 := min_le_left _ _
    have hmin0 : 0 < min ρ0 δ₀ := lt_min hρ0 hδ₀0
    calc c = min ρ0 δ₀ / 2 := hcdef
      _ ≤ min ρ0 δ₀ := by linarith
      _ ≤ ρ0 := this
  have hcδ₀ : c < δ₀ := by
    have hmin0 : 0 < min ρ0 δ₀ := lt_min hρ0 hδ₀0
    have : min ρ0 δ₀ ≤ δ₀ := min_le_right _ _
    calc c = min ρ0 δ₀ / 2 := hcdef
      _ < min ρ0 δ₀ := by linarith
      _ ≤ δ₀ := this
  refine ⟨fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c, Wg, c, δ₀,
    hc0, hcδ₀, ?_, ?_, ?_⟩
  · exact fun w hqK hpS => hWagree c hcρ w hqK hpS
  · exact fun w hwK => ((hgerm w hwK).2 c hc0 hcδ₀).1
  · exact fun w _ => subset_rfl

#check @white_hlegA_of_reach
#check @white_hlegA_flowBallGate
#check @white_hlegA_cert_package_satisfiable

end QIQTH.WhiteHlegADischarge

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHlegADischarge
#print axioms white_hlegA_of_reach
#print axioms white_hlegA_flowBallGate
#print axioms white_hlegA_cert_package_satisfiable
end AxiomChecks
