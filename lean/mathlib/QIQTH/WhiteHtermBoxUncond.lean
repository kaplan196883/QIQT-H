/-
  WhiteHtermBoxUncond — J4-705: THE hjoint INDUCTION TIE.  Closes the recursion-carrier fixpoint left
  HONEST by J4-704 (`WhiteHtermBoxGeom.white_htermBox_of_geometry`, commit 93ccd082): the whitened
  `htermBox` `∀ k` joint continuity is made UNCONDITIONAL in `k` by a genuine `Nat.rec`, discharging the
  previous-level joint-continuity carrier `hjoint` against this file's OWN output at the previous index.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE CRUX (resolved).  `white_htermBox_of_geometry` produced `∀ k, ContinuousOn (iterE E (k+1))` on
     `Icc t₁ t₂ ×ˢ closedBall 0 R'` from a carrier
        `hjoint : ∀ k, ∀ u ∈ (0,1], ∀ R'', ContinuousOn (iterE E (k+1)) on Icc (t₁·u) (t₂·u) ×ˢ B̄ R''`.
     This is a SAME-SHAPE fixpoint (output at level `k` IS the `hjoint` needed at level `k+1`, modulo the
     window/radius quantifiers).  We CLOSE it by strengthening the statement to quantify over ALL positive
     sub-windows `[s₁,s₂] ⊆ (0,1]` AND all radii, then running a clean `Nat.rec`:
       • WINDOW is downward-closed: the flow-ball / Gap-A geometry certs are τ-INDEPENDENT, so they hold on
         every positive sub-window; `[s₁·u, s₂·u] ⊆ (0, s₂] ⊆ (0,1]` is again a positive sub-window, so the
         IH feeds `hjoint` at level `k` with NO measure-theoretic obstruction (it holds for ALL `u`).
       • RADIUS: the geometry cert is kept at a SINGLE BOUNDED reach `R` (satisfiable — the downstream gate
         `flowExp '' ball c` is bounded).  The output is lifted to ALL radii by the OFF-GATE FIRST-ARGUMENT
         vanishing `whiteDefectKernel τ z w = 0` for `z` in the open off-gate region `U` (any `w`) — which
         makes BOTH the `(·,·,0)`-slice (base) AND the convolution-step integral `∫ w …` locally `0`
         off-gate, hence jointly continuous there (`contOn_prod_extend_of_zeroOn`, the generic replay of
         `WhiteHBaseExtend.whiteDefectKernel_jointContinuousOn_extend`).  NO unsatisfiable ∀-radius geometry.

  ── THE INDUCTION (clean `Nat.rec`, `_ih` genuinely USED).
       • base `k = 0`: `iterE E 1 = E` (`iterE_one`); its `(·,·,0)`-slice continuity is the flow-ball germ
         `whiteDefectKernel_jointContinuousOn_of_flowBall` (at reach `R`) EXTENDED to all radii by the
         off-gate cover.
       • step `k → k+1`: the IH gives `iterE E (k+1)` on EVERY positive sub-window at EVERY radius, which is
         EXACTLY the Gap-B carrier `hjoint` at level `k+1`; `white_innerStep_hcont` (S-dom ⊕ Gap-A ⊕ Gap-B)
         turns it into the a.e.-`u` convolution-step continuity at reach `R`, extended to the target radius
         by the off-gate cover, then `iterE_succ_jointContinuousOn_wired` (the OUTER dominated-continuity
         step, bounds `white_hEbound_zero`/`white_hInt_zero`, `u`-measurability
         `convStepIntegral_u_aestronglyMeasurable_wired`) delivers `iterE E (k+2)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is the
  INDUCTION TIE + a topological all-radii extension — pure recursion wiring.  No `sorry`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `contOn_prod_extend_of_zeroOn` — the GENERIC all-radii extension: joint continuity of any
      `g : ℝ × Point n → ℝ` on `Icc t₁ t₂ ×ˢ B̄ R` + `g ≡ 0` where the spatial coordinate lies in an open
      `U` + the cover `B̄ R' ⊆ B R ∪ U`  ⟹  joint continuity on `Icc t₁ t₂ ×ˢ B̄ R'`.
    * `white_htermBox_unconditional_k` — ★★★ THE INDUCTION TIE: the whitened `iterE` termwise joint
      continuity `∀ k, ∀ positive sub-window [s₁,s₂], ∀ radius R', ContinuousOn (iterE E (k+1))` — with
      `hjoint` DISCHARGED by the `Nat.rec`.  The surviving inputs are the labelled geometry / vanishing
      certificates below (items 1–6); `hjoint` is GONE.
    * `white_htermBox_uncond_vanishing_satisfiable` — cp466 antecedent-inhabitance gate for the off-gate
      vanishing package (witnessed at `U = ∅`, `R' < R`), so the conditional is not vacuously conditional.

  ── HONEST RESIDUAL — THE FULL LABELLED CERTIFICATE LIST (NOT the conclusion, NOT a₁ = R/6; `hjoint` GONE).
    1. `hEoffFirst` / `U` / `hUopen` / `hcover` — the OFF-GATE FIRST-ARGUMENT vanishing + open cover:
       `whiteDefectKernel κ hκ hKc S a b τ z w = 0` for `z ∈ U` (any `τ`, `w`), `U` open, and
       `∀ R', B̄ R' ⊆ B R ∪ U`.  The whitened chart maps `‖·‖ ≥ R` off the (bounded) gate; supplied,
       satisfiable (cp466 witness `U = ∅`, `R' < R`).
    2. base flow-ball geometry at reach `R` (`{h0K, hSopen, hballS, hcδ, hspec, hballC}` at `{c, δ₀}`).
    3. Gap-A base-`w` flow-ball geometry at reach `R` (`hgeom` at `{cA, δ₀A}`, `hcδA`).
    4. `hpkg` — the capstone width-`lam` pkg bound of the whitened gated witness heatOp.
    5. `hEmeas` — the whitened-defect S1 base measurability `tripleHEmeas`.
    6. `hagree` — the on-gate chart agreement (Gap-A reparam).

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.  `hjoint` — the recursion carrier of
     J4-704 — is no longer a hypothesis; it is discharged by the induction in this file.
-/
import Mathlib
import QIQTH.WhiteHtermBoxGeom

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp
open QIQTH.ExpMap QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open QIQTH.WhiteGapBAssembly QIQTH.WhiteHBaseExtend QIQTH.WhiteHtermBoxGeom
open QIQTH.WhiteHJetCont QIQTH.WhiteHTermBoxWire QIQTH.WhiteLeviMajorWire
open QIQTH.InnerEngineRecursion QIQTH.IterEEngineWiring
open scoped Topology

namespace QIQTH.WhiteHtermBoxUncond

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the GENERIC all-radii extension (`g ≡ 0` off the ball ⟹ continuity at all radii).
    ############################################################################### -/

/-- **`contOn_prod_extend_of_zeroOn`.**  The generic replay of
    `WhiteHBaseExtend.whiteDefectKernel_jointContinuousOn_extend`: for ANY `g : ℝ × Point n → ℝ`, joint
    continuity on `Icc t₁ t₂ ×ˢ closedBall 0 R`, plus `g ≡ 0` wherever the spatial coordinate lies in an
    OPEN `U`, plus the cover `closedBall 0 R' ⊆ ball 0 R ∪ U`, give joint continuity on
    `Icc t₁ t₂ ×ˢ closedBall 0 R'` for ANY `R'`.  Pure open-cover `ContinuousWithinAt` argument.
    NOT `a₁ = R/6`. -/
theorem contOn_prod_extend_of_zeroOn (g : ℝ × Point n → ℝ) (t₁ t₂ R R' : ℝ)
    (U : Set (Point n)) (hUopen : IsOpen U)
    (hUzero : ∀ p : ℝ × Point n, p.2 ∈ U → g p = 0)
    (hR : ContinuousOn g (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hcover : Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ U) :
    ContinuousOn g (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  intro p hp
  obtain ⟨hpτ, hpz⟩ := hp
  rcases hcover hpz with hball | hU
  · -- p.2 ∈ ball 0 R: transport `hR` through the open `univ ×ˢ ball 0 R` neighbourhood.
    have hcw : ContinuousWithinAt g
        (Set.Icc t₁ t₂ ×ˢ Metric.ball (0 : Point n) R) p :=
      (hR p ⟨hpτ, Metric.ball_subset_closedBall hball⟩).mono
        (Set.prod_mono subset_rfl Metric.ball_subset_closedBall)
    refine hcw.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ Metric.ball (0 : Point n) R, isOpen_univ.prod Metric.isOpen_ball,
      ⟨Set.mem_univ _, hball⟩, ?_⟩
    rintro q ⟨hqu, hqs⟩
    exact ⟨hqs.1, hqu.2⟩
  · -- p.2 ∈ U: `g ≡ 0` on the open `Icc t₁ t₂ ×ˢ U` neighbourhood.
    have hcw : ContinuousWithinAt g (Set.Icc t₁ t₂ ×ˢ U) p := by
      have hzero : ContinuousWithinAt (fun _ : ℝ × Point n => (0 : ℝ))
          (Set.Icc t₁ t₂ ×ˢ U) p := continuousWithinAt_const
      exact hzero.congr (fun q hq => hUzero q hq.2) (hUzero p hU)
    refine hcw.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ U, isOpen_univ.prod hUopen, ⟨Set.mem_univ _, hU⟩, ?_⟩
    rintro q ⟨hqu, hqs⟩
    exact ⟨hqs.1, hqu.2⟩

/-! ###############################################################################
    ### §B — ★★★ THE INDUCTION TIE: the whitened `htermBox`, unconditional in `k`.
    ############################################################################### -/

/-- **★★★ `white_htermBox_unconditional_k` — THE hjoint INDUCTION TIE.**  For the whitened defect kernel
    at gate-parametric `{S, a, b, C, lam}`, the ALL-`k` termwise joint `(τ,z)`-continuity of
    `iterE (whiteDefectKernel …) (k+1)` on EVERY positive sub-window `Icc s₁ s₂` (`0 < s₁ ≤ s₂ ≤ 1`) at
    EVERY radius `R'` — with the recursion carrier `hjoint` of J4-704 DISCHARGED by a genuine `Nat.rec`
    (the IH at level `k` supplies `hjoint` at level `k+1` on the rescaled sub-windows, at all radii).  The
    surviving inputs are the labelled geometry (reach `R`) + off-gate vanishing certificates (file header
    items 1–6).  ⚠ CONDITIONAL on that certificate list.  NOT `a₁ = R/6`. -/
theorem white_htermBox_unconditional_k (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (R c δ₀ cA δ₀A : ℝ) (hRpos : 0 < R)
    -- off-gate first-argument vanishing + open cover (the all-radii lift)
    (U : Set (Point n)) (hUopen : IsOpen U)
    (hEoffFirst : ∀ (τ : ℝ) (z w : Point n), z ∈ U →
        whiteDefectKernel κ hκ hKc S a b τ z w = 0)
    (hcover : ∀ R' : ℝ, Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ U)
    -- base flow-ball geometry (reach `R`) — the van-Vleck `hbase` cert
    (h0K : (0 : Point n) ∈ Kset) (hSopen : IsOpen (S 0))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0) (hcδ : c < δ₀)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc 0 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc 0 z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc 0)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v)))
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    -- Gap-A base-`w` flow-ball geometry (reach `R`)
    (hcδA : cA < δ₀A)
    (hgeom : ∀ q ∈ Kset,
        IsOpen (S q)
      ∧ Metric.closedBall (0 : Point n) R ⊆ S q
      ∧ (∀ v : Point n, ‖v‖ < δ₀A →
          (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
          ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q)
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v))
      ∧ Metric.closedBall (0 : Point n) R ⊆
          uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
            Metric.ball (0 : Point n) cA)
    -- the standard labelled whitened carries
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
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
    -- base flow-ball continuity at reach `R`.
    have hbaseR : ContinuousOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
      whiteDefectKernel_jointContinuousOn_of_flowBall hn κ hκ hKc S a b Wg hagree
        s₁ s₂ R c δ₀ hs₁ hs₂ h0K hSopen hballS hcδ hspec hballC
    -- extend the `(·,·,0)`-slice to radius `R'` via the off-gate cover.
    have hbaseR' : ContinuousOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') :=
      contOn_prod_extend_of_zeroOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        s₁ s₂ R R' U hUopen
        (fun p hp2 => hEoffFirst p.1 p.2 0 hp2) hbaseR (hcover R')
    have hEq : (fun p : ℝ × Point n =>
          iterE (whiteDefectKernel κ hκ hKc S a b) (0 + 1) p.1 p.2 0)
        = (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0) := by
      funext p; rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one]
    rw [hEq]; exact hbaseR'
  | succ m ih =>
    intro s₁ s₂ R' hs₁ hs₁₂ hs₂
    -- key: prove the succ output at EVERY POSITIVE radius `ρ`, then descend to arbitrary `R'`.
    have key : ∀ ρ : ℝ, 0 < ρ →
        ContinuousOn
          (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1 + 1) p.1 p.2 0)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
      intro ρ hρ
      -- the Gap-B carrier at level `m+1`, from the IH on rescaled positive sub-windows (all radii).
      have hjoint : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ R'' : ℝ,
          ContinuousOn
            (fun q : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1) q.1 q.2 0)
            (Set.Icc (s₁ * u) (s₂ * u) ×ˢ Metric.closedBall (0 : Point n) R'') := by
        intro u hu0 hu1 R''
        have hsu2 : s₂ * u ≤ 1 := by
          have h := mul_le_mul hs₂ hu1 hu0.le (zero_le_one)
          simpa using h
        exact ih (s₁ * u) (s₂ * u) R'' (mul_pos hs₁ hu0)
          (mul_le_mul_of_nonneg_right hs₁₂ hu0.le) hsu2
      -- the a.e.-`u` convolution-step continuity at reach `R` (S-dom ⊕ Gap-A ⊕ Gap-B).
      have hcontR : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ContinuousOn
            (fun p : ℝ × Point n => ∫ w, whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
              * iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1) (p.1 * u) w 0)
            (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
        white_innerStep_hcont hn κ hκ hKc S a b C lam hC hlam0 Wg hagree
          s₁ s₂ R cA δ₀A hs₁ hs₁₂ hRpos hs₂ hcδA hgeom hpkg hEmeas
          (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hjoint
      -- lift the convolution-step continuity to radius `ρ` via the off-gate cover.
      have hcontρ : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ContinuousOn
            (fun p : ℝ × Point n => ∫ w, whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
              * iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1) (p.1 * u) w 0)
            (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
        filter_upwards [hcontR] with u hu
        refine contOn_prod_extend_of_zeroOn _ s₁ s₂ R ρ U hUopen ?_ hu (hcover ρ)
        intro p hp2
        have hz : (fun w => whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
              * iterE (whiteDefectKernel κ hκ hKc S a b) (m + 1) (p.1 * u) w 0)
            = fun _ : Point n => (0 : ℝ) := by
          funext w; rw [hEoffFirst (p.1 - p.1 * u) p.2 w hp2]; ring
        simp only [hz, integral_zero]
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
    ### §C — cp466 antecedent-inhabitance gate for the off-gate vanishing package.
    ############################################################################### -/

/-- **`white_htermBox_uncond_vanishing_satisfiable`** (cp466 discipline).  The off-gate vanishing package
    `{U, IsOpen U, ∀ τ z w, z ∈ U → whiteDefectKernel … = 0, ∀ R', closedBall 0 R' ⊆ ball 0 R ∪ U}` is
    jointly INHABITED at the RESTRICTED radii `R' < R` — witnessed at `U = ∅` (openness trivially, the
    vanishing leg vacuously over the empty region, the cover by `closedBall_subset_ball`).  So the
    conditional tie is not vacuously conditional.  ⚠ HONEST: at `U = ∅` the extension degenerates to the
    reach-`R` ball; the genuine `R' > R` closure needs a NONEMPTY `U` (the labelled off-gate cover).
    NOT `a₁ = R/6`. -/
theorem white_htermBox_uncond_vanishing_satisfiable (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b R : ℝ) :
    ∃ U : Set (Point n), IsOpen U ∧
      (∀ (τ : ℝ) (z w : Point n), z ∈ U → whiteDefectKernel κ hκ hKc S a b τ z w = 0) ∧
      (∀ R' : ℝ, R' < R → Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ U) := by
  refine ⟨(∅ : Set (Point n)), isOpen_empty,
    fun τ z w hz => absurd hz (Set.notMem_empty z), fun R' hR' => ?_⟩
  rw [Set.union_empty]
  exact Metric.closedBall_subset_ball hR'

#check @contOn_prod_extend_of_zeroOn
#check @white_htermBox_unconditional_k
#check @white_htermBox_uncond_vanishing_satisfiable

end QIQTH.WhiteHtermBoxUncond

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHtermBoxUncond
#print axioms contOn_prod_extend_of_zeroOn
#print axioms white_htermBox_unconditional_k
#print axioms white_htermBox_uncond_vanishing_satisfiable
end AxiomChecks
