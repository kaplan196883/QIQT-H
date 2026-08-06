/-
  BoundaryLimAssembly — J4-305: the BOUNDARY-LIMIT assembly for the truncated-Duhamel pile.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / limit-plumbing brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.

  The upstream `MovingFBoundaryLim.hBoundaryLim_concrete` (J4-280) concludes the boundary member
      `Tendsto (fun m => BoundaryTrunc Wit F m t) atTop (𝓝 (F t 0 0))`
  from the frozen chart-image approximate identity (SEQ ∘ FROZEN) PLUS three F-facts of the frozen Levi
  slice (`hf_meas`, `hf_bdd`, `hf_cont`) and the labelled moving-correction carry `hMovingCorr`.

  This file discharges/assembles the ANALYTIC ingredients of two of those carries from the J4-304 joint
  continuity `GateGeometryResiduals.leviSlice_hf_cont_FINAL` (the joint `(s,z)`-continuity of the Levi
  `0`-slice `F := leviSeries (heatOp g gi Wit)` on `Icc t₁ t₂ ×ˢ closedBall 0 R`):

    • (B1) `heine_timeShift_sup_tendsto` — from a joint `ContinuousOn` on the compact strip,
      Heine–Cantor (uniform continuity on the compact) gives the EVENTUAL-UNIFORM time-shift sup limit
          `∀ ε>0, ∀ᶠ m, ∀ z ∈ closedBall 0 r, |F (t − ε_m) z − F t z| < ε`,
      i.e. the on-ball moving-vs-frozen difference is eventually uniformly small.  This is the
      `sup_ball |f_m − f| → 0` ingredient of the (UNIF) moving-correction assembly (deliverable (ii) of
      `MovingCorrAssembly`), stated in the eventual-uniform form (no `sSup`).  Kernel-agnostic.

    • (B3) `frozenSlice_continuousAt_zero_of_jointContinuousOn` — the frozen `z`-slice continuity at `0`
      (`ContinuousAt (fun z => F t z) 0`, EXACTLY the `hf_cont` slot of `hBoundaryLim_concrete`) obtained
      from the SAME joint continuity by restricting to `s = t` (interior of the strip) and composing with
      `z ↦ (t, z)`.  Kernel-agnostic; genuinely DISCHARGES the J4-280 `hf_cont` carry from the FINAL.

    • (B4) `hBoundaryLim_ASSEMBLED` — `hBoundaryLim_concrete` re-exported with `hf_cont` INTERNALISED
      (supplied by (B3) from the FINAL's joint continuity), leaving the honest residual input list.

  The full `hMovingCorr` assembly (on-ball × mass + the two off-ball tails + integral splitting) still
  needs the integrability recombination; it is CARRIED, honestly labelled, with its sub-facts named in
  the `hBoundaryLim_ASSEMBLED` docstring.  ⚠ STILL NOT `a₁ = R/6`.
-/
import QIQTH.GateGeometryResiduals
import QIQTH.MovingCorrAssembly

open MeasureTheory Filter Metric
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant QIQTH.ExpMap
open scoped Topology

namespace QIQTH.BoundaryLimAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (B1) — the Heine–Cantor eventual-uniform time-shift sup limit.
    ############################################################################### -/

/-- **★★ (B1) `heine_timeShift_sup_tendsto`.**  Heine–Cantor on the compact strip.  If a slice
    `(s,z) ↦ F s z` is `ContinuousOn` the compact `Icc t₁ t₂ ×ˢ closedBall 0 R`, and `t ∈ (t₁, t₂]` with
    a sub-ball radius `r ≤ R`, then the time-shift difference is EVENTUALLY UNIFORMLY small along the
    boundary sequence `ε_m → 0⁺`:
        `∀ ε>0, ∀ᶠ m, ∀ z ∈ closedBall 0 r, |F (t − ε_m) z − F t z| < ε`.

    Route: `IsCompact.uniformContinuousOn_of_continuous` gives `UniformContinuousOn`; the ε–δ form
    (`Metric.uniformContinuousOn_iff`) plus `ε_m → 0` (`epsSeq_tendsto`, whence eventually `ε_m < δ` and
    `t − ε_m > t₁`) closes it, using `dist ((t−ε_m), z) (t, z) = ε_m` in the product sup-metric.

    HONEST: the only hypothesis is the joint `ContinuousOn` (supplied by
    `GateGeometryResiduals.leviSlice_hf_cont_FINAL` at the concrete gate); it is NOT the conclusion (a
    uniform-smallness statement about the time-SHIFT difference).  ⚠ NOT `a₁ = R/6`. -/
theorem heine_timeShift_sup_tendsto
    (F : ℝ → Point n → ℝ) (t₁ t₂ R r t : ℝ)
    (hrR : r ≤ R) (ht₁ : t₁ < t) (ht₂ : t ≤ t₂)
    (hcont : ContinuousOn (fun p : ℝ × Point n => F p.1 p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ z ∈ Metric.closedBall (0 : Point n) r,
      |F (t - epsSeq m) z - F t z| < ε := by
  -- Heine–Cantor on the compact strip.
  have hs : IsCompact (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : Point n) R)
  have huc := hs.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδprop⟩ := huc ε hε
  -- Eventually `ε_m < δ` and `t₁ < t − ε_m`.
  have h1 : ∀ᶠ m in atTop, epsSeq m ∈ Set.Iio δ :=
    epsSeq_tendsto.eventually (Iio_mem_nhds hδ)
  have hshift : Tendsto (fun m => t - epsSeq m) atTop (𝓝 t) := by
    have h := (tendsto_const_nhds (x := t)).sub epsSeq_tendsto
    simpa using h
  have h2 : ∀ᶠ m in atTop, t - epsSeq m ∈ Set.Ioi t₁ :=
    hshift.eventually (Ioi_mem_nhds ht₁)
  filter_upwards [h1, h2] with m hmδ hmt₁
  have hmδ' : epsSeq m < δ := Set.mem_Iio.mp hmδ
  have hmt₁' : t₁ < t - epsSeq m := Set.mem_Ioi.mp hmt₁
  have hpos := epsSeq_pos m
  intro z hz
  have hzR : z ∈ Metric.closedBall (0 : Point n) R :=
    (Metric.closedBall_subset_closedBall hrR) hz
  have hpmem : (t - epsSeq m, z) ∈
      Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R := by
    refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨le_of_lt hmt₁', ?_⟩, hzR⟩
    linarith [ht₂, hpos]
  have hqmem : (t, z) ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R :=
    Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨le_of_lt ht₁, ht₂⟩, hzR⟩
  have hdist : dist (t - epsSeq m, z) (t, z) < δ := by
    rw [Prod.dist_eq]
    have h1t : dist (t - epsSeq m) t = epsSeq m := by
      rw [Real.dist_eq, show t - epsSeq m - t = -epsSeq m by ring, abs_neg,
        abs_of_pos hpos]
    rw [h1t, dist_self, max_eq_left hpos.le]
    exact hmδ'
  have hfin := hδprop (t - epsSeq m, z) hpmem (t, z) hqmem hdist
  rw [Real.dist_eq] at hfin
  exact hfin

/-! ###############################################################################
    ### (B3) — the frozen `z`-slice continuity at `0` from the joint continuity.
    ############################################################################### -/

/-- **★★ (B3) `frozenSlice_continuousAt_zero_of_jointContinuousOn`.**  The frozen `z`-slice continuity
    at the origin `ContinuousAt (fun z => F t z) 0` (EXACTLY the `hf_cont` slot of
    `MovingFBoundaryLim.hBoundaryLim_concrete`), extracted from the joint `(s,z)`-continuity of `F` on
    the compact strip `Icc t₁ t₂ ×ˢ closedBall 0 R` by:
      • the strip is a neighbourhood of `(t, 0)` (`t ∈ (t₁,t₂)`, `0 < R`), so `ContinuousOn.continuousAt`
        gives joint `ContinuousAt` at `(t,0)`;
      • compose with the continuous slice `z ↦ (t, z)` (`Continuous.prodMk_right`).
    Kernel-agnostic; genuinely DISCHARGES the J4-280 `hf_cont` carry from the FINAL joint continuity.
    ⚠ NOT `a₁ = R/6`. -/
theorem frozenSlice_continuousAt_zero_of_jointContinuousOn
    (F : ℝ → Point n → ℝ) (t₁ t₂ R t : ℝ)
    (ht₁ : t₁ < t) (ht₂ : t < t₂) (hR : 0 < R)
    (hcont : ContinuousOn (fun p : ℝ × Point n => F p.1 p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousAt (fun z => F t z) 0 := by
  have hmem : Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R ∈
      𝓝 ((t, 0) : ℝ × Point n) :=
    prod_mem_nhds (Icc_mem_nhds ht₁ ht₂) (Metric.closedBall_mem_nhds (0 : Point n) hR)
  have hjoint : ContinuousAt (fun p : ℝ × Point n => F p.1 p.2) (t, 0) :=
    hcont.continuousAt hmem
  have hmap : ContinuousAt (fun z : Point n => ((t, z) : ℝ × Point n)) 0 :=
    (Continuous.prodMk_right t).continuousAt
  have hcomp := hjoint.comp hmap
  simpa using hcomp

/-! ###############################################################################
    ### (B4) — the full `hBoundaryLim` with `hf_cont` internalised from the FINAL.
    ############################################################################### -/

/-- **★★★ (B4) `hBoundaryLim_ASSEMBLED`.**  The boundary-limit member of the truncated-Duhamel pile at
    the concrete van-Vleck gate, with the J4-280 `hf_cont` carry INTERNALISED: it is supplied by (B3)
    from the joint continuity `GateGeometryResiduals.leviSlice_hf_cont_FINAL` (J4-304), which is threaded
    through its full satisfiable bundle (`hEbound`/`hInt`/`hEmeas`/`hbase`/`hgeoBundle`/`hfgBundle` +
    summable envelope).  Concludes
        `Tendsto (fun m => BoundaryTrunc Wit F m t) atTop (𝓝 (F t 0 0))`,
    `Wit := vanVleckGatedWitness g gi hC hK S a b`,  `F := leviSeries (heatOp g gi Wit)`.

    FINAL HONEST INPUT LIST (none is the conclusion; all satisfiable):
      • standing geometry / metric / gauge — `hC, hK, h0Kmem, hg, hgi, hgpos, hgdet0`;
      • gate data — `S, a, b, ha, hab`; the strip `t₁ < t < t₂`, `0 < t₁`, `0 < R`;
      • the FINAL's continuity bundle — `κ, C, hκ, hC0, hEbound, hInt, hEmeas, hbase, hgeoBundle,
        hfgBundle, env, hu, hbound` (⟹ joint `(s,z)`-continuity ⟹ `hf_cont` via (B3));
      • the two REMAINING frozen-slice F-facts — `hf_meas` (banked via
        `LeviSeriesLocalData.leviSeries_stronglyMeasurable_of_termwise`), `hf_bdd` (banked via the Levi
        envelope `GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated`);
      • the gate-activation carries `rS, hrS, hKball, hSact` and the witness-slice measurability
        `hWslice`; the zeroth wide domination `lam, τ₀, CW, hlam, hτ₀, hCW, hDom`;
      • the labelled (UNIF) moving-correction carry `hMovingCorr` (→ 0; NOT the conclusion).  Its
        remaining sub-facts, all named here: the ON-ball part `|∫_ball Wit(ε_m)·(F(t−ε_m)−F t)| ≤
        (∫_ball|Wit(ε_m)|)·sup_ball|F(t−ε_m)−F t|`, bounded by `CW·ε` eventually via (B1)
        `heine_timeShift_sup_tendsto` + `MovingCorrAssembly.epsSeq_witnessSlice_mass_eventually_le`; the
        two OFF-ball tails via `GateAnnulusSplit.offBall_integral_tendsto_zero`; the per-`m` integral
        split `BoundaryTrunc − frozenInt = onBall + tail₁ − tail₂` via `integral_add_compl` (integrability
        from `hWslice` + `hDom` + `hf_bdd`).  This recombination is the residual left carried.
    ⚠ STILL NOT `a₁ = R/6`. -/
theorem hBoundaryLim_ASSEMBLED
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    -- the strip window (`t` in the interior):
    (κ Cc : ℝ) (hκ : 0 < κ) (hCc0 : 0 ≤ Cc)
    (t₁ t₂ R t : ℝ) (ht₁pos : 0 < t₁) (hlt₁ : t₁ < t) (hlt₂ : t < t₂) (hR : 0 < R)
    -- the FINAL's joint-continuity bundle:
    (hEbound : ∀ τ p q, 0 < τ →
      |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q| ≤ Cc * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) κ 0 Cc)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n =>
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) q.1 q.2.1 q.2.2))
    (hbase : ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hgeoBundle : ∀ w ∈ K, ∃ ρc cw ρ₀w C_Dw : ℝ,
      0 < ρc ∧
      ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK w) (Metric.ball w ρc) ∧
      S w = uniformFlowExp g gi hC hK w '' Metric.ball 0 cw ∧
      0 < cw ∧ cw < ρ₀w ∧ 0 ≤ C_Dw ∧
      (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀w →
        ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_Dw * ‖v‖ * ‖v‖) ∧
      closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 cw)
        ⊆ uniformFlowExp g gi hC hK w '' Metric.closedBall 0 cw ∧
      cw + C_Dw * cw * cw < ρc)
    (hfgBundle : ∀ w ∈ K, ∀ s₁ s₂ : ℝ, 0 < s₁ →
      ∃ Rg cw ρ₀w C_Dw : ℝ,
        0 < Rg ∧
        ContinuousOn (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall w Rg) ∧
        S w = uniformFlowExp g gi hC hK w '' Metric.ball 0 cw ∧
        0 < cw ∧ cw < ρ₀w ∧ 0 ≤ C_Dw ∧
        (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀w →
          ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_Dw * ‖v‖ * ‖v‖) ∧
        closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 cw)
          ⊆ uniformFlowExp g gi hC hK w '' Metric.closedBall 0 cw ∧
        (∀ v : Point n, ‖v‖ ≤ cw →
          uniformInverseChart g gi hC hK w (uniformFlowExp g gi hC hK w v) = v) ∧
        b + C_Dw * b * b < Rg)
    (env : ℕ → ℝ) (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1)
          * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) p.1 p.2 0‖
        ≤ env k)
    -- the two REMAINING frozen-slice F-facts (banked, satisfiable):
    (hf_meas : Measurable
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0))
    (hf_bdd : ∃ Cf : ℝ, ∀ z,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0| ≤ Cf)
    -- gate-activation carries + witness-slice measurability:
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z)
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z) volume)
    -- zeroth wide domination:
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    -- the labelled (UNIF) moving-correction carry (→ 0; NOT the conclusion):
    (hMovingCorr : Tendsto
      (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) m t
          - ∫ z, vanVleckGatedWitness g gi hC hK S a b (epsSeq m) (0 : Point n) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0)
      atTop (𝓝 0)) :
    Tendsto
      (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hC hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) m t)
      atTop
      (𝓝 (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t 0 0)) := by
  -- (1) joint continuity from the FINAL.
  have hjoint := QIQTH.GateGeometryResiduals.leviSlice_hf_cont_FINAL
    g gi hC hK S a b ha hab κ Cc hκ hCc0 t₁ t₂ R ht₁pos (le_of_lt (lt_trans hlt₁ hlt₂)) hR
    hEbound hInt hEmeas hbase hgeoBundle hfgBundle env hu hbound
  -- (2) extract `hf_cont` at `0` via (B3).
  have hf_cont := frozenSlice_continuousAt_zero_of_jointContinuousOn
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
    t₁ t₂ R t hlt₁ hlt₂ hR hjoint
  -- (3) feed `hBoundaryLim_concrete`.
  exact QIQTH.MovingFBoundaryLim.hBoundaryLim_concrete
    g gi hC hK h0Kmem hg hgi hgpos S a b ha hab hgdet0 t
    hf_meas hf_bdd hf_cont rS hrS hKball hSact hWslice
    lam τ₀ CW hlam hτ₀ hCW hDom hMovingCorr

#check @heine_timeShift_sup_tendsto
#check @frozenSlice_continuousAt_zero_of_jointContinuousOn
#check @hBoundaryLim_ASSEMBLED

end QIQTH.BoundaryLimAssembly

section AxiomChecks
open QIQTH.BoundaryLimAssembly
#print axioms heine_timeShift_sup_tendsto
#print axioms frozenSlice_continuousAt_zero_of_jointContinuousOn
#print axioms hBoundaryLim_ASSEMBLED
end AxiomChecks
