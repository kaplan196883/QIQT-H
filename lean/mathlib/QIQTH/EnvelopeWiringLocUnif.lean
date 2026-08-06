/-
  EnvelopeWiringLocUnif — J4-307: the envelope wiring (+ the loc-unif start).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / envelope-plumbing brick.  No `sorry` (header prose excepted), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.

  The J4-306 `MovingCorrRecombination.hBoundaryLim_FULLY_INTERNAL` carries — beyond its standing
  satisfiable list — TWO named-provider ENVELOPE carries:

    • `hFmov_bdd` / `hFfro_bdd` : a SINGLE window-uniform global bound
        `|leviSeries (heatOp Wit) (t − ε_m) z 0| ≤ Cf` (∀ m, z)   and   `|leviSeries (heatOp Wit) t z 0| ≤ Cf` (∀ z).
    • `hfmov_meas` : measurability of the moving Levi slice `z ↦ leviSeries (heatOp Wit) (t − ε_m) z 0`.

  This file DISCHARGES those from the banked providers:

    • (E1) `leviSlice_window_uniform_bound` — the SINGLE `Cf` with the `∀ m,z` moving bound AND the
      frozen bound, from the Levi envelope (`LeviSeriesLocalData.hFenv` /
      `leviSeries_dominatedW_le`, shape `|leviSeries E τ p q| ≤ C_L·baseKernelW 2 0 τ p q` on `(0,T]`)
      composed with the Gaussian DIAGONAL peak (`gaussDdim_le_diagonal`) and the width-antitone
      diagonal (`gaussDdim_zero_antitone`), i.e. exactly `BoundaryAssembly.B_le_MB` applied at the
      frozen time `t` and every moving time `t − ε_m`.  The window floor `ε₀ < t` (with `ε_m ≤ ε₀`,
      satisfiable by `ε₀ = 1 = epsSeq 0` since `epsSeq m = 1/(m+1) ≤ 1`, choosing the diffusion time
      `t > 1`) keeps EVERY slice time positive — `t − ε_m ≥ t − ε₀ > 0` — so NO negative-time case
      arises and the diagonal width `2(t − ε₀)` is a fixed positive floor.

    • (E2) `leviSlice_moving_meas` — the per-`m` moving-slice measurability from the banked slice
      family (`LeviSeriesLocalData.hFmeas` / `leviSeries_stronglyMeasurable_of_termwise`), instantiated
      at each moving time `t − ε_m`.

    • (E3) `hBoundaryLim_DONE` — `hBoundaryLim_FULLY_INTERNAL` with (E1)+(E2) fed, so the two envelope
      carries are replaced by a SINGLE `LeviSeriesLocalData (heatOp Wit) C T` package (whose `hFenv`
      and `hFmeas` are exactly the named providers) plus the window-floor data.  Its truly-final input
      list is the consumer's standing satisfiable list + `{hLocal, T, ε₀, floor}` (listed in its
      docstring).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import QIQTH.MovingCorrRecombination
import QIQTH.BoundaryAssembly
import QIQTH.LeviSeriesLocalData

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant QIQTH.ExpMap
open scoped Topology

namespace QIQTH.EnvelopeWiringLocUnif

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (E1) — the single window-uniform `Cf` (moving + frozen slices).
    ############################################################################### -/

/-- **★★ (E1) `leviSlice_window_uniform_bound`.**  From the Levi-series width-`2` envelope on the
    window `(0,T]`
        `hLdom : |leviSeries E τ p q| ≤ C_L·baseKernelW 2 0 τ p q`  (`0 < τ ≤ T`),
    together with the window floor `ε₀ < t` (`∀ m, epsSeq m ≤ ε₀`, `0 ≤ ε₀`, `t ≤ T`), there is a
    SINGLE constant `Cf ≥ 0` bounding BOTH the moving Levi slices and the frozen Levi slice, UNIFORMLY
    in the space variable:
        `|leviSeries E (t − epsSeq m) z 0| ≤ Cf`   (∀ m z)   and   `|leviSeries E t z 0| ≤ Cf`   (∀ z).
    `Cf := C_L·gaussDdim (2(t − ε₀)) 0`.  Route: rewrite the envelope into the plain Gaussian
    (`baseKernelW_zero_apply`) and apply `B_le_MB` (diagonal-peak `gaussDdim_le_diagonal` +
    width-antitone `gaussDdim_zero_antitone`) at the frozen time `s = t` and every moving time
    `s = t − epsSeq m`; the floor `ε₀ < t` with `epsSeq m ≤ ε₀` gives `t − ε₀ ≤ t − epsSeq m` and
    `0 < t − ε₀`, so all slice times are positive and share the `s`-free diagonal bound.
    The floor is satisfiable (`ε₀ = 1`, `epsSeq m = 1/(m+1) ≤ 1`, diffusion time `t > 1`), non-vacuous,
    and not the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem leviSlice_window_uniform_bound
    (E : ℝ → Point n → Point n → ℝ) (C_L T ε₀ t : ℝ) (hC_L : 0 ≤ C_L)
    (hLdom : ∀ τ (p q : Point n), 0 < τ → τ ≤ T →
      |leviSeries E τ p q| ≤ C_L * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hε₀ : 0 ≤ ε₀) (hε₀t : ε₀ < t) (htT : t ≤ T)
    (hεbnd : ∀ m, epsSeq m ≤ ε₀) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧
      (∀ m (z : Point n), |leviSeries E (t - epsSeq m) z 0| ≤ Cf) ∧
      (∀ z : Point n, |leviSeries E t z 0| ≤ Cf) := by
  -- Rewrite the envelope into the plain-Gaussian `B_le_MB` shape.
  have hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
      |leviSeries E s z y| ≤ C_L * gaussDdim (2 * s) (z - y) := by
    intro s hs hsT z y
    have h := hLdom s z y hs hsT
    rwa [baseKernelW_zero_apply] at h
  have ha : (0 : ℝ) < 2 * (t - ε₀) := by linarith
  refine ⟨C_L * gaussDdim (2 * (t - ε₀)) (0 : Point n),
    mul_nonneg hC_L (gaussDdim_nonneg _ _), ?_, ?_⟩
  · -- moving slices
    intro m z
    have hp : 0 < epsSeq m := epsSeq_pos m
    have hεm := hεbnd m
    have hspos : (0 : ℝ) < t - epsSeq m := by linarith
    exact B_le_MB (leviSeries E) C_L T (2 * (t - ε₀)) hC_L hBdom ha
      (t - epsSeq m) (by linarith) (by linarith) z
  · -- frozen slice
    intro z
    exact B_le_MB (leviSeries E) C_L T (2 * (t - ε₀)) hC_L hBdom ha
      t (by linarith) htT z

/-! ###############################################################################
    ### (E2) — the per-`m` moving-slice measurability.
    ############################################################################### -/

/-- **★★ (E2) `leviSlice_moving_meas`.**  From the banked Levi slice-measurability family
        `hFmeas : ∀ s, 0 < s → s ≤ T → ∀ y, AEStronglyMeasurable (fun z => leviSeries E s z y)`
    (the `LeviSeriesLocalData.hFmeas` field, built by `leviSeries_stronglyMeasurable_of_termwise`)
    and the same window floor, the moving Levi slice is `AEStronglyMeasurable` at every `m`:
        `∀ m, AEStronglyMeasurable (fun z => leviSeries E (t − epsSeq m) z 0)`.
    Route: each moving time `t − epsSeq m` is positive (`epsSeq m ≤ ε₀ < t`) and `≤ T` (`t ≤ T`,
    `epsSeq m > 0`), so `hFmeas` applies directly.  ⚠ NOT `a₁ = R/6`. -/
theorem leviSlice_moving_meas
    (E : ℝ → Point n → Point n → ℝ) (T ε₀ t : ℝ)
    (hε₀t : ε₀ < t) (htT : t ≤ T) (hεbnd : ∀ m, epsSeq m ≤ ε₀)
    (hFmeas : ∀ s, 0 < s → s ≤ T → ∀ y : Point n,
      AEStronglyMeasurable (fun z : Point n => leviSeries E s z y) (volume : Measure (Point n))) :
    ∀ m, AEStronglyMeasurable
      (fun z : Point n => leviSeries E (t - epsSeq m) z 0) (volume : Measure (Point n)) := by
  intro m
  have hp : 0 < epsSeq m := epsSeq_pos m
  have hεm := hεbnd m
  have hspos : (0 : ℝ) < t - epsSeq m := by linarith
  have hsT : t - epsSeq m ≤ T := by linarith
  exact hFmeas (t - epsSeq m) hspos hsT 0

/-! ###############################################################################
    ### (STRETCH) — the t-UNIFORM Heine boundary sup (loc-unif start).
    ############################################################################### -/

/-- **★★ (STRETCH) `heine_timeShift_sup_tendsto_tUniform`.**  The `t`-UNIFORM promotion of the B1
    Heine sup (`BoundaryLimAssembly.heine_timeShift_sup_tendsto`): the moving-vs-frozen slice sup is
    eventually small UNIFORMLY over BOTH the time window `t ∈ [ta, tb]` (with `t₁ < ta ≤ tb ≤ t₂`) AND
    the space ball `z ∈ closedBall 0 r` (`r ≤ R`):
        `∀ᶠ m, ∀ t ∈ [ta,tb], ∀ z ∈ closedBall 0 r, |F (t − epsSeq m) z − F t z| < ε`.
    This is exactly the joint-in-`(t,z)` upgrade the `tendstoLocallyUniformlyOn` boundary consumers
    (`DerivConvDischarge.derivConv_of_data`'s `hbdryLU` slot,
    `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`) want.  Route: Heine–Cantor uniform continuity
    of `F` on the compact strip `Icc t₁ t₂ ×ˢ closedBall 0 R` supplies a SINGLE `t`-free modulus `δ`;
    since the shift distance `dist ((t − epsSeq m, z), (t, z)) = epsSeq m` is `t`- and `z`-free, one
    eventual `epsSeq m < δ` (plus `epsSeq m < ta − t₁`, keeping `t − epsSeq m ≥ t₁` for all
    `t ≥ ta`) closes it uniformly.  Kernel-agnostic.  ⚠ NOT `a₁ = R/6`. -/
theorem heine_timeShift_sup_tendsto_tUniform
    (F : ℝ → Point n → ℝ) (t₁ t₂ R r ta tb : ℝ)
    (hrR : r ≤ R) (ht₁ta : t₁ < ta) (htab : ta ≤ tb) (htb₂ : tb ≤ t₂)
    (hcont : ContinuousOn (fun p : ℝ × Point n => F p.1 p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ t ∈ Set.Icc ta tb, ∀ z ∈ Metric.closedBall (0 : Point n) r,
      |F (t - epsSeq m) z - F t z| < ε := by
  -- Heine–Cantor: a single `t`-free modulus on the compact strip.
  have hs : IsCompact (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : Point n) R)
  have huc := hs.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδprop⟩ := huc ε hε
  -- Eventually `ε_m < δ` and `ε_m < ta − t₁` (the latter keeps `t − ε_m ≥ t₁` for all `t ≥ ta`).
  have hgap : (0 : ℝ) < ta - t₁ := by linarith
  have h1 : ∀ᶠ m in atTop, epsSeq m ∈ Set.Iio δ :=
    epsSeq_tendsto.eventually (Iio_mem_nhds hδ)
  have h2 : ∀ᶠ m in atTop, epsSeq m ∈ Set.Iio (ta - t₁) :=
    epsSeq_tendsto.eventually (Iio_mem_nhds hgap)
  filter_upwards [h1, h2] with m hmδ hmgap
  have hmδ' : epsSeq m < δ := Set.mem_Iio.mp hmδ
  have hmgap' : epsSeq m < ta - t₁ := Set.mem_Iio.mp hmgap
  have hpos := epsSeq_pos m
  intro t ht z hz
  obtain ⟨hta, htb⟩ := Set.mem_Icc.mp ht
  have hzR : z ∈ Metric.closedBall (0 : Point n) R :=
    (Metric.closedBall_subset_closedBall hrR) hz
  have hpmem : (t - epsSeq m, z) ∈
      Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R := by
    refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨by linarith, by linarith⟩, hzR⟩
  have hqmem : (t, z) ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R :=
    Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨by linarith, by linarith⟩, hzR⟩
  have hdist : dist (t - epsSeq m, z) (t, z) < δ := by
    rw [Prod.dist_eq]
    have h1t : dist (t - epsSeq m) t = epsSeq m := by
      rw [Real.dist_eq, show t - epsSeq m - t = -epsSeq m by ring, abs_neg, abs_of_pos hpos]
    rw [h1t, dist_self, max_eq_left hpos.le]
    exact hmδ'
  have hfin := hδprop (t - epsSeq m, z) hpmem (t, z) hqmem hdist
  rw [Real.dist_eq] at hfin
  exact hfin

/-! ###############################################################################
    ### (E3) — the DEFINITIVE boundary member: envelope carries discharged.
    ############################################################################### -/

/-- **★★★ (E3) `hBoundaryLim_DONE`.**  The DEFINITIVE truncated-Duhamel boundary member at the
    concrete van-Vleck gate: `MovingCorrRecombination.hBoundaryLim_FULLY_INTERNAL` with its TWO
    envelope carries (`Cf`/`hFmov_bdd`/`hFfro_bdd` and `hfmov_meas`) now DISCHARGED via (E1)+(E2), so
    they are replaced by a SINGLE `LeviSeriesLocalData (heatOp Wit) C T` package plus the window-floor
    data.  Concludes
        `Tendsto (fun m => BoundaryTrunc Wit F m t) atTop (𝓝 (F t 0 0))`,
    `Wit := vanVleckGatedWitness g gi hC hK S a b`, `F := leviSeries (heatOp g gi Wit)`.

    `hLocal.hFenv` (= `leviSeries_dominatedW_le`) feeds (E1) → the single `Cf` and both slice bounds;
    `hLocal.hFmeas` (= `leviSeries_stronglyMeasurable_of_termwise`) feeds (E2) → the moving-slice
    measurability.  Both are the NAMED envelope providers, so no opaque envelope carry survives.

    ── DEFINITIVE HONEST INPUT LIST (none is the conclusion; all satisfiable; no `hMovingCorr`, no
       opaque envelope bound):  the consumer's standing satisfiable list —
         • geometry / metric / gauge — `hC, hK, h0Kmem, hg, hgi, hgpos, hgdet0`;
         • gate data — `S, a, b, ha, hab`; strip `0 < t₁ < t < t₂`, `0 < R`;
         • the FINAL continuity bundle — `κ, Cc, hκ, hCc0, hEbound, hInt, hEmeas, hbase,
           hgeoBundle, hfgBundle, env, hu, hbound`;
         • frozen-slice measurability `hf_meas`; gate-activation `rS, hrS, hKball, hSact`;
           witness-slice measurability `hWslice`; zeroth wide domination `lam, τ₀, CW, hlam, hτ₀,
           hCW, hDom`;
       PLUS the SINGLE replacement of the two envelope carries:
         • `hLocal : LeviSeriesLocalData (heatOp g gi Wit) C T` — the banked Levi-window package (its
           `hFenv` = the envelope provider, its `hFmeas` = the measurability provider);
         • the window floor `T, ε₀, hε₀ (0 ≤ ε₀), hε₀t (ε₀ < t), htT (t ≤ T),
           hεbnd (∀ m, epsSeq m ≤ ε₀)` — satisfiable by `ε₀ = 1 = epsSeq 0`, diffusion time `t > 1`.
    ⚠ STILL NOT `a₁ = R/6`. -/
theorem hBoundaryLim_DONE
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    (κ Cc : ℝ) (hκ : 0 < κ) (hCc0 : 0 ≤ Cc)
    (t₁ t₂ R t : ℝ) (ht₁pos : 0 < t₁) (hlt₁ : t₁ < t) (hlt₂ : t < t₂) (hR : 0 < R)
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
    (hf_meas : Measurable
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0))
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z)
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z) volume)
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    -- ★ THE SINGLE replacement of the two envelope carries: the banked Levi-window package + floor.
    (C T ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀t : ε₀ < t) (htT : t ≤ T) (hεbnd : ∀ m, epsSeq m ≤ ε₀)
    (hLocal : QIQTH.LeviSeriesLocalData.LeviSeriesLocalData
      (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C T) :
    Tendsto
      (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hC hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) m t)
      atTop
      (𝓝 (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t 0 0)) := by
  obtain ⟨C_L, hC_L, hLdom⟩ := hLocal.hFenv
  obtain ⟨Cf, hCf0, hFmov_bdd, hFfro_bdd⟩ :=
    leviSlice_window_uniform_bound
      (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C_L T ε₀ t hC_L hLdom hε₀ hε₀t htT hεbnd
  have hfmov_meas := leviSlice_moving_meas
    (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) T ε₀ t hε₀t htT hεbnd hLocal.hFmeas
  exact QIQTH.MovingCorrRecombination.hBoundaryLim_FULLY_INTERNAL
    g gi hC hK h0Kmem hg hgi hgpos S a b ha hab hgdet0 κ Cc hκ hCc0 t₁ t₂ R t
    ht₁pos hlt₁ hlt₂ hR hEbound hInt hEmeas hbase hgeoBundle hfgBundle env hu hbound
    hf_meas rS hrS hKball hSact hWslice lam τ₀ CW hlam hτ₀ hCW hDom
    Cf hFmov_bdd hFfro_bdd hfmov_meas

#check @leviSlice_window_uniform_bound
#check @leviSlice_moving_meas
#check @heine_timeShift_sup_tendsto_tUniform
#check @hBoundaryLim_DONE

end QIQTH.EnvelopeWiringLocUnif

section AxiomChecks
open QIQTH.EnvelopeWiringLocUnif
#print axioms leviSlice_window_uniform_bound
#print axioms leviSlice_moving_meas
#print axioms heine_timeShift_sup_tendsto_tUniform
#print axioms hBoundaryLim_DONE
end AxiomChecks
