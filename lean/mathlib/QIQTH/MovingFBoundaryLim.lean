/-
  MovingFBoundaryLim — J4-280: the MOVING-`f` step toward `hBoundaryLim`, via the W1-FREE
  chart-image approximate identity (`GateAnnulusSplit.chartImage_approx_identity_final`, J4-279).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / limit-plumbing brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TARGET — `hBoundaryLim` (the boundary-limit member of the truncated-Duhamel pile).

  `TruncatedDuhamelData.truncatedDuhamelCore_of_daLim` consumes, at the concrete van-Vleck witness
  `Wit := vanVleckGatedWitness g gi hC hK S a b` and source `F := leviSeries (heatOp g gi Wit)`:
      `hBoundaryLim : Tendsto (fun m => BoundaryTrunc Wit F m t) atTop (𝓝 (F t 0 0))`,
  where (`HeatResidualBound.BoundaryTrunc`, def, with `t − (t − ε_m) = ε_m`)
      `BoundaryTrunc Wit F m t = ∫ z, Wit (t − (t − ε_m)) 0 z · F (t − ε_m) z 0`
                              = ∫ z, Wit (ε_m) 0 z · F (t − ε_m) z 0`,   `ε_m := epsSeq m → 0⁺`.

  ── WHY A NEW ROUTE.  The banked provider `HeatResidualBound.boundaryTrunc_tendsto` (W1) reaches this
  limit only through `boundary_tendstoLocallyUniformlyOn`, whose carry `hAnear` asserts the witness is
  Gaussian **at `z`** (`A τ 0 z = gaussDdim τ z · (u₀ z + τ·u₁ z)`).  Per `DaLimLUConcreteDischarge`
  (header §"WHY THE PROVIDER-∃ EXPORT … IS NOT ATTEMPTED", lines 61–71), `hAnear` is the **W1 structural
  wall**: the concrete `H_G` is Gaussian at the CHART IMAGE `W z 0`, not at `z`, so `hAnear` is NOT
  established (risking an unsatisfiable hypothesis) at a general gate.  The J4-279 fixed-`f` chart-image
  approximate identity `GateAnnulusSplit.chartImage_approx_identity_final` reaches the SAME concentration
  through the chart change-of-variables — WITHOUT `hAnear`.  This file wires that W1-free AI to the
  sequence `ε_m` and packages the moving-`f` correction.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE 3ε DECOMPOSITION.  With the frozen slice `f z := F t z 0` and the moving slice
  `f_m z := F (t − ε_m) z 0` (so `BoundaryTrunc = ∫ Wit(ε_m)·f_m`, and `f 0 = F t 0 0` = the target):

      |∫ Wit(ε_m)·f_m − F t 0 0|
          ≤ |∫ Wit(ε_m)·(f_m − f)|      -- (UNIF) moving-vs-frozen correction
          + |∫ Wit(ε_m)·f − f 0|        -- (SEQ ∘ AI) the fixed-`f` concentration at `f`
          + |f 0 − F t 0 0|.            -- ZERO by definition (`f 0 = F t 0 0`).

  ── (SEQ)  `tendsto_comp_epsSeq` — the fixed-`f` AI is a `𝓝[>]0`-limit; composing with `ε_m → 0⁺`
     turns it into an `atTop` sequence limit.  General, kernel-agnostic.
  ── (FROZEN)  `frozenBoundary_tendsto` — (SEQ) applied to `chartImage_approx_identity_final` at the
     frozen Levi slice `f := fun z => leviSeries (heatOp g gi Wit) t z 0`:
        `Tendsto (fun m => ∫ z, Wit (ε_m) 0 z · F t z 0) atTop (𝓝 (F t 0 0))`.
     This is the SECOND term of the decomposition — landed, W1-free.
  ── (HB)  `hBoundaryLim_concrete` — (FROZEN) plus the labelled (UNIF) moving-correction carry
     `hMovingCorr` (the FIRST term → 0) recombine to the full `hBoundaryLim`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE F-FACT MAP (banked provider vs carried — honest).  `F := leviSeries (heatOp g gi Wit)`:

    • measurability of the frozen slice `z ↦ F t z 0`  — CARRIED `hf_meas`; banked provider
      `LeviSeriesLocalData.leviSeries_stronglyMeasurable_of_termwise` (and the joint version in
      `InnerMeasFubini`).  Satisfiable.
    • global boundedness `∃ Cf, ∀ z, |F t z 0| ≤ Cf`  — CARRIED `hf_bdd`; satisfiable from the Levi
      envelope `GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated`
      (`|F t z 0| ≤ C_L·gaussDdim (2t) (z−0) ≤ C_L·gaussDdim (2t) 0`, the Gaussian max at 0, finite for
      the fixed `t > 0`).
    • continuity at 0 `ContinuousAt (fun z => F t z 0) 0`  — CARRIED `hf_cont`; UNBANKED as a proven
      fact.  It is the SAME satisfiable continuity carry that `boundaryTrunc_tendsto` bundles as its
      `hBcont` (joint continuity of `F` on `Ioc 0 T × univ`); no repo lemma proves it for `leviSeries`
      at the concrete gate (the Levi series is a convergent series of continuous convolutions — the
      standard justification — but the continuity theorem is not banked).
    • (UNIF) the moving-correction limit  — CARRIED `hMovingCorr`:
        `Tendsto (fun m => BoundaryTrunc Wit F m t − ∫ z, Wit (ε_m) 0 z · F t z 0) atTop (𝓝 0)`.
      This is NOT the conclusion (that is `→ F t 0 0`); it is the genuine lower ingredient "the
      moving-`f` correction vanishes".  Satisfiable: on the compact time-window `[t/2, 2t] × closedBall`,
      `F` is uniformly continuous (from the joint-continuity carry above), so
      `sup_{z∈ball} |F (t−ε_m) z 0 − F t z 0| → 0`; combined with the bounded witness mass
      `∫ |Wit(ε_m) 0 ·| ≤ CW` (the zeroth wide domination `hDom` + `∫ gaussDdim = 1`) on the ball and the
      Gaussian-tail envelope off the ball (`GateAnnulusSplit.offBall_integral_tendsto_zero`-style), the
      correction integral → 0.  This assembly (uniform-continuity-on-compact + on/off-ball split) is the
      residual left for a follow-on brick; here it is carried, honestly labelled.

  ⚠  STILL NOT `a₁ = R/6`.  This brick lands (SEQ) + (FROZEN) — the W1-free second term of the boundary
  decomposition — and packages the full `hBoundaryLim` conditional only on the labelled (UNIF) carry.
-/
import QIQTH.GateAnnulusSplit
import QIQTH.TruncatedDuhamelData

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel
open scoped Topology

namespace QIQTH.MovingFBoundaryLim

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (SEQ) — the `ε_m`-composition of a `𝓝[>]0` limit.
    ############################################################################### -/

/-- **`epsSeq_tendsto_nhdsWithin`.**  The concrete `ε`-sequence `ε_m = 1/(m+1)` tends to `0` from
    ABOVE (`𝓝[>]0`): it tends to `0` (`epsSeq_tendsto`) and is eventually — indeed always — positive
    (`epsSeq_pos`).  The membership form needed to `Tendsto.comp` a `𝓝[>]0`-limit into an `atTop`
    sequence.  NOT `a₁ = R/6`. -/
theorem epsSeq_tendsto_nhdsWithin :
    Tendsto epsSeq atTop (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨epsSeq_tendsto, ?_⟩
  filter_upwards with m
  exact Set.mem_Ioi.mpr (epsSeq_pos m)

/-- **★ (SEQ) `tendsto_comp_epsSeq`.**  A fixed-`f` approximate identity is a `𝓝[>]0`-limit of the
    scale parameter `τ`; composing it with `ε_m → 0⁺` (`epsSeq_tendsto_nhdsWithin`) yields the `atTop`
    sequence limit along `ε_m`.  Kernel-agnostic bridge from the AI to the boundary-sequence form.
    `Tendsto.comp` only (no ascribed-lambda `ContinuousOn.comp`).  NOT `a₁ = R/6`. -/
theorem tendsto_comp_epsSeq {L : ℝ} {φ : ℝ → ℝ}
    (hφ : Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun m => φ (epsSeq m)) atTop (𝓝 L) :=
  hφ.comp epsSeq_tendsto_nhdsWithin

/-! ###############################################################################
    ### (FROZEN) — the fixed-`f` chart-image AI at the frozen Levi slice, sequenced.
    ############################################################################### -/

/-- **★★ (FROZEN) `frozenBoundary_tendsto`.**  The SECOND term of the 3ε decomposition, landed W1-free.
    Feeding the frozen Levi slice `f := fun z => leviSeries (heatOp g gi Wit) t z 0` (with
    `Wit := vanVleckGatedWitness g gi hC hK S a b`) into the J4-279 fixed-`f` chart-image approximate
    identity `GateAnnulusSplit.chartImage_approx_identity_final`, then composing the resulting `𝓝[>]0`
    concentration with `ε_m → 0⁺` (SEQ), gives the FROZEN boundary-sequence limit
        `Tendsto (fun m => ∫ z, Wit (ε_m) 0 z · F t z 0) atTop (𝓝 (F t 0 0))`.
    The hypothesis list is EXACTLY that of `chartImage_approx_identity_final` (standing geometry, metric
    carries, gauge, `0 < a < b`, the three F-facts of the frozen slice, the gate-activation carries, the
    witness-slice measurability, the zeroth wide domination) — all satisfiable, NONE Gaussian-at-`z`
    (`hAnear`), NONE the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem frozenBoundary_tendsto
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    (t : ℝ)
    -- the three F-facts of the FROZEN Levi slice `z ↦ leviSeries (heatOp g gi Wit) t z 0`:
    (hf_meas : Measurable
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0))
    (hf_bdd : ∃ Cf : ℝ, ∀ z,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0| ≤ Cf)
    (hf_cont : ContinuousAt
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0) 0)
    -- gate-activation carries (discharge `hGgate`, satisfiable via the openness exports):
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z)
    -- witness-slice measurability (for the split's integrability):
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z) volume)
    -- zeroth wide domination (discharge the annulus split):
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z) :
    Tendsto
      (fun m => ∫ z, vanVleckGatedWitness g gi hC hK S a b (epsSeq m) (0 : Point n) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0)
      atTop
      (𝓝 (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t 0 0)) := by
  obtain ⟨ρ, _hρ, hAI⟩ :=
    QIQTH.GateAnnulusSplit.chartImage_approx_identity_final
      g gi hC hK h0Kmem hg hgi hgpos S a b ha hab hgdet0
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0)
      hf_meas hf_bdd hf_cont
      rS hrS hKball hSact hWslice
      lam τ₀ CW hlam hτ₀ hCW hDom
  exact tendsto_comp_epsSeq hAI

/-! ###############################################################################
    ### (HB) — the full `hBoundaryLim` at the concrete gate (FROZEN + labelled UNIF).
    ############################################################################### -/

/-- **★★★ (HB) `hBoundaryLim_concrete`.**  The full boundary-limit member of the truncated-Duhamel
    pile at the concrete van-Vleck gate, W1-free:
        `Tendsto (fun m => BoundaryTrunc Wit F m t) atTop (𝓝 (F t 0 0))`,
    `Wit := vanVleckGatedWitness g gi hC hK S a b`,  `F := leviSeries (heatOp g gi Wit)`.
    Route: `BoundaryTrunc = (BoundaryTrunc − frozenInt) + frozenInt`, where `frozenInt` is the frozen
    integral of `frozenBoundary_tendsto` (→ `F t 0 0`); the first summand → `0` by the labelled
    moving-correction carry `hMovingCorr` (the (UNIF) term); `Tendsto.add` + `sub_add_cancel` recombine.

    `hMovingCorr` is NOT the conclusion (which is `→ F t 0 0`); it is the genuine (UNIF) ingredient
    "the moving-`f` correction vanishes" (`→ 0`), satisfiable via uniform-continuity-on-compact of `F` +
    the bounded witness mass + the Gaussian off-ball tail (see file header §F-FACT MAP).  All other
    hypotheses are exactly those of `frozenBoundary_tendsto`; NONE is `hAnear` (Gaussian-at-`z`), NONE is
    the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hBoundaryLim_concrete
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    (t : ℝ)
    (hf_meas : Measurable
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0))
    (hf_bdd : ∃ Cf : ℝ, ∀ z,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0| ≤ Cf)
    (hf_cont : ContinuousAt
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0) 0)
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z)
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z) volume)
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    -- (UNIF) the labelled moving-correction carry (→ 0; NOT the conclusion):
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
  have hFrozen := frozenBoundary_tendsto g gi hC hK h0Kmem hg hgi hgpos S a b ha hab hgdet0 t
    hf_meas hf_bdd hf_cont rS hrS hKball hSact hWslice lam τ₀ CW hlam hτ₀ hCW hDom
  have hsum := hMovingCorr.add hFrozen
  rw [zero_add] at hsum
  refine hsum.congr (fun m => ?_)
  ring

#check @frozenBoundary_tendsto
#check @hBoundaryLim_concrete

end QIQTH.MovingFBoundaryLim

section AxiomChecks
open QIQTH.MovingFBoundaryLim
#print axioms tendsto_comp_epsSeq
#print axioms frozenBoundary_tendsto
#print axioms hBoundaryLim_concrete
end AxiomChecks
