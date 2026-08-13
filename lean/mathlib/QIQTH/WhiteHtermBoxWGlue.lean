/-
  WhiteHtermBoxWGlue — J4-711 (Route (β) BRICK 2): THE VANISHING-LEG GLUE — the POINTWISE
  dominated-continuity interface that breaks the box-uniform reach wall.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE WALL RESTATED (J4-709 `WhiteHtermBoxReach.uniform_reach_bound_unsat`).  The banked per-level
     recursion engine `InnerEngineRecursion.innerStep_cont_ae` discharges the inner convolution-step
     continuity `(τ,z) ↦ ∫ w, E (τ−τ·u) z w · iterE E k (τ·u) w 0` through the Gap-A slot
        `hcontE : ∀ᵐ u, ∀ᵐ w, ContinuousOn (fun p => E (p.1−p.1·u) p.2 w) (Icc ×ˢ closedBall 0 R)`,
     i.e. via Mathlib's `continuousOn_of_dominated`, whose continuity input is the BOX-UNIFORM a.e.-`w`
     slot `∀ᵐ w, ContinuousOn (E · · w) (box)`.  At the concrete flow gate `S w = flowExp_w '' ball 0 c`
     the whitened kernel `whiteDefectKernel … τ p w` carries a HARD spatial indicator `p ∈ S w`
     (`gatedKernel … = if p ∈ S w then heatOp … else 0`, `GlobalHunifAssembly.gatedKernel`), so
     `p ↦ whiteDefectKernel … τ p w` is genuinely DISCONTINUOUS at every `p ∈ frontier (S w)` where the
     underlying heat defect is nonzero.

  ── THE HONEST CRUX VERDICT (the boundary-dichotomy, precisely).  For a box `Icc ×ˢ K` with `K` LARGE
     (radius up to the level-`k` support `M + k·ρ`), the BOX-UNIFORM slot `∀ᵐ w, ContinuousOn (E · · w)
     (Icc ×ˢ K)` is UNSATISFIABLE: as `w` ranges over the compact base set `Kset`, the gate frontiers
     `frontier (S w)` are all bounded and, for `K` large enough to contain them, `frontier (S w) ∩ K ≠ ∅`
     for a POSITIVE-measure set of bases `w` — each such `w` breaks `ContinuousOn` on the WHOLE box at its
     boundary point.  The bad-`w` set is NOT null; the box-uniform a.e.-`w` slot is the WRONG interface,
     and the "null boundary" fact `∀ z₀, volume {w | z₀ ∈ frontier (S w)} = 0` (quantifiers `∀z₀ ∀ᵐw`)
     cannot repair it (quantifier order: box continuity fixes `w` first and quantifies over all `p∈K`).

     THE FIX (this brick).  Mathlib's POINTWISE engine `continuousWithinAt_of_dominated` needs only the
     POINTWISE slot `h_cont : ∀ᵐ w, ContinuousWithinAt (E · · w) s p₀` — the continuity is required only
     AT the evaluation point `p₀`, for a.e. `w`.  With the field point `z₀ := p₀.2` FIXED, the bad-`w`
     set `{w | z₀ ∈ frontier (S w)}` IS null (the null-frontier certificate `hnull`, provable at the
     flow gate — the ball witness `S w = ball w c` gives `frontier (S w) = sphere w c`, so
     `{w | z₀ ∈ sphere w c} = sphere z₀ c`, Lebesgue-null in dimension `n ≥ 1`).  Off that null set the
     TRICHOTOMY closes: `z₀ ∈ interior (S w)` (in-gate — the J4-710 set-generic `_at_set` capstone on a
     small ball ⟹ `ContinuousWithinAt`, carried labelled as `hInterior`) OR `z₀ ∉ closure (S w)`
     (exterior — the off-gate vanishing `whiteGated_heatOp_zero_offGate` makes `E ≡ 0` on a spatial
     neighbourhood, hence `ContinuousWithinAt` unconditionally).  Then `ContinuousWithinAt` at EVERY
     `p₀ ∈ Icc ×ˢ K` reassembles `ContinuousOn (Icc ×ˢ K)` — the box continuity we want — WITHOUT the
     unsatisfiable box-uniform a.e.-`w` slot.  The uniform-reach wall is GONE; the residue is the honest
     `hnull` (null-frontier, a codim-1 sphere-image cert — LABELLED) and `hInterior` (the in-gate leg,
     the J4-710 set-generic substrate — LABELLED).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `contOn_integral_of_ae_continuousWithinAt` — ★ THE POINTWISE GLUE ENGINE (kernel-generic): box
      `ContinuousOn (fun p => ∫ w, F p w)` from the POINTWISE a.e.-`w` `ContinuousWithinAt` slot + a
      `p`-uniform integrable dominator, via `continuousWithinAt_of_dominated` at every box point.  This
      is the drop-in replacement for the box-uniform `continuousOn_of_dominated` interface.
    * `ae_continuousWithinAt_of_null_frontier` — ★ THE DICHOTOMY→a.e. STEP: from a null-frontier cert
      `volume {w | z₀ ∈ Fr w} = 0` and a per-`w` off-frontier continuity `hgood`, the pointwise
      a.e.-`w` `ContinuousWithinAt` slot.
    * `whiteDefectKernel_continuousWithinAt_offFrontier` — ★ THE CONCRETE per-`w` DICHOTOMY at the
      whitened kernel: for `z₀ := p₀.2 ∉ frontier (S w)`, `ContinuousWithinAt` of the convolution
      integrand `whiteDefectKernel … (τ−τ·u) z w · iterE … w 0`, gluing the exterior/off-base VANISHING
      legs (proved) to the in-gate `hInterior` leg (carried labelled).
    * `null_frontier_ball_satisfiable` — cp466: the null-frontier cert is INHABITED NON-vacuously at the
      genuine ball gate `S w = ball w c` (frontier `= sphere w c` nonempty for `c > 0`, yet the per-`z₀`
      `w`-slice is the Lebesgue-null sphere `sphere z₀ c`, `n ≥ 1`).
    * `pointwise_glue_package_satisfiable` — cp466: the pointwise-glue hypothesis package is jointly
      inhabited (`F ≡ 0`), so the engine is not vacuously conditional.

  ⚠  HONEST FIREWALL.  Pointwise dominated-continuity GLUE + the boundary-dichotomy crux verdict ONLY.
  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` is a labelled carrier,
  untouched).  The box continuity is CONDITIONAL on the labelled `hnull` (null-frontier) and `hInterior`
  (in-gate) certificates — each satisfiable / non-vacuous (cp466) and characterised, NOT papered over.
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  hypothesis equal to (or trivially yielding) the conclusion, no existing file edited, nothing
  committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.
-/
import Mathlib
import QIQTH.WhiteHtermBoxW0
import QIQTH.WhiteHJetContWSet

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open QIQTH.WhiteHtermBoxW0
open scoped Topology

namespace QIQTH.WhiteHtermBoxWGlue

variable {n : ℕ}

/-! ###############################################################################
    ### §A — ★ THE POINTWISE GLUE ENGINE (kernel-generic).
    ############################################################################### -/

/-- **★ `contOn_integral_of_ae_continuousWithinAt`.**  Box `ContinuousOn` of a parametric integral
    `p ↦ ∫ w, F p w` from the POINTWISE a.e.-`w` `ContinuousWithinAt` slot, via Mathlib's
    `continuousWithinAt_of_dominated` applied at every point of the box.  This is the drop-in
    replacement for the box-uniform `continuousOn_of_dominated` interface: its continuity input
    `hcont` fixes the evaluation point `p₀` FIRST and only needs a.e.-`w` continuity THERE — the
    interface the boundary-dichotomy can satisfy (`ae_continuousWithinAt_of_null_frontier`).
    NOT `a₁ = R/6`. -/
theorem contOn_integral_of_ae_continuousWithinAt
    (F : (ℝ × Point n) → Point n → ℝ) (s : Set (ℝ × Point n)) (bound : Point n → ℝ)
    (hbound_int : Integrable bound volume)
    (hmeas : ∀ p ∈ s, AEStronglyMeasurable (F p) volume)
    (hbound : ∀ p ∈ s, ∀ᵐ w ∂volume, ‖F p w‖ ≤ bound w)
    (hcont : ∀ p₀ ∈ s, ∀ᵐ w ∂volume, ContinuousWithinAt (fun p => F p w) s p₀) :
    ContinuousOn (fun p => ∫ w, F p w) s := by
  intro p₀ hp₀
  refine continuousWithinAt_of_dominated ?_ ?_ hbound_int (hcont p₀ hp₀)
  · exact eventually_nhdsWithin_of_forall (fun p hp => hmeas p hp)
  · exact eventually_nhdsWithin_of_forall (fun p hp => hbound p hp)

/-! ###############################################################################
    ### §B — ★ THE DICHOTOMY → a.e.-`w` step (null frontier removes the bad `w`).
    ############################################################################### -/

/-- **★ `ae_continuousWithinAt_of_null_frontier`.**  Given a per-base "bad set" family `Fr` (to be
    instantiated at `Fr w := frontier (S w)`), a null-frontier certificate
    `volume {w | z₀ ∈ Fr w} = 0`, and a per-`w` off-frontier continuity `hgood`, the POINTWISE a.e.-`w`
    `ContinuousWithinAt` slot at `p₀`.  The bad `w` (those with `z₀ ∈ Fr w`) form a null set, so a.e.
    `w` are good.  This is the exact `hcont`-fibre `contOn_integral_of_ae_continuousWithinAt` needs.
    NOT `a₁ = R/6`. -/
theorem ae_continuousWithinAt_of_null_frontier
    (F : (ℝ × Point n) → Point n → ℝ) (s : Set (ℝ × Point n)) (p₀ : ℝ × Point n)
    (z₀ : Point n) (Fr : Point n → Set (Point n))
    (hnull : volume {w : Point n | z₀ ∈ Fr w} = 0)
    (hgood : ∀ w : Point n, z₀ ∉ Fr w → ContinuousWithinAt (fun p => F p w) s p₀) :
    ∀ᵐ w ∂volume, ContinuousWithinAt (fun p => F p w) s p₀ := by
  have hae : {w : Point n | z₀ ∉ Fr w} ∈ ae volume := by
    rw [mem_ae_iff]
    have hcompl : {w : Point n | z₀ ∉ Fr w}ᶜ = {w : Point n | z₀ ∈ Fr w} := by
      ext w; simp
    rw [hcompl]; exact hnull
  filter_upwards [hae] with w hw
  exact hgood w hw

/-! ###############################################################################
    ### §C — cp466 satisfiability: the null-frontier cert at the genuine ball gate.
    ############################################################################### -/

/-- **`null_frontier_ball_satisfiable`** (cp466 discipline).  The null-frontier certificate is
    INHABITED NON-vacuously at the genuine ball gate `S w = Metric.ball w c`: `frontier (ball w c)`
    is the sphere `sphere w c` (nonempty for `c > 0`), YET the per-`z₀` `w`-slice
    `{w | z₀ ∈ frontier (ball w c)}` lies in the sphere `sphere z₀ c`, which is Lebesgue-null in
    dimension `n ≥ 1` (`Measure.addHaar_sphere`).  So `hnull` is a real, satisfiable geometric input,
    not a vacuous one.  NOT `a₁ = R/6`. -/
theorem null_frontier_ball_satisfiable (hn : 0 < n) (z₀ : Point n) (c : ℝ) :
    volume {w : Point n | z₀ ∈ frontier (Metric.ball w c)} = 0 := by
  haveI : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Point n) := Pi.nontrivial
  refine measure_mono_null ?_ (Measure.addHaar_sphere volume z₀ c)
  intro w hw
  have hmem : z₀ ∈ Metric.sphere w c := Metric.frontier_ball_subset_sphere hw
  rw [Metric.mem_sphere] at hmem
  rw [Metric.mem_sphere, dist_comm]
  exact hmem

/-! ###############################################################################
    ### §D — ★ THE CONCRETE per-`w` DICHOTOMY at the whitened defect kernel.
    ############################################################################### -/

/-- **★ `whiteDefectKernel_continuousWithinAt_offFrontier`.**  The concrete per-`w` off-frontier
    continuity of the convolution-step integrand at a box point `p₀`, with field point `z₀ := p₀.2`.
    For `z₀ ∉ frontier (S w)` the trichotomy closes:
      • `w ∉ Kset` (off-base) — `whiteDefectKernel … · w ≡ 0`, so the integrand `≡ 0` near `p₀`;
      • `z₀ ∉ closure (S w)` (exterior) — off-gate vanishing (`whiteGated_heatOp_zero_offGate`) makes
        `whiteDefectKernel … · w ≡ 0` on a spatial neighbourhood of `z₀`, so the integrand `≡ 0` near `p₀`;
      • `z₀ ∈ interior (S w)` (in-gate) — the labelled `hInterior` leg (the J4-710 set-generic `_at_set`
        capstone on a small ball supplies this `ContinuousWithinAt`; carried as an honest certificate).
    The two vanishing legs are PROVED here (side-condition-free); the in-gate leg is the J4-710 substrate,
    carried labelled.  ⚠ CONDITIONAL on `hInterior`.  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_continuousWithinAt_offFrontier (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b u : ℝ)
    (k : ℕ) (s : Set (ℝ × Point n)) (p₀ : ℝ × Point n)
    (hInterior : ∀ w : Point n, w ∈ Kset → p₀.2 ∈ interior (S w) →
      ContinuousWithinAt
        (fun p : ℝ × Point n =>
          whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
            * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0) s p₀)
    (w : Point n) (hfr : p₀.2 ∉ frontier (S w)) :
    ContinuousWithinAt
      (fun p : ℝ × Point n =>
        whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
          * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0) s p₀ := by
  -- Local vanishing helper: an OPEN spatial `V ∋ p₀.2` on which the kernel head is identically `0`
  -- (for every time) ⟹ the whole integrand `≡ 0` on `univ ×ˢ V` ⟹ `ContinuousWithinAt` via `≡ const 0`.
  have hvanish : ∀ V : Set (Point n), IsOpen V → p₀.2 ∈ V →
      (∀ z ∈ V, ∀ τ : ℝ, whiteDefectKernel κ hκ hKc S a b τ z w = 0) →
      ContinuousWithinAt
        (fun p : ℝ × Point n =>
          whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
            * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0) s p₀ := by
    intro V hVopen hz₀V hker0
    have hopenP : IsOpen ((Set.univ : Set ℝ) ×ˢ V) := isOpen_univ.prod hVopen
    have hp₀P : p₀ ∈ (Set.univ : Set ℝ) ×ˢ V := ⟨Set.mem_univ _, hz₀V⟩
    have heq : (fun p : ℝ × Point n =>
          whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
            * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0)
        =ᶠ[𝓝 p₀] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopenP.mem_nhds hp₀P] with p hp
      rw [hker0 p.2 hp.2 (p.1 - p.1 * u), zero_mul]
    refine continuousWithinAt_const.congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) ?_
    have : whiteDefectKernel κ hκ hKc S a b (p₀.1 - p₀.1 * u) p₀.2 w = 0 :=
      hker0 p₀.2 hz₀V (p₀.1 - p₀.1 * u)
    rw [this, zero_mul]
  -- trichotomy off the frontier: `interior (S w)` (in-gate) vs `(closure (S w))ᶜ` (exterior).
  have hdi : p₀.2 ∈ interior (S w) ∨ p₀.2 ∉ closure (S w) := by
    rcases em (p₀.2 ∈ interior (S w)) with h | h
    · exact Or.inl h
    · exact Or.inr (fun hc => hfr ⟨hc, h⟩)
  by_cases hwK : w ∈ Kset
  · rcases hdi with hint | hext
    · -- in-gate: carried labelled.
      exact hInterior w hwK hint
    · -- exterior: off-gate vanishing on the open set `(closure (S w))ᶜ`.
      have hz₀c : p₀.2 ∈ (closure (S w))ᶜ := hext
      have hVsub : (closure (S w))ᶜ ⊆ {p' : Point n | p' ∉ S w} :=
        fun x hx hxS => hx (subset_closure hxS)
      refine hvanish (closure (S w))ᶜ isClosed_closure.isOpen_compl hz₀c ?_
      intro z hzV τ
      have hoff : {p' : Point n | p' ∉ S w} ∈ nhds z :=
        Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hzV) hVsub
      by_cases hτ : 0 < τ ∧ τ ≤ 1
      · rw [whiteDefectKernel_eq κ hκ hKc S a b hτ.1 hτ.2 z w]
        exact whiteGated_heatOp_zero_offGate κ hκ hKc S a b τ z w (Or.inr hoff)
      · simp only [whiteDefectKernel, if_neg hτ]
  · -- off-base: kernel identically `0` on all of `Point n`.
    refine hvanish Set.univ isOpen_univ (Set.mem_univ _) ?_
    intro z _ τ
    by_cases hτ : 0 < τ ∧ τ ≤ 1
    · rw [whiteDefectKernel_eq κ hκ hKc S a b hτ.1 hτ.2 z w]
      exact whiteGated_heatOp_zero_offGate κ hκ hKc S a b τ z w (Or.inl hwK)
    · simp only [whiteDefectKernel, if_neg hτ]

/-! ###############################################################################
    ### §E — cp466 satisfiability of the pointwise-glue hypothesis package.
    ############################################################################### -/

/-- **`pointwise_glue_package_satisfiable`** (cp466 discipline).  The pointwise-glue engine's
    hypothesis package is jointly inhabited — witnessed at `F ≡ 0`, `bound ≡ 0`: the integrable
    dominator, the a.e. bound, the strong measurability, and the pointwise a.e.-`w` `ContinuousWithinAt`
    slot all hold, and the conclusion `ContinuousOn (fun _ => ∫ w, 0) s` is the genuine (constant)
    output.  So `contOn_integral_of_ae_continuousWithinAt` is not vacuously conditional.
    NOT `a₁ = R/6`. -/
theorem pointwise_glue_package_satisfiable (s : Set (ℝ × Point n)) :
    ∃ (F : (ℝ × Point n) → Point n → ℝ) (bound : Point n → ℝ),
      Integrable bound volume ∧
      (∀ p ∈ s, AEStronglyMeasurable (F p) volume) ∧
      (∀ p ∈ s, ∀ᵐ w ∂volume, ‖F p w‖ ≤ bound w) ∧
      (∀ p₀ ∈ s, ∀ᵐ w ∂volume, ContinuousWithinAt (fun p => F p w) s p₀) := by
  refine ⟨fun _ _ => 0, fun _ => 0, integrable_zero _ _ _, ?_, ?_, ?_⟩
  · exact fun p _ => aestronglyMeasurable_const
  · exact fun p _ => Filter.Eventually.of_forall (fun w => by simp)
  · exact fun p₀ _ => Filter.Eventually.of_forall (fun w => continuousWithinAt_const)

/-! ###############################################################################
    ### §F — ★★★ THE ASSEMBLED VANISHING-LEG GLUE: box continuity via the pointwise route.
    ############################################################################### -/

/-- **★★★ `whiteConvStep_contOn_of_null_frontier` — THE ASSEMBLED GLUE.**  Box `ContinuousOn` of the
    whitened convolution step `(τ,z) ↦ ∫ w, whiteDefectKernel … (τ−τ·u) z w · iterE … w 0` on `Icc ×ˢ K`,
    obtained through the POINTWISE dominated-continuity route (§A) + the null-frontier dichotomy (§B) +
    the concrete per-`w` trichotomy (§D).  The BOX-UNIFORM reach wall
    (`WhiteHtermBoxReach.uniform_reach_bound_unsat`) is BYPASSED: `K` may be arbitrarily large.
    The residue is exactly the two labelled certificates —
      • `hnull` — the null-frontier cert `∀ z₀, volume {w | z₀ ∈ frontier (S w)} = 0` (satisfiable at the
        genuine ball gate, `null_frontier_ball_satisfiable`);
      • `hInterior` — the in-gate `ContinuousWithinAt` at each interior field point (the J4-710
        set-generic `_at_set` substrate; carried labelled per box point);
    plus the standard dominated-convergence data (`hbound_int`, `hmeas`, `hbound`).  ⚠ CONDITIONAL on the
    two labelled geometric certificates.  NOT `a₁ = R/6`. -/
theorem whiteConvStep_contOn_of_null_frontier (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b u : ℝ)
    (k : ℕ) (t₁ t₂ : ℝ) (K : Set (Point n)) (bound : Point n → ℝ)
    (hbound_int : Integrable bound volume)
    (hmeas : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ K),
      AEStronglyMeasurable
        (fun w => whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
          * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0) volume)
    (hbound : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ K), ∀ᵐ w ∂volume,
      ‖whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
          * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0‖ ≤ bound w)
    (hnull : ∀ z₀ : Point n, volume {w : Point n | z₀ ∈ frontier (S w)} = 0)
    (hInterior : ∀ p₀ ∈ (Set.Icc t₁ t₂ ×ˢ K), ∀ w : Point n, w ∈ Kset →
        p₀.2 ∈ interior (S w) →
      ContinuousWithinAt
        (fun p : ℝ × Point n =>
          whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
            * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ K) p₀) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        ∫ w, whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
          * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0)
      (Set.Icc t₁ t₂ ×ˢ K) := by
  refine contOn_integral_of_ae_continuousWithinAt _ _ bound hbound_int hmeas hbound ?_
  intro p₀ hp₀
  refine ae_continuousWithinAt_of_null_frontier _ _ p₀ p₀.2 (fun w => frontier (S w))
    (hnull p₀.2) ?_
  intro w hfr
  exact whiteDefectKernel_continuousWithinAt_offFrontier κ hκ hKc S a b u k
    (Set.Icc t₁ t₂ ×ˢ K) p₀ (hInterior p₀ hp₀) w hfr

#check @contOn_integral_of_ae_continuousWithinAt
#check @ae_continuousWithinAt_of_null_frontier
#check @null_frontier_ball_satisfiable
#check @whiteDefectKernel_continuousWithinAt_offFrontier
#check @pointwise_glue_package_satisfiable
#check @whiteConvStep_contOn_of_null_frontier

end QIQTH.WhiteHtermBoxWGlue

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHtermBoxWGlue
#print axioms contOn_integral_of_ae_continuousWithinAt
#print axioms ae_continuousWithinAt_of_null_frontier
#print axioms null_frontier_ball_satisfiable
#print axioms whiteDefectKernel_continuousWithinAt_offFrontier
#print axioms pointwise_glue_package_satisfiable
#print axioms whiteConvStep_contOn_of_null_frontier
end AxiomChecks
