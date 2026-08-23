/-
  ChartOverlapConsumerTripleTwoSeeds — J4-1126: dispatch 4 of the "inverse-branch
  overlap-uniqueness bridge" sub-campaign (greenlit J4-1122, hub lemma J4-1123, two-seed
  `Set.EqOn` corollary J4-1124, open-overlap germ compatibility J4-1125, per gpt-5.6-sol high
  consult 2026-08-24 x4).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  Reads `ChartJointBorel.lean` (the ACTUAL `chartJoint_measurable_of_rep` /
  `tripleHEmeas_concrete_v2` / `a1_R6_assembled_v5` consumer) to determine precisely which
  derivative shape it needs from the overlap-agreement machinery. Every derivative hypothesis in
  `hcarField` / `hcarField2` is of the form

    `HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) jj)
      (Pfield w.2.2 w.2.1 jj) (w.2.1 k)`

  i.e. the BASE point `w.2.2` (the `q`-slot, first argument of `uniformInverseChart`) is held
  FIXED throughout, and the derivative is taken only in the SECOND (field-point `p`) argument,
  one coordinate at a time. `ChartJointBorel.lean` NEVER needs a full joint `fderiv` mixing both
  arguments — only this second-variable-only "fiber" derivative (base point frozen). Confirmed
  with `gpt-5.6-sol` (high, 2026-08-24, fourth consult): "the consumer needs derivatives only
  along curves `s ↦ uniformInverseChart ... q (Function.update p k s) jj` with `q` fixed... a
  coordinate-line derivative in the second-variable fiber," NOT the full joint derivative.

  ## The deliverable.

  `chartCoherent_consumer_triple_at_overlap_two_seeds` — same setup as J4-1125's germ-agreement
  lemma, with the overlap conclusion strengthened from a bare germ fact to the CONSUMER TRIPLE
  Sol specified for J4-1126: for every `ξ ∈ U1 ∩ U2`,
    (a) `chartCoherent1 ξ.1 ξ.2 = chartCoherent2 ξ.1 ξ.2` (value agreement, `hIn`-shaped),
    (b) `fderiv ℝ (fun p => chartCoherent1 ξ.1 p) ξ.2 = fderiv ℝ (fun p => chartCoherent2 ξ.1 p)
         ξ.2` (SECOND-VARIABLE-ONLY fiber-derivative agreement, base point `ξ.1` frozen — the
         derivative shape `ChartJointBorel.lean` actually consumes, NOT a joint fderiv),
    (c) `ξ ∈ U1 ∩ U2` (`hcar`-shaped carrier/overlap membership, restated for direct downstream
         `obtain`-consumption alongside (a)/(b)).

  Proof of (b): compose J4-1125's germ fact `(fun η => chartCoherent1 η.1 η.2) =ᶠ[nhds ξ]
  (fun η => chartCoherent2 η.1 η.2)` with the fiber-inclusion map `p ↦ (ξ.1, p)`, which is
  continuous and sends `ξ.2 ↦ ξ` (since `ξ = (ξ.1, ξ.2)`), via `Filter.EventuallyEq.comp_tendsto`;
  this yields the SLICED germ `(fun p => chartCoherent1 ξ.1 p) =ᶠ[nhds ξ.2]
  (fun p => chartCoherent2 ξ.1 p)`, to which `Filter.EventuallyEq.fderiv_eq` applies directly.
  Proof of (a): `Filter.Eventually.self_of_nhds` on the original (unsliced) germ. No new IFT/ODE
  analysis, no new quantitative/analytic estimate (confirmed with `gpt-5.6-sol`, high,
  2026-08-24: no sympy check triggered — pure filter/calculus congruence API).

  Per Sol's fourth consult, this `fderiv`-shaped lemma is a genuine, non-vacuous, sound
  intermediate step, but NOT yet the literal interface `hcarField`/`hcarField2` consume (those
  want per-coordinate `HasDerivAt` at `Function.update ξ.2 k s`, not a packaged `fderiv`). Sol's
  scoped plan for J4-1127 (next dispatch): transfer the germ fact along the COORDINATE-LINE map
  `s ↦ (ξ.1, Function.update ξ.2 k s)` directly (via `EventuallyEq.comp_tendsto` +
  `Filter.EventuallyEq.hasDerivAt_iff`), producing the literal
  `HasDerivAt (fun s => chartCoherent1 ξ.1 (Function.update ξ.2 k s) jj) d (ξ.2 k) ↔
   HasDerivAt (fun s => chartCoherent2 ξ.1 (Function.update ξ.2 k s) jj) d (ξ.2 k)`
  transfer lemma, plus the analogous `uniformInverseChart ↔ chartCoherentᵢ` transfer on each `Uᵢ`,
  which together let a representative's derivative data (`Pfield`, `Pifield`, `Pjfield`,
  `Qfield`) discharge `hcarField`/`hcarField2` without ever invoking a full joint `fderiv`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. Pure logical/filter/calculus-congruence upgrade built on
  the already-banked `ChartOverlapGermCompatibilityTwoSeeds.lean` germ fact — no new analytic
  estimate, no `sorry`, no new axioms, no vacuous/unsatisfiable hypotheses (the overlap
  `U1 ∩ U2` is not asserted nonempty; the conclusion is the correct CONDITIONAL "for every `ξ` in
  the overlap, the consumer triple holds" shape), no existing file edited. `a₁ = R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ChartOverlapGermCompatibilityTwoSeeds

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★ J4-1126 — `chartCoherent_consumer_triple_at_overlap_two_seeds`: target-facing
    value/derivative/carrier consumer triple.** At the SAME uniform radius `r₀` from the hub
    lemma, for any TWO seeds `(z₀,v₀)` and `(z₀',v₀')` (both `z₀, z₀' ∈ interior K`, both
    velocities `< r₀`), there are coherently-built charts `chartCoherent1`, `chartCoherent2` and
    OPEN neighbourhoods `U1 ∋ (z₀, exp z₀ v₀)`, `U2 ∋ (z₀', exp z₀' v₀')` on which
    `uniformInverseChart` agrees with `chartCoherent1`, resp. `chartCoherent2` (`Set.EqOn`), such
    that for EVERY `ξ ∈ U1 ∩ U2` the CONSUMER TRIPLE holds: value agreement, SECOND-VARIABLE-ONLY
    fiber-derivative agreement (base point `ξ.1` frozen — the exact shape `ChartJointBorel.lean`
    consumes, not a joint `fderiv`), and carrier membership. -/
theorem chartCoherent_consumer_triple_at_overlap_two_seeds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ),
      ∀ z₀ : Point n, z₀ ∈ interior K → ∀ v₀ : Point n, ‖v₀‖ < r₀ →
      ∀ z₀' : Point n, z₀' ∈ interior K → ∀ v₀' : Point n, ‖v₀'‖ < r₀ →
      ∃ chartCoherent1 chartCoherent2 : Point n → Point n → Point n,
      ∃ U1 : Set (Point n × Point n), IsOpen U1 ∧
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ U1 ∧
      ∃ U2 : Set (Point n × Point n), IsOpen U2 ∧
        ((z₀', uniformFlowExp g gi hC hK z₀' v₀') : Point n × Point n) ∈ U2 ∧
        Set.EqOn (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2)
          (fun ξ : Point n × Point n => chartCoherent1 ξ.1 ξ.2) U1 ∧
        Set.EqOn (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2)
          (fun ξ : Point n × Point n => chartCoherent2 ξ.1 ξ.2) U2 ∧
        ∀ ξ ∈ U1 ∩ U2,
          chartCoherent1 ξ.1 ξ.2 = chartCoherent2 ξ.1 ξ.2 ∧
          fderiv ℝ (fun p : Point n => chartCoherent1 ξ.1 p) ξ.2
            = fderiv ℝ (fun p : Point n => chartCoherent2 ξ.1 p) ξ.2 ∧
          ξ ∈ U1 ∩ U2 := by
  classical
  obtain ⟨r₀, hr₀pos, hall⟩ := chartCoherent_germ_agree_at_overlap_two_seeds g gi hC hK
  refine ⟨r₀, hr₀pos, ?_⟩
  intro z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  obtain ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem,
    hEqOn1, hEqOn2, hgermAll⟩ := hall z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  refine ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem,
    hEqOn1, hEqOn2, ?_⟩
  intro ξ hξ
  have hgerm := hgermAll ξ hξ
  refine ⟨hgerm.self_of_nhds, ?_, hξ⟩
  -- Slice the joint germ down to the `ξ.1`-fixed fiber via the continuous inclusion `p ↦ (ξ.1, p)`.
  have hcont : Filter.Tendsto (fun p : Point n => ((ξ.1, p) : Point n × Point n))
      (nhds ξ.2) (nhds ξ) := by
    have h1 : Filter.Tendsto (fun _ : Point n => ξ.1) (nhds ξ.2) (nhds ξ.1) :=
      tendsto_const_nhds
    have h2 : Filter.Tendsto (id : Point n → Point n) (nhds ξ.2) (nhds ξ.2) := Filter.tendsto_id
    have hprod := h1.prodMk h2
    rw [← nhds_prod_eq] at hprod
    simpa [Prod.mk.eta] using hprod
  have hsliced : (fun p : Point n => chartCoherent1 ξ.1 p)
      =ᶠ[nhds ξ.2] (fun p : Point n => chartCoherent2 ξ.1 p) :=
    hgerm.comp_tendsto hcont
  exact hsliced.fderiv_eq

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms chartCoherent_consumer_triple_at_overlap_two_seeds
end AxiomChecks
