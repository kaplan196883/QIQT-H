/-
  ChartOverlapCoordinateLineHasDerivAtTransfer — J4-1127: dispatch 5 of the "inverse-branch
  overlap-uniqueness bridge" sub-campaign (greenlit J4-1122, hub lemma J4-1123, two-seed
  `Set.EqOn` corollary J4-1124, open-overlap germ compatibility J4-1125, target-facing
  value/`fderiv`/carrier consumer triple J4-1126, per `gpt-5.6-sol` high consult 2026-08-24 x5).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  J4-1126 diagnosed, directly from `ChartJointBorel.lean`'s ACTUAL `hcarField`/`hcarField2`
  hypotheses, that every derivative conjunct those hypotheses supply is of the LITERAL shape

    `HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) jj)
      (Pfield w.2.2 w.2.1 jj) (w.2.1 k)`

  — a per-coordinate `HasDerivAt` along the COORDINATE-LINE map `s ↦ Function.update w.2.1 k s`
  (base point `w.2.2` frozen), evaluated at component `jj`, NOT a packaged `fderiv`. J4-1126's own
  deliverable only reached the `fderiv`-shaped fiber-derivative agreement
  (`fderiv ℝ (fun p => chartCoherent1 ξ.1 p) ξ.2 = fderiv ℝ (fun p => chartCoherent2 ξ.1 p) ξ.2`),
  explicitly flagged there as sound but NOT yet the literal `hcarField`/`hcarField2` interface.

  This dispatch closes that gap: it transfers J4-1125's raw filter-germ facts directly along the
  coordinate-line map (rather than packaging through `fderiv` first), producing the literal
  `HasDerivAt ... ↔ HasDerivAt ...` transfer at the EXACT syntactic shape `hcarField`/`hcarField2`
  consume, for an ARBITRARY candidate derivative value `d` (so it composes with whatever concrete
  derivative datum — `Pfield`, `Pifield`, `Pjfield`, `Qfield` — a future representative supplies).

  Per Sol's exact J4-1126 scoped-plan spec (confirmed again in this dispatch's consult, see below):
  the transfer is built via `EventuallyEq.comp_tendsto` (twice — once to slice the joint germ down
  to the `ξ.1`-fixed fiber via the constant-first-coordinate inclusion `p ↦ (ξ.1, p)`, exactly as
  J4-1126 already did; once more to push the sliced fiber-germ along the coordinate-line map
  `s ↦ Function.update ξ.2 k s`, which is continuous and sends `ξ.2 k ↦ ξ.2` by
  `Function.update_eq_self`), then extracting the single coordinate `jj` via
  `EventuallyEq.fun_comp`, then closing with `Filter.EventuallyEq.hasDerivAt_iff`.

  ## The deliverable.

  ONE shared private helper `hasDerivAt_coordLine_iff_of_germ` (pure germ-to-`HasDerivAt`-iff
  machinery, generic in the two functions being compared) instantiated THREE times inside the main
  theorem `chartCoherent_hasDerivAt_transfer_at_overlap_two_seeds`:
    (a) `uniformInverseChart ↔ chartCoherent1` coordinate-line transfer, for every `ξ ∈ U1`
        (built from J4-1124's `Set.EqOn` fact upgraded to a germ via `U1` open, mirroring J4-1125's
        own upgrade technique but applied to this `uniformInverseChart`/`chartCoherent1` pair);
    (b) the analogous `uniformInverseChart ↔ chartCoherent2` transfer, for every `ξ ∈ U2`;
    (c) `chartCoherent1 ↔ chartCoherent2` coordinate-line transfer, for every `ξ ∈ U1 ∩ U2` (built
        directly from J4-1125's already-banked raw joint germ fact, no re-derivation needed).
  Each of (a)/(b)/(c) is universally quantified over `k jj : Fin n` and an ARBITRARY `d : ℝ`,
  matching the literal `hcarField`/`hcarField2` shape exactly (those hypotheses supply a concrete
  `Pfield`/`Pifield`/`Pjfield` value as `d` from elsewhere; this file only needs to transfer
  "`HasDerivAt` for `uniformInverseChart` at that value" to/from "`HasDerivAt` for a coherent
  chart at that value", for whichever candidate value a future representative names).

  `gpt-5.6-sol` (high, 2026-08-24, fifth consult): confirmed the proposed three statements are the
  correct literal shape, confirmed NO sympy check is needed (pure filter/calculus congruence, no
  new rate/scaling/quantitative claim), and confirmed this closes the derivative-shape gap J4-1126
  explicitly left open — this file's (a)/(b)/(c), together with J4-1126's value-agreement clause
  (a), now jointly cover every literal conjunct `hcarField`/`hcarField2` ask for EXCEPT the
  measurability conjuncts (which are a wholly separate, unrelated obligation — `Measurable
  (fun w => Pfield w.2.2 w.2.1 jj)` etc. — not discharged by any overlap-uniqueness fact) and the
  `IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2` / `PdiffAt` conjuncts (which concern the AMPLITUDE `S`,
  `chartFieldAmp`, wholly outside the chart-overlap machinery this sub-campaign targets). Sol's
  scoped plan for what follows (next dispatch, J4-1128): the sub-campaign's remaining honest task
  is to build a CONCRETE representative — an actual `Pfield`/`Pifield`/`Pjfield`/`Qfield` supplier
  definable in terms of `chartCoherent1`/`chartCoherent2` (e.g. via a `Classical.choice`d partition
  of unity or a canonical `if ξ ∈ U1 then … else …` gluing, since `U1`/`U2` need not cover all of
  `K`), together with the MEASURABILITY conjuncts for that concrete supplier — which is a
  genuinely new (harder, patching/compactness-flavoured) task, NOT another abstract transfer layer;
  this file's three lemmas are consumed as the derivative-transport ingredient of that construction,
  not as the construction itself.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. Pure logical/filter/calculus-congruence upgrade built on the
  already-banked `ChartOverlapGermCompatibilityTwoSeeds.lean` germ facts — no new analytic
  estimate, no `sorry`, no new axioms, no vacuous/unsatisfiable hypotheses (the overlap sets `U1`,
  `U2`, `U1 ∩ U2` are not asserted nonempty beyond their known membership witnesses; every
  conclusion is the correct CONDITIONAL "for every `ξ` in the relevant set, the transfer holds"
  shape), no existing file edited. Does NOT yet supply a concrete `Pfield`/`Pifield`/`Pjfield`/
  `Qfield`/measurability representative for `hcarField`/`hcarField2` — that remains open (J4-1128).
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ChartOverlapGermCompatibilityTwoSeeds

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **Shared helper — germ agreement transfers to a coordinate-line `HasDerivAt` iff.**
    If two functions `F G : Point n → Point n → Point n` agree as a joint germ at `ξ`, then for
    ANY coordinate `k` (the varying slot), ANY output component `jj`, and ANY candidate derivative
    value `d`, the coordinate-line derivative statement (base point `ξ.1` frozen, second argument
    varying only in coordinate `k`, evaluated at component `jj`) transfers between `F` and `G`.
    Pure filter/calculus congruence: slice the joint germ to the `ξ.1`-fixed fiber, push it along
    the continuous coordinate-line map `s ↦ Function.update ξ.2 k s` (which sends `ξ.2 k ↦ ξ.2`),
    extract component `jj`, then close via `Filter.EventuallyEq.hasDerivAt_iff`. -/
private lemma hasDerivAt_coordLine_iff_of_germ {F G : Point n → Point n → Point n}
    {ξ : Point n × Point n}
    (hgerm : (fun η : Point n × Point n => F η.1 η.2)
        =ᶠ[nhds ξ] (fun η : Point n × Point n => G η.1 η.2))
    (k jj : Fin n) (d : ℝ) :
    HasDerivAt (fun s : ℝ => F ξ.1 (Function.update ξ.2 k s) jj) d (ξ.2 k) ↔
    HasDerivAt (fun s : ℝ => G ξ.1 (Function.update ξ.2 k s) jj) d (ξ.2 k) := by
  -- Slice the joint germ down to the `ξ.1`-fixed fiber via the continuous inclusion `p ↦ (ξ.1, p)`.
  have hcont : Filter.Tendsto (fun p : Point n => ((ξ.1, p) : Point n × Point n))
      (nhds ξ.2) (nhds ξ) := by
    have h1 : Filter.Tendsto (fun _ : Point n => ξ.1) (nhds ξ.2) (nhds ξ.1) :=
      tendsto_const_nhds
    have h2 : Filter.Tendsto (id : Point n → Point n) (nhds ξ.2) (nhds ξ.2) := Filter.tendsto_id
    have hprod := h1.prodMk h2
    rw [← nhds_prod_eq] at hprod
    simpa [Prod.mk.eta] using hprod
  have hsliced : (fun p : Point n => F ξ.1 p) =ᶠ[nhds ξ.2] (fun p : Point n => G ξ.1 p) :=
    hgerm.comp_tendsto hcont
  -- Push the sliced fiber germ along the coordinate-line map `s ↦ Function.update ξ.2 k s`.
  have hupdateTendsto : Filter.Tendsto (fun s : ℝ => Function.update ξ.2 k s)
      (nhds (ξ.2 k)) (nhds ξ.2) := by
    have hf : Filter.Tendsto (fun _ : ℝ => ξ.2) (nhds (ξ.2 k)) (nhds ξ.2) := tendsto_const_nhds
    have hg : Filter.Tendsto (id : ℝ → ℝ) (nhds (ξ.2 k)) (nhds (ξ.2 k)) := Filter.tendsto_id
    have h := hf.update k hg
    simpa [Function.update_eq_self] using h
  have hline : (fun s : ℝ => F ξ.1 (Function.update ξ.2 k s))
      =ᶠ[nhds (ξ.2 k)] (fun s : ℝ => G ξ.1 (Function.update ξ.2 k s)) :=
    hsliced.comp_tendsto hupdateTendsto
  -- Extract the single output component `jj`.
  have hcoord : (fun s : ℝ => F ξ.1 (Function.update ξ.2 k s) jj)
      =ᶠ[nhds (ξ.2 k)] (fun s : ℝ => G ξ.1 (Function.update ξ.2 k s) jj) := by
    have := hline.fun_comp (fun v : Point n => v jj)
    simpa [Function.comp] using this
  exact hcoord.hasDerivAt_iff

/-- **★ J4-1127 — `chartCoherent_hasDerivAt_transfer_at_overlap_two_seeds`: literal coordinate-line
    `HasDerivAt` transfer at the exact `hcarField`/`hcarField2` shape.** At the SAME uniform radius
    `r₀` from the hub lemma, for any TWO seeds `(z₀,v₀)`, `(z₀',v₀')`, there are coherently-built
    charts `chartCoherent1`, `chartCoherent2` and OPEN neighbourhoods `U1`, `U2` such that: (a) on
    `U1`, for every `k jj : Fin n` and every candidate derivative value `d : ℝ`, the coordinate-line
    `HasDerivAt` statement for `uniformInverseChart` transfers to/from the one for `chartCoherent1`;
    (b) the analogous transfer on `U2` for `chartCoherent2`; (c) on the overlap `U1 ∩ U2`, the
    coordinate-line `HasDerivAt` statement transfers directly between `chartCoherent1` and
    `chartCoherent2`. This is the literal shape `ChartJointBorel.lean`'s `hcarField`/`hcarField2`
    consume. -/
theorem chartCoherent_hasDerivAt_transfer_at_overlap_two_seeds (g gi : Point n → Fin n → Fin n → ℝ)
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
        (∀ ξ ∈ U1, ∀ k jj : Fin n, ∀ d : ℝ,
          HasDerivAt
            (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
            d (ξ.2 k)
          ↔ HasDerivAt (fun s : ℝ => chartCoherent1 ξ.1 (Function.update ξ.2 k s) jj) d
              (ξ.2 k)) ∧
        (∀ ξ ∈ U2, ∀ k jj : Fin n, ∀ d : ℝ,
          HasDerivAt
            (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
            d (ξ.2 k)
          ↔ HasDerivAt (fun s : ℝ => chartCoherent2 ξ.1 (Function.update ξ.2 k s) jj) d
              (ξ.2 k)) ∧
        (∀ ξ ∈ U1 ∩ U2, ∀ k jj : Fin n, ∀ d : ℝ,
          HasDerivAt (fun s : ℝ => chartCoherent1 ξ.1 (Function.update ξ.2 k s) jj) d (ξ.2 k)
          ↔ HasDerivAt (fun s : ℝ => chartCoherent2 ξ.1 (Function.update ξ.2 k s) jj) d
              (ξ.2 k)) := by
  classical
  obtain ⟨r₀, hr₀pos, hall⟩ := chartCoherent_germ_agree_at_overlap_two_seeds g gi hC hK
  refine ⟨r₀, hr₀pos, ?_⟩
  intro z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  obtain ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem,
    hEqOn1, hEqOn2, hgermAll⟩ := hall z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  refine ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem, ?_, ?_, ?_⟩
  · intro ξ hξ k jj d
    have hgerm : (fun η : Point n × Point n => uniformInverseChart g gi hC hK η.1 η.2)
        =ᶠ[nhds ξ] (fun η : Point n × Point n => chartCoherent1 η.1 η.2) := by
      filter_upwards [hU1open.mem_nhds hξ] with η hη using hEqOn1 hη
    exact hasDerivAt_coordLine_iff_of_germ hgerm k jj d
  · intro ξ hξ k jj d
    have hgerm : (fun η : Point n × Point n => uniformInverseChart g gi hC hK η.1 η.2)
        =ᶠ[nhds ξ] (fun η : Point n × Point n => chartCoherent2 η.1 η.2) := by
      filter_upwards [hU2open.mem_nhds hξ] with η hη using hEqOn2 hη
    exact hasDerivAt_coordLine_iff_of_germ hgerm k jj d
  · intro ξ hξ k jj d
    exact hasDerivAt_coordLine_iff_of_germ (hgermAll ξ hξ) k jj d

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms chartCoherent_hasDerivAt_transfer_at_overlap_two_seeds
end AxiomChecks
