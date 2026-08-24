/-
  ChartCoherentPFieldCompatibleFamily — J4-1132: dispatch 10 of the "inverse-branch
  overlap-uniqueness bridge" sub-campaign (greenlit J4-1122, hub lemma J4-1123, two-seed
  `Set.EqOn` corollary J4-1124, open-overlap germ compatibility J4-1125, target-facing
  value/`fderiv`/carrier consumer triple J4-1126, literal coordinate-line `HasDerivAt` transfer
  J4-1127, first-order coefficient-field agreement J4-1128, second-order (`Qfield`) agreement
  J4-1129, concrete single-seed `fderiv`-built representative J4-1130, abstract finite
  measurable-gluing lemma J4-1131, per `gpt-5.6-sol` high consult 2026-08-24 x10).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  J4-1131's own "Next dispatch" note lists SIX sub-steps for the geometric half of the gluing:
  (1) generalize J4-1130's single-seed `U`/`Pfield` construction to arbitrary seeds; (2) pairwise
  compatibility `Set.EqOn` on overlaps; (3) coverage of a genuinely COMPACT `K₀ ⊆ interior K`;
  (4) extract the finite subcover via compactness; (5) instantiate `exists_measurable_glue_finset_
  field`; (6) identify the glued result with J4-1130's local-correctness fact on `K₀`.

  Per Sol's tenth consult, steps (3)+(4) require a wholly NEW, not-yet-discharged geometric fact
  (coverage of a compact target by images of the flow-exp map — nothing in the tower establishes
  this yet) and were explicitly scoped OUT of this dispatch. Sol recommended bundling (1)+(2) into
  a self-contained "compatible family" theorem, stopping short of compactness/coverage.

  **A simplification found while implementing Sol's plan.** Sol's draft assumed step (2) would
  need to invoke J4-1128 (`chartCoherent_field_agree_at_overlap_two_seeds`), which bridges TWO
  DIFFERENT per-seed charts `chartCoherent1`/`chartCoherent2` via a germ-transfer argument. But
  re-reading J4-1130's literal conclusion shows its `Pfield` witnesses the coordinate-line
  derivative of `uniformInverseChart` ITSELF — the single, seed-INDEPENDENT global function — not
  of any per-seed `chartCoherent`. Consequently, for two different seeds' representatives `P1`
  (on `U1`) and `P2` (on `U2`), agreement on `U1 ∩ U2` follows DIRECTLY from `HasDerivAt.unique`
  applied to the SAME curve `uniformInverseChart`'s derivative at the SAME point — no need for
  J4-1128's germ-bridging machinery at all (that machinery does the harder work of relating two
  *different* representing functions `chartCoherent1 ≠ chartCoherent2`, which is not the situation
  here once both representatives are already stated for the same `uniformInverseChart`).

  ## The construction.

  `exists_chartCoherent_pfield_compatible_family`: at the SAME uniform radius `r₀` from J4-1130,
  produces TOTAL (junk-valued outside the admissible domain, exactly as `choose` naturally
  produces) functions `Pfield : Point n → Point n → Fin n → Point n → Point n → Fin n → ℝ` and
  `U : Point n → Point n → Fin n → Set (Point n × Point n)`, indexed by the seed `(z₀, v₀)` AND
  the differentiated coordinate `k` (Sol's flagged quantifier-order caution: `k` sits inside
  J4-1130's per-seed `∀`, before its `∃`, so it must be part of the family index, not left
  universally quantified outside), such that: (1) for every admissible seed/`k`, `U z₀ v₀ k` is
  open, measurable, contains the seed's image point, `Pfield z₀ v₀ k` is globally `Measurable`
  per output component (re-derived from J4-1130's `w.2.2 w.2.1`-order measurability fact via
  composition with the swap `ξ ↦ (0, ξ.2, ξ.1)`, into the more directly `exists_measurable_glue_
  finset_field`-consumable `ξ ↦ Pfield … ξ.1 ξ.2 jj` order), and witnesses `uniformInverseChart`'s
  `k`-coordinate-line derivative throughout `U z₀ v₀ k`; (2) for any two admissible seeds sharing
  the SAME `k`, `Pfield` for one agrees with `Pfield` for the other throughout the overlap of
  their `U`s — proved directly via `HasDerivAt.unique`, per the simplification above.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. No `sorry`, no new axioms, no vacuous/unsatisfiable
  hypotheses, no existing file edited. This file builds ONLY the compatible FAMILY (steps (1)+(2)
  of J4-1131's six-step plan) — it does NOT establish coverage of any compact `K₀ ⊆ interior K` by
  the family's open sets (step (3), a genuinely NEW geometric fact this tower has never
  established: nothing here shows the seed-indexed neighbourhoods, as the seed ranges over an
  admissible compact subset, actually COVER any particular target compact set — this needs real
  facts about the flow-exp map's image sweeping out a neighbourhood, not yet proved anywhere),
  does NOT extract a finite subcover (step (4), mechanical but dependent on (3)), does NOT
  instantiate `exists_measurable_glue_finset_field` (step (5)), and does NOT identify a glued
  result with J4-1130's local correctness on any `K₀` (step (6)). `a₁ = R/6` remains STRICTLY
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ChartCoherentDerivativeFieldRepresentative

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★★ J4-1132 — `exists_chartCoherent_pfield_compatible_family`: the seed-indexed,
    pairwise-compatible family of J4-1130 representatives (dispatch 10, steps (1)+(2) of J4-1131's
    six-step geometric-gluing plan).** At the SAME uniform radius `r₀` as J4-1130, there are total
    functions `Pfield`/`U`, indexed by seed `(z₀,v₀)` and differentiated coordinate `k`, such that
    for every admissible `(z₀,v₀,k)` (`z₀ ∈ interior K`, `‖v₀‖ < r₀`): `U z₀ v₀ k` is open,
    measurable, and contains the seed's image point; `Pfield z₀ v₀ k` is globally `Measurable` per
    output component (in the `ξ ↦ Pfield … ξ.1 ξ.2 jj` order `exists_measurable_glue_finset_field`
    consumes); and `Pfield z₀ v₀ k` witnesses `uniformInverseChart`'s `k`-coordinate-line derivative
    throughout `U z₀ v₀ k`. Moreover, for any two admissible seeds sharing the same `k`, their
    representatives agree throughout the overlap of their `U`s — direct from `HasDerivAt.unique`,
    since both witness the SAME global `uniformInverseChart`. Does NOT address coverage of any
    compact target set by these `U`s (a separate, not-yet-established geometric fact; see the
    file-level firewall). -/
theorem exists_chartCoherent_pfield_compatible_family
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ),
      ∃ (Pfield : Point n → Point n → Fin n → Point n → Point n → Fin n → ℝ)
        (U : Point n → Point n → Fin n → Set (Point n × Point n)),
        (∀ z₀ v₀ (k : Fin n), z₀ ∈ interior K → ‖v₀‖ < r₀ →
          IsOpen (U z₀ v₀ k) ∧
          MeasurableSet (U z₀ v₀ k) ∧
          ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ U z₀ v₀ k ∧
          (∀ jj : Fin n,
            Measurable (fun ξ : Point n × Point n => Pfield z₀ v₀ k ξ.1 ξ.2 jj)) ∧
          (∀ ξ ∈ U z₀ v₀ k, ∀ jj : Fin n,
            HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
              (Pfield z₀ v₀ k ξ.1 ξ.2 jj) (ξ.2 k))) ∧
        (∀ z₀ v₀ (k : Fin n) z₀' v₀',
          z₀ ∈ interior K → ‖v₀‖ < r₀ → z₀' ∈ interior K → ‖v₀'‖ < r₀ →
          ∀ ξ ∈ U z₀ v₀ k ∩ U z₀' v₀' k, ∀ jj : Fin n,
            Pfield z₀ v₀ k ξ.1 ξ.2 jj = Pfield z₀' v₀' k ξ.1 ξ.2 jj) := by
  classical
  obtain ⟨r₀, hr₀pos, hall⟩ := chartCoherent_pfield_representative_single_seed g gi hC hK
  refine ⟨r₀, hr₀pos, ?_⟩
  -- Package the per-seed existential into a total, `choose`-friendly form (junk outside the
  -- admissible domain, exactly as `choose` naturally produces).
  have hchoice : ∀ z₀ v₀ (k : Fin n),
      ∃ (Pfield0 : Point n → Point n → Fin n → ℝ) (U0 : Set (Point n × Point n)),
        (z₀ ∈ interior K → ‖v₀‖ < r₀ →
          IsOpen U0 ∧ MeasurableSet U0 ∧
          ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ U0 ∧
          (∀ jj : Fin n, Measurable (fun ξ : Point n × Point n => Pfield0 ξ.1 ξ.2 jj)) ∧
          (∀ ξ ∈ U0, ∀ jj : Fin n,
            HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
              (Pfield0 ξ.1 ξ.2 jj) (ξ.2 k))) := by
    intro z₀ v₀ k
    by_cases hz₀ : z₀ ∈ interior K
    · by_cases hv₀ : ‖v₀‖ < r₀
      · obtain ⟨Pfield0, hmeasW, U0, hU0open, hU0mem, hU0deriv⟩ := hall z₀ hz₀ v₀ hv₀ k
        refine ⟨Pfield0, U0, fun _ _ => ⟨hU0open, hU0open.measurableSet, hU0mem, ?_, hU0deriv⟩⟩
        intro jj
        have hswap : Measurable (fun ξ : Point n × Point n =>
            ((0, ξ.2, ξ.1) : ℝ × Point n × Point n)) :=
          Measurable.prodMk measurable_const (Measurable.prodMk measurable_snd measurable_fst)
        simpa using (hmeasW jj).comp hswap
      · exact ⟨fun _ _ _ => 0, ∅, fun _ hv₀' => absurd hv₀' hv₀⟩
    · exact ⟨fun _ _ _ => 0, ∅, fun hz₀' _ => absurd hz₀' hz₀⟩
  choose Pfield U hspec using hchoice
  refine ⟨Pfield, U, ?_, ?_⟩
  · intro z₀ v₀ k hz₀ hv₀
    exact hspec z₀ v₀ k hz₀ hv₀
  · intro z₀ v₀ k z₀' v₀' hz₀ hv₀ hz₀' hv₀' ξ hξ jj
    have h1 := (hspec z₀ v₀ k hz₀ hv₀).2.2.2.2 ξ hξ.1 jj
    have h2 := (hspec z₀' v₀' k hz₀' hv₀').2.2.2.2 ξ hξ.2 jj
    exact h1.unique h2

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms exists_chartCoherent_pfield_compatible_family
end AxiomChecks
