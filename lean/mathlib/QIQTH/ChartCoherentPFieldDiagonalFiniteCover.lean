/-
  ChartCoherentPFieldDiagonalFiniteCover — J4-1133: dispatch 11 of the "inverse-branch
  overlap-uniqueness bridge" sub-campaign (greenlit J4-1122, hub lemma J4-1123, two-seed
  `Set.EqOn` corollary J4-1124, open-overlap germ compatibility J4-1125, target-facing
  value/`fderiv`/carrier consumer triple J4-1126, literal coordinate-line `HasDerivAt` transfer
  J4-1127, first-order coefficient-field agreement J4-1128, second-order (`Qfield`) agreement
  J4-1129, concrete single-seed `fderiv`-built representative J4-1130, abstract finite
  measurable-gluing lemma J4-1131, seed-indexed pairwise-compatible `Pfield` family J4-1132,
  per `gpt-5.6-sol` high consult 2026-08-24 x11).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  J4-1132's own "Next dispatch" note flagged step (3) of J4-1131's six-step geometric-gluing plan
  — coverage of a compact `K₀ ⊆ interior K` by the family's open sets `U z₀ v₀ k` — as the genuinely
  new, not-yet-established geometric obligation gating steps (4)-(6). This dispatch's eleventh Sol
  consult (BEFORE any Lean) delivered two decisive findings:

  (a) **Finite-subcover extraction needs NO uniform radius on the abstract `U z₀ v₀ k = U0 ∩ V0`.**
      Heine–Borel only needs an open COVER (union ⊇ target); the individual radii — genuinely
      unquantified in J4-1130/J4-1132's `mem_nhds_iff`-derived construction — are irrelevant to
      extracting a finite subcover.

  (b) **`hcarField`'s literal quantifier, read exactly as stated in `ChartJointBorel.lean`, forces
      `S q = Set.univ` for every `q ∈ K`** (instantiate `w := (1, p, q)` for an ARBITRARY `p` — the
      clause's `w.2.1 ∈ S w.2.2` then holds for that arbitrary `p`, for every `p`). So the eventual
      "identify with `hcarField`" step (6) of the six-step plan is NOT achievable by this local
      seed-gluing construction as `hcarField` is literally typed (a local chart cannot witness
      derivatives at literally EVERY point `p`, however far from `q`) — a structural finding about
      the TARGET, independent of anything built in this sub-campaign so far, and orthogonal to
      whether steps (3)/(4) themselves are buildable.

  Per Sol's explicit recommendation, THIS dispatch builds the honestly-scoped, genuinely achievable
  piece: **diagonal finite-subcover coverage** — the compact diagonal `Δ K₀ := {(q,q) : q ∈ K₀}` is
  covered "for free" by openness alone (`(q,q) = (q, uniformFlowExp q 0) ∈ U q 0 k` via
  `uniformFlowExp_zero`, no sharp-reach machinery needed), and — since `Δ K₀` is itself compact (a
  continuous image of the compact `K₀`) — Mathlib's `IsCompact.elim_finite_subcover_image` extracts
  a genuine FINITE subfamily of seed points `t ⊆ K₀` whose `U`-sets already cover all of `Δ K₀`.
  This is steps (3)+(4) of the six-step plan, honestly restricted to the diagonal target that the
  seed-family's zero-velocity slice actually reaches "for free."

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. No `sorry`, no new axioms, no vacuous/unsatisfiable
  hypotheses, no existing file edited (NEW FILE). This file covers ONLY the DIAGONAL `Δ K₀`, NOT any
  genuine 2D neighbourhood/tube of `K₀ × Point n` (per Sol's finding (b) above, the literal
  `hcarField` target needs `S q = univ`, which no local construction — diagonal or tube — can ever
  supply; the honest target for this sub-campaign was never "literal `hcarField`" but the local
  correctness the earlier dispatches established). Does NOT instantiate
  `exists_measurable_glue_finset_field` (step (5)) or identify a glued result with J4-1130's local
  correctness (step (6)) — both deferred to the next dispatch, which should also independently
  record Sol's structural finding (b) as a standalone quantifier-audit fact. `a₁ = R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ChartCoherentPFieldCompatibleFamily

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★★ J4-1133 — `chartCoherent_pfield_diagonal_finite_cover`: finite-subcover coverage of the
    compact diagonal `Δ K₀` by J4-1132's seed-indexed family (dispatch 11, steps (3)+(4) of
    J4-1131's six-step plan, restricted to the diagonal per Sol's eleventh consult).** For every
    compact `K ⊇` compact `K₀ ⊆ interior K` and every coordinate `k`, at the SAME uniform radius
    `r₀` as J4-1132's compatible family (`Pfield`/`U`, with all the family's open/measurable/carrier/
    pairwise-agreement properties), there is a FINITE set of seed points `t ⊆ K₀` such that the
    zero-velocity slice `{U z₀ 0 k : z₀ ∈ t}` already covers the whole diagonal
    `Δ K₀ := {(q,q) : q ∈ K₀}`. Proof: `(q, q) = (q, uniformFlowExp q 0) ∈ U q 0 k` for every `q ∈
    K₀` (openness membership from J4-1132's family spec + `uniformFlowExp_zero`), so `{U z₀ 0 k}_
    {z₀∈K₀}` is an open cover of the compact `Δ K₀`; `IsCompact.elim_finite_subcover_image` extracts
    the finite subfamily. No uniform radius on the abstract `U z₀ v₀ k` is needed — Heine–Borel only
    consumes the cover, not any quantitative size of its members. -/
theorem chartCoherent_pfield_diagonal_finite_cover
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {K₀ : Set (Point n)} (hK₀ : IsCompact K₀) (hK₀sub : K₀ ⊆ interior K) (k : Fin n) :
    ∃ r₀ > (0 : ℝ),
      ∃ (Pfield : Point n → Point n → Fin n → Point n → Point n → Fin n → ℝ)
        (U : Point n → Point n → Fin n → Set (Point n × Point n)),
        (∀ z₀ v₀ (k' : Fin n), z₀ ∈ interior K → ‖v₀‖ < r₀ →
          IsOpen (U z₀ v₀ k') ∧
          MeasurableSet (U z₀ v₀ k') ∧
          ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ U z₀ v₀ k' ∧
          (∀ jj : Fin n,
            Measurable (fun ξ : Point n × Point n => Pfield z₀ v₀ k' ξ.1 ξ.2 jj)) ∧
          (∀ ξ ∈ U z₀ v₀ k', ∀ jj : Fin n,
            HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k' s) jj)
              (Pfield z₀ v₀ k' ξ.1 ξ.2 jj) (ξ.2 k'))) ∧
        (∀ z₀ v₀ (k' : Fin n) z₀' v₀',
          z₀ ∈ interior K → ‖v₀‖ < r₀ → z₀' ∈ interior K → ‖v₀'‖ < r₀ →
          ∀ ξ ∈ U z₀ v₀ k' ∩ U z₀' v₀' k', ∀ jj : Fin n,
            Pfield z₀ v₀ k' ξ.1 ξ.2 jj = Pfield z₀' v₀' k' ξ.1 ξ.2 jj) ∧
        ∃ t : Finset (Point n), (↑t ⊆ K₀) ∧
          (fun q => ((q, q) : Point n × Point n)) '' K₀ ⊆ ⋃ z₀ ∈ t, U z₀ 0 k := by
  obtain ⟨r₀, hr₀pos, Pfield, U, hall, hagree⟩ :=
    exists_chartCoherent_pfield_compatible_family g gi hC hK
  refine ⟨r₀, hr₀pos, Pfield, U, hall, hagree, ?_⟩
  -- The zero-velocity slice `U · 0 k` covers the compact diagonal `Δ K₀`.
  set s : Set (Point n × Point n) := (fun q => ((q, q) : Point n × Point n)) '' K₀ with hsdef
  have hscompact : IsCompact s := hK₀.image (by fun_prop)
  have hc₁ : ∀ i ∈ K₀, IsOpen (U i 0 k) := by
    intro i hi
    have hiint : i ∈ interior K := hK₀sub hi
    have h0lt : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀pos
    exact (hall i 0 k hiint h0lt).1
  have hc₂ : s ⊆ ⋃ i ∈ K₀, U i 0 k := by
    rintro x ⟨q, hq, rfl⟩
    have hiint : q ∈ interior K := hK₀sub hq
    have h0lt : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀pos
    have hmem := (hall q 0 k hiint h0lt).2.2.1
    have hqK : q ∈ K := interior_subset hiint
    have hz0 : uniformFlowExp g gi hC hK q 0 = q := uniformFlowExp_zero g gi hC hK q hqK
    rw [hz0] at hmem
    exact Set.mem_biUnion hq hmem
  obtain ⟨b', hb'sub, hb'fin, hb'cov⟩ :=
    IsCompact.elim_finite_subcover_image hscompact hc₁ hc₂
  refine ⟨hb'fin.toFinset, ?_, ?_⟩
  · rw [hb'fin.coe_toFinset]; exact hb'sub
  · rw [show (⋃ z₀ ∈ hb'fin.toFinset, U z₀ 0 k) = ⋃ z₀ ∈ b', U z₀ 0 k by
      simp [hb'fin.coe_toFinset]]
    exact hb'cov

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms chartCoherent_pfield_diagonal_finite_cover
end AxiomChecks
