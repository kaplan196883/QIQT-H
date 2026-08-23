/-
  ChartOverlapUniquenessTwoSeeds — J4-1124: dispatch 2 of the "inverse-branch overlap-uniqueness
  bridge" sub-campaign (greenlit J4-1122, hub lemma built J4-1123, per gpt-5.6-sol high consult
  2026-08-24 x2).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  `ChartOverlapUniquenessGeneralCenter.lean`'s `uniformInverseChart_agree_chartCoherent_uniform`
  gives, at a SINGLE uniform radius `r₀`, for EVERY seed `(z₀,v₀)` with `z₀ ∈ interior K` and
  `‖v₀‖ < r₀`, a coherently-built chart `chartCoherent` that agrees with the shared opaque
  `Classical.choose`-selected `uniformInverseChart` on an entire neighbourhood of the image point
  `(z₀, exp_{z₀} v₀)` (an `=ᶠ[nhds …]` germ fact).

  Per Sol's 2026-08-24 correction of the naive ("two different base points agree at a shared
  chart-argument") false shape, the VALID next step is: apply the hub lemma at TWO independently
  chosen seeds `(z₀,v₀)` and `(z₀',v₀')`, extract EXPLICIT open witnessing neighbourhoods `U1`, `U2`
  of the two germ facts (via `Filter.eventuallyEq_iff_exists_mem` + `mem_nhds_iff` for openness),
  and observe that on the overlap `U1 ∩ U2` BOTH coherent charts equal the SAME hub
  `uniformInverseChart`, hence equal EACH OTHER there — transitivity through the hub, not a direct
  (false) comparison of the two charts.

  Per a follow-up Sol consult (dispatch-2 sizing), the witnessing neighbourhoods are strengthened to
  be OPEN (not just "in the filter"), and the local agreement is phrased via `Set.EqOn`, which is
  what the future derivative-transport step (targeting `hInDeriv`) will need: on `U1 ∩ U2` (open,
  as an intersection of two opens), the two coherent charts agree on a WHOLE neighbourhood of any
  overlap point `ξ`, not merely pointwise at `ξ`.

  ## The deliverable.

  `chartCoherent_agree_at_overlap_two_seeds` — for two seeds within the uniform radius `r₀`, there
  are open sets `U1 ∋ (z₀, exp z₀ v₀)` and `U2 ∋ (z₀', exp z₀' v₀')` on which `uniformInverseChart`
  agrees (`Set.EqOn`) with `chartCoherent1`, resp. `chartCoherent2`, and on the (possibly empty, but
  when nonempty genuinely informative) overlap `U1 ∩ U2` the two coherent charts agree with EACH
  OTHER. This is pure transitivity/set-logic packaging of J4-1123's hub lemma applied twice — no new
  IFT/ODE analysis, no new quantitative or analytic estimate (confirmed with `gpt-5.6-sol`, high,
  2026-08-24: no sympy check triggered, this is pure filter/set logic).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. Pure logical transitivity/packaging built on the already-banked
  `ChartOverlapUniquenessGeneralCenter.lean` hub lemma — no new analytic estimate, no `sorry`, no new
  axioms, no vacuous/unsatisfiable hypotheses (the overlap `U1 ∩ U2` is not asserted nonempty; the
  conclusion is the correct CONDITIONAL "if `ξ` is in the overlap, then agreement" shape), no existing
  file edited. `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ChartOverlapUniquenessGeneralCenter

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★ J4-1124 — `chartCoherent_agree_at_overlap_two_seeds`: the two-seed overlap-uniqueness
    corollary.** At the SAME uniform radius `r₀` from the hub lemma, for any TWO seeds `(z₀,v₀)`
    and `(z₀',v₀')` (both `z₀, z₀' ∈ interior K`, both velocities `< r₀`), there are coherently-built
    charts `chartCoherent1`, `chartCoherent2` and OPEN neighbourhoods `U1 ∋ (z₀, exp z₀ v₀)`,
    `U2 ∋ (z₀', exp z₀' v₀')` on which `uniformInverseChart` agrees with `chartCoherent1`, resp.
    `chartCoherent2` (`Set.EqOn`), such that on the overlap `U1 ∩ U2` the two coherent charts agree
    with EACH OTHER — via transitivity through the shared hub `uniformInverseChart`, exactly Sol's
    corrected (non-false) overlap-uniqueness shape. -/
theorem chartCoherent_agree_at_overlap_two_seeds (g gi : Point n → Fin n → Fin n → ℝ)
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
        Set.EqOn (fun ξ : Point n × Point n => chartCoherent1 ξ.1 ξ.2)
          (fun ξ : Point n × Point n => chartCoherent2 ξ.1 ξ.2) (U1 ∩ U2) := by
  classical
  obtain ⟨r₀, hr₀pos, hall⟩ := uniformInverseChart_agree_chartCoherent_uniform g gi hC hK
  refine ⟨r₀, hr₀pos, ?_⟩
  intro z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  obtain ⟨chartCoherent1, _hcd1, _hval1, hEq1⟩ := hall z₀ hz₀ v₀ hv₀
  obtain ⟨chartCoherent2, _hcd2, _hval2, hEq2⟩ := hall z₀' hz₀' v₀' hv₀'
  -- extract explicit witnessing MEMBER sets from the two germ facts.
  obtain ⟨s1, hs1mem, hs1eq⟩ := Filter.eventuallyEq_iff_exists_mem.mp hEq1
  obtain ⟨s2, hs2mem, hs2eq⟩ := Filter.eventuallyEq_iff_exists_mem.mp hEq2
  -- upgrade to OPEN witnessing sets (needed for the derivative-facing next dispatch).
  obtain ⟨U1, hU1sub, hU1open, hU1mem⟩ := mem_nhds_iff.mp hs1mem
  obtain ⟨U2, hU2sub, hU2open, hU2mem⟩ := mem_nhds_iff.mp hs2mem
  refine ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem, ?_, ?_, ?_⟩
  · intro ξ hξ; exact hs1eq (hU1sub hξ)
  · intro ξ hξ; exact hs2eq (hU2sub hξ)
  · intro ξ hξ
    obtain ⟨hξ1, hξ2⟩ := hξ
    have e1 : uniformInverseChart g gi hC hK ξ.1 ξ.2 = chartCoherent1 ξ.1 ξ.2 :=
      hs1eq (hU1sub hξ1)
    have e2 : uniformInverseChart g gi hC hK ξ.1 ξ.2 = chartCoherent2 ξ.1 ξ.2 :=
      hs2eq (hU2sub hξ2)
    exact e1.symm.trans e2

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms chartCoherent_agree_at_overlap_two_seeds
end AxiomChecks
