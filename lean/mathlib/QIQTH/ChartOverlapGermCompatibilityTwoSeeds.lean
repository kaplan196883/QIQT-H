/-
  ChartOverlapGermCompatibilityTwoSeeds — J4-1125: dispatch 3 of the "inverse-branch
  overlap-uniqueness bridge" sub-campaign (greenlit J4-1122, hub lemma J4-1123, two-seed
  `Set.EqOn` corollary J4-1124, per gpt-5.6-sol high consult 2026-08-24 x3).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  `ChartOverlapUniquenessTwoSeeds.lean`'s `chartCoherent_agree_at_overlap_two_seeds` gives, for
  two seeds `(z₀,v₀)`, `(z₀',v₀')`, OPEN neighbourhoods `U1`, `U2` of the two image points and
  coherently-built charts `chartCoherent1`, `chartCoherent2` such that on the overlap `U1 ∩ U2`
  the two coherent charts agree pointwise (`Set.EqOn ... (U1 ∩ U2)`).

  Per Sol's J4-1124 scoped plan, J4-1125 upgrades this pointwise `Set.EqOn` overlap fact to a
  full FILTER-germ equality: for every `ξ ∈ U1 ∩ U2`, `chartCoherent1 =ᶠ[nhds ξ] chartCoherent2`
  (as curried functions of the pair `η.1 η.2`). Sol confirmed (2026-08-24, third consult) this is
  genuinely mechanical: since `U1 ∩ U2` is open (`IsOpen.inter`) and contains `ξ`, `U1 ∩ U2 ∈ 𝓝 ξ`
  via `IsOpen.mem_nhds`; the germ equality is then exactly `Filter.eventually_of_mem` (via
  `filter_upwards`) applied to the `Set.EqOn` fact restricted to that neighbourhood. Sol also
  confirmed the useful downstream shape is precisely `∀ ξ ∈ U1 ∩ U2, F =ᶠ[𝓝 ξ] G` (pointwise-germ,
  NOT some stronger "simultaneous" packaging — `𝓝 ξ` necessarily depends on `ξ`, so the `Set.EqOn`
  fact together with openness already is the uniform whole-overlap information; the germ form is
  its per-point unpacking, which is what Mathlib's `Filter.EventuallyEq.fderiv_eq` /
  `Filter.EventuallyEq.self_of_nhds` congruence API consumes for the future derivative-transport
  step (targeting `hInDeriv` in J4-1126)).

  ## The deliverable.

  `chartCoherent_germ_agree_at_overlap_two_seeds` — same setup as J4-1124's corollary, with the
  overlap conclusion strengthened from `Set.EqOn` to: for every `ξ ∈ U1 ∩ U2`, the curried
  functions `fun η => chartCoherent1 η.1 η.2` and `fun η => chartCoherent2 η.1 η.2` agree as
  GERMS at `ξ` (`=ᶠ[nhds ξ]`). Pure filter-logic upgrade of J4-1124's `Set.EqOn` fact — no new
  IFT/ODE analysis, no new quantitative or analytic estimate (confirmed with `gpt-5.6-sol`, high,
  2026-08-24: no sympy check triggered).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. Pure logical/filter upgrade built on the already-banked
  `ChartOverlapUniquenessTwoSeeds.lean` corollary — no new analytic estimate, no `sorry`, no new
  axioms, no vacuous/unsatisfiable hypotheses (the overlap `U1 ∩ U2` is not asserted nonempty; the
  conclusion is the correct CONDITIONAL "for every `ξ` in the overlap, germ agreement" shape), no
  existing file edited. `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.
-/
import QIQTH.ChartOverlapUniquenessTwoSeeds

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★ J4-1125 — `chartCoherent_germ_agree_at_overlap_two_seeds`: open-overlap germ
    compatibility.** At the SAME uniform radius `r₀` from the hub lemma, for any TWO seeds
    `(z₀,v₀)` and `(z₀',v₀')` (both `z₀, z₀' ∈ interior K`, both velocities `< r₀`), there are
    coherently-built charts `chartCoherent1`, `chartCoherent2` and OPEN neighbourhoods
    `U1 ∋ (z₀, exp z₀ v₀)`, `U2 ∋ (z₀', exp z₀' v₀')` on which `uniformInverseChart` agrees with
    `chartCoherent1`, resp. `chartCoherent2` (`Set.EqOn`), such that for EVERY `ξ ∈ U1 ∩ U2` the
    two coherent charts agree as GERMS at `ξ` (`=ᶠ[nhds ξ]`) — the upgrade of J4-1124's pointwise
    `Set.EqOn` overlap fact that the future derivative-transport step needs. -/
theorem chartCoherent_germ_agree_at_overlap_two_seeds (g gi : Point n → Fin n → Fin n → ℝ)
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
          (fun η : Point n × Point n => chartCoherent1 η.1 η.2)
            =ᶠ[nhds ξ] (fun η : Point n × Point n => chartCoherent2 η.1 η.2) := by
  classical
  obtain ⟨r₀, hr₀pos, hall⟩ := chartCoherent_agree_at_overlap_two_seeds g gi hC hK
  refine ⟨r₀, hr₀pos, ?_⟩
  intro z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  obtain ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem,
    hEqOn1, hEqOn2, hOverlapEqOn⟩ := hall z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  refine ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem,
    hEqOn1, hEqOn2, ?_⟩
  intro ξ hξ
  have hmem : U1 ∩ U2 ∈ nhds ξ := (hU1open.inter hU2open).mem_nhds hξ
  filter_upwards [hmem] with η hη using hOverlapEqOn hη

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms chartCoherent_germ_agree_at_overlap_two_seeds
end AxiomChecks
