/-
  ChartOverlapUniquenessGeneralCenter — J4-1123: dispatch 1 of the "inverse-branch overlap-uniqueness
  bridge" sub-campaign (greenlit J4-1122, per gpt-5.6-sol high consult 2026-08-24).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  `GeneralCenterCoherentInverseChart.lean`'s `uniformInverseChart_jointContDiffAt_generalCenter`
  proves, INTERNALLY, an eventual-equality step
      `uniformInverseChart g gi hC hK =ᶠ[nhds (z₀, exp_{z₀} v₀)] chartCoherent`
  (where `chartCoherent` is the coherent joint inverse chart built ONCE, via Mathlib's
  `ContDiffAt.localInverse` of the augmented map `G(q,v) = (q, uniformFlowExp q v)`, at the seed
  `(z₀, v₀)`), then immediately consumes it via `hcd.congr_of_eventuallyEq hEq` to conclude
  `ContDiffAt ℝ 2 uniformInverseChart (z₀, exp z₀ v₀)` — discarding the intermediate equality as a
  private proof step.

  Per the J4-1122 scoping (Finding 2) and a fresh `gpt-5.6-sol` (high) consult 2026-08-24, this
  intermediate equality IS exactly the right SMALLEST reusable "overlap-uniqueness" brick: it shows
  the OPAQUE `Classical.choose`-selected `uniformInverseChart` literally COINCIDES, on an entire open
  neighbourhood of `(z₀, exp_{z₀} v₀)` in `Point n × Point n` (not just AT that one point), with a
  SINGLE coherently-built chart `chartCoherent` that carries NO per-point re-selection. This file
  extracts that step as standalone public API (`uniformInverseChart_agree_chartCoherent`), reusing
  `generalCenter_coherent_joint_chart`'s existing construction and proof pattern verbatim (no new
  IFT/ODE analysis — pure packaging of already-proven content, per Sol's dispatch-1 sizing).

  Sol's key correction (2026-08-24 consult): a naive "two DIFFERENT base points q₁≠q₂ agreeing at a
  COMMON chart-argument p" corollary is FALSE in general (already false in the flat model
  `chart(q,p) = p - q`, which genuinely depends on `q`). The valid next-step corollary (deferred to a
  later dispatch) is instead: two coherent charts seeded at DIFFERENT centers `(z₀,v₀)` and
  `(z₀',v₀')`, each evaluated at the SAME input `ξ = (q,p)` in the intersection of their two
  neighbourhoods, agree (`uniformInverseChart` being the shared "hub" they both agree with). This
  file supplies the "hub" comparison only; the two-seed-agreement corollary is NOT attempted here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. Pure re-exposure/packaging of already-banked IFT/ODE content
  (`GeneralCenterCoherentInverseChart.lean`) as reusable API — no new analytic estimate, no `sorry`,
  no new axioms, no vacuous/unsatisfiable hypotheses, no existing file edited.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.GeneralCenterCoherentInverseChart

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★ J4-1123 — `uniformInverseChart_agree_chartCoherent`: the overlap-uniqueness "hub" lemma.**
    At the general centre `(z₀, exp_{z₀} v₀)` (`z₀ ∈ interior K`, `‖v₀‖` below the derived
    invertibility threshold), there is a coherently-built chart `chartCoherent` — built ONCE via
    `generalCenter_coherent_joint_chart`, with NO per-point re-selection — that AGREES with the
    opaque `Classical.choose`-selected `uniformInverseChart` on an ENTIRE open neighbourhood `U` of
    the centre in `Point n × Point n` (`=ᶠ[nhds …]`, not merely a pointwise coincidence). This is the
    exact intermediate step `GeneralCenterCoherentInverseChart.lean`'s
    `uniformInverseChart_jointContDiffAt_generalCenter` proves and discards internally; here it is
    exposed as standalone, reusable overlap-uniqueness API. -/
theorem uniformInverseChart_agree_chartCoherent (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K)
    (v₀ : Point n) (hv₀ρ : ‖v₀‖ < uniformFlowRadius g gi hC hK)
    (hInv : ‖fderiv ℝ (uniformFlowExp g gi hC hK z₀) v₀
              - ContinuousLinearMap.id ℝ (Point n)‖ < 1)
    (δ₀ : ℝ) (hδ₀pos : 0 < δ₀) (hv₀δ₀ : ‖v₀‖ < δ₀)
    (hchart : ∀ q ∈ K, (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z))
            =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v)) ∧
      (∀ c : ℝ, 0 < c → c < δ₀ →
        IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
        closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
          ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c)) :
    ∃ chartCoherent : Point n → Point n → Point n,
      ContDiffAt ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∧
      chartCoherent z₀ (uniformFlowExp g gi hC hK z₀ v₀) = v₀ ∧
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2)
        =ᶠ[nhds ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n)]
        (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2) := by
  classical
  obtain ⟨chartCoherent, hcd, hval, hinv⟩ :=
    generalCenter_coherent_joint_chart g gi hC hK z₀ hz₀ v₀ hv₀ρ hInv
  refine ⟨chartCoherent, hcd, hval, ?_⟩
  -- base point stays in `interior K` (hence in `K`).
  have hball : ∀ᶠ ξ in nhds ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n),
      ξ.1 ∈ interior K := by
    have hopen : IsOpen {ξ : Point n × Point n | ξ.1 ∈ interior K} :=
      isOpen_interior.preimage continuous_fst
    exact hopen.mem_nhds hz₀
  -- the chart value stays within the germ radius `δ₀` (joint continuity + value `v₀`, `‖v₀‖<δ₀`).
  have hsmall : ∀ᶠ ξ in nhds ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n),
      chartCoherent ξ.1 ξ.2 ∈ Metric.ball (0 : Point n) δ₀ := by
    have hcont : ContinuousAt (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) := hcd.continuousAt
    refine hcont.eventually_mem ?_
    show Metric.ball (0 : Point n) δ₀ ∈ nhds (chartCoherent z₀ (uniformFlowExp g gi hC hK z₀ v₀))
    rw [hval]
    exact Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hv₀δ₀)
  filter_upwards [hinv, hball, hsmall] with ξ hξinv hξball hξsmall
  have hξ1K : ξ.1 ∈ K := interior_subset hξball
  set v : Point n := chartCoherent ξ.1 ξ.2 with hvdef
  have hvδ₀ : ‖v‖ < δ₀ := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hξsmall
  obtain ⟨hgerm, _hWc2⟩ := (hchart ξ.1 hξ1K).1 v hvδ₀
  have hleft : uniformInverseChart g gi hC hK ξ.1 (uniformFlowExp g gi hC hK ξ.1 v) = v :=
    hgerm.eq_of_nhds
  have hforward : uniformFlowExp g gi hC hK ξ.1 v = ξ.2 := hξinv
  rw [hforward] at hleft
  show uniformInverseChart g gi hC hK ξ.1 ξ.2 = chartCoherent ξ.1 ξ.2
  rw [← hvdef]; exact hleft

/-- **★ J4-1123 — `uniformInverseChart_agree_chartCoherent_uniform`: the same hub lemma, packaged at
    the SINGLE uniform radius `r₀` (bundling the flow radius, the germ radius `δ₀`, and the Neumann
    threshold), exactly mirroring `uniformInverseChart_jointContDiffAt_generalCenter`'s hypothesis
    surface but exposing the `=ᶠ[nhds …]` overlap-uniqueness content instead of only the composed
    `ContDiffAt` conclusion. This is the form future overlap-uniqueness corollaries (comparing TWO
    independently-seeded coherent charts at a shared evaluation point) should build on. -/
theorem uniformInverseChart_agree_chartCoherent_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∀ z₀ : Point n, z₀ ∈ interior K → ∀ v₀ : Point n, ‖v₀‖ < r₀ →
      ∃ chartCoherent : Point n → Point n → Point n,
        ContDiffAt ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
          ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∧
        chartCoherent z₀ (uniformFlowExp g gi hC hK z₀ v₀) = v₀ ∧
        (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2)
          =ᶠ[nhds ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n)]
          (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2) := by
  classical
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hnid⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  obtain ⟨δ₀, hδ₀pos, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  have hρpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  have hCD1pos : (0 : ℝ) < C_D + 1 := by linarith
  set r₀ : ℝ := min (min (uniformFlowRadius g gi hC hK) δ₀) (min ρ₀ (1 / (C_D + 1))) with hr₀def
  have hr₀pos : 0 < r₀ := by
    rw [hr₀def]
    refine lt_min (lt_min hρpos hδ₀pos) (lt_min hρ₀pos ?_)
    positivity
  refine ⟨r₀, hr₀pos, ?_⟩
  intro z₀ hz₀ v₀ hv₀
  have hz₀K : z₀ ∈ K := interior_subset hz₀
  have hv₀ρ : ‖v₀‖ < uniformFlowRadius g gi hC hK := by
    have hle : r₀ ≤ uniformFlowRadius g gi hC hK := by
      rw [hr₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hv₀δ₀ : ‖v₀‖ < δ₀ := by
    have hle : r₀ ≤ δ₀ := by
      rw [hr₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hv₀ρ₀ : ‖v₀‖ < ρ₀ := by
    have hle : r₀ ≤ ρ₀ := by
      rw [hr₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hv₀inv : ‖v₀‖ < 1 / (C_D + 1) := by
    have hle : r₀ ≤ 1 / (C_D + 1) := by
      rw [hr₀def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hInv : ‖fderiv ℝ (uniformFlowExp g gi hC hK z₀) v₀
                - ContinuousLinearMap.id ℝ (Point n)‖ < 1 := by
    have hb := hnid z₀ hz₀K v₀ hv₀ρ₀
    have hCDv : C_D * ‖v₀‖ < 1 := by
      have h1 : C_D * ‖v₀‖ ≤ C_D * (1 / (C_D + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hv₀inv) hCD0
      have h2 : C_D * (1 / (C_D + 1)) < 1 := by
        rw [mul_one_div, div_lt_one hCD1pos]; linarith
      linarith
    linarith [hb]
  exact uniformInverseChart_agree_chartCoherent g gi hC hK z₀ hz₀ v₀ hv₀ρ hInv δ₀ hδ₀pos hv₀δ₀ hchart

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms uniformInverseChart_agree_chartCoherent
#print axioms uniformInverseChart_agree_chartCoherent_uniform
end AxiomChecks
