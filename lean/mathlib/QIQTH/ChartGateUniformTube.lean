/-
  ChartGateUniformTube — J4-1140: dispatch 18 of the "inverse-branch overlap-uniqueness bridge"
  sub-campaign, the "uniform tube kill/compress test" per J4-1139's decisive audit (`gpt-5.6-sol`,
  high, seventeenth consult 2026-08-24).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does (and does NOT do).

  J4-1139 found `OffSVanishing.lean` (J4-235, `8bb219e7`, 2026-08-05) already discharges the exact
  literal `hOffS`/`hOffS2` conjunct shapes of `GatedRepSFix.tripleHEmeas_concrete_v4` — but ONLY for
  the concrete flow-ball gate `S_c q := uniformFlowExp … q '' Metric.ball 0 c`, whereas the CURRENT
  sub-campaign's gate is the shrunk intersection `S_∩ q := ⋂ k, fiberGate (G k) q`
  (`ChartGateConcreteInstantiation.lean`, J4-1136). Sol's recommended kill/compress test: attempt a
  "uniform tube" lemma `∀ q ∈ K₀, ∃ c₀ > 0, S_c₀ q ⊆ S_∩ q` — if it goes through with tools already
  in hand, `hOffS_concrete`/`hOffS2_concrete` transport for free via gate-monotonicity; if not,
  re-scope.

  ## The construction (POSITIVE result — the tube containment IS true and IS provable here).

  Two ingredients, both ALREADY BANKED (no new geometric axiom, no `sorry`):
  * `G k` is OPEN and contains the WHOLE diagonal `Δ K₀ := {(q,q) : q ∈ K₀}` (from
    `chartGate_concrete_S_construction`'s own `hall`/`htcov`/`hGeq` clauses — re-derived here exactly
    as in that file's own openness proof). Since `Δ K₀` is compact (continuous image of compact
    `K₀`) and `G k` is open ⊇ `Δ K₀`, Mathlib's `IsCompact.exists_thickening_subset_open` gives a
    per-`k` thickening radius `δ k > 0` with `Metric.thickening (δ k) (Δ K₀) ⊆ G k`. Taking the
    FINITE min `τ := Finset.univ.inf' _ δ` over `k : Fin n` (finite index, `hn : 0 < n` gives
    nonemptiness) gives ONE shared `τ > 0` with `Metric.thickening τ (Δ K₀) ⊆ G k` for EVERY `k`
    simultaneously.
  * `uniformFlowExp_displacement_bound` (`NearIsometryBudget.lean`, J4-96, D2) already gives a
    UNIFORM (in `q ∈ K`) quadratic near-identity bound `‖φ_q v − q − v‖ ≤ C_D·‖v‖·‖v‖` for
    `‖v‖ < ρ₀`; combined with the triangle inequality this gives `‖φ_q v − q‖ ≤ ‖v‖·(1+C_D·‖v‖)`,
    UNIFORMLY in `q`, and → 0 as `‖v‖ → 0`. Choosing `c₀ := min ρ₀ (min 1 (τ/(2+2·C_D)))` forces
    `‖v‖ < c₀ ⟹ ‖φ_q v − q‖ < τ` for every `q ∈ K` — i.e. `(q, φ_q v)` lies within `τ` of the
    diagonal point `(q,q) ∈ Δ K₀` (via `Prod.dist_eq` + `dist_self`), hence inside
    `Metric.thickening τ (Δ K₀) ⊆ G k` for EVERY `k`, hence `φ_q v ∈ fiberGate (G k) q` for every
    `k`, hence `φ_q v ∈ S_∩ q` (via `hSeq`).

  `chartGate_concrete_S_uniform_tube` bundles the FULL `chartGate_concrete_S_construction` output
  PLUS this extra `∃ c₀ > 0, ∀ q ∈ K₀, uniformFlowExp … q '' Metric.ball 0 c₀ ⊆ S q` conjunct —
  the literal "uniform tube" containment Sol's kill test targeted.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. No `sorry`, no new axioms, no vacuous/unsatisfiable
  hypotheses, no existing file edited (NEW FILE). This dispatch builds ONLY the uniform-tube
  containment `S_c₀ q ⊆ S_∩ q` (for `q ∈ K₀`) — it does NOT yet: transport `hOffS_concrete`/
  `hOffS2_concrete` from `OffSVanishing.lean` through this containment via gate-monotonicity (the
  ELEMENTARY next step: `p ∉ S_∩ q ⟹ p ∉ S_c₀ q` by contraposing this file's `⊆`, then apply
  `witness_eventuallyEq_zero_offGate` unconditionally, since that lemma's collar proof never
  actually inspects `S`'s SHAPE beyond the `hSeq : S = fun z => φ_z '' ball 0 c` equation supplied
  as a HYPOTHESIS — so it is NOT immediately reusable verbatim for `S_∩`; a small adapter lemma
  is still needed, DEFERRED to the next dispatch); assemble `hcarField`/`hcarField2`'s on-gate
  branch; discharge `PdiffAt (chartFieldAmp …)`; or produce any actual `tripleHEmeas_concrete_v4`/
  `a1_R6_assembled_v7` invocation. `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ChartGateConcreteInstantiation
import QIQTH.NearIsometryBudget

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★★★ `chartGate_concrete_S_uniform_tube`** — dispatch 18 payoff (Sol's uniform-tube kill
    test): the FULL `chartGate_concrete_S_construction` package (J4-1136) PLUS a uniform radius
    `c₀ > 0` for which the concrete flow-ball gate `S_{c₀} q := uniformFlowExp … q '' Metric.ball 0
    c₀` is contained in the shrunk-intersection gate `S q` for EVERY `q ∈ K₀`. This is the exact
    "uniform tube" containment needed to transport `OffSVanishing.lean`'s `hOffS_concrete`/
    `hOffS2_concrete` (proved at `S_{c₀}`) onto `S_∩` via gate-monotonicity (deferred to the next
    dispatch). -/
theorem chartGate_concrete_S_uniform_tube (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {K₀ : Set (Point n)} (hK₀ : IsCompact K₀) (hK₀sub : K₀ ⊆ interior K) :
    ∃ (r₀ : ℝ) (_ : 0 < r₀)
      (Pfield : Point n → Point n → Fin n → Point n → Point n → Fin n → ℝ)
      (U : Point n → Point n → Fin n → Set (Point n × Point n))
      (t : Fin n → Finset (Point n))
      (G : Fin n → Set (Point n × Point n))
      (S : Point n → Set (Point n)),
      (∀ z₀ v₀ (k : Fin n), z₀ ∈ interior K → ‖v₀‖ < r₀ →
        IsOpen (U z₀ v₀ k) ∧
        MeasurableSet (U z₀ v₀ k) ∧
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ U z₀ v₀ k ∧
        (∀ jj : Fin n, Measurable (fun ξ : Point n × Point n => Pfield z₀ v₀ k ξ.1 ξ.2 jj)) ∧
        (∀ ξ ∈ U z₀ v₀ k, ∀ jj : Fin n,
          HasDerivAt
            (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
            (Pfield z₀ v₀ k ξ.1 ξ.2 jj) (ξ.2 k))) ∧
      (∀ z₀ v₀ (k : Fin n) z₀' v₀',
        z₀ ∈ interior K → ‖v₀‖ < r₀ → z₀' ∈ interior K → ‖v₀'‖ < r₀ →
        ∀ ξ ∈ U z₀ v₀ k ∩ U z₀' v₀' k, ∀ jj : Fin n,
          Pfield z₀ v₀ k ξ.1 ξ.2 jj = Pfield z₀' v₀' k ξ.1 ξ.2 jj) ∧
      (∀ k, ↑(t k) ⊆ K₀) ∧
      (∀ k, (fun q => ((q, q) : Point n × Point n)) '' K₀ ⊆ ⋃ z₀ ∈ t k, U z₀ 0 k) ∧
      (∀ k, G k = ⋃ z₀ ∈ t k, U z₀ 0 k) ∧
      (∀ q, S q = ⋂ k, fiberGate (G k) q) ∧
      (∀ q p : Point n, p ∈ S q ↔ ∀ k, ∃ z₀ ∈ t k, ((q, p) : Point n × Point n) ∈ U z₀ 0 k) ∧
      (∀ q, IsOpen (S q)) ∧
      MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} ∧
      (∀ q ∈ K₀, q ∈ S q) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ q ∈ K₀,
        uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c₀ ⊆ S q) := by
  classical
  obtain ⟨r₀, hr₀pos, Pfield, U, t, G, S, hall, hagree, htsub, htcov, hGeq, hSeq, hmemSiff, hSopen,
    hKSmeas, hdiag⟩ := chartGate_concrete_S_construction hn g gi hC hK hK₀ hK₀sub
  refine ⟨r₀, hr₀pos, Pfield, U, t, G, S, hall, hagree, htsub, htcov, hGeq, hSeq, hmemSiff, hSopen,
    hKSmeas, hdiag, ?_⟩
  -- `G k` open (re-derived exactly as inside `chartGate_concrete_S_construction`).
  have hGopen : ∀ k, IsOpen (G k) := by
    intro k
    rw [hGeq k]
    exact isOpen_biUnion (fun z₀ hz₀ =>
      (hall z₀ 0 k (hK₀sub (htsub k hz₀)) (by rw [norm_zero]; exact hr₀pos)).1)
  -- the diagonal of `K₀` is compact and sits inside every `G k`.
  set Δ : Set (Point n × Point n) := (fun q => ((q, q) : Point n × Point n)) '' K₀ with hΔdef
  have hΔcompact : IsCompact Δ := hK₀.image (by fun_prop)
  have hΔsubG : ∀ k, Δ ⊆ G k := by
    intro k; rw [hGeq k]; exact htcov k
  -- per-`k` thickening radius, then a single shared minimum over the finite index `Fin n`.
  have hthick : ∀ k, ∃ δ : ℝ, 0 < δ ∧ Metric.thickening δ Δ ⊆ G k :=
    fun k => hΔcompact.exists_thickening_subset_open (hGopen k) (hΔsubG k)
  choose δ hδpos hδsub using hthick
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set τ : ℝ := Finset.univ.inf' hne δ with hτdef
  have hτpos : 0 < τ := (Finset.lt_inf'_iff hne).mpr (fun k _ => hδpos k)
  have hτle : ∀ k, τ ≤ δ k := fun k => Finset.inf'_le δ (Finset.mem_univ k)
  have hτsub : ∀ k, Metric.thickening τ Δ ⊆ G k :=
    fun k => (Metric.thickening_mono (hτle k) Δ).trans (hδsub k)
  -- the uniform quadratic displacement bound, uniform in `q ∈ K`.
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hdisp⟩ := uniformFlowExp_displacement_bound g gi hC hK
  have hτ24pos : (0 : ℝ) < 2 + 2 * C_D := by linarith
  set c₀ : ℝ := min ρ₀ (min 1 (τ / (2 + 2 * C_D))) with hc₀def
  have hc₀pos : 0 < c₀ := lt_min hρ₀pos (lt_min one_pos (div_pos hτpos hτ24pos))
  refine ⟨c₀, hc₀pos, ?_⟩
  intro q hq
  have hqK : q ∈ K := interior_subset (hK₀sub hq)
  rintro p ⟨v, hv, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hv
  have hvρ₀ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv1 : ‖v‖ < 1 := lt_of_lt_of_le hv ((min_le_right _ _).trans (min_le_left _ _))
  have hvτ : ‖v‖ < τ / (2 + 2 * C_D) := lt_of_lt_of_le hv ((min_le_right _ _).trans (min_le_right _ _))
  have hd := hdisp q hqK v hvρ₀
  -- `‖φ_q v − q‖ ≤ ‖v‖·(1 + C_D·‖v‖)`.
  have hnorm_le : ‖uniformFlowExp g gi hC hK q v - q‖ ≤ ‖v‖ * (1 + C_D * ‖v‖) := by
    have heq : (uniformFlowExp g gi hC hK q v - q - v) + v
        = uniformFlowExp g gi hC hK q v - q := by abel
    calc ‖uniformFlowExp g gi hC hK q v - q‖
        = ‖(uniformFlowExp g gi hC hK q v - q - v) + v‖ := by rw [heq]
      _ ≤ ‖uniformFlowExp g gi hC hK q v - q - v‖ + ‖v‖ := norm_add_le _ _
      _ ≤ C_D * ‖v‖ * ‖v‖ + ‖v‖ := by linarith [hd]
      _ = ‖v‖ * (1 + C_D * ‖v‖) := by ring
  -- that bound is `< τ` from the choice of `c₀`.
  have hbound_lt_τ : ‖v‖ * (1 + C_D * ‖v‖) < τ := by
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
    have hstep : ‖v‖ * (2 + 2 * C_D) < τ := (lt_div_iff₀ hτ24pos).mp hvτ
    nlinarith [mul_nonneg hCD0 hv0, mul_nonneg hCD0 (mul_nonneg hv0 hv0), sq_nonneg (1 - ‖v‖)]
  have hxlt : ‖uniformFlowExp g gi hC hK q v - q‖ < τ := lt_of_le_of_lt hnorm_le hbound_lt_τ
  -- `(q, φ_q v)` is within `τ` of the diagonal point `(q,q) ∈ Δ`.
  have hd2 : dist ((q, uniformFlowExp g gi hC hK q v) : Point n × Point n)
      ((q, q) : Point n × Point n) = ‖uniformFlowExp g gi hC hK q v - q‖ := by
    rw [Prod.dist_eq, dist_self, dist_eq_norm]
    exact max_eq_right (norm_nonneg _)
  have hmemthick : ((q, uniformFlowExp g gi hC hK q v) : Point n × Point n) ∈
      Metric.thickening τ Δ := by
    rw [Metric.mem_thickening_iff]
    exact ⟨(q, q), Set.mem_image_of_mem _ hq, hd2 ▸ hxlt⟩
  have hallk : ∀ k, ((q, uniformFlowExp g gi hC hK q v) : Point n × Point n) ∈ G k :=
    fun k => hτsub k hmemthick
  rw [hSeq q]
  simp only [Set.mem_iInter, mem_fiberGate]
  exact hallk

end QIQTH.ExpMap

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ExpMap
#print axioms chartGate_concrete_S_uniform_tube
end AxiomChecks
