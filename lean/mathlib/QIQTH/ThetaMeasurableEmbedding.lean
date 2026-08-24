/-
  ThetaMeasurableEmbedding — J4-1147: dispatch 1 of Sol's 4-dispatch plan to close `hWmeas`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It packages
  three small, reusable measurability pieces that dispatches 26/27/28 will assemble into a NEW canonical
  chart `uniformInverseChart'` whose joint measurability (`hWmeas'`) is provable — unlike the existing
  per-point `Exists.choose`-built `uniformInverseChart`, which is blocked by proof-irrelevance
  (J4-1145).  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no existing
  file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `TubeDomain K c` — the Borel domain `K ×ˢ Metric.ball 0 c` on which the flow-graph map is a
      measurable embedding; and `thetaMap g gi hC hK` — the forward-flow graph map
      `Θ (q,v) = (q, φ_q v)` (`φ_q = uniformFlowExp g gi hC hK q`).

    * `theta_measurableEmbedding` — ★ THE REUSABLE LUSIN–SOUSLIN CORE, refactored out of
      `ConcreteGateInstantiation.hKSmeas_concrete` (J4-234): a single uniform radius `δ₀ > 0` such that
      for every `0 < c < δ₀`, `(TubeDomain K c).restrict (thetaMap g gi hC hK)` is a
      `MeasurableEmbedding` (jointly continuous + injective on the tube via the germ left-inverse, then
      `ContinuousOn.measurableEmbedding`).

    * `embeddingPullbackDflt` — the GENERIC zero/default-extended partial-inverse-measurability lemma:
      for any `MeasurableEmbedding f`, any measurable `g` and any measurable default `dflt`, the map
      `Function.extend f g dflt` is measurable AND recovers `g` on the range (`= g x` at every `f x`).
      This is a thin, honest repackaging of Mathlib's `MeasurableEmbedding.measurable_extend` +
      `Function.Injective.extend_apply` — no `Nonempty`/`Inhabited` obligation.

    * `uniformInverseChart'` — the NEW canonical chart, defined as the velocity coordinate of the
      default-extended partial inverse of `thetaMap` (NOT via `Exists.choose`): on the tube it recovers
      `v` (`uniformInverseChart'_flow_eq`), off the graph it is `0`.

    * `uniformInverseChart'_joint_measurable` — ★★ THE PAYOFF SHAPE: a single `δ₀ > 0` such that for
      every `0 < c < δ₀` the joint map `fun w : ℝ × Point n × Point n => uniformInverseChart' … c w.2.2
      w.2.1` is `Measurable`.  This is exactly the `hWmeas` shape that was unclosable for the opaque
      `uniformInverseChart` — here it is DERIVED, not assumed.

  ## WHAT REMAINS (dispatches 26/27/28, NOT this dispatch).
    * dispatch 26 — the germ bridge: `uniformInverseChart'` satisfies the `huniformChart` shape (germ +
      `ContDiffAt ℝ 2` + open/closure) that `gatedWitness_hEboundW_final_gen` consumes; the `C²` germ is
      transported from the OLD `uniformInverseChart` across their eventual equality on the tube image
      (both equal the true inverse), since the raw `extend` is not smooth.
    * dispatch 27 — instantiate `gatedWitness_hEboundW_final_gen` at `W := uniformInverseChart' … c`.
    * dispatch 28 — the parallel residualization theorem for `uniformInverseChart'` (mirroring J4-1143).

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ConcreteGateInstantiation

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.FlowJointContinuity
open scoped Topology BigOperators ContDiff

namespace QIQTH.ThetaMeasurableEmbedding

variable {n : ℕ}

/-! ###############################################################################
    ### THE GENERIC PIECE — default-extended partial inverse of a measurable embedding.
    ############################################################################### -/

/-- **`embeddingPullbackDflt` — the generic default-extended partial-inverse lemma.**  For any
    `MeasurableEmbedding f : α → β`, any measurable `g : α → γ` and any measurable default
    `dflt : β → γ`, the default-extended partial inverse `Function.extend f g dflt : β → γ` is
    `Measurable` and recovers `g` on the range (`= g x` at every `f x`).  Thin repackaging of
    `MeasurableEmbedding.measurable_extend` + `Function.Injective.extend_apply`; no `Nonempty`
    obligation on the source.  NOT `a₁ = R/6`. -/
theorem embeddingPullbackDflt {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α → β} (hf : MeasurableEmbedding f)
    {g : α → γ} (hg : Measurable g) {dflt : β → γ} (hdflt : Measurable dflt) :
    Measurable (Function.extend f g dflt) ∧
      ∀ x, Function.extend f g dflt (f x) = g x :=
  ⟨hf.measurable_extend hg hdflt, fun x => hf.injective.extend_apply g dflt x⟩

/-! ###############################################################################
    ### THE TUBE DOMAIN AND FLOW-GRAPH MAP.
    ############################################################################### -/

/-- **`TubeDomain K c`** — the Borel domain `K ×ˢ Metric.ball 0 c` on which the forward-flow graph map
    is a measurable embedding.  NOT `a₁ = R/6`. -/
def TubeDomain (K : Set (Point n)) (c : ℝ) : Set (Point n × Point n) :=
  K ×ˢ Metric.ball (0 : Point n) c

/-- **`thetaMap g gi hC hK`** — the forward-flow graph map `Θ (q,v) = (q, φ_q v)` with
    `φ_q = uniformFlowExp g gi hC hK q`.  NOT `a₁ = R/6`. -/
noncomputable def thetaMap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    Point n × Point n → Point n × Point n :=
  fun p => (p.1, uniformFlowExp g gi hC hK p.1 p.2)

/-! ###############################################################################
    ### ★ THE LUSIN–SOUSLIN CORE — `thetaMap` is a measurable embedding on the tube.
    ###   (refactored from `ConcreteGateInstantiation.hKSmeas_concrete`, J4-234)
    ############################################################################### -/

/-- **★ `theta_measurableEmbedding` — the reusable Lusin–Souslin core.**  A single uniform radius
    `δ₀ > 0` (`= min (germ radius) (uniformFlowRadius)`) such that for every `0 < c < δ₀`,
    `(TubeDomain K c).restrict (thetaMap g gi hC hK)` is a `MeasurableEmbedding`.  The forward-flow
    graph map `Θ (q,v) = (q, φ_q v)` is jointly continuous (`uniformFlowExp_joint_continuousOn`) and
    injective on the tube (via the germ left-inverse `uniformInverseChart_huniformChart`), so
    `ContinuousOn.measurableEmbedding` makes `D.restrict Θ` a measurable embedding.  Refactored from
    `ConcreteGateInstantiation.hKSmeas_concrete` (J4-234).  NOT `a₁ = R/6`. -/
theorem theta_measurableEmbedding (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      MeasurableEmbedding ((TubeDomain K c).restrict (thetaMap g gi hC hK)) := by
  classical
  obtain ⟨δg, hδg, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  have hRpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨min δg (uniformFlowRadius g gi hC hK), lt_min hδg hRpos, ?_⟩
  intro c hc0 hcδ
  have hcg : c < δg := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcR : c < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hcδ (min_le_right _ _)
  -- germ left inverse on `ball 0 c`.
  have hLeftInv : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < c →
      uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
    intro q hq v hv
    have hgerm := ((hchart q hq).1 v (lt_trans hv hcg)).1
    simpa using hgerm.eq_of_nhds
  have hDmeas : MeasurableSet (TubeDomain K c) :=
    hK.isClosed.measurableSet.prod measurableSet_ball
  have hDsub : TubeDomain K c ⊆ K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) :=
    Set.prod_mono (Set.Subset.refl K) (Metric.ball_subset_ball (le_of_lt hcR))
  have hsnd : ContinuousOn (fun p : Point n × Point n =>
      uniformFlowExp g gi hC hK p.1 p.2) (TubeDomain K c) :=
    (uniformFlowExp_joint_continuousOn g gi hC hK).mono hDsub
  have hΘcont : ContinuousOn (thetaMap g gi hC hK) (TubeDomain K c) := by
    unfold thetaMap
    exact (continuous_fst.continuousOn).prodMk hsnd
  have hΘinj : Set.InjOn (thetaMap g gi hC hK) (TubeDomain K c) := by
    intro x hx y hy hxy
    rw [TubeDomain, Set.mem_prod] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    rw [mem_ball_zero_iff] at hx2 hy2
    simp only [thetaMap, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have hx2' : uniformInverseChart g gi hC hK x.1 (uniformFlowExp g gi hC hK x.1 x.2) = x.2 :=
      hLeftInv x.1 hx1 x.2 hx2
    have hy2' : uniformInverseChart g gi hC hK x.1 (uniformFlowExp g gi hC hK x.1 y.2) = y.2 :=
      hLeftInv x.1 hx1 y.2 hy2
    have hval : uniformFlowExp g gi hC hK x.1 x.2 = uniformFlowExp g gi hC hK x.1 y.2 := by
      rw [h2, ← h1]
    have hxy2 : x.2 = y.2 := by rw [← hx2', hval, hy2']
    exact Prod.ext_iff.mpr ⟨h1, hxy2⟩
  exact ContinuousOn.measurableEmbedding hDmeas hΘcont hΘinj

/-! ###############################################################################
    ### THE NEW CANONICAL CHART — velocity coordinate of the default-extended inverse.
    ############################################################################### -/

/-- **`uniformInverseChart'` — the NEW canonical chart (no `Exists.choose`).**  Defined as the velocity
    coordinate of the default-extended partial inverse of `thetaMap`: on the tube (`p = φ_q v`,
    `(q,v) ∈ TubeDomain K c`) it recovers `v`; off the graph it is `0`.  This is the non-opaque
    replacement for `uniformInverseChart` that admits a joint-measurability proof.  NOT `a₁ = R/6`. -/
noncomputable def uniformInverseChart' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) :
    Point n → Point n → Point n :=
  fun q p =>
    Function.extend
      ((TubeDomain K c).restrict (thetaMap g gi hC hK))
      (fun x : ↥(TubeDomain K c) => (x : Point n × Point n).2)
      (fun _ => (0 : Point n))
      (q, p)

/-- **`uniformInverseChart'_flow_eq` — the tube left-inverse equation.**  For `0 < c < δ₀` (the radius
    of `theta_measurableEmbedding`), `q ∈ K` and `‖v‖ < c`, the new chart recovers `v`:
    `uniformInverseChart' … c q (φ_q v) = v`.  Non-opaque: proved from `Function.Injective.extend_apply`
    at the subtype point `⟨(q,v), _⟩`, NOT from any `Exists.choose` spec.  NOT `a₁ = R/6`. -/
theorem uniformInverseChart'_flow_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {c : ℝ}
    (hemb : MeasurableEmbedding ((TubeDomain K c).restrict (thetaMap g gi hC hK)))
    {q : Point n} (hq : q ∈ K) {v : Point n} (hv : ‖v‖ < c) :
    uniformInverseChart' g gi hC hK c q (uniformFlowExp g gi hC hK q v) = v := by
  have hmem : (q, v) ∈ TubeDomain K c := by
    rw [TubeDomain, Set.mem_prod]
    exact ⟨hq, mem_ball_zero_iff.mpr hv⟩
  have hkey := hemb.injective.extend_apply
    (fun x : ↥(TubeDomain K c) => (x : Point n × Point n).2)
    (fun _ => (0 : Point n)) ⟨(q, v), hmem⟩
  -- `(TubeDomain K c).restrict (thetaMap …) ⟨(q,v),_⟩ = (q, φ_q v)`.
  simpa [uniformInverseChart', Set.restrict, thetaMap] using hkey

/-! ###############################################################################
    ### ★★ THE PAYOFF — joint measurability of the new chart (the `hWmeas` shape).
    ############################################################################### -/

/-- **★★ `uniformInverseChart'_joint_measurable` — the closable `hWmeas` shape.**  A single `δ₀ > 0`
    such that for every `0 < c < δ₀` the joint map
      `fun w : ℝ × Point n × Point n => uniformInverseChart' g gi hC hK c w.2.2 w.2.1`
    is `Measurable`.  This is exactly the `hWmeas` shape (per J4-1145) — UNGATED in the field point —
    that was UNCLOSABLE for the opaque `uniformInverseChart`; here it is DERIVED from
    `embeddingPullbackDflt` + `theta_measurableEmbedding`, composed with the measurable coordinate swap.
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart'_joint_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      Measurable (fun w : ℝ × Point n × Point n =>
        uniformInverseChart' g gi hC hK c w.2.2 w.2.1) := by
  obtain ⟨δ₀, hδ₀, hemb⟩ := theta_measurableEmbedding g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  have hpull := (embeddingPullbackDflt (hemb c hc0 hcδ)
    (g := fun x : ↥(TubeDomain K c) => (x : Point n × Point n).2)
    (measurable_subtype_coe.snd)
    (dflt := fun _ => (0 : Point n)) measurable_const).1
  -- `uniformInverseChart' … c q p = extend … (q,p)`, so the (q,p)-joint map IS the extend map.
  have hqp : Measurable (fun qp : Point n × Point n =>
      uniformInverseChart' g gi hC hK c qp.1 qp.2) := hpull
  -- compose with the measurable swap `w ↦ (w.2.2, w.2.1)`.
  exact hqp.comp ((measurable_snd.snd).prodMk measurable_snd.fst)

end QIQTH.ThetaMeasurableEmbedding

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ThetaMeasurableEmbedding
#print axioms embeddingPullbackDflt
#print axioms theta_measurableEmbedding
#print axioms uniformInverseChart'
#print axioms uniformInverseChart'_flow_eq
#print axioms uniformInverseChart'_joint_measurable
end AxiomChecks
