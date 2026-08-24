/-
  GatedTauRepProdSWith — J4-1160: dispatch of the chart-parametric rebuild campaign, Phase 4 Task A/B
  opening — Canary **C2 ("FirstHWMConsumerPrime")**.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  genericizes the EARLIEST `hWmeas`-shaped-hypothesis-consuming audit theorem in the
  `HgateSatAudit`/`GatedRepSFix`/`HEmeasBorelAudit` import-order lineage
  (`HgateSatAudit.gatedTauRepProdS_measurable`, `QIQTH/HgateSatAudit.lean:263-292`) over an ABSTRACT
  chart `W`, per `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md` Phase 4 Task A/B, then instantiates
  the primed copy at `W := uniformInverseChart' g gi hC hK c`, discharging the generic `hWmeas`
  hypothesis via `ThetaMeasurableEmbedding.uniformInverseChart'_joint_measurable` (J4-1147).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS IS THE EARLIEST `hWmeas`-CONSUMING AUDIT THEOREM.

  Import order (not filename order): `HgateSatAudit.lean` imports only `ChartJetHessianMixed` (no
  audit-chain predecessor); `GatedRepSFix.lean` imports `HgateSatAudit` + `GatedDerivRepProduct`;
  `HEmeasBorelAudit.lean` imports `HEmeasRecon`/`SecondDerivEnvelope`/`IterEMeasurable` (a DIFFERENT,
  later branch). So `HgateSatAudit.lean` is upstream of the other two in this lineage. Within
  `HgateSatAudit.lean` itself, `gatedTauRepProdS_measurable` (line 263) is the FIRST theorem whose
  hypothesis list contains a raw joint-chart-measurability premise of exactly the `hWmeas` shape:
  `hChartMeas : Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2
  w.2.1)` — earlier theorems in the file (`gate_Sconj_impossible`, `hcarTau_unsat`, etc., §1) are pure
  UNSATISFIABILITY results about the gate predicate and consume no chart-measurability hypothesis at
  all. (The later `tauDeriv_prod_stronglyMeasurable_v4`, line 380, bundles the same `hChartMeas` inside
  an `hcar` existential — it is downstream of `gatedTauRepProdS_measurable`, not earlier.)

  ## THE CRUX CHECK (canary condition) — SHAPE MATCH, VERIFIED.

  `uniformInverseChart'_joint_measurable` (`ThetaMeasurableEmbedding.lean:204-221`) concludes, for a
  chosen `0 < c < δ₀`:
    `Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart' g gi hC hK c w.2.2 w.2.1)`
  — IDENTICAL variable order/shape (`w.2.2` then `w.2.1`, same ambient type `ℝ × Point n × Point n`) to
  `gatedTauRepProdS_measurable`'s `hChartMeas`. The only difference is the extra tube-radius argument
  `c`, which is simply absorbed into the abstract `W` at instantiation time
  (`W := uniformInverseChart' g gi hC hK c`, a fixed partial application) — no currying mismatch, no
  sigma-algebra mismatch, no argument-order mismatch.

  Re-inspecting `gatedTauRepProdS_measurable`'s PROOF confirms `hChartMeas` (renamed `hWmeas` in the
  generic sibling) is used ONLY for raw measurability composition — `gaussDdim_uncurry_measurable.comp
  (measurable_fst.prodMk hWmeas)` and `(measurable_pi_apply i).comp hWmeas` — never for any hidden
  geometric/reachability fact, never to identify the chart pointwise with anything else, never outside
  the bounded-tube discipline (the def itself never claims anything about the RANGE of `W`, only its
  measurability). **CANARY C2 RESULT: PASS**, cleanly, exactly matching J4-1158's C1 pattern (mechanical
  `W`-for-`uniformInverseChart` substitution of the old proof, verbatim).

  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `gatedTauRepProdSWith` — chart-generic sibling of `HgateSatAudit.gatedTauRepProdS`, at an
      ABSTRACT `W : Point n → Point n → Point n` in place of `uniformInverseChart g gi hC hK`.
    * `gatedTauRepProdSWith_uniformInverseChart` — the `rfl` compatibility bridge:
      `gatedTauRepProdSWith … (uniformInverseChart g gi hC hK) = gatedTauRepProdS …`.
    * `gatedTauRepProdS'` — the PRIMED instance, `gatedTauRepProdSWith … (uniformInverseChart' g gi hC
      hK c)`.
    * `gatedTauRepProdSWith_measurable` — chart-generic sibling of `gatedTauRepProdS_measurable`, over
      abstract `W` + `hWmeas : Measurable (fun w => W w.2.2 w.2.1)` (Phase 4 Task A).
    * `gatedTauRepProdS'_measurable` — ★★ THE CANARY DELIVERABLE (Phase 4 Task B): the primed
      measurability audit theorem, `∃ δ₀ > 0, ∀ c, 0 < c → c < δ₀ → Measurable (gatedTauRepProdS' … c)`,
      with the chart-measurability hypothesis fully DISCHARGED via
      `uniformInverseChart'_joint_measurable` — no free `hWmeas`/`hChartMeas` hypothesis remains.

  ## WHAT THIS DOES NOT DO.
  Does NOT claim `gatedTauRepProdS' = gatedTauRepProdS` or any global old/new chart equality (false in
  general). Does NOT genericize `witnessTauDeriv_eq_gatedTauRepProdS` or
  `tauDeriv_prod_stronglyMeasurable_v4` (those consume `hgate`/`HasDerivAt` data about `chartFieldAmp`,
  not raw chart measurability — out of THIS canary's narrow scope; left for the next Phase 4 Task B
  dispatch, per the plan's "push genericity through each subsequent audit structure"). Does NOT touch
  `GatedRepSFix.lean`/`HEmeasBorelAudit.lean` (later in the lineage).

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.HgateSatAudit
import QIQTH.ThetaMeasurableEmbedding

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open QIQTH.ThetaMeasurableEmbedding
open scoped Topology BigOperators ContDiff

namespace QIQTH.HgateSatAudit

variable {n : ℕ}

/-! ###############################################################################
    ### `gatedTauRepProdSWith` — chart-generic sibling of `gatedTauRepProdS`.
    ############################################################################### -/

/-- **`gatedTauRepProdSWith`.**  Chart-generic sibling of `gatedTauRepProdS`, at an ABSTRACT
    `W : Point n → Point n → Point n` in place of `uniformInverseChart g gi hC hK`. Identical closed
    form and gate. NOT `a₁ = R/6`. -/
noncomputable def gatedTauRepProdSWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) (W : Point n → Point n → Point n) :
    ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
    (fun w : ℝ × Point n × Point n =>
      ((∑ i, ((W w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1)))
            * gaussDdim w.1 (W w.2.2 w.2.1))
          * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
        + gaussDdim w.1 (W w.2.2 w.2.1) * Cfield w.2.2 w.2.1)

/-- **`gatedTauRepProdSWith_uniformInverseChart`** — the compatibility bridge, `rfl`. -/
theorem gatedTauRepProdSWith_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) :
    gatedTauRepProdSWith g gi hC hK S a b Cfield (uniformInverseChart g gi hC hK)
      = gatedTauRepProdS g gi hC hK S a b Cfield := rfl

/-- **`gatedTauRepProdS'`** — the PRIMED instance at `uniformInverseChart' g gi hC hK c`. -/
noncomputable def gatedTauRepProdS' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) (c : ℝ) : ℝ × Point n × Point n → ℝ :=
  gatedTauRepProdSWith g gi hC hK S a b Cfield (uniformInverseChart' g gi hC hK c)

/-! ###############################################################################
    ### `gatedTauRepProdSWith_measurable` — Phase 4 Task A: generic over `W` + `hWmeas`.
    ############################################################################### -/

/-- **★ `gatedTauRepProdSWith_measurable`.**  Chart-generic sibling of `gatedTauRepProdS_measurable`:
    joint `(τ,p,q)`-Borel measurability of the re-gated τ representative, from `hKSmeas`, an ABSTRACT
    `hWmeas : Measurable (fun w => W w.2.2 w.2.1)`, and the same factor measurabilities. Proof is a
    mechanical `W`-for-`uniformInverseChart g gi hC hK` substitution of the old proof — `hWmeas` is used
    ONLY for raw measurability composition, exactly as the canary requires. NOT `a₁ = R/6`. -/
theorem gatedTauRepProdSWith_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) (W : Point n → Point n → Point n)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hWmeas : Measurable (fun w : ℝ × Point n × Point n => W w.2.2 w.2.1))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hCmeas : Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)) :
    Measurable (gatedTauRepProdSWith g gi hC hK S a b Cfield W) := by
  unfold gatedTauRepProdSWith
  have hG : Measurable
      (fun w : ℝ × Point n × Point n => gaussDdim w.1 (W w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hWmeas)
  have hCoef : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ i, ((W w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) := by
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    have h1 : Measurable
        (fun w : ℝ × Point n × Point n => (W w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2)) :=
      (((measurable_pi_apply i).comp hWmeas).pow_const 2).div
        (measurable_const.mul (measurable_fst.pow_const 2))
    have h2 : Measurable (fun w : ℝ × Point n × Point n => (1 : ℝ) / (2 * w.1)) :=
      measurable_const.div (measurable_const.mul measurable_fst)
    exact h1.sub h2
  exact (((hCoef.mul hG).mul hAmpMeas).add (hG.mul hCmeas)).indicator hKSmeas

/-! ###############################################################################
    ### `gatedTauRepProdS'_measurable` — Phase 4 Task B, the CANARY C2 DELIVERABLE.
    ############################################################################### -/

/-- **★★ `gatedTauRepProdS'_measurable`.**  THE CANARY C2 ("FirstHWMConsumerPrime") DELIVERABLE:
    instantiating `gatedTauRepProdSWith_measurable` at the NEW chart `W := uniformInverseChart' g gi hC
    hK c`, discharging the generic `hWmeas` hypothesis via `uniformInverseChart'_joint_measurable`
    (J4-1147) — no free chart-measurability hypothesis remains. Matches the existential `∃ δ₀ > 0, ∀ c,
    0 < c → c < δ₀ → …` shape of `uniformInverseChart'_joint_measurable` itself. NOT `a₁ = R/6`. -/
theorem gatedTauRepProdS'_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hCmeas : Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      Measurable (gatedTauRepProdS' g gi hC hK S a b Cfield c) := by
  obtain ⟨δ₀, hδ₀, hmeas⟩ := uniformInverseChart'_joint_measurable g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  unfold gatedTauRepProdS'
  exact gatedTauRepProdSWith_measurable g gi hC hK S a b Cfield
    (uniformInverseChart' g gi hC hK c) hKSmeas (hmeas c hc0 hcδ) hAmpMeas hCmeas

end QIQTH.HgateSatAudit

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HgateSatAudit
#print axioms gatedTauRepProdSWith_uniformInverseChart
#print axioms gatedTauRepProdSWith_measurable
#print axioms gatedTauRepProdS'_measurable
end AxiomChecks
