/-
  WitnessTauDerivEqWith — J4-1161: dispatch of the chart-parametric rebuild campaign, Phase 4 Task B
  continuation from J4-1160 — genericizes `HgateSatAudit.witnessTauDeriv_eq_gatedTauRepProdS` and
  `HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4`, per
  `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## A GENUINE OBSTRUCTION FOUND AND ROUTED AROUND (not forced, not silently patched).

  The dispatch brief instructed reusing `HgateSatAudit.gatedTauRepProdSWith` (`GatedTauRepProdSWith.lean`,
  J4-1160) verbatim as the RHS representative.  Direct inspection of that def (lines 93-103) shows it is
  only PARTIALLY chart-generic: it threads the abstract chart `W` through the GAUSSIAN-ARGUMENT slots
  (`W w.2.2 w.2.1` inside `gaussDdim`/the coefficient sum) but its AMPLITUDE term still calls the
  concrete, chart-HARDWIRED `chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1` literally — NOT
  `chartFieldAmpWith g gi hC hK a b W …`.  This was harmless for J4-1160's own goal (pure joint
  measurability of the representative: `hAmpMeas` is a free hypothesis whose STATEMENT never needs to
  reference `W`), but it is FATAL for a genuine chart-generic τ-DERIVATIVE identity theorem: the
  product-rule identity needs the un-differentiated amplitude VALUE term inside the representative to
  equal `chartFieldAmpWith … W …` at the SAME `W` used by the witness derivative — literally FALSE for
  `W ≠ uniformInverseChart g gi hC hK` (confirmed by direct computation: at `W := uniformInverseChart'`,
  `chartFieldAmp` — hardwired to the OLD chart — is a different real number in general from
  `chartFieldAmp' … c`, so `ring`/`exact` would fail with no available bridging hypothesis).

  RESOLUTION (routine engineering, not abandonment — matches the precedent set by
  `WitnessFieldDerivConsumersWith.witnessFieldDerivWith_gate_eq`, J4-1158, which threads
  `chartFieldAmpWith … W` throughout, NOT the hardwired `chartFieldAmp`): this file builds its OWN,
  FULLY chart-generic representative `gatedTauRepProdSGenWith` — identical shape to
  `gatedTauRepProdSWith` except the amplitude term is `chartFieldAmpWith g gi hC hK a b W …` — and
  proves the derivative identity against THAT.  `GatedTauRepProdSWith.lean` is left completely untouched
  (never edited); `gatedTauRepProdSWith`/`gatedTauRepProdS'`/`gatedTauRepProdS'_measurable` remain
  exactly as banked (still a valid, useful — if only partially generic — measurability-only artifact for
  the OLD amplitude).  `gatedTauRepProdSGenWith … (uniformInverseChart g gi hC hK) =
  gatedTauRepProdSWith … (uniformInverseChart g gi hC hK) = gatedTauRepProdS …` all by `rfl` (the two
  representatives coincide exactly ON the old chart, where `chartFieldAmpWith … (uniformInverseChart …)
  = chartFieldAmp …` is itself `rfl`) — so nothing already banked is contradicted, only supplemented.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `gatedTauRepProdSGenWith` — the FULLY chart-generic τ representative (Gaussian argument AND
      amplitude both at abstract `W`).
    * `gatedTauRepProdSGenWith_uniformInverseChart` — `rfl` bridge to the OLD `gatedTauRepProdS`.
    * `gatedTauRepProdSGen'` — the PRIMED instance at `uniformInverseChart' g gi hC hK c`.
    * `gatedTauRepProdSGenWith_measurable` / `gatedTauRepProdSGen'_measurable` — the generic-`W`+`hWmeas`
      and primed (chart-measurability DISCHARGED via `uniformInverseChart'_joint_measurable`)
      measurability siblings, mirroring J4-1160's Task A/B pattern for the corrected representative.
    * ★★ `witnessTauDeriv_eq_gatedTauRepProdSWith` — the GENERIC sibling of
      `HgateSatAudit.witnessTauDeriv_eq_gatedTauRepProdS`: chart-generic `hgate` (about
      `chartFieldAmpWith … W`), chart-generic witness (`vanVleckGatedWitnessWith … W`), RHS
      `gatedTauRepProdSGenWith`.  Proof is a MECHANICAL `W`-for-`uniformInverseChart` substitution of the
      old proof, verbatim (the two ingredients it leans on —
      `WitnessFieldDerivConsumersWith.vanVleckGatedWitnessWith_gate_apply`, J4-1158, and
      `GlobalHunifAssembly.gatedKernel_apply_of_notMem` — were ALREADY chart-generic).
    * `witnessTauDeriv_eq_gatedTauRepProdSWith_recovers_old` — the compatibility bridge recovering the
      OLD theorem's exact statement at `W := uniformInverseChart g gi hC hK` (closes by direct
      application + the `rfl` bridges above — no new proof content).
    * ★★★ `witnessTauDeriv_eq_gatedTauRepProdS'` — the PRIMED instantiation at
      `uniformInverseChart' g gi hC hK c`: the first genuine relational τ-derivative identity connecting
      the PRIMED witness (`vanVleckGatedWitness'`) to `chartFieldAmp'`, closing with NO extra machinery
      beyond the caller-supplied `hgate`.
    * `tauDeriv_prod_stronglyMeasurable_v4With` — the generic sibling of
      `HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4`, over abstract `W` + `hWmeas` (chart
      measurability pulled OUT of the `hcar` existential as its own hypothesis, mirroring how
      `gatedTauRepProdSWith_measurable` generalized `gatedTauRepProdS_measurable`'s `hChartMeas`).
    * ★★★ `tauDeriv_prod_stronglyMeasurable_v4'` — the PRIMED instantiation: `hWmeas` fully DISCHARGED
      via `uniformInverseChart'_joint_measurable` (no free chart-measurability hypothesis remains); the
      genuinely amplitude-analytic hypotheses (`hAmpMeas`/`hgate`, about `chartFieldAmp'`, per tube
      radius `c`) remain as caller-supplied inputs — exactly as they must, since they are NOT
      chart-measurability facts.

  ## CANARY C3 ASSESSMENT — HONEST, NOT OVERCLAIMED.
  The plan defines Canary C3 ("PrimeHEmeasAudit") as "a complete primed `HEmeasBorelAudit`-level result
  with no raw `hWmeas` hypothesis" (target dispatch 16-20).  `tauDeriv_prod_stronglyMeasurable_v4'` above
  IS a primed result with no raw `hWmeas`/chart-measurability hypothesis — but it lives at the
  `HgateSatAudit`-level τ-carrier ONLY, not at the `HEmeasBorelAudit` level, and the field/field² carriers
  (§3 of `HgateSatAudit.lean`, still PROSE-only re-thread plan, never formalized even in the OLD
  concrete file) remain untouched.  `GatedRepSFix.lean`/`HEmeasBorelAudit.lean` are NOT touched this
  dispatch.  So this dispatch is a genuine STEP TOWARD Canary C3 (closes the τ-carrier leg of Phase 4
  Task B, matching J4-1160's own forward note), NOT Canary C3 itself.  Next dispatch target: either (a)
  the field/field² carrier re-thread this file's header documents was never even formalized for the OLD
  chart (so the SAME v4-style honest fix needs to land in a NEW file for `GatedDerivRepProduct`/
  `ChartJetHessianMixed`-style field carriers before it can be genericized), or (b) push into
  `GatedRepSFix.lean`/`HEmeasBorelAudit.lean` directly if a τ-only entry point exists there.

  ## WHAT THIS DOES NOT DO.
  Does NOT claim `gatedTauRepProdSGen' = gatedTauRepProdSWith` or any cross-representative identity
  beyond the shared `rfl` value at the OLD chart.  Does NOT touch `GatedRepSFix.lean`/
  `HEmeasBorelAudit.lean`.  Does NOT genericize the field/field² (`hcarField`/`hcarField2`) carriers (§3
  prose plan in `HgateSatAudit.lean`, never formalized even for the old chart).  Does NOT edit
  `HgateSatAudit.lean`, `AmplitudePackage.lean`, `GlobalHunifAssembly.lean`, or any `*With.lean` file.

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.HgateSatAudit
import QIQTH.WitnessFieldDerivConsumersWith

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open QIQTH.ThetaMeasurableEmbedding
open scoped Topology BigOperators ContDiff

namespace QIQTH.HgateSatAudit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The FULLY chart-generic τ representative — `gatedTauRepProdSGenWith`.
    ############################################################################### -/

/-- **`gatedTauRepProdSGenWith`.**  The FULLY chart-generic sibling of `gatedTauRepProdS`: both the
    Gaussian-argument slots AND the amplitude term are at the abstract `W`
    (`chartFieldAmpWith … W`, NOT the hardwired `chartFieldAmp`).  See the header for why this
    supplements — rather than reuses — `GatedTauRepProdSWith.gatedTauRepProdSWith`.  NOT `a₁ = R/6`. -/
noncomputable def gatedTauRepProdSGenWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) (W : Point n → Point n → Point n) :
    ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
    (fun w : ℝ × Point n × Point n =>
      ((∑ i, ((W w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1)))
            * gaussDdim w.1 (W w.2.2 w.2.1))
          * chartFieldAmpWith g gi hC hK a b W w.1 w.2.2 w.2.1
        + gaussDdim w.1 (W w.2.2 w.2.1) * Cfield w.2.2 w.2.1)

/-- **`gatedTauRepProdSGenWith_uniformInverseChart`** — the `rfl` compatibility bridge to the OLD
    `gatedTauRepProdS` (valid because `chartFieldAmpWith … (uniformInverseChart …) = chartFieldAmp …`
    is itself `rfl`). -/
theorem gatedTauRepProdSGenWith_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) :
    gatedTauRepProdSGenWith g gi hC hK S a b Cfield (uniformInverseChart g gi hC hK)
      = gatedTauRepProdS g gi hC hK S a b Cfield := rfl

/-- **`gatedTauRepProdSGen'`** — the PRIMED instance at `uniformInverseChart' g gi hC hK c`. -/
noncomputable def gatedTauRepProdSGen' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) (c : ℝ) : ℝ × Point n × Point n → ℝ :=
  gatedTauRepProdSGenWith g gi hC hK S a b Cfield (uniformInverseChart' g gi hC hK c)

/-! ###############################################################################
    ### Measurability — generic-`W` and primed (chart-measurability discharged) siblings.
    ############################################################################### -/

/-- **`gatedTauRepProdSGenWith_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the FULLY generic
    τ representative, from `hKSmeas`, an ABSTRACT `hWmeas`, and the amplitude/`Cfield` measurabilities
    (about `chartFieldAmpWith … W`, matching the representative's own amplitude term). NOT `a₁ = R/6`. -/
theorem gatedTauRepProdSGenWith_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) (W : Point n → Point n → Point n)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hWmeas : Measurable (fun w : ℝ × Point n × Point n => W w.2.2 w.2.1))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmpWith g gi hC hK a b W w.1 w.2.2 w.2.1))
    (hCmeas : Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)) :
    Measurable (gatedTauRepProdSGenWith g gi hC hK S a b Cfield W) := by
  unfold gatedTauRepProdSGenWith
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

/-- **★★ `gatedTauRepProdSGen'_measurable`.**  The primed measurability audit for the FULLY generic
    representative: chart joint-measurability DISCHARGED via `uniformInverseChart'_joint_measurable`
    (J4-1147); the amplitude measurability hypothesis is genuinely `c`-dependent here (since
    `chartFieldAmp'` itself depends on `c`), supplied per-`c` by the caller. NOT `a₁ = R/6`. -/
theorem gatedTauRepProdSGen'_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hAmpMeas : ∀ c : ℝ, Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp' g gi hC hK a b c w.1 w.2.2 w.2.1))
    (hCmeas : Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      Measurable (gatedTauRepProdSGen' g gi hC hK S a b Cfield c) := by
  obtain ⟨δ₀, hδ₀, hmeas⟩ := uniformInverseChart'_joint_measurable g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  unfold gatedTauRepProdSGen'
  exact gatedTauRepProdSGenWith_measurable g gi hC hK S a b Cfield
    (uniformInverseChart' g gi hC hK c) hKSmeas (hmeas c hc0 hcδ) (hAmpMeas c) hCmeas

/-! ###############################################################################
    ### ★★ THE GENERIC DERIVATIVE IDENTITY — `witnessTauDeriv_eq_gatedTauRepProdSWith`.
    ############################################################################### -/

/-- **★★ `witnessTauDeriv_eq_gatedTauRepProdSWith` — the GENERIC τ EVERYWHERE IDENTITY.**  Chart-generic
    sibling of `HgateSatAudit.witnessTauDeriv_eq_gatedTauRepProdS`, at an ABSTRACT `W`.  Proof mirrors
    the old one EXACTLY (mechanical `W`-for-`uniformInverseChart` substitution): the two ingredients it
    leans on, `vanVleckGatedWitnessWith_gate_apply` (J4-1158) and `gatedKernel_apply_of_notMem`
    (`GlobalHunifAssembly.lean`), were ALREADY chart-generic. NOT `a₁ = R/6`. -/
theorem witnessTauDeriv_eq_gatedTauRepProdSWith (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) (W : Point n → Point n → Point n)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        HasDerivAt (fun u : ℝ => chartFieldAmpWith g gi hC hK a b W u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1) :
    ∀ w : ℝ × Point n × Point n,
      deriv (fun u => vanVleckGatedWitnessWith g gi hC hK S a b W u w.2.1 w.2.2) w.1
        = gatedTauRepProdSGenWith g gi hC hK S a b Cfield W w := by
  intro w
  simp only [gatedTauRepProdSGenWith]
  by_cases hzKS : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
  · obtain ⟨hzK, hpS⟩ := hzKS
    rw [Set.indicator_of_mem
      (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from ⟨hzK, hpS⟩)]
    set v := W w.2.2 w.2.1 with hvdef
    by_cases hτ : 0 < w.1
    · -- ON FULL GATE, τ > 0: the funext factorisation + product rule.
      have hamp := hgate w hzK hτ hpS
      have hfe : (fun u => vanVleckGatedWitnessWith g gi hC hK S a b W u w.2.1 w.2.2)
          = (fun u => gaussDdim u v * chartFieldAmpWith g gi hC hK a b W u w.2.2 w.2.1) := by
        funext u
        rw [vanVleckGatedWitnessWith_gate_apply g gi hC hK S a b W u hzK hpS]
        simp only [chartFieldAmpWith, hvdef]
        ring
      have hgauss_deriv_eq : deriv (fun u => gaussDdim u v) w.1
          = (∑ i, ((v i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) * gaussDdim w.1 v := by
        rw [gaussDdim_heat_eqn w.1 hτ v, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => gaussDdim_pd_pd_i w.1 hτ v i)
      have hgd : DifferentiableAt ℝ (fun u => gaussDdim u v) w.1 := by
        have h := HasDerivAt.fun_finsetProd
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => heatKernel1D_hasDerivAt_t w.1 (v i) hτ)
        simpa only [gaussDdim] using h.differentiableAt
      have hg : HasDerivAt (fun u => gaussDdim u v)
          ((∑ i, ((v i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) * gaussDdim w.1 v) w.1 := by
        have h0 := hgd.hasDerivAt
        rwa [hgauss_deriv_eq] at h0
      rw [hfe]
      exact (hg.mul hamp).deriv
    · -- ON FULL GATE, τ ≤ 0: both sides `0`.
      rw [not_lt] at hτ
      have hzero_le : ∀ u : ℝ, u ≤ 0 →
          vanVleckGatedWitnessWith g gi hC hK S a b W u w.2.1 w.2.2 = 0 := by
        intro u hu
        rw [vanVleckGatedWitnessWith_gate_apply g gi hC hK S a b W u hzK hpS,
            gaussDdim_eq_zero_of_nonpos hn u (W w.2.2 w.2.1) hu]
        ring
      have hDW : HasDerivWithinAt
          (fun u => vanVleckGatedWitnessWith g gi hC hK S a b W u w.2.1 w.2.2) 0 (Set.Iic w.1) w.1 := by
        refine (hasDerivAt_const w.1 (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
        · exact eventuallyEq_of_mem self_mem_nhdsWithin
            (fun u hu => hzero_le u (le_trans (Set.mem_Iic.mp hu) hτ))
        · exact hzero_le w.1 hτ
      have hderiv0 :
          deriv (fun u => vanVleckGatedWitnessWith g gi hC hK S a b W u w.2.1 w.2.2) w.1 = 0 :=
        hDW.deriv_eq_zero (uniqueDiffWithinAt_Iic w.1)
      rw [hderiv0, hvdef, gaussDdim_eq_zero_of_nonpos hn w.1 (W w.2.2 w.2.1) hτ]
      ring
  · -- OFF the FULL gate: the `u`-function is identically `0`.
    rw [Set.indicator_of_notMem
      (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from hzKS)]
    have hzero : (fun u => vanVleckGatedWitnessWith g gi hC hK S a b W u w.2.1 w.2.2)
        = (fun _ => (0 : ℝ)) := by
      funext u
      unfold vanVleckGatedWitnessWith
      exact gatedKernel_apply_of_notMem K S _ u w.2.1 w.2.2 (not_and_or.mp hzKS)
    rw [hzero]
    simp

/-- **`witnessTauDeriv_eq_gatedTauRepProdSWith_recovers_old`** — the compatibility bridge:
    instantiating the generic identity at `W := uniformInverseChart g gi hC hK` recovers the OLD
    theorem's exact statement (`hgate`/conclusion both about `chartFieldAmp`/`vanVleckGatedWitness`/
    `gatedTauRepProdS`, via the `rfl` bridges of the underlying defs). NOT `a₁ = R/6`. -/
theorem witnessTauDeriv_eq_gatedTauRepProdSWith_recovers_old (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1) :
    ∀ w : ℝ × Point n × Point n,
      deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1
        = gatedTauRepProdS g gi hC hK S a b Cfield w := by
  exact witnessTauDeriv_eq_gatedTauRepProdSWith hn g gi hC hK S a b Cfield
    (uniformInverseChart g gi hC hK) hgate

/-! ###############################################################################
    ### ★★★ THE PRIMED IDENTITY — `witnessTauDeriv_eq_gatedTauRepProdS'`.
    ############################################################################### -/

/-- **★★★ `witnessTauDeriv_eq_gatedTauRepProdS'`.**  Instantiating the generic identity at
    `W := uniformInverseChart' g gi hC hK c`: the FIRST genuine relational τ-derivative identity
    connecting the PRIMED witness `vanVleckGatedWitness'` to `chartFieldAmp'` — closes with NO extra
    machinery beyond the caller-supplied `hgate`. NOT `a₁ = R/6`. -/
theorem witnessTauDeriv_eq_gatedTauRepProdS' (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (c : ℝ)
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        HasDerivAt (fun u : ℝ => chartFieldAmp' g gi hC hK a b c u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1) :
    ∀ w : ℝ × Point n × Point n,
      deriv (fun u => vanVleckGatedWitness' g gi hC hK S a b c u w.2.1 w.2.2) w.1
        = gatedTauRepProdSGen' g gi hC hK S a b Cfield c w := by
  unfold vanVleckGatedWitness' gatedTauRepProdSGen'
  exact witnessTauDeriv_eq_gatedTauRepProdSWith hn g gi hC hK S a b Cfield
    (uniformInverseChart' g gi hC hK c) hgate

/-! ###############################################################################
    ### The strongly-measurable capstone — generic and primed.
    ############################################################################### -/

/-- **`tauDeriv_prod_stronglyMeasurable_v4With`.**  Chart-generic sibling of
    `HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4`: over an ABSTRACT `W` + `hWmeas` (pulled OUT of
    the `hcar` existential, mirroring how `gatedTauRepProdSWith_measurable` generalized
    `gatedTauRepProdS_measurable`'s `hChartMeas`). NOT `a₁ = R/6`. -/
theorem tauDeriv_prod_stronglyMeasurable_v4With (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (W : Point n → Point n → Point n)
    (hWmeas : Measurable (fun w : ℝ × Point n × Point n => W w.2.2 w.2.1))
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmpWith g gi hC hK a b W w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmpWith g gi hC hK a b W u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      deriv (fun u => vanVleckGatedWitnessWith g gi hC hK S a b W u w.2.1 w.2.2) w.1) := by
  obtain ⟨Cfield, hAmpMeas, hCmeas, hgate⟩ := hcar
  have hrw : (fun w : ℝ × Point n × Point n =>
        deriv (fun u => vanVleckGatedWitnessWith g gi hC hK S a b W u w.2.1 w.2.2) w.1)
      = gatedTauRepProdSGenWith g gi hC hK S a b Cfield W := by
    funext w
    exact witnessTauDeriv_eq_gatedTauRepProdSWith hn g gi hC hK S a b Cfield W hgate w
  rw [hrw]
  exact (gatedTauRepProdSGenWith_measurable g gi hC hK S a b Cfield W hKSmeas hWmeas hAmpMeas
    hCmeas).stronglyMeasurable

/-- **★★★ `tauDeriv_prod_stronglyMeasurable_v4'`.**  The PRIMED instantiation: chart joint-measurability
    `hWmeas` fully DISCHARGED via `uniformInverseChart'_joint_measurable` (J4-1147) — no free chart-
    measurability hypothesis remains.  The genuinely amplitude-analytic hypotheses (about
    `chartFieldAmp'`, per tube radius `c`) remain as caller-supplied inputs, since they are NOT
    chart-measurability facts.  This is the τ-carrier leg of the honest v4 fix, fully genericized and
    primed. NOT `a₁ = R/6`. -/
theorem tauDeriv_prod_stronglyMeasurable_v4' (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∀ c : ℝ, 0 < c → ∃ Cfield : Point n → Point n → ℝ,
        Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp' g gi hC hK a b c w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp' g gi hC hK a b c u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        deriv (fun u => vanVleckGatedWitness' g gi hC hK S a b c u w.2.1 w.2.2) w.1) := by
  obtain ⟨δ₀, hδ₀, hmeas⟩ := uniformInverseChart'_joint_measurable g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  obtain ⟨Cfield, hAmpMeas, hCmeas, hgate⟩ := hcar c hc0
  unfold vanVleckGatedWitness'
  have hrw : (fun w : ℝ × Point n × Point n =>
        deriv (fun u =>
          vanVleckGatedWitnessWith g gi hC hK S a b (uniformInverseChart' g gi hC hK c) u
            w.2.1 w.2.2) w.1)
      = gatedTauRepProdSGenWith g gi hC hK S a b Cfield (uniformInverseChart' g gi hC hK c) := by
    funext w
    exact witnessTauDeriv_eq_gatedTauRepProdSWith hn g gi hC hK S a b Cfield
      (uniformInverseChart' g gi hC hK c) hgate w
  rw [hrw]
  exact (gatedTauRepProdSGenWith_measurable g gi hC hK S a b Cfield
    (uniformInverseChart' g gi hC hK c) hKSmeas (hmeas c hc0 hcδ) hAmpMeas
    hCmeas).stronglyMeasurable

end QIQTH.HgateSatAudit

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HgateSatAudit
#print axioms gatedTauRepProdSGenWith_uniformInverseChart
#print axioms gatedTauRepProdSGenWith_measurable
#print axioms gatedTauRepProdSGen'_measurable
#print axioms witnessTauDeriv_eq_gatedTauRepProdSWith
#print axioms witnessTauDeriv_eq_gatedTauRepProdSWith_recovers_old
#print axioms witnessTauDeriv_eq_gatedTauRepProdS'
#print axioms tauDeriv_prod_stronglyMeasurable_v4With
#print axioms tauDeriv_prod_stronglyMeasurable_v4'
end AxiomChecks
