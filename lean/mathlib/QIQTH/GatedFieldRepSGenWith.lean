/-
  GatedFieldRepSGenWith — J4-1162: dispatch 14 of the chart-parametric rebuild campaign, Phase 4 Task B
  continuation — genericizes `GatedRepSFix.gatedDerivRepProdS` §A (the FIRST field-`pd` v4 carrier) over
  an abstract chart `W`, per `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS PATH, NOT THE "FIELD/FIELD² PROSE-ONLY §3" PATH.

  J4-1161's own forward note framed the next step as a choice between (a) formalizing the field/field²
  v4 carriers described as "prose-only" in `HgateSatAudit.lean` §3, or (b) checking whether a τ-only
  entry point already exists in `GatedRepSFix.lean`/`HEmeasBorelAudit.lean`.  DIRECT RE-READ of
  `GatedRepSFix.lean` in full (J4-232, predates this rebuild campaign) shows J4-1161's premise was
  STALE: the field/field² v4 honest-fix carriers are **NOT** prose-only — they were ALREADY FULLY
  FORMALIZED for the OLD chart in `GatedRepSFix.lean` §A/§B/§C
  (`gatedDerivRepProdS`/`gatedDerivRepProdS_measurable`/`witnessFieldDeriv_eq_gatedDerivRepProdS`/
  `firstFieldPd_prod_stronglyMeasurable_v4`, and the mixed-second-derivative analogues, culminating in
  `tripleHEmeas_concrete_v4` — an `HEmeasBorelAudit`-level S1 result).  `HgateSatAudit.lean`'s own §3 is
  simply out of date relative to `GatedRepSFix.lean` (a LATER file, J4-232 vs J4-231, that already
  executed the plan §3 sketched).  So the CHEAPER path is (b): genericize `GatedRepSFix.lean`'s ALREADY
  PROVEN §A content the same mechanical way the τ carrier was genericized in `WitnessTauDerivEqWith.lean`
  (J4-1161) — NOT re-derive field/field² math from scratch.

  Precedent for the "amplitude term must be genuinely `chartFieldAmpWith … W`, not the hardwired
  `chartFieldAmp`" requirement (J4-1161's own obstruction) applies here too: `GatedRepSFix`'s
  `gatedDerivRepProdS` calls `chartFieldAmp`/`pd (chartFieldAmp …)` directly, so this file builds its
  OWN fully chart-generic representative `gatedDerivRepProdSGenWith` (amplitude terms via
  `chartFieldAmpWith … W`), exactly mirroring `WitnessTauDerivEqWith.gatedTauRepProdSGenWith`.
  `GatedRepSFix.lean` is left completely UNTOUCHED (never edited); its `gatedDerivRepProdS` /
  `gatedDerivRepProdS_measurable` / `witnessFieldDeriv_eq_gatedDerivRepProdS` /
  `firstFieldPd_prod_stronglyMeasurable_v4` / `tripleHEmeas_concrete_v4` remain exactly as banked.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `gatedDerivRepProdSGenWith` — the FULLY chart-generic first field-`pd` representative (Gaussian
      argument AND both amplitude terms at abstract `W`, via `chartFieldAmpWith`).
    * `gatedDerivRepProdSGenWith_uniformInverseChart` — `rfl` bridge to the OLD `GatedRepSFix.gatedDerivRepProdS`.
    * `gatedDerivRepProdSGen'` — the PRIMED instance at `uniformInverseChart' g gi hC hK c`.
    * `gatedDerivRepProdSGenWith_measurable` / `gatedDerivRepProdSGen'_measurable` — the generic-`W`+`hWmeas`
      and primed (chart-measurability DISCHARGED via `uniformInverseChart'_joint_measurable`)
      measurability siblings.
    * `witnessFieldDerivWith_eq_zero_of_nonpos` — the GENERIC sibling of
      `GatedDInstantiation.witnessFieldDeriv_eq_zero_of_nonpos`: threading `W` through
      `vanVleckGatedWitnessWith` instead of the concrete `vanVleckGatedWitness`.  Mechanical
      substitution (the underlying `heatParametrix_eq_zero_of_nonpos` fact never depended on the chart
      argument in the OLD proof either — it was already passed as an opaque `_`).
    * ★★ `witnessFieldDerivWith_eq_gatedDerivRepProdSWith` — the GENERIC sibling of
      `GatedRepSFix.witnessFieldDeriv_eq_gatedDerivRepProdS`: chart-generic `hgate` (about
      `chartFieldAmpWith … W`), chart-generic `hOffS`, RHS `gatedDerivRepProdSGenWith`.  Proof mirrors
      the old one verbatim, leaning on `WitnessFieldDerivConsumersWith.witnessFieldDerivWith_gate_eq`
      (J4-1158), `witnessFieldDerivWith_offGate_eq_zero` (J4-1158), and
      `witnessFieldDerivWith_eq_zero_of_nonpos` (this file) — all already chart-generic.
    * `witnessFieldDerivWith_eq_gatedDerivRepProdSWith_recovers_old` — compatibility bridge recovering
      the OLD theorem's exact statement at `W := uniformInverseChart g gi hC hK`.
    * ★★★ `witnessFieldDeriv_eq_gatedDerivRepProdS'` — the PRIMED instantiation: the first genuine
      relational field-derivative identity connecting `witnessFieldDeriv'`/`vanVleckGatedWitness'` to
      `chartFieldAmp'`, closing with NO extra machinery beyond the caller-supplied `hgate`/`hOffS`.
    * `firstFieldPd_prod_stronglyMeasurable_v4With` — generic sibling of
      `GatedRepSFix.firstFieldPd_prod_stronglyMeasurable_v4`, over abstract `W` + `hWmeas` (pulled OUT
      of the `hcar` existential, mirroring `WitnessTauDerivEqWith.tauDeriv_prod_stronglyMeasurable_v4With`).
    * ★★★ `firstFieldPd_prod_stronglyMeasurable_v4'` — the PRIMED instantiation: `hWmeas` fully
      DISCHARGED via `uniformInverseChart'_joint_measurable` — no free chart-measurability hypothesis
      remains; the genuinely amplitude-analytic hypotheses (about `chartFieldAmp'`, per tube radius `c`)
      remain as caller-supplied inputs.

  ## CANARY C3 ASSESSMENT — HONEST, NOT OVERCLAIMED.
  This closes the FIRST field-`pd` (conjunct (2) of the `HEmeasBorelAudit` triple) leg of Phase 4 Task B
  in a chart-generic + primed form, extending J4-1161's τ-carrier (conjunct (1)) leg.  Conjunct (3) (the
  mixed second field-`pd`, `GatedRepSFix` §B) and the assembled `tripleHEmeas_concrete_v4`-analogue
  (`GatedRepSFix` §C) are STILL NOT genericized — Canary C3 ("PrimeHEmeasAudit": a complete primed
  `HEmeasBorelAudit`-level triple result with no raw `hWmeas`) is NOT YET REACHED.  This dispatch is a
  further STEP TOWARD C3 (2 of 3 conjuncts now chart-generic + primed), not C3 itself.  Next dispatch
  target: genericize `GatedRepSFix` §B (`gatedMixed2RepProdS`/`witnessMixed2_eq_gatedMixed2RepProdS`/
  `secondFieldPd_prod_stronglyMeasurable_v4`) the identical way, THEN assemble the generic + primed
  triple (`tripleHEmeas_concrete_v4With`/`_v4'`) via `HEmeasBorelAudit.tripleHEmeas_of_surface` — that
  assembly step IS Canary C3 once all three conjuncts are primed.

  ## WHAT THIS DOES NOT DO.
  Does NOT touch `GatedRepSFix.lean`, `HgateSatAudit.lean`, `HEmeasBorelAudit.lean`, or any `*With.lean`
  file (all left completely unedited).  Does NOT genericize the mixed second field-`pd` carrier (§B) or
  assemble the triple (§C) — next dispatch.  Does NOT claim `gatedDerivRepProdSGen' =
  gatedDerivRepProdS` or any cross-representative identity beyond the shared `rfl` value at the OLD
  chart.

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.GatedRepSFix
import QIQTH.WitnessFieldDerivConsumersWith

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ThetaMeasurableEmbedding
open scoped Topology BigOperators ContDiff

namespace QIQTH.GatedRepSFix

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The FULLY chart-generic first field-`pd` representative — `gatedDerivRepProdSGenWith`.
    ############################################################################### -/

/-- **`gatedDerivRepProdSGenWith`.**  The FULLY chart-generic sibling of `gatedDerivRepProdS`: both
    Gaussian-argument slots AND both amplitude terms are at the abstract `W`
    (`chartFieldAmpWith … W`, NOT the hardwired `chartFieldAmp`).  See the header for why this
    supplements — rather than reuses — `GatedRepSFix.gatedDerivRepProdS`.  NOT `a₁ = R/6`. -/
noncomputable def gatedDerivRepProdSGenWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ) (W : Point n → Point n → Point n) :
    ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
    (fun w : ℝ × Point n × Point n =>
      gaussDdim w.1 (W w.2.2 w.2.1)
          * (-(∑ j, W w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) / (2 * w.1))
          * chartFieldAmpWith g gi hC hK a b W w.1 w.2.2 w.2.1
        + gaussDdim w.1 (W w.2.2 w.2.1)
          * pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) k w.2.1)

/-- **`gatedDerivRepProdSGenWith_uniformInverseChart`** — the `rfl` compatibility bridge to the OLD
    `GatedRepSFix.gatedDerivRepProdS` (valid because `chartFieldAmpWith … (uniformInverseChart …) =
    chartFieldAmp …` is itself `rfl`). -/
theorem gatedDerivRepProdSGenWith_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ) :
    gatedDerivRepProdSGenWith g gi hC hK S a b k Pfield (uniformInverseChart g gi hC hK)
      = gatedDerivRepProdS g gi hC hK S a b k Pfield := rfl

/-- **`gatedDerivRepProdSGen'`** — the PRIMED instance at `uniformInverseChart' g gi hC hK c`. -/
noncomputable def gatedDerivRepProdSGen' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ) (c : ℝ) : ℝ × Point n × Point n → ℝ :=
  gatedDerivRepProdSGenWith g gi hC hK S a b k Pfield (uniformInverseChart' g gi hC hK c)

/-! ###############################################################################
    ### Measurability — generic-`W` and primed (chart-measurability discharged) siblings.
    ############################################################################### -/

/-- **`gatedDerivRepProdSGenWith_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the FULLY
    generic first field-`pd` representative, from `hKSmeas`, an ABSTRACT `hWmeas`, and the
    amplitude/derivative measurabilities (about `chartFieldAmpWith … W`, matching the representative's
    own amplitude terms). NOT `a₁ = R/6`. -/
theorem gatedDerivRepProdSGenWith_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ) (W : Point n → Point n → Point n)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hWmeas : Measurable (fun w : ℝ × Point n × Point n => W w.2.2 w.2.1))
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmpWith g gi hC hK a b W w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) k w.2.1)) :
    Measurable (gatedDerivRepProdSGenWith g gi hC hK S a b k Pfield W) := by
  unfold gatedDerivRepProdSGenWith
  have hG : Measurable
      (fun w : ℝ × Point n × Point n => gaussDdim w.1 (W w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hWmeas)
  have hSum : Measurable
      (fun w : ℝ × Point n × Point n => ∑ j, W w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp hWmeas).mul (hPmeas j)
  have hSc : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ j, W w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) / (2 * w.1)) :=
    hSum.neg.div (measurable_const.mul measurable_fst)
  exact (((hG.mul hSc).mul hAmpMeas).add (hG.mul hAmpDerivMeas)).indicator hKSmeas

/-- **★★ `gatedDerivRepProdSGen'_measurable`.**  The primed measurability audit for the FULLY generic
    first field-`pd` representative: chart joint-measurability DISCHARGED via
    `uniformInverseChart'_joint_measurable` (J4-1147). NOT `a₁ = R/6`. -/
theorem gatedDerivRepProdSGen'_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hAmpMeas : ∀ c : ℝ, Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp' g gi hC hK a b c w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : ∀ c : ℝ, Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) k w.2.1)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      Measurable (gatedDerivRepProdSGen' g gi hC hK S a b k Pfield c) := by
  obtain ⟨δ₀, hδ₀, hmeas⟩ := uniformInverseChart'_joint_measurable g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  unfold gatedDerivRepProdSGen'
  exact gatedDerivRepProdSGenWith_measurable g gi hC hK S a b k Pfield
    (uniformInverseChart' g gi hC hK c) hKSmeas (hmeas c hc0 hcδ) hPmeas (hAmpMeas c) (hAmpDerivMeas c)

/-! ###############################################################################
    ### The chart-generic nonpositive-`τ` vanishing — `witnessFieldDerivWith_eq_zero_of_nonpos`.
    ############################################################################### -/

/-- **`witnessFieldDerivWith_eq_zero_of_nonpos`.**  Chart-generic sibling of
    `GatedDInstantiation.witnessFieldDeriv_eq_zero_of_nonpos`: for `τ ≤ 0` (and `0 < n`) the generic
    gated witness slot is identically `0` (the `heatParametrix` factor vanishes regardless of the chart
    argument — the OLD proof already passed it as an opaque `_`), so its field `pd` — the first
    field-derivative kernel — is `0`.  NOT `a₁ = R/6`. -/
theorem witnessFieldDerivWith_eq_zero_of_nonpos (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (W : Point n → Point n → Point n) (hτ : τ ≤ 0) :
    witnessFieldDerivWith g gi hC hK S a b i τ p z W = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z = 0 := by
    intro x'
    have hH : globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b W τ x' z = 0 := by
      unfold globalCutoffParametrixWitnessN
      rw [heatParametrix_eq_zero_of_nonpos hn 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) τ _ hτ, mul_zero]
    rw [vanVleckGatedWitnessWith]
    by_cases hz : z ∈ K
    · by_cases hx : x' ∈ S z
      · rw [gatedKernel_apply_of_mem K S _ τ hz hx]; exact hH
      · exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inr hx)
    · exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  unfold witnessFieldDerivWith
  simp only [hzero]
  exact pd_const 0 i p

/-! ###############################################################################
    ### ★★ THE GENERIC DERIVATIVE IDENTITY — `witnessFieldDerivWith_eq_gatedDerivRepProdSWith`.
    ############################################################################### -/

/-- **★★ `witnessFieldDerivWith_eq_gatedDerivRepProdSWith` — the GENERIC FIELD EVERYWHERE IDENTITY.**
    Chart-generic sibling of `GatedRepSFix.witnessFieldDeriv_eq_gatedDerivRepProdS`, at an ABSTRACT `W`.
    Proof mirrors the old one EXACTLY (mechanical `W`-for-`uniformInverseChart` substitution): the three
    ingredients it leans on — `WitnessFieldDerivConsumersWith.witnessFieldDerivWith_gate_eq` (J4-1158),
    `witnessFieldDerivWith_offGate_eq_zero` (J4-1158), and `witnessFieldDerivWith_eq_zero_of_nonpos`
    (this file) — were ALREADY (or are now) chart-generic. NOT `a₁ = R/6`. -/
theorem witnessFieldDerivWith_eq_gatedDerivRepProdSWith (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (Pfield : Point n → Point n → Fin n → ℝ) (W : Point n → Point n → Point n)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => W w.2.2 (Function.update w.2.1 k s) j)
          (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
        PdiffAt (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) k w.2.1)
    (hOffS : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        witnessFieldDerivWith g gi hC hK S a b k w.1 w.2.1 w.2.2 W = 0) :
    ∀ w : ℝ × Point n × Point n,
      witnessFieldDerivWith g gi hC hK S a b k w.1 w.2.1 w.2.2 W
        = gatedDerivRepProdSGenWith g gi hC hK S a b k Pfield W w := by
  intro w
  simp only [gatedDerivRepProdSGenWith]
  by_cases hzKS : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
  · obtain ⟨hzK, hpS⟩ := hzKS
    rw [Set.indicator_of_mem
      (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from ⟨hzK, hpS⟩)]
    by_cases hτ : 0 < w.1
    · obtain ⟨hSopen, hjet, hamp⟩ := hgate w hzK hτ hpS
      exact witnessFieldDerivWith_gate_eq g gi hC hK S a b k w.1 hτ W w.2.2 hzK hSopen w.2.1 hpS
        (Pfield w.2.2 w.2.1) hjet hamp
    · rw [not_lt] at hτ
      rw [witnessFieldDerivWith_eq_zero_of_nonpos hn g gi hC hK S a b k
            w.1 w.2.1 w.2.2 W hτ,
          gaussDdim_eq_zero_of_nonpos hn w.1 (W w.2.2 w.2.1) hτ]
      ring
  · rw [Set.indicator_of_notMem
      (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from hzKS)]
    by_cases hzK : w.2.2 ∈ K
    · have hpS : w.2.1 ∉ S w.2.2 := fun h => hzKS ⟨hzK, h⟩
      by_cases hτ : 0 < w.1
      · exact hOffS w hzK hτ hpS
      · rw [not_lt] at hτ
        exact witnessFieldDerivWith_eq_zero_of_nonpos hn g gi hC hK S a b k
          w.1 w.2.1 w.2.2 W hτ
    · exact witnessFieldDerivWith_offGate_eq_zero g gi hC hK S a b k w.1 w.2.1 w.2.2 W hzK

/-- **`witnessFieldDerivWith_eq_gatedDerivRepProdSWith_recovers_old`** — the compatibility bridge:
    instantiating the generic identity at `W := uniformInverseChart g gi hC hK` recovers the OLD
    theorem's exact statement. NOT `a₁ = R/6`. -/
theorem witnessFieldDerivWith_eq_gatedDerivRepProdSWith_recovers_old (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (Pfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
          (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
    (hOffS : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0) :
    ∀ w : ℝ × Point n × Point n,
      witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2
        = gatedDerivRepProdS g gi hC hK S a b k Pfield w := by
  exact witnessFieldDerivWith_eq_gatedDerivRepProdSWith hn g gi hC hK S a b k Pfield
    (uniformInverseChart g gi hC hK) hgate hOffS

/-! ###############################################################################
    ### ★★★ THE PRIMED IDENTITY — `witnessFieldDeriv_eq_gatedDerivRepProdS'`.
    ############################################################################### -/

/-- **★★★ `witnessFieldDeriv_eq_gatedDerivRepProdS'`.**  Instantiating the generic identity at
    `W := uniformInverseChart' g gi hC hK c`: the FIRST genuine relational field-derivative identity
    connecting `witnessFieldDeriv'`/`vanVleckGatedWitness'` to `chartFieldAmp'` — closes with NO extra
    machinery beyond the caller-supplied `hgate`/`hOffS`. NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_eq_gatedDerivRepProdS' (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c : ℝ)
    (k : Fin n) (Pfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => uniformInverseChart' g gi hC hK c w.2.2 (Function.update w.2.1 k s) j)
          (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
        PdiffAt (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) k w.2.1)
    (hOffS : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        witnessFieldDeriv' g gi hC hK S a b c k w.1 w.2.1 w.2.2 = 0) :
    ∀ w : ℝ × Point n × Point n,
      witnessFieldDeriv' g gi hC hK S a b c k w.1 w.2.1 w.2.2
        = gatedDerivRepProdSGen' g gi hC hK S a b k Pfield c w := by
  unfold witnessFieldDeriv' gatedDerivRepProdSGen'
  exact witnessFieldDerivWith_eq_gatedDerivRepProdSWith hn g gi hC hK S a b k Pfield
    (uniformInverseChart' g gi hC hK c) hgate hOffS

/-! ###############################################################################
    ### The strongly-measurable capstone — generic and primed.
    ############################################################################### -/

/-- **`firstFieldPd_prod_stronglyMeasurable_v4With`.**  Chart-generic sibling of
    `GatedRepSFix.firstFieldPd_prod_stronglyMeasurable_v4`: over an ABSTRACT `W` + `hWmeas` (pulled OUT
    of the `hcar` existential). NOT `a₁ = R/6`. -/
theorem firstFieldPd_prod_stronglyMeasurable_v4With (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (W : Point n → Point n → Point n)
    (hWmeas : Measurable (fun w : ℝ × Point n × Point n => W w.2.2 w.2.1))
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmpWith g gi hC hK a b W w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => W w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDerivWith g gi hC hK S a b k w.1 w.2.1 w.2.2 W = 0)) :
    ∀ k : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun x => vanVleckGatedWitnessWith g gi hC hK S a b W w.1 x w.2.2) k w.2.1) := by
  intro k
  obtain ⟨Pfield, hPmeas, hAmpMeas, hAmpDerivMeas, hgate, hOffS⟩ := hcar k
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun x => vanVleckGatedWitnessWith g gi hC hK S a b W w.1 x w.2.2) k w.2.1)
      = gatedDerivRepProdSGenWith g gi hC hK S a b k Pfield W := by
    funext w
    show witnessFieldDerivWith g gi hC hK S a b k w.1 w.2.1 w.2.2 W = _
    exact witnessFieldDerivWith_eq_gatedDerivRepProdSWith hn g gi hC hK S a b k Pfield W hgate hOffS w
  rw [hrw]
  exact (gatedDerivRepProdSGenWith_measurable g gi hC hK S a b k Pfield W hKSmeas hWmeas hPmeas
    hAmpMeas hAmpDerivMeas).stronglyMeasurable

/-- **★★★ `firstFieldPd_prod_stronglyMeasurable_v4'`.**  The PRIMED instantiation: chart
    joint-measurability `hWmeas` fully DISCHARGED via `uniformInverseChart'_joint_measurable` (J4-1147)
    — no free chart-measurability hypothesis remains.  The genuinely amplitude-analytic hypotheses
    (about `chartFieldAmp'`, per tube radius `c`) remain as caller-supplied inputs. NOT `a₁ = R/6`. -/
theorem firstFieldPd_prod_stronglyMeasurable_v4' (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∀ c : ℝ, 0 < c → ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp' g gi hC hK a b c w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart' g gi hC hK c w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDeriv' g gi hC hK S a b c k w.1 w.2.1 w.2.2 = 0)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ k : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        pd (fun x => vanVleckGatedWitness' g gi hC hK S a b c w.1 x w.2.2) k w.2.1) := by
  obtain ⟨δ₀, hδ₀, hmeas⟩ := uniformInverseChart'_joint_measurable g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ k
  obtain ⟨Pfield, hPmeas, hAmpMeas, hAmpDerivMeas, hgate, hOffS⟩ := hcar c hc0 k
  unfold vanVleckGatedWitness'
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun x =>
          vanVleckGatedWitnessWith g gi hC hK S a b (uniformInverseChart' g gi hC hK c) w.1 x w.2.2)
          k w.2.1)
      = gatedDerivRepProdSGenWith g gi hC hK S a b k Pfield (uniformInverseChart' g gi hC hK c) := by
    funext w
    show witnessFieldDerivWith g gi hC hK S a b k w.1 w.2.1 w.2.2
        (uniformInverseChart' g gi hC hK c) = _
    exact witnessFieldDerivWith_eq_gatedDerivRepProdSWith hn g gi hC hK S a b k Pfield
      (uniformInverseChart' g gi hC hK c) hgate hOffS w
  rw [hrw]
  exact (gatedDerivRepProdSGenWith_measurable g gi hC hK S a b k Pfield
    (uniformInverseChart' g gi hC hK c) hKSmeas (hmeas c hc0 hcδ) hPmeas
    hAmpMeas hAmpDerivMeas).stronglyMeasurable

end QIQTH.GatedRepSFix

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GatedRepSFix
#print axioms gatedDerivRepProdSGenWith_uniformInverseChart
#print axioms gatedDerivRepProdSGenWith_measurable
#print axioms gatedDerivRepProdSGen'_measurable
#print axioms witnessFieldDerivWith_eq_zero_of_nonpos
#print axioms witnessFieldDerivWith_eq_gatedDerivRepProdSWith
#print axioms witnessFieldDerivWith_eq_gatedDerivRepProdSWith_recovers_old
#print axioms witnessFieldDeriv_eq_gatedDerivRepProdS'
#print axioms firstFieldPd_prod_stronglyMeasurable_v4With
#print axioms firstFieldPd_prod_stronglyMeasurable_v4'
end AxiomChecks
