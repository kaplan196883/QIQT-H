/-
  GatedMixed2RepSGenWith — J4-1163: dispatch 15 of the chart-parametric rebuild campaign, Phase 4 Task B
  continuation — genericizes `GatedRepSFix.gatedMixed2RepProdS` §B (the MIXED second field-`pd` v4
  carrier) over an abstract chart `W`, per `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS IS THE THIRD (LAST) CONJUNCT NEEDED FOR CANARY C3.

  J4-1161 (`WitnessTauDerivEqWith.lean`) genericized + primed conjunct (1) (`∂_τ`, the τ-carrier).
  J4-1162 (`GatedFieldRepSGenWith.lean`) genericized + primed conjunct (2) (the first field-`pd`
  carrier, `GatedRepSFix` §A).  This dispatch genericizes + primes conjunct (3) (the MIXED second
  field-`pd` carrier, `GatedRepSFix` §B: `gatedMixed2RepProdS` / `gatedMixed2RepProdS_measurable` /
  `witnessMixed2_eq_gatedMixed2RepProdS` / `secondFieldPd_prod_stronglyMeasurable_v4`) the IDENTICAL
  mechanical way — building a NEW, fully chart-generic representative `gatedMixed2RepProdSGenWith`
  (amplitude terms via `chartFieldAmpWith … W`, not the hardwired `chartFieldAmp`, per J4-1161's own
  precedent/obstruction for why the hardwired amplitude cannot be reused for a genuine derivative
  identity).  `GatedRepSFix.lean` is left completely UNTOUCHED (never edited).

  The prerequisite chart-generic layer this needs — `witnessMixed_gate_eq` / `witnessMixed_offGate_eq_zero`
  / `witnessMixed_eq_zero_of_nonpos` (`ChartJetHessianMixed.lean`) — did NOT already exist in generic
  form (unlike J4-1158's `witnessFieldDeriv_gate_eq`, genericized earlier as
  `witnessFieldDerivWith_gate_eq`).  DIRECT RE-READ of `ChartJetHessianMixed.lean` confirms the
  underlying mixed Leibniz–Gaussian normal forms it leans on — `gaussComp_pd_pd_mixed` and
  `gaussComp_amp_pd_pd_mixed` (§A of that file) — are ALREADY fully chart-generic (abstract `V : Point n
  → Point n`, `A : Point n → ℝ`, no `uniformInverseChart`/`chartFieldAmp` reference in their own bodies),
  exactly like the diagonal case's ingredients were for J4-1158.  So genericizing `witnessMixed_gate_eq`
  itself (§B of `ChartJetHessianMixed.lean`) is the SAME mechanical `W`-for-`uniformInverseChart`,
  `chartFieldAmpWith … W`-for-`chartFieldAmp` substitution — built here as `witnessMixedWith_gate_eq`
  (this file supplies BOTH the missing generic derivative-identity layer AND the representative/
  measurability layer in one dispatch, since the former was a genuine prerequisite gap, not previously
  identified as its own separate step).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `witnessMixedWith_gate_eq` — chart-generic sibling of `ChartJetHessianMixed.witnessMixed_gate_eq`
      (the on-gate mixed order-2 Leibniz–Gaussian formula), at abstract `W`.  Mechanical substitution:
      the two ingredients it leans on (`ChartJetHessianMixed.pd_pd_congr_at_mixed`,
      `ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed`) were ALREADY chart-generic;
      `vanVleckGatedWitnessWith_gate_apply` (J4-1158) supplies the generic on-gate exact value.
    * `witnessMixedWith_offGate_eq_zero` / `witnessMixedWith_eq_zero_of_nonpos` — chart-generic siblings
      of the off-gate / nonpositive-τ vanishing theorems (the gate machinery
      `gatedKernel_apply_of_notMem` is already chart-independent, transfers verbatim).
    * `gatedMixed2RepProdSGenWith` — the FULLY chart-generic mixed second field-`pd` representative
      (Gaussian argument AND all three amplitude terms at abstract `W`, via `chartFieldAmpWith`).
    * `gatedMixed2RepProdSGenWith_uniformInverseChart` — `rfl` bridge to the OLD
      `GatedRepSFix.gatedMixed2RepProdS`.
    * `gatedMixed2RepProdSGen'` — the PRIMED instance at `uniformInverseChart' g gi hC hK c`.
    * `gatedMixed2RepProdSGenWith_measurable` / `gatedMixed2RepProdSGen'_measurable` — the generic-`W`+
      `hWmeas` and primed (chart-measurability DISCHARGED via `uniformInverseChart'_joint_measurable`)
      measurability siblings.
    * ★★ `witnessMixedWith_eq_gatedMixed2RepProdSGenWith` — the GENERIC MIXED EVERYWHERE IDENTITY:
      chart-generic sibling of `GatedRepSFix.witnessMixed2_eq_gatedMixed2RepProdS`, mirroring the old
      proof verbatim.
    * `witnessMixedWith_eq_gatedMixed2RepProdSGenWith_recovers_old` — compatibility bridge recovering
      the OLD theorem's exact statement at `W := uniformInverseChart g gi hC hK`.
    * ★★★ `witnessMixed2_eq_gatedMixed2RepProdS'` — the PRIMED instantiation: the first genuine
      relational mixed-second-field-derivative identity connecting `vanVleckGatedWitness'` to
      `chartFieldAmp'`, closing with NO extra machinery beyond the caller-supplied `hgate`/`hOffS2`.
    * `secondFieldPd_prod_stronglyMeasurable_v4With` — generic sibling of
      `GatedRepSFix.secondFieldPd_prod_stronglyMeasurable_v4`, over abstract `W` + `hWmeas` (pulled OUT
      of the `hcar` existential).
    * ★★★ `secondFieldPd_prod_stronglyMeasurable_v4'` — the PRIMED instantiation: `hWmeas` fully
      DISCHARGED via `uniformInverseChart'_joint_measurable` — no free chart-measurability hypothesis
      remains; the genuinely amplitude-analytic hypotheses (about `chartFieldAmp'`, per tube radius `c`)
      remain as caller-supplied inputs.

  ## CANARY C3 ASSESSMENT — HONEST, NOT OVERCLAIMED.
  All THREE `HEmeasBorelAudit` conjuncts (τ / first field-`pd` / mixed second field-`pd`) are now
  chart-generic + primed.  Canary C3 ("PrimeHEmeasAudit": a complete primed `HEmeasBorelAudit`-level
  triple result with no raw `hWmeas`) requires ASSEMBLING these three primed conjuncts, plus the `gi`/
  `christoffel` measurabilities (already chart-independent, `hgi`/`hchr`), through
  `HEmeasBorelAudit.tripleHEmeas_of_surface` into a single primed `tripleHEmeas_concrete_v4'`-shaped
  capstone — the `BorelDischargeSurface` for `vanVleckGatedWitness'`.  THAT ASSEMBLY IS NOT ATTEMPTED IN
  THIS FILE (this file lands the three-conjunct prerequisite only); it is the immediate next-dispatch
  target and the genuine content of Canary C3 itself.

  ## WHAT THIS DOES NOT DO.
  Does NOT touch `GatedRepSFix.lean`, `ChartJetHessianMixed.lean`, `HgateSatAudit.lean`,
  `HEmeasBorelAudit.lean`, or any `*With.lean` file (all left completely unedited).  Does NOT assemble
  the triple (`tripleHEmeas_concrete_v4With`/`_v4'`) — that is Canary C3 itself, next dispatch.  Does NOT
  claim `gatedMixed2RepProdSGen' = gatedMixed2RepProdS` or any cross-representative identity beyond the
  shared `rfl` value at the OLD chart.

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.GatedRepSFix
import QIQTH.ChartJetHessianMixed
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
    ### The chart-generic mixed on-gate/off-gate/nonpos derivative-identity layer.
    ############################################################################### -/

/-- **`witnessMixedWith_gate_eq`.**  Chart-generic sibling of `ChartJetHessianMixed.witnessMixed_gate_eq`:
    on the OPEN gate, at the ABSTRACT chart `W`, the off-diagonal second field-`pd` of the generic gated
    witness equals the mixed Leibniz–Gaussian normal form.  Proof mirrors the old one EXACTLY (`W z`
    substituted for `uniformInverseChart g gi hC hK z`, `chartFieldAmpWith … W` for `chartFieldAmp`) —
    the two ingredients it leans on (`pd_pd_congr_at_mixed`, `gaussComp_amp_pd_pd_mixed`) were ALREADY
    chart-generic. NOT `a₁ = R/6`. -/
theorem witnessMixedWith_gate_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (W : Point n → Point n → Point n)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetVi : ∀ x k, HasDerivAt
      (fun s : ℝ => W z (Function.update x i s) k) (Pi x k) (x i))
    (hJetVj : ∀ x k, HasDerivAt
      (fun s : ℝ => W z (Function.update x j s) k) (Pj x k) (x j))
    (hJetQ : ∀ k, HasDerivAt
      (fun s : ℝ => Pj (Function.update p i s) k) (Q k) (p i))
    (hAmpj1 : ∀ x, PdiffAt (chartFieldAmpWith g gi hC hK a b W τ z) j x)
    (hAmpi1 : PdiffAt (chartFieldAmpWith g gi hC hK a b W τ z) i p)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmpWith g gi hC hK a b W τ z) j y) i p) :
    pd (fun y => pd (fun x' => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z) j y) i p
      = gaussDdim τ (W z p)
          * ((∑ k, W z p k * Pi p k) * (∑ k, W z p k * Pj p k) / (4 * τ ^ 2)
              - ((∑ k, Pi p k * Pj p k) + (∑ k, W z p k * Q k)) / (2 * τ))
          * chartFieldAmpWith g gi hC hK a b W τ z p
        + (gaussDdim τ (W z p)
              * (-(∑ k, W z p k * Pj p k) / (2 * τ)))
            * pd (chartFieldAmpWith g gi hC hK a b W τ z) i p
        + (gaussDdim τ (W z p)
              * (-(∑ k, W z p k * Pi p k) / (2 * τ)))
            * pd (chartFieldAmpWith g gi hC hK a b W τ z) j p
        + gaussDdim τ (W z p)
            * pd (fun y => pd (chartFieldAmpWith g gi hC hK a b W τ z) j y) i p := by
  have hev : (fun x' : Point n => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z)
      =ᶠ[𝓝 p]
      (fun x' : Point n => gaussDdim τ (W z x')
          * chartFieldAmpWith g gi hC hK a b W τ z x') := by
    refine eventually_nhds_iff.mpr ⟨S z, ?_, hSopen, hp⟩
    intro x' hx'
    show vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z
        = gaussDdim τ (W z x') * chartFieldAmpWith g gi hC hK a b W τ z x'
    rw [vanVleckGatedWitnessWith_gate_apply g gi hC hK S a b W τ hz hx']
    simp only [chartFieldAmpWith]
    ring
  rw [QIQTH.ChartJetHessianMixed.pd_pd_congr_at_mixed
        (fun x' => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z)
        (fun x' => gaussDdim τ (W z x') * chartFieldAmpWith g gi hC hK a b W τ z x') i j p hev,
      QIQTH.ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed (W z)
        (chartFieldAmpWith g gi hC hK a b W τ z) Pi Pj Q τ hτ i j p hJetVi hJetVj hJetQ
        hAmpj1 hAmpi1 hAmp2]

/-- **`witnessMixedWith_offGate_eq_zero`.**  Chart-generic sibling of
    `ChartJetHessianMixed.witnessMixed_offGate_eq_zero`. NOT `a₁ = R/6`. -/
theorem witnessMixedWith_offGate_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (p z : Point n) (W : Point n → Point n → Point n) (hz : z ∉ K) :
    pd (fun y => pd (fun x' => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z) j y) i p = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z = 0 := by
    intro x'
    unfold vanVleckGatedWitnessWith
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  have hin : (fun y : Point n =>
        pd (fun x' : Point n => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z) j y)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext y
    simp only [hzero]
    exact pd_const 0 j y
  rw [hin]
  exact pd_const 0 i p

/-- **`witnessMixedWith_eq_zero_of_nonpos`.**  Chart-generic sibling of
    `ChartJetHessianMixed.witnessMixed_eq_zero_of_nonpos`. NOT `a₁ = R/6`. -/
theorem witnessMixedWith_eq_zero_of_nonpos (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (p z : Point n) (W : Point n → Point n → Point n) (hτ : τ ≤ 0) :
    pd (fun y => pd (fun x' => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z) j y) i p = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z = 0 := by
    intro x'
    by_cases hpS : x' ∈ S z
    · by_cases hzK : z ∈ K
      · rw [vanVleckGatedWitnessWith_gate_apply g gi hC hK S a b W τ hzK hpS,
            gaussDdim_eq_zero_of_nonpos hn τ (W z x') hτ]
        ring
      · unfold vanVleckGatedWitnessWith
        exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hzK)
    · unfold vanVleckGatedWitnessWith
      exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inr hpS)
  have hin : (fun y : Point n =>
        pd (fun x' : Point n => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z) j y)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext y
    simp only [hzero]
    exact pd_const 0 j y
  rw [hin]
  exact pd_const 0 i p

/-! ###############################################################################
    ### The FULLY chart-generic mixed second field-`pd` representative — `gatedMixed2RepProdSGenWith`.
    ############################################################################### -/

/-- **`gatedMixed2RepProdSGenWith`.**  The FULLY chart-generic sibling of `gatedMixed2RepProdS`: the
    Gaussian-argument slots AND all three amplitude terms are at the abstract `W`
    (`chartFieldAmpWith … W`, NOT the hardwired `chartFieldAmp`). NOT `a₁ = R/6`. -/
noncomputable def gatedMixed2RepProdSGenWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ) (W : Point n → Point n → Point n) :
    ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
    (fun w : ℝ × Point n × Point n =>
      gaussDdim w.1 (W w.2.2 w.2.1)
          * ((∑ k, W w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k)
                * (∑ k, W w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                / (4 * w.1 ^ 2)
              - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                  + (∑ k, W w.2.2 w.2.1 k * Qfield w.2.2 w.2.1 k))
                / (2 * w.1))
          * chartFieldAmpWith g gi hC hK a b W w.1 w.2.2 w.2.1
        + (gaussDdim w.1 (W w.2.2 w.2.1)
              * (-(∑ k, W w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                  / (2 * w.1)))
            * pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) i w.2.1
        + (gaussDdim w.1 (W w.2.2 w.2.1)
              * (-(∑ k, W w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k)
                  / (2 * w.1)))
            * pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j w.2.1
        + gaussDdim w.1 (W w.2.2 w.2.1)
            * pd (fun y => pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j y) i w.2.1)

/-- **`gatedMixed2RepProdSGenWith_uniformInverseChart`** — the `rfl` compatibility bridge to the OLD
    `GatedRepSFix.gatedMixed2RepProdS`. -/
theorem gatedMixed2RepProdSGenWith_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ) :
    gatedMixed2RepProdSGenWith g gi hC hK S a b i j Pifield Pjfield Qfield
        (uniformInverseChart g gi hC hK)
      = gatedMixed2RepProdS g gi hC hK S a b i j Pifield Pjfield Qfield := rfl

/-- **`gatedMixed2RepProdSGen'`** — the PRIMED instance at `uniformInverseChart' g gi hC hK c`. -/
noncomputable def gatedMixed2RepProdSGen' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ) (c : ℝ) : ℝ × Point n × Point n → ℝ :=
  gatedMixed2RepProdSGenWith g gi hC hK S a b i j Pifield Pjfield Qfield
    (uniformInverseChart' g gi hC hK c)

/-! ###############################################################################
    ### Measurability — generic-`W` and primed (chart-measurability discharged) siblings.
    ############################################################################### -/

/-- **`gatedMixed2RepProdSGenWith_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the FULLY
    generic mixed second field-`pd` representative, from `hKSmeas`, an ABSTRACT `hWmeas`, and the
    amplitude/derivative measurabilities (about `chartFieldAmpWith … W`). NOT `a₁ = R/6`. -/
theorem gatedMixed2RepProdSGenWith_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ) (W : Point n → Point n → Point n)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hWmeas : Measurable (fun w : ℝ × Point n × Point n => W w.2.2 w.2.1))
    (hPimeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
    (hPjmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
    (hQmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmpWith g gi hC hK a b W w.1 w.2.2 w.2.1))
    (hAmpDerivIMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) i w.2.1))
    (hAmpDerivJMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j w.2.1))
    (hAmpDeriv2Meas : Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j y) i w.2.1)) :
    Measurable (gatedMixed2RepProdSGenWith g gi hC hK S a b i j Pifield Pjfield Qfield W) := by
  unfold gatedMixed2RepProdSGenWith
  have hG : Measurable
      (fun w : ℝ × Point n × Point n => gaussDdim w.1 (W w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hWmeas)
  have hVPi : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, W w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hWmeas).mul (hPimeas k)
  have hVPj : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, W w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hWmeas).mul (hPjmeas k)
  have hPiPj : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact (hPimeas k).mul (hPjmeas k)
  have hVQ : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, W w.2.2 w.2.1 k * Qfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hWmeas).mul (hQmeas k)
  have hden2 : Measurable (fun w : ℝ × Point n × Point n => 4 * w.1 ^ 2) :=
    measurable_const.mul (measurable_fst.pow_const 2)
  have hden1 : Measurable (fun w : ℝ × Point n × Point n => 2 * w.1) :=
    measurable_const.mul measurable_fst
  have hHess : Measurable
      (fun w : ℝ × Point n × Point n =>
        (∑ k, W w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k)
            * (∑ k, W w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
            / (4 * w.1 ^ 2)
          - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
              + (∑ k, W w.2.2 w.2.1 k * Qfield w.2.2 w.2.1 k))
            / (2 * w.1)) :=
    ((hVPi.mul hVPj).div hden2).sub ((hPiPj.add hVQ).div hden1)
  have hGradj : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ k, W w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPj.neg.div hden1
  have hGradi : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ k, W w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPi.neg.div hden1
  exact (((((hG.mul hHess).mul hAmpMeas).add
      ((hG.mul hGradj).mul hAmpDerivIMeas)).add
      ((hG.mul hGradi).mul hAmpDerivJMeas)).add
      (hG.mul hAmpDeriv2Meas)).indicator hKSmeas

/-- **★★ `gatedMixed2RepProdSGen'_measurable`.**  The primed measurability audit for the FULLY generic
    mixed second field-`pd` representative: chart joint-measurability DISCHARGED via
    `uniformInverseChart'_joint_measurable` (J4-1147). NOT `a₁ = R/6`. -/
theorem gatedMixed2RepProdSGen'_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hPimeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
    (hPjmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
    (hQmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
    (hAmpMeas : ∀ c : ℝ, Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp' g gi hC hK a b c w.1 w.2.2 w.2.1))
    (hAmpDerivIMeas : ∀ c : ℝ, Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) i w.2.1))
    (hAmpDerivJMeas : ∀ c : ℝ, Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j w.2.1))
    (hAmpDeriv2Meas : ∀ c : ℝ, Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j y) i w.2.1)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      Measurable (gatedMixed2RepProdSGen' g gi hC hK S a b i j Pifield Pjfield Qfield c) := by
  obtain ⟨δ₀, hδ₀, hmeas⟩ := uniformInverseChart'_joint_measurable g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  unfold gatedMixed2RepProdSGen'
  exact gatedMixed2RepProdSGenWith_measurable g gi hC hK S a b i j Pifield Pjfield Qfield
    (uniformInverseChart' g gi hC hK c) hKSmeas (hmeas c hc0 hcδ) hPimeas hPjmeas hQmeas
    (hAmpMeas c) (hAmpDerivIMeas c) (hAmpDerivJMeas c) (hAmpDeriv2Meas c)

/-! ###############################################################################
    ### ★★ THE GENERIC MIXED EVERYWHERE IDENTITY — `witnessMixedWith_eq_gatedMixed2RepProdSGenWith`.
    ############################################################################### -/

/-- **★★ `witnessMixedWith_eq_gatedMixed2RepProdSGenWith` — the GENERIC MIXED EVERYWHERE IDENTITY.**
    Chart-generic sibling of `GatedRepSFix.witnessMixed2_eq_gatedMixed2RepProdS`, at an ABSTRACT `W`.
    Proof mirrors the old one EXACTLY. NOT `a₁ = R/6`. -/
theorem witnessMixedWith_eq_gatedMixed2RepProdSGenWith (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (W : Point n → Point n → Point n)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => W w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => W w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
          (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y, PdiffAt (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        pd (fun y => pd (fun x => vanVleckGatedWitnessWith g gi hC hK S a b W w.1 x w.2.2) j y)
          i w.2.1 = 0) :
    ∀ w : ℝ × Point n × Point n,
      pd (fun y => pd (fun x => vanVleckGatedWitnessWith g gi hC hK S a b W w.1 x w.2.2) j y)
        i w.2.1
        = gatedMixed2RepProdSGenWith g gi hC hK S a b i j Pifield Pjfield Qfield W w := by
  intro w
  simp only [gatedMixed2RepProdSGenWith]
  by_cases hzKS : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
  · obtain ⟨hzK, hpS⟩ := hzKS
    rw [Set.indicator_of_mem
      (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from ⟨hzK, hpS⟩)]
    by_cases hτ : 0 < w.1
    · obtain ⟨hSopen, hjetVi, hjetVj, hjetQ, hampj, hampi, hamp2⟩ := hgate w hzK hτ hpS
      exact witnessMixedWith_gate_eq g gi hC hK S a b i j w.1 hτ W w.2.2 hzK hSopen w.2.1 hpS
        (Pifield w.2.2) (Pjfield w.2.2) (Qfield w.2.2 w.2.1)
        hjetVi hjetVj hjetQ hampj hampi hamp2
    · rw [not_lt] at hτ
      rw [witnessMixedWith_eq_zero_of_nonpos hn g gi hC hK S a b i j
            w.1 w.2.1 w.2.2 W hτ,
          gaussDdim_eq_zero_of_nonpos hn w.1 (W w.2.2 w.2.1) hτ]
      ring
  · rw [Set.indicator_of_notMem
      (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from hzKS)]
    by_cases hzK : w.2.2 ∈ K
    · have hpS : w.2.1 ∉ S w.2.2 := fun h => hzKS ⟨hzK, h⟩
      by_cases hτ : 0 < w.1
      · exact hOffS2 w hzK hτ hpS
      · rw [not_lt] at hτ
        exact witnessMixedWith_eq_zero_of_nonpos hn g gi hC hK S a b i j
          w.1 w.2.1 w.2.2 W hτ
    · exact witnessMixedWith_offGate_eq_zero g gi hC hK S a b i j w.1 w.2.1 w.2.2 W hzK

/-- **`witnessMixedWith_eq_gatedMixed2RepProdSGenWith_recovers_old`** — the compatibility bridge:
    instantiating the generic identity at `W := uniformInverseChart g gi hC hK` recovers the OLD
    theorem's exact statement. NOT `a₁ = R/6`. -/
theorem witnessMixedWith_eq_gatedMixed2RepProdSGenWith_recovers_old (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
          (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
          = 0) :
    ∀ w : ℝ × Point n × Point n,
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
        = gatedMixed2RepProdS g gi hC hK S a b i j Pifield Pjfield Qfield w := by
  exact witnessMixedWith_eq_gatedMixed2RepProdSGenWith hn g gi hC hK S a b i j
    Pifield Pjfield Qfield (uniformInverseChart g gi hC hK) hgate hOffS2

/-! ###############################################################################
    ### ★★★ THE PRIMED IDENTITY — `witnessMixed2_eq_gatedMixed2RepProdS'`.
    ############################################################################### -/

/-- **★★★ `witnessMixed2_eq_gatedMixed2RepProdS'`.**  Instantiating the generic identity at
    `W := uniformInverseChart' g gi hC hK c`: the FIRST genuine relational mixed-second-field-derivative
    identity connecting `vanVleckGatedWitness'` to `chartFieldAmp'`, closing with NO extra machinery
    beyond the caller-supplied `hgate`/`hOffS2`. NOT `a₁ = R/6`. -/
theorem witnessMixed2_eq_gatedMixed2RepProdS' (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart' g gi hC hK c w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart' g gi hC hK c w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
          (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y, PdiffAt (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        pd (fun y => pd (fun x => vanVleckGatedWitness' g gi hC hK S a b c w.1 x w.2.2) j y)
          i w.2.1 = 0) :
    ∀ w : ℝ × Point n × Point n,
      pd (fun y => pd (fun x => vanVleckGatedWitness' g gi hC hK S a b c w.1 x w.2.2) j y) i w.2.1
        = gatedMixed2RepProdSGen' g gi hC hK S a b i j Pifield Pjfield Qfield c w := by
  unfold vanVleckGatedWitness' gatedMixed2RepProdSGen'
  exact witnessMixedWith_eq_gatedMixed2RepProdSGenWith hn g gi hC hK S a b i j
    Pifield Pjfield Qfield (uniformInverseChart' g gi hC hK c) hgate hOffS2

/-! ###############################################################################
    ### The strongly-measurable capstone — generic and primed.
    ############################################################################### -/

/-- **`secondFieldPd_prod_stronglyMeasurable_v4With`.**  Chart-generic sibling of
    `GatedRepSFix.secondFieldPd_prod_stronglyMeasurable_v4`: over an ABSTRACT `W` + `hWmeas` (pulled OUT
    of the `hcar` existential). NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_stronglyMeasurable_v4With (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (W : Point n → Point n → Point n)
    (hWmeas : Measurable (fun w : ℝ × Point n × Point n => W w.2.2 w.2.1))
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmpWith g gi hC hK a b W w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => W w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => W w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmpWith g gi hC hK a b W w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitnessWith g gi hC hK S a b W w.1 x w.2.2) j y)
              i w.2.1 = 0)) :
    ∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitnessWith g gi hC hK S a b W w.1 x w.2.2) j y)
        i w.2.1) := by
  intro i j
  obtain ⟨Pifield, Pjfield, Qfield, hPimeas, hPjmeas, hQmeas, hAmpMeas,
    hAmpDerivIMeas, hAmpDerivJMeas, hAmpDeriv2Meas, hgate, hOffS2⟩ := hcar i j
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (fun x => vanVleckGatedWitnessWith g gi hC hK S a b W w.1 x w.2.2) j y)
          i w.2.1)
      = gatedMixed2RepProdSGenWith g gi hC hK S a b i j Pifield Pjfield Qfield W := by
    funext w
    exact witnessMixedWith_eq_gatedMixed2RepProdSGenWith hn g gi hC hK S a b i j
      Pifield Pjfield Qfield W hgate hOffS2 w
  rw [hrw]
  exact (gatedMixed2RepProdSGenWith_measurable g gi hC hK S a b i j Pifield Pjfield Qfield W
    hKSmeas hWmeas hPimeas hPjmeas hQmeas hAmpMeas hAmpDerivIMeas hAmpDerivJMeas
    hAmpDeriv2Meas).stronglyMeasurable

/-- **★★★ `secondFieldPd_prod_stronglyMeasurable_v4'`.**  The PRIMED instantiation: chart
    joint-measurability `hWmeas` fully DISCHARGED via `uniformInverseChart'_joint_measurable`
    (J4-1147) — no free chart-measurability hypothesis remains.  The genuinely amplitude-analytic
    hypotheses (about `chartFieldAmp'`, per tube radius `c`) remain as caller-supplied inputs.
    NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_stronglyMeasurable_v4' (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∀ c : ℝ, 0 < c → ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp' g gi hC hK a b c w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart' g gi hC hK c w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart' g gi hC hK c w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x =>
              vanVleckGatedWitness' g gi hC hK S a b c w.1 x w.2.2) j y) i w.2.1 = 0)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (fun x =>
          vanVleckGatedWitness' g gi hC hK S a b c w.1 x w.2.2) j y) i w.2.1) := by
  obtain ⟨δ₀, hδ₀, hmeas⟩ := uniformInverseChart'_joint_measurable g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ i j
  obtain ⟨Pifield, Pjfield, Qfield, hPimeas, hPjmeas, hQmeas, hAmpMeas,
    hAmpDerivIMeas, hAmpDerivJMeas, hAmpDeriv2Meas, hgate, hOffS2⟩ := hcar c hc0 i j
  unfold vanVleckGatedWitness'
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (fun x =>
          vanVleckGatedWitnessWith g gi hC hK S a b (uniformInverseChart' g gi hC hK c) w.1 x w.2.2)
          j y) i w.2.1)
      = gatedMixed2RepProdSGenWith g gi hC hK S a b i j Pifield Pjfield Qfield
          (uniformInverseChart' g gi hC hK c) := by
    funext w
    exact witnessMixedWith_eq_gatedMixed2RepProdSGenWith hn g gi hC hK S a b i j
      Pifield Pjfield Qfield (uniformInverseChart' g gi hC hK c) hgate hOffS2 w
  rw [hrw]
  exact (gatedMixed2RepProdSGenWith_measurable g gi hC hK S a b i j Pifield Pjfield Qfield
    (uniformInverseChart' g gi hC hK c) hKSmeas (hmeas c hc0 hcδ) hPimeas hPjmeas hQmeas
    hAmpMeas hAmpDerivIMeas hAmpDerivJMeas hAmpDeriv2Meas).stronglyMeasurable

end QIQTH.GatedRepSFix

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GatedRepSFix
#print axioms witnessMixedWith_gate_eq
#print axioms witnessMixedWith_offGate_eq_zero
#print axioms witnessMixedWith_eq_zero_of_nonpos
#print axioms gatedMixed2RepProdSGenWith_uniformInverseChart
#print axioms gatedMixed2RepProdSGenWith_measurable
#print axioms gatedMixed2RepProdSGen'_measurable
#print axioms witnessMixedWith_eq_gatedMixed2RepProdSGenWith
#print axioms witnessMixedWith_eq_gatedMixed2RepProdSGenWith_recovers_old
#print axioms witnessMixed2_eq_gatedMixed2RepProdS'
#print axioms secondFieldPd_prod_stronglyMeasurable_v4With
#print axioms secondFieldPd_prod_stronglyMeasurable_v4'
end AxiomChecks
