/-
  WitnessFieldDerivConsumersWith — J4-1158: Phase 2, Task B + Canary C1 of the chart-parametric
  rebuild campaign (dispatch 3 of the newly-authorized full rebuild).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  genericizes the `EngineInstantiation.lean` theorems whose STATEMENT directly names
  `witnessFieldDeriv`/`witnessFieldDeriv2` — Phase 2 Task A's own consumer set, per
  `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md` — over the abstract chart `W`, threading through
  `WitnessFieldDerivWith.lean` (J4-1157) and `ChartFieldAmpWith.lean` (J4-1156).  It also supplies
  Canary C1 ("FirstDerivativeDiamond"): the FIRST genuine relational theorem connecting a PRIMED
  witness derivative (`witnessFieldDeriv'`) to `chartFieldAmp'` — the generic + primed sibling of
  `EngineInstantiation.witnessFieldDeriv_gate_eq`.  No `sorry`, no new axioms, no `:= True`, no
  vacuous/unsatisfiable hypotheses, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## TASK B SCOPE (consumer theorems in `EngineInstantiation.lean` whose statement names
  `witnessFieldDeriv`/`witnessFieldDeriv2`; confirmed by direct read of that file in full):
    1. `witnessFieldDeriv2_center`                       → genericized below (`witnessFieldDeriv2With_center`)
    2. `witnessFieldDeriv2_eq_pd_witnessFieldDeriv`       → genericized below (`..._eq_pd_...With`)
    3. `witnessFieldDeriv_gate_eq`   ★ (= Canary C1's OLD analogue) → genericized + PRIMED below
    4. `witnessFieldDeriv_offGate_eq_zero`                → genericized below
    5. `witnessFieldDeriv2_offGate_eq_zero`               → genericized below
    6. `witnessFieldDeriv_gate_abs_le`                    → genericized + PRIMED below
    7. `witness_secondOrder_interchange` — NOT ATTEMPTED THIS DISPATCH.  Its statement threads
       `heatConvFrozen (vanVleckGatedWitness g gi hC hK S acut bcut)` DIRECTLY (the chart-hardwired
       engine entry point of `SecondOrderInterchange.pd_pd_heatConvFrozen_interchange`), not merely
       `witnessFieldDeriv`/`witnessFieldDeriv2`; genericizing it needs a `heatConvFrozenWith`
       (Phase 3/4 territory per the plan — the measurability/audit + engine-assembly layers), out of
       scope for a Task B definitional-threading dispatch.  Left for a future dispatch.

  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `vanVleckGatedWitnessWith_gate_apply` — chart-generic sibling of
      `AmplitudePackage.vanVleckGatedWitness_gate_apply` (the on-gate exact-value unfolding), needed as
      a support lemma for the generic gate-formula proofs below. Pure threading (`gatedKernel_apply_of_mem`
      + `globalCutoffParametrixWitnessN` + `heatParametrix_one_apply` are ALL already chart-generic).

    * `witnessSecondXDerivWith` / `witnessFieldDeriv2With_center` — chart-generic sibling of
      `witnessSecondXDeriv` / `witnessFieldDeriv2_center` (`rfl`).

    * `witnessFieldDeriv2With_eq_pd_witnessFieldDerivWith` — chart-generic sibling of
      `witnessFieldDeriv2_eq_pd_witnessFieldDeriv` (`rfl`).

    * `witnessFieldDerivWith_offGate_eq_zero` / `witnessFieldDeriv2With_offGate_eq_zero` — chart-generic
      siblings of the off-gate vanishing theorems (the gate machinery `gatedKernel_apply_of_notMem` is
      ALREADY chart-independent, so these transfer verbatim).

    * ★★ `witnessFieldDerivWith_gate_eq` — CANARY C1's GENERIC LAYER: the chart-generic sibling of
      `witnessFieldDeriv_gate_eq`.  Proof mirrors the old one EXACTLY, `W z` substituted for
      `uniformInverseChart g gi hC hK z` throughout — this works because the two ingredients the old
      proof leans on, `gaussComp_hasDerivAt_line`/`gaussComp_pd` (`ChartJetHessian.lean`), were ALREADY
      stated over an abstract chart map `V : Point n → Point n → Point n` (not tied to
      `uniformInverseChart`), and `chartFieldAmpWith` (J4-1156) supplies the generic amplitude.

    * ★★★ `witnessFieldDeriv'_gate_eq` — CANARY C1 ITSELF ("FirstDerivativeDiamond"): instantiating
      `witnessFieldDerivWith_gate_eq` at `W := uniformInverseChart' g gi hC hK c` gives the FIRST
      genuine relational theorem connecting the PRIMED witness derivative `witnessFieldDeriv'` to
      `chartFieldAmp'` — the on-gate factored-derivative formula for the NEW, jointly-measurable chart.
      CANARY RESULT: **PASS**, closes cleanly with NO extra machinery beyond what J4-1156/1157 already
      supplied (no global chart reachability, no global old/new equality, no agreement-outside-the-tube
      argument, no global `ContDiff` beyond the caller-supplied `hJetV`/`hAmp1` local hypotheses — those
      are carried exactly as in the old theorem, just re-pointed at `uniformInverseChart'`).

    * `witnessFieldDerivWith_gate_abs_le` / `witnessFieldDeriv'_gate_abs_le` — the generic + primed
      siblings of the on-gate factorized domination (E2), following the same triangle-inequality proof
      verbatim off the generic/primed gate-equality formula.

  ## WHAT THIS DOES NOT DO.
  Does NOT genericize `witness_secondOrder_interchange` (needs `heatConvFrozenWith`, out of scope).
  Does NOT claim `witnessFieldDeriv' = witnessFieldDeriv` or `chartFieldAmp' = chartFieldAmp` (false in
  general; the two charts agree only on a bounded tube image).  Does not touch the
  measurability/audit chain (Phase 4).

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.WitnessFieldDerivWith
import QIQTH.ChartFieldAmpWith

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel
open QIQTH.ThetaMeasurableEmbedding
open scoped Interval Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### Support — the chart-generic on-gate exact value of `vanVleckGatedWitnessWith`.
    ############################################################################### -/

/-- **Support — `vanVleckGatedWitnessWith_gate_apply`.**  Chart-generic sibling of
    `AmplitudePackage.vanVleckGatedWitness_gate_apply`: on the gate (`q ∈ K`, `p ∈ S q`) the generic
    gated witness equals its ungated parametrix, at the ABSTRACT chart `W`.  Pure threading
    (`gatedKernel_apply_of_mem` + `globalCutoffParametrixWitnessN` + `heatParametrix_one_apply`, all
    already chart-generic). NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitnessWith_gate_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (W : Point n → Point n → Point n) (τ : ℝ) {p q : Point n} (hq : q ∈ K) (hp : p ∈ S q) :
    vanVleckGatedWitnessWith g gi hC hK S a b W τ p q
      = radialCutoff a b (W q p)
        * (gaussDdim τ (W q p)
            * vanVleck g (W q p) ^ (-(1 : ℝ) / 2)
            * (transportCoeff (transportOp (vanVleck g) g gi) 0 (W q p)
              + transportCoeff (transportOp (vanVleck g) g gi) 1 (W q p) * τ)) := by
  unfold vanVleckGatedWitnessWith
  rw [gatedKernel_apply_of_mem K S _ τ hq hp]
  simp only [globalCutoffParametrixWitnessN]
  rw [heatParametrix_one_apply]

/-! ###############################################################################
    ### Task B(1,2) — the chart-generic center identity and stacking identity.
    ############################################################################### -/

/-- **Task B — `witnessSecondXDerivWith`.**  Chart-generic sibling of `witnessSecondXDeriv`, built
    from `vanVleckGatedWitnessWith` at the abstract chart `W`. NOT `a₁ = R/6`. -/
noncomputable def witnessSecondXDerivWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (W : Point n → Point n → Point n) : ℝ :=
  pd (fun x : Point n =>
      pd (fun x' : Point n => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z) i x) i (0 : Point n)

/-- **Task B — `witnessFieldDeriv2With_center`.**  Chart-generic sibling of `witnessFieldDeriv2_center`
    (`rfl`). NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2With_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (W : Point n → Point n → Point n) :
    witnessFieldDeriv2With g gi hC hK S a b i τ (0 : Point n) z W
      = witnessSecondXDerivWith g gi hC hK S a b i τ z W := rfl

/-- **Task B — `witnessFieldDeriv2With_eq_pd_witnessFieldDerivWith`.**  Chart-generic sibling of
    `witnessFieldDeriv2_eq_pd_witnessFieldDeriv` (`rfl`). NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2With_eq_pd_witnessFieldDerivWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (W : Point n → Point n → Point n) :
    witnessFieldDeriv2With g gi hC hK S a b i τ p z W
      = pd (fun x : Point n => witnessFieldDerivWith g gi hC hK S a b i τ x z W) i p := rfl

/-! ###############################################################################
    ### Task B(4,5) — the chart-generic off-gate vanishing.
    ############################################################################### -/

/-- **Task B — `witnessFieldDerivWith_offGate_eq_zero`.**  Chart-generic sibling of
    `witnessFieldDeriv_offGate_eq_zero`: the gate machinery (`gatedKernel_apply_of_notMem`) is already
    chart-independent, so this transfers verbatim. NOT `a₁ = R/6`. -/
theorem witnessFieldDerivWith_offGate_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (W : Point n → Point n → Point n) (hz : z ∉ K) :
    witnessFieldDerivWith g gi hC hK S a b i τ p z W = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z = 0 := by
    intro x'
    unfold vanVleckGatedWitnessWith
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  unfold witnessFieldDerivWith
  simp only [hzero]
  exact pd_const 0 i p

/-- **Task B — `witnessFieldDeriv2With_offGate_eq_zero`.**  Chart-generic sibling of
    `witnessFieldDeriv2_offGate_eq_zero`. NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2With_offGate_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (W : Point n → Point n → Point n) (hz : z ∉ K) :
    witnessFieldDeriv2With g gi hC hK S a b i τ p z W = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z = 0 := by
    intro x'
    unfold vanVleckGatedWitnessWith
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  unfold witnessFieldDeriv2With
  have hin : (fun x : Point n =>
        pd (fun x' : Point n => vanVleckGatedWitnessWith g gi hC hK S a b W τ x' z) i x)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext x
    simp only [hzero]
    exact pd_const 0 i x
  rw [hin]
  exact pd_const 0 i p

/-! ###############################################################################
    ### Task B(3) / ★★ CANARY C1 GENERIC LAYER — `witnessFieldDerivWith_gate_eq`.
    ############################################################################### -/

/-- **★★ CANARY C1 GENERIC LAYER — `witnessFieldDerivWith_gate_eq`.**  Chart-generic sibling of
    `EngineInstantiation.witnessFieldDeriv_gate_eq`: on the OPEN gate, at the ABSTRACT chart `W`,
      `dH i τ p z = G_τ(W z p)·(−(∑ₖ (W z p)ₖ·Pₖ)/(2τ))·A(p) + G_τ(W z p)·∂ᵢA(p)`,
    with `A := chartFieldAmpWith … W`.  Proof mirrors the old theorem EXACTLY, `W z` substituted for
    `uniformInverseChart g gi hC hK z` throughout: this works because `gaussComp_hasDerivAt_line` /
    `gaussComp_pd` (`ChartJetHessian.lean`) were ALREADY stated over an abstract chart map, and
    `chartFieldAmpWith` supplies the generic amplitude. NOT `a₁ = R/6`. -/
theorem witnessFieldDerivWith_gate_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (W : Point n → Point n → Point n)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun s : ℝ => W z (Function.update p i s) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmpWith g gi hC hK a b W τ z) i p) :
    witnessFieldDerivWith g gi hC hK S a b i τ p z W
      = gaussDdim τ (W z p)
          * (-(∑ k, W z p k * Pval k) / (2 * τ))
          * chartFieldAmpWith g gi hC hK a b W τ z p
        + gaussDdim τ (W z p)
          * pd (chartFieldAmpWith g gi hC hK a b W τ z) i p := by
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
  unfold witnessFieldDerivWith
  rw [pd_congr_of_eventuallyEq _ _ i p hev]
  have hGf : PdiffAt (fun x' => gaussDdim τ (W z x')) i p :=
    (gaussComp_hasDerivAt_line (W z) Pval τ hτ i p hJetV).differentiableAt
  rw [pd_mul (fun x' => gaussDdim τ (W z x'))
        (chartFieldAmpWith g gi hC hK a b W τ z) i p hGf hAmp1,
      gaussComp_pd (W z) Pval τ hτ i p hJetV]

/-! ###############################################################################
    ### ★★★ CANARY C1 — `witnessFieldDeriv'_gate_eq` (the PRIMED "FirstDerivativeDiamond").
    ############################################################################### -/

/-- **★★★ CANARY C1 — `witnessFieldDeriv'_gate_eq` — "FirstDerivativeDiamond".**  Instantiating
    `witnessFieldDerivWith_gate_eq` at `W := uniformInverseChart' g gi hC hK c` (J4-1147/1148/1149):
    the FIRST genuine relational theorem connecting the PRIMED witness derivative
    `witnessFieldDeriv'` to `chartFieldAmp'`.  CANARY RESULT: PASS — closes with no extra machinery
    (no global chart reachability, no global old/new chart equality, no bounded-tube agreement
    argument, no global `ContDiff` beyond the caller-supplied local `hJetV`/`hAmp1`). NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv'_gate_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart' g gi hC hK c z (Function.update p i s) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmp' g gi hC hK a b c τ z) i p) :
    witnessFieldDeriv' g gi hC hK S a b c i τ p z
      = gaussDdim τ (uniformInverseChart' g gi hC hK c z p)
          * (-(∑ k, uniformInverseChart' g gi hC hK c z p k * Pval k) / (2 * τ))
          * chartFieldAmp' g gi hC hK a b c τ z p
        + gaussDdim τ (uniformInverseChart' g gi hC hK c z p)
          * pd (chartFieldAmp' g gi hC hK a b c τ z) i p := by
  unfold witnessFieldDeriv' chartFieldAmp'
  exact witnessFieldDerivWith_gate_eq g gi hC hK S a b i τ hτ (uniformInverseChart' g gi hC hK c)
    z hz hSopen p hp Pval hJetV hAmp1

/-! ###############################################################################
    ### Task B(6) / Canary C1 corollary — the generic + primed on-gate factorized domination.
    ############################################################################### -/

/-- **Task B — `witnessFieldDerivWith_gate_abs_le`.**  Chart-generic sibling of
    `witnessFieldDeriv_gate_abs_le`: same triangle-inequality proof off the generic gate-equality
    formula. NOT `a₁ = R/6`. -/
theorem witnessFieldDerivWith_gate_abs_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ) (W : Point n → Point n → Point n)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun s : ℝ => W z (Function.update p i s) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmpWith g gi hC hK a b W τ z) i p)
    (Bs Ba Bd : ℝ)
    (hSc : |(-(∑ k, W z p k * Pval k) / (2 * τ))| ≤ Bs)
    (hBa : |chartFieldAmpWith g gi hC hK a b W τ z p| ≤ Ba)
    (hBd : |pd (chartFieldAmpWith g gi hC hK a b W τ z) i p| ≤ Bd) :
    |witnessFieldDerivWith g gi hC hK S a b i τ p z W|
      ≤ gaussDdim τ (W z p) * (Bs * Ba + Bd) := by
  rw [witnessFieldDerivWith_gate_eq g gi hC hK S a b i τ hτ W z hz hSopen p hp Pval hJetV hAmp1]
  set G := gaussDdim τ (W z p) with hGdef
  set sc := -(∑ k, W z p k * Pval k) / (2 * τ) with hscdef
  set A := chartFieldAmpWith g gi hC hK a b W τ z p with hAdef
  set dA := pd (chartFieldAmpWith g gi hC hK a b W τ z) i p with hdAdef
  have hGnn : 0 ≤ G := gaussDdim_nonneg _ _
  have hBsnn : 0 ≤ Bs := le_trans (abs_nonneg _) hSc
  calc |G * sc * A + G * dA|
      ≤ |G * sc * A| + |G * dA| := abs_add_le _ _
    _ = G * |sc| * |A| + G * |dA| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hGnn]
    _ ≤ G * Bs * Ba + G * Bd := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left hBd hGnn)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hSc hGnn) hBa (abs_nonneg _)
          (mul_nonneg hGnn hBsnn)
    _ = G * (Bs * Ba + Bd) := by ring

/-- **Canary C1 corollary — `witnessFieldDeriv'_gate_abs_le`.**  Instantiating
    `witnessFieldDerivWith_gate_abs_le` at `W := uniformInverseChart' g gi hC hK c`: the on-gate
    factorized domination for the PRIMED first-derivative kernel `witnessFieldDeriv'`, in terms of
    `chartFieldAmp'`. NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv'_gate_abs_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart' g gi hC hK c z (Function.update p i s) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmp' g gi hC hK a b c τ z) i p)
    (Bs Ba Bd : ℝ)
    (hSc : |(-(∑ k, uniformInverseChart' g gi hC hK c z p k * Pval k) / (2 * τ))| ≤ Bs)
    (hBa : |chartFieldAmp' g gi hC hK a b c τ z p| ≤ Ba)
    (hBd : |pd (chartFieldAmp' g gi hC hK a b c τ z) i p| ≤ Bd) :
    |witnessFieldDeriv' g gi hC hK S a b c i τ p z|
      ≤ gaussDdim τ (uniformInverseChart' g gi hC hK c z p) * (Bs * Ba + Bd) := by
  unfold witnessFieldDeriv'
  exact witnessFieldDerivWith_gate_abs_le g gi hC hK S a b i τ hτ (uniformInverseChart' g gi hC hK c)
    z hz hSopen p hp Pval hJetV hAmp1 Bs Ba Bd hSc hBa hBd

end QIQTH.HeatResidualBound

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms vanVleckGatedWitnessWith_gate_apply
#print axioms witnessSecondXDerivWith
#print axioms witnessFieldDeriv2With_center
#print axioms witnessFieldDeriv2With_eq_pd_witnessFieldDerivWith
#print axioms witnessFieldDerivWith_offGate_eq_zero
#print axioms witnessFieldDeriv2With_offGate_eq_zero
#print axioms witnessFieldDerivWith_gate_eq
#print axioms witnessFieldDeriv'_gate_eq
#print axioms witnessFieldDerivWith_gate_abs_le
#print axioms witnessFieldDeriv'_gate_abs_le
end AxiomChecks
