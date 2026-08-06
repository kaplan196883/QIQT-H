/-
  CConvV2WgInstantiation — J4-328 (facade-v2 brick 11 of 14): instantiating the chart-parametric v2
  slice interface at the PIECEWISE chart `Wg`, and proving the WITNESS-EQUALITY BRIDGE that identifies
  the generic `Wg`-witness with the CONCRETE `vanVleckGatedWitness`.  ONE brick of the `a₁ = R/6`
  heat-kernel campaign (SOL CONSULT #9, docs/qg_roadmap/JET4_TOWER_PLAN.md).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It routes the
  banked chart-intrinsic measurability walls INTERNAL (through `B2MeasurabilityDissolution.Wg`) and
  bridges the opaque-chart `gatedWitnessW` (brick 3, `CConvV2ChartInterface`) to the concrete
  `vanVleckGatedWitness` at the on-gate agreement region.  NO `sorry` (header prose excepted), NO new
  axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis in this file's OWN theorems, no existing
  file edited, nothing committed.  The `.choose`-heavy `uniformInverseChart` is touched ONLY through the
  banked agreement PROPERTY (`wg_walls23_from_banked`'s regional agreement) — never unfolded; `Wg` is a
  transparent `if-then-else` and is unfolded freely.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (U0) THE RECON — `SliceChartData` field discharge verdicts at `Wg`.

  `SliceChartData K S u (Wg Γ G) Amp` (`CConvV2Contracts`) has five fields.  At the piecewise chart
  `Wg Γ G` the verdicts are:

  ── `hWjoint` (joint `(s,z)`-measurability of `fun p ↦ Wg Γ G p.2 (update x i w)`) — **DISCHARGED
     INTERNAL** from the banked `B2MeasurabilityDissolution.wg_chartB_measurable` (needs only
     `MeasurableSet Γ` + `Measurable G`, both banked in `wg_walls23_from_banked`).  This is the chart
     wall that was previously an external carry; here it is proved from `Wg`'s transparency.

  ── `hDeriv` (on-gate chart-Jacobian line-derivative column `Pval`) — **HONEST CARRY.**  The derivative
     of `Wg` AT an on-gate point equals the derivative of `uniformInverseChart` (they agree on a nbhd of
     the gate point via `wg_eventuallyEq_chart_onGate` + `HasDerivAt.congr_of_eventuallyEq`), so it is
     dischargeable from the banked concrete jet `CConvV2ChartComparison.chart_firstJet_column_center`;
     but that transfer needs the concrete `C²` field-centre carry and the gate openness, so it is passed
     through as a named satisfiable hypothesis (satisfiability: `sliceChartData_trivial`).

  ── `hAmpDiff` (on-gate amplitude partial-differentiability `PdiffAt (Amp τ z) i x`) — **HONEST CARRY.**
     `Amp` is a FREE parameter of `SliceChartData`; its concrete instantiation `chartFieldAmp`
     (`NormalFormDischarge`) bakes `uniformInverseChart`, so `hAmpDiff` is chart-geometry, NOT a `Wg`
     wall.  Carried through generically (satisfiable at `Amp ≡ 0` / the banked amplitude jets).

  ── `hRadialLower` / `hRadialUpper` (two-sided radial comparison `½·r²z ≤ r²(W z x) ≤ 2·r²z`) — **HONEST
     CARRY.**  On-gate `Wg z x = uniformInverseChart z x` (agreement), so these reduce to the banked
     centre comparison `CConvV2ChartComparison.chart_radial_twosided_center`; carried through (the
     general-field-point comparison is the banked coercivity carry, not a `Wg` wall).

  VERDICT: exactly ONE field (`hWjoint`) is a chart MEASURABILITY wall dischargeable at `Wg`; the other
  four are chart-GEOMETRY carries (satisfiable, never the conclusion), independent of the piecewise
  representative.  The slice INTERFACE (`sliceInterfaceW_of_data`) consumes ONLY `hWjoint`.

  ## (U2) THE WITNESS-EQUALITY BRIDGE — verdict: **CLEAN (no cutoff collar).**
  `globalCutoffParametrixWitnessN N Θ u a b Vmap τ p q = radialCutoff a b (Vmap q p)·heatParametrix N Θ u
  τ (Vmap q p)` (`OrderNResidual`): the inner kernel evaluates `Vmap` ONLY at the SAME `(q,p)` pair, not
  at any shifted argument.  In `gatedKernel K S H`, that pair is used only ON the gate (`q ∈ K`,
  `p ∈ S q`).  So the bridge needs ONLY the on-gate agreement `Wg Γ G q p = uniformInverseChart g gi hC
  hK q p` (for `q ∈ K`, `p ∈ S q`) — NO radial-cutoff-support collar condition arises.  Off-gate BOTH
  witnesses are `0` (the gate indicator).  The agreement is the banked regional agreement restricted to
  the gate collar `c ≤ ρ` (gate radius ≤ regional-agreement radius), certified satisfiable in
  `wg_agree_onGate_satisfiable` from `wg_walls23_from_banked`.

  ## WHAT THIS FILE LANDS.
    • (U1) `sliceChartData_at_Wg` — `SliceChartData K S u (Wg Γ G) Amp` with `hWjoint` discharged from
      the banked `wg_chartB_measurable`, the four geometry fields named satisfiable carries.
    • (U2) `wg_agree_onGate` — on-gate agreement `Wg Γ G q p = uniformInverseChart z x` from the banked
      flow-image regional agreement + the gate collar; `gatedWitnessW_Wg_eq_vanVleckGatedWitness` — THE
      bridge (as functions); `wg_agree_onGate_satisfiable` — satisfiability from `wg_walls23_from_banked`.
    • (U3) `sliceInterface_CONCRETE` — the three witness legs (`hSliceCont ∧ hWq ∧ hWa`) for the CONCRETE
      `vanVleckGatedWitness`, via U2 rewriting `sliceInterfaceW_of_data` at `Wg` — the chart-intrinsic
      `hVmapMeas`/`hChartB` walls now INTERNAL.
    • (U4) `wg_hCover_leg` — the on-gate `C²` (`hCover`-analog) re-export for the brick-14 consumer.

  NOT `a₁ = R/6`.
-/
import QIQTH.CConvV2ChartInterface
import QIQTH.B2MeasurabilityDissolution
import QIQTH.CConvV2Contracts

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance QIQTH.ExpMap
open QIQTH.HeatResidualBound QIQTH.B2MeasurabilityDissolution
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.CConvV2ChartInterface QIQTH.CConvV2Contracts
open scoped Topology

namespace QIQTH.CConvV2WgInstantiation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 (U1) — `SliceChartData` at the piecewise chart `Wg` (`hWjoint` INTERNAL).
    ############################################################################### -/

/-- **★★ (U1) `sliceChartData_at_Wg`.**  The `SliceChartData` instance at the piecewise chart `Wg Γ G`
    (`B2MeasurabilityDissolution`) and an arbitrary amplitude family `Amp`.  The ONLY chart MEASURABILITY
    wall `hWjoint` is DISCHARGED INTERNAL from the banked `wg_chartB_measurable` (needs only
    `MeasurableSet Γ` + `Measurable G`); the four chart-GEOMETRY fields (`hDeriv`, `hAmpDiff`,
    `hRadialLower`, `hRadialUpper`) are named satisfiable carries (independent of the piecewise
    representative — see U0; satisfiable via `sliceChartData_trivial`).  ⚠ NOT `a₁ = R/6`. -/
theorem sliceChartData_at_Wg (K : Set (Point n)) (S : Point n → Set (Point n)) (u : Set (Point n))
    (Γ : Set (Point n × Point n)) (G : Point n × Point n → Point n)
    (Amp : ℝ → Point n → Point n → ℝ)
    (hΓ : MeasurableSet Γ) (hG : Measurable G)
    (hDeriv : ∀ x ∈ u, ∀ i : Fin n, ∀ z ∈ K, x ∈ S z →
        ∃ Pval : Fin n → ℝ, ∀ k : Fin n,
          HasDerivAt (fun r : ℝ => Wg Γ G z (Function.update x i r) k) (Pval k) (x i))
    (hAmpDiff : ∀ x ∈ u, ∀ i : Fin n, ∀ τ : ℝ, ∀ z ∈ K, x ∈ S z →
        PdiffAt (fun x' => Amp τ z x') i x)
    (hRadialLower : ∀ x ∈ u, ∀ z ∈ K, x ∈ S z →
        (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Wg Γ G z x))
    (hRadialUpper : ∀ x ∈ u, ∀ z ∈ K, x ∈ S z →
        rncRadialSq (Wg Γ G z x) ≤ 2 * rncRadialSq z) :
    SliceChartData K S u (Wg Γ G) Amp where
  hWjoint := fun _x₀ _hx₀ i =>
    Filter.Eventually.of_forall (fun x w => wg_chartB_measurable Γ G hΓ hG (Function.update x i w))
  hDeriv := hDeriv
  hAmpDiff := hAmpDiff
  hRadialLower := hRadialLower
  hRadialUpper := hRadialUpper

/-! ###############################################################################
    ### §2 (U2) — THE WITNESS-EQUALITY BRIDGE.
    ############################################################################### -/

/-- **★★ (U2) `wg_agree_onGate` — on-gate agreement `Wg Γ G z p = uniformInverseChart z p`.**  From the
    banked flow-image regional agreement (`uniformInverseChart z (φ_z v) = G (z, φ_z v)` for `‖v‖ ≤ ρ`),
    the gate collar `c ≤ ρ` and the constant-radius gate `S z = φ_z '' ball 0 c`, `Wg Γ G` agrees with the
    inverse chart at EVERY on-gate point `(z, p)` (`z ∈ K`, `p ∈ S z`).  Reason: `p = φ_z v` with
    `‖v‖ < c ≤ ρ`, so `(z,p) ∈ Γ ⟹ Wg Γ G z p = G (z,p)`, and the agreement gives `uniformInverseChart
    z p = G (z,p)` too.  (Goes through the banked agreement PROPERTY — never unfolds the `.choose` chart.)
    ⚠ NOT `a₁ = R/6`. -/
theorem wg_agree_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {S : Point n → Set (Point n)}
    {Γ : Set (Point n × Point n)} (hΓeq : Γ = {q : Point n × Point n | q.1 ∈ K ∧ q.2 ∈ S q.1})
    (G : Point n × Point n → Point n) (c ρ : ℝ) (hcρ : c ≤ ρ)
    (hSz : ∀ z ∈ K, S z = uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
    (hagree : ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ ρ →
        uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v)
          = G (q, uniformFlowExp g gi hC hK q v)) :
    ∀ q ∈ K, ∀ p ∈ S q, Wg Γ G q p = uniformInverseChart g gi hC hK q p := by
  intro q hq p hp
  have hpimg : p ∈ uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c := by
    rw [← hSz q hq]; exact hp
  obtain ⟨v, hv, hvp⟩ := hpimg
  rw [mem_ball_zero_iff] at hv
  have hvρ : ‖v‖ ≤ ρ := le_trans hv.le hcρ
  have hqp : (q, p) ∈ Γ := by rw [hΓeq]; exact ⟨hq, hp⟩
  have hWg : Wg Γ G q p = G (q, p) := by simp only [Wg, if_pos hqp]
  rw [hWg, ← hvp]
  exact (hagree q hq v hvρ).symm

/-- **★★★ (U2) `gatedWitnessW_Wg_eq_vanVleckGatedWitness` — THE WITNESS-EQUALITY BRIDGE.**  As FUNCTIONS
    `ℝ → Point → Point → ℝ`, the generic gated witness at the piecewise chart `Wg Γ G` (brick 3,
    `CConvV2ChartInterface.gatedWitnessW`) EQUALS the concrete `vanVleckGatedWitness g gi hC hK S a b`,
    given the on-gate agreement `hAgree` (from `wg_agree_onGate`).  Proof: `funext τ p q` + the gate
    indicator case split.  OFF-gate (`q ∉ K` or `p ∉ S q`) both sides are `0`
    (`gatedKernel_apply_of_notMem`).  ON-gate the inner kernel `globalCutoffParametrixWitnessN … Vmap τ p
    q = radialCutoff a b (Vmap q p)·heatParametrix … (Vmap q p)` evaluates the chart at the SAME on-gate
    pair `(q,p)` where `Wg Γ G q p = uniformInverseChart q p` (`hAgree`) — so no cutoff-collar condition
    is needed (U2 verdict: CLEAN).  ⚠ NOT `a₁ = R/6`. -/
theorem gatedWitnessW_Wg_eq_vanVleckGatedWitness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Γ : Set (Point n × Point n)) (G : Point n × Point n → Point n)
    (hAgree : ∀ q ∈ K, ∀ p ∈ S q, Wg Γ G q p = uniformInverseChart g gi hC hK q p) :
    gatedWitnessW g gi a b K S (Wg Γ G) = vanVleckGatedWitness g gi hC hK S a b := by
  funext τ p q
  simp only [gatedWitnessW, vanVleckGatedWitness]
  by_cases hq : q ∈ K
  · by_cases hp : p ∈ S q
    · rw [gatedKernel_apply_of_mem K S _ τ hq hp, gatedKernel_apply_of_mem K S _ τ hq hp]
      simp only [globalCutoffParametrixWitnessN]
      rw [hAgree q hq p hp]
    · rw [gatedKernel_apply_of_notMem K S _ τ p q (Or.inr hp),
          gatedKernel_apply_of_notMem K S _ τ p q (Or.inr hp)]
  · rw [gatedKernel_apply_of_notMem K S _ τ p q (Or.inl hq),
        gatedKernel_apply_of_notMem K S _ τ p q (Or.inl hq)]

/-- **★★ (U2) `wg_agree_onGate_satisfiable` — the on-gate agreement is SATISFIABLE from banked builders.**
    Citing `B2MeasurabilityDissolution.wg_walls23_from_banked` (which packages the banked regional
    agreement `flowInverse_jointMeasurable_regional` + the reach `hKSmeas_concrete`), there is a gate
    radius `c > 0`, a jointly-measurable `G`, and the gate `Γ = {(z,p) | z∈K ∧ p∈S z}` (with `S z = φ_z ''
    ball 0 c`) such that `Γ` is measurable, `G` is measurable, AND the on-gate agreement `Wg Γ G q p =
    uniformInverseChart q p` holds for every `q ∈ K`, `p ∈ S q`.  This certifies the `hAgree` hypothesis
    of the bridge (and the `hΓ`/`hG` of `sliceChartData_at_Wg`) is non-vacuous, not `False`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem wg_agree_onGate_satisfiable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ c > (0 : ℝ), ∃ G : Point n × Point n → Point n, Measurable G ∧
      ∃ Γ : Set (Point n × Point n),
        Γ = {q : Point n × Point n | q.1 ∈ K ∧
              q.2 ∈ uniformFlowExp g gi hC hK q.1 '' Metric.ball (0 : Point n) c} ∧
        MeasurableSet Γ ∧
        (∀ q ∈ K, ∀ p ∈ (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c),
          Wg Γ G q p = uniformInverseChart g gi hC hK q p) := by
  obtain ⟨ρ, hρ, G, hGmeas, hagree, δ₀, hδ₀, hspec⟩ := wg_walls23_from_banked g gi hC hK
  refine ⟨min ρ (δ₀ / 2), lt_min hρ (by positivity), G, hGmeas, ?_⟩
  set c := min ρ (δ₀ / 2) with hcdef
  have hcρ : c ≤ ρ := min_le_left _ _
  have hc0 : 0 < c := lt_min hρ (by positivity)
  have hcδ : c < δ₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  set Γ : Set (Point n × Point n) := {q : Point n × Point n | q.1 ∈ K ∧ q.2 ∈ S q.1} with hΓdef
  have hΓmeas : MeasurableSet Γ := (hspec c hc0 hcδ).1
  refine ⟨Γ, rfl, hΓmeas, ?_⟩
  exact wg_agree_onGate g gi hC hK (S := S) (Γ := Γ) hΓdef G c ρ hcρ
    (fun z _hz => rfl) hagree

/-! ###############################################################################
    ### §3 (U3) — THE THREE CONCRETE WITNESS LEGS (`hSliceCont ∧ hWq ∧ hWa`), walls INTERNAL.
    ############################################################################### -/

/-- **★★★ (U3) `sliceInterface_CONCRETE` — the three slice-interface legs for the CONCRETE
    `vanVleckGatedWitness`.**  Rewrites the opaque-chart three-leg interface `sliceInterfaceW_of_data`
    (brick 3) at `Vmap := Wg Γ G` through the witness-equality bridge (U2) to land on the CONCRETE
    `vanVleckGatedWitness g gi hC hK S a b`.  The chart-intrinsic measurability walls
    `hVmapMeas`/`hChartB` are now INTERNAL (routed through `Wg` via `wg_chartB_measurable`, packaged in
    the `chart : SliceChartData … (Wg Γ G)` — its `hWjoint` field discharged from `hΓ`/`hG` in
    `sliceChartData_at_Wg`).  Honest carries: `hSmeasSet` (gate-set data), the coefficient data
    (`hΘc`/`hΘne`/`huc`), the per-`p` slice-continuity dichotomy `hSliceData` (chart geometry), the
    `chart` package, and `hAgree` (satisfiable — `wg_agree_onGate_satisfiable`).  ⚠ NOT `a₁ = R/6`. -/
theorem sliceInterface_CONCRETE (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u₀ : Set (Point n)) {Amp : ℝ → Point n → Point n → ℝ}
    (Γ : Set (Point n × Point n)) (G : Point n × Point n → Point n)
    (hSmeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (chart : SliceChartData K S u₀ (Wg Γ G) Amp)
    (hSliceData : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
        (p.2 ∉ K)
        ∨ (p.2 ∈ K
            ∧ (∀ q, q ∉ S p.2 → radialCutoff a b (Wg Γ G p.2 q) = 0)
            ∧ Continuous
                (fun w : ℝ =>
                  innerKernelFieldW g gi a b (Wg Γ G) (t - p.1) p.2 (Function.update x i w))))
    (hAgree : ∀ q ∈ K, ∀ p ∈ S q, Wg Γ G q p = uniformInverseChart g gi hC hK q p) :
    (∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ p : ℝ × Point n, Continuous
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2))
    ∧ (∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ q : ℚ,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1)
            (Function.update x i (x i + (q : ℝ))) p.2))
    ∧ (∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i (x i)) p.2)) := by
  have hbridge := gatedWitnessW_Wg_eq_vanVleckGatedWitness g gi hC hK S a b Γ G hAgree
  have hlegs := sliceInterfaceW_of_data g gi a b (K := K) S (Wg Γ G) t u₀ (Amp := Amp)
    hK.measurableSet hSmeasSet hΘc hΘne huc chart hSliceData
  rw [hbridge] at hlegs
  exact hlegs

/-! ###############################################################################
    ### §4 (U4) — the `hCover`-analog re-export for the brick-14 consumer.
    ############################################################################### -/

/-- **★ (U4) `wg_hCover_leg` — the on-gate `C²` (`hCover`-analog) at `Wg`.**  A re-export of the banked
    `B2MeasurabilityDissolution.wg_contDiffAt_onGate`, shaped for the brick-14 `hCover` consumer: under
    the gate collar (`c ≤ ρ`, `S z = φ_z '' ball 0 c` open) and the regional agreement, the on-gate `C²`
    regularity of the inverse chart transfers to `Wg Γ G z` at every gate point `x`.  ⚠ NOT `a₁ = R/6`. -/
theorem wg_hCover_leg (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {S : Point n → Set (Point n)}
    {Γ : Set (Point n × Point n)} (hΓeq : Γ = {q : Point n × Point n | q.1 ∈ K ∧ q.2 ∈ S q.1})
    (G : Point n × Point n → Point n)
    (z : Point n) (hzK : z ∈ K) (c ρ : ℝ) (hcρ : c ≤ ρ)
    (hSz : S z = uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
    (hSzopen : IsOpen (S z))
    (hagree : ∀ v : Point n, ‖v‖ ≤ ρ →
        uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v)
          = G (z, uniformFlowExp g gi hC hK z v))
    {x : Point n} (hxSz : x ∈ S z)
    (hWc2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x) :
    ContDiffAt ℝ 2 (fun p : Point n => Wg Γ G z p) x :=
  wg_contDiffAt_onGate g gi hC hK hΓeq G z hzK c ρ hcρ hSz hSzopen hagree hxSz hWc2

end QIQTH.CConvV2WgInstantiation

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvV2WgInstantiation
#print axioms sliceChartData_at_Wg
#print axioms wg_agree_onGate
#print axioms gatedWitnessW_Wg_eq_vanVleckGatedWitness
#print axioms wg_agree_onGate_satisfiable
#print axioms sliceInterface_CONCRETE
#print axioms wg_hCover_leg
end AxiomChecks
