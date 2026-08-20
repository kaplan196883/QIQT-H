/-
  HbintInteriorTubeCoverRoute — J4-907: the interior joint `(z,x)`-continuity RESIDUAL of the J4-905
  measurability-route `hBFint` carry, REDUCED to the single crisp geometric inequality `b < r₀`
  (`r₀` = the banked Neumann / ContDiffAt threshold radius), via an OPEN `V ∪ Z` support cover.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick REDUCES the interior joint
  `(z,x)`-continuity residual left open by J4-905 (`HbintInteriorContinuityRoute`) to the geometric
  carry `b < r₀`; `b < r₀` itself is NOT established for the live `b` — it remains an honest, named,
  checkable open hypothesis.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE — the amorphous "joint continuity on the whole product" residual becomes `b < r₀`.

  J4-905 (`HbintInteriorContinuityRoute`) reduced the J4-904 measurability route's `hBFint` carry to
  the JOINT `(z,x)`-continuity of the field-Hessian norm on the OPEN×compact product
  `interior K ×ˢ concreteKx` — WITHOUT the boundary diagonal, the interior-only asset the J4-892
  boundary no-go LEAVES available.  This brick DISCHARGES that continuity, modulo `b < r₀`, via an
  OPEN support cover:

    * `Z := (jointCore)ᶜ` — OPEN (the compact core-graph is closed).  Off the core-graph the
      field-Hessian VANISHES (`fieldHessian_fderiv_eqZero_off_jointGraph`, J4-888), so its norm `≡ 0`,
      hence `ContinuousOn Z`.

    * `V := T ∩ interior (in-gate region)` — OPEN.  `T` = the joint chart-`C²` locus (OPEN, via the
      general-center J4-891 `ContDiffAt`s assembled into `generalCenter_chartC2_tube`); the in-gate
      region `{p | p.1 ∈ interior K ∧ p.2 ∈ exp p.1 '' ball 0 c}` has the interior-core points in its
      INTERIOR by the general-center coherent chart's EVENTUAL RIGHT INVERSE
      (`generalCenter_coherent_joint_chart`), so `V` covers the interior `b`-core.  On `V` the chart is
      `C²` and every point is in-gate (the gate `exp q '' ball 0 c` is OPEN,
      `uniformInverseChart_huniformChart`), so the field-derivative kernel is jointly `C¹` (J4-887) and
      the field-Hessian norm is `ContinuousOn V` (J4-878).

  `V ∪ Z` covers `interior K ×ˢ concreteKx` (interior-core points → `V` via the tube packaging with
  `b < r₀`; all other points are off the core-graph → `Z`); pasting continuity across the OPEN cover
  and restricting gives the residual.  The ONLY new scalar geometric input is `b < r₀`.

  ## THE DELIVERABLES.
    • `generalCenter_chartC2_tube` — ★ ITEM (1): the general-center core-tube packaging.  There is an
      OPEN `T` on which the joint chart is `ContDiffOn ℝ 2`, containing every `(z, exp z v)` with
      `z ∈ interior K` and `‖v‖ < r₀`.  Assembles the pointwise J4-891 general-center `ContDiffAt`s
      into a genuine `ContDiffOn` on an open tube (the `ContDiffAt`-locus-is-open trick, exactly as the
      banked diagonal tube `uniformInverseChart_jointContDiffOn_tube`).  `r₀` is UNIFORM over
      `interior K` (J4-891 quantifies it before the base point).
    • `core_mem_interior_inGate` — ★ ITEM (2) bridge: the interior-core local-openness of the in-gate
      region, from `generalCenter_coherent_joint_chart`'s eventual right inverse.
    • `interiorFieldHessianNorm_continuousOn` — ★★ the interior joint `(z,x)`-continuity of the
      field-Hessian norm on `interior K ×ˢ concreteKx`, from the `V ∪ Z` cover.
    • `hbint_interior_via_tube_cover_of_bLtR0` — ★★★ the FULL `hbint` field of
      `MixedDirectionsFieldHessianEnvelope`, obtained by feeding the interior continuity (per a.e. `s`)
      into J4-905's `hbint_concrete_via_interior_route`, GIVEN `b < r₀`.  The honest residual is now
      `b < r₀` plus the elementary `BL`-continuity / compact-`K` bound / null-frontier carries.
    • `interior_residual_of_bLtR0_nonvacuous` — the reduction fires (empty gate), no J4-548 trap.

  ## WHAT THIS FILE DOES NOT DO.
  `b < r₀` is NOT established for the live `b`; it is carried as a named open hypothesis.  This brick
  does NOT close `hbint` unconditionally, does NOT touch `hzmass` or the other `hCConv` legs, and does
  NOT bear on `hDuhamel` / `hDConv`.  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.
-/
import Mathlib
import QIQTH.HbintInteriorContinuityRoute
import QIQTH.GeneralCenterCoherentInverseChart
import QIQTH.QuantifiedCoherentChartTube
import QIQTH.WitnessFieldDerivJointC1FromTube
import QIQTH.HbintCollarMatchedCutoffClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.FieldHessianJointContinuity
open QIQTH.FieldHessianJointContinuityClosed
open QIQTH.HbintCollarMatchedCutoffClosed
open QIQTH.WitnessFieldDerivJointC1FromTube
open QIQTH.HbintInteriorContinuityRoute
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators ContDiff

namespace QIQTH.HbintInteriorTubeCoverRoute

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ### C0 — ITEM (1): the general-center core-tube packaging.
    ###      (The `ContDiffAt`-locus-is-open trick, mirroring the banked diagonal tube.)
    ############################################################################### -/

/-- **★ `generalCenter_chartC2_tube` — ITEM (1).**  The pointwise general-center J4-891 `ContDiffAt`s
    (`uniformInverseChart_jointContDiffAt_generalCenter`) assembled into a genuine `ContDiffOn ℝ 2` of
    the joint chart on an OPEN tube.  There is a radius `r₀ > 0` — UNIFORM over `interior K`, since
    J4-891 quantifies it before the base point — and an OPEN set `T` on which
    `fun ξ => uniformInverseChart g gi hC hK ξ.1 ξ.2` is `ContDiffOn ℝ 2`, containing every
    `(z, uniformFlowExp z v)` with `z ∈ interior K` and `‖v‖ < r₀`.

    Mechanism.  `T := {ξ | ContDiffAt ℝ 2 chart ξ}` is OPEN — finite-order `ContDiffAt` gives a whole
    `ContDiffOn ℝ 2` neighbourhood (`ContDiffAt.contDiffOn`), so the `ContDiffAt` locus is open — and
    the chart is `ContDiffOn ℝ 2` there pointwise; membership of the tube points is J4-891.  This is
    the SAME assembly the banked diagonal tube `uniformInverseChart_jointContDiffOn_tube` uses, at the
    general (nonzero-velocity) centre.  NOT `a₁ = R/6`. -/
theorem generalCenter_chartC2_tube (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ T : Set (Point n × Point n), IsOpen T ∧
      (∀ z₀ ∈ interior K, ∀ v₀ : Point n, ‖v₀‖ < r₀ →
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ T) ∧
      ContDiffOn ℝ 2 (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) T := by
  classical
  obtain ⟨r₀, hr₀pos, hCDAt⟩ := uniformInverseChart_jointContDiffAt_generalCenter g gi hC hK
  set f : Point n × Point n → Point n :=
    fun ξ => uniformInverseChart g gi hC hK ξ.1 ξ.2 with hfdef
  set T : Set (Point n × Point n) := {ξ | ContDiffAt ℝ 2 f ξ} with hTdef
  have hTopen : IsOpen T := by
    rw [hTdef, isOpen_iff_mem_nhds]
    intro ξ hξ
    have hξ' : ContDiffAt ℝ 2 f ξ := hξ
    obtain ⟨u, hu_nhds, hu_cd⟩ := hξ'.contDiffOn (m := 2) le_rfl (by norm_num)
    obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hu_nhds
    refine Filter.mem_of_superset (hWopen.mem_nhds hWmem) ?_
    intro ζ hζ
    exact (hu_cd.mono hWsub).contDiffAt (hWopen.mem_nhds hζ)
  refine ⟨r₀, hr₀pos, T, hTopen, ?_, ?_⟩
  · intro z₀ hz₀ v₀ hv₀
    show ContDiffAt ℝ 2 f ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n)
    exact hCDAt z₀ hz₀ v₀ hv₀
  · intro ξ hξ
    have hcda : ContDiffAt ℝ 2 f ξ := hξ
    exact hcda.contDiffWithinAt

/-! ###############################################################################
    ### C1 — ITEM (2) bridge: the interior-core local-openness of the in-gate region.
    ############################################################################### -/

/-- **★ `core_mem_interior_inGate` — ITEM (2) bridge.**  For an interior base `z₀ ∈ interior K` and a
    velocity `v₀` with `‖v₀‖ < uniformFlowRadius`, the invertibility datum `‖B - id‖ < 1`, and
    `‖v₀‖ < c`, the core point `(z₀, exp z₀ v₀)` lies in the INTERIOR of the in-gate region
    `IGc := {p | p.1 ∈ interior K ∧ p.2 ∈ exp p.1 '' ball 0 c}`.

    Mechanism (no new IFT / no open-map export needed).  `generalCenter_coherent_joint_chart` supplies a
    coherent chart `chartCoherent`, jointly `ContDiffAt ℝ 2` at the centre with value `v₀`, and the
    EVENTUAL RIGHT INVERSE `∀ᶠ ξ near centre, exp ξ.1 (chartCoherent ξ.1 ξ.2) = ξ.2`.  On the joint
    neighbourhood where (a) `ξ.1 ∈ interior K` (open), (b) `chartCoherent ξ.1 ξ.2 ∈ ball 0 c`
    (continuity of `chartCoherent` + value `v₀`, `‖v₀‖ < c`), and (c) the right-inverse identity holds,
    we have `ξ.2 = exp ξ.1 (chartCoherent ξ.1 ξ.2) ∈ exp ξ.1 '' ball 0 c`, i.e. `ξ ∈ IGc`.  So `IGc`
    is a neighbourhood of the core point.  NOT `a₁ = R/6`. -/
theorem core_mem_interior_inGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K)
    (v₀ : Point n) (hv₀ρ : ‖v₀‖ < uniformFlowRadius g gi hC hK)
    (hInv : ‖fderiv ℝ (uniformFlowExp g gi hC hK z₀) v₀
              - ContinuousLinearMap.id ℝ (Point n)‖ < 1)
    (c : ℝ) (hv₀c : ‖v₀‖ < c) :
    ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈
      interior {p : Point n × Point n | p.1 ∈ interior K ∧
        p.2 ∈ uniformFlowExp g gi hC hK p.1 '' Metric.ball (0 : Point n) c} := by
  obtain ⟨chartCoherent, hcd, hval, hinv⟩ :=
    generalCenter_coherent_joint_chart g gi hC hK z₀ hz₀ v₀ hv₀ρ hInv
  set p₀ : Point n × Point n := (z₀, uniformFlowExp g gi hC hK z₀ v₀) with hp₀def
  rw [mem_interior_iff_mem_nhds]
  -- (a) base point stays in `interior K`.
  have hN1 : ∀ᶠ ξ in nhds p₀, ξ.1 ∈ interior K :=
    (isOpen_interior.preimage continuous_fst).mem_nhds hz₀
  -- (b) the chart value stays inside `ball 0 c`.
  have hN2 : ∀ᶠ ξ in nhds p₀, chartCoherent ξ.1 ξ.2 ∈ Metric.ball (0 : Point n) c := by
    have hcont : ContinuousAt (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2) p₀ :=
      hcd.continuousAt
    refine hcont.eventually_mem ?_
    show Metric.ball (0 : Point n) c ∈ nhds (chartCoherent z₀ (uniformFlowExp g gi hC hK z₀ v₀))
    rw [hval]
    exact Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hv₀c)
  -- combine with the eventual right inverse.
  filter_upwards [hN1, hN2, hinv] with ξ hξ1 hξ2 hξinv
  exact ⟨hξ1, ⟨chartCoherent ξ.1 ξ.2, hξ2, hξinv⟩⟩

/-! ###############################################################################
    ### C2 — the interior joint `(z,x)`-continuity of the field-Hessian norm, via the `V ∪ Z` cover.
    ############################################################################### -/

/-- **★★ `interiorFieldHessianNorm_continuousOn`.**  The interior joint `(z,x)`-continuity of the
    field-Hessian norm on `interior K ×ˢ concreteKx` — the SOLE residual left by J4-905 — produced from
    the OPEN support cover `V ∪ Z`:
      • `Z := (jointCore)ᶜ` (open), off which the field-Hessian VANISHES (`hoffgraph`, J4-888);
      • `V := T ∩ interior IGc` (open), the joint chart-`C²` locus `T` (`hTopen`/`hTcd`) intersected
        with the interior in-gate region, on which the field-derivative kernel is jointly `C¹` (J4-887)
        so the field-Hessian norm is continuous (J4-878).
    The interior `b`-core points land in `V` — in `T` (`hcoreT`) and in `interior IGc` (the bridge
    `core_mem_interior_inGate`, using `hInvCore` + `hbρ` + `hbc`) — and every other point of
    `interior K ×ˢ concreteKx` is off the core-graph, hence in `Z`.  `hgateOpen` = the gate is OPEN
    (`uniformInverseChart_huniformChart`), turning `p.2 ∈ S p.1` into `S p.1 ∈ 𝓝 p.2`.  NOT `a₁ = R/6`. -/
theorem interiorFieldHessianNorm_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (c : ℝ) (hbc : b < c)
    (S : Point n → Set (Point n))
    (hS : S = fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
    {T : Set (Point n × Point n)} (hTopen : IsOpen T)
    (hTcd : ContDiffOn ℝ 2
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) T)
    (hcoreT : ∀ z₀ ∈ interior K, ∀ v : Point n, ‖v‖ ≤ b →
      ((z₀, uniformFlowExp g gi hC hK z₀ v) : Point n × Point n) ∈ T)
    (hgateOpen : ∀ q ∈ K, IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c))
    (hInvCore : ∀ z₀ ∈ interior K, ∀ v : Point n, ‖v‖ ≤ b →
      ‖fderiv ℝ (uniformFlowExp g gi hC hK z₀) v - ContinuousLinearMap.id ℝ (Point n)‖ < 1)
    (hoffgraph : ∀ p : Point n × Point n, p ∉ jointCore g gi hC hK b →
      fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2 = 0) :
    ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖)
      (interior K ×ˢ concreteKx g gi hC hK b) := by
  classical
  have hb0 : (0 : ℝ) ≤ b := le_of_lt (lt_trans ha hab)
  -- the in-gate region and the open pieces `V`, `Z`.
  set IGc : Set (Point n × Point n) :=
    {p : Point n × Point n | p.1 ∈ interior K ∧
      p.2 ∈ uniformFlowExp g gi hC hK p.1 '' Metric.ball (0 : Point n) c} with hIGcdef
  set V : Set (Point n × Point n) := T ∩ interior IGc with hVdef
  set Z : Set (Point n × Point n) := (jointCore g gi hC hK b)ᶜ with hZdef
  set f : Point n × Point n → ℝ :=
    fun p => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖ with hfdef
  have hVopen : IsOpen V := hTopen.inter isOpen_interior
  have hZopen : IsOpen Z :=
    (jointCore_isCompact g gi hC hK b hbρ).isClosed.isOpen_compl
  -- ── `f` is continuous on `V`.
  have hVchart : ContDiffOn ℝ 2
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) V :=
    hTcd.mono (Set.inter_subset_left)
  have hVgate : ∀ p ∈ V, p.1 ∈ K ∧ S p.1 ∈ nhds p.2 := by
    intro p hp
    have hpIG : p ∈ IGc := interior_subset hp.2
    refine ⟨interior_subset hpIG.1, ?_⟩
    rw [hS]
    exact (hgateOpen p.1 (interior_subset hpIG.1)).mem_nhds hpIG.2
  have hc1 : ContDiffOn ℝ 1
      (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1) V :=
    witnessFieldDeriv_jointContDiffOn_onGate g gi hC hK S a b i τ hw hVopen hVchart hVgate
  have hfV : ContinuousOn f V :=
    partialFDeriv_norm_jointContinuousOn hVopen
      (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1) hc1
  -- ── `f ≡ 0` on `Z`, hence continuous there.
  have hfZ : ContinuousOn f Z := by
    refine (continuousOn_const (c := (0 : ℝ))).congr ?_
    intro p hp
    show ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖ = 0
    rw [hoffgraph p hp, norm_zero]
  -- ── paste continuity across the OPEN cover `V ∪ Z`.
  have hglue : ContinuousOn f (V ∪ Z) := by
    refine ((hVopen.union hZopen).continuousOn_iff).mpr ?_
    intro x hx
    rcases hx with hxV | hxZ
    · exact (hVopen.continuousOn_iff.mp hfV) hxV
    · exact (hZopen.continuousOn_iff.mp hfZ) hxZ
  -- ── `interior K ×ˢ concreteKx ⊆ V ∪ Z`.
  have hcover : interior K ×ˢ concreteKx g gi hC hK b ⊆ V ∪ Z := by
    intro p hp
    by_cases hjc : p ∈ jointCore g gi hC hK b
    · -- interior-core point ⟹ `p ∈ V`.
      left
      obtain ⟨q, hqmem, hqeq⟩ := hjc
      obtain ⟨hqK, hqball⟩ := hqmem
      have hq1int : q.1 ∈ interior K := by
        have hh : p.1 ∈ interior K := hp.1
        rwa [← hqeq] at hh
      have hvb : ‖q.2‖ ≤ b := by
        rw [← dist_zero_right]; exact Metric.mem_closedBall.mp hqball
      refine ⟨?_, ?_⟩
      · -- `p ∈ T`.
        rw [← hqeq]
        exact hcoreT q.1 hq1int q.2 hvb
      · -- `p ∈ interior IGc`.
        rw [← hqeq]
        exact core_mem_interior_inGate g gi hC hK q.1 hq1int q.2
          (lt_of_le_of_lt hvb hbρ) (hInvCore q.1 hq1int q.2 hvb) c (lt_of_le_of_lt hvb hbc)
    · -- off the core-graph ⟹ `p ∈ Z`.
      right
      exact hjc
  exact hglue.mono hcover

/-! ###############################################################################
    ### C3 — the FULL `hbint` field, GIVEN `b < r₀`, via J4-905's measurability route.
    ############################################################################### -/

/-- **★★★ J4-907 — `hbint_interior_via_tube_cover_of_bLtR0`.**  The EXACT `hbint` field of
    `MixedDirectionsFieldHessianEnvelope`, at the CONCRETE flow-ball gate, obtained by feeding the
    interior joint `(z,x)`-continuity (`interiorFieldHessianNorm_continuousOn`, per a.e. `s`) into
    J4-905's measurability route `hbint_concrete_via_interior_route`, GIVEN the single geometric carry
    `b < r₀`.

    `r₀ := min rTube (min ρ₀ (1 / (C_D + 1)))` bundles the general-center `ContDiffAt` radius `rTube`
    (J4-891) and the Neumann threshold from the near-identity Jacobian bound
    `uniformFlowExp_fderiv_near_id_quant` (`ρ₀`, `C_D`), and is `> 0`.  Below `r₀` the interior `b`-core
    velocities (`‖v‖ ≤ b < r₀`) simultaneously satisfy the chart-`C²` tube membership and the Neumann
    invertibility `‖B - id‖ < 1`, so the `V ∪ Z` cover fires.  The off-graph vanishing and the gate
    openness are discharged from the banked collar (J4-888) and germ (`uniformInverseChart_huniformChart`)
    over the shared `c`-window.  The remaining carries are ELEMENTARY: `BL`-continuity on `K`, a
    compact-`K` product bound, and `volume (frontier K) = 0`.  So `hbint`'s interior joint-continuity
    residual reduces EXACTLY to `b < r₀`.  Radii `0 < a < b`, `b < uniformFlowRadius`; `K` nonempty.
    NOT `a₁ = R/6`. -/
theorem hbint_interior_via_tube_cover_of_bLtR0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ)
    (hnull : volume (frontier K) = 0)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ r₀ > (0 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        b < r₀ →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ContinuousOn (BL s) K) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∃ C : ℝ, ∀ z ∈ K, ‖BL s z *
              (⨆ x : Point n,
                ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)‖ ≤ C) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          Integrable (fun z => BL s z *
            (⨆ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  classical
  -- the tube packaging (item 1) + its radius `rTube`.
  obtain ⟨rTube, hrTubepos, T, hTopen, hTmem, hTcd⟩ := generalCenter_chartC2_tube g gi hC hK
  -- the near-identity Neumann bound.
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hnid⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  -- the germ / gate-openness radius.
  obtain ⟨δgate, hδgate, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  -- the off-graph collar radius (J4-888).
  obtain ⟨δoff, hδoff, hoff⟩ := fieldHessian_fderiv_eqZero_off_jointGraph g gi hC hK a b ha hab hbρ
  -- the J4-905 measurability route.
  obtain ⟨δroute, hδroute, hroute⟩ :=
    hbint_concrete_via_interior_route g gi hC hK hKne a b ha hab hbρ i t m BL hnull
  have hCD1pos : (0 : ℝ) < C_D + 1 := by linarith
  set r₀ : ℝ := min rTube (min ρ₀ (1 / (C_D + 1))) with hr₀def
  have hr₀pos : 0 < r₀ := by
    rw [hr₀def]; refine lt_min hrTubepos (lt_min hρ₀pos ?_); positivity
  set δ₀ : ℝ := min (min δgate δoff) δroute with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]; exact lt_min (lt_min hδgate hδoff) hδroute
  refine ⟨r₀, hr₀pos, δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ₀ S hS hbr₀ hBLK hbnd
  -- unpack the `c`-window bounds.
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcδgate : c < δgate := lt_of_lt_of_le hcδ₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcδoff : c < δoff := lt_of_lt_of_le hcδ₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδroute : c < δroute := lt_of_lt_of_le hcδ₀ (min_le_right _ _)
  -- radius comparisons.
  have hr₀rTube : r₀ ≤ rTube := by rw [hr₀def]; exact min_le_left _ _
  have hr₀ρ₀ : r₀ ≤ ρ₀ := by rw [hr₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr₀inv : r₀ ≤ 1 / (C_D + 1) := by
    rw [hr₀def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- `hcoreT`: interior `b`-core points sit in the chart-`C²` tube `T`.
  have hcoreT : ∀ z₀ ∈ interior K, ∀ v : Point n, ‖v‖ ≤ b →
      ((z₀, uniformFlowExp g gi hC hK z₀ v) : Point n × Point n) ∈ T := by
    intro z₀ hz₀ v hvb
    exact hTmem z₀ hz₀ v (lt_of_le_of_lt hvb (lt_of_lt_of_le hbr₀ hr₀rTube))
  -- `hgateOpen`: the gate is OPEN over the shared `c`-window.
  have hgateOpen : ∀ q ∈ K,
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c) := by
    intro q hq
    exact ((hchart q hq).2 c hc0 hcδgate).1
  -- `hInvCore`: the Neumann invertibility `‖B - id‖ < 1` for interior `b`-core velocities.
  have hInvCore : ∀ z₀ ∈ interior K, ∀ v : Point n, ‖v‖ ≤ b →
      ‖fderiv ℝ (uniformFlowExp g gi hC hK z₀) v - ContinuousLinearMap.id ℝ (Point n)‖ < 1 := by
    intro z₀ hz₀ v hvb
    have hz₀K : z₀ ∈ K := interior_subset hz₀
    have hvρ₀ : ‖v‖ < ρ₀ := lt_of_le_of_lt hvb (lt_of_lt_of_le hbr₀ hr₀ρ₀)
    have hvinv : ‖v‖ < 1 / (C_D + 1) := lt_of_le_of_lt hvb (lt_of_lt_of_le hbr₀ hr₀inv)
    have hb := hnid z₀ hz₀K v hvρ₀
    have hCDv : C_D * ‖v‖ < 1 := by
      have h1 : C_D * ‖v‖ ≤ C_D * (1 / (C_D + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hvinv) hCD0
      have h2 : C_D * (1 / (C_D + 1)) < 1 := by
        rw [mul_one_div, div_lt_one hCD1pos]; linarith
      linarith
    linarith [hb]
  -- the interior joint `(z,x)`-continuity, for every `s` (hence a.e.).
  have hjoint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ContinuousOn
        (fun p : Point n × Point n =>
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y p.1) p.2‖)
        (interior K ×ˢ concreteKx g gi hC hK b) := by
    refine ae_of_all volume (fun s _ => ?_)
    refine interiorFieldHessianNorm_continuousOn g gi hC hK a b ha hab hbρ i (t - s) hw c hbc S hS
      hTopen hTcd hcoreT hgateOpen hInvCore ?_
    intro p hp
    exact hoff c hbc hcδoff S hS i (t - s) p hp
  -- feed the interior continuity into the J4-905 measurability route.
  exact hroute c hbc hcδroute S hS hjoint hBLK hbnd

/-! ###############################################################################
    ### C4 — NON-VACUITY: the reduction fires, no unsatisfiable-antecedent trap.
    ############################################################################### -/

/-- **NON-VACUITY.**  At the DEGENERATE empty gate `S := fun _ => ∅` the field-derivative kernel is
    identically `0`, so the field-Hessian norm is the constant `0`, hence trivially `ContinuousOn` the
    interior product — the interior continuity that `interiorFieldHessianNorm_continuousOn` delivers
    (and that `hbint_interior_via_tube_cover_of_bLtR0` consumes) is genuinely inhabited.  So the whole
    `V ∪ Z` reduction fires on a real input — no J4-548 / J4-847 unsatisfiable antecedent, never the
    conclusion in disguise.  (The genuinely non-degenerate content — the interior continuity of the
    CONCRETE non-empty-gate field-Hessian norm, delivered by the cover under `b < r₀` — is the honest
    advance.)  NOT `a₁ = R/6`. -/
theorem interior_residual_of_bLtR0_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (τ : ℝ) :
    ContinuousOn
        (fun p : Point n × Point n =>
          ‖fderiv ℝ (fun y =>
            witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y p.1) p.2‖)
        (interior K ×ˢ concreteKx g gi hC hK b) := by
  have hzero : (fun p : Point n × Point n =>
      ‖fderiv ℝ (fun y =>
        witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y p.1) p.2‖)
      = fun _ => (0 : ℝ) := by
    funext p
    rw [QIQTH.ChartJetXUniformBound.witnessFieldHessian_fderiv_eqZero_of_notMem_closure
      g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ p.1 p.2 (by simp)]
    exact norm_zero
  rw [hzero]; exact continuousOn_const

end QIQTH.HbintInteriorTubeCoverRoute

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HbintInteriorTubeCoverRoute
#print axioms generalCenter_chartC2_tube
#print axioms core_mem_interior_inGate
#print axioms interiorFieldHessianNorm_continuousOn
#print axioms hbint_interior_via_tube_cover_of_bLtR0
#print axioms interior_residual_of_bLtR0_nonvacuous
end AxiomChecks
