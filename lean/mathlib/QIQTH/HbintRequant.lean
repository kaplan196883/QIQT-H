/-
  HbintRequant — the `b < r₀` OPACITY discharge: the tube/Neumann radius `r₀` and the c-window
  chart-germ ceiling `δ₀` of the J4-907 interior tube-cover `hbint` route, REQUANTIFIED BEFORE the
  cutoff parameters `(a, b)`, so a prescribed-ceiling gate producer can align `b < r₀ ∧ c < δ₀`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the J4-907 residual).  `HbintInteriorTubeCoverRoute.hbint_interior_via_tube_cover_of_bLtR0`
  produces the FULL `hbint` integrability at a concrete flow-ball gate GIVEN the single geometric carry
  `b < r₀`, where `r₀ := min rTube (min ρ₀ (1/(C_D+1)))` and the c-window ceiling
  `δ₀ := min (min δgate δoff) δroute` — but BOTH `r₀` and `δ₀` are produced AFTER the theorem's explicit
  `(a, b)` parameters.  The intended alignment prescribes a gate via the banked constant-radius producer
  `gatedWitnessN1_hEboundW_le_lin_CONST_prescribed(…ε, hε)` (which yields `0 < a < b < c` with `c < ε`,
  `ε` chosen BEFORE `(a, b)`); to close `b < r₀ ∧ c < δ₀` one must set `ε := min r₀ δ₀` — needing `r₀`
  and `δ₀` available BEFORE `(a, b)`.  This is exactly the `ReachRequant`/`CurvedA1ReachAlign` situation.

  ── ★★ THE PROVENANCE AUDIT (verified by reading the Lean).
    • `r₀`'s pieces `rTube` (`generalCenter_chartC2_tube`), `ρ₀`,`C_D`
      (`uniformFlowExp_fderiv_near_id_quant`) take NO `(a, b)` — already `(a, b)`-free.
    • The c-window ceiling bottoms out UNIFORMLY at the SINGLE `(a, b)`-free chart-germ radius of
      `HeatResidualBound.uniformInverseChart_huniformChart`:
        `δgate`  = that germ directly;
        `δoff`   via `fieldHessian_fderiv_eqZero_off_jointGraph` → `fieldHessian_zero_offCore`
                  → `witness_zero_offCore` → the germ (the `a b ha hab hbρ` enter only per-point bodies);
        `δroute` via `hbint_concrete_via_interior_route` → `hBFint_concrete_of_jointInteriorContinuous`
                  → `fieldHessian_vanish_off_concreteKx` → `fieldHessian_zero_offCore` → the germ.
  Hence the honest ∃∀-swap is PROVABLE by replaying each supplier with the germ radius `obtain`ed above
  `(a, b)` — this file does exactly that, level by level, ending at `hbint_interior_via_tube_cover_requant`:
    `∃ r₀ > 0, ∃ δ₀ > 0, ∀ a b, 0 < a → a < b → b < uniformFlowRadius → ∀ c, b < c → c < δ₀ → …
       → b < r₀ → (BL/compact carries) → [∀ᵐ s, Integrable …]`
  — the tube radius AND the chart-germ ceiling both available BEFORE the gate parameters.

  Every proof below is a hoisted replay of the corresponding banked theorem (named in each docstring);
  no new mathematical content, no new axioms, no `sorry`, no `:= True`.

  ⚠ HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick only re-quantifies PROVED
  geometric radius suppliers; the `b < r₀` carry is DISCHARGED against a prescribed gate (see the
  companion capstone), the elementary `BL`-continuity / compact-`K` bound / null-frontier carries remain
  honest hypotheses.  No existing file is edited.
-/
import Mathlib
import QIQTH.HbintInteriorTubeCoverRoute
import QIQTH.CurvedA1ReachAlign

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.OffSVanishing QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.FieldHessianJointContinuity
open QIQTH.FieldHessianJointContinuityClosed
open QIQTH.HbintMeasurabilityNullFrontier
open QIQTH.HbintCollarMatchedCutoffClosed
open QIQTH.WitnessFieldDerivJointC1FromTube
open QIQTH.HbintInteriorContinuityRoute
open QIQTH.HbintInteriorTubeCoverRoute
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.PullbackMetric QIQTH.CurvedA1ReachAlign
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.HbintRequant

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ### R1 — the off-core witness vanishing, radius (chart germ) BEFORE `(a, b)`.
    ###      (hoisted replay of `HGateBoundedConcreteDischarge.witness_zero_offCore`.)
    ############################################################################### -/

/-- **★ R1 — `witness_zero_offCore_requant`.**  Hoisted replay of
    `HGateBoundedConcreteDischarge.witness_zero_offCore`: the radius is the `(a, b)`-free chart germ of
    `uniformInverseChart_huniformChart`, now produced BEFORE `(a, b)`.  NOT `a₁ = R/6`. -/
theorem witness_zero_offCore_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (τ : ℝ) (q : Point n), q ∈ K →
          ∀ x : Point n, x ∉ closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b) →
            vanVleckGatedWitness g gi hC hK S a b τ x q = 0 := by
  obtain ⟨δ₀, hδ₀pos, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq τ q hq x hxU
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  obtain ⟨hgerm, _hball⟩ := hspec q hq
  have hSq : S q = uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c := by rw [hSeq]
  have hxNotBall : x ∉ uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b :=
    fun h => hxU (subset_closure h)
  show vanVleckGatedWitness g gi hC hK S a b τ x q = 0
  unfold vanVleckGatedWitness
  by_cases hxS : x ∈ S q
  · rw [gatedKernel_apply_of_mem K S _ τ hq hxS]
    rw [hSq] at hxS
    obtain ⟨v, hv, hvx⟩ := hxS
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    have hWqv : uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
      have hh := ((hgerm v (lt_trans hvc hcδ)).1).eq_of_nhds
      simpa using hh
    have hWqx : uniformInverseChart g gi hC hK q x = v := by rw [← hvx]; exact hWqv
    have hcut0 : radialCutoff a b v = 0 := by
      by_contra hne
      have hlt : rncRadialSq v < b ^ 2 := by
        by_contra hge
        exact hne (radialCutoff_eq_zero ha hab (not_lt.mp hge))
      have hsqle : ‖v‖ * ‖v‖ ≤ rncRadial v * rncRadial v :=
        mul_le_mul (norm_le_rncRadial v) (norm_le_rncRadial v) (norm_nonneg v)
          (rncRadial_nonneg v)
      have hnv2 : ‖v‖ ^ 2 < b ^ 2 := by
        have hsq := rncRadial_sq v
        nlinarith [hsqle, hlt, hsq]
      have hnvb : ‖v‖ < b := lt_of_pow_lt_pow_left₀ 2 hb0.le hnv2
      exact hxNotBall ⟨v, mem_ball_zero_iff.mpr hnvb, hvx⟩
    unfold globalCutoffParametrixWitnessN
    rw [hWqx, hcut0, zero_mul]
  · rw [gatedKernel_apply_of_notMem K S _ τ x q (Or.inr hxS)]

/-! ###############################################################################
    ### R2 — the off-core field-Hessian vanishing, radius BEFORE `(a, b)`.
    ###      (hoisted replay of `HGateBoundedConcreteDischarge.fieldHessian_zero_offCore`.)
    ############################################################################### -/

/-- **★ R2 — `fieldHessian_zero_offCore_requant`.**  Hoisted replay of
    `HGateBoundedConcreteDischarge.fieldHessian_zero_offCore` off R1.  NOT `a₁ = R/6`. -/
theorem fieldHessian_zero_offCore_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (τ : ℝ) (q : Point n), q ∈ K →
          ∀ x : Point n, x ∉ closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b) →
            fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y q) x = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar0⟩ := witness_zero_offCore_requant g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq i τ q hq x hxU
  have hcollar := hcollar0 a b ha hab c hbc hcδ S hSeq
  have hUopen : IsOpen ((closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b))ᶜ) :=
    isClosed_closure.isOpen_compl
  have hwit : (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' q) =ᶠ[nhds x] (fun _ => 0) := by
    refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hxU) ?_
    intro y hy
    exact hcollar τ q hq y hy
  have hf0 : (fun y => witnessFieldDeriv g gi hC hK S a b i τ y q) =ᶠ[nhds x] (fun _ => 0) := by
    have hnest := (eventually_eventually_nhds (p := fun y =>
      (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' q) y = (fun _ => (0 : ℝ)) y)).mpr hwit
    filter_upwards [hnest] with y hy
    show pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' q) i y = 0
    rw [pd_congr_of_eventuallyEq _ _ i y hy]
    exact pd_zero_fun i y
  rw [hf0.fderiv_eq]
  exact fderiv_const_apply (0 : ℝ)

/-! ###############################################################################
    ### R2b — the off-jointGraph field-Hessian vanishing, radius BEFORE `(a, b)`.
    ###       (hoisted replay of `HbintCollarMatchedCutoffClosed.fieldHessian_fderiv_eqZero_off_jointGraph`.)
    ############################################################################### -/

/-- **★ R2b — `fieldHessian_fderiv_eqZero_off_jointGraph_requant`.**  Hoisted replay of
    `HbintCollarMatchedCutoffClosed.fieldHessian_fderiv_eqZero_off_jointGraph` off R2 (`hbρ` now under
    the `∀ a b`).  NOT `a₁ = R/6`. -/
theorem fieldHessian_fderiv_eqZero_off_jointGraph_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → b < uniformFlowRadius g gi hC hK →
      ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (τ : ℝ) (p : Point n × Point n),
          p ∉ jointCore g gi hC hK b →
            fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2 = 0 := by
  obtain ⟨δ₀, hδ₀, hoff0⟩ := fieldHessian_zero_offCore_requant g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro a b ha hab hbρ c hbc hcδ S hSeq i τ p hp
  have hoff := hoff0 a b ha hab c hbc hcδ S hSeq
  by_cases hzK : p.1 ∈ K
  · have hxNotClosedBall : p.2 ∉ uniformFlowExp g gi hC hK p.1 '' Metric.closedBall (0 : Point n) b := by
      intro hx
      obtain ⟨v, hv, hvx⟩ := hx
      exact hp ⟨(p.1, v), ⟨hzK, hv⟩, by rw [Prod.ext_iff]; exact ⟨rfl, hvx⟩⟩
    have hxNotCore : p.2 ∉ closure (uniformFlowExp g gi hC hK p.1 '' Metric.ball (0 : Point n) b) := by
      intro hx
      have hsub : closure (uniformFlowExp g gi hC hK p.1 '' Metric.ball (0 : Point n) b)
          ⊆ uniformFlowExp g gi hC hK p.1 '' Metric.closedBall (0 : Point n) b := by
        refine closure_minimal ?_ (closedBall_image_isClosed g gi hC hK b hbρ p.1 hzK)
        exact Set.image_mono Metric.ball_subset_closedBall
      exact hxNotClosedBall (hsub hx)
    exact hoff i τ p.1 hzK p.2 hxNotCore
  · exact QIQTH.HZMassIntegrabilityAttempt.witnessFieldHessian_fderiv_eqZero_of_base_notMem_K
      g gi hC hK S a b i τ p.1 hzK p.2

/-! ###############################################################################
    ### R3 — the off-`concreteKx` field-Hessian vanishing, radius BEFORE `(a, b)`.
    ###      (hoisted replay of `FieldHessianJointContinuity.fieldHessian_vanish_off_concreteKx`.)
    ############################################################################### -/

/-- **★ R3 — `fieldHessian_vanish_off_concreteKx_requant`.**  Hoisted replay of
    `FieldHessianJointContinuity.fieldHessian_vanish_off_concreteKx` off R2.  NOT `a₁ = R/6`. -/
theorem fieldHessian_vanish_off_concreteKx_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → b < uniformFlowRadius g gi hC hK →
      ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (τ : ℝ) (z : Point n), z ∈ K →
          ∀ x ∉ concreteKx g gi hC hK b,
            fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0 := by
  obtain ⟨δ₀, hδ₀, hoff0⟩ := fieldHessian_zero_offCore_requant g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro a b ha hab hbρ c hbc hcδ S hSeq i τ z hz x hxKx
  have hoff := hoff0 a b ha hab c hbc hcδ S hSeq
  have hxcore : x ∉ closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b) :=
    fun h => hxKx (core_subset_concreteKx g gi hC hK b hbρ z hz h)
  exact hoff i τ z hz x hxcore

/-! ###############################################################################
    ### R4 — the interior `ciSup`-continuity route, radius BEFORE `(a, b)`.
    ###      (hoisted replay of `HbintInteriorContinuityRoute.hBFint_concrete_of_jointInteriorContinuous`.)
    ############################################################################### -/

/-- **★★ R4 — `hBFint_concrete_of_jointInteriorContinuous_requant`.**  Hoisted replay of
    `HbintInteriorContinuityRoute.hBFint_concrete_of_jointInteriorContinuous` off R3.  NOT `a₁ = R/6`. -/
theorem hBFint_concrete_of_jointInteriorContinuous_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (i : Fin n) (t : ℝ) (m : ℕ) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → b < uniformFlowRadius g gi hC hK →
      ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ContinuousOn
              (fun p : Point n × Point n =>
                ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y p.1) p.2‖)
              (interior K ×ˢ concreteKx g gi hC hK b)) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          ContinuousOn
            (fun z => ⨆ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖) (interior K) := by
  obtain ⟨δ₀, hδ₀, hvan0⟩ := fieldHessian_vanish_off_concreteKx_requant g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro a b ha hab hbρ c hbc hcδ S hSeq hjoint
  have hvan := hvan0 a b ha hab hbρ c hbc hcδ S hSeq
  have hb0 : (0 : ℝ) ≤ b := le_of_lt (lt_trans ha hab)
  filter_upwards [hjoint] with s hjs hsU
  refine BF_interiorContinuousOn_of_jointContinuousOn g gi hC hK S a b i (t - s)
    (concreteKx_isCompact g gi hC hK b hbρ) (concreteKx_nonempty g gi hC hK b hKne hb0)
    ?_ (hjs hsU)
  intro z hz x hx
  exact hvan i (t - s) z (interior_subset hz) x hx

/-! ###############################################################################
    ### R5 — the interior-route `hbint`, radius BEFORE `(a, b)`.
    ###      (hoisted replay of `HbintInteriorContinuityRoute.hbint_concrete_via_interior_route`.)
    ############################################################################### -/

/-- **★★ R5 — `hbint_concrete_via_interior_route_requant`.**  Hoisted replay of
    `HbintInteriorContinuityRoute.hbint_concrete_via_interior_route` off R4.  NOT `a₁ = R/6`. -/
theorem hbint_concrete_via_interior_route_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (i : Fin n) (t : ℝ) (m : ℕ)
    (BL : ℝ → Point n → ℝ) (hnull : volume (frontier K) = 0) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → b < uniformFlowRadius g gi hC hK →
      ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ContinuousOn
              (fun p : Point n × Point n =>
                ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y p.1) p.2‖)
              (interior K ×ˢ concreteKx g gi hC hK b)) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ContinuousOn (BL s) K) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∃ C : ℝ, ∀ z ∈ K, ‖BL s z *
              (⨆ x : Point n,
                ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)‖ ≤ C) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          Integrable (fun z => BL s z *
            (⨆ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  obtain ⟨δ₀, hδ₀, hBFint0⟩ :=
    hBFint_concrete_of_jointInteriorContinuous_requant g gi hC hK hKne i t m
  refine ⟨δ₀, hδ₀, ?_⟩
  intro a b ha hab hbρ c hbc hcδ S hSeq hjoint hBLK hbnd
  refine hbint_of_interiorContinuous_nullFrontier hK.isClosed hK hnull
    BL (fun s z => ⨆ x : Point n,
      ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖) t m
    (hBFint0 a b ha hab hbρ c hbc hcδ S hSeq hjoint) ?_ hBLK hbnd
  filter_upwards with s _ z hz
  exact BF_ciSup_eqZero_of_base_notMem_K g gi hC hK S a b i (t - s) z hz

/-! ###############################################################################
    ### R6 — the tube-cover `hbint`, `r₀` AND `δ₀` BOTH BEFORE `(a, b)`.
    ###      (hoisted replay of `HbintInteriorTubeCoverRoute.hbint_interior_via_tube_cover_of_bLtR0`.)
    ############################################################################### -/

/-- **★★★ R6 — `hbint_interior_via_tube_cover_requant`.**  The `r₀`- AND `δ₀`-hoisted form of
    `HbintInteriorTubeCoverRoute.hbint_interior_via_tube_cover_of_bLtR0`: the tube/Neumann radius `r₀`
    and the chart-germ c-window ceiling `δ₀` are BOTH produced BEFORE the gate parameters `(a, b)`, so a
    prescribed-ceiling gate producer can set its ceiling `ε ≤ min r₀ δ₀` and align `b < r₀ ∧ c < δ₀`
    for the live gate.  Interior tube-cover mechanics are IDENTICAL to J4-907; only the quantifier order
    is honestly swapped (every supplier radius audited `(a, b)`-free).  NOT `a₁ = R/6`. -/
theorem hbint_interior_via_tube_cover_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (i : Fin n) (t : ℝ) (m : ℕ)
    (BL : ℝ → Point n → ℝ) (hnull : volume (frontier K) = 0)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ r₀ > (0 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b →
      b < uniformFlowRadius g gi hC hK →
      ∀ c : ℝ, b < c → c < δ₀ →
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
  -- tube packaging (item 1) + its radius `rTube` — `(a,b)`-free.
  obtain ⟨rTube, hrTubepos, T, hTopen, hTmem, hTcd⟩ := generalCenter_chartC2_tube g gi hC hK
  -- near-identity Neumann bound — `(a,b)`-free.
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hnid⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  -- germ / gate-openness radius — `(a,b)`-free.
  obtain ⟨δgate, hδgate, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  -- off-jointGraph collar radius — hoisted (R2b).
  obtain ⟨δoff, hδoff, hoff0⟩ := fieldHessian_fderiv_eqZero_off_jointGraph_requant g gi hC hK
  -- interior measurability route — hoisted (R5).
  obtain ⟨δroute, hδroute, hroute0⟩ :=
    hbint_concrete_via_interior_route_requant g gi hC hK hKne i t m BL hnull
  have hCD1pos : (0 : ℝ) < C_D + 1 := by linarith
  set r₀ : ℝ := min rTube (min ρ₀ (1 / (C_D + 1))) with hr₀def
  have hr₀pos : 0 < r₀ := by
    rw [hr₀def]; refine lt_min hrTubepos (lt_min hρ₀pos ?_); positivity
  set δ₀ : ℝ := min (min δgate δoff) δroute with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]; exact lt_min (lt_min hδgate hδoff) hδroute
  refine ⟨r₀, hr₀pos, δ₀, hδ₀pos, ?_⟩
  intro a b ha hab hbρ c hbc hcδ₀ S hS hbr₀ hBLK hbnd
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
    exact hoff0 a b ha hab hbρ c hbc hcδoff S hS i (t - s) p hp
  -- feed the interior continuity into the hoisted measurability route.
  exact hroute0 a b ha hab hbρ c hbc hcδroute S hS hjoint hBLK hbnd

/-! ###############################################################################
    ### CAP — THE ALIGNMENT: the `b < r₀` obstruction CLOSED at the genuinely-curved witness.
    ############################################################################### -/

/-- **★★★ CAP — `hbint_bLtR0_closed_curved`.**  THE ALIGNMENT CAPSTONE.  For the genuinely-curved
    witness `g^κ = curvedRNCMetric κ` (`κ < 0`), `1 ≤ n`, GIVEN only the mainline-standard carried
    inputs {`hChr`, `hw`}, there are gate parameters `0 < a < b < c` at the CONCRETE flow-ball gate
    `S c` such that the interior tube-cover `hbint` (R6) holds — with its `b < r₀` obstruction FULLY
    DISCHARGED — leaving only the ELEMENTARY `BL`-continuity and compact-`K` sup-bound carries.

    Route: hoist `r₀`,`δ₀` before `(a, b)` (R6, `hbint_interior_via_tube_cover_requant`) at `K = {0}`;
    obtain the flow radius `ρ`; prescribe `ε := min r₀ (min δ₀ ρ)` into the banked constant-radius
    producer `gatedWitnessN1_hEboundW_le_lin_CONST_prescribed` (which uses the SAME raw flow-ball gate,
    NOT `constGate`), yielding `0 < a < b < c` with `c < ε`; then
      `b < c < ε ≤ r₀ ⟹ b < r₀`,  `c < ε ≤ δ₀ ⟹ c < δ₀`,  `b < c < ε ≤ ρ ⟹ b < ρ`,
    so every R6 antecedent fires.  The producer's own defect-bound conclusion is not consumed — only
    the gate ordering `0 < a < b < c` is harvested, so there is NO `constGate`/flow-ball object
    mismatch.  NON-VACUOUS: the producer's curved hypotheses {`hgnd`,`hframeK`,`hCoeffU0`,`hCoeffLin1`}
    are exactly the satisfiable curved bundle of `curvedRNC_heatOp_dom_pkg_prescribed`.  NOT `a₁ = R/6`
    — this closes only the `b < r₀` geometric carry of one `hCConv` sub-leg; `a₁ = R/6` remains
    CONDITIONAL on {hDuhamel, hDConv, hCConv}. -/
theorem hbint_bLtR0_closed_curved (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      ((∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          ContinuousOn (BL s) ({(0 : Point n)} : Set (Point n))) →
      (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          ∃ C : ℝ, ∀ z ∈ ({(0 : Point n)} : Set (Point n)), ‖BL s z *
            (⨆ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
                (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
                  '' Metric.ball (0 : Point n) c) a b i (t - s) y z) x‖)‖ ≤ C) →
      ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z *
          (⨆ x : Point n,
            ‖fderiv ℝ (fun y => witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
              (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
                '' Metric.ball (0 : Point n) c) a b i (t - s) y z) x‖)) volume) := by
  classical
  have hn0 : 0 < n := by omega
  haveI : Inhabited (Fin n) := ⟨⟨0, hn0⟩⟩
  haveI : Nontrivial (Point n) := Pi.nontrivial
  set K : Set (Point n) := {(0 : Point n)} with hKdef
  have hK : IsCompact K := isCompact_singleton
  have hKne : K.Nonempty := ⟨0, rfl⟩
  -- curved metric plumbing (mirrors `curvedRNC_heatOp_dom_pkg_prescribed`).
  have hg : ∀ (a b : Fin n), ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => curvedRNCMetric κ y a b) :=
    fun a b => curvedRNCMetric_contDiff κ a b
  have hgsymm : ∀ (y : Point n) a b, curvedRNCMetric κ y a b = curvedRNCMetric κ y b a :=
    fun y a b => curvedRNCMetric_symm κ y a b
  have hinvF : ∀ (y : Point n) a b,
      (∑ σ, curvedRNCMetric κ y a σ * curvedRNCInv κ y σ b) = if a = b then (1 : ℝ) else 0 :=
    fun y a b => curvedRNCMetric_hinvF κ hκ.le y a b
  have hg0 : ∀ i j, curvedRNCMetric κ (0 : Point n) i j = if i = j then (1 : ℝ) else 0 :=
    fun i j => curvedRNCMetric_zero κ i j
  have hdg0 : ∀ a b e, pd (fun y => curvedRNCMetric κ y a b) e (0 : Point n) = 0 :=
    fun a b e => QIQTH.GaussGaugeToHgauge.curvedRNCMetric_pd_zero κ a b e
  have hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => curvedRNCMetric κ y a b)) := by
    intro y
    rw [isUnit_matToCLM_iff (fun a b => curvedRNCMetric κ y a b), Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (curvedRNCMetric_det_pos κ hκ.le y).ne'
  have hframeK : ∀ q ∈ K, ∀ i j,
      curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0) := by
    intro q hq i j
    rw [hKdef] at hq
    rw [Set.mem_singleton_iff.mp hq]; exact hg0 i j
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck (curvedRNCMetric κ) (curvedRNCInv κ) hg hChr hK hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ))
      (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound (curvedRNCMetric κ) (curvedRNCInv κ) hg hChr hK hgnd hgsymm hinvF hframeK
      (vanVleck (curvedRNCMetric κ))
      (fun j => transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
        (curvedRNCMetric κ) (curvedRNCInv κ)) (j + 1)) (hw 1)
  set ρc : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρc := lt_min hρ0 hρ1
  -- the null frontier of `K = {0}`.
  have hnull : volume (frontier K) = 0 := by
    have hsub : frontier K ⊆ K := by
      rw [hKdef]
      have h := frontier_subset_closure (s := ({(0 : Point n)} : Set (Point n)))
      rwa [closure_singleton] at h
    exact measure_mono_null hsub (by rw [hKdef]; exact measure_singleton 0)
  -- the ∞-smoothness of the folded coefficient (for R6).
  have hwInf : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ) :=
    fun k => (hw k).of_le le_top
  -- R6: `r₀`,`δ₀` before `(a,b)`.
  obtain ⟨r₀, hr₀, δ₀, hδ₀, hR6⟩ :=
    hbint_interior_via_tube_cover_requant (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK hKne i t m BL
      hnull hwInf
  -- the flow radius, and the prescribed ceiling `ε := min r₀ (min δ₀ ρ)`.
  set ρ : ℝ := uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK with hρdef
  have hρpos : 0 < ρ := uniformFlowRadius_pos (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
  set ε : ℝ := min r₀ (min δ₀ ρ) with hεdef
  have hε : 0 < ε := lt_min hr₀ (lt_min hδ₀ hρpos)
  -- the prescribed-ceiling gate producer: harvest `0 < a < b < c` with `c < ε` (raw flow-ball gate).
  obtain ⟨a, b, C, c, ha, hab, -, hbc, hcε, -, -, -, -⟩ :=
    gatedWitnessN1_hEboundW_le_lin_CONST_prescribed (curvedRNCMetric κ) (curvedRNCInv κ) hg hChr hK
      hgnd hgsymm hinvF hframeK
      (vanVleck (curvedRNCMetric κ))
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
        (curvedRNCMetric κ) (curvedRNCInv κ)))
      hw ρc C0 C1 hρc0 hC0 hC1
      (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
      (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
      ε hε
  -- the three discharged R6 antecedents.
  have hbr₀ : b < r₀ := lt_of_lt_of_le (lt_trans hbc hcε) (min_le_left _ _)
  have hcδ₀ : c < δ₀ := lt_of_lt_of_le hcε (le_trans (min_le_right _ _) (min_le_left _ _))
  have hbρ : b < ρ := lt_of_lt_of_le (lt_trans hbc hcε) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨a, b, c, ha, hab, hbc, fun hBLK hbnd => ?_⟩
  exact hR6 a b ha hab hbρ c hbc hcδ₀ _ rfl hbr₀ hBLK hbnd

end QIQTH.HbintRequant

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HbintRequant
#print axioms witness_zero_offCore_requant
#print axioms fieldHessian_zero_offCore_requant
#print axioms fieldHessian_fderiv_eqZero_off_jointGraph_requant
#print axioms fieldHessian_vanish_off_concreteKx_requant
#print axioms hBFint_concrete_of_jointInteriorContinuous_requant
#print axioms hbint_concrete_via_interior_route_requant
#print axioms hbint_interior_via_tube_cover_requant
#print axioms hbint_bLtR0_closed_curved
end AxiomChecks
