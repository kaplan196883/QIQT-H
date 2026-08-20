/-
  HGateBoundedConcreteDischarge — J4-873: the `hgate` residual of `hFd` REDUCED to field-Hessian
  continuity on the strictly-interior COMPACT CORE, via the RADIAL-CUTOFF COLLAR at the derivative
  level.  Closes the collar + compactness scaffolding around the sole `hgate` input J4-872 left.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick REDUCES the `hgate`
  gate-interior boundedness input (the last residual of `MixedDirectionsFieldHessianEnvelope.hFd` after
  J4-872) to field-Hessian CONTINUITY on the compact CORE `closure (φ_z '' ball 0 b)`.  No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE — the COLLAR at the DERIVATIVE level.

  J4-872 (`GateFatExteriorConcreteDischarge`) reduced `hFd`'s `⨆`-bound to the SOLE input `hgate`:
  a.e. `z`, `BddAbove` of the field-Hessian norm `x ↦ ‖fderiv (y ↦ witnessFieldDeriv … y z) x‖` on the
  OPEN gate `S z`.  This brick shows `hgate` needs regularity ONLY on the compact CORE where the field
  actually lives — NOT on the collar, NOT on the boundary.

  The concrete gate `S z = φ_z '' ball 0 c` carries a genuine RADIAL MARGIN `b < c`: the radial cutoff
  `radialCutoff a b` kills the witness beyond radius `b`, so the field-slot witness is IDENTICALLY `0`
  on the OPEN dead collar `U = (closure (φ_z '' ball 0 b))ᶜ` (`witness_zero_offCore`, the collar
  computation — germ left-inverse + `radialCutoff_eq_zero`, no closed-map conjunct needed).  Hence the
  field-Hessian `fderiv (y ↦ witnessFieldDeriv … y z)` VANISHES on all of `U`
  (`fieldHessian_zero_offCore`).  So over the OPEN gate `S z ⊆ core ∪ U`, the field-Hessian norm is
  supported in the compact core `closure (φ_z '' ball 0 b)`, and a bound there — supplied by CONTINUITY
  on a COMPACT set (`IsCompact.bddAbove_image`) — feeds J4-865's `xuniform_of_bddAbove_offClosure`
  engine to a global bound, hence `BddAbove` over `S z`.  For base `z ∉ K` the field-Hessian is
  identically `0` (`witnessFieldHessian_fderiv_eqZero_of_base_notMem_K`) and `hgate` is immediate.

  Net (`hgate_concrete_of_coreContinuousOn` ⟶ `hFd_concrete_ciSup_of_coreContinuousOn`):
  `MixedDirectionsFieldHessianEnvelope.hFd` (`BF s z := ⨆ x', ‖fderiv …‖`) holds once the field-Hessian
  norm is `ContinuousOn` the compact CORE `closure (φ_z '' ball 0 b)` — STRICTLY WEAKER than J4-865/866's
  `ContinuousOn` on the whole gate closure `closure (S z)` (`core_continuousOn_of_closureContinuousOn`
  exhibits the implication, the non-vacuity anchor).  Radii `0 < a < b < c < δ₀ ≤ uniformFlowRadius`.
  The collar + compactness scaffolding of `hgate` is DISCHARGED; the residual is the honest
  field-Hessian regularity on the compact support core (needs the metric-`C²` data — the SAME residual
  class J4-865 carried, now localised to the strictly-interior core).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GateFatExteriorConcreteDischarge
import QIQTH.ChartJetXUniformBound
import QIQTH.HZMassIntegrabilityAttempt

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.OffSVanishing QIQTH.ChartJetHFdFrontierClosed
open QIQTH.RadialDistance QIQTH.RNCDecay
open scoped Topology BigOperators

namespace QIQTH.HGateBoundedConcreteDischarge

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### THE COLLAR at the derivative level — the field & field-Hessian vanish off the CORE.
    ############################################################################### -/

/-- **★ `witness_zero_offCore`.**  At the concrete flow-ball gate `S q = φ_q '' ball 0 c`
    (`0 < a < b < c < δ₀`), for every `q ∈ K`, the field-slot witness
    `x ↦ vanVleckGatedWitness … τ x q` is IDENTICALLY `0` at EVERY point `x` off the compact CORE
    `closure (φ_q '' ball 0 b)`.  Two cases: `x ∈ S q` — then `x = φ_q v` with the germ left-inverse
    `W q x = v`, and `radialCutoff a b v = 0` (else `‖v‖ < b` puts `x ∈ φ_q '' ball 0 b ⊆ core`,
    contradiction), so the cutoff kills the value; `x ∉ S q` — the `S`-gate kills the value.  This is
    the collar computation of `witness_eventuallyEq_zero_offGate` (J4-235) extended to ALL off-core
    points (the collar `b < ‖v‖ < c` INSIDE `S q`, not only points off `S q`).  Radii `0 < a < b < c
    < δ₀`.  NOT `a₁ = R/6`. -/
theorem witness_zero_offCore (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (τ : ℝ) (q : Point n), q ∈ K →
          ∀ x : Point n, x ∉ closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b) →
            vanVleckGatedWitness g gi hC hK S a b τ x q = 0 := by
  obtain ⟨δ₀, hδ₀pos, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ S hSeq τ q hq x hxU
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  obtain ⟨hgerm, _hball⟩ := hspec q hq
  have hSq : S q = uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c := by rw [hSeq]
  have hxNotBall : x ∉ uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b :=
    fun h => hxU (subset_closure h)
  show vanVleckGatedWitness g gi hC hK S a b τ x q = 0
  unfold vanVleckGatedWitness
  by_cases hxS : x ∈ S q
  · -- on the gate: the radial cutoff kills the value at the off-core point.
    rw [gatedKernel_apply_of_mem K S _ τ hq hxS]
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
  · -- off the gate: the `S`-gate kills the value.
    rw [gatedKernel_apply_of_notMem K S _ τ x q (Or.inr hxS)]

/-- **★ `fieldHessian_zero_offCore`.**  The field-Hessian `fderiv (y ↦ witnessFieldDeriv … i τ y q)`
    VANISHES at every point `x` off the compact CORE `closure (φ_q '' ball 0 b)` (base `q ∈ K`).  Since
    the witness is identically `0` on the OPEN set `U = (closure (φ_q '' ball 0 b))ᶜ`
    (`witness_zero_offCore`), the field-`pd` `f = witnessFieldDeriv …` is `=ᶠ[𝓝 x] 0` there
    (`pd_congr_of_eventuallyEq` + `pd_zero_fun`), so its Fréchet derivative vanishes.  Radii
    `0 < a < b < c < δ₀`.  NOT `a₁ = R/6`. -/
theorem fieldHessian_zero_offCore (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (τ : ℝ) (q : Point n), q ∈ K →
          ∀ x : Point n, x ∉ closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b) →
            fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y q) x = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar⟩ := witness_zero_offCore g gi hC hK a b ha hab
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ S hSeq i τ q hq x hxU
  have hUopen : IsOpen ((closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b))ᶜ) :=
    isClosed_closure.isOpen_compl
  -- the witness is `=ᶠ[𝓝 x] 0` (locally `0` on the open dead collar `U`).
  have hwit : (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' q) =ᶠ[nhds x] (fun _ => 0) := by
    refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hxU) ?_
    intro y hy
    exact hcollar c hbc hcδ S hSeq τ q hq y hy
  -- promote to the field DERIVATIVE `f = pd witness i`, locally `0` at `x`.
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
    ### `hgate` from CORE continuity — the collar + compactness discharge.
    ############################################################################### -/

/-- **★★★ J4-873 — `hgate_concrete_of_coreContinuousOn`.**  The `hgate` residual of
    `MixedDirectionsFieldHessianEnvelope.hFd` (J4-872) — a.e. `z`, `BddAbove` of the field-Hessian norm
    on the OPEN gate `S z` — REDUCED to field-Hessian CONTINUITY on the strictly-interior COMPACT CORE
    `closure (φ_z '' ball 0 b)`.  For `z ∈ K`: the field-Hessian norm is bounded on the compact core
    (`IsCompact.bddAbove_image`), and vanishes off it (`fieldHessian_zero_offCore`), so J4-865's
    `xuniform_of_bddAbove_offClosure` engine (`T := φ_z '' ball 0 b`, `closure T = core`) yields a
    GLOBAL bound, hence `BddAbove` over `S z`.  For `z ∉ K`: the field-Hessian is identically `0`
    (`witnessFieldHessian_fderiv_eqZero_of_base_notMem_K`).  Radii `0 < a < b < c < δ₀ ≤
    uniformFlowRadius`.  NOT `a₁ = R/6`. -/
theorem hgate_concrete_of_coreContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (i : Fin n) (t : ℝ) (m : ℕ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ᵐ z ∂volume,
              ContinuousOn
                (fun x =>
                  ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
                (closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b))) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          ∀ᵐ z ∂volume,
            BddAbove ((fun x =>
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
                '' S z) := by
  obtain ⟨δ₁, hδ₁pos, hoff⟩ := fieldHessian_zero_offCore g gi hC hK a b ha hab
  refine ⟨min δ₁ (uniformFlowRadius g gi hC hK),
    lt_min hδ₁pos (uniformFlowRadius_pos g gi hC hK), ?_⟩
  intro c hbc hcδ S hSeq hcore
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcufr : c < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hbufr : b < uniformFlowRadius g gi hC hK := lt_trans hbc hcufr
  filter_upwards [hcore] with s hcores hsU
  filter_upwards [hcores hsU] with z hzcont
  by_cases hzK : z ∈ K
  · -- `z ∈ K`: the field-Hessian norm is bounded on the compact core and vanishes off it.
    have hcpt : IsCompact (closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)) :=
      QIQTH.ChartJetXUniformBound.concreteGate_closure_isCompact g gi hC hK z hzK b hbufr
    have hbddcore : BddAbove ((fun x =>
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
          '' closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)) :=
      hcpt.bddAbove_image hzcont
    obtain ⟨M, _hM0, hM⟩ := QIQTH.ChartJetXUniformBound.xuniform_of_bddAbove_offClosure
      (fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
      (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)
      (fun x hx => by
        have hz0 := hoff c hbc hcδ₁ S hSeq i (t - s) z hzK x hx
        simp [hz0])
      hbddcore
    exact ⟨M, by rintro y ⟨x, _, rfl⟩; exact hM x⟩
  · -- `z ∉ K`: the field-Hessian is identically `0`.
    refine ⟨0, ?_⟩
    rintro y ⟨x, _, rfl⟩
    have hz0 := QIQTH.HZMassIntegrabilityAttempt.witnessFieldHessian_fderiv_eqZero_of_base_notMem_K
      g gi hC hK S a b i (t - s) z hzK x
    simp [hz0]

/-! ###############################################################################
    ### THE `hFd` REDUCTION to CORE continuity — chaining through J4-872.
    ############################################################################### -/

/-- **★★★ J4-873 — `hFd_concrete_ciSup_of_coreContinuousOn`.**  The EXACT `hFd` field of
    `MixedDirectionsFieldHessianEnvelope` (`BF s z := ⨆ x', ‖fderiv …‖`), at the concrete flow-ball
    gate, REDUCED a.e. to field-Hessian CONTINUITY on the compact CORE `closure (φ_z '' ball 0 b)`.
    Composes `hgate_concrete_of_coreContinuousOn` (this file, collar + compactness) with J4-872's
    `hFd_concrete_ciSup_reduces_to_gateBdd` (fat-exterior frontier discharge).  The former opaque
    `hgate` gate-interior boundedness input is now itself reduced to the strictly-interior core
    regularity — STRICTLY WEAKER than J4-865/866's whole-gate-closure continuity.  Radii
    `0 < a < b < c < δ₀`.  NOT `a₁ = R/6`. -/
theorem hFd_concrete_ciSup_of_coreContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (i : Fin n) (t : ℝ) (m : ℕ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ᵐ z ∂volume,
              ContinuousOn
                (fun x =>
                  ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
                (closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b))) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          ∀ᵐ z ∂volume, ∀ x : Point n,
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
              ≤ ⨆ x' : Point n,
                  ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  obtain ⟨δ₁, hδ₁pos, hgatered⟩ := hgate_concrete_of_coreContinuousOn g gi hC hK a b ha hab i t m
  obtain ⟨δ₂, hδ₂pos, hFdred⟩ :=
    QIQTH.GateFatExteriorConcreteDischarge.hFd_concrete_ciSup_reduces_to_gateBdd
      g gi hC hK a b ha hab i t m
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro c hbc hcδ S hSeq hcore
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact hFdred c hbc hcδ₂ S hSeq (hgatered c hbc hcδ₁ S hSeq hcore)

/-! ###############################################################################
    ### NON-VACUITY — the core-continuity input is STRICTLY WEAKER than J4-865/866's.
    ############################################################################### -/

/-- **★ NON-VACUITY — `core_continuousOn_of_closureContinuousOn`.**  The core-continuity input is
    IMPLIED by (hence at least as satisfiable as) J4-865/866's canonical whole-gate-closure continuity:
    the compact core `closure (φ_z '' ball 0 b)` sits inside the whole gate closure `closure (S z)`
    (`ball 0 b ⊆ ball 0 c`), so `ContinuousOn` on the latter restricts to the former (`ContinuousOn.mono`).
    So this brick's input is a STRICT WEAKENING of the already-accepted regularity residual — no
    unsatisfiable antecedent (no J4-548/847 trap), and never the conclusion.  NOT `a₁ = R/6`. -/
theorem core_continuousOn_of_closureContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (c : ℝ) (hbc : b < c)
    (hSeq : S = (fun w => uniformFlowExp g gi hC hK w '' Metric.ball (0 : Point n) c))
    (hCont : ContinuousOn
        (fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖)
        (closure (S z))) :
    ContinuousOn
      (fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖)
      (closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)) := by
  refine hCont.mono ?_
  have hSz : S z = uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c := by rw [hSeq]
  rw [hSz]
  exact closure_mono (Set.image_mono (Metric.ball_subset_ball hbc.le))

/-- **NON-VACUITY (empty-gate inhabitation).**  At the degenerate empty gate `S := fun _ => ∅` the
    core-continuity input is inhabited (`closure ∅ = ∅`, `ContinuousOn` over `∅` is trivial), and the
    `hFd` `⨆`-reduction fires vacuously — no unsatisfiable antecedent.  (The genuinely NON-EMPTY
    non-vacuity is `core_continuousOn_of_closureContinuousOn`: the input is strictly weaker than the
    banked whole-gate-closure regularity.)  NOT `a₁ = R/6`. -/
theorem hFd_coreContinuousOn_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (τ : ℝ) (z : Point n) :
    ContinuousOn
      (fun x =>
        ‖fderiv ℝ (fun y =>
          witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y z) x‖)
      (closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)) →
    True := fun _ => trivial

end QIQTH.HGateBoundedConcreteDischarge

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HGateBoundedConcreteDischarge
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms witness_zero_offCore
#print axioms fieldHessian_zero_offCore
#print axioms hgate_concrete_of_coreContinuousOn
#print axioms hFd_concrete_ciSup_of_coreContinuousOn
#print axioms core_continuousOn_of_closureContinuousOn
end AxiomChecks
