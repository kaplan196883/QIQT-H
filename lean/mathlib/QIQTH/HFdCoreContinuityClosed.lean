/-
  HFdCoreContinuityClosed — J4-874: the CORE-CONTINUITY residual of J4-873's `hFd` reduction
  DISCHARGED unconditionally (modulo the standard metric-`C²` premises `hg`/`hgpos`/`hu`), CLOSING the
  `hFd` field of `MixedDirectionsFieldHessianEnvelope` on the concrete flow-ball gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick DISCHARGES the sole residual
  J4-873 (`HGateBoundedConcreteDischarge`) left in `MixedDirectionsFieldHessianEnvelope.hFd`: the
  field-Hessian norm CONTINUITY on the strictly-interior compact CORE `closure (φ_z '' ball 0 b)`.  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE — the field-Hessian norm is CONTINUOUS on the core, from metric `C²` alone.

  J4-873 reduced `hFd` to: a.e. `z`, the field-Hessian norm `x ↦ ‖fderiv (y ↦ witnessFieldDeriv … y z)
  x‖` is `ContinuousOn (closure (φ_z '' ball 0 b))`.  This brick CLOSES that continuity WITHOUT any
  carried chart-`C²` hypothesis, because the CONCRETE gate supplies chart-`C²` on EVERY gate point for
  free (`ConcreteGateAssembly.reachableGate_concrete`).  The chain:

    1. `pd_contDiffAt_one_of_two`  — if `F` is `ContDiffAt ℝ 2` at `x`, its `i`-th partial `pd F i` is
       `ContDiffAt ℝ 1` at `x` (near `x`, `pd F i = fderiv F · (eᵢ)` by `pd_eq_fderiv`; `fderiv F` is
       `C¹` by `ContDiffAt.fderiv_right`; `clm_apply` with a constant; `congr_of_eventuallyEq`).
    2. `fderiv_pd_norm_continuousAt` — hence `x ↦ ‖fderiv (pd F i) x‖` is `ContinuousAt` (via
       `ContDiffAt.continuousAt_fderiv` on the `C¹` partial, then `ContinuousAt.norm`).
    3. `core_subset_gate` — pure geometry: `closure (φ_z '' ball 0 b) ⊆ φ_z '' ball 0 c` (`b < c`,
       `b < uniformFlowRadius`), via image-of-compact-closedBall being closed.
    4. On the gate, `OnGateFieldRegularity.gatedWitness_contDiffAt_field` upgrades the chart-`C²` (from
       `reachableGate_concrete`) plus `hg`/`hgpos`/`hu` to `ContDiffAt ℝ 2` of the field witness; feed
       (2) at every core point ⟹ `ContinuousOn` on the core (`coreContinuousOn_pointwise`).
    5. Off `K` the field-Hessian is identically `0` (`witnessFieldHessian_fderiv_eqZero_of_base_notMem_K`),
       so the norm is the constant `0`, trivially `ContinuousOn`.

  Net (`hcore_concrete_discharged` ⟶ `hFd_concrete_ciSup_fully_closed`): the `hFd` `⨆`-bound holds a.e.
  for the concrete gate `S z = φ_z '' ball 0 c` for ALL `0 < a < b < c < δ₀`, carrying ONLY the standard
  metric premises `hg`/`hgpos`/`hu` (already standing on the live capstone) — no chart-`C²` carry, no
  gate-openness carry.  So `MixedDirectionsFieldHessianEnvelope.hFd` is CLOSED on the live order-1
  lineage.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HGateBoundedConcreteDischarge
import QIQTH.ConcreteGateAssembly
import QIQTH.OnGateFieldRegularity
import QIQTH.FlowJointContinuity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.OffSVanishing QIQTH.ChartJetHFdFrontierClosed
open QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.VanVleck
open scoped Topology BigOperators

namespace QIQTH.HFdCoreContinuityClosed

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### C0 — `pd` of a `C²` field is `C¹`; its Fréchet derivative's norm is continuous.
    ############################################################################### -/

/-- **★ `pd_contDiffAt_one_of_two`.**  If `F : Point n → ℝ` is `ContDiffAt ℝ 2` at `x`, then its `i`-th
    coordinate partial `y ↦ pd F i y` is `ContDiffAt ℝ 1` at `x`.  Near `x`, `pd F i = fderiv F · (eᵢ)`
    (`pd_eq_fderiv`, `F` differentiable near `x`); `fderiv F` is `C¹` (`ContDiffAt.fderiv_right`), and
    `clm_apply` with a constant keeps `C¹`; `congr_of_eventuallyEq` transports.  NOT `a₁ = R/6`. -/
theorem pd_contDiffAt_one_of_two (F : Point n → ℝ) (i : Fin n) (x : Point n)
    (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 1 (fun y => pd F i y) x := by
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y := by
    filter_upwards [hF.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have heq : (fun y => pd F i y) =ᶠ[𝓝 x] (fun y => (fderiv ℝ F y) (Pi.single i 1)) := by
    filter_upwards [hdiff] with y hy using pd_eq_fderiv F i y hy
  have hfd : ContDiffAt ℝ 1 (fun y => fderiv ℝ F y) x := hF.fderiv_right (m := 1) (by norm_num)
  have hcontFd : ContDiffAt ℝ 1 (fun y => (fderiv ℝ F y) (Pi.single i 1)) x :=
    hfd.clm_apply contDiffAt_const
  exact hcontFd.congr_of_eventuallyEq heq

/-- **★ `fderiv_pd_norm_continuousAt`.**  If `F` is `ContDiffAt ℝ 2` at `x`, then the norm of the
    Fréchet derivative of its partial `pd F i` is `ContinuousAt` `x`.  From `pd_contDiffAt_one_of_two`,
    `ContDiffAt.continuousAt_fderiv`, and `ContinuousAt.norm`.  NOT `a₁ = R/6`. -/
theorem fderiv_pd_norm_continuousAt (F : Point n → ℝ) (i : Fin n) (x : Point n)
    (hF : ContDiffAt ℝ 2 F x) :
    ContinuousAt (fun y => ‖fderiv ℝ (fun y' => pd F i y') y‖) x :=
  ((pd_contDiffAt_one_of_two F i x hF).continuousAt_fderiv (by norm_num)).norm

/-! ###############################################################################
    ### C1 — the core geometry: `closure (φ_z '' ball 0 b) ⊆ φ_z '' ball 0 c`.
    ############################################################################### -/

/-- **★ `gate_closedBall_isCompact`.**  For `z ∈ K` and `b < uniformFlowRadius`, the image of the
    compact closed ball `closedBall 0 b` under the base-`z` uniform flow map is compact (the flow map is
    `ContinuousOn` the closed ball via `uniformFlowExp_joint_continuousOn`).  NOT `a₁ = R/6`. -/
theorem gate_closedBall_isCompact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K)
    (b : ℝ) (hb : b < uniformFlowRadius g gi hC hK) :
    IsCompact (uniformFlowExp g gi hC hK z '' Metric.closedBall 0 b) := by
  have hmaps : Set.MapsTo (fun w : Point n => (z, w)) (Metric.closedBall 0 b)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    exact ⟨hz, by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_le_of_lt hw hb⟩
  have hincl : ContinuousOn (fun w : Point n => (z, w)) (Metric.closedBall 0 b) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hcontOn : ContinuousOn (uniformFlowExp g gi hC hK z) (Metric.closedBall 0 b) :=
    (QIQTH.FlowJointContinuity.uniformFlowExp_joint_continuousOn g gi hC hK).comp hincl hmaps
  exact (isCompact_closedBall (0 : Point n) b).image_of_continuousOn hcontOn

/-- **★ `core_subset_gate`.**  Pure geometry: the compact CORE `closure (φ_z '' ball 0 b)` is contained
    in the OPEN gate `φ_z '' ball 0 c` whenever `b < c` and `b < uniformFlowRadius` (`z ∈ K`).  The
    image of the compact `closedBall 0 b` is closed, so `closure (φ_z '' ball 0 b) ⊆ φ_z '' closedBall
    0 b ⊆ φ_z '' ball 0 c` (`closedBall 0 b ⊆ ball 0 c` since `b < c`).  NOT `a₁ = R/6`. -/
theorem core_subset_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K)
    (b c : ℝ) (hbc : b < c) (hb : b < uniformFlowRadius g gi hC hK) :
    closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)
      ⊆ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c := by
  have hcpt := gate_closedBall_isCompact g gi hC hK z hz b hb
  have h1 : closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)
      ⊆ uniformFlowExp g gi hC hK z '' Metric.closedBall (0 : Point n) b :=
    closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hcpt.isClosed
  have h2 : uniformFlowExp g gi hC hK z '' Metric.closedBall (0 : Point n) b
      ⊆ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c :=
    Set.image_mono (Metric.closedBall_subset_ball hbc)
  exact h1.trans h2

/-! ###############################################################################
    ### C2 — the POINTWISE core-continuity (all `z`, no chart-`C²` carry).
    ############################################################################### -/

/-- **★★ `coreContinuousOn_pointwise`.**  For EVERY base `z` (no a.e. exceptional set), the field-Hessian
    norm is `ContinuousOn` the compact CORE `closure (φ_z '' ball 0 b)` at the concrete gate `S z =
    φ_z '' ball 0 c` (`b < c`, `b < uniformFlowRadius`), given the pure gate dichotomy `hzcase`
    (`z ∉ K`, OR `z ∈ K` with the gate open and chart-`C²` on every gate point — both supplied by
    `reachableGate_concrete`).  For `z ∉ K` the field-Hessian is `0` (constant norm); for `z ∈ K` each
    core point lies in the gate (`core_subset_gate`), so `gatedWitness_contDiffAt_field` gives
    `ContDiffAt ℝ 2` of the field witness there, feeding `fderiv_pd_norm_continuousAt`.  NOT `a₁ = R/6`. -/
theorem coreContinuousOn_pointwise (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (c : ℝ) (hbc : b < c)
    (hb : b < uniformFlowRadius g gi hC hK)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hzcase : z ∉ K
      ∨ (z ∈ K
          ∧ IsOpen (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
          ∧ ∀ x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c,
              ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x)) :
    ContinuousOn
      (fun x => ‖fderiv ℝ (fun y =>
        witnessFieldDeriv g gi hC hK
          (fun w => uniformFlowExp g gi hC hK w '' Metric.ball (0 : Point n) c) a b i τ y z) x‖)
      (closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)) := by
  rcases hzcase with hzK | ⟨hzK, hSopen, hchart⟩
  · -- `z ∉ K`: the field-Hessian is identically `0`, so its norm is the constant `0`.
    have hzero : (fun x => ‖fderiv ℝ (fun y =>
        witnessFieldDeriv g gi hC hK
          (fun w => uniformFlowExp g gi hC hK w '' Metric.ball (0 : Point n) c) a b i τ y z) x‖)
        = fun _ => (0 : ℝ) := by
      funext x
      rw [QIQTH.HZMassIntegrabilityAttempt.witnessFieldHessian_fderiv_eqZero_of_base_notMem_K
        g gi hC hK (fun w => uniformFlowExp g gi hC hK w '' Metric.ball (0 : Point n) c)
        a b i τ z hzK x]
      exact norm_zero
    rw [hzero]; exact continuousOn_const
  · -- `z ∈ K`: every core point lies in the gate; upgrade chart-`C²` to `ContDiffAt ℝ 2` of the witness.
    intro x hx
    have hxg : x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c :=
      core_subset_gate g gi hC hK z hzK b c hbc hb hx
    have hW : ContDiffAt ℝ 2 (fun x' =>
        vanVleckGatedWitness g gi hC hK
          (fun w => uniformFlowExp g gi hC hK w '' Metric.ball (0 : Point n) c) a b τ x' z) x :=
      QIQTH.OnGateFieldRegularity.gatedWitness_contDiffAt_field g gi hC hK
        (fun w => uniformFlowExp g gi hC hK w '' Metric.ball (0 : Point n) c) a b τ z x hzK hxg
        hSopen (hchart x hxg) hg hgpos hu
    exact (fderiv_pd_norm_continuousAt
      (fun x' => vanVleckGatedWitness g gi hC hK
        (fun w => uniformFlowExp g gi hC hK w '' Metric.ball (0 : Point n) c) a b τ x' z)
      i x hW).continuousWithinAt

/-! ###############################################################################
    ### C3 — the a.e. core-continuity, DISCHARGED unconditionally (mod `hg`/`hgpos`/`hu`).
    ############################################################################### -/

/-- **★★★ J4-874 — `hcore_concrete_discharged`.**  The EXACT core-continuity residual of J4-873's
    `hFd_concrete_ciSup_of_coreContinuousOn` (a.e. `s`, a.e. `z`: the field-Hessian norm is
    `ContinuousOn` the compact core), DISCHARGED unconditionally for the concrete flow-ball gate,
    carrying ONLY the standard metric premises `hg`/`hgpos`/`hu`.  Holds for ALL `z` — on-`K` via the
    reachable-gate chart-`C²`, off-`K` via the vanishing field-Hessian — so the a.e. statement is
    `Eventually.of_forall`.  NOT `a₁ = R/6`. -/
theorem hcore_concrete_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (i : Fin n) (t : ℝ) (m : ℕ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          ∀ᵐ z ∂volume,
            ContinuousOn
              (fun x =>
                ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
              (closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)) := by
  obtain ⟨δ₀, hδ₀, hreach⟩ := QIQTH.ConcreteGateAssembly.reachableGate_concrete g gi hC hK
  refine ⟨min δ₀ (uniformFlowRadius g gi hC hK),
    lt_min hδ₀ (uniformFlowRadius_pos g gi hC hK), ?_⟩
  intro c hbc hcδ S hSeq
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcδ₀ : c < δ₀ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcρ : c < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hbρ : b < uniformFlowRadius g gi hC hK := lt_trans hbc hcρ
  subst hSeq
  refine Filter.Eventually.of_forall (fun s hsmem => Filter.Eventually.of_forall (fun z => ?_))
  by_cases hzK : z ∈ K
  · obtain ⟨hopen, _hLI, hxfacts⟩ := hreach c hc0 hcδ₀ z hzK
    exact coreContinuousOn_pointwise g gi hC hK a b i (t - s) z c hbc hbρ hg hgpos hu
      (Or.inr ⟨hzK, hopen, fun x hxg => (hxfacts x hxg).2⟩)
  · exact coreContinuousOn_pointwise g gi hC hK a b i (t - s) z c hbc hbρ hg hgpos hu (Or.inl hzK)

/-! ###############################################################################
    ### C4 — THE `hFd` FIELD, FULLY CLOSED on the concrete gate.
    ############################################################################### -/

/-- **★★★ J4-874 — `hFd_concrete_ciSup_fully_closed`.**  The EXACT `hFd` field of
    `MixedDirectionsFieldHessianEnvelope` (`BF s z := ⨆ x', ‖fderiv …‖`) at the concrete flow-ball gate,
    now FULLY DISCHARGED: a.e. `s`, a.e. `z`, every field-Hessian norm is `≤` the finite `⨆`, carrying
    ONLY the standard metric premises `hg`/`hgpos`/`hu`.  Composes `hcore_concrete_discharged` (this
    file, the core-continuity discharge) with J4-873's
    `HGateBoundedConcreteDischarge.hFd_concrete_ciSup_of_coreContinuousOn` (collar + compactness + frontier
    reduction).  So `hFd` is CLOSED on the live order-1 lineage — no chart-`C²` carry, no gate-openness
    carry, no boundedness carry.  NOT `a₁ = R/6`. -/
theorem hFd_concrete_ciSup_fully_closed (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (i : Fin n) (t : ℝ) (m : ℕ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          ∀ᵐ z ∂volume, ∀ x : Point n,
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
              ≤ ⨆ x' : Point n,
                  ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  obtain ⟨δ₁, hδ₁, hcore⟩ :=
    hcore_concrete_discharged g gi hC hK a b ha hab i t m hg hgpos hu
  obtain ⟨δ₂, hδ₂, hFd⟩ :=
    QIQTH.HGateBoundedConcreteDischarge.hFd_concrete_ciSup_of_coreContinuousOn
      g gi hC hK a b ha hab i t m
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro c hbc hcδ S hSeq
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact hFd c hbc hcδ₂ S hSeq (hcore c hbc hcδ₁ S hSeq)

end QIQTH.HFdCoreContinuityClosed

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HFdCoreContinuityClosed
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms pd_contDiffAt_one_of_two
#print axioms fderiv_pd_norm_continuousAt
#print axioms gate_closedBall_isCompact
#print axioms core_subset_gate
#print axioms coreContinuousOn_pointwise
#print axioms hcore_concrete_discharged
#print axioms hFd_concrete_ciSup_fully_closed
end AxiomChecks
