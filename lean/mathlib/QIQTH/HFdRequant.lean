/-
  HFdRequant — the (a,b)-HOISTED replay of the `hFd` field-Hessian `⨆`-envelope tower, exposing the
  jet reach `δ₀` BEFORE the gate parameters `(a,b)`, closing the quantifier-order obstruction that
  blocked the FULL joint assembly of `MixedDirectionsFieldHessianEnvelope` at the curved witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick performs a
  MECHANICAL requantification (∃∀-swap) of the already-banked `hFd` reduction tower — no new analytic
  content — turning `hFd_concrete_ciSup_fully_closed` (which exposes `δ₀` only AFTER `(a,b)`) into a
  version that exposes an `(a,b)`-FREE `δ₀` first.  No `sorry`, no new axioms, no `:= True`, no vacuous
  hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY (the quantifier-order obstruction).

  The full joint inhabitation of `MixedDirectionsFieldHessianEnvelope` at `K = {0}` needs all five
  fields at a COMMON gate `(a,b,c, S = φ_·'' ball 0 c)`.  Four of them (`hbint`, `hzmass`, `hkint`,
  `hLevi`) hold for ANY parameters (null-support / tautological at `K = {0}`).  The fifth, `hFd`, holds
  only for `c < δ₀(a,b)`, and the mainline gate-parameter producer
  `gatedWitnessN1_hEboundW_le_lin_CONST_prescribed` returns `∃ a b C c` with `c < ε` for a PRESCRIBED
  `ε`, choosing `a,b` ITSELF — so setting `ε := δ₀(a,b)` is CIRCULAR.

  ## THE RESOLUTION — `hFd`'s `δ₀` is `(a,b)`-INDEPENDENT (provenance-audited, code-verified).

  Every radius feeding `hFd_concrete_ciSup_fully_closed`'s `δ₀` bottoms out in the `(a,b)`-FREE reaches
  `{uniformInverseChart_huniformChart, uniformFlowRadius, reachableGate_concrete}`; the parameters
  `a,b` enter ONLY the per-point proof bodies, never a radius.  So the reach can be HOISTED before
  `(a,b)`, exactly the pattern already validated by `HbintRequant` (J4-983) and `ReachRequant`/
  `CurvedA1ReachAlign` (J4-599).  The prerequisites `witness_offGate_requant` (ReachRequant) and
  `fieldHessian_zero_offCore_requant` (HbintRequant) are already banked `(a,b)`-free; this file completes
  the chain up to `hFd_concrete_ciSup_fully_closed_requant`.  With that reach in hand one prescribes
  `ε := δ₀` into the base producer and the circularity is gone.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HFdCoreContinuityClosed
import QIQTH.HGateBoundedConcreteDischarge
import QIQTH.GateFatExteriorConcreteDischarge
import QIQTH.HbintRequant
import QIQTH.ReachRequant
import QIQTH.ConcreteGateAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.OffSVanishing QIQTH.ChartJetHFdFrontierClosed
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.VanVleck
open scoped Topology BigOperators

namespace QIQTH.HFdRequant

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — frontier local-vanishing, `(a,b)`-free reach.
    ############################################################################### -/

/-- **★ `witness_frontier_requant`.**  Hoisted replay of
    `GateFatExteriorConcreteDischarge.witness_eventuallyEq_zero_frontier`: the field-slot witness
    vanishes on a neighbourhood of every frontier point of the concrete gate, with the reach `δ₀`
    exposed BEFORE `(a,b)` (`= min` of the `(a,b)`-free off-gate reach `witness_offGate_requant` and the
    chart reach).  NOT `a₁ = R/6`. -/
theorem witness_frontier_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (τ : ℝ) (z x : Point n), x ∈ frontier (S z) →
          (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) =ᶠ[nhds x] (fun _ => 0) := by
  obtain ⟨δ₁, hδ₁pos, hcollar⟩ := QIQTH.ReachRequant.witness_offGate_requant g gi hC hK
  obtain ⟨δ₂, hδ₂pos, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq τ z x hx
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  have hc0 : (0 : ℝ) < c := lt_trans hb0 hbc
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (min_le_right _ _)
  by_cases hzK : z ∈ K
  · have hopen : IsOpen (S z) := by
      rw [hSeq]; exact ((hchart z hzK).2 c hc0 hcδ₂).1
    have hxnotS : x ∉ S z := by
      have hsub : frontier (S z) ⊆ (S z)ᶜ := by
        rw [← frontier_compl]
        exact frontier_subset_closure.trans hopen.isClosed_compl.closure_eq.subset
      exact hsub hx
    exact hcollar a b ha hab c hbc hcδ₁ S hSeq τ z hzK x hxnotS
  · refine Filter.Eventually.of_forall (fun x' => ?_)
    show vanVleckGatedWitness g gi hC hK S a b τ x' z = 0
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hzK)

/-! ###############################################################################
    ### §2 — `GateFatExterior` discharge, `(a,b)`-free reach.
    ############################################################################### -/

/-- **★ `gateFatExterior_concrete_requant`.**  Hoisted replay of
    `GateFatExteriorConcreteDischarge.gateFatExterior_concrete` (reach from `witness_frontier_requant`).
    NOT `a₁ = R/6`. -/
theorem gateFatExterior_concrete_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (τ : ℝ) (z : Point n),
          GateFatExterior (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) (S z) := by
  obtain ⟨δ₀, hδ₀pos, hfront⟩ := witness_frontier_requant g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq i τ z x hx _hdiff
  have hwit : (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) =ᶠ[nhds x] (fun _ => 0) :=
    hfront a b ha hab c hbc hcδ S hSeq τ z x hx
  have hf0 : (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) =ᶠ[nhds x] (fun _ => 0) := by
    have hnest := (eventually_eventually_nhds (p := fun y =>
      (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) y = (fun _ => (0 : ℝ)) y)).mpr hwit
    filter_upwards [hnest] with y hy
    show pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y = 0
    rw [pd_congr_of_eventuallyEq _ _ i y hy]
    exact pd_zero_fun i y
  refine ⟨hf0.eq_of_nhds, (⇑(Pi.basisFun ℝ (Fin n))), (Pi.basisFun ℝ (Fin n)).span_eq, ?_⟩
  intro j
  have hcont : Continuous (fun s : ℝ => x + s • (Pi.basisFun ℝ (Fin n)) j) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hcurve : Filter.Tendsto (fun s : ℝ => x + s • (Pi.basisFun ℝ (Fin n)) j)
      (nhds 0) (nhds x) := by
    have h := hcont.tendsto 0
    simpa using h
  have hpre : ∀ᶠ s in nhds (0 : ℝ),
      (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z)
          (x + s • (Pi.basisFun ℝ (Fin n)) j) = 0 :=
    hcurve.eventually hf0
  exact hpre.filter_mono nhdsWithin_le_nhds

/-- **★ `hfat_concrete_requant`.**  Hoisted replay of `GateFatExteriorConcreteDischarge.hfat_concrete`.
    NOT `a₁ = R/6`. -/
theorem hfat_concrete_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (t : ℝ) (m : ℕ),
          ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ᵐ z ∂volume,
              GateFatExterior (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) (S z) := by
  obtain ⟨δ₀, hδ₀pos, hcg⟩ := gateFatExterior_concrete_requant g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq i t m
  refine Filter.Eventually.of_forall (fun s => ?_)
  intro _
  refine Filter.Eventually.of_forall (fun z => ?_)
  exact hcg a b ha hab c hbc hcδ S hSeq i (t - s) z

/-- **★ `hFd_reduces_to_gateBdd_requant`.**  Hoisted replay of
    `GateFatExteriorConcreteDischarge.hFd_concrete_ciSup_reduces_to_gateBdd`.  NOT `a₁ = R/6`. -/
theorem hFd_reduces_to_gateBdd_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ (i : Fin n) (t : ℝ) (m : ℕ),
      ∀ c : ℝ, b < c → c < δ₀ →
        ∀ (S : Point n → Set (Point n)),
          S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
              ∀ᵐ z ∂volume,
                BddAbove ((fun x =>
                  ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
                    '' S z)) →
          ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ᵐ z ∂volume, ∀ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
                ≤ ⨆ x' : Point n,
                    ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  obtain ⟨δ₀, hδ₀pos, hfat⟩ := hfat_concrete_requant g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro a b ha hab i t m c hbc hcδ S hSeq hgate
  exact witnessFieldHessian_hFd_ciSup_of_gateBdd_fatExterior
    g gi hC hK S a b i t m hgate (hfat a b ha hab c hbc hcδ S hSeq i t m)

/-! ###############################################################################
    ### §3 — gate-interior boundedness from core continuity, `(a,b)`-free reach.
    ############################################################################### -/

/-- **★ `hgate_coreCont_requant`.**  Hoisted replay of
    `HGateBoundedConcreteDischarge.hgate_concrete_of_coreContinuousOn` (reach `= min` of the
    `(a,b)`-free `fieldHessian_zero_offCore_requant` reach and `uniformFlowRadius`).  NOT `a₁ = R/6`. -/
theorem hgate_coreCont_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ (i : Fin n) (t : ℝ) (m : ℕ),
      ∀ c : ℝ, b < c → c < δ₀ →
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
  obtain ⟨δ₁, hδ₁pos, hoff⟩ := QIQTH.HbintRequant.fieldHessian_zero_offCore_requant g gi hC hK
  refine ⟨min δ₁ (uniformFlowRadius g gi hC hK),
    lt_min hδ₁pos (uniformFlowRadius_pos g gi hC hK), ?_⟩
  intro a b ha hab i t m c hbc hcδ S hSeq hcore
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcufr : c < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hbufr : b < uniformFlowRadius g gi hC hK := lt_trans hbc hcufr
  filter_upwards [hcore] with s hcores hsU
  filter_upwards [hcores hsU] with z hzcont
  by_cases hzK : z ∈ K
  · have hcpt : IsCompact (closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)) :=
      QIQTH.ChartJetXUniformBound.concreteGate_closure_isCompact g gi hC hK z hzK b hbufr
    have hbddcore : BddAbove ((fun x =>
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
          '' closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)) :=
      hcpt.bddAbove_image hzcont
    obtain ⟨M, _hM0, hM⟩ := QIQTH.ChartJetXUniformBound.xuniform_of_bddAbove_offClosure
      (fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
      (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)
      (fun x hx => by
        have hz0 := hoff a b ha hab c hbc hcδ₁ S hSeq i (t - s) z hzK x hx
        simp [hz0])
      hbddcore
    exact ⟨M, by rintro y ⟨x, _, rfl⟩; exact hM x⟩
  · refine ⟨0, ?_⟩
    rintro y ⟨x, _, rfl⟩
    have hz0 := QIQTH.HZMassIntegrabilityAttempt.witnessFieldHessian_fderiv_eqZero_of_base_notMem_K
      g gi hC hK S a b i (t - s) z hzK x
    simp [hz0]

/-- **★ `hFd_ciSup_of_coreCont_requant`.**  Hoisted replay of
    `HGateBoundedConcreteDischarge.hFd_concrete_ciSup_of_coreContinuousOn`, combining
    `hgate_coreCont_requant` and `hFd_reduces_to_gateBdd_requant`.  NOT `a₁ = R/6`. -/
theorem hFd_ciSup_of_coreCont_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ (i : Fin n) (t : ℝ) (m : ℕ),
      ∀ c : ℝ, b < c → c < δ₀ →
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
  obtain ⟨δ₁, hδ₁pos, hgatered⟩ := hgate_coreCont_requant g gi hC hK
  obtain ⟨δ₂, hδ₂pos, hFdred⟩ := hFd_reduces_to_gateBdd_requant g gi hC hK
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro a b ha hab i t m c hbc hcδ S hSeq hcore
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact hFdred a b ha hab i t m c hbc hcδ₂ S hSeq
    (hgatered a b ha hab i t m c hbc hcδ₁ S hSeq hcore)

/-! ###############################################################################
    ### §4 — a.e. core continuity, `(a,b)`-free reach.
    ############################################################################### -/

/-- **★ `hcore_discharged_requant`.**  Hoisted replay of
    `HFdCoreContinuityClosed.hcore_concrete_discharged` (reach `= min` of the `(a,b)`-free
    `reachableGate_concrete` reach and `uniformFlowRadius`; the per-point continuity
    `coreContinuousOn_pointwise` is reused verbatim, taking `a,b` only in its body).  Carries the
    standard metric premises `hg`/`hgpos`/`hu`.  NOT `a₁ = R/6`. -/
theorem hcore_discharged_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ (i : Fin n) (t : ℝ) (m : ℕ),
      ∀ c : ℝ, b < c → c < δ₀ →
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
  intro a b ha hab i t m c hbc hcδ S hSeq
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcδ₀ : c < δ₀ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcρ : c < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hbρ : b < uniformFlowRadius g gi hC hK := lt_trans hbc hcρ
  subst hSeq
  refine Filter.Eventually.of_forall (fun s hsmem => Filter.Eventually.of_forall (fun z => ?_))
  by_cases hzK : z ∈ K
  · obtain ⟨hopen, _hLI, hxfacts⟩ := hreach c hc0 hcδ₀ z hzK
    exact QIQTH.HFdCoreContinuityClosed.coreContinuousOn_pointwise g gi hC hK a b i (t - s) z c hbc
      hbρ hg hgpos hu (Or.inr ⟨hzK, hopen, fun x hxg => (hxfacts x hxg).2⟩)
  · exact QIQTH.HFdCoreContinuityClosed.coreContinuousOn_pointwise g gi hC hK a b i (t - s) z c hbc
      hbρ hg hgpos hu (Or.inl hzK)

/-! ###############################################################################
    ### §5 — ★★★ THE `hFd` field, `(a,b)`-FREE reach.
    ############################################################################### -/

/-- **★★★ `hFd_fully_closed_requant`.**  The (a,b)-HOISTED replay of J4-874's
    `HFdCoreContinuityClosed.hFd_concrete_ciSup_fully_closed`: the EXACT `hFd` field of
    `MixedDirectionsFieldHessianEnvelope` (`BF s z := ⨆ x', ‖fderiv …‖`) at the concrete flow-ball gate,
    with the jet reach `δ₀ > 0` exposed BEFORE the gate parameters `(a,b)`.  Composes
    `hcore_discharged_requant` with `hFd_ciSup_of_coreCont_requant`, carrying only the standard metric
    premises `hg`/`hgpos`/`hu`.  This is the reach that breaks the quantifier-order obstruction:
    prescribing `ε := δ₀` into `gatedWitnessN1_hEboundW_le_lin_CONST_prescribed` yields gate parameters
    `0 < a < b < c < δ₀` at which `hFd` fires.  NOT `a₁ = R/6`. -/
theorem hFd_fully_closed_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ (i : Fin n) (t : ℝ) (m : ℕ),
      ∀ c : ℝ, b < c → c < δ₀ →
        ∀ (S : Point n → Set (Point n)),
          S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
          ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ᵐ z ∂volume, ∀ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
                ≤ ⨆ x' : Point n,
                    ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  obtain ⟨δ₁, hδ₁, hcore⟩ := hcore_discharged_requant g gi hC hK hg hgpos hu
  obtain ⟨δ₂, hδ₂, hFd⟩ := hFd_ciSup_of_coreCont_requant g gi hC hK
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro a b ha hab i t m c hbc hcδ S hSeq
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact hFd a b ha hab i t m c hbc hcδ₂ S hSeq (hcore a b ha hab i t m c hbc hcδ₁ S hSeq)

end QIQTH.HFdRequant

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HFdRequant
#print axioms witness_frontier_requant
#print axioms gateFatExterior_concrete_requant
#print axioms hfat_concrete_requant
#print axioms hFd_reduces_to_gateBdd_requant
#print axioms hgate_coreCont_requant
#print axioms hFd_ciSup_of_coreCont_requant
#print axioms hcore_discharged_requant
#print axioms hFd_fully_closed_requant
end AxiomChecks
