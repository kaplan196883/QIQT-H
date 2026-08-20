/-
  GateFatExteriorConcreteDischarge — J4-872: the `GateFatExterior` predicate GENUINELY DISCHARGED for
  the CONCRETE flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`, closing the
  `hfat` residual J4-870 isolated from `MixedDirectionsFieldHessianEnvelope.hFd`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick DISCHARGES the
  `GateFatExterior` gate-geometry input of J4-870's fat-exterior `hFd` reduction, at the concrete
  flow-ball gate.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none
  equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE — the COLLAR route (no invariance-of-domain / open-map / half-space geometry).

  J4-870 (`ChartJetHFdFrontierClosed`) reduced `hFd` to the fat-exterior predicate `GateFatExterior`:
  at every frontier point `x` of the gate where the field-derivative `f := fun y => witnessFieldDeriv …`
  is differentiable, `f x = 0` AND `f` vanishes eventually along a SPANNING family of one-sided rays.
  J4-871 (`UniformFlowExpGlobalInjectivity`) supplied global injectivity of `uniformFlowExp`, expecting
  a hard boundary-cone construction (open map ⟹ frontier = image of sphere ⟹ exterior half-space of
  directions at each boundary point).

  This brick shows that construction is UNNECESSARY.  The gate is chosen with a genuine RADIAL MARGIN
  `b < c`: the witness field is supported inside `closure (φ_z '' ball 0 b)` (radial cutoff `radialCutoff
  a b` kills it beyond radius `b`), whose closure sits INSIDE the gate `S z = φ_z '' ball 0 c`
  (`closedBall 0 b ⊆ ball 0 c`).  Hence the gate's topological boundary `frontier (S z)` lies entirely in
  the OPEN dead collar `(closure (φ_z '' ball 0 b))ᶜ`, on which the witness is IDENTICALLY `0` — this is
  exactly `OffSVanishing.witness_eventuallyEq_zero_offGate` (J4-235): since `S z` is OPEN
  (`uniformInverseChart_huniformChart`), a frontier point `x` is off the gate (`x ∉ S z`), so the collar
  lemma gives `witness =ᶠ[𝓝 x] 0`, hence the field-derivative `f = pd witness i =ᶠ[𝓝 x] 0`.

  With `f` locally `≡ 0` near `x`, the fat-exterior data is IMMEDIATE and FULL (not merely a half-space):
    • `f x = 0`                         — `EventuallyEq.eq_of_nhds`;
    • spanning directions               — the WHOLE standard basis `Pi.basisFun` (span `⊤`);
    • one-sided vanishing along each     — `f (x + t • eⱼ) = 0` for ALL directions and all small `t > 0`,
      because the ray stays in the open nbhd on which `f ≡ 0` (continuity of `t ↦ x + t • eⱼ` at `0`).

  For base points `z ∉ K` the gate `q ∉ K` branch of `gatedKernel` makes the witness identically `0`
  everywhere, so `f ≡ 0` and the same data applies with no gate geometry at all.

  Net: `GateFatExterior (fun y => witnessFieldDeriv … i τ y z) (S z)` holds for EVERY `z`, every `i`,
  every `τ` — so `hFd`'s fat-exterior input is fully discharged, and `hFd`'s `⨆`-bound now reduces to the
  single remaining gate-interior boundedness input `hgate` (`hFd_concrete_ciSup_reduces_to_gateBdd`).
  Radii carried honestly: `0 < a < b < c < δ₀`, `δ₀` the single uniform chart radius.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetHFdFrontierClosed
import QIQTH.OffSVanishing

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.OffSVanishing QIQTH.ChartJetHFdFrontierClosed
open scoped Topology BigOperators

namespace QIQTH.GateFatExteriorConcreteDischarge

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### The unified off-gate local-vanishing helper (both `z ∈ K` and `z ∉ K`).
    ############################################################################### -/

/-- **The field-slot witness vanishes on a neighbourhood of every frontier point of the concrete gate.**
    For `z ∈ K`: the gate `S z` is open (`uniformInverseChart_huniformChart`), so a frontier point `x` is
    off the gate; the collar lemma `witness_eventuallyEq_zero_offGate` then gives local vanishing.  For
    `z ∉ K`: the `q ∉ K` branch of `gatedKernel` makes the witness identically `0`, so it vanishes near
    every point.  Radii `0 < a < b < c < δ₀`. -/
theorem witness_eventuallyEq_zero_frontier (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (τ : ℝ) (z x : Point n), x ∈ frontier (S z) →
          (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) =ᶠ[nhds x] (fun _ => 0) := by
  obtain ⟨δ₁, hδ₁pos, hcollar⟩ := witness_eventuallyEq_zero_offGate g gi hC hK a b ha hab
  obtain ⟨δ₂, hδ₂pos, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro c hbc hcδ S hSeq τ z x hx
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  have hc0 : (0 : ℝ) < c := lt_trans hb0 hbc
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (min_le_right _ _)
  by_cases hzK : z ∈ K
  · -- `z ∈ K`: the gate is open, so the frontier point is off the gate; collar lemma fires.
    have hopen : IsOpen (S z) := by
      rw [hSeq]; exact ((hchart z hzK).2 c hc0 hcδ₂).1
    have hxnotS : x ∉ S z := by
      have hsub : frontier (S z) ⊆ (S z)ᶜ := by
        rw [← frontier_compl]
        exact frontier_subset_closure.trans hopen.isClosed_compl.closure_eq.subset
      exact hsub hx
    exact hcollar c hbc hcδ₁ S hSeq τ z hzK x hxnotS
  · -- `z ∉ K`: the `q ∉ K` gate branch kills the witness everywhere.
    refine Filter.Eventually.of_forall (fun x' => ?_)
    show vanVleckGatedWitness g gi hC hK S a b τ x' z = 0
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hzK)

/-! ###############################################################################
    ### The concrete-gate `GateFatExterior` discharge.
    ############################################################################### -/

/-- **★★ J4-872 — `gateFatExterior_concrete`: `GateFatExterior` DISCHARGED at the concrete flow-ball
    gate.**  For every `z`, every field-slot direction `i`, and every time `τ`, the witness field
    derivative `f := fun y => witnessFieldDeriv g gi hC hK S a b i τ y z` satisfies the fat-exterior
    predicate on the concrete gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`.

    Mechanism (collar): at a frontier point `x`, `witness =ᶠ[𝓝 x] 0` (`witness_eventuallyEq_zero_frontier`,
    since `frontier (S z)` sits in the dead collar `b < ‖·‖`), hence `f = pd witness i =ᶠ[𝓝 x] 0`.  Then
    `f x = 0`, the FULL standard basis spans, and `f (x + t • eⱼ) = 0` for all `j` and all small `t > 0`
    (the ray stays in the open nbhd on which `f ≡ 0`).  Radii `0 < a < b < c < δ₀`.  NOT `a₁ = R/6`. -/
theorem gateFatExterior_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (τ : ℝ) (z : Point n),
          GateFatExterior (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) (S z) := by
  obtain ⟨δ₀, hδ₀pos, hfront⟩ := witness_eventuallyEq_zero_frontier g gi hC hK a b ha hab
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ S hSeq i τ z x hx _hdiff
  -- the field-slot witness is locally `0` at the frontier point `x`.
  have hwit : (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) =ᶠ[nhds x] (fun _ => 0) :=
    hfront c hbc hcδ S hSeq τ z x hx
  -- promote to the field DERIVATIVE `f = pd witness i`, locally `0` at `x`.
  have hf0 : (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) =ᶠ[nhds x] (fun _ => 0) := by
    have hnest := (eventually_eventually_nhds (p := fun y =>
      (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) y = (fun _ => (0 : ℝ)) y)).mpr hwit
    filter_upwards [hnest] with y hy
    show pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y = 0
    rw [pd_congr_of_eventuallyEq _ _ i y hy]
    exact pd_zero_fun i y
  -- fat-exterior data: value `0` at `x`, the full standard basis spans, one-sided vanishing all around.
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

/-! ###############################################################################
    ### The a.e. `hfat` shape + the `hFd` `⨆`-reduction to the sole `hgate` residual.
    ############################################################################### -/

/-- **★★ J4-872 — `hfat_concrete`: the EXACT a.e. `hfat` input of J4-870's fat-exterior `hFd`
    reduction, discharged at the concrete gate.**  Trivial a.e. lift of `gateFatExterior_concrete`
    (which holds for EVERY `z`).  NOT `a₁ = R/6`. -/
theorem hfat_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (t : ℝ) (m : ℕ),
          ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ᵐ z ∂volume,
              GateFatExterior (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) (S z) := by
  obtain ⟨δ₀, hδ₀pos, hcg⟩ := gateFatExterior_concrete g gi hC hK a b ha hab
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ S hSeq i t m
  refine Filter.Eventually.of_forall (fun s => ?_)
  intro _
  refine Filter.Eventually.of_forall (fun z => ?_)
  exact hcg c hbc hcδ S hSeq i (t - s) z

/-- **★★★ J4-872 — `hFd_concrete_ciSup_reduces_to_gateBdd`: at the concrete gate, `hFd`'s `⨆`-bound
    reduces to the SOLE remaining `hgate` (gate-interior boundedness) input.**  Feeds
    `witnessFieldHessian_hFd_ciSup_of_gateBdd_fatExterior` (J4-870) with the now-discharged fat-exterior
    input `hfat_concrete`, so the mixed-directions field-Hessian envelope `hFd` (with `BF s z := ⨆ x',
    ‖fderiv …‖`) holds given only `hgate`.  The former opaque frontier residual is GONE.  NOT
    `a₁ = R/6`. -/
theorem hFd_concrete_ciSup_reduces_to_gateBdd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (i : Fin n) (t : ℝ) (m : ℕ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
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
  obtain ⟨δ₀, hδ₀pos, hfat⟩ := hfat_concrete g gi hC hK a b ha hab
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ S hSeq hgate
  exact witnessFieldHessian_hFd_ciSup_of_gateBdd_fatExterior g gi hC hK S a b i t m
    hgate (hfat c hbc hcδ S hSeq i t m)

end QIQTH.GateFatExteriorConcreteDischarge

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.GateFatExteriorConcreteDischarge
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms witness_eventuallyEq_zero_frontier
#print axioms gateFatExterior_concrete
#print axioms hfat_concrete
#print axioms hFd_concrete_ciSup_reduces_to_gateBdd
end AxiomChecks
