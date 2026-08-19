/-
  ChartJetXUniformBound — J4-865: the x-UNIFORM field-Hessian bound for `hFd`, via GATE COMPACTNESS.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick supplies the `x`-uniform
  reduction of the `hFd` field of `MixedDirectionsFieldHessianEnvelope` (J4-843) — the wall flagged at
  cp732/J4-864.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none
  equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DECISIVE FINDING (fact-finding result the mission asked for).

  `hFd` needs `‖fderiv (y ↦ witnessFieldDeriv … y z) x‖ ≤ BF s z` UNIFORMLY over ALL field points
  `x : Point n`.  The earlier J4-864 route tried a Gaussian×polynomial `x`-moment sup and correctly
  found it a hard estimate (the scalar factors grow polynomially in `x`, only the Gaussian decays).

  THIS FILE takes the ALTERNATIVE route the mission flagged as most promising — GATE COMPACTNESS — and
  it WORKS: `witnessFieldDeriv … y z = pd_i (x' ↦ H_G τ x' z) y` is the field-partial of the GATED
  witness `H_G = gatedKernel K S H`, whose spatial gate `S z` HARD-KILLS the kernel off `S z`.  Two
  structural facts follow:

    (1) OFF-GATE VANISHING (`witnessFieldDeriv_eqZero_of_notMem_closure`, PROVED unconditionally):
        for `y ∉ closure (S z)`, the gated kernel is `0` on a whole neighbourhood of `y`, so its
        field-`pd` — and hence `fderiv (y ↦ witnessFieldDeriv … y z)` at any such `x` — VANISHES.
        The "active" set of the field-Hessian is therefore contained in the COMPACT set `closure (S z)`.

    (2) GATE COMPACTNESS (`concreteGate_closure_isCompact`, PROVED for the CONCRETE gate):
        the concrete gate is `S z = uniformFlowExp z '' ball 0 c`; its closure is contained in the
        continuous image `uniformFlowExp z '' closedBall 0 c` of a compact ball, hence is COMPACT.

  So "uniform over ALL of `Point n`" collapses to "uniform over a KNOWN COMPACT SET" — a continuous
  dominator on `closure (S z)` attains a finite max (`IsCompact.bddAbove_image`), and off the closure the
  field-Hessian is `0`.  The `x`-uniform bound `∃ M, ∀ x, ‖fderiv …‖ ≤ M` (and its `hFd` a.e. packaging
  with the EXPLICIT envelope `BF s z := ⨆ x, ‖fderiv …‖`) then follow with no Gaussian-moment estimate.

  ## WHAT LANDS (ns `QIQTH.ChartJetXUniformBound`).
    • `xuniform_of_bddAbove_offClosure` / `bddAbove_image_of_isCompact_dominated`
      / `bddAbove_range_of_compact_dominated` / `xuniform_of_compact_dominated`
        — the ABSTRACT compactness engine (fully unconditional).
    • `witnessFieldDeriv_eqZero_of_notMem_closure` — off-gate vanishing of the field-`pd` (PROVED).
    • `witnessFieldHessian_fderiv_eqZero_of_notMem_closure` — off-gate vanishing of the field-Hessian
      CLM (PROVED); supplies the `hzero` leg.
    • `concreteGate_closure_isCompact` — ★ the DECISIVE finding: the concrete gate closure is compact.
    • `witnessFieldHessian_opNorm_xuniform_of_compactGate` — ★★ the `x`-uniform operator-norm bound
      `∃ M ≥ 0, ∀ x, ‖fderiv …‖ ≤ M` from {compact gate, continuous dominator on the gate}.
    • `witnessFieldHessian_hFd_ciSup_of_compactGate` — ★★★ the EXACT `hFd` field of
      `MixedDirectionsFieldHessianEnvelope`, with the EXPLICIT envelope
      `BF s z := ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x‖`, reduced a.e. to
      {compact gate confinement, a.e. continuous-dominated field-Hessian on the gate}.

  ⚠ HONEST RESIDUAL.  The one genuine remaining input is `hdom` — a CONTINUOUS dominator of the gated
  field-Hessian norm on `closure (S z)` (true because the smooth witness field-Hessian is continuous and
  dominates on the OPEN gate; the gate BOUNDARY is the only subtlety).  This is a MUCH weaker input than
  the Gaussian×polynomial `x`-moment estimate J4-864 faced.  A full `MixedDirectionsFieldHessianEnvelope`
  instance additionally needs `hLevi`/`hkint`/`hbint` and the deep §C `hzmass` `z`-mass integrability.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedDirectionsFieldHessianEnvelope
import QIQTH.FlowJointContinuity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.FlowJointContinuity
open scoped Topology BigOperators

namespace QIQTH.ChartJetXUniformBound

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### THE ABSTRACT COMPACTNESS ENGINE (fully unconditional).
    ############################################################################### -/

/-- **Engine 1.**  A function bounded ABOVE on `closure T` and `≤ 0` off `closure T` is bounded above
    globally by a non-negative constant.  (No topology beyond the definition of `closure`.) -/
theorem xuniform_of_bddAbove_offClosure (F : Point n → ℝ) (T : Set (Point n))
    (hzero : ∀ x, x ∉ closure T → F x ≤ 0)
    (hbdd : BddAbove (F '' closure T)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, F x ≤ M := by
  obtain ⟨B, hB⟩ := hbdd
  refine ⟨max 0 B, le_max_left _ _, fun x => ?_⟩
  by_cases hx : x ∈ closure T
  · exact le_trans (hB (mem_image_of_mem F hx)) (le_max_right _ _)
  · exact le_trans (hzero x hx) (le_max_left _ _)

/-- **Engine 2.**  If `closure T` is COMPACT, `G` is continuous, and `F ≤ G` on `closure T`, then `F`
    is bounded above on `closure T` (a continuous function on a compact set attains a max, via
    `IsCompact.bddAbove_image`, and `F` is dominated by it). -/
theorem bddAbove_image_of_isCompact_dominated (F G : Point n → ℝ) (T : Set (Point n))
    (hcpt : IsCompact (closure T)) (hG : Continuous G)
    (hdom : ∀ x ∈ closure T, F x ≤ G x) :
    BddAbove (F '' closure T) := by
  obtain ⟨C, hC⟩ := hcpt.bddAbove_image hG.continuousOn
  refine ⟨C, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact le_trans (hdom x hx) (hC (mem_image_of_mem G hx))

/-- **Engine (combined).**  `x`-uniform upper bound from {compact gate closure, continuous dominator on
    the closure, `≤ 0` off the closure}. -/
theorem xuniform_of_compact_dominated (F G : Point n → ℝ) (T : Set (Point n))
    (hcpt : IsCompact (closure T)) (hG : Continuous G)
    (hzero : ∀ x, x ∉ closure T → F x ≤ 0)
    (hdom : ∀ x ∈ closure T, F x ≤ G x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, F x ≤ M :=
  xuniform_of_bddAbove_offClosure F T hzero
    (bddAbove_image_of_isCompact_dominated F G T hcpt hG hdom)

/-- **Engine (range form).**  Same hypotheses ⟹ the whole RANGE of `F` is bounded above — the shape
    needed to feed `le_ciSup` when the envelope is taken to be the global `⨆`. -/
theorem bddAbove_range_of_compact_dominated (F G : Point n → ℝ) (T : Set (Point n))
    (hcpt : IsCompact (closure T)) (hG : Continuous G)
    (hzero : ∀ x, x ∉ closure T → F x ≤ 0)
    (hdom : ∀ x ∈ closure T, F x ≤ G x) :
    BddAbove (Set.range F) := by
  obtain ⟨M, _, hM⟩ := xuniform_of_compact_dominated F G T hcpt hG hzero hdom
  exact ⟨M, by rintro y ⟨x, rfl⟩; exact hM x⟩

/-! ###############################################################################
    ### OFF-GATE VANISHING of the concrete field-`pd` and field-Hessian.
    ############################################################################### -/

/-- **★ OFF-GATE VANISHING (first order).**  For a field point `y ∉ closure (S z)`, the gated witness
    `x' ↦ H_G τ x' z` is identically `0` on the open neighbourhood `(closure (S z))ᶜ` of `y` (every
    `x'` there is off the spatial gate `S z`), so its field-`pd` — the first field-derivative kernel
    `witnessFieldDeriv` — vanishes.  Unconditional; no `z ∈ K` assumption needed. -/
theorem witnessFieldDeriv_eqZero_of_notMem_closure (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (y : Point n) (hy : y ∉ closure (S z)) :
    witnessFieldDeriv g gi hC hK S a b i τ y z = 0 := by
  -- the gated witness is `0` at every point of the open set `(closure (S z))ᶜ`.
  have hF0 : ∀ x' ∈ (closure (S z))ᶜ,
      vanVleckGatedWitness g gi hC hK S a b τ x' z = 0 := by
    intro x' hx'
    have hx'S : x' ∉ S z := fun h => hx' (subset_closure h)
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inr hx'S)
  -- the coordinate line through `y` stays in `(closure (S z))ᶜ` near `y i`.
  have hUopen : IsOpen ((closure (S z))ᶜ) := isClosed_closure.isOpen_compl
  have hcontAt : ContinuousAt (Function.update y i) (y i) :=
    (hasDerivAt_update y i (y i)).continuousAt
  have hy0 : Function.update y i (y i) = y := Function.update_eq_self i y
  have hpre : (Function.update y i) ⁻¹' (closure (S z))ᶜ ∈ nhds (y i) := by
    apply hcontAt.preimage_mem_nhds
    rw [hy0]; exact hUopen.mem_nhds hy
  -- hence the line-restricted witness is eventually `0`, so its derivative is `0`.
  have hev : (fun t => vanVleckGatedWitness g gi hC hK S a b τ (Function.update y i t) z)
      =ᶠ[nhds (y i)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hpre] with t ht
    exact hF0 _ ht
  unfold witnessFieldDeriv pd
  rw [hev.deriv_eq, deriv_const]

/-- **★★ OFF-GATE VANISHING of the field-Hessian CLM.**  For `x ∉ closure (S z)`, the field-derivative
    kernel `y ↦ witnessFieldDeriv … y z` is `0` on a neighbourhood of `x` (by the first-order vanishing,
    on the open set `(closure (S z))ᶜ`), so its Fréchet derivative — the field-Hessian CLM the `hFd`
    envelope bounds — vanishes at `x`.  This is the `hzero` leg of the compactness engine. -/
theorem witnessFieldHessian_fderiv_eqZero_of_notMem_closure (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (x : Point n) (hx : x ∉ closure (S z)) :
    fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0 := by
  have hU : (closure (S z))ᶜ ∈ nhds x := isClosed_closure.isOpen_compl.mem_nhds hx
  have heq : (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU] with y hy
    exact witnessFieldDeriv_eqZero_of_notMem_closure g gi hC hK S a b i τ z y hy
  rw [heq.fderiv_eq]
  exact fderiv_const_apply (0 : ℝ)

/-! ###############################################################################
    ### THE DECISIVE FINDING — the concrete gate confines `x` to a COMPACT set.
    ############################################################################### -/

/-- **★ GATE COMPACTNESS (the decisive fact-finding result).**  For the CONCRETE spatial gate
    `S z = uniformFlowExp z '' ball 0 c` (`z ∈ K`, `c < uniformFlowRadius`), the CLOSURE of the gate is
    COMPACT: it is contained in the continuous image `uniformFlowExp z '' closedBall 0 c` of the compact
    closed ball (joint flow continuity `uniformFlowExp_joint_continuousOn`), and a closed subset of a
    compact set is compact.  This is exactly what makes `hFd`'s "uniform over all `x`" collapse to
    "uniform over a compact set". -/
theorem concreteGate_closure_isCompact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K)
    (c : ℝ) (hc : c < uniformFlowRadius g gi hC hK) :
    IsCompact (closure (uniformFlowExp g gi hC hK z '' Metric.ball 0 c)) := by
  -- `w ↦ (z, w)` maps `closedBall 0 c` into `K ×ˢ ball 0 ρ`.
  have hmaps : Set.MapsTo (fun w : Point n => (z, w)) (Metric.closedBall 0 c)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    exact ⟨hz, by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_le_of_lt hw hc⟩
  have hincl : ContinuousOn (fun w : Point n => (z, w)) (Metric.closedBall 0 c) :=
    (continuous_const.prodMk continuous_id).continuousOn
  -- so `uniformFlowExp z` is continuous on `closedBall 0 c` (composition with joint continuity).
  have hcontOn : ContinuousOn (uniformFlowExp g gi hC hK z) (Metric.closedBall 0 c) :=
    (uniformFlowExp_joint_continuousOn g gi hC hK).comp hincl hmaps
  -- the image of the compact closed ball is compact.
  have himg : IsCompact (uniformFlowExp g gi hC hK z '' Metric.closedBall 0 c) :=
    (isCompact_closedBall (0 : Point n) c).image_of_continuousOn hcontOn
  -- `closure (image ball) ⊆ image closedBall`, closed subset of a compact set is compact.
  have hsub : uniformFlowExp g gi hC hK z '' Metric.ball 0 c
      ⊆ uniformFlowExp g gi hC hK z '' Metric.closedBall 0 c :=
    Set.image_mono Metric.ball_subset_closedBall
  exact himg.of_isClosed_subset isClosed_closure (closure_minimal hsub himg.isClosed)

/-! ###############################################################################
    ### THE `x`-UNIFORM FIELD-HESSIAN BOUND and the `hFd` reduction.
    ############################################################################### -/

/-- **★★ THE `x`-UNIFORM OPERATOR-NORM BOUND.**  Given a COMPACT gate closure and a CONTINUOUS dominator
    `G` of the gated field-Hessian norm on `closure (S z)`, the field-Hessian is bounded UNIFORMLY over
    ALL `x : Point n` by a single non-negative constant — the gate compactness does all the heavy
    lifting (off the closure the Hessian is `0`, on it `G` attains a max).  This is exactly the inner
    statement of `MixedDirectionsFieldHessianEnvelope.hFd` at a fixed `(s, z)`. -/
theorem witnessFieldHessian_opNorm_xuniform_of_compactGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (G : Point n → ℝ)
    (hcpt : IsCompact (closure (S z))) (hGcont : Continuous G)
    (hdom : ∀ x ∈ closure (S z),
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖ ≤ G x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Point n,
      ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖ ≤ M := by
  refine xuniform_of_compact_dominated
    (fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖) G (S z)
    hcpt hGcont (fun x hx => ?_) hdom
  have h0 := witnessFieldHessian_fderiv_eqZero_of_notMem_closure g gi hC hK S a b i τ z x hx
  simp [h0]

/-- **★★★ THE `hFd` REDUCTION with an EXPLICIT envelope.**  The EXACT `hFd` field of
    `MixedDirectionsFieldHessianEnvelope`, with the EXPLICIT operator-norm envelope
    `BF s z := ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x‖`, reduced a.e. to the two
    gate-geometry inputs:
      • `hcpt`  — a.e. the gate closure `closure (S z)` is COMPACT (discharged for the concrete gate by
                  `concreteGate_closure_isCompact`);
      • `hdom`  — a.e. the gated field-Hessian norm is dominated on `closure (S z)` by SOME continuous
                  function (true because the smooth witness field-Hessian is continuous and dominates on
                  the open gate — the honest residual, far weaker than a Gaussian-moment estimate).
    The envelope `BF` is a genuine finite `⨆` (bounded via the compactness engine), so downstream
    consumers get an explicit dominator, not an opaque existential.  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_hFd_ciSup_of_compactGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ)
    (hcpt : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, IsCompact (closure (S z)))
    (hdom : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∃ G : Point n → ℝ, Continuous G ∧
          ∀ x ∈ closure (S z),
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ ≤ G x) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  filter_upwards [hcpt, hdom] with s hcpts hdoms hsUioc
  filter_upwards [hcpts hsUioc, hdoms hsUioc] with z hzc hzd
  obtain ⟨G, hGcont, hGdom⟩ := hzd
  intro x
  have hbdd : BddAbove (Set.range
      (fun x' => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖)) :=
    bddAbove_range_of_compact_dominated
      (fun x' => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖) G (S z)
      hzc hGcont
      (fun x' hx' => by
        have h0 := witnessFieldHessian_fderiv_eqZero_of_notMem_closure
          g gi hC hK S a b i (t - s) z x' hx'
        simp [h0])
      hGdom
  exact le_ciSup hbdd x

/-! ###############################################################################
    ### NON-VACUITY.
    ############################################################################### -/

/-- **Non-vacuity of the compactness engine's antecedents.**  The hypotheses of
    `witnessFieldHessian_opNorm_xuniform_of_compactGate` are jointly satisfiable at the EMPTY gate
    `S := fun _ => ∅` (compact empty closure, `G := 0` continuous, `hdom` vacuous), yielding the
    `x`-uniform bound.  (The much stronger non-vacuity — a genuinely NON-EMPTY compact gate — is
    `concreteGate_closure_isCompact` for the concrete `uniformFlowExp`-image gate.)  No unsatisfiable
    antecedent (J4-548/847 trap avoided). -/
theorem xuniform_of_compactGate_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (τ : ℝ) (z : Point n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Point n,
      ‖fderiv ℝ (fun y =>
          witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y z) x‖ ≤ M :=
  witnessFieldHessian_opNorm_xuniform_of_compactGate g gi hC hK (fun _ => ∅) a b i τ z
    (fun _ => 0)
    (by rw [closure_empty]; exact isCompact_empty)
    continuous_const
    (by intro x hx; simp at hx)

end QIQTH.ChartJetXUniformBound

section AxiomChecks
open QIQTH.ChartJetXUniformBound
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms witnessFieldDeriv_eqZero_of_notMem_closure
#print axioms witnessFieldHessian_fderiv_eqZero_of_notMem_closure
#print axioms concreteGate_closure_isCompact
#print axioms witnessFieldHessian_opNorm_xuniform_of_compactGate
#print axioms witnessFieldHessian_hFd_ciSup_of_compactGate
#print axioms xuniform_of_compactGate_nonvacuous
end AxiomChecks
