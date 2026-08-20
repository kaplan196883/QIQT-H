/-
  HbintInteriorContinuityRoute — J4-905: the INTERIOR-continuity carry `hBFint` of the J4-904
  MEASURABILITY route (`HbintMeasurabilityNullFrontier.hbint_of_interiorContinuous_nullFrontier`),
  discharged for the CONCRETE envelope `BF s z := ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … y z) x‖`
  down to its true residual — the JOINT `(z,x)`-continuity of the field-Hessian norm on the OPEN
  `interior K ×ˢ concreteKx`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick DISCHARGES the Berge /
  supremum-localization scaffolding of the J4-904 measurability route's `hBFint` carry (the ONE task
  J4-904 left open: interior-continuity of the concrete `⨆`-envelope), REDUCING it — exactly as J4-877
  did for the boundary-BLOCKED full-`K` route — to the joint `(z,x)`-continuity of the field-Hessian
  norm on the OPEN co-boundary product `interior K ×ˢ concreteKx`.  It does **NOT** close `hbint`.  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE — the interior analogue of J4-877, feeding the J4-904 no-go DODGE.

  J4-892 (`BTubeCompactnessAssembly`) PROVED that the joint field-Hessian continuity route is boundary-
  UNSATISFIABLE: the open in-gate chart-`C²` cover of the core-graph forces its base projection
  `⊆ interior K`, so it CANNOT contain the boundary diagonal `(z₀,z₀)` for `z₀ ∈ K \ interior K`.
  J4-904 (`HbintMeasurabilityNullFrontier`) turned this obstruction into an OPPORTUNITY: `hbint` needs
  only INTEGRABILITY, so `AEStronglyMeasurable` tolerates the Lebesgue-NULL discontinuity locus `∂K`.
  Its `hbint_of_interiorContinuous_nullFrontier` reduces `hbint` to four carries, the ONLY non-trivial
  one being `hBFint`: `ContinuousOn (BF s) (interior K)` on the OPEN interior — precisely the domain the
  no-go LEAVES available.

  This brick discharges that `hBFint` for the concrete `BF`.  The `univ`-supremum `BF s z := ⨆ x, ‖·‖`
  and the off-`concreteKx` localization are handled by the SAME abstract Berge engine J4-877 built
  (`FieldHessianJointContinuity.continuousOn_ciSup_of_jointContinuousOn`), which is FULLY GENERAL in the
  base set `P` — so we instantiate `P := interior K` verbatim.  The off-`concreteKx` field-Hessian
  vanishing (`fieldHessian_vanish_off_concreteKx`, banked for `z ∈ K ⊇ interior K`) and the compactness /
  nonemptiness of `concreteKx` are all banked.  The SOLE residual left is the joint `(z,x)`-continuity of
  the field-Hessian norm on `interior K ×ˢ concreteKx` — an OPEN×compact product WITHOUT the boundary
  diagonal, exactly what the interior-only coherent chart tower (J4-884/887/889/890/891) is built to
  feed.  Confirmed the interior route is the campaign's surviving asset past the boundary no-go.
  NOT `a₁ = R/6`.

  ## WHAT LANDS (ns `QIQTH.HbintInteriorContinuityRoute`).
    • `BF_interiorContinuousOn_of_jointContinuousOn` — ★★ the interior analogue of J4-877's
      `BF_zContinuousOn_of_jointContinuousOn`: `ContinuousOn (BF s) (interior K)` from off-`Kx` vanishing
      (`z ∈ interior K`) + joint `(z,x)`-continuity on `interior K ×ˢ Kx`.
    • `fieldHessianNorm_interiorJointContinuous_of_jointC1` — ★ the interior joint continuity from a
      joint `ContDiffOn ℝ 1` carry of the field-derivative kernel on an OPEN `U ⊇ interior K ×ˢ Kx`
      (reuses J4-878's `partialFDeriv_norm_jointContinuousOn`, `.mono`'d to the interior product).
    • `hBFint_concrete_of_jointInteriorContinuous` — ★★★ the EXACT `hBFint` carry of J4-904, REDUCED
      a.e. to the interior joint continuity residual (concrete flow-ball gate; off-`Kx` vanishing
      discharged from banked infra).
    • `hbint_concrete_via_interior_route` — ★★★ the full `hbint` field of
      `MixedDirectionsFieldHessianEnvelope`, obtained by feeding `hBFint_concrete_of_jointInteriorContinuous`
      into J4-904 (with the banked off-`K` `BF` vanishing, and the elementary `BL`-continuity / compact-`K`
      bound / null-frontier carries).  So the J4-904 measurability route CLOSES the `hBFint` sup-scaffolding;
      the honest residual is the interior joint `(z,x)`-continuity (+ the elementary carries).
    • `BF_interior_residual_nonvacuous` — the interior joint-continuity residual is inhabited (empty gate).
-/
import Mathlib
import QIQTH.HbintMeasurabilityNullFrontier
import QIQTH.FieldHessianJointContinuityClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.FieldHessianJointContinuity
open QIQTH.FieldHessianJointContinuityClosed
open QIQTH.HbintMeasurabilityNullFrontier
open scoped Topology BigOperators

namespace QIQTH.HbintInteriorContinuityRoute

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C1 — `BF` interior-continuity from JOINT `(z,x)` field-Hessian-norm continuity.
    ###      (The interior analogue of J4-877's `BF_zContinuousOn_of_jointContinuousOn`.)
    ############################################################################### -/

/-- **★★ `BF_interiorContinuousOn_of_jointContinuousOn`.**  The concrete envelope
    `BF s z := ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … y z) x‖` is `ContinuousOn (interior K)`, given a
    FIXED nonempty compact `Kx` off which the field-Hessian vanishes for every `z ∈ interior K`
    (`hvanish`) and JOINT `(z,x)`-continuity of the field-Hessian norm on `interior K ×ˢ Kx` (`hjoint`).
    A direct instantiation of J4-877's abstract Berge engine
    `continuousOn_ciSup_of_jointContinuousOn` at the base set `P := interior K` (the engine is fully
    general in `P`).  This is the interior analogue of `BF_zContinuousOn_of_jointContinuousOn` — the ONE
    task the J4-904 measurability route left open.  NOT `a₁ = R/6`. -/
theorem BF_interiorContinuousOn_of_jointContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) {Kx : Set (Point n)} (hKx : IsCompact Kx) (hKxne : Kx.Nonempty)
    (hvanish : ∀ z ∈ interior K, ∀ x ∉ Kx,
      fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0)
    (hjoint : ContinuousOn
        (fun p : Point n × Point n =>
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖)
        (interior K ×ˢ Kx)) :
    ContinuousOn
      (fun z => ⨆ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖) (interior K) :=
  continuousOn_ciSup_of_jointContinuousOn hKx hKxne
    (fun z x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖)
    (fun z x => norm_nonneg _)
    (fun z hz x hx => by
      show ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖ = 0
      rw [hvanish z hz x hx]; exact norm_zero)
    hjoint

/-! ###############################################################################
    ### C2 — the interior joint continuity from a joint `C¹` carry on an OPEN `U`.
    ############################################################################### -/

/-- **★ `fieldHessianNorm_interiorJointContinuous_of_jointC1`.**  The joint `(z,x)`-continuity of the
    field-Hessian norm on `interior K ×ˢ Kx` — the residual `BF_interiorContinuousOn_of_jointContinuousOn`
    consumes — produced from a JOINT `ContDiffOn ℝ 1` carry of the joint field-derivative kernel
    `Ψ (z,y) := witnessFieldDeriv … y z` on an OPEN neighbourhood `U ⊇ interior K ×ˢ Kx`.  Reuses J4-878's
    general engine `partialFDeriv_norm_jointContinuousOn` and restricts with `.mono` to the interior
    product.  Because `interior K` is OPEN and off the boundary diagonal, this joint-`C¹` carry is exactly
    the interior-only coherent-chart regularity the boundary no-go LEAVES available.  NOT `a₁ = R/6`. -/
theorem fieldHessianNorm_interiorJointContinuous_of_jointC1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) {Kx : Set (Point n)}
    {U : Set (Point n × Point n)} (hU : IsOpen U) (hsub : interior K ×ˢ Kx ⊆ U)
    (hjointC1 : ContDiffOn ℝ 1
      (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1) U) :
    ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖)
      (interior K ×ˢ Kx) :=
  (partialFDeriv_norm_jointContinuousOn hU
    (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1)
    hjointC1).mono hsub

/-! ###############################################################################
    ### C3 — the `hBFint` carry of J4-904, REDUCED a.e. to the interior joint continuity.
    ############################################################################### -/

/-- **★★★ J4-905 — `hBFint_concrete_of_jointInteriorContinuous`.**  The EXACT `hBFint` carry the J4-904
    measurability route (`hbint_of_interiorContinuous_nullFrontier`) consumes, at the CONCRETE flow-ball
    gate, REDUCED a.e. to the SOLE residual — JOINT `(z,x)`-continuity of the field-Hessian norm on the
    OPEN `interior K ×ˢ concreteKx`.  The off-`Kx` vanishing (`z ∈ interior K ⊆ K`), the compactness and
    nonemptiness of `concreteKx` are DISCHARGED internally from banked infra
    (`fieldHessian_vanish_off_concreteKx`, `concreteKx_isCompact`, `concreteKx_nonempty`).  Radii
    `0 < a < b < c < δ₀`, `b < uniformFlowRadius`; `K` nonempty (for the `concreteKx` inhabitant).
    NOT `a₁ = R/6`. -/
theorem hBFint_concrete_of_jointInteriorContinuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (t : ℝ) (m : ℕ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
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
  obtain ⟨δ₀, hδ₀, hvan⟩ := fieldHessian_vanish_off_concreteKx g gi hC hK a b ha hab hbρ
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq hjoint
  have hb0 : (0 : ℝ) ≤ b := le_of_lt (lt_trans ha hab)
  filter_upwards [hjoint] with s hjs hsU
  refine BF_interiorContinuousOn_of_jointContinuousOn g gi hC hK S a b i (t - s)
    (concreteKx_isCompact g gi hC hK b hbρ) (concreteKx_nonempty g gi hC hK b hKne hb0)
    ?_ (hjs hsU)
  intro z hz x hx
  exact hvan c hbc hcδ S hSeq i (t - s) z (interior_subset hz) x hx

/-! ###############################################################################
    ### C4 — the full `hbint` field via the J4-904 measurability route.
    ############################################################################### -/

/-- **★★★ J4-905 — `hbint_concrete_via_interior_route`.**  The EXACT `hbint` field of
    `MixedDirectionsFieldHessianEnvelope`, at the CONCRETE flow-ball gate, obtained by feeding the
    interior-continuity discharge `hBFint_concrete_of_jointInteriorContinuous` (C3) into the J4-904
    measurability route `hbint_of_interiorContinuous_nullFrontier`.  The off-`K` `BF` vanishing is the
    banked `BF_ciSup_eqZero_of_base_notMem_K` (J4-867); the remaining carries are ELEMENTARY:
    `BL`-continuity on `K`, a compact-`K` product bound, and `volume (frontier K) = 0` (discharged for the
    live ball `K = closedBall 0 r` by `volume_frontier_closedBall_eq_zero`).  So the J4-904 route CLOSES
    the `hBFint` Berge / supremum scaffolding of `hbint`; the honest residual is the interior joint
    `(z,x)`-continuity of the field-Hessian norm on `interior K ×ˢ concreteKx` (the interior-only chart
    regularity the boundary no-go LEAVES available), plus the elementary `BL`-continuity / compact-`K`
    bound.  Radii `0 < a < b < c < δ₀`, `b < uniformFlowRadius`; `K` nonempty.  NOT `a₁ = R/6`. -/
theorem hbint_concrete_via_interior_route (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ)
    (hnull : volume (frontier K) = 0) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
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
  obtain ⟨δ₀, hδ₀, hBFint⟩ :=
    hBFint_concrete_of_jointInteriorContinuous g gi hC hK hKne a b ha hab hbρ i t m
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq hjoint hBLK hbnd
  refine hbint_of_interiorContinuous_nullFrontier hK.isClosed hK hnull
    BL (fun s z => ⨆ x : Point n,
      ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖) t m
    (hBFint c hbc hcδ S hSeq hjoint) ?_ hBLK hbnd
  filter_upwards with s _ z hz
  exact BF_ciSup_eqZero_of_base_notMem_K g gi hC hK S a b i (t - s) z hz

/-! ###############################################################################
    ### C5 — NON-VACUITY of the interior joint-continuity residual.
    ############################################################################### -/

/-- **NON-VACUITY.**  The interior joint-continuity residual of `BF_interiorContinuousOn_of_jointContinuousOn`
    is inhabited at the empty gate `S := fun _ => ∅` and any `Kx`: there the field-derivative kernel is
    identically `0` on the gate, so the field-Hessian norm is the constant `0`, hence trivially
    `ContinuousOn (interior K ×ˢ Kx)`.  So the reduction fires — no unsatisfiable antecedent (no
    J4-548/847 trap), never the conclusion.  (The genuinely non-trivial residual — interior joint
    `(z,x)`-continuity of the CONCRETE non-empty-gate field-Hessian norm — is the honest interior-only
    chart content that remains.)  NOT `a₁ = R/6`. -/
theorem BF_interior_residual_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (τ : ℝ)
    {Kx : Set (Point n)} :
    ContinuousOn
        (fun p : Point n × Point n =>
          ‖fderiv ℝ (fun y =>
            witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y p.1) p.2‖)
        (interior K ×ˢ Kx) := by
  have hzero : (fun p : Point n × Point n =>
      ‖fderiv ℝ (fun y =>
        witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y p.1) p.2‖)
      = fun _ => (0 : ℝ) := by
    funext p
    rw [QIQTH.ChartJetXUniformBound.witnessFieldHessian_fderiv_eqZero_of_notMem_closure
      g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ p.1 p.2
      (by simp)]
    exact norm_zero
  rw [hzero]; exact continuousOn_const

end QIQTH.HbintInteriorContinuityRoute

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HbintInteriorContinuityRoute
#print axioms BF_interiorContinuousOn_of_jointContinuousOn
#print axioms fieldHessianNorm_interiorJointContinuous_of_jointC1
#print axioms hBFint_concrete_of_jointInteriorContinuous
#print axioms hbint_concrete_via_interior_route
#print axioms BF_interior_residual_nonvacuous
end AxiomChecks
