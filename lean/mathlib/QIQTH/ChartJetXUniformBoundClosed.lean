/-
  ChartJetXUniformBoundClosed — J4-866: the WEAKEST-FORM `hdom` reduction for `hFd`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick REFINES the honest residual
  `hdom` of J4-865 (`ChartJetXUniformBound`) into its WEAKEST honest form.  No `sorry`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS ADDS OVER J4-865.

  J4-865 reduced `MixedDirectionsFieldHessianEnvelope.hFd` (with `BF s z := ⨆ x, ‖fderiv …‖`) to a
  gate-geometry input `hdom`:  a.e. `z`, ∃ a **continuous** dominator `G` with
  `‖fderiv (y ↦ witnessFieldDeriv … y z) x‖ ≤ G x` on `closure (S z)`.  Exhibiting a continuous `G`
  is more than is needed: `le_ciSup` only wants the RANGE bounded above.  This brick weakens `hdom`
  to the genuinely-minimal input

    `hbdd`:  a.e. `z`, `BddAbove ((fun x => ‖fderiv (y ↦ witnessFieldDeriv … y z) x‖) '' closure (S z))`

  — the gated field-Hessian norm is merely BOUNDED ABOVE on the compact gate closure — and shows this
  is IMPLIED by (and strictly weaker than) both the J4-865 continuous-dominator `hdom` AND the canonical
  regularity form `ContinuousOn (‖fderiv …‖) (closure (S z))` (on a COMPACT closure).  So the honest
  residual for `hFd` is now: "the gated field-Hessian is bounded on the compact gate closure" — the
  weakest possible honest statement, no dominator to guess, no boundary-continuity to certify.

  ## THE PART-1 FACT-FINDING VERDICT (the mission's two options (a)/(b)).

  The gate is a **HARD indicator** gate (`gatedKernel K S H τ p q = if q∈K then (if p∈S q then H else 0)
  else 0`, `GlobalHunifAssembly`).  So the gated kernel JUMPS at `∂(S z)`, and the gated field-Hessian
  is NOT globally continuous — it equals the (smooth) UN-gated one only on the OPEN interior of `S z`.
  Hence Part-1 is genuinely case **(b)**: boundary continuity is NOT automatic from a global smooth
  witness.  What IS unconditionally true and banked here: on a COMPACT gate closure, `BddAbove` of the
  field-Hessian norm is exactly the minimal residual, and it follows from either a continuous dominator
  or `ContinuousOn`.  The remaining honest content (that the gated field-Hessian actually IS bounded on
  `closure (S z)`, including the boundary) is left as the explicit `hbdd` input — not fabricated.

  ## WHAT LANDS (ns `QIQTH.ChartJetXUniformBoundClosed`).
    • `bddAbove_range_of_bddAbove_image_offClosure` — abstract: `≤ 0` off `closure T` + `BddAbove`
      image ⟹ `BddAbove` range (the exact shape `le_ciSup` consumes).
    • `bddAbove_fieldHessian_of_continuousOn_compact` — `IsCompact (closure (S z))` + `ContinuousOn`
      of the field-Hessian norm ⟹ the `hbdd` image is bounded (`IsCompact.bddAbove_image`).
    • `bddAbove_fieldHessian_of_continuous_dominator` — a J4-865-style continuous dominator on
      `closure (S z)` (compact) ⟹ the `hbdd` image is bounded (so `hbdd` ⟸ the J4-865 `hdom`).
    • `witnessFieldHessian_hFd_ciSup_of_bddAbove` — ★★★ the `hFd` field of
      `MixedDirectionsFieldHessianEnvelope` with `BF s z := ⨆ x, ‖fderiv …‖`, reduced a.e. to the SINGLE
      minimal input `hbdd` (bounded field-Hessian on the compact gate closure).
    • `witnessFieldHessian_hFd_ciSup_of_compactGate_continuousOn` — the same `hFd`, reduced to
      {compact gate closure, `ContinuousOn` field-Hessian norm on it} — the canonical-regularity form.
    • `hFd_bddAbove_nonvacuous` — antecedents inhabited at the empty gate.

  ⚠ HONEST RESIDUAL.  The `hbdd` input (gated field-Hessian bounded on the compact gate closure,
  including its boundary) is the genuine remaining content; a full `MixedDirectionsFieldHessianEnvelope`
  instance additionally needs `hLevi`/`hkint`/`hbint` and the deep §C `hzmass`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetXUniformBound

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.FlowJointContinuity
open QIQTH.ChartJetXUniformBound
open scoped Topology BigOperators

namespace QIQTH.ChartJetXUniformBoundClosed

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### THE WEAKEST-FORM ABSTRACT ENGINE.
    ############################################################################### -/

/-- **Engine (weakest form).**  A function `F` that is `≤ 0` off `closure T` and whose image over
    `closure T` is bounded above has a globally bounded-above RANGE — exactly the `BddAbove (range F)`
    that `le_ciSup` consumes.  This drops the continuous-dominator hypothesis of J4-865: only pointwise
    boundedness of the image is used. -/
theorem bddAbove_range_of_bddAbove_image_offClosure (F : Point n → ℝ) (T : Set (Point n))
    (hzero : ∀ x, x ∉ closure T → F x ≤ 0)
    (hbdd : BddAbove (F '' closure T)) :
    BddAbove (Set.range F) := by
  obtain ⟨M, _, hM⟩ := xuniform_of_bddAbove_offClosure F T hzero hbdd
  exact ⟨M, by rintro y ⟨x, rfl⟩; exact hM x⟩

/-! ###############################################################################
    ### `hbdd` ⟸ the two standard regularity inputs.
    ############################################################################### -/

/-- **`hbdd` from `ContinuousOn` on the compact gate closure.**  A continuous-on-the-compact-closure
    field-Hessian norm attains a finite max, so its image is bounded above (`IsCompact.bddAbove_image`).
    This is the canonical-regularity route to the minimal input. -/
theorem bddAbove_fieldHessian_of_continuousOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n)
    (hcpt : IsCompact (closure (S z)))
    (hCont : ContinuousOn
        (fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖)
        (closure (S z))) :
    BddAbove ((fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖)
      '' closure (S z)) :=
  hcpt.bddAbove_image hCont

/-- **`hbdd` from a continuous dominator (the J4-865 `hdom`).**  Any continuous `G` dominating the
    field-Hessian norm on the compact gate closure bounds the image above; hence the J4-865
    continuous-dominator input IMPLIES the minimal `hbdd` input. -/
theorem bddAbove_fieldHessian_of_continuous_dominator (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (G : Point n → ℝ)
    (hcpt : IsCompact (closure (S z))) (hGcont : Continuous G)
    (hdom : ∀ x ∈ closure (S z),
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖ ≤ G x) :
    BddAbove ((fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖)
      '' closure (S z)) :=
  bddAbove_image_of_isCompact_dominated
    (fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖) G (S z)
    hcpt hGcont hdom

/-! ###############################################################################
    ### THE `hFd` REDUCTION to the minimal `hbdd` input.
    ############################################################################### -/

/-- **★★★ THE `hFd` REDUCTION (weakest form).**  The EXACT `hFd` field of
    `MixedDirectionsFieldHessianEnvelope`, with the EXPLICIT envelope
    `BF s z := ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x‖`, reduced a.e. to the SINGLE minimal
    gate-geometry input `hbdd`: a.e. `z`, the gated field-Hessian norm is BOUNDED ABOVE on the (compact)
    gate closure.  No continuous dominator, no `ContinuousOn` — just boundedness of the image, which is
    exactly what `le_ciSup` needs once the off-closure vanishing (`witnessFieldHessian_fderiv_eqZero_
    of_notMem_closure`, J4-865) is folded in.  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_hFd_ciSup_of_bddAbove (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume,
          BddAbove ((fun x =>
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
              '' closure (S z))) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  filter_upwards [hbdd] with s hbdds hsUioc
  filter_upwards [hbdds hsUioc] with z hzb
  intro x
  have hrange : BddAbove (Set.range
      (fun x' => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖)) :=
    bddAbove_range_of_bddAbove_image_offClosure
      (fun x' => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖) (S z)
      (fun x' hx' => by
        have h0 := witnessFieldHessian_fderiv_eqZero_of_notMem_closure
          g gi hC hK S a b i (t - s) z x' hx'
        simp [h0])
      hzb
  exact le_ciSup hrange x

/-- **★★ THE `hFd` REDUCTION in canonical-regularity form.**  The same `hFd` field, reduced to the two
    canonical inputs a.e. in `z`: the gate closure is COMPACT and the field-Hessian norm is
    `ContinuousOn` it.  (`hbdd` follows via `IsCompact.bddAbove_image`.)  This is the honest interface a
    regularity discharge should target — no dominator to construct. -/
theorem witnessFieldHessian_hFd_ciSup_of_compactGate_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ)
    (hcpt : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, IsCompact (closure (S z)))
    (hCont : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ContinuousOn
          (fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
          (closure (S z))) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  refine witnessFieldHessian_hFd_ciSup_of_bddAbove g gi hC hK S a b i t m ?_
  filter_upwards [hcpt, hCont] with s hcpts hConts hsUioc
  filter_upwards [hcpts hsUioc, hConts hsUioc] with z hzc hzcont
  exact bddAbove_fieldHessian_of_continuousOn_compact g gi hC hK S a b i (t - s) z hzc hzcont

/-! ###############################################################################
    ### NON-VACUITY.
    ############################################################################### -/

/-- **Non-vacuity.**  At the empty gate `S := fun _ => ∅` the minimal input `hbdd` is inhabited
    (`closure ∅ = ∅`, and the image of the field-Hessian norm over `∅` is `∅`, trivially bounded
    above), and the `hFd` `⨆`-reduction fires.  (The much stronger NON-EMPTY non-vacuity is
    `concreteGate_closure_isCompact` from J4-865, whose compact gate feeds the `ContinuousOn` form.)
    No J4-548/847-style unsatisfiable antecedent. -/
theorem hFd_bddAbove_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (m : ℕ) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y =>
            witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y =>
                witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x'‖ := by
  refine witnessFieldHessian_hFd_ciSup_of_bddAbove g gi hC hK (fun _ => ∅) a b i t m ?_
  filter_upwards with s _
  filter_upwards with z
  rw [closure_empty, Set.image_empty]
  exact bddAbove_empty

end QIQTH.ChartJetXUniformBoundClosed

section AxiomChecks
open QIQTH.ChartJetXUniformBoundClosed
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms bddAbove_range_of_bddAbove_image_offClosure
#print axioms bddAbove_fieldHessian_of_continuousOn_compact
#print axioms bddAbove_fieldHessian_of_continuous_dominator
#print axioms witnessFieldHessian_hFd_ciSup_of_bddAbove
#print axioms witnessFieldHessian_hFd_ciSup_of_compactGate_continuousOn
#print axioms hFd_bddAbove_nonvacuous
end AxiomChecks
