/-
  ChartJetHFdBoundaryClosed — J4-869: the FRONTIER LOCALISATION of the `hFd` boundary residual.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick SHARPENS the honest residual
  `hbdd` of J4-866 (`ChartJetXUniformBoundClosed`).  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.
  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PART-1 FACT-FINDING VERDICT (the mission's two hoped-for shortcuts, both refuted precisely).

  The gate is a HARD indicator gate (`gatedKernel … = if q∈K then (if p∈S q then H else 0) else 0`,
  `GlobalHunifAssembly`), so the gated FIELD `y ↦ witnessFieldDeriv … y z` (`= pd_i` of the gated
  van-Vleck witness) is DISCONTINUOUS at `∂(S z)` (it equals the smooth field-`pd` on the OPEN interior
  and `0` off `closure (S z)`).  The object `hbdd` bounds is `x ↦ ‖fderiv (y ↦ witnessFieldDeriv … y z)
  x‖` — the field-HESSIAN norm, i.e. `‖fderiv (gated field)‖`, NOT `gated (‖fderiv (smooth field)‖)`.
  That distinction refutes BOTH hoped-for shortcuts:

    (a)  "off-gate = 0 makes it trivial."  FALSE for `hbdd`.  The off-gate vanishing
         (`witnessFieldHessian_fderiv_eqZero_of_notMem_closure`) bounds the field-Hessian norm OUTSIDE
         `closure (S z)` — it says nothing about its values ON `closure (S z)`, which is exactly the set
         `hbdd`'s image ranges over.  (It is already fully exploited by J4-866's
         `bddAbove_range_of_bddAbove_image_offClosure` to pass from image-on-closure to global range;
         it cannot ALSO discharge the image-on-closure bound.)

    (b)  "upper-semicontinuity attains the max."  FALSE as stated.  At `x ∈ ∂(S z)` the gated field is
         discontinuous, hence NOT differentiable, so Mathlib's `fderiv` returns `0` there — the
         field-Hessian norm DROPS to `0` at the frontier while interior points near `x` carry the
         (generically non-zero) smooth Hessian.  That is a DOWNWARD jump, which BREAKS upper-
         semicontinuity at `∂(S z)` (`limsup > value`).  The standard `IsOpen.upperSemicontinuousOn`
         lemmas apply to `1_S · f`, not to `‖fderiv (1_S · f)‖`; the derivative does not commute with
         the gate.  So neither shortcut closes `hbdd`.

  ## WHAT THIS BRICK ADDS (the correct, honest advance).

  A fully-general set-topology split `closure T ⊆ T ∪ frontier T` LOCALISES the residual: the field-
  Hessian is bounded on the compact `closure (S z)` iff it is bounded on the gate `S z` AND on the
  FRONTIER `frontier (S z)`.  The first piece is where the field is SMOOTH (`S z` open ⟹ gated = ungated
  locally), so it is the tractable part; the second is the genuine boundary content — now sharply
  isolated to the frontier (a LOWER-dimensional set) instead of the whole closure.  And the frontier
  piece is discharged EXACTLY when the field-Hessian VANISHES on `∂(S z)` — which, by (b) above, is the
  generic situation (the field is discontinuous there, so `fderiv = 0`).  We bank:

    • `closure_subset_self_union_frontier` — `closure T ⊆ T ∪ frontier T` (fully general).
    • `bddAbove_image_closure_of_gate_frontier` — `BddAbove (F '' closure T)` from bounds on `F '' T`
      and `F '' frontier T`.
    • `bddAbove_image_frontier_of_fderiv_zero` — the frontier field-Hessian image is bounded (by `0`)
      when `fderiv (gated field) = 0` on `frontier (S z)`.
    • `frontier_fderiv_eqZero_of_not_differentiable` — the generic mechanism: at any frontier point
      where the gated field is NOT differentiable, `fderiv = 0` (Mathlib convention) — i.e. the DOWNWARD
      jump of (b) makes the field-Hessian vanish there automatically.
    • `witnessFieldHessian_hFd_ciSup_of_gateBdd_frontierZero` — ★★ the EXACT `hFd` field of
      `MixedDirectionsFieldHessianEnvelope` (envelope `BF s z := ⨆ x, ‖fderiv …‖`), reduced a.e. to the
      SHARPENED pair {field-Hessian bounded on the gate `S z`, field-Hessian vanishes on `∂(S z)`}.
      Strictly refines J4-866's single `hbdd` (bounded on the whole closure).
    • `hFd_frontierLocalised_nonvacuous` — antecedents inhabited at the empty gate.

  ⚠ HONEST RESIDUAL.  The boundary problem is NOT eliminated — it is LOCALISED to `frontier (S z)` and
  characterised as field-Hessian vanishing there.  A full `MixedDirectionsFieldHessianEnvelope` instance
  additionally needs `hLevi`/`hkint`/`hbint` and the deep §C `hzmass`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetXUniformBoundClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.FlowJointContinuity
open QIQTH.ChartJetXUniformBound QIQTH.ChartJetXUniformBoundClosed
open scoped Topology BigOperators

namespace QIQTH.ChartJetHFdBoundaryClosed

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### THE GENERAL SET-TOPOLOGY SPLIT.
    ############################################################################### -/

/-- **General split.**  Every point of `closure T` is either in `T` (via `interior T ⊆ T`) or in the
    frontier `frontier T = closure T \ interior T`.  Hence `closure T ⊆ T ∪ frontier T`.  This is the
    localisation that confines the honest boundary residual to `frontier (S z)`. -/
theorem closure_subset_self_union_frontier (T : Set (Point n)) :
    closure T ⊆ T ∪ frontier T := by
  intro x hx
  by_cases hi : x ∈ interior T
  · exact Or.inl (interior_subset hi)
  · exact Or.inr ⟨hx, hi⟩

/-- **`BddAbove` on the closure from gate + frontier bounds.**  If `F` is bounded above on the gate `T`
    and on its frontier, it is bounded above on `closure T` (which `closure_subset_self_union_frontier`
    covers by `T ∪ frontier T`).  This is the exact `hbdd`-shape J4-866 consumes, with the closure
    replaced by its two honest pieces. -/
theorem bddAbove_image_closure_of_gate_frontier (F : Point n → ℝ) (T : Set (Point n))
    (hgate : BddAbove (F '' T)) (hfront : BddAbove (F '' frontier T)) :
    BddAbove (F '' closure T) := by
  have hsub : F '' closure T ⊆ (F '' T) ∪ (F '' frontier T) := by
    rw [← Set.image_union]
    exact Set.image_mono (closure_subset_self_union_frontier T)
  exact (hgate.union hfront).mono hsub

/-! ###############################################################################
    ### THE FRONTIER PIECE — vanishing field-Hessian bounds it.
    ############################################################################### -/

/-- **Frontier field-Hessian image bounded from frontier vanishing.**  If the gated field-Hessian CLM
    `fderiv (y ↦ witnessFieldDeriv … y z)` vanishes at every frontier point of the gate, then the
    field-Hessian norm is `≤ 0` on `frontier (S z)`, so its image there is bounded above (by `0`). -/
theorem bddAbove_image_frontier_of_fderiv_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n)
    (hfz : ∀ x ∈ frontier (S z),
        fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0) :
    BddAbove ((fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖)
      '' frontier (S z)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  simp only
  rw [hfz x hx]
  simp

/-- **The generic frontier mechanism (Part-1 verdict (b), formalised).**  At any frontier point where
    the gated field `y ↦ witnessFieldDeriv … y z` is NOT differentiable, Mathlib's `fderiv` returns `0`.
    Since the gated field is discontinuous across `∂(S z)` (smooth inside, `0` outside), it fails to be
    differentiable there generically — so the field-Hessian VANISHES on `∂(S z)` automatically, which is
    exactly the downward jump that BREAKS upper-semicontinuity yet HELPS the `BddAbove` residual. -/
theorem frontier_fderiv_eqZero_of_not_differentiable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (x : Point n)
    (hnd : ¬ DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x) :
    fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0 :=
  fderiv_zero_of_not_differentiableAt hnd

/-! ###############################################################################
    ### THE SHARPENED `hFd` REDUCTION.
    ############################################################################### -/

/-- **★★ THE FRONTIER-LOCALISED `hFd` REDUCTION.**  The EXACT `hFd` field of
    `MixedDirectionsFieldHessianEnvelope`, with the EXPLICIT envelope
    `BF s z := ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x‖`, reduced a.e. to the SHARPENED pair:
      • `hgate` — the field-Hessian norm is bounded above on the GATE `S z` (where the field is smooth);
      • `hfz`   — the field-Hessian VANISHES on the FRONTIER `∂(S z)` (the generic boundary situation).
    Strictly refines J4-866's `witnessFieldHessian_hFd_ciSup_of_bddAbove` (which needed boundedness on
    the WHOLE closure): the honest residual is now split into a smooth-interior piece and a frontier
    piece.  Discharged by feeding `bddAbove_image_closure_of_gate_frontier` into the J4-866 reduction.
    NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_hFd_ciSup_of_gateBdd_frontierZero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ)
    (hgate : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume,
          BddAbove ((fun x =>
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
              '' S z))
    (hfz : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ x ∈ frontier (S z),
          fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x = 0) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  refine witnessFieldHessian_hFd_ciSup_of_bddAbove g gi hC hK S a b i t m ?_
  filter_upwards [hgate, hfz] with s hgs hfzs hsUioc
  filter_upwards [hgs hsUioc, hfzs hsUioc] with z hzg hzf
  exact bddAbove_image_closure_of_gate_frontier
    (fun x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖) (S z)
    hzg
    (bddAbove_image_frontier_of_fderiv_zero g gi hC hK S a b i (t - s) z hzf)

/-! ###############################################################################
    ### NON-VACUITY.
    ############################################################################### -/

/-- **Non-vacuity.**  At the empty gate `S := fun _ => ∅` both sharpened inputs are inhabited
    (`frontier ∅ = ∅`, `F '' ∅ = ∅` trivially bounded above, and the frontier-vanishing is vacuous),
    and the `hFd` `⨆`-reduction fires.  No J4-548/847-style unsatisfiable antecedent. -/
theorem hFd_frontierLocalised_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (m : ℕ) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y =>
            witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y =>
                witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x'‖ := by
  refine witnessFieldHessian_hFd_ciSup_of_gateBdd_frontierZero g gi hC hK (fun _ => ∅) a b i t m ?_ ?_
  · filter_upwards with s _
    filter_upwards with z
    rw [Set.image_empty]
    exact bddAbove_empty
  · filter_upwards with s _
    filter_upwards with z
    intro x hx
    rw [frontier_empty] at hx
    exact absurd hx (Set.notMem_empty x)

end QIQTH.ChartJetHFdBoundaryClosed

section AxiomChecks
open QIQTH.ChartJetHFdBoundaryClosed
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms closure_subset_self_union_frontier
#print axioms bddAbove_image_closure_of_gate_frontier
#print axioms bddAbove_image_frontier_of_fderiv_zero
#print axioms frontier_fderiv_eqZero_of_not_differentiable
#print axioms witnessFieldHessian_hFd_ciSup_of_gateBdd_frontierZero
#print axioms hFd_frontierLocalised_nonvacuous
end AxiomChecks
