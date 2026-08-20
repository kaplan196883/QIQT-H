/-
  ChartJetHFdFrontierClosed — J4-870: the CASE-A/CASE-B SPLIT of the `hFd` frontier residual.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick SHARPENS the frontier
  residual `hfz` of J4-869 (`ChartJetHFdBoundaryClosed`).  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.
  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE.

  J4-869 localised `MixedDirectionsFieldHessianEnvelope.hFd` to the single frontier input `hfz`:
      `∀ x ∈ frontier (S z), fderiv ℝ (fun y => witnessFieldDeriv … i (t−s) y z) x = 0`,
  and noted this is GENERICALLY true (the gated field is discontinuous at the frontier ⟹ not
  differentiable there ⟹ Mathlib's `fderiv` returns `0` by convention), but flagged a residual sliver
  at the NON-generic frontier points where the field HAPPENS to be differentiable.  This brick resolves
  the split cleanly and honestly:

    • **CASE A — `x` is NOT a point of differentiability.**  `fderiv_zero_of_not_differentiableAt`
      closes it verbatim (Mathlib convention): the discontinuous downward jump makes the field-Hessian
      vanish.  FULLY GENERAL, no gate geometry needed.  (This is the generic case; already the mechanism
      of J4-869's `frontier_fderiv_eqZero_of_not_differentiable`.)

    • **CASE B — `x` IS (surprisingly) a point of differentiability** on the frontier.  This is the
      non-generic coincidence (the smooth field-derivative ALSO vanishes continuously into `x`, so there
      is no jump).  We PROVE — fully generally — that if a real function `f`, DIFFERENTIABLE at `x` with
      `f x = 0`, vanishes eventually along a positive one-sided ray in each of a set of directions whose
      SPAN is the whole space, then `fderiv f x = 0`.  The mechanism is a chain-rule/one-sided-limit
      argument (`dirDeriv_eq_zero_of_eventually_zero_nhdsGT`): the directional derivative along any such
      direction equals the one-sided derivative of a curve that is eventually `0`, hence `0`; and a
      `ℝ`-linear map killing a spanning set is `0`.

  The frontier requirement `hfz` is then EXACTLY the fat-exterior-cone geometric predicate
  `GateFatExterior` (Case B data) at the differentiable frontier points — the honest residual is
  reduced from an opaque "`fderiv = 0` on the frontier" to a concrete, checkable statement about the
  gate's exterior geometry (that at each frontier point the OPEN exterior of the gate approaches along a
  spanning set of directions), with Case A fully mechanised.

  ⚠ HONEST RESIDUAL.  `hFd` is NOT fully discharged unconditionally: Case B's `GateFatExterior` is a
  genuine gate-geometry input.  For the concrete flow-ball gate `S z = uniformFlowExp z '' ball 0 c`,
  its exterior IS "fat" at each boundary point (the boundary is the smooth image of a sphere), but a
  Lean discharge of that geometric fact requires GLOBAL injectivity of `uniformFlowExp` on a
  neighbourhood of `closedBall 0 c` (so exterior ball points map to genuine exterior of the image),
  which is NOT among the banked local-inverse facts — so we carry `GateFatExterior` as the explicit,
  non-vacuous residual (inhabited: `GateFatExterior (fun _ => 0) T` holds for EVERY gate `T`, incl.
  non-empty).  A full `MixedDirectionsFieldHessianEnvelope` instance additionally needs the gate-bound
  `hgate`, `hLevi`/`hkint`/`hbint`, and the deep §C `hzmass`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetHFdBoundaryClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.FlowJointContinuity
open QIQTH.ChartJetXUniformBound QIQTH.ChartJetXUniformBoundClosed QIQTH.ChartJetHFdBoundaryClosed
open scoped Topology BigOperators

namespace QIQTH.ChartJetHFdFrontierClosed

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### CASE B — the general one-sided directional-vanishing forcing lemma.
    ############################################################################### -/

/-- **Directional derivative forced to `0` by one-sided eventual vanishing.**  If `f` has Fréchet
    derivative `L` at `x`, `f x = 0`, and `f (x + t • v) = 0` for `t` in a right-neighbourhood of `0`,
    then `L v = 0`.  Proof: the curve `t ↦ f (x + t • v)` has derivative `L v` at `0` (chain rule); on
    `Ioi 0` it is eventually `0` and equals `0` at `0`, so its `Ioi`-restricted derivative is `0`; the
    `Ioi 0` set has a unique derivative at `0`, forcing `L v = 0`. -/
theorem dirDeriv_eq_zero_of_eventually_zero_nhdsGT
    {f : Point n → ℝ} {x v : Point n} {L : Point n →L[ℝ] ℝ}
    (hL : HasFDerivAt f L x) (hx : f x = 0)
    (hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x + t • v) = 0) : L v = 0 := by
  -- The curve `t ↦ f (x + t • v)` has derivative `L v` at `0` — this is exactly the line derivative
  -- of `f` at `x` in direction `v`, which the Fréchet derivative supplies as `L v`.
  have hcomp : HasDerivAt (fun t : ℝ => f (x + t • v)) (L v) 0 := hL.hasLineDerivAt v
  have hg_Lv : HasDerivWithinAt (fun t : ℝ => f (x + t • v)) (L v) (Set.Ioi 0) 0 :=
    hcomp.hasDerivWithinAt
  -- The same curve is eventually `0` on `Ioi 0` and is `0` at `0`, so it has derivative `0` there.
  have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Ioi 0) 0 :=
    hasDerivWithinAt_const 0 (Set.Ioi 0) 0
  have hg_0 : HasDerivWithinAt (fun t : ℝ => f (x + t • v)) 0 (Set.Ioi 0) 0 := by
    refine hconst.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hev] with t ht using ht
    · simp only [zero_smul, add_zero]; exact hx
  -- Uniqueness of the `Ioi 0`-derivative at `0`.
  have hu : UniqueDiffWithinAt ℝ (Set.Ioi (0 : ℝ)) 0 := uniqueDiffWithinAt_Ioi 0
  have e1 : derivWithin (fun t : ℝ => f (x + t • v)) (Set.Ioi 0) 0 = L v := hg_Lv.derivWithin hu
  have e2 : derivWithin (fun t : ℝ => f (x + t • v)) (Set.Ioi 0) 0 = 0 := hg_0.derivWithin hu
  rw [e1] at e2
  exact e2

/-- **Full `fderiv` forced to `0` by spanning one-sided exterior directions.**  If `f` is
    differentiable at `x` with `f x = 0`, and along each direction `dir i` (whose span is the whole
    space) `f` vanishes on a right-neighbourhood of `0`, then `fderiv ℝ f x = 0`.  The directional
    forcing lemma kills `L` on the spanning family; a `ℝ`-linear map vanishing on a spanning set is
    `0`. -/
theorem fderiv_eq_zero_of_spanning_dirs
    {f : Point n → ℝ} {x : Point n} (hf : DifferentiableAt ℝ f x) (hx : f x = 0)
    {ι : Sort*} (dir : ι → Point n) (hspan : Submodule.span ℝ (Set.range dir) = ⊤)
    (hev : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x + t • dir i) = 0) :
    fderiv ℝ f x = 0 := by
  set L := fderiv ℝ f x with hLdef
  have hL : HasFDerivAt f L x := hf.hasFDerivAt
  have hzero : ∀ i, L (dir i) = 0 := fun i =>
    dirDeriv_eq_zero_of_eventually_zero_nhdsGT hL hx (hev i)
  have hlin : (L : Point n →ₗ[ℝ] ℝ) = 0 :=
    LinearMap.ext_on_range hspan (fun i => hzero i)
  apply ContinuousLinearMap.ext
  intro w
  have hw : (L : Point n →ₗ[ℝ] ℝ) w = 0 := by rw [hlin]; rfl
  simpa using hw

/-! ###############################################################################
    ### THE FAT-EXTERIOR GATE PREDICATE + the CASE-A/CASE-B combination.
    ############################################################################### -/

/-- **The fat-exterior-cone gate predicate (Case-B data).**  At every frontier point of `T` where `f`
    is differentiable, `f` vanishes at the point and along a SPANNING set of one-sided directions —
    exactly what Case B needs.  (At the discontinuous — non-differentiable — frontier points, Case A
    supplies `fderiv = 0` without any data; this predicate only carries the non-generic differentiable
    frontier points.) -/
def GateFatExterior (f : Point n → ℝ) (T : Set (Point n)) : Prop :=
  ∀ x ∈ frontier T, DifferentiableAt ℝ f x →
    f x = 0 ∧ ∃ dir : Fin n → Point n,
      Submodule.span ℝ (Set.range dir) = ⊤ ∧
      ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x + t • dir i) = 0

/-- **Case A + Case B ⟹ field-Hessian vanishes on the whole frontier.**  Splitting each frontier point
    by differentiability: Case A (`fderiv_zero_of_not_differentiableAt`) for the generic discontinuous
    points, Case B (`fderiv_eq_zero_of_spanning_dirs`, fed by `GateFatExterior`) for the non-generic
    differentiable ones. -/
theorem frontier_fderiv_eqZero_of_fatExterior (f : Point n → ℝ) (T : Set (Point n))
    (h : GateFatExterior f T) : ∀ x ∈ frontier T, fderiv ℝ f x = 0 := by
  intro x hx
  by_cases hd : DifferentiableAt ℝ f x
  · obtain ⟨hx0, dir, hspan, hev⟩ := h x hx hd
    exact fderiv_eq_zero_of_spanning_dirs hd hx0 dir hspan hev
  · exact fderiv_zero_of_not_differentiableAt hd

/-! ###############################################################################
    ### NON-VACUITY of the predicate.
    ############################################################################### -/

/-- **`GateFatExterior` is genuinely inhabited (not just at the empty gate).**  The zero function
    satisfies it for EVERY gate `T` (including non-empty ones with non-empty frontier): at any point
    `f = 0`, and the standard basis `Pi.basisFun` gives a spanning family along which `f ≡ 0`.  This
    rules out a J4-548/847-style vacuously-unsatisfiable predicate. -/
theorem gateFatExterior_zero (T : Set (Point n)) :
    GateFatExterior (fun _ => (0 : ℝ)) T := by
  intro x _ _
  refine ⟨rfl, (⇑(Pi.basisFun ℝ (Fin n))), (Pi.basisFun ℝ (Fin n)).span_eq, ?_⟩
  intro i
  exact Filter.Eventually.of_forall (fun t => rfl)

/-- **`GateFatExterior` at the empty gate is vacuously true** (`frontier ∅ = ∅`). -/
theorem gateFatExterior_empty (f : Point n → ℝ) :
    GateFatExterior f (∅ : Set (Point n)) := by
  intro x hx
  rw [frontier_empty] at hx
  exact absurd hx (Set.notMem_empty x)

/-! ###############################################################################
    ### THE SHARPENED `hFd` REDUCTION.
    ############################################################################### -/

/-- **★★ THE FAT-EXTERIOR `hFd` REDUCTION.**  The EXACT `hFd` field of
    `MixedDirectionsFieldHessianEnvelope` (envelope `BF s z := ⨆ x, ‖fderiv …‖`), reduced a.e. to:
      • `hgate` — the field-Hessian norm is bounded above on the GATE `S z` (the smooth interior);
      • `hfat`  — the `GateFatExterior` predicate for the witness field on `S z` (Case-B geometry).
    Strictly refines J4-869's `witnessFieldHessian_hFd_ciSup_of_gateBdd_frontierZero`: the opaque
    frontier-vanishing `hfz` is now DISCHARGED from `hfat` via the fully-general Case-A/Case-B split
    (`frontier_fderiv_eqZero_of_fatExterior`).  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_hFd_ciSup_of_gateBdd_fatExterior (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ)
    (hgate : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume,
          BddAbove ((fun x =>
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)
              '' S z))
    (hfat : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume,
          GateFatExterior (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) (S z)) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  refine witnessFieldHessian_hFd_ciSup_of_gateBdd_frontierZero g gi hC hK S a b i t m hgate ?_
  filter_upwards [hfat] with s hfs hsUioc
  filter_upwards [hfs hsUioc] with z hzf
  exact frontier_fderiv_eqZero_of_fatExterior
    (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) (S z) hzf

/-- **Non-vacuity.**  At the empty gate `S := fun _ => ∅` both inputs are inhabited
    (`gateFatExterior_empty`, `Set.image_empty` bounded) and the `hFd` `⨆`-reduction fires.  No
    J4-548/847-style unsatisfiable antecedent. -/
theorem hFd_fatExterior_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (m : ℕ) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y =>
            witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y =>
                witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x'‖ := by
  refine witnessFieldHessian_hFd_ciSup_of_gateBdd_fatExterior g gi hC hK (fun _ => ∅) a b i t m ?_ ?_
  · filter_upwards with s _
    filter_upwards with z
    rw [Set.image_empty]
    exact bddAbove_empty
  · filter_upwards with s _
    filter_upwards with z
    exact gateFatExterior_empty _

end QIQTH.ChartJetHFdFrontierClosed

section AxiomChecks
open QIQTH.ChartJetHFdFrontierClosed
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms dirDeriv_eq_zero_of_eventually_zero_nhdsGT
#print axioms fderiv_eq_zero_of_spanning_dirs
#print axioms frontier_fderiv_eqZero_of_fatExterior
#print axioms gateFatExterior_zero
#print axioms gateFatExterior_empty
#print axioms witnessFieldHessian_hFd_ciSup_of_gateBdd_fatExterior
#print axioms hFd_fatExterior_nonvacuous
end AxiomChecks
