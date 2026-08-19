/-
  MixedFieldHessianOpNormCombinator — J4-863 (b2): the CLM OPERATOR-NORM combinator that assembles the
  per-index (diagonal + off-diagonal) scalar Hessian bounds into a single operator-norm bound on the
  field-Hessian CLM `fderiv ℝ (fun y => witnessFieldDeriv … i τ y z) x` — the exact object the
  `MixedDirectionsFieldHessianEnvelope.hFd` field (J4-843) requires.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  This brick performs the purely-linear-algebraic assembly step (b2):
  it takes the ALREADY-BANKED per-entry scalar Hessian bounds — the DIAGONAL
  `SecondDerivEnvelope.witnessFieldDeriv2_gate_abs_le` (`∂ᵢ∂ᵢH`) and the OFF-DIAGONAL
  `WitnessMixedHessianMagnitudeBound.witnessMixed_gate_abs_le` (`∂ᵢ∂ⱼH`, J4-862) — and combines the
  `n` of them into an operator-norm bound `‖fderiv (∂ᵢH)‖ ≤ Σⱼ bbⱼ` on the full field-gradient CLM
  that `kPrime` carries (`FderivBulkConcrete.kPrime`).  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.
  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE NORM STRUCTURE (why the combination constant is the ℓ¹ SUM, no equivalence factor).

  `Point n = Fin n → ℝ` (`Curvature.Point`) carries the Pi / **SUP** norm (`‖v‖ = ⊔ⱼ |vⱼ|`).  For a
  continuous linear FUNCTIONAL `L : (Fin n → ℝ) →L[ℝ] ℝ` this makes the operator norm the ℓ¹ dual:
    `‖L‖ ≤ Σⱼ |L eⱼ|`  (the SUM of the basis-component magnitudes; NO norm-equivalence constant).
  This exact reduction is the ALREADY-BANKED `KPrimeOpNormSliver.opNorm_le_sum_apply_single` (J4-779).
  The genuinely-new bridge here is `pd_eq_fderiv` (`Curvature`): `fderiv ℝ f x eⱼ = pd f j x`, which
  turns each basis-component `|L eⱼ|` into the partial-derivative magnitude `|∂ⱼ(∂ᵢH)|` that the banked
  entrywise envelopes control.

  ## THE DELIVERABLE (ns `QIQTH.MixedFieldHessianOpNormCombinator`).

    • `opNorm_fderiv_le_sum_pd` — ★ PURE, GENERIC: for differentiable `f : Point n → ℝ`, if every
      partial obeys `|pd f j x| ≤ bb j` then `‖fderiv ℝ f x‖ ≤ Σⱼ bb j`.  (Sup-norm ⇒ ℓ¹ dual, via
      `opNorm_le_sum_apply_single` fed the `pd_eq_fderiv` bridge.)

    • `witnessFieldHessian_opNorm_le_sum` — ★★ the specialised per-`x` field-Hessian combinator:
      `‖fderiv ℝ (fun y => witnessFieldDeriv … i τ y z) x‖ ≤ Σⱼ bb j` from per-index `pd`-bounds.

    • `witnessFieldHessian_component_diag_eq` / `witnessFieldHessian_component_offdiag_eq` — ★ the two
      BRIDGE IDENTITIES routing each `bb j` slot to the banked entrywise envelope: the `j = i` component
      IS `witnessFieldDeriv2 … i τ x z` (bounded by the DIAGONAL envelope), and the `j ≠ i` component IS
      the mixed Hessian object `pd (∂ᵢH) j` (bounded by `witnessMixed_gate_abs_le` at index roles
      `(i,j) ↦ (j,i)`).  Both are `rfl` (pure definitional unfolding of `witnessFieldDeriv`).

    • `witnessFieldHessian_opNorm_le_piecewise` — ★★★ THE ASSEMBLY: given ONE diagonal bound `bdiag`
      and the `n−1` off-diagonal bounds `boff j`, `‖fderiv ℝ (∂ᵢH) x‖ ≤ Σⱼ (if j = i then bdiag else
      boff j)` — the literal "combine the entrywise scalar bounds into a single CLM operator-norm
      bound" step.

    • `witnessFieldHessian_opNorm_xuniform` — ★★★ the `hFd` SHAPE: if the per-index bounds are
      `x`-UNIFORM (`bb` independent of `x`), then `∀ x, ‖fderiv ℝ (fun y => witnessFieldDeriv … i τ y z)
      x‖ ≤ Σⱼ bb j` — EXACTLY `MixedDirectionsFieldHessianEnvelope.hFd`'s inner statement with
      `BF s z := Σⱼ bb j` (at `τ := t − s`).  So `hFd` REDUCES to an `x`-uniform per-index Hessian
      bound — the operator-norm combination is now closed; the residual is the `x`-uniformisation of the
      entrywise envelopes (`WitnessMixedPartialUniformBound` Part-2 content), NOT the CLM assembly.

  ## `x`-UNIFORMITY (verified, item 4 of the brief).  The entrywise envelope RHS
  `gaussDdim τ (uniformInverseChart z p) · (…)` of BOTH banked bounds is evaluated at `p = x`, hence is
  NOT `x`-free in its raw form; `hFd` needs an `x`-uniform `BF`.  `witnessFieldHessian_opNorm_xuniform`
  therefore takes the per-index bounds ALREADY in `x`-uniform form (`∀ x j, |pd … j x| ≤ bb j`, `bb`
  not depending on `x`) and delivers precisely the `x`-uniform `hFd` conclusion.  The combinator is
  genuinely `x`-uniform: no hypothesis or constant depends on `x` beyond the supplied uniform `bb`.

  ## NON-VACUITY.  `witnessFieldHessian_opNorm_le_sum_tight` instantiates `bb j := |pd … j x|` at the
  tightest values (every side-condition `le_refl`), so the combinator's antecedent set is inhabited
  precisely when the witness field-derivative is differentiable at `x` — which holds for the smooth
  gate data (the concrete curved witness of the banked diagonal/mixed measurability chain).  No
  conclusion-in-disguise; no unsatisfiable antecedent.  All mains std-3.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.KPrimeOpNormSliver
import QIQTH.SecondDerivEnvelope
import QIQTH.WitnessMixedHessianMagnitudeBound

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.FlatHeatEquation
open scoped Topology Interval BigOperators

namespace QIQTH.MixedFieldHessianOpNormCombinator

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C0 — the generic sup-norm ⇒ ℓ¹ fderiv bound from partial-derivative bounds.
    ############################################################################### -/

/-- **★ C0 — `opNorm_fderiv_le_sum_pd`.**  Generic: on `Point n = Fin n → ℝ` (the SUP norm), the
    operator norm of the Fréchet derivative of a differentiable scalar field is bounded by the ℓ¹ sum of
    its partial-derivative magnitudes: if `|pd f j x| ≤ bb j` for every `j`, then
    `‖fderiv ℝ f x‖ ≤ Σⱼ bb j`.  Combines the banked ℓ¹ operator-norm reduction
    `KPrimeOpNormSliver.opNorm_le_sum_apply_single` with the `pd_eq_fderiv` bridge
    `fderiv ℝ f x eⱼ = pd f j x`.  NOT `a₁ = R/6`. -/
theorem opNorm_fderiv_le_sum_pd (f : Point n → ℝ) (x : Point n) (bb : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x) (hb : ∀ j, |pd f j x| ≤ bb j) :
    ‖fderiv ℝ f x‖ ≤ ∑ j, bb j := by
  refine QIQTH.KPrimeOpNormSliver.opNorm_le_sum_apply_single (fderiv ℝ f x) bb (fun j => ?_)
  rw [← pd_eq_fderiv f j x hf]
  exact hb j

/-! ###############################################################################
    ### C1 — the specialised per-`x` field-Hessian operator-norm combinator.
    ############################################################################### -/

/-- **★★ C1 — `witnessFieldHessian_opNorm_le_sum`.**  The field-Hessian CLM `fderiv ℝ (fun y =>
    witnessFieldDeriv … i τ y z) x` (the object `FderivBulkConcrete.kPrime` carries, scaled by the Levi
    factor) has operator norm bounded by the ℓ¹ sum of its per-index second-partial magnitudes: from
    differentiability of `y ↦ witnessFieldDeriv … i τ y z` at `x` and per-index bounds
    `|pd (fun y => witnessFieldDeriv … i τ y z) j x| ≤ bb j`,
      `‖fderiv ℝ (fun y => witnessFieldDeriv … i τ y z) x‖ ≤ Σⱼ bb j`.
    NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_opNorm_le_sum (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (x z : Point n) (bb : Fin n → ℝ)
    (hf : DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x)
    (hb : ∀ j, |pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) j x| ≤ bb j) :
    ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖ ≤ ∑ j, bb j :=
  opNorm_fderiv_le_sum_pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x bb hf hb

/-! ###############################################################################
    ### C2 — the two BRIDGE IDENTITIES routing each `bb j` slot to a banked envelope.
    ############################################################################### -/

/-- **★ C2a — `witnessFieldHessian_component_diag_eq`.**  The `j = i` (DIAGONAL) component of the
    field-Hessian is definitionally the second field-derivative kernel `witnessFieldDeriv2 … i τ x z`,
    hence bounded by the banked DIAGONAL envelope `SecondDerivEnvelope.witnessFieldDeriv2_gate_abs_le`.
    Pure unfolding of `witnessFieldDeriv`/`witnessFieldDeriv2`.  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_component_diag_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (x z : Point n) :
    pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) i x
      = witnessFieldDeriv2 g gi hC hK S a b i τ x z := rfl

/-- **★ C2b — `witnessFieldHessian_component_offdiag_eq`.**  The `j ≠ i` (OFF-DIAGONAL) component of the
    field-Hessian is definitionally the mixed Hessian object `pd (fun y => pd (∂ᵢH-integrand) i y) j x`
    — exactly the object the banked OFF-DIAGONAL envelope
    `WitnessMixedHessianMagnitudeBound.witnessMixed_gate_abs_le` bounds when its two index arguments are
    taken in the order `(i,j) ↦ (j,i)` (outer `j`, inner `i`).  Pure unfolding of `witnessFieldDeriv`.
    NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_component_offdiag_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (x z : Point n) :
    pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) j x
      = pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y) j x := rfl

/-- **★ C2c — `witnessFieldHessian_component_offdiag_le`.**  Bound-transport form of C2b: any bound on
    the mixed Hessian object (e.g. the banked `witnessMixed_gate_abs_le` at index roles `(j,i)`)
    transports verbatim to the off-diagonal field-Hessian component.  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_component_offdiag_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (x z : Point n) (Bnd : ℝ)
    (hmixed : |pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y) j x|
        ≤ Bnd) :
    |pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) j x| ≤ Bnd := hmixed

/-! ###############################################################################
    ### C3 — THE ASSEMBLY: combine one diagonal + `n−1` off-diagonal bounds.
    ############################################################################### -/

/-- **★★★ C3 — `witnessFieldHessian_opNorm_le_piecewise`.**  THE literal b2 assembly: given ONE diagonal
    bound `bdiag` on the `∂ᵢ∂ᵢH` component and the `n−1` off-diagonal bounds `boff j` on the `∂ⱼ∂ᵢH`
    (`j ≠ i`) components, the full field-Hessian CLM obeys the single operator-norm bound
      `‖fderiv ℝ (fun y => witnessFieldDeriv … i τ y z) x‖ ≤ Σⱼ (if j = i then bdiag else boff j)`.
    This is exactly "combine the `n²`/`n(n−1)` entrywise scalar bounds into one CLM operator-norm
    bound".  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_opNorm_le_piecewise (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (x z : Point n) (bdiag : ℝ) (boff : Fin n → ℝ)
    (hf : DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x)
    (hdiag : |pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) i x| ≤ bdiag)
    (hoff : ∀ j, j ≠ i →
        |pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) j x| ≤ boff j) :
    ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖
      ≤ ∑ j, (if j = i then bdiag else boff j) := by
  refine witnessFieldHessian_opNorm_le_sum g gi hC hK S a b i τ x z
    (fun j => if j = i then bdiag else boff j) hf (fun j => ?_)
  by_cases hj : j = i
  · subst hj; simpa only [if_pos rfl] using hdiag
  · simpa only [if_neg hj] using hoff j hj

/-! ###############################################################################
    ### C4 — THE `hFd` SHAPE: the `x`-uniform combinator.
    ############################################################################### -/

/-- **★★★ C4 — `witnessFieldHessian_opNorm_xuniform`.**  THE `MixedDirectionsFieldHessianEnvelope.hFd`
    reduction: if the per-index second-partial bounds are `x`-UNIFORM (`bb` independent of `x`), then
      `∀ x, ‖fderiv ℝ (fun y => witnessFieldDeriv … i τ y z) x‖ ≤ Σⱼ bb j`,
    which is EXACTLY the inner statement of `hFd` with `BF s z := Σⱼ bb j` (at `τ := t − s`).  So the
    `hFd` field REDUCES to an `x`-uniform per-index Hessian bound: the CLM operator-norm combination is
    fully discharged here; the only residual is the `x`-uniformisation of the (banked, `x`-pointwise)
    diagonal/mixed entrywise envelopes.  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_opNorm_xuniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (bb : Fin n → ℝ)
    (hf : ∀ x, DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x)
    (hb : ∀ x j, |pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) j x| ≤ bb j) :
    ∀ x, ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖ ≤ ∑ j, bb j :=
  fun x => witnessFieldHessian_opNorm_le_sum g gi hC hK S a b i τ x z bb (hf x) (fun j => hb x j)

/-! ###############################################################################
    ### C5 — NON-VACUITY WITNESS (tightest bounds need only differentiability).
    ############################################################################### -/

/-- **★ C5 — `witnessFieldHessian_opNorm_le_sum_tight`.**  Instantiating the per-index bounds at their
    tightest values `bb j := |pd … j x|` (every side-condition `le_refl`) needs NOTHING beyond
    differentiability of `y ↦ witnessFieldDeriv … i τ y z` at `x`.  This exhibits the combinator's
    antecedent set as inhabited precisely when the witness field-derivative is differentiable at `x`
    (which holds for the smooth gate data of the banked diagonal/mixed measurability chain) — no
    unsatisfiable antecedent, no conclusion-in-disguise.  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_opNorm_le_sum_tight (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (x z : Point n)
    (hf : DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x) :
    ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖
      ≤ ∑ j, |pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) j x| :=
  witnessFieldHessian_opNorm_le_sum g gi hC hK S a b i τ x z
    (fun j => |pd (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) j x|) hf
    (fun _ => le_refl _)

end QIQTH.MixedFieldHessianOpNormCombinator

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedFieldHessianOpNormCombinator
#print axioms opNorm_fderiv_le_sum_pd
#print axioms witnessFieldHessian_opNorm_le_sum
#print axioms witnessFieldHessian_component_diag_eq
#print axioms witnessFieldHessian_component_offdiag_eq
#print axioms witnessFieldHessian_component_offdiag_le
#print axioms witnessFieldHessian_opNorm_le_piecewise
#print axioms witnessFieldHessian_opNorm_xuniform
#print axioms witnessFieldHessian_opNorm_le_sum_tight
end AxiomChecks
