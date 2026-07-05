import QIQTH.Spectral.MultiplicationOp
import QIQTH.Spectral.PVM
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The position projection-valued measure on `L²(μ)`

Bundles the multiplication-operator spectral-projection bricks of `QIQTH.Spectral.Multiplication`
(`MultiplicationOp.lean`) into a genuine `QIQTH.Spectral.ProjectionValuedMeasure α (Lp ℂ 2 μ)`: the
**position PVM**, `E(A) = M_{𝟙_A}` (multiplication by the indicator of `A`). All the structure fields —
self-adjoint idempotents, `E(∅)=0`, `E(univ)=1`, multiplicativity `E(A∩B)=E(A)·E(B)`, and the strong
(`HasSum`) countable σ-additivity `∑ₙ E(Aₙ)x = E(⋃Aₙ)x` for pairwise-disjoint measurable `Aₙ` — are the
machine-checked bricks 1–15. This is the canonical PVM whose Fourier-Plancherel conjugate is the momentum
PVM (the route to the boost generator / `WedgeKMSFlux #5`); axiom-free.
-/

namespace QIQTH.Spectral.Multiplication

open MeasureTheory
open scoped Classical

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The position PVM's projection on an arbitrary set: `E(A) = M_{𝟙_A}` on measurable `A`, `0` otherwise. -/
noncomputable def posPVM_E (A : Set α) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  if h : MeasurableSet A then indMul h else 0

theorem posPVM_E_eq {A : Set α} (hA : MeasurableSet A) : posPVM_E (μ := μ) A = indMul hA := dif_pos hA

/-- **The position projection-valued measure** on `L²(μ)`: `E(A) = M_{𝟙_A}`. The bundled
    `ProjectionValuedMeasure` assembled from the spectral-projection bricks (self-adjoint idempotents, the
    PV-content identities, and the strong `HasSum` σ-additivity). -/
noncomputable def positionPVM : ProjectionValuedMeasure α (Lp ℂ 2 μ) where
  E := posPVM_E
  isSA := fun _ hs => by rw [posPVM_E_eq hs]; exact indMul_isSelfAdjoint hs
  isIdem := fun _ hs => by rw [posPVM_E_eq hs]; exact indMul_idempotent hs
  E_empty := by rw [posPVM_E_eq MeasurableSet.empty, indMul_empty]
  E_univ := by rw [posPVM_E_eq MeasurableSet.univ, indMul_univ]
  E_inter := fun _ _ hs ht => by
    rw [posPVM_E_eq (hs.inter ht), posPVM_E_eq hs, posPVM_E_eq ht]
    exact (indMul_inter hs ht).symm
  hasSum_iUnion := fun {A} hAmeas hd x => by
    have e1 : (fun n => posPVM_E (μ := μ) (A n) x) = (fun n => indMul (hAmeas n) x) := by
      funext n; rw [posPVM_E_eq (hAmeas n)]
    rw [e1, posPVM_E_eq (MeasurableSet.iUnion hAmeas)]
    exact hasSum_indMul_iUnion hAmeas hd x

/-- **The position PVM's scalar mass is the Born `|ψ|²` measure of `A`:** `‖E(A)x‖² = ∫_A ‖x‖² dμ` — the `L²`
    mass of the state `x` on `A`. As `A` varies this *is* the (unnormalized) Born position-probability
    distribution `|ψ(a)|² dμ(a)` of the state. -/
theorem positionPVM_norm_sq (x : Lp ℂ 2 μ) {A : Set α} (hA : MeasurableSet A) :
    ‖(positionPVM (μ := μ)).E A x‖ ^ 2 = ∫ a in A, ‖x a‖ ^ 2 ∂μ := by
  rw [show (positionPVM (μ := μ)).E A = indMul hA from posPVM_E_eq hA, norm_indMul_sq]

/-- **The position PVM's scalar spectral measure is the Born `|ψ|²` position measure:**
    `(scalarMeasure x)(A) = ENNReal.ofReal (∫_A ‖x‖² dμ)`. The spectral measure of the position observable
    *is* the position-probability distribution of the state — the Born rule for position, read off the PVM. -/
theorem positionPVM_scalarMeasure (x : Lp ℂ 2 μ) {A : Set α} (hA : MeasurableSet A) :
    (positionPVM (μ := μ)).scalarMeasure x A = ENNReal.ofReal (∫ a in A, ‖x a‖ ^ 2 ∂μ) := by
  rw [(positionPVM (μ := μ)).scalarMeasure_apply x hA]
  congr 1
  rw [show (positionPVM (μ := μ)).E A = indMul hA from posPVM_E_eq hA, norm_indMul_sq]

/-- **The position scalar spectral measure is the Born `|x|²` density measure:**
    `scalarMeasure x = μ.withDensity (a ↦ ‖x a‖²)` — the position-probability distribution of the state `x` is
    the measure with Radon–Nikodym density `|x|²` w.r.t. `μ`. The measure-level form of the Born rule for
    position (the set-level `positionPVM_scalarMeasure` integrated against `withDensity`). -/
theorem positionPVM_scalarMeasure_eq_withDensity (x : Lp ℂ 2 μ) :
    (positionPVM (μ := μ)).scalarMeasure x
      = μ.withDensity (fun a => ENNReal.ofReal (‖x a‖ ^ 2)) := by
  have hxsq : MeasureTheory.Integrable (fun a => ‖x a‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x)).mp (Lp.memLp x)
  refine MeasureTheory.Measure.ext fun A hA => ?_
  rw [positionPVM_scalarMeasure x hA, MeasureTheory.withDensity_apply _ hA]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hxsq.restrict
    (Filter.Eventually.of_forall fun a => sq_nonneg _)

/-- **The position Born expectation value:** the position PVM's diagonal functional is the `|x|²`-weighted
    integral, `⟪f(X)⟫_x = D_f(x) = ∫ f(a) ‖x a‖² dμ`. The expectation of any bounded function `f` of the
    position observable in the (unnormalized) state `x` is `∫ f(a) |x(a)|² da` — the Born expectation rule for
    position, read off the spectral measure (`diagInt = ∫ f d(scalarMeasure x)` against the `|x|²` density). -/
theorem positionPVM_diagInt (f : α → ℂ) (x : Lp ℂ 2 μ) :
    (positionPVM (μ := μ)).diagInt f x = ∫ a, f a * (‖x a‖ ^ 2 : ℂ) ∂μ := by
  rw [ProjectionValuedMeasure.diagInt, positionPVM_scalarMeasure_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul₀
      ((Lp.aestronglyMeasurable x).norm.aemeasurable.pow_const 2).ennreal_ofReal
      (Filter.Eventually.of_forall fun a => ENNReal.ofReal_lt_top) f]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  show (ENNReal.ofReal (‖x a‖ ^ 2)).toReal • f a = f a * (‖x a‖ ^ 2 : ℂ)
  rw [ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  push_cast
  ring

/-- **The bounded-Borel functional calculus of the position PVM is the multiplication operator:**
    `Φ(φ) = M_φ` for every bounded measurable symbol `φ`. That is, the abstract Borel functional calculus
    built from the position PVM (`boundedFC`) coincides with the concrete multiplication operator `mulOp φ`
    on `L²(μ)`. Proof: both are determined by their sesquilinear forms; the diagonal of `M_φ` is the position
    diagonal functional (`⟪z, M_φ z⟫ = ∫ φ ‖z‖² = diagInt φ z`), and the PVM's `boundedFC` is the polarization
    of exactly this diagonal (`inner_boundedFC` + `bilinDiag`), so the two sesquilinear forms agree and hence
    the operators agree. This anchors the position PVM's Borel calculus to the honest multiplication operator
    (the `f ↦ f(X)` functional calculus of the position observable `X`). -/
theorem boundedFC_positionPVM_eq_mulOp {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ s, ‖φ s‖ ≤ C) :
    (positionPVM (α := α) (μ := μ)).boundedFC hφ hC0 hC = mulOp hφ hC0 hC := by
  -- The quadratic form of `M_φ` is the position diagonal functional `diagInt φ`.
  have hQ : ∀ z : Lp ℂ 2 μ,
      (positionPVM (α := α) (μ := μ)).diagInt φ z = inner ℂ z (mulOp hφ hC0 hC z) := by
    intro z
    rw [positionPVM_diagInt, MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [mulOp_coeFn hφ hC0 hC z] with a e1
    have hcm : (starRingEnd ℂ) (z a) * z a = (‖z a‖ ^ 2 : ℂ) := by
      simpa using RCLike.conj_mul (z a)
    rw [e1, RCLike.inner_apply', mul_left_comm, hcm]
  -- Two operators agree iff their sesquilinear forms agree.
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [(positionPVM (α := α) (μ := μ)).inner_boundedFC, ProjectionValuedMeasure.bilinDiag]
  simp only [hQ, map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I, ← pow_two, Complex.I_sq, mul_add, mul_sub, ← mul_assoc,
    mul_neg, neg_neg, one_mul, neg_one_mul, sub_sub]
  ring

end QIQTH.Spectral.Multiplication
