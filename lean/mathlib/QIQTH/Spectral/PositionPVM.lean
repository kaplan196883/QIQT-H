import QIQTH.Spectral.MultiplicationOp
import QIQTH.Spectral.PVM

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

end QIQTH.Spectral.Multiplication
