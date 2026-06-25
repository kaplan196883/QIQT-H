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

end QIQTH.Spectral.Multiplication
