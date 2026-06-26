import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The translation operator on `L²(ℝ)`

The **translation operator** `τ_t : L²(ℝ) → L²(ℝ)`, `(τ_t f)(x) = f(x + t)`, is a ℂ-linear isometry because the
Lebesgue measure is translation-invariant (`MeasureTheory.Lp.compMeasurePreservingₗᵢ` with the measure-preserving
shift `· + t`). This is the concrete one-parameter family of unitaries whose **generator is the momentum operator**
`P` (`e^{itP} = τ_t`), and hence the kinematic object behind `WedgeKMSFlux #5` (spatial translation / the boost
generator on the free field).

**Honest scope:** this file delivers the translation operator as an axiom-free ℂ-linear isometry with its pointwise
action and isometry. The remaining steps — the one-parameter **group law** `τ_s ∘ τ_t = τ_{s+t}`, **strong
continuity** `t ↦ τ_t f` continuous, and the **identification of the generator with the momentum PVM**
`P = ∫ k dÊ(k)` (Stone's theorem) — are the M4 Stone / unbounded-FC frontier; and the GR chain beyond `#5` stays
gated on the physical wedge inputs `#1/#3/#4`.
-/

namespace QIQTH.Spectral.Multiplication

open MeasureTheory

/-- The **translation operator** `τ_t` on `L²(ℝ)`: `(τ_t f)(x) = f(x + t)`. A ℂ-linear isometry (Lebesgue
    measure is translation-invariant). The one-parameter family whose generator is the momentum operator. -/
noncomputable def translationLp (t : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (· + t) (measurePreserving_add_right volume t)

/-- The pointwise action of the translation operator: `τ_t f =ᵐ fun x => f (x + t)`. -/
theorem coeFn_translationLp (t : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    translationLp t g =ᵐ[volume] fun x => g (x + t) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving g (measurePreserving_add_right volume t)

/-- The translation operator is an isometry: `‖τ_t f‖ = ‖f‖` (unitarity on `L²`). -/
@[simp] theorem norm_translationLp (t : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖translationLp t g‖ = ‖g‖ := (translationLp t).norm_map g

/-- **The one-parameter group law** `τ_s ∘ τ_t = τ_{s+t}`: translations compose additively. With
    `coeFn_translationLp` this makes `t ↦ τ_t` an additive one-parameter group of unitaries on `L²(ℝ)` (its
    generator is the momentum operator). The ae-composition uses that `· + s` is measure-preserving. -/
theorem translationLp_add (s t : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    translationLp s (translationLp t g) = translationLp (s + t) g := by
  have hqmp := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving
  have h2s : (fun x => (translationLp t g : ℝ → ℂ) (x + s))
      =ᵐ[volume] fun x => (g : ℝ → ℂ) (x + s + t) :=
    hqmp.tendsto_ae.eventually (coeFn_translationLp t g)
  refine Lp.ext ?_
  filter_upwards [coeFn_translationLp s (translationLp t g), h2s, coeFn_translationLp (s + t) g]
    with x e1 e2 e3
  rw [e1, e2, e3, add_assoc]

end QIQTH.Spectral.Multiplication
