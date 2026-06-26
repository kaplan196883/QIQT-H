import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
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

/-- **Strong continuity of the translation group:** `t ↦ τ_t F` is continuous `ℝ → L²(ℝ)` for every state `F`.
    Together with the group law this makes `t ↦ τ_t` a strongly-continuous one-parameter unitary group — the
    `C₀`-group hypothesis of Stone's theorem (whose generator is the momentum operator `P`). Proof: the family
    `t ↦ (· + t) : ℝ → C(ℝ,ℝ)` is continuous (via `ContinuousMap.curry` of the jointly-continuous `(t,x) ↦ x+t`),
    and `Lp` composition is continuous in the composing map (`Continuous.compMeasurePreservingLp`). -/
theorem continuous_translationLp (F : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous (fun t : ℝ => translationLp t F) := by
  let Φ : C(ℝ × ℝ, ℝ) := ⟨fun p => p.2 + p.1, by fun_prop⟩
  let g : C(ℝ, C(ℝ, ℝ)) := Φ.curry
  have hgm : ∀ t : ℝ, MeasurePreserving (g t) (volume : Measure ℝ) volume :=
    fun t => measurePreserving_add_right volume t
  have hcont : Continuous (fun t : ℝ => Lp.compMeasurePreserving (g t) (hgm t) F) :=
    (continuous_const).compMeasurePreservingLp (map_continuous g) hgm (by norm_num)
  exact hcont

/-- The translation at `t = 0` is the identity: `τ_0 = id`. -/
@[simp] theorem translationLp_zero (g : Lp ℂ 2 (volume : Measure ℝ)) : translationLp 0 g = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_translationLp 0 g] with x e1
  rw [e1, add_zero]

/-- **The translation operator as a unitary `≃ₗᵢ`** (one-parameter *group* of unitaries): `τ_t` is invertible
    with inverse `τ_{-t}` (from the group law `τ_t ∘ τ_{-t} = τ_0 = id`). This packages translation as a genuine
    unitary on `L²(ℝ)` — the form conjugation/modular machinery consumes. -/
noncomputable def translationUnitary (t : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective (translationLp t)
    (fun g => ⟨translationLp (-t) g, by
      rw [translationLp_add, add_neg_cancel, translationLp_zero]⟩)

@[simp] theorem translationUnitary_apply (t : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    translationUnitary t g = translationLp t g := rfl

@[simp] theorem translationUnitary_symm_apply (t : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (translationUnitary t).symm g = translationLp (-t) g := by
  apply (translationUnitary t).injective
  rw [LinearIsometryEquiv.apply_symm_apply, translationUnitary_apply, translationLp_add,
    add_neg_cancel, translationLp_zero]

end QIQTH.Spectral.Multiplication
