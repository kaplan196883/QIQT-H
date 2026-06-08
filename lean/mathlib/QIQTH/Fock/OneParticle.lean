/-
  F1 — The one-particle space and the boost as a one-parameter unitary group.

  This is the bottom rung of the Fock/CCR foundation (`FOCK_CCR_FOUNDATION_PLAN.md`): the genuine
  CONTINUUM replacement for `FreeFieldTypicality`'s finite mode set `m` and mode-permutation boost
  `e : m ≃ m`.  Here the boost is a genuine one-parameter group of *measure-preserving* transformations
  of a continuum momentum space, and it acts on the one-particle Hilbert space `L²` by a one-parameter
  group of **unitaries** (the second-quantized version `Γ(U₁(t))` in Phase F2 is the continuum
  `diagBoost`).

  ## Abstract core (general, axiom-free)
  `MPFlow μ` packages a one-parameter group `χ : ℝ → X → X` of `μ`-measure-preserving maps.  From it we
  build `MPFlow.unitary t : L²(μ) ≃ₗᵢ[ℂ] L²(μ)` — a genuine **unitary** (surjective linear isometry) —
  acting contravariantly by `ψ ↦ ψ ∘ χ_{-t}`, with the one-parameter group law `unitary_add_apply`
  (`U(s+t) = U(s)∘U(t)`) and `unitary_zero_apply` (`U(0)=id`).  Unitarity is automatic from
  measure-preservation; the whole construction rides Mathlib's `Lp.compMeasurePreserving`.

  ## Concrete: the 1+1D massive Lorentz boost  (rapidity = translation)
  For a free scalar field of mass `m > 0` in 1+1 dimensions, the mass shell is parametrized by spatial
  momentum `p ∈ ℝ` with energy `ω_p = √(p²+m²)`, and the Lorentz-invariant measure is `dΩ_m = dp/(2ω_p)`.
  Under the **rapidity** substitution `p = m·sinh θ` (so `ω_p = m·cosh θ`):
    • the invariant measure becomes `dΩ_m = (m·cosh θ)dθ / (2·m·cosh θ) = ½ dθ`  (∝ Lebesgue), and
    • the Lorentz boost of rapidity `t` acts by `θ ↦ θ + t`  (since
      `p' = ω sinh t + p cosh t = m·sinh(θ+t)`).
  So in rapidity coordinates the one-particle space is `L²(ℝ, ½·volume) ≅ L²(ℝ, volume)` and the boost
  is **translation** `θ ↦ θ + t`.  `boostFlow` is exactly this — `translationFlow` reinterpreted as the
  1+1D mass-`m` boost — and `boostUnitary t` is the genuine continuum boost unitary group.  No Jacobian
  is needed: in rapidity coordinates the measure is Lebesgue and the boost is a translation, both
  already measure-preserving in Mathlib.

  HONEST SCOPE: this delivers the continuum boost UNITARY GROUP on the one-particle space (and the
  general measure-preserving-flow → unitary-group machinery).  Strong continuity (the Stone generator)
  and the 3+1D mass-shell Jacobian are the immediately following increments; Fock space / Weyl is F2/F3.
  Axiom-free.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

namespace QIQTH.Fock.OneParticle

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A measure-preserving one-parameter flow on `(X, μ)`: a one-parameter group `χ` of
    `μ`-measure-preserving maps.  The continuum analogue of a one-parameter group of permutations of
    the (finite) mode set in `FreeFieldTypicality`. -/
structure MPFlow {X : Type*} [MeasurableSpace X] (μ : Measure X) where
  /-- The flow map at time `t`. -/
  flow : ℝ → X → X
  /-- Each time-slice preserves `μ`. -/
  mp : ∀ t, MeasurePreserving (flow t) μ μ
  /-- The flow at time `0` is the identity. -/
  flow_zero : flow 0 = id
  /-- One-parameter group law. -/
  flow_add : ∀ s t, flow (s + t) = flow s ∘ flow t

namespace MPFlow

/-- Composing twice along the flow chains the times:
    `ψ ∘ χ_b ∘ χ_a = ψ ∘ χ_{b+a}` at the level of `L²`. -/
theorem comp_chain (Φ : MPFlow μ) (a b : ℝ) (g : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving (Φ.flow a) (Φ.mp a)
        (Lp.compMeasurePreserving (Φ.flow b) (Φ.mp b) g)
      = Lp.compMeasurePreserving (Φ.flow (b + a)) (Φ.mp (b + a)) g := by
  rw [← Lp.compMeasurePreserving_comp_apply g (Φ.mp b) (Φ.mp a)]
  have hfun : Φ.flow b ∘ Φ.flow a = Φ.flow (b + a) := (Φ.flow_add b a).symm
  simp only [hfun]

/-- **The boost unitary** at flow-time `t`: the unitary `ψ ↦ ψ ∘ χ_{-t}` on `L²(μ)`.  A genuine
    unitary (surjective linear isometry); unitarity is automatic from measure-preservation. -/
noncomputable def unitary (Φ : MPFlow μ) (t : ℝ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ (Φ.flow (-t)) (Φ.mp (-t)))
    (fun h => ⟨Lp.compMeasurePreservingₗᵢ ℂ (Φ.flow t) (Φ.mp t) h, by
      show Lp.compMeasurePreserving (Φ.flow (-t)) (Φ.mp (-t))
          (Lp.compMeasurePreserving (Φ.flow t) (Φ.mp t) h) = h
      rw [comp_chain Φ (-t) t h]
      simp only [add_neg_cancel, Φ.flow_zero]
      exact Lp.compMeasurePreserving_id_apply h⟩)

/-- The boost unitary acts by precomposition with the inverse-time flow. -/
theorem unitary_apply (Φ : MPFlow μ) (t : ℝ) (g : Lp ℂ 2 μ) :
    Φ.unitary t g = Lp.compMeasurePreserving (Φ.flow (-t)) (Φ.mp (-t)) g := by
  show (LinearIsometryEquiv.ofSurjective _ _) g = _
  rw [LinearIsometryEquiv.coe_ofSurjective]
  rfl

/-- **One-parameter group law**: `U(s+t) = U(s) ∘ U(t)`. -/
theorem unitary_add_apply (Φ : MPFlow μ) (s t : ℝ) (g : Lp ℂ 2 μ) :
    Φ.unitary (s + t) g = Φ.unitary s (Φ.unitary t g) := by
  rw [unitary_apply, unitary_apply, unitary_apply, comp_chain Φ (-s) (-t) g,
    show -(s + t) = -t + -s from by ring]

/-- `U(0) = id`. -/
theorem unitary_zero_apply (Φ : MPFlow μ) (g : Lp ℂ 2 μ) : Φ.unitary 0 g = g := by
  rw [unitary_apply]
  simp only [neg_zero, Φ.flow_zero]
  exact Lp.compMeasurePreserving_id_apply g

end MPFlow

/-- **The translation flow** on `(ℝ, volume)`: `χ_t = (· + t)`, measure-preserving since Lebesgue
    measure is translation-invariant. -/
noncomputable def translationFlow : MPFlow (volume : Measure ℝ) where
  flow t := fun x => x + t
  mp t := measurePreserving_add_right volume t
  flow_zero := by funext x; simp
  flow_add s t := by funext x; show x + (s + t) = (x + t) + s; ring

/-- **The 1+1D massive Lorentz boost flow.**  In rapidity coordinates `θ` (where `p = m·sinh θ`), the
    Lorentz-invariant one-particle measure `dΩ_m = dp/2ω_p` is `½·volume` (∝ Lebesgue) and the boost of
    rapidity `t` is the translation `θ ↦ θ + t`.  So the genuine continuum mass-`m` boost flow IS the
    translation flow (read in rapidity coordinates). -/
noncomputable def boostFlow : MPFlow (volume : Measure ℝ) := translationFlow

/-- **The 1+1D continuum boost unitary group** on the one-particle space `L²(ℝ) = L²(mass shell, dΩ_m)`
    (in rapidity coordinates).  This is the genuine continuum replacement for
    `FreeFieldTypicality`'s finite mode-permutation boost: a one-parameter group of unitaries
    (`boostUnitary_add_apply`, `boostUnitary_zero_apply`) implementing a real Lorentz symmetry. -/
noncomputable def boostUnitary (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  boostFlow.unitary t

/-- The boost unitaries form a one-parameter group. -/
theorem boostUnitary_add_apply (s t : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    boostUnitary (s + t) g = boostUnitary s (boostUnitary t g) :=
  boostFlow.unitary_add_apply s t g

/-- The boost at rapidity `0` is the identity. -/
theorem boostUnitary_zero_apply (g : Lp ℂ 2 (volume : Measure ℝ)) :
    boostUnitary 0 g = g :=
  boostFlow.unitary_zero_apply g

end QIQTH.Fock.OneParticle
