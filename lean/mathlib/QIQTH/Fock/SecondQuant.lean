/-
  F2-Γ — second quantization `Γ`, on exponential vectors (pre-Hilbert level).

  For a one-particle linear isometry `A : H →ₗᵢ[ℂ] H`, the **second quantization** `Γ(A)` acts on the
  Fock space by `Γ(A) e(f) = e(A f)` (Parthasarathy §19).  At the pre-Hilbert level this is simply the
  pushforward of the index, `Finsupp.lmapDomain A` (since `e(f) = single f 1` and
  `mapDomain A (single f 1) = single (A f) 1`).

  Results (axiom-free):
    * `secondQuantPre_expVec` — `Γ(A) e(f) = e(A f)`;
    * `fockInner_secondQuant` — `Γ(A)` preserves the coherent-state inner product (`A` isometric), so
      `Γ(A)` is **isometric** on the Fock space;
    * `secondQuantPre_vacuum` — `Γ(A) Ω = Ω` (the vacuum is invariant, since `A 0 = 0`);
    * `secondQuantPre_comp` — functoriality `Γ(A) ∘ Γ(B) = Γ(A ∘ B)`.

  Specialized to the F1 Lorentz boost `boostUnitary t` (a unitary on the one-particle space
  `L²(ℝ)`), `boostFock t = Γ(boostUnitary t)` is the boost acting on the Fock space, and
  `boostFock_vacuum` is its **vacuum invariance** `Γ(U₁(t)) Ω = Ω` — the key input to boost-covariance
  of the typicality measure (the full F6 prize).  Axiom-free.
-/
import QIQTH.Fock.FockSpace
import QIQTH.Fock.OneParticle
import QIQTH.Fock.Weyl
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Tactic

namespace QIQTH.Fock

open Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Second quantization** at the pre-Hilbert level: `Γ(A)` pushes the index forward along `A`, so
    `Γ(A) e(f) = e(A f)`. -/
noncomputable def secondQuantPre (A : H →ₗᵢ[ℂ] H) : FockPre H →ₗ[ℂ] FockPre H :=
  Finsupp.lmapDomain ℂ ℂ A

/-- `Γ(A) e(f) = e(A f)`. -/
@[simp] theorem secondQuantPre_expVec (A : H →ₗᵢ[ℂ] H) (f : H) :
    secondQuantPre A (FockPre.expVec f) = FockPre.expVec (A f) := by
  show Finsupp.mapDomain (⇑A) (Finsupp.single f 1) = Finsupp.single (A f) 1
  exact Finsupp.mapDomain_single

/-- **`Γ(A)` is isometric**: it preserves the coherent-state inner product (because `A` does).  The
    pushforward needs no injectivity — the inner product is additive in each coefficient, so
    `sum_mapDomain_index` applies. -/
theorem fockInner_secondQuant (A : H →ₗᵢ[ℂ] H) (φ ψ : H →₀ ℂ) :
    fockInner (Finsupp.mapDomain A φ) (Finsupp.mapDomain A ψ) = fockInner φ ψ := by
  unfold fockInner
  rw [Finsupp.sum_mapDomain_index
        (fun b => by simp) (fun b m₁ m₂ => by simp [star_add, add_mul, Finsupp.sum_add])]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_mapDomain_index
        (fun b => by simp) (fun b m₁ m₂ => by simp [mul_add])]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [A.inner_map_map]

/-- **The vacuum is `Γ(A)`-invariant**: `Γ(A) Ω = Ω` (since `A 0 = 0`). -/
@[simp] theorem secondQuantPre_vacuum (A : H →ₗᵢ[ℂ] H) :
    secondQuantPre A (FockPre.expVec (0 : H)) = FockPre.expVec (0 : H) := by
  rw [secondQuantPre_expVec, map_zero]

/-- **Functoriality**: `Γ(A) (Γ(B) φ) = Γ(A ∘ B) φ`. -/
theorem secondQuantPre_comp (A B : H →ₗᵢ[ℂ] H) (φ : FockPre H) :
    secondQuantPre A (secondQuantPre B φ) = secondQuantPre (A.comp B) φ := by
  show Finsupp.mapDomain (⇑A) (Finsupp.mapDomain (⇑B) φ) = Finsupp.mapDomain (⇑(A.comp B)) φ
  rw [LinearIsometry.coe_comp, Finsupp.mapDomain_comp]

/-! ### The Lorentz boost on the Fock space (F1 → Fock) -/

/-- **The Lorentz boost acting on the Fock space** over the one-particle space `L²(ℝ)`: the second
    quantization `Γ(U₁(t))` of the F1 boost unitary `boostUnitary t`.  (Pre-Hilbert level.) -/
noncomputable def boostFock (t : ℝ) :
    FockPre (Lp ℂ 2 (volume : Measure ℝ)) →ₗ[ℂ] FockPre (Lp ℂ 2 (volume : Measure ℝ)) :=
  secondQuantPre (QIQTH.Fock.OneParticle.boostUnitary t).toLinearIsometry

/-- **Vacuum invariance of the boost**: `Γ(U₁(t)) Ω = Ω`.  The boost fixes the Fock vacuum — the key
    input to boost-covariance of the typicality measure μ∞. -/
@[simp] theorem boostFock_vacuum (t : ℝ) :
    boostFock t (FockPre.expVec 0) = FockPre.expVec 0 :=
  secondQuantPre_vacuum _

/-- **The boost is isometric on the Fock space** (it preserves the coherent-state inner product). -/
theorem fockInner_boostFock (t : ℝ)
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ) →₀ ℂ) :
    fockInner (Finsupp.mapDomain (QIQTH.Fock.OneParticle.boostUnitary t) φ)
        (Finsupp.mapDomain (QIQTH.Fock.OneParticle.boostUnitary t) ψ)
      = fockInner φ ψ :=
  fockInner_secondQuant (QIQTH.Fock.OneParticle.boostUnitary t).toLinearIsometry φ ψ

/-- The boost as a **linear isometry** of the pre-Fock space (bundling `boostFock` with the
    inner-product preservation `fockInner_boostFock`). -/
noncomputable def boostFockₗᵢ (t : ℝ) :
    FockPre (Lp ℂ 2 (volume : Measure ℝ)) →ₗᵢ[ℂ] FockPre (Lp ℂ 2 (volume : Measure ℝ)) :=
  LinearMap.isometryOfInner (boostFock t) (fun φ ψ => fockInner_boostFock t φ ψ)

/-- **The Lorentz boost as a genuine isometry of the Fock HILBERT space** `Fock (L²(ℝ))`: the unique
    continuous extension of the pre-level boost to the completion (`UniformSpace.Completion.map`). -/
noncomputable def boostFockH (t : ℝ) :
    Fock (Lp ℂ 2 (volume : Measure ℝ)) → Fock (Lp ℂ 2 (volume : Measure ℝ)) :=
  UniformSpace.Completion.map (boostFockₗᵢ t)

/-- The boost is an **isometry of the Fock Hilbert space** (extension of an isometry to the
    completion). -/
theorem boostFockH_isometry (t : ℝ) : Isometry (boostFockH t) :=
  (boostFockₗᵢ t).isometry.completion_map

/-- **Vacuum invariance on the Fock Hilbert space:** the Lorentz boost fixes the vacuum,
    `Γ(U₁(t)) Ω = Ω`, as a genuine identity in the completed Fock space `Fock (L²(ℝ))`. -/
theorem boostFockH_vacuum (t : ℝ) : boostFockH t Fock.vacuum = Fock.vacuum := by
  have hΩ : (boostFockₗᵢ t) (FockPre.expVec 0) = FockPre.expVec 0 := boostFock_vacuum t
  show UniformSpace.Completion.map (boostFockₗᵢ t)
        ((FockPre.expVec 0 : FockPre (Lp ℂ 2 (volume : Measure ℝ))) : Fock _)
      = ((FockPre.expVec 0 : FockPre (Lp ℂ 2 (volume : Measure ℝ))) : Fock _)
  rw [UniformSpace.Completion.map_coe (boostFockₗᵢ t).isometry.uniformContinuous, hΩ]

/-- **Boost-invariance of the quasifree vacuum state** (on the Weyl observables): the vacuum value
    `⟪Ω, W(U₁(t) u) Ω⟫ = ⟪Ω, W(u) Ω⟫`.  The quasifree vacuum state is **Lorentz-boost invariant** —
    because the boost preserves the one-particle norm (`‖U₁(t)u‖ = ‖u‖`), so `exp(−½‖u‖²)` is unchanged.
    This is the physical heart of boost-covariance: the vacuum state of the relativistic free field is
    Lorentz invariant. -/
theorem weylCoeff_vacuum_boost_invariant (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Weyl.weylCoeff (QIQTH.Fock.OneParticle.boostUnitary t u) (0 : Lp ℂ 2 (volume : Measure ℝ))
      = Weyl.weylCoeff u 0 :=
  Weyl.weylCoeff_vacuum_isometry_invariant
    (QIQTH.Fock.OneParticle.boostUnitary t).toLinearIsometry u

end QIQTH.Fock
