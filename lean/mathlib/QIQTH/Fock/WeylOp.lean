/-
  F3 keystone — the bounded WEYL OPERATOR `W(u)` on the Fock space.

  Per the GPT-5.5-pro review, this is THE load-bearing missing operator: the actual unitary
  `W(u) : Fock H → Fock H` (not just the characteristic value `weylCoeff`), acting on coherent vectors by
      `W(u) e(g) = weylCoeff u g · e(g + u)`,   `weylCoeff u g = exp(−½⟪u,u⟫ − ⟪u,g⟫)`.
  On the pre-Fock space `FockPre H = H →₀ ℂ` this is the linear map `weylPre u` (built with
  `Finsupp.lsum`).  Its **isometry** — `fockInner (W(u)φ) (W(u)ψ) = fockInner φ ψ` — is the
  `weyl_isometry` identity summed over the coherent-vector expansion; this is what makes `W(u)` unitary.
  It then extends to a genuine **isometry of the Fock Hilbert space** `weylH u` (the `Completion.map`
  pattern of `boostFockH`), with `⟪Ω, W(u)Ω⟫ = exp(−½‖u‖²)` (the quasifree value).  Axiom-free.
-/
import QIQTH.Fock.FockSpace
import QIQTH.Fock.Weyl
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic

namespace QIQTH.Fock

open Complex
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The Weyl operator at the pre-Hilbert level**: the linear map with `W(u) e(g) = c·e(g+u)`,
    `c = weylCoeff u g`. -/
noncomputable def weylPre (u : H) : FockPre H →ₗ[ℂ] FockPre H :=
  Finsupp.lsum ℂ fun g => LinearMap.toSpanSingleton ℂ (FockPre H)
    (Weyl.weylCoeff u g • FockPre.expVec (g + u))

/-- `W(u)` as a sum of translated, scaled coherent vectors. -/
theorem weylPre_apply (u : H) (φ : H →₀ ℂ) :
    weylPre u φ = φ.sum (fun g a => Finsupp.single (g + u) (a * Weyl.weylCoeff u g)) := by
  have hl : weylPre u φ = φ.sum (fun g => ⇑(LinearMap.toSpanSingleton ℂ (FockPre H)
      (Weyl.weylCoeff u g • FockPre.expVec (g + u)))) := Finsupp.lsum_apply ℂ _ φ
  rw [hl]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [LinearMap.toSpanSingleton_apply, smul_smul]
  show (φ g * Weyl.weylCoeff u g) • Finsupp.single (g + u) (1 : ℂ)
      = Finsupp.single (g + u) (φ g * Weyl.weylCoeff u g)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `W(u) e(g) = weylCoeff u g · e(g + u)`. -/
@[simp] theorem weylPre_expVec (u g : H) :
    weylPre u (FockPre.expVec g) = Weyl.weylCoeff u g • FockPre.expVec (g + u) := by
  rw [weylPre_apply]
  rw [show FockPre.expVec g = Finsupp.single g (1 : ℂ) from rfl, Finsupp.sum_single_index (by simp),
    one_mul]
  show Finsupp.single (g + u) (Weyl.weylCoeff u g)
      = Weyl.weylCoeff u g • Finsupp.single (g + u) (1 : ℂ)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Helper: collapse a sum of translated singles inside a `Finsupp.sum`. -/
private theorem sum_single_translate {H β : Type*} [AddCommMonoid β] (φ : H →₀ ℂ) (σ : H → H)
    (F : H → ℂ → ℂ) (G : H → ℂ → β) (hG0 : ∀ q, G q 0 = 0)
    (hGadd : ∀ q c c', G q (c + c') = G q c + G q c') :
    (φ.sum (fun g a => Finsupp.single (σ g) (F g a))).sum G
      = φ.sum (fun g a => G (σ g) (F g a)) := by
  rw [Finsupp.sum_sum_index hG0 hGadd]
  exact Finsupp.sum_congr fun g _ => Finsupp.sum_single_index (hG0 _)

/-- **`W(u)` is isometric**: it preserves the coherent-state inner product.  This is the
    `weyl_isometry` identity summed over the expansion — the algebraic content making `W(u)` unitary. -/
theorem fockInner_weyl (u : H) (φ ψ : H →₀ ℂ) :
    fockInner (weylPre u φ) (weylPre u ψ) = fockInner φ ψ := by
  rw [weylPre_apply, weylPre_apply]
  unfold fockInner
  rw [sum_single_translate φ (· + u) (fun g a => a * Weyl.weylCoeff u g)
        (fun p c => (ψ.sum fun h b => Finsupp.single (h + u) (b * Weyl.weylCoeff u h)).sum
          fun q d => star c * Complex.exp ⟪p, q⟫_ℂ * d)
        (by intro q; simp) (by intro q c c'; simp [star_add, add_mul, ← Finsupp.sum_add])]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [sum_single_translate ψ (· + u) (fun h b => b * Weyl.weylCoeff u h)
        (fun q d => star (φ g * Weyl.weylCoeff u g) * Complex.exp ⟪g + u, q⟫_ℂ * d)
        (by intro q; simp) (by intro q c c'; ring)]
  refine Finsupp.sum_congr fun h _ => ?_
  have hw := Weyl.weyl_isometry u g h
  simp only [star_mul', RCLike.star_def]
  linear_combination (starRingEnd ℂ (φ g) * (ψ h)) * hw

/-- `W(0) = id` (the Weyl operator at `0` is the identity). -/
theorem weylPre_zero : weylPre (0 : H) = LinearMap.id := by
  ext φ
  simp [weylPre_apply, Weyl.weylCoeff_zero_left, Finsupp.sum_single]

/-- The Fock inner product is linear in its second argument. -/
theorem fockInner_smul_right (c : ℂ) (φ ψ : H →₀ ℂ) :
    fockInner φ (c • ψ) = c * fockInner φ ψ := by
  rw [← fockInner_conj φ (c • ψ), fockInner_smul_left, map_mul, Complex.conj_conj, fockInner_conj]

/-- **`W(u)` as a linear isometry** of the pre-Fock space. -/
noncomputable def weylₗᵢ (u : H) : FockPre H →ₗᵢ[ℂ] FockPre H :=
  LinearMap.isometryOfInner (weylPre u) (fun φ ψ => fockInner_weyl u φ ψ)

/-- **The Weyl operator on the Fock HILBERT space** `Fock H`: the unique continuous extension of
    `weylₗᵢ u` to the completion. -/
noncomputable def weylH (u : H) : Fock H → Fock H := UniformSpace.Completion.map (weylₗᵢ u)

/-- `W(u)` is an **isometry of the Fock Hilbert space**. -/
theorem weylH_isometry (u : H) : Isometry (weylH u) :=
  (weylₗᵢ u).isometry.completion_map

/-- **The quasifree vacuum value** at the level of the inner product:
    `⟪Ω, W(u) Ω⟫ = weylCoeff u 0 = exp(−½⟪u,u⟫) = exp(−½‖u‖²)`. -/
theorem fockInner_vacuum_weyl (u : H) :
    fockInner (FockPre.expVec 0) (weylPre u (FockPre.expVec 0))
      = Complex.exp (-(1 / 2 : ℂ) * ⟪u, u⟫_ℂ) := by
  have hw : weylPre u (FockPre.expVec 0) = Finsupp.single u (Weyl.weylCoeff u 0) := by
    rw [weylPre_apply, show FockPre.expVec (0 : H) = Finsupp.single 0 1 from rfl,
      Finsupp.sum_single_index (by simp), one_mul, zero_add]
  rw [hw]
  show fockInner (Finsupp.single 0 1) (Finsupp.single u (Weyl.weylCoeff u 0)) = _
  unfold fockInner
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), Weyl.weylCoeff_vacuum]
  simp [inner_zero_left]