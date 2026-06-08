/-
  F3 (part) — the Weyl / CCR algebraic core, on exponential vectors.

  The Weyl operator `W(u)` of the bosonic Fock space acts on exponential vectors by
      `W(u) e(g) = weylCoeff u g · e(g + u)`,   `weylCoeff u g = exp(−½⟪u,u⟫ − ⟪u,g⟫)`
  (Parthasarathy §20).  This module proves the two algebraic facts on which the Weyl operators rest:

  * **`weyl_isometry`** — the prescribed action preserves the coherent-state inner product
    (`conj(c_g)·c_h·⟪e(g+u),e(h+u)⟫ = ⟪e(g),e(h)⟫`), i.e. `W(u)` is an isometry — hence (being onto,
    `W(−u)` inverts it) a **unitary**.  This is the algebraic heart of CCR unitarity.
  * **`weylCoeff_vacuum`** — `W(u)Ω = exp(−½⟪u,u⟫)·e(u)`, so the vacuum expectation is
    `⟪Ω, W(u)Ω⟫ = exp(−½‖u‖²)` — the defining value of the **quasifree** vacuum state.

  Building the bounded operator `W(u)` on the Fock space (linear extension + bounded extension to the
  completion) is the remaining F3 step; the algebra here is its core.  Axiom-free.
-/
import QIQTH.Fock.FockSpace
import Mathlib.Tactic

namespace QIQTH.Fock.Weyl

open Complex
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The **Weyl coefficient**: `W(u) e(g) = weylCoeff u g · e(g + u)` with
    `weylCoeff u g = exp(−½⟪u,u⟫ − ⟪u,g⟫)`. -/
noncomputable def weylCoeff (u g : H) : ℂ := Complex.exp (-(1 / 2 : ℂ) * ⟪u, u⟫_ℂ - ⟪u, g⟫_ℂ)

/-- **Weyl unitarity (isometry) identity.**  The prescribed action of `W(u)` on exponential vectors
    preserves the coherent-state inner product:
    `conj(weylCoeff u g) · weylCoeff u h · ⟪e(g+u), e(h+u)⟫ = ⟪e(g), e(h)⟫`
    (using `⟪e(a),e(b)⟫ = exp⟪a,b⟫`).  Hence `W(u)` is an isometry on the Fock space. -/
theorem weyl_isometry (u g h : H) :
    conj (weylCoeff u g) * weylCoeff u h * Complex.exp ⟪g + u, h + u⟫_ℂ
      = Complex.exp ⟪g, h⟫_ℂ := by
  unfold weylCoeff
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_sub, map_mul, map_neg, map_div₀, map_one, map_ofNat, inner_conj_symm,
    inner_add_left, inner_add_right]
  ring

/-- **Weyl adjoint identity** `W(u)* = W(−u)` at the coefficient level: the per-term identity behind
    `⟪W(u) e(g), e(h)⟫ = ⟪e(g), W(−u) e(h)⟫`, namely
    `conj(weylCoeff u g) · exp⟪g+u, h⟫ = exp⟪g, h−u⟫ · weylCoeff (−u) h`
    (both sides reduce to `exp` of the SAME exponent).  Hence `W(u)` is unitary with inverse `W(−u)`. -/
theorem weylCoeff_adjoint (u g h : H) :
    conj (weylCoeff u g) * Complex.exp ⟪g + u, h⟫_ℂ
      = Complex.exp ⟪g, h - u⟫_ℂ * weylCoeff (-u) h := by
  unfold weylCoeff
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_sub, map_mul, map_neg, map_div₀, map_one, map_ofNat, inner_conj_symm,
    inner_add_left, inner_sub_right, inner_neg_left, inner_neg_right]
  ring

/-- The **quasifree vacuum value**: `W(u)Ω = exp(−½⟪u,u⟫)·e(u)`, so the vacuum expectation is
    `⟪Ω, W(u)Ω⟫ = weylCoeff u 0 = exp(−½‖u‖²)` — the value defining the quasifree state. -/
theorem weylCoeff_vacuum (u : H) :
    weylCoeff u (0 : H) = Complex.exp (-(1 / 2 : ℂ) * ⟪u, u⟫_ℂ) := by
  unfold weylCoeff
  simp [inner_zero_right]

/-- `W(0) = id` at the coefficient level: `weylCoeff 0 g = 1`. -/
@[simp] theorem weylCoeff_zero_left (g : H) : weylCoeff (0 : H) g = 1 := by
  unfold weylCoeff
  simp [inner_zero_left]

/-- **The quasifree vacuum value is invariant under any one-particle isometry**:
    `⟪Ω, W(A u) Ω⟫ = ⟪Ω, W(u) Ω⟫` for a linear isometry `A`, because the value `exp(−½‖u‖²)` depends
    only on `⟪u,u⟫`, which `A` preserves.  Specialized to the Lorentz boost `A = U₁(t)` this is the
    **boost-invariance of the quasifree vacuum state** — the physical statement of vacuum covariance. -/
theorem weylCoeff_vacuum_isometry_invariant (A : H →ₗᵢ[ℂ] H) (u : H) :
    weylCoeff (A u) (0 : H) = weylCoeff u (0 : H) := by
  rw [weylCoeff_vacuum, weylCoeff_vacuum, A.inner_map_map]

/-- **`weylCoeff` is invariant under any one-particle isometry**: `weylCoeff (A u) (A v) = weylCoeff u v`
    (it depends only on `⟪u,u⟫` and `⟪u,v⟫`, which `A` preserves).  The engine of boost-covariance of
    every vacuum Weyl correlation. -/
theorem weylCoeff_isometry_invariant (A : H →ₗᵢ[ℂ] H) (u v : H) :
    weylCoeff (A u) (A v) = weylCoeff u v := by
  unfold weylCoeff
  rw [A.inner_map_map, A.inner_map_map]

end QIQTH.Fock.Weyl
