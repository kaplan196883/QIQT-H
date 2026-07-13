/-
  # The abstract heat semigroup `e^{−tA}` via our own bounded Borel functional calculus

  This file builds the **ABSTRACT heat semigroup** `e^{−tA}` of a positive self-adjoint
  operator `A` — presented as `A = ∫ a dE` for a nonnegative symbol `a : Ω → ℝ` and a
  projection-valued measure `E` (`QIQTH.Spectral.ProjectionValuedMeasure`) — assembled
  entirely from our OWN bounded Borel functional calculus (`QIQTH.Spectral.boundedFC` and
  its laws in `PVM.lean`).  It delivers:

    • the **semigroup law** `e^{−sA} · e^{−tA} = e^{−(s+t)A}`  (`heatSemigroup_mul`),
    • the **`t=0` identity** `e^{0·A} = 1`                      (`heatSemigroup_zero`),
    • a **uniform operator bound** `‖e^{−tA}‖ ≤ 2`             (`heatSemigroup_norm_le`),
    • **positivity** `0 ≤ Re⟪x, e^{−tA} x⟫`                    (`heatSemigroup_inner_nonneg`).

  ⚠ The uniform bound is the tower's `2C` (here `C = 1`), NOT the sharp contraction
  `‖e^{−tA}‖ ≤ 1`; the sharp bound needs a sharper FC estimate absent from the current
  `boundedFC` layer.  This is stated honestly, not hidden.

  ## Scope (Phase A of `HEAT_KERNEL_INFRASTRUCTURE_PLAN.md`)

  This is the **ABSTRACT operator semigroup ONLY**.  It does NOT build the manifold heat
  kernel.  That the Laplace–Beltrami `Δ` on `L²(M)` is such an operator (Phase C), that it
  has discrete spectrum (Phase D — Rellich compactness, absent from Mathlib), or that it
  has a smooth integral kernel `p_t(x,y)` (Phase E — elliptic regularity, absent) are the
  WALL.  This file is NOT the conjecture, NOT the strong holographic principle, NOT quantum
  gravity — just the semigroup algebra.  No axioms, no `sorry`.

  Assembled from existing `QIQTH.Spectral` FC laws; adds NO new infrastructure and NO
  project axioms.
-/

import QIQTH.Spectral.PVM
import QIQTH.Spectral.UnboundedFC

namespace QIQTH
namespace Spectral

open scoped BigOperators

variable {Ω : Type*} {H : Type*}
  [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **heat symbol** `e^{−t·a(ω)}` for a (nonnegative) generator symbol `a : Ω → ℝ`:
    the `ℝ → ℂ` coercion of the real exponent `−(t·a ω)` fed to `Complex.exp`.  For `t ≥ 0`
    and `a ≥ 0` it is a real number in `(0,1]`. -/
noncomputable def heatSymbol (a : Ω → ℝ) (t : ℝ) : Ω → ℂ :=
  fun ω => Complex.exp ((-(t * a ω) : ℝ) : ℂ)

/-- The heat symbol is measurable whenever the generator symbol is. -/
theorem heatSymbol_measurable {a : Ω → ℝ} (ha : Measurable a) (t : ℝ) :
    Measurable (heatSymbol a t) := by
  unfold heatSymbol
  fun_prop

omit [MeasurableSpace Ω] in
/-- For `t ≥ 0` and `a ≥ 0` the heat symbol is a contraction: `‖e^{−t a(ω)}‖ ≤ 1`.
    (`‖Complex.exp z‖ = Real.exp z.re` with `z.re = −(t·a ω) ≤ 0`.) -/
theorem heatSymbol_norm_le {a : Ω → ℝ} (ha0 : ∀ ω, 0 ≤ a ω) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    ‖heatSymbol a t ω‖ ≤ 1 := by
  rw [heatSymbol, Complex.norm_exp, Complex.ofReal_re]
  calc Real.exp (-(t * a ω))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg ht (ha0 ω)))
    _ = 1 := Real.exp_zero

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure Ω H)

/-- **★ The abstract heat semigroup `e^{−tA}`** of the positive self-adjoint operator
    `A = ∫ a dE` (`a ≥ 0`), defined through the bounded Borel functional calculus of its
    heat symbol.  A genuine operator on `H` for every `t ≥ 0`. -/
noncomputable def heatSemigroup {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {t : ℝ} (ht : 0 ≤ t) : H →L[ℂ] H :=
  P.boundedFC (heatSymbol_measurable ha t) zero_le_one (heatSymbol_norm_le ha0 ht)

/-- **★★ The semigroup law** `e^{−sA} · e^{−tA} = e^{−(s+t)A}`.
    From `boundedFC_mul` (multiplicativity of the FC) and the pointwise identity
    `e^{−s a} · e^{−t a} = e^{−(s+t) a}` (`Complex.exp_add`). -/
theorem heatSemigroup_mul {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    P.heatSemigroup ha ha0 hs * P.heatSemigroup ha ha0 ht
      = P.heatSemigroup ha ha0 (add_nonneg hs ht) := by
  have hpm : Measurable (fun ω => heatSymbol a s ω * heatSymbol a t ω) :=
    (heatSymbol_measurable ha s).mul (heatSymbol_measurable ha t)
  have hpb : ∀ ω, ‖heatSymbol a s ω * heatSymbol a t ω‖ ≤ 1 := fun ω => by
    rw [norm_mul]
    nlinarith [heatSymbol_norm_le ha0 hs ω, heatSymbol_norm_le ha0 ht ω,
      norm_nonneg (heatSymbol a s ω), norm_nonneg (heatSymbol a t ω)]
  have hsym : heatSymbol a (s + t) = fun ω => heatSymbol a s ω * heatSymbol a t ω := by
    funext ω
    have he : (-(( s + t) * a ω) : ℝ) = -(s * a ω) + -(t * a ω) := by ring
    simp only [heatSymbol, he, Complex.ofReal_add, Complex.exp_add]
  simp only [heatSemigroup]
  rw [← P.boundedFC_mul (heatSymbol_measurable ha s) zero_le_one (heatSymbol_norm_le ha0 hs)
      (heatSymbol_measurable ha t) zero_le_one (heatSymbol_norm_le ha0 ht) hpm zero_le_one hpb]
  exact (P.boundedFC_congr (heatSymbol_measurable ha (s + t)) zero_le_one
    (heatSymbol_norm_le ha0 (add_nonneg hs ht)) hpm zero_le_one hpb hsym).symm

/-- **★ The `t = 0` identity** `e^{0·A} = 1` (unitality of the semigroup at the origin).
    `heatSymbol a 0 = 1` pointwise, and `boundedFC (const 1) = 1`. -/
theorem heatSemigroup_zero {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω) :
    P.heatSemigroup ha ha0 (le_refl (0 : ℝ)) = 1 := by
  have h1 : heatSymbol a 0 = (fun _ => (1 : ℂ)) := by
    funext ω; simp [heatSymbol]
  simp only [heatSemigroup]
  rw [P.boundedFC_congr (heatSymbol_measurable ha 0) zero_le_one
      (heatSymbol_norm_le ha0 (le_refl 0)) measurable_const (norm_nonneg (1 : ℂ))
      (fun _ => le_rfl) h1, P.boundedFC_const (1 : ℂ), one_smul]

/-- **★ Uniform operator bound** `‖e^{−tA}‖ ≤ 2`.  This is the tower's `2C` estimate with
    `C = 1` (`boundedFC_norm_le`), NOT the sharp contraction `≤ 1`. -/
theorem heatSemigroup_norm_le {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {t : ℝ} (ht : 0 ≤ t) : ‖P.heatSemigroup ha ha0 ht‖ ≤ 2 := by
  simpa [heatSemigroup] using
    P.boundedFC_norm_le (heatSymbol_measurable ha t) zero_le_one (heatSymbol_norm_le ha0 ht)

/-- **★ Positivity** `0 ≤ Re⟪x, e^{−tA} x⟫`: `e^{−tA}` is a positive operator.
    `⟪x, e^{−tA} x⟫ = ∫ e^{−t a} dμ_x` (`inner_boundedFC_self`), a real integral of the
    nonnegative real symbol, so its real part is `≥ 0`. -/
theorem heatSemigroup_inner_nonneg {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {t : ℝ} (ht : 0 ≤ t) (x : H) :
    0 ≤ (inner ℂ x (P.heatSemigroup ha ha0 ht x)).re := by
  have hpt : ∀ ω, heatSymbol a t ω = ((Real.exp (-(t * a ω)) : ℝ) : ℂ) := fun ω => by
    rw [heatSymbol, Complex.ofReal_exp]
  simp only [heatSemigroup]
  rw [P.inner_boundedFC_self (heatSymbol_measurable ha t) zero_le_one (heatSymbol_norm_le ha0 ht) x]
  have hre : (∫ ω, heatSymbol a t ω ∂(P.scalarMeasure x))
      = ((∫ ω, Real.exp (-(t * a ω)) ∂(P.scalarMeasure x) : ℝ) : ℂ) := by
    simp only [hpt]; exact integral_ofReal
  rw [hre, Complex.ofReal_re]
  exact MeasureTheory.integral_nonneg (fun ω => (Real.exp_pos _).le)

end ProjectionValuedMeasure

end Spectral
end QIQTH
