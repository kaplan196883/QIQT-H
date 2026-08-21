/-
  JacobiConservation — curvature skew-adjointness and the Jacobi conservation corollary
  (Gauss-lemma radial-orthogonality infrastructure, sub-campaign step).

  Two chart-independent differential-geometry facts, built on the banked metric-compatibility engine
  (`QIQTH.CovariantLeibniz.metricPair_velocity_field_leibniz_at`, J4-990) and the banked first-pair
  antisymmetry of the lowered Riemann tensor (`QIQTH.Curvature.lowered_riemann_antisymm`).

  1. **Curvature skew-adjointness** `⟨γ', R(J,γ')γ'⟩_g = 0`.  With the file's Riemann sign convention
     `R^ρ_{σμν}` (so the curvature endomorphism `R(X,Y)Z` has components `R^ρ_{σμν} Z^σ X^μ Y^ν`), the
     term `R(J,γ')γ'` has components `C^b = ∑_{σμν} R^b_{σμν} (γ')^σ J^μ (γ')^ν`.  Pairing with the
     velocity `v = γ'` via the metric gives `∑_{a,σ,μ,ν} R_{aσμν} v^a v^σ w^μ v^ν` with the fully-lowered
     `R_{aσμν} = ∑_b g_{ab} R^b_{σμν}` **antisymmetric in the first pair `(a,σ)`**
     (`lowered_riemann_antisymm`), contracted against the SYMMETRIC `v^a v^σ` — hence zero.

  2. **Jacobi conservation** `d/dτ ⟨γ', J⟩_g` is CONSTANT, giving `⟨γ'(τ), J(τ)⟩_g = τ · ⟨v, w⟩` when
     `J(0)=0` and `∇_t J(0)=w`, `γ'(0)=v`.  Apply the velocity-field Leibniz rule TWICE: first
     `d/dτ⟨γ',J⟩ = ⟨γ',A⟩` (`A=∇_tJ`), then `d/dτ⟨γ',A⟩ = ⟨γ',∇_tA⟩ = ⟨γ',−R(J,γ')γ'⟩ = 0` (skew-
     adjointness + the CARRIED Jacobi equation `∇_t A = −R(J,γ')γ'`).  So `⟨γ',A⟩` is constant `= ⟨v,w⟩`,
     and integrating with `⟨γ'(0),J(0)⟩ = 0` gives `⟨γ'(τ),J(τ)⟩ = τ⟨v,w⟩` — the radial-orthogonality
     content of the Gauss lemma at the linearized level.

  HONEST SCOPE (what is NOT here): the Jacobi field `J`, its covariant derivative `A = ∇_t J`, and the
  Jacobi equation `∇_t A = −R(J,γ')γ'` are all CARRIED as hypotheses (mirroring how the parallel/Leibniz
  layers carry their fields).  There is NO identification of `J(1)` with `d(exp)_v(w)` — that is exactly
  the opaque-Skolemized-chart `C¹`-in-initial-condition wall (blocker J3) the Jacobi approach RELOCATES
  rather than removes.  So this does NOT make `a₁ = R/6` unconditional; it remains strictly conditional
  on `{hDuhamel, hDConv, hCConv}`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.CovariantMetricLeibniz

namespace QIQTH.JacobiConservation

open QIQTH.Curvature QIQTH.CovariantLeibniz Finset

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### Curvature skew-adjointness -/

/-- **Curvature skew-adjointness** `⟨v, R(w,v)v⟩_g = 0`.  For a symmetric, invertible, `C¹` metric `g`
    with smooth Christoffel symbols, and vectors `v, w` at a point `x`, the metric pairing of `v` with
    the curvature term `(R(w,v)v)^b = ∑_{σμν} R^b_{σμν} v^σ w^μ v^ν` vanishes:

      `∑_{a,b} g_{ab} v^a (∑_{σμν} R^b_{σμν} v^σ w^μ v^ν) = 0`.

    Proof: contracting the lowered Riemann tensor `∑_b g_{ab} R^b_{σμν}` — which is antisymmetric in the
    first pair `(a,σ)` by `lowered_riemann_antisymm` — against the SYMMETRIC `v^a v^σ` gives `X = −X`,
    hence `X = 0`.  This is the metric algebra behind `⟨γ', R(J,γ')γ'⟩ = 0` (with `v = γ'`, `w = J`). -/
theorem curvature_velocity_pairing_zero
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x : Point n) (v w : Fin n → ℝ) :
    (∑ a, ∑ b, g x a b * v a *
        (∑ σ, ∑ μ, ∑ ν, riemann g gi b σ μ ν x * v σ * w μ * v ν)) = 0 := by
  -- Reorganize to the lowered/contracted form `∑_{a,σ,μ,ν} (∑_b g_{ab} R^b_{σμν}) v^a v^σ w^μ v^ν`.
  have hPconv : (∑ a, ∑ b, g x a b * v a *
          (∑ σ, ∑ μ, ∑ ν, riemann g gi b σ μ ν x * v σ * w μ * v ν))
      = ∑ a, ∑ σ, ∑ μ, ∑ ν,
          (∑ b, g x a b * riemann g gi b σ μ ν x) * v a * v σ * w μ * v ν := by
    apply Finset.sum_congr rfl; intro a _
    rw [show (∑ b, g x a b * v a *
            (∑ σ, ∑ μ, ∑ ν, riemann g gi b σ μ ν x * v σ * w μ * v ν))
          = ∑ b, ∑ σ, ∑ μ, ∑ ν,
            (g x a b * v a * (riemann g gi b σ μ ν x * v σ * w μ * v ν)) from by
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro σ _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro μ _
        rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro σ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro μ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro ν _
    rw [show (∑ b, g x a b * v a * (riemann g gi b σ μ ν x * v σ * w μ * v ν))
          = ∑ b, (g x a b * riemann g gi b σ μ ν x) * (v a * v σ * w μ * v ν) from
        Finset.sum_congr rfl (fun b _ => by ring),
        ← Finset.sum_mul]
    ring
  rw [hPconv]
  -- The lowered/contracted form is its own negation via the `(a,σ)` swap + first-pair antisymmetry.
  have hswap : (∑ a, ∑ σ, ∑ μ, ∑ ν,
        (∑ b, g x a b * riemann g gi b σ μ ν x) * v a * v σ * w μ * v ν)
      = ∑ a, ∑ σ, ∑ μ, ∑ ν,
        (∑ b, g x σ b * riemann g gi b a μ ν x) * v σ * v a * w μ * v ν := by
    rw [Finset.sum_comm]
  have hpaired : (∑ a, ∑ σ, ∑ μ, ∑ ν,
        (∑ b, g x a b * riemann g gi b σ μ ν x) * v a * v σ * w μ * v ν)
      + (∑ a, ∑ σ, ∑ μ, ∑ ν,
        (∑ b, g x σ b * riemann g gi b a μ ν x) * v σ * v a * w μ * v ν) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro σ _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro μ _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro ν _
    have hanti := lowered_riemann_antisymm g gi hsymm hinv hCg hC a σ μ ν x
    have hfac : (∑ b, g x a b * riemann g gi b σ μ ν x) * v a * v σ * w μ * v ν
          + (∑ b, g x σ b * riemann g gi b a μ ν x) * v σ * v a * w μ * v ν
        = ((∑ b, g x a b * riemann g gi b σ μ ν x)
            + (∑ b, g x σ b * riemann g gi b a μ ν x)) * (v a * v σ * w μ * v ν) := by ring
    rw [hfac, hanti, zero_mul]
  -- From `T = Tswap` and `T + Tswap = 0`, conclude `T = 0`.
  linarith [hpaired, hswap]

/-! ### The Jacobi conservation corollary -/

/-- **Jacobi conservation of the radial pairing.**  Let `g` be a symmetric, invertible, `C¹` metric with
    smooth Christoffel symbols.  Let `γ` be a geodesic with velocity `γ'` (`∇_t γ' = 0`), and `J` a
    vector field along `γ` with covariant derivative `A = ∇_t J` and second covariant derivative
    satisfying the **Jacobi equation** `∇_t A = −R(J,γ')γ'`.  Then the radial pairing is linear in `τ`:

      `⟨γ'(τ), J(τ)⟩_g = τ · ⟨γ'(0), (∇_t J)(0)⟩_g`,

    i.e. `∑_{ab} g_{ab}(γτ) γ'(τ)^a J(τ)^b = τ · ∑_{ab} g_{ab}(γ0) γ'(0)^a A(0)^b`, provided `J(0)=0`.

    This is the linearized radial-orthogonality content of the Gauss lemma: `d/dτ⟨γ',J⟩` is CONSTANT
    (its derivative `⟨γ', ∇_t A⟩ = −⟨γ', R(J,γ')γ'⟩ = 0` by `curvature_velocity_pairing_zero`), and
    integrating from `⟨γ'(0),J(0)⟩ = 0` gives the linear-in-`τ` law.  All hypotheses are carried at every
    `τ` (the field `J`, its covariant derivative `A`, and the Jacobi equation are hypotheses, not
    constructed from `d(exp)` of a variation). -/
theorem jacobi_radial_pairing_linear
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hCg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (γ γ' γ'' J J' A A' : ℝ → Point n)
    (hγ : ∀ τ, HasDerivAt γ (γ' τ) τ)
    (hγ' : ∀ τ, ∀ i, HasDerivAt (fun s => γ' s i) (γ'' τ i) τ)
    (hJ : ∀ τ, ∀ i, HasDerivAt (fun s => J s i) (J' τ i) τ)
    (hA : ∀ τ, ∀ i, HasDerivAt (fun s => A s i) (A' τ i) τ)
    (hgeo : ∀ τ, ∀ i, γ'' τ i = -∑ j, ∑ k, christoffel g gi i j k (γ τ) * γ' τ j * γ' τ k)
    (hJcov : ∀ τ, ∀ i, J' τ i = A τ i - ∑ j, ∑ k, christoffel g gi i j k (γ τ) * γ' τ j * J τ k)
    (hJacobi : ∀ τ, ∀ i, A' τ i
        = (-(∑ σ, ∑ μ, ∑ ν, riemann g gi i σ μ ν (γ τ) * γ' τ σ * J τ μ * γ' τ ν))
          - ∑ j, ∑ k, christoffel g gi i j k (γ τ) * γ' τ j * A τ k)
    (hJ0 : ∀ i, J 0 i = 0) (τ : ℝ) :
    (∑ a, ∑ b, g (γ τ) a b * γ' τ a * J τ b)
      = τ * ∑ a, ∑ b, g (γ 0) a b * γ' 0 a * A 0 b := by
  -- First Leibniz: `d/dτ ⟨γ', J⟩ = ⟨γ', A⟩`.
  have hHderiv : ∀ τ, HasDerivAt (fun s => ∑ a, ∑ b, g (γ s) a b * γ' s a * J s b)
      (∑ a, ∑ b, g (γ τ) a b * γ' τ a * A τ b) τ := fun τ =>
    metricPair_velocity_field_leibniz_at g gi hCg hsymm γ γ' γ'' J J' A
      (fun a b => hinv (γ τ) a b) (hγ τ) (hγ' τ) (hJ τ) (hgeo τ) (hJcov τ)
  -- Second Leibniz: `d/dτ ⟨γ', A⟩ = ⟨γ', ∇_t A⟩ = −⟨γ', R(J,γ')γ'⟩ = 0`.
  have hKderiv : ∀ τ, HasDerivAt (fun s => ∑ a, ∑ b, g (γ s) a b * γ' s a * A s b) 0 τ := by
    intro τ
    have hlz := metricPair_velocity_field_leibniz_at g gi hCg hsymm
        γ γ' γ'' A A'
        (fun s i => -(∑ σ, ∑ μ, ∑ ν, riemann g gi i σ μ ν (γ s) * γ' s σ * J s μ * γ' s ν))
        (fun a b => hinv (γ τ) a b) (hγ τ) (hγ' τ) (hA τ) (hgeo τ) (hJacobi τ)
    have hval : (∑ a, ∑ b, g (γ τ) a b * γ' τ a *
          (-(∑ σ, ∑ μ, ∑ ν, riemann g gi b σ μ ν (γ τ) * γ' τ σ * J τ μ * γ' τ ν))) = 0 := by
      have hsk := curvature_velocity_pairing_zero g gi hsymm hinv hCg hC (γ τ) (γ' τ) (J τ)
      simp only [mul_neg, Finset.sum_neg_distrib]
      rw [hsk, neg_zero]
    rw [hval] at hlz
    exact hlz
  -- `⟨γ', A⟩` is constant (= its value at `0`).
  have hKconst : ∀ τ, (∑ a, ∑ b, g (γ τ) a b * γ' τ a * A τ b)
      = (∑ a, ∑ b, g (γ 0) a b * γ' 0 a * A 0 b) := fun τ => by
    exact is_const_of_deriv_eq_zero (fun s => (hKderiv s).differentiableAt)
      (fun s => (hKderiv s).deriv) τ 0
  -- `D(s) = ⟨γ',J⟩(s) − s·⟨v,w⟩` has zero derivative everywhere.
  have hDderiv : ∀ τ, HasDerivAt (fun s => (∑ a, ∑ b, g (γ s) a b * γ' s a * J s b)
        - s * (∑ a, ∑ b, g (γ 0) a b * γ' 0 a * A 0 b)) 0 τ := by
    intro τ
    have h1 := hHderiv τ
    have h2 : HasDerivAt (fun s : ℝ => s * (∑ a, ∑ b, g (γ 0) a b * γ' 0 a * A 0 b))
        (∑ a, ∑ b, g (γ 0) a b * γ' 0 a * A 0 b) τ := by
      simpa using (hasDerivAt_id τ).mul_const (∑ a, ∑ b, g (γ 0) a b * γ' 0 a * A 0 b)
    have h3 := h1.sub h2
    rw [hKconst τ, sub_self] at h3
    exact h3
  -- Hence `D` is constant `= D(0) = ⟨γ'(0),J(0)⟩ = 0`.
  have hDconst := is_const_of_deriv_eq_zero (fun s => (hDderiv s).differentiableAt)
    (fun s => (hDderiv s).deriv) τ 0
  have hH0 : (∑ a, ∑ b, g (γ 0) a b * γ' 0 a * J 0 b) = 0 := by
    apply Finset.sum_eq_zero; intro a _
    apply Finset.sum_eq_zero; intro b _
    rw [hJ0 b]; ring
  simp only [zero_mul, sub_zero] at hDconst
  rw [hH0] at hDconst
  linarith [hDconst]

end QIQTH.JacobiConservation
