/-
  HeatParametrixError — the heat-operator residual of the flat Gaussian leading term.

  P2c-LEADING brick.  This connects the two landed P2 bricks
  (`QIQTH.LaplaceBeltrami` and `QIQTH.FlatHeatEquation`) by forming the residual of the heat
  operator `(∂_t − Δ_g)` applied to the flat-space Gaussian `gaussDdim` used as the leading
  parametrix term, and showing that this residual VANISHES at a Riemannian-normal-coordinate
  center (the diagonal).

  What is built:
    • `heatResidual g gi t x = ∂_t G − Δ_g G` — the heat-operator error of the flat Gaussian;
    • `heatResidual_eq_flat_minus_g` — for `t>0` this equals `(Δ_flat − Δ_g) G`, isolating the
      error as the difference between the flat and curved Laplacians on `G`
      (using `gaussDdim_heat_eqn`, i.e. `∂_t G = Δ_flat G`);
    • `heatResidual_at_rnc_center` — for `t>0`, at an RNC center (`g^{ij}(x₀)=δ`, `Γ(x₀)=0`)
      the flat and curved Laplacians coincide (`laplaceBeltrami_at_rnc_center`), so the residual
      is `0`.  This is the key fact: the flat Gaussian is a genuine leading parametrix — the
      heat-operator error vanishes at the normal-coordinate center;
    • `heatResidual_curvature_form` — the explicit "metric-deviation" form of the error,
      `∑_ij (δ^{ij} − g^{ij}) ∂_i∂_j G + ∑_ijk g^{ij} Γ^k_ij ∂_k G`, substituting the Gaussian's
      partials, making the O(|x|²·curvature) structure explicit (the input to the u₁ transport
      equation).

  ⚠ HONEST SCOPE. This is the P2c LEADING residual only.  It does NOT build the full parametrix,
  the curved heat kernel, the Seeley–DeWitt recursion, or the general `a₁ = R/6`.
  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.LaplaceBeltrami
import QIQTH.FlatHeatEquation

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation

namespace QIQTH.HeatParametrixError

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **The heat-operator residual of the flat Gaussian leading term.**
    `heatResidual g gi t x = (∂_t − Δ_g) G` where `G = gaussDdim` is the flat-space Gaussian
    used as the leading parametrix term.  This is the leading-order error the parametrix
    coefficients `u₁,…` must cancel. -/
noncomputable def heatResidual (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (x : Point n) : ℝ :=
  deriv (fun s => gaussDdim s x) t - laplaceBeltrami g gi (gaussDdim t) x

/-- **The residual is the flat-minus-curved Laplacian on `G`.**  For `t>0`, since the flat
    Gaussian solves the flat heat equation `∂_t G = ∑_i ∂_i² G` (`gaussDdim_heat_eqn`), the
    heat-operator residual reduces to `(Δ_flat − Δ_g) G`. -/
theorem heatResidual_eq_flat_minus_g (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (x : Point n) :
    heatResidual g gi t x
      = (∑ i, pd (fun y => pd (fun z => gaussDdim t z) i y) i x)
        - laplaceBeltrami g gi (gaussDdim t) x := by
  rw [heatResidual, gaussDdim_heat_eqn t ht x]

/-- **The residual vanishes at a Riemannian-normal-coordinate center.**  For `t>0`, at an RNC
    center (`g^{ij}(x₀)=δ^{ij}` and `Γ^k_{ij}(x₀)=0`) the curved Laplacian `Δ_g` reduces to the
    flat Laplacian `∑_i ∂_i²` (`laplaceBeltrami_at_rnc_center`), which is exactly the flat term in
    the residual, so they cancel.  KEY FACT: the flat Gaussian is a genuine leading parametrix —
    the heat-operator error VANISHES at the normal-coordinate center (the diagonal). -/
theorem heatResidual_at_rnc_center (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (x₀ : Point n) (hgi : ∀ i j, gi x₀ i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j x₀ = 0) :
    heatResidual g gi t x₀ = 0 := by
  rw [heatResidual_eq_flat_minus_g g gi t ht x₀,
      laplaceBeltrami_at_rnc_center g gi (gaussDdim t) x₀ hgi hΓ,
      sub_eq_zero]

/-- **The explicit metric-deviation (curvature) form of the residual.**  For `t>0`,
    `heatResidual g gi t x = ∑_{i,j} (δ^{ij} − g^{ij}(x))·∂_i∂_j G + ∑_{i,j,k} g^{ij}(x) Γ^k_{ij}(x) ∂_k G`.
    This isolates the error as the metric deviation `(δ − g^{ij})` contracted with the Gaussian's
    second partials plus the Christoffel drift contracted with its first partials — the structural
    input to the `u₁` transport equation.  (The first block collapses on the diagonal to the flat
    Laplacian `∑_i ∂_i² G`; the two blocks together are exactly `(Δ_flat − Δ_g) G`.) -/
theorem heatResidual_curvature_form (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (x : Point n) :
    heatResidual g gi t x
      = (∑ i, ∑ j, ((if i = j then (1:ℝ) else 0) - gi x i j)
            * pd (fun y => pd (gaussDdim t) j y) i x)
        + ∑ i, ∑ j, ∑ k, gi x i j * christoffel g gi k i j x
            * pd (gaussDdim t) k x := by
  -- collapse of the identity-metric block to the flat Laplacian `∑_i ∂_i² G`
  have hdelta : (∑ i, ∑ j, (if i = j then (1:ℝ) else 0)
        * pd (fun y => pd (gaussDdim t) j y) i x)
      = ∑ i, pd (fun y => pd (fun z => gaussDdim t z) i y) i x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (∑ j, (if i = j then (1:ℝ) else 0) * pd (fun y => pd (gaussDdim t) j y) i x)
        = ∑ j, (if i = j then pd (fun y => pd (gaussDdim t) j y) i x else 0) from
          Finset.sum_congr rfl (fun j _ => by split <;> simp)]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
  -- `Δ_g G` split into its `g^{ij} ∂_i∂_j G` and `g^{ij} Γ^k_{ij} ∂_k G` blocks
  have hlap : laplaceBeltrami g gi (gaussDdim t) x
      = (∑ i, ∑ j, gi x i j * pd (fun y => pd (gaussDdim t) j y) i x)
        - ∑ i, ∑ j, ∑ k, gi x i j * christoffel g gi k i j x
            * pd (gaussDdim t) k x := by
    simp only [laplaceBeltrami]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- the metric-deviation block = flat Laplacian − `g^{ij} ∂_i∂_j G`
  have hrhs : (∑ i, ∑ j, ((if i = j then (1:ℝ) else 0) - gi x i j)
        * pd (fun y => pd (gaussDdim t) j y) i x)
      = (∑ i, pd (fun y => pd (fun z => gaussDdim t z) i y) i x)
        - ∑ i, ∑ j, gi x i j * pd (fun y => pd (gaussDdim t) j y) i x := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hdelta]
  rw [heatResidual_eq_flat_minus_g g gi t ht x, hlap, hrhs]
  ring

end QIQTH.HeatParametrixError
