/-
  FlatHeatEquation — the flat Gaussian (leading parametrix term) solves the flat heat equation.

  WHAT IS DERIVED HERE (the honest boundary — read it).
  This is the P2c LEADING-ORDER fact of the heat-kernel parametrix: the flat-space Gaussian
  fundamental solution `heatKernel1D` (and its `d`-dimensional product form `gaussDdim`) solves
  the FLAT heat equation `∂_t G = Δ_flat G`. Concretely:

    • the 1-D chain: the `x`-derivative, the second `x`-derivative, and the crux `t`-derivative
      of `G_t(x) = (√(4πt))⁻¹·exp(−x²/(4t))`, culminating in `heatKernel1D_heat_eqn`
      (`∂_t G = ∂²_x G`); the point is that the `(4πt)^{−1/2}` prefactor's `t`-dependence is
      exactly what makes `∂_t` match `∂²_x`;
    • the `d`-dimensional product form `gaussDdim t x = ∏ₖ G_t(xₖ)`, its coordinate first/second
      partials (`gaussDdim_pd_i`, `gaussDdim_pd_pd_i`), and `gaussDdim_heat_eqn`
      (`∂_t G = ∑ᵢ ∂ᵢ² G = Δ_flat G`) — summing the 1-D fact over the `d` product factors.

  ⚠ HONEST SCOPE. This is the FLAT (leading) parametrix term ONLY. It does NOT build the full
  parametrix, the curved-space (Riemannian) heat kernel, the Seeley–DeWitt recursion, or the
  general `a₁ = R/6` coefficient (P2a–e, the deep analytic wall). It connects the flat Laplacian
  `∑ᵢ ∂ᵢ²` of `QIQTH.LaplaceBeltrami.laplaceBeltrami_at_rnc_center` to `∂_t` of the Gaussian.
  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.HeatKernelA1

open Finset
open QIQTH.Curvature QIQTH.HeatKernelA1

namespace QIQTH.FlatHeatEquation

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### The 1-D chain (#1–#4): the flat Gaussian solves `∂_t u = ∂²_x u`. -/

/-- **#1 — the `x`-derivative.** `∂_x G_t(x) = (−x/(2t))·G_t(x)`. Chain rule on `exp(−x²/(4t))`;
    the prefactor `(√(4πt))⁻¹` is an `x`-constant. -/
theorem heatKernel1D_hasDerivAt_x (t x : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x => heatKernel1D t x) ((-x / (2 * t)) * heatKernel1D t x) x := by
  have htne : t ≠ 0 := ht.ne'
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have hu : HasDerivAt (fun x : ℝ => -x ^ 2 / (4 * t)) (-x / (2 * t)) x := by
    have h2 := (h1.neg).div_const (4 * t)
    convert h2 using 1
    field_simp
    ring
  have hc := (hu.exp).const_mul (Real.sqrt (4 * Real.pi * t))⁻¹
  convert hc using 1
  rw [heatKernel1D]; ring

/-- **#2 (as `HasDerivAt`) — the derivative of the first-derivative function.**
    `∂_x [(−x/(2t))·G_t(x)] = ((x²/(4t²)) − 1/(2t))·G_t(x)` (product rule on #1's RHS). -/
theorem heatKernel1D_hasDerivAt_deriv_x (t x : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x => (-x / (2 * t)) * heatKernel1D t x)
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel1D t x) x := by
  have ha : HasDerivAt (fun x : ℝ => -x / (2 * t)) (-1 / (2 * t)) x :=
    (hasDerivAt_id' (x := x) : HasDerivAt (fun y : ℝ => y) 1 x).neg.div_const (2 * t)
  have key := ha.mul (heatKernel1D_hasDerivAt_x t x ht)
  convert key using 1
  ring

/-- **#2 — the second `x`-derivative.** `∂²_x G_t(x) = ((x²/(4t²)) − 1/(2t))·G_t(x)`. -/
theorem heatKernel1D_deriv2_x (t x : ℝ) (ht : 0 < t) :
    deriv (fun x => deriv (fun x => heatKernel1D t x) x) x
      = (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel1D t x := by
  have h1 : (fun x => deriv (fun x => heatKernel1D t x) x)
      = (fun x => (-x / (2 * t)) * heatKernel1D t x) :=
    funext (fun y => (heatKernel1D_hasDerivAt_x t y ht).deriv)
  rw [h1]
  exact (heatKernel1D_hasDerivAt_deriv_x t x ht).deriv

/-- **#3 (THE CRUX) — the `t`-derivative.** `∂_t G_t(x) = ((x²/(4t²)) − 1/(2t))·G_t(x)` for `t>0`.
    The prefactor `(√(4πt))⁻¹` contributes `−1/(2t)·(…)` and the exponent contributes
    `x²/(4t²)·(…)`; together they equal the second `x`-derivative of #2 — this is what makes the
    Gaussian a fundamental solution. -/
theorem heatKernel1D_hasDerivAt_t (t x : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t => heatKernel1D t x)
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel1D t x) t := by
  have htne : t ≠ 0 := ht.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * t) := Real.sqrt_pos.mpr hpos
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := hsqrt_pos.ne'
  have hu : HasDerivAt (fun t => 4 * Real.pi * t) (4 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
  -- the prefactor `A(t) = (√(4πt))⁻¹` with `A'(t) = (−1/(2t))·A(t)`
  have hA : HasDerivAt (fun t => (Real.sqrt (4 * Real.pi * t))⁻¹)
      ((-(1 / (2 * t))) * (Real.sqrt (4 * Real.pi * t))⁻¹) t := by
    have h := (hu.sqrt hpos.ne').inv hsqrt_ne
    convert h using 1
    rw [Real.sq_sqrt hpos.le]
    field_simp
  -- the exponent `v(t) = −x²/(4t)` with `v'(t) = x²/(4t²)`
  have hv : HasDerivAt (fun t => -x ^ 2 / (4 * t)) (x ^ 2 / (4 * t ^ 2)) t := by
    have hcst : HasDerivAt (fun _ : ℝ => -x ^ 2) 0 t := hasDerivAt_const t (-x ^ 2)
    have hden : HasDerivAt (fun t => 4 * t) 4 t := by simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have h := hcst.div hden ((by positivity : (0 : ℝ) < 4 * t).ne')
    convert h using 1
    field_simp
    ring
  have hB := hv.exp
  have key := hA.mul hB
  convert key using 1
  rw [heatKernel1D]; ring

/-- **#4 — the 1-D flat heat equation.** `∂_t G_t(x) = ∂²_x G_t(x)` for `t>0`: the crux
    `t`-derivative (#3) equals the second `x`-derivative (#2). -/
theorem heatKernel1D_heat_eqn (t x : ℝ) (ht : 0 < t) :
    deriv (fun t => heatKernel1D t x) t
      = deriv (fun x => deriv (fun x => heatKernel1D t x) x) x := by
  rw [(heatKernel1D_hasDerivAt_t t x ht).deriv, heatKernel1D_deriv2_x t x ht]

/-! ### The `d`-dimensional product form (#5–#7). -/

/-- **#5 — the `d`-dimensional flat Gaussian** `G_t(x) = ∏ₖ G_t(xₖ)`, the density used in the
    moment integrals of `QIQTH.HeatKernelA1` (`∫ (∏ₖ heatKernel1D t (x k))·… `). -/
noncomputable def gaussDdim (t : ℝ) (x : Point n) : ℝ := ∏ k, heatKernel1D t (x k)

/-- **#6a — the coordinate first partial.** `∂ᵢ G(x) = (−xᵢ/(2t))·G(x)`: only the `i`-th factor
    varies in the `i`-direction, so the product rule reduces to #1 times the frozen factors. -/
theorem gaussDdim_pd_i (t : ℝ) (ht : 0 < t) (x : Point n) (i : Fin n) :
    pd (fun y => gaussDdim t y) i x = (-(x i) / (2 * t)) * gaussDdim t x := by
  simp only [pd, gaussDdim]
  have hfun : (fun s => ∏ k, heatKernel1D t (Function.update x i s k))
      = (fun s => heatKernel1D t s * ∏ k ∈ Finset.univ.erase i, heatKernel1D t (x k)) := by
    funext s
    rw [← Finset.mul_prod_erase Finset.univ
        (fun k => heatKernel1D t (Function.update x i s k)) (Finset.mem_univ i)]
    congr 1
    · show heatKernel1D t (Function.update x i s i) = heatKernel1D t s
      rw [Function.update_self]
    · exact Finset.prod_congr rfl (fun k hk => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])
  rw [hfun, ((heatKernel1D_hasDerivAt_x t (x i) ht).mul_const _).deriv, mul_assoc,
      Finset.mul_prod_erase Finset.univ (fun k => heatKernel1D t (x k)) (Finset.mem_univ i)]

/-- **#6b — the coordinate second partial.** `∂ᵢ² G(x) = ((xᵢ²/(4t²)) − 1/(2t))·G(x)`: apply the
    first-partial `gaussDdim_pd_i`, then differentiate again in the `i`-direction via #2. -/
theorem gaussDdim_pd_pd_i (t : ℝ) (ht : 0 < t) (x : Point n) (i : Fin n) :
    pd (fun y => pd (fun z => gaussDdim t z) i y) i x
      = ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussDdim t x := by
  have hinner : (fun y => pd (fun z => gaussDdim t z) i y)
      = (fun y => (-(y i) / (2 * t)) * gaussDdim t y) :=
    funext (fun y => gaussDdim_pd_i t ht y i)
  rw [hinner]
  simp only [pd, gaussDdim]
  have hprod_eq : ∀ s : ℝ, ∏ k, heatKernel1D t (Function.update x i s k)
      = heatKernel1D t s * ∏ k ∈ Finset.univ.erase i, heatKernel1D t (x k) := by
    intro s
    rw [← Finset.mul_prod_erase Finset.univ
        (fun k => heatKernel1D t (Function.update x i s k)) (Finset.mem_univ i)]
    congr 1
    · show heatKernel1D t (Function.update x i s i) = heatKernel1D t s
      rw [Function.update_self]
    · exact Finset.prod_congr rfl (fun k hk => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])
  have hfun : (fun s => -(Function.update x i s i) / (2 * t)
        * ∏ k, heatKernel1D t (Function.update x i s k))
      = (fun s => ((-s / (2 * t)) * heatKernel1D t s)
        * ∏ k ∈ Finset.univ.erase i, heatKernel1D t (x k)) := by
    funext s
    rw [hprod_eq s, Function.update_self]
    ring
  rw [hfun, ((heatKernel1D_hasDerivAt_deriv_x t (x i) ht).mul_const _).deriv, mul_assoc,
      Finset.mul_prod_erase Finset.univ (fun k => heatKernel1D t (x k)) (Finset.mem_univ i)]

/-- **#7 — the `d`-dimensional flat heat equation (P2c leading term).**
    `∂_t G(x) = ∑ᵢ ∂ᵢ² G(x) = Δ_flat G(x)` for `t>0`. The `t`-derivative of the product (#3, summed
    over the `d` factors via the Leibniz rule) equals the trace of the coordinate second partials
    (#6b). This is the leading parametrix term solving the flat heat equation, connecting `∂_t` of
    the Gaussian to the flat Laplacian `∑ᵢ ∂ᵢ²` of
    `QIQTH.LaplaceBeltrami.laplaceBeltrami_at_rnc_center`. -/
theorem gaussDdim_heat_eqn (t : ℝ) (ht : 0 < t) (x : Point n) :
    deriv (fun t => gaussDdim t x) t
      = ∑ i, pd (fun y => pd (fun z => gaussDdim t z) i y) i x := by
  have hRHS : (∑ i, pd (fun y => pd (fun z => gaussDdim t z) i y) i x)
      = ∑ i, ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussDdim t x :=
    Finset.sum_congr rfl (fun i _ => gaussDdim_pd_pd_i t ht x i)
  have hprod : HasDerivAt (fun s : ℝ => ∏ k, heatKernel1D s (x k))
      (∑ k, (∏ j ∈ Finset.univ.erase k, heatKernel1D t (x j))
        • (((x k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel1D t (x k))) t :=
    HasDerivAt.fun_finsetProd (fun i _ => heatKernel1D_hasDerivAt_t t (x i) ht)
  have hL : deriv (fun t => gaussDdim t x) t
      = ∑ k, (∏ j ∈ Finset.univ.erase k, heatKernel1D t (x j))
        • (((x k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel1D t (x k)) := hprod.deriv
  rw [hRHS, hL]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [smul_eq_mul, gaussDdim]
  rw [← Finset.prod_erase_mul Finset.univ (fun m => heatKernel1D t (x m)) (Finset.mem_univ k)]
  ring

end QIQTH.FlatHeatEquation
