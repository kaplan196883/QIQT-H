/-
  HeatParametrixOrder — P2c(-order): the FIRST-ORDER parametrix improves on the flat leading term.

  WHAT IS BUILT HERE (the honest boundary — read it).
  This file assembles the per-order residual cancellation of the Minakshisundaram–DeWitt heat
  parametrix at the DIAGONAL (Riemannian-normal-coordinate center, which in these coordinates is
  the Gaussian center `0`).  Rosenberg §3.2.1: the parametrix
      H_N(t,x) = G·Θ^{−1/2}·Σ_{k≤N} u_k t^k
  is designed so that `(∂_t − Δ_g)H_N = −G·Θ^{−1/2}·(Δ_g u_N)·t^N` — every lower order cancels via
  the transport equations.  For `N = 1` at the diagonal this is genuinely DERIVED here:

    • `heatResidual_leading_diag_vanish` — the order-0 parametrix (just the flat Gaussian `G`) has
      vanishing heat-operator residual at the diagonal center (the P2c-order restatement of
      `HeatParametrixError.heatResidual_at_rnc_center`);

    • `parametrixResidual` — the heat-operator residual `(∂_t − Δ_g)H_1` of the FULL first-order
      ansatz `H_1 = G·Θ^{−1/2}·(u_0 + u_1 t)`;

    • `pd_pd_mul` / `pd_pd_mul_mixed` — the pointwise flat second-order Leibniz rules
      `∂_i∂_j(f h) = (∂_i∂_j f)h + (∂_j f)(∂_i h) + (∂_i f)(∂_j h) + f(∂_i∂_j h)`, derived from the
      first-order `pd_mul`;

    • `laplaceBeltrami_mul` — the genuine second-order product rule for the curved Laplacian,
      `Δ_g(f h) = (Δ_g f)h + f(Δ_g h) + Σ_{ij} g^{ij}((∂_i f)(∂_j h) + (∂_j f)(∂_i h))`
      (the `2⟨∇f,∇h⟩_g` cross-gradient term written symmetrically), derived from `pd_pd_mul_mixed`
      and the linearity of `Δ_g`;

    • `laplaceBeltrami_gaussMul_at_zero` — the DIAGONAL specialization: at the center `0` the
      Gaussian gradient vanishes (`∂_i G(0) = 0`), so the cross-gradient term drops and
      `Δ_g(G·w)(0) = (Δ_g G)(0)·w(0) + G(0)·(Δ_g w)(0)`;

    • `parametrixResidual_telescope` (UNCONDITIONAL) — the full first-order residual at the diagonal,
      `parametrixResidual(0) = G(0)·(Θ^{−1/2}u_1(0) − Δ_g(Θ^{−1/2}u_0)(0) − t·Δ_g(Θ^{−1/2}u_1)(0))`.
      The flat-Laplacian `Δ_g G` term of `∂_t` (the flat heat equation `gaussDdim_heat_eqn`) cancels
      EXACTLY against the corresponding term of `Δ_g H_1` — this is the mechanism that pushes the
      residual to order `t`.  No transport hypothesis is used: this is the genuine, unconditional
      first-order telescoping;

    • `parametrixResidual_transport_identity` — feeding in the u₁ TRANSPORT EQUATION
      `Θ^{−1/2}u_1(0) = Δ_g(Θ^{−1/2}u_0)(0)` (the DeWitt recursion, carried as the geometric input,
      exactly as `HeatTransportRecursion.TransportRecursion.udiag_rec`/`transport_center` carry it),
      the `t^0` order cancels and the residual collapses to the pure order-`t` remainder
      `parametrixResidual(0) = −G(0)·Δ_g(Θ^{−1/2}u_1)(0)·t`
      — Rosenberg's `−G·Θ^{−1/2}(Δ_g u_N)t^N` for `N = 1`.

  ⚠ HONEST SCOPE.  This is the FIRST-ORDER, DIAGONAL cancellation.  It does NOT build the general
  order-`N` recursion, the OFF-diagonal parametrix (which needs the geodesic-radial `r∂_r` transport
  ODE / the van-Vleck determinant as a genuine function — the P2b/P2d wall recorded in
  `QIQTH.HeatTransportRecursion`), the parametrix-convergence / `O(t^N)` error estimate (the P2d
  Levi/Duhamel wall), the curved heat KERNEL, or the general `a₁ = R/6` (P2e).  The transport
  equation feeding `parametrixResidual_transport_identity` is CARRIED (the DeWitt geometric input),
  not derived here.  No axioms, no `sorry`.

  Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1.
-/
import Mathlib
import QIQTH.HeatParametrixError
import QIQTH.HeatParametrixAnsatz
import QIQTH.HeatTransportRecursion

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatParametrixError QIQTH.HeatParametrixAnsatz

namespace QIQTH.HeatParametrixOrder

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### #1 — the order-0 (flat leading term) residual vanishes at the diagonal. -/

/-- **The order-0 parametrix improves nothing to correct: its residual already vanishes at the
    diagonal.**  The leading parametrix term is the flat Gaussian `G` alone (`H_0 = G`), whose
    heat-operator residual `(∂_t − Δ_g)G` vanishes at a Riemannian-normal-coordinate center
    (`g^{ij}(x₀)=δ`, `Γ(x₀)=0`).  This is the P2c-order restatement of
    `HeatParametrixError.heatResidual_at_rnc_center`: the flat Gaussian is a genuine leading
    parametrix, so the first-order term `u₁` only needs to cancel the NEXT order. -/
theorem heatResidual_leading_diag_vanish (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (x₀ : Point n) (hgi : ∀ i j, gi x₀ i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j x₀ = 0) :
    heatResidual g gi t x₀ = 0 :=
  heatResidual_at_rnc_center g gi t ht x₀ hgi hΓ

/-! ### #2 — the heat-operator residual of the full first-order ansatz. -/

/-- **The heat-operator residual of the first-order parametrix** `H_1 = G·Θ^{−1/2}·(u_0 + u_1 t)`:
    `parametrixResidual g gi Θ u t x = (∂_t − Δ_g) H_1 (t,x)`. -/
noncomputable def parametrixResidual (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (t : ℝ) (x : Point n) : ℝ :=
  deriv (fun s => heatParametrix 1 Θ u s x) t
    - laplaceBeltrami g gi (heatParametrix 1 Θ u t) x

/-! ### Smoothness of the flat Gaussian in the space variable. -/

/-- The flat Gaussian `y ↦ gaussDdim t y = ∏_k (√(4πt))⁻¹ exp(−(y k)²/(4t))` is `C^∞`. -/
theorem gaussDdim_contDiff (t : ℝ) : ContDiff ℝ ⊤ (fun y : Point n => gaussDdim t y) := by
  unfold gaussDdim heatKernel1D
  fun_prop

/-! ### The second-order Leibniz rules for `pd` (flat) and `Δ_g` (curved). -/

/-- **Mixed flat second-order Leibniz.**
    `∂_i∂_j(f h) = (∂_i∂_j f)h + (∂_j f)(∂_i h) + (∂_i f)(∂_j h) + f(∂_i∂_j h)`,
    derived by applying the first-order `pd_mul` twice. -/
theorem pd_pd_mul_mixed (f h : Point n → ℝ) (i j : Fin n) (x : Point n)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h) :
    pd (fun y => pd (fun z => f z * h z) j y) i x
      = pd (fun y => pd f j y) i x * h x + pd f j x * pd h i x
        + pd f i x * pd h j x + f x * pd (fun y => pd h j y) i x := by
  have hinner : (fun y => pd (fun z => f z * h z) j y)
      = (fun y => pd f j y * h y + f y * pd h j y) :=
    funext (fun y => pd_mul f h j y (PdiffAt_of_contDiff f hf j y) (PdiffAt_of_contDiff h hh j y))
  rw [hinner,
      pd_add (fun y => pd f j y * h y) (fun y => f y * pd h j y) i x
        ((PdiffAt_pd f hf j i x).mul (PdiffAt_of_contDiff h hh i x))
        ((PdiffAt_of_contDiff f hf i x).mul (PdiffAt_pd h hh j i x)),
      pd_mul (fun y => pd f j y) h i x (PdiffAt_pd f hf j i x) (PdiffAt_of_contDiff h hh i x),
      pd_mul f (fun y => pd h j y) i x (PdiffAt_of_contDiff f hf i x) (PdiffAt_pd h hh j i x)]
  ring

/-- **Same-index flat second-order Leibniz.**
    `∂_i²(f h) = (∂_i² f)h + 2(∂_i f)(∂_i h) + f(∂_i² h)`.  The `i = j` case of `pd_pd_mul_mixed`. -/
theorem pd_pd_mul (f h : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h) :
    pd (fun y => pd (fun z => f z * h z) i y) i x
      = pd (fun y => pd f i y) i x * h x + 2 * (pd f i x * pd h i x)
        + f x * pd (fun y => pd h i y) i x := by
  rw [pd_pd_mul_mixed f h i i x hf hh]; ring

/-- **The second-order product rule for the curved Laplacian.**
    `Δ_g(f h) = (Δ_g f)h + f(Δ_g h) + Σ_{ij} g^{ij}((∂_i f)(∂_j h) + (∂_j f)(∂_i h))`.
    The last block is the `2⟨∇f,∇h⟩_g` cross-gradient term (written symmetrically so no metric
    symmetry is needed); derived from `pd_pd_mul_mixed` and the linearity of `pd`. -/
theorem laplaceBeltrami_mul (g gi : Point n → Fin n → Fin n → ℝ) (f h : Point n → ℝ) (x : Point n)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h) :
    laplaceBeltrami g gi (fun y => f y * h y) x
      = laplaceBeltrami g gi f x * h x + f x * laplaceBeltrami g gi h x
        + ∑ i, ∑ j, gi x i j * (pd f i x * pd h j x + pd f j x * pd h i x) := by
  simp only [laplaceBeltrami]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- expand the (i,j) integrand of `Δ_g(fh)`
  have hsec : pd (fun y => pd (fun z => f z * h z) j y) i x
      = pd (fun y => pd f j y) i x * h x + pd f j x * pd h i x
        + pd f i x * pd h j x + f x * pd (fun y => pd h j y) i x :=
    pd_pd_mul_mixed f h i j x hf hh
  -- expand the first-order Leibniz inside the Christoffel drift `∂_k(fh)`
  have hΓ : (∑ k, christoffel g gi k i j x * pd (fun z => f z * h z) k x)
      = (∑ k, christoffel g gi k i j x * pd f k x) * h x
        + f x * ∑ k, christoffel g gi k i j x * pd h k x := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_mul f h k x (PdiffAt_of_contDiff f hf k x) (PdiffAt_of_contDiff h hh k x)]; ring
  rw [hsec, hΓ]; ring

/-! ### The diagonal Gaussian-product Laplacian (cross-gradient drops at the center). -/

/-- **`Δ_g(G·w)` at the diagonal center `0`.**  At the Riemannian-normal-coordinate center — which
    in these coordinates is the Gaussian center `0` — the Gaussian gradient vanishes
    (`∂_i G(0) = 0`, `gaussDdim_pd_i` at `0`), so the cross-gradient term of `laplaceBeltrami_mul`
    drops and `Δ_g(G·w)(0) = (Δ_g G)(0)·w(0) + G(0)·(Δ_g w)(0)`.  This is the diagonal simplification
    that makes the first-order residual telescope. -/
theorem laplaceBeltrami_gaussMul_at_zero (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (w : Point n → ℝ) (hw : ContDiff ℝ ⊤ w)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) :
    laplaceBeltrami g gi (fun y => gaussDdim t y * w y) (0 : Point n)
      = laplaceBeltrami g gi (gaussDdim t) (0 : Point n) * w (0 : Point n)
        + gaussDdim t (0 : Point n) * laplaceBeltrami g gi w (0 : Point n) := by
  rw [laplaceBeltrami_at_rnc_center g gi (fun y => gaussDdim t y * w y) (0 : Point n) hgi hΓ,
      laplaceBeltrami_at_rnc_center g gi (gaussDdim t) (0 : Point n) hgi hΓ,
      laplaceBeltrami_at_rnc_center g gi w (0 : Point n) hgi hΓ,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_pd_mul (gaussDdim t) w i (0 : Point n) (gaussDdim_contDiff t) hw]
  have hg0 : pd (fun z => gaussDdim t z) i (0 : Point n) = 0 := by
    rw [gaussDdim_pd_i t ht (0 : Point n) i]; simp
  rw [hg0]; ring

/-! ### #3 — the first-order residual telescopes to the order-`t` remainder. -/

/-- **THE FIRST-ORDER TELESCOPING (unconditional).**  At the diagonal center `0`, the heat-operator
    residual of the first-order parametrix is
    `parametrixResidual(0)
       = G(0)·(Θ^{−1/2}u_1(0) − Δ_g(Θ^{−1/2}u_0)(0) − t·Δ_g(Θ^{−1/2}u_1)(0))`.
    MECHANISM: the `∂_t` of `H_1` contributes `(∂_t G)·Θ^{−1/2}(u_0+u_1 t) + G·Θ^{−1/2}u_1`, and by
    the flat heat equation (`gaussDdim_heat_eqn`) `∂_t G = Δ_g G` at the center; this `Δ_g G` term
    cancels EXACTLY against the `(Δ_g G)·w` term of `Δ_g H_1` (`laplaceBeltrami_gaussMul_at_zero`),
    pushing the residual to the two smooth-factor Laplacian terms.  No transport hypothesis is used.
    (`Θ` is only ever evaluated through the carried smooth folded coefficients `Θ^{−1/2}u_0`,
    `Θ^{−1/2}u_1`.) -/
theorem parametrixResidual_telescope (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hΘu0 : ContDiff ℝ ⊤ (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 0 y))
    (hΘu1 : ContDiff ℝ ⊤ (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 1 y)) :
    parametrixResidual g gi Θ u t (0 : Point n)
      = gaussDdim t (0 : Point n)
        * ((Θ (0 : Point n)) ^ (-(1 : ℝ) / 2) * u 1 (0 : Point n)
            - laplaceBeltrami g gi (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 0 y) (0 : Point n)
            - t * laplaceBeltrami g gi (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 1 y) (0 : Point n)) := by
  -- the smooth space-factor `w = Θ^{−1/2}(u_0 + u_1 t)`, and its smoothness
  have hwfacCD : ContDiff ℝ ⊤ (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * (u 0 y + u 1 y * t)) := by
    have he : (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * (u 0 y + u 1 y * t))
        = (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 0 y + t * ((Θ y) ^ (-(1 : ℝ) / 2) * u 1 y)) := by
      funext y; ring
    rw [he]; exact hΘu0.add (contDiff_const.mul hΘu1)
  -- (A) the `t`-derivative of `H_1(·,0)` via the product rule
  have hgaussHD : HasDerivAt (fun s => gaussDdim s (0 : Point n))
      (deriv (fun s => gaussDdim s (0 : Point n)) t) t := by
    have hFP := HasDerivAt.fun_finsetProd
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        heatKernel1D_hasDerivAt_t t ((0 : Point n) i) ht)
    exact hFP.differentiableAt.hasDerivAt
  have hmul : HasDerivAt (fun s : ℝ => u 1 (0 : Point n) * s) (u 1 (0 : Point n)) t := by
    simpa using (hasDerivAt_id t).const_mul (u 1 (0 : Point n))
  have hbase : HasDerivAt (fun s : ℝ => u 0 (0 : Point n) + u 1 (0 : Point n) * s)
      (u 1 (0 : Point n)) t := hmul.const_add (u 0 (0 : Point n))
  have hlin := hbase.const_mul ((Θ (0 : Point n)) ^ (-(1 : ℝ) / 2))
  have hderiv_fun : (fun s => heatParametrix 1 Θ u s (0 : Point n))
      = (fun s => gaussDdim s (0 : Point n)
          * ((Θ (0 : Point n)) ^ (-(1 : ℝ) / 2) * (u 0 (0 : Point n) + u 1 (0 : Point n) * s))) := by
    funext s
    simp only [heatParametrix, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      zero_add]
    ring
  have hderivval : deriv (fun s => heatParametrix 1 Θ u s (0 : Point n)) t
      = deriv (fun s => gaussDdim s (0 : Point n)) t
          * ((Θ (0 : Point n)) ^ (-(1 : ℝ) / 2) * (u 0 (0 : Point n) + u 1 (0 : Point n) * t))
        + gaussDdim t (0 : Point n)
          * ((Θ (0 : Point n)) ^ (-(1 : ℝ) / 2) * u 1 (0 : Point n)) := by
    rw [hderiv_fun]; exact (hgaussHD.mul hlin).deriv
  -- (B) the `Δ_g` of `H_1(t,·)` via the diagonal Gaussian-product rule
  have hHeq : heatParametrix 1 Θ u t
      = (fun y => gaussDdim t y * ((Θ y) ^ (-(1 : ℝ) / 2) * (u 0 y + u 1 y * t))) := by
    funext y
    simp only [heatParametrix, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      zero_add]
    ring
  have hΔval : laplaceBeltrami g gi (heatParametrix 1 Θ u t) (0 : Point n)
      = laplaceBeltrami g gi (gaussDdim t) (0 : Point n)
          * ((Θ (0 : Point n)) ^ (-(1 : ℝ) / 2) * (u 0 (0 : Point n) + u 1 (0 : Point n) * t))
        + gaussDdim t (0 : Point n)
          * laplaceBeltrami g gi
              (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * (u 0 y + u 1 y * t)) (0 : Point n) := by
    rw [hHeq]
    exact laplaceBeltrami_gaussMul_at_zero g gi t ht
      (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * (u 0 y + u 1 y * t)) hwfacCD hgi hΓ
  -- split the smooth-factor Laplacian `Δ_g(Θ^{−1/2}(u_0+u_1 t))` into its `u_0` and `u_1` parts
  have hΔwfac : laplaceBeltrami g gi
        (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * (u 0 y + u 1 y * t)) (0 : Point n)
      = laplaceBeltrami g gi (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 0 y) (0 : Point n)
        + t * laplaceBeltrami g gi (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 1 y) (0 : Point n) := by
    have he : (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * (u 0 y + u 1 y * t))
        = (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 0 y + t * ((Θ y) ^ (-(1 : ℝ) / 2) * u 1 y)) := by
      funext y; ring
    rw [he, laplaceBeltrami_add g gi (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 0 y)
          (fun y => t * ((Θ y) ^ (-(1 : ℝ) / 2) * u 1 y)) (0 : Point n) hΘu0
          (contDiff_const.mul hΘu1),
        laplaceBeltrami_const_mul g gi t (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 1 y) (0 : Point n) hΘu1]
  -- the flat heat equation turns `∂_t G` into `Δ_g G` at the center, and the two cancel
  have hheat : deriv (fun s => gaussDdim s (0 : Point n)) t
      = laplaceBeltrami g gi (gaussDdim t) (0 : Point n) := by
    rw [gaussDdim_heat_eqn t ht (0 : Point n),
        laplaceBeltrami_at_rnc_center g gi (gaussDdim t) (0 : Point n) hgi hΓ]
  -- assemble
  unfold parametrixResidual
  rw [hderivval, hΔval, hΔwfac, hheat]
  ring

/-- **THE ORDER-`t` REMAINDER (with the u₁ transport equation).**  Feeding in the DeWitt transport
    equation `Θ^{−1/2}u_1(0) = Δ_g(Θ^{−1/2}u_0)(0)` (the geometric input carried by the DeWitt
    recursion — cf. `HeatTransportRecursion.TransportRecursion`), the `t^0` order of the first-order
    residual cancels and it collapses to the pure order-`t` remainder
    `parametrixResidual(0) = −G(0)·Δ_g(Θ^{−1/2}u_1)(0)·t`
    — Rosenberg §3.2.1's `(∂_t − Δ_g)H_N = −G·Θ^{−1/2}(Δ_g u_N)t^N` for `N = 1` at the diagonal.
    The first-order parametrix genuinely improves the leading term: the residual is `O(t)` (with a
    coefficient set by the next transport datum), not `O(1)`. -/
theorem parametrixResidual_transport_identity (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hΘu0 : ContDiff ℝ ⊤ (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 0 y))
    (hΘu1 : ContDiff ℝ ⊤ (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 1 y))
    (htransport : (Θ (0 : Point n)) ^ (-(1 : ℝ) / 2) * u 1 (0 : Point n)
        = laplaceBeltrami g gi (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 0 y) (0 : Point n)) :
    parametrixResidual g gi Θ u t (0 : Point n)
      = - gaussDdim t (0 : Point n)
          * laplaceBeltrami g gi (fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 1 y) (0 : Point n) * t := by
  rw [parametrixResidual_telescope g gi Θ u t ht hgi hΓ hΘu0 hΘu1, htransport]
  ring

end QIQTH.HeatParametrixOrder
