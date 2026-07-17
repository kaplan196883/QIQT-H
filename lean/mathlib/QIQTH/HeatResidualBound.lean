/-
  HeatResidualBound — J5a of the Jacobi/van-Vleck campaign: the RESIDUAL TELESCOPING IDENTITY
  (the deep analytic core, general-`N`, at the diagonal).

  WHAT IS BUILT HERE (the honest boundary — read it).
  Rosenberg §3.2.1: the Minakshisundaram–DeWitt parametrix
      H_N(t,x) = G(t,x)·Θ(x)^{−1/2}·Σ_{k≤N} u_k(x)·t^k
  has its transport coefficients `u_k` chosen (the DeWitt recursion, J3/J4) precisely so that the
  heat-operator residual `(∂_t − Δ_g)H_N` TELESCOPES: every order `t^0…t^{N−1}` cancels, leaving only
  the `t^N` tail `−G·Θ^{−1/2}(Δ_g u_N)·t^N`.  This file proves that telescoping IDENTITY at the
  DIAGONAL (RNC center `0`) for GENERAL `N`, generalizing the first-order
  `HeatParametrixOrder.parametrixResidual_telescope` / `parametrixResidual_transport_identity`.

  Working with the FOLDED coefficients `w_k(y) = Θ(y)^{−1/2}·u_k(y)` (exactly as the first-order
  bricks fold `Θ^{−1/2}u_k`), we build:

    • `foldedCoeff Θ u k` — the folded coefficient `y ↦ Θ(y)^{−1/2} u_k(y)`;
    • `heatParametrix_folded` — `H_N = G·Σ_{k≤N} w_k·t^k` (the ansatz rewritten with the `Θ^{−1/2}`
      folded into each coefficient);
    • `laplaceBeltrami_sum_pow` — `Δ_g(Σ_{k≤N} c_k·t^k) = Σ_{k≤N} (Δ_g c_k)·t^k` (linearity of `Δ_g`
      over the polynomial-in-`t` sum, from `laplaceBeltrami_add`/`laplaceBeltrami_const_mul`);
    • `telescope_bracket` — THE algebraic heart: given the diagonal transport recursion
      `(k+1)·a_{k+1} = b_k` for `k < N`, the bracket
        `Σ_{k≤N} a_k·(k·t^{k−1}) − Σ_{k≤N} b_k·t^k = − b_N·t^N`
      (reindex the derivative sum, peel the top of the Laplacian sum, cancel each order by the
      recursion);
    • `parametrixResidualN` — the general-`N` heat-operator residual `(∂_t − Δ_g)H_N`;
    • `parametrixResidual_telescope_N` — THE GENERAL-`N` DIAGONAL TELESCOPING IDENTITY: given the
      diagonal folded transport recursion `hrec` (`(k+1) w_{k+1}(0) = Δ_g w_k(0)` for `k < N`),
        `(∂_t − Δ_g)H_N(t,0) = − G(0)·Δ_g(w_N)(0)·t^N` ,
      i.e. all lower orders `t^0…t^{N−1}` cancel and only the `t^N` tail (set by the next transport
      datum `Δ_g u_N`) survives — Rosenberg's `−G·Θ^{−1/2}(Δ_g u_N)t^N` for general `N`.

  MECHANISM (unconditional part).  `∂_t` of `H_N` contributes `(∂_t G)·Σ w_k t^k + G·Σ k w_k t^{k−1}`,
  and by the flat heat equation (`gaussDdim_heat_eqn`) `∂_t G = Δ_g G` at the center; this `Δ_g G`
  term cancels EXACTLY against the `(Δ_g G)·Σ w_k t^k` term of `Δ_g H_N`
  (`laplaceBeltrami_gaussMul_at_zero`, the Gaussian gradient vanishing at the center), pushing the
  residual to `G·(Σ k w_k t^{k−1} − Σ (Δ_g w_k) t^k)`.  The transport recursion `hrec` then
  telescopes this bracket to `−(Δ_g w_N)t^N`.

  ⚠ HONEST SCOPE (binding).  This is the general-`N` telescoping IDENTITY at the DIAGONAL.  It is
  exactly the ALGEBRAIC HEART (J5a) of the residual estimate.  It does NOT yet build:
    – the OFF-diagonal (`v ≠ 0`) telescoping — the diagonal simplification
      `laplaceBeltrami_gaussMul_at_zero` uses the Gaussian gradient `∂_i G(0)=0`, so the
      cross-gradient `2⟨∇G,∇w⟩_g` term of `laplaceBeltrami_mul` (which does NOT vanish off the
      diagonal) is not carried here — that is the CHECKPOINTED step (see the closing note);
    – the Gaussian BOUND on the `t^N` tail (J5b, rides on this + C4a/C4b `GaussianPolyBound`);
    – `a₁ = R/6` (J6).
  The folded transport recursion `hrec` and the coefficient smoothness `hw` are CARRIED as genuine,
  load-bearing, non-vacuous hypotheses (they come from J3/J4 — `transportCoeff_succ_transport_eq`
  and the DeWitt smoothness).  No axioms, no `sorry`.

  Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1.
-/
import Mathlib
import QIQTH.ParametrixFunction
import QIQTH.HeatParametrixOrder
import QIQTH.GaussianPolyBound
import QIQTH.RadialDistance

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatParametrixError QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.RadialDistance

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ### #1 — the folded coefficients `w_k = Θ^{−1/2}·u_k` and the folded parametrix. -/

/-- The **folded DeWitt coefficient** `w_k(y) = Θ(y)^{−1/2}·u_k(y)` — the `Θ^{−1/2}` prefactor of the
    parametrix ansatz folded into each transport coefficient, exactly as the first-order bricks
    (`HeatParametrixOrder`) fold `Θ^{−1/2}u_0`, `Θ^{−1/2}u_1`. -/
noncomputable def foldedCoeff (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (k : ℕ) : Point n → ℝ :=
  fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u k y

/-- **The parametrix ansatz in folded form.**  `H_N(t,x) = G(t,x)·Σ_{k≤N} w_k(x)·t^k`, i.e. the
    `Θ(x)^{−1/2}` prefactor of `heatParametrix` distributed into each coefficient `w_k = Θ^{−1/2}u_k`.
    (No hypotheses: a purely algebraic re-association.) -/
theorem heatParametrix_folded (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (x : Point n) :
    heatParametrix N Θ u t x
      = gaussDdim t x * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k x * t ^ k := by
  rw [heatParametrix, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [foldedCoeff]; ring

/-! ### #2 — `Δ_g` linearity over the polynomial-in-`t` sum. -/

/-- **`Δ_g` of a polynomial-in-`t` sum of fields** `Δ_g(Σ_{k≤N} c_k·t^k) = Σ_{k≤N} (Δ_g c_k)·t^k`.
    Linearity of the Laplace–Beltrami operator over the finite sum (each `t^k` a constant), by
    induction on `N` from `laplaceBeltrami_add` and `laplaceBeltrami_const_mul`. -/
theorem laplaceBeltrami_sum_pow (g gi : Point n → Fin n → Fin n → ℝ) (c : ℕ → Point n → ℝ)
    (t : ℝ) (x : Point n) (N : ℕ) (hc : ∀ k, ContDiff ℝ ⊤ (c k)) :
    laplaceBeltrami g gi (fun y => ∑ k ∈ Finset.range (N + 1), c k y * t ^ k) x
      = ∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (c k) x * t ^ k := by
  induction N with
  | zero => simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one]
  | succ M ih =>
    have hpart : ContDiff ℝ ⊤ (fun y => ∑ k ∈ Finset.range (M + 1), c k y * t ^ k) :=
      ContDiff.sum (fun k _ => (hc k).mul contDiff_const)
    have hlast : ContDiff ℝ ⊤ (fun y => t ^ (M + 1) * c (M + 1) y) :=
      contDiff_const.mul (hc (M + 1))
    have hsplit : (fun y => ∑ k ∈ Finset.range (M + 1 + 1), c k y * t ^ k)
        = (fun y => (∑ k ∈ Finset.range (M + 1), c k y * t ^ k) + t ^ (M + 1) * c (M + 1) y) := by
      funext y; rw [Finset.sum_range_succ]; ring
    rw [hsplit,
        laplaceBeltrami_add g gi (fun y => ∑ k ∈ Finset.range (M + 1), c k y * t ^ k)
          (fun y => t ^ (M + 1) * c (M + 1) y) x hpart hlast, ih,
        laplaceBeltrami_const_mul g gi (t ^ (M + 1)) (c (M + 1)) x (hc (M + 1)),
        Finset.sum_range_succ (fun k => laplaceBeltrami g gi (c k) x * t ^ k) (M + 1)]
    ring

/-! ### #3 — the telescoping bracket (the algebraic heart). -/

/-- **THE TELESCOPING BRACKET.**  Given the diagonal transport recursion `(k+1)·a_{k+1} = b_k` for
    every `k < N`, the DeWitt bracket collapses to its `t^N` boundary term:
      `Σ_{k≤N} a_k·(k·t^{k−1}) − Σ_{k≤N} b_k·t^k = − b_N·t^N` .
    Here the first sum is the `∂_t`-derivative of `Σ a_k t^k` (the `k=0` term vanishing), the second
    is the `Δ_g`-image `Σ b_k t^k`; reindexing the first (`Finset.sum_range_succ'`) and peeling the
    top of the second (`Finset.sum_range_succ`) matches orders `t^0…t^{N−1}`, each killed by the
    recursion, leaving `−b_N t^N`.  This is the pure-algebra core of the residual telescoping. -/
theorem telescope_bracket (a b : ℕ → ℝ) (t : ℝ) (N : ℕ)
    (hrec : ∀ k, k < N → ((k : ℝ) + 1) * a (k + 1) = b k) :
    (∑ k ∈ Finset.range (N + 1), a k * ((k : ℝ) * t ^ (k - 1)))
        - ∑ k ∈ Finset.range (N + 1), b k * t ^ k
      = - b N * t ^ N := by
  rw [Finset.sum_range_succ' (fun k => a k * ((k : ℝ) * t ^ (k - 1))) N,
      Finset.sum_range_succ (fun k => b k * t ^ k) N]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  -- the two `range N` sums match termwise via the recursion
  have hzero : (∑ k ∈ Finset.range N, a (k + 1) * (((k + 1 : ℕ) : ℝ) * t ^ k))
      = ∑ k ∈ Finset.range N, b k * t ^ k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < N := Finset.mem_range.mp hk
    rw [← hrec k hk']; push_cast; ring
  rw [hzero]; ring

/-! ### #4 — the general-`N` heat-operator residual and its diagonal telescoping. -/

/-- **The heat-operator residual of the `N`-term parametrix** `H_N = G·Θ^{−1/2}·Σ_{k≤N} u_k t^k`:
    `parametrixResidualN N g gi Θ u t x = (∂_t − Δ_g) H_N (t,x)`.  (For `N = 1` this is
    `HeatParametrixOrder.parametrixResidual`.) -/
noncomputable def parametrixResidualN (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (t : ℝ) (x : Point n) : ℝ :=
  deriv (fun s => heatParametrix N Θ u s x) t
    - laplaceBeltrami g gi (heatParametrix N Θ u t) x

/-- **THE GENERAL-`N` DIAGONAL TELESCOPING IDENTITY (J5a).**  At the RNC diagonal center `0`
    (`g^{ij}(0)=δ`, `Γ(0)=0`), GIVEN the folded diagonal transport recursion
      `hrec : ∀ k < N, (k+1)·w_{k+1}(0) = Δ_g(w_k)(0)`   (`w_k = Θ^{−1/2}u_k`, from J3/J4)
    and the coefficient smoothness `hw`, the heat-operator residual of `H_N` is EXACTLY the `t^N`
    tail:
      `(∂_t − Δ_g) H_N(t,0) = − G(0)·Δ_g(Θ^{−1/2}u_N)(0)·t^N` .

    Every lower order `t^0…t^{N−1}` cancels: the `∂_t G = Δ_g G` flat-heat term cancels the leading
    Laplacian term (`laplaceBeltrami_gaussMul_at_zero`), and `hrec` telescopes the remaining bracket
    (`telescope_bracket`).  This is Rosenberg §3.2.1's `(∂_t − Δ_g)H_N = −G·Θ^{−1/2}(Δ_g u_N)t^N` at
    the diagonal, for general `N`. -/
theorem parametrixResidual_telescope_N (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hrec : ∀ k, k < N →
      ((k : ℝ) + 1) * foldedCoeff Θ u (k + 1) (0 : Point n)
        = laplaceBeltrami g gi (foldedCoeff Θ u k) (0 : Point n)) :
    parametrixResidualN N g gi Θ u t (0 : Point n)
      = - gaussDdim t (0 : Point n)
          * laplaceBeltrami g gi (foldedCoeff Θ u N) (0 : Point n) * t ^ N := by
  -- (A) the `t`-derivative of `H_N(·,0)` via the product rule `(∂_t G)·P + G·(∂_t P)`
  have hgaussHD : HasDerivAt (fun s => gaussDdim s (0 : Point n))
      (deriv (fun s => gaussDdim s (0 : Point n)) t) t := by
    have hFP := HasDerivAt.fun_finsetProd
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        heatKernel1D_hasDerivAt_t t ((0 : Point n) i) ht)
    exact hFP.differentiableAt.hasDerivAt
  have hpoly : HasDerivAt
      (fun s => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k (0 : Point n) * s ^ k)
      (∑ k ∈ Finset.range (N + 1),
        foldedCoeff Θ u k (0 : Point n) * ((k : ℝ) * t ^ (k - 1))) t := by
    have key : HasDerivAt
        (∑ k ∈ Finset.range (N + 1), fun s : ℝ => foldedCoeff Θ u k (0 : Point n) * s ^ k)
        (∑ k ∈ Finset.range (N + 1),
          foldedCoeff Θ u k (0 : Point n) * ((k : ℝ) * t ^ (k - 1))) t :=
      HasDerivAt.sum (fun k _ => (hasDerivAt_pow k t).const_mul (foldedCoeff Θ u k (0 : Point n)))
    have hfun : (∑ k ∈ Finset.range (N + 1), fun s : ℝ => foldedCoeff Θ u k (0 : Point n) * s ^ k)
        = (fun s => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k (0 : Point n) * s ^ k) := by
      funext s; simp only [Finset.sum_apply]
    rw [hfun] at key
    exact key
  have hderiv_fun : (fun s => heatParametrix N Θ u s (0 : Point n))
      = (fun s => gaussDdim s (0 : Point n)
          * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k (0 : Point n) * s ^ k) :=
    funext (fun s => heatParametrix_folded N Θ u s (0 : Point n))
  have hderivval : deriv (fun s => heatParametrix N Θ u s (0 : Point n)) t
      = deriv (fun s => gaussDdim s (0 : Point n)) t
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k (0 : Point n) * t ^ k)
        + gaussDdim t (0 : Point n)
          * ∑ k ∈ Finset.range (N + 1),
              foldedCoeff Θ u k (0 : Point n) * ((k : ℝ) * t ^ (k - 1)) := by
    rw [hderiv_fun]; exact (hgaussHD.mul hpoly).deriv
  -- (B) the `Δ_g` of `H_N(t,·)` via the diagonal Gaussian-product rule + `Δ_g` sum-linearity
  have hwsum : ContDiff ℝ ⊤
      (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) :=
    ContDiff.sum (fun k _ => (hw k).mul contDiff_const)
  have hHeq : heatParametrix N Θ u t
      = (fun y => gaussDdim t y * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) :=
    funext (fun y => heatParametrix_folded N Θ u t y)
  have hΔval : laplaceBeltrami g gi (heatParametrix N Θ u t) (0 : Point n)
      = laplaceBeltrami g gi (gaussDdim t) (0 : Point n)
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k (0 : Point n) * t ^ k)
        + gaussDdim t (0 : Point n)
          * ∑ k ∈ Finset.range (N + 1),
              laplaceBeltrami g gi (foldedCoeff Θ u k) (0 : Point n) * t ^ k := by
    rw [hHeq,
        laplaceBeltrami_gaussMul_at_zero g gi t ht
          (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) hwsum hgi hΓ,
        laplaceBeltrami_sum_pow g gi (foldedCoeff Θ u) t (0 : Point n) N hw]
  -- the flat heat equation turns `∂_t G` into `Δ_g G` at the center
  have hheat : deriv (fun s => gaussDdim s (0 : Point n)) t
      = laplaceBeltrami g gi (gaussDdim t) (0 : Point n) := by
    rw [gaussDdim_heat_eqn t ht (0 : Point n),
        laplaceBeltrami_at_rnc_center g gi (gaussDdim t) (0 : Point n) hgi hΓ]
  -- the telescoping bracket
  have hbr := telescope_bracket (fun k => foldedCoeff Θ u k (0 : Point n))
    (fun k => laplaceBeltrami g gi (foldedCoeff Θ u k) (0 : Point n)) t N hrec
  -- assemble: the `Δ_g G · Σ w_k t^k` terms cancel, the bracket telescopes
  unfold parametrixResidualN
  rw [hderivval, hΔval, hheat]
  linear_combination gaussDdim t (0 : Point n) * hbr

/-! ### J5-offdiag — the cross-gradient = radial-derivative identity and the off-diagonal
    residual decomposition (the analytic crux).

  J5a telescoped the residual AT THE DIAGONAL (`v = 0`), where the Gaussian gradient `∂ᵢG(0) = 0`
  lets `laplaceBeltrami_gaussMul_at_zero` DROP the cross-gradient term of `laplaceBeltrami_mul`.
  Off the diagonal that term is NONZERO.  This section proves the structural fact that makes the
  off-diagonal construction work: the (Euclidean) cross-gradient `Σᵢ (∂ᵢG)(∂ᵢh)` is EXACTLY a
  radial-derivative term — the Euler field `r∂_r` — because `∂ᵢG = (−vⁱ/2t)G`.  This is why the
  DeWitt `(k + r∂_r)`-transport recursion is built to absorb it. -/

/-! #### #1 — the Gaussian gradient `∂ᵢG(v) = (−vⁱ/2t)G(v)` (off the diagonal too). -/

/-- **The Gaussian gradient, everywhere.**  `∂ᵢ G_t(v) = (−vⁱ/(2t))·G_t(v)` — the componentwise
    gradient of the flat `d`-dimensional Gaussian, valid at EVERY point `v` (not just the center).
    This is `FlatHeatEquation.gaussDdim_pd_i`; unlike the diagonal simplification of J5a it does NOT
    vanish for `v ≠ 0`.  It is the seed of the cross-gradient = radial-derivative identity. -/
theorem gaussDdim_pd_eq (t : ℝ) (ht : 0 < t) (v : Point n) (i : Fin n) :
    pd (fun y => gaussDdim t y) i v = (-(v i) / (2 * t)) * gaussDdim t v :=
  gaussDdim_pd_i t ht v i

/-! #### #2 — THE KEY IDENTITY: the cross-gradient IS the radial derivative. -/

/-- **THE CROSS-GRADIENT = RADIAL-DERIVATIVE IDENTITY.**  For any smooth field `h`, the Euclidean
    inner product of the Gaussian gradient with `∇h`,
      `Σᵢ (∂ᵢG)(∂ᵢh) = (−1/(2t))·G·(r∂_r h)` ,
    where `r∂_r h = radialDeriv h = Σᵢ vⁱ ∂ᵢh` is the Euler radial field.  MECHANISM: `∂ᵢG =
    (−vⁱ/2t)G` (#1), so `Σᵢ ∂ᵢG ∂ᵢh = (−1/2t)G·Σᵢ vⁱ ∂ᵢh = (−1/2t)G·(r∂_r h)` — the coordinate
    weight `vⁱ` from the Gaussian gradient is EXACTLY the Euler field's weight.  This is THE reason
    the off-diagonal telescoping can work: the cross-gradient term is a radial-derivative term, and
    the transport recursion `(k + r∂_r)w_k = Δ_g w_{k−1}` is designed to absorb it. -/
theorem crossGrad_eq_radial (t : ℝ) (ht : 0 < t) (h : Point n → ℝ) (v : Point n) :
    (∑ i, pd (fun y => gaussDdim t y) i v * pd h i v)
      = (-1 / (2 * t)) * gaussDdim t v * radialDeriv h v := by
  simp only [radialDeriv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gaussDdim_pd_eq t ht v i]; ring

/-- **The full (symmetric, flat-metric) cross-gradient term equals `−(1/t)·G·(r∂_r h)`.**  Under the
    RNC-center flat inverse metric `gⁱʲ = δⁱʲ`, the cross-gradient block of `laplaceBeltrami_mul`,
      `Σᵢⱼ δⁱʲ ((∂ᵢG)(∂ⱼh) + (∂ⱼG)(∂ᵢh)) = 2·Σᵢ (∂ᵢG)(∂ᵢh)` ,
    collapses (via #2) to `−(1/t)·G·(r∂_r h)`.  This is the cross-gradient term written as the pure
    radial-derivative term the transport recursion absorbs — the identity behind the "radial term
    absorbs the cross-gradient" step of the off-diagonal telescoping. -/
theorem flatCrossTerm_eq (t : ℝ) (ht : 0 < t) (h : Point n → ℝ) (v : Point n) :
    (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0)
        * (pd (fun y => gaussDdim t y) i v * pd h j v
            + pd (fun y => gaussDdim t y) j v * pd h i v))
      = (-1 / t) * gaussDdim t v * radialDeriv h v := by
  have hstep : ∀ i : Fin n, (∑ j, (if i = j then (1 : ℝ) else 0)
      * (pd (fun y => gaussDdim t y) i v * pd h j v
          + pd (fun y => gaussDdim t y) j v * pd h i v))
      = 2 * (pd (fun y => gaussDdim t y) i v * pd h i v) := by
    intro i
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i
      (fun j => pd (fun y => gaussDdim t y) i v * pd h j v
        + pd (fun y => gaussDdim t y) j v * pd h i v)]
    simp only [Finset.mem_univ, if_true]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.mul_sum,
      crossGrad_eq_radial t ht h v]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-! #### #3 — the off-diagonal residual decomposition and the "radial term absorbs the
    cross-gradient" step (the reachable part of the crux; the curvature term is checkpointed). -/

/-- **THE OFF-DIAGONAL RESIDUAL DECOMPOSITION (general metric, general point `v`).**  Without any
    diagonal simplification, the heat-operator residual of `H_N = G·Σ_{k≤N} w_k t^k` splits, by the
    `∂_t` product rule and the FULL curved product rule `laplaceBeltrami_mul` (cross-gradient kept),
    into four pieces:
      `(∂_t − Δ_g)H_N(t,v)`
        `= ((∂_t G) − Δ_g G)(v)·Σ_{k≤N} w_k(v) t^k`          -- (I) the flat-Gaussian CURVATURE term
        `+ G(v)·Σ_{k≤N} w_k(v)·(k t^{k−1})`                   -- (II) the ∂_t of the coefficient poly
        `− G(v)·Σ_{k≤N} (Δ_g w_k)(v) t^k`                     -- (III) the Δ_g of the coefficient poly
        `− Σᵢⱼ gⁱʲ ((∂ᵢG)(∂ⱼP) + (∂ⱼG)(∂ᵢP))(v)` .            -- (IV) the cross-gradient
    At the diagonal (`v = 0`) piece (I) vanishes (flat heat equation + `Δ_g = Δ_flat` at an RNC
    center) and piece (IV) vanishes (`∂ᵢG(0) = 0`), recovering J5a.  Off the diagonal neither
    vanishes: (I) is the flat-Gaussian curvature residue `(∂_t − Δ_g)G` and (IV) is the cross-gradient
    that #2/`flatCrossTerm_eq` identify as a radial-derivative term.  This decomposition is a genuine,
    unconditional identity (only coefficient smoothness `hw` is used). -/
theorem parametrixResidual_offdiag_decomp (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    parametrixResidualN N g gi Θ u t v
      = (deriv (fun s => gaussDdim s v) t - laplaceBeltrami g gi (gaussDdim t) v)
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
            * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
        - gaussDdim t v
            * (∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        - (∑ i, ∑ j, gi v i j
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
  -- (A) the `t`-derivative of `H_N(·,v)` via the product rule `(∂_t G)·P + G·(∂_t P)`
  have hgaussHD : HasDerivAt (fun s => gaussDdim s v)
      (deriv (fun s => gaussDdim s v) t) t := by
    have hFP := HasDerivAt.fun_finsetProd
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        heatKernel1D_hasDerivAt_t t (v i) ht)
    exact hFP.differentiableAt.hasDerivAt
  have hpoly : HasDerivAt
      (fun s => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * s ^ k)
      (∑ k ∈ Finset.range (N + 1),
        foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1))) t := by
    have key : HasDerivAt
        (∑ k ∈ Finset.range (N + 1), fun s : ℝ => foldedCoeff Θ u k v * s ^ k)
        (∑ k ∈ Finset.range (N + 1),
          foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1))) t :=
      HasDerivAt.sum (fun k _ => (hasDerivAt_pow k t).const_mul (foldedCoeff Θ u k v))
    have hfun : (∑ k ∈ Finset.range (N + 1), fun s : ℝ => foldedCoeff Θ u k v * s ^ k)
        = (fun s => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * s ^ k) := by
      funext s; simp only [Finset.sum_apply]
    rw [hfun] at key
    exact key
  have hderiv_fun : (fun s => heatParametrix N Θ u s v)
      = (fun s => gaussDdim s v
          * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * s ^ k) :=
    funext (fun s => heatParametrix_folded N Θ u s v)
  have hderivval : deriv (fun s => heatParametrix N Θ u s v) t
      = deriv (fun s => gaussDdim s v) t
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
          * ∑ k ∈ Finset.range (N + 1),
              foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)) := by
    rw [hderiv_fun]; exact (hgaussHD.mul hpoly).deriv
  -- (B) the `Δ_g` of `H_N(t,·)` via the FULL curved product rule (cross-gradient KEPT)
  have hwsum : ContDiff ℝ ⊤
      (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) :=
    ContDiff.sum (fun k _ => (hw k).mul contDiff_const)
  have hHeq : heatParametrix N Θ u t
      = (fun y => gaussDdim t y * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) :=
    funext (fun y => heatParametrix_folded N Θ u t y)
  have hΔval : laplaceBeltrami g gi (heatParametrix N Θ u t) v
      = laplaceBeltrami g gi (gaussDdim t) v
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
          * (∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        + ∑ i, ∑ j, gi v i j
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v) := by
    rw [hHeq,
        laplaceBeltrami_mul g gi (fun y => gaussDdim t y)
          (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) v
          (gaussDdim_contDiff t) hwsum,
        laplaceBeltrami_sum_pow g gi (foldedCoeff Θ u) t v N hw]
  unfold parametrixResidualN
  rw [hderivval, hΔval]
  ring

/-- **THE OFF-DIAGONAL ABSORPTION IDENTITY — "the radial term absorbs the cross-gradient".**
    Rewriting the cross-gradient of the decomposition as its FLAT part plus a metric-deviation part
    (`gⁱʲ = δⁱʲ + (gⁱʲ − δⁱʲ)`), the flat part is `−(1/t)·G·(r∂_r P)` (`flatCrossTerm_eq`, via the
    #2 identity), so its subtraction in `(∂_t − Δ_g)H_N` becomes `+(1/t)·G·(r∂_r P)` — the RADIAL
    TRANSPORT term.  Hence the residual is
      `(∂_t − Δ_g)H_N(t,v)`
        `= ((∂_t G) − Δ_g G)(v)·P(v)`                                   -- (I) curvature residue ⚠ CHECKPOINT
        `+ G(v)·( ∂_t P + (1/t)·(r∂_r P) )(v)`                          -- (II) the RADIAL-TRANSPORT operator
        `− G(v)·Σ_{k≤N} (Δ_g w_k)(v) t^k`                               -- (III) Δ_g of the coefficients
        `− Σᵢⱼ (gⁱʲ − δⁱʲ)((∂ᵢG)(∂ⱼP)+(∂ⱼG)(∂ᵢP))(v)` .                 -- (IV) metric-deviation residue ⚠ CHECKPOINT
    Piece (II) is exactly `∂_t P + t⁻¹ r∂_r P = Σ_k (k w_k + r∂_r w_k) t^{k−1}`, the flat-Gaussian
    radial-transport operator whose order-`t^{k−1}` term is `(k + r∂_r)w_k` — precisely the LHS of the
    DeWitt off-diagonal transport recursion `(k + r∂_r)w_k = Δ_g w_{k−1}`.  So the cross-gradient of
    the curved Laplacian has been ABSORBED into the radial transport, converting J5a's diagonal-only
    telescoping into a precise identity whose ONLY obstructions to full off-diagonal telescoping are
    the two flagged residues:
      • (I)  the flat-Gaussian CURVATURE term `(∂_t − Δ_g)G` off-diagonal — the metric-deviation of
             the Laplacian acting on the Gaussian (needs the off-diagonal `Δ_g − Δ_flat` estimate);
      • (IV) the metric-deviation of the cross-gradient, `Σᵢⱼ (gⁱʲ − δⁱʲ)(…)` (needs `gⁱʲ − δⁱʲ =
             O(r²)` from RNC).
    Both vanish at the diagonal (`v = 0`), recovering J5a; both are the genuine residue of J5-offdiag.
    (Only coefficient smoothness `hw` is used; the metric is arbitrary.) -/
theorem parametrixResidual_offdiag_absorbed (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    parametrixResidualN N g gi Θ u t v
      = (deriv (fun s => gaussDdim s v) t - laplaceBeltrami g gi (gaussDdim t) v)
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
            * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
        + (1 / t) * gaussDdim t v
            * radialDeriv (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) v
        - gaussDdim t v
            * (∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        - (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
  -- split the curved cross-gradient into its metric-deviation part + the flat (δ) part
  have hsplit : (∑ i, ∑ j, gi v i j
        * (pd (fun y => gaussDdim t y) i v
              * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
          + pd (fun y => gaussDdim t y) j v
              * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v))
      = (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
          * (pd (fun y => gaussDdim t y) i v
                * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
            + pd (fun y => gaussDdim t y) j v
                * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v))
        + (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0)
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [parametrixResidual_offdiag_decomp N g gi Θ u t ht v hw, hsplit,
      flatCrossTerm_eq t ht
        (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) v]
  ring

end QIQTH.HeatResidualBound
