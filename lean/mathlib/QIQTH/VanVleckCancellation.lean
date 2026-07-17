/-
  VanVleckCancellation — J5-vanvleck of the Jacobi/van-Vleck campaign
  (docs/qg_roadmap/JACOBI_VANVLECK_PLAN.md): THE VAN-VLECK LEADING CANCELLATION and the DERIVATION of
  the parametrix diagonal coefficient `u₁(0) = R/6`.

  WHAT IS BUILT HERE (the honest boundary — read it).

  The Minakshisundaram–DeWitt parametrix `H_N = G·Θ^{−1/2}·Σ u_k t^k` (`ParametrixFunction`) carries a
  transport-source operator `T`; its first diagonal coefficient is a labelled input
  `hu1 : transportCoeff T 1 (0) = R/6` in `ParametrixFunction.heatParametrixFn_diagonal_a1`.  This file
  DERIVES that value for the CONCRETE DeWitt source `T = transportOp (vanVleck g) g gi`
  (`= Θ^{−1/2} Δ_g (Θ^{1/2} ·)`, `HeatTransportRecursion.transportOp`, `Θ = vanVleck g`), turning the
  carried `R/6` into a THEOREM:

      transportCoeff (transportOp (vanVleck g) g gi) 1 (0) = (∑ i, Ric i i) / 6 .

  MECHANISM (the van-Vleck leading cancellation, at the diagonal).
    • The radial (Euler) field vanishes at the RNC centre (`radialDeriv_zero`), so the DeWitt radial
      transport recursion `(k+1 + r∂_r) u_{k+1} = T u_k` (J4) collapses at `0` to
      `u_{k+1}(0) = (1/(k+1))·T(u_k)(0)` — `transportCoeff_one_diag`.  This is the diagonal face of the
      van-Vleck cancellation: the `O(1/t)` radial-derivative singularity that `Θ^{−1/2}` is chosen to
      kill (`HeatResidualBound.parametrixResidual_offdiag_absorbed`, piece (II)) contributes `0` at the
      centre, leaving the pure `Δ_g` driver.
    • With `u_0 ≡ 1` and `T = transportOp Θ g gi`, the `k=0` datum is `T(1)(0) = Θ(0)^{−1/2}·Δ_g(Θ^{1/2})(0)`;
      since `Θ(0) = 1` (`vanVleck_zero`) this is `Δ_g(Θ^{1/2})(0)` — `transportOp_const_one_diag`.
    • `Θ^{1/2} = (vanVleck g)^{1/2} = (det g)^{−1/4}` near the centre, so `Δ_g(Θ^{1/2})(0)` is the flat
      trace of the Hessian of `(det g)^{−1/4}` at an RNC centre.  The van-Vleck power-chain rule at a
      critical point (`rpow_pd_pd_crit`: `∂∂(F^p)(0) = p·∂∂F(0)` where `F(0)=1, ∂F(0)=0`) with `p=−1/4`
      converts this to `(−1/4)·tr ∂∂(det g)(0)`, and the metric-Hessian trace `tr ∂∂(det g)(0) = −⅔ Ric`
      (the RNC datum `htr`, via `det_pd_pd_diag`) gives `(−1/4)·(−⅔)·R = R/6` — `laplaceBeltrami_detpow_diag`.

  This is EXACTLY where `R/6` enters: the surviving `t⁰` diagonal term of `(∂_t−Δ_g)(G·Θ^{−1/2})` is
  `Θ^{−1/2}Δ_g(Θ^{1/2})(0) = R/6` (Rosenberg §3.2.1, Gilkey; the van-Vleck factor cancels the leading
  singular term and leaves the scalar-curvature diagonal value).

  ⚠ HONEST SCOPE (binding).  This DERIVES the DIAGONAL coefficient `u₁(0) = R/6` for the concrete
  van-Vleck source, DISCHARGING the labelled `hu1` of `heatParametrixFn_diagonal_a1`
  (`heatParametrixFn_diagonal_a1_derived`).  It uses:
    • `htr : tr ∂∂g(0) = −⅔ Ric` — the RNC metric-Hessian-trace datum (carried EXACTLY as
      `RNCExpansion.sqrtdet_pd_pd` demands; RNC3 `rnc_htr_of_gauge` discharges it from the
      normal-coordinate gauge — genuine, load-bearing, non-vacuous: remove it and `R/6` is false);
    • `hsrc : ContDiff ℝ ⊤ (transportOp (vanVleck g) g gi (fun _ => 1))` — the J3 transport-source
      smoothness (genuine, load-bearing: `transportCoeff_succ_transport_eq`'s IBP needs it);
    • RNC-centre data `hgi, hΓ, hg0, hdg0` (the normal-coordinate chart).
  It does NOT build: the OFF-DIAGONAL leading-transport ODE as an autonomous identity (that is the
  radial-transport engine of J3/`HeatResidualBound.parametrixResidual_offdiag_absorbed`), the `O(t^N)`
  Gaussian bound (J5b), nor the true-kernel `a₁` (which additionally needs parametrix convergence).
  The CHECKPOINT for the full off-diagonal cancellation is recorded precisely at the end of the file.
  No axioms, no `sorry`.

  Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1; Berline–Getzler–Vergne §2.5;
  Gilkey, *Invariance Theory…*.
-/
import Mathlib
import QIQTH.VanVleck
import QIQTH.RadialDistance
import QIQTH.HeatResidualBound
import QIQTH.HeatTransportRecursion
import QIQTH.ParametrixFunction
import QIQTH.RNCExpansion
import QIQTH.LaplaceBeltrami

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open Real

namespace QIQTH.VanVleckCancellation

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ### #0 — the radial (Euler) field vanishes at the RNC centre. -/

/-- **The radial derivative vanishes at the centre `0`.**  `r∂_r f(0) = ∑ᵢ 0·∂ᵢf(0) = 0` — the Euler
    field `∑ᵢ vⁱ∂ᵢ` has all coefficients `vⁱ = 0` at the centre.  This is the diagonal face of the
    van-Vleck leading cancellation: the `O(1/t)` radial-derivative singularity absorbed by `Θ^{−1/2}`
    (`HeatResidualBound.parametrixResidual_offdiag_absorbed`, piece (II)) contributes `0` at the centre. -/
theorem radialDeriv_zero (f : Point n → ℝ) : radialDeriv f (0 : Point n) = 0 := by
  simp only [radialDeriv, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-! ### #1a — the diagonal transport recursion collapse `u₁(0) = T(1)(0)`. -/

/-- **The diagonal collapse of the DeWitt transport recursion.**  Since `r∂_r` vanishes at the centre
    (`radialDeriv_zero`), the radial transport ODE `(1 + r∂_r) u₁ = T u₀` (J4's
    `transportCoeff_succ_transport_eq` at `k=0`) reduces at `0` to `u₁(0) = T(u₀)(0)`.  Given the J3
    transport-source smoothness `hf`. -/
theorem transportCoeff_one_diag (T : (Point n → ℝ) → (Point n → ℝ))
    (hf : ContDiff ℝ ⊤ (T (transportCoeff T 0))) :
    transportCoeff T 1 (0 : Point n) = T (transportCoeff T 0) (0 : Point n) := by
  have h := transportCoeff_succ_transport_eq T 0 hf (0 : Point n)
  rw [radialDeriv_zero] at h
  simpa using h

/-! ### #1b — the van-Vleck power-chain rule at a critical point (the leading-cancellation atom). -/

/-- **First-order chain rule for `F^p` where `F > 0`**: `∂ᵢ(F^p) = (p·F^{p−1})·∂ᵢF`.  The `rpow`
    counterpart of `RNCExpansion.pd_comp_sqrt`. -/
theorem pd_comp_rpow (F : Point n → ℝ) (p : ℝ) (i : Fin n) (x : Point n)
    (hF : PdiffAt F i x) (hpos : 0 < F x) :
    pd (fun y => (F y) ^ p) i x = (p * (F x) ^ (p - 1)) * pd F i x := by
  simp only [pd]
  have hval : F (Function.update x i (x i)) = F x := by rw [Function.update_eq_self]
  have hrpow : HasDerivAt (fun z : ℝ => z ^ p) (p * (F x) ^ (p - 1))
      (F (Function.update x i (x i))) := by
    rw [hval]; exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hpos))
  exact (hrpow.comp (x i) hF.hasDerivAt).deriv

/-- **THE VAN-VLECK POWER-CHAIN RULE AT A CRITICAL POINT.**  For `F(x) = 1` and `∂F(x) = 0`, the second
    derivative of `F^p` is `p` times that of `F`:
      `∂_c∂_d (F^p) (x) = p · ∂_c∂_d F (x)` .
    (The `(∂F)²·p(p−1)F^{p−2}` cross term drops because `∂F(x)=0`; the prefactor `p·F^{p−1}(x) = p`.)
    This is the atom of the van-Vleck cancellation: `Θ^{−1/2} = (det g)^{κ}` is a POWER of the metric
    determinant, so its Laplacian at the centre is `κ` times the metric-Hessian trace.  The `rpow`
    counterpart of `RNCExpansion.sqrt_pd_pd`. -/
theorem rpow_pd_pd_crit (F : Point n → ℝ) (p : ℝ) (c d : Fin n) (x : Point n)
    (hF : ContDiff ℝ ⊤ F) (hval : F x = 1) (hcrit : ∀ e, pd F e x = 0) :
    pd (fun y => pd (fun w => (F w) ^ p) d y) c x = p * pd (fun y => pd F d y) c x := by
  have hpos : 0 < F x := by rw [hval]; norm_num
  have hne : F x ≠ 0 := ne_of_gt hpos
  have hcont : Continuous F := hF.continuous
  have hnhds : ∀ᶠ y in nhds x, 0 < F y :=
    continuousAt_const.eventually_lt hcont.continuousAt hpos
  -- the chain rule holds eventually near x (where F > 0)
  have hchain : (fun y => pd (fun w => (F w) ^ p) d y)
      =ᶠ[nhds x] (fun y => (p * (F y) ^ (p - 1)) * pd F d y) := by
    filter_upwards [hnhds] with y hy
    exact pd_comp_rpow F p d y (PdiffAt_of_contDiff F hF d y) hy
  rw [pd_congr c x hchain]
  -- differentiability of the two factors at x
  have hB : PdiffAt (fun y => pd F d y) c x := PdiffAt_pd F hF d c x
  have hγc : DifferentiableAt ℝ (fun t => F (Function.update x c t)) (x c) :=
    PdiffAt_of_contDiff F hF c x
  have hFxc : F (Function.update x c (x c)) = F x := by rw [Function.update_eq_self]
  have hrpowd : DifferentiableAt ℝ (fun z : ℝ => z ^ (p - 1)) (F (Function.update x c (x c))) := by
    rw [hFxc]; exact (Real.hasDerivAt_rpow_const (Or.inl hne)).differentiableAt
  have hcompd : DifferentiableAt ℝ (fun t => (F (Function.update x c t)) ^ (p - 1)) (x c) := by
    have h := hrpowd.comp (x c) hγc
    simpa [Function.comp] using h
  have hA : PdiffAt (fun y => p * (F y) ^ (p - 1)) c x := by
    show DifferentiableAt ℝ (fun t => p * (F (Function.update x c t)) ^ (p - 1)) (x c)
    exact (differentiableAt_const p).mul hcompd
  rw [pd_mul (fun y => p * (F y) ^ (p - 1)) (fun y => pd F d y) c x hA hB]
  rw [hcrit d, mul_zero, zero_add, hval, Real.one_rpow, mul_one]

/-! ### #1c — the metric-determinant Hessian trace (`det g` at the RNC centre). -/

/-- **The second derivative of `det g` at the centre collapses to the metric-Hessian trace.**
    `∂_c∂_d (det g) (0) = ∑ₐ ∂_c∂_d g_{aa}(0)` — the `σ=1` permutation term survives (`g(0)=δ`), all
    `σ≠1` terms vanish (a moved off-diagonal `g_{σi,i}(0)=0`), and the cross-Leibniz `∂g·∂g` terms drop
    (`∂g(0)=0`).  Extracted from `RNCExpansion.sqrtdet_pd_pd`'s internal computation. -/
theorem det_pd_pd_diag (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0) (c d : Fin n) :
    pd (fun y => pd (fun w => Matrix.det (g w)) d y) c 0
      = ∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0 := by
  rw [det_pd_pd_expand g hg hdg0 c d, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.prod_eq_one (fun i _ => by rw [hg0 i i]; exact Matrix.one_apply_eq i), mul_one]
  · intro σ _ hσ
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro k _
    apply mul_eq_zero_of_right
    obtain ⟨i0, hi0mem, hi0⟩ := perm_moves_in_erase σ hσ k
    exact Finset.prod_eq_zero hi0mem (by rw [hg0 (σ i0) i0]; exact Matrix.one_apply_ne hi0)
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### #1d — `Δ_g((det g)^{−1/4})(0) = R/6` (the van-Vleck leading value at the diagonal). -/

/-- **THE VAN-VLECK LEADING DIAGONAL VALUE.**  The Laplace–Beltrami of `(det g)^{−1/4}` at an RNC centre
    is the scalar curvature over `6`:
      `Δ_g ((det g)^{−1/4}) (0) = (∑ᵢ Ric_{ii}) / 6` .
    ROUTE: at the RNC centre `Δ_g = ∑ᵢ ∂ᵢ²` (`laplaceBeltrami_at_rnc_center`); the van-Vleck power-chain
    rule (`rpow_pd_pd_crit`, `p = −1/4`, `det g(0)=1`, `∂ det g(0)=0`) converts `∂ᵢ²((det g)^{−1/4})(0)`
    to `(−1/4)·∂ᵢ²(det g)(0)`; `det_pd_pd_diag` + the carried metric-Hessian trace `htr` gives
    `∂ᵢ²(det g)(0) = ∑ₐ ∂ᵢ² g_{aa}(0) = −⅔ Ric_{ii}`; and `(−1/4)·(−⅔)·∑ Ric_{ii} = (∑Ric)/6`.
    `htr` is load-bearing (RNC3 discharges it from the gauge). -/
theorem laplaceBeltrami_detpow_diag (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d) :
    laplaceBeltrami g gi (fun y => (Matrix.det (g y)) ^ (-(1 : ℝ) / 4)) (0 : Point n)
      = (∑ i, Ric i i) / 6 := by
  have hF : ContDiff ℝ ⊤ (fun y => Matrix.det (g y)) := det_contDiff g hg
  have hg0mat : g 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by funext i j; exact hg0 i j
  have hF0 : (fun y => Matrix.det (g y)) 0 = 1 := by
    show Matrix.det (g 0) = 1; rw [hg0mat, Matrix.det_one]
  have hcrit : ∀ e, pd (fun y => Matrix.det (g y)) e 0 = 0 := det_pd_first g hg hdg0
  rw [laplaceBeltrami_at_rnc_center g gi _ (0 : Point n) hgi hΓ]
  have hstep : ∀ i : Fin n,
      pd (fun y => pd (fun w => (Matrix.det (g w)) ^ (-(1 : ℝ) / 4)) i y) i (0 : Point n)
        = (-(1 : ℝ) / 4) * ∑ a, pd (fun y => pd (fun w => g w a a) i y) i 0 := by
    intro i
    rw [rpow_pd_pd_crit (fun y => Matrix.det (g y)) (-(1 : ℝ) / 4) i i (0 : Point n) hF hF0 hcrit,
        det_pd_pd_diag g hg hg0 hdg0 i i]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  have hval : ∀ i : Fin n, (-(1 : ℝ) / 4) * ∑ a, pd (fun y => pd (fun w => g w a a) i y) i 0
      = (1 / 6) * Ric i i := by
    intro i; rw [htr i i]; ring
  rw [Finset.sum_congr rfl (fun i _ => hval i), ← Finset.mul_sum]; ring

/-- **`Δ_g` depends only on the germ.**  If `f = h` on a neighbourhood of `x`, then
    `Δ_g f (x) = Δ_g h (x)` — the Laplace–Beltrami operator sees `f` only through `pd f`, `pd (pd f)`
    at `x`, all germ-local.  Used to swap `Θ^{1/2} = (vanVleck g)^{1/2}` for `(det g)^{−1/4}` near `0`. -/
theorem laplaceBeltrami_congr_nhds (g gi : Point n → Fin n → Fin n → ℝ) (f h : Point n → ℝ)
    (x : Point n) (hfh : ∀ᶠ y in nhds x, f y = h y) :
    laplaceBeltrami g gi f x = laplaceBeltrami g gi h x := by
  have hpd1 : ∀ k, pd f k x = pd h k x := fun k => pd_congr k x hfh
  have hpd2 : ∀ i j, pd (fun y => pd f j y) i x = pd (fun y => pd h j y) i x := by
    intro i j
    refine pd_congr i x ?_
    filter_upwards [hfh.eventually_nhds] with y hy
    exact pd_congr j y hy
  simp only [laplaceBeltrami]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hpd2 i j]
  have hsum : (∑ k, christoffel g gi k i j x * pd f k x)
      = ∑ k, christoffel g gi k i j x * pd h k x :=
    Finset.sum_congr rfl (fun k _ => by rw [hpd1 k])
  rw [hsum]

/-! ### #1e — the DeWitt source diagonal value (`transportOp` on the constant `1`). -/

/-- **The van-Vleck DeWitt source at the centre is `Δ_g(Θ^{1/2})(0)`.**  For `Θ(0)=1` the outer
    `Θ^{−1/2}(0) = 1`, so `transportOp Θ g gi 1 (0) = Δ_g(Θ^{1/2})(0)`. -/
theorem transportOp_const_one_diag (Θ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (hΘ0 : Θ (0 : Point n) = 1) :
    transportOp Θ g gi (fun _ => 1) (0 : Point n)
      = laplaceBeltrami g gi (fun y => Θ y ^ ((1 : ℝ) / 2)) (0 : Point n) := by
  unfold transportOp
  rw [hΘ0,
      show (1 : ℝ) ^ (-(1 / 2) : ℝ) = 1 from Real.one_rpow _, one_mul,
      show (fun y => Θ y ^ ((1 / 2) : ℝ) * (1 : ℝ)) = (fun y => Θ y ^ ((1 : ℝ) / 2)) from
        funext (fun y => by rw [mul_one])]

/-- **THE DERIVED DIAGONAL `R/6` FOR THE CONCRETE VAN-VLECK DeWitt SOURCE.**  The DeWitt transport
    source `T = transportOp (vanVleck g) g gi = Θ^{−1/2}Δ_g(Θ^{1/2}·)` at the centre, applied to the
    base `u₀ ≡ 1`, equals the scalar curvature over `6`:
      `transportOp (vanVleck g) g gi 1 (0) = (∑ᵢ Ric_{ii}) / 6` .
    ROUTE: `transportOp_const_one_diag` (Θ(0)=1) reduces it to `Δ_g(Θ^{1/2})(0)`; near the centre
    `Θ^{1/2} = (vanVleck g)^{1/2} = (det g)^{−1/4}` (`laplaceBeltrami_congr_nhds`, det>0); then
    `laplaceBeltrami_detpow_diag` gives `R/6`.  This is the surviving `t⁰` diagonal term of the
    van-Vleck-cancelled residual `(∂_t−Δ_g)(G·Θ^{−1/2})`. -/
theorem transportSource_diag_eq_scalarCurv (g gi : Point n → Fin n → Fin n → ℝ)
    (Ric : Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d) :
    transportOp (vanVleck g) g gi (fun _ => 1) (0 : Point n) = (∑ i, Ric i i) / 6 := by
  have hg0mat : g 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by funext i j; exact hg0 i j
  have hdet0 : Matrix.det (g 0) = 1 := by rw [hg0mat, Matrix.det_one]
  rw [transportOp_const_one_diag (vanVleck g) g gi (vanVleck_zero g hdet0)]
  -- Θ^{1/2} = (det g)^{−1/4} near 0 (det > 0), so the Laplacians agree
  have hcont : Continuous (fun y => Matrix.det (g y)) := (det_contDiff g hg).continuous
  have hpos : ∀ᶠ y in nhds (0 : Point n), 0 < Matrix.det (g y) :=
    continuousAt_const.eventually_lt hcont.continuousAt (by rw [hdet0]; norm_num)
  have hev : ∀ᶠ y in nhds (0 : Point n),
      (vanVleck g y) ^ ((1 : ℝ) / 2) = (Matrix.det (g y)) ^ (-(1 : ℝ) / 4) := by
    filter_upwards [hpos] with y hy
    rw [vanVleck, Real.inv_rpow (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul (le_of_lt hy),
        show (-(1 : ℝ) / 4) = -((1 : ℝ) / 2 * (1 / 2)) from by ring,
        Real.rpow_neg (le_of_lt hy)]
  rw [laplaceBeltrami_congr_nhds g gi (fun y => (vanVleck g y) ^ ((1 : ℝ) / 2))
        (fun y => (Matrix.det (g y)) ^ (-(1 : ℝ) / 4)) (0 : Point n) hev]
  exact laplaceBeltrami_detpow_diag g gi Ric hg hg0 hgi hΓ hdg0 htr

/-! ### #1f — the payoff: `transportCoeff (vanVleck DeWitt source) 1 (0) = R/6`, DERIVED. -/

/-- ★ **THE DERIVED PARAMETRIX DIAGONAL `u₁(0) = R/6`.**  For the concrete van-Vleck DeWitt source
    `T = transportOp (vanVleck g) g gi`, the assembled transport coefficient `u₁ = transportCoeff T 1`
    at the centre is the scalar curvature over `6`:
      `transportCoeff (transportOp (vanVleck g) g gi) 1 (0) = (∑ᵢ Ric_{ii}) / 6` .
    Wiring `transportCoeff_one_diag` (diagonal recursion collapse, `u₀ ≡ 1`) to
    `transportSource_diag_eq_scalarCurv` (the van-Vleck leading value).  This turns the labelled input
    `hu1` of `ParametrixFunction.heatParametrixFn_diagonal_a1` into a THEOREM — the parametrix diagonal
    `a₁` is now DERIVED `R/6`, not carried, for the concrete van-Vleck coefficients.
    `hsrc` (transport-source smoothness) and `htr` (RNC metric-Hessian trace) are genuine, load-bearing. -/
theorem transportCoeff_vanVleck_one_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (Ric : Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤ (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0))) :
    transportCoeff (transportOp (vanVleck g) g gi) 1 (0 : Point n) = (∑ i, Ric i i) / 6 := by
  rw [transportCoeff_one_diag (transportOp (vanVleck g) g gi) hsrc, transportCoeff_zero]
  exact transportSource_diag_eq_scalarCurv g gi Ric hg hg0 hgi hΓ hdg0 htr

/-- ★ **THE DISCHARGED PARAMETRIX DIAGONAL EXPANSION.**  The concrete van-Vleck parametrix diagonal
    expansion of `ParametrixFunction.heatParametrixFn_diagonal_a1`, with its labelled `u₁(0)=R/6` input
    now SUPPLIED by `transportCoeff_vanVleck_one_diag` (`R := ∑ᵢ Ric_{ii}`, the scalar curvature):
      `H_N(t,0) = (4πt)^{−d/2} · (1 + ((∑Ric)/6)·t + Σ_{2≤k≤N} u_k(0) t^k)` .
    The `t¹` coefficient is DERIVED `R/6`, no longer carried.  Genuine hypotheses: RNC-centre data,
    the metric-Hessian trace `htr`, and the transport-source smoothness `hsrc`. -/
theorem heatParametrixFn_diagonal_a1_derived (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Ric : Fin n → Fin n → ℝ) (t : ℝ) (hN : 1 ≤ N)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤ (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0))) :
    heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n)
      = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
        * (1 + ((∑ i, Ric i i) / 6) * t
            + ∑ k ∈ Finset.Ico 2 (N + 1),
                transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ k) := by
  have hdet0 : Matrix.det (g 0) = 1 := by
    have hg0mat : g 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by funext i j; exact hg0 i j
    rw [hg0mat, Matrix.det_one]
  exact heatParametrixFn_diagonal_a1 N g (transportOp (vanVleck g) g gi) t (∑ i, Ric i i) hdet0 hN
    (transportCoeff_vanVleck_one_diag g gi Ric hg hg0 hgi hΓ hdg0 htr hsrc)

/-!
### CHECKPOINT — the OFF-DIAGONAL van-Vleck leading cancellation (NOT derived here).

What this file DERIVES is the DIAGONAL (`v = 0`) leading value: the surviving `t⁰` term of
`(∂_t − Δ_g)(G·Θ^{−1/2})` at the centre is `Θ^{−1/2}Δ_g(Θ^{1/2})(0) = R/6`.  This is exactly the point
where `R/6` enters, and it is now a theorem (`transportSource_diag_eq_scalarCurv`,
`transportCoeff_vanVleck_one_diag`).

The FULL off-diagonal leading cancellation — the statement that `Θ = vanVleck` solves the leading
transport ODE so that `(∂_t − Δ_g)(G·Θ^{−1/2})` has NO `O(1/t)` singular term for `v ≠ 0` — is NOT
proved here.  Its precise content and the exact blocking computation:

  • The off-diagonal residual is ALREADY decomposed unconditionally in
    `HeatResidualBound.parametrixResidual_offdiag_absorbed`: the cross-gradient of the curved Laplacian
    is rewritten as the RADIAL-TRANSPORT term `+(1/t)·G·(r∂_r P)` (piece (II)), leaving two flagged
    residues — (I) the flat-Gaussian curvature term `(∂_t − Δ_g)G` off-diagonal, and (IV) the
    metric-deviation cross-gradient `Σᵢⱼ (gⁱʲ − δⁱʲ)(∂ᵢG)(∂ⱼP)`.
  • The van-Vleck LEADING cancellation is the `k=0` order of this: `Θ^{−1/2}` must satisfy
      `(r∂_r) Θ^{−1/2} + (½ (r∂_r) log det g̃) · Θ^{−1/2} = 0`
    equivalently `Θ^{−1/2} = (det g̃)^{+1/4}·(‖v‖-Jacobian factor)`, so that the `O(1/t)` coefficient of
    `(∂_t − Δ_g)(G·Θ^{−1/2})` vanishes for ALL `v`.

  THE EXACT BLOCKING IDENTITY (the checkpoint): the radial logarithmic-derivative identity
      `(r∂_r) log √(det g̃) (v)  =  −2·(Δ_flat r²/4 − d/2)`   [the Jacobi/van-Vleck ODE]
  connecting the Euler derivative of `log det g̃` to the exponential-map Jacobian.  It requires the
  geodesic-radial structure of `det g̃` along rays (`∂_r log det g̃`), i.e. the exponential-map /
  Jacobi-field machinery ABSENT from Mathlib (the shared Riemannian-heat-kernel gap recorded across the
  J-series and in `docs/qg_roadmap/HEAT_KERNEL_GAP_PLAN.md`).  Only the RADIAL-DERIVATIVE-of-`det g̃`
  identity blocks the off-diagonal `O(1/t)` cancellation; the diagonal value (`R/6`) — where that radial
  term contributes `0` (`radialDeriv_zero`) — is fully derived above.

No axioms, no `sorry`.
-/

end QIQTH.VanVleckCancellation
