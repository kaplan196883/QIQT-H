/-
  ConcreteDominations — J4-112: the CONCRETE regularity/domination bricks for the space-time Duhamel
  convolution capstone (hDuhamel campaign step 2), plus the LOAD-BEARING `⊤`→`C²` capstone-shape fix.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## The D4 verdict (load-bearing, decisive): the capstone's `hCH`/`hCConv` `⊤` requirement is
     OVERKILL — `ContDiffAt ℝ 2` (`C²`) suffices, and the concrete `H_G` chart is only `C²`.

  The restricted `a₁ = R/6` capstone `trueKernel_diagonal_a1_eq_R6_residual_restricted`
  (`RestrictedEboundW.lean`) carries
      • `hCH   : ContDiff ℝ ⊤ (fun p => H t p 0)`,
      • `hCConv : ContDiff ℝ ⊤ (fun p => heatConv H (leviSeries …) t p 0)`.
  These flow to EXACTLY ONE consumer: `TrueHeatKernel.trueHeatKernel_heat_eqn(_levi)` →
  `TrueHeatKernel.heatOp_add` → `LaplaceBeltrami.laplaceBeltrami_add`, whose `ContDiff ℝ ⊤` is used
  ONLY through `PdiffAt_of_contDiff` (needs `C¹`) and `PdiffAt_pd` (needs `C²`) — i.e. at most TWO
  spatial derivatives.  Since the gated van-Vleck witness `H_G` is only `C²` in the spatial slot (the
  inverse chart `uniformInverseChart` is `ContDiffOn ℝ 2`, NOT `⊤`), the `⊤` slot is UNSATISFIABLE
  for `H_G`; a `ContDiffAt ℝ 2` restatement is FORCED and SUFFICIENT (mirrors the J4-104 pattern and
  the existing `LaplaceBeltramiFiniteReg.laplaceBeltrami_mul_C2`).

  WHAT LANDS HERE.
    • (D4 engine) `laplaceBeltrami_add_C2` (the `C²` Leibniz-additivity), `heatOp_add_C2`,
      and the two weakened heat-equation capstones `trueHeatKernel_heat_eqn_C2` /
      `trueHeatKernel_heat_eqn_levi_C2` — the `⊤`→`ContDiffAt ℝ 2` ports of the `TrueHeatKernel`
      engine, and the fully-weakened restricted `a₁ = R/6` capstone
      `trueKernel_diagonal_a1_eq_R6_residual_restricted_C2`.
    • (D3) `heatParametrixFn_one_diag_differentiableAt` — the diagonal `t`-differentiability of the
      order-1 parametrix `u ↦ H₁(u,0)` for `t > 0` (explicit `(√(4πu))⁻ⁿ·(a₀+a₁u)` form), and its
      gated composition `gatedWitnessN1_hDH` discharging the capstone's `hDH` for the concrete
      van-Vleck witness `H_G` via the diag-eval `gatedWitnessN1_diag_eval_vanVleck`.

  ⚠ HONEST SCOPE (firewall).  NOT attempted here (the remaining hDuhamel/Levi bricks, mapped in the
  closing comment):
    • (D1) the pointwise Gaussian domination `|H_G τ p q| ≤ C_H·gaussDdim(c_H·τ)(p−q)` — needs the
      near-isometry CHART TRANSFER (J4-96, `NearIsometryBudget`) converting the chart-variable width
      `gaussDdim τ (W_q p)` to the `(p−q)` width, plus a compact-support amplitude sup bound;
    • (D2) the Levi-series domination `|leviSeries (heatOp g gi H_G) τ p q| ≤ C_L(T)·baseKernelW …`
      on `(0,T]` — the width-2 engine sum (`leviSeries_summableW_le` / `iterConvW_bound_le`);
    • (D5) the `hDConv` two-term diagonal Leibniz assembly (needs the ε→0 delta-family removal).
  NOT unconditional `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.OrderOneTower
import QIQTH.LaplaceBeltramiFiniteReg

open MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.ParametrixFunction QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.RadialDistance QIQTH.VanVleckCancellation
open QIQTH.GaussianWidthTolerant
open scoped BigOperators Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### D4a. The `C²` Laplace–Beltrami additivity — the `⊤`→`ContDiffAt ℝ 2` port. -/

/-- **`laplaceBeltrami_add_C2` — the `ContDiffAt ℝ 2` additivity of `Δ_g`.**  The finite-regularity
    analogue of `LaplaceBeltrami.laplaceBeltrami_add`: `Δ_g(f+h)(x) = Δ_g f(x) + Δ_g h(x)` needs only
    `C²` at the single point `x` (all first/second partials via `PdiffAt_of_contDiffAt` /
    `PdiffAt_pd_of_contDiffAt`), not global `ContDiff ℝ ⊤`.  Mirrors the `pd_pd_mul_C2` germ skeleton:
    the first partial of the sum agrees with the sum of first partials on a `nhds x` germ (where both
    fields are differentiable), and `∂ᵢ` respects the germ (`pd_congr_nhds`).  As in the `C^∞`
    version, the metric / Christoffel data enter only as VALUES at `x`, so NO metric-regularity
    hypothesis is needed. -/
theorem laplaceBeltrami_add_C2 (g gi : Point n → Fin n → Fin n → ℝ) (f h : Point n → ℝ) (x : Point n)
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) :
    laplaceBeltrami g gi (fun y => f y + h y) x
      = laplaceBeltrami g gi f x + laplaceBeltrami g gi h x := by
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by norm_num)
  have hh1 : ContDiffAt ℝ 1 h x := hh.of_le (by norm_num)
  simp only [laplaceBeltrami]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- first partial of the sum agrees with the sum of first partials on a germ at `x`
  have hstep : (fun y => pd (fun z => f z + h z) j y)
      =ᶠ[nhds x] (fun y => pd f j y + pd h j y) := by
    have hf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
      have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 1 f y := hf1.eventually (by norm_num)
      filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
    have hh_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ h y := by
      have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 1 h y := hh1.eventually (by norm_num)
      filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
    filter_upwards [hf_ev, hh_ev] with y hfy hhy
    exact pd_add f h j y (pdiffAt_of_differentiableAt f j y hfy)
      (pdiffAt_of_differentiableAt h j y hhy)
  rw [pd_congr_nhds i x hstep,
      pd_add (fun y => pd f j y) (fun y => pd h j y) i x
        (PdiffAt_pd_of_contDiffAt f j i x hf) (PdiffAt_pd_of_contDiffAt h j i x hh)]
  have hΓ : (∑ k, christoffel g gi k i j x * pd (fun z => f z + h z) k x)
      = (∑ k, christoffel g gi k i j x * pd f k x)
        + (∑ k, christoffel g gi k i j x * pd h k x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_add f h k x (PdiffAt_of_contDiffAt f k x hf1) (PdiffAt_of_contDiffAt h k x hh1)]; ring
  rw [hΓ]; ring

/-! ### D4b. The `C²` heat-operator additivity. -/

/-- **`heatOp_add_C2` — the `ContDiffAt ℝ 2` linearity of the heat operator.**  The `⊤`→`C²` port of
    `TrueHeatKernel.heatOp_add`: the spatial-smoothness carries are weakened from `ContDiff ℝ ⊤` to
    `ContDiffAt ℝ 2` at the base point `x` (all that `laplaceBeltrami_add_C2` needs).  `deriv_add` on
    the `∂_t` piece is unchanged. -/
theorem heatOp_add_C2 (g gi : Point n → Fin n → Fin n → ℝ) (K₁ K₂ : ℝ → Point n → Point n → ℝ)
    (t : ℝ) (x y : Point n)
    (hD₁ : DifferentiableAt ℝ (fun u => K₁ u x y) t)
    (hD₂ : DifferentiableAt ℝ (fun u => K₂ u x y) t)
    (hC₁ : ContDiffAt ℝ 2 (fun p => K₁ t p y) x)
    (hC₂ : ContDiffAt ℝ 2 (fun p => K₂ t p y) x) :
    heatOp g gi (fun τ p q => K₁ τ p q + K₂ τ p q) t x y
      = heatOp g gi K₁ t x y + heatOp g gi K₂ t x y := by
  simp only [heatOp]
  have hderiv : deriv (fun u => K₁ u x y + K₂ u x y) t
      = deriv (fun u => K₁ u x y) t + deriv (fun u => K₂ u x y) t := deriv_add hD₁ hD₂
  have hlap : laplaceBeltrami g gi (fun p => K₁ t p y + K₂ t p y) x
      = laplaceBeltrami g gi (fun p => K₁ t p y) x
        + laplaceBeltrami g gi (fun p => K₂ t p y) x :=
    laplaceBeltrami_add_C2 g gi (fun p => K₁ t p y) (fun p => K₂ t p y) x hC₁ hC₂
  rw [hderiv, hlap]; ring

/-! ### D4c. The `C²` heat-equation capstones (`⊤`→`ContDiffAt ℝ 2`). -/

/-- **`trueHeatKernel_heat_eqn_C2` — the `ContDiffAt ℝ 2` port of `trueHeatKernel_heat_eqn`.**
    Identical to `TrueHeatKernel.trueHeatKernel_heat_eqn` EXCEPT `hCH`/`hCConv` are weakened from
    `ContDiff ℝ ⊤` to `ContDiffAt ℝ 2` at `x` (the D4 verdict: `heatOp_add`'s only use of the spatial
    smoothness is two derivatives).  Proof identical, calling `heatOp_add_C2`. -/
theorem trueHeatKernel_heat_eqn_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (H E F : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hE : heatOp g gi H t x y = E t x y)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H F u p q) t x y
        = F t x y + heatConv E F t x y)
    (hVolterra : F t x y = - E t x y - heatConv E F t x y)
    (hDH : DifferentiableAt ℝ (fun u => H u x y) t)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H F u x y) t)
    (hCH : ContDiffAt ℝ 2 (fun p => H t p y) x)
    (hCConv : ContDiffAt ℝ 2 (fun p => heatConv H F t p y) x) :
    heatOp g gi (trueHeatKernel H F) t x y = 0 := by
  have hsplit : heatOp g gi (trueHeatKernel H F) t x y
      = heatOp g gi H t x y + heatOp g gi (fun u p q => heatConv H F u p q) t x y := by
    have := heatOp_add_C2 g gi H (fun u p q => heatConv H F u p q) t x y hDH hDConv hCH hCConv
    exact this
  rw [hsplit, hE, hDuhamel, hVolterra]; ring

/-- **`trueHeatKernel_heat_eqn_levi_C2` — the `ContDiffAt ℝ 2` port of `trueHeatKernel_heat_eqn_levi`.**
    The signed-Levi capstone with the spatial smoothness weakened to `ContDiffAt ℝ 2`.  Plugs
    `TrueHeatKernel.leviSeries_volterra` (unchanged) into `trueHeatKernel_heat_eqn_C2`. -/
theorem trueHeatKernel_heat_eqn_levi_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (H E : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hE : heatOp g gi H t x y = E t x y)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries E) u p q) t x y
        = leviSeries E t x y + heatConv E (leviSeries E) t x y)
    (hSum : Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t x y))
    (hInter : heatConv E (leviSeries E) t x y
        = ∑' k : ℕ, heatConv E (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q) t x y)
    (hDH : DifferentiableAt ℝ (fun u => H u x y) t)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries E) u x y) t)
    (hCH : ContDiffAt ℝ 2 (fun p => H t p y) x)
    (hCConv : ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries E) t p y) x) :
    heatOp g gi (trueHeatKernel H (leviSeries E)) t x y = 0 :=
  trueHeatKernel_heat_eqn_C2 g gi H E (leviSeries E) t x y hE hDuhamel
    (leviSeries_volterra E t x y hSum hInter) hDH hDConv hCH hCConv

/-! ### D4d. The fully-weakened restricted `a₁ = R/6` capstone (the D4 payoff). -/

/-- **★ `trueKernel_diagonal_a1_eq_R6_residual_restricted_C2` — the `(0,t]`-restricted `a₁ = R/6`
    capstone with `hCH`/`hCConv` WEAKENED to `ContDiffAt ℝ 2`.**  Verbatim
    `trueKernel_diagonal_a1_eq_R6_residual_restricted` EXCEPT the two spatial-smoothness carries are
    `ContDiffAt ℝ 2` (D4 verdict), so the concrete `C²`-only van-Vleck witness `H_G` can actually
    satisfy them.  All other carries (`hEboundW_le`, `hInt`, `hDuhamel`, `hInter`, `hHdiag`, `hDH`,
    `hDConv`, RNC data) are unchanged.  Uses the restricted Neumann convergence
    `neumann_summable_alpha0_width2_le` and calls `trueHeatKernel_heat_eqn_levi_C2`.
    STILL CONDITIONAL; NOT unconditional `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_restricted_C2
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    (H : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hHdiag : H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi H τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi H) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
        = leviSeries (heatOp g gi H) t 0 0
          + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)
    (hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi H)
            (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0)
    (hDH : DifferentiableAt ℝ (fun u => H u 0 0) t)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t)
    (hCH : ContDiffAt ℝ 2 (fun p => H t p 0) (0 : Point n))
    (hCConv : ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (0 : Point n)) :
    heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  have hpref : (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n ≠ 0 :=
    pow_ne_zero n (ne_of_gt (QIQTH.GaussianConvolution.heatKernel1D_pos t 0 ht))
  have ht2 : (t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
  -- (A) THE TRUE KERNEL SOLVES THE HEAT EQUATION — via the `(0,t]`-RESTRICTED Neumann convergence.
  have hIterSum := neumann_summable_alpha0_width2_le (heatOp g gi H) C hC t
    hEboundW_le hInt t ht le_rfl (0 : Point n) (0 : Point n)
  have hSum : Summable
      (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) t (0 : Point n) (0 : Point n)) := by
    have habs : Summable
        (fun k : ℕ => |iterE (heatOp g gi H) (k + 1) t (0 : Point n) (0 : Point n)|) :=
      summable_abs_iff.mpr hIterSum
    refine Summable.of_norm_bounded habs (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    simp
  have hHeat : heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0 :=
    trueHeatKernel_heat_eqn_levi_C2 g gi H (heatOp g gi H) t 0 0 rfl hDuhamel hSum hInter
      hDH hDConv hCH hCConv
  -- (B) THE DIAGONAL `a₁ = R/6` EXPANSION (identical to the parent).
  have hParam := heatParametrixFn_diagonal_a1_derived N g gi Ric t hN hg hg0 hgi hΓ hdg0 htr hsrc
  have htail_eq : (∑ k ∈ Finset.Ico 2 (N + 1),
        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ k)
      = t ^ 2 * ∑ k ∈ Finset.Ico 2 (N + 1),
        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ (k - 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hpow : t ^ 2 * t ^ (k - 2) = t ^ k := by
      rw [← pow_add]; congr 1; omega
    rw [← hpow]; ring
  have hExp : trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
      = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
        * (1 + ((∑ i, Ric i i) / 6) * t
            + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                          * t ^ (k - 2))
                      + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                          / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
    rw [trueHeatKernel_apply, hHdiag, hParam, htail_eq]
    field_simp
    ring
  exact ⟨hHeat, hExp⟩

/-! ### D3. Diagonal `t`-differentiability of the order-1 parametrix (`hDH` concrete). -/

/-- **D3 — `heatParametrixFn_one_diag_differentiableAt`.**  For `t > 0`, the order-1 parametrix on the
    diagonal `u ↦ H₁(u, 0)` is differentiable at `t`.  On the diagonal it has the EXPLICIT closed form
        `H₁(u,0) = (√(4πu))⁻ⁿ · (vanVleck g 0)^{−1/2} · (a₀ + a₁·u)`,
    `a_k = transportCoeff T k 0` (via `heatParametrixFn_apply`, `gaussDdim_diagonal`,
    `heatKernel1D_zero`), a product of `(√(4πu))⁻ⁿ` (differentiable at `u = t` since `4πt > 0`, so the
    root is nonzero) and an affine polynomial.  Genuine hypothesis `0 < t` (the `√`-inverse is
    singular at `0`). -/
theorem heatParametrixFn_one_diag_differentiableAt (g : Point n → Fin n → Fin n → ℝ)
    (T : (Point n → ℝ) → (Point n → ℝ)) (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ (fun u => heatParametrixFn 1 g T u (0 : Point n)) t := by
  have hfun : (fun u => heatParametrixFn 1 g T u (0 : Point n))
      = fun u => ((Real.sqrt (4 * Real.pi * u))⁻¹) ^ n * (vanVleck g (0 : Point n)) ^ (-(1 : ℝ) / 2)
          * ∑ k ∈ Finset.range (1 + 1), transportCoeff T k (0 : Point n) * u ^ k := by
    funext u
    rw [heatParametrixFn_apply, gaussDdim_diagonal, heatKernel1D_zero]
  rw [hfun]
  have h4πt : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hne : (4 * Real.pi * t) ≠ 0 := ne_of_gt h4πt
  have hg4 : DifferentiableAt ℝ (fun u : ℝ => 4 * Real.pi * u) t := by fun_prop
  have hsqrt : DifferentiableAt ℝ (fun u : ℝ => Real.sqrt (4 * Real.pi * u)) t := hg4.sqrt hne
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h4πt)
  have hinv : DifferentiableAt ℝ (fun u : ℝ => (Real.sqrt (4 * Real.pi * u))⁻¹) t :=
    hsqrt.inv hsqrt_ne
  have hpow : DifferentiableAt ℝ (fun u : ℝ => ((Real.sqrt (4 * Real.pi * u))⁻¹) ^ n) t := hinv.pow n
  have hpoly : DifferentiableAt ℝ
      (fun u : ℝ => ∑ k ∈ Finset.range (1 + 1), transportCoeff T k (0 : Point n) * u ^ k) t := by
    fun_prop
  exact (hpow.mul_const _).mul hpoly

/-- **D3 payoff — `gatedWitnessN1_hDH`.**  The capstone's `hDH` for the CONCRETE gated van-Vleck
    order-1 witness `H_G`: `u ↦ H_G(u, 0, 0)` is differentiable at `t > 0`.  On the diagonal the gate
    collapses (`gatedWitnessN1_diag_eval_vanVleck`, valid `∀ u`) to `H₁(u, 0)`, whose diagonal
    differentiability is `heatParametrixFn_one_diag_differentiableAt`.  Genuine gate hypotheses
    (`0 < a < b`, `0 ∈ K`, `0 ∈ S 0`, `Vmap 0 0 = 0`, `0 < t`). -/
theorem gatedWitnessN1_hDH (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Vmap : Point n → Point n → Point n) (t : ℝ) (ht : 0 < t)
    (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0) (hV : Vmap 0 0 = 0) :
    DifferentiableAt ℝ
      (fun u => gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap) u 0 0) t := by
  have hcongr : (fun u => gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap) u 0 0)
      = fun u => heatParametrixFn 1 g (transportOp (vanVleck g) g gi) u (0 : Point n) := by
    funext u
    exact gatedWitnessN1_diag_eval_vanVleck g gi K S a b ha hab Vmap u hK0 hS0 hV
  rw [hcongr]
  exact heatParametrixFn_one_diag_differentiableAt g (transportOp (vanVleck g) g gi) t ht

/-! ### Campaign map — the remaining hDuhamel/Levi bricks (D1, D2, D5), NOT attempted here.

    ▸ D1 (pointwise Gaussian domination of `H_G`).  `|H_G τ p q| ≤ C_H·gaussDdim(c_H·τ)(p−q)`.
      On the gate `H_G = radialCutoff·(gaussDdim τ (W_q p))·amplitude`; the cutoff is `≤ 1` and the
      amplitude `(vanVleck)^{−1/2}·(w₀+τ·w₁)` is bounded on the compact chart-ball, giving the EASY
      chart-variable bound `|H_G τ p q| ≤ C(1+τ)·gaussDdim τ (W_q p)`.  The `(W_q p)`→`(p−q)` width
      conversion is the NEAR-ISOMETRY CHART TRANSFER (J4-96, `NearIsometryBudget` — `‖p−q‖ ≤
      √(4/3)·‖W p‖`, `‖W p‖ ≤ 2‖p−q‖` on the gate), producing `gaussDdim((3/2)τ)(p−q)` with margin.
      Off-gate `H_G = 0`.  Needs the chart-transfer machinery loaded.

    ▸ D2 (Levi-series domination).  `|leviSeries (heatOp g gi H_G) τ p q| ≤ C_L(T)·baseKernelW 2 0`
      on `(0,T]`, from the width-2 engine: term-bound via `iterConvW_bound_le`, summed against the
      model geometric/Γ-decay series `scaledIterKernelW_summable`.  `hEboundW_le` (the one-step input)
      is LANDED (`gatedWitnessN1_hEboundW_le_vanVleck_final`, `CoeffU1Fix.lean`).

    ▸ D5 (`hDConv` diagonal Leibniz).  The two-term derivative of `u ↦ heatConv H_G (leviSeries E)
      u 0 0` at `t`: FTC-upper (`heatConvFrozen_hasDerivAt_upper_of_dominated`, `HeatConvRegularity`)
      + ε-truncated under-integral Leibniz (`heatConv_hasDerivAt_underIntegral`) at the moving
      diagonal, with the ε→0 delta-family removal.  Needs D1/D2 as domination inputs.

    None of D1/D2/D5 is attempted here; each is a genuine, separately-labeled brick. -/

end QIQTH.HeatResidualBound
