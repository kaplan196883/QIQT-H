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

    • (D1, J4-113) THE WITNESS GAUSSIAN DOMINATION, CONDITIONAL FORM.  For the gated order-1 van-Vleck
      witness `H_G`, the pointwise bound `|H_G τ p q| ≤ (A₀+A₁τ)·√(3/2)ⁿ·gaussDdim((3/2)τ)(p−q)`
      (`τ > 0`), delivered CONDITIONALLY on a `GateSqControl` certificate (the near-isometry
      square-comparison `rncRadialSq (p−q) ≤ (3/2)·rncRadialSq (W_q p)` on the gate — exactly what the
      chart transfer `gaussDdim_le_gaussDdim_chart` consumes).  Decomposition:
        • `exists_cutoff_foldedCoeff_bound` — the compact-support amplitude sup (EVT on `closedBall 0 b`,
          off-ball via `radialCutoff_eq_zero`): `∃ A ≥ 0, ∀ v, |radialCutoff a b v · w_k v| ≤ A`;
        • `globalWitnessN1_absDominated_of_sqControl` — the UNGATED pointwise estimate, from the two
          amplitude sups + the square-comparison via `gaussDdim_le_gaussDdim_chart (c=1,d=3/2)`;
        • `gatedWitnessN1_D1_of_gateSqControl` — the GATED lift (off-gate `= 0`; on-gate the ungated
          estimate) and its `∃ A₀ A₁` packaging `exists_D1_constants_of_gateSqControl`;
        • `gateSqControl_of_flowBall` — the geometry lemma producing `GateSqControl` for the concrete
          flow-ball gate `S q = φ_q '' ball 0 c` from the chart-inverse property + the `hdisp`
          near-isometry budget (`uniformFlowExp_hdisp_ball`, J4-96).

  ⚠ HONEST SCOPE (firewall).  D1 above is CONDITIONAL on `GateSqControl` (a gate-geometry certificate).
  The MERGE with the opaque `gatedWitnessN1_hEboundW_le_vanVleck_final` capstone (exposing its `S` so a
  single `∃ a b … S` carries `hEboundW_le ∧ hDH ∧ D1` together) is NOT done here — it needs the hE chain
  strengthened to also return the `GateSqControl` certificate; the conditional theorem is immediately
  reusable once that `S` is exposed (per the standard opaque-∃ non-recoverability).  Also NOT attempted:
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
open QIQTH.GaussianWidthTolerant QIQTH.RNCDecay QIQTH.ResidueBound
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

/-! ### D1. The witness Gaussian domination `|H_G| ≤ C_H·gaussDdim`, CONDITIONAL on `GateSqControl`. -/

/-- **`GateSqControl` — the gate square-comparison certificate.**  The single geometric fact the D1
    chart transfer needs from the gate: on the gate (`q ∈ K`, `p ∈ S q`), the ambient displacement
    `p − q` is controlled by the chart-variable `W q p` with the near-isometry margin
    `rncRadialSq (p − q) ≤ (3/2)·rncRadialSq (W q p)`.  This abstracts the near-isometry width budget
    away from the concrete flow-ball gate; `gateSqControl_of_flowBall` discharges it for
    `S q = φ_q '' ball 0 c`. -/
def GateSqControl (K : Set (Point n)) (S : Point n → Set (Point n))
    (W : Point n → Point n → Point n) : Prop :=
  ∀ q, q ∈ K → ∀ p, p ∈ S q → rncRadialSq (p - q) ≤ (3 / 2 : ℝ) * rncRadialSq (W q p)

/-- **D1a — the compact-support amplitude sup.**  The cutoff-folded coefficient
    `v ↦ radialCutoff a b v · foldedCoeff Θ u k v` is continuous (product of the smooth cutoff and the
    `C∞` folded coefficient) and supported in `closedBall 0 b` (the cutoff vanishes for
    `b² ≤ rncRadialSq v`, via `radialCutoff_eq_zero`), hence globally bounded by its EVT sup on the
    compact ball (`IsCompact.exists_bound_of_continuousOn`).  Genuine hypotheses `0 < a < b` (for the
    cutoff geometry) and the folded smoothness `hwk` (for continuity). -/
theorem exists_cutoff_foldedCoeff_bound (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (k : ℕ)
    (ha : 0 < a) (hab : a < b)
    (hwk : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ v : Point n, |radialCutoff a b v * foldedCoeff Θ u k v| ≤ A := by
  have hb0 : 0 < b := lt_trans ha hab
  have hcont : Continuous (fun v : Point n => radialCutoff a b v * foldedCoeff Θ u k v) :=
    (radialCutoff_contDiff a b).continuous.mul hwk.continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Point n) b).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun v => ?_⟩
  by_cases hv : v ∈ Metric.closedBall (0 : Point n) b
  · have h := hC v hv
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · rw [mem_closedBall_zero_iff, not_le] at hv
    have hb2 : b ^ 2 ≤ rncRadialSq v := by
      have hnr : ‖v‖ ≤ rncRadial v := norm_le_rncRadial v
      have hlt : b < rncRadial v := lt_of_lt_of_le hv hnr
      rw [← rncRadial_sq v]
      nlinarith [hlt, hb0.le]
    rw [radialCutoff_eq_zero ha hab hb2, zero_mul, abs_zero]
    exact le_max_right _ _

/-- **D1b — the UNGATED pointwise witness domination.**  For `τ > 0`, with the two amplitude sups
    `A₀`, `A₁` (`|radialCutoff·w_k (W q p)| ≤ A_k`) and the gate square-comparison `hsq`, the order-1
    global-cutoff witness is Gaussian-dominated at the ambient displacement width:
        `|globalCutoffParametrixWitnessN 1 Θ u a b W τ p q|
            ≤ (A₀ + A₁·τ)·√(3/2)ⁿ·gaussDdim((3/2)·τ)(p − q)`.
    Folds the witness (`heatParametrix_folded`), bounds `|Φ₀ + τ·Φ₁| ≤ A₀ + A₁τ`, and transfers the
    chart-variable width to `(p − q)` via `gaussDdim_le_gaussDdim_chart` (`c = 1`, `d = 3/2`, whose
    width budget is exactly `hsq`). -/
theorem globalWitnessN1_absDominated_of_sqControl (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (W : Point n → Point n → Point n) (τ : ℝ) (p q : Point n) (hτ : 0 < τ)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hbnd0 : |radialCutoff a b (W q p) * foldedCoeff Θ u 0 (W q p)| ≤ A₀)
    (hbnd1 : |radialCutoff a b (W q p) * foldedCoeff Θ u 1 (W q p)| ≤ A₁)
    (hsq : rncRadialSq (p - q) ≤ (3 / 2 : ℝ) * rncRadialSq (W q p)) :
    |globalCutoffParametrixWitnessN 1 Θ u a b W τ p q|
      ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  have hval : globalCutoffParametrixWitnessN 1 Θ u a b W τ p q
      = gaussDdim τ (W q p) * (radialCutoff a b (W q p) * foldedCoeff Θ u 0 (W q p)
          + radialCutoff a b (W q p) * foldedCoeff Θ u 1 (W q p) * τ) := by
    simp only [globalCutoffParametrixWitnessN, heatParametrix_folded, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, pow_zero, pow_one, mul_one]
    ring
  rw [hval]
  have hG0 : (0 : ℝ) ≤ gaussDdim τ (W q p) := gaussDdim_nonneg _ _
  have hAτ : (0 : ℝ) ≤ A₀ + A₁ * τ := add_nonneg hA₀ (mul_nonneg hA₁ hτ.le)
  have hstep1 : |gaussDdim τ (W q p) * (radialCutoff a b (W q p) * foldedCoeff Θ u 0 (W q p)
          + radialCutoff a b (W q p) * foldedCoeff Θ u 1 (W q p) * τ)|
      ≤ gaussDdim τ (W q p) * (A₀ + A₁ * τ) := by
    rw [abs_mul, abs_of_nonneg hG0]
    apply mul_le_mul_of_nonneg_left _ hG0
    calc |radialCutoff a b (W q p) * foldedCoeff Θ u 0 (W q p)
            + radialCutoff a b (W q p) * foldedCoeff Θ u 1 (W q p) * τ|
        ≤ |radialCutoff a b (W q p) * foldedCoeff Θ u 0 (W q p)|
            + |radialCutoff a b (W q p) * foldedCoeff Θ u 1 (W q p) * τ| := abs_add_le _ _
      _ = |radialCutoff a b (W q p) * foldedCoeff Θ u 0 (W q p)|
            + |radialCutoff a b (W q p) * foldedCoeff Θ u 1 (W q p)| * τ := by
            rw [abs_mul (radialCutoff a b (W q p) * foldedCoeff Θ u 1 (W q p)) τ, abs_of_pos hτ]
      _ ≤ A₀ + A₁ * τ := add_le_add hbnd0 (mul_le_mul_of_nonneg_right hbnd1 hτ.le)
  have hchart := gaussDdim_le_gaussDdim_chart (c := (1 : ℝ)) (d := (3 / 2 : ℝ)) one_pos
    (by norm_num) hτ (v := W q p) (w := p - q) (by rw [one_mul]; exact hsq)
  rw [one_mul, show ((3 : ℝ) / 2 / 1) = 3 / 2 from by norm_num] at hchart
  calc |gaussDdim τ (W q p) * (radialCutoff a b (W q p) * foldedCoeff Θ u 0 (W q p)
            + radialCutoff a b (W q p) * foldedCoeff Θ u 1 (W q p) * τ)|
      ≤ gaussDdim τ (W q p) * (A₀ + A₁ * τ) := hstep1
    _ ≤ (Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) * (A₀ + A₁ * τ) :=
        mul_le_mul_of_nonneg_right hchart hAτ
    _ = (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by ring

/-- **D1c — the GATED witness domination, from a `GateSqControl` certificate.**  Lifts D1b through the
    hard gate: off-gate (`q ∉ K` or `p ∉ S q`) the gated kernel vanishes and the RHS is nonnegative;
    on-gate the square-comparison `hgate` feeds `globalWitnessN1_absDominated_of_sqControl`.  The
    amplitude bounds are the GLOBAL sups (`∀ v`) from `exists_cutoff_foldedCoeff_bound`. -/
theorem gatedWitnessN1_D1_of_gateSqControl (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (W : Point n → Point n → Point n) (K : Set (Point n)) (S : Point n → Set (Point n))
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hb0 : ∀ v : Point n, |radialCutoff a b v * foldedCoeff Θ u 0 v| ≤ A₀)
    (hb1 : ∀ v : Point n, |radialCutoff a b v * foldedCoeff Θ u 1 v| ≤ A₁)
    (hgate : GateSqControl K S W) :
    ∀ (τ : ℝ) (p q : Point n), 0 < τ →
      |gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b W) τ p q|
        ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  intro τ p q hτ
  have hRHS : (0 : ℝ) ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) :=
    mul_nonneg (mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hτ.le))
      (pow_nonneg (Real.sqrt_nonneg _) n)) (gaussDdim_nonneg _ _)
  by_cases hq : q ∈ K
  · by_cases hp : p ∈ S q
    · rw [gatedKernel_apply_of_mem K S _ τ hq hp]
      exact globalWitnessN1_absDominated_of_sqControl Θ u a b W τ p q hτ A₀ A₁ hA₀ hA₁
        (hb0 _) (hb1 _) (hgate q hq p hp)
    · rw [gatedKernel_apply_of_notMem K S _ τ p q (Or.inr hp), abs_zero]; exact hRHS
  · rw [gatedKernel_apply_of_notMem K S _ τ p q (Or.inl hq), abs_zero]; exact hRHS

/-- **D1d — the `∃ A₀ A₁` packaging.**  Combines the two amplitude sups
    (`exists_cutoff_foldedCoeff_bound` at `k = 0, 1`) with the gated lift `gatedWitnessN1_D1_of_gateSqControl`
    into the affine-domination existential, given a `GateSqControl` certificate for `(K, S, W)`. -/
theorem exists_D1_constants_of_gateSqControl (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (W : Point n → Point n → Point n) (K : Set (Point n)) (S : Point n → Set (Point n))
    (ha : 0 < a) (hab : a < b)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hgate : GateSqControl K S W) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∀ (τ : ℝ) (p q : Point n), 0 < τ →
      |gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b W) τ p q|
        ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  obtain ⟨A₀, hA₀, hb0⟩ := exists_cutoff_foldedCoeff_bound Θ u a b 0 ha hab (hw 0)
  obtain ⟨A₁, hA₁, hb1⟩ := exists_cutoff_foldedCoeff_bound Θ u a b 1 ha hab (hw 1)
  exact ⟨A₀, A₁, hA₀, hA₁,
    gatedWitnessN1_D1_of_gateSqControl Θ u a b W K S A₀ A₁ hA₀ hA₁ hb0 hb1 hgate⟩

/-- **D1e — the geometry lemma: `GateSqControl` for the concrete flow-ball gate.**  For the flow-ball
    gate `S q = φ_q '' ball 0 c` (with `φ` the flow and `W` its inverse chart), the square-comparison
    holds from the chart-inverse property `hinv` (`W_q (φ_q v) = v` on the ball) and the near-isometry
    width budget `hdisp` (`(3/2)·rncRadialSq (φ_q v − q) ≤ 2·rncRadialSq v` for `‖v‖ < r₁`, e.g.
    `uniformFlowExp_hdisp_ball`), given the radius nesting `c ≤ r₁`.  Fully abstract in `φ`, `W` — no
    dependence on the concrete `uniformFlowExp`; instantiate with `φ = uniformFlowExp …`,
    `W = uniformInverseChart …`. -/
theorem gateSqControl_of_flowBall (K : Set (Point n)) (W φ : Point n → Point n → Point n) (c r₁ : ℝ)
    (hcr : c ≤ r₁)
    (hinv : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < c → W q (φ q v) = v)
    (hdisp : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₁ →
      (3 / 2 : ℝ) * rncRadialSq (φ q v - q) ≤ 2 * rncRadialSq v) :
    GateSqControl K (fun q => φ q '' Metric.ball 0 c) W := by
  intro q hq p hp
  obtain ⟨v, hvmem, hvp⟩ := hp
  rw [mem_ball_zero_iff] at hvmem
  rw [← hvp, hinv q hq v hvmem]
  have hd := hdisp q hq v (lt_of_lt_of_le hvmem hcr)
  nlinarith [hd, rncRadialSq_nonneg v, rncRadialSq_nonneg (φ q v - q)]

/-! ### Campaign map — the remaining hDuhamel/Levi bricks (D1, D2, D5), NOT attempted here.

    ▸ D1 (pointwise Gaussian domination of `H_G`).  LANDED CONDITIONALLY above (J4-113):
      `gatedWitnessN1_D1_of_gateSqControl` / `exists_D1_constants_of_gateSqControl` give
      `|H_G τ p q| ≤ (A₀+A₁τ)·√(3/2)ⁿ·gaussDdim((3/2)τ)(p−q)` given a `GateSqControl` certificate,
      discharged for the flow-ball gate by `gateSqControl_of_flowBall` (from the chart inverse + the
      `hdisp` near-isometry budget).  REMAINING: merge the certificate into the opaque hE capstone so
      one `∃ … S` carries `hEboundW_le ∧ hDH ∧ D1` (needs the hE chain to expose its `S`).

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
