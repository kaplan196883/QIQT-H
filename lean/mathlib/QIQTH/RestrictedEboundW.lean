/-
  RestrictedEboundW — the `(0,t]`-RESTRICTED width-2 residual-bound variant of the true-kernel
  diagonal Seeley–DeWitt `a₁ = R/6` chain (J4-104).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHY THIS FILE EXISTS (the J4-103 hEboundW-SHAPE FIX).

  The `N=1` gated witness's residual satisfies a MIXED-α bound
      `|E τ p q| ≤ C·(baseKernelW 2 0 + baseKernelW 2 1) τ p q`
  (an α=1 diagonal tail = an extra `τ`-power), which CANNOT satisfy the capstone's hardcoded
  `∀ τ, α = 0` shape `|E τ p q| ≤ C·baseKernelW 2 0 τ p q` (linear-`τ` tail is not `≤` a τ-free one
  for ALL τ).  But the Levi/Duhamel theory only ever evaluates the residual at times `τ ≤ t` (the
  Neumann series `E∗E∗…∗E` at time `t` integrates intermediate times over `(0,t)`-simplices).

  ── F1 CENSUS (decisive, verdict YES). ────────────────────────────────────────────────────────
  Inside `TrueKernelA1.trueKernel_diagonal_a1_eq_R6`, `hEboundW` and `hInt` are consumed in EXACTLY
  ONE place:
      `neumann_summable_alpha0_width2 E C hC hEboundW hInt t ht 0 0`
  producing `Summable (fun k => iterE E (k+1) t 0 0)` — a series at the FIXED capstone time `t`.
  Tracing the callees:
    • `neumann_summable_alpha0_width2` = `leviSeries_summableW … at κ=2, α=0`;
    • `leviSeries_summableW` feeds `hEboundW`/`hInt` into `iterConvW_bound … (k+1) t`;
    • `iterConvW_bound`'s succ step passes the one-step bound into `heatConv_le_of_abs_le_pos`,
      whose PROOF (`integral_mono_on_of_le_Ioo` over `Ioo 0 t`) only evaluates the bound at
      `τ = t−s` and `τ = s` for `s ∈ (0,t)` — i.e. **only at `τ ∈ (0,t)`**;
    • `hInt` is only ever invoked at the OUTER time of each convolution (`hInt m hm t ht x y`), and
      its five integral conjuncts at outer time `t` reference `E`/dominators only on `[0,t]`.
  ⟹ EVERY `hEboundW`/`hInt` evaluation in the whole capstone chain is at a time `≤ t`.  So the
  `∀ τ∈(0,t]`-restricted one-step bound is SUFFICIENT.  (Route (β) of the mission.)

  ── F2 (this file). ───────────────────────────────────────────────────────────────────────────
  The restricted chain `heatConv_le_of_abs_le_pos_le` → `iterConvW_bound_le` →
  `leviSeries_summableW_le` → `neumann_summable_alpha0_width2_le`, then the restricted capstone
  `trueKernel_diagonal_a1_eq_R6_residual_restricted`: IDENTICAL to
  `TrueKernelA1.trueKernel_diagonal_a1_eq_R6_residual` EXCEPT the C4c primitive `hEboundW` is
  WEAKENED to `hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t → |heatOp g gi H τ p q| ≤ C·baseKernelW 2 0 τ p q`
  (only on `(0,t]`).  `hInt` stays the FULL `IterConvIntegrableW` (the census shows it is only ever
  used at times `≤ t`, so the full family trivially covers the restricted need; keeping it full means
  the existing full producers feed it verbatim).

  ── F3 (this file, the route-β payload). ──────────────────────────────────────────────────────
  `mixedAlpha_to_alpha0_le` / `capstone_inputs_N1_shape`: ON `(0,t]`,
      `baseKernelW 2 1 τ p q = τ · baseKernelW 2 0 τ p q ≤ t · baseKernelW 2 0 τ p q`,
  so the MIXED-α restricted bound becomes a PURE α=0 restricted bound with constant `C·(1+t)` — this
  is EXACTLY the `hEboundW_le` the restricted capstone consumes.  This turns the achievable N=1
  residual SHAPE into the capstone-consumed shape.

  ⚠ HONEST SCOPE (binding, firewall).  This is STILL CONDITIONAL.  What is NOT touched:
    • the GLOBAL / off-diagonal reach of the N=1 witness (`residualN1_gaussianWide_ball` is a LOCAL
      spatial-ball bound at a SINGLE fixed `t`, base point `0`, in `gaussDdimWide`), and its
      `τ`-uniformization (single-`t` ⟹ `∀ τ≤t` with ONE constant and ONE radius) — that whole
      step (LOCAL→GLOBAL + single-`t`→`∀τ` + `gaussDdimWide`→`baseKernelW`) is the C4c wall and is
      NOT discharged here.  `capstone_inputs_N1_shape` TAKES the mixed-α `(0,t]`-restricted bound as
      a hypothesis; it does NOT derive it from the geometry.
  NOT unconditional `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.TrueKernelA1Reduced

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### 1. The `(0,t]`-restricted positive-time `heatConv` domination step. -/

/-- **The `(0,t]`-RESTRICTED positive-time `heatConv` domination step.**  Identical to
    `LeviSeries.heatConv_le_of_abs_le_pos` except the one-step bounds `hA`, `hB` are only demanded on
    `(0,t]` (`0 < τ → τ ≤ t`).  Sound because `heatConv` integrates over `s ∈ Ioo 0 t`, where the
    inner times `t−s` and `s` are both in `(0,t)` — so the bounds are only ever evaluated at `τ ≤ t`
    (indeed `< t`).  Proof mirrors the parent, supplying the extra `τ ≤ t` from `s ∈ Ioo 0 t`. -/
theorem heatConv_le_of_abs_le_pos_le (A B A' B' : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (ht : 0 < t)
    (hA : ∀ τ p q, 0 < τ → τ ≤ t → |A τ p q| ≤ A' τ p q)
    (hB : ∀ τ p q, 0 < τ → τ ≤ t → |B τ p q| ≤ B' τ p q)
    (hI1 : IntervalIntegrable (fun s => ‖∫ z, A (t - s) x z * B s z y‖) volume 0 t)
    (hI2 : IntervalIntegrable (fun s => ∫ z, |A (t - s) x z| * |B s z y|) volume 0 t)
    (hIf : ∀ s, Integrable (fun z => |A (t - s) x z| * |B s z y|))
    (hIg : ∀ s, Integrable (fun z => A' (t - s) x z * B' s z y))
    (hIsg : IntervalIntegrable (fun s => ∫ z, A' (t - s) x z * B' s z y) volume 0 t) :
    |heatConv A B t x y| ≤ heatConv A' B' t x y := by
  refine le_trans (heatConv_abs_le A B t x y ht.le hI1 hI2) ?_
  simp only [heatConv]
  refine intervalIntegral.integral_mono_on_of_le_Ioo ht.le hI2 hIsg (fun s hs => ?_)
  obtain ⟨hs0, hst⟩ := hs
  have hts : 0 < t - s := by linarith
  refine integral_mono (hIf s) (hIg s) (fun z => ?_)
  have hAz := hA (t - s) x z hts (by linarith)
  have hBz := hB s z y hs0 (by linarith)
  exact mul_le_mul hAz hBz (abs_nonneg _) (le_trans (abs_nonneg _) hAz)

/-! ### 2. The `(0,T]`-restricted iterated residual bound. -/

/-- **The `(0,T]`-RESTRICTED width-tolerant iterated residual bound.**  Mirror of
    `iterConvW_bound` with the one-step bound `hEbound` restricted to `(0,T]` and the conclusion to
    `t ≤ T`.  `hInt` stays the FULL `IterConvIntegrableW` (only ever used at the outer time `t ≤ T`).
    The induction goes through: at outer time `t ≤ T`, all inner evaluations are at `τ ≤ t ≤ T`, so
    the restricted bound and inductive hypothesis feed `heatConv_le_of_abs_le_pos_le`. -/
theorem iterConvW_bound_le (E : ℝ → Point n → Point n → ℝ) (κ α C T : ℝ)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * baseKernelW κ α τ p q)
    (hInt : IterConvIntegrableW E κ α C) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → t ≤ T → ∀ (x y : Point n),
      |iterE E k t x y| ≤ C ^ k * iterKernelW κ α k t x y := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro t ht htT x y
      rw [iterE_one, pow_one, iterKernelW_one]
      exact hEbound t x y ht htT
  | succ m hm ih =>
      intro t ht htT x y
      obtain ⟨hI1, hI2, hIf, hIg, hIsg⟩ := hInt m hm t ht x y
      rw [iterE_succ E hm, iterKernelW_succ κ α hm]
      simp only [heatConvK_apply]
      have hbound := heatConv_le_of_abs_le_pos_le E (iterE E m)
        (fun τ p q => C * baseKernelW κ α τ p q) (fun τ p q => C ^ m * iterKernelW κ α m τ p q)
        t x y ht
        (fun τ p q hτ hτt => hEbound τ p q hτ (le_trans hτt htT))
        (fun τ p q hτ hτt => ih τ hτ (le_trans hτt htT) p q)
        hI1 hI2 hIf hIg hIsg
      calc |heatConv E (iterE E m) t x y|
          ≤ heatConv (fun τ p q => C * baseKernelW κ α τ p q)
              (fun τ p q => C ^ m * iterKernelW κ α m τ p q) t x y := hbound
        _ = C ^ (m + 1) * heatConv (baseKernelW κ α) (iterKernelW κ α m) t x y := by
              rw [heatConv_smul_left C (baseKernelW κ α)
                    (fun τ p q => C ^ m * iterKernelW κ α m τ p q),
                  heatConv_smul_right (C ^ m) (baseKernelW κ α) (iterKernelW κ α m), pow_succ]
              ring

/-! ### 3. The `(0,T]`-restricted width-tolerant Neumann convergence. -/

/-- **The `(0,T]`-RESTRICTED width-tolerant Neumann convergence.**  Mirror of `leviSeries_summableW`
    with `hEbound` restricted to `(0,T]` and the evaluation time `t ≤ T`.  Comparison test against the
    (unchanged, width-independent) model series `scaledIterKernelW_summable`, term-dominated by the
    restricted `iterConvW_bound_le`. -/
theorem leviSeries_summableW_le (E : ℝ → Point n → Point n → ℝ) (κ α C T : ℝ)
    (hκ : 0 < κ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * baseKernelW κ α τ p q)
    (hInt : IterConvIntegrableW E κ α C) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (x y : Point n) :
    Summable (fun k : ℕ => iterE E (k + 1) t x y) := by
  refine Summable.of_norm_bounded (scaledIterKernelW_summable κ α t C hκ hα ht hC x y) (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact iterConvW_bound_le E κ α C T hEbound hInt (k + 1) (by omega) t ht htT x y

/-- **★ THE `(0,T]`-RESTRICTED REDUCTION (κ=2, α=0).**  Given the SINGLE C4c input restricted to
    `(0,T]`, `hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C·baseKernelW 2 0 τ p q`, `C ≥ 0`,
    and the carried per-step integrability, the residual Neumann series converges at every `t ≤ T`.
    Direct instantiation of `leviSeries_summableW_le`. -/
theorem neumann_summable_alpha0_width2_le (E : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (T : ℝ)
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW E 2 0 C) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (x y : Point n) :
    Summable (fun k : ℕ => iterE E (k + 1) t x y) :=
  leviSeries_summableW_le E 2 0 C T (by norm_num) le_rfl hC hEboundW_le hInt t ht htT x y

/-! ### 4. F3 — the route-β SHAPE bridge (mixed-α on `(0,T]` ⟹ pure α=0 on `(0,T]`). -/

/-- **The width-1 base kernel is `τ ·` the width-0 one.**  `baseKernelW κ 1 τ p q = τ · baseKernelW
    κ 0 τ p q` (from `Real.rpow_one`/`Real.rpow_zero`).  This is the exact identity that collapses the
    α=1 diagonal tail into a `τ`-multiple of the α=0 kernel. -/
theorem baseKernelW_one_eq_tau_mul (κ τ : ℝ) (p q : Point n) :
    baseKernelW κ (1 : ℝ) τ p q = τ * baseKernelW κ (0 : ℝ) τ p q := by
  simp only [baseKernelW, Real.rpow_one, Real.rpow_zero, one_mul]

/-- **★ F3 — THE ROUTE-β SHAPE BRIDGE.**  On `(0,T]`, a MIXED-α bound
        `|E τ p q| ≤ C·(baseKernelW 2 0 + baseKernelW 2 1) τ p q`
    is a PURE α=0 bound with constant `C·(1+T)`:
        `|E τ p q| ≤ (C·(1+T))·baseKernelW 2 0 τ p q`   (for `0 < τ ≤ T`).
    Because `baseKernelW 2 1 τ = τ·baseKernelW 2 0 τ` and `baseKernelW 2 0 ≥ 0`, `τ ≤ T`.  This is the
    decisive route-(β) fix: it turns the shape J4-103 established for the `N=1` residual into the
    `(0,t]`-restricted `hEboundW_le` the restricted capstone consumes. -/
theorem mixedAlpha_to_alpha0_le (E : ℝ → Point n → Point n → ℝ) (C T : ℝ) (hC : 0 ≤ C)
    (hmix : ∀ τ p q, 0 < τ → τ ≤ T →
      |E τ p q| ≤ C * (baseKernelW (2 : ℝ) (0 : ℝ) τ p q + baseKernelW (2 : ℝ) (1 : ℝ) τ p q)) :
    ∀ τ p q, 0 < τ → τ ≤ T →
      |E τ p q| ≤ (C * (1 + T)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  intro τ p q hτ hτT
  have hb0 : 0 ≤ baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    rw [baseKernelW_zero_apply]; exact QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have h1 : baseKernelW (2 : ℝ) (1 : ℝ) τ p q = τ * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
    baseKernelW_one_eq_tau_mul 2 τ p q
  calc |E τ p q|
      ≤ C * (baseKernelW (2 : ℝ) (0 : ℝ) τ p q + baseKernelW (2 : ℝ) (1 : ℝ) τ p q) :=
        hmix τ p q hτ hτT
    _ = C * (1 + τ) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by rw [h1]; ring
    _ ≤ (C * (1 + T)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
        apply mul_le_mul_of_nonneg_right _ hb0
        apply mul_le_mul_of_nonneg_left _ hC
        linarith

/-- **★ F3 PACKAGE — `capstone_inputs_N1_shape`.**  Specialization of `mixedAlpha_to_alpha0_le` to the
    ACTUAL residual `E := heatOp g gi H`, at `T := t`: GIVEN the mixed-α `(0,t]`-restricted bound on
    the residual (the shape J4-103 established the `N=1` gated witness satisfies), it produces EXACTLY
    the restricted capstone's `hEboundW_le` with constant `C·(1+t)`.

    ⚠ Firewall: this TAKES the mixed-α `(0,t]`-restricted bound as a hypothesis; the step from the
    LOCAL, single-`t`, base-point-`0`, `gaussDdimWide` witness `residualN1_gaussianWide_ball` to this
    GLOBAL `∀τ≤t` mixed bound (LOCAL→GLOBAL + single-`t`→`∀τ`-uniformization) is the C4c wall, NOT
    discharged here. -/
theorem capstone_inputs_N1_shape (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (C t : ℝ) (hC : 0 ≤ C)
    (hmix : ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi H τ p q|
        ≤ C * (baseKernelW (2 : ℝ) (0 : ℝ) τ p q + baseKernelW (2 : ℝ) (1 : ℝ) τ p q)) :
    ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi H τ p q| ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  mixedAlpha_to_alpha0_le (heatOp g gi H) C t hC hmix

/-! ### 5. ★ THE RESTRICTED CAPSTONE (F2). -/

/-- **★ THE `(0,t]`-RESTRICTED CONDITIONAL CAPSTONE — `hEboundW` WEAKENED to `(0,t]`.**  Identical to
    `TrueKernelA1.trueKernel_diagonal_a1_eq_R6_residual` EXCEPT the C4c primitive is weakened from the
    hardcoded `∀ τ, α=0` shape to the `(0,t]`-restricted one:
        `hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t → |heatOp g gi H τ p q| ≤ C·baseKernelW 2 0 τ p q`.
    (F1 census: the whole chain only evaluates the residual at times `≤ t`, so this suffices.)  The
    true kernel `K = H + H∗(leviSeries (heatOp g gi H))` solves the heat equation AND
        `K(t,0,0) = (4πt)^{−d/2} · (1 + (R/6)·t + t²·remainder)`,   `R = ∑ᵢ Ric_{ii}`.

    Remaining carries (all genuine, labeled): `hEboundW_le` (★ C4c wall, `(0,t]`-restricted on the
    actual residual), `hInt` (full `IterConvIntegrableW`), `hDuhamel`, `hInter`, `hHdiag`, RNC data.
    STILL CONDITIONAL; NOT unconditional `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_restricted
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
    -- ★ THE SINGLE C4c PRIMITIVE, `(0,t]`-RESTRICTED, on the ACTUAL residual `heatOp g gi H`:
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
    (hCH : ContDiff ℝ ⊤ (fun p => H t p 0))
    (hCConv : ContDiff ℝ ⊤ (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0)) :
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
    trueHeatKernel_heat_eqn_levi g gi H (heatOp g gi H) t 0 0 rfl hDuhamel hSum hInter
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

end QIQTH.HeatResidualBound
