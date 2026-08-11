/-
  FrozenK2 — J4-614: the k = 2 budget bridge, ROUTE (b) LANDED IN FULL — the `o(t)`-budget consumer
  variant of `corrHigher_bounded_of_slice` (the `√s`-tolerant slice budget, the `t^{3/2}` assembled
  rate, and the `o(t)`-sufficiency Tendsto certificate for the `a₁` step) — PLUS the first Route-(a)
  lever: the HALF-MOMENT Gaussian absorb family (`‖v‖·G_τ ≤ C·√τ·G_{λτ}` and its cubic companion),
  the exact moment-conversion mechanism of the genuine `E∗E : O(√s) → O(s)` upgrade.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ROUTE VERDICT (Sol consult, gpt-5.6-sol, 2026-08-11 — decisive).
    (1) Route (a) — the genuine `O((t−s)+s)` slice bound for the frozen `E∗E` — IS mathematically
        TRUE, and in fact the STRONGER pointwise center-column bound `|E∗E(s,z,0)| ≤ C·s·G_{Ms}(z)`
        holds: the ambient `H(t−s)` localization is not even needed — the INNER center-column
        Gaussian `G_{2σ}(w)` already pays the `|w|` factor, the `|z−w|` factors are absorbed by
        fixed-width moment absorption, and the time integral is the Beta `∫₀^s(1+√(σ/(s−σ)))dσ =
        (1+π/2)s`.  The banked `O(√s)` is an ARTIFACT of using the generic `C/√τ` outer bound.
        NO intrinsic `s·log s` or `√s` obstruction.
    (2) But route (a) is NOT a one-brick job (2–3 bricks, 3–4 with gate/tail split): it needs
        (i) the weighted-Hessian/half-moment Gaussian package, (ii) a NEW affine-difference
        supplier `|gⁱʲ(z)−gⁱʲ(w)| ≤ L·‖z−w‖·(‖z‖+‖w‖)` with ZERO constant term (a mere Lipschitz
        bound leaves `a^{−1/2}` and only reproduces `O(√s)`), with the frozen r-gate handled
        pointwise (support/convexity or an inside/outside tail split), and (iii) the refined
        `E∗E` center-column theorem (two convolutions + `B(3/2,1/2)` + width comparison).
    (3) VERDICT: land route (b) fully NOW (this file) + the half-moment lever (package (i),
        §4 below); schedule (ii)+(iii) as the follow-up bricks that restore the bounded-`cRem`
        `O(t²)` API.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS HERE.
    ▸ ★ `duhamel_simplex_sqrt_bound` (+ `_ae`) — the √-tolerant Duhamel assembly: a per-slice
        `K·((t−s)+s) + K'·√s` budget assembles to `K·t² + K'·t^{3/2}` (constant-majorant trick:
        `(t−s)+s = t` on the path and `√s ≤ √t`).
    ▸ ★ `corrHigher_bounded_of_slice_sqrt` — the o(t)-budget consumer variant: the `hCorrHigher`
        EQUALITY shape (`heatConv = pref·(t²·cRem)`, concrete witness) + the honest family bound
        `|heatConv| ≤ K·t² + K'·t^{3/2}` + the remainder rate `|cRem| ≤ (K + K'/√t)/|pref|` —
        ⚠ `cRem = O(t^{−1/2})`, NOT bounded: this is strictly weaker than the `O(t²)` API of
        `corrHigher_bounded_of_slice`; what survives is exactly `o(t)`.
    ▸ ★ `sqrt_remainder_o_t` / `corrHigher_sqrt_o_t` — THE `o(t)` SUFFICIENCY, SYNTACTIC: from the
        family `√s`-budget slice bound, `heatConv H F t 0 0 / t → 0` as `t → 0⁺` — the correction
        does NOT shift the `t¹` coefficient.  CONSUMPTION CHECK vs the capstone
        (`TrueKernelA1.trueKernel_diagonal_a1_eq_R6`): the capstone consumes `hCorrHigher` only as
        a FIXED-`t` equality with `cRem` a free real — so the equality conjunct of
        `corrHigher_bounded_of_slice_sqrt` feeds it UNCHANGED (the `O(t²)` API is syntactically
        kept); the honest boundedness layer is replaced by this Tendsto certificate.
    ▸ ★ `gaussDdim_absorb_half` / `gaussDdim_absorb_half_cubic` / `gaussDdim_moment_half` /
        `gaussDdim_moment_half_self` — the ROUTE-(a) LEVER: the half-power moment absorbs
        `√(r²(z)/τ)·G_τ(w) ≤ C·G_{λτ}(z)` (via `√x ≤ 1+x` + the banked k=0/1 absorbs), the cubic
        companion `√x·(1+x)·G ≤ C·G'` (via `√x(1+x) ≤ (1+x)²` + k=0/1/2), and the moment form
        `‖v‖-weight: √(r²(z))·G_τ(w) ≤ C·√τ·G_{λτ}(z)` (+ self-column instantiation at λ = 4) —
        exactly the `|x|`-pays-`√time` conversion the genuine k = 2 bridge needs.
    ▸ ★ `frozenK2_tail_slice_sqrt` / `frozenK2_tail_corr_bound` — the FROZEN WIRING: for any
        Gaussian-dominated slice kernel `|H(a,0,z)| ≤ C_H·G_{2a}(0−z)`, the k ≥ 2 column tail of
        the frozen Levi series feeds the slice `≤ C_H·C_tail·√s·G_{2t}(0)` and assembles to
        `≤ C_H·C_tail·G_{2t}(0)·t^{3/2}` on `0 < t ≤ 1`.  ⚠ NORMALIZATION (Sol check 3): the
        constant carries the DIAGONAL GAUSSIAN MASS `G_{2t}(0) ≈ (8πt)^{−n/2}` explicitly — it is
        `t`-uniform only RELATIVE to the diagonal prefactor, matching the capstone's
        `pref = (4πt)^{−n/2}` normalization; the absolute constant is NOT t-uniform.
    ▸ NON-VACUITY: `duhamel_sqrt_witness_pos` — the √-budget hypothesis is inhabited by the
        genuinely NONZERO slice `r a s = √s` (with `K = 0, K' = 1`) whose assembled integral is
        strictly positive; the consumer is not exercised on the empty/zero case only.

  ⚠ HONEST SCOPE.  `a₁ = R/6` remains CONDITIONAL: the flat tower is non-vacuous and closed; the
  curved side still owes the COMPLETION of this k = 2 thread (the affine-difference supplier +
  the refined `E∗E = O(s)` theorem restoring the bounded-`cRem` `O(t²)` API — this brick lands the
  `o(t)` fallback + the moment lever only), the k = 1 `SliceBoundO1`/transport-cancellation
  thread, the per-q producer re-assembly, the fat-K hEmeas/hAdom/hcont piles, the capstone
  co-instantiation, and the prior piles.  No axioms, no sorry.
-/
import Mathlib
import QIQTH.FrozenColumn

open Finset Filter Topology MeasureTheory
open scoped Interval
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.FrozenGauss QIQTH.FrozenDefect
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.AlphaLevi QIQTH.FrozenWire QIQTH.FrozenColumn

namespace QIQTH.FrozenK2

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. ★ The √-tolerant Duhamel assembly. -/

/-- **★ The √-tolerant Duhamel-simplex assembly.**  If the traced residual slice obeys the MIXED
    budget `‖r (τ−s) s‖ ≤ K·((τ−s)+s) + K'·√s` on the Duhamel path, then — since `(τ−s)+s = τ` is
    constant and `√s ≤ √τ` there — the assembled correction obeys
        `‖∫₀^τ r (τ−s) s ds‖ ≤ K·τ² + K'·τ^{3/2}`.
    The `K`-part is the (still-open) k = 1 transport budget; the `K'·√s` part is what the k ≥ 2
    frozen column tail SUPPLIES today (J4-613).  ⚠ `τ^{3/2}` is `o(τ)` but NOT `O(τ²)`. -/
theorem duhamel_simplex_sqrt_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ → ℝ → E) (K K' τ : ℝ) (hτ : 0 ≤ τ) (hK' : 0 ≤ K')
    (hr : ∀ s ∈ Ι (0 : ℝ) τ, ‖r (τ - s) s‖ ≤ K * ((τ - s) + s) + K' * Real.sqrt s) :
    ‖∫ s in (0 : ℝ)..τ, r (τ - s) s‖ ≤ K * τ ^ 2 + K' * (τ * Real.sqrt τ) := by
  have hr' : ∀ s ∈ Ι (0 : ℝ) τ, ‖r (τ - s) s‖ ≤ K * τ + K' * Real.sqrt τ := by
    intro s hs
    have hs' : s ∈ Set.Ioc (0 : ℝ) τ := by rwa [Set.uIoc_of_le hτ] at hs
    have hsqrt : Real.sqrt s ≤ Real.sqrt τ := Real.sqrt_le_sqrt hs'.2
    calc ‖r (τ - s) s‖ ≤ K * ((τ - s) + s) + K' * Real.sqrt s := hr s hs
      _ = K * τ + K' * Real.sqrt s := by ring_nf
      _ ≤ K * τ + K' * Real.sqrt τ := by gcongr
  calc ‖∫ s in (0 : ℝ)..τ, r (τ - s) s‖
      ≤ (K * τ + K' * Real.sqrt τ) * |τ - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hr'
    _ = K * τ ^ 2 + K' * (τ * Real.sqrt τ) := by
        rw [sub_zero, abs_of_nonneg hτ]; ring

/-- **The a.e. variant** — the mixed budget need only hold OFF a null set of slice times (needed
    downstream because the frozen slice bound holds for `s < t` strictly; the endpoint `s = t`,
    where the parametrix age is `0`, is a single point of measure zero). -/
theorem duhamel_simplex_sqrt_bound_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ → ℝ → E) (K K' τ : ℝ) (hτ : 0 ≤ τ) (hK' : 0 ≤ K')
    (hr : ∀ᵐ s : ℝ, s ∈ Ι (0 : ℝ) τ → ‖r (τ - s) s‖ ≤ K * ((τ - s) + s) + K' * Real.sqrt s) :
    ‖∫ s in (0 : ℝ)..τ, r (τ - s) s‖ ≤ K * τ ^ 2 + K' * (τ * Real.sqrt τ) := by
  have hr' : ∀ᵐ s : ℝ, s ∈ Ι (0 : ℝ) τ → ‖r (τ - s) s‖ ≤ K * τ + K' * Real.sqrt τ := by
    filter_upwards [hr] with s hs hmem
    have hs' : s ∈ Set.Ioc (0 : ℝ) τ := by rwa [Set.uIoc_of_le hτ] at hmem
    have hsqrt : Real.sqrt s ≤ Real.sqrt τ := Real.sqrt_le_sqrt hs'.2
    calc ‖r (τ - s) s‖ ≤ K * ((τ - s) + s) + K' * Real.sqrt s := hs hmem
      _ = K * τ + K' * Real.sqrt s := by ring_nf
      _ ≤ K * τ + K' * Real.sqrt τ := by gcongr
  calc ‖∫ s in (0 : ℝ)..τ, r (τ - s) s‖
      ≤ (K * τ + K' * Real.sqrt τ) * |τ - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const_ae hr'
    _ = K * τ ^ 2 + K' * (τ * Real.sqrt τ) := by
        rw [sub_zero, abs_of_nonneg hτ]; ring

/-! ### 2. ★ The o(t)-budget consumer variant of `corrHigher_bounded_of_slice`. -/

/-- **★ `corrHigher_bounded_of_slice_sqrt` — the `o(t)`-budget consumer variant (ROUTE b).**
    Fix `t > 0`, `pref ≠ 0`, `K' ≥ 0`.  IF the traced residual slice obeys the MIXED budget
        `‖∫ z, H (t−s) 0 z · F s z 0‖ ≤ K·((t−s)+s) + K'·√s`   on `s ∈ Ι 0 t`,
    THEN
      (i)   the `hCorrHigher` EQUALITY shape holds with the concrete witness
            `cRem = heatConv H F t 0 0 / (pref·t²)` — SYNTACTICALLY consumable by the capstone
            `trueKernel_diagonal_a1_eq_R6` exactly as the `O(t²)` route's witness is;
      (ii)  the honest FAMILY bound `|heatConv H F t 0 0| ≤ K·t² + K'·t^{3/2}`;
      (iii) the remainder rate `|cRem| ≤ (K + K'/√t)/|pref|` — ⚠ `O(t^{−1/2})`, NOT bounded:
            the genuine `O(t²)` bounded-`cRem` content is NOT recovered by this route; what
            survives (and suffices for the `a₁` coefficient) is the `o(t)` statement of
            `corrHigher_sqrt_o_t` below.  ⚠ NOT `a₁ = R/6`. -/
theorem corrHigher_bounded_of_slice_sqrt
    (H F : ℝ → Point n → Point n → ℝ) (pref K K' t : ℝ)
    (ht : 0 < t) (hpref : pref ≠ 0) (hK' : 0 ≤ K')
    (hslice : ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ z, H (t - s) 0 z * F s z 0‖ ≤ K * ((t - s) + s) + K' * Real.sqrt s) :
    heatConv H F t 0 0 = pref * (t ^ 2 * (heatConv H F t 0 0 / (pref * t ^ 2)))
      ∧ |heatConv H F t 0 0| ≤ K * t ^ 2 + K' * (t * Real.sqrt t)
      ∧ |heatConv H F t 0 0 / (pref * t ^ 2)| ≤ (K + K' / Real.sqrt t) / |pref| := by
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hpt2 : pref * t ^ 2 ≠ 0 := mul_ne_zero hpref (ne_of_gt ht2)
  have hstpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hbound : ‖heatConv H F t 0 0‖ ≤ K * t ^ 2 + K' * (t * Real.sqrt t) :=
    duhamel_simplex_sqrt_bound (fun a s' => ∫ z, H a 0 z * F s' z 0) K K' t ht.le hK' hslice
  rw [Real.norm_eq_abs] at hbound
  have hpref_pos : (0 : ℝ) < |pref| := abs_pos.mpr hpref
  refine ⟨by field_simp, hbound, ?_⟩
  -- the remainder-rate conjunct: `(K·t² + K'·t√t)/t² = K + K'/√t`.
  have key : K * t ^ 2 + K' * (t * Real.sqrt t) = (K + K' / Real.sqrt t) * t ^ 2 := by
    have h1 : t ^ 2 / Real.sqrt t = t * Real.sqrt t := by
      rw [div_eq_iff hstpos.ne']
      linear_combination (-t) * hst
    calc K * t ^ 2 + K' * (t * Real.sqrt t)
        = K * t ^ 2 + K' * (t ^ 2 / Real.sqrt t) := by rw [h1]
      _ = (K + K' / Real.sqrt t) * t ^ 2 := by ring
  calc |heatConv H F t 0 0 / (pref * t ^ 2)|
      = |heatConv H F t 0 0| / (|pref| * t ^ 2) := by
        rw [abs_div, abs_mul, abs_of_pos ht2]
    _ ≤ (K * t ^ 2 + K' * (t * Real.sqrt t)) / (|pref| * t ^ 2) := by
        gcongr
    _ = (t ^ 2 * (K + K' / Real.sqrt t)) / (t ^ 2 * |pref|) := by
        rw [key]; ring_nf
    _ = (K + K' / Real.sqrt t) / |pref| :=
        mul_div_mul_left _ _ (ne_of_gt ht2)

/-! ### 3. ★ The `o(t)` sufficiency — the Tendsto certificates for the `a₁` step. -/

/-- **★ `sqrt_remainder_o_t` — the `t^{3/2}` family budget is `o(t)`.**  ANY family `corr` with
    `|corr t| ≤ K·t² + K'·t^{3/2}` on `(0,1]` has `corr t / t → 0` as `t → 0⁺` — the `t¹`
    coefficient extracted from `pref·(1 + a₁·t + corr t)`-shaped diagonals is NOT shifted by
    `corr`.  This is the PRECISE sense in which the √s slice budget suffices for `a₁` (the
    J4-613 `integral_sqrt_le_linear` o(t) verdict, upgraded to an actual limit statement). -/
theorem sqrt_remainder_o_t (corr : ℝ → ℝ) (K K' : ℝ)
    (hbd : ∀ t : ℝ, 0 < t → t ≤ 1 → |corr t| ≤ K * t ^ 2 + K' * (t * Real.sqrt t)) :
    Tendsto (fun t => corr t / t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hg : Tendsto (fun t : ℝ => K * t + K' * Real.sqrt t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => K * t + K' * Real.sqrt t := by
      exact (continuous_const.mul continuous_id).add
        (continuous_const.mul Real.continuous_sqrt)
    have h0 := hc.tendsto 0
    simp only [mul_zero, Real.sqrt_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hg
  have hlt1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt1] with t ht0 ht1
  have ht0' : (0 : ℝ) < t := ht0
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0', div_le_iff₀ ht0']
  calc |corr t| ≤ K * t ^ 2 + K' * (t * Real.sqrt t) := hbd t ht0' ht1.le
    _ = (K * t + K' * Real.sqrt t) * t := by ring

/-- **★ `corrHigher_sqrt_o_t` — THE `o(t)` CONSUMPTION, END-TO-END.**  If the traced residual
    slice obeys the mixed `K·((t−s)+s) + K'·√s` budget for every `t ∈ (0,1]`, then the assembled
    Levi/Duhamel correction satisfies
        `heatConv H F t 0 0 / t  →  0`   as `t → 0⁺`.
    CONSUMPTION CHECK against the capstone: `trueKernel_diagonal_a1_eq_R6` carries `hCorrHigher`
    only as a FIXED-`t` equality `heatConv = pref·(t²·cRem)` with `cRem` a free real — the
    equality conjunct of `corrHigher_bounded_of_slice_sqrt` serves it verbatim, so the capstone's
    `O(t²)` API is syntactically UNCHANGED; this theorem is the replacement HONESTY layer: the
    diagonal's non-parametrix correction is `o(t)`, hence the `t¹` coefficient (`a₁ = R/6` on the
    parametrix side) is not shifted.  ⚠ NOT `a₁ = R/6` (the k = 1 transport budget `K` is still
    a carried hypothesis here, and the frozen wiring below carries the diagonal Gaussian mass). -/
theorem corrHigher_sqrt_o_t
    (H F : ℝ → Point n → Point n → ℝ) (K K' : ℝ) (hK' : 0 ≤ K')
    (hslice : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ z, H (t - s) 0 z * F s z 0‖ ≤ K * ((t - s) + s) + K' * Real.sqrt s) :
    Tendsto (fun t => heatConv H F t 0 0 / t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine sqrt_remainder_o_t (fun t => heatConv H F t 0 0) K K' (fun t ht0 ht1 => ?_)
  have hb : ‖heatConv H F t 0 0‖ ≤ K * t ^ 2 + K' * (t * Real.sqrt t) :=
    duhamel_simplex_sqrt_bound (fun a s' => ∫ z, H a 0 z * F s' z 0) K K' t ht0.le hK'
      (hslice t ht0 ht1)
  rwa [Real.norm_eq_abs] at hb

/-! ### 4. ★ THE ROUTE-(a) LEVER — the half-moment Gaussian absorb family. -/

/-- **★ `gaussDdim_absorb_half` — the HALF-power moment absorb.**  Under the banked gate, the
    half-moment weight is absorbed: `√(r²(z)/τ)·G_τ(w) ≤ C·G_{λτ}(z)`.  Via `√x ≤ 1 + x`
    (`(√x−1)² ≥ 0`) + the banked `k = 0` and `k = 1` absorbs.  This is the missing HALF-STEP of
    the `gaussDdim_absorb_*` integer family — the mechanism converting ONE `‖·‖` factor of the
    k = 2 bridge into a `√τ` after Gaussian localization. -/
theorem gaussDdim_absorb_half
    {η lam : ℝ} (hη1 : η < 1) (hlam : 1 < lam) (hlamη : 1 / lam < 1 - η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w z : Point n),
      (1 - η) * rncRadialSq z ≤ rncRadialSq w →
        Real.sqrt (rncRadialSq z / τ) * gaussDdim τ w ≤ C * gaussDdim (lam * τ) z := by
  obtain ⟨C0, hC0, h0⟩ := gaussDdim_absorb_zero (n := n) hη1 hlam hlamη
  obtain ⟨C1, hC1, h1⟩ := gaussDdim_absorb_one (n := n) hη1 hlam hlamη
  refine ⟨C0 + C1, by positivity, fun τ hτ w z hgate => ?_⟩
  have hx : (0 : ℝ) ≤ rncRadialSq z / τ :=
    div_nonneg (rncRadialSq_nonneg z) hτ.le
  have hsq : Real.sqrt (rncRadialSq z / τ) ≤ 1 + rncRadialSq z / τ := by
    nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt (rncRadialSq z / τ) - 1),
      Real.sqrt_nonneg (rncRadialSq z / τ)]
  have hG : 0 ≤ gaussDdim τ w := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  calc Real.sqrt (rncRadialSq z / τ) * gaussDdim τ w
      ≤ (1 + rncRadialSq z / τ) * gaussDdim τ w := mul_le_mul_of_nonneg_right hsq hG
    _ = gaussDdim τ w + (rncRadialSq z / τ) * gaussDdim τ w := by ring
    _ ≤ C0 * gaussDdim (lam * τ) z + C1 * gaussDdim (lam * τ) z :=
        add_le_add (h0 τ hτ w z hgate) (h1 τ hτ w z hgate)
    _ = (C0 + C1) * gaussDdim (lam * τ) z := by ring

/-- **★ `gaussDdim_absorb_half_cubic` — the cubic companion** (Sol's weighted-Hessian shape):
    `√(r²(z)/τ)·(1 + r²(z)/τ)·G_τ(w) ≤ C·G_{λτ}(z)` — exactly the prefactor of
    `|x|·a^{−1}(1 + |x|²/a)·G` after pulling out `a^{−1/2}`; via `√x(1+x) ≤ (1+x)²` + the banked
    `k = 0, 1, 2` absorbs. -/
theorem gaussDdim_absorb_half_cubic
    {η lam : ℝ} (hη1 : η < 1) (hlam : 1 < lam) (hlamη : 1 / lam < 1 - η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w z : Point n),
      (1 - η) * rncRadialSq z ≤ rncRadialSq w →
        Real.sqrt (rncRadialSq z / τ) * (1 + rncRadialSq z / τ) * gaussDdim τ w
          ≤ C * gaussDdim (lam * τ) z := by
  obtain ⟨C0, hC0, h0⟩ := gaussDdim_absorb_zero (n := n) hη1 hlam hlamη
  obtain ⟨C1, hC1, h1⟩ := gaussDdim_absorb_one (n := n) hη1 hlam hlamη
  obtain ⟨C2, hC2, h2⟩ := gaussDdim_absorb_two (n := n) hη1 hlam hlamη
  refine ⟨C0 + 2 * C1 + C2, by positivity, fun τ hτ w z hgate => ?_⟩
  have hx : (0 : ℝ) ≤ rncRadialSq z / τ :=
    div_nonneg (rncRadialSq_nonneg z) hτ.le
  have hsq : Real.sqrt (rncRadialSq z / τ) ≤ 1 + rncRadialSq z / τ := by
    nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt (rncRadialSq z / τ) - 1),
      Real.sqrt_nonneg (rncRadialSq z / τ)]
  have hcube : Real.sqrt (rncRadialSq z / τ) * (1 + rncRadialSq z / τ)
      ≤ 1 + 2 * (rncRadialSq z / τ) + (rncRadialSq z / τ) ^ 2 := by
    have h1x : (0 : ℝ) ≤ 1 + rncRadialSq z / τ := by linarith
    calc Real.sqrt (rncRadialSq z / τ) * (1 + rncRadialSq z / τ)
        ≤ (1 + rncRadialSq z / τ) * (1 + rncRadialSq z / τ) :=
          mul_le_mul_of_nonneg_right hsq h1x
      _ = 1 + 2 * (rncRadialSq z / τ) + (rncRadialSq z / τ) ^ 2 := by ring
  have hG : 0 ≤ gaussDdim τ w := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  calc Real.sqrt (rncRadialSq z / τ) * (1 + rncRadialSq z / τ) * gaussDdim τ w
      ≤ (1 + 2 * (rncRadialSq z / τ) + (rncRadialSq z / τ) ^ 2) * gaussDdim τ w :=
        mul_le_mul_of_nonneg_right hcube hG
    _ = gaussDdim τ w + 2 * ((rncRadialSq z / τ) * gaussDdim τ w)
          + (rncRadialSq z / τ) ^ 2 * gaussDdim τ w := by ring
    _ ≤ C0 * gaussDdim (lam * τ) z + 2 * (C1 * gaussDdim (lam * τ) z)
          + C2 * gaussDdim (lam * τ) z := by
        have hb0 := h0 τ hτ w z hgate
        have hb1 := h1 τ hτ w z hgate
        have hb2 := h2 τ hτ w z hgate
        have hb1' : 2 * ((rncRadialSq z / τ) * gaussDdim τ w)
            ≤ 2 * (C1 * gaussDdim (lam * τ) z) := by linarith
        linarith
    _ = (C0 + 2 * C1 + C2) * gaussDdim (lam * τ) z := by ring

/-- **★ `gaussDdim_moment_half` — the `‖v‖`-moment pays `√τ`.**  Under the gate,
        `√(r²(z))·G_τ(w) ≤ C·√τ·G_{λτ}(z)`
    — the EXACT bridge-moment conversion (`|offset| · Gaussian ≲ √time · wider Gaussian`) that the
    genuine k = 2 `E∗E` upgrade spends once per norm factor. -/
theorem gaussDdim_moment_half
    {η lam : ℝ} (hη1 : η < 1) (hlam : 1 < lam) (hlamη : 1 / lam < 1 - η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w z : Point n),
      (1 - η) * rncRadialSq z ≤ rncRadialSq w →
        Real.sqrt (rncRadialSq z) * gaussDdim τ w
          ≤ C * Real.sqrt τ * gaussDdim (lam * τ) z := by
  obtain ⟨C, hC, hb⟩ := gaussDdim_absorb_half (n := n) hη1 hlam hlamη
  refine ⟨C, hC, fun τ hτ w z hgate => ?_⟩
  have hτr : τ * (rncRadialSq z / τ) = rncRadialSq z := by
    field_simp
  have hsplit : Real.sqrt (rncRadialSq z)
      = Real.sqrt τ * Real.sqrt (rncRadialSq z / τ) := by
    rw [← Real.sqrt_mul hτ.le, hτr]
  calc Real.sqrt (rncRadialSq z) * gaussDdim τ w
      = Real.sqrt τ * (Real.sqrt (rncRadialSq z / τ) * gaussDdim τ w) := by
        rw [hsplit]; ring
    _ ≤ Real.sqrt τ * (C * gaussDdim (lam * τ) z) :=
        mul_le_mul_of_nonneg_left (hb τ hτ w z hgate) (Real.sqrt_nonneg τ)
    _ = C * Real.sqrt τ * gaussDdim (lam * τ) z := by ring

/-- **The self-column instantiation** (`w = z`, `η = 1/2`, `λ = 4` — the gate is trivial):
    `√(r²(v))·G_τ(v) ≤ C·√τ·G_{4τ}(v)` for ALL `τ > 0, v` — the unconditional single-variable
    moment lemma, ready for the inner-Gaussian `|w|`-payment of the k = 2 bridge. -/
theorem gaussDdim_moment_half_self :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ v : Point n,
      Real.sqrt (rncRadialSq v) * gaussDdim τ v
        ≤ C * Real.sqrt τ * gaussDdim (4 * τ) v := by
  obtain ⟨C, hC, hb⟩ := gaussDdim_moment_half (n := n) (η := 1 / 2) (lam := 4)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun τ hτ v => hb τ hτ v v ?_⟩
  nlinarith [rncRadialSq_nonneg v]

/-! ### 5. ★ THE FROZEN WIRING — the k ≥ 2 column tail feeds the √s slice budget. -/

/-- **★ `frozenK2_tail_slice_sqrt` — the frozen k ≥ 2 tail FITS the `K'·√s` slice budget.**  For
    `Kc ≤ 0`, `r ≥ 0` there is `C_t ≥ 0` such that for EVERY Gaussian-dominated slice kernel
    (`|H(a,0,z)| ≤ C_H·G_{2a}(0−z)`, `a > 0`) and all `0 < s < t`, `s ≤ 1`:
        `‖∫ z, H(t−s,0,z)·(leviSeries E_frozen + E_frozen)(s,z,0)‖
             ≤ (C_H·C_t)·(√s·G_{2t}(0))`.
    Chapman–Kolmogorov composition: the integrand is dominated by
    `C_H·C_t·√s · G_{2(t−s)}(0−z)·G_{2s}(z−0)` (J4-613 column tail), whose `z`-integral is
    EXACTLY `G_{2t}(0)` by the banked Gaussian semigroup.  ⚠ NORMALIZATION: the diagonal mass
    `G_{2t}(0) ≈ (8πt)^{−n/2}` is carried EXPLICITLY — `t`-uniformity holds only relative to the
    capstone's diagonal prefactor, not absolutely. -/
theorem frozenK2_tail_slice_sqrt (Kc r : ℝ) (hK : Kc ≤ 0) (hr : 0 ≤ r) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (z : Point n), 0 < a →
          |H a 0 z| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - z)) →
        ∀ (t s : ℝ), 0 < s → s < t → s ≤ 1 →
          ‖∫ z, H (t - s) 0 z
              * (leviSeries (frozenDefectKernel Kc r) s z 0 + frozenDefectKernel Kc r s z 0)‖
            ≤ (C_H * C_t) * (Real.sqrt s * gaussDdim (2 * t) (0 : Point n)) := by
  obtain ⟨C_col, C_tail, hCcol, hCtail, hbd⟩ :=
    frozenColumn_leviSeries_bound (n := n) Kc r hK hr
  refine ⟨C_tail, hCtail, fun H C_H hCH hH t s hs hst hs1 => ?_⟩
  have hts : 0 < t - s := by linarith
  have hg_int : Integrable (fun z : Point n =>
      (C_H * C_tail * Real.sqrt s)
        * (gaussDdim (2 * (t - s)) ((0 : Point n) - z)
            * gaussDdim (2 * s) (z - (0 : Point n)))) volume :=
    (gaussDdim_mul_integrable (2 * (t - s)) (2 * s) (0 : Point n) (0 : Point n)).const_mul _
  have hpt : ∀ z : Point n,
      ‖H (t - s) 0 z
          * (leviSeries (frozenDefectKernel Kc r) s z 0 + frozenDefectKernel Kc r s z 0)‖
        ≤ (C_H * C_tail * Real.sqrt s)
            * (gaussDdim (2 * (t - s)) ((0 : Point n) - z)
                * gaussDdim (2 * s) (z - (0 : Point n))) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hH (t - s) z hts
    have h2 := (hbd s z hs hs1).2
    have hGnn : (0 : ℝ) ≤ gaussDdim (2 * (t - s)) ((0 : Point n) - z) :=
      QIQTH.ResidueBound.gaussDdim_nonneg _ _
    calc |H (t - s) 0 z|
          * |leviSeries (frozenDefectKernel Kc r) s z 0 + frozenDefectKernel Kc r s z 0|
        ≤ (C_H * gaussDdim (2 * (t - s)) ((0 : Point n) - z))
            * (C_tail * (Real.sqrt s * gaussDdim (2 * s) (z - (0 : Point n)))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCH hGnn)
      _ = (C_H * C_tail * Real.sqrt s)
            * (gaussDdim (2 * (t - s)) ((0 : Point n) - z)
                * gaussDdim (2 * s) (z - (0 : Point n))) := by ring
  calc ‖∫ z, H (t - s) 0 z
          * (leviSeries (frozenDefectKernel Kc r) s z 0 + frozenDefectKernel Kc r s z 0)‖
      ≤ ∫ z, (C_H * C_tail * Real.sqrt s)
          * (gaussDdim (2 * (t - s)) ((0 : Point n) - z)
              * gaussDdim (2 * s) (z - (0 : Point n))) :=
        MeasureTheory.norm_integral_le_of_norm_le hg_int (ae_of_all _ hpt)
    _ = (C_H * C_tail * Real.sqrt s)
          * ∫ z, gaussDdim (2 * (t - s)) ((0 : Point n) - z)
              * gaussDdim (2 * s) (z - (0 : Point n)) :=
        integral_const_mul _ _
    _ = (C_H * C_tail * Real.sqrt s)
          * gaussDdim (2 * (t - s) + 2 * s) ((0 : Point n) - 0) := by
        rw [QIQTH.GaussianConvolution.gaussDdim_conv (2 * (t - s)) (2 * s)
          (by linarith) (by linarith) (0 : Point n) (0 : Point n)]
    _ = (C_H * C_tail) * (Real.sqrt s * gaussDdim (2 * t) (0 : Point n)) := by
        rw [show 2 * (t - s) + 2 * s = 2 * t from by ring,
            show (0 : Point n) - 0 = 0 from sub_zero 0]
        ring

/-- **★ `frozenK2_tail_corr_bound` — the assembled frozen tail correction is `O(t^{3/2})`.**  For
    `Kc ≤ 0`, `r ≥ 0`, a Gaussian-dominated slice kernel `H`, and `0 < t ≤ 1`:
        `‖∫₀^t ∫ z, H(t−s,0,z)·(leviSeries E_frozen + E_frozen)(s,z,0) dz ds‖
             ≤ (C_H·C_t·G_{2t}(0))·t^{3/2}`.
    (The `s = t` endpoint, where the age is `0`, is null — the a.e. assembly.)  Together with
    `sqrt_remainder_o_t` this is the frozen k ≥ 2 tail's `o(t)` certificate RELATIVE to the
    diagonal mass; the k = 1 (`−E`, transport) part is NOT included — it is the separate
    still-open thread.  ⚠ NOT `a₁ = R/6`. -/
theorem frozenK2_tail_corr_bound (Kc r : ℝ) (hK : Kc ≤ 0) (hr : 0 ≤ r) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (z : Point n), 0 < a →
          |H a 0 z| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - z)) →
        ∀ t : ℝ, 0 < t → t ≤ 1 →
          ‖∫ s in (0 : ℝ)..t, ∫ z, H (t - s) 0 z
              * (leviSeries (frozenDefectKernel Kc r) s z 0 + frozenDefectKernel Kc r s z 0)‖
            ≤ (C_H * C_t * gaussDdim (2 * t) (0 : Point n)) * (t * Real.sqrt t) := by
  obtain ⟨C_t, hCt, hsl⟩ := frozenK2_tail_slice_sqrt (n := n) Kc r hK hr
  refine ⟨C_t, hCt, fun H C_H hCH hH t ht ht1 => ?_⟩
  have hK' : (0 : ℝ) ≤ C_H * C_t * gaussDdim (2 * t) (0 : Point n) :=
    mul_nonneg (mul_nonneg hCH hCt) (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  have hae : ∀ᵐ s : ℝ, s ∈ Ι (0 : ℝ) t →
      ‖(fun a s' => ∫ z, H a 0 z
          * (leviSeries (frozenDefectKernel Kc r) s' z 0 + frozenDefectKernel Kc r s' z 0))
          (t - s) s‖
        ≤ (0 : ℝ) * ((t - s) + s)
            + (C_H * C_t * gaussDdim (2 * t) (0 : Point n)) * Real.sqrt s := by
    filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)]
      with s hsne hmem
    have hs' : s ∈ Set.Ioc (0 : ℝ) t := by rwa [Set.uIoc_of_le ht.le] at hmem
    have hst : s < t := lt_of_le_of_ne hs'.2 (by simpa using hsne)
    have hb := hsl H C_H hCH hH t s hs'.1 hst (le_trans hs'.2 ht1)
    calc ‖∫ z, H (t - s) 0 z
            * (leviSeries (frozenDefectKernel Kc r) s z 0 + frozenDefectKernel Kc r s z 0)‖
        ≤ (C_H * C_t) * (Real.sqrt s * gaussDdim (2 * t) (0 : Point n)) := hb
      _ = (0 : ℝ) * ((t - s) + s)
            + (C_H * C_t * gaussDdim (2 * t) (0 : Point n)) * Real.sqrt s := by ring
  have := duhamel_simplex_sqrt_bound_ae
    (fun a s' => ∫ z, H a 0 z
      * (leviSeries (frozenDefectKernel Kc r) s' z 0 + frozenDefectKernel Kc r s' z 0))
    0 (C_H * C_t * gaussDdim (2 * t) (0 : Point n)) t ht.le hK' hae
  calc ‖∫ s in (0 : ℝ)..t, ∫ z, H (t - s) 0 z
          * (leviSeries (frozenDefectKernel Kc r) s z 0 + frozenDefectKernel Kc r s z 0)‖
      ≤ 0 * t ^ 2 + (C_H * C_t * gaussDdim (2 * t) (0 : Point n)) * (t * Real.sqrt t) := this
    _ = (C_H * C_t * gaussDdim (2 * t) (0 : Point n)) * (t * Real.sqrt t) := by ring

/-! ### 6. NON-VACUITY — the √-budget consumer is exercised on a genuinely nonzero slice. -/

/-- **NON-VACUITY (adversarial).**  The mixed √-budget hypothesis of
    `duhamel_simplex_sqrt_bound` is inhabited by the genuinely NONZERO slice family
    `r a s = √s` (`K = 0`, `K' = 1`), and its assembled integral `∫₀^t √s ds` is STRICTLY
    POSITIVE for `t > 0` — the consumer route is not certified on the zero slice only. -/
theorem duhamel_sqrt_witness_pos (t : ℝ) (ht : 0 < t) :
    (∀ s ∈ Ι (0 : ℝ) t,
        ‖(fun (_ : ℝ) (s' : ℝ) => Real.sqrt s') (t - s) s‖
          ≤ (0 : ℝ) * ((t - s) + s) + 1 * Real.sqrt s)
      ∧ 0 < ∫ s in (0 : ℝ)..t, Real.sqrt s := by
  constructor
  · intro s _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
    simp
  · exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (Real.continuous_sqrt.intervalIntegrable 0 t)
      (fun x hx => Real.sqrt_pos.mpr hx.1) ht

end QIQTH.FrozenK2

section AxiomChecks
open QIQTH.FrozenK2
#print axioms duhamel_simplex_sqrt_bound
#print axioms duhamel_simplex_sqrt_bound_ae
#print axioms corrHigher_bounded_of_slice_sqrt
#print axioms sqrt_remainder_o_t
#print axioms corrHigher_sqrt_o_t
#print axioms gaussDdim_absorb_half
#print axioms gaussDdim_absorb_half_cubic
#print axioms gaussDdim_moment_half
#print axioms gaussDdim_moment_half_self
#print axioms frozenK2_tail_slice_sqrt
#print axioms frozenK2_tail_corr_bound
#print axioms duhamel_sqrt_witness_pos
end AxiomChecks
