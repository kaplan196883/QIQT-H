/-
  ModelIntegrableW — M6 / analytic carry: the MODEL-side (Gaussian dominator) integrability
  conjuncts of `IterConvIntegrableW`, discharged UNCONDITIONALLY.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  The true-kernel Levi/Duhamel convergence is reduced (all std-3) to one geometric input
  `hEboundW` + the per-step integrability family `IterConvIntegrableW` (defined in
  `ParametrixHEboundWiring`).  That family bundles FIVE integral facts.  Three of them (conjuncts
  (1),(2),(3)) genuinely depend on the ACTUAL residual `E`.  The remaining TWO — conjuncts (4),(5) —
  are about the MODEL Gaussian dominators `baseKernelW κ α` / `iterKernelW κ α` ONLY:

    (4)  `∀ s, Integrable (fun z => C · baseKernelW κ α (t−s) x z · (C^k · iterKernelW κ α k s z y))`
    (5)  `IntervalIntegrable (fun s => ∫ z, C · baseKernelW κ α (t−s) x z · (C^k · iterKernelW κ α k s z y)) 0 t`

  They carry NO dependence on the residual, the geometry, or the recenter/off-diagonal wall — they
  are pure Gaussian facts.  This file proves them unconditionally at `α = 0` (the case
  `trueKernel_diagonal_a1_eq_R6` uses, `κ = 2`), for ALL width `κ > 0`, ALL `k ≥ 1`, ALL dimension
  `n`, discharging conjuncts (4) and (5).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS HERE.

    ▸ Gaussian integrability workhorses (all times, all `n`):
      • `heatKernel1D_mul_integrable` — the 1-D product `w ↦ G_a(c−w)·G_b(w−d)` is Lebesgue
        integrable for ALL `a,b` (integrable factor × bounded factor; the nonpositive-time kernel
        vanishes).
      • `gaussDdim_mul_integrable` — the `d`-dim product `z ↦ G_a(x−z)·G_b(z−y)` is integrable, via
        `Integrable.fin_nat_prod` over the coordinate 1-D products (uniform in `n`, incl. `n = 0`).
      • `gaussDdim_eq_zero_of_nonpos` / `iterKernelW_of_nonpos_time` — the model kernels vanish at
        nonpositive time when `n ≥ 1` (kills the boundary of the `∀ s` quantifier).

    ▸ The model conjuncts (the deliverable):
      • `modelZ_integrableW` — conjunct (4): the `z`-integrand is integrable for EVERY `s` (interior
        `0<s<t` via the Gaussian-product workhorse + `iterKernelW_eq` closed form + `gaussDdim_conv`;
        boundary via `n = 0` finiteness / `n ≥ 1` vanishing).
      • `modelS_intervalIntegrableW` — conjunct (5): the `s ↦ ∫ z (…)` map is interval-integrable on
        `[0,t]`, since a.e. on `(0,t]` it equals `const · s^(k−1)` (`gaussDdim_conv` collapses the
        `z`-convolution to `gaussDdim (κ·t) (x−y)`, `iterKernelW_eq` supplies the `Γ`/time-power),
        a continuous/`rpow`-integrable function; the single endpoint `s = t` is null.
      • `iterConvIntegrableW_model` — packages (4)∧(5) in the exact shape they occupy in
        `IterConvIntegrableW E κ 0 C`, so a later full discharge of `hInt` can cite them directly.

  ⚠ HONEST SCOPE.  This is the MODEL-SIDE carry only.  Conjuncts (1),(2),(3) of `IterConvIntegrableW`
  (the residual-side interval/Lebesgue integrability of the ACTUAL iterated convolutions `iterE E k`)
  are NOT touched here — they depend on `E` and stay carried.  NOT `a₁ = R/6`.  No `sorry`, no new
  axioms, no vacuous hypotheses; every carried positivity (`0 < t`, `0 < κ`, `1 ≤ k`) is genuine.
-/
import Mathlib
import QIQTH.ParametrixHEboundWiring
import QIQTH.GaussianConvolution

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.GaussianWidthTolerant QIQTH.HeatDuhamel

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 800000

/-! ### 1. Elementary 1-D flat-kernel facts. -/

/-- The flat 1-D kernel is EVEN: `G_a(c−w) = G_a(w−c)` (depends on the argument through its square). -/
theorem heatKernel1D_sub_comm (a c w : ℝ) :
    heatKernel1D a (c - w) = heatKernel1D a (w - c) := by
  simp only [heatKernel1D]
  rw [show (c - w) ^ 2 = (w - c) ^ 2 from by ring]

/-- At NONPOSITIVE time the flat 1-D kernel VANISHES: `a ≤ 0 → G_a(x) = 0` (the `√(4πa)`
    normalization is `0`, hence its inverse is `0`). -/
theorem heatKernel1D_of_nonpos (a x : ℝ) (ha : a ≤ 0) : heatKernel1D a x = 0 := by
  rw [heatKernel1D,
      Real.sqrt_eq_zero_of_nonpos (by nlinarith [Real.pi_pos] : 4 * Real.pi * a ≤ 0),
      inv_zero, zero_mul]

/-- The flat 1-D kernel is integrable at EVERY time (positive: Gaussian; nonpositive: the zero
    function). -/
theorem heatKernel1D_integrable' (a : ℝ) : Integrable (fun w => heatKernel1D a w) volume := by
  by_cases ha : 0 < a
  · exact heatKernel1D_integrable a ha
  · push_neg at ha
    have hz : (fun w => heatKernel1D a w) = fun _ => (0 : ℝ) := by
      funext w; exact heatKernel1D_of_nonpos a w ha
    rw [hz]; exact integrable_zero _ _ _

/-- The reflected/translated 1-D kernel `w ↦ G_a(c−w)` is integrable at every time. -/
theorem heatKernel1D_shift_integrable (a c : ℝ) :
    Integrable (fun w => heatKernel1D a (c - w)) volume := by
  have h := (heatKernel1D_integrable' a).comp_sub_right c
  have he : (fun w => heatKernel1D a (c - w)) = fun w => heatKernel1D a (w - c) := by
    funext w; exact heatKernel1D_sub_comm a c w
  rw [he]; exact h

/-- The flat 1-D kernel is uniformly bounded by its peak normalization `(√(4πb))⁻¹` (which is `0` at
    nonpositive time). -/
theorem heatKernel1D_abs_le (b u : ℝ) :
    |heatKernel1D b u| ≤ (Real.sqrt (4 * Real.pi * b))⁻¹ := by
  by_cases hb : 0 < b
  · rw [heatKernel1D, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt (4*Real.pi*b))⁻¹)]
    have hexp : |Real.exp (-u ^ 2 / (4 * b))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-u ^ 2 / (4 * b)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith [sq_nonneg u])
      simpa using this
    calc (Real.sqrt (4 * Real.pi * b))⁻¹ * |Real.exp (-u ^ 2 / (4 * b))|
        ≤ (Real.sqrt (4 * Real.pi * b))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (Real.sqrt (4 * Real.pi * b))⁻¹ := mul_one _
  · push_neg at hb
    rw [heatKernel1D_of_nonpos b u hb, abs_zero]
    positivity

/-- The flat 1-D kernel is continuous in its space argument. -/
theorem heatKernel1D_continuous (b : ℝ) : Continuous (fun u => heatKernel1D b u) := by
  unfold heatKernel1D; fun_prop

/-! ### 2. Gaussian-product integrability (the workhorse). -/

/-- **The 1-D two-kernel product is integrable at ALL times.**  `w ↦ G_a(c−w) · G_b(w−d)` is
    Lebesgue integrable: the first factor is integrable (`heatKernel1D_shift_integrable`) and the
    second is bounded by `(√(4πb))⁻¹` (`heatKernel1D_abs_le`), so `Integrable.mul_bdd` applies. -/
theorem heatKernel1D_mul_integrable (a b c d : ℝ) :
    Integrable (fun w => heatKernel1D a (c - w) * heatKernel1D b (w - d)) volume := by
  refine (heatKernel1D_shift_integrable a c).mul_bdd
    (c := (Real.sqrt (4 * Real.pi * b))⁻¹)
    (((heatKernel1D_continuous b).comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
    (ae_of_all _ (fun w => ?_))
  rw [Real.norm_eq_abs]; exact heatKernel1D_abs_le b (w - d)

/-- **The `d`-dim two-Gaussian product is integrable at ALL times, uniformly in `n`.**
    `z ↦ gaussDdim a (x−z) · gaussDdim b (z−y)` is integrable on `Point n = Fin n → ℝ`: the product
    factors coordinatewise into 1-D products (`heatKernel1D_mul_integrable`), and
    `Integrable.fin_nat_prod` bundles them (this handles `n = 0` via the empty-product finite-measure
    base case). -/
theorem gaussDdim_mul_integrable (a b : ℝ) (x y : Point n) :
    Integrable (fun z : Point n => gaussDdim a (x - z) * gaussDdim b (z - y)) volume := by
  have hpt : (fun z : Point n => gaussDdim a (x - z) * gaussDdim b (z - y))
      = fun z => ∏ i, heatKernel1D a (x i - z i) * heatKernel1D b (z i - y i) := by
    funext z
    simp only [gaussDdim]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by rw [Pi.sub_apply, Pi.sub_apply])
  have hf : ∀ i : Fin n,
      Integrable (fun w => heatKernel1D a (x i - w) * heatKernel1D b (w - y i)) volume :=
    fun i => heatKernel1D_mul_integrable a b (x i) (y i)
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-! ### 3. Vanishing of the model kernels at nonpositive time (`n ≥ 1`). -/

/-- **The `d`-dim Gaussian vanishes at nonpositive time when `n ≥ 1`.**  `a ≤ 0 → gaussDdim a v = 0`
    (any single coordinate factor is `0`). -/
theorem gaussDdim_eq_zero_of_nonpos (hn : 1 ≤ n) {a : ℝ} (ha : a ≤ 0) (v : Point n) :
    gaussDdim a v = 0 := by
  simp only [gaussDdim]
  obtain ⟨i⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (heatKernel1D_of_nonpos a (v i) ha)

/-- **The width-`κ` iterated model kernel VANISHES at nonpositive time when `n ≥ 1`.**  For `κ > 0`,
    `s ≤ 0`, and any `k ≥ 1`, `iterKernelW κ α k s z y = 0`.  Base `k = 1`: the base kernel's
    Gaussian is at time `κ·s ≤ 0`, hence `0`.  Step: the convolution integrates over `s' ∈ [s,0]`,
    where the inner factor `iterKernelW κ α k s'` already vanishes by the inductive hypothesis. -/
theorem iterKernelW_of_nonpos_time (κ α : ℝ) (hκ : 0 < κ) (hn : 1 ≤ n) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℝ), s ≤ 0 → ∀ (z y : Point n),
      iterKernelW κ α k s z y = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro s hs z y
      rw [iterKernelW_one]
      unfold baseKernelW
      rw [gaussDdim_eq_zero_of_nonpos hn (by nlinarith : κ * s ≤ 0) (z - y), mul_zero]
  | succ m hm ih =>
      intro s hs z y
      rw [iterKernelW_succ κ α hm, heatConvK_apply]
      simp only [heatConv]
      refine (intervalIntegral.integral_congr (fun s' hs' => ?_)).trans
        intervalIntegral.integral_zero
      have hmem : s' ∈ Set.Icc s 0 := by rwa [Set.uIcc_of_ge hs] at hs'
      have hz : (fun w => baseKernelW κ α (s - s') z w * iterKernelW κ α m s' w y)
          = fun _ => (0 : ℝ) := by
        funext w; rw [ih s' hmem.2 w y, mul_zero]
      show (∫ w, baseKernelW κ α (s - s') z w * iterKernelW κ α m s' w y) = 0
      rw [hz, integral_zero]

/-! ### 4. Conjunct (4): the `z`-integrand is integrable for every `s`. -/

/-- **★ MODEL CONJUNCT (4) — the `z`-integrand is integrable for EVERY `s`.**  For `κ > 0`, `α = 0`,
    `k ≥ 1`, `t > 0`, and all `x y s`,
        `Integrable (fun z => C · baseKernelW κ 0 (t−s) x z · (C^k · iterKernelW κ 0 k s z y))`.
    Interior `0 < s < t`: `baseKernelW_zero_apply` + `iterKernelW_eq` turn the integrand into a
    constant times `gaussDdim (κ(t−s)) (x−z) · gaussDdim (κs) (z−y)`, integrable by
    `gaussDdim_mul_integrable`.  Boundary (`s ≤ 0` or `t ≤ s`): for `n = 0` the space is finite
    (`Integrable.of_finite`); for `n ≥ 1` a model factor vanishes (`iterKernelW_of_nonpos_time` /
    `gaussDdim_eq_zero_of_nonpos`), so the integrand is `0`. -/
theorem modelZ_integrableW (κ C : ℝ) (hκ : 0 < κ) (k : ℕ) (hk : 1 ≤ k)
    (t : ℝ) (ht : 0 < t) (x y : Point n) (s : ℝ) :
    Integrable
      (fun z => C * baseKernelW κ 0 (t - s) x z * (C ^ k * iterKernelW κ 0 k s z y)) volume := by
  by_cases hs : 0 < s ∧ s < t
  · obtain ⟨hs0, hst⟩ := hs
    have hform : (fun z => C * baseKernelW κ 0 (t - s) x z * (C ^ k * iterKernelW κ 0 k s z y))
        = fun z => (C * C ^ k
              * (Real.Gamma (0 + 1) ^ k / Real.Gamma ((k : ℝ) * (0 + 1)))
              * s ^ ((k : ℝ) * (0 + 1) - 1))
            * (gaussDdim (κ * (t - s)) (x - z) * gaussDdim (κ * s) (z - y)) := by
      funext z
      rw [baseKernelW_zero_apply, iterKernelW_eq κ 0 hκ (by norm_num) s hs0 z y hk]
      ring
    rw [hform]
    exact (gaussDdim_mul_integrable (κ * (t - s)) (κ * s) x y).const_mul _
  · rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      exact Integrable.of_finite
    · have hzero : (fun z => C * baseKernelW κ 0 (t - s) x z * (C ^ k * iterKernelW κ 0 k s z y))
          = fun _ => (0 : ℝ) := by
        funext z
        rcases not_and_or.mp hs with h | h
        · push_neg at h
          rw [iterKernelW_of_nonpos_time κ 0 hκ hn1 k hk s h z y, mul_zero, mul_zero]
        · push_neg at h
          rw [baseKernelW_zero_apply,
              gaussDdim_eq_zero_of_nonpos hn1 (by nlinarith : κ * (t - s) ≤ 0) (x - z),
              mul_zero, zero_mul]
      rw [hzero]; exact integrable_zero _ _ _

/-! ### 5. Conjunct (5): the `s`-integral is interval-integrable on `[0,t]`. -/

/-- **★ MODEL CONJUNCT (5) — the `s ↦ ∫ z (…)` map is interval-integrable on `[0,t]`.**  For `κ > 0`,
    `α = 0`, `k ≥ 1`, `t > 0`, and all `x y`,
        `IntervalIntegrable (fun s => ∫ z, C · baseKernelW κ 0 (t−s) x z · (C^k · iterKernelW κ 0 k s z y)) 0 t`.
    On `(0,t]` (minus the null endpoint `s = t`) the inner `z`-convolution collapses by
    `gaussDdim_conv` to `gaussDdim (κ·t) (x−y)` (widths add: `κ(t−s)+κs = κt`), and `iterKernelW_eq`
    supplies the `Γ`/time-power, so the map equals the `rpow`-integrable `const · s^(k−1)`; the
    endpoint `s = t` is a null set. -/
theorem modelS_intervalIntegrableW (κ C : ℝ) (hκ : 0 < κ) (k : ℕ) (hk : 1 ≤ k)
    (t : ℝ) (ht : 0 < t) (x y : Point n) :
    IntervalIntegrable
      (fun s => ∫ z, C * baseKernelW κ 0 (t - s) x z * (C ^ k * iterKernelW κ 0 k s z y))
      volume 0 t := by
  -- the continuous / `rpow`-integrable dominator on `[0,t]`
  have he1 : (-1 : ℝ) < (k : ℝ) * (0 + 1) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hg_ii : IntervalIntegrable
      (fun s => (C * C ^ k * (Real.Gamma (0 + 1) ^ k / Real.Gamma ((k : ℝ) * (0 + 1)))
                  * gaussDdim (κ * t) (x - y))
                * s ^ ((k : ℝ) * (0 + 1) - 1)) volume 0 t :=
    (intervalIntegral.intervalIntegrable_rpow' he1).const_mul _
  -- move to `IntegrableOn (Ioc 0 t)` and adjust on the null endpoint
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  have hg : IntegrableOn
      (fun s => (C * C ^ k * (Real.Gamma (0 + 1) ^ k / Real.Gamma ((k : ℝ) * (0 + 1)))
                  * gaussDdim (κ * t) (x - y))
                * s ^ ((k : ℝ) * (0 + 1) - 1)) (Set.Ioc 0 t) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]; exact hg_ii
  refine hg.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
  intro hmem
  obtain ⟨hs0, hsle⟩ := hmem
  have hsne : s ≠ t := by simpa using hst
  have hst2 : s < t := lt_of_le_of_ne hsle hsne
  have hts : 0 < t - s := by linarith
  have hform : (fun z => C * baseKernelW κ 0 (t - s) x z * (C ^ k * iterKernelW κ 0 k s z y))
      = fun z => (C * C ^ k
            * (Real.Gamma (0 + 1) ^ k / Real.Gamma ((k : ℝ) * (0 + 1)))
            * s ^ ((k : ℝ) * (0 + 1) - 1))
          * (gaussDdim (κ * (t - s)) (x - z) * gaussDdim (κ * s) (z - y)) := by
    funext z
    rw [baseKernelW_zero_apply, iterKernelW_eq κ 0 hκ (by norm_num) s hs0 z y hk]
    ring
  show (C * C ^ k * (Real.Gamma (0 + 1) ^ k / Real.Gamma ((k : ℝ) * (0 + 1)))
          * gaussDdim (κ * t) (x - y))
        * s ^ ((k : ℝ) * (0 + 1) - 1)
      = ∫ z, C * baseKernelW κ 0 (t - s) x z * (C ^ k * iterKernelW κ 0 k s z y)
  rw [hform, integral_const_mul,
      gaussDdim_conv (κ * (t - s)) (κ * s) (mul_pos hκ hts) (mul_pos hκ hs0) x y,
      show κ * (t - s) + κ * s = κ * t from by ring]
  ring

/-! ### 6. ★ The packaged model integrability (conjuncts (4) ∧ (5)). -/

/-- **★ THE MODEL-SIDE INTEGRABILITY (conjuncts (4) ∧ (5) of `IterConvIntegrableW E κ 0 C`),
    UNCONDITIONAL.**  For `κ > 0`, `α = 0`, every `k ≥ 1`, `t > 0`, and `x y`, both model conjuncts
    of the per-step integrability family hold — the last two of the five `IterConvIntegrableW`
    demands, discharged with no dependence on the residual `E`, the geometry, or the far-field /
    off-diagonal wall.  A later full discharge of `hInt : IterConvIntegrableW E 2 0 C` can cite this
    for its `(4)∧(5)` slots (combining it with the residual-side (1),(2),(3), which stay carried). -/
theorem iterConvIntegrableW_model (κ C : ℝ) (hκ : 0 < κ) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      (∀ s, Integrable
        (fun z => C * baseKernelW κ 0 (t - s) x z * (C ^ k * iterKernelW κ 0 k s z y))) ∧
      IntervalIntegrable
        (fun s => ∫ z, C * baseKernelW κ 0 (t - s) x z * (C ^ k * iterKernelW κ 0 k s z y))
        volume 0 t :=
  fun k hk t ht x y =>
    ⟨fun s => modelZ_integrableW κ C hκ k hk t ht x y s,
     modelS_intervalIntegrableW κ C hκ k hk t ht x y⟩

end QIQTH.HeatResidualBound
