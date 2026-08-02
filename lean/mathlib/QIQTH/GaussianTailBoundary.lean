/-
  GaussianTailBoundary — J4-119: discharging the two carries of the delta-family brick.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  `DeltaFamilyBoundary` (J4-118) reduced the singular `hDelta` carry of the diagonal
  Duhamel `hDConv` chain to the approximate-identity core `tendsto_integral_gaussDdim_smul`, which
  itself carries TWO deferred inputs:
    • `hTail`  — the Gaussian tail vanishes: `∫_{ballᶜ} G_{ε_m} → 0`  (a genuine Gaussian-decay fact);
    • `hBoundary` (Brick 2) — the moving-peak concentration
        `∫ z, A(ε_m) 0 z · B(u−ε_m) z 0  →  B(u) 0 0`  LOCALLY UNIFORMLY in `u`.
  This file DISCHARGES both.

  WHAT LANDS.
    (T1)  `gaussDdim_tail_tendsto_zero` — THE `hTail` DISCHARGE.  On `Point n = Fin n → ℝ` with the
          Pi (sup) metric, `(ball 0 δ)ᶜ ⊆ ⋃ i {|z i| ≥ δ}`; a union bound + the Fubini product form
          factor each coordinate slab into the 1-D tail `∫_{|y|≥δ} G_t`, which is bounded by
          `√2·exp(−δ²/(8t))` (elementary Gaussian tail, `heatKernel1D_tail_le`) → 0 as `t = ε_m → 0`.
          UNCONDITIONAL: no carries.  Slots straight into `tendsto_integral_gaussDdim_smul`'s `hTail`.
    (T1★) `tendsto_integral_gaussDdim_smul_of_meas` — the Lemma-3.14 core with `hTail` GONE.
    (T2)  `tendsto_integral_gaussDdim_smul_family` — the EQUICONTINUOUS-FAMILY approximate identity:
          for a uniformly-bounded family `h m` with `h m → c` uniformly near `0` (`hEqui`), the
          Gaussian sampling converges: `∫ G_{ε_m}·h m → c`.  Same near/far split as J4-118, now with
          T1's tail available unconditionally.  Carries only base measurability `hmeas`.
    (T2u) `tendstoUniformlyOn_integral_gaussDdim_smul_family` — the PARAMETER-UNIFORM version over a
          type `ι` (all constants parameter-free), producing `TendstoUniformlyOn ... φ atTop K`.  This
          is the engine for the loc-unif boundary limit (T3): the boundary MAIN term is exactly a
          gaussDdim-sampling of `u ↦ u₀(z)·B(u−ε_m, z, 0)` over a compact time-slice `K`.

  ⚠ HONEST FIREWALL.
    LANDED (unconditional): the 1-D Gaussian tail bound (T1) and hence the FULL `hTail` discharge —
      `gaussDdim_tail_tendsto_zero` takes NO analytic carry, and slots straight into the `hTail` slot
      of `DeltaFamilyBoundary.tendsto_integral_gaussDdim_smul` (see `..._of_meas`).  So one of the two
      carries of J4-118 is closed outright.
    LANDED given base measurability: the family approximate identity (T2) and its parameter-uniform
      form (T2u) — these carry ONLY `hmeas`-type base measurability of the sampled family (the
      deferred measurability family, consistent with J4-118) and the uniform-approach input `hEqui`
      (a genuine equicontinuity fact, NOT the conclusion, non-vacuous).
    CARRIED / NOT YET IN THIS FILE: T3 (`hBoundary`, Brick 2) — the loc-uniform boundary limit is
      NOT discharged here.  T2u supplies its main-term engine, but the full 4-way split (main /
      `ε·u₁` / off-ball / mass-defect) with the `A`/`B` Gaussian dominations, the compact time-floor,
      and loc-unif-on-a-general-set reassembly remains the open frontier of this brick.  `hBoundary`
      therefore stays a labelled carry in `DeltaFamilyBoundary.hDelta_*_of_boundary`.
    NO `sorry`, no new axioms, no `expRho` in statements.  NOT `a₁ = R/6` — this closes the `hTail`
    carry outright and builds the T2/T2u engine for `hBoundary`; one brick of the campaign.
-/
import Mathlib
import QIQTH.DeltaFamilyBoundary

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open QIQTH.HeatKernelA1
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### T1. The Gaussian tail vanishes — the `hTail` discharge. -/

/-- **1-D GAUSSIAN TAIL BOUND.**  For `δ, t > 0`, the 1-D heat kernel's tail beyond `δ` is
    controlled by an elementary decaying bound:
        `∫_{|y| ≥ δ} G_t(y) dy ≤ √2 · exp(−δ²/(8t))`.
    ROUTE: on `{|y| ≥ δ}`, `−y²/(4t) ≤ −δ²/(8t) − y²/(8t)`, so
    `G_t(y) ≤ √2·exp(−δ²/(8t))·G_{2t}(y)` (the prefactor identity `√2·(√(8πt))⁻¹ = (√(4πt))⁻¹`);
    extend the set integral to all of `ℝ` (nonneg) and use `∫ G_{2t} = 1`. -/
theorem heatKernel1D_tail_le (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    ∫ y in {y : ℝ | δ ≤ |y|}, heatKernel1D t y ≤ Real.sqrt 2 * Real.exp (-(δ ^ 2) / (8 * t)) := by
  classical
  have htne : t ≠ 0 := ht.ne'
  set c : ℝ := Real.sqrt 2 * Real.exp (-(δ ^ 2) / (8 * t)) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hJmeas : MeasurableSet {y : ℝ | δ ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  -- prefactor identity
  have hpre : Real.sqrt 2 * (Real.sqrt (4 * Real.pi * (2 * t)))⁻¹
      = (Real.sqrt (4 * Real.pi * t))⁻¹ := by
    have h1 : 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) := by ring
    rw [h1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)), one_mul]
  -- pointwise bound on the tail set
  have hpt : ∀ y : ℝ, δ ≤ |y| → heatKernel1D t y ≤ c * heatKernel1D (2 * t) y := by
    intro y hy
    have hyy : δ ^ 2 ≤ y ^ 2 := by
      nlinarith [sq_abs y, mul_le_mul hy hy hδ.le (abs_nonneg y)]
    have harg : -y ^ 2 / (4 * t)
        ≤ -(δ ^ 2) / (8 * t) + -y ^ 2 / (4 * (2 * t)) := by
      have hdiff : -(δ ^ 2) / (8 * t) + -y ^ 2 / (4 * (2 * t)) - (-y ^ 2 / (4 * t))
          = (y ^ 2 - δ ^ 2) / (8 * t) := by field_simp; ring
      have hnn : (0 : ℝ) ≤ (y ^ 2 - δ ^ 2) / (8 * t) :=
        div_nonneg (by linarith) (by positivity)
      linarith [hdiff, hnn]
    have hexp : Real.exp (-y ^ 2 / (4 * t))
        ≤ Real.exp (-(δ ^ 2) / (8 * t)) * Real.exp (-y ^ 2 / (4 * (2 * t))) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr harg
    have hRHS : c * heatKernel1D (2 * t) y
        = (Real.sqrt (4 * Real.pi * t))⁻¹
            * (Real.exp (-(δ ^ 2) / (8 * t)) * Real.exp (-y ^ 2 / (4 * (2 * t)))) := by
      rw [hc, heatKernel1D, ← hpre]; ring
    rw [hRHS, heatKernel1D]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  -- integrability of the dominating function
  have hInt : Integrable (fun y => c * heatKernel1D (2 * t) y) volume :=
    (heatKernel1D_integrable (2 * t) (by linarith)).const_mul c
  calc ∫ y in {y : ℝ | δ ≤ |y|}, heatKernel1D t y
      ≤ ∫ y in {y : ℝ | δ ≤ |y|}, c * heatKernel1D (2 * t) y := by
        refine setIntegral_mono_on (heatKernel1D_integrable t ht).integrableOn
          hInt.integrableOn hJmeas (fun y hy => hpt y hy)
    _ ≤ ∫ y : ℝ, c * heatKernel1D (2 * t) y := by
        refine setIntegral_le_integral hInt (ae_of_all _ (fun y => ?_))
        exact mul_nonneg hc0 (heatKernel1D_pos (2 * t) y (by linarith)).le
    _ = c := by
        rw [integral_const_mul, gaussianZerothMoment_oneD (2 * t) (by linarith), mul_one]

/-- **COORDINATE SLAB = 1-D TAIL.**  The `d`-dim Gaussian mass over a single-coordinate slab
    `{z | δ ≤ |z i|}` equals the 1-D tail: `∫_{δ ≤ |z i|} G_t(z) = ∫_{δ ≤ |y|} G_t(y)`.  The
    indicator of the slab factors through the `i`-th coordinate, so the Fubini product form
    `integral_fintype_prod_volume_eq_prod` collapses all `j ≠ i` factors to `∫ G_t = 1`. -/
theorem slab_integral_eq_oneDim (δ t : ℝ) (ht : 0 < t) (i : Fin n) :
    ∫ z in {z : Point n | δ ≤ |z i|}, gaussDdim t z
      = ∫ y in {y : ℝ | δ ≤ |y|}, heatKernel1D t y := by
  classical
  have hJmeas : MeasurableSet {y : ℝ | δ ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hSimeas : MeasurableSet {z : Point n | δ ≤ |z i|} :=
    measurableSet_le measurable_const (measurable_pi_apply i).abs
  rw [← integral_indicator hSimeas]
  have hpt : ∀ z : Point n,
      {z : Point n | δ ≤ |z i|}.indicator (gaussDdim t) z
        = ∏ k, (fun (k' : Fin n) (y : ℝ) =>
            if k' = i then {y : ℝ | δ ≤ |y|}.indicator (heatKernel1D t) y
            else heatKernel1D t y) k (z k) := by
    intro z
    by_cases hz : z ∈ {z : Point n | δ ≤ |z i|}
    · rw [Set.indicator_of_mem hz]
      have hzi : z i ∈ {y : ℝ | δ ≤ |y|} := hz
      simp only [gaussDdim]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      by_cases hk : k = i
      · subst hk
        show heatKernel1D t (z k)
          = (if k = k then {y : ℝ | δ ≤ |y|}.indicator (heatKernel1D t) (z k)
             else heatKernel1D t (z k))
        rw [if_pos rfl, Set.indicator_of_mem hzi]
      · show heatKernel1D t (z k)
          = (if k = i then {y : ℝ | δ ≤ |y|}.indicator (heatKernel1D t) (z k)
             else heatKernel1D t (z k))
        rw [if_neg hk]
    · rw [Set.indicator_of_notMem hz]
      have hzi : z i ∉ {y : ℝ | δ ≤ |y|} := hz
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      show (if i = i then {y : ℝ | δ ≤ |y|}.indicator (heatKernel1D t) (z i)
            else heatKernel1D t (z i)) = 0
      rw [if_pos rfl, Set.indicator_of_notMem hzi]
  rw [integral_congr_ae (ae_of_all _ hpt),
      integral_fintype_prod_volume_eq_prod
        (fun (k' : Fin n) (y : ℝ) =>
          if k' = i then {y : ℝ | δ ≤ |y|}.indicator (heatKernel1D t) y
          else heatKernel1D t y)]
  have hcoord : ∀ k : Fin n,
      (∫ y : ℝ, if k = i then {y : ℝ | δ ≤ |y|}.indicator (heatKernel1D t) y
                else heatKernel1D t y)
        = (if k = i then (∫ y in {y : ℝ | δ ≤ |y|}, heatKernel1D t y) else 1) := by
    intro k
    by_cases hk : k = i
    · simp only [if_pos hk]; rw [integral_indicator hJmeas]
    · simp only [if_neg hk]; exact gaussianZerothMoment_oneD t ht
  rw [Finset.prod_congr rfl (fun k _ => hcoord k), Fintype.prod_ite_eq']

/-- **UNION-BOUND TAIL.**  The `d`-dim Gaussian mass outside the sup-ball is bounded by the sum of
    the single-coordinate slab masses: `∫_{(ball 0 δ)ᶜ} G_t ≤ ∑ i ∫_{δ ≤ |z i|} G_t`.  Uses
    `(ball 0 δ)ᶜ ⊆ ⋃ i {δ ≤ |z i|}` (the Pi sup-metric `dist_pi_lt_iff`) and the pointwise
    indicator estimate `indicator_{⋃} ≤ ∑ indicator`. -/
theorem tail_le_sum_slabs (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim t z
      ≤ ∑ i : Fin n, ∫ z in {z : Point n | δ ≤ |z i|}, gaussDdim t z := by
  classical
  have hGint : Integrable (fun z : Point n => gaussDdim t z) volume := gaussDdim_integrable t ht
  have hGnn : ∀ z : Point n, 0 ≤ gaussDdim t z := fun z => gaussDdim_nonneg t z
  have hSimeas : ∀ i : Fin n, MeasurableSet {z : Point n | δ ≤ |z i|} :=
    fun i => measurableSet_le measurable_const (measurable_pi_apply i).abs
  have hptind : ∀ z : Point n,
      (Metric.ball (0 : Point n) δ)ᶜ.indicator (gaussDdim t) z
        ≤ ∑ i : Fin n, ({z : Point n | δ ≤ |z i|}).indicator (gaussDdim t) z := by
    intro z
    by_cases hz : z ∈ (Metric.ball (0 : Point n) δ)ᶜ
    · rw [Set.indicator_of_mem hz]
      obtain ⟨j, hj⟩ : ∃ j : Fin n, δ ≤ |z j| := by
        by_contra hcon
        simp only [not_exists, not_le] at hcon
        apply hz
        simp only [Metric.mem_ball]
        rw [dist_pi_lt_iff hδ]
        intro b
        simp only [Pi.zero_apply, Real.dist_eq, sub_zero]
        exact hcon b
      have hzj : z ∈ {z : Point n | δ ≤ |z j|} := hj
      calc gaussDdim t z
          = ({z : Point n | δ ≤ |z j|}).indicator (gaussDdim t) z :=
            (Set.indicator_of_mem hzj _).symm
        _ ≤ ∑ i : Fin n, ({z : Point n | δ ≤ |z i|}).indicator (gaussDdim t) z :=
            Finset.single_le_sum
              (f := fun i : Fin n => ({z : Point n | δ ≤ |z i|}).indicator (gaussDdim t) z)
              (fun i _ => Set.indicator_nonneg (fun z _ => hGnn z) z) (Finset.mem_univ j)
    · rw [Set.indicator_of_notMem hz]
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun z _ => hGnn z) z)
  rw [← integral_indicator (measurableSet_ball.compl)]
  calc ∫ z, (Metric.ball (0 : Point n) δ)ᶜ.indicator (gaussDdim t) z
      ≤ ∫ z, ∑ i : Fin n, ({z : Point n | δ ≤ |z i|}).indicator (gaussDdim t) z := by
        refine integral_mono (hGint.indicator (measurableSet_ball.compl)) ?_ hptind
        exact integrable_finsetSum _ (fun i _ => hGint.indicator (hSimeas i))
    _ = ∑ i : Fin n, ∫ z, ({z : Point n | δ ≤ |z i|}).indicator (gaussDdim t) z :=
        integral_finsetSum _ (fun i _ => hGint.indicator (hSimeas i))
    _ = ∑ i : Fin n, ∫ z in {z : Point n | δ ≤ |z i|}, gaussDdim t z :=
        Finset.sum_congr rfl (fun i _ => integral_indicator (hSimeas i))

/-- **COMBINED d-DIM TAIL BOUND.**  `∫_{(ball 0 δ)ᶜ} G_t ≤ n · √2 · exp(−δ²/(8t))`. -/
theorem gaussDdim_tail_le (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim t z
      ≤ (n : ℝ) * (Real.sqrt 2 * Real.exp (-(δ ^ 2) / (8 * t))) := by
  calc ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim t z
      ≤ ∑ i : Fin n, ∫ z in {z : Point n | δ ≤ |z i|}, gaussDdim t z :=
        tail_le_sum_slabs δ t hδ ht
    _ = ∑ _i : Fin n, ∫ y in {y : ℝ | δ ≤ |y|}, heatKernel1D t y :=
        Finset.sum_congr rfl (fun i _ => slab_integral_eq_oneDim δ t ht i)
    _ ≤ ∑ _i : Fin n, Real.sqrt 2 * Real.exp (-(δ ^ 2) / (8 * t)) :=
        Finset.sum_le_sum (fun i _ => heatKernel1D_tail_le δ t hδ ht)
    _ = (n : ℝ) * (Real.sqrt 2 * Real.exp (-(δ ^ 2) / (8 * t))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **★ J4-119 (T1) — THE `hTail` DISCHARGE (UNCONDITIONAL).**  For any sequence `ε_m ↓ 0` (through
    positive values), the Gaussian tail outside every fixed ball vanishes:
        `∫_{(ball 0 δ)ᶜ} G_{ε_m} → 0`   as `m → ∞`,   for all `δ > 0`.
    Squeeze between `0` and `n·√2·exp(−δ²/(8 ε_m)) → 0` (`gaussDdim_tail_le`).  This is EXACTLY the
    shape of the `hTail` slot of `DeltaFamilyBoundary.tendsto_integral_gaussDdim_smul`, discharged
    with NO analytic carry. -/
theorem gaussDdim_tail_tendsto_zero (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ))) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun m => ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z)
        atTop (𝓝 0) := by
  intro δ hδ
  have hεpos : ∀ᶠ m in atTop, 0 < ε m := hε.eventually eventually_mem_nhdsWithin
  have hginv : Tendsto (fun m => (ε m)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp hε
  have hgbound : Tendsto (fun m => (n : ℝ) * (Real.sqrt 2 * Real.exp (-(δ ^ 2) / (8 * ε m))))
      atTop (𝓝 0) := by
    have harg : Tendsto (fun m => -(δ ^ 2) / (8 * ε m)) atTop atBot := by
      have hrw : (fun m => -(δ ^ 2) / (8 * ε m)) = (fun m => (-(δ ^ 2) / 8) * (ε m)⁻¹) := by
        funext m; ring
      rw [hrw]
      exact Tendsto.const_mul_atTop_of_neg (by have := pow_pos hδ 2; linarith) hginv
    have hexp0 : Tendsto (fun m => Real.exp (-(δ ^ 2) / (8 * ε m))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    have : Tendsto (fun m => (n : ℝ) * (Real.sqrt 2 * Real.exp (-(δ ^ 2) / (8 * ε m))))
        atTop (𝓝 ((n : ℝ) * (Real.sqrt 2 * 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hexp0)
    simpa using this
  refine squeeze_zero' ?_ ?_ hgbound
  · filter_upwards [hεpos] with m hm
    exact setIntegral_nonneg (measurableSet_ball.compl) (fun z _ => gaussDdim_nonneg (ε m) z)
  · filter_upwards [hεpos] with m hm
    exact gaussDdim_tail_le δ (ε m) hδ hm

/-! ### T1★. The Lemma-3.14 core with `hTail` discharged. -/

/-- **★ J4-119 (T1★) — LEMMA 3.14 WITH `hTail` GONE.**  The approximate-identity core
    `DeltaFamilyBoundary.tendsto_integral_gaussDdim_smul`, now UNCONDITIONAL on the Gaussian tail:
    for `ε_m ↓ 0` and `h` bounded, continuous at `0`, `∫ G_{ε_m}·h → h 0`.  The `hTail` slot is
    filled by T1.  Carries only the base measurability `hmeas`. -/
theorem tendsto_integral_gaussDdim_smul_of_meas
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (h : Point n → ℝ) (C : ℝ) (hCbd : ∀ z, |h z| ≤ C)
    (hcont : ContinuousAt h 0) (hmeas : AEStronglyMeasurable h volume) :
    Tendsto (fun m => ∫ z : Point n, gaussDdim (ε m) z * h z) atTop (𝓝 (h 0)) :=
  tendsto_integral_gaussDdim_smul ε hε h C hCbd hcont hmeas
    (gaussDdim_tail_tendsto_zero ε hε)

/-! ### T2. The equicontinuous-family approximate identity. -/

/-- **★★ J4-119 (T2) — THE FAMILY APPROXIMATE IDENTITY.**  Let `ε_m ↓ 0` and let `h m` be a family
    of `volume`-a.e.-measurable functions uniformly bounded by `C`.  If `h m → c` UNIFORMLY over a
    shrinking neighbourhood of the origin (`hEqui`: for every `η` there is a ball on which, eventually
    in `m`, `|h m − c| ≤ η`), then the Gaussian delta family samples the common limit:
        `∫ z, G_{ε_m} z · h m z  →  c`.
    Proof = the J4-118 near/far split against mass-one, with the tail (T1) now unconditional and the
    near part controlled by `hEqui` instead of pointwise continuity.  Carries only base measurability
    `hmeas`.  NOT `a₁ = R/6`. -/
theorem tendsto_integral_gaussDdim_smul_family
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (h : ℕ → Point n → ℝ) (C : ℝ) (hCbd : ∀ m z, |h m z| ≤ C)
    (hmeas : ∀ m, AEStronglyMeasurable (h m) volume)
    (c : ℝ)
    (hEqui : ∀ η > 0, ∃ δ > 0, ∀ᶠ m in atTop,
        ∀ z ∈ Metric.ball (0 : Point n) δ, |h m z - c| ≤ η) :
    Tendsto (fun m => ∫ z : Point n, gaussDdim (ε m) z * h m z) atTop (𝓝 c) := by
  classical
  refine Metric.tendsto_atTop.2 (fun η ηpos => ?_)
  obtain ⟨δ, δpos, hδev⟩ := hEqui (η / 2) (by linarith)
  have hεpos : ∀ᶠ m in atTop, 0 < ε m := hε.eventually eventually_mem_nhdsWithin
  set B : ℝ := C + |c| with hB
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (h 0 0)) (hCbd 0 0)
  have hB0 : 0 ≤ B := by rw [hB]; exact add_nonneg hC0 (abs_nonneg c)
  have htail0 : Tendsto
      (fun m => B * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z) atTop (𝓝 0) := by
    have := (gaussDdim_tail_tendsto_zero (n := n) ε hε δ δpos).const_mul B
    simpa using this
  have htailev : ∀ᶠ m in atTop,
      B * (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z) < η / 2 :=
    htail0.eventually (Iio_mem_nhds (by linarith))
  have hcomb : ∀ᶠ m in atTop, dist (∫ z : Point n, gaussDdim (ε m) z * h m z) c < η := by
    filter_upwards [hεpos, htailev, hδev] with m hεm htailm hnearm
    have hGint : Integrable (fun z : Point n => gaussDdim (ε m) z) volume :=
      gaussDdim_integrable (ε m) hεm
    have hmass : ∫ z : Point n, gaussDdim (ε m) z = 1 := gaussDdim_integral_eq_one (ε m) hεm
    have hGnn : ∀ z : Point n, 0 ≤ gaussDdim (ε m) z := fun z => gaussDdim_nonneg _ _
    have hGhint : Integrable (fun z : Point n => gaussDdim (ε m) z * h m z) volume :=
      hGint.mul_bdd (hmeas m) (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hCbd m z))
    have hGh0int : Integrable (fun z : Point n => gaussDdim (ε m) z * c) volume :=
      hGint.mul_const c
    have hFmeas : AEStronglyMeasurable (fun z : Point n => |h m z - c|) volume :=
      continuous_abs.comp_aestronglyMeasurable ((hmeas m).sub aestronglyMeasurable_const)
    have hFbd : ∀ z : Point n, |h m z - c| ≤ B := fun z => by
      calc |h m z - c| ≤ |h m z| + |c| := abs_sub _ _
        _ ≤ C + |c| := by linarith [hCbd m z]
    have hFint : Integrable (fun z : Point n => gaussDdim (ε m) z * |h m z - c|) volume :=
      hGint.mul_bdd hFmeas (ae_of_all _ (fun z => by rw [Real.norm_eq_abs, abs_abs]; exact hFbd z))
    have hh0 : (∫ z : Point n, gaussDdim (ε m) z * c) = c := by
      rw [integral_mul_const, hmass, one_mul]
    have hsub : (∫ z : Point n, gaussDdim (ε m) z * h m z) - c
        = ∫ z : Point n, gaussDdim (ε m) z * (h m z - c) := by
      have hdiff : (∫ z : Point n, gaussDdim (ε m) z * (h m z - c))
          = (∫ z : Point n, gaussDdim (ε m) z * h m z)
            - ∫ z : Point n, gaussDdim (ε m) z * c := by
        rw [← integral_sub hGhint hGh0int]
        apply integral_congr_ae; refine ae_of_all _ (fun z => ?_); ring
      rw [hdiff, hh0]
    have hdist_le : dist (∫ z : Point n, gaussDdim (ε m) z * h m z) c
        ≤ ∫ z : Point n, gaussDdim (ε m) z * |h m z - c| := by
      rw [Real.dist_eq, hsub]
      calc |∫ z : Point n, gaussDdim (ε m) z * (h m z - c)|
          = ‖∫ z : Point n, gaussDdim (ε m) z * (h m z - c)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ z : Point n, ‖gaussDdim (ε m) z * (h m z - c)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ z : Point n, gaussDdim (ε m) z * |h m z - c| := by
            apply integral_congr_ae; refine ae_of_all _ (fun z => ?_)
            simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn z)]
    have hsplit : (∫ z : Point n, gaussDdim (ε m) z * |h m z - c|)
        = (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * |h m z - c|)
          + ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h m z - c| := by
      rw [integral_add_compl measurableSet_ball hFint]
    have hnear : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * |h m z - c|)
        ≤ η / 2 := by
      have hmono : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * |h m z - c|)
          ≤ ∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * (η / 2) := by
        refine setIntegral_mono_on hFint.integrableOn (hGint.mul_const _).integrableOn
          measurableSet_ball (fun z hz => ?_)
        exact mul_le_mul_of_nonneg_left (hnearm z hz) (hGnn z)
      have hcalc : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * (η / 2)) ≤ η / 2 := by
        rw [integral_mul_const]
        have hballmass : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z) ≤ 1 := by
          rw [← hmass]; exact setIntegral_le_integral hGint (ae_of_all _ hGnn)
        calc (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z) * (η / 2)
            ≤ 1 * (η / 2) := mul_le_mul_of_nonneg_right hballmass (by linarith)
          _ = η / 2 := by ring
      exact le_trans hmono hcalc
    have hfar : (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h m z - c|)
        ≤ B * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z := by
      have hmono : (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h m z - c|)
          ≤ ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * B := by
        refine setIntegral_mono_on hFint.integrableOn (hGint.mul_const _).integrableOn
          measurableSet_ball.compl (fun z _ => ?_)
        exact mul_le_mul_of_nonneg_left (hFbd z) (hGnn z)
      rw [integral_mul_const] at hmono
      calc (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h m z - c|)
          ≤ (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z) * B := hmono
        _ = B * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z := by ring
    calc dist (∫ z : Point n, gaussDdim (ε m) z * h m z) c
        ≤ ∫ z : Point n, gaussDdim (ε m) z * |h m z - c| := hdist_le
      _ = _ := hsplit
      _ ≤ η / 2 + B * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z :=
          add_le_add hnear hfar
      _ < η / 2 + η / 2 := by linarith [htailm]
      _ = η := by ring
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcomb
  exact ⟨N, hN⟩

/-! ### T2u. The parameter-uniform family approximate identity. -/

/-- **★★ J4-119 (T2u) — THE PARAMETER-UNIFORM FAMILY APPROXIMATE IDENTITY.**  The workhorse for the
    loc-uniform boundary limit.  Over an arbitrary parameter set `K ⊆ ι`, if the sampled family
    `h m p` is uniformly bounded by `C` and converges to `φ p` UNIFORMLY over `K` on a shrinking
    origin-neighbourhood (`hEqui`, uniform in `p`), then the Gaussian sampling converges UNIFORMLY on
    `K`:
        `TendstoUniformlyOn (fun m p => ∫ z, G_{ε_m} z · h m p z) φ atTop K`.
    Same near/far split as T2 with all constants parameter-free; the near part uses the `p`-uniform
    `hEqui`.  Carries only base measurability `hmeas`.  NOT `a₁ = R/6`. -/
theorem tendstoUniformlyOn_integral_gaussDdim_smul_family
    {ι : Type*} (K : Set ι)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (h : ℕ → ι → Point n → ℝ) (C : ℝ) (hCbd : ∀ m p z, |h m p z| ≤ C)
    (hmeas : ∀ m p, AEStronglyMeasurable (h m p) volume)
    (φ : ι → ℝ) (hφbd : ∀ p ∈ K, |φ p| ≤ C)
    (hEqui : ∀ η > 0, ∃ δ > 0, ∀ᶠ m in atTop,
        ∀ p ∈ K, ∀ z ∈ Metric.ball (0 : Point n) δ, |h m p z - φ p| ≤ η) :
    TendstoUniformlyOn (fun m p => ∫ z : Point n, gaussDdim (ε m) z * h m p z) φ atTop K := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro η ηpos
  obtain ⟨δ, δpos, hδev⟩ := hEqui (η / 2) (by linarith)
  have hεpos : ∀ᶠ m in atTop, 0 < ε m := hε.eventually eventually_mem_nhdsWithin
  set B : ℝ := 2 * C with hB
  have htail0 : Tendsto
      (fun m => B * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z) atTop (𝓝 0) := by
    have := (gaussDdim_tail_tendsto_zero (n := n) ε hε δ δpos).const_mul B
    simpa using this
  have htailev : ∀ᶠ m in atTop,
      B * (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z) < η / 2 :=
    htail0.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hεpos, htailev, hδev] with m hεm htailm hnearm
  intro p hp
  rw [dist_comm]
  -- reduce to the T2 bound with `c := φ p`, `B := 2C`
  have hGint : Integrable (fun z : Point n => gaussDdim (ε m) z) volume :=
    gaussDdim_integrable (ε m) hεm
  have hmass : ∫ z : Point n, gaussDdim (ε m) z = 1 := gaussDdim_integral_eq_one (ε m) hεm
  have hGnn : ∀ z : Point n, 0 ≤ gaussDdim (ε m) z := fun z => gaussDdim_nonneg _ _
  have hGhint : Integrable (fun z : Point n => gaussDdim (ε m) z * h m p z) volume :=
    hGint.mul_bdd (hmeas m p) (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hCbd m p z))
  have hGh0int : Integrable (fun z : Point n => gaussDdim (ε m) z * φ p) volume :=
    hGint.mul_const (φ p)
  have hFmeas : AEStronglyMeasurable (fun z : Point n => |h m p z - φ p|) volume :=
    continuous_abs.comp_aestronglyMeasurable ((hmeas m p).sub aestronglyMeasurable_const)
  have hFbd : ∀ z : Point n, |h m p z - φ p| ≤ B := fun z => by
    calc |h m p z - φ p| ≤ |h m p z| + |φ p| := abs_sub _ _
      _ ≤ C + C := add_le_add (hCbd m p z) (hφbd p hp)
      _ = B := by rw [hB]; ring
  have hFint : Integrable (fun z : Point n => gaussDdim (ε m) z * |h m p z - φ p|) volume :=
    hGint.mul_bdd hFmeas (ae_of_all _ (fun z => by rw [Real.norm_eq_abs, abs_abs]; exact hFbd z))
  have hh0 : (∫ z : Point n, gaussDdim (ε m) z * φ p) = φ p := by
    rw [integral_mul_const, hmass, one_mul]
  have hsub : (∫ z : Point n, gaussDdim (ε m) z * h m p z) - φ p
      = ∫ z : Point n, gaussDdim (ε m) z * (h m p z - φ p) := by
    have hdiff : (∫ z : Point n, gaussDdim (ε m) z * (h m p z - φ p))
        = (∫ z : Point n, gaussDdim (ε m) z * h m p z)
          - ∫ z : Point n, gaussDdim (ε m) z * φ p := by
      rw [← integral_sub hGhint hGh0int]
      apply integral_congr_ae; refine ae_of_all _ (fun z => ?_); ring
    rw [hdiff, hh0]
  have hdist_le : dist (∫ z : Point n, gaussDdim (ε m) z * h m p z) (φ p)
      ≤ ∫ z : Point n, gaussDdim (ε m) z * |h m p z - φ p| := by
    rw [Real.dist_eq, hsub]
    calc |∫ z : Point n, gaussDdim (ε m) z * (h m p z - φ p)|
        = ‖∫ z : Point n, gaussDdim (ε m) z * (h m p z - φ p)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z : Point n, ‖gaussDdim (ε m) z * (h m p z - φ p)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ z : Point n, gaussDdim (ε m) z * |h m p z - φ p| := by
          apply integral_congr_ae; refine ae_of_all _ (fun z => ?_)
          simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn z)]
  have hsplit : (∫ z : Point n, gaussDdim (ε m) z * |h m p z - φ p|)
      = (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * |h m p z - φ p|)
        + ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h m p z - φ p| := by
    rw [integral_add_compl measurableSet_ball hFint]
  have hnear : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * |h m p z - φ p|)
      ≤ η / 2 := by
    have hmono : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * |h m p z - φ p|)
        ≤ ∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * (η / 2) := by
      refine setIntegral_mono_on hFint.integrableOn (hGint.mul_const _).integrableOn
        measurableSet_ball (fun z hz => ?_)
      exact mul_le_mul_of_nonneg_left (hnearm p hp z hz) (hGnn z)
    have hcalc : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * (η / 2)) ≤ η / 2 := by
      rw [integral_mul_const]
      have hballmass : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z) ≤ 1 := by
        rw [← hmass]; exact setIntegral_le_integral hGint (ae_of_all _ hGnn)
      calc (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z) * (η / 2)
          ≤ 1 * (η / 2) := mul_le_mul_of_nonneg_right hballmass (by linarith)
        _ = η / 2 := by ring
    exact le_trans hmono hcalc
  have hfar : (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h m p z - φ p|)
      ≤ B * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z := by
    have hmono : (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h m p z - φ p|)
        ≤ ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * B := by
      refine setIntegral_mono_on hFint.integrableOn (hGint.mul_const _).integrableOn
        measurableSet_ball.compl (fun z _ => ?_)
      exact mul_le_mul_of_nonneg_left (hFbd z) (hGnn z)
    rw [integral_mul_const] at hmono
    calc (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h m p z - φ p|)
        ≤ (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z) * B := hmono
      _ = B * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z := by ring
  calc dist (∫ z : Point n, gaussDdim (ε m) z * h m p z) (φ p)
      ≤ ∫ z : Point n, gaussDdim (ε m) z * |h m p z - φ p| := hdist_le
    _ = _ := hsplit
    _ ≤ η / 2 + B * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z :=
        add_le_add hnear hfar
    _ < η / 2 + η / 2 := by linarith [htailm]
    _ = η := by ring

end QIQTH.HeatResidualBound

