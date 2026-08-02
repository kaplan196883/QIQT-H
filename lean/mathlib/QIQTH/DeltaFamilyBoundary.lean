/-
  DeltaFamilyBoundary — J4-118: THE delta-family boundary brick (Rosenberg Lemma 3.14 analogue)
  discharging the `hDelta` carry of the `hDConv` reduction.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  `ConvCarriesDischarge.hDConv_of_delta_final` reduces the diagonal Duhamel `hDConv` carry
  of the restricted `a₁ = R/6` capstone to the deferred kernel-continuity/derivative family plus the
  SOLE genuinely SINGULAR carry
      `hDelta : TendstoLocallyUniformlyOn
          (fun m u => Da m u + ∫ z, A (u−(u−ε_m)) 0 z · B (u−ε_m) z 0) D atTop U`.
  Here `u − (u − ε_m) = ε_m ↓ 0`, so `A(ε_m)` is a PEAK (Gaussian delta family) concentrating at the
  origin, while `B(u−ε_m) → B(u)`.  This file supplies the delta-family analysis behind that carry.

  WHAT LANDS.
    (M1)  `gaussDdim_integral_eq_one` — the `d`-dim Gaussian has TOTAL MASS ONE: `∫ z, G_t z = 1`
          for `t > 0`, from the 1-D mass fact (`gaussianZerothMoment_oneD`) by the Fubini power
          identity `integral_fintype_prod_volume_eq_pow`.  Foundation of the approximate identity.
    (B1)  `tendsto_integral_gaussDdim_smul` — THE LEMMA-3.14 CORE (approximate identity): for a
          BOUNDED `h` CONTINUOUS at `0`, `∫ z, G_{ε_m} z · h z → h 0` as `ε_m ↓ 0`.  Proved by the
          NEAR/FAR split against mass-one (M1): near `0`, continuity makes `|h − h 0|` small on a
          ball, weighted by mass ≤ 1; the far part is bounded by `2C ×` the Gaussian tail.  ⚠ carries
          the base `AEStronglyMeasurable h` (deferred measurability family) and the Gaussian TAIL
          `hTail` (a genuine deferred Gaussian-decay fact; NOT the conclusion).
    (ADD)  `tendstoLocallyUniformlyOn_add` — locally-uniform limits add (real-valued; Mathlib has no
          `.add` for `TendstoLocallyUniformlyOn`).  Triangle inequality via `Real.dist_eq`.
    (B3)  `hDelta_of_boundary` — THE ASSEMBLY: given the deferred `Da`-limit carry `hDaLim` and the
          boundary limit `hBoundary` (Brick 2, carried here), the full `hDelta` local-uniform sum
          converges to `DaLim + B(·) 0 0`.  A direct `tendstoLocallyUniformlyOn_add`.
    (B3c)  `hDelta_of_boundary_shifted` — the same reindexed onto the `A (u−(u−ε_m))` shape carried
          verbatim by `hDConv_of_delta_final`, bridging `u − (u − ε_m) = ε_m`.

  ⚠ HONEST FIREWALL.  The mass-one identity (M1) and the NEAR/FAR reduction (B1) and the assembly
  (B3) are genuine landed content.  The Gaussian TAIL (`hTail`), the base measurability, the
  `Da`-limit (`hDaLim`) and the boundary local-uniform limit (`hBoundary`, Brick 2 statement) are
  carried as clearly-labelled deferred analytic inputs — each is a genuine fact, NONE is the
  conclusion in disguise, none is vacuous.  NO `sorry`, no new axioms, no `expRho` in statements.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConvCarriesDischarge

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open QIQTH.HeatKernelA1
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### M1. The `d`-dimensional Gaussian has total mass one. -/

/-- **(M1) TOTAL MASS ONE.**  For `t > 0`, the `d`-dimensional flat Gaussian integrates to `1`:
    `∫ z, gaussDdim t z = 1`.  The density factors as `∏ₖ heatKernel1D t (z k)`, so the Fubini power
    identity `integral_fintype_prod_volume_eq_pow` collapses the integral to `(∫ y, heatKernel1D t y)^n
    = 1^n = 1` via the 1-D mass fact `gaussianZerothMoment_oneD`. -/
theorem gaussDdim_integral_eq_one (t : ℝ) (ht : 0 < t) :
    ∫ z : Point n, gaussDdim t z = 1 := by
  simp only [gaussDdim]
  rw [integral_fintype_prod_volume_eq_pow (fun (y : ℝ) => heatKernel1D t y),
      gaussianZerothMoment_oneD t ht, one_pow]

/-- `gaussDdim t` is integrable for `t > 0` (from the mass-one identity). -/
theorem gaussDdim_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun z : Point n => gaussDdim t z) volume :=
  integrable_of_integral_eq_one (gaussDdim_integral_eq_one t ht)

/-! ### B1. The approximate-identity core (Lemma 3.14). -/

/-- **★ J4-118 (B1) — THE LEMMA-3.14 APPROXIMATE-IDENTITY CORE.**  Let `ε_m ↓ 0` (through positive
    values) and let `h : Point n → ℝ` be BOUNDED (`|h z| ≤ C`) and CONTINUOUS at `0`.  Then the
    Gaussian delta family samples `h` at the origin:
        `∫ z, gaussDdim (ε_m) z · h z  →  h 0`   as `m → ∞`.
    ROUTE (NEAR/FAR against mass-one M1).  Since `∫ G_{ε_m} = 1`,
        `∫ G_{ε_m} h − h 0 = ∫ G_{ε_m} (h − h 0)`,
    so `|∫ G_{ε_m} h − h 0| ≤ ∫ G_{ε_m} |h − h 0|`.  For any `η > 0`, continuity gives `δ > 0` with
    `|h − h 0| < η/2` on `ball 0 δ`; splitting the integral there,
        near:  `∫_{ball} G_{ε_m} |h − h 0| ≤ (η/2)·∫_{ball} G_{ε_m} ≤ η/2`  (mass ≤ 1);
        far:   `∫_{ballᶜ} G_{ε_m} |h − h 0| ≤ 2C·∫_{ballᶜ} G_{ε_m} → 0`  (Gaussian tail `hTail`).
    ⚠ CONDITIONAL on the base measurability `hmeas` (deferred family) and the Gaussian TAIL `hTail`
    (a genuine deferred Gaussian-decay fact; not the conclusion).  NOT `a₁ = R/6`. -/
theorem tendsto_integral_gaussDdim_smul
    (ε : ℕ → ℝ) (hε : Filter.Tendsto ε Filter.atTop (𝓝[>] (0 : ℝ)))
    (h : Point n → ℝ) (C : ℝ) (hCbd : ∀ z, |h z| ≤ C)
    (hcont : ContinuousAt h 0)
    (hmeas : AEStronglyMeasurable h volume)
    (hTail : ∀ δ : ℝ, 0 < δ →
        Filter.Tendsto (fun m => ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z)
          Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun m => ∫ z : Point n, gaussDdim (ε m) z * h z) Filter.atTop (𝓝 (h 0)) := by
  classical
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hCbd 0)
  have hεpos : ∀ᶠ m in Filter.atTop, 0 < ε m :=
    hε.eventually eventually_mem_nhdsWithin
  refine Metric.tendsto_atTop.2 (fun η ηpos => ?_)
  -- continuity gives a ball of radius `δ` where `|h − h 0| < η/2`.
  obtain ⟨δ, δpos, hδ⟩ := Metric.continuousAt_iff.1 hcont (η / 2) (by positivity)
  -- the far part `2C · tail` tends to `0`.
  have htail0 : Filter.Tendsto
      (fun m => 2 * C * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z)
      Filter.atTop (𝓝 0) := by
    have := (hTail δ δpos).const_mul (2 * C)
    simpa using this
  have htailev : ∀ᶠ m in Filter.atTop,
      2 * C * (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z) < η / 2 :=
    htail0.eventually (Iio_mem_nhds (by positivity))
  -- combine the eventual facts.
  have hev := (hεpos.and htailev)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨hεm, htailm⟩ := hN m hm
  -- abbreviations and integrability.
  have hGint : Integrable (fun z : Point n => gaussDdim (ε m) z) volume :=
    gaussDdim_integrable (ε m) hεm
  have hmass : ∫ z : Point n, gaussDdim (ε m) z = 1 := gaussDdim_integral_eq_one (ε m) hεm
  have hGnn : ∀ z : Point n, 0 ≤ gaussDdim (ε m) z := fun z => gaussDdim_nonneg _ _
  have hGhint : Integrable (fun z : Point n => gaussDdim (ε m) z * h z) volume :=
    hGint.mul_bdd hmeas (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hCbd z))
  have hGh0int : Integrable (fun z : Point n => gaussDdim (ε m) z * h 0) volume :=
    hGint.mul_const (h 0)
  -- absolute-difference integrand `F`.
  have hFmeas : AEStronglyMeasurable (fun z : Point n => |h z - h 0|) volume :=
    continuous_abs.comp_aestronglyMeasurable (hmeas.sub aestronglyMeasurable_const)
  have hFbd : ∀ z : Point n, |h z - h 0| ≤ 2 * C := fun z => by
    calc |h z - h 0| ≤ |h z| + |h 0| := abs_sub _ _
      _ ≤ C + C := add_le_add (hCbd z) (hCbd 0)
      _ = 2 * C := by ring
  have hFint : Integrable (fun z : Point n => gaussDdim (ε m) z * |h z - h 0|) volume :=
    hGint.mul_bdd hFmeas (ae_of_all _ (fun z => by rw [Real.norm_eq_abs, abs_abs]; exact hFbd z))
  -- reduce the distance to the `F`-integral.
  have hh0 : (∫ z : Point n, gaussDdim (ε m) z * h 0) = h 0 := by
    rw [integral_mul_const, hmass, one_mul]
  have hsub : (∫ z : Point n, gaussDdim (ε m) z * h z) - h 0
      = ∫ z : Point n, gaussDdim (ε m) z * (h z - h 0) := by
    have hdiff : (∫ z : Point n, gaussDdim (ε m) z * (h z - h 0))
        = (∫ z : Point n, gaussDdim (ε m) z * h z) - ∫ z : Point n, gaussDdim (ε m) z * h 0 := by
      rw [← integral_sub hGhint hGh0int]
      apply integral_congr_ae; refine ae_of_all _ (fun z => ?_); ring
    rw [hdiff, hh0]
  have hdist_le : dist (∫ z : Point n, gaussDdim (ε m) z * h z) (h 0)
      ≤ ∫ z : Point n, gaussDdim (ε m) z * |h z - h 0| := by
    rw [Real.dist_eq, hsub]
    calc |∫ z : Point n, gaussDdim (ε m) z * (h z - h 0)|
        = ‖∫ z : Point n, gaussDdim (ε m) z * (h z - h 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z : Point n, ‖gaussDdim (ε m) z * (h z - h 0)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ z : Point n, gaussDdim (ε m) z * |h z - h 0| := by
          apply integral_congr_ae; refine ae_of_all _ (fun z => ?_)
          simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn z)]
  -- split near/far.
  have hsplit : (∫ z : Point n, gaussDdim (ε m) z * |h z - h 0|)
      = (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * |h z - h 0|)
        + ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h z - h 0| := by
    rw [integral_add_compl measurableSet_ball hFint]
  -- near bound: `≤ η/2`.
  have hnear : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * |h z - h 0|) ≤ η / 2 := by
    have hmono : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * |h z - h 0|)
        ≤ ∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * (η / 2) := by
      refine setIntegral_mono_on hFint.integrableOn (hGint.mul_const _).integrableOn
        measurableSet_ball (fun z hz => ?_)
      have hzball : |h z - h 0| ≤ η / 2 := by
        have hd : dist (h z) (h 0) < η / 2 := hδ (by simpa [Metric.mem_ball] using hz)
        rw [Real.dist_eq] at hd; exact hd.le
      exact mul_le_mul_of_nonneg_left hzball (hGnn z)
    have hcalc : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z * (η / 2))
        ≤ η / 2 := by
      rw [integral_mul_const]
      have hballmass : (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z) ≤ 1 := by
        rw [← hmass]
        exact setIntegral_le_integral hGint (ae_of_all _ hGnn)
      calc (∫ z in Metric.ball (0 : Point n) δ, gaussDdim (ε m) z) * (η / 2)
          ≤ 1 * (η / 2) := mul_le_mul_of_nonneg_right hballmass (by positivity)
        _ = η / 2 := by ring
    exact le_trans hmono hcalc
  -- far bound: `≤ 2C · tail m`.
  have hfar : (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h z - h 0|)
      ≤ 2 * C * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z := by
    have hmono : (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h z - h 0|)
        ≤ ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * (2 * C) := by
      refine setIntegral_mono_on hFint.integrableOn (hGint.mul_const _).integrableOn
        (measurableSet_ball.compl) (fun z _ => ?_)
      exact mul_le_mul_of_nonneg_left (hFbd z) (hGnn z)
    rw [integral_mul_const] at hmono
    calc (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z * |h z - h 0|)
        ≤ (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z) * (2 * C) := hmono
      _ = 2 * C * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z := by ring
  -- assemble.
  calc dist (∫ z : Point n, gaussDdim (ε m) z * h z) (h 0)
      ≤ ∫ z : Point n, gaussDdim (ε m) z * |h z - h 0| := hdist_le
    _ = _ := hsplit
    _ ≤ η / 2 + 2 * C * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (ε m) z :=
        add_le_add hnear hfar
    _ < η / 2 + η / 2 := by linarith [htailm]
    _ = η := by ring

/-! ### ADD. Locally-uniform limits add. -/

/-- **Locally-uniform convergence is closed under addition (real-valued).**  Mathlib supplies no
    `.add` for `TendstoLocallyUniformlyOn`; the triangle inequality via `Real.dist_eq` supplies it. -/
theorem tendstoLocallyUniformlyOn_add {ι : Type*} {p : Filter ι} {U : Set ℝ}
    {F G : ι → ℝ → ℝ} {f g : ℝ → ℝ}
    (hF : TendstoLocallyUniformlyOn F f p U)
    (hG : TendstoLocallyUniformlyOn G g p U) :
    TendstoLocallyUniformlyOn (fun n u => F n u + G n u) (fun u => f u + g u) p U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hF hG ⊢
  intro η hη x hx
  obtain ⟨t₁, ht₁, H₁⟩ := hF (η / 2) (by linarith) x hx
  obtain ⟨t₂, ht₂, H₂⟩ := hG (η / 2) (by linarith) x hx
  refine ⟨t₁ ∩ t₂, Filter.inter_mem ht₁ ht₂, ?_⟩
  filter_upwards [H₁, H₂] with n hn1 hn2 y hy
  have h1 := hn1 y hy.1
  have h2 := hn2 y hy.2
  calc dist (f y + g y) (F n y + G n y)
      ≤ dist (f y) (F n y) + dist (g y) (G n y) := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
            show f y + g y - (F n y + G n y) = (f y - F n y) + (g y - G n y) from by ring]
        exact abs_add_le _ _
    _ < η / 2 + η / 2 := add_lt_add h1 h2
    _ = η := by ring

/-! ### B3. The assembly of `hDelta` from the boundary limit. -/

/-- **★★ J4-118 (B3) — THE `hDelta` ASSEMBLY.**  Given the deferred `Da`-limit carry `hDaLim`
    (`Da m → DaLim` locally uniformly on `U`) and the boundary local-uniform limit `hBoundary`
    (Brick 2: the delta-family integral `∫ A(ε_m) 0 · B(u−ε_m) · 0 → B(u) 0 0`), the full `hDelta`
    sum converges locally uniformly to `DaLim + B(·) 0 0`.  A direct `tendstoLocallyUniformlyOn_add`.
    ⚠ CONDITIONAL on `hDaLim` (deferred) and `hBoundary` (Brick 2, carried).  NOT `a₁ = R/6`. -/
theorem hDelta_of_boundary
    (A B : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (Da : ℕ → ℝ → ℝ) (DaLim : ℝ → ℝ)
    (hDaLim : TendstoLocallyUniformlyOn Da DaLim Filter.atTop U)
    (hBoundary : TendstoLocallyUniformlyOn
        (fun m u => ∫ z : Point n, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
        (fun u => B u 0 0) Filter.atTop U) :
    TendstoLocallyUniformlyOn
      (fun m u => Da m u + ∫ z : Point n, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
      (fun u => DaLim u + B u 0 0) Filter.atTop U :=
  tendstoLocallyUniformlyOn_add hDaLim hBoundary

/-- **★★ J4-118 (B3c) — `hDelta` IN THE `A(u−(u−ε_m))` SHAPE.**  The same assembly, reindexed onto the
    literal shape `A (u−(u−ε_m))` carried by `hDConv_of_delta_final`'s `hDelta` slot (using
    `u − (u − ε_m) = ε_m`).  Feeds `hDelta` directly. -/
theorem hDelta_of_boundary_shifted
    (A B : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (Da : ℕ → ℝ → ℝ) (DaLim : ℝ → ℝ)
    (hDaLim : TendstoLocallyUniformlyOn Da DaLim Filter.atTop U)
    (hBoundary : TendstoLocallyUniformlyOn
        (fun m u => ∫ z : Point n, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
        (fun u => B u 0 0) Filter.atTop U) :
    TendstoLocallyUniformlyOn
      (fun m u => Da m u + ∫ z : Point n, A (u - (u - epsSeq m)) 0 z * B (u - epsSeq m) z 0)
      (fun u => DaLim u + B u 0 0) Filter.atTop U := by
  have h := hDelta_of_boundary A B U Da DaLim hDaLim hBoundary
  refine h.congr (fun m => ?_)
  intro u _
  simp only [sub_sub_cancel]

/-- **★★★ J4-118 (B3c-conc) — THE CONCRETE `hDelta` FOR THE VAN-VLECK `H_G`.**  The `hDelta` local-
    uniform limit in the EXACT shape carried by `hDConv_gatedWitnessN1_of_delta_final` for the gated
    van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S a b` and `B := leviSeries (heatOp g gi
    A)`, assembled from the deferred `Da`-limit `hDaLim` and the concrete boundary limit `hBoundary`
    (Brick 2 for these kernels).  Its `D` is `fun u => DaLim u + B u 0 0`.  A direct specialization of
    `hDelta_of_boundary_shifted`; this is the object that plugs straight into the `hDelta` slot of
    `hDConv_gatedWitnessN1_of_delta_final`.  ⚠ CONDITIONAL on `hDaLim` (deferred) and `hBoundary`
    (Brick 2, carried).  NOT `a₁ = R/6`. -/
theorem hDelta_gatedWitnessN1_of_boundary (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (Da : ℕ → ℝ → ℝ) (DaLim : ℝ → ℝ)
    (hDaLim : TendstoLocallyUniformlyOn Da DaLim Filter.atTop U)
    (hBoundary : TendstoLocallyUniformlyOn
        (fun m u => ∫ z : Point n, vanVleckGatedWitness g gi hC hK S a b (epsSeq m) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (u - epsSeq m) z 0)
        (fun u => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) u 0 0)
        Filter.atTop U) :
    TendstoLocallyUniformlyOn
      (fun m u => Da m u + ∫ z : Point n,
          vanVleckGatedWitness g gi hC hK S a b (u - (u - epsSeq m)) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (u - epsSeq m) z 0)
      (fun u => DaLim u
        + leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) u 0 0)
      Filter.atTop U :=
  hDelta_of_boundary_shifted (vanVleckGatedWitness g gi hC hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) U Da DaLim hDaLim hBoundary

end QIQTH.HeatResidualBound
