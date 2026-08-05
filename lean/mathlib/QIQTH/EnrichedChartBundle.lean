/-
  EnrichedChartBundle — J4-278: the ENRICHED base-varying change-of-variables bundle and the
  Layer-C `hbound`/`hlocal` discharge — shrinking the W1 fixed-`f` chart-image approximate-identity
  carry list from FOUR (`hGgate`, `hSupp`, `hbound`, `hlocal`) to TWO (`hGgate`, `hSupp`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the W1 wall of the a₁ = R/6 campaign).  `QIQTH.FixedFTrioDischarge.chartImage_approx_
  identity_v2` (J4-277) is the fixed-`f` W1 capstone; it discharged the measurability member (C3)
  but still CARRIED `hbound`/`hlocal` (C4/C5).  Those two need, over the WHOLE chart image
  `Ω := Wbv '' ball 0 ρ`, a uniform amplitude sup-bound and a uniform Jacobian lower bound, plus the
  inverse-continuity facts `V w → 0` and `|det (f' (V w))| → 1` as `w → 0`.  The J4-274 bundle
  `baseVaryingIFTPackage_unconditional` exposes `f'` only POINTWISE and gives NO continuity of the
  inverse `V` on `Ω`, so the composition could not be closed.  The precise diagnosis: an ENRICHED
  bundle that ALSO exports (i) `V`'s continuity on `Ω`, (ii) the centre value `V 0 = 0`, (iii) the
  pin `f' = fderiv Wbv` and a uniform Jacobian lower bound, and (iv) the det-continuity/normalisation
  at the centre — is needed.

  ── WHAT LANDS HERE (honest composition; the ★ DISCHARGES).
    • `enrichedChartBundle` — ★★ THE ENRICHED BUNDLE.  Re-runs the J4-272
      `ContDiffAt.toOpenPartialHomeomorph` construction (unconditionally, via the J4-274 entry points
      `terminalVel0_contDiffAt_two` + `hbaseC2_of_terminalVel_contDiffAt`), but this time PROJECTS OUT
      the extra facts the partial homeomorph already contains: the inverse's continuity on `Ω`
      (`Φ.continuousOn_symm` restricted to `Ω ⊆ Φ.target`), the openness of `Ω`, the centre value
      `V 0 = 0`, the derivative pin `f' = fderiv Wbv`, a uniform Jacobian lower bound `1/2 < |det f'|`
      on the ball, and the det-continuity `ContinuousAt |det (fderiv Wbv ·)| 0` with normalisation
      `|det (fderiv Wbv 0)| = 1` (the centre derivative is `-id`, whose determinant is `(-1)ⁿ`).
      Crucially it takes a CAP parameter `ρcap` and guarantees `ρ ≤ ρcap` — this is the ρ-choice that
      lets the caller shrink the bundle radius under any externally-obtained amplitude/Jacobian radius.
    • `bundleV_tendsto_zero`, `bundleDet_tendsto_one` — ★ the two inverse-limit wrappers:
      `V w → 0` and `|det (f' (V w))| → 1` as `w → 0` within `Ω`, from the enriched exports.
    • `chartImage_approx_identity_v3` — ★★ THE v3 CAPSTONE.  Same fixed-`f` W1 limit as v2, but with
      `hbound` AND `hlocal` DISCHARGED, so the carry list is only `hGgate` and `hSupp`.  Route: obtain
      the amplitude sup-bound radius `ρA` (`baseSlotAmp_bound`), build the enriched bundle capped at
      `ρA` (so `V (Ω) ⊆ ball 0 ρ ⊆ closedBall 0 ρA`), then:
        – `hbound` from `baseSlotAmp_bound` (‖amp‖ ≤ CA on `closedBall 0 ρA`) + `|f| ≤ Cf` (carried) +
          the uniform Jacobian lower bound `1/2 < |det f'|` (enriched);
        – `hlocal` from the product-filter limit `amp · f / |det| → A₀ · f0 / 1 = f0`, assembled from
          `baseSlotAmp_joint_limit`, `bundleV_tendsto_zero`, `bundleDet_tendsto_one`, `f`-continuity at
          `0`, and the normalisation `A₀ = 1` (`baseChartAmp_centre_eq_one`, given `det g 0 = 1`), then
          unpacked into the `∀ε ∃r ∀ᶠτ ∀ᵐw` shape via `eventually_prod_iff` + `mem_nhdsWithin_iff`.

  ── THE FINAL CARRY LIST of `chartImage_approx_identity_v3` (for the produced `(ρ, V, f')`).  TWO
     genuine, simultaneously-satisfiable inputs (the annulus/gate split, obstruction (B)):
       (C1) `hGgate` — the witness gate is active on `ball 0 ρ`;
       (C2) `hSupp`  — the witness vanishes off `ball 0 ρ`, τ-uniformly.
     Plus the STANDING carries (each strictly weaker than the Tendsto, each satisfiable): the metric
     regularity/positivity `{hg, hgi, hgpos}` (the RNC metric `δ` has them), the gauge normalisation
     `det g 0 = 1` (RNC), `f` measurable + globally bounded + continuous at `0`, and `0 < a < b`.

  ── HONEST RESIDUAL (what is NOT done here, and WHY).
    • Obstruction (B), the `hSupp` gate-vs-CoV ball/annulus split, is UNCHANGED and remains carried —
      a SEPARATE thread (the `WideBoundaryLimDischarge` split), not addressed here.
    • `hbound` requires `f` GLOBALLY bounded (`|f x| ≤ Cf`); `hlocal` requires `f` continuous at `0`
      and the gauge `det g 0 = 1`.  These are the standard approximate-identity inputs — the sampled
      test function is bounded and continuous at the concentration point, and the RNC gauge is the
      metric normalisation the repo already carries elsewhere.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  These are analytic composition
  bricks (an enriched change-of-variables package + a bounded/continuous approximate-identity
  discharge).  No `sorry` (prose only), no new axioms, no `:= True`, no vacuous / unsatisfiable /
  conclusion-in-disguise hypotheses: the enriched exports are all PROVEN by the partial-homeomorph
  construction (not assumed), and the discharged `hbound`/`hlocal` are removed from the surface.  The
  remaining carries (`hGgate`, `hSupp`, the metric carries, `det g 0 = 1`, `f`-boundedness/continuity,
  `0 < a < b`) are each strictly weaker than the Tendsto conclusion.  No existing file is edited.
-/
import Mathlib
import QIQTH.FixedFTrioDischarge
import QIQTH.BaseVaryingIFTPackage

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.EnrichedChartBundle

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The enriched base-varying change-of-variables bundle (with a radius cap). -/

/-- **★★ `enrichedChartBundle` — the ENRICHED base-varying CoV bundle, UNCONDITIONAL, capped.**
    Re-runs the `ContDiffAt.toOpenPartialHomeomorph` construction of `baseVaryingIFTPackage`
    (unconditionally, via `terminalVel0_contDiffAt_two` + `hbaseC2_of_terminalVel_contDiffAt`) and
    additionally exports:
      • `ContinuousOn V Ω`  (the inverse `V = Φ.symm` is continuous on `Ω := Wbv '' ball 0 ρ`);
      • `IsOpen Ω`;
      • `V 0 = 0`  (the centre value);
      • `f' = fderiv ℝ Wbv` on the ball  (the derivative pin);
      • `1/2 < |det (f' ·)|` on the ball  (a uniform Jacobian lower bound);
      • `ContinuousAt (|det (fderiv Wbv ·)|) 0` and `|det (fderiv Wbv 0)| = 1`  (the centre derivative
        is `-id`, whose determinant is `(-1)ⁿ` of modulus `1`).
    The CAP `ρ ≤ ρcap` lets the caller pre-commit the bundle radius under any externally-obtained
    amplitude/Jacobian radius (the ρ-choice that closes `hbound`/`hlocal`).  M2/M3 and all enrichments
    are PROVEN, not assumed.  NOT `a₁ = R/6`. -/
theorem enrichedChartBundle (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (ρcap : ℝ) (hρcap : 0 < ρcap) :
    ∃ ρ > (0 : ℝ), ρ ≤ ρcap ∧
      ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
        MeasurableSet (Metric.ball (0 : Point n) ρ)
        ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
            HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
              (Metric.ball (0 : Point n) ρ) z)
        ∧ Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ)
        ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
            V (uniformInverseChart g gi hC hK z 0) = z)
        ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
        ∧ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)
            ∈ 𝓝 (0 : Point n)
        ∧ ContinuousOn V
            ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))
        ∧ IsOpen
            ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))
        ∧ V 0 = 0
        ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
            f' z = fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z)
        ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ, (1 : ℝ) / 2 < |(f' z).det|)
        ∧ ContinuousAt
            (fun y => |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) y).det|)
            (0 : Point n)
        ∧ |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)).det| = 1 := by
  classical
  set Wbv : Point n → Point n := fun z => uniformInverseChart g gi hC hK z 0 with hWbvdef
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  have hWbv0 : Wbv 0 = 0 := uniformInverseChart_zero g gi hC hK h0K
  have hbaseC2 : ContDiffAt ℝ 2 Wbv 0 :=
    QIQTH.GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt g gi hC hK h0Kmem
      (QIQTH.TerminalVelC2.terminalVel0_contDiffAt_two g gi hC hK h0K)
  set e : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.neg ℝ with hedef
  have hW'0 : HasFDerivAt Wbv ((e : Point n →L[ℝ] Point n)) 0 := by
    rw [hWbvdef, hedef]
    exact QIQTH.BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center g gi hC hK h0Kmem
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hfderiv0 : fderiv ℝ Wbv 0 = (e : Point n →L[ℝ] Point n) := hW'0.fderiv
  set Φ := hbaseC2.toOpenPartialHomeomorph Wbv hW'0 hn2 with hΦdef
  have hΦcoe : (⇑Φ : Point n → Point n) = Wbv := by
    rw [hΦdef]; exact hbaseC2.toOpenPartialHomeomorph_coe hW'0 hn2
  have h0src : (0 : Point n) ∈ Φ.source := by
    rw [hΦdef]; exact hbaseC2.mem_toOpenPartialHomeomorph_source hW'0 hn2
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.isOpen_iff.mp Φ.open_source 0 h0src
  have hevC2 : ∀ᶠ y in 𝓝 (0 : Point n), ContDiffAt ℝ 2 Wbv y := hbaseC2.eventually (by norm_num)
  have hevdiff : ∀ᶠ y in 𝓝 (0 : Point n), DifferentiableAt ℝ Wbv y :=
    hevC2.mono (fun _ hy => hy.differentiableAt (by norm_num))
  have hfderiv_cont : ContinuousAt (fun y => fderiv ℝ Wbv y) 0 :=
    (hbaseC2.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hdetabs_cont : ContinuousAt (fun y => |(fderiv ℝ Wbv y).det|) 0 :=
    (continuous_abs.continuousAt).comp
      ((ContinuousLinearMap.continuous_det.continuousAt).comp hfderiv_cont)
  -- The centre determinant is `det (-id) = (-1)ⁿ`, of modulus `1`.
  have hdet0val : |(fderiv ℝ Wbv 0).det| = 1 := by
    rw [hfderiv0]
    have hcoe : (e : Point n →L[ℝ] Point n) = -ContinuousLinearMap.id ℝ (Point n) := by
      ext x; simp [hedef]
    rw [hcoe]
    have hL : (((-ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n) = (-1 : ℝ) • LinearMap.id := by ext x; simp
    show |LinearMap.det (((-ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n)| = 1
    rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one, abs_pow]
    norm_num
  have hdet0abs : (0 : ℝ) < |(fderiv ℝ Wbv 0).det| := by rw [hdet0val]; norm_num
  have hevdet : ∀ᶠ y in 𝓝 (0 : Point n),
      |(fderiv ℝ Wbv 0).det| / 2 < |(fderiv ℝ Wbv y).det| :=
    hdetabs_cont.tendsto.eventually (eventually_gt_nhds (by linarith [hdet0abs]))
  obtain ⟨ε, hε, hεspec⟩ := Metric.eventually_nhds_iff.mp (hevdiff.and hevdet)
  set ρ := min (min δ₁ ε) ρcap with hρdef
  have hρpos : 0 < ρ := lt_min (lt_min hδ₁ hε) hρcap
  have hρδ : ρ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρε : ρ ≤ ε := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρcap' : ρ ≤ ρcap := min_le_right _ _
  have hballsrc : Metric.ball (0 : Point n) ρ ⊆ Φ.source :=
    fun z hz => hδ₁sub (Metric.ball_subset_ball hρδ hz)
  have h0ball : (0 : Point n) ∈ Metric.ball (0 : Point n) ρ := Metric.mem_ball_self hρpos
  have hΩsub : Wbv '' Metric.ball (0 : Point n) ρ ⊆ Φ.target := by
    rintro w ⟨z, hz, rfl⟩
    have hcz : (⇑Φ : Point n → Point n) z = Wbv z := congrFun hΦcoe z
    rw [← hcz]
    exact Φ.map_source (hballsrc hz)
  have hopen : IsOpen (Wbv '' Metric.ball (0 : Point n) ρ) := by
    have h := Φ.isOpen_image_of_subset_source Metric.isOpen_ball hballsrc
    rwa [hΦcoe] at h
  have hΩnhds : Wbv '' Metric.ball (0 : Point n) ρ ∈ 𝓝 (0 : Point n) :=
    hopen.mem_nhds ⟨0, h0ball, hWbv0⟩
  have hV0 : (⇑Φ.symm : Point n → Point n) 0 = 0 := by
    have h := Φ.left_inv (hballsrc h0ball)
    have hcz0 : (⇑Φ : Point n → Point n) 0 = 0 := by rw [congrFun hΦcoe 0]; exact hWbv0
    rw [hcz0] at h; exact h
  refine ⟨ρ, hρpos, hρcap', (⇑Φ.symm : Point n → Point n), (fun z => fderiv ℝ Wbv z),
    measurableSet_ball, ?_, ?_, ?_, ?_, hΩnhds, ?_, hopen, hV0, ?_, ?_, hdetabs_cont, hdet0val⟩
  · -- M1: within-derivative field.
    intro z hz
    have hzε : dist z (0 : Point n) < ε := lt_of_lt_of_le (Metric.mem_ball.mp hz) hρε
    exact ((hεspec hzε).1.hasFDerivAt).hasFDerivWithinAt
  · -- M2: injectivity on the ball.
    have hinjS : Set.InjOn (⇑Φ) Φ.source := Φ.injOn
    rw [hΦcoe] at hinjS
    exact hinjS.mono hballsrc
  · -- M3: left inverse on the ball.
    intro z hz
    have h := Φ.left_inv (hballsrc hz)
    have hcz : (⇑Φ : Point n → Point n) z = Wbv z := congrFun hΦcoe z
    rw [hcz] at h; exact h
  · -- M4: positive Jacobian.
    intro z hz
    have hzε : dist z (0 : Point n) < ε := lt_of_lt_of_le (Metric.mem_ball.mp hz) hρε
    have hd := (hεspec hzε).2
    rw [hdet0val] at hd
    exact lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hd
  · -- ContinuousOn V Ω.
    exact Φ.continuousOn_symm.mono hΩsub
  · -- f' = fderiv Wbv on the ball.
    intro z _; rfl
  · -- uniform Jacobian lower bound 1/2 < |det f'|.
    intro z hz
    have hzε : dist z (0 : Point n) < ε := lt_of_lt_of_le (Metric.mem_ball.mp hz) hρε
    have hd := (hεspec hzε).2
    rw [hdet0val] at hd
    exact hd

/-! ### The inverse-limit wrappers. -/

/-- **★ `bundleV_tendsto_zero` — the CoV inverse tends to `0`.**  `ContinuousOn V Ω` with `0 ∈ Ω`
    and `V 0 = 0` gives `Tendsto V (𝓝[Ω] 0) (𝓝 0)`.  NOT `a₁ = R/6`. -/
theorem bundleV_tendsto_zero (V : Point n → Point n) (Ω : Set (Point n))
    (hVcont : ContinuousOn V Ω) (h0Ω : (0 : Point n) ∈ Ω) (hV0 : V 0 = 0) :
    Tendsto V (𝓝[Ω] (0 : Point n)) (𝓝 (0 : Point n)) := by
  have h : Tendsto V (𝓝[Ω] (0 : Point n)) (𝓝 (V 0)) := hVcont 0 h0Ω
  rwa [hV0] at h

/-- **★ `bundleDet_tendsto_one` — the Jacobian modulus tends to `1` along the inverse.**  On
    `Ω := Wbv '' ball 0 ρ`, `f' (V w) = fderiv Wbv (V w)` (the pin, since `V w ∈ ball`), and
    `|det (fderiv Wbv ·)|` is continuous at `0` with value `1`; composing with `V w → 0` gives
    `Tendsto (fun w => |det (f' (V w))|) (𝓝[Ω] 0) (𝓝 1)`.  NOT `a₁ = R/6`. -/
theorem bundleDet_tendsto_one (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (ρ : ℝ) (V : Point n → Point n)
    (f' : Point n → (Point n →L[ℝ] Point n))
    (hVmaps : ∀ w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ,
      V w ∈ Metric.ball (0 : Point n) ρ)
    (hf'eq : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      f' z = fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z)
    (hVto0 : Tendsto V
      (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
        (0 : Point n)) (𝓝 (0 : Point n)))
    (hdetcont : ContinuousAt
      (fun y => |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) y).det|) (0 : Point n))
    (hdetval : |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)).det| = 1) :
    Tendsto (fun w => |(f' (V w)).det|)
      (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
        (0 : Point n)) (𝓝 (1 : ℝ)) := by
  have hcomp : Tendsto
      (fun w => |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|)
      (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
        (0 : Point n)) (𝓝 (1 : ℝ)) := by
    have h := hdetcont.tendsto.comp hVto0
    rwa [hdetval] at h
  have hEq :
      (fun w => |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|)
        =ᶠ[𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
            (0 : Point n)]
      (fun w => |(f' (V w)).det|) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hf'eq (V w) (hVmaps w hw)]
  exact Filter.Tendsto.congr' hEq hcomp

/-! ### The v3 capstone — `hbound`/`hlocal` discharged, only `hGgate`/`hSupp` remain. -/

/-- **★★ `chartImage_approx_identity_v3` — THE v3 CAPSTONE.**  The fixed-`f` W1 limit with the
    change-of-variables bundle (M1–M4), the chart-image measurability, the Layer-C measurability
    member (C3), AND the boundedness/local-limit members (`hbound`/`hlocal`, C4/C5) all discharged.
    From the standing geometry `(hC, hK, K ∈ 𝓝 0)`, the metric carries `{hg, hgi, hgpos}`, the gauge
    `det g 0 = 1`, `0 < a < b`, and `f` measurable + globally bounded + continuous at `0`, there EXIST
    a CoV radius `ρ`, inverse `V`, and derivative field `f'` such that, provided ONLY the TWO
    remaining carries hold for `(ρ, V, f')` —
      • `hGgate` : the witness gate is active on `ball 0 ρ`;
      • `hSupp`  : the witness vanishes off `ball 0 ρ`, τ-uniformly —
    the boundary witness sampled against `f` concentrates at `f 0`:
        `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`.

    ROUTE.  `baseSlotAmp_bound` → amplitude radius `ρA`; `enrichedChartBundle … ρA` → `(ρ, V, f')`
    with `ρ ≤ ρA` (so `V (Ω) ⊆ ball 0 ρ ⊆ closedBall 0 ρA`); `hbound` from the amplitude bound + `|f|`
    bound + `1/2 < |det f'|`; `hlocal` from the product-filter limit `amp · f / |det| → 1 · f0 / 1`
    (via `baseSlotAmp_joint_limit`, `bundleV_tendsto_zero`, `bundleDet_tendsto_one`, `f`-continuity,
    `A₀ = 1`), unpacked with `eventually_prod_iff`; feed
    `ChartImageAIConcrete.chartImage_approx_identity_conditional`.

    ⚠ CONDITIONAL only on `hGgate`/`hSupp` (obstruction (B), the ball/annulus split), plus the
    standing satisfiable carries.  NOT `a₁ = R/6`. -/
theorem chartImage_approx_identity_v3
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    (f : Point n → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ Cf : ℝ, ∀ x, |f x| ≤ Cf)
    (hf_cont : ContinuousAt f 0) :
    ∃ ρ > (0 : ℝ),
      (∀ z ∈ Metric.ball (0 : Point n) ρ, z ∈ K ∧ (0 : Point n) ∈ S z) →
      (∀ τ, ∀ z, z ∉ Metric.ball (0 : Point n) ρ →
        vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z = 0) →
      Tendsto (fun τ => ∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  -- Amplitude sup-bound with a radius `ρA`.
  obtain ⟨ρA, hρA, CA, hCA⟩ :=
    QIQTH.BaseSlotAmplitude.baseSlotAmp_bound g gi hC hK h0Kmem hg hgi hgpos a b 1
  -- Enriched bundle capped at `ρA`.
  obtain ⟨ρ, hρ, hρcaple, V, f', _hballmeas, hfd, hinj, hV, hJpos, hΩnhds,
      hVcont, _hΩopen, hV0, hf'eq, hdetlb, hdetcont, hdetval⟩ :=
    enrichedChartBundle g gi hC hK h0Kmem ρA hρA
  refine ⟨ρ, hρ, fun hGgate hSupp => ?_⟩
  -- Chart-image measurability (C3 measurability set + moving integrand).
  have hΩmeas : MeasurableSet
      ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)) :=
    QIQTH.FixedFChartImageAI.chartImage_measurableSet_of_bundle g gi hC hK ρ f' hfd hinj
  have hmeas :=
    QIQTH.FixedFTrioDischarge.chartImage_trio_hmeas g gi hC hK hg hgi hgpos a b f hf_meas ρ V f'
      hfd hinj hV
  -- `V` maps `Ω` into the ball; `0 ∈ Ω`.
  have hVmaps : ∀ w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ,
      V w ∈ Metric.ball (0 : Point n) ρ := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := hw; rw [hV z hz]; exact hz
  have h0Ω : (0 : Point n) ∈
      (fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ :=
    ⟨0, Metric.mem_ball_self hρ, uniformInverseChart_zero g gi hC hK h0K⟩
  -- Inverse limits.
  have hVto0 := bundleV_tendsto_zero V
    ((fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ)
    hVcont h0Ω hV0
  have hdet1 := bundleDet_tendsto_one g gi hC hK ρ V f' hVmaps hf'eq hVto0 hdetcont hdetval
  -- `hbound`: uniform sup-bound of the moving integrand on `Ω`.
  have hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict
          ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))),
        ‖chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|‖ ≤ C := by
    obtain ⟨Cf, hCf⟩ := hf_bdd
    have hCf0 : (0 : ℝ) ≤ Cf := le_trans (abs_nonneg _) (hCf 0)
    have hCA0 : (0 : ℝ) ≤ CA :=
      le_trans (abs_nonneg _)
        (hCA 0 ⟨le_refl 0, zero_le_one⟩ 0 (Metric.mem_closedBall_self hρA.le))
    have hτicc : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 := by
      have hIio : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
      filter_upwards [self_mem_nhdsWithin, hIio] with τ hτpos hτlt
      exact ⟨le_of_lt hτpos, le_of_lt hτlt⟩
    refine ⟨2 * CA * Cf, ?_⟩
    filter_upwards [hτicc] with τ hτ
    refine (ae_restrict_iff' hΩmeas).mpr (Filter.Eventually.of_forall (fun w => ?_))
    intro hwΩ
    have hVwball : V w ∈ Metric.ball (0 : Point n) ρ := hVmaps w hwΩ
    have hVwcball : V w ∈ Metric.closedBall (0 : Point n) ρA :=
      (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall hρcaple)) hVwball
    have hampb : |chartFieldAmp g gi hC hK a b τ (V w) 0| ≤ CA := hCA τ hτ (V w) hVwcball
    have hfb : |f (V w)| ≤ Cf := hCf (V w)
    have hdetb : (1 : ℝ) / 2 < |(f' (V w)).det| := hdetlb (V w) hVwball
    have hdetpos : (0 : ℝ) < |(f' (V w)).det| := lt_trans (by norm_num) hdetb
    have h1 : |chartFieldAmp g gi hC hK a b τ (V w) 0| * |f (V w)| ≤ CA * Cf :=
      mul_le_mul hampb hfb (abs_nonneg _) hCA0
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_abs, div_le_iff₀ hdetpos]
    nlinarith [h1, hdetb, mul_nonneg hCA0 hCf0]
  -- `hlocal`: joint `(τ, w) → (0⁺, 0)` limit of the moving integrand to `f 0`.
  have hlocal : ∀ ε > 0, ∃ r > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict
          ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))),
        ‖w‖ < r →
          ‖chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det| - f 0‖ < ε := by
    obtain ⟨_ρ0, _hρ0, hAjoint⟩ :=
      QIQTH.BaseSlotAmplitude.baseSlotAmp_joint_limit g gi hC hK h0Kmem hg hgi hgpos a b
    have hA0 : chartFieldAmp g gi hC hK a b 0 0 0 = 1 :=
      QIQTH.FixedFTrioDischarge.baseChartAmp_centre_eq_one g gi hC hK h0K a b ha hab hgdet0
    have hGto : Tendsto (fun p : ℝ × Point n =>
        chartFieldAmp g gi hC hK a b p.1 (V p.2) 0 * f (V p.2) / |(f' (V p.2)).det|)
        ((𝓝[>] (0 : ℝ)) ×ˢ
          (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
            (0 : Point n)))
        (𝓝 (f 0)) := by
      have hamp : Tendsto
          (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b p.1 (V p.2) 0)
          ((𝓝[>] (0 : ℝ)) ×ˢ
            (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
              (0 : Point n)))
          (𝓝 1) := by
        have h := hAjoint.comp (tendsto_id.prodMap hVto0)
        rw [hA0] at h
        exact h
      have hfV : Tendsto (fun p : ℝ × Point n => f (V p.2))
          ((𝓝[>] (0 : ℝ)) ×ˢ
            (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
              (0 : Point n)))
          (𝓝 (f 0)) :=
        ((hf_cont.tendsto).comp hVto0).comp tendsto_snd
      have hdetV : Tendsto (fun p : ℝ × Point n => |(f' (V p.2)).det|)
          ((𝓝[>] (0 : ℝ)) ×ˢ
            (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
              (0 : Point n)))
          (𝓝 1) := hdet1.comp tendsto_snd
      have hmul := (hamp.mul hfV).div hdetV one_ne_zero
      rw [one_mul, div_one] at hmul
      exact hmul
    intro ε hε
    have hnhd : Metric.ball (f 0) ε ∈ 𝓝 (f 0) := Metric.ball_mem_nhds _ hε
    have hpre := hGto.eventually hnhd
    rw [eventually_prod_iff] at hpre
    obtain ⟨pa, hpa, pb, hpb, hcomb⟩ := hpre
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hpb
    obtain ⟨r, hr, hrsub⟩ := hpb
    refine ⟨r, hr, ?_⟩
    filter_upwards [hpa] with τ hτpa
    refine (ae_restrict_iff' hΩmeas).mpr (Filter.Eventually.of_forall (fun w => ?_))
    intro hwΩ hwr
    have hwpb : pb w := hrsub ⟨mem_ball_zero_iff.mpr hwr, hwΩ⟩
    have hin : chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|
        ∈ Metric.ball (f 0) ε := hcomb hτpa hwpb
    rw [Metric.mem_ball, Real.dist_eq] at hin
    rw [Real.norm_eq_abs]
    exact hin
  -- Feed the J4-271 conditional capstone.
  exact QIQTH.ChartImageAIConcrete.chartImage_approx_identity_conditional
    g gi hC hK S a b f ρ V f' hfd hinj hV hJpos hGgate hSupp hΩmeas hΩnhds hmeas hbound hlocal

end QIQTH.EnrichedChartBundle

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.EnrichedChartBundle
#print axioms enrichedChartBundle
#print axioms bundleV_tendsto_zero
#print axioms bundleDet_tendsto_one
#print axioms chartImage_approx_identity_v3
end AxiomChecks
