/-
  WideSliverBoundary — J4-253: wide-route brick 6, the SLIVER ESTIMATES + BOUNDARY NEAR-DIAGONAL
  data AT THE WIDE WIDTH.  Parallel to the narrow `SliverSumPlumbing` / `ETailRateBound` /
  `GaussianApproxIdentity` machinery, at the wide Gaussian width `lam·τ`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  No
  `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no
  conclusion-in-disguise.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── THE CONVERGENCE ANALYSIS (crude vs. moment-aware — which route wins, and WHY).
     The wide brick-5 package (`WideWitnessAmplitude.WideAmplitudePackage`) carries the CRUDE second
     domination `hSecond : |witnessSecondXDeriv … i τ z| ≤ C·τ⁻¹·gaussDdim (lam·τ) z`.  Feeding this
     into the sliver strip `∫ s in (u−ε)..u, ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0`
     (with `|F| ≤ C_L·gaussDdim (2s)`) and collapsing the `z`-integral by the SAME Chapman–Kolmogorov
     mass the narrow route uses (`gaussDdim_selfmul_integral`: `∫ z, G_a z·G_b z = G_{a+b}(0)`) gives
     the per-slice bound
         `‖∫ z, witnessSecondXDeriv … (u−s) z · F s z 0‖ ≤ C·(u−s)⁻¹·C_L·gaussDdim (lam(u−s)+2s) 0`.
     The `gaussDdim (lam(u−s)+2s) 0` factor is `s`-uniformly BOUNDED (width `≥ 2s ≥ 2(u−ε)`,
     width-antitone at `0`), so the strip integral is dominated by
         `C·C_L·(floor) · ∫ s in (u−ε)..u, (u−s)⁻¹ ds  =  C·C_L·(floor) · ∫_0^ε t⁻¹ dt  =  +∞`.
     ★ THE CRUDE ROUTE DIVERGES: the raw `τ⁻¹` endpoint is NOT strip-integrable (Sol note #4:
     "the raw `s⁻¹` endpoint is NOT integrable — use the banked cancellation/splitting").  This is
     recorded HONESTLY as the theorem `wide_second_inner_slice_bound` (the per-slice `τ⁻¹` bound, a
     genuine consequence of the wide domination) together with this note that its strip integral
     diverges.  ★ THE MOMENT-AWARE ROUTE WINS: exactly as in the narrow route, the finite `√ε` rate
     is NOT read off a pointwise `τ⁻¹` sup — it comes from the per-coordinate strip amplitudes
     `|slivInt i m| ≤ D0 i·2√ε + D1 i·ε` produced by the moment structure (the `(z_i²/τ²)·G` terms
     integrate to a SECOND MOMENT `∼ τ` that cancels one power of `τ⁻¹`; the narrow banked source is
     `NormalFormDischarge.witness_sliver2_concrete` via the three-term normal form).  The wide
     analogue of that per-coordinate `√ε` bound is the honest CARRIED input of `wide_sliver_sum_bound`
     below (its genuine derivation = the wide three-term moment brick, bricks 7–10 = the
     dichotomy/trichotomy/majorant campaign).  The plumbing here banks the sum-over-coordinates and
     the `√ε → 0` rate at the wide width, exactly mirroring `SliverSumPlumbing.sliver_sum_bound` /
     `DaLimLUWallRecon.sliver_sum_bound_U`.

  ── WHAT LANDS.
    (B)  `wide_width_tendsto` — `τ ↦ lam·τ` maps `𝓝[>] 0 → 𝓝[>] 0` (`lam > 0`); the width composer.
    (B1) `gaussDdim_wide_approx_identity` — ★ THE WIDE BOUNDARY / APPROXIMATE IDENTITY: for `f`
         bounded, continuous at `0`, a.e.-measurable,
             `∫ z, gaussDdim (lam·τ) z · f z  →  f 0`   in `𝓝[>] (0 : ℝ)`,
         since `lam·τ ↓ 0` keeps `gaussDdim (lam·τ)` an approximate identity.  From
         `GaussianApproxIdentity.gaussDdim_approx_identity` composed with `wide_width_tendsto`.  This
         is the wide-width `hAnear`-analogue the boundary-limit (`BoundaryAssembly`-style) consumers
         need.
    (B2) `gaussDdim_wide_approx_identity_family` — the wide-indexed amplitude version (`A (lam·τ)`),
         via the family identity composed with `wide_width_tendsto`.
    (S)  `wide_second_inner_slice_bound` — ★ THE PER-SLICE WIDE SECOND BOUND (the crude route, made
         honest): from the wide (global) domination `|D2H τ z| ≤ C·τ⁻¹·gaussDdim (lam·τ) z` and
         `|F| ≤ C_L·gaussDdim (2s)`, the per-slice `z`-pairing is `≤ C·(u−s)⁻¹·C_L·gaussDdim
         (lam(u−s)+2s) 0`.  The `(u−s)⁻¹` is REAL — its strip integral diverges (see the analysis);
         this theorem exhibits precisely where the crude route fails, and is the honest per-slice
         building block for the moment cancellation.
    (P)  `wide_sliver_sum_bound` / `wide_sliver_sum_bound_U` — ★ THE WIDE SLIVER SUM PLUMBING (the
         moment-aware route): from the CARRIED per-coordinate `√ε` strip bounds (the wide analogue of
         `witness_sliver2_concrete`'s output), the sum over `i : Fin n` obeys
             `‖∑ i, slivInt i m‖ ≤ B(ε_m)`,   `B e := ∑ i (D0 i·2√e + D1 i·e)`,   `B(ε_m) → 0`.
         Mirrors `sliver_sum_bound` (`u`-free) and `sliver_sum_bound_U` (`∀ u ∈ U`) at the wide width.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ETailRateBound
import QIQTH.InnerSliceBounds
import QIQTH.GaussianApproxIdentity
import QIQTH.SliverSumPlumbing

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.GaussianConvolution
open QIQTH.ResidueBound
open scoped Interval Topology BigOperators

namespace QIQTH.WideSliverBoundary

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (B) — the width composer `τ ↦ lam·τ : 𝓝[>] 0 → 𝓝[>] 0`.
    ############################################################################### -/

/-- **`wide_width_tendsto`.**  For `lam > 0` the width dilation `τ ↦ lam·τ` maps the half-open
    origin filter into itself: `Tendsto (fun τ => lam·τ) (𝓝[>] 0) (𝓝[>] 0)`.  (Continuity gives the
    `𝓝 0`-limit; `lam·τ > 0` for `τ > 0` keeps the image inside `Ioi 0`.)  NOT `a₁ = R/6`. -/
theorem wide_width_tendsto (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun τ : ℝ => lam * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h0 : Tendsto (fun τ : ℝ => lam * τ) (𝓝 (0 : ℝ)) (𝓝 (lam * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact mul_pos hlam hτ

/-! ###############################################################################
    ### (B1)(B2) — the WIDE boundary / approximate identity at width `lam·τ`.
    ############################################################################### -/

/-- **★★ (B1) `gaussDdim_wide_approx_identity` — THE WIDE GAUSSIAN APPROXIMATE IDENTITY.**  For
    `f : Point n → ℝ` BOUNDED (`|f z| ≤ C`), CONTINUOUS at `0`, and `volume`-a.e.-measurable, and any
    fixed width gap `lam > 0`, the wide Gaussian delta family samples `f` at the origin as `τ ↓ 0`:
        `∫ z, gaussDdim (lam·τ) z · f z  →  f 0`   in `𝓝[>] (0 : ℝ)`.
    Route: `GaussianApproxIdentity.gaussDdim_approx_identity` (the base-width identity) composed with
    `wide_width_tendsto` (`lam·τ ↓ 0`).  This is the wide-width boundary datum the `BoundaryAssembly`-
    style consumers need.  ⚠ CONDITIONAL only on base measurability `hmeas`, exactly as the base
    identity.  NOT `a₁ = R/6`. -/
theorem gaussDdim_wide_approx_identity (lam : ℝ) (hlam : 0 < lam)
    (f : Point n → ℝ) (C : ℝ) (hCbd : ∀ z, |f z| ≤ C)
    (hcont : ContinuousAt f 0) (hmeas : AEStronglyMeasurable f volume) :
    Tendsto (fun τ => ∫ z : Point n, gaussDdim (lam * τ) z * f z) (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
  (QIQTH.GaussianApproxIdentity.gaussDdim_approx_identity f C hCbd hcont hmeas).comp
    (wide_width_tendsto lam hlam)

/-- **★★ (B2) `gaussDdim_wide_approx_identity_family` — THE WIDE AMPLITUDE / FAMILY IDENTITY.**  For a
    uniformly bounded (`|A τ z| ≤ C`), per-`τ` a.e.-measurable amplitude `A` approaching a common
    value `c` uniformly near the origin (`hEqui`, in `𝓝[>] 0` form), the wide Gaussian samples the
    common limit with the amplitude read at the WIDE argument:
        `∫ z, gaussDdim (lam·τ) z · A (lam·τ) z  →  c`   in `𝓝[>] (0 : ℝ)`.
    Route: `GaussianApproxIdentity.gaussDdim_approx_identity_family` composed with `wide_width_tendsto`.
    `hEqui` is a genuine uniform-approach input (NOT the conclusion, non-vacuous).  NOT `a₁ = R/6`. -/
theorem gaussDdim_wide_approx_identity_family (lam : ℝ) (hlam : 0 < lam)
    (A : ℝ → Point n → ℝ) (C : ℝ) (hCbd : ∀ τ z, |A τ z| ≤ C)
    (hmeas : ∀ τ, AEStronglyMeasurable (A τ) volume) (c : ℝ)
    (hEqui : ∀ η > 0, ∃ δ > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ z ∈ Metric.ball (0 : Point n) δ, |A τ z - c| ≤ η) :
    Tendsto (fun τ => ∫ z : Point n, gaussDdim (lam * τ) z * A (lam * τ) z)
      (𝓝[>] (0 : ℝ)) (𝓝 c) :=
  (QIQTH.GaussianApproxIdentity.gaussDdim_approx_identity_family A C hCbd hmeas c hEqui).comp
    (wide_width_tendsto lam hlam)

/-! ###############################################################################
    ### (S) — the per-slice WIDE second bound (the crude route, made honest).
    ############################################################################### -/

/-- **★★ (S) `wide_second_inner_slice_bound` — THE PER-SLICE WIDE SECOND BOUND.**  On the residual
    strip `s ∈ (u−εm, u]`, the inner `z`-pairing of a wide-dominated second kernel `D2H` against `F`
    obeys
        `‖∫ z, D2H (u−s) z · F s z 0‖ ≤ C·(u−s)⁻¹·C_L·gaussDdim (lam(u−s)+2s) 0`.
    From the wide (global) domination `hDom : |D2H τ z| ≤ C·τ⁻¹·gaussDdim (lam·τ) z` (`τ > 0`; `D2H`
    vanishing at `τ ≤ 0`, `hDzero`) and the width-2 `F`-domination `hFdom` (`F` vanishing at `s ≤ 0`,
    `hFzero`), via the same-point Chapman–Kolmogorov mass `gaussDdim_selfmul_integral`
    (`∫ z, G_a z·G_b z = G_{a+b}(0)`).  The `τ ≤ 0` / `s ≤ 0` excursions are killed by vanishing.

    ⚠ HONEST NOTE.  The `(u−s)⁻¹` factor is REAL and IRREDUCIBLE from the crude wide domination: its
    strip integral `∫ s in (u−εm)..u, (u−s)⁻¹ ds = +∞` DIVERGES (`∫_0^εm t⁻¹ dt`).  This theorem is
    the honest per-slice building block that exhibits exactly the divergent endpoint; the finite `√ε`
    strip rate comes NOT from this bound but from the moment-aware per-coordinate amplitudes fed to
    `wide_sliver_sum_bound`.  NOT `a₁ = R/6`. -/
theorem wide_second_inner_slice_bound
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (lam C C_L T u εm : ℝ)
    (hlam : 0 < lam) (hC : 0 ≤ C) (hC_L : 0 ≤ C_L) (hεm : 0 ≤ εm) (huT : u ≤ T)
    (hDom : ∀ τ, 0 < τ → ∀ z : Point n, |D2H τ z| ≤ C * τ⁻¹ * gaussDdim (lam * τ) z)
    (hDzero : ∀ τ, τ ≤ 0 → ∀ z : Point n, D2H τ z = 0)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (s : ℝ) (hsmem : s ∈ Set.uIoc (u - εm) u) :
    ‖∫ (z : Point n), D2H (u - s) z * F s z 0‖
      ≤ C * (u - s)⁻¹ * C_L * gaussDdim (lam * (u - s) + 2 * s) (0 : Point n) := by
  rw [Set.uIoc_of_le (by linarith : u - εm ≤ u)] at hsmem
  rcases lt_or_ge 0 (u - s) with hτpos | hτle
  · rcases lt_or_ge 0 s with hspos | hsle
    · -- `0 < s`, `0 < τ = u−s` : full wide domination.
      have hsT : s ≤ T := le_trans hsmem.2 huT
      have hτinv : 0 ≤ (u - s)⁻¹ := (inv_pos.mpr hτpos).le
      set c : ℝ := C * (u - s)⁻¹ * C_L with hc
      have hdomg : Integrable
          (fun z : Point n => c * (gaussDdim (lam * (u - s)) z * gaussDdim (2 * s) z)) volume :=
        (gaussDdim_selfmul_integrable (lam * (u - s)) (2 * s)).const_mul c
      have hnn : (fun _ : Point n => (0 : ℝ)) ≤ᵐ[volume]
          (fun z : Point n => |D2H (u - s) z| * |F s z 0|) :=
        ae_of_all _ (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hle : (fun z : Point n => |D2H (u - s) z| * |F s z 0|)
          ≤ᵐ[volume]
            (fun z : Point n => c * (gaussDdim (lam * (u - s)) z * gaussDdim (2 * s) z)) := by
        refine ae_of_all _ (fun z => ?_)
        have hA' := hDom (u - s) hτpos z
        have hB' : |F s z 0| ≤ C_L * gaussDdim (2 * s) z := by
          simpa only [sub_zero] using hFdom s hspos hsT z 0
        have hbnn : 0 ≤ C * (u - s)⁻¹ * gaussDdim (lam * (u - s)) z :=
          mul_nonneg (mul_nonneg hC hτinv) (gaussDdim_nonneg _ _)
        calc |D2H (u - s) z| * |F s z 0|
            ≤ (C * (u - s)⁻¹ * gaussDdim (lam * (u - s)) z) * (C_L * gaussDdim (2 * s) z) :=
              mul_le_mul hA' hB' (abs_nonneg _) hbnn
          _ = c * (gaussDdim (lam * (u - s)) z * gaussDdim (2 * s) z) := by rw [hc]; ring
      calc ‖∫ (z : Point n), D2H (u - s) z * F s z 0‖
          ≤ ∫ (z : Point n), ‖D2H (u - s) z * F s z 0‖ := norm_integral_le_integral_norm _
        _ = ∫ (z : Point n), |D2H (u - s) z| * |F s z 0| := by
            simp only [Real.norm_eq_abs, abs_mul]
        _ ≤ ∫ (z : Point n), c * (gaussDdim (lam * (u - s)) z * gaussDdim (2 * s) z) :=
            integral_mono_of_nonneg hnn hdomg hle
        _ = c * gaussDdim (lam * (u - s) + 2 * s) (0 : Point n) := by
            rw [integral_const_mul, gaussDdim_selfmul_integral (lam * (u - s)) (2 * s)
              (mul_pos hlam hτpos) (by linarith)]
    · -- `s ≤ 0` : `F` vanishes.
      have hz : (fun z : Point n => D2H (u - s) z * F s z 0) = fun _ => (0 : ℝ) := by
        funext z; rw [hFzero s hsle z 0, mul_zero]
      rw [hz]; simp only [integral_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hτpos.le)) hC_L)
        (gaussDdim_nonneg _ _)
  · -- `u − s ≤ 0` : on the strip `s ≤ u`, so `u − s = 0`; the second kernel vanishes.
    have hus0 : u - s = 0 := le_antisymm hτle (by linarith [hsmem.2])
    have hzfun : (fun z : Point n => D2H (u - s) z * F s z 0) = fun _ => (0 : ℝ) := by
      funext z; rw [hDzero (u - s) (le_of_eq hus0) z, zero_mul]
    have hLHS : ∫ (z : Point n), D2H (u - s) z * F s z 0 = 0 := by
      rw [hzfun]; exact integral_zero _ _
    rw [hLHS, norm_zero, hus0]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (le_of_eq inv_zero.symm)) hC_L)
      (gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### (P) — the WIDE sliver sum plumbing (the moment-aware `√ε` route).
    ############################################################################### -/

/-- **★★ (P) `wide_sliver_sum_bound` — THE WIDE SLIVER SUM PLUMBING (`u`-free).**  From the CARRIED
    per-coordinate `√ε` strip bounds (the wide analogue of `NormalFormDischarge.witness_sliver2_concrete`'s
    output — the honest moment-aware amplitudes, whose derivation is the wide three-term brick)
      `|slivInt i m| ≤ D0 i · (2√ε_m) + D1 i · ε_m`   (`D0 i, D1 i ≥ 0`),
    the sum over `i : Fin n` obeys
      `‖∑ i, slivInt i m‖ ≤ B(ε_m)`   with `B e := ∑ i (D0 i·2√e + D1 i·e)`,   and   `B(ε_m) → 0`.
    Route: `norm_sum_le` + `Finset.sum_le_sum` for the bound; `tendsto_finsetSum` over the per-`i`
    `sliverBound_tendsto_zero` (`√ε` rate) for the limit.  Mirrors `SliverSumPlumbing.sliver_sum_bound`
    at the wide width.  NOT `a₁ = R/6`. -/
theorem wide_sliver_sum_bound (slivInt : Fin n → ℕ → ℝ) (D0 D1 : Fin n → ℝ)
    (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ),
        |slivInt i m| ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :
    ∃ B : ℝ → ℝ,
      (∀ m, ‖∑ i, slivInt i m‖ ≤ B (epsSeq m))
      ∧ Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0) := by
  refine ⟨fun e => ∑ i, (D0 i * (2 * Real.sqrt e) + D1 i * e), ?_, ?_⟩
  · intro m
    calc ‖∑ i, slivInt i m‖
        ≤ ∑ i, ‖slivInt i m‖ := norm_sum_le _ _
      _ = ∑ i, |slivInt i m| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑ i, (D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :=
          Finset.sum_le_sum (fun i _ => hbnd i m)
  · have hsum : Tendsto
        (fun m => ∑ i, (D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)) atTop
        (𝓝 (∑ _i : Fin n, (0 : ℝ))) :=
      tendsto_finsetSum _ (fun i _ => sliverBound_tendsto_zero (D0 i) (D1 i))
    simpa using hsum

/-- **★★ (P) `wide_sliver_sum_bound_U` — THE WIDE SLIVER SUM PLUMBING (`∀ u ∈ U`).**  The loc-uniform
    upgrade of `wide_sliver_sum_bound`: from the `u`-uniform per-coordinate `√ε` strip bounds
      `|slivInt i m u| ≤ D0 i · (2√ε_m) + D1 i · ε_m`   (`∀ i m, ∀ u ∈ U`),
    the sum obeys, with the SAME `u`-free `B e := ∑ i (D0 i·2√e + D1 i·e)`,
      `‖∑ i, slivInt i m u‖ ≤ B(ε_m)`   (`∀ m, ∀ u ∈ U`),   and   `B(ε_m) → 0`.
    Mirrors `DaLimLUWallRecon.sliver_sum_bound_U` at the wide width — this is the shape brick 11
    (`WideA1Assembly`) threads into the wide capstone's sliver slot.  NOT `a₁ = R/6`. -/
theorem wide_sliver_sum_bound_U {U : Set ℝ} (slivInt : Fin n → ℕ → ℝ → ℝ) (D0 D1 : Fin n → ℝ)
    (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |slivInt i m u| ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :
    ∃ B : ℝ → ℝ,
      (∀ (m : ℕ), ∀ u ∈ U, ‖∑ i, slivInt i m u‖ ≤ B (epsSeq m))
      ∧ Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0) := by
  refine ⟨fun e => ∑ i, (D0 i * (2 * Real.sqrt e) + D1 i * e), ?_, ?_⟩
  · intro m u hu
    calc ‖∑ i, slivInt i m u‖
        ≤ ∑ i, ‖slivInt i m u‖ := norm_sum_le _ _
      _ = ∑ i, |slivInt i m u| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑ i, (D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :=
          Finset.sum_le_sum (fun i _ => hbnd i m u hu)
  · have hsum : Tendsto
        (fun m => ∑ i, (D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)) atTop
        (𝓝 (∑ _i : Fin n, (0 : ℝ))) :=
      tendsto_finsetSum _ (fun i _ => sliverBound_tendsto_zero (D0 i) (D1 i))
    simpa using hsum

end QIQTH.WideSliverBoundary

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.WideSliverBoundary.wide_width_tendsto
#print axioms QIQTH.WideSliverBoundary.gaussDdim_wide_approx_identity
#print axioms QIQTH.WideSliverBoundary.gaussDdim_wide_approx_identity_family
#print axioms QIQTH.WideSliverBoundary.wide_second_inner_slice_bound
#print axioms QIQTH.WideSliverBoundary.wide_sliver_sum_bound
#print axioms QIQTH.WideSliverBoundary.wide_sliver_sum_bound_U
