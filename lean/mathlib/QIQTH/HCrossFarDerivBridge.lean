/-
  HCrossFarDerivBridge — the mean-value (FTC) bridge that reduces the OPEN `H_far` carry of J4-927's
  integrated `hCross` split to the GENERATOR IDENTITY plus a per-shift census bound (the shape J4-924's
  `two_term_census_bound_uniform` supplies).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE brick.  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, none
  equal to the conclusion, no existing file edited.

  ## WHERE THIS SITS (verified against the live defs + gpt-5.6-sol high audit, not memory).
  J4-927 (`HCrossIntegratedSplit.lean`) reduced the live `hCross` mixed-second-difference binder (for the
  `h,k > 0` quadrant) to exactly three carries on the inner τ-shift difference
      `D(s) := Φ(u+h,s) − Φ(u,s)`,   `Φ(a,s) := ∫ z, A(a−s) x z · B s z y` :
    • `H_near`  (cheap, boundedness on the `O(h)` strip),
    • `H_zero`  (cheap, finite propagation `W(≤0)=0`),
    • `H_far`   `|Φ(u+h,s) − Φ(u,s)| ≤ C_far·h·(u−s)^{−1/2}`   on `s ∈ Ioo (u−ε) u`  — the ONLY hard one.

  J4-924 (`GaussTauTraceChartTransported.lean`) proved `two_term_census_bound_uniform`:
      `|∫_Ω (∑ᵢ(zᵢ²/4τ² − 1/2τ))·gaussDdim τ z·q₁  +  ∫_Ω gaussDdim τ z·q₂| ≤ Cpair/√τ`.
  The weight `(∑ᵢ zᵢ²/4τ² − n/2τ)·gaussDdim = ∂_τ gaussDdim` EXACTLY, so J4-924 bounds the τ-DERIVATIVE
  census integral by `Cpair·τ^{−1/2}` — the SAME `(u−s)^{−1/2}` envelope `H_far` wants, but with NO factor
  of `h` and at a SINGLE τ.

  ## WHAT J4-924 DOES — AND DOES NOT — GIVE `H_far` (gpt-5.6-sol high, verbatim verdict).  J4-924 is the
  CORRECT RHS ENVELOPE but does **not** compose to supply `H_far` directly.  Two genuine implications
  remain, both = the "opaque chart wall":
    (i)  the GENERATOR IDENTITY `∂_a Φ(a,s) = g(a,s)` where `g` is the census expression J4-924 bounds
         (differentiation under the integral sign + the chart change-of-variables turning the CURVED
         `∫_z A(a−s) x z · B s z y` derivative into J4-924's FLAT `∫_Ω(∑…)gaussDdim·q₁ + ∫_Ω G·q₂` shape);
    (ii) the FINITE-DIFFERENCE step `Φ(u+h,s) − Φ(u,s) = ∫_u^{u+h} ∂_a Φ(a,s) da`, supplying the `h` factor.
  Step (ii) is ROUTINE 1-D calculus; step (i) is the substantive wall.  This file DISCHARGES step (ii)
  generically (`abs_sub_le_mul_of_hasDerivAt`, a mean-value bound), and threads it so `H_far` reduces to
  exactly the named generator identity `hderiv` + the per-shift census bound `hgbound` (J4-924 modulo the
  chart CoV, applied uniformly over `a ∈ [u,u+h]`, using `(a−s)^{−1/2} ≤ (u−s)^{−1/2}` for `a ≥ u`).

  ## WHAT LANDS.
    • `abs_sub_le_mul_of_hasDerivAt` — ★ the generic mean-value bridge: a uniform derivative bound `K`
      on `[u,u+h]` gives `|f(u+h) − f u| ≤ K·h`.  (Mathlib `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`.)
    • `hfar_of_hasDerivAt` — ★★ reduces the EXACT `H_far` shape to `{hderiv, hgbound}` (per `s`), using the
      monotone envelope `hgbound a ≤ C_far·(u−s)^{−1/2}` (uniform over the shift interval).
    • `hcross_split_bound_of_hderiv` — ★★★ the full live `hCross` binder from `{hderiv, hgbound, H_near,
      H_zero}` + the four interval-integrabilities — J4-927's capstone with the `H_far` carry REPLACED by
      the generator identity `hderiv`.
    • `..._hyp_satisfiable` witnesses (non-vacuity, TEETH: genuine `HasDerivAt` of `sin`/`cos∘affine`, and
      the `cos·Gaussian` convolution `Φ(a,s) = C·cos(a−s)` with `∂_a Φ = −C·sin(a−s)`).

  ⚠  STILL NOT `a₁ = R/6`.  This does NOT close `hCross`: the generator identity `hderiv` (chart CoV +
  differentiation under the integral) remains UNBUILT — it IS the opaque chart wall, now cleanly localized.
  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`.
-/
import Mathlib
import QIQTH.HeatDuhamel
import QIQTH.HCrossIntegratedSplit

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatDuhamel
open scoped Interval

namespace QIQTH.HeatResidualBound

/-! ###############################################################################
    ### §A — the generic mean-value bridge (derivative bound ⟹ finite-difference bound).
    ############################################################################### -/

/-- **★ `abs_sub_le_mul_of_hasDerivAt` — the generic mean-value bridge.**  If `f : ℝ → ℝ` has derivative
    `g a` at every `a ∈ [u, u+h]` (`h ≥ 0`) and `|g a| ≤ K` there, then `|f(u+h) − f u| ≤ K·h`.  This is
    the FINITE-DIFFERENCE step: a uniform derivative bound over the length-`h` shift interval yields the
    `K·h` increment (supplying the `h` factor that a single-τ census bound lacks).  Route: Mathlib's
    convex mean-value inequality `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `Icc u (u+h)`.
    NOT `a₁ = R/6`. -/
theorem abs_sub_le_mul_of_hasDerivAt (f g : ℝ → ℝ) (u h K : ℝ) (hh : 0 ≤ h)
    (hderiv : ∀ a ∈ Set.Icc u (u + h), HasDerivAt f (g a) a)
    (hbound : ∀ a ∈ Set.Icc u (u + h), |g a| ≤ K) :
    |f (u + h) - f u| ≤ K * h := by
  have hconv : Convex ℝ (Set.Icc u (u + h)) := convex_Icc u (u + h)
  have hmem_u : u ∈ Set.Icc u (u + h) := Set.left_mem_Icc.mpr (by linarith)
  have hmem_uh : u + h ∈ Set.Icc u (u + h) := Set.right_mem_Icc.mpr (by linarith)
  have hkey := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := g) (C := K)
    (fun x hx => (hderiv x hx).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hbound x hx)
    hmem_u hmem_uh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u + h - u)] at hkey
  have huhu : u + h - u = h := by ring
  rw [huhu] at hkey
  exact hkey

/-! ###############################################################################
    ### §B — `H_far` reduced to the generator identity + per-shift census bound.
    ############################################################################### -/

/-- **★★ `hfar_of_hasDerivAt` — the EXACT `H_far` shape from `{hderiv, hgbound}`.**  Writing
    `Φ(a,s) := ∫ z, A(a−s) x z · B s z y` (so `Φ(u+h,s) = ∫ z, A(u+h−s)…`, `Φ(u,s) = ∫ z, A(u−s)…`),
    GIVEN, for every `s ∈ Ioo (u−ε) u`,
      • (hderiv) `∀ a ∈ [u,u+h]`, the map `a' ↦ Φ(a',s)` has derivative `g s a` at `a` — the GENERATOR
        IDENTITY (differentiation under the integral + chart CoV = the opaque chart wall);
      • (hgbound) `∀ a ∈ [u,u+h]`, `|g s a| ≤ C_far·(u−s)^{−1/2}` — the per-shift census bound (J4-924's
        `two_term_census_bound_uniform` supplies this envelope; `(a−s)^{−1/2} ≤ (u−s)^{−1/2}` for `a ≥ u`),
    the EXACT live `H_far` carry holds:
      `∀ s ∈ Ioo (u−ε) u, |(∫ z, A(u+h−s) x z · B s z y) − (∫ z, A(u−s) x z · B s z y)| ≤ C_far·h·(u−s)^{−1/2}`.
    Route: `abs_sub_le_mul_of_hasDerivAt` per `s`, then `K·h = C_far·(u−s)^{−1/2}·h = C_far·h·(u−s)^{−1/2}`.
    NOT `a₁ = R/6`. -/
theorem hfar_of_hasDerivAt {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u ε h C_far : ℝ)
    (hh : 0 ≤ h) (hCf : 0 ≤ C_far)
    (g : ℝ → ℝ → ℝ)
    (hderiv : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        HasDerivAt (fun a' => ∫ z, A (a' - s) x z * B s z y) (g s a) a)
    (hgbound : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        |g s a| ≤ C_far * (u - s) ^ (-(1 : ℝ) / 2)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |(∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y)|
        ≤ C_far * h * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro s hs
  have hbridge := abs_sub_le_mul_of_hasDerivAt
    (fun a' => ∫ z, A (a' - s) x z * B s z y) (g s) u h
    (C_far * (u - s) ^ (-(1 : ℝ) / 2)) hh
    (hderiv s hs) (hgbound s hs)
  -- rewrite the endpoints and reorder the constant product.
  have heq : C_far * (u - s) ^ (-(1 : ℝ) / 2) * h = C_far * h * (u - s) ^ (-(1 : ℝ) / 2) := by ring
  rw [heq] at hbridge
  exact hbridge

/-! ###############################################################################
    ### §C — the CAPSTONE: the live `hCross` binder from the generator identity.
    ############################################################################### -/

set_option maxHeartbeats 800000 in
/-- **★★★ `hcross_split_bound_of_hderiv` — the live `hCross` binder from the GENERATOR IDENTITY.**  J4-927's
    `hcross_mixed_second_diff_split_bound`, with the `H_far` carry REPLACED by `{hderiv, hgbound}` (the
    generator identity + per-shift census bound).  For the frozen convolution of ANY `A B`, base times
    `a = u`, `b = u − ε`, shifts `h,k > 0`, GIVEN the four interval-integrabilities, the generator identity
    `hderiv`, the census bound `hgbound`, and the cheap carries `H_near`/`H_zero`, the MIXED SECOND
    DIFFERENCE obeys the exact live `hCross` binder
        `|Δ²|  ≤  (2·C_far/√ε + 2·M/ε) · (|h|·|k|)`.
    Route: `hfar_of_hasDerivAt` supplies `H_far`, then J4-927's `hcross_mixed_second_diff_split_bound`
    assembles.  This localizes the whole `hCross` wall (for `h,k>0`) to the generator identity `hderiv`
    (chart CoV + differentiation under the integral — STILL the opaque chart wall).  NOT `a₁ = R/6`. -/
theorem hcross_split_bound_of_hderiv {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (hk : 0 < k) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hah_hi : IntervalIntegrable
      (fun s => ∫ z, A (u + h - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (ha_hi : IntervalIntegrable
      (fun s => ∫ z, A (u - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (hah_lo : IntervalIntegrable (fun s => ∫ z, A (u + h - s) x z * B s z y) volume 0 (u - ε))
    (ha_lo : IntervalIntegrable (fun s => ∫ z, A (u - s) x z * B s z y) volume 0 (u - ε))
    (g : ℝ → ℝ → ℝ)
    (hderiv : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        HasDerivAt (fun a' => ∫ z, A (a' - s) x z * B s z y) (g s a) a)
    (hgbound : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        |g s a| ≤ C_far * (u - s) ^ (-(1 : ℝ) / 2))
    (H_near : ∀ s ∈ Set.Icc u (u + h),
        |(∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y)| ≤ 2 * M)
    (H_zero : ∀ s ∈ Set.Ioi (u + h),
        (∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y) = 0) :
    |heatConvFrozen A B (u + h) (u - ε + k) x y - heatConvFrozen A B (u + h) (u - ε) x y
        - heatConvFrozen A B u (u - ε + k) x y + heatConvFrozen A B u (u - ε) x y|
      ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (|h| * |k|) := by
  have H_far := hfar_of_hasDerivAt A B x y u ε h C_far hh.le hCf g hderiv hgbound
  exact hcross_mixed_second_diff_split_bound A B x y u ε h k C_far M hε hh hk hCf hM
    hah_hi ha_hi hah_lo ha_lo H_far H_near H_zero

/-! ###############################################################################
    ### §D — NON-VACUITY (the hypothesis bundles are jointly satisfiable, with TEETH).
    ############################################################################### -/

/-- **Non-vacuity of `abs_sub_le_mul_of_hasDerivAt`, with TEETH.**  Exercised at `f = sin`, `g = cos`,
    `K = 1` on `[0, π]` (`u = 0, h = π`): a genuine non-affine `HasDerivAt` (`Real.hasDerivAt_sin`) with a
    tight bound `|cos a| ≤ 1` — NOT `0 ≤ 0`, and the conclusion `|sin π − sin 0| = 0 ≤ 1·π` is non-degenerate
    (`K·h = π > 0`).  NOT `a₁ = R/6`. -/
theorem abs_sub_le_mul_of_hasDerivAt_hyp_satisfiable :
    ∃ (f g : ℝ → ℝ) (u h K : ℝ),
      0 ≤ h ∧ 0 < K * h ∧
      (∀ a ∈ Set.Icc u (u + h), HasDerivAt f (g a) a) ∧
      (∀ a ∈ Set.Icc u (u + h), |g a| ≤ K) := by
  refine ⟨Real.sin, Real.cos, 0, Real.pi, 1, Real.pi_pos.le, by
    rw [one_mul]; exact Real.pi_pos, fun a _ => Real.hasDerivAt_sin a, fun a _ => ?_⟩
  exact abs_le.mpr ⟨Real.neg_one_le_cos a, Real.cos_le_one a⟩

/-- **Non-vacuity of `hfar_of_hasDerivAt`, with TEETH.**  Exercised at the genuine convolution witness
    `A τ x z := Real.cos τ · Real.exp (−‖z‖²)`, `B s z y := 1`, so
    `Φ(a,s) = ∫ z, cos(a−s)·exp(−‖z‖²) = C·cos(a−s)` (`C := ∫ exp(−‖z‖²)`, extracted by the UNCONDITIONAL
    `integral_const_mul`), with genuine derivative `∂_a Φ = −C·sin(a−s)` (`g s a := −(sin(a−s)·C)`, via
    `Real.hasDerivAt_cos` ∘ `(id − const)` then `.mul_const C`).  The census bound
    `|g s a| = |sin(a−s)|·|C| ≤ |C| ≤ |C|·(−s)^{−1/2} = C_far·(u−s)^{−1/2}` is met with `u=0, ε=1, h=1,
    C_far := |C|`, since `(−s)^{−1/2} = (√(−s))⁻¹ ≥ 1` for `s ∈ (−1,0)`.  The `HasDerivAt`/`sin`-bound
    machinery is genuinely exercised (NOT `0 ≤ 0`).  NOT `a₁ = R/6`. -/
theorem hfar_of_hasDerivAt_hyp_satisfiable {n : ℕ} :
    ∃ (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u ε h C_far : ℝ) (g : ℝ → ℝ → ℝ),
      0 ≤ h ∧ 0 ≤ C_far ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          HasDerivAt (fun a' => ∫ z, A (a' - s) x z * B s z y) (g s a) a) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          |g s a| ≤ C_far * (u - s) ^ (-(1 : ℝ) / 2)) := by
  classical
  refine ⟨fun τ _ z => Real.cos τ * Real.exp (-‖z‖ ^ 2), fun _ _ _ => (1 : ℝ),
    0, 0, 0, 1, 1, |∫ z : Point n, Real.exp (-‖z‖ ^ 2)|,
    fun s a => -(Real.sin (a - s) * (∫ z : Point n, Real.exp (-‖z‖ ^ 2))),
    one_pos.le, abs_nonneg _, ?_, ?_⟩
  · -- hderiv: the a-derivative of the cos·Gaussian convolution.
    intro s _ a _
    have hfun : (fun a' => ∫ z : Point n, Real.cos (a' - s) * Real.exp (-‖z‖ ^ 2) * 1)
        = fun a' => Real.cos (a' - s) * (∫ z : Point n, Real.exp (-‖z‖ ^ 2)) := by
      funext a'
      simp only [mul_one]
      rw [integral_const_mul]
    rw [hfun]
    have hcos : HasDerivAt (fun a' => Real.cos (a' - s)) (-Real.sin (a - s)) a := by
      have h1 : HasDerivAt (fun a' : ℝ => a' - s) 1 a := (hasDerivAt_id a).sub_const s
      have h2 := (Real.hasDerivAt_cos (a - s)).comp a h1
      simpa using h2
    have h3 := hcos.mul_const (∫ z : Point n, Real.exp (-‖z‖ ^ 2))
    have hval : -Real.sin (a - s) * (∫ z : Point n, Real.exp (-‖z‖ ^ 2))
        = -(Real.sin (a - s) * (∫ z : Point n, Real.exp (-‖z‖ ^ 2))) := by ring
    rw [hval] at h3
    exact h3
  · -- hgbound: |sin(a−s)|·|C| ≤ |C|·(−s)^{−1/2}.
    intro s hs a _
    simp only [Set.mem_Ioo] at hs
    have hspos : (0 : ℝ) < 0 - s := by linarith [hs.2]
    have hslt : 0 - s < 1 := by linarith [hs.1]
    have hsqrtlt : Real.sqrt (0 - s) < 1 := by
      calc Real.sqrt (0 - s) < Real.sqrt 1 := Real.sqrt_lt_sqrt hspos.le hslt
        _ = 1 := Real.sqrt_one
    have hinv : (1 : ℝ) ≤ (0 - s) ^ (-(1 : ℝ) / 2) := by
      rw [(inv_sqrt_eq_rpow (0 - s) hspos).symm]
      exact (one_le_inv₀ (Real.sqrt_pos.mpr hspos)).mpr hsqrtlt.le
    have habs : |(-(Real.sin (a - s) * (∫ z : Point n, Real.exp (-‖z‖ ^ 2))))|
        = |Real.sin (a - s)| * |∫ z : Point n, Real.exp (-‖z‖ ^ 2)| := by
      rw [abs_neg, abs_mul]
    rw [habs]
    have hsin : |Real.sin (a - s)| ≤ 1 := Real.abs_sin_le_one (a - s)
    have hCabs_nn : (0 : ℝ) ≤ |∫ z : Point n, Real.exp (-‖z‖ ^ 2)| := abs_nonneg _
    calc |Real.sin (a - s)| * |∫ z : Point n, Real.exp (-‖z‖ ^ 2)|
        ≤ 1 * |∫ z : Point n, Real.exp (-‖z‖ ^ 2)| :=
          mul_le_mul_of_nonneg_right hsin hCabs_nn
      _ = |∫ z : Point n, Real.exp (-‖z‖ ^ 2)| * 1 := by ring
      _ ≤ |∫ z : Point n, Real.exp (-‖z‖ ^ 2)| * (0 - s) ^ (-(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hinv hCabs_nn

end QIQTH.HeatResidualBound
