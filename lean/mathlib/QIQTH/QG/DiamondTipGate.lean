/-
  The DIAMOND-TIP gate, CERTIFIED (QG_CAMPAIGN_PLAN.md follow-on to I4; results in
  `docs/qg_roadmap/DIAMOND_TIP_TEST_RESULTS.md`, numerics `scripts/diamond_tip_test.py`).

  The test: does a causal-diamond truncation leave the tip vector `u^μ_D` in the vacuum effective action?
  Executed 2026-07-02 (GPT-5.5-pro-designed, two consult rounds; closed forms validated to ≤0.16%):
  • the anisotropic (tip-vector) family: `Δc²(s) = 2C·anisoH s` with `s = √(a/b)` and
    `anisoH s = (1−s)(3s²+9s+4)/(4(1+s)²)` — the χ≠1 deformation IS the diamond tip vector;
  • the rapidity-average escape fails: the boost-averaged cutoff's null log channel equals `W/12` exactly
    (LINEAR growth — not a regulator), and the boost-averaged LV operator diverges like `e^{2W}/8W`.

  Certified here (all axiom-free, std-3):
  • `anisoH_eq_zero_iff` / `tipSplit_eq_zero_iff` — within the family the splitting VANISHES IFF the
    regulator is isotropic (`s = 1`, the O(4) point): any tip-anchored truncation generically fails;
  • `anisoH_hasDerivAt_one` / `tipSplit_hasDerivAt_one` — FIRST-ORDER sensitivity: slope `−1` (resp. the
    nonzero `−2C`) at the symmetric point — the tip vector is felt at first order, not tuned away;
  • `anisoH_zero` — the spatial endpoint `anisoH 0 = 1` (consistency with the executed CPSUV gate);
  • `boostAvg_log_channel` + `boostAvg_diverges` — `∫₀^W ((W−t)/2W)² dt = W/12 → ∞`: the boost average of
    frame cutoffs has NO regulator limit (the noncompactness of the boost group, machine-checked);
  • `sinh_ge_add_cube` + `u0sq_avg_diverges` — `⟨(u⁰)²⟩_W = 1/2 + sinh(2W)/4W → ∞`: averaging the
    generated LV operator has no invariant limit either.

  ⚠ Honest scope: closed forms certified; the loop integrals are numerically validated, not formalized.
  FORCED CONCLUSION (see the results doc): finite capacity is consistent only as a STATE/ALGEBRA-LEVEL
  covariant constraint (entropy of the diamond algebra in the covariant vacuum — what the QIQT-H Lean
  formalization already is), never as a frame regulator. NOT QG. Std-3.
-/
import Mathlib
import QIQTH.QG.CpsuvGate

namespace QIQTH.QG.DiamondTip

open Real Filter intervalIntegral

/-! ## Part 1 — the tip-vector family -/

/-- The anisotropic one-loop splitting shape in `s = √(a/b)` (Gaussian both-lines scheme):
    `Δc² = 2C·anisoH s`. -/
noncomputable def anisoH (s : ℝ) : ℝ := (1 - s) * (3 * s ^ 2 + 9 * s + 4) / (4 * (1 + s) ^ 2)

/-- The spatial endpoint: `anisoH 0 = 1` (the executed CPSUV gate's `2C` value). -/
theorem anisoH_zero : anisoH 0 = 1 := by
  rw [anisoH]
  norm_num

/-- The O(4) point vanishes. -/
theorem anisoH_one : anisoH 1 = 0 := by
  rw [anisoH]
  norm_num

/-- **The tip-vector kill: within the family, the splitting is zero IFF the regulator is isotropic.**
    For `s > 0` the quadratic factor and the denominator are strictly positive, so the only zero is
    `s = 1` — any tip-anchored (`s ≠ 1`) truncation generically fails. -/
theorem anisoH_eq_zero_iff (s : ℝ) (hs : 0 < s) : anisoH s = 0 ↔ s = 1 := by
  rw [anisoH, div_eq_zero_iff]
  have hden : (4 * (1 + s) ^ 2 : ℝ) ≠ 0 := by positivity
  have hquad : (3 * s ^ 2 + 9 * s + 4 : ℝ) ≠ 0 := by positivity
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · exact absurd h' hquad
    · exact absurd h hden
  · intro h
    subst h
    norm_num

/-- **First-order sensitivity at the symmetric point: `dH/ds|₁ = −1`.** The tip deformation is felt at
    FIRST order — it cannot be tuned away by proximity to the O(4) point. -/
theorem anisoH_hasDerivAt_one : HasDerivAt anisoH (-1) 1 := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 1)
  have h2 : HasDerivAt (fun s : ℝ => 3 * s ^ 2 + 9 * s + 4) 15 1 := by
    have ha : HasDerivAt (fun s : ℝ => 3 * s ^ 2) 6 1 := by
      have := (hasDerivAt_pow 2 (1 : ℝ)).const_mul 3
      norm_num at this
      exact this
    have hb : HasDerivAt (fun s : ℝ => 9 * s) 9 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_mul 9
    have := (ha.add hb).add_const 4
    convert this using 1
    norm_num
  have hnum : HasDerivAt (fun s : ℝ => (1 - s) * (3 * s ^ 2 + 9 * s + 4)) (-16) 1 := by
    have := h1.mul h2
    norm_num at this
    exact this
  have hden : HasDerivAt (fun s : ℝ => 4 * (1 + s) ^ 2) 16 1 := by
    have hbase : HasDerivAt (fun s : ℝ => 1 + s) 1 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_add 1
    have := (hbase.pow 2).const_mul 4
    norm_num at this
    exact this
  have hden_ne : (4 * (1 + (1 : ℝ)) ^ 2 : ℝ) ≠ 0 := by norm_num
  have hdiv := hnum.div hden hden_ne
  show HasDerivAt (fun s : ℝ => (1 - s) * (3 * s ^ 2 + 9 * s + 4) / (4 * (1 + s) ^ 2)) (-1) 1
  convert hdiv using 1
  norm_num

/-- The physical splitting `Δc²(s) = 2C·anisoH s` (`C = cpsuvConst`). -/
noncomputable def tipSplit (s : ℝ) : ℝ := 2 * QIQTH.QG.Cpsuv.cpsuvConst * anisoH s

/-- **The splitting vanishes IFF isotropic** — the certified kill of tip-anchored truncations. -/
theorem tipSplit_eq_zero_iff (s : ℝ) (hs : 0 < s) : tipSplit s = 0 ↔ s = 1 := by
  rw [tipSplit, mul_eq_zero]
  have hC := QIQTH.QG.Cpsuv.cpsuvConst_pos
  constructor
  · rintro (h | h)
    · exact absurd h (by positivity)
    · exact (anisoH_eq_zero_iff s hs).mp h
  · intro h
    exact Or.inr ((anisoH_eq_zero_iff s hs).mpr h)

/-- **The certified first-order tip signature: slope `−2C ≠ 0` at the symmetric point.** -/
theorem tipSplit_hasDerivAt_one :
    HasDerivAt tipSplit (-(2 * QIQTH.QG.Cpsuv.cpsuvConst)) 1 ∧
      -(2 * QIQTH.QG.Cpsuv.cpsuvConst) ≠ 0 := by
  have hC := QIQTH.QG.Cpsuv.cpsuvConst_pos
  constructor
  · have := anisoH_hasDerivAt_one.const_mul (2 * QIQTH.QG.Cpsuv.cpsuvConst)
    have heq : 2 * QIQTH.QG.Cpsuv.cpsuvConst * (-1) = -(2 * QIQTH.QG.Cpsuv.cpsuvConst) := by ring
    rw [heq] at this
    exact this
  · intro h
    nlinarith [h]

/-! ## Part 2 — the rapidity average is not a regulator -/

/-- **The boost-averaged null log channel is EXACTLY `W/12`** — linear growth in the rapidity window:
    `∫₀^W ((W−t)/2W)² dt = W/12`. -/
theorem boostAvg_log_channel (W : ℝ) (hW : 0 < W) :
    ∫ t in (0 : ℝ)..W, ((W - t) / (2 * W)) ^ 2 = W / 12 := by
  have hW2 : (W : ℝ) ≠ 0 := hW.ne'
  have hcong : ∀ t : ℝ, ((W - t) / (2 * W)) ^ 2
      = (1 / (4 * W ^ 2)) * (W ^ 2 - 2 * W * t + t ^ 2) := by
    intro t
    field_simp
    ring
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      (1 / (4 * W ^ 2)) * (W ^ 2 - 2 * W * t + t ^ 2)) (fun t _ => hcong t),
    intervalIntegral.integral_const_mul]
  have hint2 : IntervalIntegrable (fun t : ℝ => 2 * W * t) MeasureTheory.volume 0 W :=
    intervalIntegrable_id.const_mul _
  have hpoly : (∫ t in (0 : ℝ)..W, (W ^ 2 - 2 * W * t + t ^ 2)) = W ^ 3 / 3 := by
    rw [intervalIntegral.integral_add ((_root_.intervalIntegrable_const).sub hint2)
        (intervalIntegrable_pow 2),
      intervalIntegral.integral_sub _root_.intervalIntegrable_const hint2,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
      integral_pow]
    push_cast
    ring
  rw [hpoly]
  field_simp
  ring

/-- **The no-rescue certificate: the channel DIVERGES with the window** — the boost-averaged cutoff has
    no regulator limit (`W/12 → ∞`). Averaging over the noncompact boost family of diamond frames does
    not produce covariance. -/
theorem boostAvg_diverges :
    Tendsto (fun W : ℝ => ∫ t in (0 : ℝ)..W, ((W - t) / (2 * W)) ^ 2) atTop atTop := by
  have hEq : (fun W : ℝ => W / 12) =ᶠ[atTop]
      fun W : ℝ => ∫ t in (0 : ℝ)..W, ((W - t) / (2 * W)) ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with W hW
    exact (boostAvg_log_channel W hW).symm
  exact Tendsto.congr' hEq (tendsto_id.atTop_div_const (by norm_num))

/-- The cubic lower bound `sinh x ≥ x + x³/6` for `x ≥ 0` (two monotone-antiderivative steps:
    `sinh t ≥ t` ⟹ `cosh t ≥ 1 + t²/2` ⟹ the bound). -/
theorem sinh_ge_add_cube (x : ℝ) (hx : 0 ≤ x) : x + x ^ 3 / 6 ≤ Real.sinh x := by
  have hcosh : ∀ y : ℝ, 0 ≤ y → 1 + y ^ 2 / 2 ≤ Real.cosh y := by
    intro y hy
    have hd : MonotoneOn (fun t : ℝ => Real.cosh t - 1 - t ^ 2 / 2) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact ((Real.continuous_cosh.sub continuous_const).sub
          ((continuous_pow 2).div_const 2)).continuousOn
      · exact ((Real.differentiable_cosh.sub (differentiable_const 1)).sub
          ((differentiable_pow 2).div_const 2)).differentiableOn
      · intro t ht
        have ht' : 0 ≤ t := le_of_lt (by simpa using ht)
        have hDt : HasDerivAt (fun t : ℝ => Real.cosh t - 1 - t ^ 2 / 2)
            (Real.sinh t - t) t := by
          have h1 := (Real.hasDerivAt_cosh t).sub (hasDerivAt_const t (1 : ℝ))
          have h2 := (hasDerivAt_pow 2 t).div_const 2
          have h12 := h1.sub h2
          norm_num at h12 ⊢
          convert h12 using 1
        rw [hDt.deriv]
        have hsinh : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr ht'
        linarith
    have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
    have := hd h0 (Set.mem_Ici.mpr hy) hy
    simp only [Real.cosh_zero] at this
    linarith
  have hmono2 : MonotoneOn (fun t : ℝ => Real.sinh t - t - t ^ 3 / 6) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact ((Real.continuous_sinh.sub continuous_id).sub
        ((continuous_pow 3).div_const 6)).continuousOn
    · exact ((Real.differentiable_sinh.sub differentiable_id).sub
        ((differentiable_pow 3).div_const 6)).differentiableOn
    · intro t ht
      have ht' : 0 ≤ t := le_of_lt (by simpa using ht)
      have hDt : HasDerivAt (fun t : ℝ => Real.sinh t - t - t ^ 3 / 6)
          (Real.cosh t - 1 - 3 * t ^ 2 / 6) t := by
        have h1 := (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
        have h2 := (hasDerivAt_pow 3 t).div_const 6
        have h12 := h1.sub h2
        norm_num at h12 ⊢
        convert h12 using 1
      rw [hDt.deriv]
      have := hcosh t ht'
      nlinarith
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
  have := hmono2 h0 (Set.mem_Ici.mpr hx) hx
  simp only [Real.sinh_zero] at this
  linarith

/-- The boost-averaged generated LV coefficient `⟨(u⁰)²⟩_W = 1/2 + sinh(2W)/(4W)`. -/
noncomputable def u0sqAvg (W : ℝ) : ℝ := 1 / 2 + Real.sinh (2 * W) / (4 * W)

/-- **The generated-operator average diverges too**: `⟨(u⁰)²⟩_W ≥ 1 + W²/3 → ∞` — there is no
    Lorentz-invariant limit of the averaged LV operator. -/
theorem u0sq_avg_diverges : Tendsto u0sqAvg atTop atTop := by
  have hbound : (fun W : ℝ => 1 + W ^ 2 / 3) ≤ᶠ[atTop] u0sqAvg := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with W hW
    have hs := sinh_ge_add_cube (2 * W) (by linarith)
    have hdivle : (2 * W + (2 * W) ^ 3 / 6) / (4 * W) ≤ Real.sinh (2 * W) / (4 * W) := by
      gcongr
    have heq : (2 * W + (2 * W) ^ 3 / 6) / (4 * W) = 1 / 2 + W ^ 2 / 3 := by
      field_simp
      ring
    show 1 + W ^ 2 / 3 ≤ 1 / 2 + Real.sinh (2 * W) / (4 * W)
    linarith [heq ▸ hdivle]
  have hg : Tendsto (fun W : ℝ => 1 + W ^ 2 / 3) atTop atTop :=
    tendsto_atTop_add_const_left _ 1
      ((tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num))
  exact tendsto_atTop_mono' atTop hbound hg

end QIQTH.QG.DiamondTip
