import Mathlib
import QIQTH.Sphere3HeatTrace
import QIQTH.FlatTorusHeatKernel

/-!
# The `a₁ = R/6 = 1` short-time limit on the unit `S³` (Jacobi/Euler–Maclaurin closure)

**What this file closes.** The Weyl-normalized heat trace `f(t) = t^{3/2} Θ₃(t)` on the unit 3-sphere
(`d = 3`, scalar curvature `R = 6`) satisfies the subleading Seeley–DeWitt limit
`sphere3HeatTrace_a1 : (f(t) − √π/4)/t → √π/4` as `t → 0⁺`, i.e. `f(t) = √π/4 + (√π/4)·t + o(t)`.
The subleading coefficient `√π/4 = a₀·(R/6)` with `R/6 = 1` — i.e. `a₁ = R/6` VALIDATED on a SECOND
curved manifold (a different dimension than the existing `S²` result).

**Mechanism.** From the exact reindex `Θ₃(t) = e^{t}·S(t)` (`sphere3HeatTrace_eq`, imported), with
`S(t) = Σ_{m≥1} m² e^{-t m²}` (`sphere3ShiftedSum`), the `e^{t}` factor's Taylor term `1 + t + …`
carries the `a₁` constant: writing `S(t) = (√π/4) t^{-3/2} + R(t)`, one gets
`(f(t) − √π/4)/t = e^{t}·t^{1/2}·R(t) + (√π/4)·(e^{t} − 1)/t`.  The second term `→ √π/4`
(`(e^{t}−1)/t → 1`, the derivative of `exp` at `0`), and the first `→ 0` because `t^{1/2}·R(t) → 0`.

The crux is `S(t) = (√π/4) t^{-3/2} + O(1)`, i.e. the theta remainder `R(t)` is *bounded* as
`t → 0⁺` (`R(t)` bounded suffices — the leading term is pinned by the Weyl integral; no exact
coefficient of the remainder is needed, since the `a₁` term comes from `e^{t}`, not from `S`).  This
is exactly the (first-order) Euler–Maclaurin identity `S(t) = ∫₀^∞ F + ∫₀^∞ ({x}−½) F'(x) dx` with
`F(x) = x² e^{-t x²}` (`sphere3ShiftedSum_em1`; `∫₀^∞ F = √(π/t)/(4t) = (√π/4) t^{-3/2}` is the
Weyl term, `F(0) = 0` so no `½` boundary), where a further *third-order* integration by parts against
the periodic Bernoulli functions turns the remainder into `R(t) = ∫₀^∞ Q₃(x) F'''(x) dx`
(`sphere3_R_eq`; both boundary terms vanish since `F'(0) = F'(∞) = 0`).  Because `F` is EVEN and a
pure `√t`-scaling of a fixed Schwartz profile, the odd Gaussian moments make
`∫₀^∞ |F'''(t,x)| dx = 24t·(1/2t) + 36t²·(1/2t²) + 8t³·(1/t³) = 12 + 18 + 8 = 38` a
`t`-independent constant, so `|R(t)| ≤ 19` (`sphere3_R_bound`) and `t^{1/2} R(t) → 0`.

**Firewall (binding, honest).** This VALIDATES `a₁ = R/6` on the `S³` geometry via its EXPLICIT
spectrum `{l(l+2), mult (l+1)²}` of `−Δ` (the CARRIED classical input, exactly as the circle's
`{(2πk)²}` and the `S²` `{l(l+1)}`).  It uses NONE of the missing infrastructure — no Rellich
compactness, no elliptic regularity, no trace-class API, no curved heat-kernel EXISTENCE.  It does
NOT discharge the GENERAL curved `a₁ = R/6`, which needs the manifold heat-kernel parametrix
(curvature/volume/short-time expansion) — the wall; only reachable here because the `S³` spectrum is
explicit (there is no explicit spectrum in general).  This is NOT the conjecture, NOT the strong
holographic principle, NOT quantum gravity.  No `axiom`, no `sorry`.
-/

namespace QIQTH.Sphere3HeatTrace

open scoped Real
open Filter Topology MeasureTheory

/-! ### The spectral density `F(x) = x² e^{-t x²}` and its first three derivatives -/

/-- The `S³` shifted-sum spectral density `F(x) = x² e^{-t x²}` (continuous interpolation of the
shifted-sum summand `emF t m = m² e^{-t m²}`). -/
noncomputable def emF (t x : ℝ) : ℝ := x ^ 2 * Real.exp (-t * x ^ 2)

/-- `F'(x) = (2x − 2t x³) e^{-t x²}`. -/
noncomputable def emF' (t x : ℝ) : ℝ := (2 * x - 2 * t * x ^ 3) * Real.exp (-t * x ^ 2)

/-- `F''(x) = (2 − 10t x² + 4t² x⁴) e^{-t x²}`. -/
noncomputable def emF'' (t x : ℝ) : ℝ :=
  (2 - 10 * t * x ^ 2 + 4 * t ^ 2 * x ^ 4) * Real.exp (-t * x ^ 2)

/-- `F'''(x) = (−24t x + 36t² x³ − 8t³ x⁵) e^{-t x²}`. -/
noncomputable def emF''' (t x : ℝ) : ℝ :=
  (-24 * t * x + 36 * t ^ 2 * x ^ 3 - 8 * t ^ 3 * x ^ 5) * Real.exp (-t * x ^ 2)

variable {t : ℝ}

/-- `HasDerivAt` of the gaussian factor `y ↦ e^{-t y²}`. -/
private theorem hasDerivAt_expSq (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-t * y ^ 2)) (Real.exp (-t * x ^ 2) * (-t * (2 * x))) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  exact (hpow.const_mul (-t)).exp

theorem hasDerivAt_emF (x : ℝ) : HasDerivAt (emF t) (emF' t x) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have h := hpow.mul (hasDerivAt_expSq (t := t) x)
  unfold emF emF'
  convert h using 1
  ring

theorem hasDerivAt_emF' (x : ℝ) : HasDerivAt (emF' t) (emF'' t x) x := by
  have hQ : HasDerivAt (fun y : ℝ => 2 * y - 2 * t * y ^ 3) (2 - 2 * t * (3 * x ^ 2)) x := by
    have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
    exact h1.sub (h3.const_mul (2 * t))
  have h := hQ.mul (hasDerivAt_expSq (t := t) x)
  unfold emF' emF''
  convert h using 1
  ring

theorem hasDerivAt_emF'' (x : ℝ) : HasDerivAt (emF'' t) (emF''' t x) x := by
  have hR : HasDerivAt (fun y : ℝ => 2 - 10 * t * y ^ 2 + 4 * t ^ 2 * y ^ 4)
      (-10 * t * (2 * x) + 4 * t ^ 2 * (4 * x ^ 3)) x := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by simpa using hasDerivAt_pow 4 x
    have hC : HasDerivAt (fun y : ℝ => (2 : ℝ) - 10 * t * y ^ 2) (0 - 10 * t * (2 * x)) x :=
      (hasDerivAt_const x 2).sub (h2.const_mul (10 * t))
    have hD := hC.add (h4.const_mul (4 * t ^ 2))
    convert hD using 1
    ring
  have h := hR.mul (hasDerivAt_expSq (t := t) x)
  unfold emF'' emF'''
  convert h using 1
  ring

@[fun_prop] theorem continuous_emF : Continuous (emF t) := by unfold emF; fun_prop
@[fun_prop] theorem continuous_emF' : Continuous (emF' t) := by unfold emF'; fun_prop
@[fun_prop] theorem continuous_emF'' : Continuous (emF'' t) := by unfold emF''; fun_prop
@[fun_prop] theorem continuous_emF''' : Continuous (emF''' t) := by unfold emF'''; fun_prop

theorem deriv_emF : deriv (emF t) = emF' t := funext fun x => (hasDerivAt_emF x).deriv

/-! ### Decay at `∞` and the odd Gaussian moments -/

/-- `x^n e^{-t x²} → 0` as `x → ∞` (dominated by `x^n e^{-t x}` for `x ≥ 1`). -/
private theorem pow_mul_expSq_tendsto (ht : 0 < t) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-t * x ^ 2)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-t * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) t ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlin ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxn : x ^ (n : ℝ) = x ^ n := by rw [Real.rpow_natCast]
    have hle : Real.exp (-t * x ^ 2) ≤ Real.exp (-t * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg ht.le (mul_nonneg (by linarith : (0 : ℝ) ≤ x)
        (by linarith : (0 : ℝ) ≤ x - 1))]
    rw [hxn]
    exact mul_le_mul_of_nonneg_left hle (pow_nonneg (by linarith) n)

theorem emF_tendsto_zero (ht : 0 < t) : Tendsto (emF t) atTop (𝓝 0) := by
  refine (pow_mul_expSq_tendsto ht 2).congr (fun x => ?_); unfold emF; ring

theorem emF'_tendsto_zero (ht : 0 < t) : Tendsto (emF' t) atTop (𝓝 0) := by
  have h1 := pow_mul_expSq_tendsto ht 1
  have h3 := pow_mul_expSq_tendsto ht 3
  have hc := (h1.const_mul (2 : ℝ)).sub (h3.const_mul (2 * t))
  simp only [mul_zero, sub_zero] at hc
  refine hc.congr (fun x => ?_); unfold emF'; ring

/-- `∫_{(0,∞)} x³ e^{-t x²} = 1/(2t²)`. FTC with antiderivative `(−x²/(2t) − 1/(2t²)) e^{-t x²}`. -/
theorem momExp3 (ht : 0 < t) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ 3 * Real.exp (-t * x ^ 2) = 1 / (2 * t ^ 2) := by
  have ht0 : t ≠ 0 := ht.ne'
  set g : ℝ → ℝ := fun x => (-(x ^ 2 / (2 * t)) - 1 / (2 * t ^ 2)) * Real.exp (-t * x ^ 2) with hg
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (x ^ 3 * Real.exp (-t * x ^ 2)) x := by
    intro x _
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have hP : HasDerivAt (fun y : ℝ => -(y ^ 2 / (2 * t)) - 1 / (2 * t ^ 2))
        (-((2 * x) / (2 * t))) x := ((h2.div_const (2 * t)).neg).sub_const (1 / (2 * t ^ 2))
    have h := hP.mul (hasDerivAt_expSq (t := t) x)
    convert h using 1
    field_simp
    ring
  have hint : IntegrableOn (fun x : ℝ => x ^ 3 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq ht (by norm_num : (-1 : ℝ) < 3)).integrableOn
      (s := Set.Ioi (0 : ℝ))
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have htend : Tendsto g atTop (𝓝 0) := by
    have h2 := pow_mul_expSq_tendsto ht 2
    have h0 := pow_mul_expSq_tendsto ht 0
    have hc := (h2.const_mul (-(1 / (2 * t)))).sub (h0.const_mul (1 / (2 * t ^ 2)))
    simp only [mul_zero, sub_zero] at hc
    refine hc.congr (fun x => ?_); rw [hg]; simp only [pow_zero, one_mul]; ring
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [hmain]
  have hg0 : g 0 = -(1 / (2 * t ^ 2)) := by rw [hg]; simp
  rw [hg0]; ring

/-- `∫_{(0,∞)} x⁵ e^{-t x²} = 1/t³`. FTC with antiderivative `(−x⁴/(2t) − x²/t² − 1/t³) e^{-t x²}`. -/
theorem momExp5 (ht : 0 < t) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ 5 * Real.exp (-t * x ^ 2) = 1 / t ^ 3 := by
  have ht0 : t ≠ 0 := ht.ne'
  set g : ℝ → ℝ :=
    fun x => (-(x ^ 4 / (2 * t)) - x ^ 2 / t ^ 2 - 1 / t ^ 3) * Real.exp (-t * x ^ 2) with hg
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (x ^ 5 * Real.exp (-t * x ^ 2)) x := by
    intro x _
    have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by simpa using hasDerivAt_pow 4 x
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have hP : HasDerivAt (fun y : ℝ => -(y ^ 4 / (2 * t)) - y ^ 2 / t ^ 2 - 1 / t ^ 3)
        (-((4 * x ^ 3) / (2 * t)) - (2 * x) / t ^ 2) x :=
      (((h4.div_const (2 * t)).neg).sub (h2.div_const (t ^ 2))).sub_const (1 / t ^ 3)
    have h := hP.mul (hasDerivAt_expSq (t := t) x)
    convert h using 1
    field_simp
    ring
  have hint : IntegrableOn (fun x : ℝ => x ^ 5 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq ht (by norm_num : (-1 : ℝ) < 5)).integrableOn
      (s := Set.Ioi (0 : ℝ))
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have htend : Tendsto g atTop (𝓝 0) := by
    have h4 := pow_mul_expSq_tendsto ht 4
    have h2 := pow_mul_expSq_tendsto ht 2
    have h0 := pow_mul_expSq_tendsto ht 0
    have hc := ((h4.const_mul (-(1 / (2 * t)))).sub (h2.const_mul (1 / t ^ 2))).sub
      (h0.const_mul (1 / t ^ 3))
    simp only [mul_zero, sub_zero] at hc
    refine hc.congr (fun x => ?_); rw [hg]; simp only [pow_zero, one_mul]; ring
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [hmain]
  have hg0 : g 0 = -(1 / t ^ 3) := by rw [hg]; simp
  rw [hg0]; ring

/-! ### Integrability -/

theorem integrableOn_emF (ht : 0 < t) : IntegrableOn (emF t) (Set.Ioi (0 : ℝ)) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq ht (by norm_num : (-1 : ℝ) < 2)).integrableOn
    (s := Set.Ioi (0 : ℝ))
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [emF]; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem intOn_xk (ht : 0 < t) {r : ℝ} (hr : -1 < r) {k : ℕ} (hk : (k : ℝ) = r) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq ht hr).integrableOn (s := Set.Ioi (0 : ℝ))
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [← hk, Real.rpow_natCast]

theorem integrableOn_emF' (ht : 0 < t) : IntegrableOn (emF' t) (Set.Ioi (0 : ℝ)) := by
  have hM1 : IntegrableOn (fun x : ℝ => x ^ 1 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    intOn_xk ht (by norm_num : (-1 : ℝ) < 1) (by norm_num)
  have hM3 : IntegrableOn (fun x : ℝ => x ^ 3 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    intOn_xk ht (by norm_num : (-1 : ℝ) < 3) (by norm_num)
  have h : IntegrableOn (fun x : ℝ => 2 * (x ^ 1 * Real.exp (-t * x ^ 2))
      - 2 * t * (x ^ 3 * Real.exp (-t * x ^ 2))) (Set.Ioi (0 : ℝ)) :=
    (hM1.const_mul (2 : ℝ)).sub (hM3.const_mul (2 * t))
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  unfold emF'; ring

theorem integrableOn_emF''' (ht : 0 < t) : IntegrableOn (emF''' t) (Set.Ioi (0 : ℝ)) := by
  have hM1 : IntegrableOn (fun x : ℝ => x ^ 1 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    intOn_xk ht (by norm_num : (-1 : ℝ) < 1) (by norm_num)
  have hM3 : IntegrableOn (fun x : ℝ => x ^ 3 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    intOn_xk ht (by norm_num : (-1 : ℝ) < 3) (by norm_num)
  have hM5 : IntegrableOn (fun x : ℝ => x ^ 5 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    intOn_xk ht (by norm_num : (-1 : ℝ) < 5) (by norm_num)
  have h : IntegrableOn (fun x : ℝ => -24 * t * (x ^ 1 * Real.exp (-t * x ^ 2))
      + 36 * t ^ 2 * (x ^ 3 * Real.exp (-t * x ^ 2))
      + -8 * t ^ 3 * (x ^ 5 * Real.exp (-t * x ^ 2))) (Set.Ioi (0 : ℝ)) :=
    ((hM1.const_mul (-24 * t)).add (hM3.const_mul (36 * t ^ 2))).add (hM5.const_mul (-8 * t ^ 3))
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  unfold emF'''; ring

theorem integrableOn_emF'_fract (ht : 0 < t) :
    IntegrableOn (fun x => emF' t x * Int.fract x) (Set.Ioi (0 : ℝ)) := by
  have hI := integrableOn_emF' ht
  have hmeas : AEStronglyMeasurable (fun x => emF' t x * Int.fract x)
      (volume.restrict (Set.Ioi 0)) :=
    continuous_emF'.aestronglyMeasurable.mul measurable_fract.aestronglyMeasurable
  refine Integrable.mono' hI.norm hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _
  rw [norm_mul, Real.norm_eq_abs]
  have hf : |Int.fract x| ≤ 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg x)]; exact (Int.fract_lt_one x).le
  calc ‖emF' t x‖ * ‖Int.fract x‖ ≤ ‖emF' t x‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rwa [Real.norm_eq_abs]
    _ = ‖emF' t x‖ := by ring

/-- `∫_{(0,∞)} F'(x) dx = F(∞) − F(0) = 0`. -/
theorem integral_emF'_eq (ht : 0 < t) : ∫ x in Set.Ioi (0 : ℝ), emF' t x = 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x (_ : x ∈ Set.Ici (0 : ℝ)) =>
    hasDerivAt_emF x) (integrableOn_emF' ht) (emF_tendsto_zero ht)
  rw [h]; simp [emF]

/-! ### The `∫|F'''| = 38` constant bound (odd Gaussian moments) -/

/-- `∫_{(0,∞)} |F'''(t,x)| dx ≤ 38`, a `t`-independent constant. Pointwise
`|F'''| ≤ (24t x + 36t² x³ + 8t³ x⁵) e^{-t x²}`, whose integral is
`24t·(1/2t) + 36t²·(1/2t²) + 8t³·(1/t³) = 12 + 18 + 8 = 38`. -/
theorem emF'''_abs_int_le (ht : 0 < t) :
    ∫ x in Set.Ioi (0 : ℝ), |emF''' t x| ≤ 38 := by
  have ht0 : t ≠ 0 := ht.ne'
  have hM1 : IntegrableOn (fun x : ℝ => x * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    (integrable_mul_exp_neg_mul_sq ht).integrableOn
  have hM3 : IntegrableOn (fun x : ℝ => x ^ 3 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    intOn_xk ht (by norm_num : (-1 : ℝ) < 3) (by norm_num)
  have hM5 : IntegrableOn (fun x : ℝ => x ^ 5 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    intOn_xk ht (by norm_num : (-1 : ℝ) < 5) (by norm_num)
  have habs : IntegrableOn (fun x => |emF''' t x|) (Set.Ioi (0 : ℝ)) := (integrableOn_emF''' ht).abs
  set D : ℝ → ℝ := fun x => 24 * t * (x * Real.exp (-t * x ^ 2))
      + 36 * t ^ 2 * (x ^ 3 * Real.exp (-t * x ^ 2))
      + 8 * t ^ 3 * (x ^ 5 * Real.exp (-t * x ^ 2)) with hD
  have hDint : IntegrableOn D (Set.Ioi (0 : ℝ)) :=
    ((hM1.const_mul (24 * t)).add (hM3.const_mul (36 * t ^ 2))).add (hM5.const_mul (8 * t ^ 3))
  have hDval : ∫ x in Set.Ioi (0 : ℝ), D x = 38 := by
    have hAdd1 : IntegrableOn (fun x : ℝ => 24 * t * (x * Real.exp (-t * x ^ 2))
        + 36 * t ^ 2 * (x ^ 3 * Real.exp (-t * x ^ 2))) (Set.Ioi (0 : ℝ)) :=
      (hM1.const_mul (24 * t)).add (hM3.const_mul (36 * t ^ 2))
    have hC5 : IntegrableOn (fun x : ℝ => 8 * t ^ 3 * (x ^ 5 * Real.exp (-t * x ^ 2)))
        (Set.Ioi (0 : ℝ)) := hM5.const_mul (8 * t ^ 3)
    simp only [hD]
    rw [integral_add hAdd1 hC5, integral_add (hM1.const_mul (24 * t)) (hM3.const_mul (36 * t ^ 2)),
      integral_const_mul, integral_const_mul, integral_const_mul,
      gaussMoment1 ht, momExp3 ht, momExp5 ht]
    field_simp
    ring
  calc ∫ x in Set.Ioi (0 : ℝ), |emF''' t x|
      ≤ ∫ x in Set.Ioi (0 : ℝ), D x := by
        apply setIntegral_mono_on habs hDint measurableSet_Ioi
        intro x hx
        have hx0 : (0 : ℝ) < x := hx
        have hEpos : 0 < Real.exp (-t * x ^ 2) := Real.exp_pos _
        have hcoef : |(-24 * t * x + 36 * t ^ 2 * x ^ 3 - 8 * t ^ 3 * x ^ 5)|
            ≤ 24 * t * x + 36 * t ^ 2 * x ^ 3 + 8 * t ^ 3 * x ^ 5 := by
          rw [abs_le]; constructor <;>
            nlinarith [mul_nonneg ht.le hx0.le,
              mul_nonneg (pow_nonneg ht.le 2) (pow_nonneg hx0.le 3),
              mul_nonneg (pow_nonneg ht.le 3) (pow_nonneg hx0.le 5)]
        calc |emF''' t x|
            = |(-24 * t * x + 36 * t ^ 2 * x ^ 3 - 8 * t ^ 3 * x ^ 5)| * Real.exp (-t * x ^ 2) := by
              unfold emF'''; rw [abs_mul, abs_of_pos hEpos]
          _ ≤ (24 * t * x + 36 * t ^ 2 * x ^ 3 + 8 * t ^ 3 * x ^ 5) * Real.exp (-t * x ^ 2) :=
              mul_le_mul_of_nonneg_right hcoef hEpos.le
          _ = D x := by rw [hD]; ring
    _ = 38 := hDval

/-! ### The periodic Bernoulli antiderivatives `Q₃`, `p₂`, `p₃` (verbatim substrate) -/

/-- `Q₃(x) = {x}³/6 − {x}²/4 + {x}/12`, the periodic Bernoulli-3 antiderivative. -/
noncomputable def emQ3 (x : ℝ) : ℝ :=
  (Int.fract x) ^ 3 / 6 - (Int.fract x) ^ 2 / 4 + (Int.fract x) / 12

/-- `p₂(x) = (x−n)²/2 − (x−n)/2 + 1/12` on `[n, n+1]`. -/
noncomputable def emP2 (n : ℕ) (x : ℝ) : ℝ := (x - n) ^ 2 / 2 - (x - n) / 2 + 1 / 12

/-- `p₃(x) = (x−n)³/6 − (x−n)²/4 + (x−n)/12` on `[n, n+1]`. -/
noncomputable def emP3 (n : ℕ) (x : ℝ) : ℝ := (x - n) ^ 3 / 6 - (x - n) ^ 2 / 4 + (x - n) / 12

@[fun_prop] theorem continuous_emP2 (n : ℕ) : Continuous (emP2 n) := by unfold emP2; fun_prop
@[fun_prop] theorem continuous_emP3 (n : ℕ) : Continuous (emP3 n) := by unfold emP3; fun_prop

theorem hasDerivAt_emP2 (n : ℕ) (x : ℝ) : HasDerivAt (emP2 n) ((x - n) - 1 / 2) x := by
  have hb : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x := by
    simpa using (hasDerivAt_id x).sub_const (n : ℝ)
  have hsq : HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 2) (2 * (x - n) * 1) x := by
    simpa using hb.pow 2
  have h := ((hsq.div_const 2).sub (hb.div_const 2)).add_const (1 / 12 : ℝ)
  show HasDerivAt (emP2 n) ((x - n) - 1 / 2) x
  unfold emP2; convert h using 1; ring

theorem hasDerivAt_emP3 (n : ℕ) (x : ℝ) : HasDerivAt (emP3 n) (emP2 n x) x := by
  have hb : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x := by
    simpa using (hasDerivAt_id x).sub_const (n : ℝ)
  have hcube : HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 3) (3 * (x - n) ^ 2 * 1) x := by
    simpa using hb.pow 3
  have hsq : HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 2) (2 * (x - n) * 1) x := by
    simpa using hb.pow 2
  have h := ((hcube.div_const 6).sub (hsq.div_const 4)).add (hb.div_const 12)
  show HasDerivAt (emP3 n) (emP2 n x) x
  unfold emP3; convert h using 1; unfold emP2; ring

theorem emP2_left (n : ℕ) : emP2 n (n : ℝ) = 1 / 12 := by unfold emP2; simp
theorem emP2_right (n : ℕ) : emP2 n ((n : ℝ) + 1) = 1 / 12 := by unfold emP2; ring
theorem emP3_left (n : ℕ) : emP3 n (n : ℝ) = 0 := by unfold emP3; simp
theorem emP3_right (n : ℕ) : emP3 n ((n : ℝ) + 1) = 0 := by unfold emP3; ring

theorem fract_eq_sub_natCast (n : ℕ) {x : ℝ} (hx0 : (n : ℝ) ≤ x) (hx1 : x < (n : ℝ) + 1) :
    Int.fract x = x - (n : ℝ) := by
  have hfloor : ⌊x⌋ = (n : ℤ) := by
    rw [Int.floor_eq_iff]; refine ⟨by push_cast; linarith, by push_cast; linarith⟩
  have h := Int.self_sub_fract x
  rw [hfloor] at h; push_cast at h; linarith

theorem emQ3_eq_emP3 (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    emQ3 x = emP3 n x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · have hx1 : x = (n : ℝ) + 1 := h
    have hfr : Int.fract x = 0 := by
      rw [hx1, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Int.fract_natCast]
    rw [hx1]; unfold emQ3 emP3; rw [hx1] at hfr; rw [hfr]; norm_num
  · have hfr : Int.fract x = x - (n : ℝ) := fract_eq_sub_natCast n hx.1 h
    unfold emQ3 emP3; rw [hfr]

theorem emQ3_bound (x : ℝ) : |emQ3 x| ≤ 1 / 2 := by
  have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  unfold emQ3
  rw [abs_le]
  constructor <;>
    nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) (mul_nonneg h0 h0),
      mul_nonneg (sub_nonneg.mpr h1.le) h0, mul_nonneg (mul_nonneg h0 h0) h0, h0, h1]

theorem measurable_emQ3 : Measurable emQ3 := by
  unfold emQ3
  exact (((measurable_fract.pow_const 3).div_const 6).sub
    ((measurable_fract.pow_const 2).div_const 4)).add (measurable_fract.div_const 12)

theorem integrableOn_fract_sub_half_mul_emF' (ht : 0 < t) :
    IntegrableOn (fun x => (Int.fract x - 1 / 2) * emF' t x) (Set.Ioi (0 : ℝ)) := by
  have h1 := integrableOn_emF'_fract ht
  have h2 := (integrableOn_emF' ht).const_mul (1 / 2)
  refine (h1.sub h2).congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]; ring

theorem integrableOn_emQ3_mul_emF''' (ht : 0 < t) :
    IntegrableOn (fun x => emQ3 x * emF''' t x) (Set.Ioi (0 : ℝ)) := by
  refine Integrable.mono' ((integrableOn_emF''' ht).norm.const_mul (1 / 2))
    (measurable_emQ3.mul continuous_emF'''.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |emQ3 x| * |emF''' t x| ≤ (1 / 2) * |emF''' t x| :=
        mul_le_mul_of_nonneg_right (emQ3_bound x) (abs_nonneg _)
    _ = 1 / 2 * ‖emF''' t x‖ := by rw [Real.norm_eq_abs]

/-! ### Third-order Euler–Maclaurin: `∫ ({x}−½) F' = ∫ Q₃ F'''` -/

theorem ibp_interval (n : ℕ) :
    ∫ x in (n : ℝ)..((n : ℝ) + 1), (Int.fract x - 1 / 2) * emF' t x
      = (1 / 12) * (emF' t ((n : ℝ) + 1) - emF' t (n : ℝ))
        + ∫ x in (n : ℝ)..((n : ℝ) + 1), emQ3 x * emF''' t x := by
  have iiφ'' : IntervalIntegrable (emF'' t) volume (n : ℝ) ((n : ℝ) + 1) :=
    continuous_emF''.intervalIntegrable _ _
  have iiφ''' : IntervalIntegrable (emF''' t) volume (n : ℝ) ((n : ℝ) + 1) :=
    continuous_emF'''.intervalIntegrable _ _
  have iip2' : IntervalIntegrable (fun x => (x - (n : ℝ)) - 1 / 2) volume (n : ℝ) ((n : ℝ) + 1) :=
    (by fun_prop : Continuous fun x : ℝ => (x - (n : ℝ)) - 1 / 2).intervalIntegrable _ _
  have iip2 : IntervalIntegrable (emP2 n) volume (n : ℝ) ((n : ℝ) + 1) :=
    (continuous_emP2 n).intervalIntegrable _ _
  have eqI := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n : ℝ) + 1)
    (u := emP2 n) (v := emF' t) (u' := fun x => (x - (n : ℝ)) - 1 / 2) (v' := emF'' t)
    (fun x _ => hasDerivAt_emP2 n x) (fun x _ => hasDerivAt_emF' x) iip2' iiφ''
  have eqII := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n : ℝ) + 1)
    (u := emP3 n) (v := emF'' t) (u' := emP2 n) (v' := emF''' t)
    (fun x _ => hasDerivAt_emP3 n x) (fun x _ => hasDerivAt_emF'' x) iip2 iiφ'''
  rw [emP2_left, emP2_right] at eqI
  rw [emP3_left, emP3_right] at eqII
  simp only [zero_mul, sub_zero, zero_sub] at eqII
  have haeq : ∫ x in (n : ℝ)..((n : ℝ) + 1), (Int.fract x - 1 / 2) * emF' t x
      = ∫ x in (n : ℝ)..((n : ℝ) + 1), ((x - (n : ℝ)) - 1 / 2) * emF' t x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : {((n : ℝ) + 1)}ᶜ ∈ ae volume := compl_mem_ae_iff.mpr (measure_singleton _)
    filter_upwards [hnull] with x hx hmem
    have hxne : x ≠ (n : ℝ) + 1 := hx
    rw [Set.uIoc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hmem
    have hx1 : x < (n : ℝ) + 1 := lt_of_le_of_ne hmem.2 hxne
    have hfr : Int.fract x = x - (n : ℝ) := fract_eq_sub_natCast n (le_of_lt hmem.1) hx1
    rw [show (Int.fract x - 1 / 2) = ((x - (n : ℝ)) - 1 / 2) by rw [hfr]]
  have hceq : ∫ x in (n : ℝ)..((n : ℝ) + 1), emQ3 x * emF''' t x
      = ∫ x in (n : ℝ)..((n : ℝ) + 1), emP3 n x * emF''' t x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hx
    show emQ3 x * emF''' t x = emP3 n x * emF''' t x
    rw [emQ3_eq_emP3 n hx]
  rw [haeq, hceq]
  linarith [eqI, eqII]

theorem heat_em3_partial (ht : 0 < t) (N : ℕ) :
    ∫ x in (0 : ℝ)..(N : ℝ), (Int.fract x - 1 / 2) * emF' t x
      = (1 / 12) * (emF' t (N : ℝ) - emF' t 0)
        + ∫ x in (0 : ℝ)..(N : ℝ), emQ3 x * emF''' t x := by
  have hgInt := integrableOn_fract_sub_half_mul_emF' ht
  have hqInt := integrableOn_emQ3_mul_emF''' ht
  have hgIIab : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      IntervalIntegrable (fun x => (Int.fract x - 1 / 2) * emF' t x) volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hgInt.mono_set (fun x hx => lt_of_le_of_lt ha hx.1)
  have hqIIab : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      IntervalIntegrable (fun x => emQ3 x * emF''' t x) volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hqInt.mono_set (fun x hx => lt_of_le_of_lt ha hx.1)
  induction N with
  | zero => simp
  | succ M IH =>
    have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    rw [hcast,
      ← intervalIntegral.integral_add_adjacent_intervals
        (hgIIab 0 (M : ℝ) le_rfl (Nat.cast_nonneg M))
        (hgIIab (M : ℝ) ((M : ℝ) + 1) (Nat.cast_nonneg M) (by linarith)),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hqIIab 0 (M : ℝ) le_rfl (Nat.cast_nonneg M))
        (hqIIab (M : ℝ) ((M : ℝ) + 1) (Nat.cast_nonneg M) (by linarith)),
      IH, ibp_interval M]
    ring

/-- **The theta remainder as an `Q₃ F'''` integral.** `∫_{(0,∞)} ({x}−½) F' = ∫_{(0,∞)} Q₃ F'''`,
since the telescoped boundary `(1/12)(F'(∞) − F'(0)) = 0` (`F'(0) = F'(∞) = 0`). -/
theorem sphere3_R_eq (ht : 0 < t) :
    (∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emF' t x)
      = ∫ x in Set.Ioi (0 : ℝ), emQ3 x * emF''' t x := by
  have hL : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ), (Int.fract x - 1 / 2) * emF' t x)
      atTop (𝓝 (∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emF' t x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_fract_sub_half_mul_emF' ht)
      tendsto_natCast_atTop_atTop
  have hQ : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ), emQ3 x * emF''' t x)
      atTop (𝓝 (∫ x in Set.Ioi (0 : ℝ), emQ3 x * emF''' t x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_emQ3_mul_emF''' ht)
      tendsto_natCast_atTop_atTop
  have hF'N : Tendsto (fun N : ℕ => emF' t (N : ℝ)) atTop (𝓝 0) :=
    (emF'_tendsto_zero ht).comp tendsto_natCast_atTop_atTop
  have hbd : Tendsto (fun N : ℕ => (1 / 12) * (emF' t (N : ℝ) - emF' t 0)) atTop
      (𝓝 ((1 / 12) * (0 - emF' t 0))) := (hF'N.sub_const (emF' t 0)).const_mul (1 / 12)
  have huniq := tendsto_nhds_unique (hL.congr (fun N => heat_em3_partial ht N)) (hbd.add hQ)
  rw [huniq]
  have hF'0 : emF' t 0 = 0 := by simp [emF']
  rw [hF'0]; ring

/-- **The remainder is bounded by `19`.** `|∫_{(0,∞)} ({x}−½) F'| ≤ (1/2)·∫|F'''| ≤ (1/2)·38 = 19`. -/
theorem sphere3_R_bound (ht : 0 < t) :
    |∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emF' t x| ≤ 19 := by
  rw [sphere3_R_eq ht, ← Real.norm_eq_abs]
  calc ‖∫ x in Set.Ioi (0 : ℝ), emQ3 x * emF''' t x‖
      ≤ ∫ x in Set.Ioi (0 : ℝ), ‖emQ3 x * emF''' t x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), (1 / 2) * |emF''' t x| := by
        apply setIntegral_mono_on (integrableOn_emQ3_mul_emF''' ht).norm
          ((integrableOn_emF''' ht).abs.const_mul (1 / 2)) measurableSet_Ioi
        intro x _
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (emQ3_bound x) (abs_nonneg _)
    _ = (1 / 2) * ∫ x in Set.Ioi (0 : ℝ), |emF''' t x| := by rw [integral_const_mul]
    _ ≤ (1 / 2) * 38 := mul_le_mul_of_nonneg_left (emF'''_abs_int_le ht) (by norm_num)
    _ = 19 := by norm_num

/-! ### The EM-1 identity and the assembled `a₁` limit -/

/-- **First-order Euler–Maclaurin (Abel) identity** for the shifted sum:
`Σ_{k=0}^{m} F(k) = ∫_0^m F + ∫_0^m F'(x)·{x} dx` (with `F(0) = 0`, so no boundary term). -/
theorem emFinite (ht : 0 < t) (m : ℕ) :
    ∑ k ∈ Finset.Icc 0 m, emF t k
      = (∫ x in (0 : ℝ)..m, emF t x) + (∫ x in (0 : ℝ)..m, emF' t x * Int.fract x) := by
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) m, DifferentiableAt ℝ (emF t) x :=
    fun x _ => (hasDerivAt_emF x).differentiableAt
  have hintderiv : IntegrableOn (deriv (emF t)) (Set.Icc (0 : ℝ) m) := by
    rw [deriv_emF]; exact continuous_emF'.integrableOn_Icc
  have key := sum_mul_eq_sub_integral_mul' (c := fun _ => (1 : ℝ)) (f := emF t) m hdiff hintderiv
  simp only [mul_one] at key
  rw [key]
  have hcard : (∑ _k ∈ Finset.Icc 0 m, (1 : ℝ)) = (m : ℝ) + 1 := by
    rw [Finset.sum_const, Nat.card_Icc]; push_cast; ring
  rw [hcard, deriv_emF]
  have hfloor : ∫ x in Set.Ioc (0 : ℝ) m, emF' t x * ∑ _k ∈ Finset.Icc 0 ⌊x⌋₊, (1 : ℝ)
      = ∫ x in Set.Ioc (0 : ℝ) m, emF' t x * ((⌊x⌋₊ : ℝ) + 1) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only [Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul, mul_one]
    push_cast; ring
  rw [hfloor, ← intervalIntegral.integral_of_le (Nat.cast_nonneg m)]
  have hint_x1 : IntervalIntegrable (fun x => emF' t x * (x + 1)) volume 0 m :=
    (continuous_emF'.mul (by fun_prop)).intervalIntegrable _ _
  have hint_fr : IntervalIntegrable (fun x => emF' t x * Int.fract x) volume 0 m :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg m)).mpr
      ((integrableOn_emF'_fract ht).mono_set Set.Ioc_subset_Ioi_self)
  have e1 : ∫ x in (0 : ℝ)..m, emF' t x * ((⌊x⌋₊ : ℝ) + 1)
      = ∫ x in (0 : ℝ)..m, (emF' t x * (x + 1) - emF' t x * Int.fract x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (Nat.cast_nonneg m)] at hx
    have hx0 : 0 ≤ x := hx.1
    have hfl : (⌊x⌋₊ : ℝ) = x - Int.fract x := by
      have h2 : (⌊x⌋₊ : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast Int.natCast_floor_eq_floor hx0
      rw [Int.fract, h2]; ring
    simp only [hfl]; ring
  rw [e1, intervalIntegral.integral_sub hint_x1 hint_fr]
  have hIBP : ∫ x in (0 : ℝ)..m, emF' t x * (x + 1)
      = emF t m * (m + 1) - emF t 0 * 1 - ∫ x in (0 : ℝ)..m, emF t x := by
    have hpsi : ∀ x : ℝ, HasDerivAt (fun y => emF t y * (y + 1))
        (emF' t x * (x + 1) + emF t x * 1) x := by
      intro x
      exact (hasDerivAt_emF x).mul (by simpa using (hasDerivAt_id x).add_const 1)
    have hftc : ∫ x in (0 : ℝ)..m, (emF' t x * (x + 1) + emF t x * 1)
        = (emF t m * (m + 1)) - (emF t 0 * (0 + 1)) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hpsi x)]
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [intervalIntegral.integral_add (hint_x1)
      (Continuous.intervalIntegrable (u := fun x : ℝ => emF t x * 1) (by fun_prop) _ _)] at hftc
    simp only [mul_one] at hftc ⊢; linarith [hftc]
  rw [hIBP]
  have hF0 : emF t 0 = 0 := by simp [emF]
  rw [hF0]; ring

theorem sphere3ShiftedSum_emFract (ht : 0 < t) :
    sphere3ShiftedSum t
      = (∫ x in Set.Ioi (0 : ℝ), emF t x) + ∫ x in Set.Ioi (0 : ℝ), emF' t x * Int.fract x := by
  have htendL : Tendsto (fun m : ℕ => ∑ k ∈ Finset.Icc 0 m, emF t k) atTop
      (𝓝 (sphere3ShiftedSum t)) := by
    have h1 : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, emF t k
        = ∑ k ∈ Finset.range (m + 1), (k : ℝ) ^ 2 * Real.exp (-t * (k : ℝ) ^ 2) := by
      intro m; rw [← Nat.range_succ_eq_Icc_zero]; rfl
    simp_rw [h1]
    exact ((sphere3ShiftedSum_summable ht).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have htendF : Tendsto (fun m : ℕ => ∫ x in (0 : ℝ)..m, emF t x) atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), emF t x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_emF ht) tendsto_natCast_atTop_atTop
  have htendfr : Tendsto (fun m : ℕ => ∫ x in (0 : ℝ)..m, emF' t x * Int.fract x) atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), emF' t x * Int.fract x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_emF'_fract ht) tendsto_natCast_atTop_atTop
  have := tendsto_nhds_unique (htendL.congr (fun m => emFinite ht m)) (htendF.add htendfr)
  rw [this]

/-- **The EM-1 identity for the shifted sum:** `S(t) = √(π/t)/(4t) + ∫_{(0,∞)} ({x}−½) F'(x) dx`.
The `√(π/t)/(4t) = (√π/4) t^{-3/2}` is the Weyl `a₀` integral `∫₀^∞ F`; `F(0) = 0` and `∫₀^∞ F' = 0`
mean there is no `½`-boundary and `∫({x}−½)F' = ∫{x}F'` exactly. -/
theorem sphere3ShiftedSum_em1 (ht : 0 < t) :
    sphere3ShiftedSum t
      = Real.sqrt (π / t) / (4 * t) + ∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emF' t x := by
  have hF : (∫ x in Set.Ioi (0 : ℝ), emF t x) = Real.sqrt (π / t) / (4 * t) := by
    simp only [emF]; exact gaussMoment2 ht
  have hconv : ∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emF' t x
      = ∫ x in Set.Ioi (0 : ℝ), emF' t x * Int.fract x := by
    have hsplit : ∀ x, (Int.fract x - 1 / 2) * emF' t x
        = emF' t x * Int.fract x - (1 / 2) * emF' t x := fun x => by ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hsplit x),
      MeasureTheory.integral_sub (integrableOn_emF'_fract ht)
        ((integrableOn_emF' ht).const_mul (1 / 2)),
      MeasureTheory.integral_const_mul, integral_emF'_eq ht, mul_zero, sub_zero]
  rw [sphere3ShiftedSum_emFract ht, hconv, hF]

private lemma rpow32_eq (ht : 0 < t) : t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

private lemma A_scale (ht : 0 < t) :
    t ^ ((3 : ℝ) / 2) * (Real.sqrt (π / t) / (4 * t)) = Real.sqrt π / 4 := by
  have hsp : Real.sqrt t * Real.sqrt (π / t) = Real.sqrt π := by
    rw [← Real.sqrt_mul ht.le]; congr 1; field_simp
  rw [rpow32_eq ht, show t * Real.sqrt t * (Real.sqrt (π / t) / (4 * t))
    = (Real.sqrt t * Real.sqrt (π / t)) * (t / (4 * t)) by ring, hsp,
    show t / (4 * t) = 1 / 4 by field_simp]
  ring

/-- **★★★ The `a₁ = R/6 = 1` short-time limit on the unit `S³`.**
`(t^{3/2} Θ₃(t) − √π/4)/t → √π/4` as `t → 0⁺`, i.e. `t^{3/2} Θ₃(t) = √π/4 + (√π/4) t + o(t)`.
The subleading coefficient `√π/4 = a₀·(R/6)` with `R/6 = 1` — the Seeley–DeWitt curvature term on a
SECOND curved manifold (dimension `d = 3`, `R = 6`), obtained from the reindex `Θ₃ = e^{t}·S`, the
EM-1 identity `S(t) = (√π/4) t^{-3/2} + R(t)` (`sphere3ShiftedSum_em1`) with `|R(t)| ≤ 19`
(`sphere3_R_bound`), and `(e^{t}−1)/t → 1`. -/
theorem sphere3HeatTrace_a1 :
    Filter.Tendsto (fun t : ℝ => (t ^ ((3 : ℝ) / 2) * sphere3HeatTrace t - Real.sqrt π / 4) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt π / 4)) := by
  -- `(e^t − 1)/t → 1` (derivative of `exp` at `0`).
  have hE1 : Tendsto (fun t : ℝ => (Real.exp t - 1) / t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_exp 0)
    rw [Real.exp_zero] at h
    have hmono : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono 0 (fun x hx => ne_of_gt hx)
    refine (h.mono_left hmono).congr (fun s => ?_)
    rw [slope_def_field, Real.exp_zero, sub_zero]
  have hexp1 : Tendsto (fun t : ℝ => Real.exp t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Tendsto (fun t : ℝ => Real.exp t) (𝓝 (0 : ℝ)) (𝓝 1) := by
      simpa using Real.continuous_exp.tendsto (0 : ℝ)
    exact hc.mono_left nhdsWithin_le_nhds
  -- `√t · R(t) → 0` (since `|R(t)| ≤ 19`).
  have hR0 : Tendsto (fun t : ℝ =>
      Real.sqrt t * ∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emF' t x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t => Real.sqrt t * 19)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
      exact mul_le_mul_of_nonneg_left (sphere3_R_bound ht') (Real.sqrt_nonneg t)
    · have hs : Tendsto (fun t : ℝ => Real.sqrt t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc := Real.continuous_sqrt.tendsto (0 : ℝ); rw [Real.sqrt_zero] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      simpa using hs.mul_const 19
  -- The pointwise algebraic decomposition on `t > 0`.
  have hcongr : (fun t : ℝ => (t ^ ((3 : ℝ) / 2) * sphere3HeatTrace t - Real.sqrt π / 4) / t)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun t => Real.sqrt π / 4 * ((Real.exp t - 1) / t)
        + Real.exp t * (Real.sqrt t * ∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emF' t x)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    have hne : t ≠ 0 := ht'.ne'
    rw [sphere3HeatTrace_eq ht', sphere3ShiftedSum_em1 ht']
    set R := ∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emF' t x with hRdef
    have key : t ^ ((3 : ℝ) / 2) * (Real.exp t * (Real.sqrt (π / t) / (4 * t) + R))
        = Real.exp t * (Real.sqrt π / 4) + Real.exp t * (t * Real.sqrt t * R) := by
      have hrw : t ^ ((3 : ℝ) / 2) * (Real.exp t * (Real.sqrt (π / t) / (4 * t) + R))
          = Real.exp t * (t ^ ((3 : ℝ) / 2) * (Real.sqrt (π / t) / (4 * t)))
            + Real.exp t * (t ^ ((3 : ℝ) / 2) * R) := by ring
      rw [hrw, A_scale ht', rpow32_eq ht']
    rw [key]
    field_simp
    ring
  rw [tendsto_congr' hcongr]
  have hlim := ((tendsto_const_nhds (x := Real.sqrt π / 4)).mul hE1).add (hexp1.mul hR0)
  simpa using hlim

/-- The `a₁`-coefficient tie: `a₁-coeff = a₀·(R/6)`, with `a₀ = √π/4` and `R/6 = 6/6 = 1` on the
unit `S³`. -/
theorem sphere3_a1_coeff_eq_a0_mul_R_div_six :
    (Real.sqrt π / 4) = (Real.sqrt π / 4) * (6 / 6) := by norm_num

end QIQTH.Sphere3HeatTrace
