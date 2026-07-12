/-
  HEAT-KERNEL THERMAL — the winding heat-kernel representation of the 1D thermal boson:
  the conjecture's one-loop leg acquires its proper-time form (duality campaign, brick D3b).

  Brick D3a (`QIQTH.ContinuumEntropy`) proved that the microscopic record entropy equals the
  EXACT continuum thermal entropy of the 1D massless boson: `∫₀^∞ s_∞(βω) dω = π²/(3β)`,
  i.e. entropy density `S/L = (1/π)·π²/(3β) = π/(3β)`.  THIS brick proves that the SAME
  thermodynamics has a one-loop HEAT-KERNEL representation: the winding-subtracted
  proper-time integral on the thermal cylinder `S¹_β × ℝ` evaluates EXACTLY to the canonical
  Bose free energy.

  The heat-kernel side.  The per-unit-length heat trace on the cylinder `S¹_β × ℝ` is, by
  images, `(β/√(4πt))·(4πt)^{-1/2}·Σ_{m∈ℤ} e^{−m²β²/4t}` — the flat 1D prefactor
  `(4πt)^{-1/2}` being the DERIVED coefficient of `QIQTH.HeatKernelOneD.heatDensity_oneD`
  (`(1/2π)∫e^{−tk²}dk = (4πt)^{-1/2}`), and the Euclidean-time factor `β/√(4πt)` carrying
  the same derived kernel around the thermal circle.  NORMALIZATION, stated honestly: the
  one-loop `log Z` carries `½∫₀^∞ (dt/t)(…)`; the two prefactors multiply to `β/(4πt)`, the
  `±m` windings are folded into twice the positive sum, and the factor `2` cancels the loop
  `½`, so the nonzero-winding thermal piece is EXACTLY

      log Z_th / L  =  (β/4π) · Σ_{n≥0} ∫₀^∞ t^{−2} e^{−((n+1)β)²/4t} dt,

  which is the expression formalized in `heat_logZ_density` and proved `= π/(6β)`.  The
  `m = 0` winding (the vacuum/UV piece, divergent as `t → 0`) is removed BY CONSTRUCTION:
  the thermal part is DEFINED as the nonzero-winding sum — an honest definition, not a
  derived renormalization.

  What is PROVED here (all axiom-free):
  • `proper_time_integral` — the elementary proper-time integral
    `∫₀^∞ t^{−2} e^{−a²/4t} dt = 4/a²` (explicit antiderivative + FTC on `(0,∞)`);
  • `heat_logZ_density` — ★ the winding heat-kernel identity: the winding-subtracted
    one-loop sum equals `π/(6β)` exactly (termwise proper-time integral + BASEL);
  • `canonical_logZ_density` — the canonical bridge: the Bose free-energy integral
    `−(1/π)∫₀^∞ log(1−e^{−βω}) dω = π/(6β)` (log series + Tonelli, the D3a idioms);
  • `windings_eq_canonical` — the two representations agree: ONE object, TWO descriptions;
  • `hasDerivAt_logZ_density`, `entropy_density_relation` — the thermodynamic relations
    `E/L = −∂_β log Z/L = π/(6β²)` and `S/L = log Z/L + β·E/L = π/(3β)`;
  • `heat_kernel_entropy_eq_record_entropy` — the D3a JOIN: `π/(3β)` IS the DOS-weighted
    record-code continuum entropy `(1/π)·∫₀^∞ s_∞(βω) dω`;
  • `record_entropy_has_heat_kernel_form` — ★★ the capstone package: winding identity +
    canonical equality + entropy relation + D3a identification, in one conjunction.
    THE CONJECTURE'S FIRST TWO TERMS NOW BOTH POSSESS THE SAME HEAT-KERNEL FORM — the
    "one-loop continuum entropy" leg is no longer prose;
  • `naive_winding_diverges` — the guard: dropping the Euclidean-time trace factor
    `β/√(4πt)` (keeping only the spatial `t^{−3/2}`-type kernel) gives termwise `1/((n+1)β)`,
    whose sum is HARMONIC and machine-checked to diverge — the correct cylinder trace
    REQUIRES the Euclidean factor.

  ────────────────────────────────────────────────────────────────────────────────────────
  MANDATORY FIREWALL (honest scope).  The SMOOTH thermal cylinder ONLY — NOT the cone:
  conical entropy needs the heat kernel on `C_α` (Sommerfeld formulas, cone coefficients,
  `t → 0` UV control, renormalization of `G`) — CITED as the next rung, not built here.
  The `m = 0` (vacuum/UV) winding term is removed BY CONSTRUCTION (the thermal piece is
  defined as the nonzero-winding sum).  No induced-`G` leg, no `β → 0` saturation, no
  interchange of limits beyond what is proved.  1D massless field only.  This is NOT the
  DY7 conjecture (it is its second rung), NOT the strong holographic principle, and NOT
  quantum gravity.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.ContinuumEntropy

namespace QIQTH.HeatKernelThermal

open MeasureTheory Filter Set
open scoped Topology

/-! ### 1. The proper-time integral `∫₀^∞ t⁻² e^{−a²/4t} dt = 4/a²`

The key elementary lemma: the explicit antiderivative `t ↦ (4/a²)·e^{−a²/4t}` has
derivative `t⁻²·e^{−a²/4t}`, vanishes as `t → 0⁺`, and tends to `4/a²` as `t → ∞`;
FTC on `(0,∞)` (`integral_Ioi_of_hasDerivAt_of_nonneg`) does the rest. -/

/-- The exponent normal form: `−a²/(4t) = (−a²/4)·t⁻¹` (an identity of real numbers,
    valid for all `t` including `0` by the junk-value conventions). -/
theorem exponent_form (a s : ℝ) : -(a^2)/(4*s) = -(a^2)/4 * s⁻¹ := by
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- **The proper-time antiderivative** `t ↦ (4/a²)·e^{−a²/(4t)}` for `t > 0`
    (extended by `0` at `t ≤ 0`, its right limit). -/
noncomputable def properTimeAnti (a t : ℝ) : ℝ :=
  if 0 < t then 4/a^2 * Real.exp (-(a^2)/(4*t)) else 0

theorem properTimeAnti_of_pos {a t : ℝ} (ht : 0 < t) :
    properTimeAnti a t = 4/a^2 * Real.exp (-(a^2)/(4*t)) := if_pos ht

theorem properTimeAnti_zero (a : ℝ) : properTimeAnti a 0 = 0 := if_neg (lt_irrefl 0)

/-- The antiderivative property: `d/dt [(4/a²)·e^{−a²/(4t)}] = t⁻²·e^{−a²/(4t)}` on `(0,∞)`. -/
theorem hasDerivAt_properTimeAnti {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (properTimeAnti a) ((1/t^2) * Real.exp (-(a^2)/(4*t))) t := by
  -- chain rule on the explicit formula
  have h1 : HasDerivAt (fun s : ℝ => s⁻¹) (-(t^2)⁻¹) t := hasDerivAt_inv ht.ne'
  have h4 := ((h1.const_mul (-(a^2)/4)).exp).const_mul (4/a^2)
  -- transfer along the local equality with `properTimeAnti a`
  have heq : properTimeAnti a =ᶠ[𝓝 t] fun s => 4/a^2 * Real.exp (-(a^2)/4 * s⁻¹) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    rw [properTimeAnti_of_pos (Set.mem_Ioi.mp hs), exponent_form]
  have h5 := h4.congr_of_eventuallyEq heq
  -- identify the derivative value
  have hval : (1/t^2) * Real.exp (-(a^2)/(4*t))
      = 4/a^2 * (Real.exp (-(a^2)/4 * t⁻¹) * (-(a^2)/4 * -(t^2)⁻¹)) := by
    rw [exponent_form a t]
    field_simp
  rw [hval]
  exact h5

/-- The antiderivative vanishes as `t → 0⁺`: the exponent tends to `−∞`. -/
theorem tendsto_properTimeAnti_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (properTimeAnti a) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hpos : (0:ℝ) < a^2/4 := by positivity
  have h1 : Tendsto (fun s : ℝ => a^2/4 * s⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    Tendsto.const_mul_atTop hpos tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun s : ℝ => -(a^2)/4 * s⁻¹) (𝓝[>] (0:ℝ)) atBot := by
    have h := tendsto_neg_atTop_atBot.comp h1
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards with s
    simp only [Function.comp_apply]
    ring
  have hexp : Tendsto (fun s : ℝ => Real.exp (-(a^2)/4 * s⁻¹)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    Real.tendsto_exp_comp_nhds_zero.mpr h2
  have h4 := hexp.const_mul (4/a^2)
  rw [mul_zero] at h4
  refine Filter.Tendsto.congr' ?_ h4
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [properTimeAnti_of_pos (Set.mem_Ioi.mp hs), exponent_form]

/-- Right continuity of the antiderivative at `0` (the FTC boundary hypothesis). -/
theorem continuousWithinAt_properTimeAnti {a : ℝ} (ha : 0 < a) :
    ContinuousWithinAt (properTimeAnti a) (Set.Ici (0:ℝ)) 0 := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  unfold ContinuousWithinAt
  rw [properTimeAnti_zero]
  exact tendsto_properTimeAnti_zero ha

/-- The antiderivative tends to `4/a²` at `+∞`: the exponent tends to `0`. -/
theorem tendsto_properTimeAnti_atTop (a : ℝ) :
    Tendsto (properTimeAnti a) atTop (𝓝 (4/a^2)) := by
  have h0 : Tendsto (fun s : ℝ => -(a^2)/4 * s⁻¹) atTop (𝓝 0) := by
    have h2 := tendsto_inv_atTop_zero.const_mul (-(a^2)/4)
    simpa using h2
  have hexp : Tendsto (fun s : ℝ => Real.exp (-(a^2)/4 * s⁻¹)) atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp h0
    simpa [Function.comp] using h
  have h4 := hexp.const_mul (4/a^2)
  rw [mul_one] at h4
  refine Filter.Tendsto.congr' ?_ h4
  filter_upwards [Ioi_mem_atTop (0:ℝ)] with s hs
  rw [properTimeAnti_of_pos (Set.mem_Ioi.mp hs), exponent_form]

/-- The proper-time integrand is integrable on `(0,∞)` — automatic from nonnegativity of
    the derivative and existence of the limit (`integrableOn_Ioi_deriv_of_nonneg`). -/
theorem integrableOn_proper_time {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn
      (fun t => (1/t^2) * Real.exp (-(a^2)/(4*t))) (Set.Ioi (0:ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg (continuousWithinAt_properTimeAnti ha)
    (fun t ht => hasDerivAt_properTimeAnti ha (Set.mem_Ioi.mp ht))
    (fun t _ht => by positivity)
    (tendsto_properTimeAnti_atTop a)

/-- **THE PROPER-TIME INTEGRAL**: `∫₀^∞ t⁻² e^{−a²/(4t)} dt = 4/a²` for `a > 0` —
    the elementary evaluation behind every winding term of the cylinder heat trace. -/
theorem proper_time_integral (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Ioi (0:ℝ), (1/t^2) * Real.exp (-(a^2)/(4*t)) = 4/a^2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (continuousWithinAt_properTimeAnti ha)
    (fun t ht => hasDerivAt_properTimeAnti ha (Set.mem_Ioi.mp ht))
    (fun t _ht => by positivity)
    (tendsto_properTimeAnti_atTop a)
  rwa [properTimeAnti_zero, sub_zero] at h

/-! ### 2. ★ The winding heat-kernel identity -/

/-- **★ THE WINDING-SUBTRACTED ONE-LOOP HEAT-KERNEL REPRESENTATION** on the thermal
    cylinder `S¹_β × ℝ`: the per-unit-length trace is `(β/4πt)·Σ_{m≠0} e^{−m²β²/4t}` (the
    image sum over windings of the held flat 1D kernel `(4πt)^{−1/2}` of
    `QIQTH.HeatKernelOneD.heatDensity_oneD`, times the Euclidean-time factor `β·(4πt)^{−1/2}`;
    the `±m` windings are combined into `2×` the positive sum and the `2` folded into the
    one-loop `½`, so `log Z_th/L = ½∫(dt/t)·(β/4πt)·Σ_{m≠0}(…) = (β/4π)·Σ_{n≥0}∫t^{−2}(…)`
    exactly as formalized).  The `m = 0` term is the vacuum/UV piece, REMOVED BY
    CONSTRUCTION — the thermal part is DEFINED as the nonzero-winding sum.

    Termwise the proper-time integral gives `4/((n+1)β)²`, so the sum is
    `(β/4π)·(4/β²)·Σ 1/(n+1)² = (1/πβ)·π²/6 = π/(6β)` — BASEL closes it. -/
theorem heat_logZ_density {β : ℝ} (hβ : 0 < β) :
    (β/(4*Real.pi)) * (∑' n : ℕ, ∫ t in Set.Ioi (0:ℝ),
        (1/t^2) * Real.exp (-(((n+1:ℕ):ℝ)*β)^2/(4*t))) = Real.pi/(6*β) := by
  have hπ := Real.pi_pos
  -- termwise proper-time evaluation
  have hterm : ∀ n : ℕ, (∫ t in Set.Ioi (0:ℝ),
      (1/t^2) * Real.exp (-(((n+1:ℕ):ℝ)*β)^2/(4*t))) = 4/(((n+1:ℕ):ℝ)*β)^2 := by
    intro n
    have hn : (0:ℝ) < ((n+1:ℕ):ℝ)*β :=
      mul_pos (by exact_mod_cast Nat.succ_pos n) hβ
    exact proper_time_integral _ hn
  -- the summed value, from held BASEL
  have hb := QIQTH.ContinuumEntropy.hasSum_basel_shifted.mul_left (4/β^2)
  have heq2 : (fun n : ℕ => 4/β^2 * (1/((n:ℝ)+1)^2))
      = fun n : ℕ => 4/(((n+1:ℕ):ℝ)*β)^2 := by
    funext n
    have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
    push_cast
    rw [mul_pow]
    field_simp
  rw [heq2] at hb
  rw [tsum_congr hterm, hb.tsum_eq]
  field_simp

/-! ### 3. The canonical bridge — the Bose free energy, term by term -/

/-- The `n`-th term of the Bose logarithm series: `e^{−(n+1)x}/(n+1)`. -/
noncomputable def logSeriesTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(((n:ℝ)+1) * x)) / ((n:ℝ)+1)

theorem logSeriesTerm_nonneg (n : ℕ) (x : ℝ) : 0 ≤ logSeriesTerm n x := by
  have h := Real.exp_pos (-(((n:ℝ)+1) * x))
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  exact div_nonneg h.le hn.le

/-- The logarithm series: for `x > 0`, `Σ_{n≥0} e^{−(n+1)x}/(n+1) = −log(1−e^{−x})` —
    the held D3a series usage (`Real.hasSum_pow_div_log_of_abs_lt_one`). -/
theorem hasSum_logSeriesTerm {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => logSeriesTerm n x) (-Real.log (1 - Real.exp (-x))) := by
  have he : (0:ℝ) < Real.exp (-x) := Real.exp_pos _
  have hlog : HasSum (fun n : ℕ => Real.exp (-x) ^ (n+1) / ((n:ℝ)+1))
      (-Real.log (1 - Real.exp (-x))) :=
    Real.hasSum_pow_div_log_of_abs_lt_one
      (by rw [abs_of_nonneg he.le, Real.exp_lt_one_iff]; linarith)
  have hfun : (fun n : ℕ => Real.exp (-x) ^ (n+1) / ((n:ℝ)+1))
      = fun n : ℕ => logSeriesTerm n x := by
    funext n
    have hp : Real.exp (-x) ^ (n+1) = Real.exp (-(((n:ℝ)+1) * x)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [logSeriesTerm, hp]
  rwa [hfun] at hlog

theorem integrableOn_logSeriesTerm (n : ℕ) :
    MeasureTheory.IntegrableOn (fun x => logSeriesTerm n x) (Set.Ioi (0:ℝ)) := by
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  simp only [logSeriesTerm]
  exact (QIQTH.ContinuumEntropy.integrableOn_exp_neg_mul_Ioi hn).div_const _

/-- The termwise integral: `∫₀^∞ e^{−(n+1)x}/(n+1) dx = 1/(n+1)²` (held `∫e^{−ax}=1/a`). -/
theorem integral_logSeriesTerm (n : ℕ) :
    ∫ x in Set.Ioi (0:ℝ), logSeriesTerm n x = 1/((n:ℝ)+1)^2 := by
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  simp only [logSeriesTerm]
  rw [MeasureTheory.integral_div, QIQTH.ContinuumEntropy.integral_exp_neg_mul_Ioi hn,
    div_eq_mul_inv, one_div, pow_two, mul_inv]

/-- The integrand of the Bose free energy is nonnegative on `(0,∞)`. -/
theorem neg_log_one_sub_exp_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ -Real.log (1 - Real.exp (-x)) := by
  have he : (0:ℝ) < Real.exp (-x) := Real.exp_pos _
  have h1 : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h : Real.log (1 - Real.exp (-x)) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  linarith

theorem continuousOn_neg_log_one_sub_exp :
    ContinuousOn (fun x : ℝ => -Real.log (1 - Real.exp (-x))) (Set.Ioi (0:ℝ)) := by
  apply ContinuousOn.neg
  apply ContinuousOn.log
  · exact continuousOn_const.sub (Real.continuous_exp.comp continuous_neg).continuousOn
  · intro x hx
    have hx' : (0:ℝ) < x := hx
    have h1 : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    exact ne_of_gt (by linarith)

/-- The Lebesgue (ENNReal) form of the Bose free-energy integral — Tonelli for the
    nonnegative logarithm-series terms, then BASEL (the D3a `lintegral_tsum` idiom). -/
theorem lintegral_ofReal_neg_log :
    ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (-Real.log (1 - Real.exp (-x)))
      = ENNReal.ofReal (Real.pi^2/6) := by
  have hcont : ∀ n : ℕ, Continuous fun x : ℝ => logSeriesTerm n x := by
    intro n
    have hc : Continuous fun x : ℝ => Real.exp (-(((n:ℝ)+1) * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
    exact hc.div_const _
  -- pointwise series expansion on (0,∞)
  have h1 : ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (-Real.log (1 - Real.exp (-x)))
      = ∫⁻ x in Set.Ioi (0:ℝ), ∑' n : ℕ, ENNReal.ofReal (logSeriesTerm n x) := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : (0:ℝ) < x := hx
    show ENNReal.ofReal (-Real.log (1 - Real.exp (-x)))
      = ∑' n : ℕ, ENNReal.ofReal (logSeriesTerm n x)
    rw [← (hasSum_logSeriesTerm hx').tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => logSeriesTerm_nonneg n x)
      (hasSum_logSeriesTerm hx').summable
  -- Tonelli
  have h2 : ∫⁻ x in Set.Ioi (0:ℝ), ∑' n : ℕ, ENNReal.ofReal (logSeriesTerm n x)
      = ∑' n : ℕ, ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (logSeriesTerm n x) :=
    MeasureTheory.lintegral_tsum fun n => ((hcont n).measurable.ennreal_ofReal).aemeasurable
  -- termwise value
  have h3 : ∀ n : ℕ, ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (logSeriesTerm n x)
      = ENNReal.ofReal (1/((n:ℝ)+1)^2) := by
    intro n
    have hnn : (0 : ℝ → ℝ)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))] fun x => logSeriesTerm n x :=
      Filter.Eventually.of_forall fun x => logSeriesTerm_nonneg n x
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_logSeriesTerm n) hnn,
      integral_logSeriesTerm n]
  rw [h1, h2, tsum_congr h3,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      QIQTH.ContinuumEntropy.hasSum_basel_shifted.summable,
    QIQTH.ContinuumEntropy.hasSum_basel_shifted.tsum_eq]

/-- The Bose free-energy integrand is integrable on `(0,∞)` (unscaled form). -/
theorem integrableOn_neg_log_one_sub_exp_base :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => -Real.log (1 - Real.exp (-x))) (Set.Ioi (0:ℝ)) := by
  have hae : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))]
      fun x => -Real.log (1 - Real.exp (-x)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    exact neg_log_one_sub_exp_nonneg hx
  refine ⟨continuousOn_neg_log_one_sub_exp.aestronglyMeasurable measurableSet_Ioi, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hae, lintegral_ofReal_neg_log]
  exact ENNReal.ofReal_lt_top

/-- The unscaled Bose free-energy integral: `∫₀^∞ −log(1−e^{−x}) dx = π²/6`. -/
theorem integral_neg_log_one_sub_exp :
    ∫ x in Set.Ioi (0:ℝ), -Real.log (1 - Real.exp (-x)) = Real.pi^2/6 := by
  have hae : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))]
      fun x => -Real.log (1 - Real.exp (-x)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    exact neg_log_one_sub_exp_nonneg hx
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hae
      (continuousOn_neg_log_one_sub_exp.aestronglyMeasurable measurableSet_Ioi),
    lintegral_ofReal_neg_log, ENNReal.toReal_ofReal (by positivity)]

/-- Scaled integrability, as needed by the canonical bridge. -/
theorem integrableOn_neg_log_one_sub_exp {β : ℝ} (hβ : 0 < β) :
    MeasureTheory.IntegrableOn
      (fun ω => -Real.log (1 - Real.exp (-(β*ω)))) (Set.Ioi (0:ℝ)) :=
  (integrableOn_Ioi_comp_mul_left_iff
      (fun x => -Real.log (1 - Real.exp (-x))) 0 hβ).mpr
    (by rw [mul_zero]; exact integrableOn_neg_log_one_sub_exp_base)

/-- The scaled Bose free-energy integral: `∫₀^∞ −log(1−e^{−βω}) dω = π²/(6β)`. -/
theorem integral_neg_log_one_sub_exp_scaled {β : ℝ} (hβ : 0 < β) :
    ∫ ω in Set.Ioi (0:ℝ), -Real.log (1 - Real.exp (-(β*ω))) = Real.pi^2/(6*β) := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (fun x => -Real.log (1 - Real.exp (-x))) 0 hβ
  rw [mul_zero] at h
  rw [h, integral_neg_log_one_sub_exp, smul_eq_mul]
  field_simp

/-- **THE CANONICAL BRIDGE**: the canonical thermal free-energy density of the 1D massless
    boson, `log Z_th/L = −(1/π)∫₀^∞ log(1−e^{−βω}) dω`, equals `π/(6β)` — the SAME value
    as the winding heat-kernel sum.  (The `1/π` is the DOS factor: reciprocal `Δω = π/L`
    mode spacing, exactly as in D3a.) -/
theorem canonical_logZ_density {β : ℝ} (hβ : 0 < β) :
    -(1/Real.pi) * ∫ ω in Set.Ioi (0:ℝ), Real.log (1 - Real.exp (-(β*ω)))
      = Real.pi/(6*β) := by
  have h2 := integral_neg_log_one_sub_exp_scaled hβ
  rw [MeasureTheory.integral_neg] at h2
  have h3 : ∫ ω in Set.Ioi (0:ℝ), Real.log (1 - Real.exp (-(β*ω)))
      = -(Real.pi^2/(6*β)) := by linarith
  rw [h3]
  have hπ := Real.pi_pos
  field_simp

/-- **ONE OBJECT, TWO DESCRIPTIONS** (the named bridge): the winding-subtracted one-loop
    heat-kernel sum on the thermal cylinder EQUALS the canonical Bose free energy — the
    "thermal" and "one-loop" legs of the conjecture meet at the thermodynamic level. -/
theorem windings_eq_canonical {β : ℝ} (hβ : 0 < β) :
    (β/(4*Real.pi)) * (∑' n : ℕ, ∫ t in Set.Ioi (0:ℝ),
        (1/t^2) * Real.exp (-(((n+1:ℕ):ℝ)*β)^2/(4*t)))
      = -(1/Real.pi) * ∫ ω in Set.Ioi (0:ℝ), Real.log (1 - Real.exp (-(β*ω))) := by
  rw [heat_logZ_density hβ, canonical_logZ_density hβ]

/-! ### 4. The thermodynamic relations and the D3a join -/

/-- The closed-form free-energy density `log Z/L = π/(6β)`, the common value of the
    winding heat-kernel representation (`heat_logZ_density`) and the canonical Bose
    integral (`canonical_logZ_density`). -/
noncomputable def logZ_density (β : ℝ) : ℝ := Real.pi/(6*β)

theorem logZ_density_eq_windings {β : ℝ} (hβ : 0 < β) :
    logZ_density β = (β/(4*Real.pi)) * (∑' n : ℕ, ∫ t in Set.Ioi (0:ℝ),
      (1/t^2) * Real.exp (-(((n+1:ℕ):ℝ)*β)^2/(4*t))) := by
  simpa [logZ_density] using (heat_logZ_density hβ).symm

/-- The energy density is minus the `β`-derivative of the free-energy density:
    `−d/dβ [π/(6β)] = π/(6β²)`, i.e. `E/L = π/(6β²)` — the 1D Stefan–Boltzmann law. -/
theorem hasDerivAt_logZ_density {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun b : ℝ => Real.pi/(6*b)) (-(Real.pi/(6*β^2))) β := by
  have h1 := (hasDerivAt_inv hβ.ne').const_mul (Real.pi/6)
  have heq : (fun b : ℝ => Real.pi/(6*b)) = fun b : ℝ => Real.pi/6 * b⁻¹ := by
    funext b
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [heq]
  have hval : -(Real.pi/(6*β^2)) = Real.pi/6 * -(β^2)⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hval]
  exact h1

/-- ★ **The entropy relation** `S/L = log Z/L + β·E/L`: `π/(6β) + β·π/(6β²) = π/(3β)` —
    the thermodynamic entropy density of the heat-kernel/canonical free energy. -/
theorem entropy_density_relation {β : ℝ} (hβ : 0 < β) :
    Real.pi/(6*β) + β * (Real.pi/(6*β^2)) = Real.pi/(3*β) := by
  field_simp
  ring

/-- ★★ **THE D3a JOIN**: the entropy density `π/(3β)` extracted from the heat-kernel
    (winding) representation EQUALS the DOS-weighted record-code continuum entropy of
    D3a — `(1/π)·∫₀^∞ s_∞(βω) dω` with the HELD `integral_sInf_scaled = π²/(3β)`. -/
theorem heat_kernel_entropy_eq_record_entropy {β : ℝ} (hβ : 0 < β) :
    Real.pi/(3*β)
      = (1/Real.pi) * ∫ ω in Set.Ioi (0:ℝ), QIQTH.ContinuumEntropy.sInf (β*ω) := by
  rw [QIQTH.ContinuumEntropy.integral_sInf_scaled hβ]
  have hπ := Real.pi_pos
  field_simp

/-- **★★ THE CAPSTONE — the record entropy acquires its heat-kernel form** (brick D3b of
    the duality campaign, the second continuum rung of the DY7 conjecture
    `QIQTH.Conjectures.FlatSpaceRecordGravityCorrespondence`).

    The composed statement, for every inverse temperature `β > 0`:
    1. **the winding heat-kernel identity** — the winding-subtracted one-loop proper-time
       sum on the thermal cylinder `S¹_β × ℝ` equals `π/(6β)` (`heat_logZ_density`);
    2. **the canonical equality** — the canonical Bose free-energy density equals the same
       `π/(6β)` (`canonical_logZ_density`); hence the two representations agree
       (`windings_eq_canonical`): one object, two descriptions;
    3. **the entropy relation** — `S/L = log Z/L + β·E/L = π/(3β)`, with
       `E/L = −d/dβ log Z/L` the genuine derivative (`hasDerivAt_logZ_density`);
    4. **the D3a identification** — `π/(3β)` IS the DOS-weighted record-code continuum
       entropy `(1/π)·∫₀^∞ s_∞(βω) dω` of the held `integral_sInf_scaled`.

    So the DY7 conjecture's first two terms — microscopic record entropy and one-loop
    continuum entropy — now both possess the same machine-checked heat-kernel form.

    FIREWALL: smooth thermal cylinder only — no cone, no Sommerfeld/conical coefficients,
    no induced `G`, no `β → 0` saturation; the `m = 0` winding is removed by construction;
    see the header. -/
theorem record_entropy_has_heat_kernel_form {β : ℝ} (hβ : 0 < β) :
    ((β/(4*Real.pi)) * (∑' n : ℕ, ∫ t in Set.Ioi (0:ℝ),
        (1/t^2) * Real.exp (-(((n+1:ℕ):ℝ)*β)^2/(4*t))) = Real.pi/(6*β))
    ∧ (-(1/Real.pi) * ∫ ω in Set.Ioi (0:ℝ), Real.log (1 - Real.exp (-(β*ω)))
        = Real.pi/(6*β))
    ∧ (Real.pi/(6*β) + β * (Real.pi/(6*β^2)) = Real.pi/(3*β))
    ∧ (Real.pi/(3*β)
        = (1/Real.pi) * ∫ ω in Set.Ioi (0:ℝ), QIQTH.ContinuumEntropy.sInf (β*ω)) :=
  ⟨heat_logZ_density hβ, canonical_logZ_density hβ,
    entropy_density_relation hβ, heat_kernel_entropy_eq_record_entropy hβ⟩

/-! ### 5. The guard — the naive kernel without the Euclidean-time factor diverges -/

/-- **THE GUARD**: dropping the Euclidean-time trace factor `β·(4πt)^{−1/2}` from the
    cylinder trace (keeping only the spatial kernel) changes the termwise proper-time
    integral from `∝ 1/((n+1)β)²` to `∝ 1/((n+1)β)` — and the resulting winding sum is
    HARMONIC: it does not converge.  Machine-checked: the correct cylinder trace REQUIRES
    the `β/√(4πt)` Euclidean factor; the naive spatial-only kernel fails. -/
theorem naive_winding_diverges {β : ℝ} (hβ : 0 < β) :
    ¬ Summable (fun n : ℕ => 1/(((n+1:ℕ):ℝ)*β)) := by
  intro h
  have h2 := h.mul_right β
  have heq : (fun n : ℕ => 1/(((n+1:ℕ):ℝ)*β) * β) = fun n : ℕ => 1/((n+1:ℕ):ℝ) := by
    funext n
    have hn : (0:ℝ) < ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
    field_simp
  rw [heq] at h2
  exact (mt (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)) 1).mp
    Real.not_summable_one_div_natCast) h2

end QIQTH.HeatKernelThermal
