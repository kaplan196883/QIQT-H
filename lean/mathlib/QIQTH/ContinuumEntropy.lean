/-
  CONTINUUM ENTROPY — the mode-density limit and the exact Bose integral: the first
  continuum rung of the record/gravity correspondence (duality campaign, brick D3a).

  The DY7 conjecture (`QIQTH.Conjectures.FlatSpaceRecordGravityCorrespondence`) equates the
  microscopic continuum record entropy with the one-loop continuum entropy (and both with
  `area/4G_ind`).  Its first two terms meet HERE at their simplest genuine contact point:
  the finite record-region entropy (DY5 `entropy_gibbs_region` — a finite sum of per-mode
  entropies whose `D → ∞` per-mode limit is the DS3 Planck form,
  `tendsto_thermalEntropy_planck`) converges, along refining mode families, to the EXACT
  continuum thermal entropy of the 1D massless boson:

      ∫₀^∞ s_∞(βω) dω = π²/(3β),      s_∞(x) = x/(eˣ−1) − log(1−e^{−x}),

  the standard `c = 1` free-boson thermal result.  (With the `Δω = π/L` mode spacing of a
  length-`L` region, the physical entropy density per unit length is
  `(1/π)·π²/(3β) = π/(3β)` — the DOS factor `1/π` is exactly the reciprocal mode spacing;
  see `entropy_density_form`.)  The Bose integral is derived from scratch: the geometric
  series `1/(eˣ−1) = Σ_{n≥1} e^{−nx}`, the logarithm series `−log(1−r) = Σ_{n≥1} rⁿ/n`,
  Tonelli (monotone-convergence interchange for the nonnegative terms), the elementary
  exponential moments `∫₀^∞ e^{−ax} = 1/a`, `∫₀^∞ x·e^{−ax} = 1/a²`, and BASEL
  (`hasSum_zeta_two`: `Σ 1/n² = π²/6`) — no dilogarithms anywhere.

  What is PROVED here (all axiom-free):
  • `sInf` — the Planck entropy kernel, tied to the held DS3 limit
    (`sInf_eq_planck_form`, `tendsto_thermalEntropy_sInf`);
  • `sInf_eq_tsum` — the two-series expansion of the kernel;
  • `integral_sInf` — ★ the exact Bose integral `∫₀^∞ s_∞ = π²/3` (with `integrable_sInf`),
    and its scaled form `∫₀^∞ s_∞(βω) dω = π²/(3β)`;
  • `entropyRiemannSum_tendsto` — the mode-density (Riemann-sum) limit: the scaled finite
    mode sums over a compact frequency window converge to the window integral;
  • `cutoff_integral_tendsto` — window exhaustion: the compact-window integrals converge
    to the exact value `π²/(3β)`;
  • `record_entropy_continuum_limit` — ★★ the capstone package (both limits, one theorem).

  ────────────────────────────────────────────────────────────────────────────────────────
  MANDATORY FIREWALL (honest scope).  This rung does NOT prove the DY7 conjecture:
  • no conical singularities and no heat-kernel area coefficients appear here;
  • no UV renormalization and no induced Newton constant — the `G_ind` leg is untouched;
  • no gauge, contact, or edge-mode subtleties;
  • the `β → 0` saturation regime is NOT addressed — the saturated `A/4G` statement lives
    in the finite-truncated model; this rung is the positive-temperature continuum limit;
  • the interchange of the truncation limit `D → ∞` with the mode-density limit is NOT
    addressed: the two limits are taken in the stated order (first `D → ∞` per mode — the
    held DS3 theorem — then the mode-density limit of the resulting Planck kernel);
  • 1D massless field only; the refining mode families are INPUTS (the uniform grids),
    not derived from a dynamical cutoff.
  This is NOT the strong holographic principle and NOT quantum gravity.
  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.Decoupling.EntropyRegimes

namespace QIQTH.ContinuumEntropy

open MeasureTheory Filter Set
open scoped Topology

/-! ### 1. The Planck entropy kernel -/

/-- **The Planck entropy kernel** `s_∞(x) = x/(eˣ−1) − log(1−e^{−x})` for `x > 0`
    (extended by `0` elsewhere): the `D → ∞` per-mode thermal entropy of the record code
    at `x = βω` (the held DS3 limit — see `tendsto_thermalEntropy_sInf`). -/
noncomputable def sInf (x : ℝ) : ℝ :=
  if 0 < x then x / (Real.exp x - 1) - Real.log (1 - Real.exp (-x)) else 0

theorem sInf_of_pos {x : ℝ} (hx : 0 < x) :
    sInf x = x / (Real.exp x - 1) - Real.log (1 - Real.exp (-x)) := if_pos hx

theorem sInf_of_nonpos {x : ℝ} (hx : ¬0 < x) : sInf x = 0 := if_neg hx

/-- The kernel is nonnegative: for `x > 0` both `x/(eˣ−1) > 0` and `−log(1−e^{−x}) > 0`. -/
theorem sInf_nonneg (x : ℝ) : 0 ≤ sInf x := by
  by_cases hx : 0 < x
  · rw [sInf_of_pos hx]
    have hex : (1 : ℝ) < Real.exp x := by rw [Real.one_lt_exp_iff]; exact hx
    have he : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
    have h1 : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    have hlog : Real.log (1 - Real.exp (-x)) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    have hdiv : 0 ≤ x / (Real.exp x - 1) := div_nonneg hx.le (by linarith)
    linarith
  · rw [sInf_of_nonpos hx]

/-- The kernel is continuous on `(0, ∞)`. -/
theorem sInf_continuousOn : ContinuousOn sInf (Set.Ioi (0 : ℝ)) := by
  have h : ContinuousOn
      (fun x : ℝ => x / (Real.exp x - 1) - Real.log (1 - Real.exp (-x))) (Set.Ioi 0) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.div continuous_id.continuousOn
        (Real.continuous_exp.sub continuous_const).continuousOn
      intro x hx
      have hex : (1 : ℝ) < Real.exp x := by rw [Real.one_lt_exp_iff]; exact hx
      exact ne_of_gt (by linarith)
    · apply ContinuousOn.log
      · exact continuousOn_const.sub (Real.continuous_exp.comp continuous_neg).continuousOn
      · intro x hx
        have h1 : Real.exp (-x) < 1 := by
          rw [Real.exp_lt_one_iff]
          have : (0 : ℝ) < x := hx
          linarith
        exact ne_of_gt (by linarith)
  exact h.congr fun x hx => sInf_of_pos hx

/-! ### The DS3 bridge — `sInf` IS the held Planck-form limit -/

/-- **The DS3 bridge**: `sInf` agrees (for `x > 0`) with the held DS3 Planck expression
    `−log(1−e^{−x}) + x·e^{−x}/(1−e^{−x})` — the limit value of
    `QIQTH.Decoupling.tendsto_thermalEntropy_planck`. -/
theorem sInf_eq_planck_form {x : ℝ} (hx : 0 < x) :
    sInf x = -Real.log (1 - Real.exp (-x))
      + x * (Real.exp (-x) / (1 - Real.exp (-x))) := by
  rw [sInf_of_pos hx, QIQTH.Decoupling.planck_form hx]
  ring

/-- **The genuine DS3 connection**: the truncated record-code thermal entropy `S_D(x)`
    converges to `sInf x` as `D → ∞`, at every fixed `x = βω > 0`.  This is the held DS3
    theorem restated with THIS file's kernel as the limit. -/
theorem tendsto_thermalEntropy_sInf {x : ℝ} (hx : 0 < x) :
    Tendsto (fun D : ℕ => QIQTH.Decoupling.thermalEntropy D x) atTop (𝓝 (sInf x)) := by
  rw [sInf_eq_planck_form hx]
  exact QIQTH.Decoupling.tendsto_thermalEntropy_planck hx

/-! ### 2. The series expansion of the kernel -/

/-- The `n`-th Boltzmann term of the kernel's expansion:
    `x·e^{−(n+1)x} + e^{−(n+1)x}/(n+1)`. -/
noncomputable def boseTerm (n : ℕ) (x : ℝ) : ℝ :=
  x * Real.exp (-(((n : ℝ) + 1) * x)) + Real.exp (-(((n : ℝ) + 1) * x)) / ((n : ℝ) + 1)

theorem boseTerm_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ boseTerm n x := by
  apply add_nonneg
  · exact mul_nonneg hx (Real.exp_pos _).le
  · exact div_nonneg (Real.exp_pos _).le (by positivity)

/-- **The series expansion holds**: for `x > 0`, the Boltzmann terms sum to `sInf x`.
    Geometric series for `x/(eˣ−1)`, logarithm series for `−log(1−e^{−x})`. -/
theorem hasSum_boseTerm {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => boseTerm n x) (sInf x) := by
  have he : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have h1 : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  -- the shifted geometric series: Σ_{n≥0} r^{n+1} = r·(1−r)⁻¹
  have hgeo : HasSum (fun n : ℕ => Real.exp (-x) ^ (n + 1))
      (Real.exp (-x) * (1 - Real.exp (-x))⁻¹) := by
    simpa [pow_succ'] using (hasSum_geometric_of_lt_one he.le h1).mul_left (Real.exp (-x))
  -- the logarithm series: Σ_{n≥0} r^{n+1}/(n+1) = −log(1−r)
  have hlog : HasSum (fun n : ℕ => Real.exp (-x) ^ (n + 1) / ((n : ℝ) + 1))
      (-Real.log (1 - Real.exp (-x))) :=
    Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg he.le])
  have hsum := (hgeo.mul_left x).add hlog
  have hfun : (fun n : ℕ =>
        x * Real.exp (-x) ^ (n + 1) + Real.exp (-x) ^ (n + 1) / ((n : ℝ) + 1))
      = fun n : ℕ => boseTerm n x := by
    funext n
    have hp : Real.exp (-x) ^ (n + 1) = Real.exp (-(((n : ℝ) + 1) * x)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [boseTerm, hp]
  rw [hfun] at hsum
  have hval : x * (Real.exp (-x) * (1 - Real.exp (-x))⁻¹) + -Real.log (1 - Real.exp (-x))
      = sInf x := by
    rw [sInf_of_pos hx, ← QIQTH.Decoupling.planck_form hx, div_eq_mul_inv]
    ring
  rwa [hval] at hsum

/-- **The series expansion** (tsum form): for `x > 0`,
    `sInf x = Σ_{n≥0} (x·e^{−(n+1)x} + e^{−(n+1)x}/(n+1))`. -/
theorem sInf_eq_tsum {x : ℝ} (hx : 0 < x) :
    sInf x = ∑' n : ℕ,
      (x * Real.exp (-(((n : ℝ) + 1) * x)) + Real.exp (-(((n : ℝ) + 1) * x)) / ((n : ℝ) + 1)) :=
  (hasSum_boseTerm hx).tsum_eq.symm

/-! ### 3. The elementary exponential integrals on `(0, ∞)` -/

/-- `∫₀^∞ e^{−ax} dx = 1/a` for `a > 0`. -/
theorem integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(a * x)) = a⁻¹ := by
  have h : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(a * x)))
      = a⁻¹ • ∫ y in Set.Ioi (0 : ℝ), Real.exp (-y) := by
    simpa using MeasureTheory.integral_comp_mul_left_Ioi (fun y => Real.exp (-y)) 0 ha
  rw [h, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]

/-- `∫₀^∞ x·e^{−ax} dx = 1/a²` for `a > 0` — the `Γ(2)` moment. -/
theorem integral_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-(a * x)) = (a ^ 2)⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a) two_pos ha
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at h
  simp only [Real.rpow_one] at h
  rw [h, Real.Gamma_two, mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, one_div, inv_pow]

theorem integrableOn_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun x => Real.exp (-(a * x))) (Set.Ioi (0 : ℝ)) := by
  simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0

theorem integrableOn_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun x => x * Real.exp (-(a * x))) (Set.Ioi (0 : ℝ)) := by
  -- the Γ(2) integrand is integrable …
  have h2 : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x) * x) (Set.Ioi 0) := by
    have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
    rw [show (2 : ℝ) - 1 = 1 by norm_num] at h
    simpa [Real.rpow_one] using h
  -- … hence so is its rescaling …
  have h3 : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.exp (-(a * x)) * (a * x)) (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => Real.exp (-y) * y) 0 ha).mpr
      (by rw [mul_zero]; exact h2)
  -- … and our integrand is `a⁻¹` times it
  have heq : (fun x : ℝ => x * Real.exp (-(a * x)))
      = fun x : ℝ => a⁻¹ * (Real.exp (-(a * x)) * (a * x)) := by
    funext x
    have hinv : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
    calc x * Real.exp (-(a * x)) = (a⁻¹ * a) * (x * Real.exp (-(a * x))) := by
          rw [hinv, one_mul]
      _ = a⁻¹ * (Real.exp (-(a * x)) * (a * x)) := by ring
  rw [heq]
  exact h3.const_mul _

/-! ### 4. ★ The Bose integral `∫₀^∞ s_∞ = π²/3` -/

theorem integrableOn_boseTerm (n : ℕ) :
    MeasureTheory.IntegrableOn (fun x => boseTerm n x) (Set.Ioi (0 : ℝ)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [boseTerm]
  exact (integrableOn_mul_exp_neg_mul_Ioi hn).add
    ((integrableOn_exp_neg_mul_Ioi hn).div_const _)

/-- The termwise integral: `∫₀^∞ boseTerm n = 1/(n+1)² + 1/(n+1)² = 2/(n+1)²`. -/
theorem integral_boseTerm (n : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), boseTerm n x = 2 / ((n : ℝ) + 1) ^ 2 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 := integrableOn_mul_exp_neg_mul_Ioi hn
  have h2 := (integrableOn_exp_neg_mul_Ioi hn).div_const ((n : ℝ) + 1)
  simp only [boseTerm]
  rw [MeasureTheory.integral_add h1 h2, MeasureTheory.integral_div,
    integral_mul_exp_neg_mul_Ioi hn, integral_exp_neg_mul_Ioi hn]
  field_simp
  ring

/-- BASEL, shifted to the `n ↦ n+1` indexing: `Σ_{n≥0} 1/(n+1)² = π²/6`. -/
theorem hasSum_basel_shifted :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2)
      (Real.pi ^ 2 / 6 + ∑ i ∈ Finset.range 1, (1 : ℝ) / ((i : ℝ)) ^ 2) := by
    simpa using hasSum_zeta_two
  have h1 := (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) 1).mpr h
  have heq : (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ)) : ℝ) ^ 2)
      = fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    funext n
    push_cast
    ring
  rwa [heq] at h1

/-- The termwise integrals sum to `π²/3`. -/
theorem hasSum_two_div_sq :
    HasSum (fun n : ℕ => 2 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 3) := by
  have h := hasSum_basel_shifted.mul_left 2
  have heq : (fun n : ℕ => 2 * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2))
      = fun n : ℕ => 2 / ((n : ℝ) + 1) ^ 2 := by
    funext n
    rw [mul_one_div]
  rw [heq] at h
  rwa [show 2 * (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 3 by ring] at h

/-- The Lebesgue (ENNReal) form of the Bose integral — Tonelli for the nonnegative
    Boltzmann terms, then BASEL. -/
theorem lintegral_ofReal_sInf :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (sInf x) = ENNReal.ofReal (Real.pi ^ 2 / 3) := by
  have hcont : ∀ n : ℕ, Continuous fun x : ℝ => boseTerm n x := by
    intro n
    have hc : Continuous fun x : ℝ => Real.exp (-(((n : ℝ) + 1) * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
    exact (continuous_id.mul hc).add (hc.div_const _)
  -- pointwise: ofReal (sInf x) = Σ ofReal (boseTerm n x) on (0,∞)
  have h1 : ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (sInf x)
      = ∫⁻ x in Set.Ioi (0 : ℝ), ∑' n : ℕ, ENNReal.ofReal (boseTerm n x) := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    show ENNReal.ofReal (sInf x) = ∑' n : ℕ, ENNReal.ofReal (boseTerm n x)
    rw [← (hasSum_boseTerm hx').tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => boseTerm_nonneg n hx'.le)
      (hasSum_boseTerm hx').summable
  -- Tonelli
  have h2 : ∫⁻ x in Set.Ioi (0 : ℝ), ∑' n : ℕ, ENNReal.ofReal (boseTerm n x)
      = ∑' n : ℕ, ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (boseTerm n x) :=
    MeasureTheory.lintegral_tsum fun n => ((hcont n).measurable.ennreal_ofReal).aemeasurable
  -- termwise value
  have h3 : ∀ n : ℕ, ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (boseTerm n x)
      = ENNReal.ofReal (2 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have hnn : (0 : ℝ → ℝ)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] fun x => boseTerm n x := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      exact boseTerm_nonneg n (le_of_lt hx)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_boseTerm n) hnn,
      integral_boseTerm n]
  rw [h1, h2, tsum_congr h3,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hasSum_two_div_sq.summable,
    hasSum_two_div_sq.tsum_eq]

/-- **The kernel is integrable on `(0, ∞)`.** -/
theorem integrable_sInf : MeasureTheory.IntegrableOn sInf (Set.Ioi (0 : ℝ)) := by
  refine ⟨sInf_continuousOn.aestronglyMeasurable measurableSet_Ioi, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => sInf_nonneg x)]
  rw [lintegral_ofReal_sInf]
  exact ENNReal.ofReal_lt_top

/-- **★ THE BOSE INTEGRAL**: `∫₀^∞ s_∞(x) dx = π²/3`, from scratch (geometric + log
    series, Tonelli, Basel — no dilogarithms). -/
theorem integral_sInf : ∫ x in Set.Ioi (0 : ℝ), sInf x = Real.pi ^ 2 / 3 := by
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sInf_nonneg x)
      (sInf_continuousOn.aestronglyMeasurable measurableSet_Ioi),
    lintegral_ofReal_sInf, ENNReal.toReal_ofReal (by positivity)]

theorem integrableOn_sInf_scaled {β : ℝ} (hβ : 0 < β) :
    MeasureTheory.IntegrableOn (fun ω => sInf (β * ω)) (Set.Ioi (0 : ℝ)) :=
  (integrableOn_Ioi_comp_mul_left_iff sInf 0 hβ).mpr (by rw [mul_zero]; exact integrable_sInf)

/-- **The scaled Bose integral**: `∫₀^∞ s_∞(βω) dω = π²/(3β)` — the exact continuum thermal
    entropy of the 1D massless boson at inverse temperature `β` (per `π/L` mode spacing). -/
theorem integral_sInf_scaled {β : ℝ} (hβ : 0 < β) :
    ∫ ω in Set.Ioi (0 : ℝ), sInf (β * ω) = Real.pi ^ 2 / (3 * β) := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi sInf 0 hβ
  rw [mul_zero] at h
  rw [h, integral_sInf, smul_eq_mul]
  field_simp

/-! ### 5. The mode-density / Riemann-sum limit -/

/-- The uniform grid point `a + k·(b−a)/(N+1)` of the `(N+1)`-point refinement of `[a,b]` —
    the `k`-th mode frequency of the refining mode family. -/
noncomputable def gridPt (a b : ℝ) (N k : ℕ) : ℝ := a + k * ((b - a) / (N + 1))

theorem gridPt_zero (a b : ℝ) (N : ℕ) : gridPt a b N 0 = a := by
  simp [gridPt]

theorem gridPt_succ_sub (a b : ℝ) (N k : ℕ) :
    gridPt a b N (k + 1) - gridPt a b N k = (b - a) / (N + 1) := by
  simp only [gridPt]
  push_cast
  ring

theorem gridPt_last (a b : ℝ) (N : ℕ) : gridPt a b N (N + 1) = b := by
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  simp only [gridPt]
  push_cast
  field_simp
  ring

theorem gridPt_le_succ {a b : ℝ} (hab : a ≤ b) (N k : ℕ) :
    gridPt a b N k ≤ gridPt a b N (k + 1) := by
  have hs := gridPt_succ_sub a b N k
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hh0 : (0 : ℝ) ≤ (b - a) / ((N : ℝ) + 1) := div_nonneg (by linarith) hN.le
  linarith

theorem gridPt_mem_Icc {a b : ℝ} (hab : a ≤ b) (N k : ℕ) (hk : k ≤ N + 1) :
    gridPt a b N k ∈ Set.Icc a b := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hh0 : (0 : ℝ) ≤ (b - a) / ((N : ℝ) + 1) := div_nonneg (by linarith) hN.le
  constructor
  · have h0 : (0 : ℝ) ≤ (k : ℝ) * ((b - a) / ((N : ℝ) + 1)) :=
      mul_nonneg (Nat.cast_nonneg k) hh0
    simp only [gridPt]
    linarith
  · have hkr : (k : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hk
    have h1 : (k : ℝ) * ((b - a) / ((N : ℝ) + 1))
        ≤ ((N : ℝ) + 1) * ((b - a) / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hkr hh0
    have h2 : ((N : ℝ) + 1) * ((b - a) / ((N : ℝ) + 1)) = b - a := by
      field_simp
    simp only [gridPt]
    linarith

/-- **The Riemann-sum limit for a continuous function**: the uniform left-endpoint Riemann
    sums of `f` over `[a,b]` converge to `∫_a^b f`.  Direct proof: compact ⟹ uniformly
    continuous ⟹ the standard `ε`-estimate between the sum and the integral. -/
theorem riemann_sum_tendsto_integral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    Tendsto (fun N : ℕ => ((b - a) / (N + 1)) *
        ∑ k ∈ Finset.range (N + 1), f (gridPt a b N k)) atTop
      (𝓝 (∫ ω in a..b, f ω)) := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hunif : UniformContinuousOn f (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hb1 : (0 : ℝ) < b - a + 1 := by linarith
  have hε' : 0 < ε / (b - a + 1) := div_pos hε hb1
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp hunif (ε / (b - a + 1)) hε'
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N₀, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hNne : ((N : ℝ) + 1) ≠ 0 := hNpos.ne'
  have hh0 : (0 : ℝ) ≤ (b - a) / ((N : ℝ) + 1) := div_nonneg hba hNpos.le
  -- the mesh is below δ
  have hmesh : (b - a) / ((N : ℝ) + 1) < δ := by
    have hN' : ((N₀ : ℝ)) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN₀
    nlinarith [mul_le_mul_of_nonneg_left hN' hδ.le]
  -- interval integrability on each subinterval
  have hgint : ∀ k < N + 1,
      IntervalIntegrable f MeasureTheory.volume (gridPt a b N k) (gridPt a b N (k + 1)) := by
    intro k hk
    apply (hf.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le (gridPt_le_succ hab N k)]
    exact Set.Icc_subset_Icc (gridPt_mem_Icc hab N k (by omega)).1
      (gridPt_mem_Icc hab N (k + 1) (by omega)).2
  -- the integral splits over the grid
  have hdecomp : (∑ k ∈ Finset.range (N + 1),
        ∫ ω in gridPt a b N k..gridPt a b N (k + 1), f ω)
      = ∫ ω in a..b, f ω := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (μ := MeasureTheory.volume) (f := f) (a := gridPt a b N) (n := N + 1) hgint
    rwa [gridPt_zero, gridPt_last] at h
  -- the per-cell estimate
  have hterm : ∀ k ∈ Finset.range (N + 1),
      |((b - a) / ((N : ℝ) + 1)) * f (gridPt a b N k)
          - ∫ ω in gridPt a b N k..gridPt a b N (k + 1), f ω|
        ≤ (ε / (b - a + 1)) * ((b - a) / ((N : ℝ) + 1)) := by
    intro k hk
    have hkN : k < N + 1 := Finset.mem_range.mp hk
    have hmem : gridPt a b N k ∈ Set.Icc a b := gridPt_mem_Icc hab N k (by omega)
    have hmem1 : gridPt a b N (k + 1) ∈ Set.Icc a b := gridPt_mem_Icc hab N (k + 1) (by omega)
    have hle : gridPt a b N k ≤ gridPt a b N (k + 1) := gridPt_le_succ hab N k
    have hconst : ((b - a) / ((N : ℝ) + 1)) * f (gridPt a b N k)
        = ∫ _ω in gridPt a b N k..gridPt a b N (k + 1), f (gridPt a b N k) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, gridPt_succ_sub]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hgint k hkN)]
    have hbd : ∀ ω ∈ Set.uIoc (gridPt a b N k) (gridPt a b N (k + 1)),
        ‖f (gridPt a b N k) - f ω‖ ≤ ε / (b - a + 1) := by
      intro ω hω
      rw [Set.uIoc_of_le hle] at hω
      have hωI : ω ∈ Set.Icc a b := ⟨le_trans hmem.1 hω.1.le, le_trans hω.2 hmem1.2⟩
      have hdist : dist (gridPt a b N k) ω < δ := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith [hω.1] : gridPt a b N k - ω ≤ 0)]
        have hs := gridPt_succ_sub a b N k
        have h2 := hω.2
        linarith [hmesh]
      have h := hδ' (gridPt a b N k) hmem ω hωI hdist
      rw [Real.dist_eq] at h
      rw [Real.norm_eq_abs]
      exact h.le
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs, gridPt_succ_sub, abs_of_nonneg hh0] at hb
    exact hb
  -- assemble
  rw [Real.dist_eq, ← hdecomp, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range (N + 1), (((b - a) / ((N : ℝ) + 1)) * f (gridPt a b N k)
          - ∫ ω in gridPt a b N k..gridPt a b N (k + 1), f ω)|
      ≤ ∑ k ∈ Finset.range (N + 1), |((b - a) / ((N : ℝ) + 1)) * f (gridPt a b N k)
          - ∫ ω in gridPt a b N k..gridPt a b N (k + 1), f ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (N + 1), (ε / (b - a + 1)) * ((b - a) / ((N : ℝ) + 1)) :=
        Finset.sum_le_sum hterm
    _ = ((N : ℝ) + 1) * ((ε / (b - a + 1)) * ((b - a) / ((N : ℝ) + 1))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = (ε / (b - a + 1)) * ((b - a) / ((N : ℝ) + 1) * ((N : ℝ) + 1)) := by ring
    _ = (ε / (b - a + 1)) * (b - a) := by rw [div_mul_cancel₀ _ hNne]
    _ = ε * ((b - a) / (b - a + 1)) := by ring
    _ < ε * 1 := by
        refine mul_lt_mul_of_pos_left ?_ hε
        rw [div_lt_one hb1]
        linarith
    _ = ε := mul_one ε

/-- **The refining mode-family entropy sum**: mesh `(b−a)/(N+1)` times the Planck-kernel
    values at the `N+1` uniform mode frequencies of the window `[a,b]`, at inverse
    temperature `β` — the (scaled) finite record-region entropy of the mode family. -/
noncomputable def entropyRiemannSum (β a b : ℝ) (N : ℕ) : ℝ :=
  ((b - a) / (N + 1)) * ∑ k ∈ Finset.range (N + 1),
    sInf (β * (a + k * ((b - a) / (N + 1))))

/-- **The mode-density limit**: the scaled finite entropy sums over the compact frequency
    window `[a,b] ⊂ (0,∞)` converge, as the mode family refines, to the window integral of
    the continuum entropy density. -/
theorem entropyRiemannSum_tendsto {β a b : ℝ} (hβ : 0 < β) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (entropyRiemannSum β a b) atTop (𝓝 (∫ ω in a..b, sInf (β * ω))) := by
  have hf : ContinuousOn (fun ω => sInf (β * ω)) (Set.Icc a b) := by
    apply sInf_continuousOn.comp (continuous_const.mul continuous_id).continuousOn
    intro ω hω
    exact Set.mem_Ioi.mpr (mul_pos hβ (lt_of_lt_of_le ha hω.1))
  exact riemann_sum_tendsto_integral hab hf

/-- **Window exhaustion**: the compact-window integrals `∫₀^R s_∞(βω) dω` converge, as
    `R → ∞`, to the exact continuum value `π²/(3β)`. -/
theorem cutoff_integral_tendsto {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun R : ℝ => ∫ ω in (0 : ℝ)..R, sInf (β * ω)) atTop
      (𝓝 (Real.pi ^ 2 / (3 * β))) := by
  have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_sInf_scaled hβ) tendsto_id
  rwa [integral_sInf_scaled hβ] at h

/-! ### 6. ★★ The capstone package -/

/-- **★★ THE FIRST CONTINUUM RUNG of `FlatSpaceRecordGravityCorrespondence`** (the DY7
    conjecture, `QIQTH.Conjectures`): the finite record code's thermal entropy has a genuine
    continuum limit, equal to the standard `c = 1` massless-boson thermal entropy.

    The composed statement, for every inverse temperature `β > 0`:
    1. **compact-window convergence** — for every window `[a,b] ⊂ (0,∞)`, the scaled finite
       record-region entropy sums of the refining mode families converge to the window
       integral `∫_a^b s_∞(βω) dω` (the per-mode `D → ∞` Planck kernel `s_∞` being the held
       DS3 limit, `tendsto_thermalEntropy_sInf`);
    2. **window exhaustion** — those window integrals converge to the EXACT value
       `π²/(3β)` as the window exhausts `(0,∞)`.

    Physical (density) reading: a region of length `L` has mode spacing `Δω = π/L`, so its
    entropy is `(L/π)·∫₀^∞ s_∞(βω) dω = L·π/(3β)` — density `π/(3β)` per unit length, the
    standard 1D massless-boson (c = 1) thermal entropy density; the DOS factor `1/π` is the
    reciprocal mode spacing (see `entropy_density_form`).

    FIREWALL: this is the positive-temperature continuum limit ONLY — see the header;
    it does not prove the conjecture (no conical/heat-kernel/area leg, no induced `G`,
    no `β → 0` saturation, no interchange of the `D → ∞` and mode-density limits). -/
theorem record_entropy_continuum_limit {β : ℝ} (hβ : 0 < β) :
    (∀ a b : ℝ, 0 < a → a ≤ b →
      Tendsto (entropyRiemannSum β a b) atTop (𝓝 (∫ ω in a..b, sInf (β * ω))))
    ∧ Tendsto (fun R : ℝ => ∫ ω in (0 : ℝ)..R, sInf (β * ω)) atTop
        (𝓝 (Real.pi ^ 2 / (3 * β))) :=
  ⟨fun _a _b ha hab => entropyRiemannSum_tendsto hβ ha hab, cutoff_integral_tendsto hβ⟩

/-- The density reading of the capstone value: with the `Δω = π/L` mode spacing, the
    per-unit-length DOS factor is `1/π`, and `(1/π)·π²/(3β) = π/(3β)` — the standard
    `c = 1` thermal entropy density. -/
theorem entropy_density_form {β : ℝ} (hβ : 0 < β) :
    (1 / Real.pi) * (Real.pi ^ 2 / (3 * β)) = Real.pi / (3 * β) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp

end QIQTH.ContinuumEntropy
