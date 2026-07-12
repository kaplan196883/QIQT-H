/-
  ONE-LOOP DETERMINANT — the finite Gaussian one-loop determinant via the subtracted
  proper-time (Frullani) representation (conjecture-input program, brick G1).

  The DY7 conjecture `QIQTH.Conjectures.FlatSpaceRecordGravityCorrespondence` cites, among
  its FIVE physical inputs, the one-loop determinant relation `log Z = ½∫₀^∞ (dt/t) Tr K`
  as an UNPROVED input.  THIS brick discharges it AT THE FINITE LEVEL, exactly:

    • the FRULLANI identity  `log λ = ∫₀^∞ (e^{−t} − e^{−λt})/t dt`  (Part A) — proved by the
      inner FTC representation `(e^{−bt} − e^{−at})/t = ∫_b^a e^{−st} ds` and a genuine
      Tonelli (Lebesgue) swap between the proper-time half-line `(0,∞)` and the interval
      `[b,a]`, closed by the elementary moment `∫₀^∞ e^{−st} dt = 1/s` and `∫_b^a 1/s = log(a/b)`;
    • the SUBTRACTED PROPER-TIME LOG-DETERMINANT (Part B):
        `log det A = ∫₀^∞ (N e^{−t} − Tr e^{−tA})/t dt`,
      a GENUINE convergent Lebesgue integral for a finite positive spectrum `{λ_k}` — the
      Frullani subtraction of `N e^{−t}` removes the `t → 0` UV divergence of the raw
      `∫ Tr K dt/t` (which does NOT converge);
    • the DIAGONAL GAUSSIAN (Part C):  `∫ e^{−½ Σ_k λ_k x_k²} = ∏_k √(2π/λ_k)` — the finite
      product Gaussian (Mathlib's `integral_gaussian` × Fubini `integral_fintype_prod`);
    • the ASSEMBLY (Part D):  `log Z = (N/2) log(2π) − ½ log det A`, in the proper-time form
        `log Z = (N/2) log(2π) − ½ ∫₀^∞ (N e^{−t} − Tr e^{−tA})/t dt`.

  What is PROVED here (all axiom-free):
  • `integral_frullani`, `integral_frullani_one` — the Frullani log-integrals (general `a,b>0`
    and the `b = 1` form), with `integrableOn_frullani(_one)`;
  • `log_specDet_eq_properTime` — ★★ the subtracted proper-time log-determinant identity;
  • `gaussianIntegral_diagonal` — ★ the finite diagonal Gaussian;
  • `gaussianLogZ_eq_log_integral`, `gaussianLogZ_eq_properTime` — ★★ the assembled one-loop
    `log Z` in proper-time form;
  • `finite_one_loop_determinant` — the capstone conjunction.

  ────────────────────────────────────────────────────────────────────────────────────────
  MANDATORY FIREWALL (honest scope, binding).  This discharges ONE of the DY7 conjecture's
  five cited inputs at the FINITE level, NOT the conjecture.
  • FINITE-DIMENSIONAL only: a finite positive spectrum `l : ι → ℝ`, `∀ k, 0 < l k` (the
    record code's finite mode content).  The CONTINUUM functional determinant,
    ζ-regularization, heat-kernel small-`t` asymptotics, and the removal of continuum
    divergences stay CITED.
  • The DIAGONAL Gaussian is used (the record spectrum is diagonal by construction).  The
    arbitrary `Matrix.PosDef` Gaussian — needing the spectral theorem + an orthogonal change
    of variables — is a SEPARATE cited brick.
  • The RAW `½∫₀^∞ (dt/t) Tr K` is NOT a convergent Lebesgue integral (stated honestly); only
    the Frullani-SUBTRACTED form `∫ (N e^{−t} − Tr e^{−tA})/t` is — that is the object proved.
  • This is NOT the strong holographic principle and NOT quantum gravity.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.ContinuumEntropy

namespace QIQTH.OneLoopDeterminant

open MeasureTheory Filter Set
open scoped Topology

/-! ### Part A — the Frullani / proper-time log integral -/

/-- The nonnegativity (for `b ≤ a`) of the Frullani integrand on `(0,∞)`. -/
theorem frullani_nonneg_ae {a b : ℝ} (hab : b ≤ a) :
    (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))]
      fun t => (Real.exp (-(b*t)) - Real.exp (-(a*t)))/t := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0:ℝ) < t := ht
  refine div_nonneg ?_ ht'.le
  have hbt : b*t ≤ a*t := mul_le_mul_of_nonneg_right hab ht'.le
  have hle : Real.exp (-(a*t)) ≤ Real.exp (-(b*t)) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Measurability (in fact continuity on `(0,∞)`) of the Frullani integrand. -/
theorem frullani_aesm (a b : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun t => (Real.exp (-(b*t)) - Real.exp (-(a*t)))/t)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  apply ContinuousOn.div
  · exact ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-(b*t)) - Real.exp (-(a*t)))).continuousOn
  · exact continuous_id.continuousOn
  · intro t ht; exact (ht : (0:ℝ) < t).ne'

/-- **The inner FTC representation**: for `t ≠ 0` and `b ≤ a`,
    `∫_{Ioc b a} e^{−st} ds = (e^{−bt} − e^{−at})/t`.  Antiderivative `s ↦ (−1/t) e^{−st}`. -/
theorem frullani_inner {a b : ℝ} (t : ℝ) (ht : t ≠ 0) (hab : b ≤ a) :
    ∫ s in Set.Ioc b a, Real.exp (-(s*t))
      = (Real.exp (-(b*t)) - Real.exp (-(a*t)))/t := by
  rw [← intervalIntegral.integral_of_le hab]
  have hderiv : ∀ s ∈ Set.uIcc b a,
      HasDerivAt (fun s : ℝ => (-1/t) * Real.exp (-(s*t))) (Real.exp (-(s*t))) s := by
    intro s _
    have h1 : HasDerivAt (fun x : ℝ => -(x*t)) (-(1*t)) s :=
      ((hasDerivAt_id s).mul_const t).neg
    have h2 := (h1.exp).const_mul (-1/t)
    have hval : (-1/t) * (Real.exp (-(s*t)) * -(1*t)) = Real.exp (-(s*t)) := by
      rw [show (-1/t) * (Real.exp (-(s*t)) * -(1*t)) = (t/t) * Real.exp (-(s*t)) from by ring,
        div_self ht, one_mul]
    rwa [hval] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(s*t))).intervalIntegrable b a)]
  ring

/-- **The Lebesgue value of the Frullani integral (for `b ≤ a`)**:
    `∫₀^∞ ofReal((e^{−bt} − e^{−at})/t) = ofReal(log(a/b))`.  Proved by the inner FTC
    representation, a Tonelli swap `(0,∞) × [b,a]`, and `∫₀^∞ e^{−st} dt = 1/s`,
    `∫_b^a 1/s = log(a/b)`. -/
theorem lintegral_ofReal_frullani_le {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((Real.exp (-(b*t)) - Real.exp (-(a*t)))/t)
      = ENNReal.ofReal (Real.log (a/b)) := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  -- Step 1: inner FTC representation, lifted to lintegrals
  have step1 : ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((Real.exp (-(b*t)) - Real.exp (-(a*t)))/t)
      = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ s in Set.Ioc b a,
          ENNReal.ofReal (Real.exp (-(s*t))) := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht' : t ≠ 0 := (ht : (0:ℝ) < t).ne'
    show ENNReal.ofReal ((Real.exp (-(b*t)) - Real.exp (-(a*t)))/t)
      = ∫⁻ s in Set.Ioc b a, ENNReal.ofReal (Real.exp (-(s*t)))
    rw [← frullani_inner t ht' hab]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(s*t))).integrableOn_Ioc)
      (Filter.Eventually.of_forall fun s => (Real.exp_pos _).le)
  -- Step 2: Tonelli swap
  have hmeas : Measurable
      (Function.uncurry fun t s : ℝ => ENNReal.ofReal (Real.exp (-(s*t)))) := by
    have h : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.2 * p.1)))) := by
      fun_prop
    exact h
  have step2 : ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ s in Set.Ioc b a,
          ENNReal.ofReal (Real.exp (-(s*t)))
      = ∫⁻ s in Set.Ioc b a, ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (Real.exp (-(s*t))) :=
    MeasureTheory.lintegral_lintegral_swap hmeas.aemeasurable
  -- Step 3: the inner proper-time integral `∫₀^∞ e^{−st} dt = 1/s`
  have step3 : ∫⁻ s in Set.Ioc b a, ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (Real.exp (-(s*t)))
      = ∫⁻ s in Set.Ioc b a, ENNReal.ofReal s⁻¹ := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hs0 : 0 < s := hb.trans hs.1
    show ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(s*t))) = ENNReal.ofReal s⁻¹
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (QIQTH.ContinuumEntropy.integrableOn_exp_neg_mul_Ioi hs0)
        (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le),
      QIQTH.ContinuumEntropy.integral_exp_neg_mul_Ioi hs0]
  -- assemble: `∫_b^a 1/s = log(a/b)`
  rw [step1, step2, step3]
  have hInt : MeasureTheory.IntegrableOn (fun s => s⁻¹) (Set.Ioc b a) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ continuous_id.continuousOn
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact (lt_of_lt_of_le hb hs.1).ne'
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc b a)]
      fun s => s⁻¹ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    exact le_of_lt (inv_pos.mpr (hb.trans hs.1))
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hab, integral_inv_of_pos hb ha]

/-- **The Frullani integrand is integrable on `(0,∞)`** (for `b ≤ a`). -/
theorem integrableOn_frullani_le {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    MeasureTheory.IntegrableOn
      (fun t => (Real.exp (-(b*t)) - Real.exp (-(a*t)))/t) (Set.Ioi (0:ℝ)) := by
  refine ⟨frullani_aesm a b, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (frullani_nonneg_ae hab),
    lintegral_ofReal_frullani_le hb hab]
  exact ENNReal.ofReal_lt_top

/-- The Frullani integral for `b ≤ a`. -/
theorem integral_frullani_le {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    ∫ t in Set.Ioi (0:ℝ), (Real.exp (-(b*t)) - Real.exp (-(a*t)))/t = Real.log (a/b) := by
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (frullani_nonneg_ae hab)
      (frullani_aesm a b),
    lintegral_ofReal_frullani_le hb hab,
    ENNReal.toReal_ofReal (Real.log_nonneg ((one_le_div hb).mpr hab))]

/-- **THE FRULLANI IDENTITY** (general `a, b > 0`):
    `∫₀^∞ (e^{−bt} − e^{−at})/t dt = log(a/b)`. -/
theorem integral_frullani {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Set.Ioi (0:ℝ), (Real.exp (-(b*t)) - Real.exp (-(a*t)))/t = Real.log (a/b) := by
  rcases le_total b a with hab | hab
  · exact integral_frullani_le hb hab
  · have heq : ∫ t in Set.Ioi (0:ℝ), (Real.exp (-(b*t)) - Real.exp (-(a*t)))/t
        = ∫ t in Set.Ioi (0:ℝ), -((Real.exp (-(a*t)) - Real.exp (-(b*t)))/t) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      ring
    rw [heq, MeasureTheory.integral_neg, integral_frullani_le ha hab, ← Real.log_inv, inv_div]

/-- Integrability of the Frullani integrand (general `a, b > 0`). -/
theorem integrableOn_frullani {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasureTheory.IntegrableOn
      (fun t => (Real.exp (-(b*t)) - Real.exp (-(a*t)))/t) (Set.Ioi (0:ℝ)) := by
  rcases le_total b a with hab | hab
  · exact integrableOn_frullani_le hb hab
  · apply (integrableOn_frullani_le ha hab).neg.congr
    filter_upwards with t
    show -((Real.exp (-(a*t)) - Real.exp (-(b*t)))/t)
      = (Real.exp (-(b*t)) - Real.exp (-(a*t)))/t
    ring

/-- **THE FRULLANI IDENTITY (the `b = 1` downstream form)**:
    `∫₀^∞ (e^{−t} − e^{−at})/t dt = log a`. -/
theorem integral_frullani_one {a : ℝ} (ha : 0 < a) :
    ∫ t in Set.Ioi (0:ℝ), (Real.exp (-t) - Real.exp (-(a*t)))/t = Real.log a := by
  have h := integral_frullani ha (by norm_num : (0:ℝ) < 1)
  rw [div_one] at h
  rw [← h]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [one_mul]

/-- Integrability of the `b = 1` Frullani integrand. -/
theorem integrableOn_frullani_one {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn
      (fun t => (Real.exp (-t) - Real.exp (-(a*t)))/t) (Set.Ioi (0:ℝ)) := by
  apply (integrableOn_frullani ha (by norm_num : (0:ℝ) < 1)).congr
  filter_upwards with t
  rw [one_mul]

/-! ### Part B — the subtracted proper-time log-determinant identity -/

/-- **The finite heat trace** `Θ(t) = Tr e^{−tA} = ∑_k e^{−λ_k t}`. -/
noncomputable def heatTrace {ι : Type*} [Fintype ι] (l : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ k, Real.exp (-(l k * t))

/-- **The spectral determinant** `det A = ∏_k λ_k`. -/
noncomputable def specDet {ι : Type*} [Fintype ι] (l : ι → ℝ) : ℝ := ∏ k, l k

/-- **The subtracted proper-time integrand** `(N e^{−t} − Θ(t))/t`. -/
noncomputable def logDetPTIntegrand {ι : Type*} [Fintype ι] (l : ι → ℝ) (t : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) * Real.exp (-t)) - heatTrace l t)/t

/-- **★★ THE SUBTRACTED PROPER-TIME LOG-DETERMINANT IDENTITY** (finite, exact):
    for a finite positive spectrum `l : ι → ℝ`, `∀ k, 0 < l k`,
      `log det A = ∫₀^∞ (N e^{−t} − Tr e^{−tA})/t dt`,
    a genuine convergent Lebesgue integral (the `N e^{−t}` subtraction removes the `t → 0`
    divergence of the raw `∫ Tr K dt/t`). -/
theorem log_specDet_eq_properTime {ι : Type*} [Fintype ι] (l : ι → ℝ) (hl : ∀ k, 0 < l k) :
    Real.log (specDet l) = ∫ t in Set.Ioi (0:ℝ), logDetPTIntegrand l t := by
  have hspec : Real.log (specDet l) = ∑ k, Real.log (l k) := by
    simp only [specDet]
    rw [Real.log_prod (fun k _ => (hl k).ne')]
  have hpt : ∀ k, Real.log (l k)
      = ∫ t in Set.Ioi (0:ℝ), (Real.exp (-t) - Real.exp (-(l k * t)))/t :=
    fun k => (integral_frullani_one (hl k)).symm
  rw [hspec]
  simp_rw [hpt]
  rw [← MeasureTheory.integral_finsetSum Finset.univ
      (fun k _ => integrableOn_frullani_one (hl k))]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [logDetPTIntegrand, heatTrace]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Part C — the diagonal Gaussian integral -/

/-- **★ THE FINITE DIAGONAL GAUSSIAN**:
    `∫_{ℝ^ι} e^{−½ Σ_k λ_k x_k²} = ∏_k √(2π/λ_k)`.  The integrand factorizes into a product
    of one-dimensional Gaussians; Fubini (`integral_fintype_prod`) and Mathlib's
    `integral_gaussian` (`∫ e^{−b x²} = √(π/b)`, with `b = λ_k/2`) close it. -/
theorem gaussianIntegral_diagonal {ι : Type*} [Fintype ι] (l : ι → ℝ) (hl : ∀ k, 0 < l k) :
    ∫ x : ι → ℝ, Real.exp (-((∑ k, l k * (x k)^2)/2))
      = ∏ k, Real.sqrt ((2*Real.pi)/(l k)) := by
  have hfac : ∀ x : ι → ℝ, Real.exp (-((∑ k, l k * (x k)^2)/2))
      = ∏ k, Real.exp (-(l k * (x k)^2)/2) := by
    intro x
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_div, Finset.sum_neg_distrib, neg_div]
  have hone : ∀ k, ∫ x : ℝ, Real.exp (-(l k * x^2)/2) = Real.sqrt ((2*Real.pi)/(l k)) := by
    intro k
    have hrw : (fun x : ℝ => Real.exp (-(l k * x^2)/2))
        = fun x => Real.exp (-(l k/2) * x^2) := by
      funext x; congr 1; ring
    rw [hrw, integral_gaussian (l k / 2)]
    congr 1
    rw [div_div_eq_mul_div]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfac),
    integral_fintype_prod_volume_eq_prod (fun (k : ι) (x : ℝ) => Real.exp (-(l k * x^2)/2))]
  exact Finset.prod_congr rfl (fun k _ => hone k)

/-! ### Part D — the assembly: the one-loop `log Z` -/

/-- **The Gaussian log-partition function** `log Z = ∑_k ½ log(2π/λ_k)` (the log of the
    diagonal Gaussian value). -/
noncomputable def gaussianLogZ {ι : Type*} [Fintype ι] (l : ι → ℝ) : ℝ :=
  ∑ k, (1/2) * Real.log ((2*Real.pi)/(l k))

/-- `gaussianLogZ l = log(∫ e^{−½ Σ λ x²})` — the tie to the Gaussian integral of Part C. -/
theorem gaussianLogZ_eq_log_integral {ι : Type*} [Fintype ι] (l : ι → ℝ) (hl : ∀ k, 0 < l k) :
    gaussianLogZ l = Real.log (∫ x : ι → ℝ, Real.exp (-((∑ k, l k * (x k)^2)/2))) := by
  rw [gaussianIntegral_diagonal l hl,
    Real.log_prod (fun k _ => ne_of_gt (Real.sqrt_pos.mpr (div_pos (by positivity) (hl k))))]
  simp only [gaussianLogZ]
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.log_sqrt (div_nonneg (by positivity) (hl k).le)]
  ring

/-- **★★ THE FINITE GAUSSIAN ONE-LOOP DETERMINANT IDENTITY**:
    `log Z = (N/2) log(2π) − ½ ∫₀^∞ (N e^{−t} − Tr e^{−tA})/t dt`, the proper-time form of
    `log Z = (N/2) log(2π) − ½ log det A`. -/
theorem gaussianLogZ_eq_properTime {ι : Type*} [Fintype ι] (l : ι → ℝ) (hl : ∀ k, 0 < l k) :
    gaussianLogZ l = ((Fintype.card ι : ℝ)/2) * Real.log (2*Real.pi)
      - (1/2) * ∫ t in Set.Ioi (0:ℝ), logDetPTIntegrand l t := by
  have hspec : Real.log (specDet l) = ∑ k, Real.log (l k) := by
    simp only [specDet]
    rw [Real.log_prod (fun k _ => (hl k).ne')]
  have hterm : ∀ k, (1/2 : ℝ) * Real.log ((2*Real.pi)/(l k))
      = (1/2)*Real.log (2*Real.pi) - (1/2)*Real.log (l k) := by
    intro k
    rw [Real.log_div (by positivity) (hl k).ne']
    ring
  rw [← log_specDet_eq_properTime l hl, hspec]
  simp only [gaussianLogZ]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- **★★ THE GAUSSIAN ONE-LOOP DETERMINANT INPUT, FINITE/EXACT** (brick G1).

    For the record code's finite positive mode spectrum `l : ι → ℝ` (`∀ k, 0 < l k`), the
    conjunction of:
    1. the SUBTRACTED PROPER-TIME LOG-DETERMINANT
       `log det A = ∫₀^∞ (N e^{−t} − Tr e^{−tA})/t dt` — the honest convergent
       (Frullani-subtracted) form of `−½ log det`, whose `N e^{−t}` subtraction removes the
       `t → 0` UV divergence of the raw `∫ Tr K dt/t`;
    2. the DIAGONAL GAUSSIAN `∫ e^{−½ Σ λ x²} = ∏ √(2π/λ)`;
    3. the assembled one-loop `log Z = (N/2) log(2π) − ½ ∫ (N e^{−t} − Tr e^{−tA})/t` in
       proper-time form.

    This discharges the FIRST of the DY7 conjecture's five cited physical inputs
    (`QIQTH.Conjectures.FlatSpaceRecordGravityCorrespondence`) AT THE FINITE LEVEL.

    FIREWALL: finite-dimensional diagonal spectrum only; the continuum functional
    determinant, ζ-regularization, heat-kernel asymptotics, the arbitrary `PosDef` Gaussian,
    and the removal of continuum divergences stay CITED.  The raw `½∫(dt/t) Tr K` is NOT a
    convergent integral (only the subtracted form is).  NOT the conjecture, NOT the strong
    holographic principle, NOT quantum gravity.  No axioms, no `sorry`. -/
theorem finite_one_loop_determinant {ι : Type*} [Fintype ι] (l : ι → ℝ) (hl : ∀ k, 0 < l k) :
    (Real.log (specDet l) = ∫ t in Set.Ioi (0:ℝ), logDetPTIntegrand l t)
    ∧ (∫ x : ι → ℝ, Real.exp (-((∑ k, l k * (x k)^2)/2))
        = ∏ k, Real.sqrt ((2*Real.pi)/(l k)))
    ∧ (gaussianLogZ l = ((Fintype.card ι : ℝ)/2) * Real.log (2*Real.pi)
        - (1/2) * ∫ t in Set.Ioi (0:ℝ), logDetPTIntegrand l t) :=
  ⟨log_specDet_eq_properTime l hl, gaussianIntegral_diagonal l hl,
    gaussianLogZ_eq_properTime l hl⟩

end QIQTH.OneLoopDeterminant
