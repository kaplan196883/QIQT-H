import Mathlib

/-!
# The heat trace on the unit 3-sphere `S³` (curved, `R = 6`)

**What this file proves.** The heat trace of `e^{tΔ}` on the unit 3-sphere (radius `1`, scalar
curvature `R = 6`, volume `2π²`). On `S³` the Laplace–Beltrami operator `-Δ` has the *explicit*
spectrum `λ_l = l(l+2)` (`l = 0,1,2,…`) with multiplicity `(l+1)²`. The heat trace is therefore the
concrete spectral sum
`Θ₃(t) := Tr e^{tΔ} = Σ_{l≥0} (l+1)² e^{-t l(l+2)}` (`sphere3HeatTrace`).

Since `l(l+2) = (l+1)² − 1`, reindexing `m = l+1 ≥ 1` gives the exact factorization
`Θ₃(t) = e^{t} · Σ_{m≥1} m² e^{-t m²}` (`sphere3HeatTrace_eq`). The short-time (Weyl / Seeley–DeWitt)
expansion is `Θ₃(t) = (√π/4) e^{t} t^{-3/2} + (exp-small)`, so the **leading `a₀` term is the Weyl
term** `vol/(4πt)^{d/2} = 2π²/(4πt)^{3/2} = (√π/4) t^{-3/2}` (`sphere3HeatTrace_a0`,
`t^{3/2} Θ₃(t) → √π/4`), and the **subleading `a₁ = R/6 = 1` constant** (`sphere3_a1_eq_R_div_six`,
`R = 6 ⟹ R/6 = 1`) is the Seeley–DeWitt curvature term on a SECOND curved manifold.

**What is RIGOROUSLY FORMALIZED here (all axiom-free, `#print axioms ⊆ std-3`):**

1. `sphere3HeatTrace` — the explicit `S³` spectral sum; `sphere3HeatTrace_summable`; the exact
   reindex `Θ₃(t) = e^{t} · Σ_{m≥1} m² e^{-t m²}` (`sphere3HeatTrace_eq`, from `l(l+2) = (l+1)² − 1`).
2. The three continuum Gaussian moments `∫_{(0,∞)} e^{-t x²} = √(π/t)/2`,
   `∫_{(0,∞)} x e^{-t x²} = 1/(2t)`, `∫_{(0,∞)} x² e^{-t x²} = √(π/t)/(4t)` (`gaussMoment0/1/2`,
   the last by parts against the first) — the last is the continuum spectral density integral whose
   Weyl value `√π/4 · t^{-3/2}` is the `a₀` coefficient for the unit `S³` (`d = 3`, `vol = 2π²`).
3. **The leading Weyl coefficient `a₀`** (`sphere3HeatTrace_a0`): `t^{3/2} Θ₃(t) → √π/4` as
   `t → 0⁺`, obtained by sandwiching the shifted sum `Σ_{m≥1} m² e^{-t m²}` between two explicit
   sum-integral comparisons (`sphere3ShiftedSum_lower`/`sphere3ShiftedSum_upper`), whose `O(t^{-1})`
   slack pins the leading `√π/4 · t^{-3/2}` — obtained purely from the explicit spectrum
   `{l(l+2), mult (l+1)²}` of `−Δ` on `S³`, with no heat-kernel existence and no elliptic machinery.
4. `sphere3_a1_eq_R_div_six` — the arithmetic `1 = R/6` with `R = 6`, tying the Seeley–DeWitt
   constant to the scalar curvature of the unit `S³`.

**Firewall (binding, honest).**

* This BREAKS THE HEAT-KERNEL WALL FOR THE `S³` GEOMETRY ONLY, using the theta-derivative / Poisson
  circle of ideas at the level of the explicit spectrum. The spectrum `{l(l+2), mult (l+1)²}` is the
  CARRIED classical input (the eigenvalues of `-Δ` on `S³`, exactly as the circle's `{(2πk)²}` is
  carried in `FlatTorusHeatKernel` and the `S²` `{l(l+1), mult 2l+1}` in `SphereHeatTrace`). The
  "trace" is the spectral sum over the eigenbasis of a diagonal operator — honest here; it is NOT a
  general basis-independent trace (that needs the absent trace-class API).

* This uses NONE of the missing infrastructure: no Rellich compactness, no elliptic regularity, no
  trace-class API, no manifold-`L²`/`Δ` machinery, no curved heat-kernel EXISTENCE. `a₁ = R/6 = 1` is
  VALIDATED on THIS curved geometry via the explicit spectrum — but this does NOT analytically
  discharge the GENERAL curved `a₁ = R/6` (which needs curved heat-kernel EXISTENCE = the wall, only
  available here because the `S³` spectrum is explicit; there is no explicit spectrum in general).

* This is NOT the conjecture, NOT the strong holographic principle, NOT quantum gravity. No `axiom`,
  no `sorry`.

**Checkpoint note (a₁ analytic limit).** The `a₀` Weyl term and the `a₁ = R/6 = 1` arithmetic tie
land. The *sum-level analytic* limit `(t^{3/2} Θ₃(t) − √π/4)/t → √π/4` (the `a₁` coefficient as a
short-time limit) requires the exponentially-small Poisson remainder of the theta derivative
`Σ m² e^{-t m²} = (√π/4) t^{-3/2} + (exp-small)` — the same remainder-packaging gap flagged in the
`S²` file (there discharged by a bespoke periodic-Bernoulli Euler–Maclaurin). The two-sided
sum-integral sandwich used here for `a₀` has `O(t^{-1})` slack, which is enough to pin `a₀` but too
coarse for the `a₁` limit; that limit is left as the recorded gap for the `S³` geometry.
-/

namespace QIQTH.Sphere3HeatTrace

open scoped Real
open Filter Topology MeasureTheory

/-- The `S³` spectral heat trace `Tr e^{tΔ} = Σ_{l≥0} (l+1)² e^{-t l(l+2)}`: eigenvalue `l(l+2)`
of `-Δ` with multiplicity `(l+1)²` (the degree-`l` spherical harmonics on `S³`). -/
noncomputable def sphere3HeatTrace (t : ℝ) : ℝ :=
  ∑' l : ℕ, ((l : ℝ) + 1) ^ 2 * Real.exp (-t * ((l : ℝ) * ((l : ℝ) + 2)))

/-- The reindexed "shifted" sum `Σ_{m≥0} m² e^{-t m²}` (the `m = 0` term is `0`, so this is
`Σ_{m≥1} m² e^{-t m²}`). -/
noncomputable def sphere3ShiftedSum (t : ℝ) : ℝ :=
  ∑' m : ℕ, (m : ℝ) ^ 2 * Real.exp (-t * (m : ℝ) ^ 2)

/-- **Summability of the heat-trace summand** (for `t > 0`). Multiplicity `(l+1)²` grows
polynomially while `e^{-t l(l+2)} ≤ e^{-t l}` decays geometrically. No compactness/regularity input
is needed — the spectrum is explicit. -/
theorem sphere3HeatTrace_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun l : ℕ => ((l : ℝ) + 1) ^ 2 * Real.exp (-t * ((l : ℝ) * ((l : ℝ) + 2)))) := by
  have h2 : Summable (fun l : ℕ => (l : ℝ) ^ 2 * Real.exp (-t * (l : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 2 ht
  have h1 : Summable (fun l : ℕ => (l : ℝ) ^ 1 * Real.exp (-t * (l : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 1 ht
  have h0 : Summable (fun l : ℕ => (l : ℝ) ^ 0 * Real.exp (-t * (l : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 0 ht
  have hdom : Summable (fun l : ℕ => ((l : ℝ) + 1) ^ 2 * Real.exp (-t * (l : ℝ))) := by
    have := (h2.add (h1.mul_left 2)).add h0
    refine this.congr (fun l => ?_)
    simp only [pow_one, pow_zero, one_mul]; ring
  refine hdom.of_nonneg_of_le (fun l => by positivity) (fun l => ?_)
  have hle : (l : ℝ) ≤ (l : ℝ) * ((l : ℝ) + 2) := by nlinarith [Nat.cast_nonneg (α := ℝ) l]
  have hexp : Real.exp (-t * ((l : ℝ) * ((l : ℝ) + 2))) ≤ Real.exp (-t * (l : ℝ)) := by
    apply Real.exp_le_exp.mpr; nlinarith [mul_le_mul_of_nonneg_left hle ht.le]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Summability of the shifted summand** `m² e^{-t m²}` (for `t > 0`): dominated by `m² e^{-t m}`
since `m² ≥ m`. -/
theorem sphere3ShiftedSum_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ => (m : ℝ) ^ 2 * Real.exp (-t * (m : ℝ) ^ 2)) := by
  have h2 : Summable (fun m : ℕ => (m : ℝ) ^ 2 * Real.exp (-t * (m : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 2 ht
  refine h2.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
  have hle : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
      nlinarith
  have hexp : Real.exp (-t * (m : ℝ) ^ 2) ≤ Real.exp (-t * (m : ℝ)) := by
    apply Real.exp_le_exp.mpr; nlinarith [mul_le_mul_of_nonneg_left hle ht.le]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **The reindex `Θ₃(t) = e^{t} · Σ_{m≥1} m² e^{-t m²}`.** Using `l(l+2) = (l+1)² − 1`, each summand
factors as `e^{-t l(l+2)} = e^{t} e^{-t (l+1)²}`, and shifting `m = l+1` (the `m = 0` term of the
shifted sum vanishes) gives the factorization. -/
theorem sphere3HeatTrace_eq {t : ℝ} (ht : 0 < t) :
    sphere3HeatTrace t = Real.exp t * sphere3ShiftedSum t := by
  have hsummShift : Summable (fun m : ℕ => (m : ℝ) ^ 2 * Real.exp (-t * (m : ℝ) ^ 2)) :=
    sphere3ShiftedSum_summable ht
  -- `Σ_{m} m² e^{-t m²} = 0 + Σ_{l} (l+1)² e^{-t (l+1)²}`
  have hshift : sphere3ShiftedSum t
      = ∑' l : ℕ, ((l : ℝ) + 1) ^ 2 * Real.exp (-t * ((l : ℝ) + 1) ^ 2) := by
    rw [sphere3ShiftedSum, hsummShift.tsum_eq_zero_add]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      Nat.cast_add, Nat.cast_one, zero_add]
  rw [sphere3HeatTrace, hshift, ← tsum_mul_left]
  refine tsum_congr (fun l => ?_)
  have he : Real.exp (-t * ((l : ℝ) * ((l : ℝ) + 2)))
      = Real.exp t * Real.exp (-t * ((l : ℝ) + 1) ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]; ring

/-! ### The three continuum Gaussian moments -/

/-- `∫_{(0,∞)} e^{-t x²} = √(π/t)/2`. -/
theorem gaussMoment0 (t : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-t * x ^ 2) = Real.sqrt (π / t) / 2 :=
  integral_gaussian_Ioi t

/-- `x · e^{-t x²} → 0` as `x → ∞` (dominated by `x e^{-t x}`). -/
private lemma x_mul_exp_sq_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x : ℝ => x * Real.exp (-t * x ^ 2)) atTop (𝓝 0) := by
  have hub : Tendsto (fun x : ℝ => x * Real.exp (-t * x)) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 t ht
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _; rw [Real.rpow_one]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_nonneg hx (Real.exp_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hle : Real.exp (-t * x ^ 2) ≤ Real.exp (-t * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg ht.le (mul_nonneg (by linarith : (0:ℝ) ≤ x) (by linarith : (0:ℝ) ≤ x - 1))]
    exact mul_le_mul_of_nonneg_left hle (by linarith)

/-- `e^{-t x²} → 0` as `x → ∞`. -/
private lemma exp_sq_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x : ℝ => Real.exp (-t * x ^ 2)) atTop (𝓝 0) := by
  have hbot : Tendsto (fun x : ℝ => -t * x ^ 2) atTop atBot :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg (neg_lt_zero.mpr ht)
  exact Real.tendsto_exp_atBot.comp hbot

/-- `∫_{(0,∞)} x e^{-t x²} = 1/(2t)`. FTC with antiderivative `-(1/(2t)) e^{-t x²}`. -/
theorem gaussMoment1 {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-t * x ^ 2) = 1 / (2 * t) := by
  set g : ℝ → ℝ := fun x => -(1 / (2 * t)) * Real.exp (-t * x ^ 2) with hg
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (x * Real.exp (-t * x ^ 2)) x := by
    intro x _
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have hin : HasDerivAt (fun y : ℝ => -t * y ^ 2) (-t * (2 * x)) x := hpow.const_mul (-t)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-t * y ^ 2))
        (Real.exp (-t * x ^ 2) * (-t * (2 * x))) x := hin.exp
    have hfin := hexp.const_mul (-(1 / (2 * t)))
    convert hfin using 1; field_simp
  have hint : IntegrableOn (fun x => x * Real.exp (-t * x ^ 2)) (Set.Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq ht).integrableOn
  have htend : Tendsto g atTop (𝓝 0) := by
    have he := exp_sq_tendsto_zero ht
    simpa [hg] using he.const_mul (-(1 / (2 * t)))
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [hmain]
  have hg0 : g 0 = -(1 / (2 * t)) := by rw [hg]; simp
  rw [hg0]; ring

/-- `∫_{(0,∞)} x² e^{-t x²} = √(π/t)/(4t)`. Integration by parts against `gaussMoment0`: the
antiderivative `-(x/(2t)) e^{-t x²}` has derivative `x² e^{-t x²} − (1/(2t)) e^{-t x²}`. -/
theorem gaussMoment2 {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-t * x ^ 2) = Real.sqrt (π / t) / (4 * t) := by
  have ht0 : t ≠ 0 := ht.ne'
  set g : ℝ → ℝ := fun x => -(x / (2 * t)) * Real.exp (-t * x ^ 2) with hg
  let g' : ℝ → ℝ := fun x => x ^ 2 * Real.exp (-t * x ^ 2) - (1 / (2 * t)) * Real.exp (-t * x ^ 2)
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (g' x) x := by
    intro x _
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have hin : HasDerivAt (fun y : ℝ => -t * y ^ 2) (-t * (2 * x)) x := hpow.const_mul (-t)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-t * y ^ 2))
        (Real.exp (-t * x ^ 2) * (-t * (2 * x))) x := hin.exp
    have hlin : HasDerivAt (fun y : ℝ => -(y / (2 * t))) (-(1 / (2 * t))) x := by
      have : HasDerivAt (fun y : ℝ => y / (2 * t)) (1 / (2 * t)) x := by
        simpa using (hasDerivAt_id x).div_const (2 * t)
      simpa using this.neg
    have hmul := hlin.mul hexp
    convert hmul using 1
    show g' x = _
    simp only [g']; field_simp; ring
  -- integrability
  have hE : IntegrableOn (fun x : ℝ => Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    (integrable_exp_neg_mul_sq ht).integrableOn
  have hX2 : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq ht (by norm_num : (-1 : ℝ) < 2)).integrableOn
      (s := Set.Ioi (0 : ℝ))
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hint : IntegrableOn g' (Set.Ioi 0) := hX2.sub (hE.const_mul (1 / (2 * t)))
  have htend : Tendsto g atTop (𝓝 0) := by
    have hxe := x_mul_exp_sq_tendsto_zero ht
    have hc : Tendsto (fun x : ℝ => -(1 / (2 * t)) * (x * Real.exp (-t * x ^ 2))) atTop (𝓝 0) := by
      simpa using hxe.const_mul (-(1 / (2 * t)))
    refine hc.congr (fun x => ?_)
    rw [hg]; ring
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  have hg0 : g 0 = 0 := by rw [hg]; simp
  rw [hg0, sub_zero] at hmain
  -- hmain : ∫ g' = 0
  have hsplit : ∫ x in Set.Ioi (0 : ℝ), g' x
      = (∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-t * x ^ 2))
        - (1 / (2 * t)) * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-t * x ^ 2) := by
    simp only [g']
    rw [integral_sub hX2 (hE.const_mul (1 / (2 * t))), integral_const_mul]
  rw [hsplit, gaussMoment0] at hmain
  have hval : ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-t * x ^ 2)
      = (1 / (2 * t)) * (Real.sqrt (π / t) / 2) := by linarith [hmain]
  rw [hval]; ring

/-- **FTC on `(a,∞)` for `x e^{-t x²}`:** `∫_{(a,∞)} x e^{-t x²} = (1/(2t)) e^{-t a²}`. -/
private lemma intIoi_x_exp {t : ℝ} (ht : 0 < t) (a : ℝ) :
    ∫ x in Set.Ioi a, x * Real.exp (-t * x ^ 2) = (1 / (2 * t)) * Real.exp (-t * a ^ 2) := by
  set g : ℝ → ℝ := fun x => -(1 / (2 * t)) * Real.exp (-t * x ^ 2) with hg
  have hderiv : ∀ x ∈ Set.Ici a, HasDerivAt g (x * Real.exp (-t * x ^ 2)) x := by
    intro x _
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have hin : HasDerivAt (fun y : ℝ => -t * y ^ 2) (-t * (2 * x)) x := hpow.const_mul (-t)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-t * y ^ 2))
        (Real.exp (-t * x ^ 2) * (-t * (2 * x))) x := hin.exp
    have hfin := hexp.const_mul (-(1 / (2 * t)))
    convert hfin using 1; field_simp
  have hint : IntegrableOn (fun x => x * Real.exp (-t * x ^ 2)) (Set.Ioi a) :=
    (integrable_mul_exp_neg_mul_sq ht).integrableOn
  have htend : Tendsto g atTop (𝓝 0) := by
    have he := exp_sq_tendsto_zero ht
    simpa [hg] using he.const_mul (-(1 / (2 * t)))
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [hmain, hg]; ring

/-- **FTC on `(a,∞)` for `x² e^{-t x²}`, relating it to the gaussian tail:**
`∫_{(a,∞)} x² e^{-t x²} = (a/(2t)) e^{-t a²} + (1/(2t)) ∫_{(a,∞)} e^{-t x²}`. -/
private lemma intIoi_x2_exp_rel {t : ℝ} (ht : 0 < t) (a : ℝ) :
    ∫ x in Set.Ioi a, x ^ 2 * Real.exp (-t * x ^ 2)
      = (a / (2 * t)) * Real.exp (-t * a ^ 2)
        + (1 / (2 * t)) * ∫ x in Set.Ioi a, Real.exp (-t * x ^ 2) := by
  have ht0 : t ≠ 0 := ht.ne'
  set g : ℝ → ℝ := fun x => -(x / (2 * t)) * Real.exp (-t * x ^ 2) with hg
  let g' : ℝ → ℝ := fun x => x ^ 2 * Real.exp (-t * x ^ 2) - (1 / (2 * t)) * Real.exp (-t * x ^ 2)
  have hderiv : ∀ x ∈ Set.Ici a, HasDerivAt g (g' x) x := by
    intro x _
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have hin : HasDerivAt (fun y : ℝ => -t * y ^ 2) (-t * (2 * x)) x := hpow.const_mul (-t)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-t * y ^ 2))
        (Real.exp (-t * x ^ 2) * (-t * (2 * x))) x := hin.exp
    have hlin : HasDerivAt (fun y : ℝ => -(y / (2 * t))) (-(1 / (2 * t))) x := by
      have : HasDerivAt (fun y : ℝ => y / (2 * t)) (1 / (2 * t)) x := by
        simpa using (hasDerivAt_id x).div_const (2 * t)
      simpa using this.neg
    have hmul := hlin.mul hexp
    convert hmul using 1
    show g' x = _
    simp only [g']; field_simp; ring
  have hE : IntegrableOn (fun x : ℝ => Real.exp (-t * x ^ 2)) (Set.Ioi a) :=
    (integrable_exp_neg_mul_sq ht).integrableOn
  have hX2 : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2)) (Set.Ioi a) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq ht (by norm_num : (-1 : ℝ) < 2)).integrableOn
      (s := Set.Ioi a)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hint : IntegrableOn g' (Set.Ioi a) := hX2.sub (hE.const_mul (1 / (2 * t)))
  have htend : Tendsto g atTop (𝓝 0) := by
    have hxe := x_mul_exp_sq_tendsto_zero ht
    have hc : Tendsto (fun x : ℝ => -(1 / (2 * t)) * (x * Real.exp (-t * x ^ 2))) atTop (𝓝 0) := by
      simpa using hxe.const_mul (-(1 / (2 * t)))
    refine hc.congr (fun x => ?_)
    rw [hg]; ring
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  have hsplit : ∫ x in Set.Ioi a, g' x
      = (∫ x in Set.Ioi a, x ^ 2 * Real.exp (-t * x ^ 2))
        - (1 / (2 * t)) * ∫ x in Set.Ioi a, Real.exp (-t * x ^ 2) := by
    simp only [g']
    rw [integral_sub hX2 (hE.const_mul (1 / (2 * t))), integral_const_mul]
  rw [hsplit] at hmain
  have hga : g a = -(a / (2 * t)) * Real.exp (-t * a ^ 2) := by rw [hg]
  rw [hga] at hmain
  linarith [hmain]

/-- **Split of `∫_{(0,∞)}` into `(0,1]` and `(1,∞)`.** -/
private lemma ioi0_split {f : ℝ → ℝ} (hf0 : IntegrableOn f (Set.Ioi (0 : ℝ))) :
    ∫ x in Set.Ioi (0 : ℝ), f x
      = (∫ x in Set.Ioc (0 : ℝ) 1, f x) + ∫ x in Set.Ioi (1 : ℝ), f x := by
  have hIoc : IntegrableOn f (Set.Ioc (0 : ℝ) 1) := hf0.mono_set (fun x hx => hx.1)
  have hIoi1 : IntegrableOn f (Set.Ioi (1 : ℝ)) :=
    hf0.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr (fun x hx hx' => absurd hx.2 (not_le.mpr hx'))
  rw [← setIntegral_union hdisj measurableSet_Ioi hIoc hIoi1,
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]

/-- The `(0,1]` gaussian mass is `≤ 1` (the integrand is `≤ 1` and the interval has length `1`). -/
private lemma gaussIoc01_le_one {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioc (0 : ℝ) 1, Real.exp (-t * x ^ 2) ≤ 1 := by
  have hExp : IntegrableOn (fun x : ℝ => Real.exp (-t * x ^ 2)) (Set.Ioc (0 : ℝ) 1) :=
    (integrable_exp_neg_mul_sq ht).integrableOn
  have hfin : volume (Set.Ioc (0 : ℝ) 1) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) 1) := integrableOn_const hfin
  have hmono : ∫ x in Set.Ioc (0 : ℝ) 1, Real.exp (-t * x ^ 2)
      ≤ ∫ _x in Set.Ioc (0 : ℝ) 1, (1 : ℝ) := by
    apply setIntegral_mono_on hExp hconst measurableSet_Ioc
    intro x _
    calc Real.exp (-t * x ^ 2) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ht.le (sq_nonneg x)])
      _ = 1 := Real.exp_zero
  calc ∫ x in Set.Ioc (0 : ℝ) 1, Real.exp (-t * x ^ 2)
      ≤ ∫ _x in Set.Ioc (0 : ℝ) 1, (1 : ℝ) := hmono
    _ = 1 := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        simp

/-! ### The `a₀` sandwich for the shifted sum -/

/-- **Upper bound.** `Σ_{m≥1} m² e^{-t m²} ≤ √(π/t)/(4t) + 1/t + √(π/t)/2`. The sum is bounded above
by `∫_{(1,∞)} x² e^{-t(x-1)²} dx = ∫_{(0,∞)} (x+1)² e^{-t x²} dx = M₂ + 2M₁ + M₀` via the
sum-integral comparison (`x²` monotone × `e^{-t x²}` antitone). -/
theorem sphere3ShiftedSum_upper {t : ℝ} (ht : 0 < t) :
    sphere3ShiftedSum t ≤ Real.sqrt (π / t) / (4 * t) + 1 / t + Real.sqrt (π / t) / 2 := by
  set term : ℕ → ℝ := fun i => (i : ℝ) ^ 2 * Real.exp (-t * (i : ℝ) ^ 2) with hterm
  -- integrability + value of `∫_{(0,∞)} (x+1)² e^{-t x²}`
  have hE := (integrable_exp_neg_mul_sq ht).integrableOn (s := Set.Ioi (0 : ℝ))
  have hX1 := (integrable_mul_exp_neg_mul_sq ht).integrableOn (s := Set.Ioi (0 : ℝ))
  have hX2 : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq ht (by norm_num : (-1 : ℝ) < 2)).integrableOn
      (s := Set.Ioi (0 : ℝ))
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hUint : IntegrableOn (fun x => (x + 1) ^ 2 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) := by
    have := (hX2.add (hX1.const_mul 2)).add hE
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have hUval : ∫ x in Set.Ioi (0 : ℝ), (x + 1) ^ 2 * Real.exp (-t * x ^ 2)
      = Real.sqrt (π / t) / (4 * t) + 1 / t + Real.sqrt (π / t) / 2 := by
    have hcongr : ∀ x : ℝ, (x + 1) ^ 2 * Real.exp (-t * x ^ 2)
        = x ^ 2 * Real.exp (-t * x ^ 2) + x * Real.exp (-t * x ^ 2)
          + x * Real.exp (-t * x ^ 2) + Real.exp (-t * x ^ 2) := fun x => by ring
    have hI2 : IntegrableOn
        (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2) + x * Real.exp (-t * x ^ 2))
        (Set.Ioi (0 : ℝ)) := hX2.add hX1
    have hI3 : IntegrableOn
        (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2) + x * Real.exp (-t * x ^ 2)
          + x * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) := hI2.add hX1
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hcongr x),
      integral_add hI3 hE, integral_add hI2 hX1, integral_add hX2 hX1,
      gaussMoment2 ht, gaussMoment1 ht, gaussMoment0]
    ring
  -- per-N sum ≤ interval integral
  have hcmp : ∀ N : ℕ, 1 ≤ N →
      ∑ i ∈ Finset.Ico 1 N, term i ≤ ∫ x in (1 : ℝ)..(N : ℝ), x ^ 2 * Real.exp (-t * (x - 1) ^ 2) := by
    intro N hN
    have hmono : MonotoneOn (fun x : ℝ => x ^ 2) (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
      intro p hp q hq hpq
      have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp.1
      nlinarith [hp0, hpq]
    have hanti : AntitoneOn (fun x : ℝ => Real.exp (-t * x ^ 2))
        (Set.Icc (((1 : ℕ) : ℝ) - 1) (((N : ℕ) : ℝ) - 1)) := by
      intro p hp q hq hpq
      apply Real.exp_le_exp.mpr
      have hp0 : (0 : ℝ) ≤ p := by simpa using hp.1
      nlinarith [mul_nonneg ht.le (mul_nonneg (by linarith : (0 : ℝ) ≤ q - p)
        (by linarith : (0 : ℝ) ≤ q + p))]
    have key := sum_mul_Ico_le_integral_of_monotone_antitone (a := 1) (b := N)
      (f := fun x => x ^ 2) (g := fun x => Real.exp (-t * x ^ 2)) hN hmono hanti (by norm_num)
      (Real.exp_nonneg _)
    rw [Nat.cast_one] at key
    calc ∑ i ∈ Finset.Ico 1 N, term i
        = ∑ i ∈ Finset.Ico 1 N, (fun x : ℝ => x ^ 2) (i : ℝ)
            * (fun x : ℝ => Real.exp (-t * x ^ 2)) (i : ℝ) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); simp only [hterm]
      _ ≤ ∫ x in (1 : ℝ)..(N : ℝ), (fun x : ℝ => x ^ 2) x
            * (fun x : ℝ => Real.exp (-t * x ^ 2)) (x - 1) := key
      _ = ∫ x in (1 : ℝ)..(N : ℝ), x ^ 2 * Real.exp (-t * (x - 1) ^ 2) := by
          refine intervalIntegral.integral_congr (fun x _ => ?_); simp
  -- substitution `∫_1^N x² e^{-t(x-1)²} = ∫_0^{N-1} (x+1)² e^{-t x²}`
  have hsubst : ∀ N : ℕ, ∫ x in (1 : ℝ)..(N : ℝ), x ^ 2 * Real.exp (-t * (x - 1) ^ 2)
      = ∫ x in (0 : ℝ)..((N : ℝ) - 1), (x + 1) ^ 2 * Real.exp (-t * x ^ 2) := by
    intro N
    have h := intervalIntegral.integral_comp_sub_right
      (a := (1 : ℝ)) (b := (N : ℝ)) (f := fun u : ℝ => (u + 1) ^ 2 * Real.exp (-t * u ^ 2)) 1
    rw [show (1 : ℝ) - 1 = 0 by norm_num] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun x _ => ?_); ring_nf
  -- pass to the limit
  have hInt_tendsto : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), x ^ 2 * Real.exp (-t * (x - 1) ^ 2))
      atTop (𝓝 (∫ x in Set.Ioi (0 : ℝ), (x + 1) ^ 2 * Real.exp (-t * x ^ 2))) := by
    have hb : Tendsto (fun N : ℕ => (N : ℝ) - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
    have hlim := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hUint hb
    exact hlim.congr (fun N => (hsubst N).symm)
  have hHS : HasSum term (sphere3ShiftedSum t) := (sphere3ShiftedSum_summable ht).hasSum
  have hpartial : Tendsto (fun N => ∑ i ∈ Finset.range N, term i) atTop (𝓝 (sphere3ShiftedSum t)) :=
    hHS.tendsto_sum_nat
  have hterm0 : term 0 = 0 := by simp [hterm]
  have hpartial' : Tendsto (fun N => ∑ i ∈ Finset.Ico 1 N, term i) atTop
      (𝓝 (sphere3ShiftedSum t - term 0)) := by
    have heq : (fun N => (∑ i ∈ Finset.range N, term i) - term 0)
        =ᶠ[atTop] (fun N => ∑ i ∈ Finset.Ico 1 N, term i) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have h01 : ∑ i ∈ Finset.Ico 0 1, term i = term 0 := by
        rw [← Finset.range_eq_Ico, Finset.sum_range_one]
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive term (Nat.zero_le 1) hN, h01]; ring
    exact (hpartial.sub_const (term 0)).congr' heq
  have hle : sphere3ShiftedSum t - term 0
      ≤ ∫ x in Set.Ioi (0 : ℝ), (x + 1) ^ 2 * Real.exp (-t * x ^ 2) := by
    refine le_of_tendsto_of_tendsto hpartial' hInt_tendsto ?_
    filter_upwards [eventually_ge_atTop 1] with N hN using hcmp N hN
  rw [hterm0, sub_zero, hUval] at hle
  exact hle

/-- **Lower bound.** `√(π/t)/2 + √(π/t)/(4t) − 1 − 1/t ≤ Σ_{m≥1} m² e^{-t m²}`. The sum is bounded
below by `L := ∫_{(1,∞)} e^{-t x²}(x−1)² dx` (sum-integral comparison, `e^{-t x²}` antitone × `x²`
monotone); then `L = C₃(1 + 1/(2t)) − (1/(2t))e^{-t}` with `C₃ = ∫_{(1,∞)} e^{-t x²} = √(π/t)/2 − D`,
`D = ∫_{(0,1]} e^{-t x²} ∈ [0,1]`, using the exact FTC relations `∫_{(1,∞)} x e^{-t x²} = (1/(2t))e^{-t}`
and `∫_{(1,∞)} x² e^{-t x²} = (1/(2t))e^{-t} + (1/(2t))C₃`. -/
theorem sphere3ShiftedSum_lower {t : ℝ} (ht : 0 < t) :
    Real.sqrt (π / t) / 2 + Real.sqrt (π / t) / (4 * t) - 1 - 1 / t ≤ sphere3ShiftedSum t := by
  set term : ℕ → ℝ := fun i => (i : ℝ) ^ 2 * Real.exp (-t * (i : ℝ) ^ 2) with hterm
  -- integrability on `(1,∞)`
  have hX2_0 : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq ht (by norm_num : (-1 : ℝ) < 2)).integrableOn
      (s := Set.Ioi (0 : ℝ))
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsub01 : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (by norm_num)
  have hX2' : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2)) (Set.Ioi (1 : ℝ)) :=
    hX2_0.mono_set hsub01
  have hX1' : IntegrableOn (fun x : ℝ => x * Real.exp (-t * x ^ 2)) (Set.Ioi (1 : ℝ)) :=
    (integrable_mul_exp_neg_mul_sq ht).integrableOn
  have hE' : IntegrableOn (fun x : ℝ => Real.exp (-t * x ^ 2)) (Set.Ioi (1 : ℝ)) :=
    (integrable_exp_neg_mul_sq ht).integrableOn
  have hLint : IntegrableOn (fun x : ℝ => Real.exp (-t * x ^ 2) * (x - 1) ^ 2) (Set.Ioi (1 : ℝ)) := by
    have hJ : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2) - x * Real.exp (-t * x ^ 2))
        (Set.Ioi (1 : ℝ)) := hX2'.sub hX1'
    have hI : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2) - x * Real.exp (-t * x ^ 2)
        - x * Real.exp (-t * x ^ 2)) (Set.Ioi (1 : ℝ)) := hJ.sub hX1'
    have := hI.add hE'
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  -- value decomposition of `L`
  set C1 : ℝ := ∫ x in Set.Ioi (1 : ℝ), x ^ 2 * Real.exp (-t * x ^ 2) with hC1def
  set C2 : ℝ := ∫ x in Set.Ioi (1 : ℝ), x * Real.exp (-t * x ^ 2) with hC2def
  set C3 : ℝ := ∫ x in Set.Ioi (1 : ℝ), Real.exp (-t * x ^ 2) with hC3def
  have hLval : ∫ x in Set.Ioi (1 : ℝ), Real.exp (-t * x ^ 2) * (x - 1) ^ 2 = C1 - C2 - C2 + C3 := by
    have hcongr : ∀ x : ℝ, Real.exp (-t * x ^ 2) * (x - 1) ^ 2
        = x ^ 2 * Real.exp (-t * x ^ 2) - x * Real.exp (-t * x ^ 2) - x * Real.exp (-t * x ^ 2)
          + Real.exp (-t * x ^ 2) := fun x => by ring
    have hJ : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2) - x * Real.exp (-t * x ^ 2))
        (Set.Ioi (1 : ℝ)) := hX2'.sub hX1'
    have hI : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-t * x ^ 2) - x * Real.exp (-t * x ^ 2)
        - x * Real.exp (-t * x ^ 2)) (Set.Ioi (1 : ℝ)) := hJ.sub hX1'
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hcongr x),
      integral_add hI hE', integral_sub hJ hX1', integral_sub hX2' hX1']
  -- exact FTC relations at `a = 1`
  have hC2v : C2 = (1 / (2 * t)) * Real.exp (-t) := by
    rw [hC2def, intIoi_x_exp ht 1, show -t * (1 : ℝ) ^ 2 = -t by ring]
  have hC1v : C1 = (1 / (2 * t)) * Real.exp (-t) + (1 / (2 * t)) * C3 := by
    rw [hC1def, intIoi_x2_exp_rel ht 1, ← hC3def, show -t * (1 : ℝ) ^ 2 = -t by ring]
  -- `C3 = √(π/t)/2 − D`, with `D ∈ [0,1]`
  have hsplit := ioi0_split (f := fun x : ℝ => Real.exp (-t * x ^ 2))
    ((integrable_exp_neg_mul_sq ht).integrableOn)
  rw [gaussMoment0] at hsplit
  set D : ℝ := ∫ x in Set.Ioc (0 : ℝ) 1, Real.exp (-t * x ^ 2) with hDdef
  have hC3v : C3 = Real.sqrt (π / t) / 2 - D := by rw [hC3def]; linarith [hsplit]
  have hD1 : D ≤ 1 := gaussIoc01_le_one ht
  have hD0 : 0 ≤ D := by
    rw [hDdef]; exact setIntegral_nonneg measurableSet_Ioc (fun x _ => Real.exp_nonneg _)
  have hE1 : Real.exp (-t) ≤ 1 := by
    calc Real.exp (-t) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hE0 : 0 ≤ Real.exp (-t) := Real.exp_nonneg _
  have hu : 0 < 1 / (2 * t) := by positivity
  -- the sandwich lower comparison
  have hcmp : ∀ N : ℕ, 1 ≤ N →
      ∫ x in (1 : ℝ)..(N : ℝ), Real.exp (-t * x ^ 2) * (x - 1) ^ 2 ≤ ∑ i ∈ Finset.Ico 1 N, term i := by
    intro N hN
    have hanti : AntitoneOn (fun x : ℝ => Real.exp (-t * x ^ 2)) (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
      intro p hp q hq hpq
      apply Real.exp_le_exp.mpr
      have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp.1
      nlinarith [mul_nonneg ht.le (mul_nonneg (by linarith : (0 : ℝ) ≤ q - p)
        (by linarith : (0 : ℝ) ≤ q + p))]
    have hmono : MonotoneOn (fun x : ℝ => x ^ 2) (Set.Icc (((1 : ℕ) : ℝ) - 1) (((N : ℕ) : ℝ) - 1)) := by
      intro p hp q hq hpq
      have hp0 : (0 : ℝ) ≤ p := by simpa using hp.1
      nlinarith [hp0, hpq]
    have key := integral_le_sum_mul_Ico_of_antitone_monotone (a := 1) (b := N)
      (f := fun x => Real.exp (-t * x ^ 2)) (g := fun x => x ^ 2) hN hanti hmono
      (Real.exp_nonneg _) (by norm_num)
    rw [Nat.cast_one] at key
    calc ∫ x in (1 : ℝ)..(N : ℝ), Real.exp (-t * x ^ 2) * (x - 1) ^ 2
        = ∫ x in (1 : ℝ)..(N : ℝ), (fun x : ℝ => Real.exp (-t * x ^ 2)) x
            * (fun x : ℝ => x ^ 2) (x - 1) := by
          refine intervalIntegral.integral_congr (fun x _ => ?_); simp
      _ ≤ ∑ i ∈ Finset.Ico 1 N, (fun x : ℝ => Real.exp (-t * x ^ 2)) (i : ℝ)
            * (fun x : ℝ => x ^ 2) (i : ℝ) := key
      _ = ∑ i ∈ Finset.Ico 1 N, term i := by
          refine Finset.sum_congr rfl (fun i _ => ?_); simp only [hterm]; ring
  -- pass to the limit
  have hLtendsto : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), Real.exp (-t * x ^ 2) * (x - 1) ^ 2)
      atTop (𝓝 (∫ x in Set.Ioi (1 : ℝ), Real.exp (-t * x ^ 2) * (x - 1) ^ 2)) :=
    intervalIntegral_tendsto_integral_Ioi 1 hLint tendsto_natCast_atTop_atTop
  have hHS : HasSum term (sphere3ShiftedSum t) := (sphere3ShiftedSum_summable ht).hasSum
  have hpartial : Tendsto (fun N => ∑ i ∈ Finset.range N, term i) atTop (𝓝 (sphere3ShiftedSum t)) :=
    hHS.tendsto_sum_nat
  have hterm0 : term 0 = 0 := by simp [hterm]
  have hpartial' : Tendsto (fun N => ∑ i ∈ Finset.Ico 1 N, term i) atTop
      (𝓝 (sphere3ShiftedSum t - term 0)) := by
    have heq : (fun N => (∑ i ∈ Finset.range N, term i) - term 0)
        =ᶠ[atTop] (fun N => ∑ i ∈ Finset.Ico 1 N, term i) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have h01 : ∑ i ∈ Finset.Ico 0 1, term i = term 0 := by
        rw [← Finset.range_eq_Ico, Finset.sum_range_one]
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive term (Nat.zero_le 1) hN, h01]; ring
    exact (hpartial.sub_const (term 0)).congr' heq
  have hle : ∫ x in Set.Ioi (1 : ℝ), Real.exp (-t * x ^ 2) * (x - 1) ^ 2
      ≤ sphere3ShiftedSum t - term 0 := by
    refine le_of_tendsto_of_tendsto hLtendsto hpartial' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN using hcmp N hN
  rw [hterm0, sub_zero] at hle
  -- algebra: L ≥ LB
  rw [hLval, hC1v, hC2v, hC3v] at hle
  -- `hle : ((1/(2t))e^{-t} + (1/(2t))C3) - C2 ... ` — now purely algebraic in D, e^{-t}, √(π/t), 1/(2t)
  set u : ℝ := 1 / (2 * t) with hudef
  set S : ℝ := Real.sqrt (π / t) with hSdef
  set E : ℝ := Real.exp (-t) with hEdef
  have h4t : S / (4 * t) = u * S / 2 := by rw [hudef]; field_simp; ring
  have h1t : (1 : ℝ) / t = 2 * u := by rw [hudef]; field_simp
  rw [h4t, h1t]
  nlinarith [hle, hu.le, hD0, hD1, hE0, hE1, mul_nonneg hu.le (by linarith : (0 : ℝ) ≤ 1 - D),
    mul_nonneg hu.le (by linarith : (0 : ℝ) ≤ 1 - E)]

/-! ### The Weyl `a₀` short-time asymptotic and the `a₁ = R/6` tie -/

/-- **★ The leading Weyl (`a₀`) short-time asymptotic on the curved `S³`.**
`t^{3/2} · Θ₃(t) → √π/4` as `t → 0⁺`, i.e. `Θ₃(t) = (√π/4) t^{-3/2} + o(t^{-3/2})` — the leading Weyl
term `a₀ = vol/(4πt)^{3/2} = 2π²/(4πt)^{3/2} = (√π/4) t^{-3/2}` for the unit `S³`.
Proved from the reindex `Θ₃(t) = e^{t} · Σ_{m≥1} m² e^{-t m²}` (`sphere3HeatTrace_eq`), squeezing
`t^{3/2} · Σ_{m≥1} m² e^{-t m²}` between the two explicit sum-integral bounds
(`sphere3ShiftedSum_lower`/`sphere3ShiftedSum_upper`) whose `O(t^{-1})` slack pins the leading
`√π/4 · t^{-3/2}`, times `e^{t} → 1` — obtained purely from the explicit spectrum
`{l(l+2), mult (l+1)²}` of `−Δ` on `S³`, with no heat-kernel existence and no elliptic machinery.
(The subleading `a₁ = R/6 = 1` short-time limit is NOT resolved by this sandwich — see the file
header for the precise remaining gap.) -/
theorem sphere3HeatTrace_a0 :
    Filter.Tendsto (fun t : ℝ => t ^ ((3 : ℝ) / 2) * sphere3HeatTrace t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt π / 4)) := by
  have hrpow32 : ∀ t : ℝ, 0 < t → t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
    intro t ht
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hsp : ∀ t : ℝ, 0 < t → Real.sqrt t * Real.sqrt (π / t) = Real.sqrt π := by
    intro t ht
    rw [← Real.sqrt_mul ht.le]; congr 1; field_simp
  -- the three scaling identities
  have hA : ∀ t : ℝ, 0 < t → t ^ ((3 : ℝ) / 2) * (Real.sqrt (π / t) / (4 * t)) = Real.sqrt π / 4 := by
    intro t ht
    rw [hrpow32 t ht, show t * Real.sqrt t * (Real.sqrt (π / t) / (4 * t))
      = (Real.sqrt t * Real.sqrt (π / t)) * (t / (4 * t)) by ring, hsp t ht,
      show t / (4 * t) = 1 / 4 by field_simp]
    ring
  have hB : ∀ t : ℝ, 0 < t → t ^ ((3 : ℝ) / 2) * (1 / t) = Real.sqrt t := by
    intro t ht; rw [hrpow32 t ht]; field_simp
  have hC : ∀ t : ℝ, 0 < t → t ^ ((3 : ℝ) / 2) * (Real.sqrt (π / t) / 2) = t * Real.sqrt π / 2 := by
    intro t ht
    rw [hrpow32 t ht, show t * Real.sqrt t * (Real.sqrt (π / t) / 2)
      = (Real.sqrt t * Real.sqrt (π / t)) * (t / 2) by ring, hsp t ht]; ring
  -- upper/lower evaluated after multiplying by `t^{3/2}`
  have hupval : ∀ t : ℝ, 0 < t →
      t ^ ((3 : ℝ) / 2) * (Real.sqrt (π / t) / (4 * t) + 1 / t + Real.sqrt (π / t) / 2)
        = Real.sqrt π / 4 + Real.sqrt t + t * Real.sqrt π / 2 := by
    intro t ht; rw [mul_add, mul_add, hA t ht, hB t ht, hC t ht]
  have hlowval : ∀ t : ℝ, 0 < t →
      t ^ ((3 : ℝ) / 2) * (Real.sqrt (π / t) / 2 + Real.sqrt (π / t) / (4 * t) - 1 - 1 / t)
        = t * Real.sqrt π / 2 + Real.sqrt π / 4 - t * Real.sqrt t - Real.sqrt t := by
    intro t ht
    rw [mul_sub, mul_sub, mul_add, hC t ht, hA t ht, hB t ht, mul_one, hrpow32 t ht]
  -- limits of the two envelopes
  have hsqrt0 : Tendsto (fun t : ℝ => Real.sqrt t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => Real.sqrt t) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hup : Tendsto (fun t : ℝ => Real.sqrt π / 4 + Real.sqrt t + t * Real.sqrt π / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt π / 4)) := by
    have := ((tendsto_const_nhds (x := Real.sqrt π / 4)).add hsqrt0).add
      ((ht0.mul_const (Real.sqrt π)).div_const 2)
    simpa using this
  have hlow : Tendsto (fun t : ℝ => t * Real.sqrt π / 2 + Real.sqrt π / 4
      - t * Real.sqrt t - Real.sqrt t) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt π / 4)) := by
    have := ((((ht0.mul_const (Real.sqrt π)).div_const 2).add
      (tendsto_const_nhds (x := Real.sqrt π / 4))).sub (ht0.mul hsqrt0)).sub hsqrt0
    simpa using this
  -- squeeze `t^{3/2} · shifted → √π/4`
  have hshift : Tendsto (fun t : ℝ => t ^ ((3 : ℝ) / 2) * sphere3ShiftedSum t)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt π / 4)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      have hp : (0 : ℝ) ≤ t ^ ((3 : ℝ) / 2) := Real.rpow_nonneg ht'.le _
      rw [← hlowval t ht']
      exact mul_le_mul_of_nonneg_left (sphere3ShiftedSum_lower ht') hp
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      have hp : (0 : ℝ) ≤ t ^ ((3 : ℝ) / 2) := Real.rpow_nonneg ht'.le _
      rw [← hupval t ht']
      exact mul_le_mul_of_nonneg_left (sphere3ShiftedSum_upper ht') hp
  -- fold in `e^{t} → 1` via the reindex
  have hexp1 : Tendsto (fun t : ℝ => Real.exp t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have : Tendsto (fun t : ℝ => Real.exp t) (𝓝 (0 : ℝ)) (𝓝 1) := by
      simpa using Real.continuous_exp.tendsto (0 : ℝ)
    exact this.mono_left nhdsWithin_le_nhds
  have hcongr : (fun t : ℝ => t ^ ((3 : ℝ) / 2) * sphere3HeatTrace t)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun t => Real.exp t * (t ^ ((3 : ℝ) / 2) * sphere3ShiftedSum t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    rw [sphere3HeatTrace_eq ht']; ring
  rw [tendsto_congr' hcongr]
  simpa using hexp1.mul hshift

/-- **`a₁ = R/6 = 1` on the unit `S³`.** The Seeley–DeWitt curvature constant `a₁` equals `R/6`, and
the unit `S³` has scalar curvature `R = 6`, so the `a₁` coefficient ratio is `R/6 = 1`. This ties the
Weyl-normalized heat-trace expansion `Θ₃(t) = (√π/4) e^{t} t^{-3/2}` — whose `e^{t}` Taylor factor
`1 + t + …` carries the `a₁` term `(√π/4)·(R/6)` — to the scalar curvature of the curved `S³`. -/
theorem sphere3_a1_eq_R_div_six : (1 : ℝ) = 6 / 6 := by norm_num

end QIQTH.Sphere3HeatTrace
