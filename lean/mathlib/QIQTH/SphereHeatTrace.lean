import Mathlib

/-!
# The heat trace on the unit 2-sphere `S²` (curved, `R = 2`)

**What this file proves.** The heat trace of `e^{tΔ}` on the unit 2-sphere (radius `1`, scalar
curvature `R = 2`, volume `4π`). On `S²` the Laplace–Beltrami operator `-Δ` has the *explicit*
spectrum `λ_l = l(l+1)` (`l = 0,1,2,…`) with multiplicity `2l+1` (the spherical harmonics). The
heat trace is therefore the concrete spectral sum
`Θ(t) := Tr e^{tΔ} = Σ_{l≥0} (2l+1) e^{-t l(l+1)}` (`sphereHeatTrace`), whose short-time expansion
is the classical `Θ(t) = 1/t + 1/3 + O(t)` as `t → 0⁺`, where **the leading `1/t` is the Weyl term
`a₀ = vol/(4πt)^{d/2} = 4π/(4πt) = 1/t`** and **the constant `1/3` is the Seeley–DeWitt `a₁ = R/6`
term** (`R = 2` ⟹ `R/6 = 1/3`).

**What is RIGOROUSLY FORMALIZED here (all axiom-free, `#print axioms ⊆ std-3):**

1. `sphereHeatTrace` — the explicit `S²` spectral sum; `sphereHeatTrace_summable`; the exact
   factorization `Θ(t) = e^{t/4} · Σ (2l+1) e^{-t(l+1/2)²}` (`sphereHeatTrace_factor`, from
   `l(l+1) = (l+1/2)² − 1/4`).
2. **The leading Weyl coefficient `a₀ = 1/t` on the CURVED sphere, two ways:**
   * `weyl_density_integral` — the continuum spectral-density integral `∫_{(0,∞)} (2x+1) e^{-t x(x+1)} dx
     = 1/t` EXACTLY (fundamental theorem of calculus);
   * `sphereHeatTrace_asymptotic` — the discrete-sum limit `t · Θ(t) → 1` as `t → 0⁺`, obtained by
     sandwiching `Θ(t)` between two explicit sum-integral comparisons
     (`sphereHeatTrace_lower_bound`/`sphereHeatTrace_upper_bound`):
     `1 + (1/t)e^{-2t} − 2√(π/t) ≤ Θ(t) ≤ 1 + 1/t + 2√(π/t)`.
3. `sphere_a1_eq_R_div_six` — the arithmetic `1/3 = R/6` with `R = 2`, tying the constant to
   `CoordinateCurvature`'s sphere `R = 2` and `DeWittDiagonal`'s `u₁ = τ/6` (`τ = 2 ⟹ 1/3`).

**What is NOT (yet) formalized — the precise remaining gap.** The SUM-level constant limit
`Θ(t) − 1/t → 1/3` is NOT proven. The two-sided sandwich above pins only the leading `1/t`: its slack
is `O(1/√t)` (`2√(π/t)`), which dominates the `O(1)` constant, so it cannot resolve `+1/3`. Capturing
the constant needs the subleading term of `S(t) = Σ (2l+1) e^{-t(l+1/2)²} ~ 1/t + 1/12` (Poisson
summation / Euler–Maclaurin), which combines with the `e^{t/4}` prefactor's `+1/4` to give
`1/4 + 1/12 = 1/3`. So this file validates `a₀` on a curved manifold and carries `a₁ = R/6 = 1/3` as
an arithmetic/DeWitt label — it does NOT yet close the sum-level `a₁` limit.

**Firewall (binding, honest).**

* This BREAKS THE HEAT-KERNEL WALL FOR ONE MORE EXPLICIT GEOMETRY — the CURVED unit sphere — for the
  LEADING `a₀` term, NOT the general curved manifold (which stays the wall). The spectrum
  `{l(l+1), mult 2l+1}` is the CARRIED classical input (the eigenvalues of `-Δ` on `S²`, exactly as
  the circle's `{(2πk)²}` is carried in `FlatTorusHeatKernel`). The "trace" is the spectral sum over
  the eigenbasis of a diagonal operator — honest here; it is NOT a general basis-independent trace
  (that needs the absent trace-class API).

* This uses NONE of the missing infrastructure: no Rellich compactness, no elliptic regularity, no
  trace-class API, no manifold-`L²`/`Δ` machinery, no curved heat-kernel EXISTENCE. It does NOT
  analytically discharge the GENERAL `a₁ = R/6` (that needs the curved heat-kernel existence = the
  wall), and — as stated above — does not even close the `a₁` constant for THIS geometry at the sum
  level.

* This is NOT the conjecture, NOT the strong holographic principle, NOT quantum gravity. No
  `axiom`, no `sorry`.
-/

namespace QIQTH.SphereHeatTrace

open scoped Real
open Filter Topology MeasureTheory

/-- The `S²` spectral heat trace `Tr e^{tΔ} = Σ_{l≥0} (2l+1) e^{-t l(l+1)}`: eigenvalue `l(l+1)`
of `-Δ` with multiplicity `2l+1` (the spherical harmonics). -/
noncomputable def sphereHeatTrace (t : ℝ) : ℝ :=
  ∑' l : ℕ, (2 * (l : ℝ) + 1) * Real.exp (-t * ((l : ℝ) * ((l : ℝ) + 1)))

/-- The inner "shifted" sum `S(t) = Σ_{l≥0} (2l+1) e^{-t(l+1/2)²}` obtained from
`l(l+1) = (l+1/2)² − 1/4`. -/
noncomputable def sphereShiftedSum (t : ℝ) : ℝ :=
  ∑' l : ℕ, (2 * (l : ℝ) + 1) * Real.exp (-t * ((l : ℝ) + 1 / 2) ^ 2)

/-- **Summability of the heat-trace summand** (for `t > 0`). The multiplicity `2l+1` grows only
linearly while `e^{-t l(l+1)} ≤ e^{-t l}` decays geometrically, so the polynomial×geometric
comparison `summable_pow_mul_exp_neg_nat_mul` dominates. No compactness/regularity input is
needed — the spectrum is explicit. -/
theorem sphereHeatTrace_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun l : ℕ => (2 * (l : ℝ) + 1) * Real.exp (-t * ((l : ℝ) * ((l : ℝ) + 1)))) := by
  -- Dominating function `(2 l + 1) e^{-t l}` is summable.
  have h1 : Summable (fun l : ℕ => (l : ℝ) ^ 1 * Real.exp (-t * (l : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 1 ht
  have h0 : Summable (fun l : ℕ => (l : ℝ) ^ 0 * Real.exp (-t * (l : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 0 ht
  have hdom : Summable (fun l : ℕ => (2 * (l : ℝ) + 1) * Real.exp (-t * (l : ℝ))) := by
    have := (h1.mul_left 2).add h0
    refine this.congr (fun l => ?_)
    simp only [pow_one, pow_zero, one_mul]
    ring
  refine hdom.of_nonneg_of_le (fun l => by positivity) (fun l => ?_)
  -- `l(l+1) ≥ l` (for `l ≥ 0`), so `e^{-t l(l+1)} ≤ e^{-t l}`.
  have hle : (l : ℝ) ≤ (l : ℝ) * ((l : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) l]
  have hexp : Real.exp (-t * ((l : ℝ) * ((l : ℝ) + 1))) ≤ Real.exp (-t * (l : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have : -t * ((l : ℝ) * ((l : ℝ) + 1)) ≤ -t * (l : ℝ) := by
      have := mul_le_mul_of_nonneg_left hle ht.le
      nlinarith [this]
    exact this
  have hmul : (0 : ℝ) ≤ 2 * (l : ℝ) + 1 := by positivity
  exact mul_le_mul_of_nonneg_left hexp hmul

/-- **The `e^{t/4}·S(t)` factorisation.** Using `l(l+1) = (l+1/2)² − 1/4`, each summand factors as
`e^{-t l(l+1)} = e^{t/4} e^{-t(l+1/2)²}`, so `Θ(t) = e^{t/4} · S(t)`. This is an unconditional
`tsum` identity (a constant pulled out per term). -/
theorem sphereHeatTrace_factor (t : ℝ) :
    sphereHeatTrace t = Real.exp (t / 4) * sphereShiftedSum t := by
  unfold sphereHeatTrace sphereShiftedSum
  rw [← tsum_mul_left]
  refine tsum_congr (fun l => ?_)
  have he : Real.exp (-t * ((l : ℝ) * ((l : ℝ) + 1)))
      = Real.exp (t / 4) * Real.exp (-t * ((l : ℝ) + 1 / 2) ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]; ring

/-- **The continuum Weyl term `a₀`.** The smooth analogue of the spectral sum — the integral of the
spectral density `(2x+1) e^{-t x(x+1)}` over `x ∈ (0,∞)` — is EXACTLY `1/t`. This is the leading
Weyl coefficient `a₀ = vol/(4πt)^{d/2} = 4π/(4πt) = 1/t` for the unit `S²` (`d = 2`, `vol = 4π`),
obtained here by the fundamental theorem of calculus: `(2x+1)e^{-t x(x+1)} = d/dx[-(1/t)e^{-t x(x+1)}]`,
antiderivative `-(1/t)` at `0` and `0` at `∞`. The discrete heat trace `sphereHeatTrace` differs from
this continuum value by the Seeley–DeWitt corrections (the `+1/3` constant and higher). -/
theorem weyl_density_integral {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi (0 : ℝ), (2 * x + 1) * Real.exp (-t * (x * (x + 1))) = 1 / t := by
  have ht0 : t ≠ 0 := ht.ne'
  set g : ℝ → ℝ := fun x => -(1 / t) * Real.exp (-t * (x * (x + 1))) with hg
  set g' : ℝ → ℝ := fun x => (2 * x + 1) * Real.exp (-t * (x * (x + 1))) with hg'
  -- Derivative: `g' = deriv g`.
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (g' x) x := by
    intro x _
    have hpoly : HasDerivAt (fun y : ℝ => y * (y + 1)) (2 * x + 1) x := by
      have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
      have h2 : HasDerivAt (fun y : ℝ => y + 1) 1 x := by simpa using h1.add_const 1
      have hm := h1.mul h2
      convert hm using 1
      ring
    have hin : HasDerivAt (fun y : ℝ => -t * (y * (y + 1))) (-t * (2 * x + 1)) x :=
      hpoly.const_mul (-t)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-t * (y * (y + 1))))
        (Real.exp (-t * (x * (x + 1))) * (-t * (2 * x + 1))) x := hin.exp
    have hfin := hexp.const_mul (-(1 / t))
    convert hfin using 1
    rw [hg']
    field_simp
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ g' x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [hg']
    have hc : (0 : ℝ) ≤ 2 * x + 1 := by positivity
    positivity
  have htend : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have hquad : Filter.Tendsto (fun x : ℝ => x * (x + 1)) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_mono' Filter.atTop _ Filter.tendsto_id
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      simp only [id_eq]
      nlinarith [mul_nonneg hx hx]
    have hbot : Filter.Tendsto (fun x : ℝ => -t * (x * (x + 1))) Filter.atTop Filter.atBot :=
      hquad.const_mul_atTop_of_neg (neg_lt_zero.mpr ht)
    have hE : Filter.Tendsto (fun x : ℝ => Real.exp (-t * (x * (x + 1)))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hbot
    have hfin := hE.const_mul (-(1 / t))
    rw [hg]
    simpa using hfin
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend
  simp only [hg', hg] at hmain ⊢
  rw [hmain]
  simp

/-- **Generic Weyl-type improper integral + integrability** (the engine behind the leading term).
For a "completed square" quadratic `q(x) = x² + s x` with derivative `2x + s` nonnegative on
`(c, ∞)`, the fundamental theorem of calculus gives
`∫_{(c,∞)} (2x+s) e^{-t q(x)} dx = (1/t) e^{-t q(c)}`, and the integrand is integrable there. -/
private lemma weyl_pack {t : ℝ} (ht : 0 < t) (s c : ℝ)
    (hpos : ∀ x ∈ Set.Ioi c, 0 ≤ 2 * x + s) :
    (∫ x in Set.Ioi c, (2 * x + s) * Real.exp (-t * (x ^ 2 + s * x))
        = (1 / t) * Real.exp (-t * (c ^ 2 + s * c)))
      ∧ IntegrableOn (fun x => (2 * x + s) * Real.exp (-t * (x ^ 2 + s * x))) (Set.Ioi c) := by
  have ht0 : t ≠ 0 := ht.ne'
  set G : ℝ → ℝ := fun x => -(1 / t) * Real.exp (-t * (x ^ 2 + s * x)) with hG
  set G' : ℝ → ℝ := fun x => (2 * x + s) * Real.exp (-t * (x ^ 2 + s * x)) with hG'
  have hderiv : ∀ x ∈ Set.Ici c, HasDerivAt G (G' x) x := by
    intro x _
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hlin : HasDerivAt (fun x : ℝ => s * x) s x := by
      simpa using (hasDerivAt_id x).const_mul s
    have hu : HasDerivAt (fun x : ℝ => x ^ 2 + s * x) (2 * x + s) x := hpow.add hlin
    have hin : HasDerivAt (fun x : ℝ => -t * (x ^ 2 + s * x)) (-t * (2 * x + s)) x :=
      hu.const_mul (-t)
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-t * (x ^ 2 + s * x)))
        (Real.exp (-t * (x ^ 2 + s * x)) * (-t * (2 * x + s))) x := hin.exp
    have hfin := hexp.const_mul (-(1 / t))
    convert hfin using 1
    rw [hG']; field_simp
  have hgpos : ∀ x ∈ Set.Ioi c, 0 ≤ G' x := by
    intro x hx
    rw [hG']
    have := hpos x hx
    positivity
  have htend : Filter.Tendsto G Filter.atTop (nhds 0) := by
    have hquad : Filter.Tendsto (fun x : ℝ => x ^ 2 + s * x) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_mono' Filter.atTop _ Filter.tendsto_id
      filter_upwards [Filter.eventually_ge_atTop (|s| + 1)] with x hx
      simp only [id_eq]
      nlinarith [neg_abs_le s, abs_nonneg s, hx]
    have hbot : Filter.Tendsto (fun x : ℝ => -t * (x ^ 2 + s * x)) Filter.atTop Filter.atBot :=
      hquad.const_mul_atTop_of_neg (neg_lt_zero.mpr ht)
    have hE : Filter.Tendsto (fun x : ℝ => Real.exp (-t * (x ^ 2 + s * x)))
        Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp hbot
    have hfin := hE.const_mul (-(1 / t))
    rw [hG]; simpa using hfin
  refine ⟨?_, ?_⟩
  · have hval := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hgpos htend
    rw [hval]
    simp only [hG]
    ring
  · exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hgpos htend

/-- `G t` is antitone on `[0,∞)` (since `x(x+1)` is increasing there). -/
private lemma G_antitoneOn {t : ℝ} (ht : 0 < t) :
    AntitoneOn (fun x => Real.exp (-t * (x * (x + 1)))) (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  apply Real.exp_le_exp.mpr
  have hx0 : (0 : ℝ) ≤ x := hx
  have : x * (x + 1) ≤ y * (y + 1) := by nlinarith [hx0, hxy]
  nlinarith [this, ht]

/-- A gaussian-domination bound: `∫_{(c,∞)} e^{-t x(x+1)} dx ≤ √(π/t)` for `c ≥ 0`, and likewise
`∫_{(1,∞)} e^{-t x(x-1)} dx ≤ √(π/t)`. Packaged as: the integral of `e^{-t·q}` where `q(x) ≥ (x-b)²`
on `(c,∞)` is `≤ √(π/t)`, plus its integrability. -/
private lemma exp_quad_le_sqrt {t : ℝ} (ht : 0 < t) (c b : ℝ) (q : ℝ → ℝ)
    (hqc : Continuous q) (hqb : ∀ x ∈ Set.Ioi c, (x - b) ^ 2 ≤ q x) :
    (∫ x in Set.Ioi c, Real.exp (-t * q x) ≤ Real.sqrt (π / t))
      ∧ IntegrableOn (fun x => Real.exp (-t * q x)) (Set.Ioi c) := by
  have hgauss : Integrable (fun x : ℝ => Real.exp (-t * (x - b) ^ 2)) :=
    (integrable_exp_neg_mul_sq ht).comp_sub_right b
  have hFmeas : Measurable (fun x => Real.exp (-t * q x)) := by
    fun_prop
  have hdom : ∀ x ∈ Set.Ioi c, Real.exp (-t * q x) ≤ Real.exp (-t * (x - b) ^ 2) := by
    intro x hx
    apply Real.exp_le_exp.mpr
    have := hqb x hx
    nlinarith [this, ht.le]
  have hFint : IntegrableOn (fun x => Real.exp (-t * q x)) (Set.Ioi c) := by
    refine Integrable.mono' hgauss.integrableOn hFmeas.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact hdom x hx
  refine ⟨?_, hFint⟩
  calc ∫ x in Set.Ioi c, Real.exp (-t * q x)
      ≤ ∫ x in Set.Ioi c, Real.exp (-t * (x - b) ^ 2) := by
        apply setIntegral_mono_on hFint hgauss.integrableOn measurableSet_Ioi
        exact hdom
    _ ≤ ∫ x, Real.exp (-t * (x - b) ^ 2) :=
        setIntegral_le_integral hgauss (ae_of_all _ (fun x => Real.exp_nonneg _))
    _ = ∫ x, Real.exp (-t * x ^ 2) := integral_sub_right_eq_self (fun x => Real.exp (-t * x ^ 2)) b
    _ = Real.sqrt (π / t) := integral_gaussian t

/-- **Lower bound.** `sphereHeatTrace t ≥ 1 + (1/t) e^{-2t} − 2√(π/t)`. The `l = 0` term gives `1`;
the tail `∑_{l≥1}` is bounded below by `∫_{(1,∞)} (2x−1) e^{−t x(x+1)} dx` (sum-integral comparison,
`e^{−t x(x+1)}` antitone × `2x+1` monotone), which equals `(1/t)e^{-2t} − 2∫_{(1,∞)} e^{−t x(x+1)}`
with the gaussian correction `≤ √(π/t)`. -/
theorem sphereHeatTrace_lower_bound {t : ℝ} (ht : 0 < t) :
    1 + (1 / t) * Real.exp (-2 * t) - 2 * Real.sqrt (π / t) ≤ sphereHeatTrace t := by
  set Gf : ℝ → ℝ := fun x => Real.exp (-t * (x * (x + 1))) with hGf
  set lin : ℝ → ℝ := fun x => 2 * x + 1 with hlin
  set Flo : ℝ → ℝ := fun x => (2 * x - 1) * Real.exp (-t * (x * (x + 1))) with hFlo
  set term : ℕ → ℝ := fun i => (2 * (i : ℝ) + 1) * Real.exp (-t * ((i : ℝ) * ((i : ℝ) + 1)))
    with hterm
  have hmono : Monotone lin := fun p q h => by simp only [hlin]; linarith
  obtain ⟨hI1val, hI1int⟩ := weyl_pack ht 1 1 (fun x hx => by have hx' : (1 : ℝ) < x := hx; nlinarith)
  obtain ⟨hKbnd, hKint⟩ := exp_quad_le_sqrt ht 1 0 (fun x => x * (x + 1)) (by fun_prop)
      (fun x hx => by have hx' : (1 : ℝ) < x := hx; nlinarith)
  have hI1int' : IntegrableOn (fun x => (2 * x + 1) * Real.exp (-t * (x * (x + 1)))) (Set.Ioi 1) := by
    refine hI1int.congr_fun (fun x _ => ?_) measurableSet_Ioi
    congr 2; ring
  have hI1val' : ∫ x in Set.Ioi 1, (2 * x + 1) * Real.exp (-t * (x * (x + 1)))
      = (1 / t) * Real.exp (-2 * t) := by
    have hc : ∫ x in Set.Ioi 1, (2 * x + 1) * Real.exp (-t * (x * (x + 1)))
        = ∫ x in Set.Ioi 1, (2 * x + 1) * Real.exp (-t * (x ^ 2 + 1 * x)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x _ => by congr 2; ring)
    rw [hc, hI1val]; congr 2 <;> ring
  have hFloint : IntegrableOn Flo (Set.Ioi 1) := by
    have h := hI1int'.sub (hKint.const_mul 2)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [hFlo, Pi.sub_apply]; ring
  have hFloval : ∫ x in Set.Ioi 1, Flo x
      = (1 / t) * Real.exp (-2 * t) - 2 * ∫ x in Set.Ioi 1, Real.exp (-t * (x * (x + 1))) := by
    have hsplit : ∀ x, Flo x
        = (2 * x + 1) * Real.exp (-t * (x * (x + 1))) - 2 * Real.exp (-t * (x * (x + 1))) := by
      intro x; simp only [hFlo]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hsplit x),
      integral_sub hI1int' (hKint.const_mul 2), hI1val', integral_const_mul]
  -- sum-integral comparison, `a = 1`
  have hcmp : ∀ N : ℕ, 1 ≤ N →
      (∫ x in (1 : ℝ)..(N : ℝ), Flo x) ≤ ∑ i ∈ Finset.Ico 1 N, term i := by
    intro N hN
    have hf : AntitoneOn Gf (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) :=
      (G_antitoneOn ht).mono (fun x hx => Set.mem_Ici.mpr (le_trans (Nat.cast_nonneg 1) hx.1))
    have key := integral_le_sum_mul_Ico_of_antitone_monotone (a := 1) (b := N) (f := Gf) (g := lin)
      hN hf (hmono.monotoneOn _) (Real.exp_nonneg _) (by simp only [hlin]; norm_num)
    rw [Nat.cast_one] at key
    calc (∫ x in (1 : ℝ)..(N : ℝ), Flo x)
        = ∫ x in (1 : ℝ)..(N : ℝ), Gf x * lin (x - 1) := by
          refine intervalIntegral.integral_congr (fun x _ => ?_)
          simp only [hFlo, hGf, hlin]; ring
      _ ≤ ∑ i ∈ Finset.Ico 1 N, Gf (i : ℝ) * lin (i : ℝ) := key
      _ = ∑ i ∈ Finset.Ico 1 N, term i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hGf, hlin, hterm]; ring
  -- pass to the limit
  have hHS : HasSum term (sphereHeatTrace t) := (sphereHeatTrace_summable ht).hasSum
  have hpartial : Tendsto (fun N => ∑ i ∈ Finset.range N, term i) atTop (𝓝 (sphereHeatTrace t)) :=
    hHS.tendsto_sum_nat
  have hpartial' : Tendsto (fun N => ∑ i ∈ Finset.Ico 1 N, term i) atTop
      (𝓝 (sphereHeatTrace t - term 0)) := by
    have heq : (fun N => (∑ i ∈ Finset.range N, term i) - term 0)
        =ᶠ[atTop] (fun N => ∑ i ∈ Finset.Ico 1 N, term i) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have h01 : ∑ i ∈ Finset.Ico 0 1, term i = term 0 := by
        rw [← Finset.range_eq_Ico, Finset.sum_range_one]
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive term (Nat.zero_le 1) hN, h01]; ring
    exact (hpartial.sub_const (term 0)).congr' heq
  have hint_tendsto : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), Flo x) atTop
      (𝓝 (∫ x in Set.Ioi 1, Flo x)) :=
    intervalIntegral_tendsto_integral_Ioi 1 hFloint tendsto_natCast_atTop_atTop
  have hle : ∫ x in Set.Ioi 1, Flo x ≤ sphereHeatTrace t - term 0 := by
    refine le_of_tendsto_of_tendsto hint_tendsto hpartial' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN using hcmp N hN
  have hterm0 : term 0 = 1 := by simp only [hterm]; norm_num
  have hfinal : sphereHeatTrace t ≥ term 0 + ∫ x in Set.Ioi 1, Flo x := by linarith [hle]
  rw [hterm0, hFloval] at hfinal
  linarith [hfinal, hKbnd]

/-- **Upper bound.** `sphereHeatTrace t ≤ 1 + 1/t + 2√(π/t)`. The `l = 0` term gives `1`; the tail
`∑_{l≥1}` is bounded above by `∫_{(1,∞)} (2x+1) e^{−t x(x−1)} dx` (sum-integral comparison,
`2x+1` monotone × `e^{−t x(x+1)}` antitone, evaluated at the shift `x-1`), which equals
`1/t + 2∫_{(1,∞)} e^{−t x(x−1)}` with the gaussian correction `≤ √(π/t)`. -/
theorem sphereHeatTrace_upper_bound {t : ℝ} (ht : 0 < t) :
    sphereHeatTrace t ≤ 1 + 1 / t + 2 * Real.sqrt (π / t) := by
  set Gf : ℝ → ℝ := fun x => Real.exp (-t * (x * (x + 1))) with hGf
  set lin : ℝ → ℝ := fun x => 2 * x + 1 with hlin
  set Fup : ℝ → ℝ := fun x => (2 * x + 1) * Real.exp (-t * (x * (x - 1))) with hFup
  set term : ℕ → ℝ := fun i => (2 * (i : ℝ) + 1) * Real.exp (-t * ((i : ℝ) * ((i : ℝ) + 1)))
    with hterm
  have hmono : Monotone lin := fun p q h => by simp only [hlin]; linarith
  obtain ⟨hI2val, hI2int⟩ :=
    weyl_pack ht (-1) 1 (fun x hx => by have hx' : (1 : ℝ) < x := hx; nlinarith)
  obtain ⟨hK1bnd, hK1int⟩ := exp_quad_le_sqrt ht 1 1 (fun x => x * (x - 1)) (by fun_prop)
      (fun x hx => by have hx' : (1 : ℝ) < x := hx; nlinarith)
  have hI2int' : IntegrableOn (fun x => (2 * x - 1) * Real.exp (-t * (x * (x - 1)))) (Set.Ioi 1) := by
    refine hI2int.congr_fun (fun x _ => ?_) measurableSet_Ioi
    congr 2 <;> ring
  have hI2val' : ∫ x in Set.Ioi 1, (2 * x - 1) * Real.exp (-t * (x * (x - 1))) = 1 / t := by
    have hc : ∫ x in Set.Ioi 1, (2 * x - 1) * Real.exp (-t * (x * (x - 1)))
        = ∫ x in Set.Ioi 1, (2 * x + -1) * Real.exp (-t * (x ^ 2 + -1 * x)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x _ => by congr 2 <;> ring)
    rw [hc, hI2val]
    have he : -t * ((1 : ℝ) ^ 2 + -1 * 1) = 0 := by ring
    rw [he, Real.exp_zero, mul_one]
  have hFupint : IntegrableOn Fup (Set.Ioi 1) := by
    have h := hI2int'.add (hK1int.const_mul 2)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [hFup, Pi.add_apply]; ring
  have hFupval : ∫ x in Set.Ioi 1, Fup x
      = 1 / t + 2 * ∫ x in Set.Ioi 1, Real.exp (-t * (x * (x - 1))) := by
    have hsplit : ∀ x, Fup x
        = (2 * x - 1) * Real.exp (-t * (x * (x - 1))) + 2 * Real.exp (-t * (x * (x - 1))) := by
      intro x; simp only [hFup]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hsplit x),
      integral_add hI2int' (hK1int.const_mul 2), hI2val', integral_const_mul]
  have hcmp : ∀ N : ℕ, 1 ≤ N →
      (∑ i ∈ Finset.Ico 1 N, term i) ≤ ∫ x in (1 : ℝ)..(N : ℝ), Fup x := by
    intro N hN
    have hg : AntitoneOn Gf (Set.Icc (((1 : ℕ) : ℝ) - 1) (((N : ℕ) : ℝ) - 1)) :=
      (G_antitoneOn ht).mono (fun x hx => Set.mem_Ici.mpr (by
        have := hx.1; simp only [Nat.cast_one] at this; linarith))
    have key := sum_mul_Ico_le_integral_of_monotone_antitone (a := 1) (b := N) (f := lin) (g := Gf)
      hN (hmono.monotoneOn _) hg (by positivity) (Real.exp_nonneg _)
    rw [Nat.cast_one] at key
    calc (∑ i ∈ Finset.Ico 1 N, term i)
        = ∑ i ∈ Finset.Ico 1 N, lin (i : ℝ) * Gf (i : ℝ) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hGf, hlin, hterm]
      _ ≤ ∫ x in (1 : ℝ)..(N : ℝ), lin x * Gf (x - 1) := key
      _ = ∫ x in (1 : ℝ)..(N : ℝ), Fup x := by
          refine intervalIntegral.integral_congr (fun x _ => ?_)
          simp only [hFup, hGf, hlin]; ring
  have hHS : HasSum term (sphereHeatTrace t) := (sphereHeatTrace_summable ht).hasSum
  have hpartial : Tendsto (fun N => ∑ i ∈ Finset.range N, term i) atTop (𝓝 (sphereHeatTrace t)) :=
    hHS.tendsto_sum_nat
  have hpartial' : Tendsto (fun N => ∑ i ∈ Finset.Ico 1 N, term i) atTop
      (𝓝 (sphereHeatTrace t - term 0)) := by
    have heq : (fun N => (∑ i ∈ Finset.range N, term i) - term 0)
        =ᶠ[atTop] (fun N => ∑ i ∈ Finset.Ico 1 N, term i) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have h01 : ∑ i ∈ Finset.Ico 0 1, term i = term 0 := by
        rw [← Finset.range_eq_Ico, Finset.sum_range_one]
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive term (Nat.zero_le 1) hN, h01]; ring
    exact (hpartial.sub_const (term 0)).congr' heq
  have hint_tendsto : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), Fup x) atTop
      (𝓝 (∫ x in Set.Ioi 1, Fup x)) :=
    intervalIntegral_tendsto_integral_Ioi 1 hFupint tendsto_natCast_atTop_atTop
  have hle : sphereHeatTrace t - term 0 ≤ ∫ x in Set.Ioi 1, Fup x := by
    refine le_of_tendsto_of_tendsto hpartial' hint_tendsto ?_
    filter_upwards [eventually_ge_atTop 1] with N hN using hcmp N hN
  have hterm0 : term 0 = 1 := by simp only [hterm]; norm_num
  have hfinal : sphereHeatTrace t ≤ term 0 + ∫ x in Set.Ioi 1, Fup x := by linarith [hle]
  rw [hterm0, hFupval] at hfinal
  linarith [hfinal, hK1bnd]

/-- Auxiliary: `t · √(π/t) = √(π t) → 0` as `t → 0⁺`. -/
private lemma tsqrt_tendsto_zero :
    Tendsto (fun t : ℝ => t * Real.sqrt (π / t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hid : (fun t : ℝ => t * Real.sqrt (π / t)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => Real.sqrt (π * t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hpt : (0 : ℝ) ≤ π / t := by positivity
    have hsq : (t * Real.sqrt (π / t)) ^ 2 = π * t := by
      rw [mul_pow, Real.sq_sqrt hpt]; field_simp
    rw [← hsq, Real.sqrt_sq (by positivity)]
  rw [tendsto_congr' hid]
  have hπt : Tendsto (fun t : ℝ => π * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => π * t) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hπt

/-- **★ The leading Weyl (`a₀`) short-time asymptotic on the curved sphere.**
`t · sphereHeatTrace t → 1` as `t → 0⁺`, i.e. `Θ(t) = 1/t + o(1/t)` — the leading Weyl term `a₀`.
Proved by squeezing between the two-sided sandwich `1 + (1/t)e^{-2t} − 2√(π/t) ≤ Θ ≤ 1 + 1/t + 2√(π/t)`
(`sphereHeatTrace_lower_bound`/`sphereHeatTrace_upper_bound`), whose `O(1/√t)` slack pins the leading
`vol/(4πt)^{d/2} = 1/t` — obtained purely from the explicit spectrum `{l(l+1), mult 2l+1}` of `−Δ` on
`S²`, with no heat-kernel existence and no elliptic machinery. (The subleading constant `a₁ = R/6 = 1/3`
is NOT resolved by this sandwich — see the file header for the precise remaining gap.) -/
theorem sphereHeatTrace_asymptotic :
    Filter.Tendsto (fun t : ℝ => t * sphereHeatTrace t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hsqrt := tsqrt_tendsto_zero
  have h1 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlo : Tendsto (fun t : ℝ => t + Real.exp (-2 * t) - 2 * (t * Real.sqrt (π / t)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h2 : Tendsto (fun t : ℝ => Real.exp (-2 * t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hcont : Continuous (fun t : ℝ => Real.exp (-2 * t)) := by fun_prop
      have hc : Tendsto (fun t : ℝ => Real.exp (-2 * t)) (𝓝 (0 : ℝ)) (𝓝 1) := by
        simpa using hcont.tendsto (0 : ℝ)
      exact hc.mono_left nhdsWithin_le_nhds
    have := (h1.add h2).sub (hsqrt.const_mul 2)
    simpa using this
  have hhi : Tendsto (fun t : ℝ => t + 1 + 2 * (t * Real.sqrt (π / t))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have := (h1.add_const 1).add (hsqrt.const_mul 2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hmul := mul_le_mul_of_nonneg_left (sphereHeatTrace_lower_bound ht0) ht0.le
    calc t + Real.exp (-2 * t) - 2 * (t * Real.sqrt (π / t))
        = t * (1 + (1 / t) * Real.exp (-2 * t) - 2 * Real.sqrt (π / t)) := by
          field_simp [ht0.ne']
      _ ≤ t * sphereHeatTrace t := hmul
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hmul := mul_le_mul_of_nonneg_left (sphereHeatTrace_upper_bound ht0) ht0.le
    calc t * sphereHeatTrace t
        ≤ t * (1 + 1 / t + 2 * Real.sqrt (π / t)) := hmul
      _ = t + 1 + 2 * (t * Real.sqrt (π / t)) := by field_simp [ht0.ne']

/-- **`a₁ = R/6` on the sphere.** The Seeley–DeWitt constant term `1/3` equals `R/6` with `R = 2`
(the scalar curvature of the unit `S²`). Ties `sphereHeatTrace_asymptotic`'s constant to
`CoordinateCurvature`'s sphere curvature and `DeWittDiagonal`'s `u₁ = τ/6`. -/
theorem sphere_a1_eq_R_div_six : (1 : ℝ) / 3 = 2 / 6 := by norm_num

end QIQTH.SphereHeatTrace
