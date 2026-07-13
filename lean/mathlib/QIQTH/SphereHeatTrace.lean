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
4. **The EXACT first-order Euler–Maclaurin identity** `sphereHeatTrace_em1`:
   `Θ(t) = 1/t + 1/2 + ∫_{(0,∞)} (Int.fract x − 1/2)·φ'(x) dx` with `φ'(x) = (2 − t(2x+1)²)e^{-t x(x+1)}`.
   Here `1/t` is the Weyl term `a₀`, `+1/2` is the `φ(0)/2` boundary term, and the remainder integral
   `∫ P₁ φ'` (`P₁ = Int.fract − 1/2` the first periodic Bernoulli function) carries the curvature
   constant. Built purely from Mathlib's Abel summation `sum_mul_eq_sub_integral_mul'` (unit
   coefficients), splitting the floor weight `⌊x⌋+1 = (x+1) − {x}` and integrating `∫ φ'(x+1)` by
   parts — using NO Euler–Maclaurin formula and NO Bernoulli substrate (Mathlib has neither the EM
   remainder formula nor a periodic-Bernoulli-on-ℝ integration API). Supporting facts:
   `emFinite` (the finite EM identity `∑_{k≤m} φ(k) = 1 + ∫_0^m φ + ∫_0^m φ'{x}`),
   `integral_emPhi'_eq` (`∫_{(0,∞)} φ' = −1`), `integrableOn_emPhi'`/`integrableOn_emPhi'_fract`.

**What is NOT (yet) formalized — the precise remaining gap.** The SUM-level constant limit
`Θ(t) − 1/t → 1/3` is NOT proven. Two facts are now in hand — the `O(1/√t)` sandwich (item 2, which
pins only `a₀`) and the EXACT EM-1 identity `Θ(t) − 1/t = 1/2 + ∫ P₁ φ'` (item 4). What is missing is
the *limit of the remainder*: `∫_{(0,∞)} P₁(x) φ'(x) dx → −1/6` as `t → 0⁺` (equivalently
`∫ φ'·{x} → −2/3`). That limit is NOT the naive `‖P₁‖·∫|φ'|` bound (which is `O(1)`, since
`∫|φ'| = O(1)`): it requires the *second/third*-order Euler–Maclaurin estimate — a further integration
by parts against the periodic `P₂(x) = {x}²−{x}+1/6` (giving the boundary term `−φ'(0)/12 → −1/6`) and
the mean-zero cancellation `∫₀¹ P₂ = 0` (so the `P₂`-remainder is genuinely third-order, `∼ ∫ P₃ φ'''`
with `∫|φ'''| = O(√t) → 0`). Mathlib has the periodic Bernoulli *polynomials* (`ZetaValues.bernoulliFun`,
`periodizedBernoulli` on `AddCircle`) but NO Euler–Maclaurin remainder formula and no
periodic-Bernoulli-on-ℝ integration-by-parts API, so this `P₂`/`P₃` step is the precise wall. Thus this
file closes `a₀` and the EM-1 identity on the curved sphere, and carries `a₁ = R/6 = 1/3` as an
arithmetic/DeWitt label — it does NOT close the sum-level `a₁` limit `Θ(t) − 1/t → 1/3`.

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

/-! ### The exact first-order Euler–Maclaurin identity for the heat trace

The following block establishes the **exact** first-order Euler–Maclaurin (Abel-summation)
identity for the `S²` heat trace,
`Θ(t) = 1/t + 1/2 + ∫_{(0,∞)} (⟨x⟩ − 1/2)·φ'(x) dx`,
where `φ(x) = (2x+1)e^{−t x(x+1)}` is the spectral density (`emPhi`), `φ'` its derivative
(`emPhi'`), and `⟨x⟩ − 1/2 = Int.fract x − 1/2 = P₁(x)` the first periodic Bernoulli function.
This is the honest EM-1 identity that isolates the `+1/2` boundary term (from `φ(0)/2`) and the
remainder integral `∫ P₁ φ'` whose small-`t` limit is `−1/6` (giving the `a₁ = R/6 = 1/3` constant).
Proving that remainder limit needs a *second/third*-order Euler–Maclaurin estimate — the periodic
`P₂`, `P₃` machinery — which Mathlib lacks; hence the sum-level `Θ(t) − 1/t → 1/3` is NOT closed
here. What lands is the EM-1 identity itself, built from Mathlib's `sum_mul_eq_sub_integral_mul'`
(Abel summation) — no Euler–Maclaurin formula and no Bernoulli substrate required. -/

/-- The `S²` spectral density `φ(x) = (2x+1) e^{-t x(x+1)}` (the continuous interpolation of the
heat-trace summand; `emPhi t l = (2l+1) e^{-t l(l+1)}`). -/
noncomputable def emPhi (t x : ℝ) : ℝ := (2 * x + 1) * Real.exp (-t * (x * (x + 1)))

/-- The derivative of the spectral density: `φ'(x) = (2 − t(2x+1)²) e^{-t x(x+1)}`. -/
noncomputable def emPhi' (t x : ℝ) : ℝ := (2 - t * (2 * x + 1) ^ 2) * Real.exp (-t * (x * (x + 1)))

variable {t : ℝ}

/-- `HasDerivAt emPhi emPhi'`: the density is differentiable with the stated derivative. -/
theorem hasDerivAt_emPhi (x : ℝ) : HasDerivAt (emPhi t) (emPhi' t x) x := by
  have hpoly : HasDerivAt (fun y : ℝ => y * (y + 1)) (2 * x + 1) x := by
    have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun y : ℝ => y + 1) 1 x := by simpa using h1.add_const 1
    have hm := h1.mul h2; convert hm using 1; ring
  have hin : HasDerivAt (fun y : ℝ => -t * (y * (y + 1))) (-t * (2 * x + 1)) x := hpoly.const_mul (-t)
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-t * (y * (y + 1))))
      (Real.exp (-t * (x * (x + 1))) * (-t * (2 * x + 1))) x := hin.exp
  have hlin : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const 1
  have := hlin.mul hexp
  unfold emPhi emPhi'; convert this using 1; ring

theorem deriv_emPhi : deriv (emPhi t) = emPhi' t := funext fun x => (hasDerivAt_emPhi x).deriv
@[fun_prop] theorem continuous_emPhi : Continuous (emPhi t) := by unfold emPhi; fun_prop
@[fun_prop] theorem continuous_emPhi' : Continuous (emPhi' t) := by unfold emPhi'; fun_prop

/-- Integrability of `φ'` on `(0,∞)` (dominated by a poly×gaussian). -/
theorem integrableOn_emPhi' (ht : 0 < t) : IntegrableOn (emPhi' t) (Set.Ioi (0 : ℝ)) := by
  have hE : IntegrableOn (fun x : ℝ => Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    (integrable_exp_neg_mul_sq ht).integrableOn
  have h1 : IntegrableOn (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    (integrable_rpow_mul_exp_neg_mul_sq ht (by norm_num : (-1 : ℝ) < 1)).integrableOn
  have h2 : IntegrableOn (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-t * x ^ 2)) (Set.Ioi (0 : ℝ)) :=
    (integrable_rpow_mul_exp_neg_mul_sq ht (by norm_num : (-1 : ℝ) < 2)).integrableOn
  set G : ℝ → ℝ := fun x => (2 + t) * Real.exp (-t * x ^ 2) + 4 * t * (x ^ (2 : ℝ) * Real.exp (-t * x ^ 2))
      + 4 * t * (x ^ (1 : ℝ) * Real.exp (-t * x ^ 2)) with hG
  have hGint : IntegrableOn G (Set.Ioi (0 : ℝ)) :=
    ((hE.const_mul (2 + t)).add (h2.const_mul (4 * t))).add (h1.const_mul (4 * t))
  refine Integrable.mono' hGint continuous_emPhi'.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs]
  have hrp1 : x ^ (1 : ℝ) = x := Real.rpow_one x
  have hrp2 : x ^ (2 : ℝ) = x ^ 2 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hG]; simp only [hrp1, hrp2]
  have hEle : Real.exp (-t * (x * (x + 1))) ≤ Real.exp (-t * x ^ 2) := by
    apply Real.exp_le_exp.mpr; nlinarith [ht.le, hx0.le]
  have hEpos : 0 < Real.exp (-t * (x * (x + 1))) := Real.exp_pos _
  have hcoef : |2 - t * (2 * x + 1) ^ 2| ≤ 2 + t * (2 * x + 1) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (2 * x + 1), ht.le]
  calc |emPhi' t x| = |2 - t * (2 * x + 1) ^ 2| * Real.exp (-t * (x * (x + 1))) := by
        unfold emPhi'; rw [abs_mul, abs_of_pos hEpos]
    _ ≤ (2 + t * (2 * x + 1) ^ 2) * Real.exp (-t * x ^ 2) := mul_le_mul hcoef hEle hEpos.le (by positivity)
    _ = (2 + t) * Real.exp (-t * x ^ 2) + 4 * t * (x ^ 2 * Real.exp (-t * x ^ 2))
          + 4 * t * (x * Real.exp (-t * x ^ 2)) := by ring

/-- Integrability of the EM-1 remainder integrand `φ'·{x}` on `(0,∞)` (`|{x}| ≤ 1`). -/
theorem integrableOn_emPhi'_fract (ht : 0 < t) :
    IntegrableOn (fun x => emPhi' t x * Int.fract x) (Set.Ioi (0 : ℝ)) := by
  have hI := integrableOn_emPhi' ht
  have hmeas : AEStronglyMeasurable (fun x => emPhi' t x * Int.fract x)
      (volume.restrict (Set.Ioi 0)) :=
    continuous_emPhi'.aestronglyMeasurable.mul (measurable_fract).aestronglyMeasurable
  refine Integrable.mono' hI.norm hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _
  rw [norm_mul, Real.norm_eq_abs]
  have hf : |Int.fract x| ≤ 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg x)]; exact (Int.fract_lt_one x).le
  calc ‖emPhi' t x‖ * ‖Int.fract x‖ ≤ ‖emPhi' t x‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rwa [Real.norm_eq_abs]
    _ = ‖emPhi' t x‖ := by ring

/-- `φ(x) → 0` as `x → ∞` (needed for the FTC boundary term). -/
theorem emPhi_tendsto_zero (ht : 0 < t) : Tendsto (emPhi t) atTop (𝓝 0) := by
  have hlin : Tendsto (fun x : ℝ => -t * x) atTop atBot := by
    simpa using (tendsto_id (α := ℝ)).const_mul_atTop_of_neg (neg_lt_zero.mpr ht)
  have he : Tendsto (fun x : ℝ => Real.exp (-t * x)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hlin
  have hx : Tendsto (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-t * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 t ht
  have hub : Tendsto (fun x : ℝ => (2 * x + 1) * Real.exp (-t * x)) atTop (𝓝 0) := by
    have h := (hx.const_mul 2).add he
    simp only [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx0
    rw [Real.rpow_one]; ring
  have h0 : ∀ᶠ x : ℝ in atTop, 0 ≤ emPhi t x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx0; unfold emPhi; positivity
  have hle : ∀ᶠ x : ℝ in atTop, emPhi t x ≤ (2 * x + 1) * Real.exp (-t * x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx0
    unfold emPhi; apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hx0 hx0, mul_nonneg ht.le (mul_nonneg hx0 hx0)]
  exact squeeze_zero' h0 hle hub

/-- `∫_{(0,∞)} φ'(x) dx = φ(∞) − φ(0) = −1` (fundamental theorem of calculus). -/
theorem integral_emPhi'_eq (ht : 0 < t) : ∫ x in Set.Ioi (0 : ℝ), emPhi' t x = -1 := by
  have hcont : ContinuousWithinAt (emPhi t) (Set.Ici 0) 0 := continuous_emPhi.continuousWithinAt
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun x _ => hasDerivAt_emPhi x)
    (integrableOn_emPhi' ht) (emPhi_tendsto_zero ht)
  rw [this]; unfold emPhi; norm_num

/-- `∫_{(0,∞)} φ(x) dx = 1/t`, restated for `emPhi` (from `weyl_density_integral`). -/
private theorem emWeyl (ht : 0 < t) : ∫ x in Set.Ioi (0 : ℝ), emPhi t x = 1 / t := by
  unfold emPhi; exact weyl_density_integral ht

/-- Integrability of `φ` on `(0,∞)` (from `weyl_pack`). -/
private theorem emIntegrable (ht : 0 < t) : IntegrableOn (emPhi t) (Set.Ioi (0 : ℝ)) := by
  have h := (weyl_pack ht 1 0 (fun x hx => by have hx' : (0 : ℝ) < x := hx; nlinarith)).2
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  unfold emPhi; congr 2; ring

/-- **Finite Euler–Maclaurin (Abel) identity.** For every `m`,
`∑_{k=0}^{m} φ(k) = 1 + ∫_0^m φ + ∫_0^m φ'(x)·{x} dx`. Built from Mathlib's Abel summation
`sum_mul_eq_sub_integral_mul'` (with unit coefficients `c ≡ 1`): the raw floor weight `⌊x⌋+1` is
split as `(x+1) − {x}`, and `∫_0^m φ'(x)(x+1)` is integrated by parts (FTC on `φ·(x+1)`). -/
theorem emFinite (ht : 0 < t) (m : ℕ) :
    ∑ k ∈ Finset.Icc 0 m, emPhi t k
      = 1 + (∫ x in (0 : ℝ)..m, emPhi t x) + (∫ x in (0 : ℝ)..m, emPhi' t x * Int.fract x) := by
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) m, DifferentiableAt ℝ (emPhi t) x :=
    fun x _ => (hasDerivAt_emPhi x).differentiableAt
  have hintderiv : IntegrableOn (deriv (emPhi t)) (Set.Icc (0 : ℝ) m) := by
    rw [deriv_emPhi]; exact continuous_emPhi'.integrableOn_Icc
  have key := sum_mul_eq_sub_integral_mul' (c := fun _ => (1 : ℝ)) (f := emPhi t) m hdiff hintderiv
  simp only [mul_one] at key
  rw [key]
  have hcard : (∑ _k ∈ Finset.Icc 0 m, (1 : ℝ)) = (m : ℝ) + 1 := by
    rw [Finset.sum_const, Nat.card_Icc]; push_cast; ring
  rw [hcard, deriv_emPhi]
  have hfloor : ∫ x in Set.Ioc (0 : ℝ) m, emPhi' t x * ∑ _k ∈ Finset.Icc 0 ⌊x⌋₊, (1 : ℝ)
      = ∫ x in Set.Ioc (0 : ℝ) m, emPhi' t x * ((⌊x⌋₊ : ℝ) + 1) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only [Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul, mul_one]
    push_cast; ring
  rw [hfloor, ← intervalIntegral.integral_of_le (Nat.cast_nonneg m)]
  have hint_x1 : IntervalIntegrable (fun x => emPhi' t x * (x + 1)) volume 0 m :=
    (continuous_emPhi'.mul (by fun_prop)).intervalIntegrable _ _
  have hint_fr : IntervalIntegrable (fun x => emPhi' t x * Int.fract x) volume 0 m :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg m)).mpr
      ((integrableOn_emPhi'_fract ht).mono_set Set.Ioc_subset_Ioi_self)
  have e1 : ∫ x in (0 : ℝ)..m, emPhi' t x * ((⌊x⌋₊ : ℝ) + 1)
      = ∫ x in (0 : ℝ)..m, (emPhi' t x * (x + 1) - emPhi' t x * Int.fract x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (Nat.cast_nonneg m)] at hx
    have hx0 : 0 ≤ x := hx.1
    have hfl : (⌊x⌋₊ : ℝ) = x - Int.fract x := by
      have h2 : (⌊x⌋₊ : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast Int.natCast_floor_eq_floor hx0
      rw [Int.fract, h2]; ring
    simp only [hfl]; ring
  rw [e1, intervalIntegral.integral_sub hint_x1 hint_fr]
  have hIBP : ∫ x in (0 : ℝ)..m, emPhi' t x * (x + 1)
      = emPhi t m * (m + 1) - emPhi t 0 * 1 - ∫ x in (0 : ℝ)..m, emPhi t x := by
    have hpsi : ∀ x : ℝ, HasDerivAt (fun y => emPhi t y * (y + 1))
        (emPhi' t x * (x + 1) + emPhi t x * 1) x := by
      intro x
      exact (hasDerivAt_emPhi x).mul (by simpa using (hasDerivAt_id x).add_const 1)
    have hftc : ∫ x in (0 : ℝ)..m, (emPhi' t x * (x + 1) + emPhi t x * 1)
        = (emPhi t m * (m + 1)) - (emPhi t 0 * (0 + 1)) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hpsi x)]
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [intervalIntegral.integral_add (hint_x1)
      (Continuous.intervalIntegrable (u := fun x : ℝ => emPhi t x * 1) (by fun_prop) _ _)] at hftc
    simp only [mul_one] at hftc ⊢; linarith [hftc]
  rw [hIBP]
  have hphi0 : emPhi t 0 = 1 := by unfold emPhi; norm_num
  rw [hphi0]; ring

/-- The EM-1 identity in `{x}`-form: `Θ(t) = 1 + 1/t + ∫_{(0,∞)} φ'(x)·{x} dx`, obtained from
`emFinite` by passing `m → ∞` (partial sums → `sphereHeatTrace`; `∫_0^m → ∫_{(0,∞)}`). -/
theorem sphereHeatTrace_emFract (ht : 0 < t) :
    sphereHeatTrace t = 1 + 1 / t + ∫ x in Set.Ioi (0 : ℝ), emPhi' t x * Int.fract x := by
  have htendL : Tendsto (fun m : ℕ => ∑ k ∈ Finset.Icc 0 m, emPhi t k) atTop
      (𝓝 (sphereHeatTrace t)) := by
    have h1 : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, emPhi t k
        = ∑ k ∈ Finset.range (m + 1),
            (2 * (k : ℝ) + 1) * Real.exp (-t * ((k : ℝ) * ((k : ℝ) + 1))) := by
      intro m; rw [← Nat.range_succ_eq_Icc_zero]; rfl
    simp_rw [h1]
    exact ((sphereHeatTrace_summable ht).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have htendφ : Tendsto (fun m : ℕ => ∫ x in (0 : ℝ)..m, emPhi t x) atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), emPhi t x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (emIntegrable ht) tendsto_natCast_atTop_atTop
  have htendfr : Tendsto (fun m : ℕ => ∫ x in (0 : ℝ)..m, emPhi' t x * Int.fract x) atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), emPhi' t x * Int.fract x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_emPhi'_fract ht)
      tendsto_natCast_atTop_atTop
  have htendR := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ)) |>.add htendφ).add htendfr
  have := tendsto_nhds_unique (htendL.congr (fun m => emFinite ht m)) htendR
  rw [this, emWeyl ht]

/-- **★ The exact first-order Euler–Maclaurin identity for the `S²` heat trace.**
`Θ(t) = 1/t + 1/2 + ∫_{(0,∞)} (P₁ x)·φ'(x) dx`, where `P₁ x = Int.fract x − 1/2` is the first
periodic Bernoulli function and `φ'(x) = (2 − t(2x+1)²)e^{-t x(x+1)}`. The `1/t` is the Weyl term
`a₀`, the `+1/2` is the `φ(0)/2` boundary term, and the remainder `∫ P₁ φ'` carries the curvature
constant: its `t → 0⁺` limit is `−1/6`, which would give `Θ(t) − 1/t → 1/2 − 1/6 = 1/3 = a₁ = R/6`.
That remainder limit needs a second/third-order Euler–Maclaurin estimate (periodic `P₂`, `P₃`,
with the mean-zero cancellation `∫₀¹ P₂ = 0`), absent from Mathlib — so this identity is the honest
EM-1 checkpoint, and the sum-level `a₁` limit `Θ(t) − 1/t → 1/3` remains open. Proved purely from
Abel summation (`sum_mul_eq_sub_integral_mul'`); uses NO Euler–Maclaurin/Bernoulli substrate and
none of the missing curved-heat-kernel machinery. -/
theorem sphereHeatTrace_em1 (ht : 0 < t) :
    sphereHeatTrace t
      = 1 / t + 1 / 2 + ∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emPhi' t x := by
  have hconv : ∫ x in Set.Ioi (0 : ℝ), (Int.fract x - 1 / 2) * emPhi' t x
      = (∫ x in Set.Ioi (0 : ℝ), emPhi' t x * Int.fract x) + 1 / 2 := by
    have hsplit : ∀ x, (Int.fract x - 1 / 2) * emPhi' t x
        = emPhi' t x * Int.fract x - (1 / 2) * emPhi' t x := by intro x; ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hsplit x)]
    rw [MeasureTheory.integral_sub (integrableOn_emPhi'_fract ht)
      ((integrableOn_emPhi' ht).const_mul (1 / 2))]
    rw [MeasureTheory.integral_const_mul, integral_emPhi'_eq ht]; ring
  rw [hconv, sphereHeatTrace_emFract ht]; ring

end QIQTH.SphereHeatTrace
