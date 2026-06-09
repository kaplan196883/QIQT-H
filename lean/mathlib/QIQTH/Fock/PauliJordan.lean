/-
  K-localization — toward the Pauli–Jordan spacelike-support theorem (the single remaining input for the
  literal OP3b prize).  GPT-5.5-pro flagged this as the genuine analytic wall: the localized commutator
  form `Im⟪K f, K g⟫` must vanish for spacelike-separated supports, and the naive route through the
  pointwise kernel `Δ_m(z) = ∫_θ sin(η(p_m θ, z)) dθ` is *not* absolutely convergent.

  This file proves the STRUCTURAL BACKBONE of that theorem, axiom-free and `sorry`-free:

    1. `Kform_boost_invariant` — the localized symplectic (commutator) form is Lorentz-boost invariant,
       `Kform m (β_a f) (β_a g) = Kform m f g`.  (Microcausality is a boost-invariant statement.)
    2. `minkowskiDot_massShell` — the explicit phase `η(p_m θ, z) = m (z₀ cosh θ − z₁ sinh θ)`.
    3. `minkowskiDot_massShell_spacelike` — the hyperbolic REPARAMETRIZATION: for a spacelike `z`
       (`z₁² > z₀²`) the phase is a single hyperbolic sine `η(p_m θ, z) = c · sinh(θ − φ)` — the identity
       that turns the kernel into an ODD function of `θ − φ`, the source of the cancellation.
    4. `pauliJordan_trunc_equalTime_zero` — the clean EXACT case: for an equal-time separation (`z₀ = 0`)
       the truncated kernel `∫_{−R}^{R} sin(η(p_m θ, z)) dθ = 0` for *every* `R` (odd integrand).

  The remaining steps to the full theorem (documented, NOT yet formalized) are: the general-spacelike
  pointwise limit `lim_R ∫_{−R}^{R} sin(η(p_m θ,z)) dθ = 0` (odd symmetry of `c·sinh(θ−φ)` via (3) + an
  oscillatory `1/cosh` integration-by-parts tail bound for the shifted endpoints), and the bilinear assembly
  (finite-`R` Fubini on compact supports + dominated convergence using `r ≥ r₀ > 0` on compact
  spacelike-separated sets).
-/
import QIQTH.Fock.Localization
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open Real MeasureTheory

namespace QIQTH.Fock.Localization

/-! ### 1. Boost-invariance of the localized symplectic (commutator) form -/

/-- **The localized symplectic form is Lorentz-boost invariant**:
`Kform m (β_a f) (β_a g) = Kform m f g`.  Microcausality (`Im Kform = 0` for spacelike separation) is
therefore a boost-invariant statement.  Immediate from the amplitude-level boost-covariance `Krep_boost`
(boost = rapidity translation `θ ↦ θ + a`) and the translation invariance of Lebesgue measure on `ℝ`. -/
theorem Kform_boost_invariant (m a : ℝ) (f g : V → ℂ) :
    Kform m (boostTest a f) (boostTest a g) = Kform m f g := by
  simp only [Kform, Krep_boost]
  exact integral_add_right_eq_self
    (fun θ => (starRingEnd ℂ) (Krep m f θ) * Krep m g θ) a

/-! ### 2. The explicit mass-shell phase -/

/-- **The mass-shell phase**: `η(p_m θ, z) = m (z₀ cosh θ − z₁ sinh θ)`. -/
theorem minkowskiDot_massShell (m θ : ℝ) (z : V) :
    minkowskiDot (massShell m θ) z = m * (z 0 * Real.cosh θ - z 1 * Real.sinh θ) := by
  simp only [minkowskiDot, massShell_zero, massShell_one]
  ring

/-! ### 3. The hyperbolic reparametrization for spacelike separations -/

/-- A separation `z` is **spacelike** when `z₁² > z₀²` (i.e. `minkowskiSq z = z₀² − z₁² < 0`). -/
def Spacelike (z : V) : Prop := z 0 ^ 2 < z 1 ^ 2

/-- **The hyperbolic reparametrization.**  For a spacelike `z` the mass-shell phase is a single hyperbolic
sine: there are `c, φ` with `η(p_m θ, z) = c · sinh(θ − φ)` for all `θ`.  Hence as a function of `θ − φ` the
kernel `sin(η(p_m θ, z))` is ODD — the structural source of the Pauli–Jordan cancellation in the spacelike
region.  (Here `c = − m √(z₁²−z₀²)·sign z₁` and `φ` is the rapidity with `tanh φ = z₀/z₁`.) -/
theorem minkowskiDot_massShell_spacelike (m : ℝ) {z : V} (hz : Spacelike z) :
    ∃ c φ : ℝ, ∀ θ, minkowskiDot (massShell m θ) z = c * Real.sinh (θ - φ) := by
  have hz' : z 0 ^ 2 < z 1 ^ 2 := hz
  have hz1sq : 0 < z 1 ^ 2 := lt_of_le_of_lt (sq_nonneg _) hz'
  set r : ℝ := Real.sqrt (z 1 ^ 2 - z 0 ^ 2) with hrdef
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hrne : r ≠ 0 := hrpos.ne'
  have hrsq : r ^ 2 = z 1 ^ 2 - z 0 ^ 2 := Real.sq_sqrt (by linarith)
  -- sign of z₁
  set s : ℝ := if 0 ≤ z 1 then 1 else -1 with hsdef
  have hssq : s * s = 1 := by rw [hsdef]; split_ifs <;> ring
  have hs2 : s ^ 2 = 1 := by rw [pow_two]; exact hssq
  have hsz1' : |z 1| = s * z 1 := by
    rw [hsdef]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (lt_of_not_ge h), neg_one_mul]
  have hsz0sq : (s * z 0) ^ 2 = z 0 ^ 2 := by rw [mul_pow, hs2, one_mul]
  -- rapidity φ with sinh φ = s z₀ / r, cosh φ = |z₁| / r
  set φ : ℝ := Real.arsinh (s * z 0 / r) with hφdef
  have hsinhφ : Real.sinh φ = s * z 0 / r := Real.sinh_arsinh _
  have hcoshφ : Real.cosh φ = |z 1| / r := by
    rw [hφdef, Real.cosh_arsinh,
      show (1 : ℝ) + (s * z 0 / r) ^ 2 = (z 1 / r) ^ 2 by
        rw [div_pow, hsz0sq, div_pow]; field_simp; linarith [hrsq],
      Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hrpos]
  have hrcosh : r * Real.cosh φ = |z 1| := by rw [hcoshφ]; field_simp
  have hrsinh : r * Real.sinh φ = s * z 0 := by rw [hsinhφ]; field_simp
  refine ⟨-(m * s * r), φ, fun θ => ?_⟩
  rw [minkowskiDot_massShell, Real.sinh_sub,
    show -(m * s * r) * (Real.sinh θ * Real.cosh φ - Real.cosh θ * Real.sinh φ)
      = -(m * s) * (Real.sinh θ * (r * Real.cosh φ) - Real.cosh θ * (r * Real.sinh φ)) by ring,
    hrcosh, hrsinh, hsz1']
  linear_combination (-(m * (z 0 * Real.cosh θ - z 1 * Real.sinh θ))) * hssq

/-! ### 4. The exact equal-time vanishing of the truncated kernel -/

/-- **Equal-time vanishing.**  For an equal-time separation (`z₀ = 0`) the truncated Pauli–Jordan kernel
`∫_{−R}^{R} sin(η(p_m θ, z)) dθ = 0` for *every* `R` — the integrand `sin(η(p_m θ,z)) = sin(−m z₁ sinh θ)`
is ODD in `θ`, so the symmetric integral vanishes exactly (no limit needed).  This is the microcausality
cancellation in its cleanest form. -/
theorem pauliJordan_trunc_equalTime_zero (m R : ℝ) {z : V} (hz0 : z 0 = 0) :
    (∫ θ in (-R)..R, Real.sin (minkowskiDot (massShell m θ) z)) = 0 := by
  set g : ℝ → ℝ := fun θ => Real.sin (minkowskiDot (massShell m θ) z) with hg
  -- the integrand is odd
  have hodd : ∀ θ, g (-θ) = - g θ := by
    intro θ
    have e1 : minkowskiDot (massShell m (-θ)) z = m * z 1 * Real.sinh θ := by
      rw [minkowskiDot_massShell, hz0, Real.cosh_neg, Real.sinh_neg]; ring
    have e2 : minkowskiDot (massShell m θ) z = -(m * z 1 * Real.sinh θ) := by
      rw [minkowskiDot_massShell, hz0]; ring
    simp only [hg]
    rw [e1, e2, Real.sin_neg, neg_neg]
  -- ∫_{-R}^R g(-θ) dθ = ∫_{-R}^R g θ dθ  (comp_neg on the symmetric interval)
  have h1 : (∫ θ in (-R)..R, g (-θ)) = ∫ θ in (-R)..R, g θ := by
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R) g
    simp only [neg_neg] at h
    exact h
  -- but g(-θ) = -g θ, so the LHS is -∫ g
  have h2 : (∫ θ in (-R)..R, g (-θ)) = -∫ θ in (-R)..R, g θ := by
    rw [show (fun θ => g (-θ)) = (fun θ => -g θ) from funext hodd,
      intervalIntegral.integral_neg]
  -- hence ∫ g = -∫ g, so ∫ g = 0
  have h3 : (∫ θ in (-R)..R, g θ) = -∫ θ in (-R)..R, g θ := h1.symm.trans h2
  linarith

/-! ### 5. The oscillatory `1/cosh` decay bound (keystone of the general-spacelike limit) -/

/-- A clean antiderivative computation: `∫_a^b sinh x / cosh² x dx = (cosh a)⁻¹ − (cosh b)⁻¹`
(antiderivative `−(cosh x)⁻¹`). -/
theorem integral_sinh_div_cosh_sq (a b : ℝ) :
    (∫ x in a..b, Real.sinh x / Real.cosh x ^ 2) = (Real.cosh a)⁻¹ - (Real.cosh b)⁻¹ := by
  have hd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => -(Real.cosh x)⁻¹) (Real.sinh x / Real.cosh x ^ 2) x := by
    intro x _
    have h2 : HasDerivAt (fun x => (Real.cosh x)⁻¹)
        (-Real.sinh x / Real.cosh x ^ 2) x := (Real.hasDerivAt_cosh x).inv (Real.cosh_pos x).ne'
    have := h2.neg
    convert this using 1
    rw [neg_div, neg_neg]
  have hint : IntervalIntegrable (fun x => Real.sinh x / Real.cosh x ^ 2) volume a b := by
    apply Continuous.intervalIntegrable
    exact Real.continuous_sinh.div (Real.continuous_cosh.pow 2)
      (fun x => pow_ne_zero 2 (Real.cosh_pos x).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  ring

/-- **The oscillatory `1/cosh` integration-by-parts bound** — the keystone GPT-5.5-pro flagged.  For
`0 ≤ a ≤ b`, the oscillatory integral of `sin(c·sinh u)` over `[a,b]` is controlled by `1/cosh a` despite
the integrand never decaying:
`|∫_a^b sin(c·sinh u) du| ≤ 3 / (|c|·cosh a)`.
Proof: integrate by parts with `u = (c·cosh)⁻¹`, `v = −cos(c·sinh)`, so `u·v' = sin(c·sinh)`; the boundary
terms are each `≤ 1/(|c|·cosh a)` and the remainder `∫ sinh·cos/(c·cosh²)` is `≤ 1/(|c|·cosh a)` via
`integral_sinh_div_cosh_sq`.  This gives `Δ_m(z) = 0` for spacelike `z` once combined with the odd-symmetry
of the reparametrized kernel. -/
theorem abs_integral_sin_sinh_le (c : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |∫ u in a..b, Real.sin (c * Real.sinh u)| ≤ 3 / (|c| * Real.cosh a) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hb : 0 ≤ b := le_trans ha hab
  have hca : 0 < Real.cosh a := Real.cosh_pos a
  have hcb : 0 < Real.cosh b := Real.cosh_pos b
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hcab : Real.cosh a ≤ Real.cosh b :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact hab)
  have hcc : ∀ x, c * Real.cosh x ≠ 0 := fun x => mul_ne_zero hc (Real.cosh_pos x).ne'
  -- derivatives for integration by parts
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => (c * Real.cosh x)⁻¹)
        (-(c * Real.sinh x) / (c * Real.cosh x) ^ 2) x := by
    intro x _
    exact ((Real.hasDerivAt_cosh x).const_mul c).inv (hcc x)
  have hv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => -Real.cos (c * Real.sinh x))
        (Real.sin (c * Real.sinh x) * (c * Real.cosh x)) x := by
    intro x _
    have hg : HasDerivAt (fun x => c * Real.sinh x) (c * Real.cosh x) x :=
      (Real.hasDerivAt_sinh x).const_mul c
    have := ((Real.hasDerivAt_cos (c * Real.sinh x)).comp x hg).neg
    convert this using 1
    ring
  have hint_u' : IntervalIntegrable (fun x => -(c * Real.sinh x) / (c * Real.cosh x) ^ 2) volume a b := by
    apply Continuous.intervalIntegrable
    exact ((continuous_const.mul Real.continuous_sinh).neg).div
      ((continuous_const.mul Real.continuous_cosh).pow 2) (fun x => pow_ne_zero 2 (hcc x))
  have hint_v' : IntervalIntegrable
      (fun x => Real.sin (c * Real.sinh x) * (c * Real.cosh x)) volume a b := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_sin.comp (continuous_const.mul Real.continuous_sinh)).mul
      (continuous_const.mul Real.continuous_cosh)
  -- integration by parts
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hint_u' hint_v'
  -- the LHS integrand simplifies to sin(c sinh x)
  have hLHS : (∫ x in a..b, (c * Real.cosh x)⁻¹ * (Real.sin (c * Real.sinh x) * (c * Real.cosh x)))
      = ∫ x in a..b, Real.sin (c * Real.sinh x) := by
    apply intervalIntegral.integral_congr
    intro x _
    field_simp
  rw [hLHS] at key
  -- name the remainder integral and bound it
  set I : ℝ := ∫ x in a..b, -(c * Real.sinh x) / (c * Real.cosh x) ^ 2 * -Real.cos (c * Real.sinh x)
    with hI
  -- |I| ≤ ∫ |integrand| ≤ ∫ sinh/(|c| cosh²) = (1/|c|)((cosh a)⁻¹ - (cosh b)⁻¹)
  have hIbound : |I| ≤ |c|⁻¹ * ((Real.cosh a)⁻¹ - (Real.cosh b)⁻¹) := by
    have hbound1 : |I| ≤ ∫ x in a..b,
        |(-(c * Real.sinh x) / (c * Real.cosh x) ^ 2 * -Real.cos (c * Real.sinh x))| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have hpt : ∀ x ∈ Set.Icc a b,
        |(-(c * Real.sinh x) / (c * Real.cosh x) ^ 2 * -Real.cos (c * Real.sinh x))|
          ≤ |c|⁻¹ * (Real.sinh x / Real.cosh x ^ 2) := by
      intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1
      rw [abs_mul, abs_div, abs_neg, abs_neg]
      have hsinh : |c * Real.sinh x| = |c| * Real.sinh x := by
        rw [abs_mul, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx0)]
      have hcosh2 : |(c * Real.cosh x) ^ 2| = c ^ 2 * Real.cosh x ^ 2 := by
        rw [abs_pow, abs_mul, abs_of_pos (Real.cosh_pos x), mul_pow, sq_abs]
      rw [hsinh, hcosh2]
      have hcoscalc : |Real.cos (c * Real.sinh x)| ≤ 1 := Real.abs_cos_le_one _
      calc |c| * Real.sinh x / (c ^ 2 * Real.cosh x ^ 2) * |Real.cos (c * Real.sinh x)|
          ≤ |c| * Real.sinh x / (c ^ 2 * Real.cosh x ^ 2) * 1 := by
            gcongr
        _ = |c|⁻¹ * (Real.sinh x / Real.cosh x ^ 2) := by
            rw [mul_one, ← sq_abs c]
            field_simp
    have hmono : (∫ x in a..b,
        |(-(c * Real.sinh x) / (c * Real.cosh x) ^ 2 * -Real.cos (c * Real.sinh x))|)
        ≤ ∫ x in a..b, |c|⁻¹ * (Real.sinh x / Real.cosh x ^ 2) := by
      apply intervalIntegral.integral_mono_on hab _ _ hpt
      · apply Continuous.intervalIntegrable
        fun_prop (disch := intro x; exact pow_ne_zero 2 (hcc x))
      · apply Continuous.intervalIntegrable
        exact continuous_const.mul (Real.continuous_sinh.div (Real.continuous_cosh.pow 2)
          (fun x => pow_ne_zero 2 (Real.cosh_pos x).ne'))
    rw [intervalIntegral.integral_const_mul, integral_sinh_div_cosh_sq] at hmono
    exact le_trans hbound1 hmono
  -- the boundary terms
  have hbdry : ∀ t : ℝ, |(c * Real.cosh t)⁻¹ * -Real.cos (c * Real.sinh t)| ≤ (|c| * Real.cosh t)⁻¹ := by
    intro t
    rw [abs_mul, abs_neg, abs_inv, abs_mul, abs_of_pos (Real.cosh_pos t)]
    calc (|c| * Real.cosh t)⁻¹ * |Real.cos (c * Real.sinh t)|
        ≤ (|c| * Real.cosh t)⁻¹ * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ = (|c| * Real.cosh t)⁻¹ := mul_one _
  -- assemble
  rw [key]
  have e1 : (|c| * Real.cosh b)⁻¹ ≤ (|c| * Real.cosh a)⁻¹ := by
    gcongr
  calc |(c * Real.cosh b)⁻¹ * -Real.cos (c * Real.sinh b)
        - (c * Real.cosh a)⁻¹ * -Real.cos (c * Real.sinh a) - I|
      ≤ |(c * Real.cosh b)⁻¹ * -Real.cos (c * Real.sinh b)|
        + |(c * Real.cosh a)⁻¹ * -Real.cos (c * Real.sinh a)| + |I| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ (|c| * Real.cosh a)⁻¹ + (|c| * Real.cosh a)⁻¹ + |c|⁻¹ * ((Real.cosh a)⁻¹ - (Real.cosh b)⁻¹) := by
        gcongr
        · exact le_trans (hbdry b) e1
        · exact hbdry a
    _ ≤ 3 / (|c| * Real.cosh a) := by
        rw [div_eq_mul_inv, mul_inv]
        have : (0:ℝ) ≤ (Real.cosh b)⁻¹ := by positivity
        nlinarith [mul_inv_le_one (a := |c|), inv_nonneg.mpr hca.le, inv_nonneg.mpr hcabs.le, this]

/-! ### 6. The general-spacelike pointwise vanishing of the Pauli–Jordan kernel -/

/-- The symmetric integral of the odd kernel vanishes exactly: `∫_{−T}^{T} sin(c·sinh u) du = 0`. -/
theorem integral_sin_sinh_symm_zero (c T : ℝ) :
    (∫ u in (-T)..T, Real.sin (c * Real.sinh u)) = 0 := by
  have hodd : (fun u => Real.sin (c * Real.sinh (-u))) = fun u => -Real.sin (c * Real.sinh u) := by
    funext u; rw [Real.sinh_neg, mul_neg, Real.sin_neg]
  have h1 : (∫ u in (-T)..T, Real.sin (c * Real.sinh (-u)))
      = ∫ u in (-T)..T, Real.sin (c * Real.sinh u) := by
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := T)
      (fun u => Real.sin (c * Real.sinh u))
    simp only [neg_neg] at h
    exact h
  have h2 : (∫ u in (-T)..T, Real.sin (c * Real.sinh (-u)))
      = -∫ u in (-T)..T, Real.sin (c * Real.sinh u) := by
    rw [hodd, intervalIntegral.integral_neg]
  linarith [h1.symm.trans h2]

/-- The shifted-endpoint oscillatory bound (the remainder after the symmetric part cancels):
`|∫_{R−φ}^{R+φ} sin(c·sinh u) du| ≤ 3/(|c|·cosh(R−|φ|))` for `|φ| ≤ R`. -/
theorem abs_integral_shifted_le (c φ : ℝ) {R : ℝ} (hR : |φ| ≤ R) :
    |∫ u in (R - φ)..(R + φ), Real.sin (c * Real.sinh u)| ≤ 3 / (|c| * Real.cosh (R - |φ|)) := by
  rcases le_total φ 0 with hφ | hφ
  · rw [abs_of_nonpos hφ, sub_neg_eq_add]
    have ha : 0 ≤ R + φ := by rw [abs_of_nonpos hφ] at hR; linarith
    rw [intervalIntegral.integral_symm, abs_neg]
    exact abs_integral_sin_sinh_le c ha (by linarith)
  · rw [abs_of_nonneg hφ]
    have ha : 0 ≤ R - φ := by rw [abs_of_nonneg hφ] at hR; linarith
    exact abs_integral_sin_sinh_le c ha (by linarith)

/-- `(cosh ·)⁻¹ → 0` at `+∞` (cosh dominates `exp/2`). -/
theorem tendsto_inv_cosh_atTop :
    Filter.Tendsto (fun t : ℝ => (Real.cosh t)⁻¹) Filter.atTop (nhds 0) := by
  have hcoshtop : Filter.Tendsto Real.cosh Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun x => ?_)
      (Real.tendsto_exp_atTop.atTop_div_const (by norm_num : (0:ℝ) < 2))
    rw [Real.cosh_eq]
    have := (Real.exp_pos (-x)).le
    linarith
  exact tendsto_inv_atTop_zero.comp hcoshtop

/-- **The Pauli–Jordan kernel vanishes for spacelike separations** (pointwise, as the symmetric
improper integral).  For a spacelike `z`,
`lim_{R→∞} ∫_{−R}^{R} sin(η(p_m θ, z)) dθ = 0`.
This is the genuine spacelike vanishing of `Δ_m` — the heart of microcausality.  Proof: the
reparametrization (`minkowskiDot_massShell_spacelike`) makes the integrand `sin(c·sinh(θ−φ))`; after the
shift `u = θ−φ` the symmetric part `∫_{−(R−φ)}^{R−φ}` is exactly `0` (odd, `integral_sin_sinh_symm_zero`),
and the remaining length-`2|φ|` tail is bounded by `3/(|c|·cosh(R−|φ|)) → 0` (`abs_integral_shifted_le`,
the IBP keystone), so the whole integral is squeezed to `0`. -/
theorem pauliJordan_spacelike_tendsto_zero (m : ℝ) {z : V} (hz : Spacelike z) :
    Filter.Tendsto (fun R => ∫ θ in (-R)..R, Real.sin (minkowskiDot (massShell m θ) z))
      Filter.atTop (nhds 0) := by
  obtain ⟨c, φ, hcφ⟩ := minkowskiDot_massShell_spacelike m hz
  have hcont : ∀ a b : ℝ, IntervalIntegrable (fun u => Real.sin (c * Real.sinh u)) volume a b :=
    fun a b => (Real.continuous_sin.comp
      (continuous_const.mul Real.continuous_sinh)).intervalIntegrable a b
  -- rewrite the integral as a shifted oscillatory integral
  have hrw : ∀ R, (∫ θ in (-R)..R, Real.sin (minkowskiDot (massShell m θ) z))
      = ∫ u in (-R - φ)..(R - φ), Real.sin (c * Real.sinh u) := by
    intro R
    rw [show (fun θ => Real.sin (minkowskiDot (massShell m θ) z))
        = (fun θ => Real.sin (c * Real.sinh (θ - φ))) from funext fun θ => by rw [hcφ θ]]
    rw [intervalIntegral.integral_comp_sub_right (fun u => Real.sin (c * Real.sinh u)) φ]
  -- the uniform bound for R ≥ |φ|
  have hbound : ∀ R, |φ| ≤ R →
      |∫ u in (-R - φ)..(R - φ), Real.sin (c * Real.sinh u)| ≤ 3 / (|c| * Real.cosh (R - |φ|)) := by
    intro R hR
    have hneg : (∫ u in (-R - φ)..(-(R - φ)), Real.sin (c * Real.sinh u))
        = -∫ u in (R - φ)..(R + φ), Real.sin (c * Real.sinh u) := by
      have h := intervalIntegral.integral_comp_neg (a := R - φ) (b := R + φ)
        (fun u => Real.sin (c * Real.sinh u))
      simp only [Real.sinh_neg, mul_neg, Real.sin_neg, intervalIntegral.integral_neg] at h
      rw [show (-R - φ : ℝ) = -(R + φ) by ring]
      exact h.symm
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont (-R - φ) (-(R - φ)))
        (hcont (-(R - φ)) (R - φ)),
      integral_sin_sinh_symm_zero c (R - φ), add_zero, hneg, abs_neg]
    exact abs_integral_shifted_le c φ hR
  -- the bound tends to 0
  have hsub : Filter.Tendsto (fun R : ℝ => R - |φ|) Filter.atTop Filter.atTop := by
    simpa [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right Filter.atTop (-|φ|) Filter.tendsto_id
  have hBtop : Filter.Tendsto (fun R => 3 / (|c| * Real.cosh (R - |φ|))) Filter.atTop (nhds 0) := by
    have hc1 : Filter.Tendsto (fun R => (Real.cosh (R - |φ|))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_cosh_atTop.comp hsub
    have h2 := hc1.const_mul (3 * |c|⁻¹)
    rw [mul_zero] at h2
    refine h2.congr (fun R => ?_)
    rw [div_eq_mul_inv, mul_inv]; ring
  -- squeeze
  simp only [hrw]
  have hBneg : Filter.Tendsto (fun R => -(3 / (|c| * Real.cosh (R - |φ|)))) Filter.atTop (nhds 0) := by
    simpa using hBtop.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hBneg hBtop ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop |φ|] with R hR
    exact (abs_le.mp (hbound R hR)).1
  · filter_upwards [Filter.eventually_ge_atTop |φ|] with R hR
    exact (abs_le.mp (hbound R hR)).2

/-! ### 7. The uniform dominating bound (ingredient for the dominated-convergence assembly, 5c) -/

/-- The kernel reflection: `∫_{−q}^{−p} sin(c·sinh u) du = − ∫_p^q sin(c·sinh u) du` (oddness). -/
theorem reflect_integral_sin_sinh (c p q : ℝ) :
    (∫ u in (-q)..(-p), Real.sin (c * Real.sinh u))
      = -∫ u in p..q, Real.sin (c * Real.sinh u) := by
  have h := intervalIntegral.integral_comp_neg (a := p) (b := q)
    (fun u => Real.sin (c * Real.sinh u))
  simp only [Real.sinh_neg, mul_neg, Real.sin_neg, intervalIntegral.integral_neg] at h
  exact h.symm

/-- **The uniform oscillatory bound** — the dominating function for the dominated-convergence step of the
bilinear assembly (5c).  For *all* `a, b`,
`|∫_a^b sin(c·sinh u) du| ≤ 6/|c|`,
uniformly: splitting at `0`, each half is `≤ 3/|c|` by the keystone `abs_integral_sin_sinh_le` (with the
left endpoint `0`, `cosh 0 = 1`) together with the reflection for the negative half. -/
theorem abs_integral_sin_sinh_le_uniform (c a b : ℝ) :
    |∫ u in a..b, Real.sin (c * Real.sinh u)| ≤ 6 / |c| := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hcont : ∀ p q : ℝ, IntervalIntegrable (fun u => Real.sin (c * Real.sinh u)) volume p q :=
    fun p q => (Real.continuous_sin.comp
      (continuous_const.mul Real.continuous_sinh)).intervalIntegrable p q
  -- |∫_0^t| ≤ 3/|c| for every t (both signs, via the keystone + reflection)
  have h0t : ∀ t : ℝ, |∫ u in (0:ℝ)..t, Real.sin (c * Real.sinh u)| ≤ 3 / |c| := by
    intro t
    rcases le_total 0 t with ht | ht
    · have h := abs_integral_sin_sinh_le c (le_refl (0:ℝ)) ht
      rwa [Real.cosh_zero, mul_one] at h
    · have hr := reflect_integral_sin_sinh c 0 (-t)
      simp only [neg_neg, neg_zero] at hr
      rw [intervalIntegral.integral_symm 0 t] at hr
      rw [neg_injective hr]
      have key0 := abs_integral_sin_sinh_le c (le_refl (0:ℝ)) (by linarith : (0:ℝ) ≤ -t)
      rwa [Real.cosh_zero, mul_one] at key0
  -- split at 0 and add
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont a 0) (hcont 0 b)]
  refine (abs_add_le _ _).trans ?_
  have ha0 : |∫ u in a..(0:ℝ), Real.sin (c * Real.sinh u)| ≤ 3 / |c| := by
    rw [intervalIntegral.integral_symm 0 a, abs_neg]; exact h0t a
  have h6 : (6 : ℝ) / |c| = 3 / |c| + 3 / |c| := by ring
  rw [h6]; linarith [ha0, h0t b]

/-! ### 8. The `r₀ > 0` compactness bound (the other ingredient for the 5c assembly) -/

/-- **Positive spacelike interval on compact separated supports.**  If `K, L` are compact and every
`x ∈ K`, `y ∈ L` is spacelike-separated (`Spacelike (x − y)`), then the spacelike interval squared
`(x−y)₁² − (x−y)₀²` is bounded below by a *uniform* `ε > 0`.  This is what makes the dominating function
`6/|c(x−y)| = 6/(|m|·√((x−y)₁²−(x−y)₀²))` bounded (hence integrable) on `K × L` — the second ingredient
the dominated-convergence step of the bilinear assembly (5c) needs.  Proof: the continuous function
`(x,y) ↦ (x−y)₁² − (x−y)₀²` attains its (positive) minimum on the compact set `K × L`. -/
theorem exists_pos_lower_bound_slSq {K L : Set V} (hK : IsCompact K) (hL : IsCompact L)
    (hsep : ∀ x ∈ K, ∀ y ∈ L, Spacelike (x - y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ y ∈ L, ε ≤ (x - y) 1 ^ 2 - (x - y) 0 ^ 2 := by
  rcases (K ×ˢ L).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun x hx y hy => ?_⟩
    rw [Set.eq_empty_iff_forall_notMem] at hemp
    exact absurd (Set.mk_mem_prod hx hy) (hemp (x, y))
  · set g : V × V → ℝ := fun p => (p.1 - p.2) 1 ^ 2 - (p.1 - p.2) 0 ^ 2 with hg
    have hgcont : Continuous g := by rw [hg]; fun_prop
    obtain ⟨p₀, hp₀mem, hp₀min⟩ := (hK.prod hL).exists_isMinOn hne hgcont.continuousOn
    obtain ⟨hx₀, hy₀⟩ := Set.mem_prod.mp hp₀mem
    refine ⟨g p₀, ?_, fun x hx y hy => isMinOn_iff.mp hp₀min (x, y) (Set.mk_mem_prod hx hy)⟩
    have hsl : (p₀.1 - p₀.2) 0 ^ 2 < (p₀.1 - p₀.2) 1 ^ 2 := hsep p₀.1 hx₀ p₀.2 hy₀
    simp only [hg]; linarith

end QIQTH.Fock.Localization
