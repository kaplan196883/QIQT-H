/-
  CONICAL HEAT KERNEL — the exact ℤ_n orbifold cone excess and the replica coefficient:
  the conical leg at the integer-cone level (duality campaign, brick D3c).

  Brick D3b (`QIQTH.HeatKernelThermal`) gave the SMOOTH thermal cylinder `S¹_β × ℝ` its
  one-loop heat-kernel form and CITED the cone as the next rung.  THIS brick builds that
  rung at the integer-cone level: it computes, EXACTLY and `t`-independently, the non-area
  heat-trace excess of the integer cone `C_{2π/n} = ℝ²/ℤ_n` by the ℤ_n orbifold IMAGE method
  (no Sommerfeld contour analysis), and reads off the replica (entanglement) coefficient.

  ── The image method / orbifold bookkeeping.  The heat trace on the quotient cone
  `ℝ²/ℤ_n` is, by the method of images,
      Tr K_C(t) = (1/n) · Σ_{k=0}^{n-1} ∫_{ℝ²} K_flat(x, R_k x) dx,
  where `R_k` is rotation by `2πk/n` and `K_flat(x,y) = (4πt)^{-1} e^{-|x-y|²/4t}` is the
  DERIVED flat 2-D heat kernel (the `(4πt)^{-d/2}` of `QIQTH.HeatKernelOneD.heatDensity_oneD`
  at `d = 2`).  The `k = 0` term is `(4πt)^{-1}∫dx = A/(4πt)`, the divergent AREA piece,
  REMOVED BY CONSTRUCTION — the conical EXCESS is the `k ≥ 1` sum (`zmodConeExcess`).  The
  `1/n` is the orbifold volume factor.

  ── `t`-independence (UV-finiteness after area subtraction — PROVED, not asserted).  Each
  `k ≥ 1` image integral is a genuine Gaussian, and
      ∫_{ℝ²} (4πt)^{-1} e^{-|x-R_θ x|²/4t} dx = 1/(4 sin²(θ/2)),
  which carries NO `t` at all (`integral_Kplane_rot`): the `t` in the prefactor and the `t`
  in the Gaussian width cancel exactly.  This is the machine-checked statement that the
  conical excess is a finite, scale-free number — the hallmark of the log-divergent
  entanglement contribution once the area term is gone.

  ── The cosecant sum (roots of unity, a Mathlib-first).  Summing the images needs
      Σ_{k=1}^{n-1} 1/(4 sin²(πk/n)) = (n²−1)/12,   i.e.  Σ csc²(πk/n) = (n²−1)/3.
  This is proved from scratch by the roots-of-unity route (`sum_inv_four_sin_sq`,
  `sum_csc_sq`): with `ζ_k = e^{2πik/n}` the two power sums
      A = Σ 1/(1−ζ_k) = (n−1)/2,   B = Σ 1/(1−ζ_k)² = (n−1)(5−n)/12
  are the first two logarithmic derivatives at `1` of the geometric polynomial
  `∑_{j<n} X^j = ∏_{k}(X−ζ_k)`, and the real bridge `1/|1−ζ_k|² = 1/(1−ζ_k) − 1/(1−ζ_k)²`
  (valid on the unit circle) gives `Σ 1/|1−ζ_k|² = A − B = (n²−1)/12`.

  ── The exact excess and the replica reading.  Assembling,
      zmodConeExcess n t = (n²−1)/(12n) = (1/12)(n − 1/n),   for every `t > 0`
  (`zmodConeExcess_eq`, `zmodConeExcess_eq_standard`).  The interpolating replica
  coefficient `coneCoeff ν = (1/12)(ν − ν⁻¹)` agrees with the machine-checked integer-cone
  excess at every integer (`coneCoeff_nat`) and has replica derivative
      d/dν coneCoeff|_{ν=1} = 1/6
  (`hasDerivAt_coneCoeff_one`) — the famous `c/6 = 1/6` (central charge `c = 1`)
  entanglement coefficient, here obtained as the derivative at `1` of the exactly computed
  integer-cone data.  `conical_excess_exact` packages the three facts.

  Numeric sanity (comments): n=2 → A=1/2, B: only k=1, ζ=−1, `1/(1−(−1))²=1/4`,
  `(1)(3)/12 = 1/4` ✓; excess `(4−1)/24 = 1/8`.  n=3 → `2/(4·(3/4)) = 2/3 = 8/12` ✓, and
  the single image `1/(4 sin²(π/3)) + 1/(4 sin²(2π/3)) = (9−1)/12 = 2/3`, excess `8/36 = 2/9`.

  ────────────────────────────────────────────────────────────────────────────────────────
  MANDATORY FIREWALL (binding scope).  INTEGER cones `C_{2π/n}` ONLY.  The GENERAL-angle
  cone excess (Sommerfeld/Carslaw contour formulas) is CITED, not built.  The `n → 1`
  analytic continuation (the replica step) is CITED as an analytic-continuation PROBLEM; what
  is PROVED here is the interpolating function's exact agreement at the integers together
  with its derivative `1/6` at `1` — not the continuation itself.  Replica-convention
  footnote: the deficit `γ` and the excess parameter relate as `ν = 2π/γ` (here `ν = n`) or
  `m = γ/2π`; the sign/convention of the derivative depends on this choice — we fix
  `ν = n` and differentiate at `ν = 1`.  The full one-loop determinant `½∫(dt/t) Tr K_C(t)`
  and its UV regularization (which turn the excess into the log-coefficient of the
  entanglement/black-hole entropy) are CITED, not evaluated.  Smooth-manifold-with-defect
  geometry, higher dimensions, and the coupling to `A/4G` (the gravitational action, the
  renormalized `G`, and Bekenstein–Hawking) are ALL CITED.  Ties: same flat 2-D kernel as
  the held D3b cylinder (`QIQTH.HeatKernelThermal`) but a DIFFERENT quotient (rotation vs
  translation windings); the held flat-cone layer `QIQTH.ConeFlat.cone_flat_iff` is CITED
  (Gibbons–Hawking smoothness at `θ = 2π`).  This is NOT the DY7 conjecture (its third rung),
  NOT the strong holographic principle, and NOT quantum gravity.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.HeatKernelThermal

open scoped BigOperators
open Finset Polynomial MeasureTheory

noncomputable section

namespace QIQTH.ConicalHeatKernel

/-! ### PART A — the cosecant sum `Σ_{k=1}^{n-1} 1/(4 sin²(πk/n)) = (n²−1)/12`

The roots-of-unity route.  `ζ_k = e^{2πik/n}`.  The two complex power sums `A = Σ 1/(1−ζ_k)`
and `B = Σ 1/(1−ζ_k)²` are the logarithmic derivatives at `1` of the geometric polynomial
`geomPoly n = ∑_{j<n} X^j = ∏_k (X − ζ_k)`, computed via the product-rule identities
`eval_derivative_prodLin` / `eval_second_derivative_prodLin`. -/

/-- Polynomials over `ℂ`. -/
abbrev CPoly := Polynomial ℂ

/-- The geometric polynomial `∑_{j<n} Xʲ = (Xⁿ − 1)/(X − 1)`, whose roots are the nontrivial
    `n`-th roots of unity. -/
def geomPoly (n : ℕ) : CPoly := ∑ j ∈ Finset.range n, (Polynomial.X : CPoly) ^ j

/-- The monic linear factor `X − a`. -/
def linP (a : ℂ) : CPoly := (Polynomial.X : CPoly) - Polynomial.C a

/-- The product of linear factors `∏ (X − r i)`. -/
def prodLin {ι : Type*} (s : Finset ι) (r : ι → ℂ) : CPoly := ∏ i ∈ s, linP (r i)

lemma geomPoly_succ (n : ℕ) :
    geomPoly (n + 1) = geomPoly n + (Polynomial.X : CPoly) ^ n := by
  simp [geomPoly, Finset.sum_range_succ]

lemma geomPoly_mul_X_sub_one (n : ℕ) :
    geomPoly n * ((Polynomial.X : CPoly) - 1) = (Polynomial.X : CPoly) ^ n - 1 := by
  induction n with
  | zero => simp [geomPoly]
  | succ n ih => rw [geomPoly_succ, add_mul, ih, pow_succ]; ring

lemma X_sub_one_mul_geomPoly (n : ℕ) :
    ((Polynomial.X : CPoly) - 1) * geomPoly n = (Polynomial.X : CPoly) ^ n - 1 := by
  simpa [mul_comm] using geomPoly_mul_X_sub_one n

lemma geomPoly_eval_one (n : ℕ) : (geomPoly n).eval (1 : ℂ) = (n : ℂ) := by
  induction n with
  | zero => simp [geomPoly]
  | succ n ih => rw [geomPoly_succ, Polynomial.eval_add, ih]; simp

lemma derivative_X_pow_eval_one (n : ℕ) :
    (((Polynomial.X : CPoly) ^ n).derivative).eval (1 : ℂ) = (n : ℂ) := by
  cases n with
  | zero => simp
  | succ n => simp [Polynomial.derivative_X_pow]

lemma second_derivative_X_pow_eval_one (n : ℕ) :
    ((((Polynomial.X : CPoly) ^ n).derivative).derivative).eval (1 : ℂ)
      = (n : ℂ) * ((n : ℂ) - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n => simp [Polynomial.derivative_X_pow]

/-- `P'(1) = n(n−1)/2` for `P = geomPoly n` (the `Σ j` moment). -/
lemma geomPoly_derivative_eval_one (n : ℕ) :
    (geomPoly n).derivative.eval (1 : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  induction n with
  | zero => simp [geomPoly]
  | succ n ih =>
    rw [geomPoly_succ, Polynomial.derivative_add, Polynomial.eval_add, ih,
      derivative_X_pow_eval_one n]
    push_cast; ring

/-- `P''(1) = n(n−1)(n−2)/3` for `P = geomPoly n` (the `Σ j(j−1)` moment). -/
lemma geomPoly_second_derivative_eval_one (n : ℕ) :
    ((geomPoly n).derivative.derivative).eval (1 : ℂ)
      = (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2) / 3 := by
  induction n with
  | zero => simp [geomPoly]
  | succ n ih =>
    rw [geomPoly_succ, Polynomial.derivative_add, Polynomial.derivative_add,
      Polynomial.eval_add, ih, second_derivative_X_pow_eval_one n]
    push_cast; ring

lemma prodLin_eval {ι : Type*} (s : Finset ι) (r : ι → ℂ) (x : ℂ) :
    (prodLin s r).eval x = ∏ i ∈ s, (x - r i) := by
  simp [prodLin, linP, Polynomial.eval_prod]

/-- `P'(x) = P(x) · Σ_i 1/(x − r_i)` for `P = ∏(X − r_i)` (log-derivative, product form). -/
lemma eval_derivative_prodLin {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℂ) (x : ℂ) (hx : ∀ i ∈ s, x - r i ≠ 0) :
    ((prodLin s r).derivative).eval x
      = (∏ i ∈ s, (x - r i)) * (∑ i ∈ s, 1 / (x - r i)) := by
  classical
  revert hx
  refine s.induction_on ?_ ?_
  · intro _; simp [prodLin]
  · intro a s ha ih hx
    have hxa : x - r a ≠ 0 := hx a (by simp [ha])
    have hxs : ∀ i ∈ s, x - r i ≠ 0 := fun i hi => hx i (by simp [hi])
    have ih' := ih hxs
    have hprod : prodLin (insert a s) r = linP (r a) * prodLin s r := by
      simp [prodLin, ha]
    rw [hprod]
    simp only [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      linP, Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
      sub_zero, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, one_mul, ih',
      prodLin_eval, Finset.prod_insert ha, Finset.sum_insert ha]
    field_simp

/-- `P''(x) = P(x)·[(Σ 1/(x−r))² − Σ 1/(x−r)²]` for `P = ∏(X − r_i)`. -/
lemma eval_second_derivative_prodLin {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℂ) (x : ℂ) (hx : ∀ i ∈ s, x - r i ≠ 0) :
    ((prodLin s r).derivative.derivative).eval x
      = (∏ i ∈ s, (x - r i))
        * ((∑ i ∈ s, 1 / (x - r i)) ^ 2 - ∑ i ∈ s, (1 / (x - r i)) ^ 2) := by
  classical
  revert hx
  refine s.induction_on ?_ ?_
  · intro _; simp [prodLin]
  · intro a s ha ih hx
    have hxa : x - r a ≠ 0 := hx a (by simp [ha])
    have hxs : ∀ i ∈ s, x - r i ≠ 0 := fun i hi => hx i (by simp [hi])
    have ih1 := eval_derivative_prodLin s r x hxs
    have ih2 := ih hxs
    have hprod : prodLin (insert a s) r = linP (r a) * prodLin s r := by
      simp [prodLin, ha]
    rw [hprod]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.eval_add,
      Polynomial.eval_mul, linP, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, Polynomial.derivative_zero, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, one_mul, zero_mul, mul_zero, add_zero, zero_add,
      ih1, ih2, prodLin_eval, Finset.prod_insert ha, Finset.sum_insert ha]
    field_simp
    ring

/-- **A = Σ 1/(1 − r_k) = (n−1)/2**, whenever the roots factor `geomPoly n`. -/
theorem sum_inv_one_sub_of_prod_eq_geom (n : ℕ) (hn : 0 < n) (r : ℕ → ℂ)
    (hprod : prodLin (Finset.Icc 1 (n - 1)) r = geomPoly n)
    (hden : ∀ k ∈ Finset.Icc 1 (n - 1), 1 - r k ≠ 0) :
    (∑ k ∈ Finset.Icc 1 (n - 1), 1 / (1 - r k)) = ((n : ℂ) - 1) / 2 := by
  classical
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hP1 : (∏ k ∈ Finset.Icc 1 (n - 1), (1 - r k)) = (n : ℂ) := by
    have h := congrArg (fun p : CPoly => p.eval (1 : ℂ)) hprod
    simp only [prodLin, linP, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, geomPoly_eval_one] at h
    exact h
  have hD1 := eval_derivative_prodLin (Finset.Icc 1 (n - 1)) r (1 : ℂ) hden
  rw [hprod, geomPoly_derivative_eval_one n, hP1] at hD1
  apply mul_left_cancel₀ hnC
  rw [← hD1]; ring

/-- **B = Σ 1/(1 − r_k)² = (n−1)(5−n)/12**, whenever the roots factor `geomPoly n`.
    (`B = A² − P''(1)/P(1) = (n−1)²/4 − (n−1)(n−2)/3`.) -/
theorem sum_inv_one_sub_sq_of_prod_eq_geom (n : ℕ) (hn : 0 < n) (r : ℕ → ℂ)
    (hprod : prodLin (Finset.Icc 1 (n - 1)) r = geomPoly n)
    (hden : ∀ k ∈ Finset.Icc 1 (n - 1), 1 - r k ≠ 0) :
    (∑ k ∈ Finset.Icc 1 (n - 1), (1 / (1 - r k)) ^ 2)
      = (((n : ℂ) - 1) * ((5 : ℂ) - (n : ℂ))) / 12 := by
  classical
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hP1 : (∏ k ∈ Finset.Icc 1 (n - 1), (1 - r k)) = (n : ℂ) := by
    have h := congrArg (fun p : CPoly => p.eval (1 : ℂ)) hprod
    simp only [prodLin, linP, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, geomPoly_eval_one] at h
    exact h
  have hD1 := eval_derivative_prodLin (Finset.Icc 1 (n - 1)) r (1 : ℂ) hden
  rw [hprod, geomPoly_derivative_eval_one n, hP1] at hD1
  have hAval : (∑ k ∈ Finset.Icc 1 (n - 1), 1 / (1 - r k)) = ((n : ℂ) - 1) / 2 := by
    apply mul_left_cancel₀ hnC
    rw [← hD1]; ring
  have hD2 := eval_second_derivative_prodLin (Finset.Icc 1 (n - 1)) r (1 : ℂ) hden
  rw [hprod, geomPoly_second_derivative_eval_one n, hP1, hAval] at hD2
  apply mul_left_cancel₀ hnC
  linear_combination hD2

/-- `∏_{k<n} (X − ζᵏ) = Xⁿ − 1` for a primitive `n`-th root `ζ` (reindexing the
    roots-of-unity factorization `X_pow_sub_one_eq_prod`). -/
lemma prod_range_X_sub_C_pow {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    ∏ k ∈ Finset.range n, ((Polynomial.X : CPoly) - Polynomial.C (ζ ^ k))
      = (Polynomial.X : CPoly) ^ n - 1 := by
  classical
  have himg : Polynomial.nthRootsFinset n (1 : ℂ)
      = (Finset.range n).image (fun k => ζ ^ k) := by
    ext μ
    rw [Polynomial.mem_nthRootsFinset hn, Finset.mem_image]
    constructor
    · intro hμ
      haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
      exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
    · rintro ⟨k, _, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [X_pow_sub_one_eq_prod hn hζ, himg,
    Finset.prod_image (fun a ha b hb h =>
      hζ.injOn_pow (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h)]

/-- The roots `ζᵏ`, `1 ≤ k ≤ n−1`, factor `geomPoly n`. -/
lemma prodLin_powers_eq_geomPoly {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    prodLin (Finset.Icc 1 (n - 1)) (fun k => ζ ^ k) = geomPoly n := by
  classical
  have hrange : Finset.range n = insert 0 (Finset.Icc 1 (n - 1)) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hsplit : ((Polynomial.X : CPoly) - 1) * prodLin (Finset.Icc 1 (n - 1)) (fun k => ζ ^ k)
      = (Polynomial.X : CPoly) ^ n - 1 := by
    have h := prod_range_X_sub_C_pow hn hζ
    rw [hrange, Finset.prod_insert (by simp)] at h
    simpa [prodLin, linP, pow_zero, Polynomial.C_1] using h
  have hgeom := X_sub_one_mul_geomPoly n
  have hXne : ((Polynomial.X : CPoly) - 1) ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : CPoly => p.eval (0 : ℂ)) h
    norm_num at h0
  apply mul_left_cancel₀ hXne
  rw [hsplit, hgeom]

lemma one_sub_pow_ne_zero {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 (n - 1)) : 1 - ζ ^ k ≠ 0 := by
  rw [Finset.mem_Icc] at hk
  have hne : ζ ^ k ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  exact sub_ne_zero.mpr (Ne.symm hne)

/-- **A for the primitive root**: `Σ_{k=1}^{n-1} 1/(1 − ζᵏ) = (n−1)/2`. -/
theorem primitive_A {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    (∑ k ∈ Finset.Icc 1 (n - 1), 1 / (1 - ζ ^ k)) = ((n : ℂ) - 1) / 2 :=
  sum_inv_one_sub_of_prod_eq_geom n hn (fun k => ζ ^ k)
    (prodLin_powers_eq_geomPoly hn hζ) (fun k hk => one_sub_pow_ne_zero hζ hk)

/-- **B for the primitive root**: `Σ_{k=1}^{n-1} 1/(1 − ζᵏ)² = (n−1)(5−n)/12`. -/
theorem primitive_B {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    (∑ k ∈ Finset.Icc 1 (n - 1), (1 / (1 - ζ ^ k)) ^ 2)
      = (((n : ℂ) - 1) * ((5 : ℂ) - (n : ℂ))) / 12 :=
  sum_inv_one_sub_sq_of_prod_eq_geom n hn (fun k => ζ ^ k)
    (prodLin_powers_eq_geomPoly hn hζ) (fun k hk => one_sub_pow_ne_zero hζ hk)

/-! ### The real bridge — `|1 − e^{iθ}|² = 4 sin²(θ/2)` and the unit-circle identity -/

/-- `|1 − e^{iθ}|² = 4 sin²(θ/2)`. -/
lemma normSq_one_sub_exp (θ : ℝ) :
    Complex.normSq (1 - Complex.exp ((θ : ℂ) * Complex.I)) = 4 * Real.sin (θ / 2) ^ 2 := by
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 : (2 : ℝ) * (θ / 2) = θ := by ring
    have hcm := Real.cos_two_mul (θ / 2)
    rw [h2] at hcm
    have hp := Real.sin_sq_add_cos_sq (θ / 2)
    nlinarith [hcm, hp]
  nlinarith [hpyth, hc]

/-- For `|w| = 1` and `w ≠ 1`: `1/|1−w|² = 1/(1−w) − (1/(1−w))²` (complex). -/
lemma inv_normSq_eq (w : ℂ) (hw : Complex.normSq w = 1) (hw1 : w ≠ 1) :
    (1 : ℂ) / (Complex.normSq (1 - w) : ℂ) = 1 / (1 - w) - (1 / (1 - w)) ^ 2 := by
  have hw0 : w ≠ 0 := by rintro rfl; simp [Complex.normSq_zero] at hw
  have h1w : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hmul : w * (starRingEnd ℂ) w = 1 := by rw [Complex.mul_conj, hw]; norm_num
  have hconj : (starRingEnd ℂ) w = w⁻¹ := by
    field_simp
    linear_combination hmul
  have hiw : (1 : ℂ) - w⁻¹ ≠ 0 :=
    sub_ne_zero.mpr (fun h => hw1 (inv_eq_one.mp h.symm))
  have hwm1 : (w - 1) ≠ (0 : ℂ) := sub_ne_zero.mpr hw1
  have hns : ((Complex.normSq (1 - w) : ℝ) : ℂ) = (1 - w) * (1 - w⁻¹) := by
    rw [← Complex.mul_conj (1 - w), map_sub, map_one, hconj]
  rw [hns]
  field_simp
  ring

/-- **★ THE COSECANT SUM** (a Mathlib-first): `Σ_{k=1}^{n-1} 1/(4 sin²(πk/n)) = (n²−1)/12`.
    Proved from the primitive-root power sums `A − B = (n−1)/2 − (n−1)(5−n)/12 = (n²−1)/12`
    via the unit-circle bridge `1/|1−ζᵏ|² = 1/(1−ζᵏ) − 1/(1−ζᵏ)²`. -/
theorem sum_inv_four_sin_sq (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc 1 (n - 1), 1 / (4 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ)) ^ 2))
      = ((n : ℝ) ^ 2 - 1) / 12 := by
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) with hζeq
  have hζ : IsPrimitiveRoot ζ n := by rw [hζeq]; exact Complex.isPrimitiveRoot_exp n hn.ne'
  -- the images `ζᵏ = e^{i·2πk/n}`
  have hpow : ∀ k : ℕ,
      ζ ^ k = Complex.exp (((2 * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    intro k
    rw [show (((2 * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I)
          = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) by push_cast; ring,
      Complex.exp_nat_mul, ← hζeq]
  have hnormSq1 : ∀ k : ℕ, Complex.normSq (ζ ^ k) = 1 := by
    intro k
    rw [hpow k, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    linear_combination Real.sin_sq_add_cos_sq (2 * Real.pi * (k : ℝ) / (n : ℝ))
  have hnormSq_sub : ∀ k : ℕ,
      Complex.normSq (1 - ζ ^ k) = 4 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ)) ^ 2 := by
    intro k
    rw [hpow k, normSq_one_sub_exp,
      show (2 * Real.pi * (k : ℝ) / (n : ℝ)) / 2 = Real.pi * (k : ℝ) / (n : ℝ) by ring]
  have hne : ∀ k ∈ Finset.Icc 1 (n - 1), ζ ^ k ≠ 1 :=
    fun k hk => (sub_ne_zero.mp (one_sub_pow_ne_zero hζ hk)).symm
  -- the complex sum `Σ 1/|1−ζᵏ|² = A − B = (n²−1)/12`
  have hCsum : (∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℂ) / (Complex.normSq (1 - ζ ^ k) : ℂ))
      = ((n : ℂ) ^ 2 - 1) / 12 := by
    rw [Finset.sum_congr rfl
        (fun k hk => inv_normSq_eq (ζ ^ k) (hnormSq1 k) (hne k hk)),
      Finset.sum_sub_distrib, primitive_A hn hζ, primitive_B hn hζ]
    ring
  -- coerce: the complex sum is the real sum, cast to `ℂ`
  have hLreal : (∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℂ) / (Complex.normSq (1 - ζ ^ k) : ℂ))
      = ((∑ k ∈ Finset.Icc 1 (n - 1),
          1 / (4 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ)) ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hnormSq_sub k, Complex.ofReal_div, Complex.ofReal_one]
  have hcombine :
      ((∑ k ∈ Finset.Icc 1 (n - 1),
          1 / (4 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ)) ^ 2) : ℝ) : ℂ)
        = (((n : ℝ) ^ 2 - 1) / 12 : ℝ) := by
    rw [← hLreal, hCsum]; push_cast; ring
  exact_mod_cast hcombine

/-- **The `csc²` form**: `Σ_{k=1}^{n-1} 1/sin²(πk/n) = (n²−1)/3`. -/
theorem sum_csc_sq (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc 1 (n - 1), 1 / Real.sin (Real.pi * (k : ℝ) / (n : ℝ)) ^ 2)
      = ((n : ℝ) ^ 2 - 1) / 3 := by
  have h := sum_inv_four_sin_sq n hn
  have hscale : (∑ k ∈ Finset.Icc 1 (n - 1),
        1 / (4 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ)) ^ 2))
      = (1 / 4) * ∑ k ∈ Finset.Icc 1 (n - 1),
        1 / Real.sin (Real.pi * (k : ℝ) / (n : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [hscale] at h
  linarith [h]

/-! ### PART B — the Gaussian rotation integral -/

/-- Planar rotation by angle `θ` on `ℝ × ℝ`. -/
def rot2 (θ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos θ * x.1 - Real.sin θ * x.2, Real.sin θ * x.1 + Real.cos θ * x.2)

/-- Squared Euclidean distance on `ℝ × ℝ`. -/
def distSq2 (x y : ℝ × ℝ) : ℝ := (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

/-- `|x − R_θ x|² = 4 sin²(θ/2)·|x|²` — pure trigonometry. -/
lemma distSq2_rot2 (θ : ℝ) (x : ℝ × ℝ) :
    distSq2 x (rot2 θ x) = 4 * Real.sin (θ / 2) ^ 2 * (x.1 ^ 2 + x.2 ^ 2) := by
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 : (2 : ℝ) * (θ / 2) = θ := by ring
    have hcm := Real.cos_two_mul (θ / 2)
    rw [h2] at hcm
    have hp := Real.sin_sq_add_cos_sq (θ / 2)
    nlinarith [hcm, hp]
  simp only [distSq2, rot2]
  linear_combination (x.1 ^ 2 + x.2 ^ 2) * Real.sin_sq_add_cos_sq θ
    + (x.1 ^ 2 + x.2 ^ 2) * (-2) * hcos

/-- The isotropic 2-D Gaussian integral `∫_{ℝ²} e^{−c|x|²} = π/c` (Fubini + `integral_gaussian`). -/
lemma integral_exp_neg_mul_sqnorm2 {c : ℝ} (hc : 0 < c) :
    ∫ x : ℝ × ℝ, Real.exp (-(c * (x.1 ^ 2 + x.2 ^ 2))) = Real.pi / c := by
  have hfun : (fun x : ℝ × ℝ => Real.exp (-(c * (x.1 ^ 2 + x.2 ^ 2))))
      = fun x : ℝ × ℝ => Real.exp (-c * x.1 ^ 2) * Real.exp (-c * x.2 ^ 2) := by
    funext x; rw [← Real.exp_add]; congr 1; ring
  rw [hfun, Measure.volume_eq_prod,
    integral_prod_mul (fun y : ℝ => Real.exp (-c * y ^ 2)) (fun y : ℝ => Real.exp (-c * y ^ 2)),
    integral_gaussian, Real.mul_self_sqrt (le_of_lt (div_pos Real.pi_pos hc))]

/-- **★ THE ROTATION HEAT-KERNEL PLANE INTEGRAL** — `t`-INDEPENDENT:
    `∫_{ℝ²} (4πt)⁻¹ e^{−|x−R_θ x|²/4t} dx = 1/(4 sin²(θ/2))`. -/
lemma integral_Kplane_rot {t θ : ℝ} (ht : 0 < t) (hs : Real.sin (θ / 2) ≠ 0) :
    ∫ x : ℝ × ℝ, (4 * Real.pi * t)⁻¹ * Real.exp (-distSq2 x (rot2 θ x) / (4 * t))
      = 1 / (4 * Real.sin (θ / 2) ^ 2) := by
  have hs2 : (0 : ℝ) < Real.sin (θ / 2) ^ 2 := by positivity
  have hc : (0 : ℝ) < Real.sin (θ / 2) ^ 2 / t := div_pos hs2 ht
  have hint : (fun x : ℝ × ℝ =>
        (4 * Real.pi * t)⁻¹ * Real.exp (-distSq2 x (rot2 θ x) / (4 * t)))
      = fun x : ℝ × ℝ =>
        (4 * Real.pi * t)⁻¹ * Real.exp (-(Real.sin (θ / 2) ^ 2 / t * (x.1 ^ 2 + x.2 ^ 2))) := by
    funext x
    rw [distSq2_rot2]
    congr 2
    field_simp
  rw [hint, integral_const_mul, integral_exp_neg_mul_sqnorm2 hc]
  have hπ := Real.pi_pos
  field_simp

/-! ### PART C — the ℤ_n orbifold cone excess and the replica coefficient -/

/-- **The ℤ_n orbifold cone EXCESS** — the `1/n`-normalized `k ≥ 1` image sum on `ℝ²/ℤ_n`.
    The `k = 0` (area) term `A/(4πt)` is removed by construction; the `1/n` is the orbifold
    volume factor. -/
def zmodConeExcess (n : ℕ) (t : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 (n - 1),
    ∫ x : ℝ × ℝ, (4 * Real.pi * t)⁻¹ *
      Real.exp (-distSq2 x (rot2 (2 * Real.pi * (k : ℝ) / (n : ℝ)) x) / (4 * t))

/-- **★★ THE EXACT CONE EXCESS** — `zmodConeExcess n t = (n²−1)/(12n)`, for EVERY `t > 0`.
    Termwise the image integral is the `t`-independent `1/(4 sin²(πk/n))`
    (`integral_Kplane_rot`, since `sin((2πk/n)/2) = sin(πk/n) ≠ 0` for `1 ≤ k ≤ n−1`), and
    the cosecant sum `sum_inv_four_sin_sq` closes it. -/
theorem zmodConeExcess_eq (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    zmodConeExcess n t = ((n : ℝ) ^ 2 - 1) / (12 * n) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hterm : ∀ k ∈ Finset.Icc 1 (n - 1),
      (∫ x : ℝ × ℝ, (4 * Real.pi * t)⁻¹ *
        Real.exp (-distSq2 x (rot2 (2 * Real.pi * (k : ℝ) / (n : ℝ)) x) / (4 * t)))
        = 1 / (4 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ)) ^ 2) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hkn : (k : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : k < n)
    have hsinpos : 0 < Real.sin (Real.pi * (k : ℝ) / (n : ℝ)) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
        nlinarith [Real.pi_pos]
    have hsin : Real.sin ((2 * Real.pi * (k : ℝ) / (n : ℝ)) / 2) ≠ 0 := by
      rw [show (2 * Real.pi * (k : ℝ) / (n : ℝ)) / 2 = Real.pi * (k : ℝ) / (n : ℝ) by ring]
      exact ne_of_gt hsinpos
    rw [integral_Kplane_rot ht hsin,
      show (2 * Real.pi * (k : ℝ) / (n : ℝ)) / 2 = Real.pi * (k : ℝ) / (n : ℝ) by ring]
  rw [zmodConeExcess, Finset.sum_congr rfl hterm, sum_inv_four_sin_sq n hn]
  field_simp

/-- **The standard form** `zmodConeExcess n t = (1/12)(n − 1/n)`. -/
theorem zmodConeExcess_eq_standard (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    zmodConeExcess n t = (1 / 12) * ((n : ℝ) - (n : ℝ)⁻¹) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [zmodConeExcess_eq n hn t ht]
  field_simp

/-- **The replica (conical/entanglement) coefficient** `coneCoeff ν = (1/12)(ν − ν⁻¹)`. -/
def coneCoeff (ν : ℝ) : ℝ := (1 / 12) * (ν - ν⁻¹)

/-- Integer agreement: `coneCoeff n = zmodConeExcess n t` for every `t > 0`. -/
theorem coneCoeff_nat {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    coneCoeff (n : ℝ) = zmodConeExcess n t := by
  rw [coneCoeff, zmodConeExcess_eq_standard n hn t ht]

/-- **★ THE REPLICA DERIVATIVE** `d/dν coneCoeff|_{ν=1} = 1/6` — the `c/6 = 1/6`
    (central charge `c = 1`) entanglement coefficient, as the replica derivative at `1` of
    the exactly computed integer-cone excess. -/
theorem hasDerivAt_coneCoeff_one : HasDerivAt coneCoeff (1 / 6) 1 := by
  have h : HasDerivAt (fun ν : ℝ => (1 / 12) * (ν - ν⁻¹))
      ((1 / 12) * (1 - -((1 : ℝ) ^ 2)⁻¹)) 1 :=
    ((hasDerivAt_id (1 : ℝ)).sub (hasDerivAt_inv one_ne_zero)).const_mul (1 / 12)
  have hval : (1 / 12 : ℝ) * (1 - -((1 : ℝ) ^ 2)⁻¹) = 1 / 6 := by norm_num
  rw [hval] at h
  exact h

/-- **★★ THE CAPSTONE — `conical_excess_exact`** (brick D3c of the duality campaign).

    For every `n ≥ 1`:
    1. **the exact standard-form excess, `t`-independent** — for every `t > 0`,
       `zmodConeExcess n t = (1/12)(n − 1/n)` (the `t` in the prefactor and in the Gaussian
       width cancel: UV-finiteness after area subtraction, PROVED);
    2. **the integer agreement** — the interpolating replica coefficient `coneCoeff n`
       equals the machine-checked integer-cone excess `zmodConeExcess n t` (every `t > 0`);
    3. **the replica derivative** — `d/dν coneCoeff|_{ν=1} = 1/6`, the `c/6` entanglement
       coefficient (`c = 1`).

    The conical leg of the DY7 conjecture
    (`QIQTH.Conjectures.FlatSpaceRecordGravityCorrespondence`) now exists at the integer-cone
    level: the exact `ℤ_n` orbifold excess and its replica coefficient are machine-checked.

    FIREWALL: integer cones only; general-angle Sommerfeld, the `n → 1` continuation itself,
    the one-loop determinant/regularization, and the coupling to `A/4G` are CITED — see the
    header. -/
theorem conical_excess_exact (n : ℕ) (hn : 0 < n) :
    (∀ t : ℝ, 0 < t → zmodConeExcess n t = (1 / 12) * ((n : ℝ) - (n : ℝ)⁻¹))
    ∧ (∀ t : ℝ, 0 < t → coneCoeff (n : ℝ) = zmodConeExcess n t)
    ∧ HasDerivAt coneCoeff (1 / 6) 1 :=
  ⟨fun t ht => zmodConeExcess_eq_standard n hn t ht,
    fun _t ht => coneCoeff_nat hn ht,
    hasDerivAt_coneCoeff_one⟩

end QIQTH.ConicalHeatKernel
