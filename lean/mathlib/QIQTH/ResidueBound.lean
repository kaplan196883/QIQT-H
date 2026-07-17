/-
  ResidueBound — Phase J5-resbound of the Jacobi/van-Vleck campaign
  (docs/qg_roadmap/JACOBI_VANVLECK_PLAN.md).

  WHAT IS BUILT HERE (the honest boundary — read it).
  J5-offdiag (`HeatResidualBound.parametrixResidual_offdiag_absorbed`) reduced the RNC off-diagonal
  heat-parametrix residual to two decaying residues:
    (IV) the metric-deviation cross term  `Σᵢⱼ (gⁱʲ − δⁱʲ)((∂ᵢG)(∂ⱼw) + …)`  with `gⁱʲ − δⁱʲ = O(r²)`;
    (Γ)  the Christoffel term with `Γ = O(r)`.
  This file turns those DECOMPOSITIONS into actual GAUSSIAN DECAY BOUNDS: a single residue summand is
  `≤ C · t^{power} · G_wide`, where `G_wide` is the widened `d`-dimensional Gaussian.  The mechanism is
  the C4a polynomial-absorption bound `gaussian_poly_absorb` combined with the Gaussian gradient
  `∂ᵢG = (−vⁱ/2t)G` (`gaussDdim_pd_eq`), lifted from the 1-D scalar `x` to the Euclidean RNC radial
  coordinate `r = rncRadial v` via `(rncRadial v)² = rncRadialSq v = Σ(vⁱ)²`.

  Deliverables:
    • `gaussDdimWide`, `gaussDdim_eq_exp` — the `d`-dim Gaussian in closed exp form and its widened
      (exponent `−r²/8t`) partner;
    • `rncRadialSq_pow_mul_gaussDdim_le` — THE CORE even absorption:
        `(rncRadialSq v)^m · G ≤ (8^m m!) · t^m · G_wide`  (`r^{2m}·G` → `t^m` Gaussian, C4a);
    • `rncRadialCubed_mul_gaussDdim_le` — the odd `r³` absorption (√t honestly, via squaring — no rpow):
        `(rncRadial v)³ · G ≤ √3072 · t√t · G_wide`;
    • `abs_coord_le_rncRadial` — `|vⁱ| ≤ rncRadial v`;
    • `residue_christoffel_bound` — the Γ residue summand `|Γ · ∂ᵢG · w|` bounded by `4MW · G_wide`
      (`r · (r/t)G · W = (r²/t)G` → constant Gaussian);
    • `residue_metricdev_bound` — the metric-deviation residue summand `|d · ∂ᵢG · ∂ⱼw|` bounded by
      `(√3072·MW/2) · √t · G_wide` (`r² · (r/t)G · W = (r³/t)G` → `√t` Gaussian);
    • `residue_pair_bound` — the two summands combined: `≤ (4MW + (√3072·M'W'/2)√t) · G_wide`.

  ⚠ HONEST SCOPE (binding).  This is the residue DECAY BOUND, carrying the `O(r^m)` decay of the metric
  fields as EXPLICIT hypotheses (`hddecay`, `hΓdecay` — sourced abstractly from J5-residue's
  `decay_order_*_radial` applied to the concrete metric jet, which is a SEPARATE downstream wiring
  brick — the concrete `PullbackMetric` jet sourcing is NOT done here).  It is NOT the concrete
  residual bound for the actual pullback metric, NOT the full multi-index `Σᵢⱼ` assembly, NOT
  `a₁ = R/6`.  The decay / gradient-bound / `t > 0` hypotheses are genuine, load-bearing, non-vacuous
  (the bound FAILS without the decay — a generic residue is not Gaussian-controlled).  No axioms, no
  `sorry`.
-/
import Mathlib
import QIQTH.RNCDecay
import QIQTH.GaussianPolyBound
import QIQTH.RadialDistance
import QIQTH.HeatResidualBound

open QIQTH.RNCDecay QIQTH.GaussianPolyBound QIQTH.RadialDistance MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatKernelA1 QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.ResidueBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### #0 — the `d`-dimensional Gaussian in closed exponential form and its widened partner. -/

/-- **The widened `d`-dimensional Gaussian** `G_wide(t,v) = (√(4πt))⁻ⁿ · exp(−r²/(8t))`, with the same
    normalization prefactor as `gaussDdim` but the WIDER exponent `−r²/(8t)` (`r² = rncRadialSq v`).
    This is the Gaussian into which the C4a absorption deposits the polynomial factors. -/
noncomputable def gaussDdimWide (t : ℝ) (v : Point n) : ℝ :=
  ((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n * Real.exp (-(rncRadialSq v) / (8 * t))

/-- **The `d`-dim Gaussian in closed exp form** `gaussDdim t v = (√(4πt))⁻ⁿ · exp(−r²/(4t))`, where
    `r² = rncRadialSq v = Σ(vⁱ)²`.  The product `∏ₖ heatKernel1D t (vᵏ)` factors: the `n` copies of the
    prefactor collect to the `n`-th power, and `∏ₖ exp(−(vᵏ)²/4t) = exp(−Σ(vᵏ)²/4t)`. -/
theorem gaussDdim_eq_exp (t : ℝ) (v : Point n) :
    gaussDdim t v
      = ((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n
        * Real.exp (-(rncRadialSq v) / (4 * t)) := by
  have hsum : (∑ k : Fin n, -(v k) ^ 2 / (4 * t)) = -(rncRadialSq v) / (4 * t) := by
    have hterm : ∀ k : Fin n, -(v k) ^ 2 / (4 * t) = (-(4 * t)⁻¹) * (v k) ^ 2 := by
      intro k; ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, rncRadialSq]
    ring
  simp only [gaussDdim, heatKernel1D]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, hsum]

/-- `gaussDdim ≥ 0`: a product of nonnegative 1-D kernels. -/
theorem gaussDdim_nonneg (t : ℝ) (v : Point n) : 0 ≤ gaussDdim t v := by
  rw [gaussDdim]
  exact Finset.prod_nonneg (fun k _ => by rw [heatKernel1D]; positivity)

/-- `G_wide ≥ 0`. -/
theorem gaussDdimWide_nonneg (t : ℝ) (v : Point n) : 0 ≤ gaussDdimWide t v := by
  rw [gaussDdimWide]; positivity

/-! ### #1 — the coordinate bound `|vⁱ| ≤ rncRadial v`. -/

/-- **The single-coordinate bound** `|vⁱ| ≤ rncRadial v`: `(vⁱ)² ≤ Σⱼ(vʲ)² = r²`, then `√`-monotone. -/
theorem abs_coord_le_rncRadial (v : Point n) (i : Fin n) : |v i| ≤ rncRadial v := by
  rw [← Real.sqrt_sq_eq_abs, rncRadial]
  apply Real.sqrt_le_sqrt
  rw [rncRadialSq]
  exact Finset.single_le_sum (f := fun j => (v j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-! ### #2 — THE CORE even absorption `r^{2m}·G ≤ C·t^m·G_wide`. -/

/-- **THE CORE POLYNOMIAL-ABSORPTION BOUND (even powers).**  For `m : ℕ`, `t > 0`,
      `(rncRadialSq v)^m · gaussDdim t v ≤ (8^m · m!) · t^m · gaussDdimWide t v` .
    I.e. `r^{2m}·e^{−r²/4t}` is absorbed into `t^m·e^{−r²/8t}`.  This is `gaussian_poly_absorb`
    (C4a) applied with the scalar `x = rncRadial v` (so `x² = rncRadialSq v`), lifting the 1-D
    absorption to the multidimensional radial coordinate, then multiplying by the common nonnegative
    prefactor `(√(4πt))⁻ⁿ`. -/
theorem rncRadialSq_pow_mul_gaussDdim_le (m : ℕ) {t : ℝ} (ht : 0 < t) (v : Point n) :
    (rncRadialSq v) ^ m * gaussDdim t v
      ≤ (8 ^ m * (m.factorial : ℝ)) * t ^ m * gaussDdimWide t v := by
  have hkey := gaussian_poly_absorb m ht (rncRadial v)
  rw [rncRadial_sq] at hkey
  rw [gaussDdim_eq_exp, gaussDdimWide]
  set A : ℝ := ((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n with hA
  have hAn : (0 : ℝ) ≤ A := by rw [hA]; positivity
  calc (rncRadialSq v) ^ m * (A * Real.exp (-(rncRadialSq v) / (4 * t)))
      = A * ((rncRadialSq v) ^ m * Real.exp (-(rncRadialSq v) / (4 * t))) := by ring
    _ ≤ A * ((8 ^ m * (m.factorial : ℝ)) * t ^ m * Real.exp (-(rncRadialSq v) / (8 * t))) :=
        mul_le_mul_of_nonneg_left hkey hAn
    _ = (8 ^ m * (m.factorial : ℝ)) * t ^ m * (A * Real.exp (-(rncRadialSq v) / (8 * t))) := by ring

/-- **The `m = 1` specialization** `r²·G ≤ 8t·G_wide` — the shape the Christoffel residue consumes. -/
theorem rncRadialSq_mul_gaussDdim_le {t : ℝ} (ht : 0 < t) (v : Point n) :
    (rncRadial v) ^ 2 * gaussDdim t v ≤ 8 * t * gaussDdimWide t v := by
  rw [rncRadial_sq]
  have h1 := rncRadialSq_pow_mul_gaussDdim_le 1 ht v
  simpa [pow_one, Nat.factorial_one] using h1

/-! ### #3 — the odd `r³·G ≤ √3072·t√t·G_wide` absorption (√t honestly, no rpow). -/

/-- **THE ODD `r³` ABSORPTION.**  For `t > 0`,
      `(rncRadial v)³ · gaussDdim t v ≤ √3072 · (t · √t) · gaussDdimWide t v` .
    The odd power of `r` forces a `√t` (as for the 1-D odd first-derivative bound
    `heatKernel1D_deriv_x_abs_le`) — proved by SQUARING, so no `rpow`/fractional power appears: the
    crux `r³·e^{−r²/8t} ≤ √3072·t√t` follows from `(r³·e^{−r²/8t})² = r⁶·e^{−r²/4t} = (r²)³·e^{−r²/4t}
    ≤ 8³·3!·t³·e^{−r²/8t} ≤ 3072·t³` (C4a `m = 3`, and `e^{−r²/8t} ≤ 1`).  Splitting `e^{−r²/4t} =
    e^{−r²/8t}·e^{−r²/8t}` then transfers the bound to the `4t`-Gaussian. -/
theorem rncRadialCubed_mul_gaussDdim_le {t : ℝ} (ht : 0 < t) (v : Point n) :
    (rncRadial v) ^ 3 * gaussDdim t v
      ≤ Real.sqrt 3072 * (t * Real.sqrt t) * gaussDdimWide t v := by
  have htne : t ≠ 0 := ht.ne'
  set r : ℝ := rncRadial v with hr
  set rr : ℝ := rncRadialSq v with hrr
  have hr0 : 0 ≤ r := by rw [hr]; exact rncRadial_nonneg v
  have hrr_eq : r ^ 2 = rr := by rw [hr, hrr]; exact rncRadial_sq v
  -- exp(−rr/4t) = exp(−rr/8t)·exp(−rr/8t)
  have hexp_split : Real.exp (-rr / (4 * t))
      = Real.exp (-rr / (8 * t)) * Real.exp (-rr / (8 * t)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  -- exp(−rr/8t) ≤ 1
  have hle0 : -rr / (8 * t) ≤ 0 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 8 * t)]
    have : 0 ≤ rr := by rw [hrr]; exact rncRadialSq_nonneg v
    nlinarith
  have hexp1 : Real.exp (-rr / (8 * t)) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hle0
  -- C4a (m = 3) at x = r:  (r²)³·exp(−r²/4t) ≤ 8³·3!·t³·exp(−r²/8t)
  have hc4a := gaussian_poly_absorb 3 ht r
  rw [hrr_eq] at hc4a
  -- (r²)³ = rr³, so hc4a : rr³·exp(−rr/4t) ≤ 3072·t³·exp(−rr/8t)
  have hc4a' : rr ^ 3 * Real.exp (-rr / (4 * t)) ≤ 3072 * t ^ 3 * Real.exp (-rr / (8 * t)) := by
    have : (8 : ℝ) ^ 3 * ((3 : ℕ).factorial : ℝ) = 3072 := by norm_num [Nat.factorial]
    rw [this] at hc4a; exact hc4a
  -- the squared crux:  (r³·exp(−rr/8t))² ≤ 3072·t³
  have hsq : (r ^ 3 * Real.exp (-rr / (8 * t))) ^ 2 ≤ 3072 * t ^ 3 := by
    have hexpand : (r ^ 3 * Real.exp (-rr / (8 * t))) ^ 2
        = rr ^ 3 * Real.exp (-rr / (4 * t)) := by
      rw [mul_pow, hexp_split]
      rw [show (r ^ 3) ^ 2 = (r ^ 2) ^ 3 by ring, hrr_eq]
      ring
    calc (r ^ 3 * Real.exp (-rr / (8 * t))) ^ 2
        = rr ^ 3 * Real.exp (-rr / (4 * t)) := hexpand
      _ ≤ 3072 * t ^ 3 * Real.exp (-rr / (8 * t)) := hc4a'
      _ ≤ 3072 * t ^ 3 * 1 := by
          apply mul_le_mul_of_nonneg_left hexp1; positivity
      _ = 3072 * t ^ 3 := by ring
  -- crux:  r³·exp(−rr/8t) ≤ √(3072·t³) = √3072·t√t
  have hcrux : r ^ 3 * Real.exp (-rr / (8 * t)) ≤ Real.sqrt 3072 * (t * Real.sqrt t) := by
    have hlhs0 : 0 ≤ r ^ 3 * Real.exp (-rr / (8 * t)) := by positivity
    rw [show r ^ 3 * Real.exp (-rr / (8 * t))
          = Real.sqrt ((r ^ 3 * Real.exp (-rr / (8 * t))) ^ 2) from
        (Real.sqrt_sq hlhs0).symm]
    calc Real.sqrt ((r ^ 3 * Real.exp (-rr / (8 * t))) ^ 2)
        ≤ Real.sqrt (3072 * t ^ 3) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 3072 * (t * Real.sqrt t) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3072) (t ^ 3),
              show t ^ 3 = t ^ 2 * t from by ring,
              Real.sqrt_mul (by positivity) t, Real.sqrt_sq ht.le]
  -- assemble via the closed exp form
  rw [gaussDdim_eq_exp, gaussDdimWide, ← hrr]
  set A : ℝ := ((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n with hA
  have hAn : (0 : ℝ) ≤ A := by rw [hA]; positivity
  calc r ^ 3 * (A * Real.exp (-rr / (4 * t)))
      = A * (r ^ 3 * (Real.exp (-rr / (8 * t)) * Real.exp (-rr / (8 * t)))) := by
        rw [hexp_split]; ring
    _ = A * ((r ^ 3 * Real.exp (-rr / (8 * t))) * Real.exp (-rr / (8 * t))) := by ring
    _ ≤ A * ((Real.sqrt 3072 * (t * Real.sqrt t)) * Real.exp (-rr / (8 * t))) := by
        apply mul_le_mul_of_nonneg_left _ hAn
        exact mul_le_mul_of_nonneg_right hcrux (Real.exp_pos _).le
    _ = Real.sqrt 3072 * (t * Real.sqrt t) * (A * Real.exp (-rr / (8 * t))) := by ring

/-! ### #4 — the residue decay bounds (abstract in the carried metric decay). -/

/-- A four-factor product monotonicity for nonnegative reals: if each factor increases and all factors
    are nonnegative, the products compare.  (Used to bound the residue summands factor-by-factor.) -/
private theorem prod4_le {a b c d a' b' c' d' : ℝ}
    (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') (h4 : d ≤ d')
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have hab : a * b ≤ a' * b' := mul_le_mul h1 h2 hb ha'
  have habc : a * b * c ≤ a' * b' * c' := mul_le_mul hab h3 hc (mul_nonneg ha' hb')
  exact mul_le_mul habc h4 hd (mul_nonneg (mul_nonneg ha' hb') hc')

/-- **THE CHRISTOFFEL RESIDUE BOUND (Γ term, `O(r)`).**  GIVEN a scalar Christoffel component
    `Γc : Point n → ℝ` carrying the first-order RNC decay `|Γc v| ≤ M · rncRadial v` (from
    `decay_order_one_radial`, `Γ(0) = 0` at an RNC center) and a smooth folded coefficient `w` with
    `|w v| ≤ W`, the residue summand `Γc · ∂ᵢG · w` obeys
      `|Γc v · ∂ᵢG(v) · w v| ≤ 4·M·W · gaussDdimWide t v`   (for `rncRadial v ≤ ρ`).
    MECHANISM: `∂ᵢG = (−vⁱ/2t)G` (`gaussDdim_pd_eq`), so `|Γc·∂ᵢG·w| ≤ (M r)·(r/2t)·G·W = (MW/2t)·r²·G`,
    and `r²·G ≤ 8t·G_wide` (`rncRadialSq_mul_gaussDdim_le`, C4a `m=1`) gives the `t`-free constant
    `4MW`.  The `O(r)` decay `hΓdecay` and the coefficient bound `hwbound` are genuine, load-bearing
    hypotheses. -/
theorem residue_christoffel_bound {t : ℝ} (ht : 0 < t) (M ρ W : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (Γc w : Point n → ℝ) (i : Fin n)
    (hwbound : ∀ v, |w v| ≤ W)
    (hΓdecay : ∀ v, rncRadial v ≤ ρ → |Γc v| ≤ M * rncRadial v)
    {v : Point n} (hv : rncRadial v ≤ ρ) :
    |Γc v * pd (fun y => gaussDdim t y) i v * w v| ≤ 4 * M * W * gaussDdimWide t v := by
  have hG0 : 0 ≤ gaussDdim t v := gaussDdim_nonneg t v
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hc : (0 : ℝ) ≤ M * W / (2 * t) := div_nonneg (mul_nonneg hM hW) h2t.le
  have htne : t ≠ 0 := ht.ne'
  rw [gaussDdim_pd_eq t ht v i]
  calc |Γc v * ((-(v i) / (2 * t)) * gaussDdim t v) * w v|
      = |Γc v| * (|v i| / (2 * t)) * gaussDdim t v * |w v| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hG0, abs_div, abs_neg, abs_of_pos h2t]
        ring
    _ ≤ (M * rncRadial v) * (rncRadial v / (2 * t)) * gaussDdim t v * W := by
        have hr0 : 0 ≤ rncRadial v := rncRadial_nonneg v
        have hdiv : |v i| / (2 * t) ≤ rncRadial v / (2 * t) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (abs_coord_le_rncRadial v i) (by positivity)
        exact prod4_le (hΓdecay v hv) hdiv (le_refl _) (hwbound v)
          (div_nonneg (abs_nonneg _) h2t.le) hG0 (abs_nonneg _)
          (mul_nonneg hM hr0) (div_nonneg hr0 h2t.le) hG0
    _ = (M * W / (2 * t)) * ((rncRadial v) ^ 2 * gaussDdim t v) := by ring
    _ ≤ (M * W / (2 * t)) * (8 * t * gaussDdimWide t v) :=
        mul_le_mul_of_nonneg_left (rncRadialSq_mul_gaussDdim_le ht v) hc
    _ = 4 * M * W * gaussDdimWide t v := by field_simp; ring

/-- **THE METRIC-DEVIATION RESIDUE BOUND (`gⁱʲ − δⁱʲ` cross term, `O(r²)`).**  GIVEN a scalar
    metric-deviation component `d : Point n → ℝ` carrying the second-order RNC decay
    `|d v| ≤ M · (rncRadial v)²` (from `decay_order_two_radial`, `gⁱʲ−δⁱʲ` vanishing to 2nd order at an
    RNC center) and a smooth coefficient `w` whose `j`-th partial is bounded, `|∂ⱼw v| ≤ W`, the
    residue summand `d · ∂ᵢG · ∂ⱼw` obeys
      `|d v · ∂ᵢG(v) · ∂ⱼw(v)| ≤ (√3072·M·W/2) · √t · gaussDdimWide t v`   (for `rncRadial v ≤ ρ`).
    MECHANISM: `∂ᵢG = (−vⁱ/2t)G`, so `|d·∂ᵢG·∂ⱼw| ≤ (M r²)·(r/2t)·G·W = (MW/2t)·r³·G`, and the odd
    `r³·G ≤ √3072·t√t·G_wide` (`rncRadialCubed_mul_gaussDdim_le`) leaves the `√t` prefactor.  The
    `O(r²)` decay `hddecay` and the gradient bound `hgradbound` are genuine, load-bearing hypotheses. -/
theorem residue_metricdev_bound {t : ℝ} (ht : 0 < t) (M ρ W : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (d w : Point n → ℝ) (i j : Fin n)
    (hgradbound : ∀ v, |pd w j v| ≤ W)
    (hddecay : ∀ v, rncRadial v ≤ ρ → |d v| ≤ M * (rncRadial v) ^ 2)
    {v : Point n} (hv : rncRadial v ≤ ρ) :
    |d v * pd (fun y => gaussDdim t y) i v * pd w j v|
      ≤ (Real.sqrt 3072 * M * W / 2) * Real.sqrt t * gaussDdimWide t v := by
  have hG0 : 0 ≤ gaussDdim t v := gaussDdim_nonneg t v
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hc : (0 : ℝ) ≤ M * W / (2 * t) := div_nonneg (mul_nonneg hM hW) h2t.le
  have htne : t ≠ 0 := ht.ne'
  rw [gaussDdim_pd_eq t ht v i]
  calc |d v * ((-(v i) / (2 * t)) * gaussDdim t v) * pd w j v|
      = |d v| * (|v i| / (2 * t)) * gaussDdim t v * |pd w j v| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hG0, abs_div, abs_neg, abs_of_pos h2t]
        ring
    _ ≤ (M * (rncRadial v) ^ 2) * (rncRadial v / (2 * t)) * gaussDdim t v * W := by
        have hr0 : 0 ≤ rncRadial v := rncRadial_nonneg v
        have hdiv : |v i| / (2 * t) ≤ rncRadial v / (2 * t) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (abs_coord_le_rncRadial v i) (by positivity)
        exact prod4_le (hddecay v hv) hdiv (le_refl _) (hgradbound v)
          (div_nonneg (abs_nonneg _) h2t.le) hG0 (abs_nonneg _)
          (mul_nonneg hM (by positivity)) (div_nonneg hr0 h2t.le) hG0
    _ = (M * W / (2 * t)) * ((rncRadial v) ^ 3 * gaussDdim t v) := by ring
    _ ≤ (M * W / (2 * t)) * (Real.sqrt 3072 * (t * Real.sqrt t) * gaussDdimWide t v) :=
        mul_le_mul_of_nonneg_left (rncRadialCubed_mul_gaussDdim_le ht v) hc
    _ = (Real.sqrt 3072 * M * W / 2) * Real.sqrt t * gaussDdimWide t v := by
        field_simp

/-- **THE COMBINED RESIDUE-PAIR BOUND (J5b shape).**  The two residue summands together — a Christoffel
    term (`Γc`, `O(r)`, coefficient `w₁` bounded by `W₁`) plus a metric-deviation term (`d`, `O(r²)`,
    coefficient derivative `∂ⱼw₂` bounded by `W₂`) — are dominated by a single widened Gaussian with an
    explicit `(1 + √t)`-shaped prefactor:
      `|Γc·∂ᵢG·w₁| + |d·∂ᵢ'G·∂ⱼw₂| ≤ (4·M₁·W₁ + (√3072·M₂·W₂/2)·√t) · gaussDdimWide t v` .
    This is the shape the Levi/parametrix machinery (C5c / J5b) consumes: the off-diagonal residual is
    bounded by a Gaussian.  All decay / bound hypotheses are carried and load-bearing. -/
theorem residue_pair_bound {t : ℝ} (ht : 0 < t) (M₁ M₂ ρ W₁ W₂ : ℝ)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂)
    (Γc d w₁ w₂ : Point n → ℝ) (i i' j : Fin n)
    (hw₁bound : ∀ v, |w₁ v| ≤ W₁)
    (hgradbound : ∀ v, |pd w₂ j v| ≤ W₂)
    (hΓdecay : ∀ v, rncRadial v ≤ ρ → |Γc v| ≤ M₁ * rncRadial v)
    (hddecay : ∀ v, rncRadial v ≤ ρ → |d v| ≤ M₂ * (rncRadial v) ^ 2)
    {v : Point n} (hv : rncRadial v ≤ ρ) :
    |Γc v * pd (fun y => gaussDdim t y) i v * w₁ v|
        + |d v * pd (fun y => gaussDdim t y) i' v * pd w₂ j v|
      ≤ (4 * M₁ * W₁ + (Real.sqrt 3072 * M₂ * W₂ / 2) * Real.sqrt t) * gaussDdimWide t v := by
  have h1 := residue_christoffel_bound ht M₁ ρ W₁ hM₁ hW₁ Γc w₁ i hw₁bound hΓdecay hv
  have h2 := residue_metricdev_bound ht M₂ ρ W₂ hM₂ hW₂ d w₂ i' j hgradbound hddecay hv
  calc |Γc v * pd (fun y => gaussDdim t y) i v * w₁ v|
          + |d v * pd (fun y => gaussDdim t y) i' v * pd w₂ j v|
      ≤ 4 * M₁ * W₁ * gaussDdimWide t v
          + (Real.sqrt 3072 * M₂ * W₂ / 2) * Real.sqrt t * gaussDdimWide t v :=
        add_le_add h1 h2
    _ = (4 * M₁ * W₁ + (Real.sqrt 3072 * M₂ * W₂ / 2) * Real.sqrt t) * gaussDdimWide t v := by ring

end QIQTH.ResidueBound
