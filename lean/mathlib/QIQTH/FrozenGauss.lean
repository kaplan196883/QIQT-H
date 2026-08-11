/-
  FrozenGauss — J4-609: the frozen-SPD Gaussian layer (layer 6 of the fat-K (hbound-fat)
  campaign; Sol's forward-route steps 1–3 from the J4-608 route decision).

  THE MATHEMATICS.  The J4-608 gates proved that the raw center gauge cannot supply the fat-K
  Gaussian bound: the ε₀/τ defect of the FLAT principal Gaussian against the curved metric is
  irreducible (a constant metric mismatch at order 0 costs 1/τ on the diagonal).  The classical
  Levi cure is to freeze the metric at the source point `q` and use the CONSTANT-COEFFICIENT
  fundamental solution as the principal term.  For a symmetric positive matrix `A = g(q)` with
  inverse `B = g⁻¹(q)` (the frozen INVERSE metric, the coefficient of the frozen operator), the
  frozen Gaussian is

      Γ_A(τ, v) = (√(4πτ))⁻ⁿ · √(det A) · exp(−Q_A(v)/(4τ)),   Q_A(v) = ∑ᵢⱼ Aᵢⱼ vⁱ vʲ .

  CONVENTION DERIVATION (matched against the repo's flat Gaussian `gaussDdim` and the repo heat
  operator `heatOp g gi K = ∂_τ K − Δ_{g,x} K` of `QIQTH.TrueHeatKernel`): the frozen operator is
  `∑ᵢⱼ Bⁱʲ ∂ᵢ∂ⱼ` with `B = A⁻¹` the frozen inverse metric; the exponent must carry the metric `A`
  ITSELF (not its inverse), because then `∂ᵢ Γ = −(Av)ᵢ/(2τ)·Γ` and
  `∑ᵢⱼ Bⁱʲ ∂ᵢ∂ⱼ Γ = (−tr(BA)/(2τ) + vᵀA(BA)v/(4τ²))·Γ = (−n/(2τ) + Q_A(v)/(4τ²))·Γ = ∂_τ Γ`
  EXACTLY (`frozenGauss_frozen_heat`).  The prefactor power is `det A` to the PLUS one-half: at
  `A = δ` it reduces to `gaussDdim` (`frozenGauss_delta`), and classically it makes
  `∫ Γ_A(τ,·) = 1` (the √det A exactly cancels the (det A)^{−1/2} of the anisotropic Gaussian
  integral — NORMALIZATION NOTED, NOT PROVED HERE; no lemma in this file claims the integral).

  WHAT LANDS (all proved, no sorry):
    • `frozenGauss`, `quadForm` — the definitions; `frozenGauss_delta` /
      `frozenGauss_curvedRNC_center` — collapse to `gaussDdim` at the flat/center matrix.
    • `frozenGauss_pd` / `frozenGauss_pd_pd` — exact first/second coordinate partials (the `pd`
      calculus of `QIQTH.Curvature`).
    • ★ `frozenGauss_frozen_heat` — the EXACT frozen heat cancellation
      `∂_τ Γ_A = ∑ᵢⱼ Bⁱʲ ∂ᵢ(∂ⱼ Γ_A)` for τ>0, for ANY symmetric `A` with left inverse `B`
      (hypotheses componentwise, both discharged for the space form below).
    • ★ `frozenGauss_heatOp_zero` — the SAME cancellation phrased through the repo's OWN operator:
      `heatOp (fun _ => A) (fun _ => B) (fun t x _ => Γ_A(t,x)) = 0` (the Christoffel terms of a
      frozen metric vanish, `christoffel_const`); this pins the convention against `heatOp`'s
      actual derivative form — no sign/index mismatch survives.
    • ★ `frozenGauss_le_gauss` / `gauss_le_frozenGauss` — the two-sided ellipticity comparison:
      `m·‖v‖² ≤ Q_A(v) ≤ M·‖v‖²` gives
      `√det A·(√M)⁻ⁿ·G_{τ/M}(v) ≤ Γ_A(τ,v) ≤ √det A·(√m)⁻ⁿ·G_{τ/m}(v)`
      with EXPLICIT constants (equality of prefactors; the inequality lives in the exponent only).
    • Space-form instantiation `g^K = curvedRNCMetric K` (K ≤ 0):
      `quadForm_curvedRNC_lower/upper` — the eigenvalue bounds `‖v‖² ≤ Q ≤ (1+(−K/3)r²)‖v‖²` on
      `rncRadialSq q ≤ r²` (repo sign convention `g^K = δ − (K/3)(‖q‖²δ − qqᵀ)`: for K ≤ 0 the
      eigenvalues are 1 (radial) and 1+(−K/3)‖q‖² ≥ 1 (tangential) — the metric dominates δ
      GLOBALLY, so NO smallness condition `(|K|/3)r² < 1` is needed on this branch);
      `frozenGauss_comparison_spaceForm` — the assembled two-sided comparison;
      `frozenGauss_frozen_heat_spaceForm` — the cancellation at the genuinely curved witness with
      `B := curvedRNCInv K q` (inverse discharged from the banked exact `curvedRNCMetric_hinvF`).
    • Non-vacuity: `frozenGauss_matrix_ne_delta` — for K ≠ 0, n ≥ 2, q ≠ 0 the frozen matrix is
      NOT δ (some diagonal entry ≠ 1), so the frozen-heat theorem at the space form is exercised
      at a genuinely non-flat frozen point; `frozenGauss_pos` — the kernel is strictly positive.
    • `FrozenDefectBound` — the O(τ^{−1/2}) Lipschitz-defect NEXT-BRICK TARGET (J4-610) as a
      Prop ONLY.  ⚠ NOT PROVED HERE, deliberately: it is the classical Levi defect
      `|∑ᵢⱼ (gⁱʲ(q+v) − gⁱʲ(q)) ∂ᵢ∂ⱼΓ_q| ≤ (C/√τ)·G_{λτ}(v)` (α = −1/2-integrable), the next
      layer of the frozen re-base.

  ⚠ HONEST SCOPE.  This is the frozen-Gaussian FOUNDATION only.  `a₁ = R/6` remains CONDITIONAL:
  the flat tower is non-vacuous and closed, but the curved re-base still owes the τ^{−1/2}
  Lipschitz-defect bound (J4-610), the α-fork (α=−1/2 D2 consumer or per-q first-jet
  cancellation), the per-q re-based producer re-assembly, the fat-K hEmeas/hAdom/hcont piles, the
  capstone co-instantiation, and the prior piles/trio/hmassone-pre-ρ/hjets.  No axioms, no sorry.
-/
import Mathlib
import QIQTH.FlatHeatEquation
import QIQTH.GaussianWidthTransfer
import QIQTH.CurvedRNCPosDef
import QIQTH.TrueHeatKernel

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.TrueHeatKernel QIQTH.LaplaceBeltrami
open scoped Matrix

namespace QIQTH.FrozenGauss

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ### 1. The definitions. -/

/-- **The quadratic form** `Q_A(v) = ∑ᵢⱼ Aᵢⱼ vⁱ vʲ` of a (frozen) coefficient matrix. -/
noncomputable def quadForm (A : Fin n → Fin n → ℝ) (v : Point n) : ℝ :=
  ∑ i, ∑ j, A i j * v i * v j

/-- **The frozen-metric Gaussian** `Γ_A(τ,v) = (√(4πτ))⁻ⁿ · √(det A) · exp(−Q_A(v)/(4τ))`.
    `A` is the frozen METRIC `g(q)` (the exponent carries `g`, the operator carries `g⁻¹`); the
    `(det A)^{+1/2}` prefactor makes `Γ_δ = gaussDdim` and (classically) `∫Γ_A(τ,·) = 1` — the
    normalization value is NOTED here, not proved. -/
noncomputable def frozenGauss (A : Fin n → Fin n → ℝ) (τ : ℝ) (v : Point n) : ℝ :=
  (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.sqrt (Matrix.det A)
    * Real.exp (-quadForm A v / (4 * τ))

/-- `Q_δ(v) = ‖v‖²`: the flat quadratic form is `rncRadialSq`. -/
theorem quadForm_delta (v : Point n) :
    quadForm (fun i j => if i = j then (1 : ℝ) else 0) v = rncRadialSq v := by
  simp only [quadForm, rncRadialSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∀ j : Fin n, (if i = j then (1 : ℝ) else 0) * v i * v j
      = if i = j then v i * v j else 0 := fun j => by by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_ite_eq]
  simp [pow_two]

/-- `det δ = 1` for the componentwise identity matrix. -/
theorem det_delta : Matrix.det (fun i j : Fin n => if i = j then (1 : ℝ) else 0) = 1 := by
  have h1 : (fun i j : Fin n => if i = j then (1 : ℝ) else 0)
      = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext i j; rw [Matrix.one_apply]
  rw [h1, Matrix.det_one]

/-- **The δ-bridge**: at the flat matrix the frozen Gaussian IS the repo's flat Gaussian
    `gaussDdim` (via the banked closed form `gaussDdim_closed`). -/
theorem frozenGauss_delta (τ : ℝ) (v : Point n) :
    frozenGauss (fun i j => if i = j then (1 : ℝ) else 0) τ v = gaussDdim τ v := by
  rw [gaussDdim_closed]
  simp only [frozenGauss]
  rw [quadForm_delta, det_delta, Real.sqrt_one, mul_one]

/-- **The center bridge**: the frozen Gaussian at the space-form CENTER matrix `g^K(0) = δ`
    collapses to `gaussDdim` — the frozen family interpolates the flat principal term. -/
theorem frozenGauss_curvedRNC_center (K τ : ℝ) (v : Point n) :
    frozenGauss (curvedRNCMetric K (0 : Point n)) τ v = gaussDdim τ v := by
  have h : curvedRNCMetric K (0 : Point n) = (fun i j => if i = j then (1 : ℝ) else 0) :=
    funext fun i => funext fun j => curvedRNCMetric_zero K i j
  rw [h]; exact frozenGauss_delta τ v

/-- The frozen Gaussian is strictly positive for `τ > 0` and `det A > 0` (non-degeneracy gate). -/
theorem frozenGauss_pos (A : Fin n → Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hdet : 0 < Matrix.det A) (v : Point n) : 0 < frozenGauss A τ v := by
  have h1 : (0 : ℝ) < Real.sqrt (4 * Real.pi * τ) :=
    Real.sqrt_pos.mpr (by positivity)
  have h2 : (0 : ℝ) < Real.sqrt (Matrix.det A) := Real.sqrt_pos.mpr hdet
  simp only [frozenGauss]
  positivity

/-! ### 2. The `s`-slice decomposition of the quadratic form and the first partial. -/

/-- The coordinate slice of `Q_A` is an explicit quadratic polynomial:
    `Q_A(update x i s) = Aᵢᵢ s² + (∑_{k≠i}(Aᵢₖ+Aₖᵢ)xₖ)·s + (i-deleted double sum)`. -/
theorem quadForm_update (A : Fin n → Fin n → ℝ) (x : Point n) (i : Fin n) (s : ℝ) :
    quadForm A (Function.update x i s)
      = A i i * s ^ 2
        + (∑ k ∈ Finset.univ.erase i, (A i k + A k i) * x k) * s
        + ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i, A j k * x j * x k := by
  classical
  have hinner : ∀ j : Fin n,
      (∑ k, A j k * Function.update x i s j * Function.update x i s k)
        = A j i * Function.update x i s j * s
          + ∑ k ∈ Finset.univ.erase i, A j k * Function.update x i s j * x k := by
    intro j
    rw [← Finset.add_sum_erase Finset.univ
        (fun k => A j k * Function.update x i s j * Function.update x i s k) (Finset.mem_univ i)]
    congr 1
    · rw [Function.update_self]
    · exact Finset.sum_congr rfl fun k hk => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have houter : quadForm A (Function.update x i s)
      = (A i i * s * s + ∑ k ∈ Finset.univ.erase i, A i k * s * x k)
        + ∑ j ∈ Finset.univ.erase i,
            (A j i * x j * s + ∑ k ∈ Finset.univ.erase i, A j k * x j * x k) := by
    simp only [quadForm]
    rw [← Finset.add_sum_erase Finset.univ
        (fun j => ∑ k, A j k * Function.update x i s j * Function.update x i s k)
        (Finset.mem_univ i)]
    congr 1
    · rw [hinner i, Function.update_self]
    · exact Finset.sum_congr rfl fun j hj => by
        rw [hinner j, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [houter, Finset.sum_add_distrib]
  have e1 : (∑ k ∈ Finset.univ.erase i, A i k * s * x k)
      = ∑ k ∈ Finset.univ.erase i, A i k * x k * s :=
    Finset.sum_congr rfl fun k _ => by ring
  have e3 : (∑ k ∈ Finset.univ.erase i, (A i k + A k i) * x k) * s
      = (∑ k ∈ Finset.univ.erase i, A i k * x k * s)
        + ∑ k ∈ Finset.univ.erase i, A k i * x k * s := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : (∑ j ∈ Finset.univ.erase i, A j i * x j * s)
      = ∑ k ∈ Finset.univ.erase i, A k i * x k * s := rfl
  rw [e1, e3, e2]
  ring

/-- The exact `i`-th slice derivative of the quadratic form: for SYMMETRIC `A`,
    `∂ₛ Q_A(update x i s)|_{s=xᵢ} = 2(Ax)ᵢ = 2∑ₖ Aᵢₖ xₖ`. -/
theorem hasDerivAt_quadForm_update (A : Fin n → Fin n → ℝ)
    (hAsym : ∀ i j, A i j = A j i) (x : Point n) (i : Fin n) :
    HasDerivAt (fun s => quadForm A (Function.update x i s))
      (2 * ∑ k, A i k * x k) (x i) := by
  have hfe : (fun s => quadForm A (Function.update x i s))
      = (fun s => A i i * s ^ 2
          + (∑ k ∈ Finset.univ.erase i, (A i k + A k i) * x k) * s
          + ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i, A j k * x j * x k) :=
    funext fun s => quadForm_update A x i s
  rw [hfe]
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x i) (x i) := by
    simpa using hasDerivAt_pow 2 (x i)
  have hsq' := hsq.const_mul (A i i)
  have hlin : HasDerivAt
      (fun s : ℝ => (∑ k ∈ Finset.univ.erase i, (A i k + A k i) * x k) * s)
      (∑ k ∈ Finset.univ.erase i, (A i k + A k i) * x k) (x i) := by
    simpa [mul_comm] using
      (hasDerivAt_id (x i)).const_mul (∑ k ∈ Finset.univ.erase i, (A i k + A k i) * x k)
  have hpoly := (hsq'.add hlin).add_const
    (∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i, A j k * x j * x k)
  convert hpoly using 1
  have hCi : (∑ k ∈ Finset.univ.erase i, (A i k + A k i) * x k)
      = 2 * ∑ k ∈ Finset.univ.erase i, A i k * x k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hAsym k i]; ring
  have hsplit : (∑ k, A i k * x k)
      = A i i * x i + ∑ k ∈ Finset.univ.erase i, A i k * x k :=
    (Finset.add_sum_erase Finset.univ (fun k => A i k * x k) (Finset.mem_univ i)).symm
  rw [hsplit, hCi]; ring

/-- The `i`-th slice derivative of the frozen Gaussian itself:
    `∂ₛ Γ_A(τ, update v i s)|_{s=vᵢ} = −(Av)ᵢ/(2τ) · Γ_A(τ,v)`. -/
theorem hasDerivAt_frozenGauss_update (A : Fin n → Fin n → ℝ)
    (hAsym : ∀ i j, A i j = A j i) (τ : ℝ) (hτ : 0 < τ) (v : Point n) (i : Fin n) :
    HasDerivAt (fun s => frozenGauss A τ (Function.update v i s))
      ((-(∑ k, A i k * v k) / (2 * τ)) * frozenGauss A τ v) (v i) := by
  have hQ := hasDerivAt_quadForm_update A hAsym v i
  have hE : HasDerivAt (fun s => -quadForm A (Function.update v i s) / (4 * τ))
      (-(2 * ∑ k, A i k * v k) / (4 * τ)) (v i) := (hQ.neg).div_const (4 * τ)
  have hexp := hE.exp
  have hall := hexp.const_mul
    ((Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.sqrt (Matrix.det A))
  have hfun : (fun s => frozenGauss A τ (Function.update v i s))
      = (fun s => ((Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.sqrt (Matrix.det A))
          * Real.exp (-quadForm A (Function.update v i s) / (4 * τ))) := rfl
  rw [hfun]
  simp only [Function.update_eq_self] at hall
  convert hall using 1
  simp only [frozenGauss]
  field_simp
  ring

/-- **The first coordinate partial** `∂ᵢ Γ_A = −(Av)ᵢ/(2τ) · Γ_A` (the `pd` of
    `QIQTH.Curvature`). -/
theorem frozenGauss_pd (A : Fin n → Fin n → ℝ) (hAsym : ∀ i j, A i j = A j i)
    (τ : ℝ) (hτ : 0 < τ) (v : Point n) (i : Fin n) :
    pd (fun y => frozenGauss A τ y) i v
      = (-(∑ k, A i k * v k) / (2 * τ)) * frozenGauss A τ v := by
  simp only [pd]
  exact (hasDerivAt_frozenGauss_update A hAsym τ hτ v i).deriv

/-! ### 3. The second partials and the exact frozen heat cancellation. -/

/-- **The second coordinate partial** (outer `i`, inner `j`):
    `∂ᵢ(∂ⱼ Γ_A) = (−Aᵢⱼ/(2τ) + (Av)ᵢ(Av)ⱼ/(4τ²)) · Γ_A`. -/
theorem frozenGauss_pd_pd (A : Fin n → Fin n → ℝ) (hAsym : ∀ i j, A i j = A j i)
    (τ : ℝ) (hτ : 0 < τ) (v : Point n) (i j : Fin n) :
    pd (fun y => pd (fun z => frozenGauss A τ z) j y) i v
      = (-(A i j) / (2 * τ)
          + (∑ k, A i k * v k) * (∑ k, A j k * v k) / (4 * τ ^ 2)) * frozenGauss A τ v := by
  have hinnerfun : (fun y => pd (fun z => frozenGauss A τ z) j y)
      = (fun y => (-(∑ k, A j k * y k) / (2 * τ)) * frozenGauss A τ y) :=
    funext fun y => frozenGauss_pd A hAsym τ hτ y j
  rw [hinnerfun]
  simp only [pd]
  have hrow : ∀ s : ℝ, (∑ k, A j k * Function.update v i s k)
      = A j i * s + ∑ k ∈ Finset.univ.erase i, A j k * v k := by
    intro s
    rw [← Finset.add_sum_erase Finset.univ
        (fun k => A j k * Function.update v i s k) (Finset.mem_univ i)]
    congr 1
    · rw [Function.update_self]
    · exact Finset.sum_congr rfl fun k hk => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have h1 : HasDerivAt
      (fun s => -(∑ k, A j k * Function.update v i s k) / (2 * τ))
      (-(A j i) / (2 * τ)) (v i) := by
    have hfe : (fun s : ℝ => -(∑ k, A j k * Function.update v i s k) / (2 * τ))
        = (fun s => -(A j i * s + ∑ k ∈ Finset.univ.erase i, A j k * v k) / (2 * τ)) :=
      funext fun s => by rw [hrow s]
    rw [hfe]
    have hlin : HasDerivAt
        (fun s : ℝ => A j i * s + ∑ k ∈ Finset.univ.erase i, A j k * v k)
        (A j i) (v i) := by
      simpa using ((hasDerivAt_id (v i)).const_mul (A j i)).add_const
        (∑ k ∈ Finset.univ.erase i, A j k * v k)
    simpa using (hlin.neg).div_const (2 * τ)
  have h2 := hasDerivAt_frozenGauss_update A hAsym τ hτ v i
  have key := h1.mul h2
  simp only [Function.update_eq_self] at key
  refine Eq.trans key.deriv ?_
  rw [hAsym j i]
  field_simp
  ring

/-- The prefactor power-rule scalar identity (standalone: no `Point` context, safe `cases`). -/
theorem pow_prefactor_deriv (m : ℕ) (τ P : ℝ) :
    (m : ℝ) * P ^ (m - 1) * (-(1 / (2 * τ)) * P) = -((m : ℝ) / (2 * τ)) * P ^ m := by
  cases m with
  | zero => simp
  | succ k =>
    rw [Nat.add_sub_cancel, pow_succ]
    ring

/-- **The `τ`-derivative** `∂_τ Γ_A = (Q_A(v)/(4τ²) − n/(2τ)) · Γ_A` for `τ > 0` — the
    `(4πτ)^{−n/2}` prefactor contributes `−n/(2τ)`, the exponent contributes `Q/(4τ²)`. -/
theorem hasDerivAt_frozenGauss_tau (A : Fin n → Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (v : Point n) :
    HasDerivAt (fun t => frozenGauss A t v)
      ((quadForm A v / (4 * τ ^ 2) - (n : ℝ) / (2 * τ)) * frozenGauss A τ v) τ := by
  have hpos : (0 : ℝ) < 4 * Real.pi * τ := by positivity
  have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * τ) := Real.sqrt_pos.mpr hpos
  have hsqrt_ne : Real.sqrt (4 * Real.pi * τ) ≠ 0 := hsqrt_pos.ne'
  have hu : HasDerivAt (fun t => 4 * Real.pi * t) (4 * Real.pi) τ := by
    simpa using (hasDerivAt_id τ).const_mul (4 * Real.pi)
  -- the 1-D prefactor `P(t) = (√(4πt))⁻¹` with `P' = (−1/(2t))·P`
  have hP : HasDerivAt (fun t => (Real.sqrt (4 * Real.pi * t))⁻¹)
      (-(1 / (2 * τ)) * (Real.sqrt (4 * Real.pi * τ))⁻¹) τ := by
    have h := (hu.sqrt hpos.ne').inv hsqrt_ne
    convert h using 1
    rw [Real.sq_sqrt hpos.le]
    field_simp
  -- the `n`-th power `P(t)ⁿ` with derivative `(−n/(2τ))·Pⁿ`
  have hPn : HasDerivAt (fun t => (Real.sqrt (4 * Real.pi * t))⁻¹ ^ n)
      (-((n : ℝ) / (2 * τ)) * (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n) τ := by
    have h := hP.pow n
    rwa [pow_prefactor_deriv n τ ((Real.sqrt (4 * Real.pi * τ))⁻¹)] at h
  have hC : HasDerivAt
      (fun t => (Real.sqrt (4 * Real.pi * t))⁻¹ ^ n * Real.sqrt (Matrix.det A))
      (-((n : ℝ) / (2 * τ))
        * ((Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.sqrt (Matrix.det A))) τ := by
    have h := hPn.mul_const (Real.sqrt (Matrix.det A))
    convert h using 1
    ring
  -- the exponent `−Q/(4t)` with derivative `Q/(4τ²)`
  have hv : HasDerivAt (fun t => -quadForm A v / (4 * t)) (quadForm A v / (4 * τ ^ 2)) τ := by
    have hcst : HasDerivAt (fun _ : ℝ => -quadForm A v) 0 τ := hasDerivAt_const _ _
    have hden : HasDerivAt (fun t : ℝ => 4 * t) 4 τ := by
      simpa using (hasDerivAt_id τ).const_mul (4 : ℝ)
    have h := hcst.div hden ((by positivity : (0 : ℝ) < 4 * τ).ne')
    convert h using 1
    field_simp
    ring
  have hB := hv.exp
  have key := hC.mul hB
  convert key using 1
  simp only [frozenGauss]
  ring

/-- Trace reduction: `∑ᵢⱼ Bᵢⱼ Aᵢⱼ = tr(BA) = n` for symmetric `A` with left inverse `B`. -/
theorem sum_BA_trace (A B : Fin n → Fin n → ℝ) (hAsym : ∀ i j, A i j = A j i)
    (hBA : ∀ i k, (∑ j, B i j * A j k) = if i = k then (1 : ℝ) else 0) :
    (∑ i, ∑ j, B i j * A i j) = (n : ℝ) := by
  have h1 : ∀ i, (∑ j, B i j * A i j) = 1 := by
    intro i
    calc (∑ j, B i j * A i j) = ∑ j, B i j * A j i :=
          Finset.sum_congr rfl fun j _ => by rw [hAsym i j]
      _ = if i = i then (1 : ℝ) else 0 := hBA i i
      _ = 1 := if_pos rfl
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Quadratic reduction: `∑ᵢⱼ Bᵢⱼ (Av)ᵢ (Av)ⱼ = vᵀA(BA)v = Q_A(v)` for `B` a left inverse. -/
theorem sum_BA_quad (A B : Fin n → Fin n → ℝ)
    (hBA : ∀ i k, (∑ j, B i j * A j k) = if i = k then (1 : ℝ) else 0) (v : Point n) :
    (∑ i, ∑ j, B i j * ((∑ k, A i k * v k) * (∑ k, A j k * v k))) = quadForm A v := by
  have hrow : ∀ i, (∑ j, B i j * (∑ k, A j k * v k)) = v i := by
    intro i
    have h1 : ∀ j, B i j * (∑ k, A j k * v k) = ∑ k, B i j * A j k * v k := by
      intro j
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm]
    have h2 : ∀ k, (∑ j, B i j * A j k * v k) = (∑ j, B i j * A j k) * v k := fun k =>
      (Finset.sum_mul _ _ _).symm
    rw [Finset.sum_congr rfl fun k _ => h2 k,
        Finset.sum_congr rfl fun k _ => by rw [hBA i k]]
    simp
  have hswap : ∀ i, (∑ j, B i j * ((∑ k, A i k * v k) * (∑ k, A j k * v k)))
      = (∑ k, A i k * v k) * (∑ j, B i j * (∑ k, A j k * v k)) := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hswap i,
      Finset.sum_congr rfl fun i _ => by rw [hrow i]]
  simp only [quadForm]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- **★ THE EXACT FROZEN HEAT CANCELLATION (Sol step 2).**  For any symmetric `A` with left
    inverse `B` (componentwise `∑ⱼ Bᵢⱼ Aⱼₖ = δᵢₖ`) and `τ > 0`:
        `∂_τ Γ_A(τ,v) = ∑ᵢⱼ Bⁱʲ ∂ᵢ(∂ⱼ Γ_A)(τ,v)`   EXACTLY (all v, all τ>0).
    This is what kills the J4-608 ε₀/τ floor at source: the frozen Gaussian matches the frozen
    operator at order 0 with ZERO residual — the defect of the true (moving) operator against
    `Γ_q` is then purely the coefficient modulus `gⁱʲ(x) − gⁱʲ(q)` (the J4-610 target). -/
theorem frozenGauss_frozen_heat (A B : Fin n → Fin n → ℝ)
    (hAsym : ∀ i j, A i j = A j i)
    (hBA : ∀ i k, (∑ j, B i j * A j k) = if i = k then (1 : ℝ) else 0)
    (τ : ℝ) (hτ : 0 < τ) (v : Point n) :
    deriv (fun t => frozenGauss A t v) τ
      = ∑ i, ∑ j, B i j * pd (fun y => pd (fun z => frozenGauss A τ z) j y) i v := by
  rw [(hasDerivAt_frozenGauss_tau A τ hτ v).deriv]
  have hterm : ∀ i j : Fin n,
      B i j * pd (fun y => pd (fun z => frozenGauss A τ z) j y) i v
        = (-(1 / (2 * τ)) * frozenGauss A τ v) * (B i j * A i j)
          + (1 / (4 * τ ^ 2) * frozenGauss A τ v)
            * (B i j * ((∑ k, A i k * v k) * (∑ k, A j k * v k))) := by
    intro i j
    rw [frozenGauss_pd_pd A hAsym τ hτ v i j]
    ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j,
      Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_BA_trace A B hAsym hBA, sum_BA_quad A B hBA v]
  field_simp
  ring

/-! ### 4. Convention pin: the SAME cancellation through the repo's own `heatOp`. -/

/-- Christoffel symbols of a FROZEN (constant) metric field vanish identically. -/
theorem christoffel_const (A B : Fin n → Fin n → ℝ) (μ ν ρ : Fin n) (x : Point n) :
    christoffel (fun _ => A) (fun _ => B) μ ν ρ x = 0 := by
  simp only [christoffel, pd_const]
  simp

/-- **★ THE CONVENTION PIN (adversarial check).**  Phrased through the repo's OWN heat operator
    `heatOp g gi K = ∂_τ K − Δ_{g,x}K` (`QIQTH.TrueHeatKernel`) with the frozen fields
    `g ≡ A`, `gi ≡ B`: the frozen Gaussian kernel `K(t,x,y) := Γ_A(t,x)` satisfies
    `heatOp (fun _ => A) (fun _ => B) K τ v y = 0` — the Christoffel first-order terms of the
    Laplace–Beltrami operator vanish for constant coefficients (`christoffel_const`) and the
    principal part cancels exactly (`frozenGauss_frozen_heat`).  No sign/index/normalization
    mismatch against the repo's derivative conventions survives this gate. -/
theorem frozenGauss_heatOp_zero (A B : Fin n → Fin n → ℝ)
    (hAsym : ∀ i j, A i j = A j i)
    (hBA : ∀ i k, (∑ j, B i j * A j k) = if i = k then (1 : ℝ) else 0)
    (τ : ℝ) (hτ : 0 < τ) (v y : Point n) :
    heatOp (fun _ => A) (fun _ => B) (fun t x _ => frozenGauss A t x) τ v y = 0 := by
  simp only [heatOp, laplaceBeltrami]
  have hchr : ∀ i j : Fin n,
      (pd (fun p => pd (fun z => frozenGauss A τ z) j p) i v
          - ∑ k, christoffel (fun _ => A) (fun _ => B) k i j v
              * pd (fun z => frozenGauss A τ z) k v)
        = pd (fun p => pd (fun z => frozenGauss A τ z) j p) i v := by
    intro i j
    have h0 : (∑ k, christoffel (fun _ => A) (fun _ => B) k i j v
        * pd (fun z => frozenGauss A τ z) k v) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [christoffel_const, zero_mul]
    rw [h0, sub_zero]
  have hred : ∀ i j : Fin n,
      B i j * (pd (fun p => pd (fun z => frozenGauss A τ z) j p) i v
          - ∑ k, christoffel (fun _ => A) (fun _ => B) k i j v
              * pd (fun z => frozenGauss A τ z) k v)
        = B i j * pd (fun p => pd (fun z => frozenGauss A τ z) j p) i v :=
    fun i j => by rw [hchr i j]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hred i j]
  rw [← frozenGauss_frozen_heat A B hAsym hBA τ hτ v]
  exact sub_self _

/-! ### 5. The two-sided ellipticity comparison (Sol step 3). -/

/-- **Upper comparison.**  If `m·‖v‖² ≤ Q_A(v)` (`m > 0`, the LOWER ellipticity eigenvalue
    bound), then `Γ_A(τ,v) ≤ √det A · (√m)⁻ⁿ · gaussDdim (τ/m) v`.  The prefactors match
    EXACTLY (`√(4πτ)⁻ⁿ = (√m)⁻ⁿ·√(4π(τ/m))⁻ⁿ`); the inequality lives in the exponent alone. -/
theorem frozenGauss_le_gauss (A : Fin n → Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) (v : Point n)
    (m : ℝ) (hm : 0 < m) (hlow : m * rncRadialSq v ≤ quadForm A v) :
    frozenGauss A τ v
      ≤ Real.sqrt (Matrix.det A) * (Real.sqrt m)⁻¹ ^ n * gaussDdim (τ / m) v := by
  have h1 : 4 * Real.pi * τ = m * (4 * Real.pi * (τ / m)) := by
    field_simp
  have h2 : (Real.sqrt (4 * Real.pi * τ))⁻¹
      = (Real.sqrt m)⁻¹ * (Real.sqrt (4 * Real.pi * (τ / m)))⁻¹ := by
    rw [h1, Real.sqrt_mul hm.le, mul_inv]
  have hexp : Real.exp (-quadForm A v / (4 * τ))
      ≤ Real.exp (-rncRadialSq v / (4 * (τ / m))) := by
    apply Real.exp_le_exp.mpr
    rw [show -rncRadialSq v / (4 * (τ / m)) = -(m * rncRadialSq v) / (4 * τ) by
      field_simp]
    have h4 : (0 : ℝ) ≤ (4 * τ)⁻¹ := by positivity
    calc -quadForm A v / (4 * τ) = -quadForm A v * (4 * τ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ -(m * rncRadialSq v) * (4 * τ)⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) h4
      _ = -(m * rncRadialSq v) / (4 * τ) := (div_eq_mul_inv _ _).symm
  have hc : (0 : ℝ) ≤ (Real.sqrt m)⁻¹ ^ n
      * (Real.sqrt (4 * Real.pi * (τ / m)))⁻¹ ^ n * Real.sqrt (Matrix.det A) := by
    positivity
  rw [gaussDdim_closed]
  simp only [frozenGauss]
  rw [h2, mul_pow]
  calc (Real.sqrt m)⁻¹ ^ n * (Real.sqrt (4 * Real.pi * (τ / m)))⁻¹ ^ n
        * Real.sqrt (Matrix.det A) * Real.exp (-quadForm A v / (4 * τ))
      ≤ (Real.sqrt m)⁻¹ ^ n * (Real.sqrt (4 * Real.pi * (τ / m)))⁻¹ ^ n
        * Real.sqrt (Matrix.det A) * Real.exp (-rncRadialSq v / (4 * (τ / m))) := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.sqrt (Matrix.det A) * (Real.sqrt m)⁻¹ ^ n
        * ((Real.sqrt (4 * Real.pi * (τ / m)))⁻¹ ^ n
          * Real.exp (-rncRadialSq v / (4 * (τ / m)))) := by ring

/-- **Lower comparison.**  If `Q_A(v) ≤ M·‖v‖²` (`M > 0`, the UPPER ellipticity eigenvalue
    bound), then `√det A · (√M)⁻ⁿ · gaussDdim (τ/M) v ≤ Γ_A(τ,v)`. -/
theorem gauss_le_frozenGauss (A : Fin n → Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) (v : Point n)
    (M : ℝ) (hM : 0 < M) (hhigh : quadForm A v ≤ M * rncRadialSq v) :
    Real.sqrt (Matrix.det A) * (Real.sqrt M)⁻¹ ^ n * gaussDdim (τ / M) v
      ≤ frozenGauss A τ v := by
  have h1 : 4 * Real.pi * τ = M * (4 * Real.pi * (τ / M)) := by
    field_simp
  have h2 : (Real.sqrt (4 * Real.pi * τ))⁻¹
      = (Real.sqrt M)⁻¹ * (Real.sqrt (4 * Real.pi * (τ / M)))⁻¹ := by
    rw [h1, Real.sqrt_mul hM.le, mul_inv]
  have hexp : Real.exp (-rncRadialSq v / (4 * (τ / M)))
      ≤ Real.exp (-quadForm A v / (4 * τ)) := by
    apply Real.exp_le_exp.mpr
    rw [show -rncRadialSq v / (4 * (τ / M)) = -(M * rncRadialSq v) / (4 * τ) by
      field_simp]
    have h4 : (0 : ℝ) ≤ (4 * τ)⁻¹ := by positivity
    calc -(M * rncRadialSq v) / (4 * τ) = -(M * rncRadialSq v) * (4 * τ)⁻¹ :=
          div_eq_mul_inv _ _
      _ ≤ -quadForm A v * (4 * τ)⁻¹ := mul_le_mul_of_nonneg_right (by linarith) h4
      _ = -quadForm A v / (4 * τ) := (div_eq_mul_inv _ _).symm
  rw [gaussDdim_closed]
  simp only [frozenGauss]
  rw [h2, mul_pow]
  calc Real.sqrt (Matrix.det A) * (Real.sqrt M)⁻¹ ^ n
        * ((Real.sqrt (4 * Real.pi * (τ / M)))⁻¹ ^ n
          * Real.exp (-rncRadialSq v / (4 * (τ / M))))
      = (Real.sqrt M)⁻¹ ^ n * (Real.sqrt (4 * Real.pi * (τ / M)))⁻¹ ^ n
        * Real.sqrt (Matrix.det A) * Real.exp (-rncRadialSq v / (4 * (τ / M))) := by ring
    _ ≤ (Real.sqrt M)⁻¹ ^ n * (Real.sqrt (4 * Real.pi * (τ / M)))⁻¹ ^ n
        * Real.sqrt (Matrix.det A) * Real.exp (-quadForm A v / (4 * τ)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

/-! ### 6. Space-form instantiation: eigenvalue bounds on the ball and the assembled layer. -/

/-- The frozen quadratic form of the space-form witness, via the banked
    `curvedRNCMetric_quadForm`:  `Q_{g^K(q)}(v) = ‖v‖² + (K/3)(⟨q,v⟩² − ‖q‖²‖v‖²)`. -/
theorem quadForm_curvedRNC (K : ℝ) (q v : Point n) :
    quadForm (curvedRNCMetric K q) v
      = rncRadialSq v
        + (K / 3) * ((∑ i, q i * v i) ^ 2 - rncRadialSq q * rncRadialSq v) := by
  have hdot := curvedRNCMetric_quadForm K q v
  have hunf : star v ⬝ᵥ (curvedRNCMetric K q *ᵥ v)
      = ∑ i, v i * (∑ j, curvedRNCMetric K q i j * v j) := rfl
  rw [hunf] at hdot
  rw [quadForm, ← hdot]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **Lower eigenvalue bound** (`m = 1`): for `K ≤ 0`, `‖v‖² ≤ Q_{g^K(q)}(v)` for ALL `q`
    (Cauchy–Schwarz; the repo sign convention makes `g^K ≥ δ` globally on the `K ≤ 0` branch). -/
theorem quadForm_curvedRNC_lower (K : ℝ) (hK : K ≤ 0) (q v : Point n) :
    rncRadialSq v ≤ quadForm (curvedRNCMetric K q) v := by
  rw [quadForm_curvedRNC]
  have hcs : (∑ i, q i * v i) ^ 2 ≤ rncRadialSq q * rncRadialSq v := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => q i) (fun i => v i)
    simpa only [rncRadialSq] using h
  nlinarith [mul_nonneg (neg_nonneg.mpr (by linarith : K / 3 ≤ 0)) (sub_nonneg.mpr hcs)]

/-- **Upper eigenvalue bound** (`M = 1 + (−K/3)r²`): for `K ≤ 0` and `‖q‖² ≤ r²`,
    `Q_{g^K(q)}(v) ≤ (1 + (−K/3)r²)·‖v‖²` — the tangential eigenvalue `1 + (−K/3)‖q‖²` capped
    on the ball.  NO smallness condition on `r` is needed (eigenvalues are ≥ 1, not ≤ 1). -/
theorem quadForm_curvedRNC_upper (K : ℝ) (hK : K ≤ 0) (r : ℝ) (q : Point n)
    (hq : rncRadialSq q ≤ r ^ 2) (v : Point n) :
    quadForm (curvedRNCMetric K q) v ≤ (1 + (-K / 3) * r ^ 2) * rncRadialSq v := by
  rw [quadForm_curvedRNC]
  have hS : (0 : ℝ) ≤ (∑ i, q i * v i) ^ 2 := sq_nonneg _
  have hv0 : 0 ≤ rncRadialSq v := rncRadialSq_nonneg v
  have hq0 : 0 ≤ rncRadialSq q := rncRadialSq_nonneg q
  nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr (by linarith : K / 3 ≤ 0))
      (sub_nonneg.mpr hq)) hv0,
    mul_nonneg (neg_nonneg.mpr (by linarith : K / 3 ≤ 0)) hS]

/-- **★ THE SPACE-FORM TWO-SIDED COMPARISON (Sol step 3, assembled).**  On the ball
    `‖q‖² ≤ r²`, with `M := 1 + (−K/3)r²` (explicit in `r, K`; `M ≥ 1 > 0` automatically):
        `√det g^K(q) · (√M)⁻ⁿ · G_{τ/M}(v) ≤ Γ_{g^K(q)}(τ,v) ≤ √det g^K(q) · G_τ(v)`.
    The upper constant is exact (`m = 1`, no widening); the lower widens time by `1/M`. -/
theorem frozenGauss_comparison_spaceForm (K : ℝ) (hK : K ≤ 0) (r : ℝ) (q : Point n)
    (hq : rncRadialSq q ≤ r ^ 2) (τ : ℝ) (hτ : 0 < τ) (v : Point n) :
    Real.sqrt (Matrix.det (curvedRNCMetric K q))
        * (Real.sqrt (1 + (-K / 3) * r ^ 2))⁻¹ ^ n
        * gaussDdim (τ / (1 + (-K / 3) * r ^ 2)) v
      ≤ frozenGauss (curvedRNCMetric K q) τ v
    ∧ frozenGauss (curvedRNCMetric K q) τ v
      ≤ Real.sqrt (Matrix.det (curvedRNCMetric K q)) * gaussDdim τ v := by
  have hM0 : (0 : ℝ) ≤ (-K / 3) * r ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg r)
  have hM : (0 : ℝ) < 1 + (-K / 3) * r ^ 2 := by linarith
  constructor
  · exact gauss_le_frozenGauss (curvedRNCMetric K q) τ hτ v _ hM
      (quadForm_curvedRNC_upper K hK r q hq v)
  · have h := frozenGauss_le_gauss (curvedRNCMetric K q) τ hτ v 1 one_pos
      (by simpa using quadForm_curvedRNC_lower K hK q v)
    simpa using h

/-- `gi^K(q)` is a componentwise LEFT inverse of `g^K(q)` (from the banked exact right-inverse
    `curvedRNCMetric_hinvF` plus symmetry of both matrices). -/
theorem curvedRNCInv_mul_metric (K : ℝ) (hK : K ≤ 0) (q : Point n) :
    ∀ i k, (∑ j, curvedRNCInv K q i j * curvedRNCMetric K q j k)
      = if i = k then (1 : ℝ) else 0 := by
  intro i k
  have hsymgi : ∀ a b, curvedRNCInv K q a b = curvedRNCInv K q b a := by
    intro a b
    by_cases h : a = b
    · subst h; rfl
    · simp only [curvedRNCInv, if_neg h, if_neg (Ne.symm h)]; ring
  calc (∑ j, curvedRNCInv K q i j * curvedRNCMetric K q j k)
      = ∑ j, curvedRNCMetric K q k j * curvedRNCInv K q j i :=
        Finset.sum_congr rfl fun j _ => by
          rw [hsymgi i j, curvedRNCMetric_symm K q j k]; ring
    _ = if k = i then (1 : ℝ) else 0 := curvedRNCMetric_hinvF K hK q k i
    _ = if i = k then (1 : ℝ) else 0 := by
        by_cases h : i = k
        · subst h; rfl
        · rw [if_neg (fun hh => h hh.symm), if_neg h]

/-- **★ THE FROZEN HEAT CANCELLATION AT THE CURVED WITNESS** — the satisfiability gate for the
    general theorem: at `A := g^K(q)`, `B := gi^K(q)` (`K ≤ 0`, ANY `q`), all hypotheses of
    `frozenGauss_frozen_heat` are DISCHARGED (symmetry banked, inverse from
    `curvedRNCMetric_hinvF`), so `∂_τ Γ_q = ∑ᵢⱼ gⁱʲ(q) ∂ᵢ∂ⱼ Γ_q` holds unconditionally. -/
theorem frozenGauss_frozen_heat_spaceForm (K : ℝ) (hK : K ≤ 0) (q : Point n)
    (τ : ℝ) (hτ : 0 < τ) (v : Point n) :
    deriv (fun t => frozenGauss (curvedRNCMetric K q) t v) τ
      = ∑ i, ∑ j, curvedRNCInv K q i j
          * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v :=
  frozenGauss_frozen_heat (curvedRNCMetric K q) (curvedRNCInv K q)
    (fun i j => curvedRNCMetric_symm K q i j) (curvedRNCInv_mul_metric K hK q) τ hτ v

/-! ### 7. Non-vacuity: the frozen point is genuinely non-flat. -/

/-- **NON-VACUITY GATE.**  For `K ≠ 0`, `n ≥ 2`, `q ≠ 0`, the frozen matrix `g^K(q)` is NOT the
    identity: some diagonal entry differs from `1` (if all diagonal corrections vanished, summing
    `‖q‖² = qᵢ²` over `i` would force `(n−1)‖q‖² = 0`).  Hence the space-form frozen-heat theorem
    and comparison are exercised at a genuinely non-flat frozen matrix — the layer is not
    secretly the flat `gaussDdim` statement. -/
theorem frozenGauss_matrix_ne_delta (K : ℝ) (hKne : K ≠ 0) (hn : 2 ≤ n)
    (q : Point n) (hq : q ≠ 0) :
    ∃ i : Fin n, curvedRNCMetric K q i i ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  have hK3 : K / 3 ≠ 0 := div_ne_zero hKne (by norm_num)
  have hei : ∀ i : Fin n, rncRadialSq q = q i ^ 2 := by
    intro i
    have h := hcon i
    have hdiag : curvedRNCMetric K q i i
        = 1 - K / 3 * (rncRadialSq q - q i * q i) := by
      simp [curvedRNCMetric]
    rw [hdiag] at h
    have h2 : K / 3 * (rncRadialSq q - q i * q i) = 0 := by linarith
    have h3 := (mul_eq_zero.mp h2).resolve_left hK3
    have h4 : rncRadialSq q = q i * q i := by linarith
    rw [h4]; ring
  have hRpos : 0 < rncRadialSq q := rncRadialSq_pos hq
  have hsum : (∑ _i : Fin n, rncRadialSq q) = rncRadialSq q := by
    rw [Finset.sum_congr rfl fun i _ => hei i]
    rfl
  have hcount : (∑ _i : Fin n, rncRadialSq q) = (n : ℝ) * rncRadialSq q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [hsum, hcount]

/-! ### 8. The J4-610 target (STATEMENT ONLY — deliberately unproved). -/

/-- **⚠ NEXT-BRICK TARGET (J4-610) — a `Prop`, NOT proved anywhere in this file.**
    The classical `O(τ^{−1/2})` Levi/Lipschitz defect of the frozen Gaussian against the MOVING
    inverse metric on the space-form ball: the residual of the true operator applied to `Γ_q` is
    the coefficient modulus `gⁱʲ(q+v) − gⁱʲ(q)` (size `O(‖v‖)`) times the second partials
    (size `O((1 + ‖v‖²/τ)/τ)·Γ_q`), and `‖v‖·Γ ~ √τ·G_λ` folds this to `C/√τ · G_{λτ}` —
    the α = −1/2-integrable Levi defect.  Proving an inhabitant (explicit `C, lam` in
    `r, K, n`) is the next layer; nothing here claims it. -/
def FrozenDefectBound (n : ℕ) (K r C lam : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ q v : Point n, rncRadialSq q ≤ r ^ 2 →
    |∑ i, ∑ j, (curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j)
        * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v|
      ≤ C / Real.sqrt τ * gaussDdim (lam * τ) v

end QIQTH.FrozenGauss
