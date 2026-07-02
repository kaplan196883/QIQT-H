/-
  QG I4-cert (QG_CAMPAIGN_PLAN.md phase B) — the CPSUV gate, CERTIFIED.

  The Lorentz-cutoff stress test was EXECUTED 2026-07-02 (`scripts/lorentz_stress_test.py`, results in
  `docs/qg_roadmap/LORENTZ_STRESS_TEST_RESULTS.md`): in Euclidean Yukawa with a sharp preferred-frame spatial
  cutoff, the one-loop speed splitting has the closed form (GPT-5.5-pro-verified, numerics matched to 2·10⁻¹⁸)
      Δc²(X) = (1/12π²)·[2X⁵/(1+X²)^{5/2} − X³/(1+X²)^{3/2}],   X = Λ/m  (units g = 1).
  This file certifies the two decisive mathematical facts of the gate:
  • `dc2Sharp_tendsto_cpsuvConst` + `cpsuvConst_ne_zero` (capstone `cpsuv_gate_sharp_fails`) — the
    sharp-cutoff splitting tends to the NONZERO constant `1/(12π²)` as `Λ→∞`: the Lorentz violation is
    UNSUPPRESSED (no `E/Λ` decoupling) — the CPSUV FAIL for preferred-frame cutoffs, machine-checked at the
    closed-form level;
  • `covariantSplit_eq_zero` — the symmetry certificate for the surviving branch: an O(4)-symmetric two-point
    function (`Π(q) = P(q_E²)`) has IDENTICAL temporal and spatial slices, hence equal quadratic coefficients
    and `Δc² = 0` identically — the covariant regulator family passes BY SYMMETRY (the triviality of this
    proof IS the physics point: the LV operator is forbidden by the regulator's symmetry).

  ⚠ Honest scope: the closed form is the OUTPUT of the one-loop computation (validated numerically against
  adaptive quadrature; the loop integral itself is not formalized — that would need Lean QFT); the named
  residual danger (the diamond tip vector u^μ_D) is an open experiment, not settled here. NOT QG. Std-3.
-/
import Mathlib

namespace QIQTH.QG.Cpsuv

open Real Filter

/-- The CPSUV constant `1/(12π²)` — the unsuppressed one-loop speed splitting of a sharp spatial cutoff. -/
noncomputable def cpsuvConst : ℝ := 1 / (12 * Real.pi ^ 2)

theorem cpsuvConst_pos : 0 < cpsuvConst := by
  rw [cpsuvConst]
  positivity

/-- The gate's kill condition: the constant is NOT zero. -/
theorem cpsuvConst_ne_zero : cpsuvConst ≠ 0 := cpsuvConst_pos.ne'

/-- The certified sharp-cutoff one-loop speed splitting, `X = Λ/m` (Yukawa, `g = 1`). -/
noncomputable def dc2Sharp (X : ℝ) : ℝ :=
  cpsuvConst * (2 * X ^ 5 / (1 + X ^ 2) ^ ((5 : ℝ) / 2) - X ^ 3 / (1 + X ^ 2) ^ ((3 : ℝ) / 2))

/-- The base ratio `X²/(1+X²) → 1`. -/
private theorem base_tendsto : Tendsto (fun X : ℝ => X ^ 2 / (1 + X ^ 2)) atTop (nhds 1) := by
  have hden : Tendsto (fun X : ℝ => 1 + X ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
  have hinv : Tendsto (fun X : ℝ => 1 / (1 + X ^ 2)) atTop (nhds 0) := by
    simpa [one_div] using hden.inv_tendsto_atTop
  have h1 : Tendsto (fun X : ℝ => 1 - 1 / (1 + X ^ 2)) atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub hinv
    simpa using this
  refine h1.congr fun X => ?_
  have hne : (1 + X ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `(X²/(1+X²))^e → 1` for any real exponent. -/
private theorem ratio_tendsto (e : ℝ) :
    Tendsto (fun X : ℝ => (X ^ 2 / (1 + X ^ 2)) ^ e) atTop (nhds 1) := by
  have hc : ContinuousAt (fun y : ℝ => y ^ e) 1 :=
    Real.continuousAt_rpow_const 1 e (Or.inl one_ne_zero)
  have hrpow : Tendsto (fun y : ℝ => y ^ e) (nhds 1) (nhds 1) := by
    simpa [Real.one_rpow] using hc.tendsto
  exact hrpow.comp base_tendsto

/-- `X⁵/(1+X²)^{5/2}` in composed form (positive `X`). -/
private theorem ratio_eq5 (X : ℝ) (hX : 0 < X) :
    (X ^ 2 / (1 + X ^ 2)) ^ ((5 : ℝ) / 2) = X ^ 5 / (1 + X ^ 2) ^ ((5 : ℝ) / 2) := by
  rw [Real.div_rpow (sq_nonneg X) (by positivity : (0 : ℝ) ≤ 1 + X ^ 2)]
  congr 1
  rw [show (X ^ 2 : ℝ) = X ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast X 2).symm,
    ← Real.rpow_mul hX.le,
    show ((2 : ℕ) : ℝ) * ((5 : ℝ) / 2) = ((5 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- `X³/(1+X²)^{3/2}` in composed form (positive `X`). -/
private theorem ratio_eq3 (X : ℝ) (hX : 0 < X) :
    (X ^ 2 / (1 + X ^ 2)) ^ ((3 : ℝ) / 2) = X ^ 3 / (1 + X ^ 2) ^ ((3 : ℝ) / 2) := by
  rw [Real.div_rpow (sq_nonneg X) (by positivity : (0 : ℝ) ≤ 1 + X ^ 2)]
  congr 1
  rw [show (X ^ 2 : ℝ) = X ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast X 2).symm,
    ← Real.rpow_mul hX.le,
    show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- **I4-cert CAPSTONE (half 1) — the sharp-cutoff splitting tends to the CPSUV constant:** the Lorentz
    violation does NOT decouple as `Λ→∞`; it approaches the nonzero constant `1/(12π²)`. -/
theorem dc2Sharp_tendsto_cpsuvConst : Tendsto dc2Sharp atTop (nhds cpsuvConst) := by
  have h5 : Tendsto (fun X : ℝ => X ^ 5 / (1 + X ^ 2) ^ ((5 : ℝ) / 2)) atTop (nhds 1) :=
    (ratio_tendsto ((5 : ℝ) / 2)).congr'
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX; exact ratio_eq5 X hX)
  have h3 : Tendsto (fun X : ℝ => X ^ 3 / (1 + X ^ 2) ^ ((3 : ℝ) / 2)) atTop (nhds 1) :=
    (ratio_tendsto ((3 : ℝ) / 2)).congr'
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX; exact ratio_eq3 X hX)
  have hcomb :
      Tendsto (fun X : ℝ => 2 * (X ^ 5 / (1 + X ^ 2) ^ ((5 : ℝ) / 2))
        - X ^ 3 / (1 + X ^ 2) ^ ((3 : ℝ) / 2)) atTop (nhds (2 * 1 - 1)) :=
    (h5.const_mul 2).sub h3
  have hfin := hcomb.const_mul cpsuvConst
  have heq : (fun X : ℝ => cpsuvConst * (2 * (X ^ 5 / (1 + X ^ 2) ^ ((5 : ℝ) / 2))
      - X ^ 3 / (1 + X ^ 2) ^ ((3 : ℝ) / 2))) = dc2Sharp := by
    funext X
    rw [dc2Sharp, mul_div_assoc]
  rw [heq] at hfin
  norm_num at hfin
  exact hfin

/-- **I4-cert CAPSTONE — the CPSUV gate FAILS for the sharp preferred-frame cutoff:** the one-loop speed
    splitting tends to a NONZERO constant — unsuppressed Lorentz violation. The certified kill of the
    naive-spatial-cutoff branch of finite capacity. -/
theorem cpsuv_gate_sharp_fails :
    Tendsto dc2Sharp atTop (nhds cpsuvConst) ∧ cpsuvConst ≠ 0 :=
  ⟨dc2Sharp_tendsto_cpsuvConst, cpsuvConst_ne_zero⟩

/-! ## The covariant symmetry certificate (the surviving branch) -/

/-- The temporal/spatial quadratic-coefficient split of an O(4)-symmetric two-point function
    `Π(q₀,q₁) = P(q₀²+q₁²)`. -/
noncomputable def covariantSplit (P : ℝ → ℝ) : ℝ :=
  iteratedDeriv 2 (fun s : ℝ => P (0 ^ 2 + s ^ 2)) 0
    - iteratedDeriv 2 (fun t : ℝ => P (t ^ 2 + 0 ^ 2)) 0

/-- The two slices of an O(4)-symmetric two-point function are the SAME function. -/
theorem covariant_slices_eq (P : ℝ → ℝ) :
    (fun t : ℝ => P (t ^ 2 + 0 ^ 2)) = fun s : ℝ => P (0 ^ 2 + s ^ 2) := by
  funext t
  norm_num

/-- **The covariant branch passes BY SYMMETRY: `Δc² = 0` identically.** For any radial profile `P`, the
    temporal and spatial quadratic coefficients coincide — the Lorentz-violating kinetic operator is
    FORBIDDEN by the regulator's O(4) invariance. (The proof is trivial; that triviality is the point.) -/
theorem covariantSplit_eq_zero (P : ℝ → ℝ) : covariantSplit P = 0 := by
  rw [covariantSplit, ← covariant_slices_eq P, sub_self]

end QIQTH.QG.Cpsuv
