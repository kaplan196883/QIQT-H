import QIQTH.CurvedRNCPosDef
import QIQTH.VanVleck

/-!
# J4-530 — the bounded van-Vleck factor for the curved witness `g^K` (base-witness amplitude)

The `a₁ = R/6` curved-signature capstone consumes a **base-witness Gaussian domination**
`hWDom : |vanVleckGatedWitness g gi … a b τ 0 z| ≤ C_W · gaussDdim (λ·τ) z`.  Unfolding the witness,

```
vanVleckGatedWitness … τ 0 z
  = gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g) …) τ 0 z
```

whose active value is `radialCutoff a b w · gaussDdim τ w · (vanVleck g w)^(-1/2) · (u₀+u₁τ)`, evaluated
at the chart image `w = Vmap z 0`.  The single genuinely-geometric input is the Gaussian-phase transfer
`gaussDdim τ w ≤ C · gaussDdim (λτ) z` (a radial-distance / near-isometry reach fact — see honest scope
below).  Every OTHER factor is an elementary bound.  **This file discharges the van-Vleck amplitude
factor** for the genuinely-curved witness `g^K = curvedRNCMetric K`, `K ≤ 0`.

## What is proved (exact, curved, non-vacuous)

* `curvedRNCMetric_det` — the **exact van-Vleck determinant**
  `det g^K(w) = (1 − (K/3)‖w‖²)^(n−1)`, via the rank-one matrix-determinant lemma
  `Matrix.det_one_add_replicateCol_mul_replicateRow` (`g^K = α·(1 + vecMulVec ((c/α)w) w)`,
  `α = 1 − (K/3)‖w‖²`, `c = K/3`, and `α + c‖w‖² = 1`).
* `curvedRNCMetric_det_ge_one` / `…_det_le` — two-sided det control for `K ≤ 0`
  (`1 ≤ det g^K(w) ≤ (1 − (K/3)M)^(n−1)` on `‖w‖² ≤ M`), the raw material for the `Θ^{±1/2}` amplitude.
* `curvedRNCMetric_vanVleck_pos` / `…_vanVleck_le_one` — the **bounded van-Vleck factor**
  `0 < vanVleck g^K(w) ≤ 1` for `K ≤ 0`, i.e. `Θ ∈ (0,1]`, exactly the amplitude input the domination
  consumes (`Θ^{−1/2} = det^{1/4}` is then controlled through the det bounds).

## Honest scope

`K < 0` is genuinely curved (`Ric(0) = (n−1)Kδ ≠ 0`, `curvedRNCMetric_ricci_trace_diag_ne`), so these
bounds are **not** secretly the flat kernel: `det g^K = (1 − (K/3)‖w‖²)^(n−1) ≢ 1`.  This closes the
van-Vleck amplitude factor of the base-witness domination.  It does **NOT** close the full domination:
the Gaussian-phase transfer `gaussDdim τ (Vmap z 0) ≤ C·gaussDdim (λτ) z` remains an irreducible
geometric reach input (it does not follow from `DV(0)=I` and cannot be cheated on a compact gate — the
`τ→0` decay in `z` must be matched by the decay in the chart radial coordinate).  And this is only the
FIRST of ~30–40 curved heat-kernel Gaussian dominations.  **NOT** `a₁ = R/6`.
-/

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness QIQTH.VanVleck
open scoped BigOperators Matrix

namespace QIQTH.CurvedRNCVanVleckBound

variable {n : ℕ}

/-- **★★ The exact van-Vleck determinant of the curved witness.**
    `det g^K(w) = (1 − (K/3)‖w‖²)^(n−1)`, for any `K, w` with `α := 1 − (K/3)‖w‖² ≠ 0`.
    Proof: `g^K(w) = α·(1 + vecMulVec ((K/3/α)·w) w)`, so `det = α^n·(1 + w ⬝ᵥ (K/3/α)w) = α^n·α⁻¹`
    (using `α + (K/3)‖w‖² = 1`), which is `α^(n−1)`. -/
theorem curvedRNCMetric_det (K : ℝ) (w : Point n)
    (hα : (1 - K / 3 * rncRadialSq w) ≠ 0) :
    Matrix.det (curvedRNCMetric K w) = (1 - K / 3 * rncRadialSq w) ^ (n - 1) := by
  -- the rescaled denominator `3 − K‖w‖² = 3·(1 − (K/3)‖w‖²) ≠ 0`, for `field_simp`
  have h3 : (3 : ℝ) - K * rncRadialSq w ≠ 0 := fun hc => hα (by linear_combination hc / 3)
  -- rank-one decomposition `g^K(w) = α • (1 + vecMulVec ((K/3/α)•w) w)`.  The entry identity
  -- `d - (K/3)(r²d - wᵢwⱼ) = α·d + (K/3)wᵢwⱼ` holds for the opaque diagonal atom `d = δᵢⱼ`, so no
  -- case split is needed.
  have hmat : curvedRNCMetric K w
      = (1 - K / 3 * rncRadialSq w) •
        ((1 : Matrix (Fin n) (Fin n) ℝ)
         + Matrix.vecMulVec ((K / 3 / (1 - K / 3 * rncRadialSq w)) • w) w) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, curvedRNCMetric]
    field_simp
    ring
  rw [hmat, Matrix.det_smul, Fintype.card_fin, Matrix.vecMulVec_eq (ι := Unit),
      Matrix.det_one_add_replicateCol_mul_replicateRow]
  -- the dot product `w ⬝ᵥ ((K/3/α)•w) = (K/3/α)·‖w‖²`
  have hww : (w : Fin n → ℝ) ⬝ᵥ w = rncRadialSq w := by
    simp only [dotProduct, rncRadialSq, pow_two]
  have hdot : (w : Fin n → ℝ) ⬝ᵥ ((K / 3 / (1 - K / 3 * rncRadialSq w)) • w)
      = K / 3 / (1 - K / 3 * rncRadialSq w) * rncRadialSq w := by
    rw [dotProduct_smul, hww, smul_eq_mul]
  rw [hdot]
  -- `1 + (K/3/α)·‖w‖² = α⁻¹`, from `α + (K/3)‖w‖² = 1`
  have hbr : (1 : ℝ) + K / 3 / (1 - K / 3 * rncRadialSq w) * rncRadialSq w
      = (1 - K / 3 * rncRadialSq w)⁻¹ := by
    field_simp
    ring
  rw [hbr]
  -- `α^n · α⁻¹ = α^(n-1)`
  cases n with
  | zero =>
    have hr0 : rncRadialSq (w : Point 0) = 0 := by simp [rncRadialSq]
    simp [hr0]
  | succ m =>
    rw [pow_succ, Nat.add_sub_cancel, mul_assoc, mul_inv_cancel₀ hα, mul_one]

/-- For `K ≤ 0` the van-Vleck base `α = 1 − (K/3)‖w‖² ≥ 1` (non-negative curvature correction). -/
theorem curvedRNCMetric_alpha_ge_one (K : ℝ) (hK : K ≤ 0) (w : Point n) :
    1 ≤ 1 - K / 3 * rncRadialSq w := by
  nlinarith [mul_nonneg (rncRadialSq_nonneg w) (show (0 : ℝ) ≤ -(K / 3) by linarith)]

/-- **`det g^K ≥ 1` for `K ≤ 0`.**  Since `α ≥ 1`, `det g^K = α^(n−1) ≥ 1`. -/
theorem curvedRNCMetric_det_ge_one (K : ℝ) (hK : K ≤ 0) (w : Point n) :
    1 ≤ Matrix.det (curvedRNCMetric K w) := by
  have hαge : 1 ≤ 1 - K / 3 * rncRadialSq w := curvedRNCMetric_alpha_ge_one K hK w
  have hα : (1 - K / 3 * rncRadialSq w) ≠ 0 := by linarith
  rw [curvedRNCMetric_det K w hα]
  exact one_le_pow₀ hαge

/-- **`det g^K` upper bound on the cutoff support `‖w‖² ≤ M`, `K ≤ 0`.**
    `det g^K(w) = α^(n−1) ≤ (1 − (K/3)M)^(n−1)` since `1 ≤ α ≤ 1 − (K/3)M`.  This is the raw upper
    control for the `Θ^{−1/2} = det^{1/4}` amplitude factor confined to the radial cutoff. -/
theorem curvedRNCMetric_det_le (K : ℝ) (hK : K ≤ 0) (w : Point n) (M : ℝ)
    (hM : rncRadialSq w ≤ M) :
    Matrix.det (curvedRNCMetric K w) ≤ (1 - K / 3 * M) ^ (n - 1) := by
  have hαge : 1 ≤ 1 - K / 3 * rncRadialSq w := curvedRNCMetric_alpha_ge_one K hK w
  have hα : (1 - K / 3 * rncRadialSq w) ≠ 0 := by linarith
  have hmono : 1 - K / 3 * rncRadialSq w ≤ 1 - K / 3 * M := by
    nlinarith [mul_le_mul_of_nonneg_left hM (show (0 : ℝ) ≤ -(K / 3) by linarith)]
  rw [curvedRNCMetric_det K w hα]
  exact pow_le_pow_left₀ (by linarith) hmono (n - 1)

/-- **`vanVleck g^K(w) > 0` for `K ≤ 0`.**  `det g^K ≥ 1 > 0`, so `(√det)⁻¹ > 0`. -/
theorem curvedRNCMetric_vanVleck_pos (K : ℝ) (hK : K ≤ 0) (w : Point n) :
    0 < vanVleck (curvedRNCMetric K) w := by
  rw [vanVleck_apply]
  have hdet : 0 < Matrix.det (curvedRNCMetric K w) :=
    lt_of_lt_of_le zero_lt_one (curvedRNCMetric_det_ge_one K hK w)
  exact inv_pos.mpr (Real.sqrt_pos.mpr hdet)

/-- **★ The bounded van-Vleck factor — `vanVleck g^K(w) ≤ 1` for `K ≤ 0`.**  `det g^K ≥ 1` gives
    `√det ≥ 1`, hence `Θ = (√det)⁻¹ ≤ 1`.  This is the amplitude input `Θ ∈ (0,1]` of the base-witness
    Gaussian domination, for the genuinely curved witness. -/
theorem curvedRNCMetric_vanVleck_le_one (K : ℝ) (hK : K ≤ 0) (w : Point n) :
    vanVleck (curvedRNCMetric K) w ≤ 1 := by
  rw [vanVleck_apply]
  have hdet : 1 ≤ Matrix.det (curvedRNCMetric K w) := curvedRNCMetric_det_ge_one K hK w
  have hsqrt : 1 ≤ Real.sqrt (Matrix.det (curvedRNCMetric K w)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hdet
  simpa using inv_anti₀ zero_lt_one hsqrt

end QIQTH.CurvedRNCVanVleckBound

section AxiomChecks
open QIQTH.CurvedRNCVanVleckBound
#print axioms curvedRNCMetric_det
#print axioms curvedRNCMetric_det_ge_one
#print axioms curvedRNCMetric_det_le
#print axioms curvedRNCMetric_vanVleck_pos
#print axioms curvedRNCMetric_vanVleck_le_one
end AxiomChecks
