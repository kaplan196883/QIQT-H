import QIQTH.CurvedRNCVanVleckBound
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.ConvApproximants
import QIQTH.SmoothCutoff

/-!
# J4-531 — the first curved base-witness Gaussian domination (modulo the carried phase input)

The `a₁ = R/6` curved-signature capstone consumes, for the genuinely-curved witness
`g^K = curvedRNCMetric K` (`K ≤ 0`, `Ric(0) = (n−1)Kδ ≠ 0`), a **base-witness Gaussian domination**

```
|vanVleckGatedWitness g^K gi^K hChr hKset S a b τ 0 z| ≤ C_W · gaussDdim (λτ) z .
```

Unfolding the witness at `p = 0`, `q = z`, and writing `w := uniformInverseChart g^K gi^K hChr hKset z 0`,
the active (on-gate) value is

```
radialCutoff a b w · gaussDdim τ w · (vanVleck g^K w) ^ (−1/2) · (∑ₖ uₖ(w)·τᵏ) ,
```

a product of FOUR factors:

* (1) **amplitude** `(vanVleck g^K w) ^ (−1/2) = det^{1/4}` — bounded by
  `C_amp := ((1 − (K/3)b²)^(n−1))^{1/4}` via the banked J4-530 exact det bounds.  **DISCHARGED here.**
* (2) **radial cutoff** `radialCutoff a b w ∈ [0,1]` — `radialCutoff_nonneg`/`radialCutoff_le_one`,
  with `radialCutoff_eq_zero` killing the exterior.  **DISCHARGED here** (folded into (1)).
* (3) **transport-coefficient moduli** `|∑ₖ uₖ(w)·τᵏ| ≤ C_u` — **CARRIED** as `hMod` (a satisfiable
  bound: the `uₖ` are smooth and the gate is compact; computing `u₁` for `g^K` is a separate jet).
* (4) **Gaussian-phase transfer** `gaussDdim τ w ≤ C_φ · gaussDdim (λτ) z` — the IRREDUCIBLE geometric
  reach input; **CARRIED** as `hPhase`.

## What is proved

* `sqrt_inv_rpow_half` — the amplitude algebra `((√d)⁻¹)^{−1/2} = d^{1/4}` (`d > 0`).
* `curvedRNCMetric_cutoff_amp_le` — the combined amplitude+cutoff bound
  `radialCutoff a b w · (vanVleck g^K w)^{−1/2} ≤ ((1 − (K/3)b²)^(n−1))^{1/4}` for `K ≤ 0`, `0 < a < b`.
* `curvedRNC_baseWitness_dom` — ★ the FULL base-witness domination with `C_W = C_amp · C_u · C_φ`,
  **every elementary factor (amplitude, cutoff) discharged** and ONLY the two genuinely-geometric
  factors (`hMod` moduli, `hPhase` phase) carried as explicit satisfiable hypotheses.

## Honest scope

`K < 0` is genuinely curved (`curvedRNCMetric_ricci_trace_diag_ne`), `C_amp` is finite, and the RHS
genuinely dominates: this is **not** secretly flat.  The carried `hMod`/`hPhase` are satisfiable (not
contradictory) for `g^K` — for a positive time window they follow from compactness/near-isometry.  This
assembles the FIRST of ~30–40 curved heat-kernel Gaussian dominations and still leans on a carried
geometric reach input; it does **NOT** derive the coefficient.  `a₁ = R/6` remains CONDITIONAL and
effectively FLAT-ONLY.
-/

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCVanVleckBound QIQTH.VanVleck QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.FlatHeatEquation QIQTH.ResidueBound
open scoped BigOperators

namespace QIQTH.CurvedRNCBaseWitnessDom

variable {n : ℕ}

/-- **The amplitude algebra.**  For `d > 0`, `((√d)⁻¹) ^ (−1/2) = d ^ (1/4)`.  (`√d = d^{1/2}`,
    the inverse flips the sign of the exponent, and the two `−1/2` powers multiply to `+1/4`.) -/
theorem sqrt_inv_rpow_half {d : ℝ} (hd : 0 < d) :
    ((Real.sqrt d)⁻¹) ^ (-(1 : ℝ) / 2) = d ^ ((1 : ℝ) / 4) := by
  have h2 : (-(1 : ℝ) / 2) = -(1 / (2 : ℝ)) := by norm_num
  rw [h2, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_mul hd.le]
  norm_num

/-- **★ (amplitude + cutoff) — `curvedRNCMetric_cutoff_amp_le`.**  For the curved witness `g^K`
    (`K ≤ 0`) and radii `0 < a < b`, the combined cutoff·amplitude factor is bounded by the finite
    curvature constant `C_amp := ((1 − (K/3)b²)^(n−1))^{1/4}`.  Near (`r² ≤ b²`): the banked det upper
    bound `det g^K ≤ (1 − (K/3)b²)^(n−1)` gives `(vanVleck)^{−1/2} = det^{1/4} ≤ C_amp`, and
    `radialCutoff ≤ 1`.  Far (`r² > b²`): `radialCutoff = 0`, so the product is `0 ≤ C_amp`. -/
theorem curvedRNCMetric_cutoff_amp_le (K : ℝ) (hK : K ≤ 0) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (w : Point n) :
    radialCutoff a b w * (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2)
      ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) := by
  have hd0 : 0 < Matrix.det (curvedRNCMetric K w) :=
    lt_of_lt_of_le zero_lt_one (curvedRNCMetric_det_ge_one K hK w)
  have hbase0 : (0 : ℝ) ≤ 1 - K / 3 * b ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ -(K / 3) by linarith) (sq_nonneg b)]
  have hCamp0 : (0 : ℝ) ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (pow_nonneg hbase0 (n - 1)) _
  have hampeq : (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2)
      = (Matrix.det (curvedRNCMetric K w)) ^ ((1 : ℝ) / 4) := by
    rw [vanVleck_apply]; exact sqrt_inv_rpow_half hd0
  have hamp0 : 0 ≤ (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg (curvedRNCMetric_vanVleck_pos K hK w).le _
  by_cases hb2 : rncRadialSq w ≤ b ^ 2
  · -- near: use the det upper bound.
    have hdetle : Matrix.det (curvedRNCMetric K w) ≤ (1 - K / 3 * b ^ 2) ^ (n - 1) :=
      curvedRNCMetric_det_le K hK w (b ^ 2) hb2
    have hample : (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2)
        ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) := by
      rw [hampeq]; exact Real.rpow_le_rpow hd0.le hdetle (by norm_num)
    calc radialCutoff a b w * (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2)
        ≤ 1 * (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (radialCutoff_le_one a b w) hamp0
      _ = (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2) := one_mul _
      _ ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) := hample
  · -- far: the cutoff vanishes.
    push_neg at hb2
    rw [radialCutoff_eq_zero ha hab hb2.le, zero_mul]
    exact hCamp0

/-- **★★★ (assembly) — `curvedRNC_baseWitness_dom`.**  THE FIRST CURVED BASE-WITNESS DOMINATION.
    For the genuinely-curved witness `g^K = curvedRNCMetric K` (`K ≤ 0`), radii `0 < a < b`, a time
    window `0 < τ ≤ τmax`, and the two CARRIED geometric hypotheses

    * `hMod` — the transport-coefficient modulus bound `|∑ₖ uₖ(w)·τᵏ| ≤ C_u`, and
    * `hPhase` — the Gaussian-phase transfer `gaussDdim τ w ≤ C_φ · gaussDdim (λτ) z`,

    the gated base witness is dominated by `C_W · gaussDdim (λτ) z` with the FINITE constant
    `C_W := ((1 − (K/3)b²)^(n−1))^{1/4} · C_u · C_φ`.  The amplitude and cutoff factors are DISCHARGED
    (via `curvedRNCMetric_cutoff_amp_le`); only the two genuinely-geometric factors are carried.  NOT
    `a₁ = R/6`. -/
theorem curvedRNC_baseWitness_dom
    (K : ℝ) (hK : K ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (S : Point n → Set (Point n))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (τmax lam Cu Cφ : ℝ) (hCu : 0 ≤ Cu) (hCφ : 0 ≤ Cφ)
    (hMod : ∀ z τ, 0 < τ → τ ≤ τmax →
      |∑ k ∈ Finset.range 2,
          transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
              (curvedRNCMetric K) (curvedRNCInv K)) k
            (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0) * τ ^ k| ≤ Cu)
    (hPhase : ∀ z τ, 0 < τ → τ ≤ τmax →
      gaussDdim τ (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0)
        ≤ Cφ * gaussDdim (lam * τ) z) :
    ∀ z τ, 0 < τ → τ ≤ τmax →
      |vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset S a b τ 0 z|
        ≤ (((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu * Cφ) * gaussDdim (lam * τ) z := by
  have hbase0 : (0 : ℝ) ≤ 1 - K / 3 * b ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ -(K / 3) by linarith) (sq_nonneg b)]
  have hCamp0 : (0 : ℝ) ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (pow_nonneg hbase0 (n - 1)) _
  intro z τ hτ hτmax
  have hRHS0 : 0 ≤ (((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu * Cφ)
      * gaussDdim (lam * τ) z :=
    mul_nonneg (mul_nonneg (mul_nonneg hCamp0 hCu) hCφ) (gaussDdim_nonneg _ _)
  simp only [vanVleckGatedWitness, gatedKernel]
  split_ifs with hz h0
  · -- ACTIVE: unfold the witness factorization.
    simp only [globalCutoffParametrixWitnessN, heatParametrix, Nat.reduceAdd]
    set w := uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0 with hwdef
    -- moduli and phase, folded onto `w`.
    have hModw : |∑ k ∈ Finset.range 2,
        transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
            (curvedRNCMetric K) (curvedRNCInv K)) k w * τ ^ k| ≤ Cu := by
      have h := hMod z τ hτ hτmax; rw [← hwdef] at h; exact h
    have hPhasew : gaussDdim τ w ≤ Cφ * gaussDdim (lam * τ) z := by
      have h := hPhase z τ hτ hτmax; rw [← hwdef] at h; exact h
    -- amplitude + cutoff (discharged).
    have hAmp : radialCutoff a b w * (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2)
        ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) :=
      curvedRNCMetric_cutoff_amp_le K hK a b ha hab w
    -- nonnegativity of the discharged factors.
    have hcut0 : 0 ≤ radialCutoff a b w := radialCutoff_nonneg a b w
    have hGτ0 : 0 ≤ gaussDdim τ w := gaussDdim_nonneg τ w
    have hamp0 : 0 ≤ (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_nonneg (curvedRNCMetric_vanVleck_pos K hK w).le _
    -- pull the absolute value through the nonnegative factors.
    have hfactor : |radialCutoff a b w *
          (gaussDdim τ w * (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2)
            * ∑ k ∈ Finset.range 2,
                transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
                    (curvedRNCMetric K) (curvedRNCInv K)) k w * τ ^ k)|
        = radialCutoff a b w * (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2)
            * |∑ k ∈ Finset.range 2,
                transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
                    (curvedRNCMetric K) (curvedRNCInv K)) k w * τ ^ k|
            * gaussDdim τ w := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcut0, abs_of_nonneg hGτ0, abs_of_nonneg hamp0]
      ring
    rw [hfactor]
    calc radialCutoff a b w * (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2)
            * |∑ k ∈ Finset.range 2,
                transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
                    (curvedRNCMetric K) (curvedRNCInv K)) k w * τ ^ k|
            * gaussDdim τ w
        ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu * gaussDdim τ w := by
          apply mul_le_mul_of_nonneg_right _ hGτ0
          exact mul_le_mul hAmp hModw (abs_nonneg _) hCamp0
      _ ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu
            * (Cφ * gaussDdim (lam * τ) z) := by
          exact mul_le_mul_of_nonneg_left hPhasew (mul_nonneg hCamp0 hCu)
      _ = (((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu * Cφ)
            * gaussDdim (lam * τ) z := by ring
  · -- off gate (`0 ∉ S z`): the witness is `0`.
    rw [abs_zero]; exact hRHS0
  · -- off gate (`z ∉ Kset`): the witness is `0`.
    rw [abs_zero]; exact hRHS0

end QIQTH.CurvedRNCBaseWitnessDom

section AxiomChecks
open QIQTH.CurvedRNCBaseWitnessDom
#print axioms sqrt_inv_rpow_half
#print axioms curvedRNCMetric_cutoff_amp_le
#print axioms curvedRNC_baseWitness_dom
end AxiomChecks
