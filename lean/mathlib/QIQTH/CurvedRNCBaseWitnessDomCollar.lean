import QIQTH.CurvedRNCBaseWitnessDom
import QIQTH.CurvedRNCModuliBound
import QIQTH.CurvedRNCPhaseTransfer
import QIQTH.InverseChartDisplacement
import QIQTH.AmplitudeDataOnCollar

/-!
# J4-534 — the FULLY-DISCHARGED curved base-witness Gaussian domination on the reach collar

The base-witness Gaussian domination #1 (`CurvedRNCBaseWitnessDom.curvedRNC_baseWitness_dom`, J4-531)
assembled, for the genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`, `Ric(0)=(n−1)Kδ ≠ 0`),
the amplitude Gaussian domination

```
|vanVleckGatedWitness g^K gi^K hChr hKset S a b τ 0 z| ≤ C_W · gaussDdim (λτ) z
```

but carried TWO genuinely-geometric hypotheses `hMod` (transport-coefficient moduli) and `hPhase`
(Gaussian-phase transfer).  J4-532 (`curvedRNC_moduli_bound`) and J4-533 (`curvedRNC_phase_transfer`)
discharged each of those separately.  This brick **assembles all three** into the capstone's
`hDomB`/`hWDom` binder shape — the amplitude Gaussian domination

```
|vanVleckGatedWitness g^K gi^K hChr hKset S a b τ 0 z| ≤ (C_amp·C_u·C_φ) · gaussDdim (λτ) z
```

with **every factor discharged** (no abstract carried hypothesis) on the reachable collar
`z ∈ Kset`, `‖z‖ < r` — the honest residual (SATISFIABLE: any `z` near `0 ∈ Kset` with `‖z‖ < r`,
`r > 0`).  Strictly lighter than #1: whereas #1 carried BOTH `hMod` and `hPhase`, this carries neither.

## Route (every step banked)

* **amplitude + cutoff** — `curvedRNCBaseWitnessDom.curvedRNCMetric_cutoff_amp_le` (the banked J4-530
  exact det bounds): `radialCutoff a b w · (vanVleck g^K w)^(−1/2) ≤ ((1−(K/3)b²)^(n−1))^{1/4}`.
* **transport moduli** — `curvedRNCModuliBound.curvedRNC_moduli_bound` on the compact chart-reach
  ball `closedBall 0 ρ`; applicability needs the chart image `w = uniformInverseChart … z 0` to lie in
  that ball, which is exactly the UPPER near-isometry `rncRadialSq(w) ≤ 2·rncRadialSq z ≤ 2n r²`
  from the banked TWO-SIDED `InverseChartDisplacement.chartW0_rncRadialSq_error` (`L‖z‖ ≤ 1` on a
  shrunk collar), squeezed to `‖w‖ ≤ ρ := √(2n r²)` via `norm_sq_le_rncRadialSq`/`rncRadialSq_le_nsq`.
* **phase transfer** — `curvedRNCPhaseTransfer.curvedRNC_phase_transfer` (the banked exact radial
  squeeze `(1/2)·rncRadialSq z ≤ rncRadialSq(w)` ⟹ widened Gaussian, prefactor `(√2)ⁿ`).

## Honest scope

`K < 0` is genuinely curved (`curvedRNCMetric_ricci_trace_diag_ne`); `C_amp ≥ 1 > 0`, `C_u > 0`,
`C_φ = (√2)ⁿ > 0`, so the constant is finite and the RHS genuinely dominates — NOT secretly flat (the
underlying radial squeeze tolerates a real contraction, `curvedRNC_baseWitness_dom_collar_curved_satisfiable`).
The reach collar `‖z‖ < r` is the ONLY residual and is SATISFIABLE.  This completes base-witness
domination #1 of the ~30–40 curved heat-kernel Gaussian dominations WITHOUT any carried analytic
hypothesis; the full `a₁ = R/6` additionally needs the entire heatOp/Levi/error-kernel domination pile
plus the Duhamel assembly and coefficient extraction.  `a₁ = R/6` remains CONDITIONAL and effectively
FLAT-ONLY; this does **not** derive the coefficient.
-/

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCVanVleckBound QIQTH.VanVleck QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.FlatHeatEquation QIQTH.ResidueBound
open QIQTH.CurvedRNCBaseWitnessDom QIQTH.CurvedRNCModuliBound QIQTH.CurvedRNCPhaseTransfer
open QIQTH.LayerBChangeVars
open scoped BigOperators

namespace QIQTH.CurvedRNCBaseWitnessDomCollar

variable {n : ℕ}

/-- **★★★ J4-534 — `curvedRNC_baseWitness_dom_collar`.**  THE FULLY-DISCHARGED CURVED BASE-WITNESS
    GAUSSIAN DOMINATION.  For the genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`), radii
    `0 < a < b`, any gate `S`, and any time cap `τmax`, there are a reach radius `r > 0`, a finite
    constant `CW > 0`, and a width `lam > 0` such that on the reachable collar `z ∈ Kset`, `‖z‖ < r`,
    for every `0 < τ ≤ τmax`,

    ```
    |vanVleckGatedWitness g^K gi^K hChr hKset S a b τ 0 z| ≤ CW · gaussDdim (lam·τ) z .
    ```

    ALL FOUR factors discharged: amplitude + cutoff via `curvedRNCMetric_cutoff_amp_le`; transport
    moduli via `curvedRNC_moduli_bound` on the compact chart-reach ball (chart image contained by the
    banked two-sided near-isometry); Gaussian phase via `curvedRNC_phase_transfer`.  NO abstract carried
    hypothesis — the collar `‖z‖ < r` is the sole (satisfiable) residual.  Strictly lighter than the
    J4-531 base domination (which carried `hMod` and `hPhase`).  NOT `a₁ = R/6`. -/
theorem curvedRNC_baseWitness_dom_collar
    (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (S : Point n → Set (Point n))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (τmax : ℝ) :
    ∃ r > (0 : ℝ), ∃ CW > (0 : ℝ), ∃ lam > (0 : ℝ),
      ∀ z ∈ Kset, ‖z‖ < r → ∀ τ : ℝ, 0 < τ → τ ≤ τmax →
        |vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset S a b τ 0 z|
          ≤ CW * gaussDdim (lam * τ) z := by
  -- ── the three banked ingredients (all obtained once, outside the pointwise quantifier).
  obtain ⟨r_ph, hr_ph, Cφ, hCφ, lam, hlam, hPhaseAll⟩ :=
    curvedRNC_phase_transfer K hK hChr hKset τmax
  obtain ⟨r₀, hr₀, L, hL0, herr⟩ :=
    chartW0_rncRadialSq_error (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
  -- the collar radius that makes the UPPER near-isometry usable (`L‖z‖ ≤ 1`).
  set r_c : ℝ := min r₀ (1 / (L + 1)) with hr_cdef
  have hLplus : (0 : ℝ) < L + 1 := by linarith
  have hr_c_pos : 0 < r_c := lt_min hr₀ (by positivity)
  -- the compact chart-reach ball that contains every collar chart image `w`.
  set ρ : ℝ := Real.sqrt (2 * (n : ℝ) * r_c ^ 2) with hρdef
  obtain ⟨Cu, hCu_pos, hCuAll⟩ :=
    curvedRNC_moduli_bound K hK (isCompact_closedBall (0 : Point n) ρ) τmax
  -- the discharged amplitude constant `C_amp = ((1−(K/3)b²)^(n−1))^{1/4} ≥ 1 > 0`.
  have hbase1 : (1 : ℝ) ≤ 1 - K / 3 * b ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ -(K / 3) by linarith) (sq_nonneg b)]
  have hCamp_pos : (0 : ℝ) < ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (pow_pos (by linarith) (n - 1)) _
  refine ⟨min r_ph r_c, lt_min hr_ph hr_c_pos,
    ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu * Cφ,
    mul_pos (mul_pos hCamp_pos hCu_pos) hCφ, lam, hlam, ?_⟩
  intro z hzK hzr τ hτ hτmax
  -- collar bookkeeping.
  have hzr_ph : ‖z‖ < r_ph := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzr_c : ‖z‖ < r_c := lt_of_lt_of_le hzr (min_le_right _ _)
  have hz_r₀ : ‖z‖ < r₀ := lt_of_lt_of_le hzr_c (min_le_left _ _)
  have hz_Linv : ‖z‖ < 1 / (L + 1) := lt_of_lt_of_le hzr_c (min_le_right _ _)
  -- `L‖z‖ ≤ 1` on the collar.
  have hLz1 : L * ‖z‖ ≤ 1 := by
    have h1 : L * ‖z‖ ≤ L * (1 / (L + 1)) := mul_le_mul_of_nonneg_left hz_Linv.le hL0
    have h2 : L * (1 / (L + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hLplus]; linarith
    linarith
  -- ── chart-image containment `w ∈ closedBall 0 ρ`, from the UPPER near-isometry.
  obtain ⟨_hlow, hup⟩ := herr z hzK hz_r₀
  have hUB : rncRadialSq (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0)
      ≤ 2 * (n : ℝ) * r_c ^ 2 := by
    have hZ2 : ‖z‖ ^ 2 ≤ r_c ^ 2 := by nlinarith [norm_nonneg z, hzr_c, hr_c_pos.le]
    have hRZ : rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 :=
      QIQTH.AmplitudeDataOnCollar.rncRadialSq_le_nsq z
    calc rncRadialSq (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0)
        ≤ rncRadialSq z + L * ‖z‖ * rncRadialSq z := hup
      _ ≤ 2 * rncRadialSq z := by nlinarith [rncRadialSq_nonneg z, hLz1]
      _ ≤ 2 * ((n : ℝ) * ‖z‖ ^ 2) := by linarith [hRZ]
      _ ≤ 2 * ((n : ℝ) * r_c ^ 2) := by nlinarith [hZ2, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      _ = 2 * (n : ℝ) * r_c ^ 2 := by ring
  have hcontain :
      ‖uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0‖ ≤ ρ := by
    have hN2 : ‖uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0‖ ^ 2
        ≤ 2 * (n : ℝ) * r_c ^ 2 :=
      le_trans (norm_sq_le_rncRadialSq _) hUB
    calc ‖uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0‖
        = Real.sqrt (‖uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (2 * (n : ℝ) * r_c ^ 2) := Real.sqrt_le_sqrt hN2
      _ = ρ := rfl
  have hwmem : uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0
      ∈ Metric.closedBall (0 : Point n) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hcontain
  -- ── the two discharged geometric facts, now over the collar point `z`.
  have hmod := hCuAll (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0)
    hwmem τ hτ.le hτmax
  have hphase := hPhaseAll z hzK hzr_ph τ hτ hτmax
  -- ── unfold the gated witness (same split as J4-531).
  have hRHS0 : 0 ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu * Cφ
      * gaussDdim (lam * τ) z :=
    mul_nonneg (mul_nonneg (mul_nonneg hCamp_pos.le hCu_pos.le) hCφ.le) (gaussDdim_nonneg _ _)
  simp only [vanVleckGatedWitness, gatedKernel, if_pos hzK]
  split_ifs with h0
  · -- ACTIVE: unfold the witness factorization and fold to `w`.
    simp only [globalCutoffParametrixWitnessN, heatParametrix, Nat.reduceAdd]
    set w := uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0 with hwdef
    -- `hmod`/`hphase` fold to `w`.
    have hModw : |∑ k ∈ Finset.range 2,
        transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
            (curvedRNCMetric K) (curvedRNCInv K)) k w * τ ^ k| ≤ Cu := hmod
    have hPhasew : gaussDdim τ w ≤ Cφ * gaussDdim (lam * τ) z := hphase
    -- amplitude + cutoff (discharged).
    have hAmp : radialCutoff a b w * (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2)
        ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) :=
      curvedRNCMetric_cutoff_amp_le K hK.le a b ha hab w
    have hcut0 : 0 ≤ radialCutoff a b w := radialCutoff_nonneg a b w
    have hGτ0 : 0 ≤ gaussDdim τ w := gaussDdim_nonneg τ w
    have hamp0 : 0 ≤ (vanVleck (curvedRNCMetric K) w) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_nonneg (curvedRNCMetric_vanVleck_pos K hK.le w).le _
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
          exact mul_le_mul hAmp hModw (abs_nonneg _) hCamp_pos.le
      _ ≤ ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu
            * (Cφ * gaussDdim (lam * τ) z) := by
          exact mul_le_mul_of_nonneg_left hPhasew (mul_nonneg hCamp_pos.le hCu_pos.le)
      _ = ((1 - K / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu * Cφ
            * gaussDdim (lam * τ) z := by ring
  · -- off gate (`0 ∉ S z`): witness is `0`.
    rw [abs_zero]; exact hRHS0

/-- **★ J4-534 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The radial squeeze underlying the
    discharged phase factor, `(1/2)·rncRadialSq z ≤ rncRadialSq (W z)`, is inhabited by a GENUINELY
    radially-distorting map `W z = c·z`, `c = 4/5 ≠ ±1`, for every `z`.  So the fully-discharged
    collar domination tolerates the real curved-normal-coordinate contraction and is NOT the flat
    `W z = ±z`.  Curved-inhabited.  NOT `a₁ = R/6`. -/
theorem curvedRNC_baseWitness_dom_collar_curved_satisfiable :
    ∃ c : ℝ, c ≠ 1 ∧ c ≠ -1 ∧ ∀ z : Point n,
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (fun i => c * z i) :=
  QIQTH.LayerBChangeVars.phase_domination_curved_satisfiable

end QIQTH.CurvedRNCBaseWitnessDomCollar

section AxiomChecks
open QIQTH.CurvedRNCBaseWitnessDomCollar
#print axioms curvedRNC_baseWitness_dom_collar
#print axioms curvedRNC_baseWitness_dom_collar_curved_satisfiable
end AxiomChecks
