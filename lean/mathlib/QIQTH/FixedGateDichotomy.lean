/-
  FixedGateDichotomy — J4-254: wide-route brick 7, the NEAR / ANNULUS / OUTSIDE trichotomy that
  GLOBALISES the wide dominations of `WideWitnessAmplitude`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It banks
  (i) a purely-analytic ANNULUS DECAY engine (Gaussian exp-smallness beats every inverse-time power,
  turned into a super-polynomial `τ^N` remainder), and (ii) the SUPPORT-based globalisation of the
  banked on-gate-ball wide dominations (`WideAmplitudePackage.hZeroth`/`hSecond`) to ALL `z`.  No
  `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no
  conclusion-in-disguise.  No existing file is edited.

  ── THE SOL #4 TRICHOTOMY (what globalises the on-ball dominations).
     The on-gate-ball wide dominations (brick 5) are valid only for `z ∈ K`, `‖z‖ < r`.  To reach a
     GLOBAL `∀ z` bound the base point `z` splits into three regions by the chart-image radius
     `ρ z = ‖W z 0‖` (with `radialCutoff` inner radius `a`, outer radius `b`):
       (1) NEAR   (`ρ z < a`, the cutoff plateau) — the package dominations apply;
       (2) ANNULUS(`a ≤ ρ z < b`) — the Gaussian factor `gaussDdim τ (W z 0)` is exponentially small
           (`ρ z² ≥ a²`), so `(τ⁻¹)^m · exp(−a²/(4τ))` is super-poly small: `≤ C · τ^N`;
       (3) OUTSIDE(`ρ z ≥ b` or off-gate) — the witness ≡ 0 (`radialCutoff_eq_zero` /
           `gatedKernel_apply_of_notMem`).

  ── WHAT LANDS.
    (A)  `annulus_invpow_exp_le` — ★ THE ANNULUS DECAY ENGINE (generic, reusable):
             `∀ 0 < a, ∀ m N, ∃ C > 0, ∀ τ > 0, (τ⁻¹)^m · exp(−a²/(4τ)) ≤ C · τ^N`.
         The standard exp-series trick `exp(−a²/(4τ)) ≤ k!·(4τ/a²)^k` (`k = m+N`, via the banked
         `GaussianWidthTransfer.pow_mul_exp_neg_le_factorial_div`) trades `k−m = N` inverse powers for
         `τ^N`.  `annulus_invpow_exp_le_const` is the `N = 0` bounded corollary.
    (A2) `annulus_gaussDdim_le` — the ANNULUS Gaussian splitter: on `a² ≤ r²(v)`,
             `gaussDdim τ v ≤ (√(4πτ))⁻ⁿ · exp(−a²/(4τ))`.
    (B)  `zeroth_global_of_package` / `second_global_of_package` — ★ THE SUPPORT-BASED GLOBALISATION:
         from a `WideAmplitudePackage` (on-ball dominations) plus the honest support carry
         `hSupp` (the witness / its second base-jet vanishes off the gate ball — the NEAR+ANNULUS
         region maps inside `‖z‖ < r` via the near-isometry, OUTSIDE vanishes), the two dominations
         hold for ALL `z`.
    (C)  `global_of_near_far` — ★ THE TRICHOTOMY GLOBALISER WIRING THE ENGINE: from a near
         Gaussian domination and a carried far (annulus, exp-small) bound
         `|H τ z| ≤ farC·(τ⁻¹)^p·exp(−a²/(4τ))`, the annulus engine collapses the far region to a
         super-poly remainder, yielding the global sum bound
             `∀ z, |H τ z| ≤ Cn·(τ⁻¹)^m·gaussDdim (lamτ) z + C·τ^N`.
         ⚠ HONEST NOTE.  The `+ C·τ^N` remainder is a POINTWISE upper bound; it is not `z`-integrable
         as a global constant — the consumer restricts it to the compact annulus shadow (where the far
         alternative is active) before integrating.  This is why the Sol note keeps the annulus term
         SEPARATE.

  ── W4 (`CConvFacade.CConvEnvelopeData.hGateData`/`hGateData'`) VERDICT — CARRIED, not discharged.
     The `hGateData`/`hGateData'` fields are NOT width-agnostic Gaussian-dichotomy facts: they carry
     the NEAR-DIAGONAL CHART-DERIVATIVE data at the EXACT width `(t−s)` — the base-point normal-jet
     `Pval` with its `HasDerivAt`, the amplitude `PdiffAt`, the three sup-bounds `Bs/Ba/Bd`, and the
     `η = 1/2` radial gate `(1/2)·r²(z) ≤ r²(W z x)`.  These are the on-gate chart-derivative envelope
     the exact-width facade demands, NOT the annulus/width-transfer dichotomy this brick supplies.
     Discharging them is the concrete on-gate builder (a brick-11-parallel construction from the
     compact chart jets), OUTSIDE this brick's scope.  Recorded here as an honest carry.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WideWitnessAmplitude
import QIQTH.GaussianWidthTransfer

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTransfer QIQTH.ResidueBound
open QIQTH.WideWitnessAmplitude
open scoped Topology BigOperators

namespace QIQTH.FixedGateDichotomy

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (A) — the ANNULUS DECAY ENGINE (generic, reusable analysis).
    ############################################################################### -/

/-- **★★ `annulus_invpow_exp_le` — THE ANNULUS DECAY ENGINE.**  For `0 < a` and any inverse-time
    power `m` and target power `N`, there is an explicit `C > 0` with, uniformly over `τ > 0`,
        `(τ⁻¹)^m · exp(−a²/(4τ)) ≤ C · τ^N`.
    Route: with `k := m + N`, `c := a²/4 > 0`, `y := τ⁻¹ ≥ 0`, the banked series bound
    `GaussianWidthTransfer.pow_mul_exp_neg_le_factorial_div` gives
    `(τ⁻¹)^k · exp(−(a²/4)·τ⁻¹) ≤ k!/(a²/4)^k`; multiplying by `τ^N ≥ 0` and the pow trade
    `(τ⁻¹)^k · τ^N = (τ⁻¹)^m` (`τ⁻¹·τ = 1`) closes it, `C = k!/(a²/4)^k`.  Gaussian decay beats every
    inverse power, uniformly in `τ`.  NOT `a₁ = R/6`. -/
theorem annulus_invpow_exp_le (a : ℝ) (ha : 0 < a) (m N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ →
      (τ⁻¹) ^ m * Real.exp (-(a ^ 2) / (4 * τ)) ≤ C * τ ^ N := by
  have ha2 : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  have hc : (0 : ℝ) < a ^ 2 / 4 := by positivity
  set k := m + N with hkdef
  refine ⟨(k.factorial : ℝ) / (a ^ 2 / 4) ^ k,
    div_pos (by exact_mod_cast Nat.factorial_pos k) (pow_pos hc k), ?_⟩
  intro τ hτ
  have hyinv : (0 : ℝ) ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
  have hbase := pow_mul_exp_neg_le_factorial_div hc k hyinv
  -- hbase : τ⁻¹ ^ k * exp(-(a²/4 * τ⁻¹)) ≤ k! / (a²/4)^k
  have harg : -(a ^ 2 / 4 * τ⁻¹) = -(a ^ 2) / (4 * τ) := by
    rw [neg_div]; congr 1
    rw [div_mul_eq_div_div, div_eq_mul_inv (a ^ 2 / 4) τ]
  rw [harg] at hbase
  have hτpow : (0 : ℝ) ≤ τ ^ N := pow_nonneg hτ.le N
  have htrade : (τ⁻¹) ^ k * τ ^ N = (τ⁻¹) ^ m := by
    rw [hkdef, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hτ.ne', one_pow, mul_one]
  calc (τ⁻¹) ^ m * Real.exp (-(a ^ 2) / (4 * τ))
      = ((τ⁻¹) ^ k * Real.exp (-(a ^ 2) / (4 * τ))) * τ ^ N := by rw [← htrade]; ring
    _ ≤ ((k.factorial : ℝ) / (a ^ 2 / 4) ^ k) * τ ^ N :=
        mul_le_mul_of_nonneg_right hbase hτpow

/-- **`annulus_invpow_exp_le_const` — the bounded (constant) corollary** (`N = 0`).  On the annulus
    the inverse-power-times-Gaussian is bounded UNIFORMLY in `τ > 0`:
        `∃ C > 0, ∀ τ > 0, (τ⁻¹)^m · exp(−a²/(4τ)) ≤ C`.
    Immediate from `annulus_invpow_exp_le` at `N = 0` (`τ^0 = 1`).  NOT `a₁ = R/6`. -/
theorem annulus_invpow_exp_le_const (a : ℝ) (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → (τ⁻¹) ^ m * Real.exp (-(a ^ 2) / (4 * τ)) ≤ C := by
  obtain ⟨C, hC, hb⟩ := annulus_invpow_exp_le a ha m 0
  refine ⟨C, hC, ?_⟩
  intro τ hτ
  simpa using hb τ hτ

/-- **`annulus_gaussDdim_le` — THE ANNULUS GAUSSIAN SPLITTER.**  On the annulus `a² ≤ r²(v)`
    (`r²(v) = rncRadialSq v`), the width-`τ` Gaussian is bounded by its prefactor times the
    diagonal-`a` exponential:
        `gaussDdim τ v ≤ (√(4πτ))⁻ⁿ · exp(−a²/(4τ))`,
    since `−r²(v)/(4τ) ≤ −a²/(4τ)` (annulus, `4τ > 0`) and the prefactor is `≥ 0`.  Combined with
    `annulus_invpow_exp_le` (after the `√`-prefactor is bounded by an inverse-integer power) this is
    the annulus exp-smallness of the concrete witness.  NOT `a₁ = R/6`. -/
theorem annulus_gaussDdim_le {a τ : ℝ} (hτ : 0 < τ) {v : Point n}
    (hv : a ^ 2 ≤ rncRadialSq v) :
    gaussDdim τ v ≤ (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.exp (-(a ^ 2) / (4 * τ)) := by
  rw [gaussDdim_eq_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * τ)]
  exact neg_le_neg hv

/-! ###############################################################################
    ### (B) — the SUPPORT-based globalisation of the on-ball wide dominations.
    ############################################################################### -/

/-- **★★ `zeroth_global_of_package` — THE GLOBAL ZEROTH WIDE DOMINATION.**  From a
    `WideAmplitudePackage` (whose `hZeroth` is the on-gate-ball zeroth domination) and the honest
    support carry `hSupp` (wherever the field-centre witness is nonzero, the base point sits in the
    gate ball `z ∈ K`, `‖z‖ < r` — supplied by the outer `radialCutoff` support pulled back through
    the near-isometry; NOT the conclusion, satisfiable geometry), the zeroth domination holds for
    ALL `z`:
        `∃ C > 0, ∀ 0 < τ ≤ τ₀, ∀ z, |H_G τ 0 z| ≤ C · gaussDdim (lam·τ) z`.
    Off-support the witness vanishes and the RHS is `≥ 0`.  NOT `a₁ = R/6`. -/
theorem zeroth_global_of_package {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (P : WideAmplitudePackage g gi hC hK S i)
    (hSupp : ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z ≠ 0 → z ∈ K ∧ ‖z‖ < P.r) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      |vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z|
        ≤ C * gaussDdim (P.lam * τ) z := by
  obtain ⟨C, hC0, hbound⟩ := P.hZeroth
  refine ⟨C, hC0, ?_⟩
  intro τ hτ hτ0 z
  by_cases hzero : vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z = 0
  · rw [hzero, abs_zero]
    exact mul_nonneg hC0.le (gaussDdim_nonneg _ _)
  · obtain ⟨hzK, hzr⟩ := hSupp τ hτ hτ0 z hzero
    exact hbound τ hτ hτ0 z hzK hzr

/-- **★★ `second_global_of_package` — THE GLOBAL SECOND WIDE DOMINATION.**  From a
    `WideAmplitudePackage` (whose `hSecond` is the on-gate-ball second domination with the clean `τ⁻¹`
    shape) and the honest support carry `hSupp` (wherever the second base-jet of the witness is
    nonzero, the base point sits in the gate ball — the second `x`-derivative is `pd(pd(·))` at `x=0`
    of `x' ↦ H_G τ x' z`, which vanishes identically in `x'` when `z ∉ K`, and the outer cutoff pulled
    back through the near-isometry places the support inside `‖z‖ < r`; NOT the conclusion, satisfiable
    geometry), the second domination holds for ALL `z`:
        `∃ C > 0, ∀ 0 < τ ≤ τ₀, ∀ z, |D²H … i τ z| ≤ C · τ⁻¹ · gaussDdim (lam·τ) z`.
    Off-support the second jet vanishes and the RHS is `≥ 0` (`τ⁻¹ ≥ 0`).  NOT `a₁ = R/6`. -/
theorem second_global_of_package {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (P : WideAmplitudePackage g gi hC hK S i)
    (hSupp : ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      witnessSecondXDeriv g gi hC hK S P.a P.b i τ z ≠ 0 → z ∈ K ∧ ‖z‖ < P.r) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      |witnessSecondXDeriv g gi hC hK S P.a P.b i τ z|
        ≤ C * τ⁻¹ * gaussDdim (P.lam * τ) z := by
  obtain ⟨C, hC0, hbound⟩ := P.hSecond
  refine ⟨C, hC0, ?_⟩
  intro τ hτ hτ0 z
  by_cases hzero : witnessSecondXDeriv g gi hC hK S P.a P.b i τ z = 0
  · rw [hzero, abs_zero]
    exact mul_nonneg (mul_nonneg hC0.le (inv_nonneg.mpr hτ.le)) (gaussDdim_nonneg _ _)
  · obtain ⟨hzK, hzr⟩ := hSupp τ hτ hτ0 z hzero
    exact hbound τ hτ hτ0 z hzK hzr

/-! ###############################################################################
    ### (C) — the TRICHOTOMY globaliser that WIRES the annulus engine.
    ############################################################################### -/

/-- **★★ `global_of_near_far` — THE TRICHOTOMY GLOBALISER (engine-wired).**  For an abstract witness
    `H : ℝ → Point n → ℝ` split by a chart-image radius `ρ : Point n → ℝ` at the cutoff radius `a`,
    from
      * a NEAR Gaussian domination `hNear : ρ z < a → |H τ z| ≤ Cn·(τ⁻¹)^m·gaussDdim (lam·τ) z`, and
      * a FAR (annulus / exp-small) bound `hFar : a ≤ ρ z → |H τ z| ≤ farC·(τ⁻¹)^p·exp(−a²/(4τ))`
        (the honest annulus factorisation, the `√`-prefactor already absorbed into `(τ⁻¹)^p`),
    the annulus engine `annulus_invpow_exp_le` collapses the far region to a super-poly remainder,
    giving the GLOBAL sum bound
        `∃ C > 0, ∀ z, |H τ z| ≤ Cn·(τ⁻¹)^m·gaussDdim (lam·τ) z + C·τ^N`.
    ⚠ HONEST NOTE.  `+ C·τ^N` is a POINTWISE remainder (not a `z`-integrable global constant); the
    consumer restricts it to the compact annulus shadow before integrating (the Sol note keeps the
    annulus term SEPARATE).  NOT `a₁ = R/6`. -/
theorem global_of_near_far
    (H : ℝ → Point n → ℝ) (ρ : Point n → ℝ)
    (lam a Cn farC τ₀ : ℝ) (m p N : ℕ)
    (ha : 0 < a) (hCn : 0 ≤ Cn) (hfarC : 0 ≤ farC)
    (hNear : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n, ρ z < a →
      |H τ z| ≤ Cn * (τ⁻¹) ^ m * gaussDdim (lam * τ) z)
    (hFar : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n, a ≤ ρ z →
      |H τ z| ≤ farC * (τ⁻¹) ^ p * Real.exp (-(a ^ 2) / (4 * τ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
      |H τ z| ≤ Cn * (τ⁻¹) ^ m * gaussDdim (lam * τ) z + C * τ ^ N := by
  obtain ⟨Ce, hCe, hEng⟩ := annulus_invpow_exp_le a ha p N
  refine ⟨farC * Ce + 1, by nlinarith [mul_nonneg hfarC hCe.le], ?_⟩
  intro τ hτ hτ0 z
  have hGnn : 0 ≤ Cn * (τ⁻¹) ^ m * gaussDdim (lam * τ) z :=
    mul_nonneg (mul_nonneg hCn (pow_nonneg (inv_nonneg.mpr hτ.le) m)) (gaussDdim_nonneg _ _)
  have hτNnn : 0 ≤ τ ^ N := pow_nonneg hτ.le N
  rcases lt_or_ge (ρ z) a with hz | hz
  · -- NEAR: the Gaussian term; the remainder is nonnegative.
    have hn := hNear τ hτ hτ0 z hz
    have hrem : 0 ≤ (farC * Ce + 1) * τ ^ N :=
      mul_nonneg (by nlinarith [mul_nonneg hfarC hCe.le]) hτNnn
    linarith
  · -- FAR: the exp bound + the engine give a super-poly remainder; the Gaussian term is nonneg.
    have hf := hFar τ hτ hτ0 z hz
    have heng := hEng τ hτ
    have hfar' : |H τ z| ≤ farC * (Ce * τ ^ N) := by
      calc |H τ z|
          ≤ farC * ((τ⁻¹) ^ p * Real.exp (-(a ^ 2) / (4 * τ))) := by
            rw [← mul_assoc]; exact hf
        _ ≤ farC * (Ce * τ ^ N) := mul_le_mul_of_nonneg_left heng hfarC
    have hstep : farC * (Ce * τ ^ N) ≤ (farC * Ce + 1) * τ ^ N := by nlinarith [hτNnn]
    linarith
end QIQTH.FixedGateDichotomy

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.FixedGateDichotomy.annulus_invpow_exp_le
#print axioms QIQTH.FixedGateDichotomy.annulus_invpow_exp_le_const
#print axioms QIQTH.FixedGateDichotomy.annulus_gaussDdim_le
#print axioms QIQTH.FixedGateDichotomy.zeroth_global_of_package
#print axioms QIQTH.FixedGateDichotomy.second_global_of_package
#print axioms QIQTH.FixedGateDichotomy.global_of_near_far
