/-
  LeviMTest — J4-395 (Sol #16, brick 6): the Weierstrass M-test for the Levi series ⟹
  `hBcontEvery`, closing the last continuity carry of the census machinery.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack AND on the surviving
  labelled census carries.  This file only assembles, from the already-banked Levi domination and the
  banked (x-slot) termwise joint-continuity family, the every-ceiling joint continuity of the Levi
  slice `(s,z) ↦ leviSeries E s z 0` — the `hBcontEvery` carry consumed by
  `QIQTH.AllUSliceMeas.hmeasHeatLevi_allU` / `hmeasLapLevi_allU` (and their `EveryCeilingFamilies`
  downstreams).  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## SLOT ORIENTATION (M0).  The consumer's Levi factor in the pairing is `leviSeries E s z 0` — the
  slice varies `(s, z)` with the LAST (x-) slot FROZEN at `0`.  So the termwise continuity needed is
  the x-slot family `p ↦ iterE E (k+1) p.1 p.2 0` (the BANKED `IterEContinuity.iterE_jointContinuousOn`
  / `IterEEngineWiring.iterE_jointContinuousOn_wired` shape) — NOT J4-394's middle-frozen z-slot
  `iterE … p.1 0 p.2`, which serves other consumers.  This file uses the x-slot family directly, as a
  carried honest input.

  ## THE THREE STEPS.

  (M1) THE BOX-UNIFORM MAJORANT.  From the banked Levi domination `hmajor`
       (`|iterE E (k+1) τ p q| ≤ C^(k+1)·iterKernelW 2 0 (k+1) τ p q`, `0 < τ ≤ T`) and the width-2
       factorization `iterKernelW 2 0 (k+1) τ z 0 = modelCoeff 0 τ (k+1) · gaussDdim (2τ) z`
       (`iterKernelW20_factor`), the box-uniform scalar majorant is
         `M k = gaussDdim τ₀ 0 · (C^(k+1) · modelCoeff 0 T (k+1))`,
       obtained by bounding, on the box `Icc (τ₀/2) T ×ˢ closedBall 0 R`, the time-power factor
       `modelCoeff 0 τ (k+1) ≤ modelCoeff 0 T (k+1)` (`modelCoeff_zero_mono_time`, `τ ≤ T`) and the
       Gaussian factor `gaussDdim (2τ) z ≤ gaussDdim (2τ) 0 ≤ gaussDdim τ₀ 0` (diagonal peak +
       width-antitone, `2τ ≥ τ₀` since `τ ≥ τ₀/2`).  `Summable M` is the banked
       `scaledModelCoeff_summable` (the Γ/factorial decay), scaled by the constant `gaussDdim τ₀ 0`.

  (M2) THE WEIERSTRASS CONTINUITY.  The banked M-test
       `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise` (`continuousOn_tsum`), fed the
       x-slot termwise continuity `hterm` and the M1 majorant, gives box continuity of the Levi slice.

  (M3) THE CAPSTONES.  The box family (`∀ τ₀ ∈ Ioc 0 T, ∀ R`) lifts to the strip
       `Ioc 0 T ×ˢ univ` via `JointContinuityAtoms.stripContOn_of_boxes` (`leviSeries_stripContOn`),
       and quantifying over the ceiling (degenerate `Tc ≤ 0` = empty domain) yields the every-ceiling
       `hBcontEvery_of_carries` — the verbatim `∀ Tc, ContinuousOn … (Ioc 0 Tc ×ˢ univ)` shape.

  ── HONEST CARRIED INPUTS (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hmajor` — the width-2 Levi domination (`LeviSeriesLocalData.hmajor` = banked
      `iterConvW_bound_le`; satisfiable from the residual one-step bound).
    • `htermBox` / `htermBoxEvery` — the x-slot termwise joint continuity on each positive-time box,
      the banked `IterEEngineWiring.iterE_jointContinuousOn_wired` output (its own residual = the
      per-rung `hmeas`/`hcont` convolution carries — NOT this file's concern).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MovingCorrAssembly
import QIQTH.LeviSeriesLocalData
import QIQTH.JointContinuityAtoms
import QIQTH.BoundaryAssembly
import QIQTH.ConvCarriesDischarge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.GaussianWidthTolerant
open QIQTH.TrueHeatKernel QIQTH.MovingCorrAssembly QIQTH.JointContinuityAtoms
open QIQTH.LeviSeriesLocalData
open scoped Topology BigOperators

namespace QIQTH.LeviMTest

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (M1a) — the two scalar helpers: width-2 factorization + `modelCoeff` time-monotonicity.
    ############################################################################### -/

/-- **`iterKernelW20_factor`.**  The width-2, order-0 iterated model kernel factorizes into the
    width-independent model coefficient times the (doubled-width) Gaussian:
        `iterKernelW 2 0 (k+1) τ z 0 = modelCoeff 0 τ (k+1) · gaussDdim (2·τ) z`   (`0 < τ`).
    Pure algebra: `GaussianWidthTolerant.iterKernelW_eq` (κ=2, α=0), `sub_zero`, and the definition of
    `modelCoeff` (both sides carry the same `Γ`/`rpow` prefactor).  NOT `a₁ = R/6`. -/
theorem iterKernelW20_factor (τ : ℝ) (hτ : 0 < τ) (z : Point n) (k : ℕ) :
    iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) τ z 0
      = modelCoeff (0 : ℝ) τ (k + 1) * gaussDdim (2 * τ) z := by
  rw [iterKernelW_eq (2 : ℝ) (0 : ℝ) (by norm_num) (by norm_num) τ hτ z 0 (k := k + 1) (by omega),
      sub_zero]
  unfold modelCoeff
  ring

/-- **`modelCoeff_zero_mono_time`.**  The order-0 model coefficient is monotone in time: for `0 < τ ≤ T`
    and `k`,
        `modelCoeff 0 τ (k+1) ≤ modelCoeff 0 T (k+1)`.
    The only time-dependence is the factor `τ^((k+1)·1 − 1) = τ^k` (real `rpow`, exponent `≥ 0`); the
    positive `Γ`-prefactor is time-free.  Via `Real.rpow_le_rpow` + `mul_le_mul_of_nonneg_left`.
    NOT `a₁ = R/6`. -/
theorem modelCoeff_zero_mono_time (k : ℕ) {τ T : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T) :
    modelCoeff (0 : ℝ) τ (k + 1) ≤ modelCoeff (0 : ℝ) T (k + 1) := by
  unfold modelCoeff
  have hpre : (0 : ℝ) ≤ Real.Gamma (0 + 1) ^ (k + 1) / Real.Gamma (((k + 1 : ℕ) : ℝ) * (0 + 1)) := by
    apply div_nonneg
    · exact pow_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le (k + 1)
    · exact (Real.Gamma_pos_of_pos
        (mul_pos (by exact_mod_cast Nat.succ_pos k) (by norm_num))).le
  have hexp : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (0 + 1) - 1 := by
    push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hrpow : τ ^ (((k + 1 : ℕ) : ℝ) * (0 + 1) - 1) ≤ T ^ (((k + 1 : ℕ) : ℝ) * (0 + 1) - 1) :=
    Real.rpow_le_rpow hτ.le hτT hexp
  exact mul_le_mul_of_nonneg_left hrpow hpre

/-! ###############################################################################
    ### (M1b) — the box-uniform summable majorant.
    ############################################################################### -/

/-- **★ (M1) `leviBoxMajorant_summable` — THE SUMMABLE BOX MAJORANT.**  The box-uniform scalar majorant
        `M k = gaussDdim τ₀ 0 · (C^(k+1) · modelCoeff 0 T (k+1))`
    is `Summable`: the banked `scaledModelCoeff_summable` (α=0) provides `Σ C^(k+1)·modelCoeff 0 T (k+1)`
    (the Γ/factorial decay beats the geometric `C^(k+1)`), scaled by the constant `gaussDdim τ₀ 0`.
    NOT `a₁ = R/6`. -/
theorem leviBoxMajorant_summable (C T τ₀ : ℝ) (hC : 0 ≤ C) (hT : 0 < T) :
    Summable (fun k : ℕ =>
      gaussDdim τ₀ (0 : Point n) * (C ^ (k + 1) * modelCoeff (0 : ℝ) T (k + 1))) :=
  (scaledModelCoeff_summable (0 : ℝ) T C (le_refl 0) hT hC).mul_left (gaussDdim τ₀ (0 : Point n))

/-! ###############################################################################
    ### (M2) — the Weierstrass box continuity of the Levi slice.
    ############################################################################### -/

/-- **★★ (M2) `leviSeries_boxContOn` — THE WEIERSTRASS BOX CONTINUITY.**  On the positive-time-compact
    box `Icc (τ₀/2) T ×ˢ closedBall 0 R` (`0 < τ₀ ≤ T`), the Levi slice `p ↦ leviSeries E p.1 p.2 0`
    is jointly `ContinuousOn`, via the banked M-test
    `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise`:
      • termwise: `hterm k` (the carried x-slot termwise continuity of `iterE E (k+1)`), scaled by the
        unit-modulus sign `(−1)^(k+1)` (`continuousOn_const.mul`);
      • envelope: the M1 box-uniform summable majorant `M`, dominating `|iterE E (k+1) p.1 p.2 0|` on
        the box by the domination `hmajor` (`0 < p.1 ≤ T` on the box) + `iterKernelW20_factor` + the
        time-monotone `modelCoeff_zero_mono_time` + the Gaussian diagonal-peak / width-antitone bounds.
    Carried inputs `hmajor`, `hterm` are the genuine M-test ingredients — NEITHER is the conclusion.
    NOT `a₁ = R/6`. -/
theorem leviSeries_boxContOn
    (E : ℝ → Point n → Point n → ℝ) (C T τ₀ R : ℝ)
    (hC : 0 ≤ C) (hT : 0 < T) (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T)
    (hmajor : ∀ (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) τ p q)
    (hterm : ∀ k : ℕ, ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine leviSlice_jointContinuousOn_of_termwise E (τ₀ / 2) T R
    (fun k => gaussDdim τ₀ (0 : Point n) * (C ^ (k + 1) * modelCoeff (0 : ℝ) T (k + 1)))
    (fun k => continuousOn_const.mul (hterm k))
    (leviBoxMajorant_summable C T τ₀ hC hT)
    ?_
  intro k p hp
  have hp1lo : τ₀ / 2 ≤ p.1 := hp.1.1
  have hp1hi : p.1 ≤ T := hp.1.2
  have hp1pos : 0 < p.1 := lt_of_lt_of_le (by linarith) hp1lo
  have h2p1 : (0 : ℝ) < 2 * p.1 := by linarith
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  calc |iterE E (k + 1) p.1 p.2 0|
      ≤ C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) p.1 p.2 0 :=
        hmajor k p.1 p.2 0 hp1pos hp1hi
    _ = C ^ (k + 1) * (modelCoeff (0 : ℝ) p.1 (k + 1) * gaussDdim (2 * p.1) p.2) := by
        rw [iterKernelW20_factor p.1 hp1pos p.2 k]
    _ ≤ C ^ (k + 1) * (modelCoeff (0 : ℝ) T (k + 1) * gaussDdim τ₀ (0 : Point n)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hC (k + 1))
        refine mul_le_mul (modelCoeff_zero_mono_time k hp1pos hp1hi) ?_
          (gaussDdim_pos (2 * p.1) h2p1 p.2).le
          (modelCoeff_pos (0 : ℝ) T (by norm_num) hT (k := k + 1) (by omega)).le
        exact le_trans
          (QIQTH.HeatResidualBound.gaussDdim_le_diagonal h2p1 p.2)
          (QIQTH.HeatResidualBound.gaussDdim_zero_antitone hτ₀ (by linarith))
    _ = gaussDdim τ₀ (0 : Point n) * (C ^ (k + 1) * modelCoeff (0 : ℝ) T (k + 1)) := by ring

/-! ###############################################################################
    ### (M3) — the strip capstone and the every-ceiling `hBcontEvery`.
    ############################################################################### -/

/-- **★★ (M3) `leviSeries_stripContOn` — THE PER-CEILING STRIP CONTINUITY.**  The Levi slice
    `p ↦ leviSeries E p.1 p.2 0` is jointly `ContinuousOn` the full positive-time strip
    `Ioc 0 T ×ˢ univ`, by lifting the M2 box continuities (one per `τ₀ ∈ Ioc 0 T`, `R`) through the
    generic local-to-global `JointContinuityAtoms.stripContOn_of_boxes`.  Carried inputs: `hmajor`
    (banked domination) and the x-slot termwise box-continuity family `htermBox`.  NOT `a₁ = R/6`. -/
theorem leviSeries_stripContOn
    (E : ℝ → Point n → Point n → ℝ) (C T : ℝ) (hC : 0 ≤ C) (hT : 0 < T)
    (hmajor : ∀ (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) τ p q)
    (htermBox : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) := by
  refine stripContOn_of_boxes (fun p : ℝ × Point n => leviSeries E p.1 p.2 0) T ?_
  intro τ₀ hτ₀ R
  exact leviSeries_boxContOn E C T τ₀ R hC hT hτ₀.1 hτ₀.2 hmajor (htermBox τ₀ hτ₀ R)

/-- **★★★ (M3) `hBcontEvery_of_carries` — THE `hBcontEvery` CARRY.**  The EVERY-CEILING joint continuity
    of the Levi slice: for EVERY ceiling `Tc : ℝ`,
        `ContinuousOn (fun p => leviSeries E p.1 p.2 0) (Ioc 0 Tc ×ˢ univ)`.
    This is the verbatim `hBcontEvery` hypothesis consumed by `QIQTH.AllUSliceMeas.hmeasHeatLevi_allU`
    / `hmeasLapLevi_allU`.  Positive ceilings reduce to `leviSeries_stripContOn`; degenerate ceilings
    `Tc ≤ 0` give the empty domain (`continuousOn_empty`).  Carried inputs: `hmajor` (the banked
    domination, ceiling-form at each `Tc`) and the x-slot termwise box-continuity family
    `htermBoxEvery`.  NOT `a₁ = R/6`. -/
theorem hBcontEvery_of_carries
    (E : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hmajor : ∀ (Tc : ℝ) (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ Tc →
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) τ p q)
    (htermBoxEvery : ∀ Tc : ℝ, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) Tc, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) Tc ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ Tc : ℝ, ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Ioc (0 : ℝ) Tc ×ˢ (Set.univ : Set (Point n))) := by
  intro Tc
  by_cases hTc : (0 : ℝ) < Tc
  · exact leviSeries_stripContOn E C Tc hC hTc (hmajor Tc) (htermBoxEvery Tc)
  · have hempty : Set.Ioc (0 : ℝ) Tc = ∅ := Set.Ioc_eq_empty hTc
    rw [hempty, Set.empty_prod]
    exact continuousOn_empty _

/-! ###############################################################################
    ### (M3′) — the `LeviSeriesLocalData`-facing per-ceiling strip (honors the packaged carry).
    ############################################################################### -/

/-- **`leviSeries_stripContOn_of_data`.**  The per-ceiling strip continuity read directly off the
    banked `LeviSeriesLocalData E C T` package: its `hmajor` field (the width-2 domination) and `hC`/`hT`
    feed `leviSeries_stripContOn`; only the x-slot termwise box family `htermBox` remains carried.
    NOT `a₁ = R/6`. -/
theorem leviSeries_stripContOn_of_data
    {E : ℝ → Point n → Point n → ℝ} {C T : ℝ} (data : LeviSeriesLocalData E C T)
    (htermBox : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) :=
  leviSeries_stripContOn E C T data.hC data.hT
    (fun k τ p q hτ hτT => data.hmajor k τ p q hτ hτT) htermBox

/-! ###############################################################################
    ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound).
    ############################################################################### -/

#check @iterKernelW20_factor
#check @modelCoeff_zero_mono_time
#check @leviBoxMajorant_summable
#check @leviSeries_boxContOn
#check @leviSeries_stripContOn
#check @hBcontEvery_of_carries
#check @leviSeries_stripContOn_of_data

#print axioms iterKernelW20_factor
#print axioms modelCoeff_zero_mono_time
#print axioms leviBoxMajorant_summable
#print axioms leviSeries_boxContOn
#print axioms leviSeries_stripContOn
#print axioms hBcontEvery_of_carries
#print axioms leviSeries_stripContOn_of_data

end QIQTH.LeviMTest
