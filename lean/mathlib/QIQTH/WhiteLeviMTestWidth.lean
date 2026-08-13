/-
  WhiteLeviMTestWidth — J4-694: the WIDTH-GENERIC (`lam`) replay of the `QIQTH.LeviMTest` Weierstrass
  M-test assembly for the Levi slice, freeing the `hBcontEvery_of_carries` machinery from its
  width-2 hardcode so it can consume the whitened (`whiteDefectKernel`, width `lam = whiteLam ≥ 2`)
  domination directly.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It only
  re-derives, at a GENERAL width `lam` (`0 < lam`), the exact `LeviMTest` assembly chain
  (`iterKernelW20_factor` → `leviBoxMajorant_summable` → `leviSeries_boxContOn` →
  `leviSeries_stripContOn` → `hBcontEvery_of_carries`).  Every step is the mechanical width-`lam`
  mirror of the banked width-2 proof; the `modelCoeff` time-power factor (`α = 0`) is width-free, so
  the summable majorant `scaledModelCoeff_summable` and the time-monotonicity
  `LeviMTest.modelCoeff_zero_mono_time` are REUSED verbatim.  No `sorry` (header prose excepted), no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or
  trivially yielding) the conclusion, no existing file edited, nothing committed, nothing wired into
  `QIQTH.lean` / `AxiomAudit`.

  ── WHY WIDTH-GENERIC.  The whitened Levi domination (`WhiteHBdomAllRows`, `white_hBdom_discharged`)
     lands at the whitened width `lam = whiteLam`, and the per-term iterated bound
     `iterConvW_bound` at the whitened one-step `gaussDdim (lam·τ)` shape (`white_hEuni`, `α = 0`)
     produces `iterKernelW lam 0`.  The banked `LeviMTest.hBcontEvery_of_carries` only accepts
     `iterKernelW (2:ℝ) 0`.  This file's `hBcontEvery_of_carries_width` accepts `iterKernelW lam 0`
     for any `0 < lam`, matching the whitened width exactly (no `lam = 2` coincidence needed).

  ── THE ONLY WIDTH-SENSITIVE STEP.  The factorization + diagonal-peak / width-antitone box majorant:
       `iterKernelW lam 0 (k+1) τ z 0 = modelCoeff 0 τ (k+1) · gaussDdim (lam·τ) z`,
     and on the box `Icc (τ₀/2) T ×ˢ closedBall 0 R` (`τ ≥ τ₀/2`, `lam > 0`),
       `gaussDdim (lam·τ) z ≤ gaussDdim (lam·τ) 0 ≤ gaussDdim (lam·τ₀/2) 0`,
     so the box-uniform summable majorant is `M k = gaussDdim (lam·τ₀/2) 0 · (C^(k+1)·modelCoeff 0 T (k+1))`.
     (The width-2 file used `gaussDdim τ₀ 0` because `2·(τ₀/2) = τ₀`; here the peak sits at `lam·τ₀/2`.)

  ── HONEST CARRIED INPUTS (each satisfiable, non-vacuous, NEVER the conclusion) — verbatim the
     `LeviMTest` carries, only re-widthed:
    • `hmajor` — the width-`lam` Levi domination `|iterE E (k+1) τ p q| ≤ C^(k+1)·iterKernelW lam 0 (k+1) τ p q`.
    • `htermBox` / `htermBoxEvery` — the x-slot termwise joint continuity on each positive-time box
      (the whitened `iterE` termwise joint continuity, the M-test residual, still open).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MovingCorrAssembly
import QIQTH.JointContinuityAtoms
import QIQTH.LeviMTest

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.GaussianWidthTolerant
open QIQTH.TrueHeatKernel QIQTH.MovingCorrAssembly QIQTH.JointContinuityAtoms
open scoped Topology BigOperators

namespace QIQTH.WhiteLeviMTestWidth

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (W1) — the WIDTH-GENERIC factorization of the order-0 iterated model kernel.
    ############################################################################### -/

/-- **`iterKernelW_width0_factor`.**  At ANY width `lam > 0` (not just `2`), the order-0 iterated
    model kernel factorizes into the width-independent model coefficient times the width-`lam`
    Gaussian:
        `iterKernelW lam 0 (k+1) τ z 0 = modelCoeff 0 τ (k+1) · gaussDdim (lam·τ) z`   (`0 < τ`).
    The width-`lam` mirror of `LeviMTest.iterKernelW20_factor`, via `iterKernelW_eq` (`κ = lam`,
    `α = 0`, needs only `0 < lam`) + `sub_zero` + the definition of `modelCoeff`.  NOT `a₁ = R/6`. -/
theorem iterKernelW_width0_factor (lam τ : ℝ) (hlam : 0 < lam) (hτ : 0 < τ) (z : Point n) (k : ℕ) :
    iterKernelW lam (0 : ℝ) (k + 1) τ z 0
      = modelCoeff (0 : ℝ) τ (k + 1) * gaussDdim (lam * τ) z := by
  rw [iterKernelW_eq lam (0 : ℝ) hlam (by norm_num) τ hτ z 0 (k := k + 1) (by omega),
      sub_zero]
  unfold modelCoeff
  ring

/-! ###############################################################################
    ### (W2) — the box-uniform summable majorant at width `lam`.
    ############################################################################### -/

/-- **★ (W2) `leviBoxMajorant_width_summable`.**  The width-`lam` box-uniform scalar majorant
        `M k = gaussDdim (lam·τ₀/2) 0 · (C^(k+1) · modelCoeff 0 T (k+1))`
    is `Summable` — the banked `LeviMTest.leviBoxMajorant_summable` at the constant Gaussian peak
    `gaussDdim (lam·τ₀/2) 0` (the `α = 0` `modelCoeff` decay is width-free).  NOT `a₁ = R/6`. -/
theorem leviBoxMajorant_width_summable (C T lam τ₀ : ℝ) (hC : 0 ≤ C) (hT : 0 < T) :
    Summable (fun k : ℕ =>
      gaussDdim (lam * τ₀ / 2) (0 : Point n) * (C ^ (k + 1) * modelCoeff (0 : ℝ) T (k + 1))) :=
  QIQTH.LeviMTest.leviBoxMajorant_summable C T (lam * τ₀ / 2) hC hT

/-! ###############################################################################
    ### (W3) — the Weierstrass box continuity of the Levi slice at width `lam`.
    ############################################################################### -/

/-- **★★ (W3) `leviSeries_boxContOn_width` — THE WEIERSTRASS BOX CONTINUITY (width-generic).**  On the
    positive-time-compact box `Icc (τ₀/2) T ×ˢ closedBall 0 R` (`0 < τ₀ ≤ T`, `0 < lam`), the Levi
    slice `p ↦ leviSeries E p.1 p.2 0` is jointly `ContinuousOn`, via
    `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise`:
      • termwise: the carried x-slot termwise continuity `hterm k`, signed by `(−1)^(k+1)`;
      • envelope: the (W2) box-uniform summable majorant, dominating `|iterE E (k+1) p.1 p.2 0|` on
        the box via `hmajor` (`0 < p.1 ≤ T`) + `iterKernelW_width0_factor` + the time-monotone
        `modelCoeff_zero_mono_time` + the width-`lam` Gaussian diagonal-peak / antitone bounds.
    The width-2 mirror is `LeviMTest.leviSeries_boxContOn`.  Carried inputs `hmajor`, `hterm` are the
    genuine M-test ingredients — NEITHER is the conclusion.  NOT `a₁ = R/6`. -/
theorem leviSeries_boxContOn_width
    (E : ℝ → Point n → Point n → ℝ) (C T lam τ₀ R : ℝ)
    (hC : 0 ≤ C) (hT : 0 < T) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T)
    (hmajor : ∀ (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW lam (0 : ℝ) (k + 1) τ p q)
    (hterm : ∀ k : ℕ, ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine leviSlice_jointContinuousOn_of_termwise E (τ₀ / 2) T R
    (fun k => gaussDdim (lam * τ₀ / 2) (0 : Point n) * (C ^ (k + 1) * modelCoeff (0 : ℝ) T (k + 1)))
    (fun k => continuousOn_const.mul (hterm k))
    (leviBoxMajorant_width_summable C T lam τ₀ hC hT)
    ?_
  intro k p hp
  have hp1lo : τ₀ / 2 ≤ p.1 := hp.1.1
  have hp1hi : p.1 ≤ T := hp.1.2
  have hp1pos : 0 < p.1 := lt_of_lt_of_le (by linarith) hp1lo
  have hlamp1 : (0 : ℝ) < lam * p.1 := mul_pos hlam hp1pos
  have hlamτ₀2 : (0 : ℝ) < lam * τ₀ / 2 := by positivity
  have hle : lam * τ₀ / 2 ≤ lam * p.1 := by nlinarith
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  calc |iterE E (k + 1) p.1 p.2 0|
      ≤ C ^ (k + 1) * iterKernelW lam (0 : ℝ) (k + 1) p.1 p.2 0 :=
        hmajor k p.1 p.2 0 hp1pos hp1hi
    _ = C ^ (k + 1) * (modelCoeff (0 : ℝ) p.1 (k + 1) * gaussDdim (lam * p.1) p.2) := by
        rw [iterKernelW_width0_factor lam p.1 hlam hp1pos p.2 k]
    _ ≤ C ^ (k + 1) * (modelCoeff (0 : ℝ) T (k + 1) * gaussDdim (lam * τ₀ / 2) (0 : Point n)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hC (k + 1))
        refine mul_le_mul (QIQTH.LeviMTest.modelCoeff_zero_mono_time k hp1pos hp1hi) ?_
          (gaussDdim_pos (lam * p.1) hlamp1 p.2).le
          (modelCoeff_pos (0 : ℝ) T (by norm_num) hT (k := k + 1) (by omega)).le
        exact le_trans
          (QIQTH.HeatResidualBound.gaussDdim_le_diagonal hlamp1 p.2)
          (QIQTH.HeatResidualBound.gaussDdim_zero_antitone hlamτ₀2 hle)
    _ = gaussDdim (lam * τ₀ / 2) (0 : Point n) * (C ^ (k + 1) * modelCoeff (0 : ℝ) T (k + 1)) := by
        ring

/-! ###############################################################################
    ### (W4) — the strip capstone and the width-generic every-ceiling `hBcontEvery`.
    ############################################################################### -/

/-- **★★ (W4) `leviSeries_stripContOn_width` — THE PER-CEILING STRIP CONTINUITY (width-generic).**  The
    Levi slice `p ↦ leviSeries E p.1 p.2 0` is jointly `ContinuousOn` the positive-time strip
    `Ioc 0 T ×ˢ univ`, lifting the (W3) box continuities through `JointContinuityAtoms.stripContOn_of_boxes`.
    Width-2 mirror: `LeviMTest.leviSeries_stripContOn`.  Carried: `hmajor` (width-`lam` domination) +
    the x-slot termwise box family `htermBox`.  NOT `a₁ = R/6`. -/
theorem leviSeries_stripContOn_width
    (E : ℝ → Point n → Point n → ℝ) (C T lam : ℝ) (hC : 0 ≤ C) (hT : 0 < T) (hlam : 0 < lam)
    (hmajor : ∀ (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW lam (0 : ℝ) (k + 1) τ p q)
    (htermBox : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) := by
  refine stripContOn_of_boxes (fun p : ℝ × Point n => leviSeries E p.1 p.2 0) T ?_
  intro τ₀ hτ₀ R
  exact leviSeries_boxContOn_width E C T lam τ₀ R hC hT hlam hτ₀.1 hτ₀.2 hmajor (htermBox τ₀ hτ₀ R)

/-- **★★★ (W4) `hBcontEvery_of_carries_width` — THE WIDTH-GENERIC `hBcontEvery` CARRY.**  The
    EVERY-CEILING joint continuity of the Levi slice: for EVERY ceiling `Tc : ℝ`,
        `ContinuousOn (fun p => leviSeries E p.1 p.2 0) (Ioc 0 Tc ×ˢ univ)`,
    from the width-`lam` domination (`hmajor`, ceiling-form) and the x-slot termwise box family
    (`htermBoxEvery`).  This is the verbatim `hBcontEvery` shape consumed by
    `WhiteHcontWitnessFactor.white_hInnerCont_leviJoint`'s `hJoint` carry (at ceiling `u`), now at the
    whitened width `lam` (no `lam = 2` coincidence needed).  Positive ceilings reduce to
    `leviSeries_stripContOn_width`; degenerate `Tc ≤ 0` give the empty domain.  Width-2 mirror:
    `LeviMTest.hBcontEvery_of_carries`.  NOT `a₁ = R/6`. -/
theorem hBcontEvery_of_carries_width
    (E : ℝ → Point n → Point n → ℝ) (C lam : ℝ) (hC : 0 ≤ C) (hlam : 0 < lam)
    (hmajor : ∀ (Tc : ℝ) (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ Tc →
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW lam (0 : ℝ) (k + 1) τ p q)
    (htermBoxEvery : ∀ Tc : ℝ, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) Tc, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) Tc ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ Tc : ℝ, ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Ioc (0 : ℝ) Tc ×ˢ (Set.univ : Set (Point n))) := by
  intro Tc
  by_cases hTc : (0 : ℝ) < Tc
  · exact leviSeries_stripContOn_width E C Tc lam hC hTc hlam (hmajor Tc) (htermBoxEvery Tc)
  · have hempty : Set.Ioc (0 : ℝ) Tc = ∅ := Set.Ioc_eq_empty hTc
    rw [hempty, Set.empty_prod]
    exact continuousOn_empty _

/-! ###############################################################################
    ### (W5) — the WINDOWED `hJoint`-shape corollary (the exact carry consumer).
    ############################################################################### -/

/-- **★★★ (W5) `leviJoint_window_of_carries_width` — THE `hJoint` CARRY, width-generic.**  Produces the
    EXACT shape consumed by `WhiteHcontWitnessFactor.white_hInnerCont_leviJoint`'s `hJoint` argument:
        `∀ u ∈ U, ContinuousOn (fun p => leviSeries E p.1 p.2 0) (Ioc 0 u ×ˢ univ)`,
    from the two width-`lam` carries — the per-window domination `hmajor` and the per-window x-slot
    termwise box-continuity family `htermBox`.  Per `u ∈ U`: positive `u` reduces to
    `leviSeries_stripContOn_width` (ceiling `T = u`); degenerate `u ≤ 0` gives the empty domain.
    Instantiating `E := whiteDefectKernel κ hκ hKc S a b` and `lam := whiteLam` discharges the whole
    `hJoint` carry MODULO exactly `{hmajor, htermBox}` at the whitened width — where `htermBox` IS the
    whitened `iterE` TERMWISE joint continuity (the surviving M-test residual).  NOT `a₁ = R/6`. -/
theorem leviJoint_window_of_carries_width
    (E : ℝ → Point n → Point n → ℝ) (C lam : ℝ) (hC : 0 ≤ C) (hlam : 0 < lam) (U : Set ℝ)
    (hmajor : ∀ u ∈ U, ∀ (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ u →
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW lam (0 : ℝ) (k + 1) τ p q)
    (htermBox : ∀ u ∈ U, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) u, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) u ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ u ∈ U, ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (Point n))) := by
  intro u hu
  by_cases hup : (0 : ℝ) < u
  · exact leviSeries_stripContOn_width E C u lam hC hup hlam (hmajor u hu) (htermBox u hu)
  · have hempty : Set.Ioc (0 : ℝ) u = ∅ := Set.Ioc_eq_empty hup
    rw [hempty, Set.empty_prod]
    exact continuousOn_empty _

#check @iterKernelW_width0_factor
#check @leviBoxMajorant_width_summable
#check @leviSeries_boxContOn_width
#check @leviSeries_stripContOn_width
#check @hBcontEvery_of_carries_width
#check @leviJoint_window_of_carries_width

end QIQTH.WhiteLeviMTestWidth

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteLeviMTestWidth
#print axioms iterKernelW_width0_factor
#print axioms leviBoxMajorant_width_summable
#print axioms leviSeries_boxContOn_width
#print axioms leviSeries_stripContOn_width
#print axioms hBcontEvery_of_carries_width
#print axioms leviJoint_window_of_carries_width
end AxiomChecks
