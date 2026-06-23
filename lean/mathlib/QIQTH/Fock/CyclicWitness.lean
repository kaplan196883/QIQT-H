/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The concrete cyclic Reeh–Schlieder witness

This file assembles the cyclic discharge: a concrete wedge-supported nice generator (a smooth
compactly-supported bump centred deep in the right wedge), whose boost orbit is total in `L²` once its
one-particle amplitude is not a.e. zero — discharging `NiceWedgeCyclic m` (modulo the single concrete
fact `Krep m (bump) ≢ 0`) via the complete Wiener–Tauberian machinery of `QIQTH.Fock.WienerL2`.
-/
import QIQTH.Fock.BoostKMS
import QIQTH.Fock.LocalizedWitness
import Mathlib.Analysis.Calculus.BumpFunction.Normed

namespace QIQTH.Fock.CyclicWitness

open MeasureTheory Metric
open scoped ContDiff
open QIQTH.Fock.Localization QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW QIQTH.Fock.BoostKMS
  QIQTH.Fock.WienerL2

/-- **A concrete wedge-supported nice generator**: the bump centred at `(0, 10)` (well inside the right
    wedge), with margin `δ = 6`.  Its support has `|x⁰| ≤ 2`, `|x¹ − 10| ≤ 2`, so `x¹ − x⁰ ≥ 6` and
    `x¹ + x⁰ ≥ 6`; `Krep ∈ L²` is automatic (`bumpC_Krep_memLp`). -/
noncomputable def bumpNiceTest (m : ℝ) (hm : m ≠ 0) : NiceTest m where
  f := bumpC 0 10
  cont := bumpC_continuous 0 10
  cpt := bumpC_hasCompactSupport 0 10
  δ := 6
  hδ := by norm_num
  margin := fun x hx => by
    have hsupp : x ∈ Function.support (bumpReal 0 10) := by
      simpa only [bumpC, Function.mem_support, Complex.ofReal_ne_zero] using hx
    obtain ⟨h0, h1⟩ := bumpReal_support_subset 0 10 hsupp
    rw [sub_zero, abs_le] at h0
    rw [abs_le] at h1
    exact ⟨by linarith [h0.1, h0.2, h1.1, h1.2], by linarith [h0.1, h0.2, h1.1, h1.2]⟩
  real := bumpC_real 0 10
  memLp := bumpC_Krep_memLp m 0 10 hm

/-- **★★★ `NiceWedgeCyclic` from the concrete bump generator**, modulo its amplitude being nonzero.
    The single remaining concrete analytic fact for the cyclic Reeh–Schlieder discharge is
    `Krep m (bumpC 0 10) ≢ 0` — that the wedge bump has a nonzero one-particle amplitude.  Given it,
    the whole cyclic input is discharged: `niceWedgeCyclic_of_fourier_ne_zero` fed by the complete Wiener
    theorem (`fourierL2_Krep_ne_zero`). -/
theorem niceWedgeCyclic_bump (m : ℝ) (hm : m ≠ 0)
    (hKrep : ¬ (Krep m (⇑((bumpC_hasCompactSupport (0 : ℝ) 10).toSchwartzMap
        (bumpC_contDiff 0 10))) =ᵐ[volume] (0 : ℝ → ℂ))) :
    NiceWedgeCyclic m :=
  niceWedgeCyclic_of_fourier_ne_zero m (bumpNiceTest m hm)
    (fourierL2_Krep_ne_zero
      ((bumpC_hasCompactSupport 0 10).toSchwartzMap (bumpC_contDiff 0 10)) hm hKrep)

/-- **The Minkowski–Fourier transform of a product bump factorizes** into two 1D bump Fourier integrals
    (Fubini over `Fin 2 → ℝ`, `integral_fintype_prod_volume_eq_prod`).  The entry point for the amplitude
    nonvanishing: each factor is a 1D Fourier integral of a `ContDiffBump`. -/
theorem minkowskiFourier_bumpC (cT cX : ℝ) (p : V) :
    minkowskiFourier (bumpC cT cX) p
      = (∫ y : ℝ, Complex.exp (-Complex.I * (p 0 * y : ℝ)) * (↑(bump1 cT y) : ℂ))
        * (∫ y : ℝ, Complex.exp (Complex.I * (p 1 * y : ℝ)) * (↑(bump1 cX y) : ℂ)) := by
  rw [minkowskiFourier]
  have key : (fun x : V =>
        Complex.exp (-Complex.I * ((minkowskiDot p x : ℝ) : ℂ)) * bumpC cT cX x)
      = fun x : V => ∏ i : Fin 2,
          (![fun y : ℝ => Complex.exp (-Complex.I * (p 0 * y : ℝ)) * (↑(bump1 cT y) : ℂ),
             fun y : ℝ => Complex.exp (Complex.I * (p 1 * y : ℝ)) * (↑(bump1 cX y) : ℂ)] i) (x i) := by
    funext x
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, bumpC, bumpReal,
      minkowskiDot, Complex.ofReal_mul, Complex.ofReal_sub]
    rw [show (-Complex.I * ((p 0 : ℂ) * (x 0 : ℂ) - (p 1 : ℂ) * (x 1 : ℂ)))
        = -Complex.I * ((p 0 : ℂ) * (x 0 : ℂ)) + Complex.I * ((p 1 : ℂ) * (x 1 : ℂ)) by ring,
      Complex.exp_add]
    push_cast
    ring
  rw [key, integral_fintype_prod_volume_eq_prod, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **The bump amplitude at `θ = 0`**, factored: `Krep m (bumpC cT cX) 0 = (1/√2)·A(m)·∫bump1 cX`, where
    `A(m) = ∫ e^{−imy}·bump1 cT(y) dy` (the shell point is `(m, 0)`, so the second factor's phase is `e^0 = 1`).
    Reduces the amplitude nonvanishing to `A(m) ≠ 0` (the second factor `∫ bump1 cX > 0`). -/
theorem Krep_bumpC_zero (m cT cX : ℝ) :
    Krep m (bumpC cT cX) 0
      = (1 / Real.sqrt 2 : ℂ)
        * ((∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 cT y) : ℂ))
          * (∫ y : ℝ, (↑(bump1 cX y) : ℂ))) := by
  rw [Krep, minkowskiFourier_bumpC]
  simp only [massShell_zero, massShell_one, Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero,
    zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]

/-- **The amplitude nonvanishing, reduced to ONE 1D Fourier integral.**  `Krep m (bumpC cT cX) ≢ 0` holds
    as soon as the 1D bump Fourier integral `A(m) = ∫ e^{−imy}·bump1 cT(y) dy ≠ 0` (the other factor
    `∫ bump1 cX > 0` is `ContDiffBump.integral_pos`; `Krep` is continuous, so `≢ᵐ0 ⟺ ∃θ≠0`). -/
theorem Krep_bumpC_ne_zero_of (m cT cX : ℝ)
    (hA : (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 cT y) : ℂ)) ≠ 0) :
    ¬ (Krep m (bumpC cT cX) =ᵐ[volume] (0 : ℝ → ℂ)) := by
  have hB : (∫ y : ℝ, (↑(bump1 cX y) : ℂ)) ≠ 0 := by
    have hofReal : (∫ y : ℝ, (↑(bump1 cX y) : ℂ)) = ((∫ y : ℝ, bump1 cX y : ℝ) : ℂ) :=
      integral_ofReal
    rw [hofReal]
    exact_mod_cast (bump1 cX).integral_pos.ne'
  have hsqrt : (1 / Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, one_ne_zero, Complex.ofReal_eq_zero, false_or]
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  intro hae
  have hcont : Continuous (Krep m (bumpC cT cX)) :=
    Krep_continuous
      ((bumpC_continuous cT cX).integrable_of_hasCompactSupport (bumpC_hasCompactSupport cT cX))
  have h0 : Krep m (bumpC cT cX) 0 = 0 :=
    congrFun ((hcont.ae_eq_iff_eq volume continuous_zero).mp hae) 0
  rw [Krep_bumpC_zero] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact hsqrt h
  · rcases mul_eq_zero.mp h with h | h
    · exact hA h
    · exact hB h

/-- The real part of the 1D bump Fourier integrand: `Re(e^{−imy}·bump1 0(y)) = cos(my)·bump1 0(y)`. -/
theorem bump1_fourier_re_eq (m y : ℝ) :
    (Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ)).re
      = Real.cos (m * y) * bump1 0 y := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  congr 1
  rw [show -Complex.I * ((m * y : ℝ) : ℂ) = ((-(m * y) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- **★★★★★ The cyclic Reeh–Schlieder discharge, reduced to a single 1D Fourier integral.**
    `NiceWedgeCyclic m` holds as soon as the 1D bump Fourier integral `∫ e^{−imy}·bump1 0(y) dy ≠ 0`.
    Everything else — the complete Wiener–Tauberian theorem, the FT-holomorphy and L²↔L¹ agreement
    (both built from scratch), the `NiceTest` construction, and the bump amplitude factorization — is
    machine-checked and axiom-free.  This is the irreducible concrete analytic input of the free-field
    one-particle Bisognano–Wichmann's cyclic side. -/
theorem niceWedgeCyclic_of_bump_fourier_ne_zero (m : ℝ) (hm : m ≠ 0)
    (hA : (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ)) ≠ 0) :
    NiceWedgeCyclic m :=
  niceWedgeCyclic_bump m hm (Krep_bumpC_ne_zero_of m 0 10 hA)

/-- **The 1D bump Fourier integral is nonzero for `0 < m < π/4`** (the fixed radius-2 bump): its real part
    `∫ cos(my)·bump1 0(y) dy > 0`, since `cos(my) > 0` on the support `|y| < 2` (as `|my| < 2m < π/2`).
    Via `RCLike.integral_re` + `bump1_fourier_re_eq` + `integral_pos_iff_support_of_nonneg`. -/
theorem bump1_fourier_ne_zero {m : ℝ} (hm0 : 0 < m) (hmπ : m < Real.pi / 4) :
    (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ)) ≠ 0 := by
  have hbnn : ∀ y : ℝ, 0 ≤ bump1 0 y := fun y => (bump1 0).nonneg
  have hcontc : Continuous (fun y : ℝ => Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ)) :=
    (Complex.continuous_exp.comp (by fun_prop)).mul
      (Complex.continuous_ofReal.comp (bump1 0).continuous)
  have hcsc : HasCompactSupport (fun y : ℝ => Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ)) :=
    ((bump1 0).hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).mul_left
  have hint : Integrable (fun y : ℝ => Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ)) :=
    hcontc.integrable_of_hasCompactSupport hcsc
  -- `cos(my) > 0` on the bump support `|y| ≤ 2` (since `|my| < 2m < π/2`)
  have hcos_pos : ∀ y : ℝ, |y| ≤ 2 → 0 < Real.cos (m * y) := by
    intro y hy
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo, ← abs_lt, abs_mul, abs_of_pos hm0]
    calc m * |y| ≤ m * 2 := by nlinarith
      _ < Real.pi / 2 := by linarith
  have hcosnn : ∀ y : ℝ, 0 ≤ Real.cos (m * y) * bump1 0 y := by
    intro y
    rcases eq_or_lt_of_le (hbnn y) with hb | hb
    · rw [← hb, mul_zero]
    · have hy : |y| < 2 := by
        have hmem : y ∈ Function.support (bump1 0) := Function.mem_support.mpr hb.ne'
        rw [(bump1 0).support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
        simpa using hmem
      have := hcos_pos y hy.le
      positivity
  have hcosint : Integrable (fun y : ℝ => Real.cos (m * y) * bump1 0 y) :=
    ((Real.continuous_cos.comp (by fun_prop)).mul (bump1 0).continuous).integrable_of_hasCompactSupport
      (bump1 0).hasCompactSupport.mul_left
  have hpos : 0 < ∫ y : ℝ, Real.cos (m * y) * bump1 0 y := by
    rw [integral_pos_iff_support_of_nonneg hcosnn hcosint]
    have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ Function.support (fun y => Real.cos (m * y) * bump1 0 y) := by
      intro y hy
      rw [Function.mem_support]
      have hyb : |y| ≤ 1 := abs_le.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      have hb1 : bump1 0 y = 1 := (bump1 0).one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hyb)
      have hcos : 0 < Real.cos (m * y) := hcos_pos y (hyb.trans (by norm_num))
      rw [hb1, mul_one]; exact hcos.ne'
    calc (0 : ENNReal) < volume (Set.Ioo (-1 : ℝ) 1) := by rw [Real.volume_Ioo]; norm_num
      _ ≤ _ := measure_mono hsub
  -- assemble: Re(∫) = ∫ cos·bump > 0, so ∫ ≠ 0
  intro h
  have hre : (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ)).re
      = ∫ y : ℝ, Real.cos (m * y) * bump1 0 y := by
    rw [show ((∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ)).re)
        = RCLike.re (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ)) from rfl,
      ← integral_re hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show RCLike.re (Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1 0 y) : ℂ))
        = Real.cos (m * y) * bump1 0 y
    rw [RCLike.re_to_complex]
    exact bump1_fourier_re_eq m y
  rw [h, Complex.zero_re] at hre
  linarith [hpos]

/-- **★★★★★★ THE CYCLIC REEH–SCHLIEDER INPUT, UNCONDITIONALLY DISCHARGED for `0 < m < π/4`, axiom-free.**
    `NiceWedgeCyclic m` holds with no hypotheses for masses in `(0, π/4)`: the concrete wedge bump `bumpC 0 10`
    has nonzero one-particle amplitude (`bump1_fourier_ne_zero` via `cos`-positivity on the bump support), and
    the complete Wiener–Tauberian machinery (`niceWedgeCyclic_of_bump_fourier_ne_zero`) does the rest.  The free-
    field one-particle Bisognano–Wichmann's cyclic side is now a *theorem*, not a hypothesis, for this mass range —
    every step (Wiener theorem, FT-holomorphy, L²↔L¹ agreement, witness, amplitude) machine-checked and axiom-free.
    General `m > 0` follows the same chain with a radius-scaled bump. -/
theorem niceWedgeCyclic_small_mass {m : ℝ} (hm0 : 0 < m) (hmπ : m < Real.pi / 4) :
    NiceWedgeCyclic m :=
  niceWedgeCyclic_of_bump_fourier_ne_zero m hm0.ne' (bump1_fourier_ne_zero hm0 hmπ)

/-! ### General mass `m > 0`: the width-scaled bump

For `m ≥ π/4` the *fixed* radius-2 bump's amplitude `A(m)` can vanish (the bump's Fourier transform has
real zeros), so the `θ = 0`-value route stalls.  The fix is a bump of radius `R` chosen so small that
`m·R < π/2` — then `cos(m y) > 0` on the *whole* support and the real part of the amplitude is a strictly
positive integral exactly as before.  Picking `R = π/(4m)` gives `m·R = π/4 < π/2` for every `m > 0`,
discharging `NiceWedgeCyclic m` unconditionally for all positive masses. -/

/-- A width-`R` 1D bump (`rIn = R/2`, `rOut = R`). -/
noncomputable def bump1W (R : ℝ) (hR : 0 < R) (c : ℝ) : ContDiffBump c :=
  ⟨R / 2, R, by linarith, by linarith⟩

@[simp] theorem bump1W_rOut (R : ℝ) (hR : 0 < R) (c : ℝ) : (bump1W R hR c).rOut = R := rfl

@[simp] theorem bump1W_rIn (R : ℝ) (hR : 0 < R) (c : ℝ) : (bump1W R hR c).rIn = R / 2 := rfl

/-- The width-`R` 2D product bump on `V = Fin 2 → ℝ`. -/
noncomputable def bumpRealW (R : ℝ) (hR : 0 < R) (cT cX : ℝ) : V → ℝ :=
  fun x => bump1W R hR cT (x 0) * bump1W R hR cX (x 1)

noncomputable def bumpCW (R : ℝ) (hR : 0 < R) (cT cX : ℝ) : V → ℂ :=
  fun x => ((bumpRealW R hR cT cX x : ℝ) : ℂ)

theorem bumpRealW_contDiff (R : ℝ) (hR : 0 < R) (cT cX : ℝ) :
    ContDiff ℝ ∞ (bumpRealW R hR cT cX) := by
  have h0 : ContDiff ℝ ∞ (fun x : V => bump1W R hR cT (x 0)) :=
    (bump1W R hR cT).contDiff.comp (contDiff_apply ℝ ℝ 0)
  have h1 : ContDiff ℝ ∞ (fun x : V => bump1W R hR cX (x 1)) :=
    (bump1W R hR cX).contDiff.comp (contDiff_apply ℝ ℝ 1)
  exact h0.mul h1

theorem bumpCW_contDiff (R : ℝ) (hR : 0 < R) (cT cX : ℝ) : ContDiff ℝ ∞ (bumpCW R hR cT cX) :=
  Complex.ofRealCLM.contDiff.comp (bumpRealW_contDiff R hR cT cX)

theorem bumpCW_continuous (R : ℝ) (hR : 0 < R) (cT cX : ℝ) : Continuous (bumpCW R hR cT cX) :=
  (bumpCW_contDiff R hR cT cX).continuous

theorem bumpCW_real (R : ℝ) (hR : 0 < R) (cT cX : ℝ) (x : V) :
    (starRingEnd ℂ) (bumpCW R hR cT cX x) = bumpCW R hR cT cX x := by
  simp [bumpCW]

theorem bumpRealW_support_subset (R : ℝ) (hR : 0 < R) (cT cX : ℝ) :
    Function.support (bumpRealW R hR cT cX) ⊆ {x : V | |x 0 - cT| ≤ R ∧ |x 1 - cX| ≤ R} := by
  intro x hx
  simp only [Function.mem_support, bumpRealW, mul_ne_zero_iff] at hx
  obtain ⟨h0, h1⟩ := hx
  have hb0 : x 0 ∈ Metric.ball cT (bump1W R hR cT).rOut :=
    (bump1W R hR cT).support_eq ▸ Function.mem_support.mpr h0
  have hb1 : x 1 ∈ Metric.ball cX (bump1W R hR cX).rOut :=
    (bump1W R hR cX).support_eq ▸ Function.mem_support.mpr h1
  rw [bump1W_rOut, Metric.mem_ball, Real.dist_eq] at hb0
  rw [bump1W_rOut, Metric.mem_ball, Real.dist_eq] at hb1
  exact ⟨hb0.le, hb1.le⟩

theorem bumpCW_hasCompactSupport (R : ℝ) (hR : 0 < R) (cT cX : ℝ) :
    HasCompactSupport (bumpCW R hR cT cX) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : V) (|cT| + |cX| + 2 * R)) (fun x hx => ?_)
  simp only [bumpCW, Complex.ofReal_eq_zero]
  by_contra h
  obtain ⟨hT, hX⟩ := bumpRealW_support_subset R hR cT cX (Function.mem_support.mpr h)
  apply hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity),
    Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (x 0) cT
    linarith [hT, abs_nonneg cX, abs_nonneg cT, hR.le]
  · rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (x 1) cX
    linarith [hX, abs_nonneg cX, abs_nonneg cT, hR.le]

/-- `Krep ∈ L²` for the width-`R` bump (smooth, compactly supported). -/
theorem bumpCW_Krep_memLp (m R : ℝ) (hR : 0 < R) (cT cX : ℝ) (hm : m ≠ 0) :
    MemLp (Krep m (bumpCW R hR cT cX)) 2 (volume : Measure ℝ) :=
  schwartz_Krep_memLp
    ((bumpCW_hasCompactSupport R hR cT cX).toSchwartzMap (bumpCW_contDiff R hR cT cX)) hm

/-- A width-`R` wedge-supported nice generator centred at `(0, cX)` with `2R < cX` (margin `δ = cX − 2R`). -/
noncomputable def bumpNiceTestW (m R cX : ℝ) (hR : 0 < R) (hm : m ≠ 0) (hcX : 2 * R < cX) :
    NiceTest m where
  f := bumpCW R hR 0 cX
  cont := bumpCW_continuous R hR 0 cX
  cpt := bumpCW_hasCompactSupport R hR 0 cX
  δ := cX - 2 * R
  hδ := by linarith
  margin := fun x hx => by
    have hsupp : x ∈ Function.support (bumpRealW R hR 0 cX) := by
      simpa only [bumpCW, Function.mem_support, Complex.ofReal_ne_zero] using hx
    obtain ⟨h0, h1⟩ := bumpRealW_support_subset R hR 0 cX hsupp
    rw [sub_zero, abs_le] at h0
    rw [abs_le] at h1
    exact ⟨by linarith [h0.1, h0.2, h1.1, h1.2], by linarith [h0.1, h0.2, h1.1, h1.2]⟩
  real := bumpCW_real R hR 0 cX
  memLp := bumpCW_Krep_memLp m R hR 0 cX hm

/-- `NiceWedgeCyclic` from the width-`R` bump generator, modulo its amplitude being nonzero. -/
theorem niceWedgeCyclic_bumpW (m R cX : ℝ) (hR : 0 < R) (hm : m ≠ 0) (hcX : 2 * R < cX)
    (hKrep : ¬ (Krep m (⇑((bumpCW_hasCompactSupport R hR 0 cX).toSchwartzMap
        (bumpCW_contDiff R hR 0 cX))) =ᵐ[volume] (0 : ℝ → ℂ))) :
    NiceWedgeCyclic m :=
  niceWedgeCyclic_of_fourier_ne_zero m (bumpNiceTestW m R cX hR hm hcX)
    (fourierL2_Krep_ne_zero
      ((bumpCW_hasCompactSupport R hR 0 cX).toSchwartzMap (bumpCW_contDiff R hR 0 cX)) hm hKrep)

/-- The width-`R` amplitude factorizes (Fubini), mirroring `minkowskiFourier_bumpC`. -/
theorem minkowskiFourier_bumpCW (R : ℝ) (hR : 0 < R) (cT cX : ℝ) (p : V) :
    minkowskiFourier (bumpCW R hR cT cX) p
      = (∫ y : ℝ, Complex.exp (-Complex.I * (p 0 * y : ℝ)) * (↑(bump1W R hR cT y) : ℂ))
        * (∫ y : ℝ, Complex.exp (Complex.I * (p 1 * y : ℝ)) * (↑(bump1W R hR cX y) : ℂ)) := by
  rw [minkowskiFourier]
  have key : (fun x : V =>
        Complex.exp (-Complex.I * ((minkowskiDot p x : ℝ) : ℂ)) * bumpCW R hR cT cX x)
      = fun x : V => ∏ i : Fin 2,
          (![fun y : ℝ => Complex.exp (-Complex.I * (p 0 * y : ℝ)) * (↑(bump1W R hR cT y) : ℂ),
             fun y : ℝ => Complex.exp (Complex.I * (p 1 * y : ℝ)) * (↑(bump1W R hR cX y) : ℂ)] i) (x i) := by
    funext x
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, bumpCW, bumpRealW,
      minkowskiDot, Complex.ofReal_mul, Complex.ofReal_sub]
    rw [show (-Complex.I * ((p 0 : ℂ) * (x 0 : ℂ) - (p 1 : ℂ) * (x 1 : ℂ)))
        = -Complex.I * ((p 0 : ℂ) * (x 0 : ℂ)) + Complex.I * ((p 1 : ℂ) * (x 1 : ℂ)) by ring,
      Complex.exp_add]
    push_cast
    ring
  rw [key, integral_fintype_prod_volume_eq_prod, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The width-`R` bump amplitude at `θ = 0`, factored. -/
theorem Krep_bumpCW_zero (m R : ℝ) (hR : 0 < R) (cT cX : ℝ) :
    Krep m (bumpCW R hR cT cX) 0
      = (1 / Real.sqrt 2 : ℂ)
        * ((∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR cT y) : ℂ))
          * (∫ y : ℝ, (↑(bump1W R hR cX y) : ℂ))) := by
  rw [Krep, minkowskiFourier_bumpCW]
  simp only [massShell_zero, massShell_one, Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero,
    zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]

/-- The width-`R` amplitude is `≢ 0` as soon as the 1D integral `∫ e^{−imy}·bump1W R cT(y) dy ≠ 0`. -/
theorem Krep_bumpCW_ne_zero_of (m R : ℝ) (hR : 0 < R) (cT cX : ℝ)
    (hA : (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR cT y) : ℂ)) ≠ 0) :
    ¬ (Krep m (bumpCW R hR cT cX) =ᵐ[volume] (0 : ℝ → ℂ)) := by
  have hB : (∫ y : ℝ, (↑(bump1W R hR cX y) : ℂ)) ≠ 0 := by
    have hofReal : (∫ y : ℝ, (↑(bump1W R hR cX y) : ℂ)) = ((∫ y : ℝ, bump1W R hR cX y : ℝ) : ℂ) :=
      integral_ofReal
    rw [hofReal]
    exact_mod_cast (bump1W R hR cX).integral_pos.ne'
  have hsqrt : (1 / Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, one_ne_zero, Complex.ofReal_eq_zero, false_or]
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  intro hae
  have hcont : Continuous (Krep m (bumpCW R hR cT cX)) :=
    Krep_continuous
      ((bumpCW_continuous R hR cT cX).integrable_of_hasCompactSupport
        (bumpCW_hasCompactSupport R hR cT cX))
  have h0 : Krep m (bumpCW R hR cT cX) 0 = 0 :=
    congrFun ((hcont.ae_eq_iff_eq volume continuous_zero).mp hae) 0
  rw [Krep_bumpCW_zero] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact hsqrt h
  · rcases mul_eq_zero.mp h with h | h
    · exact hA h
    · exact hB h

/-- The real part of the 1D Fourier integrand for an arbitrary real weight `g`: `Re(e^{−imy}·g(y)) = cos(my)·g(y)`. -/
theorem fourier_re_eq (g : ℝ → ℝ) (m y : ℝ) :
    (Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(g y) : ℂ)).re = Real.cos (m * y) * g y := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  congr 1
  rw [show -Complex.I * ((m * y : ℝ) : ℂ) = ((-(m * y) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- **The width-`R` 1D bump Fourier integral is nonzero whenever `m·R < π/2`**: its real part
    `∫ cos(my)·bump1W R 0(y) dy > 0`, since `cos(my) > 0` on the support `|y| < R` (as `|my| ≤ mR < π/2`). -/
theorem bump1W_fourier_ne_zero {m R : ℝ} (hm0 : 0 < m) (hR : 0 < R) (hmR : m * R < Real.pi / 2) :
    (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR 0 y) : ℂ)) ≠ 0 := by
  have hbnn : ∀ y : ℝ, 0 ≤ bump1W R hR 0 y := fun y => (bump1W R hR 0).nonneg
  have hcontc : Continuous
      (fun y : ℝ => Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR 0 y) : ℂ)) :=
    (Complex.continuous_exp.comp (by fun_prop)).mul
      (Complex.continuous_ofReal.comp (bump1W R hR 0).continuous)
  have hcsc : HasCompactSupport
      (fun y : ℝ => Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR 0 y) : ℂ)) :=
    ((bump1W R hR 0).hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).mul_left
  have hint : Integrable
      (fun y : ℝ => Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR 0 y) : ℂ)) :=
    hcontc.integrable_of_hasCompactSupport hcsc
  have hcos_pos : ∀ y : ℝ, |y| ≤ R → 0 < Real.cos (m * y) := by
    intro y hy
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo, ← abs_lt, abs_mul, abs_of_pos hm0]
    calc m * |y| ≤ m * R := mul_le_mul_of_nonneg_left hy hm0.le
      _ < Real.pi / 2 := hmR
  have hcosnn : ∀ y : ℝ, 0 ≤ Real.cos (m * y) * bump1W R hR 0 y := by
    intro y
    rcases eq_or_lt_of_le (hbnn y) with hb | hb
    · rw [← hb, mul_zero]
    · have hy : |y| < R := by
        have hmem : y ∈ Function.support (bump1W R hR 0) := Function.mem_support.mpr hb.ne'
        rw [(bump1W R hR 0).support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, bump1W_rOut] at hmem
        exact hmem
      have := hcos_pos y hy.le
      positivity
  have hcosint : Integrable (fun y : ℝ => Real.cos (m * y) * bump1W R hR 0 y) :=
    ((Real.continuous_cos.comp (by fun_prop)).mul
      (bump1W R hR 0).continuous).integrable_of_hasCompactSupport
      (bump1W R hR 0).hasCompactSupport.mul_left
  have hpos : 0 < ∫ y : ℝ, Real.cos (m * y) * bump1W R hR 0 y := by
    rw [integral_pos_iff_support_of_nonneg hcosnn hcosint]
    have hsub : Set.Ioo (-(R / 2)) (R / 2)
        ⊆ Function.support (fun y => Real.cos (m * y) * bump1W R hR 0 y) := by
      intro y hy
      rw [Function.mem_support]
      have hyb : |y| ≤ R / 2 := abs_le.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      have hb1 : bump1W R hR 0 y = 1 := (bump1W R hR 0).one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, bump1W_rIn]; exact hyb)
      have hcos : 0 < Real.cos (m * y) := hcos_pos y (hyb.trans (by linarith))
      rw [hb1, mul_one]; exact hcos.ne'
    calc (0 : ENNReal) < volume (Set.Ioo (-(R / 2)) (R / 2)) := by
          rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
      _ ≤ _ := measure_mono hsub
  intro h
  have hre : (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR 0 y) : ℂ)).re
      = ∫ y : ℝ, Real.cos (m * y) * bump1W R hR 0 y := by
    rw [show ((∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR 0 y) : ℂ)).re)
        = RCLike.re (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR 0 y) : ℂ)) from rfl,
      ← integral_re hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show RCLike.re (Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR 0 y) : ℂ))
        = Real.cos (m * y) * bump1W R hR 0 y
    rw [RCLike.re_to_complex]
    exact fourier_re_eq (fun t => bump1W R hR 0 t) m y
  rw [h, Complex.zero_re] at hre
  linarith [hpos]

/-- **`NiceWedgeCyclic` from a width-`R` bump whose 1D amplitude is nonzero.** -/
theorem niceWedgeCyclic_of_bumpW_fourier_ne_zero (m R cX : ℝ) (hR : 0 < R) (hm : m ≠ 0)
    (hcX : 2 * R < cX)
    (hA : (∫ y : ℝ, Complex.exp (-Complex.I * (m * y : ℝ)) * (↑(bump1W R hR 0 y) : ℂ)) ≠ 0) :
    NiceWedgeCyclic m :=
  niceWedgeCyclic_bumpW m R cX hR hm hcX (Krep_bumpCW_ne_zero_of m R hR 0 cX hA)

/-- **★★★★★★★ THE CYCLIC REEH–SCHLIEDER INPUT, UNCONDITIONALLY DISCHARGED FOR ALL `m > 0`, axiom-free.**
    `NiceWedgeCyclic m` holds with no hypotheses for *every* positive mass.  Take the width-`R` wedge bump
    with `R = π/(4m)`, centred at `(0, 2R+1)`: then `m·R = π/4 < π/2`, so `cos(m y) > 0` on its whole
    support and the amplitude's real part `∫ cos(m y)·bump1W R(y) dy > 0` (`bump1W_fourier_ne_zero`); the
    complete Wiener–Tauberian machinery does the rest.  The free-field one-particle Bisognano–Wichmann's
    cyclic Reeh–Schlieder input is now a *theorem*, not a hypothesis, for the full physical mass range
    `m > 0` — every step (Wiener theorem, FT-holomorphy, L²↔L¹ agreement, witness, amplitude) machine-checked
    and axiom-free.  This supersedes `niceWedgeCyclic_small_mass` (which is the `R = 2` special case). -/
theorem niceWedgeCyclic_pos_mass {m : ℝ} (hm0 : 0 < m) : NiceWedgeCyclic m := by
  have hR : (0 : ℝ) < Real.pi / (4 * m) := by positivity
  have hmR : m * (Real.pi / (4 * m)) < Real.pi / 2 := by
    have hmne : m ≠ 0 := hm0.ne'
    have key : m * (Real.pi / (4 * m)) = Real.pi / 4 := by field_simp
    rw [key]; linarith [Real.pi_pos]
  exact niceWedgeCyclic_of_bumpW_fourier_ne_zero m (Real.pi / (4 * m))
    (2 * (Real.pi / (4 * m)) + 1) hR hm0.ne' (by linarith) (bump1W_fourier_ne_zero hm0 hR hmR)

/-- **Strip boundary-uniqueness (top edge zero ⟹ bottom edge zero).**  A function `Φ` holomorphic on the open
    strip `{−1 < Im z < 0}`, continuous and bounded on the closed strip, that vanishes on the *entire* top edge
    (`Φ(t) = 0 ∀ real t`), vanishes on the bottom edge too (`Φ(t − i) = 0 ∀ t`).  Proof: the asymmetric Hadamard
    three-lines bound with top constant `0` gives `‖Φ z‖ ≤ 0^{1−s}·B^{s}` (`s = −Im z`), which is `0` for every
    interior point (`s < 1`), so `Φ` vanishes on the open strip; the bottom edge then follows by continuity
    (approach `t − i` from inside).  This is the modular/KMS uniqueness that the separating proof needs. -/
theorem strip_eqZero_of_top_edge_zero {Φ : ℂ → ℂ}
    (hdiff : DifferentiableOn ℂ Φ (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0))
    (hcont : ContinuousOn Φ (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0))
    (hbdd : BddAbove ((norm ∘ Φ) '' (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0)))
    (htop : ∀ t : ℝ, Φ (t : ℂ) = 0) :
    ∀ t : ℝ, Φ ((t : ℂ) - Complex.I) = 0 := by
  obtain ⟨B, hB⟩ := hbdd
  have hBmem : ∀ z : ℂ, -1 ≤ z.im → z.im ≤ 0 → ‖Φ z‖ ≤ B := fun z hz0 hz1 =>
    hB ⟨z, by rw [Set.mem_preimage, Set.mem_Icc]; exact ⟨hz0, hz1⟩, rfl⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hBmem 0 (by norm_num) (le_refl 0))
  -- interior + top vanishing via the asymmetric Hadamard three-lines (top edge constant 0)
  have hint : ∀ z : ℂ, -1 < z.im → z.im ≤ 0 → Φ z = 0 := by
    intro z hz0 hz1
    rw [← norm_le_zero_iff]
    set φ : ℂ → ℂ := fun w => -Complex.I * w with hφdef
    set G : ℂ → ℂ := fun w => Φ (φ w) with hGdef
    have hφim : ∀ w' : ℂ, (φ w').im = -w'.re := fun w' => by
      simp [hφdef, Complex.mul_im, Complex.mul_re]
    have hφre : ∀ w' : ℂ, (φ w').re = w'.im := fun w' => by
      simp [hφdef, Complex.mul_re, Complex.mul_im]
    set w : ℂ := Complex.I * z with hwdef
    have hφw : φ w = z := by
      simp only [hφdef, hwdef]
      rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    have hwre : w.re = -z.im := by rw [hwdef, Complex.mul_re, Complex.I_re, Complex.I_im]; ring
    have hφent : Differentiable ℂ φ := by rw [hφdef]; exact differentiable_id.const_mul _
    have hmaps_open : Set.MapsTo φ (Complex.HadamardThreeLines.verticalStrip 0 1)
        (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) := by
      intro w' hw'
      simp only [Complex.HadamardThreeLines.verticalStrip, Set.mem_preimage, Set.mem_Ioo] at hw'
      rw [Set.mem_preimage, Set.mem_Ioo, hφim]
      exact ⟨by linarith [hw'.2], by linarith [hw'.1]⟩
    have hmaps_closed : Set.MapsTo φ (Complex.HadamardThreeLines.verticalClosedStrip 0 1)
        (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0) := by
      intro w' hw'
      simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc] at hw'
      rw [Set.mem_preimage, Set.mem_Icc, hφim]
      exact ⟨by linarith [hw'.2], by linarith [hw'.1]⟩
    have hsub : closure (Complex.HadamardThreeLines.verticalStrip 0 1)
        ⊆ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
      have h := Complex.continuous_re.closure_preimage_subset (Set.Ioo (0 : ℝ) 1)
      rwa [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at h
    have hd : DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      ⟨hdiff.comp hφent.differentiableOn hmaps_open,
        (hcont.comp hφent.continuous.continuousOn hmaps_closed).mono hsub⟩
    have hbddG : BddAbove ((norm ∘ G) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
      refine ⟨B, ?_⟩
      rintro y ⟨w', hw', rfl⟩
      have hmem' := hmaps_closed hw'
      rw [Set.mem_preimage, Set.mem_Icc] at hmem'
      exact hBmem (φ w') hmem'.1 hmem'.2
    have ha : ∀ w' ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖G w'‖ ≤ 0 := by
      intro w' hw'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw'
      have hφeq : φ w' = (w'.im : ℂ) := Complex.ext (by rw [hφre]; simp) (by rw [hφim, hw']; simp)
      show ‖Φ (φ w')‖ ≤ 0
      rw [hφeq, htop w'.im, norm_zero]
    have hb : ∀ w' ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖G w'‖ ≤ B := by
      intro w' hw'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw'
      have hφeq : φ w' = (w'.im : ℂ) - Complex.I :=
        Complex.ext (by rw [hφre]; simp) (by rw [hφim, hw']; simp)
      show ‖Φ (φ w')‖ ≤ B
      rw [hφeq]
      have himeq : ((w'.im : ℂ) - Complex.I).im = -1 := by simp
      exact hBmem _ (le_of_eq himeq.symm) (by rw [himeq]; norm_num)
    have hmem : w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
      simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc, hwre]
      exact ⟨by linarith, by linarith⟩
    have hhad := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (l := 0) (u := 1) (a := 0) (b := B) (by norm_num) hmem hd hbddG ha hb
    have hGw : G w = Φ z := by simp only [hGdef]; rw [hφw]
    rw [hGw] at hhad
    simp only [sub_zero, div_one] at hhad
    rwa [Real.zero_rpow (by rw [hwre]; linarith : (1 : ℝ) - w.re ≠ 0), zero_mul] at hhad
  -- bottom edge by continuity (approach `t − i` from inside the strip)
  intro t
  set z₀ : ℂ := (t : ℂ) - Complex.I with hz₀
  have hz₀im : z₀.im = -1 := by rw [hz₀]; simp
  have hz₀mem : z₀ ∈ Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0 := by
    rw [Set.mem_preimage, Set.mem_Icc, hz₀im]; exact ⟨le_refl _, by norm_num⟩
  set u : ℕ → ℂ := fun n => (t : ℂ) + ((-1 + 1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I with hudef
  have huim : ∀ n, (u n).im = -1 + 1 / (n + 1 : ℝ) := by
    intro n; rw [hudef]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re]
    ring
  have hupos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1 : ℝ) := fun n => by positivity
  have hule : ∀ n : ℕ, 1 / (n + 1 : ℝ) ≤ 1 := by
    intro n; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hu0 : ∀ n, Φ (u n) = 0 := by
    intro n; refine hint _ ?_ ?_ <;> rw [huim]
    · linarith [hupos n]
    · linarith [hule n]
  have hulim : Filter.Tendsto u Filter.atTop (nhds z₀) := by
    have key : Filter.Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I) Filter.atTop
        (nhds 0) := by
      have h0 : Filter.Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
        have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
          tendsto_one_div_add_atTop_nhds_zero_nat
        rwa [Complex.ofReal_zero] at h
      simpa using h0.mul_const Complex.I
    have heq : ∀ n : ℕ, u n = z₀ + ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I := by
      intro n; rw [hudef, hz₀]; push_cast; ring
    have hsum : Filter.Tendsto (fun n : ℕ => z₀ + ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I) Filter.atTop
        (nhds (z₀ + 0)) := tendsto_const_nhds.add key
    rw [add_zero] at hsum
    exact hsum.congr (fun n => (heq n).symm)
  have hwithin : Filter.Tendsto u Filter.atTop
      (nhdsWithin z₀ (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hulim
      (Filter.Eventually.of_forall fun n => by
        rw [Set.mem_preimage, Set.mem_Icc, huim]
        exact ⟨by linarith [hupos n], by linarith [hule n]⟩)
  have hΦlim : Filter.Tendsto (fun n => Φ (u n)) Filter.atTop (nhds (Φ z₀)) :=
    Filter.Tendsto.comp (hcont z₀ hz₀mem) hwithin
  have hΦ0 : Filter.Tendsto (fun n => Φ (u n)) Filter.atTop (nhds 0) := by
    simp only [hu0]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hΦlim hΦ0

open QIQTH.StandardSubspaceModular in
/-- **★★★★★★★★ THE free-field one-particle Bisognano–Wichmann, reduced to its SINGLE remaining analytic input.**
    `modUnitary S t = boostUnitary(2πt)` for the nice-core wedge standard subspace, given ONLY the Reeh–Schlieder
    SEPARATING condition `NiceWedgeSeparating m` (no complex line / Pauli–Jordan symplectic non-degeneracy).  The
    cyclic Reeh–Schlieder input is now discharged *internally* and unconditionally for every `m > 0`
    (`niceWedgeCyclic_pos_mass`), so it is no longer a hypothesis.  Every other step — the KMS condition, the
    `𝒦`-invariance, the boost group, the standard-subspace construction, BOTH Reeh–Schlieder lattice reductions,
    AND the entire cyclic/wedge-totality input (the complete Wiener–Tauberian theorem + brick 8) — is machine-checked
    and axiom-free.  The free-field one-particle BW now rests on EXACTLY ONE concrete analytic statement: the
    symplectic non-degeneracy of the localized rapidity amplitudes.  This is the honest, irreducible frontier. -/
theorem oneParticleBW_niceWedge_of_separating {m : ℝ} (hm : 0 < m)
    (V : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)))
    (hVboost : ∀ t x, V t x = QIQTH.Fock.OneParticle.boostUnitary (2 * Real.pi * t) x)
    (hsep : NiceWedgeSeparating m) :
    ∀ t, modUnitary (niceWedgeStandardSubspace m
      (niceWedge_isSeparating_of_no_complex_line m hsep)
      (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))) t = V t :=
  oneParticleBW_niceWedge_reehSchlieder hm V hVboost hsep (niceWedgeCyclic_pos_mass hm)

end QIQTH.Fock.CyclicWitness
