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

open MeasureTheory
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

end QIQTH.Fock.CyclicWitness
