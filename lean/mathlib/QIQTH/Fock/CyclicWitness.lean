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

end QIQTH.Fock.CyclicWitness
