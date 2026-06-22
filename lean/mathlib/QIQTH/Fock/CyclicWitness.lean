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

end QIQTH.Fock.CyclicWitness
