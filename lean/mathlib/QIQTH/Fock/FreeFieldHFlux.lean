/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Free-field `hFlux` in the satisfiable `+2π` convention

`QIQT_GR_FREEFIELD_COMPLETION_PLAN.md`, Phase 1–2.  The `hFlux` machinery in `OneParticleBW.lean`
(`hasDerivAt_modularEnergy_of_boost`, `oneParticle_hFlux`) is written in the `boostUnitary(−2πt)` convention and
takes the BW identification `modUnitary S = boostUnitary(−2π·)` as a labelled input.  But the REAL modular flow of
the free-field nice-wedge standard subspace satisfies the `+2π` convention (`oneParticleBW_niceWedge_unconditional`,
axiom-free).  This file rebuilds the modular-energy = stress-flux step in the satisfiable `+2π` convention and
supplies the BW identification INTERNALLY from `oneParticleBW_niceWedge_unconditional` — so the only remaining input
is the boost-charge derivative (discharged separately from `boostEnergy_eq_neg_stressFlux`).

Axiom-free.
-/
import QIQTH.Fock.CyclicWitness

namespace QIQTH.Fock

open QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW QIQTH.Fock.BoostKMS QIQTH.Fock.CyclicWitness
  QIQTH.StandardSubspaceModular
open MeasureTheory

/-- **Modular energy = boost energy, in the `+2π` convention** (sign-flipped copy of
    `hasDerivAt_modularEnergy_of_boost`).  Given the BW identification `modUnitary S = boostUnitary(+2π·)`, the
    modular-energy derivative of `ξ` equals its boost-energy derivative. -/
theorem hasDerivAt_modularEnergy_of_boost_pos
    (S : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)))
    (hbw : ∀ (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)),
        modUnitary S t u = boostUnitary (2 * Real.pi * t) u)
    (ξ : Lp ℂ 2 (volume : Measure ℝ)) (c : ℂ)
    (h : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (2 * Real.pi * t) ξ)) c 0) :
    HasDerivAt (fun t : ℝ => inner ℂ ξ (modUnitary S t ξ)) c 0 := by
  have heq : (fun t : ℝ => inner ℂ ξ (modUnitary S t ξ))
      = (fun t : ℝ => inner ℂ ξ (boostUnitary (2 * Real.pi * t) ξ)) := by
    funext t; rw [hbw t ξ]
  rw [heq]; exact h

/-- **★ The free-field modular-energy = stress-flux derivative, BW supplied internally (Phase 2).**  For the
    nice-wedge standard subspace `S` and ANY mode `ξ`, given the boost-charge derivative `HasDerivAt (t ↦
    ⟨ξ, boostUnitary(2πt) ξ⟩) c 0`, the modular-energy derivative `HasDerivAt (t ↦ ⟨ξ, modUnitary S t ξ⟩) c 0`
    holds — with the Bisognano–Wichmann identification `modUnitary S = boostUnitary(+2π·)` supplied internally and
    axiom-free by `oneParticleBW_niceWedge_unconditional` (no labelled `hUniq`/`hStrip`, no sign mismatch). -/
theorem freeField_modularEnergy_eq_boostCharge {m : ℝ} (hm : 0 < m)
    (ξ : Lp ℂ 2 (volume : Measure ℝ)) (c : ℂ)
    (hBoostCharge : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (2 * Real.pi * t) ξ)) c 0) :
    HasDerivAt (fun t : ℝ => inner ℂ ξ
        (modUnitary (niceWedgeStandardSubspace m
          (niceWedge_isSeparating_of_no_complex_line m (niceWedgeSeparating_pos_mass hm))
          (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))) t ξ)) c 0 := by
  have hbw : ∀ (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)),
      modUnitary (niceWedgeStandardSubspace m
        (niceWedge_isSeparating_of_no_complex_line m (niceWedgeSeparating_pos_mass hm))
        (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))) t u
        = boostUnitary (2 * Real.pi * t) u := by
    intro t u
    have hBW := QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional hm
      (fun t => (boostUnitary (2 * Real.pi * t) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] _))
      (fun _ _ => rfl) t
    rw [hBW]; rfl
  exact hasDerivAt_modularEnergy_of_boost_pos _ hbw ξ c hBoostCharge

/-- **The `+2π` boost-charge derivative (purely imaginary), by the `t → −t` reflection** of the `−2π`
    `hasDerivAt_inner_boostUnitary_imaginary`.  Because `⟪ξ, boostUnitary(2πt) ξ⟫ = ⟪ξ, boostUnitary(−2π(−t)) ξ⟫`,
    the `+2π` correlation is the `−2π` one precomposed with negation, so its derivative is the negative:
    `d/dt ⟪ξ, boostUnitary(2π t) ξ⟫|₀ = i·((−(2π·∫ conj(f)·f')).im)`.  Reuses the hard dominated-convergence
    proof of the `−2π` lemma — no re-derivation.  Axiom-free. -/
theorem hasDerivAt_inner_boostUnitary_imaginary_pos
    (f f' : ℝ → ℂ) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hf_int : Integrable f (volume : Measure ℝ))
    (hF0_int : Integrable (fun θ => (starRingEnd ℂ) (f θ) * f θ) (volume : Measure ℝ))
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hf'_meas : AEStronglyMeasurable f' (volume : Measure ℝ))
    (B : ℝ) (hB : ∀ x, ‖f' x‖ ≤ B) :
    HasDerivAt
      (fun t : ℝ => inner ℂ (hf2.toLp f) (boostUnitary (2 * Real.pi * t) (hf2.toLp f)))
      (Complex.I *
        (((-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ))).im : ℝ) : ℂ)) 0 := by
  -- `hf_meas` discharged from `hfd`: differentiable everywhere ⟹ continuous ⟹ measurable (was a labelled input).
  have hf_meas : AEStronglyMeasurable f (volume : Measure ℝ) := by
    have hdiff : Differentiable ℝ f := fun x => (hfd x).differentiableAt
    exact hdiff.continuous.aestronglyMeasurable
  have him := hasDerivAt_inner_boostUnitary_imaginary f f' hf2 hf_int hF0_int hf_meas hfd hf'_meas B hB
  -- Reflection `t → −t`: `⟪ξ, boostUnitary(2πt) ξ⟫ = ⟪ξ, boostUnitary(−2π(0−t)) ξ⟫`, so the +2π correlation is
  -- the −2π one precomposed with `0 − ·`; `comp_const_sub` flips the derivative sign with no HO unification.
  have hcomp : HasDerivAt
      (fun t : ℝ => inner ℂ (hf2.toLp f) (boostUnitary (-(2 * Real.pi * (0 - t))) (hf2.toLp f)))
      (-(Complex.I *
        (((2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ)).im : ℝ) : ℂ))) 0 :=
    HasDerivAt.comp_const_sub (0 : ℝ) (0 : ℝ)
      (f := fun s => inner ℂ (hf2.toLp f) (boostUnitary (-(2 * Real.pi * s)) (hf2.toLp f)))
      (by simpa using him)
  convert hcomp using 1
  · funext t; congr 2; ring
  · simp only [Complex.neg_im, Complex.ofReal_neg]; ring

/-- **★★★ The free-field one-particle `hFlux`, FULLY ASSEMBLED in the satisfiable `+2π` convention.**  For any
    smooth wedge state `ξ = f.toLp` and the nice-wedge standard subspace `S`, the modular-energy derivative is
    `i·(2π/ℏ)·T_kk`:
    `HasDerivAt (t ↦ ⟪ξ, modUnitary S t ξ⟫) (i·(2π/ℏ·T_kk)) 0`,
    with EVERYTHING operator/analytic discharged axiom-free — the Bisognano–Wichmann identification
    (`oneParticleBW_niceWedge_unconditional`) and the boost-charge derivative
    (`hasDerivAt_inner_boostUnitary_imaginary_pos`) are both supplied internally.  The ONLY labelled input is the
    single scalar physics identification `hTkk : (2π/ℏ)·T_kk = (−(2π·∫ conj(f)·f')).im` (the conserved boost
    Killing charge = stress-tensor flux, in the `+2π` orientation).  This is the free-field `oneParticle_hFlux`
    with NO sign mismatch and NO labelled modular hypotheses.  Axiom-free. -/
theorem freeField_oneParticle_hFlux {m : ℝ} (hm : 0 < m)
    (f f' : ℝ → ℂ) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hf_int : Integrable f (volume : Measure ℝ))
    (hF0_int : Integrable (fun θ => (starRingEnd ℂ) (f θ) * f θ) (volume : Measure ℝ))
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hf'_meas : AEStronglyMeasurable f' (volume : Measure ℝ))
    (B : ℝ) (hB : ∀ x, ‖f' x‖ ≤ B) (hbar Tkk : ℝ)
    (hTkk : (2 * Real.pi / hbar * Tkk : ℝ)
        = (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ))).im) :
    HasDerivAt
      (fun t : ℝ => inner ℂ (hf2.toLp f)
        (modUnitary (niceWedgeStandardSubspace m
          (niceWedge_isSeparating_of_no_complex_line m (niceWedgeSeparating_pos_mass hm))
          (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))) t (hf2.toLp f)))
      (Complex.I * ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ)) 0 := by
  have hbc := hasDerivAt_inner_boostUnitary_imaginary_pos f f' hf2 hf_int hF0_int hfd hf'_meas B hB
  rw [show ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ)
        = (((-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ))).im : ℝ) : ℂ) by
      rw [hTkk]]
  exact freeField_modularEnergy_eq_boostCharge hm (hf2.toLp f) _ hbc

/-- **★★★ The free-field per-generator flux equation `kd = (2π/ℏ)·T_kk` (the `+2π`/nice-wedge analog of
    `component_hFlux_of_wedgeKMS_complete`).**  For the nice-wedge standard subspace `S` and smooth wedge state
    `ξ = f.toLp`, given (i) `hbridge` — that the abstract per-generator modular-energy coefficient `kd` IS the
    derivative of `t ↦ ⟪ξ, modUnitary S t ξ⟫` — and (ii) `hTkk` — the localization identification of the horizon
    stress component `T_kk` with the mode's rapidity stress flux — derivative uniqueness pins
    `kd = (2π/ℏ)·T_kk`.  This is exactly the conclusion `qiqt_bekenstein_gives_gr` consumes (it takes the kd-equation
    directly, not the `WedgeKMSFlux_complete` bundle), so it routes the free-field `+2π` `hFlux` straight into the
    GR derivation — bypassing the `−2π`/`wedgeGenSet` bundle entirely.  Everything modular/BW/boost is discharged
    axiom-free; the ONLY remaining per-generator inputs are `hbridge` (kd = modular energy of the localized mode)
    and `hTkk` (the localization map, Gap 2).  Axiom-free. -/
theorem freeField_component_hFlux {m : ℝ} (hm : 0 < m)
    (f f' : ℝ → ℂ) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hf_int : Integrable f (volume : Measure ℝ))
    (hF0_int : Integrable (fun θ => (starRingEnd ℂ) (f θ) * f θ) (volume : Measure ℝ))
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hf'_meas : AEStronglyMeasurable f' (volume : Measure ℝ))
    (B : ℝ) (hB : ∀ x, ‖f' x‖ ≤ B) (hbar kd Tkk : ℝ)
    (hTkk : (2 * Real.pi / hbar * Tkk : ℝ)
        = (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ))).im)
    (hbridge : HasDerivAt
      (fun t : ℝ => inner ℂ (hf2.toLp f)
        (modUnitary (niceWedgeStandardSubspace m
          (niceWedge_isSeparating_of_no_complex_line m (niceWedgeSeparating_pos_mass hm))
          (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))) t (hf2.toLp f)))
      (Complex.I * ((kd : ℝ) : ℂ)) 0) :
    kd = 2 * Real.pi / hbar * Tkk := by
  have hHil := freeField_oneParticle_hFlux hm f f' hf2 hf_int hF0_int hfd hf'_meas B hB
    hbar Tkk hTkk
  have huniq : Complex.I * ((kd : ℝ) : ℂ) = Complex.I * ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ) :=
    hbridge.unique hHil
  exact_mod_cast mul_left_cancel₀ Complex.I_ne_zero huniq

/-- **Non-vacuity of the localization datum's SOFT shell.**  The analytic hypotheses of `freeField_component_hFlux`
    (`MemLp`/`Integrable`/`AEStronglyMeasurable`/`HasDerivAt`/globally-bounded `‖f'‖`) are simultaneously
    satisfiable — witnessed by the Gaussian mode `θ ↦ exp(−θ²)` with derivative bound `B = 1`
    (`2|x| ≤ x²+1 ≤ exp(x²)`).  So the only genuinely-labelled part of Gap 2 is the modeling core `(hbridge, hTkk)`;
    the analytic shell is inhabited and machine-checked.  Axiom-free. -/
theorem freeField_softData_nonvacuous :
    ∃ (f f' : ℝ → ℂ) (B : ℝ),
      MemLp f 2 (volume : Measure ℝ) ∧
      Integrable f (volume : Measure ℝ) ∧
      Integrable (fun θ => (starRingEnd ℂ) (f θ) * f θ) (volume : Measure ℝ) ∧
      AEStronglyMeasurable f (volume : Measure ℝ) ∧
      (∀ x, HasDerivAt f (f' x) x) ∧
      AEStronglyMeasurable f' (volume : Measure ℝ) ∧
      (∀ x, ‖f' x‖ ≤ B) := by
  refine ⟨fun θ => (Real.exp (-θ ^ 2) : ℂ),
    fun θ => ((Real.exp (-θ ^ 2) * (-(2 * θ)) : ℝ) : ℂ), 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- MemLp f 2 : ‖f‖² = exp(−2θ²) is integrable
    have hmeas : AEStronglyMeasurable (fun θ => (Real.exp (-θ ^ 2) : ℂ)) (volume : Measure ℝ) :=
      (Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    have hge : (fun θ : ℝ => ‖(Real.exp (-θ ^ 2) : ℂ)‖ ^ 2) = fun θ : ℝ => Real.exp (-2 * θ ^ 2) := by
      funext θ
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_two,
        ← Real.exp_add, show (-θ ^ 2 + -θ ^ 2 : ℝ) = -2 * θ ^ 2 by ring]
    rw [hge]; exact integrable_exp_neg_mul_sq (by norm_num)
  · -- Integrable f
    have : Integrable (fun θ : ℝ => Real.exp (-θ ^ 2)) (volume : Measure ℝ) := by
      simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
    exact this.ofReal
  · -- Integrable (conj f · f) = exp(−2θ²)
    have hI : Integrable (fun θ : ℝ => Real.exp (-2 * θ ^ 2)) (volume : Measure ℝ) :=
      integrable_exp_neg_mul_sq (by norm_num)
    have heq : (fun θ : ℝ => (starRingEnd ℂ) (Real.exp (-θ ^ 2) : ℂ) * (Real.exp (-θ ^ 2) : ℂ))
        = fun θ : ℝ => ((Real.exp (-2 * θ ^ 2) : ℝ) : ℂ) := by
      funext θ
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add,
        show (-θ ^ 2 + -θ ^ 2 : ℝ) = -2 * θ ^ 2 by ring]
    rw [heq]; exact hI.ofReal
  · -- AEStronglyMeasurable f
    exact (Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable
  · -- HasDerivAt f (f' x) x
    intro x
    have hsq : HasDerivAt (fun θ : ℝ => -θ ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).neg
    exact hsq.exp.ofReal_comp
  · -- AEStronglyMeasurable f'
    exact (Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable
  · -- ‖f' x‖ ≤ 1
    intro x
    have hbnd : 2 * |x| ≤ Real.exp (x ^ 2) := by
      have h2 : 2 * |x| ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
      have h3 : x ^ 2 + 1 ≤ Real.exp (x ^ 2) := by have := Real.add_one_le_exp (x ^ 2); linarith
      linarith
    have hnorm : ‖((Real.exp (-x ^ 2) * (-(2 * x)) : ℝ) : ℂ)‖ = Real.exp (-x ^ 2) * (2 * |x|) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_neg,
        abs_mul, abs_two]
    rw [hnorm]
    calc Real.exp (-x ^ 2) * (2 * |x|)
        ≤ Real.exp (-x ^ 2) * Real.exp (x ^ 2) :=
          mul_le_mul_of_nonneg_left hbnd (le_of_lt (Real.exp_pos _))
      _ = 1 := by rw [← Real.exp_add]; simp

end QIQTH.Fock
