/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Sakharov Stage C — the per-mode Gaussian entanglement entropy (Srednicki building block)

The entanglement entropy of a free scalar (a lattice of coupled harmonic oscillators) in its Gaussian ground
state is, by Williamson normal form, a SUM over symplectic modes of a single-mode entropy function of the
symplectic eigenvalue `ν ≥ 1/2` (see `SAKHAROV_KG_PLAN.md`, Stage C):
```
   S(ν) = (ν + 1/2)·log(ν + 1/2) − (ν − 1/2)·log(ν − 1/2).
```
This file formalizes that per-mode function and its key properties — the entropy carried by ONE mode of the
record/oscillator network, the building block summed by the area law.  The full lattice area-law SCALING
(`Σ over modes ∝ boundary size`) is the cited formalization frontier; this is its irreducible kernel.

`S(1/2) = 0` (a minimum-uncertainty mode is pure — no entanglement), and `S` is increasing and nonnegative
(more squeezing ⟹ more entanglement).  Axiom-free.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.MeanValue

namespace QIQTH.GaussianStateEntropy

open Real

/-- The entanglement entropy carried by one symplectic mode of a Gaussian state, as a function of its symplectic
    eigenvalue `ν ≥ 1/2`. -/
noncomputable def gaussModeEntropy (ν : ℝ) : ℝ :=
  (ν + 1 / 2) * Real.log (ν + 1 / 2) - (ν - 1 / 2) * Real.log (ν - 1 / 2)

/-- A minimum-uncertainty mode (`ν = 1/2`) is pure: zero entanglement entropy. -/
theorem gaussModeEntropy_half : gaussModeEntropy (1 / 2) = 0 := by
  unfold gaussModeEntropy
  norm_num [Real.log_one]

/-- **The per-mode entropy is increasing in the symplectic eigenvalue:** `dS/dν = log((ν+1/2)/(ν−1/2)) > 0`.
    (The `+1` from each `x log x` derivative cancels.) -/
theorem gaussModeEntropy_hasDerivAt {ν : ℝ} (hν : 1 / 2 < ν) :
    HasDerivAt gaussModeEntropy (Real.log (ν + 1 / 2) - Real.log (ν - 1 / 2)) ν := by
  have hp : (0 : ℝ) < ν + 1 / 2 := by linarith
  have hm : (0 : ℝ) < ν - 1 / 2 := by linarith
  have h1 : HasDerivAt (fun x => (x + 1 / 2) * Real.log (x + 1 / 2))
      (Real.log (ν + 1 / 2) + 1) ν := by
    have hd : HasDerivAt (fun x : ℝ => x + 1 / 2) 1 ν := (hasDerivAt_id ν).add_const _
    have hl : HasDerivAt (fun x => Real.log (x + 1 / 2)) ((1 : ℝ) / (ν + 1 / 2)) ν := hd.log hp.ne'
    have hmul := hd.mul hl
    rwa [one_mul, mul_one_div, div_self hp.ne'] at hmul
  have h2 : HasDerivAt (fun x => (x - 1 / 2) * Real.log (x - 1 / 2))
      (Real.log (ν - 1 / 2) + 1) ν := by
    have hd : HasDerivAt (fun x : ℝ => x - 1 / 2) 1 ν := (hasDerivAt_id ν).sub_const _
    have hl : HasDerivAt (fun x => Real.log (x - 1 / 2)) ((1 : ℝ) / (ν - 1 / 2)) ν := hd.log hm.ne'
    have hmul := hd.mul hl
    rwa [one_mul, mul_one_div, div_self hm.ne'] at hmul
  have key := h1.sub h2
  rw [show Real.log (ν + 1 / 2) - Real.log (ν - 1 / 2)
        = (Real.log (ν + 1 / 2) + 1) - (Real.log (ν - 1 / 2) + 1) from by ring]
  exact key

/-- The per-mode derivative is strictly positive for `ν > 1/2` (`(ν+1/2)/(ν−1/2) > 1`). -/
theorem gaussModeEntropy_deriv_pos {ν : ℝ} (hν : 1 / 2 < ν) :
    0 < Real.log (ν + 1 / 2) - Real.log (ν - 1 / 2) := by
  have hm : (0 : ℝ) < ν - 1 / 2 := by linarith
  rw [sub_pos]
  exact Real.log_lt_log hm (by linarith)

/-- **The per-mode entanglement entropy is nonnegative** for `ν ≥ 1/2` (increasing from its value `0` at
    `ν = 1/2`).  Entanglement is never negative — the finite-mode building block of the entropy area law. -/
theorem gaussModeEntropy_nonneg {ν : ℝ} (hν : 1 / 2 ≤ ν) : 0 ≤ gaussModeEntropy ν := by
  rcases eq_or_lt_of_le hν with h | h
  · exact ge_of_eq (by rw [← h, gaussModeEntropy_half])
  · rw [← gaussModeEntropy_half]
    -- continuity via `negMulLog` (= −x log x), which is continuous at 0 unlike `log`
    have hrw : gaussModeEntropy = fun x => Real.negMulLog (x - 1 / 2) - Real.negMulLog (x + 1 / 2) := by
      funext x; unfold gaussModeEntropy Real.negMulLog; ring
    have hcont : ContinuousOn gaussModeEntropy (Set.Icc (1 / 2) ν) := by
      rw [hrw]
      exact ((Real.continuous_negMulLog.comp (continuous_id.sub continuous_const)).sub
        (Real.continuous_negMulLog.comp (continuous_id.add continuous_const))).continuousOn
    have hdiff : DifferentiableOn ℝ gaussModeEntropy (interior (Set.Icc (1 / 2) ν)) := by
      intro x hx
      rw [interior_Icc] at hx
      exact (gaussModeEntropy_hasDerivAt hx.1).differentiableAt.differentiableWithinAt
    have hmono : MonotoneOn gaussModeEntropy (Set.Icc (1 / 2) ν) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont hdiff
      intro x hx
      rw [interior_Icc] at hx
      rw [(gaussModeEntropy_hasDerivAt hx.1).deriv]
      exact (gaussModeEntropy_deriv_pos hx.1).le
    exact hmono (Set.left_mem_Icc.mpr hν) (Set.right_mem_Icc.mpr hν) hν

end QIQTH.GaussianStateEntropy
