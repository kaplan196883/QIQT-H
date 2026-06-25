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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

/-- `gaussModeEntropy` is continuous on all of `ℝ` (through `Real.negMulLog`, which — unlike `log` — is
    continuous at `0`, so the `x log x` factors are continuous even where the argument vanishes). -/
theorem gaussModeEntropy_continuous : Continuous gaussModeEntropy := by
  have hrw : gaussModeEntropy = fun x => Real.negMulLog (x - 1 / 2) - Real.negMulLog (x + 1 / 2) := by
    funext x; unfold gaussModeEntropy Real.negMulLog; ring
  rw [hrw]
  exact (Real.continuous_negMulLog.comp (continuous_id.sub continuous_const)).sub
    (Real.continuous_negMulLog.comp (continuous_id.add continuous_const))

/-- **A genuinely squeezed mode (`ν > 1/2`) carries strictly positive entanglement entropy.** -/
theorem gaussModeEntropy_pos {ν : ℝ} (hν : 1 / 2 < ν) : 0 < gaussModeEntropy ν := by
  rw [← gaussModeEntropy_half]
  have hmono : StrictMonoOn gaussModeEntropy (Set.Icc (1 / 2) ν) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) gaussModeEntropy_continuous.continuousOn
      (fun x hx => by
        rw [interior_Icc] at hx
        rw [(gaussModeEntropy_hasDerivAt hx.1).deriv]
        exact gaussModeEntropy_deriv_pos hx.1)
  exact hmono (Set.left_mem_Icc.mpr hν.le) (Set.right_mem_Icc.mpr hν.le) hν

/-- **The total entanglement entropy of an `n`-mode Gaussian state** — the sum, over its symplectic
    eigenvalues `νᵢ`, of the per-mode entropy.  By Williamson normal form this is the entropy the
    Srednicki/Bombelli–Koul–Lee–Sorkin area law evaluates; the area-law *scaling* of this sum with the
    boundary size (from the lattice covariance matrix's symplectic spectrum) is the cited frontier. -/
noncomputable def gaussStateEntropy {n : ℕ} (ν : Fin n → ℝ) : ℝ :=
  ∑ i, gaussModeEntropy (ν i)

/-- The total Gaussian entanglement entropy is nonnegative (a sum of nonnegative per-mode entropies). -/
theorem gaussStateEntropy_nonneg {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 / 2 ≤ ν i) :
    0 ≤ gaussStateEntropy ν :=
  Finset.sum_nonneg fun i _ => gaussModeEntropy_nonneg (hν i)

/-- A fully pure Gaussian state (every symplectic eigenvalue at the floor `1/2`) has zero entropy. -/
theorem gaussStateEntropy_pure {n : ℕ} {ν : Fin n → ℝ} (hν : ∀ i, ν i = 1 / 2) :
    gaussStateEntropy ν = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [hν i, gaussModeEntropy_half]

/-- **The total entropy vanishes iff every mode is pure** (given each `νᵢ ≥ 1/2`): the area-law summand is
    zero exactly on the unentangled state, and strictly positive as soon as any mode is squeezed. -/
theorem gaussStateEntropy_eq_zero_iff {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 / 2 ≤ ν i) :
    gaussStateEntropy ν = 0 ↔ ∀ i, ν i = 1 / 2 := by
  refine ⟨fun h i => ?_, fun h => gaussStateEntropy_pure h⟩
  have hz : gaussModeEntropy (ν i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => gaussModeEntropy_nonneg (hν j)).mp h i
      (Finset.mem_univ i)
  by_contra hne
  exact absurd hz (gaussModeEntropy_pos (lt_of_le_of_ne (hν i) (Ne.symm hne))).ne'

/-- **The entanglement entropy is supported only on the entangled (supra-floor) modes** — pure modes
    (`νᵢ = 1/2`) contribute nothing, so the total entropy is the sum over the strictly-squeezed modes
    alone.  This is the structural *seed of the area law*: the entropy **counts entangled modes**.  The
    sole remaining (cited) physics is that, for a lattice ground state, those entangled modes localize at
    the region's **boundary** (the Williamson symplectic spectrum of the covariance matrix) — which turns
    this count into `∝ boundary size`, the labelled formalization frontier. -/
theorem gaussStateEntropy_eq_sum_active {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 / 2 ≤ ν i) :
    gaussStateEntropy ν
      = ∑ i ∈ Finset.univ.filter (fun i => 1 / 2 < ν i), gaussModeEntropy (ν i) := by
  rw [gaussStateEntropy,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 1 / 2 < ν i)]
  have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬ 1 / 2 < ν i), gaussModeEntropy (ν i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [le_antisymm (not_lt.mp hi.2) (hν i), gaussModeEntropy_half]
  rw [hzero, add_zero]

/-! ### A concrete entangled instance: the two-mode squeezed vacuum

The simplest genuinely-entangled Gaussian state is the **two-mode squeezed vacuum** with squeezing `s`.
Tracing out one mode leaves a thermal state whose single symplectic eigenvalue is `ν(s) = cosh(2s)/2`
(`ν(0) = 1/2`, the pure floor; squeezing pushes it up).  Instantiating the entropy formula here gives a
concrete, non-vacuous area-law summand: entanglement (`s ≠ 0`) ⟹ strictly positive entropy; product
(`s = 0`) ⟹ zero.  This is the irreducible 2-mode model; the N-site lattice *scaling* needs the full
symplectic / Williamson spectrum (the cited frontier). -/

/-- The reduced single-mode symplectic eigenvalue of the two-mode squeezed vacuum at squeezing `s`. -/
noncomputable def twoModeSqueezedSympEig (s : ℝ) : ℝ := Real.cosh (2 * s) / 2

/-- The two-mode symplectic eigenvalue respects the pure-state floor `ν ≥ 1/2` (since `cosh ≥ 1`). -/
theorem twoModeSqueezedSympEig_ge_half (s : ℝ) : 1 / 2 ≤ twoModeSqueezedSympEig s := by
  have := Real.one_le_cosh (2 * s)
  unfold twoModeSqueezedSympEig; linarith

/-- It sits exactly at the floor iff the squeezing vanishes (no entanglement ⟺ product state). -/
theorem twoModeSqueezedSympEig_half_iff (s : ℝ) : twoModeSqueezedSympEig s = 1 / 2 ↔ s = 0 := by
  unfold twoModeSqueezedSympEig
  constructor
  · intro h
    by_contra hs
    have : 1 < Real.cosh (2 * s) := Real.one_lt_cosh.mpr (mul_ne_zero two_ne_zero hs)
    linarith
  · intro h; subst h; norm_num [Real.cosh_zero]

/-- **The two-mode squeezed vacuum carries strictly positive entanglement entropy for any nonzero
    squeezing** — the simplest concrete realization of the entropy formula on a genuinely entangled state. -/
theorem twoModeSqueezed_entropy_pos {s : ℝ} (hs : s ≠ 0) :
    0 < gaussModeEntropy (twoModeSqueezedSympEig s) := by
  have hne : twoModeSqueezedSympEig s ≠ 1 / 2 := fun h => hs ((twoModeSqueezedSympEig_half_iff s).mp h)
  exact gaussModeEntropy_pos (lt_of_le_of_ne (twoModeSqueezedSympEig_ge_half s) (Ne.symm hne))

/-- …and zero entropy exactly at zero squeezing (a product state — no entanglement). -/
theorem twoModeSqueezed_entropy_zero : gaussModeEntropy (twoModeSqueezedSympEig 0) = 0 := by
  rw [show twoModeSqueezedSympEig 0 = 1 / 2 from (twoModeSqueezedSympEig_half_iff 0).mpr rfl,
    gaussModeEntropy_half]

end QIQTH.GaussianStateEntropy
