/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# GR scaffolding — entropy / relative-entropy derivative witnesses

The GR capstones (`QiqtGrThermo.lean`, `QiqtGrGaussian.lean`, …) consume two HasDerivAt facts on each null
generator — `hS` (the Shannon entropy `Sf t = Shannon (p t)` has a derivative at `t=0`) and `hK` (the heat
functional `Sf t + KL (p t ‖ p 0)` has a derivative at `t=0`).  These are tagged `SETUP` by the track tooling:
they are pure real-analysis facts, NOT the physics floor (`hcap`/`hbound`/`hsat` = P4, `hKG` = EOM).

This file derives them from smoothness of the finite record law `p : ℝ → ι → ℝ`:
- `shannon_hasDerivAt` (Stage A1): `d/dt Shannon(p t)|₀ = -∑ (log(p₀ r)+1)·p'(r)`.
- `KL_hasDerivAt_self` (Stage A2): at the equilibrium reference `q = p 0`, `d/dt KL(p t ‖ p 0)|₀ = 0`
  (the relative-entropy correction vanishes at equilibrium), hence `KE_hasDerivAt`: the heat derivative
  equals the Shannon derivative — making `hK` derivable from `hS`.

No physics is used; only the chain rule + `∑ p t r = 1` ⟹ `∑ p'(r) = 0`.  Axiom-free.
-/
import QIQTH.BranchLedger
import QIQTH.RelEntPositivity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace QIQTH.EntropyDeriv

open QIQTH.BranchLedger QIQTH.RelEntPositivity

/-- **Stage A1 — the Shannon entropy derivative.**  For a finite record law `p : ℝ → ι → ℝ` whose
    components are differentiable at `0` with strictly positive reference values, the Shannon entropy
    `t ↦ Shannon s (p t)` is differentiable at `0` with derivative `-∑ (log(p 0 r) + 1)·p'(r)`.
    Pure chain rule (`HasDerivAt.mul`, `HasDerivAt.log`); no physics input. -/
theorem shannon_hasDerivAt {ι : Type*} (s : Finset ι) (p : ℝ → ι → ℝ) (p' : ι → ℝ)
    (hp' : ∀ r ∈ s, HasDerivAt (fun t => p t r) (p' r) 0)
    (hp0 : ∀ r ∈ s, 0 < p 0 r) :
    HasDerivAt (fun t => Shannon s (p t)) (-∑ r ∈ s, (Real.log (p 0 r) + 1) * p' r) 0 := by
  unfold Shannon
  have hterm : ∀ r ∈ s, HasDerivAt (fun t => p t r * Real.log (p t r))
      ((Real.log (p 0 r) + 1) * p' r) 0 := by
    intro r hr
    have hne : p 0 r ≠ 0 := (hp0 r hr).ne'
    have hlog : HasDerivAt (fun t => Real.log (p t r)) (p' r / p 0 r) 0 :=
      (hp' r hr).log hne
    have hmul := (hp' r hr).mul hlog
    convert hmul using 1
    field_simp
  have hsumfn := HasDerivAt.sum hterm
  have heq : (∑ r ∈ s, fun t => p t r * Real.log (p t r))
           = fun t => ∑ r ∈ s, p t r * Real.log (p t r) := by
    funext t; simp only [Finset.sum_apply]
  rw [heq] at hsumfn
  exact hsumfn.neg

/-- **Constraint derivative.**  If `∑ r∈s, p t r = 1` for all `t` (a probability law for every `t`), then
    the component derivatives sum to zero: `∑ r∈s, p'(r) = 0`.  (Differentiate the constant `1`.) -/
theorem sum_deriv_zero {ι : Type*} (s : Finset ι) (p : ℝ → ι → ℝ) (p' : ι → ℝ)
    (hp' : ∀ r ∈ s, HasDerivAt (fun t => p t r) (p' r) 0)
    (hpsum : ∀ t, ∑ r ∈ s, p t r = 1) :
    ∑ r ∈ s, p' r = 0 := by
  have hconst : HasDerivAt (fun t => ∑ r ∈ s, p t r) 0 0 := by
    have hfun : (fun t => ∑ r ∈ s, p t r) = fun _ => (1 : ℝ) := by funext t; exact hpsum t
    rw [hfun]; exact hasDerivAt_const 0 1
  have hsumfn := HasDerivAt.sum hp'
  have heq : (∑ r ∈ s, fun t => p t r) = fun t => ∑ r ∈ s, p t r := by
    funext t; simp only [Finset.sum_apply]
  rw [heq] at hsumfn
  exact HasDerivAt.unique hsumfn hconst

/-- **Stage A2 — the relative-entropy derivative vanishes at the equilibrium reference.**  With the reference
    fixed at `q = p 0` and `p t` a probability law for every `t`, the KL functional `t ↦ KL s (p t) (p 0)`
    has derivative `0` at `t=0`.  (Each term contributes `p'(r)`; the sum is `∑ p'(r) = 0`.)  This is what
    makes the capstone's `hK` derivable from `hS`: the heat correction adds nothing at equilibrium. -/
theorem KL_hasDerivAt_self {ι : Type*} (s : Finset ι) (p : ℝ → ι → ℝ) (p' : ι → ℝ)
    (hp' : ∀ r ∈ s, HasDerivAt (fun t => p t r) (p' r) 0)
    (hp0 : ∀ r ∈ s, 0 < p 0 r)
    (hpsum : ∀ t, ∑ r ∈ s, p t r = 1) :
    HasDerivAt (fun t => KL s (p t) (p 0)) 0 0 := by
  unfold KL
  have hterm : ∀ r ∈ s, HasDerivAt (fun t => p t r * Real.log (p t r / p 0 r)) (p' r) 0 := by
    intro r hr
    have hne : p 0 r ≠ 0 := (hp0 r hr).ne'
    have hdiv : HasDerivAt (fun t => p t r / p 0 r) (p' r / p 0 r) 0 :=
      (hp' r hr).div_const (p 0 r)
    have hlog : HasDerivAt (fun t => Real.log (p t r / p 0 r))
        ((p' r / p 0 r) / (p 0 r / p 0 r)) 0 :=
      hdiv.log (by rw [div_self hne]; norm_num)
    have hmul := (hp' r hr).mul hlog
    convert hmul using 1
    rw [div_self hne, Real.log_one]
    field_simp
    ring
  have hsumfn := HasDerivAt.sum hterm
  have heq : (∑ r ∈ s, fun t => p t r * Real.log (p t r / p 0 r))
           = fun t => ∑ r ∈ s, p t r * Real.log (p t r / p 0 r) := by
    funext t; simp only [Finset.sum_apply]
  rw [heq] at hsumfn
  rwa [sum_deriv_zero s p p' hp' hpsum] at hsumfn

/-- **The heat-functional derivative equals the Shannon derivative.**  Combining A1 + A2: the QIQT heat
    functional `Sf + KL(·‖p₀)` has the SAME derivative at `t=0` as the Shannon entropy alone — the
    relative-entropy term is flat at equilibrium.  This derives the capstone's `hK` from `hS`. -/
theorem KE_hasDerivAt {ι : Type*} (s : Finset ι) (p : ℝ → ι → ℝ) (p' : ι → ℝ)
    (hp' : ∀ r ∈ s, HasDerivAt (fun t => p t r) (p' r) 0)
    (hp0 : ∀ r ∈ s, 0 < p 0 r)
    (hpsum : ∀ t, ∑ r ∈ s, p t r = 1) :
    HasDerivAt (fun t => Shannon s (p t) + KL s (p t) (p 0))
      (-∑ r ∈ s, (Real.log (p 0 r) + 1) * p' r) 0 := by
  have hS := shannon_hasDerivAt s p p' hp' hp0
  have hK := KL_hasDerivAt_self s p p' hp' hp0 hpsum
  simpa using hS.add hK

end QIQTH.EntropyDeriv
