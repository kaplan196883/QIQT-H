/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Trace-Raychaudhuri under a scalar determinant rescaling

The trace-Raychaudhuri expansion `θ := tr(Y' Y⁻¹) = d/dτ log det Y` transforms *additively* under a
scalar rescaling of the determinant potential. If two invertible matrix fields `M`, `N` have
determinant potentials related (near `τ`) by
```
  log det N = log det M + f,
```
for a scalar function `f`, then their expansion scalars satisfy
```
  θ_N = θ_M + f'.
```

This is a general determinant-rescaling identity, proved by derivative uniqueness: both `θ_N` and
`θ_M + f'` are the derivative at `τ` of the *same* function `s ↦ log det (N s)` (the latter after
transporting along the eventual equality), so they coincide.

## Role in the van-Vleck endgame

This is the connection tool between the coordinate exp-differential trace and the frame trace: with
`f = −½ log det(g ∘ γ)` (the frame determinant satisfies `det E = 1/√det g`) it relates the
coordinate exp-differential trace `θ_B` to the orthonormal-frame trace `θ_Y`.

## Honest scope

This lemma is purely the determinant-rescaling identity `θ_N = θ_M + f'`. It does **not** itself
prove the Jacobi ODE `B'' = −R̃ B`, the `−Ric` van-Vleck ODE, or the heat-kernel coefficient
`a₁ = R/6`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import QIQTH.RaychaudhuriLogDet

namespace QIQTH.ExpMap

open Matrix

variable {n : ℕ}

set_option maxHeartbeats 400000

/-- **Trace-Raychaudhuri under a scalar determinant rescaling.**

If the determinant potentials of two invertible matrix fields `M`, `N` are related near `τ` by
`log det N = log det M + f` (as an eventual equality `hrel`), then the trace-Raychaudhuri expansions
transform additively:
```
  θ_N = tr(N' N⁻¹) = tr(M' M⁻¹) + f' = θ_M + f'.
```
Proof by derivative uniqueness: `raychaudhuri_logdet_firstderiv` gives `θ_N` as `d/dτ log det N` and
`θ_M` as `d/dτ log det M`; adding `hf` gives `θ_M + f'` as `d/dτ (log det M + f)`; transporting
along `hrel` makes this a second `HasDerivAt` for `s ↦ log det (N s)`, and `HasDerivAt.unique`
identifies the two derivatives. -/
theorem trace_raychaudhuri_det_factor
    (M N M' N' : ℝ → Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝ) {τ : ℝ} {f' : ℝ}
    (hM : HasDerivAt M (M' τ) τ) (huM : IsUnit (M τ))
    (hN : HasDerivAt N (N' τ) τ) (huN : IsUnit (N τ))
    (hf : HasDerivAt f f' τ)
    (hrel : (fun s => Real.log (N s).det) =ᶠ[nhds τ]
      (fun s => Real.log (M s).det + f s)) :
    (N' τ * (N τ)⁻¹).trace = (M' τ * (M τ)⁻¹).trace + f' := by
  have hlogN : HasDerivAt (fun s => Real.log (N s).det) ((N' τ * (N τ)⁻¹).trace) τ :=
    raychaudhuri_logdet_firstderiv N N' hN huN
  have hlogM : HasDerivAt (fun s => Real.log (M s).det) ((M' τ * (M τ)⁻¹).trace) τ :=
    raychaudhuri_logdet_firstderiv M M' hM huM
  have hRHS : HasDerivAt (fun s => Real.log (M s).det + f s)
      ((M' τ * (M τ)⁻¹).trace + f') τ := hlogM.add hf
  have hlogN' : HasDerivAt (fun s => Real.log (N s).det)
      ((M' τ * (M τ)⁻¹).trace + f') τ := hRHS.congr_of_eventuallyEq hrel
  exact hlogN.unique hlogN'

end QIQTH.ExpMap
