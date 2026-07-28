/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# JacobiRescale — DISCHARGING the carried `hresc` rescaling for `B s = s • D(exp_p)_{s•v}`

The Ricci-carrying radial identity `expJacobianDet_radialDeriv_eq_raychaudhuri_sub_n`
(`QIQTH/ExpJacobianRicci.lean`) carries, for an *arbitrary* matrix-valued Jacobi field
`B : ℝ → Matrix (Fin n) (Fin n) ℝ`, the labeled geometric input
```
  hresc :  log (expJacobianDet g gi hC p (s • v)) =ᶠ[𝓝 1]  log (det (B s)) − n · log s,
```
i.e. the standard Jacobi-field ↔ exp-differential **rescaling** `det B(s) = sⁿ · J(s • v)`.

This file **discharges** that hypothesis for the concrete, transparent choice
```
  B s := s • expJacobianMat g gi hC p (s • v),
```
reducing `hresc` to a pure **determinant-homogeneity** computation.  Indeed
```
  det (s • D(exp_p)_{s•v}) = s ^ (card (Fin n)) · det D(exp_p)_{s•v}   (Matrix.det_smul)
                          = sⁿ · J(s • v)                              (Fintype.card_fin),
```
so taking logs where `s > 0` and `J(s • v) > 0` (a NEIGHBOURHOOD of `s = 1`) gives
`log (det B s) = n · log s + log J(s • v)`, i.e. exactly `hresc`.

## What this does and does NOT do

* It replaces the opaque "carried standard Jacobi ↔ exp-differential identity" for THIS `B`
  with a transparent `Matrix.det_smul` computation, conditional **only** on the explicit,
  physically meaningful no-conjugate-point positivity `hpos : J(s • v) > 0` near `s = 1`.
* It does **NOT** prove the matrix Jacobi identity `B'' = −R̃ B` (that this particular
  `B = s • D(exp_p)_{s•v}` is the *clean* Jacobi field is a separate smooth-dependence fact).
* It does **NOT** prove `hpos` itself — the carried no-conjugate-point condition.
* It is unrelated to the heat-kernel coefficient `a₁ = R/6`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.JacobianDet

namespace QIQTH.JacobianRegularity

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic QIQTH.PullbackMetric
open Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **DISCHARGE of the carried `hresc` rescaling for `B s = s • D(exp_p)_{s•v}`.**

For the concrete matrix Jacobi field `B s := s • expJacobianMat g gi hC p (s • v)`, the carried
rescaling hypothesis of `expJacobianDet_radialDeriv_eq_raychaudhuri_sub_n` holds:
```
  log (expJacobianDet g gi hC p (s • v)) =ᶠ[𝓝 1]  log (det (B s)) − n · log s,
```
conditional ONLY on the explicit no-conjugate-point positivity
`hpos : ∀ᶠ s in 𝓝 1, 0 < expJacobianDet g gi hC p (s • v)`.

Proof: `det (s • M) = s ^ (card (Fin n)) • det M = sⁿ · det M` (`Matrix.det_smul`,
`Fintype.card_fin`); on the neighbourhood where `s > 0` (from `Set.Ioi 0 ∈ 𝓝 1`) and
`J(s • v) > 0` (from `hpos`), `log (sⁿ · J) = n · log s + log J` (`Real.log_mul`, `Real.log_pow`),
which rearranges to the claim.  A transparent determinant-homogeneity computation — no Jacobi
ODE, no `a₁ = R/6`. -/
theorem hresc_of_pos (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (v : Point n)
    (hpos : ∀ᶠ s in nhds (1:ℝ), 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)) :
    (fun s => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)))
      =ᶠ[nhds (1:ℝ)]
    (fun s => Real.log (((fun t => (t : ℝ) • QIQTH.JacobianDet.expJacobianMat g gi hC p (t • v)) s).det)
               - (n : ℝ) * Real.log s) := by
  -- `s > 0` in a neighbourhood of `1` (from `Set.Ioi 0 ∈ 𝓝 1`).
  have hs_pos : ∀ᶠ s in nhds (1:ℝ), (0:ℝ) < s :=
    (isOpen_Ioi).eventually_mem (by norm_num : (1:ℝ) ∈ Set.Ioi (0:ℝ))
  filter_upwards [hpos, hs_pos] with s hJpos hspos
  have hs0 : (0:ℝ) < s := hspos
  -- Unfold `expJacobianDet = det (expJacobianMat …)` so both sides share the matrix determinant.
  simp only [QIQTH.JacobianDet.expJacobianDet] at hJpos ⊢
  -- `det (s • M) = s ^ (card (Fin n)) • det M = sⁿ · det M`, then split the log.
  rw [Matrix.det_smul, Fintype.card_fin,
    Real.log_mul (pow_ne_zero n hs0.ne') hJpos.ne', Real.log_pow]
  ring

end QIQTH.JacobianRegularity
