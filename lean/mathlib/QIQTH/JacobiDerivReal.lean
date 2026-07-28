/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# JacobiDerivReal — van-Vleck radial FIRST-derivative on the REAL exp-differential `B(s)=s•D(exp_p)_{s•v}`

This file CONSOLIDATES the Ricci-carrying van-Vleck radial first-derivative identity
`expJacobianDet_radialDeriv_eq_raychaudhuri_sub_n` (`QIQTH/ExpJacobianRicci.lean`) onto the
CONCRETE, transparent exp-differential matrix Jacobi field
```
  B s := s • expJacobianMat g gi hC p (s • v)   ( = s • D(exp_p)_{s•v} ),
```
discharging every hypothesis of the abstract identity from standard no-conjugate-point data.

Concretely we assemble:

* **the matrix chain rule `hB`** — `s ↦ expJacobianMat g gi hC p (s • v)` has a derivative at
  `s = 1` (`hasDerivAt_pi` twice over the `Fin n × Fin n` entries; each entry is the `C²`
  entry map `expJacobianMat_entry_contDiffOn_two` composed with the ray `s ↦ s • v` via
  `hasDerivAt_ray`), then the scalar·matrix product rule (entrywise `HasDerivAt.fun_mul`, in the
  native `Matrix` smul) gives the derivative of `B s = s • (…)`;
* **the invertibility `hu`** — `IsUnit (B 1) = IsUnit (expJacobianMat g gi hC p v)` from
  `Matrix.isUnit_iff_isUnit_det` and the no-conjugate positivity `hJv : 0 < J(v)`;
* **the differentiability `hJdiff`** — `x ↦ log J(x)` is differentiable at `v` from the `C²`
  determinant (`expJacobianDet_contDiffOn_two`) and `log` at the nonzero value `J(v) > 0`;
* **the rescaling `hresc`** — supplied by `hresc_of_pos` (`QIQTH/JacobiRescale.lean`), a pure
  `Matrix.det_smul` homogeneity computation conditional only on `hpos : J(s • v) > 0` near `s = 1`.

The conclusion is the van-Vleck radial (Euler) first-derivative in Raychaudhuri `θ_B` form for the
actual exp differential:
```
  radialDeriv (fun x => log J(x)) v = tr(B'(1) · (D exp_p)_v⁻¹) − n.
```

## What this proves and what it does NOT

* It CLOSES the assembly of the first-derivative identity on the real object `s • D(exp_p)_{s•v}`,
  conditional ONLY on the explicit no-conjugate-point positivity data `hJv` (`J(v) > 0`) and
  `hpos` (`J(s•v) > 0` near `s = 1`).  Those two positivities are CARRIED, not proved — they are
  the standard "no conjugate point on the ray" hypotheses.
* It does **NOT** prove the deep matrix Jacobi identity `B'' = −R̃ B` (that this particular
  `B = s • D(exp_p)_{s•v}` is the *clean* Jacobi field), which would feed the geodesic Raychaudhuri
  equation `θ_B' = −Ric − tr(Θ²)`.
* It does **NOT** prove `hpos`/`hJv` themselves.
* It is UNRELATED to the heat-kernel coefficient `a₁ = R/6` (M6) and to the M5 continuum step.

This is the van-Vleck radial FIRST-derivative (`θ_B` form) for the real exp-differential,
conditional on no-conjugate data.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.ExpJacobianRicci
import QIQTH.JacobiRescale
import QIQTH.ExpJacobianRegularity

namespace QIQTH.JacobianRegularity

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.RadialDistance
open Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 1200000

/-- **The van-Vleck radial first-derivative identity on the real exp-differential.**

For the concrete exp-differential matrix Jacobi field `B s := s • expJacobianMat g gi hC p (s • v)`
( `= s • D(exp_p)_{s•v}` ), the radial (Euler) derivative of `log J` at `v` is the Raychaudhuri
expansion `θ_B := tr(B'(1) · (D exp_p)_v⁻¹)` minus `n`:
```
  radialDeriv (fun x => log J(x)) v = tr(B'(1) · (expJacobianMat g gi hC p v)⁻¹) − n,
```
where `B'(1)` is the (existentially provided) derivative of `B` at `s = 1`.

Every hypothesis of the abstract identity `expJacobianDet_radialDeriv_eq_raychaudhuri_sub_n` is
discharged here for this `B`, conditional ONLY on the standard no-conjugate-point positivity data
`hJv : 0 < J(v)` and `hpos : ∀ᶠ s in 𝓝 1, 0 < J(s • v)` (CARRIED, not proved).

This does NOT prove `B'' = −R̃ B`, does NOT prove `hpos`/`hJv`, and is unrelated to `a₁ = R/6`. -/
theorem expJacobianDet_radialDeriv_real (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (v : Point n)
    (hv : ‖v‖ < expRho g gi hC p)
    (hJv : 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p v)
    (hpos : ∀ᶠ s in nhds (1:ℝ), 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)) :
    ∃ Bd : Matrix (Fin n) (Fin n) ℝ,
      HasDerivAt (fun s : ℝ => s • QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v)) Bd 1 ∧
      radialDeriv (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v
        = (Bd * (QIQTH.JacobianDet.expJacobianMat g gi hC p v)⁻¹).trace - (n : ℝ) := by
  -- `v` lies in the (open) exp ball, hence the ball is a neighbourhood of `v`.
  have hmem : Metric.ball (0 : Point n) (expRho g gi hC p) ∈ nhds v :=
    Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hv)
  -- The exp-Jacobian determinant is `C²` on the ball, hence differentiable at `v`.
  have hdet_diff : DifferentiableAt ℝ (QIQTH.JacobianDet.expJacobianDet g gi hC p) v :=
    ((expJacobianDet_contDiffOn_two g gi hC p).differentiableOn (by norm_num)).differentiableAt hmem
  -- `x ↦ log J(x)` is differentiable at `v` (`J(v) > 0` so `log` is differentiable there).
  have hJdiff : DifferentiableAt ℝ
      (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v :=
    hdet_diff.log hJv.ne'
  -- Each Jacobian-matrix entry is `C²` on the ball, hence differentiable at `v`.
  have hentry_diff : ∀ a i, DifferentiableAt ℝ
      (fun x => QIQTH.JacobianDet.expJacobianMat g gi hC p x a i) v := fun a i =>
    ((expJacobianMat_entry_contDiffOn_two g gi hC p a i).differentiableOn
      (by norm_num)).differentiableAt hmem
  -- The entrywise derivative matrix `M'` of `s ↦ D(exp_p)_{s•v}` at `s = 1`.
  set M' : Matrix (Fin n) (Fin n) ℝ :=
    fun a i => fderiv ℝ (fun x => QIQTH.JacobianDet.expJacobianMat g gi hC p x a i) v v with hM'
  -- MATRIX CHAIN RULE: `s ↦ D(exp_p)_{s•v}` has derivative `M'` at `s = 1` (`hasDerivAt_pi` twice;
  -- each entry via `hasDerivAt_ray` on the `C²` entry map).
  have hM : HasDerivAt (fun s : ℝ => QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v)) M' 1 := by
    refine hasDerivAt_pi.mpr (fun a => hasDerivAt_pi.mpr (fun i => ?_))
    have hf1 : DifferentiableAt ℝ
        (fun x => QIQTH.JacobianDet.expJacobianMat g gi hC p x a i) ((1 : ℝ) • v) := by
      rw [one_smul]; exact hentry_diff a i
    have hd := hasDerivAt_ray (fun x => QIQTH.JacobianDet.expJacobianMat g gi hC p x a i) v hf1
    rw [one_smul] at hd
    exact hd
  -- SCALAR·MATRIX PRODUCT RULE (entrywise, in the native `Matrix` smul): `B s = s • (…)` has
  -- derivative `B'(1) = M' + D(exp_p)_v` at `s = 1`.  Each entry `s ↦ s • (D(exp_p)_{s•v})_{a i}`
  -- is `id · (entry)`, whose derivative at `1` is `M'_{a i} + (D(exp_p)_v)_{a i}` (`HasDerivAt.mul`).
  have hB : HasDerivAt (fun s : ℝ => s • QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v))
      (QIQTH.JacobianDet.expJacobianMat g gi hC p v + M') 1 := by
    refine hasDerivAt_pi.mpr (fun a => hasDerivAt_pi.mpr (fun i => ?_))
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    have hEntry : HasDerivAt
        (fun s : ℝ => QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v) a i) (M' a i) 1 :=
      (hasDerivAt_pi.mp ((hasDerivAt_pi.mp hM) a)) i
    simpa only [id_eq, one_mul, one_smul] using (hasDerivAt_id (1 : ℝ)).fun_mul hEntry
  -- INVERTIBILITY: `IsUnit (B 1) = IsUnit (D(exp_p)_v)` from `det = J(v) ≠ 0`.
  have hu : IsUnit ((fun s : ℝ => s • QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v)) 1) := by
    simp only [one_smul]
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hJv.ne'
  -- ASSEMBLE the abstract Ricci-carrying radial identity for this concrete `B`.
  refine ⟨_, hB, ?_⟩
  have key := QIQTH.ExpMap.expJacobianDet_radialDeriv_eq_raychaudhuri_sub_n g gi hC p v
    (fun s => s • QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v))
    (fun _ => QIQTH.JacobianDet.expJacobianMat g gi hC p v + M')
    hB hu hJdiff (hresc_of_pos g gi hC p v hpos)
  simpa only [one_smul] using key

end QIQTH.JacobianRegularity
