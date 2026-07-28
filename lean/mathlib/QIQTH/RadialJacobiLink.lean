import Mathlib
import QIQTH.ExpDiffVariation
import QIQTH.ExpJacobianFlow
import QIQTH.ExpJacobianRescale
import QIQTH.VanVleckRicciAssembled

/-!
# EXP-JET3-3b — the RADIAL JACOBI LINK `hBV`

This brick lands the **radial Jacobi link** `hBV`, the geometric germ feeding the
frame-decomposition `hrel` of `frameComponent_logdet_hrel` (and hence the assembled
`vanVleck_ricci_assembled`, `QIQTH/VanVleckRicciAssembled.lean`):

```
  hBV : ∀ᶠ s in nhds s₀, ∀ a j, (V j s).1 a = (s • expJacobianMat g gi hC p (s • v)) a j
```

where the exp-flow Jacobi columns are `V j s = Φ s (0, e_j)` for the direction-`v`
geodesic-variation flow `Φ` of `expDiff_flow_isGeodesicVariation` (this is exactly how `V`
is constructed inside `vanVleck_h4_assembled`, `QIQTH/VanVleckH4Assembled.lean`), and
`expJacobianMat g gi hC p x a i = (fderiv exp_p x)(e_i) a` (`QIQTH.JacobianDet.expJacobianMat`).

## The mathematics

`(V j s).1 = (Φ^v s)(0, e_j).1` is the position part, at geodesic parameter `s`, of the Jacobi
field along the direction-`v` geodesic `t ↦ exp_p(t·v)` with initial data `(J(0), J'(0)) = (0, e_j)`.
By the standard identification of Jacobi fields with variations of geodesics through the initial
velocity,

```
  (Φ^v s)(0, w).1  =  ∂_ε exp_p(s·(v + ε w)) |_{ε = 0}  =  (fderiv exp_p (s•v))(s • w),
```

the last step by the chain rule (`d/dε (s•v + ε·(s•w)) = s•w`).  Taking `w = e_j` and pulling the
scalar `s` out of the (continuous-linear) differential `fderiv exp_p (s•v)` gives

```
  (V j s).1 a  =  (fderiv exp_p (s•v))(s • e_j) a  =  s • (fderiv exp_p (s•v))(e_j) a
              =  s • expJacobianMat g gi hC p (s•v) a j  =  (s • expJacobianMat …) a j,
```

which is exactly `hBV`.  The `s•` factor is precisely the ray-vs-geodesic (Jacobi) rescaling
`J^v(s) = s · J^{s•v}(1)` that was CHECKPOINTED in `expMap_smul_eq_expTube`
(`QIQTH/ExpJacobianRescale.lean`).

## Scope (stated honestly — this is a REDUCTION, floor F1)

The genuinely deep, transverse content — that the position part of the direction-`v`
variation flow at parameter `s` equals the exp-differential at the *scaled* point `s•v` applied to
the *scaled* direction `s•w` — is the **Φ-flow rescaling** flagged as the remaining wall in the
`expMap_smul_eq_expTube` checkpoint (the transverse smooth-dependence-of-geodesics content, absent
from the repo).  Here it is carried as ONE clearly labelled, genuine (non-vacuous) hypothesis
`hΦresc`; from it `hBV` is DERIVED by the chain rule / continuous-linearity of the differential.

Two forms are provided:
* `radialJacobiLink_of_transverseRescale` — reduces `hBV` to the `fderiv`-level rescaling
  `hΦresc : (Φ s (0,w)).1 = (fderiv exp_p (s•v))(s • w)`.
* `radialJacobiLink_of_geodesicVariation` — reduces `hBV` one notch further, to the
  chain-rule-free **variation** primitive `hΦvar` (a `HasDerivAt` of the velocity-variation of
  geodesics), with the `s•` scalar and the exp-differential produced inside via `hasFDerivAt_expMap`
  and derivative uniqueness.  This carries the more honest primitive: the raw statement
  "`Φ`-flow position = velocity variation of geodesics".

Neither form is `a₁ = R/6`, and neither discharges the transverse Φ-rescaling — that single
labelled primitive is the precise remaining step.
-/

set_option maxHeartbeats 1600000

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.JacobianDet

variable {n : ℕ}

/-- **EXP-JET3-3b (floor F1) — the radial Jacobi link `hBV` from the transverse Φ-rescaling.**

Given the direction-`v` geodesic-variation flow `Φ` and the labelled (genuine, non-vacuous)
transverse rescaling germ

```
  hΦresc : ∀ᶠ s, ∀ w, (Φ s (0, w)).1 = (fderiv exp_p (s•v))(s • w),
```

the radial Jacobi link

```
  ∀ᶠ s, ∀ a j, (Φ s (0, e_j)).1 a = (s • expJacobianMat g gi hC p (s•v)) a j
```

holds near `s₀`.  This is exactly `hBV` for `V j s = Φ s (0, e_j)`, the exp-flow Jacobi columns of
`vanVleck_h4_assembled`.  Proof: apply `hΦresc` at `w = e_j`, pull the scalar `s` out of the
continuous-linear differential (`ContinuousLinearMap.map_smul`), and unfold `expJacobianMat`. -/
theorem radialJacobiLink_of_transverseRescale
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) {s₀ : ℝ}
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦresc : ∀ᶠ s in nhds s₀, ∀ (w : Point n),
        (Φ s ((0 : Point n), w)).1 = (fderiv ℝ (expMap g gi hC p) (s • v)) (s • w)) :
    ∀ᶠ s in nhds s₀, ∀ (a j : Fin n),
      (Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n))).1 a
        = (s • expJacobianMat g gi hC p (s • v)) a j := by
  filter_upwards [hΦresc] with s hs
  intro a j
  rw [hs (Pi.single j 1), ContinuousLinearMap.map_smul]
  simp only [Pi.smul_apply, Matrix.smul_apply, expJacobianMat, smul_eq_mul]

/-- **EXP-JET3-3b (floor F1, deeper primitive) — the radial Jacobi link `hBV` from the raw
geodesic-variation primitive.**

Reduces `hBV` one notch below `radialJacobiLink_of_transverseRescale`: the carried primitive
`hΦvar` is the chain-rule-free statement that the position part of the `Φ`-flow at parameter `s`
is the derivative at `ε = 0` of the geodesic velocity-variation `ε ↦ exp_p(s•v + ε • (s•w))`
(Jacobi field = variation of geodesics through the initial velocity).  The `s•` scalar and the
exp-differential `fderiv exp_p (s•v)` are then produced INSIDE, by `hasFDerivAt_expMap`
(differentiability of `exp_p` at the scaled point `s•v`, valid since `‖s•v‖ < expRho` near `s₀`)
composed with the affine reparametrisation `ε ↦ s•v + ε • (s•w)`, using uniqueness of the
derivative.  Hence the only genuine input is the velocity-variation identity itself. -/
theorem radialJacobiLink_of_geodesicVariation
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) {s₀ : ℝ} (hs₀ : |s₀| < 1)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦvar : ∀ᶠ s in nhds s₀, ∀ (w : Point n),
        HasDerivAt (fun ε : ℝ => expMap g gi hC p (s • v + ε • (s • w)))
          ((Φ s ((0 : Point n), w)).1) 0) :
    ∀ᶠ s in nhds s₀, ∀ (a j : Fin n),
      (Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n))).1 a
        = (s • expJacobianMat g gi hC p (s • v)) a j := by
  -- eventual bound `‖s•v‖ < expRho` near `s₀` (uses `|s₀| < 1` and `‖v‖ < expRho`)
  have hball : Metric.ball s₀ (1 - |s₀|) ∈ nhds s₀ :=
    Metric.ball_mem_nhds s₀ (by linarith [hs₀])
  have hsv : ∀ᶠ s in nhds s₀, ‖s • v‖ < expRho g gi hC p := by
    filter_upwards [hball] with s hsmem
    rw [Metric.mem_ball, Real.dist_eq] at hsmem
    have habs : |s| < 1 :=
      calc |s| = |s - s₀ + s₀| := by ring_nf
        _ ≤ |s - s₀| + |s₀| := abs_add_le _ _
        _ < (1 - |s₀|) + |s₀| := by linarith [hsmem]
        _ = 1 := by ring
    rw [norm_smul, Real.norm_eq_abs]
    rcases eq_or_lt_of_le (norm_nonneg v) with h | h
    · rw [← h, mul_zero]; exact expRho_pos g gi hC p
    · calc |s| * ‖v‖ < 1 * ‖v‖ := mul_lt_mul_of_pos_right habs h
        _ = ‖v‖ := one_mul _
        _ < expRho g gi hC p := hv
  filter_upwards [hΦvar, hsv] with s hs hsv_s
  intro a j
  -- `exp_p` is differentiable at the scaled point `s•v`
  obtain ⟨Ψ, -, -, hFD⟩ := hasFDerivAt_expMap g gi hC p (s • v) hsv_s
  -- the affine reparametrisation `ε ↦ s•v + ε•(s•w)` has derivative `s•w` at `0`
  have hrepar : ∀ w : Point n,
      HasDerivAt (fun ε : ℝ => (s • v) + ε • (s • w)) (s • w) 0 := by
    intro w
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (s • w)).const_add (s • v)
    simpa using this
  -- chain rule: `d/dε exp_p(s•v + ε•(s•w))|₀ = (fderiv exp_p (s•v))(s • w)`
  have hchain : ∀ w : Point n,
      HasDerivAt (fun ε : ℝ => expMap g gi hC p (s • v + ε • (s • w)))
        ((fderiv ℝ (expMap g gi hC p) (s • v)) (s • w)) 0 := by
    intro w
    have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (hl := hFD) (hf := hrepar w)
      (hy := by simp)
    rw [hFD.fderiv]
    simpa [Function.comp_def] using hcomp
  -- uniqueness of the derivative ⟹ transverse rescaling at `w = e_j`
  have hresc : (Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n))).1
      = (fderiv ℝ (expMap g gi hC p) (s • v)) (s • (Pi.single j (1 : ℝ) : Point n)) :=
    (hs (Pi.single j 1)).unique (hchain (Pi.single j 1))
  rw [hresc, ContinuousLinearMap.map_smul]
  simp only [Pi.smul_apply, Matrix.smul_apply, expJacobianMat, smul_eq_mul]

end QIQTH.ExpMap
