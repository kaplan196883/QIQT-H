/-
# RECENTER brick J4-58 — the fderiv→pullback-metric NONDEGENERACY hinge.

`RecenterAnnulusUncond.lean` reduced the cutoff-residual annulus bounds to a CONTINUITY residue that is
delivered wherever the assembled pullback operator `matToCLM (g̃ w)` is a UNIT (`g̃` nondegenerate).  Near
`0` this is `expPullbackMetric_isUnit_near_zero` (openness of units).  On the wider ball the missing input
is **`D exp_p` invertible ⟹ `g̃` nondegenerate**.  This file supplies exactly that HINGE:

  `expPullbackMetric_isUnit_of_fderiv_isUnit`:
    `IsUnit (fderiv ℝ (expMap g gi hC p) v)` → `IsUnit (matToCLM (g (exp_p v)))`
      → `IsUnit (matToCLM (fun a b => expPullbackMetric g gi hC p v a b))`.

MATH.  The pullback metric is literally the congruence
    `g̃_{ij}(v) = ∑_{a,b} g_{ab}(exp_p v) · (D exp_p v · e_i)_a · (D exp_p v · e_j)_b`,
i.e. `g̃(v) = Jᵀ · (g∘exp)(v) · J` with `J = D exp_p v` the Jacobian matrix.  A congruence `JᵀGJ` of units
is a unit: `J` a unit ⟹ `Jᵀ` a unit (`det Jᵀ = det J`), and the operator ring product of units is a unit.

The bridge `matToCLM` (a matrix `→` its `mulVec` operator) transports matrix-invertibility to operator
invertibility BOTH WAYS, via the two algebra equivalences
  `Matrix.toLinAlgEquiv'` : `Matrix ≃ₐ End`  and  `Module.End.toContinuousLinearMap` : `End ≃ₐ CLM`.

══════════════════════════════════════════════════════════════════════════════════════════════════════
⚠ HONEST SCOPE (binding).  The `g`-nondegeneracy input `hg : IsUnit (matToCLM (g (exp_p v)))` is a GENUINE
geometric hypothesis (the base metric is nondegenerate at the far point `exp_p v`), NOT the conclusion.
The conclusion `IsUnit (matToCLM g̃(v))` is DERIVED from it plus the `fderiv`-invertibility `hJ`.  This is
the exact lemma a future "`D exp_p` invertible on ball" result feeds to discharge `hgi_cont` on the ball.
NOT `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hypotheses (neither `hJ` nor `hg` equals the goal).
-/
import Mathlib
import QIQTH.PullbackMetricNondegNearZero
import QIQTH.PullbackMetric

open Finset
open QIQTH.Curvature QIQTH.ExpMap
open scoped BigOperators Matrix

namespace QIQTH.PullbackMetric

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. The matrix ↔ operator bridge: `IsUnit (matToCLM A) ↔ IsUnit A`. -/

/-- **`matToCLM` is the CLM induced by the matrix `A` via `Matrix.toLin' / mulVec`.**
    Both act as `v ↦ A *ᵥ v`, and `matToCLM A = (End.toContinuousLinearMap) (Matrix.toLinAlgEquiv' A)`. -/
theorem matToCLM_eq_algEquiv (A : Matrix (Fin n) (Fin n) ℝ) :
    matToCLM (A : Fin n → Fin n → ℝ)
      = (Module.End.toContinuousLinearMap (Point n)) (Matrix.toLinAlgEquiv' A) := by
  apply ContinuousLinearMap.ext
  intro v
  funext i
  rw [matToCLM_apply]
  have hrfl : ((Module.End.toContinuousLinearMap (Point n)) (Matrix.toLinAlgEquiv' A)) v
      = (Matrix.toLinAlgEquiv' A) v := rfl
  rw [hrfl, Matrix.toLinAlgEquiv'_apply]
  simp [Matrix.mulVec, dotProduct]

/-- **★ H2-bridge — `matToCLM A` is a UNIT iff the matrix `A` is a unit.**
    Both `Matrix.toLinAlgEquiv'` and `Module.End.toContinuousLinearMap` are algebra equivalences, hence
    monoid isomorphisms preserving `IsUnit` in both directions. -/
theorem isUnit_matToCLM_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    IsUnit (matToCLM (A : Fin n → Fin n → ℝ)) ↔ IsUnit A := by
  rw [matToCLM_eq_algEquiv]
  constructor
  · intro h
    have h1 : IsUnit (Matrix.toLinAlgEquiv' A) := by
      have h1' := h.map (Module.End.toContinuousLinearMap (Point n)).symm
      rwa [AlgEquiv.symm_apply_apply] at h1'
    have h2 := h1.map (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin n)).symm
    rwa [AlgEquiv.symm_apply_apply] at h2
  · intro hA
    exact (hA.map (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin n))).map
      (Module.End.toContinuousLinearMap (Point n))

/-! ### 2. The Jacobian matrix of a CLM and its round-trip. -/

/-- The matrix of a CLM `J` in the standard basis: `jacMat J a i = (J e_i)_a`. -/
noncomputable def jacMat (J : Point n →L[ℝ] Point n) : Matrix (Fin n) (Fin n) ℝ :=
  fun a i => J (Pi.single i 1) a

/-- **`matToCLM (jacMat J) = J`.**  The `mulVec` operator of the standard-basis matrix of `J` is `J`. -/
theorem matToCLM_jacMat (J : Point n →L[ℝ] Point n) : matToCLM (jacMat J) = J := by
  apply ContinuousLinearMap.ext
  intro w
  have hw : w = ∑ b, w b • (Pi.single b (1 : ℝ) : Point n) := by
    funext k
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  funext i
  rw [matToCLM_apply]
  simp only [jacMat]
  conv_rhs => rw [hw, map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ### 3. ★ H3 — congruence `JᵀGJ` of units is a unit (operator form). -/

/-- **★ H3 — a congruence of units is a unit.**  If the Jacobian CLM `J` is a unit and the assembled
    base-metric operator `matToCLM G` is a unit, then the pullback `matToCLM (Jᵀ G J)` is a unit.
    (`Jᵀ` a unit from `det Jᵀ = det J`; product of units in the operator ring.) -/
theorem isUnit_matToCLM_congr (J : Point n →L[ℝ] Point n) (G : Matrix (Fin n) (Fin n) ℝ)
    (hJ : IsUnit J) (hG : IsUnit (matToCLM (G : Fin n → Fin n → ℝ))) :
    IsUnit (matToCLM (((jacMat J)ᵀ * G * jacMat J : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ)) := by
  have hJm : IsUnit (jacMat J) := by
    rw [← matToCLM_jacMat J] at hJ
    exact (isUnit_matToCLM_iff (jacMat J)).mp hJ
  have hGm : IsUnit G := (isUnit_matToCLM_iff G).mp hG
  have hJt : IsUnit (jacMat J)ᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
    exact hJm
  rw [isUnit_matToCLM_iff]
  exact (hJt.mul hGm).mul hJm

/-! ### 4. ★ H4 — the hinge: `fderiv` invertible ⟹ pullback metric nondegenerate. -/

/-- **★ J4-58 — the fderiv→pullback-metric NONDEGENERACY hinge.**
    If the exponential-map differential `D exp_p v = fderiv ℝ (exp_p) v` is invertible (a unit in the
    operator ring) AND the base metric `g` is nondegenerate at the far point `exp_p v`
    (`IsUnit (matToCLM (g (exp_p v)))`, a GENUINE geometric input), then the pullback metric
    `g̃(v)` assembles to a UNIT `matToCLM (g̃ v)` — i.e. `g̃` is nondegenerate at `v`.

    Proof: `g̃(v) = Jᵀ · (g∘exp)(v) · J` is a congruence (`expPullbackMetric` is literally that sum);
    congruence of units is a unit (`isUnit_matToCLM_congr`). -/
theorem expPullbackMetric_isUnit_of_fderiv_isUnit
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (hJ : IsUnit (fderiv ℝ (expMap g gi hC p) v))
    (hg : IsUnit (matToCLM (fun a b => g (expMap g gi hC p v) a b))) :
    IsUnit (matToCLM (fun a b => expPullbackMetric g gi hC p v a b)) := by
  -- Let the congruence lemma (where `G : Matrix` is properly typed) build the product `JᵀGJ`.
  have key := isUnit_matToCLM_congr (fderiv ℝ (expMap g gi hC p) v)
    (fun a b => g (expMap g gi hC p v) a b) hJ hg
  -- Identify `g̃(v) = Jᵀ · (g∘exp) · J` entrywise; `expPullbackMetric` is literally that congruence.
  convert key using 2
  funext i j
  simp only [expPullbackMetric, Matrix.mul_apply, Matrix.transpose_apply, jacMat, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end QIQTH.PullbackMetric
