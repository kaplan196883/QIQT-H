/-
# RECENTER brick J4-61 — the `uniformFlowExp` fderiv→pullback-metric NONDEGENERACY hinge.

Brick-A(β) re-architects the residual chain off the opaque per-`q` `expMap`/`expRho` onto the
UNIFORM-flow endpoint `uniformFlowExp` (uniform-over-`K` provenance, no `Classical.choose`
injectivity radius).  J4-58 (`PullbackNondegFromFDeriv.lean`) supplied the hinge

  `IsUnit (fderiv ℝ (expMap …) v)` + base-metric nondeg ⟹ `IsUnit (matToCLM (expPullbackMetric …))`

for the OPAQUE `expMap`.  This file is the `uniformFlowExp` ANALOGUE:

  * `uniformFlowPullbackMetric` — the pullback metric of `uniformFlowExp` (mirror of `expPullbackMetric`);
  * `uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit` — the HINGE:
      `IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v)` + `IsUnit (matToCLM (g (uniformFlowExp … v)))`
        ⟹ `IsUnit (matToCLM (uniformFlowPullbackMetric g gi hC hK q v))`;
  * `uniformConfinedTubeOn_pullback_isUnit` — the certificate corollary: the uniform-radius certificate's
    `hnondeg` (fderiv-invertible over `q ∈ K`, `‖v‖ < r`) + base-metric nondeg ⟹ pullback nondeg.

MATH.  The pullback metric is literally the congruence
    `g̃_{ij}(v) = ∑_{a,b} g_{ab}(uniformFlowExp_q v) · (D uniformFlowExp_q v · e_i)_a · (… · e_j)_b`,
i.e. `g̃(v) = Jᵀ · (g∘uniformFlowExp)(v) · J` with `J = D uniformFlowExp_q v` the Jacobian matrix.  A
congruence `JᵀGJ` of units is a unit — EXACTLY the situation J4-58 already handles GENERICALLY via
`isUnit_matToCLM_congr` (NOT `expMap`-specific).  So the hinge proof is verbatim J4-58 with `expMap`
replaced by `uniformFlowExp`.

══════════════════════════════════════════════════════════════════════════════════════════════════════
⚠ HONEST SCOPE (binding).  The `g`-nondegeneracy input `hg : IsUnit (matToCLM (g (uniformFlowExp … v)))`
is a GENUINE geometric hypothesis (the base metric is nondegenerate at the far point `uniformFlowExp_q v`),
NOT the conclusion.  The conclusion `IsUnit (matToCLM (uniformFlowPullbackMetric …))` is DERIVED from it
plus the `fderiv`-invertibility `hJ` (supplied by the uniform-radius certificate's `hnondeg`).  No `sorry`,
no new axioms, no vacuous hypotheses (neither `hJ` nor `hg` equals the goal).  NOT `a₁ = R/6`.
-/
import QIQTH.PullbackNondegFromFDeriv
import QIQTH.UniformRadiusCert
import QIQTH.UniformFlowNondeg
import QIQTH.PullbackMetric
import Mathlib

open Finset
open QIQTH.Curvature QIQTH.ExpMap
open scoped BigOperators Matrix

namespace QIQTH.PullbackMetric

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### N1 — the pullback metric of `uniformFlowExp` (mirror of `expPullbackMetric`). -/

/-- **N1 — the pullback metric of the uniform-flow exp endpoint `uniformFlowExp g gi hC hK q`.**
    EXACT mirror of `expPullbackMetric`, with `expMap g gi hC p` replaced by `uniformFlowExp g gi hC hK q`:
    `g̃_{ij}(v) = ∑_{a,b} g_{ab}(uniformFlowExp_q v) · (D uniformFlowExp_q v · e_i)_a · (… · e_j)_b`. -/
noncomputable def uniformFlowPullbackMetric (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q v : Point n) (i j : Fin n) : ℝ :=
  ∑ a, ∑ b, g (uniformFlowExp g gi hC hK q v) a b
    * (fderiv ℝ (uniformFlowExp g gi hC hK q) v) (Pi.single i 1) a
    * (fderiv ℝ (uniformFlowExp g gi hC hK q) v) (Pi.single j 1) b

/-! ### N2 — the hinge: `fderiv` invertible ⟹ `uniformFlowExp` pullback metric nondegenerate. -/

/-- **★ J4-61 — the `uniformFlowExp` fderiv→pullback-metric NONDEGENERACY hinge.**
    If the uniform-flow exp differential `D uniformFlowExp_q v = fderiv ℝ (uniformFlowExp g gi hC hK q) v`
    is invertible (a unit in the operator ring) AND the base metric `g` is nondegenerate at the far point
    `uniformFlowExp_q v` (`IsUnit (matToCLM (g (uniformFlowExp … v)))`, a GENUINE geometric input), then
    the pullback metric `g̃(v)` assembles to a UNIT `matToCLM (g̃ v)` — i.e. `g̃` is nondegenerate at `v`.

    Proof (verbatim J4-58, REUSING the generic `isUnit_matToCLM_congr`): `g̃(v) = Jᵀ · (g∘F)(v) · J` is a
    congruence (`uniformFlowPullbackMetric` is literally that sum); a congruence of units is a unit. -/
theorem uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q v : Point n)
    (hJ : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v))
    (hg : IsUnit (matToCLM (fun a b => g (uniformFlowExp g gi hC hK q v) a b))) :
    IsUnit (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)) := by
  -- Generic congruence lemma (J4-58) builds the product `JᵀGJ`; NOT `expMap`-specific.
  have key := isUnit_matToCLM_congr (fderiv ℝ (uniformFlowExp g gi hC hK q) v)
    (fun a b => g (uniformFlowExp g gi hC hK q v) a b) hJ hg
  -- Identify `g̃(v) = Jᵀ · (g∘F) · J` entrywise; `uniformFlowPullbackMetric` is literally that congruence.
  convert key using 2
  funext i j
  simp only [uniformFlowPullbackMetric, Matrix.mul_apply, Matrix.transpose_apply, jacMat,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-! ### N3 — the uniform-radius certificate corollary. -/

/-- **N3 — certificate ⟹ pullback nondegeneracy over `q ∈ K`, `‖v‖ < r`.**
    The uniform-radius certificate `UniformConfinedTubeOn` carries `hnondeg` (the fderiv of
    `uniformFlowExp g gi hC hK q` is invertible for `q ∈ K`, `‖v‖ < r`).  Combined with the GENUINE
    base-metric nondegeneracy `hg` at the far point `uniformFlowExp_q v`, the hinge N2 yields pullback
    nondegeneracy.  The `hg` input is carried HONESTLY as geometry — it is NOT the conclusion. -/
theorem uniformConfinedTubeOn_pullback_isUnit
    {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {r : ℝ}
    (cert : UniformConfinedTubeOn g gi hC hK r)
    {q : Point n} (hq : q ∈ K) {v : Point n} (hv : ‖v‖ < r)
    (hg : IsUnit (matToCLM (fun a b => g (uniformFlowExp g gi hC hK q v) a b))) :
    IsUnit (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)) :=
  uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit g gi hC hK q v
    (cert.hnondeg q hq v hv) hg

end QIQTH.PullbackMetric
