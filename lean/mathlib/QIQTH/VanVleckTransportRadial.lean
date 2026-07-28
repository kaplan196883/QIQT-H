/-
  VanVleckTransportRadial — M5-a of the off-radial matrix-Jacobi campaign
  (docs/qg_roadmap/MATRIX_JACOBI_PLAN.md).

  **The radial derivative of the van-Vleck factor.**  For a positive, partially-differentiable scalar
  field `f`, the van-Vleck-type factor `Θ = f^{−1/2}` has radial (Euler) derivative

      `radialDeriv (f^{−1/2}) v = −(1/2) · f(v)^{−1/2} · radialDeriv (log f) v`.

  This is a clean chain-rule identity:  `radialDeriv h v = ∑ i vⁱ ∂ᵢ h`, and per coordinate
  `∂ᵢ(f^{−1/2}) = (−1/2) f^{−3/2} ∂ᵢf = (−1/2) f^{−1/2} · (∂ᵢf / f) = (−1/2) f^{−1/2} · ∂ᵢ(log f)`;
  summing against `vⁱ` pulls the common factor `−(1/2) f^{−1/2}` out.

  **Why it matters.**  The parametrix's off-diagonal residual
  (`QIQTH.HeatResidualBound.parametrixResidual_offdiag_absorbed`) contains the *transport* term
  `(1/t) · G · radialDeriv(Θ)` (with `foldedCoeff … 0 = Θ`, the van-Vleck factor `(det g̃)^{−1/2}`).
  With `f = det g̃`, this file rewrites that transport term in terms of `radialDeriv(log det g̃)` —
  hence, via `QIQTH.ExpMap.vanVleck_radialDeriv_via_raychaudhuri` (CONDITIONAL on `Y = D exp`, i.e.
  that `log det g̃` is the log-Jacobian whose radial derivative is `2θ`), to the Raychaudhuri
  expansion `θ`.

  ⚠ HONEST SCOPE.  This is ONLY the chain-rule identity for the transport term.  It does NOT perform
  the full `O(1/t)` cancellation (matching the transport term against the flat-Gaussian curvature
  piece (I) and the metric-deviation piece (IV)) — that is the deeper part of M5, NOT done here.  It
  does NOT give `a₁ = R/6`.  And the θ-connection remains conditional on `Y = D exp`
  (`vanVleck_radialDeriv_via_raychaudhuri`'s hypothesis).
-/
import Mathlib
import QIQTH.RadialDistance
import QIQTH.Curvature
import QIQTH.JacobianDet
import QIQTH.PullbackMetric

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.PullbackMetric
open scoped BigOperators

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-! ### #1 — the clean chain-rule identity for the van-Vleck factor `f^{−1/2}` -/

/-- **The radial derivative of `f^{−1/2}`.**  For a positive, partially-differentiable scalar field
    `f`, `radialDeriv (f^{−1/2}) v = −(1/2) · f(v)^{−1/2} · radialDeriv (log f) v`.  Pure chain rule:
    per coordinate `∂ᵢ(f^{−1/2}) = (−1/2) f^{−1/2} ∂ᵢ(log f)`, then sum against `vⁱ`. -/
theorem radialDeriv_rpow_neg_half (f : Point n → ℝ) (v : Point n) (hpos : 0 < f v)
    (hf : ∀ i, PdiffAt f i v) :
    radialDeriv (fun x => (f x) ^ (-(1/2) : ℝ)) v
      = -(1/2) * (f v) ^ (-(1/2) : ℝ) * radialDeriv (fun x => Real.log (f x)) v := by
  have hne : f v ≠ 0 := ne_of_gt hpos
  -- The one-variable slice `t ↦ f (update v i t)` has derivative `pd f i v` at `v i`.
  have hslice : ∀ i, HasDerivAt (fun t => f (Function.update v i t)) (pd f i v) (v i) :=
    fun i => (hf i).hasDerivAt
  have hupd : ∀ i, f (Function.update v i (v i)) = f v := fun i => by
    rw [Function.update_eq_self]
  -- Per-coordinate chain rule for the `rpow`.
  have hpd_rpow : ∀ i, pd (fun x => (f x) ^ (-(1/2) : ℝ)) i v
      = pd f i v * (-(1/2) : ℝ) * (f v) ^ ((-(1/2) : ℝ) - 1) := by
    intro i
    have hx : f (Function.update v i (v i)) ≠ 0 := by rw [hupd i]; exact hne
    have hd := (hslice i).rpow_const (p := (-(1/2) : ℝ)) (Or.inl hx)
    rw [hupd i] at hd
    exact hd.deriv
  -- Per-coordinate chain rule for the `log`.
  have hpd_log : ∀ i, pd (fun x => Real.log (f x)) i v = pd f i v / f v := by
    intro i
    have hx : f (Function.update v i (v i)) ≠ 0 := by rw [hupd i]; exact hne
    have hd := (hslice i).log hx
    rw [hupd i] at hd
    exact hd.deriv
  -- Assemble: rewrite each summand and pull the common factor out of the sum.
  simp only [radialDeriv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hpd_rpow i, hpd_log i, Real.rpow_sub hpos, Real.rpow_one]
  ring

/-! ### #2 — application to the van-Vleck factor `Θ = (det g̃)^{−1/2}` -/

/-- **The radial derivative of the van-Vleck factor `Θ = (det g̃)^{−1/2}`.**  Instantiating #1 at
    `f = det g̃` (the RNC pullback metric determinant `x ↦ det (g̃ x)`), the transport factor
    `Θ = (det g̃)^{−1/2}` (i.e. `foldedCoeff … 0`) has radial derivative
    `−(1/2) · (det g̃ v)^{−1/2} · radialDeriv (log det g̃) v`.  This is the identity connecting the
    parametrix transport term to `radialDeriv (log det g̃)` — hence, conditionally, to `2θ`. -/
theorem radialDeriv_vanVleck_factor
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (hpos : 0 < Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p v i j))
    (hf : ∀ i, PdiffAt
      (fun x => Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j)) i v) :
    radialDeriv
        (fun x => (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j))
          ^ (-(1/2) : ℝ)) v
      = -(1/2) * (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p v i j)) ^ (-(1/2) : ℝ)
        * radialDeriv
            (fun x => Real.log
              (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j))) v :=
  radialDeriv_rpow_neg_half _ v hpos hf

end QIQTH.ExpMap
