/-
  ParametrixTransportRadial — M5-b of the off-radial matrix-Jacobi campaign
  (docs/qg_roadmap/MATRIX_JACOBI_PLAN.md).

  **The general-power radial chain rule + the CORRECT parametrix transport term.**  For a positive,
  partially-differentiable scalar field `f` and ANY real power `p`,

      `radialDeriv (fun x => (f x)^p) v = p · f(v)^p · radialDeriv (log f) v`.

  Pure chain rule:  `radialDeriv h v = ∑ i vⁱ ∂ᵢ h`, and per coordinate
  `∂ᵢ(f^p) = p · f^{p−1} ∂ᵢf = p · f^p · (∂ᵢf / f) = p · f^p · ∂ᵢ(log f)`; summing against `vⁱ` pulls
  the common factor `p · f^p` out.  (Same shape as M5-a's `radialDeriv_rpow_neg_half`, but general `p`
  rather than the special `p = −1/2`.)

  **The p = 1/4 correction.**  The parametrix's leading FOLDED coefficient is
  `foldedCoeff … 0 = Θ^{−1/2} · u_0 = (det g̃)^{1/4} · u_0`, because the van-Vleck factor is
  `Θ = vanVleck = (det g̃)^{−1/2}` and the folding multiplies by `Θ^{−1/2} = (det g̃)^{1/4}`.  Hence the
  off-diagonal transport term `(1/t) · G · radialDeriv(foldedCoeff … 0)` needs
  `radialDeriv((det g̃)^{1/4})`, the **+1/4** power — NOT M5-a's `−1/2` power, which is `Θ` itself
  (the van-Vleck factor), not the folded leading coefficient.  Instantiating the general lemma at
  `p = 1/4`, `f = det g̃`:

      `radialDeriv((det g̃)^{1/4}) = ¼ · (det g̃)^{1/4} · radialDeriv(log det g̃)`.

  Combined with the van-Vleck ODE `vanVleck_radialDeriv_ricci_form`
  (`radialDeriv(log det g̃) = 2(θ_B − n) + …`), this expresses the parametrix `(1/t)` transport term
  via the Raychaudhuri expansion `θ_B`.

  ⚠ HONEST SCOPE.  This is ONLY the transport-term chain-rule identity (now at the correct `+1/4`
  power).  It does NOT perform the full `O(1/t)` cancellation (matching the transport term against the
  flat-Gaussian curvature piece (I) and the metric-deviation piece (IV)) — that deeper part of M5 is
  NOT done here.  It does NOT give `a₁ = R/6`.
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

/-! ### #1 — the general-power radial chain rule for `f^p` -/

/-- **The radial derivative of `f^p` for a general real power `p`.**  For a positive,
    partially-differentiable scalar field `f`,
    `radialDeriv (f^p) v = p · f(v)^p · radialDeriv (log f) v`.  Pure chain rule:  per coordinate
    `∂ᵢ(f^p) = p · f^p · ∂ᵢ(log f)`, then sum against `vⁱ`. -/
theorem radialDeriv_rpow (f : Point n → ℝ) (v : Point n) (p : ℝ) (hpos : 0 < f v)
    (hf : ∀ i, PdiffAt f i v) :
    radialDeriv (fun x => (f x) ^ (p : ℝ)) v
      = p * (f v) ^ (p : ℝ) * radialDeriv (fun x => Real.log (f x)) v := by
  have hne : f v ≠ 0 := ne_of_gt hpos
  -- The one-variable slice `t ↦ f (update v i t)` has derivative `pd f i v` at `v i`.
  have hslice : ∀ i, HasDerivAt (fun t => f (Function.update v i t)) (pd f i v) (v i) :=
    fun i => (hf i).hasDerivAt
  have hupd : ∀ i, f (Function.update v i (v i)) = f v := fun i => by
    rw [Function.update_eq_self]
  -- Per-coordinate chain rule for the `rpow`.
  have hpd_rpow : ∀ i, pd (fun x => (f x) ^ (p : ℝ)) i v
      = pd f i v * p * (f v) ^ ((p : ℝ) - 1) := by
    intro i
    have hx : f (Function.update v i (v i)) ≠ 0 := by rw [hupd i]; exact hne
    have hd := (hslice i).rpow_const (p := (p : ℝ)) (Or.inl hx)
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

/-! ### #2 — the p = 1/4 parametrix transport term for the folded leading coefficient -/

/-- **The radial derivative of the folded leading coefficient `(det g̃)^{1/4}`.**  The leading folded
    coefficient is `foldedCoeff … 0 = Θ^{−1/2} · u_0 = (det g̃)^{1/4} · u_0` (with `Θ = vanVleck =
    (det g̃)^{−1/2}`), so the parametrix transport term `(1/t) · G · radialDeriv(foldedCoeff … 0)`
    needs the **+1/4** power (correcting M5-a's `−1/2` power, which is `Θ` itself, not the folded
    coefficient).  Instantiating #1 at `f = det g̃`, `p = 1/4`:
    `radialDeriv((det g̃)^{1/4}) = ¼ · (det g̃ v)^{1/4} · radialDeriv(log det g̃)`. -/
theorem radialDeriv_foldedCoeff_leading
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (hpos : 0 < Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p v i j))
    (hdiff : ∀ i, PdiffAt
      (fun x => Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j)) i v) :
    radialDeriv
        (fun x => (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j))
          ^ ((1:ℝ)/4)) v
      = (1/4) * (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p v i j)) ^ ((1:ℝ)/4)
        * radialDeriv
            (fun x => Real.log
              (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j))) v :=
  radialDeriv_rpow _ v ((1:ℝ)/4) hpos hdiff

end QIQTH.ExpMap
