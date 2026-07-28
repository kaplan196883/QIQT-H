/-
  ParametrixTransportRicci — M5-c of the off-radial matrix-Jacobi campaign
  (docs/qg_roadmap/MATRIX_JACOBI_PLAN.md).

  **The parametrix leading transport term in Raychaudhuri form.**  The parametrix's leading FOLDED
  coefficient is `foldedCoeff … 0 = Θ^{−1/2} · u_0 = (det g̃)^{1/4} · u_0` (with `Θ = vanVleck =
  (det g̃)^{−1/2}`, and `u_0 = 1`).  So the off-diagonal `(1/t) · G · radialDeriv(foldedCoeff … 0)`
  transport term needs `radialDeriv((det g̃)^{1/4})`.  This brick assembles

    * **M5-b** (`radialDeriv_foldedCoeff_leading`): the CORRECT `+1/4` transport chain rule
      `radialDeriv((det g̃)^{1/4}) = ¼ · (det g̃)^{1/4} · radialDeriv(log det g̃)`, and

    * **EXP-JET3-3c** (`vanVleck_radialDeriv_ricci_form`): the van-Vleck radial ODE in Ricci-carrying
      form `radialDeriv(log det g̃) = 2·(θ_B − n) + radialDeriv(log det(g∘exp))`,

  into the single Raychaudhuri-form identity

    `radialDeriv((det g̃)^{1/4}) = ¼·(det g̃)^{1/4}·(2·(θ_B − n) + radialDeriv(log det(g∘exp)))`,

  where `θ_B := tr(B'(1)·B(1)⁻¹)` is the Raychaudhuri expansion of the clean matrix Jacobi field `B`
  (which obeys `θ_B' = −Ric`).  So the parametrix off-diagonal transport term is now expressed via the
  Raychaudhuri expansion.

  ⚠ HONEST SCOPE.  A DIRECT two-rewrite assembly.  It is **CONDITIONAL** on `hresc` (the EXP-JET3-3b
  rescaling geometric input) plus the B/K2 positivity/regularity hypotheses.  It is ONLY the transport
  term in Raychaudhuri form — it does NOT perform the full `O(1/t)` cancellation (matching the
  transport term against the flat-Gaussian curvature piece (I) and the metric-deviation piece (IV)),
  and it does NOT give `a₁ = R/6`.

  Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.ParametrixTransportRadial
import QIQTH.VanVleckRicciODE

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.PullbackMetric Matrix
open scoped Topology

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- **M5-c — the parametrix leading transport term `radialDeriv((det g̃)^{1/4})` in Raychaudhuri
form.**  Combining M5-b's `+1/4` transport chain rule with EXP-JET3-3c's van-Vleck Ricci ODE gives
```
  radialDeriv((det g̃)^{1/4})
    = ¼·(det g̃)^{1/4}·(2·(θ_B − n) + radialDeriv(log det(g∘exp))),
```
with `θ_B = tr(B'(1)·B(1)⁻¹)` the Raychaudhuri expansion of the clean matrix Jacobi field `B`
(obeying `θ_B' = −Ric`).  So the parametrix off-diagonal `(1/t)·G·radialDeriv(foldedCoeff … 0)`
transport term (for `u_0 = 1`) is now expressed via the Raychaudhuri expansion.

CONDITIONAL on `hresc` (the rescaling geometric input) plus the B/K2 positivity/regularity
hypotheses.  NOT the M5 `O(1/t)` cancellation matching (I)+(IV), NOT `a₁ = R/6`. -/
theorem parametrixTransport_raychaudhuri_form
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (hpos : 0 < Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p v i j))
    (hdiff : ∀ i, PdiffAt
      (fun x => Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j)) i v)
    (B B' : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hB : HasDerivAt B (B' 1) 1) (hu : IsUnit (B 1))
    (hJdiff : DifferentiableAt ℝ
      (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v)
    (hresc : (fun s => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)))
             =ᶠ[nhds (1:ℝ)] (fun s => Real.log ((B s).det) - (n : ℝ) * Real.log s))
    (hJ : ∀ᶠ x in 𝓝 v, 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p x)
    (hD : ∀ᶠ x in 𝓝 v, 0 < Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b))
    (hJp : ∀ i, PdiffAt (QIQTH.JacobianDet.expJacobianDet g gi hC p) i v)
    (hDp : ∀ i, PdiffAt (fun x => Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b)) i v) :
    radialDeriv
        (fun x => (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j))
          ^ ((1:ℝ)/4)) v
      = (1/4) * (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p v i j)) ^ ((1:ℝ)/4)
        * (2 * ((B' 1 * (B 1)⁻¹).trace - (n : ℝ))
          + radialDeriv (fun x => Real.log (Matrix.det (Matrix.of fun a b =>
              g (expMap g gi hC p x) a b))) v) := by
  rw [radialDeriv_foldedCoeff_leading g gi hC p v hpos hdiff,
    vanVleck_radialDeriv_ricci_form g gi hC p v B B' hB hu hJdiff hresc hJ hD hJp hDp]

end QIQTH.ExpMap
