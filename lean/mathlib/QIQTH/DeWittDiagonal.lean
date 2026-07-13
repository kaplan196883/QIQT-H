/-
# The DeWitt / Minakshisundaram DIAGONAL heat coefficient `u₁(x,x) = τ/6`

MANDATORY FIREWALL (binding, honest):

  • This DERIVES the DeWitt/Minakshisundaram DIAGONAL heat coefficient `u₁(x,x) = τ/6` by
    JET-ALGEBRA — the factor chain Θ's −1/6 Ric → u₀ = Θ^{−1/2}'s +1/12 →
    flat-Laplacian-of-quadratic (= 2·trace) → τ/6 is genuinely COMPUTED (Part C even
    derives Θ's −1/6 from the metric's −1/3 Riem via det/trace).

  • CARRIED (the geometric/analytic substrate we do NOT build — structure fields, never
    axioms): the normal-coordinate volume/van-Vleck 2-jet (Θ = 1 − (1/6)Ric·y², or the
    metric g = δ − (1/3)Riem·y²), the √det first-variation, the Ricci contraction, and the
    TRANSPORT diagonal-reduction `u₁(x,x) = −Δ_geom u₀|₀`.  These encode the exponential
    map, geodesic distance, the van Vleck determinant, and the radial r-integration — i.e.
    the manifold substrate + the parametrix analysis.

  • It does NOT build the heat semigroup / kernel / parametrix convergence
    (Rosenberg §3.2.2 / BGV §2.4 — the analytic wall, no Mathlib substrate).  It computes
    the coefficient GIVEN the recursion + the normal-coordinate geometry.  NOT the abstract
    coordinate-free tensor (upstream).  NOT the conjecture, NOT the strong holographic
    principle, NOT QG.  No axioms, no `sorry`.

Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1 (transport
recursion, diagonal).  Heat-kernel gap plan, Phase-4 / §3.2.1 downpayment.
-/
import Mathlib
import QIQTH.CoordinateCurvature

open scoped BigOperators

namespace QIQTH.DeWittDiagonal

/-! ## Part A — the quadratic-jet algebra (self-contained) -/

section QuadraticJet
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- quadratic coeff of `(1 + θ₂)^{−1/2} = 1 − ½θ₂ + O(|y|³)`. -/
noncomputable def invSqrtQuad (θ : ι → ι → ℝ) (a b : ι) : ℝ := -(1/2 : ℝ) * θ a b

omit [Fintype ι] [DecidableEq ι] in
lemma invSqrtQuad_spec (θ : ι → ι → ℝ) (a b : ι) :
    2 * invSqrtQuad θ a b + θ a b = 0 := by
  unfold invSqrtQuad; ring

/-- `∂²/(∂y_c)²(y_a y_b)|₀`, ordered double-sum convention (no ½). -/
def d2MonomialAtZero (c a b : ι) : ℝ := if a = c then (if b = c then (2:ℝ) else 0) else 0

def d2QuadAtZero (c : ι) (Q : ι → ι → ℝ) : ℝ := ∑ a, ∑ b, Q a b * d2MonomialAtZero c a b

lemma d2QuadAtZero_eq (c : ι) (Q : ι → ι → ℝ) : d2QuadAtZero c Q = 2 * Q c c := by
  classical
  unfold d2QuadAtZero d2MonomialAtZero
  calc (∑ a, ∑ b, Q a b * (if a = c then (if b = c then (2:ℝ) else 0) else 0))
        = ∑ a, ∑ b, (if a = c then (if b = c then Q a b * 2 else 0) else 0) := by
          simp [mul_ite]
    _ = Q c c * 2 := by simp
    _ = 2 * Q c c := by ring

/-- analytic flat Laplacian `Σ_c ∂²_c`. -/
def analyticLapQuadAtZero (Q : ι → ι → ℝ) : ℝ := ∑ c, d2QuadAtZero c Q

lemma analyticLapQuadAtZero_eq_trace (Q : ι → ι → ℝ) :
    analyticLapQuadAtZero Q = 2 * ∑ a, Q a a := by
  classical
  unfold analyticLapQuadAtZero
  calc (∑ c, d2QuadAtZero c Q) = ∑ c, 2 * Q c c := by simp [d2QuadAtZero_eq]
    _ = 2 * ∑ a, Q a a := by rw [Finset.mul_sum]

/-- geometer/positive convention `Δ_geom = −Σ∂²`. -/
def geomLapQuadAtZero (Q : ι → ι → ℝ) : ℝ := - analyticLapQuadAtZero Q

end QuadraticJet

/-! ## Part B — the normal-coordinate jet + the headline -/

structure NormalCoordJet (n : ℕ) where
  Ric : Fin n → Fin n → ℝ
  tau : ℝ
  tau_eq_trace : tau = ∑ a : Fin n, Ric a a
  thetaQuad : Fin n → Fin n → ℝ
  -- CARRIED: the normal-coordinate volume/van-Vleck 2-jet Θ = 1 − (1/6)Ric·y² + O(|y|³)
  thetaQuad_eq : ∀ a b, thetaQuad a b = -(1/6 : ℝ) * Ric a b

namespace NormalCoordJet
variable {n : ℕ} (J : NormalCoordJet n)

noncomputable def u0Quad (a b : Fin n) : ℝ := invSqrtQuad J.thetaQuad a b

lemma u0Quad_eq (a b : Fin n) : J.u0Quad a b = (1/12 : ℝ) * J.Ric a b := by
  rw [u0Quad, invSqrtQuad, J.thetaQuad_eq a b]; ring

/-- ★ the analytic Laplacian of u₀'s quadratic part = τ/6 (the derived factor chain). -/
theorem analyticLap_u0Quad_eq_tau_div_six :
    analyticLapQuadAtZero J.u0Quad = J.tau / 6 := by
  classical
  calc analyticLapQuadAtZero J.u0Quad = 2 * ∑ a : Fin n, J.u0Quad a a := by
          simpa using analyticLapQuadAtZero_eq_trace J.u0Quad
    _ = 2 * ∑ a : Fin n, (1/12 : ℝ) * J.Ric a a := by simp [u0Quad_eq]
    _ = (1/6 : ℝ) * ∑ a : Fin n, J.Ric a a := by rw [← Finset.mul_sum]; ring
    _ = J.tau / 6 := by rw [← J.tau_eq_trace]; ring

theorem minus_geomLap_u0Quad_eq_tau_div_six :
    - geomLapQuadAtZero J.u0Quad = J.tau / 6 := by
  simpa [geomLapQuadAtZero] using J.analyticLap_u0Quad_eq_tau_div_six

end NormalCoordJet

/-- the Minakshisundaram transport reduction carried as a field (NOT an axiom). -/
structure HeatTransportJet (n : ℕ) where
  jet : NormalCoordJet n
  u1diag : ℝ
  -- CARRIED: the diagonal-limit of the radial transport recursion u₁(x,x) = −Δ_geom u₀|₀
  transport_diag : u1diag = - geomLapQuadAtZero jet.u0Quad

namespace HeatTransportJet

/-- ★★ THE HEADLINE: the DeWitt diagonal heat coefficient is τ/6. -/
theorem u1diag_eq_tau_div_six {n : ℕ} (H : HeatTransportJet n) :
    H.u1diag = H.jet.tau / 6 := by
  rw [H.transport_diag]; simpa using H.jet.minus_geomLap_u0Quad_eq_tau_div_six

end HeatTransportJet

/-! ## Part C — derive Θ's −1/6 from the metric's −1/3 Riem via det/trace -/

structure MetricNormalCoordJet (n : ℕ) where
  Riem : Fin n → Fin n → Fin n → Fin n → ℝ
  Ric : Fin n → Fin n → ℝ
  tau : ℝ
  tau_eq_trace : tau = ∑ a : Fin n, Ric a a
  Ric_eq_contract : ∀ a b, Ric a b = ∑ i : Fin n, Riem i a i b
  gQuad : Fin n → Fin n → Fin n → Fin n → ℝ
  -- CARRIED: normal-coord metric g_ij = δ_ij − (1/3)R_iajb y^a y^b + O(|y|³)
  gQuad_eq : ∀ i j a b, gQuad i j a b = -(1/3 : ℝ) * Riem i a j b
  thetaQuad : Fin n → Fin n → ℝ
  -- CARRIED: √det(I + h₂) = 1 + ½ tr h₂ + O(|y|³)
  theta_from_det : ∀ a b, thetaQuad a b = (1/2 : ℝ) * ∑ i : Fin n, gQuad i i a b

namespace MetricNormalCoordJet
variable {n : ℕ} (M : MetricNormalCoordJet n)

/-- ★ DERIVE Θ's −1/6 Ric coefficient from the metric −1/3 Riem via det/trace + Ricci
contraction. -/
theorem thetaQuad_eq_neg_sixth_Ric (a b : Fin n) :
    M.thetaQuad a b = -(1/6 : ℝ) * M.Ric a b := by
  rw [M.theta_from_det a b]
  simp_rw [M.gQuad_eq]
  rw [M.Ric_eq_contract a b]
  rw [← Finset.mul_sum]; ring

/-- promote to a NormalCoordJet (so the τ/6 headline applies with the metric-derived Θ). -/
def toNormalCoordJet : NormalCoordJet n where
  Ric := M.Ric
  tau := M.tau
  tau_eq_trace := M.tau_eq_trace
  thetaQuad := M.thetaQuad
  thetaQuad_eq := M.thetaQuad_eq_neg_sixth_Ric

end MetricNormalCoordJet

/-! ## Part D — GROUNDING witness: the unit 2-sphere (τ = 2, so u₁(x,x) = 1/3)

`Ric a b = if a = b then 1 else 0` is `Ric = g` for the unit S², so
`tau = ∑ Ric a a = 2`, matching `QIQTH.CoordinateCurvature.SphereCheck.scalarCurvature_sphere = 2`. -/

/-- the normal-coordinate jet of the unit 2-sphere (`Ric = identity`, `τ = 2`). -/
noncomputable def sphereJet : NormalCoordJet 2 where
  Ric a b := if a = b then (1:ℝ) else 0
  tau := 2
  tau_eq_trace := by simp
  thetaQuad a b := -(1/6 : ℝ) * (if a = b then (1:ℝ) else 0)
  thetaQuad_eq a b := rfl

/-- the heat-transport jet of the unit 2-sphere. -/
noncomputable def sphereTransportWitness : HeatTransportJet 2 where
  jet := sphereJet
  u1diag := - geomLapQuadAtZero sphereJet.u0Quad
  transport_diag := rfl

-- τ = 2 here is our own `QIQTH.CoordinateCurvature.SphereCheck.scalarCurvature_sphere = 2`.
#check @QIQTH.CoordinateCurvature.SphereCheck.scalarCurvature_sphere

/-- the DeWitt diagonal coefficient of the unit 2-sphere is `1/3 = 2/6`. -/
theorem sphereTransportWitness_u1diag : sphereTransportWitness.u1diag = 1/3 := by
  have h := sphereTransportWitness.u1diag_eq_tau_div_six
  rw [h]
  norm_num [sphereTransportWitness, sphereJet]

end QIQTH.DeWittDiagonal
