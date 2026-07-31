/-
  FlowVelocitySecondJet — J4-31: discharging the flow-side operator q-Lipschitz bound `hFoplip` of the
  velocity SECOND jet, and thereby REDUCING `hunif`/`(J)` to the concrete second-order velocity Jacobi
  jet data (identification + two-point endpoint bound), with the opaque-tube firewall already dissolved
  by J4-30.

  ## Context

  `BasepointJetLipschitz` (J4-30) dissolved the opaque-`expTube` firewall: it welded the exp velocity
  2-jet onto a CONCRETE uniform-confinement geodesic-flow endpoint family `F` (`F_q w = (Y_{q,w} 1).1`,
  a genuine `(-2,2)` integral curve of `geodesicField`) via
  `fderiv2_expMap_eq_uniform_flow_on_overlap`, and REDUCED `(J)` to the SINGLE flow-side operator
  q-Lipschitz bound

    `hFoplip : ‖fderiv²(F_q) v − fderiv²(F_{q'}) v‖ ≤ Λ·dist(q,q')`   uniform over `v ∈ B̄(0,r)`,

  via `expMap_second_jet_hunif_of_flow_op_lipschitz`.

  `F_q : Point n → Point n` maps the initial VELOCITY `w` to the geodesic ENDPOINT position, so its
  velocity 2-jet `fderiv ℝ (fun w => fderiv ℝ F_q w) v : Point n →L[ℝ] Point n →L[ℝ] Point n` is a
  BILINEAR object.  Its value on a direction pair `(a,b)` is the endpoint of the second-order velocity
  Jacobi field for the geodesic through `(q,v)` in the seeded directions `(a,b)` — the velocity-slot,
  second-derivative analogue of the base-point first jet `V δ t` (`BasepointFDeriv`).  The direction-
  agnostic second-order variation machinery already exists (`jacobiVariation_secondOrder` /
  `BasepointJacobi2.jacobiVariation_secondOrder_basepoint` — the ODE `ξ'' = −jacobiOperator`), and the
  two-point (`q` vs `q'`) difference engine is `linODE_twopoint_diff_bound` (`BasepointJetModulus`).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `opNorm_sub_le_of_bilinear_bound` — **(the pure-analysis bilinear operator-norm packaging engine).**
    For two "bilinear-shaped" continuous-linear maps `A, B : E →L[ℝ] E' →L[ℝ] E''` whose VALUES obey a
    pointwise bilinear bound `‖A a b − B a b‖ ≤ c·‖a‖·‖b‖`, the operator norm of the difference obeys
    `‖A − B‖ ≤ c`.  Two nested `ContinuousLinearMap.opNorm_le_bound`.  Reusable, geometry-free.  This is
    what turns the vector-level (`Point n`-valued) two-point jet bound into the OPERATOR bound `hFoplip`.

  * `flowVelocity_secondJet_endpoint_twopoint_bound` — **(the inhomogeneous second-order velocity
    two-point ODE engine).**  For two second-order velocity jet fields `Z₁, Z₂` solving the INHOMOGENEOUS
    linearized geodesic ODE `Z' = DF(Y)·Z + Source` along two base geodesics `Y₁, Y₂` with the SAME seed,
    the endpoint difference is `‖Z₁ 1 − Z₂ 1‖ ≤ (Dcoef·Xb + Dsrc)·exp K`, where `Dcoef` bounds the
    base-curve coefficient separation `‖DF(Y₁) − DF(Y₂)‖`, `Xb` bounds `‖Z₂‖`, and `Dsrc` bounds the
    source separation `‖Source₁ − Source₂‖`.  A direct endpoint (`t=1`) specialization of
    `linODE_twopoint_diff_bound` (the source-carrying, second-order analogue of `jacobi_twopoint_diff_bound`).
    This is the ODE route that produces the two-point endpoint bound `hbnd` fed below (the bilinear
    `‖a‖·‖b‖` scaling arises from the bilinearity of the seed `(a,b)` in `Z`).

  * `flowVelocity_secondJet_op_lipschitz_of_jet_data` — **(the discharge of `hFoplip`).**  Given a
    supplied second-order velocity jet field `Z : Point n → Point n → Point n → Point n → ℝ → Point n`
    (`Z q v a b : ℝ → Point n`) with
      (i) the IDENTIFICATION `fderiv²(Fam q) v a b = Z q v a b 1` (`hid` — the second-order variational-
          equation identification, the velocity-slot analogue of `V δ t`), and
      (ii) the vector-level two-point endpoint bound
          `‖Z q v a b 1 − Z q' v a b 1‖ ≤ Λ·dist(q,q')·‖a‖·‖b‖` (`hbnd` — produced by the ODE engine
          above with bilinearly-scaled `Dcoef,Xb,Dsrc` and the uniform `BoundedGeometry` constants),
    the operator q-Lipschitz bound `hFoplip` holds.  DERIVED via `opNorm_sub_le_of_bilinear_bound`.

  * `expMap_second_jet_hunif_of_velocity_jet_data`,
    `expMap_common_nondeg_radius_of_velocity_jet_data` — **(the `(J)` reduction capstones).**  Chaining
    the discharged `hFoplip` through `BasepointJetLipschitz.expMap_second_jet_hunif_of_flow_op_lipschitz`
    (with the concrete exp↔flow 2nd-jet weld `hweld`) delivers `hunif`, and thence — through
    `BasepointSecondJet.expMap_common_nondeg_radius_of_base_uniform` — the UNCONDITIONAL common
    exp-nondegeneracy radius over `K`.  So `(J)` is reduced, with NO opaque tube and NO smuggled
    `hFoplip`/`hunif`, to the concrete second-order velocity Jacobi jet data (`hid` + `hbnd` + the weld).

  DERIVED vs CARRIED.  DERIVED = the bilinear operator-norm packaging, the inhomogeneous second-order
  two-point ODE engine (from `linODE_twopoint_diff_bound`), the `hFoplip` discharge, and the reduction
  chaining.  CARRIED genuine inputs (the honest velocity-slot analogue of the supplied first-order Jacobi
  field `V`, NOT the conclusion, NOT `hFoplip`, NOT `hunif`):
    * `hid` — the second-order velocity jet field `Z q v a b` and its identification with the flow-endpoint
      velocity 2-jet (the second-order variational-equation identification);
    * `hbnd` — the two-point endpoint bound of that field (an ODE-derived regularity fact, derivable via
      `flowVelocity_secondJet_endpoint_twopoint_bound` + `BoundedGeometry` uniform constants);
    * the concrete exp↔flow 2nd-jet weld `hweld` (delivered by `fderiv2_expMap_eq_uniform_flow_on_overlap`
      for `r` inside the overlap radius) and the `(I1)` uniform injectivity radius `hr_lt`.
  `hFoplip` is DERIVED (not carried); `hunif` and the common radius are DERIVED (not carried).

  HONEST CHECKPOINT (binding).  This DISCHARGES `hFoplip` from the concrete jet data (`hid`+`hbnd`) and
  REDUCES `(J)` / the unconditional common exp-nondegeneracy radius over `K` to that jet data plus the
  (already-DERIVED-elsewhere) weld and `(I1)` radius — the remaining genuine input is the second-order
  velocity Jacobi jet field `Z` with its variational-equation identification `hid` and ODE-derived
  two-point bound `hbnd`.  It does NOT build the covariant `D²/dτ²`, NOT Raychaudhuri (L3), NOT
  `a₁ = R/6`.
-/
import QIQTH.BasepointJetLipschitz
import QIQTH.BasepointJetModulus
import QIQTH.BasepointJacobi2
import QIQTH.BasepointFDeriv
import QIQTH.UniformFlowBridge
import QIQTH.BoundedGeometry
import QIQTH.BoundedGeometryConfine
import QIQTH.JacobiEquation
import QIQTH.BasepointSecondJet
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **The pure-analysis bilinear operator-norm packaging engine.**  Let `A, B : E →L[ℝ] E' →L[ℝ] E''`
    be two "bilinear-shaped" continuous-linear maps whose VALUES obey a pointwise bilinear bound
    `‖A a b − B a b‖ ≤ c·‖a‖·‖b‖` (with `c ≥ 0`).  Then the operator norm of the difference obeys
    `‖A − B‖ ≤ c`.  Proof: two nested `ContinuousLinearMap.opNorm_le_bound` — the outer with bound
    `c·‖a‖` on `‖(A − B) a‖`, the inner with bound `c·‖a‖·‖b‖` on `‖(A − B) a b‖`, unfolding the
    subtraction through `ContinuousLinearMap.sub_apply`.  Geometry-free, reusable: this converts the
    vector-level two-point jet bound into the OPERATOR q-Lipschitz bound `hFoplip`. -/
theorem opNorm_sub_le_of_bilinear_bound {E E' E'' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    (A B : E →L[ℝ] E' →L[ℝ] E'') {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a b, ‖A a b - B a b‖ ≤ c * ‖a‖ * ‖b‖) :
    ‖A - B‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc (fun a => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun b => ?_)
  have hval : ((A - B) a) b = A a b - B a b := by
    simp only [ContinuousLinearMap.sub_apply]
  rw [hval]
  exact h a b

/-- **The inhomogeneous second-order velocity two-point ODE engine (endpoint form).**  Let `Z₁, Z₂` be
    two second-order velocity jet fields solving the INHOMOGENEOUS linearized geodesic ODE
    `Z' = DF(Y)·Z + Source` along two base geodesics `Y₁, Y₂` (respectively) on `[0,1]`, with the SAME
    seed `Z₁ 0 = Z₂ 0`.  If the first coefficient is bounded `‖DF(Y₁ τ)‖ ≤ K`, the two coefficients
    differ by `‖DF(Y₁ τ) − DF(Y₂ τ)‖ ≤ Dcoef`, the second solution is bounded `‖Z₂ τ‖ ≤ Xb`, and the
    sources differ by `‖S₁ τ − S₂ τ‖ ≤ Dsrc`, then the endpoint difference obeys
        `‖Z₁ 1 − Z₂ 1‖ ≤ (Dcoef·Xb + Dsrc)·exp K`.

    A direct endpoint (`t = 1`) specialization of `linODE_twopoint_diff_bound` with the geodesic-field
    Jacobi coefficient `A_i = DF(Y_i)` and the curvature source `b_i = S_i`.  This is the source-carrying
    (second-order) analogue of `jacobi_twopoint_diff_bound`; the bilinear `‖a‖·‖b‖` scaling of the
    resulting bound arises from the bilinearity of the seed `(a,b)` in the jet field, and the constants
    `K, Dcoef, Xb, Dsrc` are uniform over a compact `K` via `BoundedGeometry`. -/
theorem flowVelocity_secondJet_endpoint_twopoint_bound (g gi : Point n → Fin n → Fin n → ℝ)
    {Y₁ Y₂ Z₁ Z₂ S₁ S₂ : ℝ → Point n × Point n} {K Dcoef Xb Dsrc : ℝ} (hK0 : 0 ≤ K)
    (hZ1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Z₁ (fderiv ℝ (geodesicField g gi) (Y₁ τ) (Z₁ τ) + S₁ τ) τ)
    (hZ2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Z₂ (fderiv ℝ (geodesicField g gi) (Y₂ τ) (Z₂ τ) + S₂ τ) τ)
    (h0 : Z₁ 0 = Z₂ 0)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y₁ τ)‖ ≤ K)
    (hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y₁ τ) - fderiv ℝ (geodesicField g gi) (Y₂ τ)‖ ≤ Dcoef)
    (hXb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Z₂ τ‖ ≤ Xb)
    (hSd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖S₁ τ - S₂ τ‖ ≤ Dsrc) :
    ‖Z₁ 1 - Z₂ 1‖ ≤ (Dcoef * Xb + Dsrc) * Real.exp K :=
  linODE_twopoint_diff_bound (E := Point n × Point n)
    (A₁ := fun τ => fderiv ℝ (geodesicField g gi) (Y₁ τ))
    (A₂ := fun τ => fderiv ℝ (geodesicField g gi) (Y₂ τ))
    (X₁ := Z₁) (X₂ := Z₂) (b₁ := S₁) (b₂ := S₂)
    (K := K) (Dcoef := Dcoef) (Xb := Xb) (Dsrc := Dsrc) hK0
    hZ1 hZ2 h0 hKb hAd hXb hSd 1 (Set.right_mem_Icc.mpr zero_le_one)

/-- **The discharge of `hFoplip` from the second-order velocity jet data.**  Given a supplied second-order
    velocity jet field `Z : Point n → Point n → Point n → Point n → ℝ → Point n` (`Z q v a b : ℝ → Point n`)
    for the concrete flow-endpoint family `Fam` with
      (i)  the IDENTIFICATION `fderiv²(Fam q) v a b = Z q v a b 1` for `q ∈ K`, `v ∈ B̄(0,r)`, all
           direction pairs `(a,b)` (`hid` — the velocity-slot second-order variational-equation
           identification), and
      (ii) the vector-level two-point endpoint bound
           `‖Z q v a b 1 − Z q' v a b 1‖ ≤ Λ·dist(q,q')·‖a‖·‖b‖` (`hbnd`),
    the flow-side OPERATOR q-Lipschitz bound `hFoplip` holds:
        `‖fderiv²(Fam q) v − fderiv²(Fam q') v‖ ≤ Λ·dist(q,q')`.
    DERIVED by `opNorm_sub_le_of_bilinear_bound` (with `c := Λ·dist(q,q')`), rewriting the bilinear values
    through the identification.  The carried genuine input is the jet field `Z` (identification `hid` +
    two-point bound `hbnd`), NOT `hFoplip`. -/
theorem flowVelocity_secondJet_op_lipschitz_of_jet_data
    {K : Set (Point n)} {r Λ : ℝ} (hΛ : 0 ≤ Λ)
    (Fam : Point n → Point n → Point n)
    (Z : Point n → Point n → Point n → Point n → ℝ → Point n)
    (hid : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      (fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v) a b = Z q v a b 1)
    (hbnd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ‖Z q v a b 1 - Z q' v a b 1‖ ≤ Λ * dist q q' * ‖a‖ * ‖b‖) :
    ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      ‖fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v
        - fderiv ℝ (fun w => fderiv ℝ (Fam q') w) v‖ ≤ Λ * dist q q' := by
  intro q hq q' hq' v hv
  refine opNorm_sub_le_of_bilinear_bound _ _ (mul_nonneg hΛ dist_nonneg) (fun a b => ?_)
  rw [hid q hq v hv a b, hid q' hq' v hv a b]
  exact hbnd q hq q' hq' v hv a b

/-- **`(J)` reduction capstone — `hunif` from the second-order velocity jet data.**  Given the concrete
    exp↔flow 2nd-jet weld `hweld` (delivered by `fderiv2_expMap_eq_uniform_flow_on_overlap` for `r`
    inside the overlap radius) and the second-order velocity jet data (`hid` + `hbnd`), the base-point
    uniform modulus `hunif` — the exact residual input of `BasepointSecondJet` — holds.  DERIVED by
    discharging `hFoplip` (`flowVelocity_secondJet_op_lipschitz_of_jet_data`) and chaining it through
    `expMap_second_jet_hunif_of_flow_op_lipschitz`.  No opaque tube, no smuggled `hFoplip`/`hunif`. -/
theorem expMap_second_jet_hunif_of_velocity_jet_data (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} {r Λ : ℝ} (hΛ : 0 ≤ Λ)
    (Fam : Point n → Point n → Point n)
    (Z : Point n → Point n → Point n → Point n → ℝ → Point n)
    (hweld : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v
        = fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v)
    (hid : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      (fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v) a b = Z q v a b 1)
    (hbnd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ‖Z q v a b 1 - Z q' v a b 1‖ ≤ Λ * dist q q' * ‖a‖ * ‖b‖) :
    ∀ ε > 0, ∃ δ > 0, ∀ q ∈ K, ∀ q' ∈ K, dist q q' < δ →
        ∀ v ∈ Metric.closedBall (0 : Point n) r,
          |‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖
            - ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q') w) v‖| ≤ ε :=
  expMap_second_jet_hunif_of_flow_op_lipschitz g gi hC hΛ Fam hweld
    (flowVelocity_secondJet_op_lipschitz_of_jet_data hΛ Fam Z hid hbnd)

/-- **`(J)` reduction capstone — the UNCONDITIONAL common exp-nondegeneracy radius over `K` from the
    second-order velocity jet data.**  With the `(I1)` uniform injectivity radius `hr_lt`
    (`r < expRho g gi hC q` for `q ∈ K`), the concrete exp↔flow 2nd-jet weld `hweld`, and the
    second-order velocity jet data (`hid` + `hbnd`), there is a single `ρ₀ > 0` with
    `IsUnit (fderiv ℝ (expMap g gi hC q) v)` for all `q ∈ K`, `‖v‖ < ρ₀`.  DERIVED by feeding the
    reduced `hunif` (`expMap_second_jet_hunif_of_velocity_jet_data`) into
    `BasepointSecondJet.expMap_common_nondeg_radius_of_base_uniform`.  This is the `(J)` payload, reduced
    with NO opaque tube and NO smuggled `hFoplip`/`hunif` — the remaining genuine input is the concrete
    second-order velocity Jacobi jet field `Z` (identification `hid` + two-point bound `hbnd`) plus the
    weld and the `(I1)` radius. -/
theorem expMap_common_nondeg_radius_of_velocity_jet_data (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {r Λ : ℝ} (hr : 0 < r) (hΛ : 0 ≤ Λ)
    (hr_lt : ∀ q ∈ K, r < expRho g gi hC q)
    (Fam : Point n → Point n → Point n)
    (Z : Point n → Point n → Point n → Point n → ℝ → Point n)
    (hweld : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v
        = fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v)
    (hid : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      (fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v) a b = Z q v a b 1)
    (hbnd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ‖Z q v a b 1 - Z q' v a b 1‖ ≤ Λ * dist q q' * ‖a‖ * ‖b‖) :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (expMap g gi hC q) v) :=
  expMap_common_nondeg_radius_of_base_uniform g gi hC hK r hr hr_lt
    (expMap_second_jet_hunif_of_velocity_jet_data g gi hC hΛ Fam Z hweld hid hbnd)

end QIQTH.ExpMap
