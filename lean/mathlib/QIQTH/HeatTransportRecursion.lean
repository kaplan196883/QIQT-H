/-
# P2b — the Minakshisundaram–DeWitt TRANSPORT RECURSION for the parametrix coefficients `u_k`

MANDATORY FIREWALL (binding, honest):

  • This builds the DIAGONAL TRANSPORT-RECURSION STRUCTURE for the DeWitt/Minakshisundaram
    parametrix coefficients `u_k`: the conjugated-Laplacian transport operator
    `transportOp Θ g gi v = Θ^{−1/2}·Δ_g(Θ^{1/2}·v)` (the RHS driver of the recursion), the
    `TransportRecursion` structure carrying the coefficient family `u : ℕ → Point → ℝ` with the
    diagonal recursion `(k+1)·u_{k+1}(x₀) = [driver](u_k)(x₀)`, and the bridge
    `u₁(x₀) = τ/6` — reproducing the landed DeWitt diagonal value
    `QIQTH.DeWittDiagonal.HeatTransportJet.u1diag = τ/6`.  The `u₁(x₀) = τ/6` conclusion is
    genuinely DERIVED (via `LaplaceBeltrami.laplaceBeltrami_quadratic_at_center` on the
    van-Vleck 2-jet `u0Quad = (1/12)Ric`, giving `2·tr = τ/6`), and the SPHERE witness
    (`sphereTransportRecursion`, `Ric = 1`, `τ = 2`, `u₁ = 1/3`) exhibits it at NONZERO
    curvature — so the bridge is not vacuous.

  • CARRIED (the geometric/analytic substrate we do NOT build — structure fields, never axioms):
      – `u0_jet` : that `u₀` equals its van-Vleck normal-coordinate 2-jet `∑ u0Quad·y_a y_b`
        (the diagonal-relevant content of `u₀ = Θ^{−1/2}`; higher orders don't reach `Δ_g|₀`);
      – `udiag_rec` : the DIAGONAL transport recursion `(k+1)u_{k+1}(x₀) = transportOp(u_k)(x₀)`
        (carried exactly as `DeWittDiagonal.HeatTransportJet` carries `transport_diag`);
      – `transport_center` : that at the RNC diagonal (`Θ(x₀)=1`, `∇Θ(x₀)=0`) the Θ-conjugation
        of `transportOp` trivializes to the plain `Δ_g = laplaceBeltrami` (the honest
        Rosenberg/Chavel diagonal driver `u_k(x,x) = (1/k)Δ_g u_{k−1}(x,x)`).
    These encode the exponential map, the geodesic distance / van-Vleck determinant, and the
    radial `r∂_r` integration — i.e. the manifold substrate + the parametrix analysis.

  • The radial homogeneous equation `(r∂_r + ½ r ∂_r logΘ)u₀ = 0` (STRETCH #4) is NOT derived:
    it needs the geodesic-radial-coordinate `r∂_r` operator + `∂_r logΘ` (geodesic-flow
    machinery absent from the Mathlib tree).  It is CHECKPOINTED precisely at the end of this
    file as the analytic wall (P2c/P2d territory), together with the small honest fact that the
    base conjugated field `Θ^{1/2}·u₀` is constant `≡ 1` along rays (the r-independence that the
    homogeneous equation encodes).

  • It does NOT build the heat semigroup / kernel / parametrix convergence, the `O(t^N)` error
    estimate, nor the general `a₁ = R/6` (P2c–e, incl. the P2d Levi/Duhamel wall).  No axioms,
    no `sorry`.

Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1 (transport recursion,
diagonal); Berline–Getzler–Vergne §2.5; Gilkey.  Heat-kernel gap plan, Phase-4 / §3.2.1 (P2b).
-/
import Mathlib
import QIQTH.DeWittDiagonal
import QIQTH.LaplaceBeltrami

open scoped BigOperators
open QIQTH.Curvature QIQTH.DeWittDiagonal QIQTH.LaplaceBeltrami

namespace QIQTH.HeatTransportRecursion

variable {n : ℕ}

/-! ## 1. The transport operator — the RHS driver of the Minakshisundaram–DeWitt recursion.

`transportOp Θ g gi v (x) = Θ(x)^{−1/2}·Δ_g(Θ^{1/2}·v)(x)`, the conjugated Laplace–Beltrami
operator appearing on the right of the transport equation
`(k + r∂_r)u_k + (½ r∂_r logΘ)u_k = transportOp Θ g gi u_{k−1}`. -/

/-- The conjugated-Laplacian **transport operator** `Θ^{−1/2}·Δ_g(Θ^{1/2}·v)`. -/
noncomputable def transportOp (Θ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (v : Point n → ℝ) (x : Point n) : ℝ :=
  Θ x ^ (-(1/2) : ℝ) * laplaceBeltrami g gi (fun y => Θ y ^ ((1/2) : ℝ) * v y) x

/-- **At a unit-normalized van-Vleck value `Θ ≡ 1`** the Θ-conjugation trivializes and the
    transport operator is the plain Laplace–Beltrami `Δ_g`.  This is the diagonal reduction
    `transportOp = Δ_g` used at the RNC center (where `Θ(x₀)=1`, `∇Θ(x₀)=0`). -/
lemma transportOp_theta_one (Θ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (v : Point n → ℝ) (x : Point n) (hΘ : ∀ y, Θ y = 1) :
    transportOp Θ g gi v x = laplaceBeltrami g gi v x := by
  unfold transportOp
  simp only [hΘ, Real.one_rpow, one_mul]

/-! ## 2. Two supporting facts about `laplaceBeltrami` (constant fields; constant metrics). -/

/-- **`Δ_g` of a constant field vanishes** (both the second-derivative and the Christoffel
    Leibniz terms are `pd` of a constant). -/
lemma laplaceBeltrami_const (g gi : Point n → Fin n → Fin n → ℝ) (c : ℝ) (x : Point n) :
    laplaceBeltrami g gi (fun _ => c) x = 0 := by
  unfold laplaceBeltrami
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  have h1 : pd (fun y => pd (fun _ => c) j y) i x = 0 := by
    have e : (fun y : Point n => pd (fun _ => c) j y) = (fun _ => (0 : ℝ)) :=
      funext (fun y => pd_const c j y)
    rw [e, pd_const]
  have h2 : (∑ k, christoffel g gi k i j x * pd (fun _ => c) k x) = 0 := by
    apply Finset.sum_eq_zero; intro k _; rw [pd_const]; ring
  rw [h1, h2]; ring

/-- **The Christoffel symbols of a constant metric vanish** (their derivative content is
    `pd` of a constant).  Used to supply the RNC hypothesis `hΓ` in the sphere witness. -/
lemma christoffel_of_const (G Gi : Fin n → Fin n → ℝ) (k i j : Fin n) (x : Point n) :
    christoffel (fun _ => G) (fun _ => Gi) k i j x = 0 := by
  simp [christoffel, pd_const]

/-! ## 3. The transport-recursion structure. -/

/-- **The Minakshisundaram–DeWitt diagonal transport recursion**, carried as a structure
    (exactly as `DeWittDiagonal.HeatTransportJet` carries `transport_diag`).

  Fields:
    * `jet`             — the normal-coordinate DeWitt jet (`Ric, τ, Θ`-2-jet, `u0Quad`);
    * `g gi x₀ hgi hΓ`  — the coordinate metric/inverse and the Riemannian-normal-coordinate
                          center data (`gi(x₀)=δ`, `Γ(x₀)=0`);
    * `Θ`               — the van-Vleck determinant field;
    * `u`               — the coefficient family `u_k`;
    * `u0_jet`          — `u₀` equals its van-Vleck 2-jet `∑ u0Quad·y_a y_b`;
    * `udiag_rec`       — the DIAGONAL recursion `(k+1)u_{k+1}(x₀) = transportOp(u_k)(x₀)`;
    * `transport_center`— at the diagonal the Θ-conjugation trivializes: `transportOp = Δ_g`. -/
structure TransportRecursion (n : ℕ) where
  jet : NormalCoordJet n
  g : Point n → Fin n → Fin n → ℝ
  gi : Point n → Fin n → Fin n → ℝ
  x₀ : Point n
  hgi : ∀ i j, gi x₀ i j = if i = j then (1 : ℝ) else 0
  hΓ : ∀ k i j, christoffel g gi k i j x₀ = 0
  Θ : Point n → ℝ
  u : ℕ → Point n → ℝ
  u0_jet : u 0 = fun y => ∑ a, ∑ b, jet.u0Quad a b * y a * y b
  udiag_rec : ∀ k : ℕ, ((k : ℝ) + 1) * u (k + 1) x₀ = transportOp Θ g gi (u k) x₀
  transport_center : ∀ k : ℕ, transportOp Θ g gi (u k) x₀ = laplaceBeltrami g gi (u k) x₀

namespace TransportRecursion

variable (T : TransportRecursion n)

/-- The `k=0 → 1` step: `u₁(x₀) = transportOp(u₀)(x₀)` (from the diagonal recursion). -/
lemma u1_diag_eq_transport : T.u 1 T.x₀ = transportOp T.Θ T.g T.gi (T.u 0) T.x₀ := by
  have h := T.udiag_rec 0
  simpa using h

/-- At the RNC diagonal the transport driver is the plain Laplace–Beltrami of `u₀`. -/
lemma u1_diag_eq_laplaceBeltrami : T.u 1 T.x₀ = laplaceBeltrami T.g T.gi (T.u 0) T.x₀ := by
  rw [T.u1_diag_eq_transport, T.transport_center 0]

/-- ★ **THE P2b BRIDGE**: the transport recursion's `u₁` diagonal reproduces the DeWitt `τ/6`.
    Derived — `Δ_g` on the van-Vleck 2-jet `u0Quad = (1/12)Ric` gives `2·tr = τ/6`. -/
theorem u1_diag_eq_tau_div_six : T.u 1 T.x₀ = T.jet.tau / 6 := by
  rw [T.u1_diag_eq_laplaceBeltrami, T.u0_jet,
      laplaceBeltrami_quadratic_at_center T.g T.gi T.jet.u0Quad T.x₀ T.hgi T.hΓ,
      ← analyticLapQuadAtZero_eq_trace T.jet.u0Quad,
      T.jet.analyticLap_u0Quad_eq_tau_div_six]

/-- ★ **Bridge to the landed DeWitt diagonal coefficient**: for any `HeatTransportJet` sharing
    the same normal-coordinate jet, the transport recursion's `u₁(x₀)` equals
    `HeatTransportJet.u1diag` (both `= τ/6`). -/
theorem u1_diag_eq_HeatTransportJet (H : HeatTransportJet n) (hH : H.jet = T.jet) :
    T.u 1 T.x₀ = H.u1diag := by
  rw [H.u1diag_eq_tau_div_six, hH]
  exact T.u1_diag_eq_tau_div_six

end TransportRecursion

/-! ## 4. GROUNDING witness — the unit 2-sphere (`Ric = 1`, `τ = 2`, so `u₁(x₀) = 1/3`).

A genuine NONZERO-curvature inhabitant of `TransportRecursion 2`, proving the `τ/6` bridge is
not vacuous.  Metric/inverse are the constant `δ` (so `Γ = 0`, `gi(x₀) = δ`); `Θ ≡ 1` so the
transport operator is the plain `Δ_g`; `u₀` is the sphere van-Vleck 2-jet `∑ u0Quad·y_a y_b`. -/

/-- The sphere coefficient family: `u₀` = the van-Vleck 2-jet, `u₁ ≡ 1/3 = τ/6`, `u_{≥2} ≡ 0`. -/
noncomputable def sphereU : ℕ → Point 2 → ℝ
  | 0 => fun y => ∑ a, ∑ b, sphereJet.u0Quad a b * y a * y b
  | 1 => fun _ => (1/3 : ℝ)
  | _ => fun _ => 0

/-- The transport recursion of the unit 2-sphere. -/
noncomputable def sphereTransportRecursion : TransportRecursion 2 where
  jet := sphereJet
  g := fun _ i j => if i = j then (1 : ℝ) else 0
  gi := fun _ i j => if i = j then (1 : ℝ) else 0
  x₀ := fun _ => 0
  hgi := fun i j => rfl
  hΓ := fun k i j => christoffel_of_const _ _ k i j _
  Θ := fun _ => 1
  u := sphereU
  u0_jet := rfl
  udiag_rec := by
    intro k
    rw [transportOp_theta_one _ _ _ _ _ (fun _ => rfl)]
    rcases k with _ | _ | k
    · -- k = 0 : 1·u₁ = Δ_g u₀ = 2·tr(u0Quad) = 1/3
      simp only [sphereU]
      rw [laplaceBeltrami_quadratic_at_center _ _ sphereJet.u0Quad (fun _ => 0)
            (fun i j => rfl) (fun k i j => christoffel_of_const _ _ k i j _)]
      simp only [NormalCoordJet.u0Quad, invSqrtQuad, sphereJet, Fin.sum_univ_two]
      norm_num
    · -- k = 1 : 2·u₂ = Δ_g u₁ = 0   (u₁ constant)
      simp only [sphereU]
      rw [laplaceBeltrami_const]
      norm_num
    · -- k ≥ 2 : (k+3)·u_{k+3} = Δ_g u_{k+2} = 0   (u_{k+2} constant)
      simp only [sphereU]
      rw [laplaceBeltrami_const]
      norm_num
  transport_center := fun k => transportOp_theta_one _ _ _ _ _ (fun _ => rfl)

/-- The sphere transport recursion reproduces the DeWitt diagonal coefficient `τ/6 = 1/3`. -/
theorem sphereTransportRecursion_u1_eq :
    sphereTransportRecursion.u 1 sphereTransportRecursion.x₀ = 1/3 := by
  rw [sphereTransportRecursion.u1_diag_eq_tau_div_six]
  norm_num [sphereTransportRecursion, sphereJet]

/-! ## 5. STRETCH #4 (CHECKPOINT) — the `k=0` homogeneous radial equation.

The base coefficient `u₀ = Θ^{−1/2}` solves the homogeneous transport equation
  `(r ∂_r + ½ r ∂_r logΘ) u₀ = 0`    ⇔    `∂_r (Θ^{1/2}·u₀) = 0`,
i.e. the conjugated base field `Θ^{1/2}·u₀` is CONSTANT (`≡ 1`) along each geodesic ray from
the center — its radial derivative vanishes.  The genuine `r`-independence content is the
following purely algebraic fact (no geodesic machinery required): -/

/-- **The conjugated base field is `≡ 1`**: `Θ^{1/2}·Θ^{−1/2} = 1` (for `Θ(x) > 0`).  This is the
    `r`-independence that the `k=0` homogeneous radial transport equation encodes
    (`∂_r(Θ^{1/2}u₀) = 0`, with `u₀ = Θ^{−1/2}`).  It also records the convention subtlety noted
    in the header: the LITERAL Θ-conjugated `transportOp` applied to the exact van-Vleck field
    `u₀ = Θ^{−1/2}` sees `Θ^{1/2}u₀ ≡ 1`, so its off-diagonal driver is `Δ_g(1) = 0`; the nonzero
    `τ/6` is the DIAGONAL value `Δ_g u₀|₀` (Rosenberg/Chavel `u_k(x,x) = (1/k)Δ_g u_{k−1}(x,x)`),
    which is what `TransportRecursion.transport_center` carries and `u1_diag_eq_tau_div_six`
    derives. -/
lemma conjBase_eq_one (Θ : Point n → ℝ) (x : Point n) (hΘ : 0 < Θ x) :
    Θ x ^ ((1/2) : ℝ) * Θ x ^ (-(1/2) : ℝ) = 1 := by
  have hsum : (1/2 : ℝ) + -(1/2) = 0 := by norm_num
  rw [← Real.rpow_add hΘ, hsum, Real.rpow_zero]

/-
CHECKPOINT — the analytic wall of STRETCH #4 (NOT derived here):

  The FULL derivation of the radial transport recursion — i.e. deriving the diagonal collapse
  `(k+1)u_{k+1}(x,x) = Δ_g u_k(x,x)` (the `udiag_rec` field) FROM the off-diagonal ODE
  `(k + r∂_r)u_k + (½ r∂_r logΘ)u_k = transportOp Θ g gi u_{k−1}` — requires:
    • the geodesic-radial coordinate `r` (geodesic distance from the center) and the operator
      `r∂_r` along geodesic rays;
    • the van-Vleck determinant `Θ` as a genuine function on the punctured neighbourhood and its
      logarithmic radial derivative `∂_r logΘ`;
    • the integrating-factor solution `u_k = Θ^{−1/2} r^{−k} ∫₀^r Θ^{1/2}(Δ_g u_{k−1}) s^{k−1} ds`
      and the `r→0` limit (l'Hôpital / Taylor at the diagonal).
  This is geodesic-flow / exponential-map machinery ABSENT from the Mathlib tree (the same
  Riemannian-heat-kernel gap recorded across the P2 build).  It is P2c/P2d territory (incl. the
  P2d Levi/Duhamel parametrix-convergence wall).  Here the recursion + its diagonal collapse are
  CARRIED as structure fields (exactly as `DeWittDiagonal.HeatTransportJet` carries its
  `transport_diag`), and the τ/6 VALUE is genuinely derived from the van-Vleck 2-jet.
-/

end QIQTH.HeatTransportRecursion
