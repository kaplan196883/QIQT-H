/-
  BasepointSmoothDep — base-point (starting-point) first-order smooth dependence of the geodesic
  flow on its initial condition.

  ODE_VARIATIONAL_PLAN.md, Phase J-b.  `GeodesicSmoothDep.geodesicVariation_exists` /
  `geodesicVariation_exists_uncond` prove that the IC-derivative of the geodesic flow EXISTS and
  equals a supplied Jacobi solution `V`, but they STATE the initial perturbation direction as the
  velocity-slot vector `(0, w)` — `hV0 : V 0 = (0, w)` and `hIC : Y s 0 − Y 0 0 = s·(0, w)`.

  KEY OBSERVATION (verified by re-reading the proofs): the `(0, w)` structure is NEVER used.  The
  only role of the direction in `geodesicVariation_exists` is the cancellation
  `Y s 0 − Y 0 0 − s·V 0 = s·(0,w) − s·(0,w) = 0` (used to seed the residual Grönwall), and in
  `geodesicVariation_hNb_discharge` it enters only through `dist(Y s 0)(Y 0 0) = |s|·‖(0,w)‖`.  Both
  work verbatim for an ARBITRARY perturbation direction `p : Point n × Point n`.  Hence the velocity-
  only *statement* is not a velocity-only *result*: generalising the direction to `p` and instantiating
  `p := (δq, 0)` gives base-point (position-slot) smooth dependence for free.

  WHAT LANDS HERE (all axiom-clean, no `sorry`; DERIVED, carrying only the SAME genuine geometric
  regularity inputs `GeodesicSmoothDep` already carries — `S` convex, the field's C² bound `‖∂²F‖ ≤ M₂`
  on `S`, the field Lipschitz on `S`, the Jacobi-coefficient bound `‖DF(Y 0 τ)‖ ≤ K`, tube containment
  `Y s τ ∈ S`, and the supplied Jacobi solution `V` — one *direction slot* over, NOT one order over):

  * `geodesicVariation_exists_dir` — the direction-generalised form of `geodesicVariation_exists`: for
    an arbitrary IC-perturbation direction `p`, the flow IC-derivative exists and equals `V t`,
    `HasDerivAt (fun s => Y s t) (V t) 0`, modulo the carried uniform quadratic field remainder `hNb`.
    (Re-proof of the L2a little-o assembly with `(0,w)` replaced by `p`.)

  * `geodesicVariation_hNb_discharge_dir` — the direction-generalised discharge of `hNb`: the uniform
    quadratic field remainder holds with `Cn = M₂·(‖p‖·e^{K₀})²` from the C² field remainder
    (`geodesicField_uniform_C2_remainder`) and the two-point Grönwall (`geodesic_twopoint_gronwall`).

  * `geodesicVariation_exists_uncond_dir` — the direction-generalised unconditional existence: combines
    the two, carrying only the genuine geometric regularity (no analytic `hNb`).

  * `geodesicBasepoint_flow_hasDerivAt` — **J-b.**  The base-point specialisation `p := (δq, 0)`: the
    directional derivative of the geodesic flow `s ↦ Y s t` with respect to a perturbation of the
    STARTING POINT (position slot) exists and equals the Jacobi field `V t`.  This is precisely the
    base-point 1st-order smooth-dependence that Mathlib's Picard–Lindelöf (Lipschitz-in-IC only) lacks.

  * `geodesicBasepoint_endpoint_position_hasDerivAt` — projecting onto the position component: the
    endpoint position `s ↦ (Y s t).1` has a base-point directional derivative `(V t).1` at `s = 0`.
    At `t = 1` this is the exp-map-shaped endpoint `q ↦ exp_q(v)` derivative in the base point `q`
    (for an abstract confined tube family; the concrete `expMap`'s `p`-dependence runs through opaque
    `Classical.choose` witnesses `expTube` and is not exposed at this level).

  HONEST CHECKPOINT (binding): this is base-point FIRST-order (J-b) directional smooth dependence for a
  one-parameter family `Y s` whose base point is perturbed linearly — the exact base-point analogue of
  L2a's velocity result, DERIVED (no new analytic input beyond the geometric regularity already carried
  by `geodesicVariation_exists_uncond`).  It does NOT assemble the directional derivatives into a full
  base-point Fréchet derivative (J-c), NOT the second-order base-point jet, NOT the joint (base,velocity)
  2-jet continuity input (J), NOT Raychaudhuri (L3), NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GeodesicSmoothDep
import QIQTH.ExpMap

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **J-b #1 (direction-generalised IC-derivative existence) — discharges L1's `hV` for an ARBITRARY
    perturbation direction `p`.**  Identical to `geodesicVariation_exists` but with the perturbation
    direction stated as an arbitrary `p : Point n × Point n` instead of the velocity-slot `(0, w)`:
    `hV0 : V 0 = p`, `hIC : Y s 0 − Y 0 0 = s·p`.  The `(0,w)` structure is never used in L2a's proof,
    so this is a verbatim re-proof.  Instantiating `p := (δq, 0)` gives the base-point case. -/
theorem geodesicVariation_exists_dir (g gi : Point n → Fin n → Fin n → ℝ)
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {p : Point n × Point n}
    {K Cn : ℝ} (hK0 : 0 ≤ K) (hCn0 : 0 ≤ Cn) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = p)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • p)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hNb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ)‖ ≤ Cn * s ^ 2) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  have hbnd : ∀ s : ℝ, ‖Y s t - Y 0 t - s • V t‖ ≤ Cn * s ^ 2 * Real.exp K := by
    intro s
    have hJ : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun σ => s • V σ)
          (fderiv ℝ (geodesicField g gi) (Y 0 τ) ((fun σ => s • V σ) τ)) τ := by
      intro τ hτ
      have hcs := (hVode τ hτ).const_smul s
      have he : s • fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)
          = fderiv ℝ (geodesicField g gi) (Y 0 τ) (s • V τ) :=
        (map_smul (fderiv ℝ (geodesicField g gi) (Y 0 τ)) s (V τ)).symm
      rw [he] at hcs
      exact hcs
    have h0 : Y s 0 - Y 0 0 - (fun σ => s • V σ) 0 = 0 := by
      simp only
      rw [hIC s, hV0]; abel
    have := geodesicVariation_residual_bound g gi hK0
      (mul_nonneg hCn0 (sq_nonneg s)) (hYode 0) (hYode s) hJ h0 hKb (hNb s) t ht
    simpa using this
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set M : ℝ := Cn * Real.exp K with hMdef
  have hM0 : 0 ≤ M := mul_nonneg hCn0 (Real.exp_pos K).le
  rw [Metric.eventually_nhds_iff]
  refine ⟨c / (M + 1), by positivity, fun s hs => ?_⟩
  rw [dist_eq_norm, sub_zero] at hs
  have hrw : Cn * s ^ 2 * Real.exp K = M * ‖s‖ ^ 2 := by
    rw [hMdef]; rw [Real.norm_eq_abs, sq_abs]; ring
  have hkey : ‖Y s t - Y 0 t - s • V t‖ ≤ M * ‖s‖ ^ 2 := hrw ▸ hbnd s
  have hMs : M * ‖s‖ ≤ c := by
    have hlt : ‖s‖ * (M + 1) < c := (lt_div_iff₀ (by positivity)).mp hs
    nlinarith [norm_nonneg s, hM0]
  calc ‖Y s t - Y 0 t - s • V t‖
      ≤ M * ‖s‖ ^ 2 := hkey
    _ = (M * ‖s‖) * ‖s‖ := by ring
    _ ≤ c * ‖s‖ := mul_le_mul_of_nonneg_right hMs (norm_nonneg _)

/-- **J-b #2 (direction-generalised discharge of `hNb`).**  The direction-generalised form of
    `geodesicVariation_hNb_discharge`: the uniform quadratic field remainder holds along the perturbed
    tube for an arbitrary direction `p`, with `Cn = M₂·(‖p‖·e^{K₀})²`, from the C² field remainder and
    the two-point Grönwall.  (`(0,w)` enters the original only via `‖(0,w)‖`; replaced by `‖p‖`.) -/
theorem geodesicVariation_hNb_discharge_dir (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {p : Point n × Point n} {S : Set (Point n × Point n)}
    {M₂ : ℝ} {K₀ : NNReal} (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • p)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ)‖
        ≤ (M₂ * (‖p‖ * Real.exp K₀) ^ 2) * s ^ 2 := by
  intro s τ hτ
  have htp := geodesic_twopoint_gronwall g gi hLip (hYode s) (hYode 0) (hmem s) (hmem 0) τ hτ
  have hd0 : dist (Y s 0) (Y 0 0) = |s| * ‖p‖ := by
    rw [dist_eq_norm, hIC s, norm_smul, Real.norm_eq_abs]
  have hexp : Real.exp ((K₀ : ℝ) * τ) ≤ Real.exp K₀ := by
    apply Real.exp_le_exp.mpr
    calc (K₀ : ℝ) * τ ≤ (K₀ : ℝ) * 1 := mul_le_mul_of_nonneg_left hτ.2 (NNReal.coe_nonneg K₀)
      _ = (K₀ : ℝ) := mul_one _
  have hLnn : 0 ≤ |s| * ‖p‖ * Real.exp K₀ := by positivity
  have hL : ‖Y s τ - Y 0 τ‖ ≤ |s| * ‖p‖ * Real.exp K₀ := by
    rw [← dist_eq_norm]
    calc dist (Y s τ) (Y 0 τ)
        ≤ dist (Y s 0) (Y 0 0) * Real.exp ((K₀ : ℝ) * τ) := htp
      _ = |s| * ‖p‖ * Real.exp ((K₀ : ℝ) * τ) := by rw [hd0]
      _ ≤ |s| * ‖p‖ * Real.exp K₀ :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have hrem := geodesicField_uniform_C2_remainder g gi hC hconv hbound2 (hmem s τ hτ) (hmem 0 τ hτ)
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ)))
      (hbound2 (Y 0 τ) (hmem 0 τ hτ))
  refine hrem.trans ?_
  have hsq : ‖Y s τ - Y 0 τ‖ ^ 2 ≤ (|s| * ‖p‖ * Real.exp K₀) ^ 2 := by
    have := mul_le_mul hL hL (norm_nonneg _) hLnn
    simpa [pow_two] using this
  calc M₂ * ‖Y s τ - Y 0 τ‖ ^ 2
      ≤ M₂ * (|s| * ‖p‖ * Real.exp K₀) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hnn
    _ = M₂ * (‖p‖ * Real.exp K₀) ^ 2 * s ^ 2 := by
        have hrw : (|s| * ‖p‖ * Real.exp K₀) ^ 2 = s ^ 2 * (‖p‖ * Real.exp K₀) ^ 2 := by
          rw [mul_assoc, mul_pow, sq_abs]
        rw [hrw]; ring

/-- **J-b #3 (direction-generalised unconditional IC-derivative existence).**  Combines
    `geodesicVariation_exists_dir` with `geodesicVariation_hNb_discharge_dir`, giving
    `HasDerivAt (fun s => Y s t) (V t) 0` for an arbitrary IC-perturbation direction `p`, carrying only
    the genuine geometric regularity — `S` convex, the field's C² bound on `S`, the field Lipschitz on
    `S`, the Jacobi-coefficient bound, tube containment, and the supplied Jacobi solution `V`. -/
theorem geodesicVariation_exists_uncond_dir (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {p : Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = p)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • p)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 t)))
      (hbound2 (Y 0 t) (hmem 0 t ht))
  have hCn0 : 0 ≤ M₂ * (‖p‖ * Real.exp K₀) ^ 2 := mul_nonneg hnn (sq_nonneg _)
  exact geodesicVariation_exists_dir g gi hK0 hCn0 ht hYode hVode hV0 hIC hKb
    (geodesicVariation_hNb_discharge_dir g gi hC hconv hbound2 hLip hYode hIC hmem)

/-- **J-b (capstone) — base-point first-order smooth dependence of the geodesic flow.**  The
    specialisation of `geodesicVariation_exists_uncond_dir` to the base-point (position-slot)
    perturbation direction `p := (δq, 0)`: for a one-parameter family `Y s` of geodesics whose STARTING
    POINT is perturbed linearly `Y s 0 − Y 0 0 = s·(δq, 0)` (fixed velocity), the directional derivative
    of the flow `s ↦ Y s t` with respect to the base point exists and equals the Jacobi field `V t`:
    `HasDerivAt (fun s => Y s t) (V t) 0`.

    This is the base-point analogue of `GeodesicSmoothDep.geodesicVariation_exists_uncond` (which does
    the velocity slot), the primitive Mathlib's Picard–Lindelöf lacks (it gives only Lipschitz — not
    differentiable — dependence on the initial condition).  DERIVED, carrying only genuine geometric
    regularity (`S` convex, C² field bound, field Lipschitz, Jacobi-coefficient bound, tube containment,
    supplied Jacobi solution) — NO analytic input beyond what the velocity result already carries. -/
theorem geodesicBasepoint_flow_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {δq : Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((δq, 0) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((δq, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => Y s t) (V t) 0 :=
  geodesicVariation_exists_uncond_dir g gi hC hK0 ht hconv hbound2 hLip hYode hVode hV0 hIC hKb hmem

/-- **J-b (endpoint position).**  Projecting the base-point flow derivative onto the position component:
    the endpoint position `s ↦ (Y s t).1` has a base-point directional derivative `(V t).1` at `s = 0`.
    At `t = 1` this is the exp-map-shaped geodesic-endpoint derivative in the base point (for an
    abstract confined tube family; the concrete `expMap`'s base-point dependence runs through opaque
    `Classical.choose` witnesses `expTube` and is not exposed here). -/
theorem geodesicBasepoint_endpoint_position_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {δq : Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((δq, 0) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((δq, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => (Y s t).1) ((V t).1) 0 := by
  have hflow : HasDerivAt (fun s => Y s t) (V t) 0 :=
    geodesicBasepoint_flow_hasDerivAt g gi hC hK0 ht hconv hbound2 hLip hYode hVode hV0 hIC hKb hmem
  have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hflow
  simpa [Function.comp] using this

end QIQTH.ExpMap
