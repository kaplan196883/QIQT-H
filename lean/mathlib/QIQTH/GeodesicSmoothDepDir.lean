/-
  GeodesicSmoothDepDir — smooth dependence of the geodesic flow on its initial condition in an
  ARBITRARY perturbation direction `ξ : Point n × Point n`, in particular the BASE-POINT (position)
  slot `ξ = (u, 0)`.

  MOTIVATION (J4-824 terminal-wall analysis).  `GeodesicSmoothDep.lean` proved the IC-derivative of
  the geodesic flow exists — but with the perturbation direction HARDCODED to `(0, w)`, i.e. the
  VELOCITY slot at a fixed base point.  Every firewall in the repo (`FlowJointRegularity.lean`§3,
  `BaseSlotAmpDeriv.lean`, `AxiomAudit.lean` J4-62) records the same limitation: "every regularity is
  in the VELOCITY slot at FIXED q; NO base-point differentiability anywhere."  The terminal `hCConv`
  wall (`ContDiffAt ℝ 1 Φ (0,0)`) needs base-slot — i.e. base-POINT — differentiability of the flow.

  KEY OBSERVATION.  The proof of `geodesicVariation_exists` NEVER uses that the first component of the
  perturbation direction is zero.  The `(0, w)` is purely cosmetic.  Replacing it with an ARBITRARY
  `ξ : Point n × Point n` gives, verbatim, the IC-derivative in direction `ξ`; instantiating
  `ξ = (u, 0)` (a POSITION perturbation) yields the first genuine BASE-POINT directional derivative of
  the geodesic flow in the repo.  This is exactly the object the "velocity-slot-only" firewalls said
  was absent — provable by the standard classical-ODE "flow is as smooth as the field" argument
  (Picard–Lindelöf + Grönwall residual), the same route `GeodesicSmoothDep.lean` already assembled for
  the velocity slot.

  WHAT LANDS HERE (all axiom-clean, no `sorry`):

  * `geodesicVariation_exists_dir` — the IC-derivative of the geodesic flow EXISTS and equals a
    supplied Jacobi solution `V`, for an ARBITRARY perturbation direction `ξ`
    (`HasDerivAt (fun s => Y s t) (V t) 0`, with `V 0 = ξ`, `Y s 0 − Y 0 0 = s·ξ`).  Direction-general
    version of `geodesicVariation_exists`; proof is the same residual-Grönwall little-o argument.

  * `geodesicVariation_hNb_discharge_dir` — the direction-general discharge of the carried quadratic
    field-remainder `hNb`, from the C² field remainder + two-point Grönwall.

  * `geodesicVariation_exists_dir_uncond` — direction-general IC-derivative existence with `hNb`
    discharged (carrying only genuine geometric regularity: `S` convex, field C² bound + Lipschitz on
    `S`, Jacobi-coefficient bound, tube containment, supplied Jacobi solution).

  * `geodesicVariation_basepoint_exists_uncond` — the BASE-POINT specialisation `ξ = (u, 0)`: the
    geodesic flow's directional derivative in the POSITION slot exists.  This is the first base-point
    directional-derivative statement for the geodesic flow in the repo — the direction the
    velocity-slot firewalls flagged as missing.

  * `geodesicVariation_basepoint_endpoint_exists_uncond` — the same, post-composed with the position
    projection `.1`: the POSITION ENDPOINT of the flow (the "exp map" output `w ↦ (tube 1).1`, here
    varied in the base point) has a base-point directional derivative.

  HONEST CHECKPOINT (binding).  This delivers the base-point DIRECTIONAL (Gâteaux) derivative of the
  geodesic flow, discharging the "velocity-slot-only" limitation for the ABSTRACT geodesic flow.  It
  does NOT (yet) supply: (i) a total/Fréchet base-point derivative or its continuity (i.e. genuine
  `ContDiffAt ℝ 1` — that needs joint direction-uniformity, one strictly stronger step); (ii) the
  wiring to the CONCRETE `.choose`-built `uniformFlowExp` (which additionally needs `q + s·u ∈ K`
  interior-openness + the tube-containment/convexity data); (iii) the terminal `hCConv` itself.  It is
  a genuine brick TOWARD base-slot C¹ — the direction slot the repo had only for velocity — not a
  discharge of `hCConv`.  It does NOT build the Jacobi equation, Raychaudhuri, or `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GeodesicSmoothDep

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **Direction-general IC-derivative existence.**  Identical to `geodesicVariation_exists` but with
    the perturbation direction an ARBITRARY `ξ : Point n × Point n` instead of the hardcoded `(0, w)`.
    For a one-parameter family `Y` of geodesics with base IC perturbed linearly by `s·ξ`, and a Jacobi
    solution `V` along the base geodesic with `V 0 = ξ`, the flow's IC-derivative at time `t` exists
    and equals `V t`:  `HasDerivAt (fun s => Y s t) (V t) 0`.

    Proof: verbatim the `geodesicVariation_exists` little-o/residual-Grönwall argument — that proof
    uses `ξ = (0,w)` only through `hV0`/`hIC`, never through the first component being zero. -/
theorem geodesicVariation_exists_dir (g gi : Point n → Fin n → Fin n → ℝ)
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {ξ : Point n × Point n}
    {K Cn : ℝ} (hK0 : 0 ≤ K) (hCn0 : 0 ≤ Cn) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ξ)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hNb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ)‖ ≤ Cn * s ^ 2) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  -- the uniform residual bound `‖Y s t − Y 0 t − s·V t‖ ≤ Cn·s²·exp K`.
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

/-- **Direction-general discharge of the carried quadratic field-remainder `hNb`.**  The
    direction-general sibling of `geodesicVariation_hNb_discharge`: with the perturbation direction an
    arbitrary `ξ`, the two-point Grönwall + C² field remainder give
    `‖F(Y s ·) − F(Y 0 ·) − DF(Y 0 ·)(Y s · − Y 0 ·)‖ ≤ (M₂·(‖ξ‖·e^{K₀})²)·s²`. -/
theorem geodesicVariation_hNb_discharge_dir (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {ξ : Point n × Point n} {S : Set (Point n × Point n)}
    {M₂ : ℝ} {K₀ : NNReal} (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ξ)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ)‖
        ≤ (M₂ * (‖ξ‖ * Real.exp K₀) ^ 2) * s ^ 2 := by
  intro s τ hτ
  have htp := geodesic_twopoint_gronwall g gi hLip (hYode s) (hYode 0) (hmem s) (hmem 0) τ hτ
  have hd0 : dist (Y s 0) (Y 0 0) = |s| * ‖ξ‖ := by
    rw [dist_eq_norm, hIC s, norm_smul, Real.norm_eq_abs]
  have hexp : Real.exp ((K₀ : ℝ) * τ) ≤ Real.exp K₀ := by
    apply Real.exp_le_exp.mpr
    calc (K₀ : ℝ) * τ ≤ (K₀ : ℝ) * 1 := mul_le_mul_of_nonneg_left hτ.2 (NNReal.coe_nonneg K₀)
      _ = (K₀ : ℝ) := mul_one _
  have hLnn : 0 ≤ |s| * ‖ξ‖ * Real.exp K₀ := by positivity
  have hL : ‖Y s τ - Y 0 τ‖ ≤ |s| * ‖ξ‖ * Real.exp K₀ := by
    rw [← dist_eq_norm]
    calc dist (Y s τ) (Y 0 τ)
        ≤ dist (Y s 0) (Y 0 0) * Real.exp ((K₀ : ℝ) * τ) := htp
      _ = |s| * ‖ξ‖ * Real.exp ((K₀ : ℝ) * τ) := by rw [hd0]
      _ ≤ |s| * ‖ξ‖ * Real.exp K₀ :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have hrem := geodesicField_uniform_C2_remainder g gi hC hconv hbound2 (hmem s τ hτ) (hmem 0 τ hτ)
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ)))
      (hbound2 (Y 0 τ) (hmem 0 τ hτ))
  refine hrem.trans ?_
  have hsq : ‖Y s τ - Y 0 τ‖ ^ 2 ≤ (|s| * ‖ξ‖ * Real.exp K₀) ^ 2 := by
    have := mul_le_mul hL hL (norm_nonneg _) hLnn
    simpa [pow_two] using this
  calc M₂ * ‖Y s τ - Y 0 τ‖ ^ 2
      ≤ M₂ * (|s| * ‖ξ‖ * Real.exp K₀) ^ 2 := mul_le_mul_of_nonneg_left hsq hnn
    _ = M₂ * (‖ξ‖ * Real.exp K₀) ^ 2 * s ^ 2 := by
        have hrw : (|s| * ‖ξ‖ * Real.exp K₀) ^ 2
            = s ^ 2 * (‖ξ‖ * Real.exp K₀) ^ 2 := by
          rw [mul_assoc, mul_pow, sq_abs]
        rw [hrw]; ring

/-- **Direction-general IC-derivative existence with `hNb` DISCHARGED.**  The direction-general
    sibling of `geodesicVariation_exists_uncond`: for an arbitrary perturbation direction `ξ`, the
    flow's IC-derivative exists and equals the supplied Jacobi solution `V`, carrying only genuine
    geometric regularity. -/
theorem geodesicVariation_exists_dir_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {ξ : Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ξ)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 t)))
      (hbound2 (Y 0 t) (hmem 0 t ht))
  have hCn0 : 0 ≤ M₂ * (‖ξ‖ * Real.exp K₀) ^ 2 := mul_nonneg hnn (sq_nonneg _)
  exact geodesicVariation_exists_dir g gi hK0 hCn0 ht hYode hVode hV0 hIC hKb
    (geodesicVariation_hNb_discharge_dir g gi hC hconv hbound2 hLip hYode hIC hmem)

/-- **BASE-POINT directional derivative of the geodesic flow.**  The specialisation of
    `geodesicVariation_exists_dir_uncond` to a POSITION perturbation `ξ = (u, 0)` (the base-point
    slot).  For a family `Y s` of geodesics with base point perturbed linearly `Y s 0 − Y 0 0 = s·(u,0)`
    (velocity held fixed) and a supplied Jacobi solution `V` with `V 0 = (u,0)`, the flow's base-point
    directional derivative exists: `HasDerivAt (fun s => Y s t) (V t) 0`.

    This is the first BASE-POINT directional-derivative statement for the geodesic flow in the repo —
    the slot the velocity-only firewalls (`FlowJointRegularity`§3, `BaseSlotAmpDeriv`) flagged as
    absent. -/
theorem geodesicVariation_basepoint_exists_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {u : Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((u, 0) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((u, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => Y s t) (V t) 0 :=
  geodesicVariation_exists_dir_uncond g gi hC hK0 ht hconv hbound2 hLip hYode hVode hV0 hIC hKb hmem

/-- **BASE-POINT directional derivative of the flow's POSITION ENDPOINT (the exp-map output).**
    Post-composing `geodesicVariation_basepoint_exists_uncond` with the position projection `.1` gives
    the base-point directional derivative of the ENDPOINT position map `s ↦ (Y s t).1` — the shape of
    the exp-map output `uniformFlowExp q w = (tube q w 1).1` when the base point is varied.  The
    derivative is the position component `(V t).1` of the Jacobi field. -/
theorem geodesicVariation_basepoint_endpoint_exists_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {u : Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((u, 0) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((u, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => (Y s t).1) (V t).1 0 := by
  have hfull : HasDerivAt (fun s => Y s t) (V t) 0 :=
    geodesicVariation_basepoint_exists_uncond g gi hC hK0 ht hconv hbound2 hLip hYode hVode hV0 hIC
      hKb hmem
  have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hfull
  simpa [Function.comp] using this

end QIQTH.ExpMap
