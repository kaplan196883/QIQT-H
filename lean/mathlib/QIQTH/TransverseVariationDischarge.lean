import Mathlib
import QIQTH.RadialJacobiLink
import QIQTH.ExpDiffVariation
import QIQTH.GeodesicSmoothDep
import QIQTH.ExpJacobianRescale

/-!
# EXP-JET3-3c — discharging / further reducing the transverse smooth-dependence primitive `hΦvar`

This brick attacks the primitive `hΦvar` consumed by
`radialJacobiLink_of_geodesicVariation` (`QIQTH/RadialJacobiLink.lean`) — the raw geodesic
velocity-variation statement that makes the radial Jacobi link `hBV` (hence the assembled
van-Vleck Ricci) unconditional.  Recall `hΦvar` (for the exp-flow `Φ` of
`expDiff_flow_isGeodesicVariation`, whose columns `V j s = Φ s (0,e_j)` build
`vanVleck_h4_assembled`) reads

```
  ∀ᶠ s, ∀ w, HasDerivAt (fun ε => exp_p(s•v + ε•(s•w))) ((Φ s (0,w)).1) 0.
```

## What lands here (floor F1 — the FULL discharge; `hBV` is now UNCONDITIONAL)

The primitive `hΦvar` is DISCHARGED outright, so `radialJacobiLink_uncond` exhibits the exp-flow
`Φ` of `expDiff_flow_isGeodesicVariation` — with `Φ 0 = id`, `fderiv exp_p v = π ∘ Φ(1) ∘ ι`, and
its `[0,1]` Jacobi law — TOGETHER with the radial Jacobi link holding for it, carrying no
hypothesis (for `s₀` in the geodesic interior `(0,1)`).

The chain of results:

* `residual_bound_rightDeriv` — a *variation-localised, right-derivative* reproof of the residual
  Grönwall `geodesicVariation_residual_bound`: the candidate Jacobi `J` is required only to be
  RIGHT differentiable (`HasDerivWithinAt … (Ici t) t` on `Ico 0 1`), matching the exp-flow's
  `HasDerivWithinAt … (Icc 0 1)` law.  This removes the endpoint obstruction (`τ = 0, 1`) that
  blocked plugging `J = ε·(fun τ => Φ τ (0,w))` into the original bound.

* `tubeTransverse_hasDerivAt_phase` — the transverse initial-velocity variation of the geodesic
  tube has, at `ε = 0`, derivative the flow value: `HasDerivAt (fun ε => expTube p (v+ε•w) s) (Φ s (0,w)) 0`.
  Proof: the residual `expTube p (v+ε•w) − expTube p v − ε·(Φ·(0,w))` is `o(ε)` via
  `residual_bound_rightDeriv` fed the field's uniform C¹ remainder
  (`geodesicField_uniform_C1_remainder`) — the same `o`-not-`O` route as `hasFDerivAt_expMap`, so
  no second-order `‖∂²F‖ ≤ M₂` bound is needed — with the confinement/Lipschitz/`‖DF‖` regularity
  built from `hC` on a fixed compact ball `S`.

* `radialJacobiLink_of_tubeTransverseVariation` — turns that (projected to the position component)
  into `hBV`, discharging `hΦvar` inside `radialJacobiLink_of_geodesicVariation` via the geodesic
  homogeneity `expMap_smul_eq_expTube` and `s•v + ε•(s•w) = s•(v+ε•w)`.

* `radialJacobiLink_uncond` — the capstone: instantiates `Φ` with the exp-flow and delivers `hBV`
  unconditionally.

The three obstructions previously flagged (variation-range localisation, flow endpoint regularity,
geometric regularity) are all resolved above.  This is NOT `a₁ = R/6`; it discharges exactly the
transverse smooth-dependence primitive `hΦvar` feeding the assembled van-Vleck Ricci radial ODE.
-/

set_option maxHeartbeats 1600000

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.JacobianDet
open Topology

variable {n : ℕ}

/-- **EXP-JET3-3c (floor F2) — the radial Jacobi link `hBV` from the clean transverse geodesic-tube
variation primitive `hΦtube`.**

Reduces `hBV` one notch below `radialJacobiLink_of_geodesicVariation`: the carried primitive is the
raw transverse smooth-dependence statement that the position part of the initial-velocity variation
of the geodesic tube at parameter `s` equals `(Φ s (0,w)).1`:

```
  hΦtube : ∀ᶠ s, ∀ w, HasDerivAt (fun ε => (expTube p (v + ε•w) s).1) ((Φ s (0,w)).1) 0.
```

The exp-map / argument-scalar / ray-vs-geodesic layers of `hΦvar` are discharged INSIDE by the
geodesic homogeneity `expMap_smul_eq_expTube` (`exp_p(s•(v+ε•w)) = (expTube p (v+ε•w) s).1` for `ε`
small and `|s| ≤ 1`) together with `s•v + ε•(s•w) = s•(v+ε•w)`.  The remaining transverse content
`hΦtube` is exactly the output shape of `geodesicVariation_exists_uncond`. -/
theorem radialJacobiLink_of_tubeTransverseVariation
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) {s₀ : ℝ} (hs₀ : |s₀| < 1)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦtube : ∀ᶠ s in nhds s₀, ∀ (w : Point n),
        HasDerivAt (fun ε : ℝ => (expTube g gi hC p (v + ε • w) s).1)
          ((Φ s ((0 : Point n), w)).1) 0) :
    ∀ᶠ s in nhds s₀, ∀ (a j : Fin n),
      (Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n))).1 a
        = (s • expJacobianMat g gi hC p (s • v)) a j := by
  -- reduce to `radialJacobiLink_of_geodesicVariation` by discharging its `hΦvar`.
  refine radialJacobiLink_of_geodesicVariation g gi hC p v hv hs₀ Φ ?_
  -- eventual bound `|s| ≤ 1` near `s₀`.
  have hle1 : ∀ᶠ s in nhds s₀, |s| ≤ 1 := by
    have hmem : Metric.ball s₀ (1 - |s₀|) ∈ nhds s₀ :=
      Metric.ball_mem_nhds s₀ (by linarith [hs₀])
    filter_upwards [hmem] with s hsmem
    rw [Metric.mem_ball, Real.dist_eq] at hsmem
    calc |s| = |s - s₀ + s₀| := by ring_nf
      _ ≤ |s - s₀| + |s₀| := abs_add_le _ _
      _ ≤ (1 - |s₀|) + |s₀| := by linarith [hsmem]
      _ = 1 := by ring
  filter_upwards [hΦtube, hle1] with s htube hs1
  intro w
  -- the tube variation at `w`.
  have htube_w := htube w
  -- geodesic homogeneity rewrite, eventually in `ε`:
  --   `exp_p(s•v + ε•(s•w)) = (expTube p (v+ε•w) s).1`  near `ε = 0`.
  have hEq : (fun ε : ℝ => expMap g gi hC p (s • v + ε • (s • w)))
      =ᶠ[nhds (0 : ℝ)] (fun ε : ℝ => (expTube g gi hC p (v + ε • w) s).1) := by
    have hρpos : 0 < (expRho g gi hC p - ‖v‖) / (‖w‖ + 1) :=
      div_pos (by linarith [hv]) (by positivity)
    have hball : Metric.ball (0 : ℝ) ((expRho g gi hC p - ‖v‖) / (‖w‖ + 1)) ∈ nhds (0 : ℝ) :=
      Metric.ball_mem_nhds 0 hρpos
    filter_upwards [hball] with ε hε
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
    -- `‖v + ε•w‖ ≤ expRho`.
    have hvew : ‖v + ε • w‖ ≤ expRho g gi hC p := by
      have hεw : |ε| * ‖w‖ < expRho g gi hC p - ‖v‖ := by
        rcases le_or_gt (‖w‖) 0 with hw | hw
        · have : ‖w‖ = 0 := le_antisymm hw (norm_nonneg _)
          rw [this, mul_zero]; linarith [hv]
        · have hlt : |ε| < (expRho g gi hC p - ‖v‖) / (‖w‖ + 1) := hε
          have := mul_lt_mul_of_pos_right hlt (by positivity : (0:ℝ) < ‖w‖ + 1)
          rw [div_mul_cancel₀ _ (by positivity : (‖w‖ + 1 : ℝ) ≠ 0)] at this
          calc |ε| * ‖w‖ ≤ |ε| * (‖w‖ + 1) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith
            _ < expRho g gi hC p - ‖v‖ := this
      calc ‖v + ε • w‖ ≤ ‖v‖ + ‖ε • w‖ := norm_add_le _ _
        _ = ‖v‖ + |ε| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ expRho g gi hC p := by linarith
    -- `s•v + ε•(s•w) = s•(v + ε•w)`.
    have harg : s • v + ε • (s • w) = s • (v + ε • w) := by
      rw [smul_add, smul_comm s ε w]
    rw [harg, expMap_smul_eq_expTube g gi hC p (v + ε • w) hvew hs1]
  exact htube_w.congr_of_eventuallyEq hEq

/-! ### Toward F1 — the variation-localised, right-derivative residual bound (discharging G2)

The workhorse `geodesicVariation_residual_bound` demands the candidate Jacobi `J` be *fully*
differentiable (`HasDerivAt`) on all of `Icc 0 1`.  For `J = ε • (fun τ => Φ τ (0,w))` the exp-flow
supplies only `HasDerivWithinAt … (Icc 0 1)`, which does not upgrade to `HasDerivAt` at the
endpoints (G2).  The bound below reproves the residual Grönwall using only the RIGHT derivative of
`J` (`HasDerivWithinAt … (Ici t) t` on `Ico 0 1`) — the exact regularity the flow law provides —
so it applies with `J` the exp-flow itself. -/

/-- **Right-derivative residual Grönwall.**  Identical conclusion to
`geodesicVariation_residual_bound`, but the candidate Jacobi `J` is required only to be *right*
differentiable along `Ici t` on `Ico 0 1` (plus continuous on `Icc 0 1`).  This matches the exp-flow
`fun τ => Φ τ (0,w)`, whose ODE law is a `HasDerivWithinAt … (Icc 0 1)`. -/
theorem residual_bound_rightDeriv (g gi : Point n → Fin n → Fin n → ℝ)
    {Y₁ Y₂ J : ℝ → Point n × Point n} {K C : ℝ} (hK0 : 0 ≤ K) (hC0 : 0 ≤ C)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t)
    (hJ : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt J (fderiv ℝ (geodesicField g gi) (Y₁ t) (J t)) (Set.Ici t) t)
    (hJcont : ContinuousOn J (Set.Icc (0 : ℝ) 1))
    (h0 : Y₂ 0 - Y₁ 0 - J 0 = 0)
    (hKb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y₁ t)‖ ≤ K)
    (hNb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y₂ t) - geodesicField g gi (Y₁ t)
          - fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t)‖ ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Y₂ t - Y₁ t - J t‖ ≤ C * Real.exp K := by
  set F := geodesicField g gi with hFdef
  -- the residual's RIGHT derivative on `Ico 0 1`:  R'(t) = DF(Y₁ t)(R t) + N t.
  have key : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun τ => Y₂ τ - Y₁ τ - J τ)
        (fderiv ℝ F (Y₁ t) (Y₂ t - Y₁ t - J t)
          + (F (Y₂ t) - F (Y₁ t) - fderiv ℝ F (Y₁ t) (Y₂ t - Y₁ t))) (Set.Ici t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
    have hb1 : HasDerivWithinAt Y₁ (F (Y₁ t)) (Set.Ici t) t := (h1 t ht').hasDerivWithinAt
    have hb2 : HasDerivWithinAt Y₂ (F (Y₂ t)) (Set.Ici t) t := (h2 t ht').hasDerivWithinAt
    have hbase : HasDerivWithinAt (fun τ => Y₂ τ - Y₁ τ - J τ)
        (F (Y₂ t) - F (Y₁ t) - fderiv ℝ F (Y₁ t) (J t)) (Set.Ici t) t :=
      (hb2.sub hb1).sub (hJ t ht)
    have hkey : fderiv ℝ F (Y₁ t) (Y₂ t - Y₁ t - J t)
          + (F (Y₂ t) - F (Y₁ t) - fderiv ℝ F (Y₁ t) (Y₂ t - Y₁ t))
        = F (Y₂ t) - F (Y₁ t) - fderiv ℝ F (Y₁ t) (J t) := by
      rw [map_sub]; abel
    rw [hkey]; exact hbase
  have hcont : ContinuousOn (fun τ => Y₂ τ - Y₁ τ - J τ) (Set.Icc 0 1) := by
    have hc1 : ContinuousOn Y₁ (Set.Icc (0:ℝ) 1) :=
      fun t ht => (h1 t ht).continuousAt.continuousWithinAt
    have hc2 : ContinuousOn Y₂ (Set.Icc (0:ℝ) 1) :=
      fun t ht => (h2 t ht).continuousAt.continuousWithinAt
    exact (hc2.sub hc1).sub hJcont
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun τ => Y₂ τ - Y₁ τ - J τ)
    (f' := fun t => fderiv ℝ F (Y₁ t) (Y₂ t - Y₁ t - J t)
      + (F (Y₂ t) - F (Y₁ t) - fderiv ℝ F (Y₁ t) (Y₂ t - Y₁ t)))
    (δ := 0) (K := K) (ε := C) (a := 0) (b := 1)
    hcont
    (fun x hx => key x hx)
    (by show ‖Y₂ 0 - Y₁ 0 - J 0‖ ≤ 0; rw [h0]; simp)
    (by
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      show ‖fderiv ℝ F (Y₁ x) (Y₂ x - Y₁ x - J x)
          + (F (Y₂ x) - F (Y₁ x) - fderiv ℝ F (Y₁ x) (Y₂ x - Y₁ x))‖
        ≤ K * ‖Y₂ x - Y₁ x - J x‖ + C
      refine (norm_add_le _ _).trans (add_le_add ?_ (hNb x hx'))
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hKb x hx') (norm_nonneg _))
  intro t ht
  refine (hmain t ht).trans ?_
  rw [sub_zero]
  exact gronwallBound_zero_le_exp K C t hK0 hC0 ht.1 ht.2

/-- Helper: for `x ∈ Ico 0 1`, `Icc 0 1` is a right-neighbourhood of `x` (`∈ 𝓝[Ici x] x`), so a
`HasDerivWithinAt … (Icc 0 1)` upgrades to `HasDerivWithinAt … (Ici x)`. -/
private theorem icc_mem_nhdsWithin_ici {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 ∈ 𝓝[Set.Ici x] x := by
  have hIci0 : Set.Ici (0 : ℝ) ∈ 𝓝[Set.Ici x] x :=
    Filter.mem_of_superset self_mem_nhdsWithin (Set.Ici_subset_Ici.mpr hx.1)
  have hIic1 : Set.Iic (1 : ℝ) ∈ 𝓝[Set.Ici x] x :=
    nhdsWithin_le_nhds (Iic_mem_nhds hx.2)
  exact Filter.mem_of_superset (Filter.inter_mem hIci0 hIic1)
    (fun y hy => Set.mem_Icc.mpr ⟨Set.mem_Ici.mp hy.1, Set.mem_Iic.mp hy.2⟩)

/-- **EXP-JET3-3c (floor F1 — the transverse discharge, phase-space form).**  For the exp-flow `Φ`
(via `expDiff_flow_isGeodesicVariation`: `Φ 0 = id` and the `[0,1]` Jacobi law `hflow`) and a
geodesic parameter `s ∈ [0,1]`, the initial-velocity variation of the geodesic tube has, at `ε = 0`,
derivative the flow value `Φ s (0,w)`:

```
  HasDerivAt (fun ε => expTube p (v + ε•w) s) (Φ s (0,w)) 0.
```

This is the genuine transverse smooth-dependence-on-initial-condition content: the residual
`R_ε = expTube p (v+ε•w) − expTube p v − ε·(Φ·(0,w))` obeys `‖R_ε s‖ ≤ M·ε²` (a variation-localised
right-derivative Grönwall, `residual_bound_rightDeriv`, whose only-right-derivative requirement is met
by the exp-flow's `HasDerivWithinAt (Icc 0 1)` law), so the difference quotient `→ Φ s (0,w)`. -/
theorem tubeTransverse_hasDerivAt_phase (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hflow : ∀ (z : Point n × Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s => Φ s z)
          (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ t z)) (Set.Icc (0 : ℝ) 1) t)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (w : Point n) :
    HasDerivAt (fun ε : ℝ => expTube g gi hC p (v + ε • w) s) (Φ s ((0 : Point n), w)) 0 := by
  classical
  set F := geodesicField g gi with hFdef
  set Rb : ℝ := expConst g gi hC p * (‖v‖ + 1) + 1 with hRbdef
  have hRb0 : 0 ≤ Rb := by rw [hRbdef]; have := expConst_nonneg g gi hC p; positivity
  set S : Set (Point n × Point n) := Metric.closedBall ((p, 0) : Point n × Point n) Rb with hSdef
  have hconvS : Convex ℝ S := convex_closedBall _ _
  have hcompS : IsCompact S := isCompact_closedBall _ _
  -- Lipschitz constant `K₀` and Jacobi-coefficient bound `K` on the compact `S`.
  obtain ⟨K₀, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) hconvS hcompS
  have hDFcont : Continuous (fderiv ℝ F) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  obtain ⟨K, hKb0⟩ := hcompS.exists_bound_of_continuousOn hDFcont.continuousOn
  have hK0 : (0 : ℝ) ≤ K :=
    le_trans (norm_nonneg _) (hKb0 (p, 0) (by rw [hSdef]; exact Metric.mem_closedBall_self hRb0))
  -- base tube data.
  have hv_le : ‖v‖ ≤ expRho g gi hC p := hv.le
  obtain ⟨hY10, hY1d, hY1conf⟩ := expTube_spec g gi hC p v hv_le
  have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hY1ode : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (expTube g gi hC p v) (F (expTube g gi hC p v t)) t :=
    fun t ht => hY1d t (hIcc_Ioo t ht)
  have hY1mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    have := hY1conf t ht
    have hle : expConst g gi hC p * ‖v‖ ≤ Rb := by
      rw [hRbdef]; have := expConst_nonneg g gi hC p; nlinarith [norm_nonneg v]
    exact le_trans this hle
  -- `V τ = Φ τ (0,w)` regularity from the flow law.
  set V : ℝ → Point n × Point n := fun τ => Φ τ ((0 : Point n), w) with hVdef
  have hVflow : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt V (fderiv ℝ F (expTube g gi hC p v t) (V t)) (Set.Icc (0 : ℝ) 1) t :=
    fun t ht => hflow ((0 : Point n), w) t ht
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hVflow t ht).continuousWithinAt
  have hV0 : V 0 = ((0, w) : Point n × Point n) := by
    simp only [hVdef, hΦ0, ContinuousLinearMap.id_apply]
  -- convert to `HasDerivAt` via the little-o characterisation, discharging the residual with the
  -- uniform C¹ remainder of the field (à la `hasFDerivAt_expMap`) — giving `o(ε)` directly, no C².
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, zero_smul, add_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  -- Grönwall/Lipschitz factor `B` and the C¹-remainder tolerance `εc`.
  set B : ℝ := ‖w‖ * Real.exp (K₀ : ℝ) * Real.exp K with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set εc : ℝ := c / (B + 1) with hεcdef
  have hεc0 : 0 < εc := div_pos hc (by positivity)
  obtain ⟨δ, hδ0, hδrem⟩ := geodesicField_uniform_C1_remainder g gi hC hconvS hcompS hεc0
  rw [Metric.eventually_nhds_iff]
  -- ε-radius: tube validity (expRho + confinement) and `‖Y₂ t − Y₁ t‖ < δ`.
  refine ⟨min (min ((expRho g gi hC p - ‖v‖) / (‖w‖ + 1)) (1 / (‖w‖ + 1)))
      (δ / (‖w‖ * Real.exp (K₀ : ℝ) + 1)),
      lt_min (lt_min (div_pos (by linarith [hv]) (by positivity)) (by positivity))
        (div_pos hδ0 (by positivity)), fun ε hε => ?_⟩
  rw [dist_eq_norm, sub_zero] at hε
  have hεv : |ε| < (expRho g gi hC p - ‖v‖) / (‖w‖ + 1) :=
    lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε1 : |ε| < 1 / (‖w‖ + 1) :=
    lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεδ : |ε| < δ / (‖w‖ * Real.exp (K₀ : ℝ) + 1) := lt_of_lt_of_le hε (min_le_right _ _)
  -- `|ε|·‖w‖` bounds and tube validity.
  have hεw_lt : |ε| * ‖w‖ < expRho g gi hC p - ‖v‖ := by
    have := mul_lt_mul_of_pos_right hεv (by positivity : (0:ℝ) < ‖w‖ + 1)
    rw [div_mul_cancel₀ _ (by positivity : (‖w‖ + 1 : ℝ) ≠ 0)] at this
    calc |ε| * ‖w‖ ≤ |ε| * (‖w‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ < _ := this
  have hεw_le1 : |ε| * ‖w‖ ≤ 1 := by
    have := mul_lt_mul_of_pos_right hε1 (by positivity : (0:ℝ) < ‖w‖ + 1)
    rw [div_mul_cancel₀ _ (by positivity : (‖w‖ + 1 : ℝ) ≠ 0)] at this
    nlinarith [abs_nonneg ε, norm_nonneg w]
  have hvew_le : ‖v + ε • w‖ ≤ expRho g gi hC p := by
    calc ‖v + ε • w‖ ≤ ‖v‖ + ‖ε • w‖ := norm_add_le _ _
      _ = ‖v‖ + |ε| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ expRho g gi hC p := by linarith
  have hltδ : |ε| * ‖w‖ * Real.exp (K₀ : ℝ) < δ := by
    have hmul := mul_lt_mul_of_pos_right hεδ
      (by positivity : (0:ℝ) < ‖w‖ * Real.exp (K₀ : ℝ) + 1)
    rw [div_mul_cancel₀ _ (by positivity : (‖w‖ * Real.exp (K₀ : ℝ) + 1 : ℝ) ≠ 0)] at hmul
    have hd : |ε| * (‖w‖ * Real.exp (K₀ : ℝ) + 1)
        = |ε| * ‖w‖ * Real.exp (K₀ : ℝ) + |ε| := by ring
    rw [hd] at hmul; linarith [abs_nonneg ε]
  -- perturbed tube data.
  obtain ⟨hY20, hY2d, hY2conf⟩ := expTube_spec g gi hC p (v + ε • w) hvew_le
  have hY2ode : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (expTube g gi hC p (v + ε • w)) (F (expTube g gi hC p (v + ε • w) t)) t :=
    fun t ht => hY2d t (hIcc_Ioo t ht)
  have hY2mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + ε • w) t ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    refine le_trans (hY2conf t ht) ?_
    have hnn := expConst_nonneg g gi hC p
    have hvew : ‖v + ε • w‖ ≤ ‖v‖ + 1 := by
      calc ‖v + ε • w‖ ≤ ‖v‖ + |ε| * ‖w‖ := by
            refine le_trans (norm_add_le _ _) ?_
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖v‖ + 1 := by linarith
    rw [hRbdef]; nlinarith [norm_nonneg v]
  -- the candidate Jacobi `J = ε • V`.
  set J : ℝ → Point n × Point n := fun τ => ε • V τ with hJdef
  have hJ : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt J (fderiv ℝ F (expTube g gi hC p v t) (J t)) (Set.Ici t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
    have hVt : HasDerivWithinAt V (fderiv ℝ F (expTube g gi hC p v t) (V t)) (Set.Ici t) t :=
      (hVflow t ht').mono_of_mem_nhdsWithin (icc_mem_nhdsWithin_ici ht)
    have hJt := hVt.const_smul ε
    have heq : ε • fderiv ℝ F (expTube g gi hC p v t) (V t)
        = fderiv ℝ F (expTube g gi hC p v t) (J t) := by
      rw [hJdef]; exact (map_smul _ ε (V t)).symm
    rw [heq] at hJt
    exact hJt
  have hJcont : ContinuousOn J (Set.Icc (0 : ℝ) 1) := hVcont.const_smul ε
  have hJ0eq : expTube g gi hC p (v + ε • w) 0 - expTube g gi hC p v 0 - J 0 = 0 := by
    have hJ0 : J 0 = expTube g gi hC p (v + ε • w) 0 - expTube g gi hC p v 0 := by
      rw [hY20, hY10]
      simp only [hJdef, hV0, Prod.smul_mk, smul_zero, Prod.mk_sub_mk, sub_self,
        add_sub_cancel_left]
    rw [hJ0]; abel
  have hKbS : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ F (expTube g gi hC p v t)‖ ≤ K :=
    fun t ht => hKb0 _ (hY1mem t ht)
  -- two-point flow-Lipschitz: `‖Y₂ t − Y₁ t‖ ≤ |ε|‖w‖ e^{K₀}` uniformly on `[0,1]`.
  have hd0 : dist (expTube g gi hC p (v + ε • w) 0) (expTube g gi hC p v 0) = |ε| * ‖w‖ := by
    rw [hY20, hY10, dist_eq_norm, Prod.mk_sub_mk, sub_self,
      show (v + ε • w) - v = ε • w by abel, Prod.norm_def]
    simp only [norm_zero, norm_smul, Real.norm_eq_abs]
    rw [max_eq_right (by positivity)]
  have hnormle : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + ε • w) t - expTube g gi hC p v t‖ ≤ |ε| * ‖w‖ * Real.exp (K₀ : ℝ) := by
    intro t ht
    have htp := geodesic_twopoint_gronwall g gi hLip hY2ode hY1ode hY2mem hY1mem t ht
    have hexp_le : Real.exp ((K₀ : ℝ) * t) ≤ Real.exp (K₀ : ℝ) := by
      apply Real.exp_le_exp.mpr
      calc (K₀ : ℝ) * t ≤ (K₀ : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (NNReal.coe_nonneg K₀)
        _ = (K₀ : ℝ) := mul_one _
    rw [← dist_eq_norm]
    calc dist (expTube g gi hC p (v + ε • w) t) (expTube g gi hC p v t)
        ≤ dist (expTube g gi hC p (v + ε • w) 0) (expTube g gi hC p v 0)
            * Real.exp ((K₀ : ℝ) * t) := htp
      _ = |ε| * ‖w‖ * Real.exp ((K₀ : ℝ) * t) := by rw [hd0]
      _ ≤ |ε| * ‖w‖ * Real.exp (K₀ : ℝ) := mul_le_mul_of_nonneg_left hexp_le (by positivity)
  -- the uniform C¹ residual `‖N t‖ ≤ εc·(|ε|‖w‖ e^{K₀})`.
  have hNb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖F (expTube g gi hC p (v + ε • w) t) - F (expTube g gi hC p v t)
          - fderiv ℝ F (expTube g gi hC p v t)
            (expTube g gi hC p (v + ε • w) t - expTube g gi hC p v t)‖
        ≤ εc * (|ε| * ‖w‖ * Real.exp (K₀ : ℝ)) := by
    intro t ht
    have hd := hδrem (expTube g gi hC p (v + ε • w) t) (hY2mem t ht)
      (expTube g gi hC p v t) (hY1mem t ht) (lt_of_le_of_lt (hnormle t ht) hltδ)
    exact hd.trans (mul_le_mul_of_nonneg_left (hnormle t ht) hεc0.le)
  -- the right-derivative residual bound at `t = s`.
  have hCbnd := residual_bound_rightDeriv g gi hK0
    (by positivity) hY1ode hY2ode hJ hJcont hJ0eq hKbS hNb s hs
  simp only [hJdef, hVdef] at hCbnd
  -- `(εc·|ε|‖w‖ e^{K₀})·e^K = εc·B·|ε| ≤ c·|ε|`.
  refine hCbnd.trans ?_
  rw [Real.norm_eq_abs]
  have hεcB : εc * B ≤ c := by
    rw [hεcdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [hc, hB0]
  calc εc * (|ε| * ‖w‖ * Real.exp (K₀ : ℝ)) * Real.exp K
      = (εc * B) * |ε| := by rw [hBdef]; ring
    _ ≤ c * |ε| := mul_le_mul_of_nonneg_right hεcB (abs_nonneg _)

/-- **EXP-JET3-3c (floor F1 — capstone).  The radial Jacobi link `hBV` is UNCONDITIONAL.**

Exhibits the exp-differential geodesic-variation flow `Φ` of `expDiff_flow_isGeodesicVariation`
(the very flow whose columns `V j s = Φ s (0, e_j)` build `vanVleck_h4_assembled`) — with all its
defining data (`Φ 0 = id`, `fderiv exp_p v = π ∘ Φ(1) ∘ ι`, the `[0,1]` Jacobi law) — together with
the radial Jacobi link holding for it:

```
  ∀ᶠ s, ∀ a j, (Φ s (0, e_j)).1 a = (s • expJacobianMat g gi hC p (s•v)) a j.
```

No hypothesis is carried: the transverse smooth-dependence primitive `hΦvar`/`hΦtube` is now DERIVED
(`tubeTransverse_hasDerivAt_phase`, via the variation-localised right-derivative Grönwall
`residual_bound_rightDeriv` + the field's uniform C¹ remainder).  This discharges the primitive that
`radialJacobiLink_of_geodesicVariation` consumed, so `hBV` — the geometric germ feeding the assembled
van-Vleck Ricci radial ODE — is unconditional (for `s₀` in the geodesic-interior `(0,1)`). -/
theorem radialJacobiLink_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) {s₀ : ℝ} (hs₀0 : 0 < s₀) (hs₀1 : s₀ < 1) :
    ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      HasFDerivAt (expMap g gi hC p)
        (expJetPi.comp ((Φ 1).comp (expJetIota (n := n)))) v ∧
      (∀ (z : Point n × Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s => Φ s z)
          (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ t z)) (Set.Icc (0 : ℝ) 1) t) ∧
      ∀ᶠ s in nhds s₀, ∀ (a j : Fin n),
        (Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n))).1 a
          = (s • expJacobianMat g gi hC p (s • v)) a j := by
  obtain ⟨Φ, hΦ0, hFD, hflow⟩ := expDiff_flow_isGeodesicVariation g gi hC p v hv
  refine ⟨Φ, hΦ0, hFD, hflow, ?_⟩
  refine radialJacobiLink_of_tubeTransverseVariation g gi hC p v hv
    (abs_lt.mpr ⟨by linarith, hs₀1⟩) Φ ?_
  -- the transverse geodesic-tube primitive `hΦtube`, discharged near `s₀ ∈ (0,1)`.
  filter_upwards [Ioo_mem_nhds hs₀0 hs₀1] with s hs_ioo
  intro w
  have hs_icc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs_ioo.1.le, hs_ioo.2.le⟩
  have hphase := tubeTransverse_hasDerivAt_phase g gi hC p v hv Φ hΦ0 hflow hs_icc w
  have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt 0 hphase
  simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', Prod.fst] using this

end QIQTH.ExpMap


