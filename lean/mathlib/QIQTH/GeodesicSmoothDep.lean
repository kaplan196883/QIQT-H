/-
  GeodesicSmoothDep — smooth dependence of the geodesic flow on its initial condition, via the
  repo's Grönwall residual machinery.

  ODE_VARIATIONAL_PLAN.md, Phase L2a.  Phase L1 (`GeodesicVariation.geodesicVariation_hasDerivAt`)
  proved the first-order variational equation CONDITIONAL on two smooth-dependence facts:
      (hV)    the IC-derivative EXISTS at each time:  `HasDerivAt (fun s => Y s t) (V t) 0`;
      (hswap) the time- and parameter-derivatives INTERCHANGE.
  This file DISCHARGES both from the residual Grönwall estimate — the standard
  C¹-dependence-on-initial-condition argument, the primitive Mathlib lacks, assembled here from the
  repo's existing pieces (`expJet_linVariation_residual_deriv`, the inhomogeneous Grönwall).

  WHAT LANDS HERE (all axiom-clean, no `sorry`):

  * `geodesicVariation_residual_bound` — UNCONDITIONAL (given the ODE + norm bounds).  For two
    geodesic integral curves `Y₁, Y₂` and ANY Jacobi solution `J` along `Y₁` (`J' = DF(Y₁)·J`) with
    the residual `R = (Y₂ − Y₁) − J` vanishing at `0`, if `‖DF(Y₁ t)‖ ≤ K` and the first-order
    Taylor remainder `‖F(Y₂) − F(Y₁) − DF(Y₁)(Y₂−Y₁)‖ ≤ C` uniformly on `[0,1]`, then
    `‖R t‖ ≤ C·exp K` for ALL `t ∈ [0,1]`.  This is the exact residual Grönwall the C¹-dependence
    argument integrates (`expJet_linVariation_residual_deriv` + `norm_le_gronwallBound_*`).

  * `geodesicVariation_exists` — the IC-derivative of the geodesic flow EXISTS and equals a supplied
    Jacobi solution `V`, i.e. `HasDerivAt (fun s => Y s t) (V t) 0` — discharging L1's `hV`.  This is
    the genuine C¹-dependence content: for a one-parameter family `Y` of geodesics with the velocity
    perturbed by `s·(0,w)`, the residual `R_s = (Y s − Y 0) − s·V` obeys `‖R_s t‖ ≤ (Cn·exp K)·s²`
    (`geodesicVariation_residual_bound` with `J = s·V`, `C = Cn·s²`), so the difference quotient
    `(Y s t − Y 0 t)/s → V t` (the `o(s)` characterisation `hasDerivAt_iff_isLittleO_nhds_zero`).
    NON-CIRCULAR: `V` is supplied as a Jacobi solution (constructed elsewhere, e.g. the fundamental
    solution `expJetFund`); the CONCLUSION — that this ODE solution IS the IC-derivative — is a
    different statement.

  * `geodesicVariation_hswap` — L1's mixed-partial `hswap` follows from `geodesicVariation_exists`
    (chain rule) + the Jacobi-solution hypothesis.

  * `geodesicVariation_hasDerivAt_of_smoothDep` — feeds `hV` and `hswap` into L1, so the first-order
    variational equation `IsGeodesicVariationAt g gi (Y 0) V t` holds through the L1 pipeline with
    BOTH smooth-dependence hypotheses discharged from the Grönwall residual.

  HONEST CHECKPOINT (binding): the discharge of L1's `hV`/`hswap` is UNCONDITIONAL modulo ONE carried
  analytic hypothesis — the *uniform quadratic* Taylor remainder of the geodesic field along the
  perturbed tube, `‖F(Y s ·) − F(Y 0 ·) − DF(Y 0 ·)(Y s · − Y 0 ·)‖ ≤ Cn·s²`.  This is the genuine
  C² input.  The repo currently proves only the FIRST-ORDER (o) remainder
  `geodesicField_uniform_C1_remainder` (`‖F a − F b − DF(b)(a−b)‖ ≤ ε‖a−b‖`); to discharge the carried
  hypothesis for the concrete geodesic tube one needs the SECOND-ORDER remainder
  `‖F a − F b − DF(b)(a−b)‖ ≤ M‖a−b‖²` (uniform C² Taylor bound of `geodesicField` on a convex
  compact set) combined with the two-point Lipschitz bound `‖Y s t − Y 0 t‖ ≤ C_L·|s|`
  (`geodesic_twopoint_gronwall`).  That uniform C² remainder is the exact missing lemma; it is
  labelled and carried, NOT faked.  This file does NOT build the (second-order) Jacobi equation (L2),
  NOT Raychaudhuri (L3), NOT the heat-kernel coefficient `a₁=R/6`.
-/
import Mathlib
import QIQTH.ExpMap
import QIQTH.GeodesicVariation

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **L2a-ii (the residual Grönwall) — UNCONDITIONAL given the ODE and the norm bounds.**  Let
    `Y₁, Y₂` be integral curves of the geodesic field on `[0,1]` and `J` ANY solution of the linear
    Jacobi equation `J' = DF(Y₁)·J` along `Y₁` (`DF = fderiv ℝ (geodesicField g gi)`).  If the
    residual `R = (Y₂ − Y₁) − J` vanishes at `0`, the Jacobi coefficient is bounded
    `‖DF(Y₁ t)‖ ≤ K`, and the first-order Taylor remainder is bounded
    `‖F(Y₂ t) − F(Y₁ t) − DF(Y₁ t)(Y₂ t − Y₁ t)‖ ≤ C` uniformly on `[0,1]`, then
    `‖Y₂ t − Y₁ t − J t‖ ≤ C·exp K` for every `t ∈ [0,1]`.

    Proof: `R` solves `R' = DF(Y₁)·R + N` with `N` the first-order Taylor remainder
    (`expJet_linVariation_residual_deriv`), so `‖R'‖ ≤ K‖R‖ + C`; Mathlib's inhomogeneous Grönwall
    `norm_le_gronwallBound_of_norm_deriv_right_le` with `R 0 = 0` gives `‖R t‖ ≤ gronwallBound 0 K C t`,
    bounded by `C·exp K` (`gronwallBound_zero_le_exp`).

    This is the exact `o(‖Y₂ 0 − Y₁ 0‖)` seed for the IC-derivative: taking `C = Cn·s²` (a quadratic
    remainder) makes the residual `O(s²)`, hence `o(s)`. -/
theorem geodesicVariation_residual_bound (g gi : Point n → Fin n → Fin n → ℝ)
    {Y₁ Y₂ J : ℝ → Point n × Point n} {K C : ℝ} (hK0 : 0 ≤ K) (hC0 : 0 ≤ C)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t)
    (hJ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y₁ t) (J t)) t)
    (h0 : Y₂ 0 - Y₁ 0 - J 0 = 0)
    (hKb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y₁ t)‖ ≤ K)
    (hNb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y₂ t) - geodesicField g gi (Y₁ t)
          - fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t)‖ ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Y₂ t - Y₁ t - J t‖ ≤ C * Real.exp K := by
  -- the residual ODE `R' = DF(Y₁)·R + N` (`expJet_linVariation_residual_deriv`).
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ => Y₂ τ - Y₁ τ - J τ)
        (fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t - J t)
          + (geodesicField g gi (Y₂ t) - geodesicField g gi (Y₁ t)
              - fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t))) t :=
    fun t ht => expJet_linVariation_residual_deriv g gi (h1 t ht) (h2 t ht) (hJ t ht)
  have hcont : ContinuousOn (fun τ => Y₂ τ - Y₁ τ - J τ) (Set.Icc 0 1) :=
    fun t ht => ((key t ht).continuousAt).continuousWithinAt
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun τ => Y₂ τ - Y₁ τ - J τ)
    (f' := fun t => fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t - J t)
      + (geodesicField g gi (Y₂ t) - geodesicField g gi (Y₁ t)
          - fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t)))
    (δ := 0) (K := K) (ε := C) (a := 0) (b := 1)
    hcont
    (fun x hx => (key x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (by show ‖Y₂ 0 - Y₁ 0 - J 0‖ ≤ 0; rw [h0]; simp)
    (by
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      show ‖fderiv ℝ (geodesicField g gi) (Y₁ x) (Y₂ x - Y₁ x - J x)
          + (geodesicField g gi (Y₂ x) - geodesicField g gi (Y₁ x)
              - fderiv ℝ (geodesicField g gi) (Y₁ x) (Y₂ x - Y₁ x))‖
        ≤ K * ‖Y₂ x - Y₁ x - J x‖ + C
      refine (norm_add_le _ _).trans (add_le_add ?_ (hNb x hx'))
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hKb x hx') (norm_nonneg _))
  intro t ht
  refine (hmain t ht).trans ?_
  rw [sub_zero]
  exact gronwallBound_zero_le_exp K C t hK0 hC0 ht.1 ht.2

/-- **L2a-iii (the IC-derivative EXISTS = `V`) — discharges L1's `hV`.**  Let `Y : ℝ → ℝ → State` be
    a one-parameter family of geodesics (`s` = variation parameter, second argument = time), with the
    base velocity perturbed linearly: `Y s 0 − Y 0 0 = s·(0,w)`.  Let `V` be a Jacobi solution along
    the base geodesic `Y 0` with `V 0 = (0,w)`.  If the Jacobi coefficient is bounded `‖DF(Y 0 s)‖ ≤ K`
    and the geodesic field obeys the UNIFORM QUADRATIC Taylor remainder
    `‖F(Y s ·) − F(Y 0 ·) − DF(Y 0 ·)(Y s · − Y 0 ·)‖ ≤ Cn·s²` on `[0,1]`, then the IC-derivative of
    the flow at time `t` EXISTS and equals `V t`:  `HasDerivAt (fun s => Y s t) (V t) 0`.

    Proof: for each `s`, `J := s·V` is a Jacobi solution with `J 0 = s·(0,w) = Y s 0 − Y 0 0`, so
    `geodesicVariation_residual_bound` (with `C = Cn·s²`) gives
    `‖Y s t − Y 0 t − s·V t‖ ≤ Cn·s²·exp K`.  Since `s² = ‖s‖²`, the residual is `O(s²) = o(s)`, which
    is exactly the little-o characterisation of `HasDerivAt (fun s => Y s t) (V t) 0`
    (`hasDerivAt_iff_isLittleO_nhds_zero`).

    HONEST: `V` is supplied as a Jacobi solution (`hVode`) — the standard construction (fundamental
    solution) is non-circular, the conclusion (this solution IS the derivative) being genuinely
    different.  The carried analytic input is `hNb` (the uniform quadratic field remainder); see the
    file header for the exact missing lemma (uniform C² remainder of `geodesicField`). -/
theorem geodesicVariation_exists (g gi : Point n → Fin n → Fin n → ℝ)
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {w : Point n}
    {K Cn : ℝ} (hK0 : 0 ≤ K) (hCn0 : 0 ≤ Cn) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((0, w) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hNb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ)‖ ≤ Cn * s ^ 2) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  -- the uniform residual bound `‖Y s t − Y 0 t − s·V t‖ ≤ Cn·s²·exp K` from L2a-ii.
  have hbnd : ∀ s : ℝ, ‖Y s t - Y 0 t - s • V t‖ ≤ Cn * s ^ 2 * Real.exp K := by
    intro s
    -- `J = s·V` is a Jacobi solution along the base geodesic.
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
  -- assemble the little-o characterisation of the IC-derivative.
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set M : ℝ := Cn * Real.exp K with hMdef
  have hM0 : 0 ≤ M := mul_nonneg hCn0 (Real.exp_pos K).le
  rw [Metric.eventually_nhds_iff]
  refine ⟨c / (M + 1), by positivity, fun s hs => ?_⟩
  rw [dist_eq_norm, sub_zero] at hs
  -- `‖residual‖ ≤ M·‖s‖²`, and `M·‖s‖² ≤ c·‖s‖` on the ball of radius `c/(M+1)`.
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

/-- **L2a-iii (the mixed-partial interchange `hswap`) — discharged.**  Under the same
    smooth-dependence hypotheses, L1's Clairaut interchange holds:
    `HasDerivAt V (deriv (fun s => F(Y s t)) 0) t`.  Proof: the IC-derivative existence
    (`geodesicVariation_exists`) + the chain rule give `deriv (fun s => F(Y s t)) 0 = DF(Y 0 t)(V t)`;
    the Jacobi-solution hypothesis `hVode` at `t` is exactly `HasDerivAt V (DF(Y 0 t)(V t)) t`. -/
theorem geodesicVariation_hswap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {w : Point n}
    {K Cn : ℝ} (hK0 : 0 ≤ K) (hCn0 : 0 ≤ Cn) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((0, w) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hNb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ)‖ ≤ Cn * s ^ 2) :
    HasDerivAt V (deriv (fun s => geodesicField g gi (Y s t)) 0) t := by
  have hex : HasDerivAt (fun s => Y s t) (V t) 0 :=
    geodesicVariation_exists g gi hK0 hCn0 ht hYode hVode hV0 hIC hKb hNb
  have hchain : HasDerivAt (fun s => geodesicField g gi (Y s t))
      (fderiv ℝ (geodesicField g gi) (Y 0 t) (V t)) 0 := by
    have := HasFDerivAt.comp_hasDerivAt (f := fun s => Y s t) (x := (0 : ℝ))
      (hasFDerivAt_geodesicField_fderiv g gi hC (Y 0 t)) hex
    simpa [Function.comp] using this
  rw [hchain.deriv]
  exact hVode t ht

/-- **L2a-iii (capstone) — the first-order variational equation with BOTH smooth-dependence
    hypotheses discharged.**  Feeding the discharged `hV` (`geodesicVariation_exists`) and `hswap`
    (`geodesicVariation_hswap`) into L1's `geodesicVariation_hasDerivAt` yields the linearized Jacobi
    equation `V'(t) = DF(Y 0 t)·V(t)` (`IsGeodesicVariationAt g gi (Y 0) V t`) through the L1
    pipeline, with the two Mathlib-absent ODE-smooth-dependence facts supplied from the Grönwall
    residual estimate rather than carried.

    The conclusion coincides with the Jacobi-solution hypothesis `hVode t` — the value delivered here
    is that L1's `hV`/`hswap` (the genuine C¹-dependence primitive) are met, modulo only the carried
    uniform quadratic field remainder `hNb`. -/
theorem geodesicVariation_hasDerivAt_of_smoothDep (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {w : Point n}
    {K Cn : ℝ} (hK0 : 0 ≤ K) (hCn0 : 0 ≤ Cn) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((0, w) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hNb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ)‖ ≤ Cn * s ^ 2) :
    IsGeodesicVariationAt g gi (Y 0) V t :=
  geodesicVariation_hasDerivAt g gi hC
    (geodesicVariation_exists g gi hK0 hCn0 ht hYode hVode hV0 hIC hKb hNb)
    (geodesicVariation_hswap g gi hC hK0 hCn0 ht hYode hVode hV0 hIC hKb hNb)

end QIQTH.ExpMap
