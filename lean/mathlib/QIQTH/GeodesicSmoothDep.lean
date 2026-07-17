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

/-! ### L2b — the uniform C² remainder (discharging L2a's carried `hNb`)

  Phase L2b of the ODE-variational campaign (ODE_VARIATIONAL_PLAN.md).  L2a
  (`geodesicVariation_exists`) proved the IC-derivative exists MODULO the carried hypothesis `hNb` —
  the *uniform quadratic* (C²) Taylor remainder of the geodesic field.  This section DISCHARGES it:

  * `decay_order_two_remainder_convex` — the general vector-valued second-order Taylor bound on a
    convex set: if `F` is C² on a convex `S` with `‖∂²F‖ ≤ M` there, then for `a, b ∈ S`,
    `‖F a − F b − DF(b)(a−b)‖ ≤ M·‖a−b‖²` (crude iterated-MVT constant `M`, not the sharp `M/2`;
    mirrors `RNCDecay.decay_order_two`, restricted to the segment `[b,a] ⊆ S` to recover the quadratic
    rate exactly as `geodesicField_uniform_C1_remainder` does).

  * `geodesicField_uniform_C2_remainder` — the specialisation to `F = geodesicField g gi` (C^∞, so the
    two differentiability facts are PROVED from `hC`, not carried): on a convex `S` where the field's
    second Fréchet derivative is bounded `‖∂²F‖ ≤ M₂`, `‖F a − F b − DF(b)(a−b)‖ ≤ M₂·‖a−b‖²`.

  * `geodesicVariation_hNb_discharge` — feeds the C² remainder + the two-point flow-Lipschitz bound
    `‖Y s τ − Y 0 τ‖ ≤ |s|·‖(0,w)‖·e^{K₀}` (`geodesic_twopoint_gronwall`) into the `hNb` shape,
    producing `‖F(Y s ·) − F(Y 0 ·) − DF(Y 0 ·)(Y s · − Y 0 ·)‖ ≤ (M₂·(‖(0,w)‖·e^{K₀})²)·s²`, i.e.
    `Cn = M₂·(‖(0,w)‖·e^{K₀})²`.  This is exactly `hNb`.

  * `geodesicVariation_exists_uncond` — plugs the discharge into `geodesicVariation_exists`, giving the
    IC-derivative existence with `hNb` DISCHARGED, carrying only the genuine geometric regularity: `S`
    convex, the field's C² bound `‖∂²F‖ ≤ M₂` on `S`, the field Lipschitz on `S` (`LipschitzOnWith K₀`),
    the Jacobi-coefficient bound `‖DF(Y 0 τ)‖ ≤ K`, tube containment `Y s τ ∈ S`, and the supplied
    Jacobi solution `V`.

  HONEST CHECKPOINT (binding): this discharges L2a's `hNb` (first-order smooth-dependence on IC) — the
  C² field remainder is UNCONDITIONAL given the field's C² bound on `S`, which is carried as the genuine
  geometric hypothesis `hbound2 : ‖∂²F‖ ≤ M₂` (a standard fact for a fixed smooth metric on a compact
  region, NOT vacuous, NOT the conclusion).  It does NOT build the second-order Jacobi equation (L2),
  NOT Raychaudhuri (L3), NOT the heat-kernel coefficient `a₁ = R/6`. -/

/-- **General vector-valued second-order Taylor remainder on a convex set.**  If `F : E → G` is
    differentiable on a convex set `S` with `fderiv F` also differentiable there and the second Fréchet
    derivative bounded `‖fderiv (fderiv F) x‖ ≤ M` on `S`, then for `a, b ∈ S`:
    `‖F a − F b − (fderiv F b)(a − b)‖ ≤ M·‖a − b‖²`.

    Route (mirrors `RNCDecay.decay_order_two`): on the segment `[b,a] ⊆ S` (convexity), the
    mean-value inequality for `fderiv F` gives `‖fderiv F x − fderiv F b‖ ≤ M·‖x − b‖ ≤ M·‖a − b‖`
    (since `‖x − b‖ ≤ ‖a − b‖` on the segment), and then
    `Convex.norm_image_sub_le_of_norm_fderiv_le'` with fixed linear map `φ = fderiv F b` yields the
    quadratic bound.  The constant is the crude iterated-MVT `M` (not the sharp Taylor `M/2`). -/
theorem decay_order_two_remainder_convex {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → G) (M : ℝ) {S : Set E} (hconv : Convex ℝ S)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ F) x)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ M)
    {a b : E} (ha : a ∈ S) (hb : b ∈ S) :
    ‖F a - F b - fderiv ℝ F b (a - b)‖ ≤ M * ‖a - b‖ ^ 2 := by
  have hM : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ F) b)) (hbound2 b hb)
  have hseg : segment ℝ b a ⊆ S := hconv.segment_subset hb ha
  have hconvseg : Convex ℝ (segment ℝ b a) := convex_segment b a
  -- gradient bound on the segment: `‖fderiv F x − fderiv F b‖ ≤ M·‖a − b‖`.
  have hgrad : ∀ x ∈ segment ℝ b a, ‖fderiv ℝ F x - fderiv ℝ F b‖ ≤ M * ‖a - b‖ := by
    intro x hx
    have hxb : ‖x - b‖ ≤ ‖a - b‖ := by
      rw [segment_eq_image'] at hx
      obtain ⟨θ, hθ, rfl⟩ := hx
      have hsub : (b + θ • (a - b)) - b = θ • (a - b) := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      calc θ * ‖a - b‖ ≤ 1 * ‖a - b‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
        _ = ‖a - b‖ := one_mul _
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ F)
      (fun y hy => hdiff2 y (hseg hy)) (fun y hy => hbound2 y (hseg hy))
      hconvseg (left_mem_segment ℝ b a) hx
    exact le_trans hmvt (mul_le_mul_of_nonneg_left hxb hM)
  -- the mean-value inequality with fixed linear map `φ = fderiv F b`.
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := F) (φ := fderiv ℝ F b)
    (fun x hx => hdiff x (hseg hx)) hgrad hconvseg (left_mem_segment ℝ b a) (right_mem_segment ℝ b a)
  calc ‖F a - F b - fderiv ℝ F b (a - b)‖ ≤ M * ‖a - b‖ * ‖a - b‖ := key
    _ = M * ‖a - b‖ ^ 2 := by ring

/-- **L2b #1 — the uniform C² Taylor remainder of the geodesic field.**  On a convex set `S` where the
    second Fréchet derivative of `F = geodesicField g gi` is bounded `‖∂²F‖ ≤ M₂`, for `a, b ∈ S`:
    `‖F a − F b − DF(b)(a − b)‖ ≤ M₂·‖a − b‖²`.

    Since `F` is `C^∞` (`contDiff_geodesicField`), both differentiability facts required by
    `decay_order_two_remainder_convex` are PROVED from `hC` — the only carried input is the genuine
    geometric second-derivative bound `hbound2`.  The `v`-component of `F` is linear (2nd-order
    remainder `0`) and the `Γ(v,v)` component's 2nd-order remainder reduces to the field's C² Taylor
    remainder; here that reduction is packaged uniformly through the field-level `‖∂²F‖ ≤ M₂` bound.

    HONEST: the constant is the crude iterated-MVT `M₂` (not the sharp `M₂/2`).  This is the exact
    lemma the file header of L2a flagged as missing; it does NOT build the Jacobi equation (L2),
    Raychaudhuri (L3), or `a₁ = R/6`. -/
theorem geodesicField_uniform_C2_remainder (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hconv : Convex ℝ S) {M₂ : ℝ}
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    {a b : Point n × Point n} (ha : a ∈ S) (hb : b ∈ S) :
    ‖geodesicField g gi a - geodesicField g gi b
        - fderiv ℝ (geodesicField g gi) b (a - b)‖ ≤ M₂ * ‖a - b‖ ^ 2 := by
  have hFdiff : Differentiable ℝ (geodesicField g gi) := geodesicField_differentiable g gi hC
  have hF2diff : Differentiable ℝ (fderiv ℝ (geodesicField g gi)) :=
    ((contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top).differentiable (by simp)
  exact decay_order_two_remainder_convex (geodesicField g gi) M₂ hconv
    (fun x _ => hFdiff x) (fun x _ => hF2diff x) hbound2 ha hb

/-- **L2b #2 — discharge of L2a's carried `hNb`.**  Feeds the C² field remainder
    (`geodesicField_uniform_C2_remainder`) and the two-point flow-Lipschitz bound
    (`geodesic_twopoint_gronwall`) into the `hNb` shape of `geodesicVariation_exists`.

    Inputs (all genuine geometry): `S` convex, the field's C² bound `‖∂²F‖ ≤ M₂` on `S`, the field
    Lipschitz on `S` (`LipschitzOnWith K₀`), the geodesic ODE `hYode`, the linear IC perturbation `hIC`
    (`Y s 0 − Y 0 0 = s·(0,w)`), and the tube containment `hmem` (`Y s τ ∈ S`).  Output:
    `‖F(Y s τ) − F(Y 0 τ) − DF(Y 0 τ)(Y s τ − Y 0 τ)‖ ≤ (M₂·(‖(0,w)‖·e^{K₀})²)·s²` on `[0,1]`.

    Chain: two-point Grönwall gives `‖Y s τ − Y 0 τ‖ ≤ dist(Y s 0)(Y 0 0)·e^{K₀τ} = |s|·‖(0,w)‖·e^{K₀}`
    (using `hIC` and `τ ≤ 1`); the C² remainder gives `‖…‖ ≤ M₂·‖Y s τ − Y 0 τ‖²`; combining and using
    `|s|² = s²` yields the quadratic bound with `Cn = M₂·(‖(0,w)‖·e^{K₀})²`. -/
theorem geodesicVariation_hNb_discharge (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {w : Point n} {S : Set (Point n × Point n)}
    {M₂ : ℝ} {K₀ : NNReal} (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ)‖
        ≤ (M₂ * (‖((0, w) : Point n × Point n)‖ * Real.exp K₀) ^ 2) * s ^ 2 := by
  intro s τ hτ
  -- two-point flow-Lipschitz on `[0,1]`.
  have htp := geodesic_twopoint_gronwall g gi hLip (hYode s) (hYode 0) (hmem s) (hmem 0) τ hτ
  have hd0 : dist (Y s 0) (Y 0 0) = |s| * ‖((0, w) : Point n × Point n)‖ := by
    rw [dist_eq_norm, hIC s, norm_smul, Real.norm_eq_abs]
  have hexp : Real.exp ((K₀ : ℝ) * τ) ≤ Real.exp K₀ := by
    apply Real.exp_le_exp.mpr
    calc (K₀ : ℝ) * τ ≤ (K₀ : ℝ) * 1 := mul_le_mul_of_nonneg_left hτ.2 (NNReal.coe_nonneg K₀)
      _ = (K₀ : ℝ) := mul_one _
  have hLnn : 0 ≤ |s| * ‖((0, w) : Point n × Point n)‖ * Real.exp K₀ := by positivity
  have hL : ‖Y s τ - Y 0 τ‖ ≤ |s| * ‖((0, w) : Point n × Point n)‖ * Real.exp K₀ := by
    rw [← dist_eq_norm]
    calc dist (Y s τ) (Y 0 τ)
        ≤ dist (Y s 0) (Y 0 0) * Real.exp ((K₀ : ℝ) * τ) := htp
      _ = |s| * ‖((0, w) : Point n × Point n)‖ * Real.exp ((K₀ : ℝ) * τ) := by rw [hd0]
      _ ≤ |s| * ‖((0, w) : Point n × Point n)‖ * Real.exp K₀ :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  -- the C² remainder at the pair `(Y s τ, Y 0 τ)`.
  have hrem := geodesicField_uniform_C2_remainder g gi hC hconv hbound2 (hmem s τ hτ) (hmem 0 τ hτ)
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ)))
      (hbound2 (Y 0 τ) (hmem 0 τ hτ))
  refine hrem.trans ?_
  have hsq : ‖Y s τ - Y 0 τ‖ ^ 2
      ≤ (|s| * ‖((0, w) : Point n × Point n)‖ * Real.exp K₀) ^ 2 := by
    have := mul_le_mul hL hL (norm_nonneg _) hLnn
    simpa [pow_two] using this
  calc M₂ * ‖Y s τ - Y 0 τ‖ ^ 2
      ≤ M₂ * (|s| * ‖((0, w) : Point n × Point n)‖ * Real.exp K₀) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hnn
    _ = M₂ * (‖((0, w) : Point n × Point n)‖ * Real.exp K₀) ^ 2 * s ^ 2 := by
        have hrw : (|s| * ‖((0, w) : Point n × Point n)‖ * Real.exp K₀) ^ 2
            = s ^ 2 * (‖((0, w) : Point n × Point n)‖ * Real.exp K₀) ^ 2 := by
          rw [mul_assoc, mul_pow, sq_abs]
        rw [hrw]; ring

/-- **L2b #3 — the IC-derivative exists, with `hNb` DISCHARGED.**  The unconditional (modulo genuine
    geometric regularity) first-order smooth-dependence-on-IC: plugging the discharge
    (`geodesicVariation_hNb_discharge`) into `geodesicVariation_exists` gives
    `HasDerivAt (fun s => Y s t) (V t) 0`, carrying only the genuine geometric hypotheses — `S` convex,
    the field's C² bound `‖∂²F‖ ≤ M₂` on `S`, the field Lipschitz on `S`, the Jacobi-coefficient bound
    `‖DF(Y 0 τ)‖ ≤ K`, tube containment `Y s τ ∈ S`, and the supplied Jacobi solution `V`.

    The one analytic hypothesis L2a carried (`hNb`, the uniform quadratic field remainder) is now
    DISCHARGED from the C² remainder (`geodesicField_uniform_C2_remainder`) + the two-point Grönwall
    (`geodesic_twopoint_gronwall`), with `Cn = M₂·(‖(0,w)‖·e^{K₀})²`. -/
theorem geodesicVariation_exists_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {w : Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((0, w) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 t)))
      (hbound2 (Y 0 t) (hmem 0 t ht))
  have hCn0 : 0 ≤ M₂ * (‖((0, w) : Point n × Point n)‖ * Real.exp K₀) ^ 2 :=
    mul_nonneg hnn (sq_nonneg _)
  exact geodesicVariation_exists g gi hK0 hCn0 ht hYode hVode hV0 hIC hKb
    (geodesicVariation_hNb_discharge g gi hC hconv hbound2 hLip hYode hIC hmem)

end QIQTH.ExpMap
