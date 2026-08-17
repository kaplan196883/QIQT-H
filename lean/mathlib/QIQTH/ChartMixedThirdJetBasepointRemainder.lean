/-
  ChartMixedThirdJetBasepointRemainder — sub-brick 3b closure: the CONCRETE quadratic-in-`s`
  remainder bounds `harem`/`hbrem` for the base-perturbed geodesic family, discharging the two
  carried hypotheses of `ChartMixedThirdJetBasepoint.secondFieldJet_basepoint_hasDerivAt`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  ODE-regularity brick: the SECOND-order base-point Taylor remainder of the geodesic flow, and of a
  smooth field composed with it.  No `sorry`, no new axioms, no vacuous / unsatisfiable hypotheses,
  no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GAP CLOSED.  `secondFieldJet_basepoint_hasDerivAt` (`ChartMixedThirdJetBasepoint`, J4-828)
  is the base-point derivative `∂_q ∂²_p V` of the chart's second field-jet, but it CARRIES two
  quadratic-in-`s` remainder bounds as hypotheses:

    `harem : ‖A s τ − A 0 τ − s • Ad τ‖ ≤ Ca·s²`   with `A s τ = fderiv (geodesicField) (Y s τ)`
    `hbrem : ‖b s τ − b 0 τ − s • bd τ‖ ≤ Cb·s²`   with `b s τ = <source> (Y s τ)`

  where `Y s := <geodesic starting at q + s·u>` is the BASE-perturbed geodesic family and `s` the base
  perturbation parameter.  Both are second-order Taylor remainders of a smooth function COMPOSED with
  the base-perturbed geodesic family — i.e. the near-C² dependence of `Y s` on `s`.  This file supplies
  them concretely, mirroring `GeodesicSmoothDep.geodesicVariation_hNb_discharge` (the FIRST-order
  base-remainder discharge) ONE ORDER UP.

  ── DESIGN NOTE (why the Lipschitz form of the second-derivative bound).  The sharp second-order
  Taylor remainder of `Φ = fderiv F` would name `‖∂³F‖` — a norm on the TRIPLE-nested continuous-linear
  space, whose `NormedAddCommGroup` instance Mathlib does not synthesise (a known module/norm diamond).
  We sidestep it: the general remainder lemma `decay_order_two_remainder_lipschitz` takes a
  `LipschitzOnWith` bound on `fderiv Φ` (which for `Φ = fderiv F` is `∂²F`, a DOUBLE-nested space that
  IS normed) — equivalent geometric content, no triple norm anywhere.  `∂²F` Lipschitz on a compact
  convex region is the standard smooth-metric fact (satisfiable, not vacuous, not the conclusion),
  carried exactly as `geodesicVariation_hNb_discharge` carries `hbound2`.

  ## WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axiom, no existing file edited):

  * `decay_order_two_remainder_lipschitz` — **general convex second-order Taylor remainder from a
    Lipschitz first-derivative.**  `‖Φ a − Φ b − DΦ(b)(a−b)‖ ≤ K·‖a−b‖²`, where `K` is the Lipschitz
    constant of `fderiv Φ` on the convex `S`.  Mirrors `decay_order_two_remainder_convex` but avoids the
    triple norm.

  * `compose_secondOrder_remainder_pt` — **general pointwise engine.**
        `‖Φ a − Φ b − DΦ(b) v‖ ≤ K·‖a − b‖² + M₁·‖a − b − v‖`
    (`K = Lip(fderiv Φ)`, `M₁ = sup ‖∂Φ‖`), via the above + operator-norm on the linearisation defect.

  * `family_secondOrder_remainder` — **s-parametrised specialisation (the `harem`/`hbrem` shape).**
    From `‖Y s τ − Y 0 τ‖ ≤ L·|s|` and `‖Y s τ − Y 0 τ − s • J τ‖ ≤ Cy·s²`:
        `‖Φ(Y s τ) − Φ(Y 0 τ) − s • (DΦ(Y 0 τ)(J τ))‖ ≤ (K·L² + M₁·Cy)·s²`.

  * `geodesicFlow_secondOrder_base_remainder` — ★ **THE key new ODE fact: the geodesic flow's C² base
    dependence.**  `‖Y s τ − Y 0 τ − s • J τ‖ ≤ (M₂·L²·exp K)·s²`, from `linODE_twopoint_diff_bound`
    applied to `Y s` (nonlinear geodesic ODE, re-expressed with the frozen Jacobi coefficient
    `A₀ τ = DF(Y 0 τ)`) vs the linear approximant `Y 0 + s • J`, whose source difference is the field's
    C² Taylor remainder `≤ M₂·‖Y s τ − Y 0 τ‖² ≤ M₂·L²·s²`.  This is `geodesicVariation_hNb_discharge`
    one order up: the SECOND base variation, not just first.

  * `secondFieldJet_harem_discharge` — **`harem` discharged concretely** (`Φ = fderiv (geodesicField)`).
  * `source_hbrem_discharge` — **`hbrem` discharged concretely** for a source `b s τ = φ(Y s τ)`, `φ` C².
  * `secondFieldJet_basepoint_hasDerivAt_remaindersDischarged` — **the wired capstone**: plugs both
    discharges into `secondFieldJet_basepoint_hasDerivAt`, giving `∂_q ∂²_p V = R t` with `harem`/`hbrem`
    REPLACED by standard geometric/ODE data; only the SECOND FIELD-JET's own ODE data remains.

  HONEST CHECKPOINT (binding).  This closes the two quadratic-in-`s` remainder walls (`harem`, `hbrem`)
  of sub-brick 3b, reducing them to the geodesic flow's genuine C² base dependence (proved here by
  Grönwall) plus standard smooth-field bounds.  It does NOT build the second-field-jet's own variational
  equation (`hR`), NOT the Fréchet (all-direction) upgrade, NOT the wiring to the concrete
  `uniformInverseChart`/`uniformFlowExp`, NOT `hCConv`, NOT Raychaudhuri, NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GeodesicSmoothDep
import QIQTH.BasepointJetModulus
import QIQTH.ChartMixedThirdJetBasepoint

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **General convex second-order Taylor remainder from a Lipschitz first derivative.**  If `Φ : E → G`
    is differentiable on a convex `S` and `fderiv Φ` is `LipschitzOnWith K` there, then for `a, b ∈ S`:
    `‖Φ a − Φ b − DΦ(b)(a − b)‖ ≤ K·‖a − b‖²`.

    Mirrors `decay_order_two_remainder_convex` but takes the Lipschitz constant of `fderiv Φ` directly,
    so it never names `∂²Φ` (avoiding the triple-nested-CLM norm diamond).  Route: on `[b,a] ⊆ S`,
    `‖DΦ(x) − DΦ(b)‖ = dist(DΦ x, DΦ b) ≤ K·dist(x,b) = K·‖x − b‖ ≤ K·‖a − b‖`, then
    `Convex.norm_image_sub_le_of_norm_fderiv_le'` with fixed `φ = DΦ(b)`.  NOT `a₁ = R/6`. -/
theorem decay_order_two_remainder_lipschitz {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Φ : E → G) {S : Set E} (hconv : Convex ℝ S)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ Φ x)
    {K : NNReal} (hlip : LipschitzOnWith K (fderiv ℝ Φ) S)
    {a b : E} (ha : a ∈ S) (hb : b ∈ S) :
    ‖Φ a - Φ b - fderiv ℝ Φ b (a - b)‖ ≤ (K : ℝ) * ‖a - b‖ ^ 2 := by
  have hseg : segment ℝ b a ⊆ S := hconv.segment_subset hb ha
  have hconvseg : Convex ℝ (segment ℝ b a) := convex_segment b a
  have hgrad : ∀ x ∈ segment ℝ b a, ‖fderiv ℝ Φ x - fderiv ℝ Φ b‖ ≤ (K : ℝ) * ‖a - b‖ := by
    intro x hx
    have hxS := hseg hx
    have hxb : ‖x - b‖ ≤ ‖a - b‖ := by
      rw [segment_eq_image'] at hx
      obtain ⟨θ, hθ, rfl⟩ := hx
      have hsub : (b + θ • (a - b)) - b = θ • (a - b) := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      calc θ * ‖a - b‖ ≤ 1 * ‖a - b‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
        _ = ‖a - b‖ := one_mul _
    have hd := hlip.dist_le_mul x hxS b hb
    rw [dist_eq_norm, dist_eq_norm] at hd
    calc ‖fderiv ℝ Φ x - fderiv ℝ Φ b‖ ≤ (K : ℝ) * ‖x - b‖ := hd
      _ ≤ (K : ℝ) * ‖a - b‖ := mul_le_mul_of_nonneg_left hxb (NNReal.coe_nonneg K)
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := Φ) (φ := fderiv ℝ Φ b)
    (fun x hx => hdiff x (hseg hx)) hgrad hconvseg (left_mem_segment ℝ b a) (right_mem_segment ℝ b a)
  calc ‖Φ a - Φ b - fderiv ℝ Φ b (a - b)‖ ≤ (K : ℝ) * ‖a - b‖ * ‖a - b‖ := key
    _ = (K : ℝ) * ‖a - b‖ ^ 2 := by ring

/-- **General pointwise second-order composition remainder.**
        `‖Φ a − Φ b − DΦ(b) v‖ ≤ K·‖a − b‖² + M₁·‖a − b − v‖`
    (`K = Lip(fderiv Φ)`, `M₁ = sup ‖∂Φ‖` on `S`).  Split
    `Φ a − Φ b − DΦ(b)v = (Φ a − Φ b − DΦ(b)(a−b)) + DΦ(b)(a − b − v)`; the first piece is
    `decay_order_two_remainder_lipschitz`, the second `≤ M₁·‖a − b − v‖` by the operator norm.
    NOT `a₁ = R/6`. -/
theorem compose_secondOrder_remainder_pt {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Φ : E → G) {S : Set E} (hconv : Convex ℝ S)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ Φ x)
    {K : NNReal} (hlip : LipschitzOnWith K (fderiv ℝ Φ) S)
    {M₁ : ℝ} (hM1 : ∀ x ∈ S, ‖fderiv ℝ Φ x‖ ≤ M₁)
    {a b : E} (ha : a ∈ S) (hb : b ∈ S) (v : E) :
    ‖Φ a - Φ b - fderiv ℝ Φ b v‖ ≤ (K : ℝ) * ‖a - b‖ ^ 2 + M₁ * ‖a - b - v‖ := by
  have hlin : fderiv ℝ Φ b (a - b - v) = fderiv ℝ Φ b (a - b) - fderiv ℝ Φ b v := map_sub _ _ _
  have key : Φ a - Φ b - fderiv ℝ Φ b v
      = (Φ a - Φ b - fderiv ℝ Φ b (a - b)) + fderiv ℝ Φ b (a - b - v) := by
    rw [hlin]; abel
  rw [key]
  refine (norm_add_le _ _).trans ?_
  have h1 := decay_order_two_remainder_lipschitz Φ hconv hdiff hlip ha hb
  have h2 : ‖fderiv ℝ Φ b (a - b - v)‖ ≤ M₁ * ‖a - b - v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM1 b hb) (norm_nonneg _))
  exact add_le_add h1 h2

/-- **s-parametrised second-order composition remainder — the `harem`/`hbrem` shape.**  Given the
    base family's first-order Lipschitz bound `‖Y s τ − Y 0 τ‖ ≤ L·|s|` and second-order base remainder
    `‖Y s τ − Y 0 τ − s • J τ‖ ≤ Cy·s²`:
        `‖Φ(Y s τ) − Φ(Y 0 τ) − s • (DΦ(Y 0 τ)(J τ))‖ ≤ (K·L² + M₁·Cy)·s²`,
    exactly the `harem` binder with `A s τ = Φ(Y s τ)` and `Ad τ = DΦ(Y 0 τ)(J τ)`.  NOT `a₁ = R/6`. -/
theorem family_secondOrder_remainder {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Φ : E → G) {S : Set E} (hconv : Convex ℝ S)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ Φ x)
    {K : NNReal} (hlip : LipschitzOnWith K (fderiv ℝ Φ) S)
    {M₁ L Cy : ℝ} (hM1 : ∀ x ∈ S, ‖fderiv ℝ Φ x‖ ≤ M₁)
    {Y : ℝ → ℝ → E} {J : ℝ → E} {τ : ℝ}
    (hYs : ∀ s : ℝ, Y s τ ∈ S) (hY0 : Y 0 τ ∈ S)
    (hL : ∀ s : ℝ, ‖Y s τ - Y 0 τ‖ ≤ L * |s|)
    (hCy : ∀ s : ℝ, ‖Y s τ - Y 0 τ - s • J τ‖ ≤ Cy * s ^ 2)
    (s : ℝ) :
    ‖Φ (Y s τ) - Φ (Y 0 τ) - s • (fderiv ℝ Φ (Y 0 τ) (J τ))‖
      ≤ ((K : ℝ) * L ^ 2 + M₁ * Cy) * s ^ 2 := by
  have hsmul : fderiv ℝ Φ (Y 0 τ) (s • J τ) = s • (fderiv ℝ Φ (Y 0 τ) (J τ)) := map_smul _ _ _
  have hpt := compose_secondOrder_remainder_pt Φ hconv hdiff hlip hM1 (hYs s) hY0 (s • J τ)
  rw [hsmul] at hpt
  refine hpt.trans ?_
  have hM10 : 0 ≤ M₁ := le_trans (norm_nonneg (fderiv ℝ Φ (Y 0 τ))) (hM1 _ hY0)
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := NNReal.coe_nonneg K
  have hLs := hL s
  have hLnn : 0 ≤ L * |s| := le_trans (norm_nonneg _) hLs
  have hsq : ‖Y s τ - Y 0 τ‖ ^ 2 ≤ L ^ 2 * s ^ 2 := by
    have hmm := mul_le_mul hLs hLs (norm_nonneg _) hLnn
    calc ‖Y s τ - Y 0 τ‖ ^ 2 = ‖Y s τ - Y 0 τ‖ * ‖Y s τ - Y 0 τ‖ := by ring
      _ ≤ (L * |s|) * (L * |s|) := hmm
      _ = L ^ 2 * s ^ 2 := by rw [← sq_abs s]; ring
  calc (K : ℝ) * ‖Y s τ - Y 0 τ‖ ^ 2 + M₁ * ‖Y s τ - Y 0 τ - s • J τ‖
      ≤ (K : ℝ) * (L ^ 2 * s ^ 2) + M₁ * (Cy * s ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hsq hK0)
          (mul_le_mul_of_nonneg_left (hCy s) hM10)
    _ = ((K : ℝ) * L ^ 2 + M₁ * Cy) * s ^ 2 := by ring

/-- ★ **The geodesic flow's C² base dependence — the second base variation.**  The base residual
    `ρ s τ = Y s τ − Y 0 τ − s • J τ` (`J` the base-Jacobi field, `J 0 = (0,w)`) is quadratic in `s`:
        `‖Y s τ − Y 0 τ − s • J τ‖ ≤ (M₂·L²·exp K)·s²`.
    `Y s` solves the nonlinear geodesic ODE; re-expressed with the frozen coefficient
    `A₀ τ = DF(Y 0 τ)` it is a linear ODE with source `b₁ = F(Y s ·) − A₀·(Y s ·)`, and the linear
    approximant `Y 0 + s • J` has source `b₂ = F(Y 0 ·) − A₀·(Y 0 ·)`.  Same coefficient (`Dcoef = 0`),
    equal seeds (`hseed`+`hJ0`), and source difference
    `b₁ − b₂ = F(Y s ·) − F(Y 0 ·) − DF(Y 0 ·)(Y s · − Y 0 ·)` — the field's C² Taylor remainder,
    `≤ M₂·‖Y s τ − Y 0 τ‖² ≤ M₂·L²·s²`.  `linODE_twopoint_diff_bound` then gives the result.
    This is `geodesicVariation_hNb_discharge` one order up.  NOT `a₁ = R/6`. -/
theorem geodesicFlow_secondOrder_base_remainder (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {J : ℝ → Point n × Point n} {w : Point n}
    {S : Set (Point n × Point n)} {M₂ K L Yb Jb : ℝ} (hK0 : 0 ≤ K)
    (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y 0 τ) (J τ)) τ)
    (hseed : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hJ0 : J 0 = ((0, w) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S)
    (hL : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y s τ - Y 0 τ‖ ≤ L * |s|)
    (hYb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y 0 τ‖ ≤ Yb)
    (hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ Jb) :
    ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Y s τ - Y 0 τ - s • J τ‖ ≤ (M₂ * L ^ 2 * Real.exp K) * s ^ 2 := by
  intro s τ hτ
  set A0 : ℝ → ((Point n × Point n) →L[ℝ] Point n × Point n) :=
    fun τ => fderiv ℝ (geodesicField g gi) (Y 0 τ) with hA0def
  set X2 : ℝ → Point n × Point n := fun τ => Y 0 τ + s • J τ with hX2def
  set b1 : ℝ → Point n × Point n := fun τ => geodesicField g gi (Y s τ) - A0 τ (Y s τ) with hb1def
  set b2 : ℝ → Point n × Point n := fun τ => geodesicField g gi (Y 0 τ) - A0 τ (Y 0 τ) with hb2def
  have hX1' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Y s) (A0 τ (Y s τ) + b1 τ) τ := by
    intro τ hτ
    have hv : A0 τ (Y s τ) + b1 τ = geodesicField g gi (Y s τ) := by simp only [hb1def]; abel
    rw [hv]; exact hYode s τ hτ
  have hX2' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt X2 (A0 τ (X2 τ) + b2 τ) τ := by
    intro τ hτ
    have hd : HasDerivAt X2 (geodesicField g gi (Y 0 τ) + s • (A0 τ (J τ))) τ :=
      (hYode 0 τ hτ).add ((hJode τ hτ).const_smul s)
    have hv : geodesicField g gi (Y 0 τ) + s • (A0 τ (J τ)) = A0 τ (X2 τ) + b2 τ := by
      simp only [hX2def, hb2def, map_add, map_smul]
      abel
    rwa [hv] at hd
  have h0 : Y s 0 = X2 0 := by
    simp only [hX2def, hJ0]
    have := hseed s; rw [sub_eq_iff_eq_add] at this; rw [this]; abel
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ)))
      (hbound2 (Y 0 τ) (hmem 0 τ hτ))
  have hbd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖b1 τ - b2 τ‖ ≤ M₂ * L ^ 2 * s ^ 2 := by
    intro τ hτ
    have hsplit : b1 τ - b2 τ
        = geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ) := by
      simp only [hb1def, hb2def, hA0def, map_sub]
      abel
    rw [hsplit]
    have hrem := geodesicField_uniform_C2_remainder g gi hC hconv hbound2
      (hmem s τ hτ) (hmem 0 τ hτ)
    refine hrem.trans ?_
    have hLs := hL s τ hτ
    have hLsnn : 0 ≤ L * |s| := le_trans (norm_nonneg _) hLs
    have hsq : ‖Y s τ - Y 0 τ‖ ^ 2 ≤ L ^ 2 * s ^ 2 := by
      have hmm := mul_le_mul hLs hLs (norm_nonneg _) hLsnn
      calc ‖Y s τ - Y 0 τ‖ ^ 2 = ‖Y s τ - Y 0 τ‖ * ‖Y s τ - Y 0 τ‖ := by ring
        _ ≤ (L * |s|) * (L * |s|) := hmm
        _ = L ^ 2 * s ^ 2 := by rw [← sq_abs s]; ring
    calc M₂ * ‖Y s τ - Y 0 τ‖ ^ 2 ≤ M₂ * (L ^ 2 * s ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hnn
      _ = M₂ * L ^ 2 * s ^ 2 := by ring
  have hX2b : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X2 τ‖ ≤ Yb + |s| * Jb := by
    intro τ hτ
    simp only [hX2def]
    refine (norm_add_le _ _).trans (add_le_add (hYb τ hτ) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hJb τ hτ) (abs_nonneg _)
  have hmain := linODE_twopoint_diff_bound (E := Point n × Point n)
    (A₁ := A0) (A₂ := A0) (X₁ := Y s) (X₂ := X2) (b₁ := b1) (b₂ := b2)
    (K := K) (Dcoef := 0) (Xb := Yb + |s| * Jb) (Dsrc := M₂ * L ^ 2 * s ^ 2)
    hK0 hX1' hX2' h0 hKb (fun τ _ => by simp) hX2b hbd
  have := hmain τ hτ
  rw [zero_mul, zero_add] at this
  have hXt : Y s τ - X2 τ = Y s τ - Y 0 τ - s • J τ := by simp only [hX2def]; abel
  rw [hXt] at this
  have heq : M₂ * L ^ 2 * s ^ 2 * Real.exp K = M₂ * L ^ 2 * Real.exp K * s ^ 2 := by ring
  rwa [heq] at this

/-- **`harem` discharged concretely.**  Specialises `family_secondOrder_remainder` at
    `Φ = fderiv (geodesicField g gi)`, with the second-order base remainder `Cy = M₂·L²·exp K` supplied
    by `geodesicFlow_secondOrder_base_remainder`.  `Φ` is C^∞, so `fderiv Φ = ∂²F` is Lipschitz on the
    convex compact region (constant `Kl`, carried); `‖fderiv Φ‖ = ‖∂²F‖ ≤ M₂` is `hbound2`.  Produces
    exactly the `harem` binder — `A s τ = fderiv (geodesicField) (Y s τ)`,
    `Ad τ = fderiv (fderiv (geodesicField)) (Y 0 τ) (J τ)`.  NOT `a₁ = R/6`. -/
theorem secondFieldJet_harem_discharge (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {J : ℝ → Point n × Point n} {w : Point n}
    {S : Set (Point n × Point n)} {M₂ K L Yb Jb : ℝ} {Kl : NNReal} (hK0 : 0 ≤ K)
    (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hlip2 : LipschitzOnWith Kl (fderiv ℝ (fderiv ℝ (geodesicField g gi))) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y 0 τ) (J τ)) τ)
    (hseed : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hJ0 : J 0 = ((0, w) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S)
    (hL : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y s τ - Y 0 τ‖ ≤ L * |s|)
    (hYb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y 0 τ‖ ≤ Yb)
    (hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ Jb)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ s : ℝ,
      ‖fderiv ℝ (geodesicField g gi) (Y s τ) - fderiv ℝ (geodesicField g gi) (Y 0 τ)
          - s • (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ) (J τ))‖
        ≤ ((Kl : ℝ) * L ^ 2 + M₂ * (M₂ * L ^ 2 * Real.exp K)) * s ^ 2 := by
  have hDF : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top
  have hdiff : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ (geodesicField g gi)) x :=
    fun x _ => (hDF.differentiable (by simp)) x
  have hCyall := geodesicFlow_secondOrder_base_remainder g gi hC hK0 hconv hbound2
    hYode hJode hseed hJ0 hKb hmem hL hYb hJb
  intro s
  exact family_secondOrder_remainder (fderiv ℝ (geodesicField g gi)) hconv hdiff hlip2
    hbound2 (fun s => hmem s τ hτ) (hmem 0 τ hτ)
    (fun s => hL s τ hτ) (fun s => hCyall s τ hτ) s

/-- **`hbrem` discharged concretely** for a source of the shape `b s τ = φ(Y s τ)` with `φ` C² (any
    smooth field of the flow — e.g. the second-jet curvature source).  Same specialisation of
    `family_secondOrder_remainder` at `Φ = φ`, with `Cy` from `geodesicFlow_secondOrder_base_remainder`.
    Produces the `hbrem` binder with `bd τ = fderiv φ (Y 0 τ) (J τ)`.  NOT `a₁ = R/6`. -/
theorem source_hbrem_discharge (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (φ : Point n × Point n → Point n × Point n)
    {Y : ℝ → ℝ → Point n × Point n} {J : ℝ → Point n × Point n} {w : Point n}
    {S : Set (Point n × Point n)} {M₂ Mφ1 K L Yb Jb : ℝ} {Kφ : NNReal} (hK0 : 0 ≤ K)
    (hconv : Convex ℝ S)
    (hφdiff : ∀ x ∈ S, DifferentiableAt ℝ φ x)
    (hφlip : LipschitzOnWith Kφ (fderiv ℝ φ) S)
    (hφb1 : ∀ x ∈ S, ‖fderiv ℝ φ x‖ ≤ Mφ1)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y 0 τ) (J τ)) τ)
    (hseed : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hJ0 : J 0 = ((0, w) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S)
    (hL : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y s τ - Y 0 τ‖ ≤ L * |s|)
    (hYb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y 0 τ‖ ≤ Yb)
    (hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ Jb)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ s : ℝ,
      ‖φ (Y s τ) - φ (Y 0 τ) - s • (fderiv ℝ φ (Y 0 τ) (J τ))‖
        ≤ ((Kφ : ℝ) * L ^ 2 + Mφ1 * (M₂ * L ^ 2 * Real.exp K)) * s ^ 2 := by
  have hCyall := geodesicFlow_secondOrder_base_remainder g gi hC hK0 hconv hbound2
    hYode hJode hseed hJ0 hKb hmem hL hYb hJb
  intro s
  exact family_secondOrder_remainder φ hconv hφdiff hφlip hφb1
    (fun s => hmem s τ hτ) (hmem 0 τ hτ)
    (fun s => hL s τ hτ) (fun s => hCyall s τ hτ) s

/-- **The wired capstone — `∂_q ∂²_p V` with `harem`/`hbrem` DISCHARGED.**  Plugs the two concrete
    remainder discharges into `secondFieldJet_basepoint_hasDerivAt` (source shape `b s τ = φ(Y s τ)`).
    The base-point derivative of the second field-jet EXISTS and equals `R t`:
        `HasDerivAt (fun s => X s t) (R t) 0`,
    with the two quadratic-in-`s` remainder walls REPLACED by standard geometric/ODE data (field ∂²
    bound + ∂² Lipschitz, source-field C² data, first-order Lipschitz, Jacobi ODE, seed, containment).
    The remaining hypotheses are exactly the SECOND FIELD-JET's own ODE data (`hX`, `hR`, seed, bounds)
    — NOT `harem`/`hbrem`.  NOT `a₁ = R/6`. -/
theorem secondFieldJet_basepoint_hasDerivAt_remaindersDischarged
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (φ : Point n × Point n → Point n × Point n)
    {Y : ℝ → ℝ → Point n × Point n} {J : ℝ → Point n × Point n} {w : Point n}
    {X : ℝ → ℝ → Point n × Point n} {R : ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ Mφ1 K L Yb Jb Kad Xb Lx Rb : ℝ} {Kl Kφ : NNReal}
    (hK0 : 0 ≤ K) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hlip2 : LipschitzOnWith Kl (fderiv ℝ (fderiv ℝ (geodesicField g gi))) S)
    (hφdiff : ∀ x ∈ S, DifferentiableAt ℝ φ x)
    (hφlip : LipschitzOnWith Kφ (fderiv ℝ φ) S)
    (hφb1 : ∀ x ∈ S, ‖fderiv ℝ φ x‖ ≤ Mφ1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y 0 τ) (J τ)) τ)
    (hseed : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hJ0 : J 0 = ((0, w) : Point n × Point n))
    (hKbY : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S)
    (hLY : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y s τ - Y 0 τ‖ ≤ L * |s|)
    (hYb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y 0 τ‖ ≤ Yb)
    (hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ Jb)
    -- the SECOND FIELD-JET's own ODE data (carried — NOT harem/hbrem):
    (hX : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (X s)
        (fderiv ℝ (geodesicField g gi) (Y s τ) (X s τ) + φ (Y s τ)) τ)
    (hR : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt R
        (fderiv ℝ (geodesicField g gi) (Y 0 τ) (R τ)
          + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ) (J τ) (X 0 τ)
            + fderiv ℝ φ (Y 0 τ) (J τ))) τ)
    (hseedX : ∀ s : ℝ, X s 0 - X 0 0 = s • R 0)
    (hXb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ‖ ≤ Xb)
    (hXlip : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ - X 0 τ‖ ≤ Lx * |s|)
    (hRb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖R τ‖ ≤ Rb)
    (hKad : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ) (J τ)‖ ≤ Kad)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => X s t) (R t) 0 := by
  refine secondFieldJet_basepoint_hasDerivAt g gi
    (Y := Y)
    (Ad := fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ) (J τ))
    (X := X) (b := fun s τ => φ (Y s τ))
    (bd := fun τ => fderiv ℝ φ (Y 0 τ) (J τ)) (R := R)
    (K := K) (Ca := (Kl : ℝ) * L ^ 2 + M₂ * (M₂ * L ^ 2 * Real.exp K))
    (Cb := (Kφ : ℝ) * L ^ 2 + Mφ1 * (M₂ * L ^ 2 * Real.exp K))
    (Xb := Xb) (Kad := Kad) (Lx := Lx) (Rb := Rb) hK0 hX hR hseedX hKbY ?harem hKad hXb hXlip hRb
    ?hbrem ht
  case harem =>
    intro s τ hτ
    exact secondFieldJet_harem_discharge g gi hC hK0 hconv hbound2 hlip2 hYode hJode hseed hJ0
      hKbY hmem hLY hYb hJb hτ s
  case hbrem =>
    intro s τ hτ
    exact source_hbrem_discharge g gi hC φ hK0 hconv hφdiff hφlip hφb1 hbound2 hYode hJode hseed hJ0
      hKbY hmem hLY hYb hJb hτ s

end QIQTH.ExpMap
