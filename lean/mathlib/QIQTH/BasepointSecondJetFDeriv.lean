/-
  BasepointSecondJetFDeriv — J4-28 (brick 1 toward `hunif`): the BASE-POINT SECOND-ORDER JET of the
  geodesic endpoint map, in Taylor form, with the LINEAR term IDENTIFIED as the first-order Jacobi
  endpoint field.

  ODE_VARIATIONAL_PLAN.md, Phase J-d.  The base-point smooth-dependence campaign is reduced
  (J4-26, `BasepointSecondJet`) to the SINGLE input `hunif` — the base-point uniform modulus of the
  velocity 2-jet of the CONCRETE exp map `expMap g gi hC q`:
      `∀ ε>0 ∃ δ>0 ∀ q q'∈K, dist q q' < δ → ∀ v∈B̄(0,r),
          |‖fderiv²(exp_q) v‖ − ‖fderiv²(exp_{q'}) v‖| ≤ ε`.
  The route to `hunif` runs through the base-point SECOND-order jet of the endpoint map `δ ↦ W δ t`.

  ## What the mission clarified (binding)

  The endpoint FIRST-order Jacobi map `δ ↦ V δ t` is LINEAR (`jacobiSol_unique`, J-c), so ITS Fréchet
  derivative is constant (`= L`) and its "second jet" is trivially `0`.  The genuine SECOND-order content
  is therefore NOT a jet of `δ ↦ V δ t`; it is the SECOND-order Taylor expansion of the ENDPOINT map
  `δ ↦ W δ t` beyond its linear part `L δ = V δ t`:
      `‖W δ t − W 0 t − V δ t − ½·B(δ,δ)‖ ≤ M·‖δ‖³`,   `B = D²(δ↦W δ t)|₀` bilinear.
  This is the base-point analogue of J-c one Fréchet order up (J-c produced the QUADRATIC endpoint
  remainder `‖W δ t − W 0 t − V δ t‖ ≤ C·‖δ‖²`; this file produces the CUBIC one with the quadratic
  Jacobi-jet term made explicit).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `geodesicBasepoint_endpoint_secondOrder_taylor` — the base-point SECOND-ORDER Taylor expansion of
    the geodesic endpoint map at the base point, with cubic remainder:
        `‖W δ t − W 0 t − V δ t − ½·(D²(δ'↦W δ' t)|₀ δ) δ‖ ≤ M·‖δ‖³`.
    DERIVED by welding TWO landed results:
      (i)  `DecayOrderThree.decay_order_three_remainder_convex` (the just-landed cubic vector-valued
           Taylor remainder on a convex set) applied to `F := (δ' ↦ W δ' t)`, `a := δ`, `b := 0`, and
      (ii) `BasepointFDeriv.geodesicBasepoint_endpoint_hasFDerivAt_exists` (J-c) — which supplies the
           continuous-linear endpoint Jacobi map `L` with `L δ = V δ t` and `HasFDerivAt (δ'↦W δ' t) L 0`
           — via `HasFDerivAt.fderiv` to IDENTIFY the analytic linear term `D(δ'↦W δ' t)|₀ δ` with the
           GEODESIC first-order Jacobi endpoint field `V δ t`.
    So the analysis lemma does the Taylor bookkeeping and the ODE (J-c) fixes the linear term as the
    Jacobi field.  The quadratic term `B = D²(δ'↦W δ' t)|₀` is the base-point second-order jet's
    bilinear form.

  * `geodesicBasepoint_endpoint_position_secondOrder_taylor` — the exp-map-shaped POSITION-component
    projection: same expansion for `(W δ t).1` with linear term `(V δ t).1` and quadratic term the
    position part of `B`.  At `t = 1` this is the base-point (`q`-side) second-order Taylor of the
    exp-map-shaped geodesic endpoint POSITION for a confined tube family.

  DERIVED vs CARRIED.  DERIVED = the Taylor weld (i)+(ii).  CARRIED genuine inputs:
    * the SAME geometric-regularity bundle J-c carries (`S` convex, C² field bound, field Lipschitz,
      Jacobi-coefficient bound, tube containment, the supplied Jacobi solutions `V δ`) — used ONLY to
      obtain, via J-c, that the analytic linear term equals the Jacobi field `V δ t`;
    * the base-point (`δ`-side) C² regularity of the endpoint map `δ' ↦ W δ' t` on a convex
      neighbourhood `Sδ` of `0` — differentiability, second differentiability, base-point symmetry, and
      the quantitative second-derivative Lipschitz constant `M` — the honest analogue of the PROVEN
      concrete regularity `expMap g gi hC q ∈ C⁴` (`ExpMapContDiffFour`), carried here for the abstract
      confined tube family exactly as the C² field bound is carried on the state side.
  The conclusion (a cubic Taylor bound with the Jacobi linear term) is NOT among the hypotheses.

  HONEST CHECKPOINT (binding).  This lands the base-point SECOND-order endpoint jet in Taylor form
  (J-d, brick 1).  It does NOT yet build: the base-point continuity/Lipschitz-in-`q` of that jet UNIFORM
  in the velocity direction; the uniform bound over `K × B̄`; `hunif`; the concrete-`expMap` weld through
  the opaque per-`q` `Classical.choose` tube; Raychaudhuri (L3); `a₁ = R/6`.
-/
import QIQTH.BasepointFDeriv
import QIQTH.BasepointJacobi2
import QIQTH.DecayOrderThree
import QIQTH.BasepointSecondJet
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **J4-28 (brick 1) — base-point SECOND-ORDER Taylor expansion of the geodesic endpoint map, with the
    linear term identified as the first-order Jacobi endpoint field.**

    For a base-point-perturbation-indexed family `W : Point n → ℝ → State` of geodesics
    (`W δ 0 − W 0 0 = (δ,0)`, fixed velocity) with Jacobi solutions `V δ` along the base geodesic `W 0`
    (`V δ 0 = (δ,0)`), and given the base-point (`δ`-side) C² regularity of the endpoint map
    `δ' ↦ W δ' t` on a convex neighbourhood `Sδ ∋ 0` (differentiability `hEdiff`, second
    differentiability `hEdiff2`, base-point symmetry `hEsymm`, second-derivative Lipschitz constant `M`
    `hElip2`), the endpoint map obeys the base-point SECOND-order Taylor expansion with cubic remainder:
        `‖W δ t − W 0 t − V δ t − ½·(D²(δ'↦W δ' t)|₀ δ) δ‖ ≤ M·‖δ‖³`.

    DERIVED by welding `DecayOrderThree.decay_order_three_remainder_convex` (cubic Taylor remainder,
    applied at `a = δ`, `b = 0`) with `geodesicBasepoint_endpoint_hasFDerivAt_exists` (J-c): the latter's
    `HasFDerivAt (δ'↦W δ' t) L 0` gives `D(δ'↦W δ' t)|₀ = L` (`HasFDerivAt.fderiv`), and `L δ = V δ t`
    identifies the analytic linear term with the geodesic first-order Jacobi endpoint field.  The
    quadratic coefficient `D²(δ'↦W δ' t)|₀` is the base-point second-order jet's bilinear form. -/
theorem geodesicBasepoint_endpoint_secondOrder_taylor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {Sδ : Set (Point n)} {M₂ K M : ℝ} {K₀ : NNReal}
    (hK0 : 0 ≤ K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hconv : Convex ℝ S) (hconvδ : Convex ℝ Sδ)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S)
    (hEdiff : ∀ x ∈ Sδ, DifferentiableAt ℝ (fun d => W d t) x)
    (hEdiff2 : ∀ x ∈ Sδ, DifferentiableAt ℝ (fderiv ℝ (fun d => W d t)) x)
    (hElip2 : ∀ z ∈ Sδ,
      ‖fderiv ℝ (fderiv ℝ (fun d => W d t)) z - fderiv ℝ (fderiv ℝ (fun d => W d t)) 0‖
        ≤ M * ‖z - 0‖)
    (hEsymm : IsSymmSndFDerivAt ℝ (fun d => W d t) 0)
    {δ : Point n} (hδmem : δ ∈ Sδ) (h0mem : (0 : Point n) ∈ Sδ) :
    ‖W δ t - W 0 t - V δ t
        - (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ (fun d => W d t)) 0 δ) δ‖ ≤ M * ‖δ‖ ^ 3 := by
  -- (i) cubic Taylor remainder of the endpoint map at `a = δ`, `b = 0`.
  have hlem := decay_order_three_remainder_convex (fun d => W d t) M hconvδ
    hEdiff hEdiff2 hElip2 hδmem h0mem hEsymm
  simp only [sub_zero] at hlem
  -- (ii) J-c: the analytic linear term equals the first-order Jacobi endpoint field `V δ t`.
  obtain ⟨L, hLeq, hFD⟩ := geodesicBasepoint_endpoint_hasFDerivAt_exists g gi hC hK0 ht hconv
    hbound2 hLip hWode hVode hV0 hIC hKb hmem
  have hfd0 : fderiv ℝ (fun d => W d t) 0 = L := hFD.fderiv
  rw [hfd0, hLeq δ] at hlem
  exact hlem

/-- **J4-28 (brick 1, position component) — the exp-map-shaped base-point second-order Taylor expansion
    of the geodesic endpoint POSITION.**  Projecting the endpoint second-order Taylor expansion onto the
    position component: with linear term the Jacobi position field `(V δ t).1` and quadratic coefficient
    the position part of the base-point second-order bilinear jet,
        `‖(W δ t).1 − (W 0 t).1 − (V δ t).1 − ½·((D²(δ'↦W δ' t)|₀ δ) δ).1‖ ≤ M·‖δ‖³`.
    At `t = 1` this is the base-point (`q`-side) second-order Taylor expansion of the exp-map-shaped
    geodesic-endpoint position for a confined tube family — the shape whose base-point modulus, uniform
    in the velocity direction, is the residual `hunif`. -/
theorem geodesicBasepoint_endpoint_position_secondOrder_taylor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {Sδ : Set (Point n)} {M₂ K M : ℝ} {K₀ : NNReal}
    (hK0 : 0 ≤ K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hconv : Convex ℝ S) (hconvδ : Convex ℝ Sδ)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S)
    (hEdiff : ∀ x ∈ Sδ, DifferentiableAt ℝ (fun d => W d t) x)
    (hEdiff2 : ∀ x ∈ Sδ, DifferentiableAt ℝ (fderiv ℝ (fun d => W d t)) x)
    (hElip2 : ∀ z ∈ Sδ,
      ‖fderiv ℝ (fderiv ℝ (fun d => W d t)) z - fderiv ℝ (fderiv ℝ (fun d => W d t)) 0‖
        ≤ M * ‖z - 0‖)
    (hEsymm : IsSymmSndFDerivAt ℝ (fun d => W d t) 0)
    {δ : Point n} (hδmem : δ ∈ Sδ) (h0mem : (0 : Point n) ∈ Sδ) :
    ‖(W δ t).1 - (W 0 t).1 - (V δ t).1
        - (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ (fun d => W d t)) 0 δ) δ).1‖ ≤ M * ‖δ‖ ^ 3 := by
  have hfull := geodesicBasepoint_endpoint_secondOrder_taylor g gi hC hK0 ht hconv hconvδ
    hbound2 hLip hWode hVode hV0 hIC hKb hmem hEdiff hEdiff2 hElip2 hEsymm hδmem h0mem
  -- the position projection is `1`-Lipschitz (norm-nonincreasing), and commutes with the linear ops.
  set Z : Point n × Point n := W δ t - W 0 t - V δ t
      - (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ (fun d => W d t)) 0 δ) δ with hZ
  have hproj : (W δ t).1 - (W 0 t).1 - (V δ t).1
      - (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ (fun d => W d t)) 0 δ) δ).1 = Z.1 := by
    rw [hZ]; simp [Prod.fst_sub, Prod.smul_fst]
  rw [hproj]
  calc ‖Z.1‖ ≤ ‖Z‖ := by
        rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ M * ‖δ‖ ^ 3 := hfull

end QIQTH.ExpMap
