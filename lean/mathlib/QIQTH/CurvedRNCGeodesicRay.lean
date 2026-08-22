/-
  CurvedRNCGeodesicRay — radial lines are geodesics of the CONCRETE curved RNC witness, and the
  exact radial-endpoint identity `uniformFlowExp z (-z) = 0` (`W_z(0) = -z`) for `curvedRNCMetric κ`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It discharges ONE previously-open geometric
  item — the corrected-`hpull` item (4), the EXACT radial endpoint `W_z(0) = -z` — but ONLY for the
  concrete curved witness `g^K = curvedRNCMetric κ` (`κ ≤ 0`), and ONLY as a geodesic-ray identity.
  It does NOT discharge the analytic trio `{hDuhamel, hDConv, hCConv}` on which `a₁ = R/6` remains
  STRICTLY conditional.

  ## What lands
  * `curvedRNC_bracket_ray_zero` — the (gi-free) lowered contracted Christoffel bracket
    `∑_{jk} (∂_j g^K_{αk} + ∂_k g^K_{αj} − ∂_α g^K_{jk})(s·z)·zʲ·zᵏ = 0` on the ray `s·z`.  The
    concrete-metric computation behind "radial lines are geodesics in normal coordinates":
    differentiating `g^K = δ − (K/3)(‖x‖²δ − x⊗x)` via the banked `pd_curvedRNCMetric_fun` gives
    the bracket `−(K/3)·s·(2δ_{αk}zʲ + 2δ_{αj}zᵏ − 4δ_{jk}z_α)`, which contracts against `zʲzᵏ`
    to `−(K/3)·s·(2z_α‖z‖² + 2z_α‖z‖² − 4z_α‖z‖²) = 0`.
  * `curvedRNC_christoffel_ray_zero` — the raised contraction `∑_{jk} Γ^i_{jk}(s·z)·zʲ·zᵏ = 0`
    for ANY inverse `gi` (the bracket is zero for every `α`, so `Γ^i = ∑_α gi_{iα}·bracket_α = 0`).
  * `curvedRNC_straightLine_hasDerivAt` — the straight line `γ(τ) = ((1−τ)·z, −z)` in phase space
    solves the geodesic ODE `γ'(τ) = F(γ(τ))` of `geodesicField (curvedRNCMetric κ) (curvedRNCInv κ)`
    at EVERY `τ` (velocity `−z`, acceleration `0` by the contraction).
  * `curvedRNC_uniformFlowExp_neg_eq_zero` — ★ item (4): `uniformFlowExp … z (−z) = 0` for
    `curvedRNCMetric κ` (`κ ≤ 0`), i.e. `W_z(0) = −z` EXACTLY, via ODE-uniqueness
    (`geodesic_local_unique`) matching the straight line against the Skolemized geodesic tube on
    `(−1, 3/2) ⊇ [0,1]`, requiring only `z ∈ K` and `‖z‖ ≤ ρ_K` (the tube's domain of validity).

  ⚠  a₁ = R/6 remains CONDITIONAL.  cp867 (item (4) exact-or-approx) does not remove
  `{hDuhamel, hDConv, hCConv}`.  This closes the exact `W_z(0)=−z` for the concrete radial-normal
  witness; it does NOT make `a₁ = R/6` unconditional.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.UniformFlowNondeg
import QIQTH.ChristoffelSmooth
import QIQTH.Geodesic
import QIQTH.UniformChartRadius

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.GaussLemmaGauge
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.GaussGaugeToHgauge
open QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound
open scoped BigOperators Topology

namespace QIQTH.CurvedRNCGeodesicRay

variable {n : ℕ}

/-! ### §1 — the ray contraction of the concrete curved Christoffel bracket. -/

/-- **★ The lowered contracted Christoffel bracket vanishes on the ray `s·z`.**  Using the banked
    general first derivative `pd_curvedRNCMetric_fun`
    (`∂_p g^K_{ir}(x) = −(K/3)(2δ_{ir}x_p − δ_{ip}x_r − δ_{rp}x_i)`), the bracket
    `∂_j g^K_{αk} + ∂_k g^K_{αj} − ∂_α g^K_{jk}` at `x = s·z` equals
    `−(K/3)·s·(2δ_{αk}zʲ + 2δ_{αj}zᵏ − 4δ_{jk}z_α)`, whose `zʲzᵏ`-contraction is
    `−(K/3)·s·(2z_α‖z‖² + 2z_α‖z‖² − 4z_α‖z‖²) = 0`.  This is the concrete-metric version of
    "radial lines are geodesics in Riemann normal coordinates". -/
theorem curvedRNC_bracket_ray_zero (K : ℝ) (z : Point n) (s : ℝ) (α : Fin n) :
    (∑ j, ∑ k,
      (pd (fun w => curvedRNCMetric K w α k) j (s • z)
        + pd (fun w => curvedRNCMetric K w α j) k (s • z)
        - pd (fun w => curvedRNCMetric K w j k) α (s • z)) * z j * z k) = 0 := by
  -- value of a partial derivative on the ray, via the banked general formula.
  have hpd : ∀ (a b p : Fin n),
      pd (fun w => curvedRNCMetric K w a b) p (s • z)
        = -(K / 3) * (2 * (if a = b then (1:ℝ) else 0) * (s * z p)
            - ((if a = p then (1:ℝ) else 0) * (s * z b)
              + (if b = p then (1:ℝ) else 0) * (s * z a))) := by
    intro a b p
    have h := congrFun (pd_curvedRNCMetric_fun K a b p) (s • z)
    simpa [Pi.smul_apply, smul_eq_mul] using h
  -- the collected per-(j,k) summand.
  have hcollect : ∀ j k : Fin n,
      (pd (fun w => curvedRNCMetric K w α k) j (s • z)
        + pd (fun w => curvedRNCMetric K w α j) k (s • z)
        - pd (fun w => curvedRNCMetric K w j k) α (s • z)) * z j * z k
      = -(K / 3) * s * (2 * (if α = k then (1:ℝ) else 0) * z j
          + 2 * (if α = j then (1:ℝ) else 0) * z k
          - 4 * (if j = k then (1:ℝ) else 0) * z α) * z j * z k := by
    intro j k
    rw [hpd α k j, hpd α j k, hpd j k α]
    -- normalise the δ's that appear with swapped indices.
    simp only [eq_comm]
    ring
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => hcollect j k))]
  -- abbreviate `R2 = ‖z‖²` (component form) and a δ-collapse helper.
  set R2 : ℝ := ∑ m, z m * z m with hR2
  have sumite : ∀ (a : Fin n) (F : Fin n → ℝ),
      (∑ k, (if a = k then (1:ℝ) else 0) * F k) = F a := by
    intro a F
    rw [Finset.sum_congr rfl (fun k _ => by by_cases h : a = k <;> simp [h] :
        ∀ k ∈ Finset.univ, (if a = k then (1:ℝ) else 0) * F k = if a = k then F k else 0)]
    rw [Finset.sum_ite_eq Finset.univ a F]; simp
  -- inner sum over k, for each fixed j.
  have hinner : ∀ j : Fin n,
      (∑ k, -(K / 3) * s * (2 * (if α = k then (1:ℝ) else 0) * z j
          + 2 * (if α = j then (1:ℝ) else 0) * z k
          - 4 * (if j = k then (1:ℝ) else 0) * z α) * z j * z k)
      = -(K / 3) * s * (2 * z j * z j * z α + 2 * (if α = j then (1:ℝ) else 0) * z j * R2
          - 4 * z α * z j * z j) := by
    intro j
    have hA : (∑ k, -(K / 3) * s * (2 * (if α = k then (1:ℝ) else 0) * z j) * z j * z k)
        = -(K / 3) * s * (2 * z j * z j * z α) := by
      rw [Finset.sum_congr rfl (fun k _ => show
          -(K / 3) * s * (2 * (if α = k then (1:ℝ) else 0) * z j) * z j * z k
            = (if α = k then (1:ℝ) else 0) * (-(K / 3) * s * (2 * z j * z j * z k)) from by ring),
        sumite α (fun k => -(K / 3) * s * (2 * z j * z j * z k))]
    have hB : (∑ k, -(K / 3) * s * (2 * (if α = j then (1:ℝ) else 0) * z k) * z j * z k)
        = -(K / 3) * s * (2 * (if α = j then (1:ℝ) else 0) * z j * R2) := by
      rw [Finset.sum_congr rfl (fun k _ => show
          -(K / 3) * s * (2 * (if α = j then (1:ℝ) else 0) * z k) * z j * z k
            = (-(K / 3) * s * (2 * (if α = j then (1:ℝ) else 0) * z j)) * (z k * z k) from by ring),
        ← Finset.mul_sum, ← hR2]; ring
    have hC : (∑ k, -(K / 3) * s * (4 * (if j = k then (1:ℝ) else 0) * z α) * z j * z k)
        = -(K / 3) * s * (4 * z α * z j * z j) := by
      rw [Finset.sum_congr rfl (fun k _ => show
          -(K / 3) * s * (4 * (if j = k then (1:ℝ) else 0) * z α) * z j * z k
            = (if j = k then (1:ℝ) else 0) * (-(K / 3) * s * (4 * z α * z j * z k)) from by ring),
        sumite j (fun k => -(K / 3) * s * (4 * z α * z j * z k))]
    rw [Finset.sum_congr rfl (fun k _ => show
        -(K / 3) * s * (2 * (if α = k then (1:ℝ) else 0) * z j
            + 2 * (if α = j then (1:ℝ) else 0) * z k
            - 4 * (if j = k then (1:ℝ) else 0) * z α) * z j * z k
          = -(K / 3) * s * (2 * (if α = k then (1:ℝ) else 0) * z j) * z j * z k
            + -(K / 3) * s * (2 * (if α = j then (1:ℝ) else 0) * z k) * z j * z k
            - -(K / 3) * s * (4 * (if j = k then (1:ℝ) else 0) * z α) * z j * z k from by ring),
      Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB, hC]; ring
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  -- outer sum over j.
  have oA : (∑ j, -(K / 3) * s * (2 * z j * z j * z α)) = -(K / 3) * s * (2 * z α * R2) := by
    rw [Finset.sum_congr rfl (fun j _ => show
        -(K / 3) * s * (2 * z j * z j * z α)
          = (-(K / 3) * s * (2 * z α)) * (z j * z j) from by ring),
      ← Finset.mul_sum, ← hR2]; ring
  have oB : (∑ j, -(K / 3) * s * (2 * (if α = j then (1:ℝ) else 0) * z j * R2))
      = -(K / 3) * s * (2 * z α * R2) := by
    rw [Finset.sum_congr rfl (fun j _ => show
        -(K / 3) * s * (2 * (if α = j then (1:ℝ) else 0) * z j * R2)
          = (if α = j then (1:ℝ) else 0) * (-(K / 3) * s * (2 * z j * R2)) from by ring),
      sumite α (fun j => -(K / 3) * s * (2 * z j * R2))]
  have oC : (∑ j, -(K / 3) * s * (4 * z α * z j * z j)) = -(K / 3) * s * (4 * z α * R2) := by
    rw [Finset.sum_congr rfl (fun j _ => show
        -(K / 3) * s * (4 * z α * z j * z j)
          = (-(K / 3) * s * (4 * z α)) * (z j * z j) from by ring),
      ← Finset.mul_sum, ← hR2]; ring
  rw [Finset.sum_congr rfl (fun j _ => show
      -(K / 3) * s * (2 * z j * z j * z α + 2 * (if α = j then (1:ℝ) else 0) * z j * R2
          - 4 * z α * z j * z j)
        = -(K / 3) * s * (2 * z j * z j * z α)
          + -(K / 3) * s * (2 * (if α = j then (1:ℝ) else 0) * z j * R2)
          - -(K / 3) * s * (4 * z α * z j * z j) from by ring),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, oA, oB, oC]; ring

/-! ### §2 — the raised contraction: `∑_{jk} Γ^i_{jk}(s·z)·zʲ·zᵏ = 0` (any inverse `gi`). -/

/-- **★ The raised contracted Christoffel vanishes on the ray `s·z`.**  Since the lowered bracket is
    zero for EVERY `α` (`curvedRNC_bracket_ray_zero`), the raised connection
    `Γ^i_{jk} = ½·∑_α gi_{iα}·bracket_{αjk}` contracts to `½·∑_α gi_{iα}·0 = 0`, for ANY inverse
    `gi` (no inverse-metric property is used). -/
theorem curvedRNC_christoffel_ray_zero (K : ℝ) (gi : Point n → Fin n → Fin n → ℝ)
    (z : Point n) (s : ℝ) (i : Fin n) :
    (∑ j, ∑ k, christoffel (curvedRNCMetric K) gi i j k (s • z) * z j * z k) = 0 := by
  have key := curvedRNC_bracket_ray_zero K z s
  -- reorder: pull the `∑_α gi_{iα}·(…)` out of the `∑_j ∑_k`.
  have hreorder :
      (∑ j, ∑ k, christoffel (curvedRNCMetric K) gi i j k (s • z) * z j * z k)
      = ∑ α, (1 / 2 * gi (s • z) i α) * (∑ j, ∑ k,
          (pd (fun w => curvedRNCMetric K w α k) j (s • z)
            + pd (fun w => curvedRNCMetric K w α j) k (s • z)
            - pd (fun w => curvedRNCMetric K w j k) α (s • z)) * z j * z k) := by
    simp only [christoffel]
    -- LHS: push `z j`, `z k` and `1/2` into the α-sum, giving a triple sum `∑ j ∑ k ∑ α T`.
    rw [show (∑ j, ∑ k, (1 / 2 * ∑ α, gi (s • z) i α *
            (pd (fun w => curvedRNCMetric K w α k) j (s • z)
              + pd (fun w => curvedRNCMetric K w α j) k (s • z)
              - pd (fun w => curvedRNCMetric K w j k) α (s • z))) * z j * z k)
        = ∑ j, ∑ k, ∑ α, (1 / 2 * gi (s • z) i α) *
            (pd (fun w => curvedRNCMetric K w α k) j (s • z)
              + pd (fun w => curvedRNCMetric K w α j) k (s • z)
              - pd (fun w => curvedRNCMetric K w j k) α (s • z)) * z j * z k from by
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun α _ => by ring)]
    -- reorder `∑ j ∑ k ∑ α  →  ∑ α ∑ j ∑ k`.
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm), Finset.sum_comm]
    -- RHS: pull `(1/2·gi_{iα})` back out of the `∑ j ∑ k`.
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hreorder]
  refine Finset.sum_eq_zero (fun α _ => ?_)
  rw [key α, mul_zero]

/-! ### §3 — the straight line is a geodesic of the concrete curved metric. -/

/-- **★ The straight-line phase curve `γ(τ) = ((1−τ)·z, −z)` solves the geodesic ODE.**  Its velocity
    is `−z` (matching `geodesicField`'s first component `(γ τ).2`) and its acceleration is `0`,
    matching `geodesicField`'s second component `fun i => −∑_{jk} Γ^i_{jk}((1−τ)·z)·(−z)ʲ·(−z)ᵏ`,
    which vanishes since `(−z)ʲ(−z)ᵏ = zʲzᵏ` and the ray contraction is zero
    (`curvedRNC_christoffel_ray_zero` at `s = 1−τ`). -/
theorem curvedRNC_straightLine_hasDerivAt (K : ℝ) (z : Point n) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => (((1 - t) • z, -z) : Point n × Point n))
      (geodesicField (curvedRNCMetric K) (curvedRNCInv K) (((1 - τ) • z, -z))) τ := by
  -- the geodesic field at the straight-line point equals `(-z, 0)`.
  have hfield : geodesicField (curvedRNCMetric K) (curvedRNCInv K) (((1 - τ) • z, -z))
      = ((-z, 0) : Point n × Point n) := by
    simp only [geodesicField]
    refine Prod.ext rfl ?_
    funext i
    have hc : (∑ j, ∑ k, christoffel (curvedRNCMetric K) (curvedRNCInv K) i j k ((1 - τ) • z)
        * (-z) j * (-z) k) = 0 := by
      rw [show (∑ j, ∑ k, christoffel (curvedRNCMetric K) (curvedRNCInv K) i j k ((1 - τ) • z)
          * (-z) j * (-z) k)
          = ∑ j, ∑ k, christoffel (curvedRNCMetric K) (curvedRNCInv K) i j k ((1 - τ) • z)
            * z j * z k from
        Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by
          simp only [Pi.neg_apply]; ring))]
      exact curvedRNC_christoffel_ray_zero K (curvedRNCInv K) z (1 - τ) i
    simp only [Pi.zero_apply]
    rw [hc, neg_zero]
  rw [hfield]
  -- derivative of the explicit curve.
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) • z) (-z : Point n) τ := by
    have hs : HasDerivAt (fun t : ℝ => (1 - t)) (-1 : ℝ) τ := by
      simpa using (hasDerivAt_id τ).const_sub 1
    have := hs.smul_const z
    simpa [neg_one_smul] using this
  have h2 : HasDerivAt (fun _ : ℝ => (-z : Point n)) (0 : Point n) τ := hasDerivAt_const τ (-z)
  exact h1.prodMk h2

/-! ### §4 — the exact radial endpoint `W_z(0) = −z` for the concrete curved metric. -/

/-- **★★ ITEM (4) — the EXACT radial endpoint for `curvedRNCMetric κ`.**  `uniformFlowExp … z (−z) = 0`,
    i.e. `W_z(0) = −z` EXACTLY (not merely `O(‖z‖²)`), for the genuinely-curved witness
    `g^K = curvedRNCMetric κ` (`κ ≤ 0`).  Requires only that `z` lies in the compact set `K` and that
    `‖z‖` is within the uniform confinement radius `ρ_K` — the tube's domain of validity.

    Proof: the Skolemized geodesic tube through `(z, −z)` and the straight line `γ(τ) = ((1−τ)·z, −z)`
    are both integral curves of `geodesicField` on `(−1, 3/2) ⊇ [0,1]`, agree at `τ = 0`
    (both `(z, −z)`), and stay in a common closed ball on which the (C^∞) field is Lipschitz, so they
    coincide by ODE-uniqueness (`geodesic_local_unique`).  At `τ = 1` the straight line is `(0, −z)`,
    hence the tube endpoint position is `0`.  ⚠ NOT `a₁ = R/6`. -/
theorem curvedRNC_uniformFlowExp_neg_eq_zero (K : ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {S : Set (Point n)} (hS : IsCompact S) (z : Point n) (hzS : z ∈ S)
    (hznorm : ‖z‖ ≤ uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS) :
    uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hC hS z (-z) = 0 := by
  -- abbreviations.
  set g := curvedRNCMetric (n := n) K with hg
  set gi := curvedRNCInv (n := n) K with hgi
  -- the geodesic tube through `(z, -z)`.
  have hnegnorm : ‖(-z)‖ ≤ uniformFlowRadius g gi hC hS := by rw [norm_neg]; exact hznorm
  have hic := uniformFlowTube_spec_ic g gi hC hS z hzS (-z) hnegnorm
  have hode := uniformFlowTube_spec_ode g gi hC hS z hzS (-z) hnegnorm
  set tube := uniformFlowTube g gi hC hS z (-z) with htube
  -- the straight line phase curve.
  set line : ℝ → Point n × Point n := fun t => (((1 - t) • z, -z) : Point n × Point n) with hline
  have hlineIC : line 0 = (z, -z) := by simp [hline]
  have hlineODE : ∀ τ : ℝ, HasDerivAt line (geodesicField g gi (line τ)) τ := by
    intro τ; simpa only [hline, hg, hgi] using curvedRNC_straightLine_hasDerivAt K z τ
  -- work on the interval `(-1, 3/2) ⊇ [0,1]`.
  have hIoosub : Set.Ioo (-1 : ℝ) (3 / 2) ⊆ Set.Ioo (-2 : ℝ) 2 :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- boundedness of the two curves on the compact `[-1, 3/2]`.
  have hlineCont : ContinuousOn line (Set.Icc (-1 : ℝ) (3 / 2)) :=
    fun τ _ => ((hlineODE τ).continuousAt).continuousWithinAt
  obtain ⟨Ml, hMl⟩ :=
    (((isCompact_Icc).image_of_continuousOn hlineCont).isBounded).subset_closedBall
      ((z, 0) : Point n × Point n)
  have hIccsub : Set.Icc (-1 : ℝ) (3 / 2) ⊆ Set.Ioo (-2 : ℝ) 2 :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have htubeCont : ContinuousOn tube (Set.Icc (-1 : ℝ) (3 / 2)) := fun τ hτ =>
    ((hode τ (hIccsub hτ)).continuousAt).continuousWithinAt
  obtain ⟨Mt, hMt⟩ :=
    (((isCompact_Icc).image_of_continuousOn htubeCont).isBounded).subset_closedBall
      ((z, 0) : Point n × Point n)
  obtain ⟨Klip, hLip⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((z, 0) : Point n × Point n) (max Ml Mt))).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hlineMem : ∀ τ ∈ Set.Ioo (-1 : ℝ) (3 / 2),
      line τ ∈ Metric.closedBall ((z, 0) : Point n × Point n) (max Ml Mt) := fun τ hτ =>
    Metric.closedBall_subset_closedBall (le_max_left _ _)
      (hMl ⟨τ, Set.Ioo_subset_Icc_self hτ, rfl⟩)
  have htubeMem : ∀ τ ∈ Set.Ioo (-1 : ℝ) (3 / 2),
      tube τ ∈ Metric.closedBall ((z, 0) : Point n × Point n) (max Ml Mt) := fun τ hτ =>
    Metric.closedBall_subset_closedBall (le_max_right _ _)
      (hMt ⟨τ, Set.Ioo_subset_Icc_self hτ, rfl⟩)
  -- ODE-uniqueness on `(-1, 3/2)`.
  have hEqon := geodesic_local_unique g gi (a := -1) (b := 3 / 2) (t₀ := 0)
    ⟨by norm_num, by norm_num⟩ hLip
    (fun τ hτ => ⟨hlineODE τ, hlineMem τ hτ⟩)
    (fun τ hτ => ⟨hode τ (hIoosub hτ), htubeMem τ hτ⟩)
    (by rw [hlineIC, hic])
  -- evaluate at `τ = 1`.
  have h1 := hEqon (show (1 : ℝ) ∈ Set.Ioo (-1 : ℝ) (3 / 2) from ⟨by norm_num, by norm_num⟩)
  -- `line 1 = (0, -z)`, so `tube 1 = (0, -z)` and its position is `0`.
  have hline1 : line 1 = ((0, -z) : Point n × Point n) := by simp [hline]
  have htube1 : tube 1 = ((0, -z) : Point n × Point n) := by rw [← h1, hline1]
  show (uniformFlowTube g gi hC hS z (-z) 1).1 = 0
  rw [← htube, htube1]

/-- **★★ ITEM (4) PROPER — the EXACT inverse-chart radial endpoint `W_z(0) = −z`** for the concrete
    curved witness `g^K = curvedRNCMetric κ` (`κ ≤ 0`).  From the banked left-inverse germ
    `uniformInverseChart_huniformChart` (`W_q(φ_q z') =ᶠ[𝓝 v] z'` for `‖v‖ < δ₀`), evaluated at
    `v = −z` (via `Filter.EventuallyEq.eq_of_nhds`, giving `W_z(φ_z(−z)) = −z`) combined with the
    forward endpoint `curvedRNC_uniformFlowExp_neg_eq_zero` (`φ_z(−z) = 0`), we get
    `uniformInverseChart … z 0 = −z` EXACTLY for all `z ∈ S` within the uniform chart radius `δ₀` and
    the confinement radius `ρ_S`.  This is `W_z(0) = −z` (not merely `O(‖z‖²)`), the object the
    `hpull` legs consume.  Non-vacuous: `δ₀ > 0` and `ρ_S > 0` (`uniformFlowRadius_pos`), so small
    nonzero `z` satisfy the hypotheses at a genuinely-curved witness (`κ < 0`, `n ≥ 2`).
    ⚠ NOT `a₁ = R/6`; it does NOT by itself discharge any `hpull` leg (those need the inverse-chart
    first/second-jet identities). -/
theorem curvedRNC_uniformInverseChart_zero_eq_neg (K : ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {S : Set (Point n)} (hS : IsCompact S) :
    ∃ δ₀ > (0 : ℝ), ∀ z ∈ S, ‖z‖ < δ₀ →
      ‖z‖ ≤ uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS →
      uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hC hS z 0 = -z := by
  obtain ⟨δ₀, hδ₀, hspec⟩ :=
    QIQTH.HeatResidualBound.uniformInverseChart_huniformChart
      (curvedRNCMetric K) (curvedRNCInv K) hC hS
  refine ⟨δ₀, hδ₀, fun z hzS hzδ hznorm => ?_⟩
  have hvnorm : ‖(-z)‖ < δ₀ := by rw [norm_neg]; exact hzδ
  obtain ⟨hgerm, _⟩ := (hspec z hzS).1 (-z) hvnorm
  have hWφ := hgerm.eq_of_nhds
  simp only at hWφ
  -- `hWφ : W_z (φ_z (-z)) = -z`; substitute `φ_z (-z) = 0`.
  rw [curvedRNC_uniformFlowExp_neg_eq_zero K hC hS z hzS hznorm] at hWφ
  exact hWφ

/-- **★ Non-vacuity: the inverse-chart endpoint identity is genuinely INHABITED.**  For `n ≥ 1` and
    any `κ` (in particular a genuinely-curved `κ < 0`, `n ≥ 2`, `Ric(0) = (n−1)κ·δ ≠ 0`), on the
    compact `S = closedBall 0 1` there is a NONZERO `z` for which `W_z(0) = −z` holds.  So the
    conclusion `uniformInverseChart … z 0 = −z` is NOT vacuously quantified at a flat/degenerate point:
    it holds at an honest nonzero point of a curved metric.  Uses `0 < ρ_S` (`uniformFlowRadius_pos`)
    and `0 < δ₀` (from the chart theorem) to place a small nonzero `z` inside both radii. -/
theorem curvedRNC_uniformInverseChart_zero_eq_neg_inhabited (K : ℝ) (hn : 1 ≤ n)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y)) :
    ∃ z : Point n, z ≠ 0 ∧
      uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hC (isCompact_closedBall (0 : Point n) 1) z 0 = -z := by
  obtain ⟨δ₀, hδ₀, hW⟩ :=
    curvedRNC_uniformInverseChart_zero_eq_neg K hC (S := Metric.closedBall (0 : Point n) 1)
      (isCompact_closedBall (0 : Point n) 1)
  have hρ : 0 < uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC (isCompact_closedBall (0 : Point n) 1) :=
    uniformFlowRadius_pos _ _ _ _
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀⟩ := hne
  -- radius strictly inside all three of: `1`, `ρ_S`, `δ₀`.
  set r : ℝ := min (min 1 (uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC (isCompact_closedBall (0 : Point n) 1))) δ₀ / 2
    with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  set z : Point n := fun j => if j = i₀ then r else 0 with hz
  have hnorm : ‖z‖ = r := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg hr0.le]
      intro j
      show ‖(if j = i₀ then r else (0 : ℝ))‖ ≤ r
      by_cases h : j = i₀
      · rw [if_pos h]; exact le_of_eq (by rw [Real.norm_eq_abs, abs_of_pos hr0])
      · rw [if_neg h, norm_zero]; exact hr0.le
    · calc r = ‖z i₀‖ := by rw [hz]; simp [Real.norm_eq_abs, abs_of_pos hr0]
        _ ≤ ‖z‖ := norm_le_pi_norm z i₀
  have hrle1 : r ≤ 1 := le_trans (by rw [hr]; linarith [min_le_left (min 1 (uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC (isCompact_closedBall (0 : Point n) 1))) δ₀]) (min_le_left _ _)
  have hrleρ : r ≤ uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC (isCompact_closedBall (0 : Point n) 1) :=
    le_trans (by rw [hr]; linarith [min_le_left (min 1 (uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC (isCompact_closedBall (0 : Point n) 1))) δ₀]) (min_le_right _ _)
  have hrltδ : r < δ₀ := by rw [hr]; linarith [min_le_right (min 1 (uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC (isCompact_closedBall (0 : Point n) 1))) δ₀]
  refine ⟨z, ?_, ?_⟩
  · intro hzero
    have := congrFun hzero i₀
    simp only [hz, if_pos rfl, Pi.zero_apply] at this
    exact (ne_of_gt hr0) this
  · exact hW z (by rw [Metric.mem_closedBall, dist_zero_right, hnorm]; exact hrle1)
      (by rw [hnorm]; exact hrltδ) (by rw [hnorm]; exact hrleρ)

end QIQTH.CurvedRNCGeodesicRay

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedRNCGeodesicRay.curvedRNC_bracket_ray_zero
#print axioms QIQTH.CurvedRNCGeodesicRay.curvedRNC_christoffel_ray_zero
#print axioms QIQTH.CurvedRNCGeodesicRay.curvedRNC_straightLine_hasDerivAt
#print axioms QIQTH.CurvedRNCGeodesicRay.curvedRNC_uniformFlowExp_neg_eq_zero
#print axioms QIQTH.CurvedRNCGeodesicRay.curvedRNC_uniformInverseChart_zero_eq_neg
#print axioms QIQTH.CurvedRNCGeodesicRay.curvedRNC_uniformInverseChart_zero_eq_neg_inhabited
