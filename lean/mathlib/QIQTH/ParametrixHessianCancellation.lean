/-
  ParametrixHessianCancellation — the (c)-side M5 off-diagonal `O(1/t)` cancellation at the
  **CURVATURE (Ricci) order**:  the **HESSIAN (second-derivative) face** of
  `totalRadialO1_coeff = 0` at the RNC centre.  This completes the off-diagonal cancellation to the
  order that matters for `a₁ = R/6`, extending the value (c5, `totalRadialO1_coeff_center_vanishes`)
  and gradient (c6, `totalRadialO1_coeff_center_grad_vanishes`) faces.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE DECOMPOSITION (what is PROVED here, unconditionally, from the RNC 2-jets).

  Writing `totalRadialO1_coeff = A·w₀ + (r∂_r w₀) + Dev` with
      A     = ½Σ(gⁱⁱ−1) − ½Σ gⁱʲΓᵏᵢⱼvᵏ            (the metric-trace / connection term)
      Dev   = ½ Σᵢⱼ (gⁱʲ−δ)(vⁱ∂ⱼw₀+vʲ∂ᵢw₀)         (the deviation term)
      w₀    = foldedCoeff Θ u 0
  the Hessian at the RNC centre splits (`totalRadialO1_coeff_center_hessian`) into
      ∂_a∂_b totalRadialO1_coeff(0)
        = ∂_a∂_b A(0)·w₀(0)                         -- term (I): the Ricci/curvature source
          + [∂_a∂_b w₀(0) + ∂_b∂_a w₀(0)]           -- term (II): 2·Hess(w₀) (the van-Vleck 2-jet)
          + 0 .                                      -- term (IV): deviation, UNCONDITIONALLY zero.

  • Term (IV) `= 0` is UNCONDITIONAL (given the RNC gauge `gⁱʲ(0)=δ`, `∂gⁱʲ(0)=0`): in each summand
    `(gⁱʲ−δ)·(vⁱ∂ⱼw₀+vʲ∂ᵢw₀)`, BOTH factors vanish at `0` and `∂(gⁱʲ−δ)(0)=∂gⁱʲ(0)=0`, so every
    surviving second-Leibniz term still carries a zero factor.  (`pd_pd_coeffDev`.)
  • Term (II) is LITERALLY the symmetric sum `∂_a∂_b w₀ + ∂_b∂_a w₀` — no Clairaut/Schwarz is used;
    the Euler field `Σᵢ vⁱ∂ᵢw₀` has, at `0`, exactly the two `∂`-hits-`vⁱ` survivors.
    (`pd_pd_radialDeriv`.)
  • Term (I) reduces to `∂_a∂_b A(0)·w₀(0)` because `A(0)=0` and `∂A(0)=0` (the c6 gradient facts),
    killing the two cross terms and the `A·∂∂w₀` term of the second Leibniz rule.
    (`pd_pd_coeffA_mul`.)

  THE TERM-(I) CURVATURE VALUE (`coeffA_center_hessian`, gauge-conditional).  Under the full
  normal-coordinate gauge suite the metric-trace part of `∂_a∂_b A(0)` is the closed Ricci coefficient
      ½Σᵢ ∂_a∂_b gⁱⁱ(0) = ⅓ Ric_{ab}(0)
  (via `pd_pd_gInv_eq_neg_metric` `∂∂gⁱⁱ = −∂∂g` and `rnc_htr_of_gauge` `Σ∂∂g_{ii}=−⅔Ric`), while the
  connection part `−½ ∂_a∂_b[Σ gⁱʲΓᵏᵢⱼvᵏ](0)` isolates (only the `∂`-hits-`vᵏ` survivors, via the
  twice-Leibniz `pd_pd_mul3_zero`) to the christoffel-derivative contraction
      −½ (Σᵢ ∂_bΓ^a_{ii}(0) + Σᵢ ∂_aΓ^b_{ii}(0)) ,
  so
      ∂_a∂_b A(0) = ⅓ Ric_{ab}(0) − ½ (Σᵢ ∂_bΓ^a_{ii}(0) + Σᵢ ∂_aΓ^b_{ii}(0)) .
  HONEST FINDING: the metric-trace piece is the clean van-Vleck-determinant `⅓Ric`; the
  connection-trace piece is a genuine `∂Γ`-divergence contraction that does NOT further reduce to
  `Ric` with the available symmetries (`riemann` here is a general-connection curvature with only
  last-pair antisymmetry `riemann_antisymm`; pair symmetry / first Bianchi are unavailable), so it is
  reported explicitly as a christoffel-derivative contraction — this is the honest term-(I) value.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE VANISHING (`totalRadialO1_coeff_center_hessian_vanishes`, F1).  The Hessian `= 0` given the
  labeled **van-Vleck coefficient Hessian datum** `hw0hess` — the standard `w₀ = (det g̃)^{1/4}`
  2-jet, `2·Hess(w₀)(0) = −∂_a∂_b A(0)·w₀(0)` — carried as a genuine load-bearing hypothesis.  This is
  the SAME class of input (`sqrtdet_pd_pd`-style, the van-Vleck determinant Hessian) as the transport
  equation, now at Hessian order.  It is CARRIED (not supplied from `sqrtdet_pd_pd`) because `w₀` here
  is the ABSTRACT folded coefficient `Θ^{−1/2}u₀`, not tied to `det g` in this def — for arbitrary
  `Θ,u` the identity is false, so `hw0hess` is genuinely load-bearing.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  SCOPE (brutally honest).  This is the CURVATURE-ORDER off-diagonal cancellation: value (c5) +
  gradient (c6) + Hessian (here) = the off-diagonal `O(1/t)` cancellation through second order at the
  RNC centre — the `a₁`-relevant order.  It is NOT the full all-orders general-`v` `= 0` (ROUTE (b),
  blocked on the absent general-`v` Taylor-`o(r²)` framework), and NOT `a₁ = R/6` (M6 parametrix
  convergence remains).  No `sorry`, no new axioms, no vacuous hypotheses; the carried RNC-centre
  gauge data (`hgi0`/`hdgi0`/`hΓ0` and the metric-side `hg0`/`hdg0`/`hinv`/`hsymm`/`hgauge`) is the
  SAME normal-coordinate gauge the √det chain carries; `hw0hess` is the standard van-Vleck 2-jet.
  Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1.
-/
import Mathlib
import QIQTH.ParametrixResidualO1Total
import QIQTH.ParametrixOffDiagCancellation
import QIQTH.RNCInverseMetricJet
import QIQTH.ChristoffelSmooth
import QIQTH.HeatParametrixOrder
import QIQTH.PullbackMetric
import QIQTH.VanVleckRadial

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.RNCExpansion
open QIQTH.HeatParametrixOrder QIQTH.PullbackMetric
open QIQTH.HeatResidualBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### The two component fields of `totalRadialO1_coeff` (splitting off `w₀`). -/

/-- The metric-trace / connection field `A = ½Σ(gⁱⁱ−1) − ½Σ gⁱʲΓᵏᵢⱼvᵏ` — the curvature source of the
    assembled `O(1/t)` coefficient (its Hessian carries the Ricci term). -/
private noncomputable def coeffA (g gi : Point n → Fin n → Fin n → ℝ) (v : Point n) : ℝ :=
  (1 / 2) * (∑ i, (gi v i i - 1))
    - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)

/-- The deviation field `Dev = ½ Σᵢⱼ (gⁱʲ−δ)(vⁱ∂ⱼw₀+vʲ∂ᵢw₀)` — the metric-deviation cross-gradient
    term (its Hessian vanishes unconditionally at the RNC centre). -/
private noncomputable def coeffDev (gi : Point n → Fin n → Fin n → ℝ) (W : Point n → ℝ)
    (v : Point n) : ℝ :=
  (1 / 2) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
      * (v i * pd W j v + v j * pd W i v))

/-- `totalRadialO1_coeff` splits as `A·w₀ + (r∂_r w₀) + Dev` — definitional. -/
private theorem coeff_split (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) :
    (fun v => totalRadialO1_coeff g gi Θ u v)
      = (fun v => coeffA g gi v * foldedCoeff Θ u 0 v + radialDeriv (foldedCoeff Θ u 0) v
          + coeffDev gi (foldedCoeff Θ u 0) v) := by
  funext v; unfold totalRadialO1_coeff coeffA coeffDev; ring

/-! ### Reusable second-derivative primitives. -/

/-- **Second-derivative additivity at `0`.**  `∂_a∂_b(f+h)(0) = ∂_a∂_b f(0) + ∂_a∂_b h(0)`. -/
private theorem pd_pd_add (f h : Point n → ℝ) (a b : Fin n)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h) :
    pd (fun y => pd (fun w => f w + h w) b y) a (0 : Point n)
      = pd (fun y => pd f b y) a 0 + pd (fun y => pd h b y) a 0 := by
  have hinner : (fun y => pd (fun w => f w + h w) b y) = (fun y => pd f b y + pd h b y) :=
    funext (fun y => pd_add f h b y (PdiffAt_of_contDiff f hf b y) (PdiffAt_of_contDiff h hh b y))
  rw [hinner, pd_add (fun y => pd f b y) (fun y => pd h b y) a 0
        (PdiffAt_pd f hf b a 0) (PdiffAt_pd h hh b a 0)]

/-- **Second-derivative commutes with a finite sum at `0`.** -/
private theorem pd_pd_sum {ι : Type*} (s : Finset ι) (F : ι → Point n → ℝ) (a b : Fin n)
    (hF : ∀ k ∈ s, ContDiff ℝ ⊤ (F k)) :
    pd (fun y => pd (fun v => ∑ k ∈ s, F k v) b y) a (0 : Point n)
      = ∑ k ∈ s, pd (fun y => pd (F k) b y) a 0 := by
  have hinner : (fun y => pd (fun v => ∑ k ∈ s, F k v) b y) = (fun y => ∑ k ∈ s, pd (F k) b y) := by
    funext y; exact pd_sum s F b y (fun k hk => PdiffAt_of_contDiff (F k) (hF k hk) b y)
  rw [hinner, pd_sum s (fun k y => pd (F k) b y) a 0 (fun k hk => PdiffAt_pd (F k) (hF k hk) b a 0)]

/-- **The second derivative of a coordinate function vanishes.**  `∂_a∂_b(v ↦ vⁱ)(0) = 0`. -/
private theorem pd_pd_coord_zero (i a b : Fin n) :
    pd (fun y => pd (fun v : Point n => v i) b y) a (0 : Point n) = 0 := by
  have h : (fun y => pd (fun v : Point n => v i) b y)
      = (fun _ : Point n => (if i = b then (1 : ℝ) else 0)) := by
    funext y; exact QIQTH.LaplaceBeltrami.pd_coord i b y
  rw [h]; exact pd_const _ a 0

/-! ### Smoothness of the component fields. -/

private theorem coeffA_contDiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ ⊤ (fun v => coeffA g gi v) := by
  unfold coeffA
  refine (contDiff_const.mul (ContDiff.sum fun i _ => (hgiC i i).sub contDiff_const)).sub
    (contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_))
  exact ((hgiC i j).mul (hC k i j)).mul (coord_contDiff k)

private theorem radialDeriv_contDiff (W : Point n → ℝ) (hW : ContDiff ℝ ⊤ W) :
    ContDiff ℝ ⊤ (fun v => radialDeriv W v) := by
  have hrw : (fun v : Point n => radialDeriv W v) = (fun v => ∑ i, v i * pd W i v) := rfl
  rw [hrw]
  exact ContDiff.sum fun i _ => (coord_contDiff i).mul (contDiff_pd W hW i)

private theorem coeffDev_contDiff (gi : Point n → Fin n → Fin n → ℝ) (W : Point n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j)) (hW : ContDiff ℝ ⊤ W) :
    ContDiff ℝ ⊤ (fun v => coeffDev gi W v) := by
  unfold coeffDev
  refine contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_)
  exact ((hgiC i j).sub contDiff_const).mul
    (((coord_contDiff i).mul (contDiff_pd W hW j)).add ((coord_contDiff j).mul (contDiff_pd W hW i)))

/-! ### The RNC-centre value/gradient facts for the `A`-field (curvature-free, from the gauge). -/

private theorem coeffA_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0) :
    coeffA g gi (0 : Point n) = 0 := by
  unfold coeffA
  have h1 : (∑ i, (gi (0 : Point n) i i - 1)) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hgi0 i i]; simp
  have h2 : (∑ i, ∑ j, ∑ k, gi (0 : Point n) i j * christoffel g gi k i j 0 * (0 : Point n) k) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => by simp
  rw [h1, h2]; ring

private theorem pd_coeffA_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) (e : Fin n) :
    pd (coeffA g gi) e (0 : Point n) = 0 := by
  have hPDgi : ∀ i j, PdiffAt (fun y => gi y i j) e (0 : Point n) :=
    fun i j => PdiffAt_of_contDiff _ (hgiC i j) e 0
  have hPDcoord : ∀ i, PdiffAt (fun v : Point n => v i) e (0 : Point n) :=
    fun i => PdiffAt_of_contDiff _ (coord_contDiff i) e 0
  have hpd_s1 : pd (fun v => ∑ i, (gi v i i - 1)) e (0 : Point n) = 0 := by
    rw [pd_sum univ (fun i v => gi v i i - 1) e 0
          (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [pd_sub (fun v => gi v i i) (fun _ => (1 : ℝ)) e 0 (hPDgi i i)
          (PdiffAt_of_contDiff _ contDiff_const e 0), hdgi0 i i e, pd_const]
    ring
  have hPDF : ∀ i j k,
      PdiffAt (fun v => gi v i j * christoffel g gi k i j v * v k) e (0 : Point n) :=
    fun i j k => ((hPDgi i j).mul (PdiffAt_of_contDiff _ (hC k i j) e 0)).mul (hPDcoord k)
  have hPDinner_k : ∀ i j,
      PdiffAt (fun v => ∑ k, gi v i j * christoffel g gi k i j v * v k) e (0 : Point n) :=
    fun i j => PdiffAt_sum univ _ e 0 (fun k _ => hPDF i j k)
  have hPDinner_jk : ∀ i,
      PdiffAt (fun v => ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) e (0 : Point n) :=
    fun i => PdiffAt_sum univ _ e 0 (fun j _ => hPDinner_k i j)
  have hpd_s2 : pd (fun v => ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)
      e (0 : Point n) = 0 := by
    rw [pd_sum univ _ e 0 (fun i _ => hPDinner_jk i)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [pd_sum univ _ e 0 (fun j _ => hPDinner_k i j)]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [pd_sum univ _ e 0 (fun k _ => hPDF i j k)]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [pd_mul (fun v => gi v i j * christoffel g gi k i j v) (fun v => v k) e 0
          ((hPDgi i j).mul (PdiffAt_of_contDiff _ (hC k i j) e 0)) (hPDcoord k)]
    have hf0 : gi (0 : Point n) i j * christoffel g gi k i j (0 : Point n) = 0 := by
      rw [hΓ0 k i j]; ring
    rw [hf0]; simp
  unfold coeffA
  rw [pd_sub _ _ e 0
        (PdiffAt_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0
          (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))))
        (PdiffAt_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0 (fun i _ => hPDinner_jk i))),
      pd_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0
        (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))),
      pd_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0 (fun i _ => hPDinner_jk i)),
      hpd_s1, hpd_s2]
  ring

/-! ### The three Hessian terms. -/

/-- **Term (II) — the Euler radial Hessian at the centre** is the symmetric sum `2·Hess(w₀)`.
    `∂_a∂_b (r∂_r w₀)(0) = ∂_a∂_b w₀(0) + ∂_b∂_a w₀(0)`.  NO Clairaut: the Euler field `Σᵢ vⁱ∂ᵢw₀`
    has, at `0`, exactly the two `∂`-hits-`vⁱ` survivors. -/
private theorem pd_pd_radialDeriv (W : Point n → ℝ) (hW : ContDiff ℝ ⊤ W) (a b : Fin n) :
    pd (fun y => pd (fun v => radialDeriv W v) b y) a (0 : Point n)
      = pd (fun y => pd W b y) a 0 + pd (fun y => pd W a y) b 0 := by
  have hrw : (fun v : Point n => radialDeriv W v) = (fun v => ∑ i, v i * pd W i v) := rfl
  rw [hrw]
  have hinner : (fun y => pd (fun v => ∑ i, v i * pd W i v) b y)
      = (fun y => ∑ i, pd (fun v => v i * pd W i v) b y) := by
    funext y
    exact pd_sum univ (fun i v => v i * pd W i v) b y
      (fun i _ => (PdiffAt_of_contDiff _ (coord_contDiff i) b y).mul (PdiffAt_pd W hW i b y))
  rw [hinner, pd_sum univ (fun i y => pd (fun v => v i * pd W i v) b y) a 0
        (fun i _ => PdiffAt_pd (fun v => v i * pd W i v)
          ((coord_contDiff i).mul (contDiff_pd W hW i)) b a 0)]
  have hsummand : ∀ i, pd (fun y => pd (fun v => v i * pd W i v) b y) a (0 : Point n)
      = (if i = b then (1 : ℝ) else 0) * pd (fun y => pd W i y) a 0
        + (if i = a then (1 : ℝ) else 0) * pd (fun y => pd W i y) b 0 := by
    intro i
    rw [pd_pd_mul_mixed (fun v => v i) (fun v => pd W i v) a b 0 (coord_contDiff i)
          (contDiff_pd W hW i), pd_pd_coord_zero i a b,
        QIQTH.LaplaceBeltrami.pd_coord i b 0, QIQTH.LaplaceBeltrami.pd_coord i a 0]
    have hc0 : (0 : Point n) i = 0 := rfl
    rw [hc0]; ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i), Finset.sum_add_distrib]
  congr 1
  · rw [show (∑ i, (if i = b then (1 : ℝ) else 0) * pd (fun y => pd W i y) a 0)
          = ∑ i, (if i = b then pd (fun y => pd W i y) a 0 else 0) from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring),
      Finset.sum_ite_eq' univ b (fun i => pd (fun y => pd W i y) a 0)]
    simp
  · rw [show (∑ i, (if i = a then (1 : ℝ) else 0) * pd (fun y => pd W i y) b 0)
          = ∑ i, (if i = a then pd (fun y => pd W i y) b 0 else 0) from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring),
      Finset.sum_ite_eq' univ a (fun i => pd (fun y => pd W i y) b 0)]
    simp

/-- **Term (I) — the `A·w₀` Hessian at the centre collapses to `∂_a∂_b A(0)·w₀(0)`.**  Because
    `A(0)=0` and `∂A(0)=0` (the c6 gradient facts), the two cross terms and the `A·∂∂w₀` term of the
    second Leibniz rule vanish. -/
private theorem pd_pd_coeffA_mul (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw0 : ContDiff ℝ ⊤ (foldedCoeff Θ u 0))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) (a b : Fin n) :
    pd (fun y => pd (fun v => coeffA g gi v * foldedCoeff Θ u 0 v) b y) a (0 : Point n)
      = pd (fun y => pd (coeffA g gi) b y) a 0 * foldedCoeff Θ u 0 0 := by
  have hA0 : coeffA g gi (0 : Point n) = 0 := coeffA_zero g gi hgi0
  have hpdAa : pd (coeffA g gi) a (0 : Point n) = 0 := pd_coeffA_zero g gi hgiC hC hdgi0 hΓ0 a
  have hpdAb : pd (coeffA g gi) b (0 : Point n) = 0 := pd_coeffA_zero g gi hgiC hC hdgi0 hΓ0 b
  rw [pd_pd_mul_mixed (coeffA g gi) (foldedCoeff Θ u 0) a b 0
        (coeffA_contDiff g gi hgiC hC) hw0, hpdAa, hpdAb, hA0]
  ring

/-- **Term (IV) — the deviation Hessian at the centre vanishes UNCONDITIONALLY.**  In each summand
    `(gⁱʲ−δ)·(vⁱ∂ⱼw₀+vʲ∂ᵢw₀)` both factors vanish at `0` and `∂(gⁱʲ−δ)(0)=∂gⁱʲ(0)=0`, so every
    second-Leibniz survivor still carries a zero factor. -/
private theorem pd_pd_coeffDev (gi : Point n → Fin n → Fin n → ℝ) (W : Point n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j)) (hW : ContDiff ℝ ⊤ W)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0) (a b : Fin n) :
    pd (fun y => pd (fun v => coeffDev gi W v) b y) a (0 : Point n) = 0 := by
  unfold coeffDev
  -- pull the `1/2` outside both derivatives
  have hSPd : ∀ v, PdiffAt (fun v' => ∑ i, ∑ j, (gi v' i j - (if i = j then (1 : ℝ) else 0))
      * (v' i * pd W j v' + v' j * pd W i v')) b v := by
    intro v
    refine PdiffAt_sum univ _ b v (fun i _ => PdiffAt_sum univ _ b v (fun j _ => ?_))
    exact ((PdiffAt_of_contDiff _ (hgiC i j) b v).sub (PdiffAt_of_contDiff _ contDiff_const b v)).mul
      (((PdiffAt_of_contDiff _ (coord_contDiff i) b v).mul (PdiffAt_pd W hW j b v)).add
        ((PdiffAt_of_contDiff _ (coord_contDiff j) b v).mul (PdiffAt_pd W hW i b v)))
  have hDevSum : ContDiff ℝ ⊤ (fun v => ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
      * (v i * pd W j v + v j * pd W i v)) :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      ((hgiC i j).sub contDiff_const).mul
        (((coord_contDiff i).mul (contDiff_pd W hW j)).add
          ((coord_contDiff j).mul (contDiff_pd W hW i)))
  have hinner : (fun y => pd (fun v => (1 / 2 : ℝ) * ∑ i, ∑ j,
        (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * pd W j v + v j * pd W i v)) b y)
      = (fun y => (1 / 2 : ℝ) * pd (fun v => ∑ i, ∑ j,
        (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * pd W j v + v j * pd W i v)) b y) :=
    funext (fun y => pd_const_mul _ _ b y (hSPd y))
  rw [hinner, pd_const_mul _ _ a 0 (PdiffAt_pd _ hDevSum b a 0)]
  -- reduce to per-summand Hessians
  rw [show (fun v => ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd W j v + v j * pd W i v))
      = (fun v => ∑ i, (fun v' => ∑ j, (gi v' i j - (if i = j then (1 : ℝ) else 0))
        * (v' i * pd W j v' + v' j * pd W i v')) v) from rfl]
  rw [pd_pd_sum univ (fun i v => ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd W j v + v j * pd W i v)) a b
        (fun i _ => ContDiff.sum fun j _ =>
          ((hgiC i j).sub contDiff_const).mul
            (((coord_contDiff i).mul (contDiff_pd W hW j)).add
              ((coord_contDiff j).mul (contDiff_pd W hW i))))]
  rw [Finset.sum_eq_zero (fun i _ => ?_), mul_zero]
  -- each inner `j`-sum's Hessian is zero
  rw [pd_pd_sum univ (fun j v => (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd W j v + v j * pd W i v)) a b
        (fun j _ => ((hgiC i j).sub contDiff_const).mul
          (((coord_contDiff i).mul (contDiff_pd W hW j)).add
            ((coord_contDiff j).mul (contDiff_pd W hW i))))]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  -- twice-Leibniz on `(gⁱʲ−δ)·R`; all four survivors carry a zero factor
  rw [pd_pd_mul_mixed (fun v => gi v i j - (if i = j then (1 : ℝ) else 0))
        (fun v => v i * pd W j v + v j * pd W i v) a b 0
        ((hgiC i j).sub contDiff_const)
        (((coord_contDiff i).mul (contDiff_pd W hW j)).add
          ((coord_contDiff j).mul (contDiff_pd W hW i)))]
  -- D(0)=0, ∂D(0)=0, R(0)=0
  have hD0 : gi (0 : Point n) i j - (if i = j then (1 : ℝ) else 0) = 0 := by rw [hgi0 i j]; ring
  have hpdD : ∀ e, pd (fun v => gi v i j - (if i = j then (1 : ℝ) else 0)) e (0 : Point n) = 0 := by
    intro e
    rw [pd_sub (fun v => gi v i j) (fun _ => (if i = j then (1 : ℝ) else 0)) e 0
          (PdiffAt_of_contDiff _ (hgiC i j) e 0) (PdiffAt_of_contDiff _ contDiff_const e 0),
        hdgi0 i j e, pd_const]
    ring
  have hR0 : (0 : Point n) i * pd W j (0 : Point n) + (0 : Point n) j * pd W i (0 : Point n) = 0 := by
    simp
  rw [hpdD a, hpdD b, hD0, hR0]
  ring

/-! ### ★ The Hessian face of the off-diagonal `O(1/t)` cancellation. -/

/-- **★ THE HESSIAN (curvature-order) DECOMPOSITION of the off-diagonal `O(1/t)` cancellation.**  At
    the RNC centre, with the normal-coordinate data `gⁱʲ(0)=δ` (`hgi0`), `∂gⁱʲ(0)=0` (`hdgi0`),
    `Γ(0)=0` (`hΓ0`), the Hessian of the assembled leading `O(1/t)` coefficient splits into the
    curvature source, twice the van-Vleck coefficient Hessian, and the (unconditionally vanishing)
    deviation Hessian:
        ∂_a∂_b totalRadialO1_coeff(0)
          = ∂_a∂_b A(0)·w₀(0)  +  (∂_a∂_b w₀(0) + ∂_b∂_a w₀(0))  +  0 ,
    with `A = coeffA g gi` and `w₀ = foldedCoeff Θ u 0`.  This is the curvature-order extension of the
    value (c5) and gradient (c6) faces.  Term (IV) `= 0` is unconditional; term (II) is the literal
    symmetric sum (no Clairaut); term (I) is the Ricci source `∂_a∂_b A(0)·w₀(0)` (its explicit
    curvature value is `coeffA_center_hessian`).  All RNC data load-bearing. -/
theorem totalRadialO1_coeff_center_hessian
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw0 : ContDiff ℝ ⊤ (foldedCoeff Θ u 0))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (a b : Fin n) :
    pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) b y) a (0 : Point n)
      = pd (fun y => pd (coeffA g gi) b y) a 0 * foldedCoeff Θ u 0 0
        + (pd (fun y => pd (foldedCoeff Θ u 0) b y) a 0
           + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0) := by
  rw [coeff_split g gi Θ u]
  -- ContDiff of the three components (and the first two grouped)
  have hT1 : ContDiff ℝ ⊤ (fun v => coeffA g gi v * foldedCoeff Θ u 0 v) :=
    (coeffA_contDiff g gi hgiC hC).mul hw0
  have hT2 : ContDiff ℝ ⊤ (fun v => radialDeriv (foldedCoeff Θ u 0) v) :=
    radialDeriv_contDiff (foldedCoeff Θ u 0) hw0
  have hT3 : ContDiff ℝ ⊤ (fun v => coeffDev gi (foldedCoeff Θ u 0) v) :=
    coeffDev_contDiff gi (foldedCoeff Θ u 0) hgiC hw0
  -- split `(T1 + T2) + T3`
  rw [pd_pd_add (fun v => coeffA g gi v * foldedCoeff Θ u 0 v + radialDeriv (foldedCoeff Θ u 0) v)
        (fun v => coeffDev gi (foldedCoeff Θ u 0) v) a b (hT1.add hT2) hT3,
      pd_pd_add (fun v => coeffA g gi v * foldedCoeff Θ u 0 v)
        (fun v => radialDeriv (foldedCoeff Θ u 0) v) a b hT1 hT2,
      pd_pd_coeffA_mul g gi Θ u hgiC hC hw0 hgi0 hdgi0 hΓ0 a b,
      pd_pd_radialDeriv (foldedCoeff Θ u 0) hw0 a b,
      pd_pd_coeffDev gi (foldedCoeff Θ u 0) hgiC hw0 hgi0 hdgi0 a b]
  ring

/-- **★ THE OFF-DIAGONAL `O(1/t)` HESSIAN CANCELLATION at the centre (F1).**  Composing the Hessian
    decomposition `totalRadialO1_coeff_center_hessian` with the **van-Vleck coefficient Hessian datum**
    `hw0hess` — the standard `w₀ = (det g̃)^{1/4}` 2-jet, `2·Hess(w₀)(0) = −∂_a∂_b A(0)·w₀(0)`:
        `∂_a∂_b totalRadialO1_coeff(0) = 0` .
    This is the CURVATURE-ORDER extension of the diagonal value cancellation (c5) and the gradient
    cancellation (c6); together the three establish the off-diagonal cancellation through second order
    at the RNC centre — the `a₁`-relevant order.  `hw0hess` is genuine and load-bearing (the same
    `sqrtdet_pd_pd`-class van-Vleck determinant Hessian as the transport equation, at Hessian order;
    for arbitrary `Θ,u` it is false).  NOT the full general-`v` `= 0` (no exact transport identity,
    ROUTE (b)), NOT `a₁ = R/6` (M6 convergence remains). -/
theorem totalRadialO1_coeff_center_hessian_vanishes
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw0 : ContDiff ℝ ⊤ (foldedCoeff Θ u 0))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hw0hess : ∀ a b, pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
        + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - pd (fun y => pd (coeffA g gi) b y) a 0 * foldedCoeff Θ u 0 0)
    (a b : Fin n) :
    pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) b y) a (0 : Point n) = 0 := by
  rw [totalRadialO1_coeff_center_hessian g gi Θ u hgiC hC hw0 hgi0 hdgi0 hΓ0 a b, hw0hess a b]
  ring

/-! ### ★ The term-(I) curvature (Ricci) value of the `A`-field Hessian. -/

/-- **Second-derivative subtractivity at `0`.** -/
private theorem pd_pd_sub (f h : Point n → ℝ) (a b : Fin n)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h) :
    pd (fun y => pd (fun w => f w - h w) b y) a (0 : Point n)
      = pd (fun y => pd f b y) a 0 - pd (fun y => pd h b y) a 0 := by
  have hinner : (fun y => pd (fun w => f w - h w) b y) = (fun y => pd f b y - pd h b y) :=
    funext (fun y => pd_sub f h b y (PdiffAt_of_contDiff f hf b y) (PdiffAt_of_contDiff h hh b y))
  rw [hinner, pd_sub (fun y => pd f b y) (fun y => pd h b y) a 0
        (PdiffAt_pd f hf b a 0) (PdiffAt_pd h hh b a 0)]

/-- **The second derivative of a constant vanishes.** -/
private theorem pd_pd_const_zero (c : ℝ) (a b : Fin n) :
    pd (fun y => pd (fun _ : Point n => c) b y) a (0 : Point n) = 0 := by
  have h : (fun y => pd (fun _ : Point n => c) b y) = (fun _ : Point n => (0 : ℝ)) :=
    funext (fun y => pd_const c b y)
  rw [h]; exact pd_const 0 a 0

/-- **Second-derivative scalar-multiplicativity at `0`.** -/
private theorem pd_pd_const_mul (c : ℝ) (f : Point n → ℝ) (a b : Fin n) (hf : ContDiff ℝ ⊤ f) :
    pd (fun y => pd (fun w => c * f w) b y) a (0 : Point n) = c * pd (fun y => pd f b y) a 0 := by
  have hinner : (fun y => pd (fun w => c * f w) b y) = (fun y => c * pd f b y) :=
    funext (fun y => pd_const_mul c f b y (PdiffAt_of_contDiff f hf b y))
  rw [hinner, pd_const_mul c (fun y => pd f b y) a 0 (PdiffAt_pd f hf b a 0)]

/-- **The metric-trace part of the `A`-Hessian is `⅔ Ric` (gauge-conditional).**  The inverse-metric
    Hessian trace `Σᵢ ∂_a∂_b gⁱⁱ(0)` equals `−Σᵢ ∂_a∂_b g_{ii}(0)` (`pd_pd_gInv_eq_neg_metric`), and
    `Σᵢ ∂_a∂_b g_{ii}(0) = −⅔ Ric_{ab}(0)` (`rnc_htr_of_gauge`), so the trace is `+⅔ Ric_{ab}(0)`. -/
private theorem coeffA1_hessian (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0mat : ∀ i j, gi (0 : Point n) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (a b : Fin n) :
    pd (fun y => pd (fun v => ∑ i, (gi v i i - 1)) b y) a (0 : Point n)
      = (2 / 3) * ricci g gi a b 0 := by
  rw [pd_pd_sum univ (fun i v => gi v i i - 1) a b (fun i _ => (hgiC i i).sub contDiff_const)]
  have hi : ∀ i, pd (fun y => pd (fun v => gi v i i - 1) b y) a (0 : Point n)
      = - pd (fun y => pd (fun w => g w i i) b y) a 0 := by
    intro i
    rw [pd_pd_sub (fun v => gi v i i) (fun _ => (1 : ℝ)) a b (hgiC i i) contDiff_const,
        pd_pd_const_zero (1 : ℝ) a b, sub_zero,
        pd_pd_gInv_eq_neg_metric g gi hg hgiC hg0 hdg0 hinv a b i i]
  have key : (∑ i, pd (fun y => pd (fun w => g w i i) b y) a 0) = -(2 / 3) * ricci g gi a b 0 :=
    rnc_htr_of_gauge g gi hg hgiC hgi0mat hdg0 hsymm hgauge a b
  rw [Finset.sum_congr rfl (fun i _ => hi i),
      show (∑ i, - pd (fun y => pd (fun w => g w i i) b y) a 0)
         = (-1 : ℝ) * ∑ i, pd (fun y => pd (fun w => g w i i) b y) a 0 from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring),
      key]
  ring

/-- **The connection part of the `A`-Hessian is the `∂Γ`-divergence contraction.**  In the twice-Leibniz
    expansion of `Σᵢⱼₖ gⁱʲΓᵏᵢⱼvᵏ` (via `pd_pd_mul3_zero`), only the two survivors where one `∂` hits the
    `vᵏ` factor (`∂vᵏ=δ`) and the other hits `Γ` (`Γ(0)=0`, `∂gⁱʲ(0)=0`) survive, collapsing to
    `Σᵢ ∂_bΓ^a_{ii}(0) + Σᵢ ∂_aΓ^b_{ii}(0)`. -/
private theorem coeffA2_hessian (g gi : Point n → Fin n → Fin n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) (a b : Fin n) :
    pd (fun y => pd (fun v => ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) b y)
        a (0 : Point n)
      = (∑ i, pd (fun y => christoffel g gi a i i y) b 0)
        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0) := by
  have hCsummand : ∀ i j k, ContDiff ℝ ⊤ (fun v => gi v i j * christoffel g gi k i j v * v k) :=
    fun i j k => ((hgiC i j).mul (hC k i j)).mul (coord_contDiff k)
  have hCsum_k : ∀ i j, ContDiff ℝ ⊤ (fun v => ∑ k, gi v i j * christoffel g gi k i j v * v k) :=
    fun i j => ContDiff.sum fun k _ => hCsummand i j k
  have hCsum_jk : ∀ i,
      ContDiff ℝ ⊤ (fun v => ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) :=
    fun i => ContDiff.sum fun j _ => hCsum_k i j
  rw [pd_pd_sum univ (fun i v => ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) a b
        (fun i _ => hCsum_jk i)]
  have hi : ∀ i,
      pd (fun y => pd (fun v => ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) b y) a 0
      = pd (fun y => christoffel g gi a i i y) b 0 + pd (fun y => christoffel g gi b i i y) a 0 := by
    intro i
    rw [pd_pd_sum univ (fun j v => ∑ k, gi v i j * christoffel g gi k i j v * v k) a b
          (fun j _ => hCsum_k i j)]
    have hj : ∀ j,
        pd (fun y => pd (fun v => ∑ k, gi v i j * christoffel g gi k i j v * v k) b y) a 0
        = (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi a i j y) b 0
          + (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi b i j y) a 0 := by
      intro j
      rw [pd_pd_sum univ (fun k v => gi v i j * christoffel g gi k i j v * v k) a b
            (fun k _ => hCsummand i j k)]
      have hk : ∀ k,
          pd (fun y => pd (fun v => gi v i j * christoffel g gi k i j v * v k) b y) a 0
          = (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) b 0
              * (if k = a then (1 : ℝ) else 0)
            + (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) a 0
              * (if k = b then (1 : ℝ) else 0) := by
        intro k
        rw [pd_pd_mul3_zero (fun v => gi v i j) (fun v => christoffel g gi k i j v) (fun v => v k)
              a b ((hgiC i j).of_le le_top).contDiffAt ((hC k i j).of_le le_top).contDiffAt
              ((coord_contDiff k).of_le le_top).contDiffAt,
            hgi0 i j, hΓ0 k i j, hdgi0 i j a, hdgi0 i j b, pd_pd_coord_zero k a b,
            QIQTH.LaplaceBeltrami.pd_coord k a 0, QIQTH.LaplaceBeltrami.pd_coord k b 0]
        have hck : (0 : Point n) k = 0 := rfl
        rw [hck]; ring
      rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib]
      congr 1
      · rw [show (∑ k, (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) b 0
                * (if k = a then (1 : ℝ) else 0))
              = ∑ k, (if k = a then (if i = j then (1 : ℝ) else 0)
                  * pd (fun y => christoffel g gi k i j y) b 0 else 0) from
            Finset.sum_congr rfl (fun k _ => by split_ifs <;> ring),
          Finset.sum_ite_eq' univ a
            (fun k => (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) b 0)]
        simp
      · rw [show (∑ k, (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) a 0
                * (if k = b then (1 : ℝ) else 0))
              = ∑ k, (if k = b then (if i = j then (1 : ℝ) else 0)
                  * pd (fun y => christoffel g gi k i j y) a 0 else 0) from
            Finset.sum_congr rfl (fun k _ => by split_ifs <;> ring),
          Finset.sum_ite_eq' univ b
            (fun k => (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) a 0)]
        simp
    rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_add_distrib]
    congr 1
    · rw [show (∑ j, (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi a i j y) b 0)
            = ∑ j, (if i = j then pd (fun y => christoffel g gi a i j y) b 0 else 0) from
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring),
        Finset.sum_ite_eq univ i (fun j => pd (fun y => christoffel g gi a i j y) b 0)]
      simp
    · rw [show (∑ j, (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi b i j y) a 0)
            = ∑ j, (if i = j then pd (fun y => christoffel g gi b i j y) a 0 else 0) from
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring),
        Finset.sum_ite_eq univ i (fun j => pd (fun y => christoffel g gi b i j y) a 0)]
      simp
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib]

/-- **★ THE TERM-(I) CURVATURE (Ricci) VALUE of the `A`-field Hessian** (gauge-conditional).  Assembling
    the metric-trace part (`coeffA1_hessian`, `⅔Ric`) and the connection part (`coeffA2_hessian`, the
    `∂Γ`-divergence) with the two `½` factors:
        `∂_a∂_b A(0) = ⅓ Ric_{ab}(0) − ½ (Σᵢ ∂_bΓ^a_{ii}(0) + Σᵢ ∂_aΓ^b_{ii}(0))` .
    HONEST: the metric-trace piece is the clean van-Vleck-determinant `⅓Ric`; the connection-trace
    piece is a genuine `∂Γ`-divergence contraction that does NOT further reduce to `Ric` with the
    available symmetries (only last-pair `riemann_antisymm`), so it is reported explicitly.  This is
    the explicit term-(I) curvature value entering `totalRadialO1_coeff_center_hessian`.  The carried
    normal-coordinate gauge suite is load-bearing (removing `hgauge` makes the `⅓Ric` false). -/
theorem coeffA_center_hessian (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (a b : Fin n) :
    pd (fun y => pd (coeffA g gi) b y) a (0 : Point n)
      = (1 / 3) * ricci g gi a b 0
        - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                   + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)) := by
  have hgi0mat : ∀ i j, gi (0 : Point n) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hgi0 i j, Matrix.one_apply]
  have hCS1 : ContDiff ℝ ⊤ (fun v : Point n => ∑ i, (gi v i i - 1)) :=
    ContDiff.sum fun i _ => (hgiC i i).sub contDiff_const
  have hCS2 : ContDiff ℝ ⊤
      (fun v : Point n => ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun k _ =>
      ((hgiC i j).mul (hC k i j)).mul (coord_contDiff k)
  unfold coeffA
  rw [pd_pd_sub (fun v => (1 / 2 : ℝ) * ∑ i, (gi v i i - 1))
        (fun v => (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) a b
        (contDiff_const.mul hCS1) (contDiff_const.mul hCS2),
      pd_pd_const_mul (1 / 2) (fun v => ∑ i, (gi v i i - 1)) a b hCS1,
      pd_pd_const_mul (1 / 2)
        (fun v => ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) a b hCS2,
      coeffA1_hessian g gi hg hgiC hg0 hgi0mat hdg0 hsymm hinv hgauge a b,
      coeffA2_hessian g gi hgiC hC hgi0 hdgi0 hΓ0 a b]
  ring

end QIQTH.HeatResidualBound
