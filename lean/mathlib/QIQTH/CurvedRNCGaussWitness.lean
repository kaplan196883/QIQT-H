import QIQTH.GaussLemmaGauge
import QIQTH.RadialDistance

/-!
# J4-523 — A genuinely CURVED RNC witness for the `hGauss` geometric floor

The `a₁ = R/6` curved-signature capstone `a1_R6_from_labelled_curved_boundary` carries the
**radial Gauss lemma** `hGauss : ∀ i, (fun x => ∑ⱼ g x i j · xʲ) =ᶠ[𝓝 0] (fun x => xⁱ)` as a
labelled geometric input.  Prior to this file the ONLY proved inhabitant of the underlying
`MetricGaussGauge` gauge was the FLAT metric (`GaussLemmaGauge.metricGaussGauge_flat`).  The J4-507
audit ledger flagged the worry that the Gauss lemma is a genuine geodesic/exp-map FLOOR — with the
suspicion that conformal / quartic look-alikes (`g = (1+ε‖x‖⁴)δ`, `e^{2φ}δ`) match the finite RNC
2-jet gauge yet FAIL the `∀x` Gauss identity.  This file exhibits a **genuinely curved** metric that
satisfies `MetricGaussGauge` **exactly** (all orders, all `x`), refuting "only flat inhabits `hGauss`".

## The witness

`curvedRNCMetric K x i j := δᵢⱼ − (K/3)(‖x‖² δᵢⱼ − xᵢ xⱼ)` on `Point n = Fin n → ℝ`.

* **Exact radial Gauss lemma** (`metricGaussGauge_curvedRNC`): the correction tensor
  `‖x‖²δᵢⱼ − xᵢxⱼ` ANNIHILATES `xʲ`, so `∑ⱼ g x i j · xʲ = xⁱ` holds EXACTLY for every `x`, every
  `K`, every `n`.  This is the DEFINING property of Riemann normal coordinates (radial gauge) — NOT a
  `confMetric`-lookalike, which fails it (`∑ⱼ e^{2φ}δᵢⱼ xʲ = e^{2φ}xⁱ ≠ xⁱ`).
* **Mainline germ** (`hGaussGerm_curvedRNC`): feeds directly into the capstone's labelled `hGauss`
  via `metricGaussGauge_imp_hGaussGerm`.
* **Genuinely curved** (`curvedRNCMetric_ricci_trace` / `…_diag_ne`): the metric-Hessian trace
  `∑ₐ ∂c∂d gₐₐ(0) = −(2/3)(n−1)K δcd`, which is EXACTLY the `htr = −(2/3)Ric` datum
  (`RNCExpansion.rnc_htr_of_gauge`).  Hence `Ric(0) = (n−1)K δ ≠ 0` for `K ≠ 0`, `n ≥ 2`: the witness
  is NOT secretly flat.

⚠ SCOPE.  This inhabits the geometric `hGauss` slice with genuine curvature.  It does NOT by itself
make the full ~280-binder capstone antecedent non-vacuous: the coupled analytic piles (measurability,
Levi-series integrability, Gaussian gate bounds) must still be instantiated.  For `K > 0` the metric is
positive-definite only on `‖x‖² < 3/K` (det `g = (1 − (K/3)‖x‖²)^{n−1}`); use `K < 0` for a globally
positive metric, or a neighbourhood of `0` for either sign.  NOT `a₁ = R/6`.
-/

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.GaussLemmaGauge
open scoped BigOperators

namespace QIQTH.CurvedRNCGaussWitness

variable {n : ℕ}

/-- **The curved RNC witness metric** `g^K_{ij}(x) = δ_{ij} − (K/3)(‖x‖² δ_{ij} − x_i x_j)`.
    The unique-to-quadratic-order constant-curvature-`K` metric in Riemann normal coordinates. -/
noncomputable def curvedRNCMetric (K : ℝ) : Point n → Fin n → Fin n → ℝ :=
  fun x i j => (if i = j then (1 : ℝ) else 0)
    - (K / 3) * (rncRadialSq x * (if i = j then (1 : ℝ) else 0) - x i * x j)

/-- The witness is symmetric: `g^K_{ij} = g^K_{ji}`. -/
theorem curvedRNCMetric_symm (K : ℝ) (x : Point n) (i j : Fin n) :
    curvedRNCMetric K x i j = curvedRNCMetric K x j i := by
  by_cases h : i = j
  · subst h; rfl
  · simp only [curvedRNCMetric, if_neg h, if_neg (Ne.symm h)]; ring

/-- The witness is the identity at the centre: `g^K(0)_{ij} = δ_{ij}`. -/
theorem curvedRNCMetric_zero (K : ℝ) (i j : Fin n) :
    curvedRNCMetric K (0 : Point n) i j = if i = j then (1 : ℝ) else 0 := by
  simp [curvedRNCMetric]

/-- Each component `x ↦ g^K_{ij}(x)` is `C^∞` (a polynomial in the coordinate projections). -/
theorem curvedRNCMetric_contDiff (K : ℝ) (i j : Fin n) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => curvedRNCMetric K x i j) := by
  have h2 : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun x : Point n => rncRadialSq x * (if i = j then (1 : ℝ) else 0)) :=
    rncRadialSq_contDiff.mul contDiff_const
  have h3 : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : Point n => x i * x j) :=
    (coord_contDiff i).mul (coord_contDiff j)
  have h4 : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun x : Point n => (K / 3) * (rncRadialSq x * (if i = j then (1 : ℝ) else 0) - x i * x j)) :=
    (contDiff_const (c := (K / 3 : ℝ))).mul (h2.sub h3)
  simpa only [curvedRNCMetric] using (contDiff_const.sub h4)

/-- **★★ THE CURVED INHABITANT — exact radial Gauss lemma.**  `∑ⱼ g^K_{ij}(x) · xʲ = xⁱ` for EVERY
    `x`, `i`, `K`, `n`.  The correction tensor `‖x‖²δᵢⱼ − xᵢxⱼ` annihilates `xʲ`, so the identity is
    EXACT (all orders), not a finite-jet approximation.  This is a genuinely curved (`K ≠ 0`)
    inhabitant of the `MetricGaussGauge` geometric floor — the first beyond the flat metric. -/
theorem metricGaussGauge_curvedRNC (K : ℝ) :
    MetricGaussGauge (curvedRNCMetric (n := n) K) := by
  intro x i
  have hA : (∑ j, (if i = j then x j else 0)) = x i := by
    rw [Finset.sum_ite_eq]; simp
  have hSq : (∑ j, x j * x j) = rncRadialSq x := by
    simp only [rncRadialSq, pow_two]
  have e1 : ∀ j : Fin n, curvedRNCMetric K x i j * x j
      = (if i = j then x j else 0)
        - ((K / 3) * rncRadialSq x) * (if i = j then x j else 0)
        + ((K / 3) * x i) * (x j * x j) := by
    intro j
    by_cases h : i = j
    · simp only [curvedRNCMetric, h, if_true]; ring
    · simp only [curvedRNCMetric, if_neg h]; ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j),
      Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [hA, hSq]
  ring

/-- **The mainline germ `hGauss` for the curved witness.**  Exactly the labelled input consumed by
    `A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary`, now discharged for a genuinely
    curved metric via the `∀x` gauge and `metricGaussGauge_imp_hGaussGerm`. -/
theorem hGaussGerm_curvedRNC (K : ℝ) :
    ∀ i, (fun x => ∑ j, curvedRNCMetric (n := n) K x i j * x j)
      =ᶠ[nhds (0 : Point n)] (fun x => x i) :=
  metricGaussGauge_imp_hGaussGerm (curvedRNCMetric K) (metricGaussGauge_curvedRNC K)

/-! ## Genuine curvature — the metric-Hessian trace `∑ₐ ∂∂gₐₐ(0) = −(2/3)(n−1)K δ`. -/

/-- The metric trace collapses to a scalar multiple of `‖x‖²`:
    `∑ₐ g^K_{aa}(x) = n − (K/3)(n−1)‖x‖²`.  Pure algebra (no derivatives). -/
theorem curvedRNCMetric_trace (K : ℝ) (x : Point n) :
    (∑ a, curvedRNCMetric K x a a) = (n : ℝ) - (K / 3) * ((n : ℝ) - 1) * rncRadialSq x := by
  have hSq : (∑ a : Fin n, x a * x a) = rncRadialSq x := by
    simp only [rncRadialSq, pow_two]
  have e1 : ∀ a : Fin n, curvedRNCMetric K x a a
      = 1 - (K / 3) * (rncRadialSq x - x a * x a) := by
    intro a; simp only [curvedRNCMetric, if_true]; ring
  rw [Finset.sum_congr rfl (fun a _ => e1 a), Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hSq]
  ring

/-- Partial derivative of a coordinate projection: `∂c(w ↦ wᵈ)(v) = δ_{dc}`. -/
theorem pd_coord (d c : Fin n) (v : Point n) :
    pd (fun w => w d) c v = if d = c then (1 : ℝ) else 0 := by
  simp only [pd]
  have hupd : (fun t => Function.update v c t d) = (fun t => if d = c then t else v d) := by
    funext t; rw [Function.update_apply]
  rw [hupd]
  by_cases h : d = c
  · subst h; simp
  · simp [h]

/-- **★ THE CURVATURE CERTIFICATE — the metric-Hessian trace.**  `∑ₐ ∂c∂d g^K_{aa}(0) =
    −(2/3)(n−1)K δcd`.  This is EXACTLY the `htr = −(2/3)Ric` datum of `RNCExpansion.rnc_htr_of_gauge`,
    so it certifies `Ric(0) = (n−1)K δ` — genuine curvature for `K ≠ 0`, `n ≥ 2`. -/
theorem curvedRNCMetric_ricci_trace (K : ℝ) (c d : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) K y a a) d x) c 0
      = -(2 / 3) * ((n : ℝ) - 1) * K * (if d = c then (1 : ℝ) else 0) := by
  -- The inner partial, as a function of `x`, is the linear field `A · xᵈ`.
  have hinner : (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) K y a a) d x)
      = (fun x => (-(K / 3 * ((n : ℝ) - 1)) * 2) * x d) := by
    funext x
    rw [show (fun y => ∑ a, curvedRNCMetric (n := n) K y a a)
          = (fun y => (n : ℝ) - (K / 3 * ((n : ℝ) - 1)) * rncRadialSq y) from
        funext (fun y => by rw [curvedRNCMetric_trace K y])]
    rw [pd_sub _ _ d x (PdiffAt_of_contDiff _ contDiff_const d x)
          (PdiffAt_of_contDiff _ (contDiff_const.mul rncRadialSq_contDiff) d x),
        pd_const,
        pd_const_mul _ _ d x (PdiffAt_of_contDiff _ rncRadialSq_contDiff d x),
        pd_rncRadialSq]
    ring
  rw [hinner,
      pd_const_mul _ _ c 0 (PdiffAt_of_contDiff _ (coord_contDiff d) c 0),
      pd_coord]
  ring

/-- **The witness is genuinely curved (the GATE).**  For `K ≠ 0` and `n ≥ 2` the diagonal
    metric-Hessian trace is nonzero, so `Ric(0) ≠ 0`: `curvedRNCMetric` is NOT secretly flat. -/
theorem curvedRNCMetric_ricci_trace_diag_ne (K : ℝ) (hK : K ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) K y a a) c x) c 0 ≠ 0 := by
  rw [curvedRNCMetric_ricci_trace K c c, if_pos rfl, mul_one]
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have h23 : -(2 / 3 : ℝ) ≠ 0 := by norm_num
  exact mul_ne_zero (mul_ne_zero h23 hn1) hK

end QIQTH.CurvedRNCGaussWitness

section AxiomChecks
open QIQTH.CurvedRNCGaussWitness
#print axioms metricGaussGauge_curvedRNC
#print axioms hGaussGerm_curvedRNC
#print axioms curvedRNCMetric_ricci_trace
#print axioms curvedRNCMetric_ricci_trace_diag_ne
end AxiomChecks
