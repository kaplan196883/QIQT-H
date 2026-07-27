import Mathlib
import QIQTH.RNCExpansion
import QIQTH.RadialDistance
import QIQTH.Curvature

/-!
# The leading (2-jet) term of the van-Vleck radial ODE — OFF the diagonal

This file lands the **directional (off-diagonal) generalization** of the already-derived diagonal
van-Vleck coefficient `a₁`.  The diagonal `a₁` used only the *trace* `∑_i ∂_i² √det g`; here we
compute the full **directional contraction** `∑_{cd} v^c v^d ∂_c∂_d √det g` and identify it with the
**Ricci quadratic form** `−(1/3) Ric(v,v)`.

## What lands

* `radialDeriv_quadraticForm` — Euler's identity for a general quadratic form:
  `(r ∂_r) (∑_{ab} c_{ab} w^a w^b) = 2 ∑_{ab} c_{ab} v^a v^b`.  UNCONDITIONAL (no hypotheses); the
  directional generalization of the model lemma `radialDeriv_rncRadialSq` (its `c = 1` special case).

* `sqrtdet_directional_hessian_ricci` — the leading OFF-DIAGONAL van-Vleck curvature coefficient:
  under the SAME four hypotheses carried by `QIQTH.RNCExpansion.sqrtdet_pd_pd`
  (`hg` smooth metric, `hg0` normal gauge at the centre, `hdg0` first jet vanishes, `htr` the
  carried metric-Hessian-trace datum `∑_a ∂_c∂_d g_{aa}(0) = −⅔ Ric_{cd}`),
  `∑_{cd} v^c v^d ∂_c∂_d √det g (0) = −(1/3) ∑_{cd} Ric_{cd} v^c v^d = −(1/3) Ric(v,v)`.
  This is the directional 2-jet of `√det g` obtained from the RNC metric 2-jet WITHOUT any matrix
  Jacobi field or `Y⁻¹`.  The carried hypotheses are genuine equations on the metric (none assumes
  the conclusion — remove `htr` and the statement is false; `htr` is discharged elsewhere by the
  radial/normal gauge, RNC3).

## What this is NOT

⚠ This is **not** the full van-Vleck radial ODE for all `v` / all orders.  The uniform-in-`v`
statement `(r ∂_r) log √det g̃ = …` that would kill the off-diagonal `O(1/t)` term needs the
exponential-map Jacobian's radial structure along rays — the singular-at-centre matrix Jacobi
field — which is the documented Mathlib-absent wall recorded at the end of
`QIQTH/VanVleckCancellation.lean`.  This file is the LEADING term of that ODE only, extracted
algebraically from the metric 2-jet.  It is **not** `a₁ = R/6` for the true heat kernel.
-/

set_option maxHeartbeats 4000000

namespace QIQTH.VanVleckRadial

open QIQTH.Curvature
open QIQTH.RadialDistance
open QIQTH.RNCExpansion
open scoped BigOperators

variable {n : ℕ}

/-- Partial derivative of a coordinate projection: `∂ᵢ (w ↦ wᵃ) = δ_{ai}`. -/
theorem pd_coord (a i : Fin n) (v : Point n) :
    pd (fun w : Point n => w a) i v = if a = i then (1 : ℝ) else 0 := by
  simp only [pd]
  have h : (fun t => (Function.update v i t) a) = (fun t => if a = i then t else v a) := by
    funext t; rw [Function.update_apply]
  rw [h]
  by_cases hai : a = i
  · subst hai; simp
  · simp [hai]

/-! ### Deliverable 1 — Euler's identity for a general quadratic form -/

/-- The partial derivative of a quadratic form.  `∂ᵢ (∑_{ab} c_{ab} w^a w^b) = ∑_a c_{ai} v^a
    + ∑_b c_{ib} v^b`:  the `i`-th coordinate hits either the `w^a` or the `w^b` factor. -/
theorem pd_quadraticForm (c : Fin n → Fin n → ℝ) (i : Fin n) (v : Point n) :
    pd (fun w => ∑ a, ∑ b, c a b * w a * w b) i v
      = (∑ a, c a i * v a) + (∑ b, c i b * v b) := by
  -- partial of a single quadratic monomial
  have hterm : ∀ a b : Fin n,
      pd (fun w : Point n => c a b * w a * w b) i v
        = c a b * (if a = i then (1 : ℝ) else 0) * v b
          + c a b * v a * (if b = i then (1 : ℝ) else 0) := by
    intro a b
    rw [pd_mul (fun w => c a b * w a) (fun w => w b) i v
          (PdiffAt_of_contDiff (fun w => c a b * w a) (contDiff_const.mul (coord_contDiff a)) i v)
          (PdiffAt_of_contDiff (fun w => w b) (coord_contDiff b) i v),
        pd_const_mul (c a b) (fun w => w a) i v
          (PdiffAt_of_contDiff (fun w => w a) (coord_contDiff a) i v),
        pd_coord a i v, pd_coord b i v]
  -- differentiability of the inner (over `b`) sum
  have hPd_inner : ∀ a : Fin n, PdiffAt (fun w : Point n => ∑ b, c a b * w a * w b) i v := by
    intro a
    exact PdiffAt_sum Finset.univ (fun b w => c a b * w a * w b) i v
      (fun b _ => PdiffAt_of_contDiff (fun w => c a b * w a * w b)
        ((contDiff_const.mul (coord_contDiff a)).mul (coord_contDiff b)) i v)
  -- differentiate through the outer and inner sums
  rw [pd_sum Finset.univ (fun a w => ∑ b, c a b * w a * w b) i v (fun a _ => hPd_inner a)]
  rw [show (∑ a, pd (fun w : Point n => ∑ b, c a b * w a * w b) i v)
        = ∑ a, ∑ b, (c a b * (if a = i then (1 : ℝ) else 0) * v b
              + c a b * v a * (if b = i then (1 : ℝ) else 0)) from
      Finset.sum_congr rfl (fun a _ => by
        rw [pd_sum Finset.univ (fun b w => c a b * w a * w b) i v
              (fun b _ => PdiffAt_of_contDiff (fun w => c a b * w a * w b)
                ((contDiff_const.mul (coord_contDiff a)).mul (coord_contDiff b)) i v)]
        exact Finset.sum_congr rfl (fun b _ => hterm a b))]
  -- rewrite each monomial as a Kronecker-delta pair
  have L : (∑ a, ∑ b, (c a b * (if a = i then (1 : ℝ) else 0) * v b
              + c a b * v a * (if b = i then (1 : ℝ) else 0)))
      = (∑ a, ∑ b, (if a = i then c a b * v b else 0))
        + (∑ a, ∑ b, (if b = i then c a b * v a else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have e1 : c a b * (if a = i then (1 : ℝ) else 0) * v b
        = if a = i then c a b * v b else 0 := by split_ifs <;> ring
    have e2 : c a b * v a * (if b = i then (1 : ℝ) else 0)
        = if b = i then c a b * v a else 0 := by split_ifs <;> ring
    rw [e1, e2]
  -- collapse the two Kronecker sums
  have F1 : (∑ a, ∑ b, (if a = i then c a b * v b else 0)) = ∑ b, c i b * v b := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun a _ ha => by simp [ha])]
    simp
  have F2 : (∑ a, ∑ b, (if b = i then c a b * v a else 0)) = ∑ a, c a i * v a := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun b _ hb => by simp [hb])]
    simp
  rw [L, F1, F2]
  exact add_comm _ _

/-- **Deliverable 1 — Euler's identity for a general quadratic form.**
    `(r ∂_r) (∑_{ab} c_{ab} w^a w^b) = 2 ∑_{ab} c_{ab} v^a v^b`.  The radial (Euler) derivative of a
    degree-2 homogeneous quadratic form is twice its value.  UNCONDITIONAL.  Generalizes
    `radialDeriv_rncRadialSq` (the `c = δ` special case). -/
theorem radialDeriv_quadraticForm (c : Fin n → Fin n → ℝ) (v : Point n) :
    radialDeriv (fun w => ∑ a, ∑ b, c a b * w a * w b) v
      = 2 * ∑ a, ∑ b, c a b * v a * v b := by
  simp only [radialDeriv]
  rw [show (∑ i, v i * pd (fun w => ∑ a, ∑ b, c a b * w a * w b) i v)
        = ∑ i, v i * ((∑ a, c a i * v a) + (∑ b, c i b * v b)) from
      Finset.sum_congr rfl (fun i _ => by rw [pd_quadraticForm c i v])]
  have split : (∑ i, v i * ((∑ a, c a i * v a) + (∑ b, c i b * v b)))
      = (∑ i, v i * ∑ a, c a i * v a) + (∑ i, v i * ∑ b, c i b * v b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_add]
  rw [split]
  have h1 : (∑ i, v i * ∑ a, c a i * v a) = ∑ a, ∑ b, c a b * v a * v b := by
    have e : (∑ i, v i * ∑ a, c a i * v a) = ∑ i, ∑ a, c a i * v a * v i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      ring
    rw [e, Finset.sum_comm]
  have h2 : (∑ i, v i * ∑ b, c i b * v b) = ∑ a, ∑ b, c a b * v a * v b := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [h1, h2]; ring

/-! ### Deliverable 2 — the directional (off-diagonal) van-Vleck 2-jet -/

/-- **Deliverable 2 — the directional (off-diagonal) van-Vleck 2-jet = the Ricci quadratic form.**
    Under the four hypotheses carried by `sqrtdet_pd_pd` (`hg`, `hg0`, `hdg0`, `htr` — none of which
    assumes the conclusion), the directional contraction of the Hessian of `√det g` at the centre is
    `−(1/3) Ric(v,v)`:
    `∑_{cd} v^c v^d ∂_c∂_d √det g (0) = −(1/3) ∑_{cd} Ric_{cd} v^c v^d`.
    The diagonal `a₁` used only the *trace* `∑_i ∂_i² √det`; this is the full directional
    contraction — the leading OFF-DIAGONAL van-Vleck curvature coefficient, obtained from the metric
    2-jet without any matrix Jacobi field or `Y⁻¹`.  NOT the uniform-in-`v` radial ODE, NOT
    `a₁ = R/6` for the true kernel. -/
theorem sqrtdet_directional_hessian_ricci (g : Point n → Fin n → Fin n → ℝ)
    (Ric : Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (v : Point n) :
    ∑ c, ∑ d, v c * v d * pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0
      = -(1 / 3) * ∑ c, ∑ d, Ric c d * v c * v d := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [sqrtdet_pd_pd g Ric hg hg0 hdg0 htr c d]
  ring

/-! ### The leading van-Vleck radial ODE in exact quadratic-Taylor-model form -/

/-- **Radial (Euler) derivative of a constant-plus-scaled field**: `(r ∂_r)(a + k·Q) = k·(r ∂_r) Q`.
    The additive constant drops (`∂ᵢ const = 0`) and the scalar pulls through the Euler operator. -/
theorem radialDeriv_add_const_scalar (Q : Point n → ℝ) (a k : ℝ) (v : Point n)
    (hQ : ∀ i, PdiffAt Q i v) :
    radialDeriv (fun w => a + k * Q w) v = k * radialDeriv Q v := by
  simp only [radialDeriv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hconst : PdiffAt (fun _ : Point n => a) i v := by exact differentiableAt_const a
  have hkQ : PdiffAt (fun w => k * Q w) i v := PdiffAt_const_mul k Q i v (hQ i)
  rw [pd_add (fun _ => a) (fun w => k * Q w) i v hconst hkQ,
      pd_const a i v, zero_add, pd_const_mul k Q i v (hQ i)]
  ring

/-- **The radial derivative of the quadratic Taylor MODEL** `w ↦ 1 + ½ ∑_{cd} C_{cd} wᶜwᵈ`
    equals the directional contraction `∑_{cd} C_{cd} vᶜvᵈ` of its Hessian coefficient `C`.
    (The constant `1` drops, and Euler's identity `radialDeriv_quadraticForm` supplies the factor
    `2`, which the `½` cancels.)  UNCONDITIONAL in `C`. -/
theorem radialDeriv_taylorModel_quadratic (C : Fin n → Fin n → ℝ) (v : Point n) :
    radialDeriv (fun w => 1 + (1 / 2) * ∑ c, ∑ d, C c d * w c * w d) v
      = ∑ c, ∑ d, C c d * v c * v d := by
  have hPdQ : ∀ i, PdiffAt (fun w => ∑ c, ∑ d, C c d * w c * w d) i v := by
    intro i
    refine PdiffAt_sum Finset.univ _ i v (fun c _ =>
      PdiffAt_sum Finset.univ _ i v (fun d _ => ?_))
    exact PdiffAt_of_contDiff (fun w => C c d * w c * w d)
      ((contDiff_const.mul (coord_contDiff c)).mul (coord_contDiff d)) i v
  have step1 :
      radialDeriv (fun w => 1 + (1 / 2) * ∑ c, ∑ d, C c d * w c * w d) v
        = (1 / 2) * radialDeriv (fun w => ∑ c, ∑ d, C c d * w c * w d) v :=
    radialDeriv_add_const_scalar (fun w => ∑ c, ∑ d, C c d * w c * w d) 1 (1 / 2) v hPdQ
  rw [step1, radialDeriv_quadraticForm C v]; ring

/-- **Deliverable 1 — the linear Taylor term of `√det g` vanishes at the RNC centre.**
    At the normal-coordinate origin `det g (0) = det 1 = 1 ≠ 0`, so `√ ∘ det g` is differentiable
    there; the chain rule gives `∂_c √det g (0) = (∂_c det g (0))/(2√det g(0))`, and the numerator
    `∂_c det g (0)` vanishes because the metric's first jet vanishes (`det_pd_first`). -/
theorem sqrtdet_pd_zero (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0) (c : Fin n) :
    pd (fun y => Real.sqrt (Matrix.det (g y))) c 0 = 0 := by
  have hg0mat : g 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext i j; exact hg0 i j
  have hne : Matrix.det (g 0) ≠ 0 := by rw [hg0mat, Matrix.det_one]; norm_num
  rw [pd_comp_sqrt (fun w => Matrix.det (g w)) c 0
        (PdiffAt_of_contDiff _ (det_contDiff g hg) c 0) hne,
      det_pd_first g hg hdg0 c, mul_zero]

/-- **Deliverable 2 — the leading van-Vleck radial ODE, exact polynomial form.**
    Let `M w := 1 + ½ ∑_{cd} (∂_c∂_d √det g (0)) wᶜwᵈ` be the quadratic Taylor MODEL of `√det g`
    at the RNC centre: its constant is `√det g(0) = 1`, its linear term vanishes
    (`sqrtdet_pd_zero`), and its Hessian is the exact 2-jet `∂_c∂_d √det g (0)`.  Then the radial
    (Euler) derivative of this model is the leading van-Vleck curvature term
    `(r ∂_r) M = −(1/3) Ric(v,v)`, obtained by gluing the model-quadratic Euler identity
    `radialDeriv_taylorModel_quadratic` to the directional Hessian↔Ricci contraction
    `sqrtdet_directional_hessian_ricci`.  The four carried hypotheses (`hg`, `hg0`, `hdg0`, `htr`)
    are genuine equations on the metric — none assumes the conclusion.  This is the leading 2-jet
    term only; NOT `√det g` beyond its 2-jet, NOT the uniform-in-`v` all-orders radial ODE, NOT
    `a₁ = R/6` for the true kernel. -/
theorem sqrtdet_taylorModel_radialDeriv_ricci (g : Point n → Fin n → Fin n → ℝ)
    (Ric : Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (v : Point n) :
    radialDeriv (fun w => 1 + (1 / 2) * ∑ c, ∑ d,
        (pd (fun y => pd (fun w' => Real.sqrt (Matrix.det (g w'))) d y) c 0) * w c * w d) v
      = -(1 / 3) * ∑ c, ∑ d, Ric c d * v c * v d := by
  have hmodel :
      radialDeriv (fun w => 1 + (1 / 2) * ∑ c, ∑ d,
          (pd (fun y => pd (fun w' => Real.sqrt (Matrix.det (g w'))) d y) c 0) * w c * w d) v
        = ∑ c, ∑ d,
          (pd (fun y => pd (fun w' => Real.sqrt (Matrix.det (g w'))) d y) c 0) * v c * v d :=
    radialDeriv_taylorModel_quadratic
      (fun c d => pd (fun y => pd (fun w' => Real.sqrt (Matrix.det (g w'))) d y) c 0) v
  rw [hmodel]
  have key := sqrtdet_directional_hessian_ricci g Ric hg hg0 hdg0 htr v
  rw [← key]
  exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => by ring))

end QIQTH.VanVleckRadial
