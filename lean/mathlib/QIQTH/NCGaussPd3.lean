/-
  NCGaussPd3 — J4-334 brick A1 of the Sol-consult-#10 plan.  The pure-calculus core of the
  four-index normal-coordinate 2-jet derivation (†): the third-derivative-at-zero product lemmas
  for the coordinate calculus `pd` of `QIQTH.Curvature`.

  ONE brick of the `a₁ = R/6` heat-kernel campaign.  ⚠ NOT `a₁ = R/6`; this file proves NOTHING new
  about `R/6`.  It supplies the honest, satisfiable product-rule algebra that — combined with the
  Gauss-lemma gauge input (brick A2) — lets the four-index metric 2-jet be derived; every hypothesis
  here is the standard C^∞ smoothness carry the capstone already provides (no `:= True`, no new
  axioms, no vacuity, no unsatisfiable carry).

  ═══════════════════════════════════════════════════════════════════════════════════════════════
  CONTENT (the coordinate `x j` of `QIQTH.Curvature.Point n = Fin n → ℝ`):
    • `pd_coord`        — `∂_r (fun y => y j) (z) = δ_{jr}` (the Kronecker delta; a linear function's
                          partial is the constant Kronecker delta).
    • `contDiff_coord`  — the coordinate function is `C^∞`.
    • `contDiff_pd`     — the partial `∂_i f` of a `C^∞` field is `C^∞`.
    • `pd_coord_mul` / `pd_coord_mul'`  — (P1) the product rule `∂_r (x j · f) = δ_{jr} f + x j ∂_r f`.
    • `pd3_coord_mul`   — (P2) the third-derivative-at-`0` product corollary: every surviving term is a
                          Kronecker hit (an undifferentiated `x j` vanishes at `0`; a doubly-differentiated
                          coordinate vanishes).
    • `pd3_sum`         — (P3) the finite-sum corollary for `F = ∑ j, x j · f j`.
  ═══════════════════════════════════════════════════════════════════════════════════════════════
  No `sorry` (this header prose excepted), no new axioms, no `:= True`, no vacuous/unsatisfiable carries.
-/
import Mathlib
import QIQTH.Curvature

open QIQTH.Curvature
open scoped BigOperators

namespace QIQTH.NCGaussPd3

variable {n : ℕ}

/-! ### Coordinate-function calculus: smoothness and the Kronecker-delta partial. -/

/-- **The coordinate function `fun y => y j` is `C^∞`.**  It is a continuous-linear projection. -/
theorem contDiff_coord (j : Fin n) : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => y j) :=
  contDiff_apply ℝ ℝ j

/-- **`∂_r (fun y => y j) (z) = δ_{jr}`.**  The partial derivative of a coordinate (linear) function
    is the Kronecker delta.  Via `pd_eq_fderiv`: `fderiv (proj j) = proj j`, evaluated on the basis
    vector `Pi.single r 1`, gives `(Pi.single r 1) j = if j = r then 1 else 0`. -/
theorem pd_coord (j r : Fin n) (z : Point n) :
    pd (fun y => y j) r z = if j = r then (1 : ℝ) else 0 := by
  have hf : HasFDerivAt (fun y : Point n => y j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) z := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt (x := z)
  rw [pd_eq_fderiv (fun y => y j) r z hf.differentiableAt, hf.fderiv]
  simp [ContinuousLinearMap.proj_apply, Pi.single_apply]

/-- **The partial `∂_i f` of a `C^∞` field is `C^∞`.**  `∂_i f = (fderiv f ·)(eᵢ)` is a continuous-linear
    evaluation of the (smooth) Fréchet derivative field. -/
theorem contDiff_pd (f : Point n → ℝ) (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) (i : Fin n) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => pd f i y) := by
  have e : (fun y => pd f i y) = (fun y => fderiv ℝ f y (Pi.single i 1)) :=
    funext (fun y => pd_eq_fderiv f i y (hf.differentiable (by simp) y))
  rw [e]
  exact (hf.fderiv_right (m := ⊤) le_top).clm_apply contDiff_const

/-! ### `PdiffAt` helper closure lemmas for the derived fields. -/

/-- The coordinate function is partially differentiable in every direction at every point. -/
theorem PdiffAt_coord (j i : Fin n) (x : Point n) : PdiffAt (fun y => y j) i x :=
  PdiffAt_of_contDiff _ (contDiff_coord j) i x

/-- A constant multiple of a partially-differentiable field is partially differentiable. -/
theorem PdiffAt_const_mul (c : ℝ) {f : Point n → ℝ} {i : Fin n} {x : Point n}
    (hf : PdiffAt f i x) : PdiffAt (fun y => c * f y) i x :=
  hf.const_mul c

/-! ### P1 — the product rule specialization. -/

/-- **P1 (multiplicative-delta form).**  `∂_r (x j · h) (z) = δ_{jr} · h(z) + x j · ∂_r h (z)`, with the
    Kronecker delta written as `(if j = r then 1 else 0)`.  Immediate from `pd_mul` + `pd_coord`. -/
theorem pd_coord_mul' (h : Point n → ℝ) (hh : ContDiff ℝ (⊤ : WithTop ℕ∞) h) (j r : Fin n) (z : Point n) :
    pd (fun x => x j * h x) r z = (if j = r then (1 : ℝ) else 0) * h z + z j * pd h r z := by
  have hmul := pd_mul (fun y => y j) h r z (PdiffAt_coord j r z) (PdiffAt_of_contDiff h hh r z)
  simp only [pd_coord] at hmul
  exact hmul

/-- **P1 (mission form).**  `∂_r (x j · f) (z) = (if j = r then f z else 0) + x j · ∂_r f (z)`. -/
theorem pd_coord_mul (f : Point n → ℝ) (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) (j r : Fin n) (z : Point n) :
    pd (fun x => x j * f x) r z = (if j = r then f z else 0) + z j * pd f r z := by
  rw [pd_coord_mul' f hf j r z]
  split_ifs <;> ring

/-! ### P2 — the third-derivative-at-zero product corollary. -/

/-- **P2.**  The mixed third derivative at the origin of a coordinate-times-field product:
    `∂_p ∂_q ∂_r (x j · f) (0)` keeps only the three "Kronecker-hit" terms — the term where the `x j`
    factor is never differentiated carries a leftover `x j = 0` at the origin and dies, and there is no
    surviving derivative of a doubly-differentiated coordinate.  Honest `C^∞` hypothesis on `f`. -/
theorem pd3_coord_mul (f : Point n → ℝ) (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) (j p q r : Fin n) :
    pd (fun y => pd (fun z => pd (fun x => x j * f x) r z) q y) p 0
      = (if j = r then pd (fun y => pd f q y) p 0 else 0)
        + (if j = q then pd (fun y => pd f r y) p 0 else 0)
        + (if j = p then pd (fun z => pd f r z) q 0 else 0) := by
  -- Step A: rewrite the innermost partial as a function of `z`.
  have hA : (fun z => pd (fun x => x j * f x) r z)
      = (fun z => (if j = r then (1 : ℝ) else 0) * f z + z j * pd f r z) :=
    funext (fun z => pd_coord_mul' f hf j r z)
  rw [hA]
  -- Step B: differentiate once more (direction `q`), as a function of `y`.
  have hB : (fun y => pd (fun z => (if j = r then (1 : ℝ) else 0) * f z + z j * pd f r z) q y)
      = (fun y => (if j = r then (1 : ℝ) else 0) * pd f q y
          + ((if j = q then (1 : ℝ) else 0) * pd f r y + y j * pd (fun z => pd f r z) q y)) := by
    funext y
    rw [pd_add (fun z => (if j = r then (1 : ℝ) else 0) * f z) (fun z => z j * pd f r z) q y
          (PdiffAt_const_mul _ (PdiffAt_of_contDiff f hf q y))
          ((PdiffAt_coord j q y).mul (PdiffAt_pd f hf r q y)),
        pd_const_mul _ f q y (PdiffAt_of_contDiff f hf q y),
        pd_coord_mul' (fun z => pd f r z) (contDiff_pd f hf r) j q y]
  rw [hB]
  -- Step C: the final derivative (direction `p`) at the origin.
  have hu1 : PdiffAt (fun y => (if j = r then (1 : ℝ) else 0) * pd f q y) p 0 :=
    PdiffAt_const_mul _ (PdiffAt_pd f hf q p 0)
  have hu2 : PdiffAt (fun y => (if j = q then (1 : ℝ) else 0) * pd f r y) p 0 :=
    PdiffAt_const_mul _ (PdiffAt_pd f hf r p 0)
  have hu3 : PdiffAt (fun y => y j * pd (fun z => pd f r z) q y) p 0 :=
    (PdiffAt_coord j p 0).mul (PdiffAt_pd (fun z => pd f r z) (contDiff_pd f hf r) q p 0)
  rw [pd_add _ _ p 0 hu1 (hu2.add hu3),
      pd_const_mul _ (fun y => pd f q y) p 0 (PdiffAt_pd f hf q p 0),
      pd_add _ _ p 0 hu2 hu3,
      pd_const_mul _ (fun y => pd f r y) p 0 (PdiffAt_pd f hf r p 0),
      pd_coord_mul' (fun y => pd (fun z => pd f r z) q y)
        (contDiff_pd (fun z => pd f r z) (contDiff_pd f hf r) q) j p 0]
  simp only [Pi.zero_apply, zero_mul, add_zero]
  split_ifs <;> ring

/-! ### P3 — the finite-sum corollary. -/

/-- **P3.**  For `F = ∑ j, x j · f j`, the mixed third derivative at the origin collapses (via `P2` on
    each summand + `Finset.sum_ite_eq'`) to the three diagonal contributions. -/
theorem pd3_sum (f : Fin n → Point n → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : WithTop ℕ∞) (f j))
    (p q r : Fin n) :
    pd (fun y => pd (fun z => pd (fun x => ∑ j, x j * f j x) r z) q y) p 0
      = pd (fun y => pd (f r) q y) p 0 + pd (fun y => pd (f q) r y) p 0
        + pd (fun y => pd (f p) r y) q 0 := by
  -- push `∂_r` through the finite sum (as a function of `z`)
  have h1 : (fun z => pd (fun x => ∑ j, x j * f j x) r z)
      = (fun z => ∑ j, pd (fun x => x j * f j x) r z) := by
    funext z
    exact pd_sum Finset.univ (fun j => fun x => x j * f j x) r z
      (fun j _ => (PdiffAt_coord j r z).mul (PdiffAt_of_contDiff (f j) (hf j) r z))
  -- push `∂_q` through the finite sum (as a function of `y`)
  have h2 : (fun y => pd (fun z => ∑ j, pd (fun x => x j * f j x) r z) q y)
      = (fun y => ∑ j, pd (fun z => pd (fun x => x j * f j x) r z) q y) := by
    funext y
    exact pd_sum Finset.univ (fun j => fun z => pd (fun x => x j * f j x) r z) q y
      (fun j _ => PdiffAt_pd (fun x => x j * f j x) ((contDiff_coord j).mul (hf j)) r q y)
  -- push `∂_p` through the finite sum (at the origin)
  rw [h1, h2,
    pd_sum Finset.univ (fun j => fun y => pd (fun z => pd (fun x => x j * f j x) r z) q y) p 0
      (fun j _ => PdiffAt_pd (fun z => pd (fun x => x j * f j x) r z)
        (contDiff_pd (fun x => x j * f j x) ((contDiff_coord j).mul (hf j)) r) q p 0)]
  -- termwise `P2`, then collapse the three Kronecker sums
  have hterm : (∑ j, pd (fun y => pd (fun z => pd (fun x => x j * f j x) r z) q y) p 0)
      = ∑ j : Fin n, ((if j = r then pd (fun y => pd (f j) q y) p 0 else 0)
          + (if j = q then pd (fun y => pd (f j) r y) p 0 else 0)
          + (if j = p then pd (fun z => pd (f j) r z) q 0 else 0)) :=
    Finset.sum_congr rfl (fun j _ => pd3_coord_mul (f j) (hf j) j p q r)
  rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end QIQTH.NCGaussPd3
