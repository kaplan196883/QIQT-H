/-
  EinsteinEquationOfState — the linear-algebraic CRUX of Jacobson's thermodynamic
  derivation of the Einstein field equation (Jacobson, PRL 1995).

  Jacobson derives Einstein's equation as an *equation of state*: demanding the Clausius
  relation `δQ = T δS` with horizon entropy `δS = η δA` (the holographic/area law) for
  EVERY local Rindler horizon gives, via Raychaudhuri focusing, a relation that holds for
  every null direction `k`:
        T_{μν} k^μ k^ν  =  (1/2πη) R_{μν} k^μ k^ν      for all null k.
  The step that upgrades this *scalar, per-direction* relation into a *tensor* field
  equation is pure linear algebra:

      a symmetric tensor that vanishes on the ENTIRE null cone of a Lorentzian metric
      is a scalar multiple of that metric.

  That is exactly what this file machine-checks, in (1+3) Minkowski, axiom-free. The
  differential geometry (the energy-flux integral, Raychaudhuri focusing) and the final
  conservation + contracted-Bianchi step that fixes `f = -½R + Λ` are NOT here — they are
  cited (see paper_strategy/51_GR_Emergent_EquationOfState.md). This file checks ONLY the
  algebraic crux: it does not, by itself, derive the Einstein equation.

  The symmetric tensor is carried by its entries `C : Fin 4 → Fin 4 → ℝ`; its quadratic
  form is written on four real components `x0 x1 x2 x3` (so no vector-evaluation overhead).
-/
import Mathlib

namespace QIQTH.EinsteinEOS

/-- Minkowski metric `(−,+,+,+)` on `Fin 4`, as a function of two indices. -/
def gm (i j : Fin 4) : ℝ := if i = j then (if i = 0 then -1 else 1) else 0

/-- The quadratic form of a *symmetric* tensor `C` evaluated on a 4-vector
    `(x0,x1,x2,x3)` — i.e. `∑_{μν} C_{μν} x^μ x^ν`, written out using `C i j = C j i`. -/
def QF (C : Fin 4 → Fin 4 → ℝ) (x0 x1 x2 x3 : ℝ) : ℝ :=
  C 0 0 * x0^2 + C 1 1 * x1^2 + C 2 2 * x2^2 + C 3 3 * x3^2
  + 2 * C 0 1 * x0 * x1 + 2 * C 0 2 * x0 * x2 + 2 * C 0 3 * x0 * x3
  + 2 * C 1 2 * x1 * x2 + 2 * C 1 3 * x1 * x3 + 2 * C 2 3 * x2 * x3

/-- **The algebraic crux of Jacobson's derivation.** A symmetric tensor `C` whose quadratic
    form vanishes on the *entire null cone* of Minkowski space (every `(x0,x1,x2,x3)` with
    `−x0²+x1²+x2²+x3² = 0`) is a scalar multiple of the metric: `C = c • g`. This is the step
    that turns the per-null-direction Clausius relation into a genuine tensor field equation. -/
theorem symmTensor_eq_smul_metric_of_null
    (C : Fin 4 → Fin 4 → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (h : ∀ x0 x1 x2 x3 : ℝ, (- x0^2 + x1^2 + x2^2 + x3^2 = 0) → QF C x0 x1 x2 x3 = 0) :
    ∃ c : ℝ, ∀ i j, C i j = c * gm i j := by
  -- evaluate the form on nine explicit null vectors
  have e1 := h 1 1 0 0 (by norm_num)
  have e2 := h 1 (-1) 0 0 (by norm_num)
  have e3 := h 1 0 1 0 (by norm_num)
  have e4 := h 1 0 (-1) 0 (by norm_num)
  have e5 := h 1 0 0 1 (by norm_num)
  have e6 := h 1 0 0 (-1) (by norm_num)
  have e7 := h 5 3 4 0 (by norm_num)      -- Pythagorean null vector (1,2 plane)
  have e8 := h 5 3 0 4 (by norm_num)      -- (1,3 plane)
  have e9 := h 5 0 3 4 (by norm_num)      -- (2,3 plane)
  simp only [QF] at e1 e2 e3 e4 e5 e6 e7 e8 e9
  ring_nf at e1 e2 e3 e4 e5 e6 e7 e8 e9
  -- extract the entries
  have hC01 : C 0 1 = 0 := by linarith
  have hC02 : C 0 2 = 0 := by linarith
  have hC03 : C 0 3 = 0 := by linarith
  have hC11 : C 1 1 = - C 0 0 := by linarith
  have hC22 : C 2 2 = - C 0 0 := by linarith
  have hC33 : C 3 3 = - C 0 0 := by linarith
  have hC12 : C 1 2 = 0 := by linarith
  have hC13 : C 1 3 = 0 := by linarith
  have hC23 : C 2 3 = 0 := by linarith
  refine ⟨- C 0 0, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [gm] <;>
    linarith [hC01, hC02, hC03, hC11, hC22, hC33, hC12, hC13, hC23,
              hsymm 0 1, hsymm 0 2, hsymm 0 3, hsymm 1 2, hsymm 1 3, hsymm 2 3]

/-- **Jacobson's step 4, as a field-equation statement.** If the stress tensor `T` and the
    Ricci tensor `E` obey the integrated Clausius relation on every null direction —
    `a · T(k,k) = E(k,k)` for all null `k`, which is what Raychaudhuri focusing supplies
    (TAKEN AS HYPOTHESIS here; the differential geometry is cited, not proved) — then they
    satisfy a genuine **tensor** equation up to a multiple of the metric:
        `a · T_{μν} = E_{μν} + f · g_{μν}`.
    Conservation `∇^μ T_{μν}=0` and the contracted Bianchi identity then fix
    `f = -½R + Λ`, giving the Einstein equation — that last step is cited, not here. -/
theorem einstein_tensor_eq_of_state
    (T E : Fin 4 → Fin 4 → ℝ) (hT : ∀ i j, T i j = T j i) (hE : ∀ i j, E i j = E j i)
    (a : ℝ)
    (clausius : ∀ x0 x1 x2 x3 : ℝ, (- x0^2 + x1^2 + x2^2 + x3^2 = 0) →
        a * QF T x0 x1 x2 x3 = QF E x0 x1 x2 x3) :
    ∃ f : ℝ, ∀ i j, a * T i j = E i j + f * gm i j := by
  set C : Fin 4 → Fin 4 → ℝ := fun i j => a * T i j - E i j with hC
  have hCsymm : ∀ i j, C i j = C j i := by
    intro i j; simp only [hC]; rw [hT i j, hE i j]
  have hnull : ∀ x0 x1 x2 x3 : ℝ, (- x0^2 + x1^2 + x2^2 + x3^2 = 0) → QF C x0 x1 x2 x3 = 0 := by
    intro x0 x1 x2 x3 hn
    have hlin : QF C x0 x1 x2 x3 = a * QF T x0 x1 x2 x3 - QF E x0 x1 x2 x3 := by
      simp only [QF, hC]; ring
    rw [hlin]; have := clausius x0 x1 x2 x3 hn; linarith
  obtain ⟨c, hc⟩ := symmTensor_eq_smul_metric_of_null C hCsymm hnull
  refine ⟨c, ?_⟩
  intro i j
  have h2 := hc i j
  simp only [hC] at h2
  linarith

/-- The bilinear form `∑_{ij} C_{ij} v^i v^j` of a tensor on a vector — the coordinate-free shape of `QF`. -/
def BL (C : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ) : ℝ := ∑ i, ∑ j, C i j * v i * v j

/-- `QF` is the bilinear form on the explicit 4-vector (for a symmetric tensor). -/
theorem QF_eq_BL (C : Fin 4 → Fin 4 → ℝ) (hC : ∀ i j, C i j = C j i) (x0 x1 x2 x3 : ℝ) :
    QF C x0 x1 x2 x3 = BL C ![x0, x1, x2, x3] := by
  simp only [BL, QF, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  rw [hC 1 0, hC 2 0, hC 3 0, hC 2 1, hC 3 1, hC 3 2]; ring

/-- **The algebraic crux for a GENERAL Lorentzian metric** (Phase 3 — the framework bridge).
    A symmetric tensor `C` whose bilinear form vanishes on the *entire null cone* of an arbitrary
    Lorentzian metric `g` is a scalar multiple of `g`. The Lorentzian hypothesis enters as Sylvester's
    law of inertia: `g` is congruent to Minkowski, `g = Pᵀ·η·P` for an invertible `P` (`hcong` with
    `P`, `Pinv` a two-sided inverse). The proof is a **congruence reduction** to the proven
    Minkowski case `symmTensor_eq_smul_metric_of_null`: transform `C` by `Pinv`, apply the Minkowski
    lemma, transform back. This is exactly what upgrades Jacobson's per-null Clausius relation
    (stated in each point's local inertial frame) into the tensor field equation. -/
theorem symmTensor_eq_smul_metric_of_null_general
    (C g : Fin 4 → Fin 4 → ℝ) (hCsymm : ∀ i j, C i j = C j i)
    (P Pinv : Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ i j, (∑ k, P i k * Pinv k j) = if i = j then (1:ℝ) else 0)
    (hPP' : ∀ i j, (∑ k, Pinv i k * P k j) = if i = j then (1:ℝ) else 0)
    (hcong : ∀ i j, g i j = ∑ k, ∑ l, P k i * gm k l * P l j)
    (hnull : ∀ v : Fin 4 → ℝ, BL g v = 0 → BL C v = 0) :
    ∃ c : ℝ, ∀ i j, C i j = c * g i j := by
  -- A `Q`-congruence of a tensor, read off through its bilinear form (pure Fin-4 rearrangement).
  have BL_transform : ∀ (M Q : Fin 4 → Fin 4 → ℝ) (w : Fin 4 → ℝ),
      BL M (fun a => ∑ k, Q a k * w k)
        = ∑ k, ∑ l, (∑ i, ∑ j, Q i k * M i j * Q j l) * w k * w l := by
    intro M Q w; simp only [BL, Fin.sum_univ_four]; ring
  -- Minkowski bilinear form, explicit.
  have BL_gm : ∀ w : Fin 4 → ℝ, BL gm w = - (w 0)^2 + (w 1)^2 + (w 2)^2 + (w 3)^2 := by
    intro w; simp only [BL, gm, Fin.sum_univ_four, Fin.reduceEq, reduceIte]; ring
  -- `g` is the `P`-congruence of `gm`.
  have hg_eq : ∀ v : Fin 4 → ℝ, BL g v = BL gm (fun a => ∑ k, P a k * v k) := by
    intro v
    rw [BL_transform gm P v, BL]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [hcong k l]
  -- `P` undoes `Pinv` on vectors.
  have hPu : ∀ (w : Fin 4 → ℝ) (a : Fin 4),
      (∑ k, P a k * (∑ m, Pinv k m * w m)) = w a := by
    intro w a
    have step : (∑ k, P a k * (∑ m, Pinv k m * w m)) = ∑ k, ∑ m, P a k * Pinv k m * w m := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [step, Finset.sum_comm]
    have step2 : ∀ m, (∑ k, P a k * Pinv k m * w m) = (if a = m then (1:ℝ) else 0) * w m := by
      intro m; rw [← hPP a m, Finset.sum_mul]
    simp_rw [step2]; simp
  -- the `Pinv`-congruence of `C` is symmetric.
  have hC'symm : ∀ k l, (∑ i, ∑ j, Pinv i k * C i j * Pinv j l)
      = (∑ i, ∑ j, Pinv i l * C i j * Pinv j k) := by
    intro k l
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [hCsymm q p]; ring
  -- apply the Minkowski crux to the transformed tensor `C' = Pinvᵀ C Pinv`.
  obtain ⟨c, hc⟩ := symmTensor_eq_smul_metric_of_null
    (fun k l => ∑ i, ∑ j, Pinv i k * C i j * Pinv j l) hC'symm
    (by
      intro x0 x1 x2 x3 hn
      rw [QF_eq_BL _ hC'symm]
      have key : BL (fun k l => ∑ i, ∑ j, Pinv i k * C i j * Pinv j l) ![x0, x1, x2, x3]
          = BL C (fun a => ∑ k, Pinv a k * (![x0, x1, x2, x3] : Fin 4 → ℝ) k) :=
        (BL_transform C Pinv ![x0, x1, x2, x3]).symm
      rw [key]
      apply hnull
      rw [hg_eq]
      have hPid : (fun a => ∑ k, P a k * (∑ m, Pinv k m * (![x0, x1, x2, x3] : Fin 4 → ℝ) m))
          = (![x0, x1, x2, x3] : Fin 4 → ℝ) := by
        funext a; exact hPu _ a
      rw [hPid, BL_gm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      linarith [hn])
  -- transform back: `C = Pᵀ C' P = c·g`.
  have hCrecon : ∀ i j, C i j
      = ∑ k, ∑ l, P k i * (∑ a, ∑ b, Pinv a k * C a b * Pinv b l) * P l j := by
    intro i j
    have h1 : (∑ a, ∑ b, C a b * (∑ k, Pinv a k * P k i) * (∑ l, Pinv b l * P l j)) = C i j := by
      simp only [hPP']
      simp [Finset.sum_ite_eq', mul_ite]
    have h2 : (∑ a, ∑ b, C a b * (∑ k, Pinv a k * P k i) * (∑ l, Pinv b l * P l j))
        = ∑ k, ∑ l, P k i * (∑ a, ∑ b, Pinv a k * C a b * Pinv b l) * P l j := by
      simp only [Fin.sum_univ_four]; ring
    exact h1.symm.trans h2
  refine ⟨c, fun i j => ?_⟩
  rw [hCrecon i j]
  simp only [hc]
  rw [hcong i j, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by ring)

end QIQTH.EinsteinEOS
