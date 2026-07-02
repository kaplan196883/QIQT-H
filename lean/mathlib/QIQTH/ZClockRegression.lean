/-
  W2 (TYPE_II_TRACE_PLAN.md) — the ℤ-clock regression: SHIFT quasi-invariance ≠ dual-circle invariance.

  The binding consult correction, machine-checked. For the discrete (ℤ-clock) crossed product, the exponential
  diagonal weight `zWeight A = ∑ e^n·A(n,n)` on finitely-supported core elements satisfies TWO different laws:
  • **`zWeight_shift_quasiInvariant`** — conjugation by the SHIFT (the discrete log-clock translation, the ℤ
    analogue of W1.5's dual shift) scales the weight by EXACTLY `e^{−1}` — the quasi-invariance that mirrors
    `τ∘θ_s = e^{−s}τ`;
  • **`zWeight_dualCircle_invariant`** — conjugation by the TRUE dual action of `M⋊ℤ` (the circle action
    `e_n ↦ e^{inθ}e_n`) leaves the weight INVARIANT (the diagonal phases cancel).
  The `e^{−1}` scaling is the SHIFT, not the dual action — mislabeling the two is the trap the consult flagged,
  and this module is the regression that keeps it impossible. Plus `zWeight_nonneg_of_diag_nonneg` (positivity on
  the diagonal-nonneg core) and `diagSum_superset` (the weight is stable under enlarging the support window).

  ⚠ Honest scope: finitely-supported (banded) core elements as ℤ×ℤ kernels — the honest domain the consult
  prescribed (bare crossed-product monomials have infinite weight); the operator/ℓ²(ℤ) packaging and the vN level
  stay with the main (ℝ-clock) ladder. Axiom-free, std-3.
-/
import Mathlib

namespace QIQTH.TypeIITrace

/-- A **banded ℤ-core element**: a kernel `A : ℤ → ℤ → ℂ` supported in the window `[−rad, rad]²`. -/
structure ZCore where
  /-- the kernel -/
  A : ℤ → ℤ → ℂ
  /-- the support radius -/
  rad : ℤ
  hsupp : ∀ m n : ℤ, (m ∉ Set.Icc (-rad) rad ∨ n ∉ Set.Icc (-rad) rad) → A m n = 0

/-- The exponential diagonal sum over a window. -/
noncomputable def diagSum (C : ZCore) (s : Finset ℤ) : ℂ :=
  ∑ n ∈ s, (Real.exp n : ℂ) * C.A n n

/-- **The ℤ dual weight** `zWeight A = ∑ e^n·A(n,n)` (over the support window). -/
noncomputable def zWeight (C : ZCore) : ℂ := diagSum C (Finset.Icc (-C.rad) C.rad)

/-- The weight is stable under enlarging the window (added diagonal entries vanish). -/
theorem diagSum_superset (C : ZCore) (s : Finset ℤ) (hs : Finset.Icc (-C.rad) C.rad ⊆ s) :
    diagSum C s = zWeight C := by
  rw [zWeight, diagSum, diagSum]
  refine (Finset.sum_subset hs fun n _ hn => ?_).symm
  have hnot : n ∉ Set.Icc (-C.rad) C.rad := by
    intro hc
    rw [Set.mem_Icc] at hc
    exact hn (Finset.mem_Icc.mpr hc)
  rw [C.hsupp n n (Or.inl hnot), mul_zero]

/-- **Conjugation by the SHIFT** (the discrete log-clock translation): `(S⁻¹AS)(m,n) = A(m+1, n+1)`. -/
def shiftConj (C : ZCore) : ZCore where
  A := fun m n => C.A (m + 1) (n + 1)
  rad := C.rad + 1
  hsupp := by
    intro m n hmn
    apply C.hsupp
    rcases hmn with h | h
    · left
      simp only [Set.mem_Icc] at h ⊢
      intro hc
      exact h ⟨by linarith [hc.1], by linarith [hc.2]⟩
    · right
      simp only [Set.mem_Icc] at h ⊢
      intro hc
      exact h ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- **Conjugation by the TRUE dual action** of `M⋊ℤ` (the circle action `e_n ↦ e^{inθ}e_n`):
    `(U_θ⁻¹AU_θ)(m,n) = e^{−imθ}·A(m,n)·e^{inθ}`. -/
noncomputable def dualCircleConj (θ : ℝ) (C : ZCore) : ZCore where
  A := fun m n => Complex.exp (-(Complex.I * m * θ)) * C.A m n * Complex.exp (Complex.I * n * θ)
  rad := C.rad
  hsupp := fun m n hmn => by rw [C.hsupp m n hmn, mul_zero, zero_mul]

/-- **W2a — SHIFT quasi-invariance: `zWeight(S⁻¹AS) = e^{−1}·zWeight(A)`.** The discrete log-clock translation
    scales the exponential weight by exactly `e^{−1}` — the ℤ mirror of the CPW scaling `τ∘θ_s = e^{−s}τ`
    (W1.5's `Iexp_dualShift`). ⚠ THE SHIFT, not the dual action. -/
theorem zWeight_shift_quasiInvariant (C : ZCore) :
    zWeight (shiftConj C) = (Real.exp (-1) : ℂ) * zWeight C := by
  have hwin : zWeight (shiftConj C) = diagSum (shiftConj C) (Finset.Icc (-(C.rad + 1)) (C.rad + 1)) := by
    rw [zWeight]
    rfl
  rw [hwin]
  have hreindex : diagSum (shiftConj C) (Finset.Icc (-(C.rad + 1)) (C.rad + 1))
      = ∑ m ∈ Finset.Icc (-C.rad) (C.rad + 2), (Real.exp ((m : ℝ) - 1) : ℂ) * C.A m m := by
    rw [diagSum]
    rw [show Finset.Icc (-C.rad) (C.rad + 2)
        = (Finset.Icc (-(C.rad + 1)) (C.rad + 1)).map
          ⟨fun n => n + 1, add_left_injective 1⟩ from ?_]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [Function.Embedding.coeFn_mk, shiftConj]
      push_cast
      ring_nf
    · rw [Finset.map_eq_image]
      ext m
      simp only [Finset.mem_image, Finset.mem_Icc, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hm1, hm2⟩
        exact ⟨m - 1, ⟨by linarith, by linarith⟩, by ring⟩
      · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
        exact ⟨by linarith, by linarith⟩
  rw [hreindex]
  have hpull : ∀ m : ℤ, (Real.exp ((m : ℝ) - 1) : ℂ) * C.A m m
      = (Real.exp (-1) : ℂ) * ((Real.exp m : ℂ) * C.A m m) := by
    intro m
    rw [show (m : ℝ) - 1 = (m : ℝ) + (-1) from by ring, Real.exp_add]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun m _ => hpull m, ← Finset.mul_sum]
  congr 1
  exact diagSum_superset C _ (Finset.Icc_subset_Icc (by linarith) (by linarith))

/-- **W2b — DUAL-CIRCLE invariance: `zWeight(U_θ⁻¹AU_θ) = zWeight(A)`.** The TRUE dual action of `M⋊ℤ` leaves
    the exponential weight INVARIANT — the diagonal phases cancel. Together with W2a this machine-checks the
    binding distinction: the `e^{−1}` scaling belongs to the SHIFT, never to the dual action. -/
theorem zWeight_dualCircle_invariant (θ : ℝ) (C : ZCore) :
    zWeight (dualCircleConj θ C) = zWeight C := by
  rw [zWeight, zWeight]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [dualCircleConj]
  have hph : Complex.exp (-(Complex.I * n * θ)) * C.A n n * Complex.exp (Complex.I * n * θ)
      = C.A n n := by
    rw [mul_comm (Complex.exp (-(Complex.I * n * θ)) * C.A n n) (Complex.exp (Complex.I * n * θ)),
      ← mul_assoc, ← Complex.exp_add]
    rw [show Complex.I * n * θ + -(Complex.I * n * θ) = 0 from by ring, Complex.exp_zero, one_mul]
  rw [hph]

/-- **Positivity on the diagonal-nonneg core**: if every diagonal entry is a nonnegative real, the weight is a
    nonnegative real. -/
theorem zWeight_nonneg_of_diag_nonneg (C : ZCore)
    (hpos : ∀ n : ℤ, 0 ≤ (C.A n n).re ∧ (C.A n n).im = 0) :
    0 ≤ (zWeight C).re ∧ (zWeight C).im = 0 := by
  rw [zWeight, diagSum]
  rw [Complex.re_sum, Complex.im_sum]
  constructor
  · refine Finset.sum_nonneg fun n _ => ?_
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (Real.exp_pos _).le (hpos n).1
  · refine Finset.sum_eq_zero fun n _ => ?_
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, (hpos n).2,
      mul_zero]

end QIQTH.TypeIITrace
