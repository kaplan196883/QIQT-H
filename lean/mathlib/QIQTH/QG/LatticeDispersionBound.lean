/-
  QG I3 (QG_CAMPAIGN_PLAN.md phase B) — the free-dispersion Lorentz-defect bound.

  The cheap, known FREE-FIELD PASS companion of the CPSUV gate: the lattice/QCA dispersion
  `E_a(p)² = m² + (4/a²)·sin²(ap/2)` deviates from the relativistic `m² + p²` by at most `a²p⁴/12` —
  the defect is `~(ap)²`-suppressed with NO rapidity-independent floor. This is exactly why the free-field
  test is NOT decisive (any lattice passes it) and the INTERACTING one-loop test (`CpsuvGate.lean`,
  `scripts/lorentz_stress_test.py`) is the gate that kills.

  Chain (all real calculus, axiom-free): `cos x ≥ 1 − x²/2` (Mathlib) ⟹ monotone `sin t − t + t³/6`
  ⟹ `sin u ≥ u − u³/6` (u ≥ 0) ⟹ `u² − sin²u ∈ [0, u⁴/3]` ⟹ the dispersion bound. Std-3.
-/
import Mathlib

namespace QIQTH.QG.Lattice

open Real

/-- The global cubic lower bound `sin u ≥ u − u³/6` for `u ≥ 0` (via the monotone antiderivative of
    `cos x − 1 + x²/2 ≥ 0`). -/
theorem sin_ge_sub_cube (u : ℝ) (hu : 0 ≤ u) : u - u ^ 3 / 6 ≤ Real.sin u := by
  have hdiff : Differentiable ℝ (fun t : ℝ => Real.sin t - t + t ^ 3 / 6) :=
    (Real.differentiable_sin.sub differentiable_id).add ((differentiable_pow 3).div_const 6)
  have hmono : MonotoneOn (fun t : ℝ => Real.sin t - t + t ^ 3 / 6) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact ((Real.continuous_sin.sub continuous_id).add
        ((continuous_pow 3).div_const 6)).continuousOn
    · exact hdiff.differentiableOn
    · intro x _
      have hD : HasDerivAt (fun t : ℝ => Real.sin t - t + t ^ 3 / 6)
          (Real.cos x - 1 + 3 * x ^ 2 / 6) x := by
        have h1 := (Real.hasDerivAt_sin x).sub (hasDerivAt_id x)
        have h2 := (hasDerivAt_pow 3 x).div_const 6
        have h12 := h1.add h2
        norm_num at h12 ⊢
        convert h12 using 1
      rw [hD.deriv]
      have hcos : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
      have h36 : (3 : ℝ) * x ^ 2 / 6 = x ^ 2 / 2 := by ring
      linarith [h36.le, h36.ge]
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
  have hu' : u ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hu
  have := hmono h0 hu' hu
  simp only [Real.sin_zero] at this
  linarith

/-- The two-sided linear bounds `−u ≤ sin u ≤ u` for `u ≥ 0`. -/
theorem sin_bounds (u : ℝ) (hu : 0 ≤ u) : -u ≤ Real.sin u ∧ Real.sin u ≤ u := by
  refine ⟨?_, Real.sin_le hu⟩
  rcases le_total u 1 with h | h
  · have hpi : u ≤ Real.pi := by linarith [Real.pi_gt_three]
    have : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu hpi
    linarith
  · have := Real.neg_one_le_sin u
    linarith

/-- `sin²u ≤ u²` (all real `u`). -/
theorem sin_sq_le_sq (u : ℝ) : Real.sin u ^ 2 ≤ u ^ 2 := by
  rcases le_total 0 u with hu | hu
  · obtain ⟨h1, h2⟩ := sin_bounds u hu
    nlinarith
  · obtain ⟨h1, h2⟩ := sin_bounds (-u) (by linarith)
    rw [Real.sin_neg] at h1 h2
    nlinarith

/-- The quartic defect bound `u² − sin²u ≤ u⁴/3` for `u ≥ 0` (factor as `(u−sin u)(u+sin u) ≤ (u³/6)(2u)`). -/
theorem sq_sub_sin_sq_le_of_nonneg (u : ℝ) (hu : 0 ≤ u) :
    u ^ 2 - Real.sin u ^ 2 ≤ u ^ 4 / 3 := by
  obtain ⟨h3, h2⟩ := sin_bounds u hu
  have h1 : u - Real.sin u ≤ u ^ 3 / 6 := by linarith [sin_ge_sub_cube u hu]
  have hfac : u ^ 2 - Real.sin u ^ 2 = (u - Real.sin u) * (u + Real.sin u) := by ring
  have hb : (u - Real.sin u) * (u + Real.sin u) ≤ (u ^ 3 / 6) * (2 * u) :=
    mul_le_mul h1 (by linarith) (by linarith) (by positivity)
  calc u ^ 2 - Real.sin u ^ 2 = (u - Real.sin u) * (u + Real.sin u) := hfac
    _ ≤ (u ^ 3 / 6) * (2 * u) := hb
    _ = u ^ 4 / 3 := by ring

/-- The quartic defect bound, all real `u` (evenness). -/
theorem sq_sub_sin_sq_le (u : ℝ) : u ^ 2 - Real.sin u ^ 2 ≤ u ^ 4 / 3 := by
  rcases le_total 0 u with hu | hu
  · exact sq_sub_sin_sq_le_of_nonneg u hu
  · have h := sq_sub_sin_sq_le_of_nonneg (-u) (by linarith)
    rw [Real.sin_neg] at h
    ring_nf at h ⊢
    linarith

/-- The lattice/QCA dispersion `E_a(p)² = m² + (4/a²)·sin²(ap/2)`. -/
noncomputable def latticeE2 (a m p : ℝ) : ℝ := m ^ 2 + (4 / a ^ 2) * Real.sin (a * p / 2) ^ 2

/-- **I3 CAPSTONE — the free-dispersion Lorentz-defect bound:** `|E_a(p)² − (m²+p²)| ≤ a²p⁴/12` — the
    free lattice defect is `(ap)²`-suppressed with NO floor. The FREE-FIELD PASS: not decisive (the
    interacting CPSUV gate is), but the certified statement that free finite-capacity kinematics can be
    arbitrarily close to Lorentz at low momentum. -/
theorem lattice_dispersion_defect_bound (a m p : ℝ) (ha : a ≠ 0) :
    |latticeE2 a m p - (m ^ 2 + p ^ 2)| ≤ a ^ 2 * p ^ 4 / 12 := by
  set u := a * p / 2 with hu
  have hkey : latticeE2 a m p - (m ^ 2 + p ^ 2) = (4 / a ^ 2) * (Real.sin u ^ 2 - u ^ 2) := by
    rw [latticeE2, hu]
    field_simp
    ring
  rw [hkey, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / a ^ 2)]
  have habs : |Real.sin u ^ 2 - u ^ 2| = u ^ 2 - Real.sin u ^ 2 := by
    rw [abs_sub_comm]
    exact abs_of_nonneg (by linarith [sin_sq_le_sq u])
  rw [habs]
  have h3 : (4 / a ^ 2) * (u ^ 4 / 3) = a ^ 2 * p ^ 4 / 12 := by
    rw [hu]
    field_simp
    ring
  calc (4 / a ^ 2) * (u ^ 2 - Real.sin u ^ 2)
      ≤ (4 / a ^ 2) * (u ^ 4 / 3) :=
        mul_le_mul_of_nonneg_left (sq_sub_sin_sq_le u) (by positivity)
    _ = a ^ 2 * p ^ 4 / 12 := h3

end QIQTH.QG.Lattice
