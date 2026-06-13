/-
RotationBorn.lean — why the exponent is 2: only the square survives superposition-mixing.

GPT-5.5 consult (2026-06-13). The sharpest answer to "why |c|² and not |c|^α" is the finite core of the
Banach–Lamperti theorem on isometries of ℓ^p: for p ≠ 2 the only norm-preserving maps are coordinate
permutations and phases (rigid relabelling), whereas **only p = 2 admits the full continuous rotation /
unitary mixing group**. Unitary dynamics IS continuous amplitude-mixing — so the square is the unique
exponent whose total-probability normalization is preserved by the dynamics itself.

We machine-check the two-coordinate core (a 2×2 rotation is the elementary unitary mixing two amplitudes):

  Σ |c_k|^α  is invariant under every rotation of two coordinates  ⟺  α = 2.

* α = 2: `born_exponent_rotation_invariant` — the square is preserved by EVERY rotation (Pythagoras).
* α ≠ 2: `lpow_rotation_invariant_forces_two` — the 45° rotation of (1,0) is an explicit witness; invariance
  there forces `2^{1−α/2} = 1`, i.e. α = 2.
* capstone `rotation_invariant_iff_exponent_two`.

This sharpens "why exponent 2" past the two no-gos (`BornRoutes.sqRule_refinement_signals`,
`RankCountNoGo.no_multiplicity_rule_is_born`): the square is not merely the irreducible posit — it is the
ONLY power-law normalization compatible with the existence of continuous unitary evolution. Honest caveat
(GPT-5.5): this is close to Gleason in symmetry language, not a deeper non-circular principle — "unitary"
already means inner-product-preserving. But it is the cleanest statement of where the 2 comes from.

HONEST SCOPE: the two-coordinate (ℝ²) core; no `sorry`, no project axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace QIQTH.RotationBorn

/-- **The square is rotation-invariant (α = 2).** The `ℓ²` normalization of two amplitudes is preserved by
every rotation that mixes them — Pythagoras. This is the link the existence of unitary dynamics needs. -/
theorem born_exponent_rotation_invariant (x y θ : ℝ) :
    |x * Real.cos θ - y * Real.sin θ| ^ (2 : ℝ) + |x * Real.sin θ + y * Real.cos θ| ^ (2 : ℝ)
      = |x| ^ (2 : ℝ) + |y| ^ (2 : ℝ) := by
  have e : ∀ t : ℝ, |t| ^ (2 : ℝ) = t ^ 2 := fun t => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact sq_abs t
  simp only [e]
  linear_combination (x ^ 2 + y ^ 2) * Real.sin_sq_add_cos_sq θ

/-- **No other exponent survives mixing (α ≠ 2 fails).** If the `ℓ^α` normalization (α > 0) were preserved
by every rotation, then the 45° rotation of `(1,0)` — which sends it to `(√2/2, √2/2)` — would give
`2·(√2/2)^α = 1`, i.e. `2^{1−α/2} = 1`, forcing α = 2. So for α ≠ 2 there is an explicit rotation that
changes the normalization: only the square is mixing-invariant. -/
theorem lpow_rotation_invariant_forces_two (α : ℝ) (hα : 0 < α)
    (hinv : ∀ x y θ : ℝ,
      |x * Real.cos θ - y * Real.sin θ| ^ α + |x * Real.sin θ + y * Real.cos θ| ^ α
        = |x| ^ α + |y| ^ α) : α = 2 := by
  have h := hinv 1 0 (Real.pi / 4)
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four] at h
  simp only [one_mul, zero_mul, sub_zero, add_zero] at h
  rw [abs_one, abs_zero, Real.one_rpow, Real.zero_rpow hα.ne', add_zero] at h
  have hs : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  rw [abs_of_pos hs] at h
  have hpow : (0 : ℝ) < (Real.sqrt 2 / 2) ^ α := Real.rpow_pos_of_pos hs α
  have h2 : (2 : ℝ) * (Real.sqrt 2 / 2) ^ α = 1 := by linarith
  have hlog : Real.log ((2 : ℝ) * (Real.sqrt 2 / 2) ^ α) = 0 := by rw [h2, Real.log_one]
  rw [Real.log_mul (by norm_num) (ne_of_gt hpow), Real.log_rpow hs] at hlog
  have hlogsqrt : Real.log (Real.sqrt 2 / 2) = -(Real.log 2 / 2) := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]; ring
  rw [hlogsqrt] at hlog
  have hL : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hfac : Real.log 2 * (1 - α / 2) = 0 := by linear_combination hlog
  rcases mul_eq_zero.mp hfac with hc | hc
  · exact absurd hc hL
  · linarith

/-- **Why the Born exponent is 2 (the Banach–Lamperti core).** Among all power-law normalizations
`Σ|c_k|^α` (α > 0), the one invariant under continuous superposition-mixing (rotation of two amplitudes) is
*exactly* the square. Unitary dynamics is such mixing, so the square is the unique exponent compatible with
unitary evolution. -/
theorem rotation_invariant_iff_exponent_two (α : ℝ) (hα : 0 < α) :
    (∀ x y θ : ℝ,
      |x * Real.cos θ - y * Real.sin θ| ^ α + |x * Real.sin θ + y * Real.cos θ| ^ α
        = |x| ^ α + |y| ^ α) ↔ α = 2 := by
  refine ⟨lpow_rotation_invariant_forces_two α hα, ?_⟩
  rintro rfl
  exact fun x y θ => born_exponent_rotation_invariant x y θ

end QIQTH.RotationBorn
