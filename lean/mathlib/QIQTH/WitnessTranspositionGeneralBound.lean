/-
  WitnessTranspositionGeneralBound — J4-823: the FULLY GENERAL two-variable transposition bound —
  closes the curved-chart sub-gap by dispensing with the displacement idealization entirely.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  The J4-818 transposition wall reconciles two orientations of the witness's second field-
  partial `Φ(p,q) := ∂ⱼ∂ᵢ[ p' ↦ H(p',q) ](p)`:
      kPrime  needs   `Φ(0, z)`   (field ∂ at 0, source `z`),
      sliver  gives   `Φ(z, 0)`   (field ∂ at `z`, source 0).
  J4-819/820/821/822 controlled their difference for a DISPLACEMENT kernel `H(p,q) = F(p−q)` (reducing
  to smoothness of the 1-variable `F`).  But the LIVE witness is `H(p,q) = (amplitude)(V(q,p))` with
  `V` the CURVED RNC inverse chart — NOT a pure displacement — so the displacement reduction left a
  "curved-chart correction" sub-gap: transporting the bound through `V`'s `(p,q)`-dependence.

  ── THE SHARPER OBSERVATION (this file).  The curved-chart correction is UNNECESSARY.  The
  transposition difference `Φ(0,z) − Φ(z,0)` is a difference of ONE two-variable function `Φ` at two
  points `(0,z)` and `(z,0)` whose distance is EXACTLY `‖z‖` (product/sup metric).  So for ANY jointly
  locally-Lipschitz `Φ`:
      `|Φ(0,z) − Φ(z,0)|  ≤  K · dist((0,z),(z,0))  =  K · ‖z‖`,
  with NO displacement structure, NO even/odd cancellation, and NO chart-specific analysis.  The
  witness's second field-partial `Φ` is jointly C^∞ (both slots) on the reach neighborhood — hence
  locally Lipschitz — so the transposition difference is O(‖z‖) = O(√ε) under the sliver window,
  matching the closed J4-817 sliver rate.  This dissolves BOTH the curved-chart correction AND the
  ∇R-cubic residual sub-gaps at once.

  ── RESULTS.
  * `dist_swap_pair`   — `dist((0,z),(z,0)) = ‖z‖` in `Point n × Point n`.
  * `general_transposition_diff_of_lipschitzOnWith` — `|Φ(0,z) − Φ(z,0)| ≤ K·‖z‖`.
  * `general_transposition_sliver_of_lipschitzOnWith` — `+ ‖z‖ ≤ √ε ⟹ ≤ K·√ε`.
  * `general_transposition_sliver_of_contDiffAt` — ★ from PURE joint smoothness at `(0,0)`:
    `∃ K r>0, ∀ ‖z‖<r ∧ ‖z‖≤√ε, |Φ(0,z) − Φ(z,0)| ≤ K·√ε`.

  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and does NOT by itself close `hCConv` on the live
  capstone.  It proves the two-variable transposition difference is O(√ε) on the sliver window for ANY
  kernel whose second field-partial `Φ` is jointly C¹ at `(0,0)` — a smoothness fact the C^∞ witness
  satisfies.  Wiring into the capstone still requires identifying the witness's `Φ` (the concrete
  `∂ⱼ∂ᵢ` in the field slot) and feeding this bound into `kPrime_opNorm_sliver_bound.hcomp` in place of
  the same-orientation sliver bound.  No `sorry`, no new axioms, no `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.Curvature

open QIQTH.Curvature
open scoped Topology NNReal

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- In `Point n × Point n` with the product (sup) metric, `dist((0,z),(z,0)) = ‖z‖`. -/
theorem dist_swap_pair (z : Point n) :
    dist (((0 : Point n), z)) ((z, (0 : Point n))) = ‖z‖ := by
  rw [Prod.dist_eq]
  simp only [dist_eq_norm, zero_sub, sub_zero, norm_neg, max_self]

/-- **★ J4-823 — THE GENERAL TWO-VARIABLE TRANSPOSITION BOUND.**  For ANY function `Φ` of two
    `Point n` variables that is `LipschitzOnWith K` on a set containing `(0,z)` and `(z,0)`, the
    transposition difference the `hCConv` wall reconciles obeys
        `|Φ(0,z) − Φ(z,0)| ≤ K · ‖z‖`.
    No displacement structure, no even/odd cancellation — the two evaluation points differ by exactly
    `‖z‖` in the product metric, so joint Lipschitz continuity alone bounds the difference. -/
theorem general_transposition_diff_of_lipschitzOnWith (Φ : Point n × Point n → ℝ) {K : ℝ≥0}
    {S : Set (Point n × Point n)} (hLip : LipschitzOnWith K Φ S) (z : Point n)
    (h1 : ((0 : Point n), z) ∈ S) (h2 : (z, (0 : Point n)) ∈ S) :
    |Φ ((0 : Point n), z) - Φ (z, (0 : Point n))| ≤ (K : ℝ) * ‖z‖ := by
  have hd := hLip.dist_le_mul ((0 : Point n), z) h1 (z, (0 : Point n)) h2
  rwa [Real.dist_eq, dist_swap_pair] at hd

/-- **★ J4-823 — SLIVER VERSION.**  Under the sliver window `‖z‖ ≤ √ε`, the general transposition
    difference obeys `|Φ(0,z) − Φ(z,0)| ≤ K·√ε` — the O(√ε) rate the closed J4-817 sliver carries. -/
theorem general_transposition_sliver_of_lipschitzOnWith (Φ : Point n × Point n → ℝ) {K : ℝ≥0}
    {ε : ℝ} {S : Set (Point n × Point n)} (hLip : LipschitzOnWith K Φ S) (z : Point n)
    (h1 : ((0 : Point n), z) ∈ S) (h2 : (z, (0 : Point n)) ∈ S) (hwin : ‖z‖ ≤ Real.sqrt ε) :
    |Φ ((0 : Point n), z) - Φ (z, (0 : Point n))| ≤ (K : ℝ) * Real.sqrt ε :=
  (general_transposition_diff_of_lipschitzOnWith Φ hLip z h1 h2).trans
    (mul_le_mul_of_nonneg_left hwin (by positivity))

/-- **★★★ J4-823 — TERMINAL: general transposition sliver bound from PURE JOINT SMOOTHNESS.**  If the
    witness's second field-partial `Φ : Point n × Point n → ℝ` is `ContDiffAt ℝ 1` at `(0,0)` — a
    smoothness fact the C^∞ witness kernel satisfies — then there are a Lipschitz constant `K` and a
    radius `r > 0` such that for every `z` with `‖z‖ < r` inside the sliver window `‖z‖ ≤ √ε`, the
    transposition difference obeys `|Φ(0,z) − Φ(z,0)| ≤ K·√ε`.  This closes the curved-chart correction
    AND the ∇R-cubic residual sub-gaps simultaneously: no displacement idealization, no chart-specific
    analysis, no even/odd cancellation — joint smoothness of the two-variable kernel is enough. -/
theorem general_transposition_sliver_of_contDiffAt (Φ : Point n × Point n → ℝ)
    (hC : ContDiffAt ℝ 1 Φ ((0 : Point n), (0 : Point n))) :
    ∃ (K : ℝ≥0) (r : ℝ), 0 < r ∧ ∀ (z : Point n) (ε : ℝ), ‖z‖ < r → ‖z‖ ≤ Real.sqrt ε →
      |Φ ((0 : Point n), z) - Φ (z, (0 : Point n))| ≤ (K : ℝ) * Real.sqrt ε := by
  obtain ⟨K, t, ht, hLip⟩ := hC.exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨K, r, hr, fun z ε hzr hwin => ?_⟩
  have hz0 : dist z (0 : Point n) = ‖z‖ := by rw [dist_eq_norm, sub_zero]
  have h1 : ((0 : Point n), z) ∈ t := hball (by
    rw [Metric.mem_ball, Prod.dist_eq]; simp only [dist_self, hz0, max_eq_right (norm_nonneg z)]
    exact hzr)
  have h2 : (z, (0 : Point n)) ∈ t := hball (by
    rw [Metric.mem_ball, Prod.dist_eq]; simp only [dist_self, hz0, max_eq_left (norm_nonneg z)]
    exact hzr)
  exact general_transposition_sliver_of_lipschitzOnWith Φ hLip z h1 h2 hwin

end QIQTH.HeatResidualBound
