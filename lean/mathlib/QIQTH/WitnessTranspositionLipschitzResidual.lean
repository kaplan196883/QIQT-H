/-
  WitnessTranspositionLipschitzResidual — J4-821: the transposition residual's sliver bound from PLAIN
  LOCAL LIPSCHITZ regularity of the kernel's second partial — no even/odd cancellation needed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (J4-820).  `residual_sliver_bound` reduced the J4-818 transposition wall to the interface
  hypothesis `hodd : |G(−z) − G(z)| ≤ L·‖z‖`, where `G = ∂ⱼ∂ᵢF` is the displacement kernel's second
  field-partial.  The sympy census justified `hodd` via the cubic-∇R odd-amplitude structure.

  ── THE SHARPER OBSERVATION (this file).  `hodd` does NOT require the delicate even/odd (∇R-cubic)
  cancellation at all — it follows from PLAIN LOCAL LIPSCHITZ CONTINUITY of `G` near the origin:
      `|G(−z) − G(z)|  =  dist(G(−z), G(z))  ≤  L · dist(−z, z)  =  L · 2‖z‖  =  2L·‖z‖`.
  Both endpoints `±z` lie in the origin-ball once `‖z‖ ≤ √ε`, and the second field-partial of the
  witness kernel IS locally Lipschitz because the C^∞ geometry makes the kernel C³ near 0.  So the
  transposition residual is controlled by REGULARITY ALONE.

  ── RESULT.  `residual_sliver_bound_of_lipschitzOnWith`: if `G = ∂ⱼ∂ᵢF` is `LipschitzOnWith L` on a
  set containing `±z`, and `‖z‖ ≤ √ε`, then the transposition residual obeys `|residual| ≤ 2L·√ε` —
  matching (up to the harmless factor 2) the O(√ε) rate the closed J4-817 sliver bound carries.  Also
  `hodd_of_lipschitzOnWith`, discharging J4-820's abstract `hodd` interface from the same Lipschitz
  data.

  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and does NOT by itself close `hCConv`.  It shows the
  J4-820 `hodd` interface is discharged by local Lipschitz continuity of the kernel's second partial —
  a C³ regularity fact.  Wiring into the live capstone still requires the concrete curved-RNC-chart
  second-partial to be exhibited as `LipschitzOnWith L` on an origin-ball (its C³-ness is available
  from the C^∞ geometry, but the explicit `LipschitzOnWith` witness on the curved chart is the residual
  work).  No `sorry`, no new axioms, no `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.WitnessTranspositionResidualBound

open QIQTH.Curvature
open scoped Topology NNReal

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- `dist (−z) z = 2·‖z‖` in the normed space `Point n`. -/
theorem dist_neg_self (z : Point n) : dist (-z) z = 2 * ‖z‖ := by
  rw [dist_eq_norm]
  have hz : -z - z = (-2 : ℝ) • z := by module
  rw [hz, norm_smul]
  norm_num

/-- **★ J4-821 — `hodd` FROM LOCAL LIPSCHITZ.**  The J4-820 interface hypothesis `hodd`
    (`|G(−z) − G(z)| ≤ L'·‖z‖`) is discharged from PLAIN local Lipschitz continuity of the kernel's
    second partial `G = ∂ⱼ∂ᵢF` — no even/odd cancellation required.  The constant is `L' = 2L`. -/
theorem hodd_of_lipschitzOnWith (F : Point n → ℝ) (i j : Fin n) (z : Point n) {L : ℝ≥0}
    {S : Set (Point n)} (hLip : LipschitzOnWith L (fun w => pd (fun y => pd F i y) j w) S)
    (hmz : -z ∈ S) (hpz : z ∈ S) :
    |pd (fun y => pd F i y) j (-z) - pd (fun y => pd F i y) j z| ≤ (2 * L) * ‖z‖ := by
  have hd := hLip.dist_le_mul (-z) hmz z hpz
  rw [Real.dist_eq, dist_neg_self] at hd
  calc |pd (fun y => pd F i y) j (-z) - pd (fun y => pd F i y) j z|
      ≤ (L : ℝ) * (2 * ‖z‖) := hd
    _ = (2 * L) * ‖z‖ := by ring

/-- **★★★ J4-821 — THE SLIVER BOUND FROM LOCAL LIPSCHITZ.**  If the kernel's second field-partial
    `G = ∂ⱼ∂ᵢF` is `LipschitzOnWith L` on a set `S` containing both endpoints `±z`, and `‖z‖ ≤ √ε`,
    then the source↔field transposition residual obeys `|residual| ≤ 2L·√ε` — matching the O(√ε) rate
    the closed J4-817 sliver bound carries.  This DISCHARGES the J4-820 `hodd` interface from pure C³
    regularity, so the J4-818 transposition wall reduces to exhibiting the curved-chart second partial
    as `LipschitzOnWith L` on an origin-ball (available from the C^∞ geometry). -/
theorem residual_sliver_bound_of_lipschitzOnWith
    (F : Point n → ℝ) (i j : Fin n) (z : Point n) {L : ℝ≥0} {ε : ℝ} {S : Set (Point n)}
    (hLip : LipschitzOnWith L (fun w => pd (fun y => pd F i y) j w) S)
    (hmz : -z ∈ S) (hpz : z ∈ S) (hwin : ‖z‖ ≤ Real.sqrt ε) :
    |pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
      - pd (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) j z| ≤ (2 * L) * Real.sqrt ε := by
  refine residual_sliver_bound F i j z (L := (2 * L : ℝ)) (ε := ε) (by positivity) ?_ hwin
  exact hodd_of_lipschitzOnWith F i j z hLip hmz hpz

end QIQTH.HeatResidualBound
