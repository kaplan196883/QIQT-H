/-
  UniformFlowThirdBound — J4-75 (Brick-A β, C³ climb): the W3 layer.  The TRILINEAR POLARIZATION
  operator-norm bound — the exact one-order-up analogue of J4-69's bilinear
  `bilinear_opNorm_le_of_symm_diag_bound` — which turns a UNIFORM DIAGONAL cubic bound on a symmetric
  third jet into a UNIFORM operator-norm bound.  This is the reusable half of the W3 target that the
  "diagonal-then-polarize" (S-b) route needs on top of W1's diagonal cubic field bound
  (`uniformFlowTube_thirdVariation_uniform_bound`, `‖Z₃ 1‖ ≤ M₃j·‖a‖³`).

  ## Context

  * R3 (the C²/Hessian layer) is CLOSED.  Its polarization brick is J4-69's
    `bilinear_opNorm_le_of_symm_diag_bound`: a SYMMETRIC bounded bilinear `B` with a diagonal bound
    `‖B a a‖ ≤ M‖a‖²` has `‖B‖ ≤ 2M`, via the parallelogram-free identity
    `4•B a b = B(a+b)(a+b) − B(a−b)(a−b)`.
  * W1 (`UniformFlowThirdJet`, `uniformFlowTube_thirdVariation_uniform_bound`) gives the intrinsic
    THIRD-variation field `Z₃` along the FIXED base tube with a uniform cubic bound `‖Z₃ 1‖ ≤ M₃j·‖a‖³`.
  * W2 (`UniformFlowThirdJetClose`) closed the per-seed THIRD-jet EXISTENCE
    `∃ L₃, HasFDerivAt (fun w => (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w) a b) L₃ v`.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled bound, no `expRho`)

  All generic over real normed spaces `E`, `F` (NO inner product / parallelogram law — `Point n` with the
  sup norm does not satisfy it; the sharp constant is `9/2`, not `1`, exactly as R3's bilinear brick got
  `2` instead of `1`).

  * `symm_trilinear_polarization` — **the parallelogram-free TRILINEAR polarization identity.**  For a
    fully-symmetric (two transpositions `hs12`, `hs23`) bounded trilinear `B`,
        `B(x+y+z)(x+y+z)(x+y+z) − B(x+y−z)(x+y−z)(x+y−z) − B(x−y+z)(x−y+z)(x−y+z)`
          `+ B(x−y−z)(x−y−z)(x−y−z) = (24 : ℝ) • B x y z`.
    DERIVED: the SYMMETRY-FREE multilinear expansion equals `(4:ℝ)•(sum over the 6 permutations of
    B x y z)` (pure `module`), then the six permutations collapse to `B x y z` by the two transpositions.

  * `symm_trilinear_deg3_bound` — **the degree-3 polarization bound.**  From a diagonal bound
    `‖B a a a‖ ≤ M‖a‖³`, `24‖B x y z‖ ≤ M(‖x+y+z‖³ + ‖x+y−z‖³ + ‖x−y+z‖³ + ‖x−y−z‖³)`.

  * `trilinear_norm_apply_le_of_symm_diag_bound` — **the product bound.**  A symmetric trilinear `B` with
    diagonal bound `‖B a a a‖ ≤ M‖a‖³` (`M ≥ 0`) satisfies `‖B x y z‖ ≤ (9/2)·M·‖x‖·‖y‖·‖z‖`, via
    unit-vector rescaling (`‖x'+y'±z'‖ ≤ 3`, cubed `≤ 27`, four terms `⟹ 24‖·‖ ≤ 108M`).

  * `trilinear_opNorm_le_of_symm_diag_bound` — **W3's polarization operator-norm bound (generic).**  Such
    a `B` has `‖B‖ ≤ (9/2)·M`, via nested `opNorm_le_bound` / `opNorm_le_bound₂`.

  ## HONEST FIREWALL (binding) — what W3 for `uniformFlowExp` still needs

  This lands the reusable POLARIZATION half of the W3 (S-b) route, fully DERIVED and generic.  Feeding it
  to close W3 for `uniformFlowExp` needs the TWO firewalled inputs, exactly mirroring how J4-69's
  `bilinear_opNorm_le_of_symm_diag_bound` needed R3's diagonal value id + Hessian symmetry:

    * (P1) the DIAGONAL VALUE ID one order up — `B₃(q,v)(a,a,a) = (Z₃ 1).1` connecting the symmetric
      third jet to W1's intrinsic third-variation field endpoint.  This is the `hid_of_doubled_data`
      analogue for the TRIPLED flow (a whole-file brick, like `JacobiOperatorFDeriv`); the naive per-slot
      Grönwall on the quadruple field `Vf` (J4-73) does NOT give it because the doubled base curve's
      confinement radius grows with `‖a‖`,`‖b‖` (the inner Jacobi `~‖b‖·E`, the doubled factor `~‖a‖·E`),
      so `sup‖D(Φ̃)(W0)‖` scales with `1+‖a‖+‖b‖` and the exponential Grönwall constant is NOT polynomial.
    * (P2) full SYMMETRY of the third jet `B₃` (the two transpositions `hs12`, `hs23`) — Clairaut for the
      third iterated derivative of the `C^∞` map `uniformFlowExp q`, packaged onto the nested-`fderiv`
      third jet.

  With (P1)+(P2) in hand, W3 is a SHORT corollary of `trilinear_opNorm_le_of_symm_diag_bound` fed W1's
  cubic bound, giving `M₃ = (9/2)·M₃j`.  Both are CARRIED (genuine inputs), NOT the conclusion.  This file
  does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.  NO `expRho`.  W4 (`uniformFlowExp ∈ C³ ⟹ g̃ ∈ C²`)
  remains the next step.
-/
import QIQTH.UniformFlowThirdJetClose
import QIQTH.QuadrupleFlowSupply
import QIQTH.UniformFlowThirdJet
import QIQTH.UniformFlowHessianDiag
import QIQTH.UniformFlowHessianBound
import Mathlib

namespace QIQTH.ExpMap

open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

/-! ### The trilinear polarization operator-norm bound (generic real normed spaces) -/

section TrilinearPolarization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Parallelogram-free TRILINEAR polarization identity.**  For a bounded trilinear map `B` that is
    fully symmetric (given via the two adjacent transpositions `hs12 : B u v w = B v u w` and
    `hs23 : B u v w = B u w v`),
        `B(x+y+z)(x+y+z)(x+y+z) − B(x+y−z)(x+y−z)(x+y−z) − B(x−y+z)(x−y+z)(x−y+z)`
          `+ B(x−y−z)(x−y−z)(x−y−z) = (24 : ℝ) • B x y z`.
    DERIVED: the SYMMETRY-FREE multilinear expansion equals `(4:ℝ) • (sum of the 6 permutations of
    `B x y z`)` (pure `module` after distributing `map_add`/`map_sub`), then the six permutations collapse
    to `B x y z` by the two transpositions. -/
theorem symm_trilinear_polarization (B : E →L[ℝ] E →L[ℝ] E →L[ℝ] F)
    (hs12 : ∀ u v w, B u v w = B v u w) (hs23 : ∀ u v w, B u v w = B u w v)
    (x y z : E) :
    B (x + y + z) (x + y + z) (x + y + z) - B (x + y - z) (x + y - z) (x + y - z)
      - B (x - y + z) (x - y + z) (x - y + z) + B (x - y - z) (x - y - z) (x - y - z)
      = (24 : ℝ) • B x y z := by
  -- Step 1: the symmetry-free multilinear identity to the 6-permutation sum.
  have hexp :
      B (x + y + z) (x + y + z) (x + y + z) - B (x + y - z) (x + y - z) (x + y - z)
        - B (x - y + z) (x - y + z) (x - y + z) + B (x - y - z) (x - y - z) (x - y - z)
        = (4 : ℝ) • (B x y z + B x z y + B y x z + B y z x + B z x y + B z y x) := by
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    module
  -- Step 2: collapse the six permutations to `B x y z`.
  have e2 : B x z y = B x y z := (hs23 x y z).symm
  have e3 : B y x z = B x y z := (hs12 x y z).symm
  have e4 : B y z x = B x y z := by rw [hs23 y z x, hs12 y x z]
  have e5 : B z x y = B x y z := by rw [hs12 z x y, hs23 x z y]
  have e6 : B z y x = B x y z := by rw [hs23 z y x, hs12 z x y, hs23 x z y]
  rw [hexp, e2, e3, e4, e5, e6]
  module

/-- **The degree-3 polarization bound.**  From the diagonal bound `‖B a a a‖ ≤ M‖a‖³`,
    `24‖B x y z‖ ≤ M(‖x+y+z‖³ + ‖x+y−z‖³ + ‖x−y+z‖³ + ‖x−y−z‖³)`. -/
theorem symm_trilinear_deg3_bound (B : E →L[ℝ] E →L[ℝ] E →L[ℝ] F)
    (hs12 : ∀ u v w, B u v w = B v u w) (hs23 : ∀ u v w, B u v w = B u w v)
    {M : ℝ} (hdiag : ∀ a : E, ‖B a a a‖ ≤ M * ‖a‖ ^ 3) (x y z : E) :
    (24 : ℝ) * ‖B x y z‖
      ≤ M * (‖x + y + z‖ ^ 3 + ‖x + y - z‖ ^ 3 + ‖x - y + z‖ ^ 3 + ‖x - y - z‖ ^ 3) := by
  have h24 : ‖(24 : ℝ) • B x y z‖ = 24 * ‖B x y z‖ := by
    rw [norm_smul]; norm_num
  calc (24 : ℝ) * ‖B x y z‖
      = ‖(24 : ℝ) • B x y z‖ := h24.symm
    _ = ‖B (x + y + z) (x + y + z) (x + y + z) - B (x + y - z) (x + y - z) (x + y - z)
          - B (x - y + z) (x - y + z) (x - y + z) + B (x - y - z) (x - y - z) (x - y - z)‖ := by
        rw [symm_trilinear_polarization B hs12 hs23 x y z]
    _ ≤ ‖B (x + y + z) (x + y + z) (x + y + z)‖ + ‖B (x + y - z) (x + y - z) (x + y - z)‖
          + ‖B (x - y + z) (x - y + z) (x - y + z)‖ + ‖B (x - y - z) (x - y - z) (x - y - z)‖ := by
        refine le_trans (norm_add_le _ _) ?_
        refine add_le_add (le_trans (norm_sub_le _ _) ?_) (le_refl _)
        exact add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ M * ‖x + y + z‖ ^ 3 + M * ‖x + y - z‖ ^ 3 + M * ‖x - y + z‖ ^ 3 + M * ‖x - y - z‖ ^ 3 :=
        add_le_add (add_le_add (add_le_add (hdiag _) (hdiag _)) (hdiag _)) (hdiag _)
    _ = M * (‖x + y + z‖ ^ 3 + ‖x + y - z‖ ^ 3 + ‖x - y + z‖ ^ 3 + ‖x - y - z‖ ^ 3) := by ring

/-- **The product bound.**  A fully-symmetric bounded trilinear map with a diagonal bound
    `‖B a a a‖ ≤ M‖a‖³` (`M ≥ 0`) satisfies `‖B x y z‖ ≤ (9/2)·M·‖x‖·‖y‖·‖z‖`.  Unit-vector rescaling:
    at unit `x' y' z'`, `‖x'±y'±z'‖ ≤ 3` so each cube `≤ 27` and the four-term deg-3 bound gives
    `24‖B x' y' z'‖ ≤ 108M`, i.e. `‖B x' y' z'‖ ≤ (9/2)M`; then rescale. -/
theorem trilinear_norm_apply_le_of_symm_diag_bound (B : E →L[ℝ] E →L[ℝ] E →L[ℝ] F)
    (hs12 : ∀ u v w, B u v w = B v u w) (hs23 : ∀ u v w, B u v w = B u w v)
    {M : ℝ} (hM : 0 ≤ M) (hdiag : ∀ a : E, ‖B a a a‖ ≤ M * ‖a‖ ^ 3) (x y z : E) :
    ‖B x y z‖ ≤ (9 / 2) * M * ‖x‖ * ‖y‖ * ‖z‖ := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp
  rcases eq_or_ne y 0 with hy | hy
  · subst hy; simp
  rcases eq_or_ne z 0 with hz | hz
  · subst hz; simp
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set x' : E := (‖x‖⁻¹) • x with hx'
  set y' : E := (‖y‖⁻¹) • y with hy'
  set z' : E := (‖z‖⁻¹) • z with hz'
  have hnx' : ‖x'‖ = 1 := by
    rw [hx', norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hnx, inv_mul_cancel₀ (ne_of_gt hnx)]
  have hny' : ‖y'‖ = 1 := by
    rw [hy', norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hny, inv_mul_cancel₀ (ne_of_gt hny)]
  have hnz' : ‖z'‖ = 1 := by
    rw [hz', norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hnz, inv_mul_cancel₀ (ne_of_gt hnz)]
  -- Cube monotonicity: `‖w‖ ≤ 3 ⟹ ‖w‖³ ≤ 27`.
  have hn3 : ∀ w : E, ‖w‖ ≤ 3 → ‖w‖ ^ 3 ≤ 27 := by
    intro w hw
    have hnn := norm_nonneg w
    nlinarith [pow_le_pow_left₀ hnn hw 3]
  -- The unit diagonal bound `‖B x' y' z'‖ ≤ (9/2)M`.
  have hunit : ‖B x' y' z'‖ ≤ (9 / 2) * M := by
    have hd := symm_trilinear_deg3_bound B hs12 hs23 hdiag x' y' z'
    -- `‖x'±y'±z'‖³ ≤ 27` (all four sign patterns).
    have hA : ‖x' + y' + z'‖ ^ 3 ≤ 27 := hn3 _ (by
      calc ‖x' + y' + z'‖ ≤ ‖x' + y'‖ + ‖z'‖ := norm_add_le _ _
        _ ≤ ‖x'‖ + ‖y'‖ + ‖z'‖ := by
              refine add_le_add (norm_add_le _ _) (le_refl _)
        _ = 3 := by rw [hnx', hny', hnz']; norm_num)
    have hBb : ‖x' + y' - z'‖ ^ 3 ≤ 27 := hn3 _ (by
      calc ‖x' + y' - z'‖ ≤ ‖x' + y'‖ + ‖z'‖ := norm_sub_le _ _
        _ ≤ ‖x'‖ + ‖y'‖ + ‖z'‖ := by
              refine add_le_add (norm_add_le _ _) (le_refl _)
        _ = 3 := by rw [hnx', hny', hnz']; norm_num)
    have hC : ‖x' - y' + z'‖ ^ 3 ≤ 27 := hn3 _ (by
      calc ‖x' - y' + z'‖ ≤ ‖x' - y'‖ + ‖z'‖ := norm_add_le _ _
        _ ≤ ‖x'‖ + ‖y'‖ + ‖z'‖ := by
              refine add_le_add (norm_sub_le _ _) (le_refl _)
        _ = 3 := by rw [hnx', hny', hnz']; norm_num)
    have hD : ‖x' - y' - z'‖ ^ 3 ≤ 27 := hn3 _ (by
      calc ‖x' - y' - z'‖ ≤ ‖x' - y'‖ + ‖z'‖ := norm_sub_le _ _
        _ ≤ ‖x'‖ + ‖y'‖ + ‖z'‖ := by
              refine add_le_add (norm_sub_le _ _) (le_refl _)
        _ = 3 := by rw [hnx', hny', hnz']; norm_num)
    nlinarith [hd, hA, hBb, hC, hD, norm_nonneg (B x' y' z'), hM]
  -- Rescale back: `B x y z = (‖x‖·‖y‖·‖z‖) • B x' y' z'`.
  have hxx : x = ‖x‖ • x' := by
    rw [hx', smul_smul, mul_inv_cancel₀ (ne_of_gt hnx), one_smul]
  have hyy : y = ‖y‖ • y' := by
    rw [hy', smul_smul, mul_inv_cancel₀ (ne_of_gt hny), one_smul]
  have hzz : z = ‖z‖ • z' := by
    rw [hz', smul_smul, mul_inv_cancel₀ (ne_of_gt hnz), one_smul]
  have hxyz : B x y z = (‖x‖ * ‖y‖ * ‖z‖) • B x' y' z' := by
    conv_lhs => rw [hxx, hyy, hzz]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul]
    congr 1
    ring
  rw [hxyz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖x‖ * ‖y‖ * ‖z‖ * ‖B x' y' z'‖
      ≤ ‖x‖ * ‖y‖ * ‖z‖ * ((9 / 2) * M) :=
        mul_le_mul_of_nonneg_left hunit (by positivity)
    _ = (9 / 2) * M * ‖x‖ * ‖y‖ * ‖z‖ := by ring

/-- **W3's polarization operator-norm bound (generic).**  A fully-symmetric bounded trilinear map with a
    diagonal cubic bound `‖B a a a‖ ≤ M‖a‖³` (`M ≥ 0`) has operator norm `‖B‖ ≤ (9/2)·M`.  DERIVED from
    the product bound `trilinear_norm_apply_le_of_symm_diag_bound` via nested `opNorm_le_bound`. -/
theorem trilinear_opNorm_le_of_symm_diag_bound (B : E →L[ℝ] E →L[ℝ] E →L[ℝ] F)
    (hs12 : ∀ u v w, B u v w = B v u w) (hs23 : ∀ u v w, B u v w = B u w v)
    {M : ℝ} (hM : 0 ≤ M) (hdiag : ∀ a : E, ‖B a a a‖ ≤ M * ‖a‖ ^ 3) :
    ‖B‖ ≤ (9 / 2) * M := by
  refine B.opNorm_le_bound (by positivity) (fun x => ?_)
  refine (B x).opNorm_le_bound₂ (by positivity) (fun y z => ?_)
  exact trilinear_norm_apply_le_of_symm_diag_bound B hs12 hs23 hM hdiag x y z

end TrilinearPolarization

end QIQTH.ExpMap
