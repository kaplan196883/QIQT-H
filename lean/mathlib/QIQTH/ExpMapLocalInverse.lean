/-
  ExpMapLocalInverse — the LOCAL INVERSE exponential map `Vmap_p = exp_p⁻¹`.

  Brick C1 (J4-14).  The forward exponential map `expMap g gi hC p : Point n → Point n` has a
  STRICT Fréchet derivative equal to the identity at the origin (`hasStrictFDerivAt_expMap`,
  ExpMap.lean).  Mathlib's inverse function theorem (`HasStrictFDerivAt.localInverse`,
  `…eventually_left_inverse`, `…eventually_right_inverse`, `…localInverse_apply_image`,
  `…to_localInverse`) then produces, for a FIXED base point `p`, a genuine local inverse function
  `expLocalInverse g gi hC p : Point n → Point n` with:

  * a two-sided inverse property (near `0` on the source, near `p = exp_p 0` on the target),
  * base value `exp_p⁻¹ p = 0`,
  * strict derivative `id` at `p` (since `id⁻¹ = id`).

  The identity strict derivative is turned into the `ContinuousLinearEquiv` the IFT requires via
  `ContinuousLinearEquiv.coe_refl` (`↑(refl) = ContinuousLinearMap.id`); `f'.symm = refl` because
  `refl.symm = refl`.

  HONEST CAPTION (binding): this is `exp_p`'s LOCAL inverse for a FIXED `p`, DERIVED entirely from the
  Mathlib inverse function theorem applied to the landed strict derivative `HasStrictFDerivAt exp_p id
  0`.  It is the fixed-`p` building block for the capstone's free parameter `Vmap q p`.  It does NOT
  build a global chart, does NOT derive the RNC gauge, is NOT a curved heat kernel, and does NOT move
  numerical-G.
-/
import Mathlib
import QIQTH.ExpMap
import QIQTH.PullbackMetric

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric
open Topology

variable {n : ℕ}

/-- The landed strict derivative `HasStrictFDerivAt exp_p id 0` re-expressed with the derivative as
    the coerced identity `ContinuousLinearEquiv` `refl` (the invertible form the inverse function
    theorem consumes).  Just `ContinuousLinearEquiv.coe_refl` applied to `hasStrictFDerivAt_expMap`. -/
theorem hasStrictFDerivAt_expMap_refl (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    HasStrictFDerivAt (expMap g gi hC p)
      ((ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n)) (0 : Point n) := by
  rw [ContinuousLinearEquiv.coe_refl]
  exact hasStrictFDerivAt_expMap g gi hC p

/-- **Brick C1 — the local inverse exponential map `exp_p⁻¹` for a fixed base point `p`.**
    The inverse function theorem's local inverse (`HasStrictFDerivAt.localInverse`) of the forward
    exponential map `expMap g gi hC p` at the origin, whose strict derivative is the identity.  This
    is the fixed-`p` building block for the capstone's `Vmap q p := expLocalInverse q p`. -/
noncomputable def expLocalInverse (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) : Point n → Point n :=
  (hasStrictFDerivAt_expMap_refl g gi hC p).localInverse
    (expMap g gi hC p) (ContinuousLinearEquiv.refl ℝ (Point n)) 0

/-- **Left inverse near the origin.**  `exp_p⁻¹ (exp_p v) = v` for `v` in a neighbourhood of `0`.
    Directly `HasStrictFDerivAt.eventually_left_inverse` of the exp-map strict derivative. -/
theorem expLocalInverse_expMap_eventually (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ∀ᶠ v in 𝓝 (0 : Point n), expLocalInverse g gi hC p (expMap g gi hC p v) = v :=
  (hasStrictFDerivAt_expMap_refl g gi hC p).eventually_left_inverse

/-- **Right inverse near the base point `p`.**  `exp_p (exp_p⁻¹ x) = x` for `x` in a neighbourhood of
    `p = exp_p 0`.  `HasStrictFDerivAt.eventually_right_inverse` gives it near `exp_p 0`; rewritten by
    `expMap_apply_zero` (`exp_p 0 = p`) to read "near `p`". -/
theorem expMap_expLocalInverse_eventually (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ∀ᶠ x in 𝓝 (p : Point n), expMap g gi hC p (expLocalInverse g gi hC p x) = x := by
  have h := (hasStrictFDerivAt_expMap_refl g gi hC p).eventually_right_inverse
  rwa [expMap_apply_zero] at h

/-- **Base value `exp_p⁻¹ p = 0`.**  The local inverse sends the base point to the origin.
    `HasStrictFDerivAt.localInverse_apply_image` gives `exp_p⁻¹ (exp_p 0) = 0`; rewrite `exp_p 0 = p`
    (`expMap_apply_zero`). -/
theorem expLocalInverse_apply_basepoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    expLocalInverse g gi hC p p = 0 := by
  have h := (hasStrictFDerivAt_expMap_refl g gi hC p).localInverse_apply_image
  rwa [expMap_apply_zero] at h

/-- **Strict derivative of the local inverse at `p` is the identity.**  `HasStrictFDerivAt exp_p⁻¹
    id p`.  From `HasStrictFDerivAt.to_localInverse` the inverse has strict derivative `(f')⁻¹` at
    `exp_p 0`; here `f' = refl`, `refl.symm = refl`, `↑refl = id`, and `exp_p 0 = p`.  This is the
    near-isometry fact `hcoord`/`H1` consume. -/
theorem hasStrictFDerivAt_expLocalInverse (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    HasStrictFDerivAt (expLocalInverse g gi hC p)
      (ContinuousLinearMap.id ℝ (Point n)) p := by
  have h := (hasStrictFDerivAt_expMap_refl g gi hC p).to_localInverse
  rwa [expMap_apply_zero, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl] at h

end QIQTH.ExpMap
