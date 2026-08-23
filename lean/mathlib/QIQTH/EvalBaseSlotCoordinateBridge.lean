/-
  EvalBaseSlotCoordinateBridge — J4-1048: the algebraic coordinate-bridge relationship between the
  BASE-slot chart `w_b := uniformInverseChart z x` (J4-1046/1014/1020/1022/1023's coordinate) and the
  EVAL-slot chart `w_e := uniformInverseChart x z` (J4-1012/1013's coordinate) — the missing link J4-1047
  precisely diagnosed as blocking `r6`'s composition.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  J4-1047's plan-review (gpt-5.6-sol, high) confirmed: `w_e := uniformInverseChart g gi hC hK
  x z` (base `x` FIXED, eval `z` running) and `w_b := uniformInverseChart g gi hC hK z x` (base `z`
  running, eval `x` FIXED) are two DIFFERENT `w`-coordinates for the SAME `z`, and the only banked link
  (`gaussDdim_reversal_link` / `reversal_link_ball_integral`) bridges only the two GAUSSIAN VALUES,
  never the image sets, inverse maps, Jacobians, or amplitudes.

  This dispatch located the RAW (non-Gaussian-wrapped) identity underneath that Gaussian link, already
  banked axiom-free in `GeodesicReversalRouteAtPoint.baseSlot_eventuallyEq_neg_terminalVel_at`:
      `(fun z => uniformInverseChart g gi hC hK z x) =ᶠ[𝓝 x]
        (fun z => − terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z))`,
  i.e. `w_b(z) =ᶠ[𝓝 x] − T_x(w_e(z))`, `T_x := terminalVelAt g gi hC hK x`.  A plan-review by
  gpt-5.6-sol (high, this dispatch) confirmed: (1) extracting an explicit radius from this raw identity
  (mirroring J4-1013's `reversal_link_ball_radius` recipe) is a genuine, useful, GO deliverable; (2) the
  IMAGE-SET identity `w_b '' D = (−T_x) '' (w_e '' D)` follows from PURE SET ALGEBRA
  (`Set.image_image` + `Set.image_congr`) given the pointwise identity on `D` — **no invertibility of
  `T_x` is needed**, contrary to J4-1013's honesty-firewall note (which was about a *different*, harder
  claim: identifying `w_e''(ball x ρ)` with `ball 0 R`, not this pure algebraic image identity); (3) the
  derivative/Jacobian factorization `D w_b(z) = −(D T_x(w_e z)) ∘ (D w_e z)` is a genuine chain-rule
  consequence, STATED CONDITIONALLY on `HasFDerivAt` hypotheses for `T_x` and `w_e` at the relevant
  points (deliberately NOT assuming `T_x` is a local diffeomorphism or globally invertible — Sol flagged
  a standalone IFT/`PartialHomeomorph` package for `T_x` as NO-GO today, a genuinely large duplicate-
  scale undertaking); (4) a companion SETWISE left-inverse relation `V_b(−T_x w) = V_e(w)` follows
  purely from the two chart CoV packages' own EXISTING left-inverse witnesses (`V_b ∘ w_b = id`,
  `V_e ∘ w_e = id` on their respective domains) composed with the raw pointwise bridge — again NO
  inversion of `T_x` itself required.

  THIS FILE supplies, generically (abstract `Wb We T`, `Vb Ve`) AND concretely (`uniformInverseChart`,
  `terminalVelAt`):
    §1 `bridge_image_eq` / `bridge_hasFDerivAt` / `bridge_det_abs` / `bridge_left_inverse` — the four
       abstract algebraic bridge facts, reusable by ANY future concrete instantiation (not committed to
       J4-1012's / J4-1046's exact CoV-package shapes, which differ in how `V`/`f'` are packaged).
    §2 `evalBase_slot_coordinate_bridge_radius` — the concrete, explicit-radius RAW vector identity
       (mirrors J4-1013's `reversal_link_ball_radius`, but for the raw `w_b`/`w_e` pair, not the
       Gaussian-wrapped version).
    §3 `evalBase_slot_coordinate_bridge_image_ball` — the concrete image-set corollary: for the SAME
       explicit `r`, every `D ⊆ ball x r` satisfies `w_b '' D = (−T_x) '' (w_e '' D)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`. No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited (NEW FILE).

  ── WHAT THIS FILE DOES **NOT** DO.  It does **NOT** build a local-diffeomorphism / IFT /
  `PartialHomeomorph` package for `T_x` (confirmed NO-GO today by gpt-5.6-sol: `T_x` is only known
  norm-controlled + `ContDiffAt ℝ 2` AT THE SINGLE POINT `0`, not proven differentiable/invertible on a
  full neighborhood — `bridge_hasFDerivAt` therefore takes `HasFDerivAt T_x A_T (w_e z)` as an EXPLICIT
  HYPOTHESIS, not something this file discharges). It does **NOT** instantiate §1's abstract facts at
  J4-1012's/J4-1046's ACTUAL `V`/`f'` objects (those two packages' `V`/`f'` come from structurally
  different existential bundles — `ChartIFTPackageGeneralQ0`'s M1–M4 tuple vs J4-1043's `K∩U` wrapper's
  own tuple — reconciling those two SPECIFIC bundles into one composed CoV, and reconciling the THREE
  independently-existentially-quantified radii (`r` here, J4-1012's `ρ`, J4-1046's `R`), remains a
  SEPARATE, NOT-attempted next step). It does **NOT** compose any of this with `terminalVelAt_
  chartReplace_sliver_bound`, `kPrime`'s literal factorization, or J4-1047's amplitude-weighted sliver
  bound into any literal difference-form bound on `nb`. It does **NOT** discharge `r6`, `nb`, `hCConv`,
  or any part of `hcomp`. `Bfac`'s other 3 summands and `fb` remain untouched. `a₁ = R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.GeodesicReversalRouteAtPoint

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound
open QIQTH.GeodesicReversalRouteAtPoint
open scoped Topology

namespace QIQTH.EvalBaseSlotCoordinateBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the ABSTRACT algebraic bridge facts (generic `Wb, We, T`, generic `Vb, Ve`).
    ############################################################################### -/

/-- **`bridge_image_eq`.**  Pure set algebra: if `Wb z = − T (We z)` for every `z ∈ D`, then the image
    sets are literally related by `−T`:  `Wb '' D = (fun w => −T w) '' (We '' D)`.  NO invertibility of
    `T` is needed — this is `Set.image_congr` composed with `Set.image_image`.  NOT `a₁ = R/6`. -/
theorem bridge_image_eq (Wb We T : Point n → Point n) (D : Set (Point n))
    (hbridge : ∀ z ∈ D, Wb z = -T (We z)) :
    Wb '' D = (fun w => -T w) '' (We '' D) := by
  rw [Set.image_image]
  exact Set.image_congr hbridge

/-- **`bridge_hasFDerivAt`.**  Chain-rule factorization of `Wb`'s derivative through the bridge: given
    the pointwise identity `Wb w = − T (We w)` holding on the OPEN ball `ball x r` (so it upgrades to an
    `EventuallyEq` at any interior point `z`), and derivatives `We` at `z` / `T` at `We z`, the composed
    derivative of `Wb` at `z` is `−(A_T ∘ A_e)`.  Deliberately hypothesis-driven on `HasFDerivAt T A_T
    (We z)` — does NOT assume `T` is differentiable everywhere nor invertible.  NOT `a₁ = R/6`. -/
theorem bridge_hasFDerivAt (Wb We T : Point n → Point n) {r : ℝ} (hr : 0 < r) {x z : Point n}
    (hz : dist z x < r)
    (hbridge : ∀ w, dist w x < r → Wb w = -T (We w))
    {Ae AT : Point n →L[ℝ] Point n}
    (hWe' : HasFDerivAt We Ae z) (hT' : HasFDerivAt T AT (We z)) :
    HasFDerivAt Wb (-(AT.comp Ae)) z := by
  have hcompRaw : HasFDerivAt (fun w => T (We w)) (AT.comp Ae) z := hT'.comp z hWe'
  have hcomp : HasFDerivAt (fun w => -T (We w)) (-(AT.comp Ae)) z := hcompRaw.neg
  have hzball : z ∈ Metric.ball x r := Metric.mem_ball.mpr hz
  have hnhd : Metric.ball x r ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hzball
  have heq : Wb =ᶠ[𝓝 z] (fun w => -T (We w)) := by
    filter_upwards [hnhd] with w hw
    exact hbridge w (Metric.mem_ball.mp hw)
  exact hcomp.congr_of_eventuallyEq heq

/-- **`bridge_det_abs`.**  The absolute-Jacobian relation matching `bridge_hasFDerivAt`'s conclusion:
        `|(−(A_T ∘ A_e)).det| = |A_T.det| · |A_e.det|`,
    a pure finite-dimensional linear-algebra fact (`ContinuousLinearMap.det` multiplicative under
    composition, and `|det(−1 • B)| = |det B|` since the sign factor `(−1)^{finrank}` has unit
    absolute value).  NOT `a₁ = R/6`. -/
theorem bridge_det_abs (Ae AT : Point n →L[ℝ] Point n) :
    |(-(AT.comp Ae)).det| = |AT.det| * |Ae.det| := by
  have hcompDet : (AT.comp Ae).det = AT.det * Ae.det := by
    simp only [ContinuousLinearMap.det]
    rw [ContinuousLinearMap.coe_comp]
    exact LinearMap.det_comp _ _
  have hnegDet : (-(AT.comp Ae)).det
      = (-1 : ℝ) ^ Module.finrank ℝ (Point n) * (AT.comp Ae).det := by
    have hcoeNeg : ((-(AT.comp Ae) : Point n →L[ℝ] Point n) : Point n →ₗ[ℝ] Point n)
        = (-1 : ℝ) • ((AT.comp Ae : Point n →L[ℝ] Point n) : Point n →ₗ[ℝ] Point n) := by
      rw [ContinuousLinearMap.coe_neg]
      ext v
      simp
    show LinearMap.det _ = _
    rw [hcoeNeg, LinearMap.det_smul]
  rw [hnegDet, hcompDet, abs_mul, abs_mul]
  have h1 : |(-1 : ℝ) ^ Module.finrank ℝ (Point n)| = 1 := by
    rw [abs_pow]; norm_num
  rw [h1, one_mul]

/-- **`bridge_left_inverse`.**  Given the raw pointwise bridge on `D` AND that `Vb`/`Ve` are genuine
    LEFT INVERSES of `Wb`/`We` on `D` (the exact shape J4-1012's / J4-1046's own CoV packages already
    supply), the two left inverses are related setwise through `T` alone — **no inversion of `T`
    itself is used**:  for every `w` in the image `We '' D`, `Vb (−T w) = Ve w`.  NOT `a₁ = R/6`. -/
theorem bridge_left_inverse (Wb We T : Point n → Point n) (Vb Ve : Point n → Point n)
    (D : Set (Point n))
    (hbridge : ∀ z ∈ D, Wb z = -T (We z))
    (hVb : ∀ z ∈ D, Vb (Wb z) = z)
    (hVe : ∀ z ∈ D, Ve (We z) = z) :
    ∀ w ∈ We '' D, Vb (-T w) = Ve w := by
  rintro w ⟨z, hz, rfl⟩
  have h1 : Vb (-T (We z)) = Vb (Wb z) := by rw [hbridge z hz]
  rw [h1, hVb z hz, hVe z hz]

/-! ###############################################################################
    ### §2 — the CONCRETE, explicit-radius raw vector bridge at `uniformInverseChart`/`terminalVelAt`.
    ############################################################################### -/

/-- **★★ `evalBase_slot_coordinate_bridge_radius`.**  The explicit-radius RAW pointwise bridge (no
    Gaussian wrapping, unlike J4-1013's `reversal_link_ball_radius`): there is `r > 0` such that for
    every `z` with `dist z x < r`,
        `uniformInverseChart g gi hC hK z x = − terminalVelAt g gi hC hK x (uniformInverseChart g gi
        hC hK x z)`,
    i.e. `w_b(z) = − T_x(w_e(z))`.  Extracted from `GeodesicReversalRouteAtPoint.baseSlot_eventuallyEq_
    neg_terminalVel_at` via `Metric.eventually_nhds_iff`, mirroring J4-1013's recipe.  UNCONDITIONAL
    given `K ∈ 𝓝 x`. NOT `a₁ = R/6`. -/
theorem evalBase_slot_coordinate_bridge_radius (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x : Point n} (hxKmem : K ∈ 𝓝 x) :
    ∃ r > (0 : ℝ), ∀ z : Point n, dist z x < r →
      uniformInverseChart g gi hC hK z x
        = -terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z) := by
  have hev := baseSlot_eventuallyEq_neg_terminalVel_at g gi hC hK hxKmem
  obtain ⟨r, hr, hspec⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨r, hr, fun z hz => hspec hz⟩

/-! ###############################################################################
    ### §3 — the CONCRETE image-set corollary on any `D ⊆ ball x r`.
    ############################################################################### -/

/-- **★★ `evalBase_slot_coordinate_bridge_image_ball`.**  Concrete instantiation of `bridge_image_eq`
    at `Wb := fun z => uniformInverseChart z x`, `We := fun z => uniformInverseChart x z`, `T :=
    terminalVelAt x`: there is `r > 0` (§2's radius) such that for EVERY `D ⊆ ball x r`,
        `(fun z => uniformInverseChart g gi hC hK z x) '' D`
          `= (fun w => − terminalVelAt g gi hC hK x w) '' ((fun z => uniformInverseChart g gi hC hK x z)
              '' D)`,
    i.e. the BASE-slot chart image of `D` literally equals the `−T_x`-image of the EVAL-slot chart image
    of `D` — the SET-LEVEL half of the coordinate bridge (Jacobian/inverse-map halves are §1's `bridge_
    hasFDerivAt`/`bridge_det_abs`/`bridge_left_inverse`, to be applied once a concrete `D` shared by both
    J4-1012's and J4-1046's CoV packages is fixed — NOT attempted here). NOT `a₁ = R/6`. -/
theorem evalBase_slot_coordinate_bridge_image_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x : Point n} (hxKmem : K ∈ 𝓝 x) :
    ∃ r > (0 : ℝ), ∀ D : Set (Point n), D ⊆ Metric.ball x r →
      (fun z => uniformInverseChart g gi hC hK z x) '' D
        = (fun w => -terminalVelAt g gi hC hK x w) ''
            ((fun z => uniformInverseChart g gi hC hK x z) '' D) := by
  obtain ⟨r, hr, hspec⟩ := evalBase_slot_coordinate_bridge_radius g gi hC hK hxKmem
  refine ⟨r, hr, fun D hD => ?_⟩
  apply bridge_image_eq
  intro z hz
  exact hspec z (Metric.mem_ball.mp (hD hz))

end QIQTH.EvalBaseSlotCoordinateBridge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.EvalBaseSlotCoordinateBridge
#print axioms bridge_image_eq
#print axioms bridge_hasFDerivAt
#print axioms bridge_det_abs
#print axioms bridge_left_inverse
#print axioms evalBase_slot_coordinate_bridge_radius
#print axioms evalBase_slot_coordinate_bridge_image_ball
end AxiomChecks
