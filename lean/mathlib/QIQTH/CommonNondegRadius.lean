/-
  CommonNondegRadius — J4-52 (F4): assembling the self-contained common exp-nondegeneracy radius
  gate `(J)` from the doubled-family SUPPLY, feeding
  `expMap_common_nondeg_radius_of_doubled_supply` (`JacobiDoubledFamily.lean`).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled `(J)`-conclusion)

  * `s1_doubled_supply_package` — the **(S1) block**, unconditional in `hC` + `IsCompact K`.
    Re-packages `confined_doubled_family_with_variation_exists` into the EXACT binder shapes the CLOSE
    bridge `expMap_common_nondeg_radius_of_doubled_supply` consumes, with the velocity radius
    `r := ρ / 2` (`ρ` the compact-uniform a-priori geodesic-confinement radius):
      the doubled family `Y`, the doubled linearized variation field `Vf`, the per-`(q,v,a,b)` compact
      convex confinement set `S`, the window `σ`, and the binders
      `hScompact / hSconvex / hYode / hVode / hV0 / hIC / hmem`.
    So over the compact `K`, the (S1) doubled-family + variation-field supply is discharged with ONLY
    `hC` + `IsCompact K` — no injectivity radius, no second-variation data.

  ## FIREWALL — what remains carried for the fully self-contained `(J)` (precise obstruction)

  The bridge `expMap_common_nondeg_radius_of_doubled_supply` additionally consumes, beyond (S1):

    (a) `hr_lt : ∀ q ∈ K, r < expRho g gi hC q` — the compact-uniform INJECTIVITY radius.  The
        confinement radius `ρ` from `geodesic_apriori_confinement_uniform` is a Picard–Lindelöf
        EXISTENCE radius derived from bounded geometry; it is NOT `≤ expRho` in general.  Discharging
        `hr_lt` from `hC` + `IsCompact K` alone requires a NEW lemma: a uniform positive lower bound
        `∃ r > 0, ∀ q ∈ K, r < expRho g gi hC q` (lower semicontinuity of `expRho` over the compact `K`),
        which is not present in the substrate.  This gates the first-jet link `hlink`
        (`hlink_of_confined_doubled_family` needs `hrad : ‖v + s·a‖ < expRho q`).

    (b) the SECOND-VARIATION / geometry block `Ybase, Zf, Src` and
        `hZf / h0d / hKbd / hZ / h0cap / hKbcap / hAd / hXb / hSd`, together with the single uniform
        constants `K', D₀, X₀, Sr₀`.  Every POINTWISE ingredient exists as a proved lemma
        (`secondVariation_field_exists`, `fderiv_geodesicField_twopoint_dist_bound`,
        `secondVariation_source_twopoint_dist_bound`, the `LipschitzOnWith` producers), but assembling
        them into the bridge's SINGLE-constant / COMMON-set shape needs three NEW glue lemmas:
          - a COMMON compact convex phase set `S*` over all `q ∈ K` (from `K` bounded:
            `S* := closedBall ((center),0) (R_K + C₀ρ + …)`), on which `Kg / Lg / Lg₂ / Kb / M₂` become
            uniform (`geodesicField_lipschitzOnWith_of_isCompact_convex`, etc.), so that the two-point
            producers give ONE `D₀ = Lg·e^{Kg}` and ONE `Sr₀`;
          - an `a,b`-INDEPENDENT base curve `Ybase q v τ = (Y q v a b 0 τ).1` (needs geodesic ODE
            uniqueness on `S*` to see the first factor is `a,b`-independent), so that `hZf`'s base
            `(Y q v a b 0 τ).1` and `hZ`'s base `Ybase q v τ` coincide for a SINGLE `Zf`;
          - the `Zf / Src` construction via `secondVariation_field_exists` with seed `0`
            (`= (Vf 0).2`), whose Grönwall bound `‖Zf τ‖ ≤ gronwallBound 0 K' Smax τ` with
            `Smax = M₂·Cp·Cw·‖a‖·‖b‖` yields `hXb` with the `a,b`-independent
            `X₀ = M₂·Cp·Cw·(e^{K'} − 1)/K'` (`Cp / Cw` the uniform Jacobi field-norm coefficients).

  This file DERIVES (S1) and does NOT smuggle `hr_lt`, `hid`, the second-variation block, `Ybase`,
  or the `(J)`-conclusion.
-/
import QIQTH.SecondVariationSourceLip
import QIQTH.SecondVariationLipschitz
import QIQTH.SecondVariationSupply
import QIQTH.DoubledFamilyLink
import QIQTH.DoubledVariationField
import QIQTH.JacobiDoubledFamily
import QIQTH.BoundedGeometry
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **(S1) doubled-family supply, in the CLOSE-bridge binder shapes (unconditional).**

    Re-packages `confined_doubled_family_with_variation_exists` with the velocity radius `r := ρ/2`
    (`v ∈ closedBall 0 r ⟺ ‖v‖ ≤ ρ/2`) into the exact `(S1)` binders of
    `expMap_common_nondeg_radius_of_doubled_supply`:
    `hScompact / hSconvex / hYode / hVode / hV0 / hIC / hmem`, over the compact `K`, from `hC` alone.

    This is the maximal `(S1)`-block supply for the CLOSE bridge; the injectivity radius `hr_lt`
    (gating `hlink`) and the second-variation / geometry block remain carried (see file firewall). -/
theorem s1_doubled_supply_package (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ),
      ∃ σ : Point n → Point n → Point n → Point n → ℝ, (∀ q v a b : Point n, 0 < σ q v a b) ∧
      ∃ Y : Point n → Point n → Point n → Point n → ℝ → ℝ →
          (Point n × Point n) × (Point n × Point n),
      ∃ Vf : Point n → Point n → Point n → Point n → ℝ →
          (Point n × Point n) × (Point n × Point n),
      ∃ S : Point n → Point n → Point n → Point n →
          Set ((Point n × Point n) × (Point n × Point n)),
        (∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
          IsCompact (S q v a b)) ∧
        (∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
          Convex ℝ (S q v a b)) ∧
        (∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
          ∀ s ∈ Set.Icc (-(σ q v a b)) (σ q v a b), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt (Y q v a b s) (doubledField g gi (Y q v a b s τ)) τ) ∧
        (∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
          ∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt (Vf q v a b)
              (fderiv ℝ (doubledField g gi) (Y q v a b 0 τ) (Vf q v a b τ)) τ) ∧
        (∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
          Vf q v a b 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n)))) ∧
        (∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
          ∀ s ∈ Set.Icc (-(σ q v a b)) (σ q v a b),
            Y q v a b s 0 - Y q v a b 0 0
              = s • (((0 : Point n), a), ((0 : Point n), (0 : Point n)))) ∧
        (∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
          ∀ s ∈ Set.Icc (-(σ q v a b)) (σ q v a b),
          ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y q v a b s τ ∈ S q v a b) := by
  classical
  obtain ⟨ρ, hρ0, C₀, _hC0, σ, hσpos, Y, Vf, S, hScompact, hSconvex, hbundle⟩ :=
    confined_doubled_family_with_variation_exists g gi hC hK
  -- Velocity radius `r := ρ/2`; `v ∈ closedBall 0 r ⟺ ‖v‖ ≤ ρ/2`.
  refine ⟨ρ / 2, by positivity, σ, hσpos, Y, Vf, S,
    (fun _ _ _ _ _ _ => hScompact _ _ _ _),
    (fun _ _ _ _ _ _ => hSconvex _ _ _ _), ?_, ?_, ?_, ?_, ?_⟩
  -- Convert `v ∈ closedBall 0 (ρ/2)` to `‖v‖ ≤ ρ/2` and read off each binder from `hbundle`.
  · intro q hq v hv a b s hs τ hτ
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    obtain ⟨_, _, hsblk⟩ := hbundle q hq v hv a b
    obtain ⟨_, hYodes, _, _, _⟩ := hsblk s hs
    exact hYodes τ hτ
  · intro q hq v hv a b τ hτ
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    obtain ⟨_, hVfode, _⟩ := hbundle q hq v hv a b
    exact hVfode τ hτ
  · intro q hq v hv a b
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    obtain ⟨hVf0, _, _⟩ := hbundle q hq v hv a b
    exact hVf0
  · intro q hq v hv a b s hs
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    obtain ⟨_, _, hsblk⟩ := hbundle q hq v hv a b
    obtain ⟨_, _, _, hICs, _⟩ := hsblk s hs
    exact hICs
  · intro q hq v hv a b s hs τ hτ
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    obtain ⟨_, _, hsblk⟩ := hbundle q hq v hv a b
    obtain ⟨_, _, _, _, hmems⟩ := hsblk s hs
    exact hmems τ hτ

end QIQTH.ExpMap
