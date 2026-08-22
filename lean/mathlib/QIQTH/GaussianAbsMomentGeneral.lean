/-
  GaussianAbsMomentGeneral — the GENERAL-`k` 1-D absolute Gaussian moment
  `∫ heatKernel1D t y · |y|^k ≤ absMomentConst k · (√t)^k`, combining the banked EVEN
  (`hk_even_moment_le`) and ODD (`oneD_absMoment_odd`) parity towers into a single statement for
  ARBITRARY `k`, and using it to DISCHARGE — unconditionally, from the fixed Gaussian model — the
  `_hmom` `(k+3)`-moment hypothesis of `HCompNearCarryConcreteDischarge.terminalVelAt_chartReplace_
  sliver_bound` (J4-879), leaving ONLY its `_hWint` integrability hypothesis.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  `terminalVelAt_chartReplace_sliver_bound` (J4-879) is the matched near-sliver rate for the
  chart-replacement cancellation integrand — `hcomp`'s near-carry `nb` payoff — but it carries TWO
  generic Gaussian hypotheses as (satisfiable, non-vacuous) inputs:
    • `_hmom : ∀ τ, 0<τ→τ≤ε → ∫ y, heatKernel1D (2τ) y · |y|^(k+3) ≤ ck3·(√(2τ))^(k+3)`  — a pure
      1-D `(k+3)`-absolute-moment bound of the fixed heat kernel;
    • `_hWint` — integrability on `ball 0 R` of the `terminalVelAt`-composed Gaussian difference.
  This file discharges `_hmom` COMPLETELY.  The banked moment tower supplies the two parity halves
  (`hk_even_moment_le`, `oneD_absMoment_odd`, both of the exact `c·(√t)^power` shape with `c` a pure
  power/factorial constant INDEPENDENT of `t`); combining them by a parity split gives the general-`k`
  moment, whose `t := 2τ`, `power := k+3` instance is EXACTLY the `_hmom` shape with the explicit
  constant `ck3 := absMomentConst (k+3)`.

  THIS FILE supplies:
    • `absMomentConst k` — the explicit parity-branched moment constant (nonneg, `absMomentConst_nonneg`).
    • `oneD_absMoment_gen` — the general-`k` 1-D absolute moment `∫ G_t·|y|^k ≤ absMomentConst k·(√t)^k`.
    • `terminalVel_sliver_hmom` — the `_hmom` shape holds with `ck3 := absMomentConst (k+3)`, for ALL k.
    • `terminalVelAt_chartReplace_sliver_bound_of_integrable` — the sliver bound with `_hmom` and its
      `hck3 : 0 ≤ ck3` side-condition DISCHARGED, so it depends only on `_hWint`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure repackaging of banked exact moment lemmas — no new asymptotics, no new analysis.  It discharges
  ONLY the `_hmom` premise (a standard 1-D Gaussian moment fact) of one banked payoff lemma; the
  `_hWint` integrability premise remains OPEN (it needs measurability of `z ↦ gaussDdim τ (terminalVelAt
  … x z)` on ALL of `ball 0 R`, whereas `terminalVelAt`'s regularity is banked only AT `0`
  (`terminalVelAt_contDiffAt_two`), not on a ball — an API-level gap in ODE dependence-on-initial-data,
  NOT discharged here).  It does NOT compose into any literal `nb` difference-bound, does NOT touch the
  Jacobian/weight domination step, does NOT alter the capstone's dependency set.  No `sorry`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing
  file edited.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HessianSliceBound
import QIQTH.HCompNearCarryConcreteDischarge

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.GeodesicReversalRouteAtPoint
open QIQTH.HCompNearCarryConcreteDischarge
open scoped Topology

namespace QIQTH.GaussianAbsMomentGeneral

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the general-`k` absolute-moment constant and its evaluation.
    ############################################################################### -/

/-- **`absMomentConst k`** — the explicit parity-branched 1-D absolute-moment constant: the EVEN
    branch `8^(k/2)·(k/2)!·√2` (from `hk_even_moment_le`) when `k` is even, the ODD branch (from
    `oneD_absMoment_odd`) otherwise.  Depends ONLY on `k`, not on the heat time.  NOT `a₁ = R/6`. -/
noncomputable def absMomentConst (k : ℕ) : ℝ :=
  if k % 2 = 0 then 8 ^ (k / 2) * ((k / 2).factorial : ℝ) * Real.sqrt 2
  else (8 ^ (k / 2 + 1) * ((k / 2 + 1).factorial : ℝ) * Real.sqrt 2
        + 8 ^ (k / 2) * ((k / 2).factorial : ℝ) * Real.sqrt 2) / 2

/-- `absMomentConst` is nonnegative (all constituents are).  NOT `a₁ = R/6`. -/
theorem absMomentConst_nonneg (k : ℕ) : 0 ≤ absMomentConst k := by
  unfold absMomentConst
  split <;> positivity

/-- Even-index evaluation of `absMomentConst`.  NOT `a₁ = R/6`. -/
theorem absMomentConst_even (m : ℕ) :
    absMomentConst (2 * m) = 8 ^ m * (m.factorial : ℝ) * Real.sqrt 2 := by
  unfold absMomentConst
  rw [if_pos (by omega : (2 * m) % 2 = 0), show (2 * m) / 2 = m from by omega]

/-- Odd-index evaluation of `absMomentConst`.  NOT `a₁ = R/6`. -/
theorem absMomentConst_odd (m : ℕ) :
    absMomentConst (2 * m + 1)
      = (8 ^ (m + 1) * ((m + 1).factorial : ℝ) * Real.sqrt 2
          + 8 ^ m * (m.factorial : ℝ) * Real.sqrt 2) / 2 := by
  unfold absMomentConst
  rw [if_neg (by omega : ¬ (2 * m + 1) % 2 = 0), show (2 * m + 1) / 2 = m from by omega]

/-! ###############################################################################
    ### §2 — the general-`k` 1-D absolute moment.
    ############################################################################### -/

/-- **★★ `oneD_absMoment_gen` — the general-`k` 1-D absolute Gaussian moment.**  For `t > 0` and any
    `k : ℕ`,
        `∫ y, heatKernel1D t y · |y|^k ≤ absMomentConst k · (√t)^k`,
    by a parity split feeding `hk_even_moment_le` (even) / `oneD_absMoment_odd` (odd).  Pure
    repackaging of the banked exact moment tower.  NOT `a₁ = R/6`. -/
theorem oneD_absMoment_gen (k : ℕ) (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ^ k ≤ absMomentConst k * (Real.sqrt t) ^ k := by
  rcases Nat.even_or_odd k with hev | hodd
  · obtain ⟨m, hm⟩ := hev
    have hk : k = 2 * m := by omega
    subst hk
    have hpow : (fun y : ℝ => heatKernel1D t y * |y| ^ (2 * m))
              = (fun y => heatKernel1D t y * (y ^ 2) ^ m) := by
      funext y; congr 1; rw [pow_mul, sq_abs]
    rw [hpow, absMomentConst_even]
    refine (hk_even_moment_le m t ht).trans (le_of_eq ?_)
    rw [show (Real.sqrt t) ^ (2 * m) = t ^ m from by rw [pow_mul, Real.sq_sqrt ht.le]]
  · obtain ⟨m, hm⟩ := hodd
    subst hm
    rw [absMomentConst_odd]
    exact oneD_absMoment_odd m t ht

/-! ###############################################################################
    ### §3 — discharging the `_hmom` `(k+3)`-moment hypothesis.
    ############################################################################### -/

/-- **`terminalVel_sliver_hmom` — the `_hmom` shape, discharged for ALL `k`.**  For any `k` and `ε`,
    the exact `(k+3)`-moment hypothesis of `terminalVelAt_chartReplace_sliver_bound` holds with the
    explicit constant `ck3 := absMomentConst (k+3)`:
        `∀ τ, 0<τ→τ≤ε → ∫ y, heatKernel1D (2τ) y · |y|^(k+3) ≤ absMomentConst (k+3)·(√(2τ))^(k+3)`.
    NOT `a₁ = R/6`. -/
theorem terminalVel_sliver_hmom (k : ℕ) (ε : ℝ) :
    ∀ τ : ℝ, 0 < τ → τ ≤ ε →
      ∫ y : ℝ, heatKernel1D (2 * τ) y * |y| ^ (k + 3)
        ≤ absMomentConst (k + 3) * (Real.sqrt (2 * τ)) ^ (k + 3) := by
  intro τ hτ _
  exact oneD_absMoment_gen (k + 3) (2 * τ) (by linarith)

/-! ###############################################################################
    ### §4 — the sliver bound with `_hmom` discharged (only `_hWint` remaining).
    ############################################################################### -/

variable {n : ℕ}

/-- **★★ `terminalVelAt_chartReplace_sliver_bound_of_integrable` — the J4-879 sliver bound with
    `_hmom` (and its `hck3 : 0 ≤ ck3` side-condition) DISCHARGED.**  Same conclusion as
    `terminalVelAt_chartReplace_sliver_bound`, with `ck3 := absMomentConst (k+3)` supplied and the
    `(k+3)`-moment hypothesis proved unconditionally (`terminalVel_sliver_hmom`), so the ONLY
    remaining premise is `_hWint` (base-Gaussian-difference integrability on `ball 0 R`).  NOT
    `a₁ = R/6`. -/
theorem terminalVelAt_chartReplace_sliver_bound_of_integrable
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    ∃ R > (0 : ℝ), ∃ L' ≥ (0 : ℝ),
      (∀ (_hWint : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
          IntegrableOn (fun z : Point n =>
              ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|)
            (Metric.ball 0 R) volume),
        ‖∫ s in (t - ε)..t,
            ∫ z in Metric.ball (0 : Point n) R,
              ‖z‖ ^ k * |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z|‖
          ≤ (L' / 4 * (Real.sqrt 2) ^ n
                * ((n : ℝ) * absMomentConst (k + 3) * (Real.sqrt 2) ^ (k + 3)))
              * (Real.sqrt ε) ^ (k + 3)) := by
  obtain ⟨R, hR, L', hL', hbound⟩ :=
    terminalVelAt_chartReplace_sliver_bound g gi hC hK hx₀K k ε hε t
      (absMomentConst (k + 3)) (absMomentConst_nonneg (k + 3))
  exact ⟨R, hR, L', hL', fun hWint => hbound hWint (terminalVel_sliver_hmom k ε)⟩

end QIQTH.GaussianAbsMomentGeneral

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.GaussianAbsMomentGeneral
#print axioms oneD_absMoment_gen
#print axioms terminalVel_sliver_hmom
#print axioms terminalVelAt_chartReplace_sliver_bound_of_integrable
end AxiomChecks
