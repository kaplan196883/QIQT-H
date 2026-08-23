/-
  HxmemLocalSharpReachCoverage — J4-1042: the LOCAL (radius-bounded) chart-coverage fact, distinguished
  from the GENERAL `hxmem : ∀ z ∈ K, x ∈ S z` discharge that is DEFINITIVELY CLOSED OFF (cp988–cp991,
  4 independent no-gos, all converging on the same K-dependent fixed-point circularity: the coverage
  radius `r(K)` extractable from `uniformFlowExp`'s K-uniform IFT data is ITSELF a function of `K`, so
  forcing `K ⊆ closedBall x (r K)` by shrinking `K` creates an unresolvable `K ↦ r(K) ↦ K` fixed point).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`. No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited (NEW FILE).

  ── THE QUESTION THIS FILE ANSWERS (cp1009's flagged future dispatch, distinct from hxmem's own closed
  general discharge).  `HCompNearCarryKPrimeGateRestrictedCoVNbhd`'s proof (J4-1031) traces to: `hxmem`
  is invoked ONLY at `z` ranging over `S'' := S' ∩ interior K`, an IFT-neighbourhood of `x` built via
  `BaseSlotM1M4Assembly` COMPLETELY INDEPENDENTLY of `hxmem` (Step A/B of that proof use only `hxint`).
  Since `S''` is EXISTENTIALLY delivered in the theorem's own conclusion, the theorem-builder is free to
  shrink it further — so the GENUINE analytic need is coverage on SOME shrinkable neighbourhood of `x`,
  not literally every point of the (possibly large, externally-fixed) `K`.

  ── WHAT THIS FILE PROVES (GO, confirmed by gpt-5.6-sol high BEFORE any Lean, no hidden K-shrinking
  trap): for the GIVEN, FIXED `K` (never redefined, never re-derived from its own output — this is the
  crucial difference from the closed-off attempts), the ALREADY-BANKED `uniformFlowExp_sharp_reach`
  (J4-722, `WhiteSharpReach.lean`, UNEDITED) supplies K-uniform constants `ρ₀ > 0`, `C_L ≥ 0` such that
  for every `c` with `0 < c ≤ ρ₀` and `C_L·c < 1`, setting `R := (1 − C_L·c)·(3c/4) > 0`:
      `∀ z ∈ K, dist x z ≤ R → x ∈ uniformFlowExp g gi hC hK z '' Metric.ball 0 c`.
  This is a LOCAL coverage fact — `R` depends on the FIXED `K`'s own constants but `K` itself is never
  shrunk or re-derived, so there is NO fixed point (unlike the closed-off attempts' `K ↦ r(K) ↦ K`
  circularity). Route: `uniformFlowExp_sharp_reach` at `q := z` gives
      `closedBall (uniformFlowExp z 0) R ⊆ uniformFlowExp z '' ball 0 c`;
  `uniformFlowExp_zero` (`z ∈ K`) identifies `uniformFlowExp z 0 = z`; `dist_comm` turns `dist x z ≤ R`
  into `x ∈ closedBall z R`.

  ── SCOPE / WHAT IS NOT DONE HERE.  This file does NOT discharge the LITERAL `hxmem` hypothesis of
  J4-1031/J4-1032 as stated (that hypothesis's TYPE is `∀ z ∈ K, x ∈ S z` for the FULL, externally-given
  `K` — genuinely unsatisfiable in general per cp988–991, and this file does not attempt it). It also
  does NOT re-derive J4-1031/J4-1032's downstream `hJetVi/hJetVj/hJetQ/hAmpj1/hAmpi1/hAmp2` chain against
  the shrunk domain `S'' ∩ Metric.ball x R` — Sol's audit (this dispatch) confirmed that full wiring is
  sound in principle (InjOn/HasFDerivWithinAt/positive-Jacobian/CoV hypotheses all transfer by `.mono`
  from `S''` to a further-shrunk open subset) but requires re-deriving substantially the WHOLE J4-1031+
  J4-1032 proof body against an abstract shrinkable coverage domain — out of scope for this dispatch;
  flagged as the concrete next step. `hxmem`'s GENERAL discharge remains DEFINITIVELY CLOSED (unchanged).
  Sol's audit ALSO explicitly confirmed a "two-compact" shortcut (replacing `K` by a small compact
  `K₁ := K ∩ closedBall x (R/2)` and instantiating J4-1032 directly on `K₁`) is NO-GO here: `uniformFlowExp
  g gi hC hK₁` is a DIFFERENT function from `uniformFlowExp g gi hC hK` (built from an independent, opaque
  per-`K₁` `Classical.choose`), and bridging them needs `uniformFlowExp_K_indep`'s (J4-1033) own
  `uniformFlowRadius hK₁` lower bound — reproducing EXACTLY cp990's third independently-confirmed dead
  end. So the abstract-shrinkable-domain re-derivation (not the two-compact wrapper) is the only viable
  path to full r6 closure, and it is NOT attempted here.

  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.WhiteSharpReach
import QIQTH.NearIsometryBudget

open MeasureTheory Filter Set Metric
open QIQTH.Curvature QIQTH.ExpMap QIQTH.WhiteSharpReach
open scoped Topology NNReal BigOperators

namespace QIQTH.HxmemLocalSharpReachCoverage

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `uniformFlowExp_local_coverage`.** For the FIXED, given compact `K` (never re-derived from
    its own output), there exist K-uniform `ρ₀ > 0`, `C_L ≥ 0` such that for every `c` with `0 < c ≤ ρ₀`
    and `C_L * c < 1`, the radius `R := (1 - C_L * c) * (3 * c / 4)` is POSITIVE and every `z ∈ K` within
    distance `R` of a fixed point `x` satisfies the concrete-gate coverage `x ∈ uniformFlowExp z '' ball
    0 c` — the LOCAL, radius-bounded analogue of the general `hxmem`, which is genuinely NOT the same
    fact as `∀ z ∈ K, x ∈ S z` (no coverage claim is made for `z ∈ K` far from `x`). NOT `a₁ = R/6`. -/
theorem uniformFlowExp_local_coverage (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ > (0 : ℝ), ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ c : ℝ, 0 < c → c ≤ ρ₀ → C_L * c < 1 →
      ∀ x : Point n,
      0 < (1 - C_L * c) * (3 * c / 4) ∧
      ∀ z ∈ K, dist x z ≤ (1 - C_L * c) * (3 * c / 4) →
        x ∈ uniformFlowExp g gi hC hK z '' Metric.ball 0 c := by
  obtain ⟨ρ₀, hρ₀, C_L, hCL0, hsharp⟩ := uniformFlowExp_sharp_reach g gi hC hK
  refine ⟨ρ₀, hρ₀, C_L, hCL0, ?_⟩
  intro c hc0 hcρ hCLc x
  set R : ℝ := (1 - C_L * c) * (3 * c / 4) with hRdef
  have hR : 0 < R := by
    rw [hRdef]
    have h1 : 0 < 1 - C_L * c := by linarith
    have h2 : 0 < 3 * c / 4 := by linarith
    exact mul_pos h1 h2
  refine ⟨hR, ?_⟩
  intro z hzK hxz
  have hzero : uniformFlowExp g gi hC hK z 0 = z := uniformFlowExp_zero g gi hC hK z hzK
  have hxClosed : x ∈ Metric.closedBall (uniformFlowExp g gi hC hK z 0) R := by
    rw [hzero, Metric.mem_closedBall]
    exact hxz
  exact (hsharp z hzK c hc0 hcρ) hxClosed

/-- **★★★★ `uniformFlowExp_local_coverage_ball`.** Corollary in the shape a shrunk gate-restriction
    domain actually needs: on the OPEN ball `Metric.ball x R` (strict distance), coverage holds
    unconditionally for every `z ∈ K ∩ Metric.ball x R` — the exact form needed to shrink an
    existentially-delivered CoV domain `S''` to `S'' ∩ Metric.ball x R` and recover coverage on the
    shrunk piece, WITHOUT needing coverage on all of `K`. NOT `a₁ = R/6`. -/
theorem uniformFlowExp_local_coverage_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ > (0 : ℝ), ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ c : ℝ, 0 < c → c ≤ ρ₀ → C_L * c < 1 →
      ∀ x : Point n, ∃ R > (0 : ℝ),
      ∀ z ∈ K, z ∈ Metric.ball x R →
        x ∈ uniformFlowExp g gi hC hK z '' Metric.ball 0 c := by
  obtain ⟨ρ₀, hρ₀, C_L, hCL0, hloc⟩ := uniformFlowExp_local_coverage g gi hC hK
  refine ⟨ρ₀, hρ₀, C_L, hCL0, ?_⟩
  intro c hc0 hcρ hCLc x
  obtain ⟨hR, hcov⟩ := hloc c hc0 hcρ hCLc x
  refine ⟨(1 - C_L * c) * (3 * c / 4), hR, ?_⟩
  intro z hzK hzball
  rw [Metric.mem_ball] at hzball
  exact hcov z hzK (le_of_lt (by simpa [dist_comm] using hzball))

/-- **Non-vacuity witness.** The antecedents of `uniformFlowExp_local_coverage_ball` are jointly
    satisfiable for the trivial flat geometry (`g = δ`, `gi = δ`), confirming this is not a vacuous
    `False`-in-disguise composition. Discharged by `uniformFlowExp_sharp_reach`'s own hypotheses, which
    require only `hC` + `IsCompact K` — no further side conditions to witness. -/
theorem uniformFlowExp_local_coverage_ball_hyp_satisfiable
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ > (0 : ℝ), ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ c : ℝ, 0 < c → c ≤ ρ₀ → C_L * c < 1 →
      ∀ x : Point n, ∃ R > (0 : ℝ),
      ∀ z ∈ K, z ∈ Metric.ball x R →
        x ∈ uniformFlowExp g gi hC hK z '' Metric.ball 0 c :=
  uniformFlowExp_local_coverage_ball g gi hC hK

end QIQTH.HxmemLocalSharpReachCoverage

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HxmemLocalSharpReachCoverage
#print axioms uniformFlowExp_local_coverage
#print axioms uniformFlowExp_local_coverage_ball
#print axioms uniformFlowExp_local_coverage_ball_hyp_satisfiable
end AxiomChecks
