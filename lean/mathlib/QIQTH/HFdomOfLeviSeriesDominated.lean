/-
  HFdomOfLeviSeriesDominated — J4-1105: `hDConv_AT_GATE`'s `hFdom` antecedent (Section-G census)
  reduced to a corollary of the ALREADY-BANKED abstract Levi-series domination
  `GatedWitnessPackage.leviSeries_dominatedW_le` (J4-114 (B), width-2 α=0), via
  `baseKernelW_zero_apply`.

  WHY / CORRECTIVE.  J4-1104's honest scope map for `hDConv_AT_GATE`'s Section-G census listed
  `hFdom` as: "no theorem anywhere bounds concrete `leviSeries`" — i.e. genuinely unattempted.
  Per this dispatch's mandated first step (search before attacking), this claim is WRONG: an
  under-crediting instance of exactly the kind this campaign has repeatedly hit (see
  `feedback_dont_undercredit_repo`).  `GatedWitnessPackage.lean` ALREADY has:

    * `leviSeries_dominatedW_le (E) (C T) (hEbound : width-2/α=0 one-step bound)
        (hInt : IterConvIntegrableW E 2 0 C) : ∃ C_L ≥ 0, ∀ τ p q, 0<τ→τ≤T→
        |leviSeries E τ p q| ≤ C_L · baseKernelW 2 0 τ p q`,

  and `ParametrixHEboundWiring.baseKernelW_zero_apply` identifies `baseKernelW 2 0 τ p q =
  gaussDdim (2·τ) (p−q)` EXACTLY (`τ^0 = 1`) — i.e. the conclusion IS `hFdom`'s literal shape
  (`|F s z y| ≤ C_L · gaussDdim (2·s) (z−y)`), for the ABSTRACT residual `E` and `F := leviSeries E`.

  `gpt-5.6-sol` (high) confirmed (this dispatch's consult): (a) the J4-1104 claim is unfair given
  this existing machinery; (b) the smallest honest non-vacuous increment is exactly THIS wrapper —
  restate `leviSeries_dominatedW_le` in `hFdom`'s literal binder shape via `hFeq`/`baseKernelW_zero_apply`,
  carrying `hEbound`+`hInt` (NOT yet closing them) — rather than attempting the full concrete
  `vanVleckGatedWitness` wiring (which additionally needs `hEmeas`, an already-tracked separate M1
  wall per `leviSeries_gatedWitnessN1_dominated`, plus a nontrivial kernel-identity bridge between
  `vanVleckGatedWitness` and `gatedKernel K S (globalCutoffParametrixWitnessN 1 …)`).

  NO new asymptotic/rate/convergence claim is introduced here — this is pure logical repackaging
  of an already-proven Gaussian-domination fact, so no fresh sympy check is needed (per the
  standing rule's scope: it applies to NEW rate claims).

  ⚠ HONEST SCOPE.  This DOES NOT discharge `hFdom` unconditionally: it shows `hFdom` reduces to
  EXACTLY `{hEbound : width-2/α=0 one-step residual domination on (0,T], hInt : IterConvIntegrableW
  E 2 0 C}` — precisely the two obligations `leviSeries_gatedWitnessN1_dominated` already tracks as
  open (`hEmeas`-conditional) for the concrete N=1 van-Vleck witness.  `a₁=R/6` remains STRICTLY
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁=R/6`.
-/
import Mathlib
import QIQTH.GatedWitnessPackage
import QIQTH.ParametrixHEboundWiring

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TrueHeatKernel
open QIQTH.LeviSeries QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound

namespace QIQTH.HFdomOfLeviSeriesDominated

variable {n : ℕ}

/-- **`hFdom` reduces to the abstract Levi-series domination.**  For `F := leviSeries E` (any
    residual kernel `E`), `C T ≥ 0`, GIVEN the width-2/α=0 one-step residual bound `hEbound` on
    `(0,T]` and the carried per-step integrability `hInt : IterConvIntegrableW E 2 0 C`, there is a
    constant `C_L ≥ 0` making EXACTLY `hDConv_AT_GATE`'s `hFdom` shape hold:
        `∀ s, 0 < s → s ≤ T → ∀ z y, |F s z y| ≤ C_L · gaussDdim (2·s) (z−y)`.
    Route: `leviSeries_dominatedW_le` (J4-114 (B)) + `baseKernelW_zero_apply` to strip the `τ^0`
    weight from `baseKernelW 2 0`, then rewrite `F` via `hFeq`. -/
theorem hFdom_of_leviSeries_dominatedW
    (E F : ℝ → Point n → Point n → ℝ) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 < T)
    (hFeq : F = leviSeries E)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * gaussDdim (2 * τ) (p - q))
    (hInt : IterConvIntegrableW E (2 : ℝ) (0 : ℝ) C) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧
      ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y) := by
  subst hFeq
  have hEboundW : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ hτT
    rw [baseKernelW_zero_apply]
    exact hEbound τ p q hτ hτT
  obtain ⟨C_L, hC_L0, hbound⟩ := leviSeries_dominatedW_le E C T hC hT hEboundW hInt
  refine ⟨C_L, hC_L0, fun s hs hsT z y => ?_⟩
  have h := hbound s z y hs hsT
  rwa [baseKernelW_zero_apply] at h

end QIQTH.HFdomOfLeviSeriesDominated
