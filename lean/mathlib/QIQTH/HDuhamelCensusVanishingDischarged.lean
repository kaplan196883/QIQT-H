/-
  HDuhamelCensusVanishingDischarged — find-and-wire discharge of TWO nonpositive-time VANISHING
  census binders of the LIVE order-1 `hDuhamel` capstone `hDuhamel_live_gate_wired`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure find-and-wire brick: it re-exposes TWO of the ~50 remaining free census binders of
  `HDuhamelLiveGateWired.hDuhamel_live_gate_wired` — the source vanishing `hFzero` (:157) and the
  amplitude vanishing `hAzero` (:172) — as THEOREMS from PURE geometry (`g,gi,hChr,hK,S,a,b` plus
  `1 ≤ n`), with NO analytic carry whatsoever.  No `sorry` (header prose excepted), no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or yielding) the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.
    • `hFzero_live` — the LIVE capstone's `hFzero` census binder
        `∀ s ≤ 0, ∀ z y, leviSeries (heatOp g gi H_G) s z y = 0`
      DISCHARGED to PURE geometry via `DaLimEasyTranche.hFzero_concrete` (which itself routes
      `DataPileWitnessAudit.hEzeroE_concrete → DaLimEasyTranche.leviSeries_eq_zero_of_nonpos`).
    • `hAzero_live` — the LIVE capstone's `hAzero` census binder
        `∀ τ ≤ 0, ∀ p q, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0`
      DISCHARGED to PURE geometry via `AmplitudeDerivativeDataConcrete.vanVleckGatedWitness_eq_zero_of_nonpos`.

  These are the EXACT propositions the census binders `hFzero`/`hAzero` carry in
  `hDuhamel_live_gate_wired` (character-for-character; at `H_G := vanVleckGatedWitness g gi hChr hK S a b`
  and `F := leviSeries (heatOp g gi H_G)`).  The `exact` proof bodies ARE the object-identity check —
  the file compiles only if the producer conclusions defeq-match the census binder shapes.

  ⚠  Both discharges depend on `1 ≤ n` (the geometry-derived nonpositive-time vanishing of the gated
  residual / amplitude needs the dimension positivity), which is itself a census binder (`hn`) of the
  capstone — so these are ZERO-NEW-CARRY discharges (they consume only geometry already present).

  ⚠  STILL NOT `a₁ = R/6`.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import QIQTH.DaLimEasyTranche
import QIQTH.AmplitudeDerivativeDataConcrete

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.HDuhamelCensusVanishingDischarged

variable {n : ℕ}

/-- **★ `hFzero_live`.**  The LIVE order-1 `hDuhamel` capstone's `hFzero` census binder — the Levi
    source `F := leviSeries (heatOp g gi H_G)` vanishes at nonpositive time — DISCHARGED to PURE
    geometry (`g,gi,hChr,hK,S,a,b` and `1 ≤ n`) via `DaLimEasyTranche.hFzero_concrete`.  NO analytic
    carry.  EXACT census binder shape (`∀ s ≤ 0, ∀ z y, F s z y = 0`).  ⚠ NOT `a₁ = R/6`. -/
theorem hFzero_live (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) :
    ∀ s : ℝ, s ≤ 0 → ∀ z y : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y = 0 :=
  QIQTH.DaLimEasyTranche.hFzero_concrete g gi hChr hK S a b hn

/-- **★ `hAzero_live`.**  The LIVE order-1 `hDuhamel` capstone's `hAzero` census binder — the concrete
    gated van-Vleck amplitude `H_G := vanVleckGatedWitness g gi hChr hK S a b` vanishes at nonpositive
    time — DISCHARGED to PURE geometry (`g,gi,hChr,hK,S,a,b` and `1 ≤ n`) via
    `AmplitudeDerivativeDataConcrete.vanVleckGatedWitness_eq_zero_of_nonpos`.  NO analytic carry.
    EXACT census binder shape (`∀ τ ≤ 0, ∀ p q, H_G τ p q = 0`).  ⚠ NOT `a₁ = R/6`. -/
theorem hAzero_live (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) :
    ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      vanVleckGatedWitness g gi hChr hK S a b τ p q = 0 :=
  fun τ hτ p q =>
    QIQTH.AmplitudeDerivativeDataConcrete.vanVleckGatedWitness_eq_zero_of_nonpos
      g gi hChr hK S a b hn τ hτ p q

end QIQTH.HDuhamelCensusVanishingDischarged

/-! ## Axiom check — both public decls are `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HDuhamelCensusVanishingDischarged
#print axioms hFzero_live
#print axioms hAzero_live
end AxiomChecks
