/-
  HGpowFromCollar — J4-545: factor the `hGpow` closure into a ROUTE-AGNOSTIC boundary
  `hGpow_from_innerWindow`, and precisely scope the surviving collar/off-collar split carry that a
  collar-bundle-driven `hGpow` would still need.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It performs
  ONE plumbing move — exposing the correct abstraction boundary of the `MemAdjHi` moment-cancellation
  carry `hGpow` — and RECORDS (does not fabricate) the genuine analytic gap that blocks producing
  `hGpow` from the collar-restricted amplitude bundle.  No `sorry`/`admit` (header prose excepted), no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to the
  conclusion, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE VERDICT (from the mainline, not guessed).

  `MemAdjHiMomentBound.hGpow_of_amplitudeData` (J4-543) produces the `hGpow` per-slice carry
      `|∫ z, witnessSecondXDeriv i (u−s) z · F s z 0| ≤ Cpair·(u−s)^{-1/2}`   on `uIoc (u−ε_m) u`
  in TWO stages:
    (I)  the per-slice OPEN-window inner bound `hinner_window` in the `K₁·(u−s)^{-1/2} + K₀` shape,
         built by `slice2_inner_bound` from the 3-term Leibniz–Gaussian expansion + amplitude sups,
         quantified over **ALL** `z ∈ ℝⁿ` (the leading `τ^{-1/2}` gain is the EXACT FULL-SPACE Hessian
         moment `∫ (z_i²−2τ)/(4τ²)·G_τ = 0`);
    (II) the closure `leviSecondPairing_le_invSqrt` (m-uniform `Cpair`) ∘
         `hGpow_uIoc_of_Ioo_zeroEndpoint` (the `Ioo → uIoc` endpoint upgrade), with the `τ = 0`
         endpoint value now discharged UNCONDITIONALLY for `n ≥ 1` (`hEndpoint_discharged`, J4-544).

  THE COLLAR BUNDLE `AmplitudeDataOnCollar.AmplitudeDerivativeDataOn (collarRegime r₀ c τ₀)` supplies
  the expansion + sups ONLY on `collarRegime τ z` (`0<τ≤τ₀ ∧ z∈K ∧ ‖z‖<r₀ ∧ ‖z‖ ≤ c√τ`).  Off-collar
  the ratio `ρ = exp((r_z − r_{W0})/4τ)` blows up, so the collar-constant amplitude bounds are
  literally FALSE off-collar.  `SliverBoundOnCollar` (J4-353) already ruled the consumption is
  **case (b)** — over ALL of `Point n` with the Gaussian envelope, NOT collar-confined — and that the
  surviving carry is the OFF-COLLAR Gaussian tail on `‖z‖ > c√τ`, which must be shown super-poly small
  and ABSORBED to RECONSTITUTE the full-space Hessian moment.

  CONSEQUENCE (Sol #J4-545 confirmed).  Producing `hGpow` from the collar bundle is a GENUINE analytic
  gap, NOT a thin banked composition: the collar HI window is NOT `⊆` collar (the z-integral is
  full-space; the collar `‖z‖ ≤ c√τ` shrinks with `τ`), and truncating the Hessian moment to the
  collar destroys the exact `τ^{-1/2}` cancellation.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS HERE.

    • `hGpow_from_innerWindow` — ★★★ the ROUTE-AGNOSTIC closure boundary: from ANY per-slice OPEN-window
      inner bound in the `K₁·(u−s)^{-1/2} + K₀` shape (however derived — all-`z` OR collar+split) plus
      `1 ≤ n`, produce the `uIoc` `hGpow` via stage (II), with the `τ = 0` endpoint supplied INTERNALLY
      from `hEndpoint_discharged`.  This faithfully factors the second half of `hGpow_of_amplitudeData`
      and is the stable interface both the all-`z` route (`slice2_inner_bound`) and the collar route
      (on-collar sliver + off-collar tail) must hit.  (Sol: worth landing — it centralises the
      absorption-into-`Cpair` + zero-endpoint closure, route-independently.)
    • `collar_hGpow_residual` — the ENUMERATED surviving carry (genuine conjunction, non-vacuous
      plumbing witness) after this factoring: `hOnCollar` (the collar bundle's on-collar 3-term
      integrand identity + amplitude sups — BANKED via `amplitudeDataOn_concrete` /
      `sliverIntegrand_on_collar`) ∧ `hOffCollarTail` (the OFF-COLLAR corrected Gaussian-tail
      remainder that reconstitutes the full-space Hessian moment, yielding the `hinner_window` shape).
      The SOLE surviving curved geometric input for the HI-leg is `hOffCollarTail`; `hOnCollar` is the
      collar bundle (whose remaining input is `hjets`).  ⚠ NOT `a₁ = R/6`.

  ⚠  `a₁ = R/6` remains CONDITIONAL and effectively FLAT-ONLY.  Exposing the closure boundary does NOT
  derive the coefficient, and does NOT close the collar route: the off-collar corrected-tail carry
  `hOffCollarTail`, the collar bundle's `hjets`, the capped leg-2 `hLapFull`, the convergence trio, and
  the Seeley–DeWitt geometric wiring ALL remain.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.AmplitudeDerivativeDataConcrete
import QIQTH.GpowBridge
import QIQTH.GpowClosure

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.RadialDistance QIQTH.GaussianConvolution
open scoped Interval Topology BigOperators

namespace QIQTH.HGpowFromCollar

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the route-agnostic `hGpow` closure boundary.
    ############################################################################### -/

/-- **★★★ `hGpow_from_innerWindow`.**  THE ROUTE-AGNOSTIC `hGpow` CLOSURE.  Faithfully factors the
    SECOND HALF (stage II) of `MemAdjHiMomentBound.hGpow_of_amplitudeData`: given the per-slice
    OPEN-window inner bound `hinner_window` in the exact `K₁·(u−s)^{-1/2} + K₀` shape — supplied by
    WHATEVER route (the all-`z` `slice2_inner_bound`, OR a collar/off-collar split) — and `1 ≤ n`
    (for the internal endpoint discharge), there is a SINGLE `m`- and `i`-uniform `Cpair ≥ 0` with the
    EXACT `hGpow` type on `Set.uIoc (u − ε_m) u`.  Route (PURE THREADING, no new analysis):
      `GpowBridge.leviSecondPairing_le_invSqrt` (⟹ `Cpair` + OPEN-window `hGpow`)
        → `GpowClosure.hGpow_uIoc_of_Ioo_zeroEndpoint` (⟹ `uIoc` `hGpow`),
    with the single `τ = 0` (`s = u`) measure-zero endpoint supplied INTERNALLY from
    `AmplitudeDerivativeDataConcrete.hEndpoint_discharged` (unconditional for `n ≥ 1`).  This is the
    stable interface both the all-`z` route and the collar route must hit.  ⚠ NOT `a₁ = R/6`. -/
theorem hGpow_from_innerWindow (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hn : 1 ≤ n)
    (K₁ K₀ : ℝ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀)
    (hinner_window : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ K₁ * (u - s) ^ (-(1 : ℝ) / 2) + K₀) :
    ∃ Cpair : ℝ, 0 ≤ Cpair ∧
      ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) := by
  -- stage II.a: the `m`-uniform `τ^{-1/2}` absorption (upper-endpoint trick) → OPEN-window `Cpair`.
  obtain ⟨Cpair, hCpair, hIoo⟩ :=
    QIQTH.GpowBridge.leviSecondPairing_le_invSqrt (n := n) U K₁ K₀ hK₁ hK₀
      (fun m i u s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      hinner_window
  -- stage II.b: the `Ioo → uIoc` endpoint upgrade → the EXACT `hGpow` type.
  refine ⟨Cpair, hCpair, ?_⟩
  exact QIQTH.GpowClosure.hGpow_uIoc_of_Ioo_zeroEndpoint (n := n) U Cpair
    (fun m i u s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    hIoo
    (QIQTH.AmplitudeDerivativeDataConcrete.hEndpoint_discharged g gi hChr hK S a b hn U)

/-! ###############################################################################
    ### §2 — the scoped surviving collar/off-collar split carry.
    ############################################################################### -/

/-- **`collar_hGpow_residual`.**  THE ENUMERATED SURVIVING RESIDUE for producing the HI-leg `hGpow`
    from the COLLAR bundle, after the J4-545 closure factoring (`hGpow_from_innerWindow`).  A genuine
    conjunction (non-vacuous plumbing witness), machine-checkable; each conjunct SATISFIABLE, none the
    conclusion.

    THE LEDGER (what a collar-driven `hinner_window` — hence `hGpow` via `hGpow_from_innerWindow` —
    still consumes):
      1. `hOnCollar`      — the collar bundle's ON-collar contribution: the 3-term Leibniz–Gaussian
         integrand identity + amplitude sup-bounds on `‖z‖ ≤ c√τ`.  This is BANKED
         (`AmplitudeDataOnCollar.amplitudeDataOn_concrete` / `SliverBoundOnCollar.sliverIntegrand_on_collar`,
         with `hD2HexpandOn` from a chart-jet bundle `hjets`).
      2. `hOffCollarTail` — ★ the OFF-COLLAR CORRECTED Gaussian-tail remainder on `‖z‖ > c√τ`: NOT a
         mere absolute bound on the truncated integrand, but the cancellation-aware remainder that
         RECONSTITUTES the full-space Hessian moment `∫ (z_i²−2τ)/(4τ²)·G_τ = 0` (destroyed by the
         `τ`-shrinking collar truncation), so that `hOnCollar + hOffCollarTail` yields the per-slice
         inner bound in the `K₁·(u−s)^{-1/2} + K₀` shape.  ⚠ This is the GENUINE unbuilt geometric
         carry — the surviving curved input of the HI-leg.

    DISCHARGED (NOT in this ledger): the `τ = 0` measure-zero endpoint value (supplied internally by
    `hGpow_from_innerWindow` from `hEndpoint_discharged`, unconditional for `n ≥ 1`), with NO residue.
    ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly this surface. -/
def collar_hGpow_residual (hOnCollar hOffCollarTail : Prop) : Prop :=
  hOnCollar ∧ hOffCollarTail

/-- The collar-`hGpow` ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem collar_hGpow_residual_intro {hOnCollar hOffCollarTail : Prop}
    (h1 : hOnCollar) (h2 : hOffCollarTail) :
    collar_hGpow_residual hOnCollar hOffCollarTail :=
  ⟨h1, h2⟩

end QIQTH.HGpowFromCollar

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HGpowFromCollar.hGpow_from_innerWindow
#print axioms QIQTH.HGpowFromCollar.collar_hGpow_residual_intro
