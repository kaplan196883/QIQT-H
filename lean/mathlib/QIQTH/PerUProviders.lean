/-
  PerUProviders — J4-405: Sol #17 F1 + the J4-404 handoff — the per-`u` provider bundle.

  Two jobs of the `a₁ = R/6` heat-kernel campaign.  This file is **NOT** `a₁ = R/6` and proves
  NOTHING about `R/6`.  `a₁ = R/6` remains CONDITIONAL on the whole `hDuhamel` / convergence-trio +
  geometric-wiring stack AND on the SURVIVING labelled census carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem here is either (P1) a re-threading of the BANKED spatial-line
  differentiation `CConvV2DerivRep.hlin_as_D` from a per-`(x,i)` provider bundle of its own genuine
  diff-under-∫ side conditions (each SATISFIABLE, non-vacuous, NONE the conclusion), or (P2) the
  DEGENERATE-window leg of the `MemInterchange` `∀ u`-widening, in which the Levi source vanishes so
  BOTH sides collapse to `0` — proved UNCONDITIONALLY.  NO `sorry` (header prose excepted), NO new
  axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding)
  a `R/6` conclusion, NO existing file edited, nothing committed, nothing wired into
  `QIQTH.lean` / `AxiomAudit`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (P1) THE CONCRETE `hlin` SIDE-CONDITION PACKAGE (Sol #17 F1).

  The FACADE's `CConvFacade.CConvDerivativeData.hlin` field is, at the concrete van-Vleck gated witness
  `W := vanVleckGatedWitness g gi hC hK S a b` and Levi source
  `Fconv := leviSeries (heatOp g gi W)`, the family
      `∀ x ∈ u, ∀ i, HasDerivAt (fun w => heatConv W Fconv t (update x i w) 0)
                       ((Dmap … Fconv t x)(Pi.single i 1)) (x i)`.
  `CConvV2DerivRep.hlin_as_D` produces EACH member from the SEVEN genuine spatial-line
  differentiation-under-∫ side conditions (`snb`/`hsnb`, `hFmeas`, `hFint`, `hF'meas`,
  `bound`/`hbdd`, `hbound`, `hdiff`).  This file BUNDLES those seven into ONE per-`(x,i)` provider
  existential (`hProv`) — the EXACT `hFrozenData`-shape of the banked D feeder `W2Finish.w2_hQ1`, but
  on the DIAGONAL non-truncated `heatConv` window `uIoc 0 t` (the `t := u`, `heatConvFrozen → heatConv`
  specialization) with `Fconv := leviSeries (heatOp g gi W)` — and threads it through `hlin_as_D` to
  export the concrete census-shaped `hlin` field.  `hProv` is the honest carry: the seven bundled
  side conditions are exactly the banked D-feeder legs (measurabilities from
  `W2Package.w2_hFmeas`/`w2_hF'meas`'s Fubini-inner engine, interval-integrability from
  `W2Finish.w2_hFint`'s capped-ceiling engine, the outer `HasDerivAt` slice family from `w2_hQ1`'s
  frozen interchange, the `bound`/`hbdd`/`hbound` triple from the W2 majorant), and the C-pile
  continuity/majorants; NONE is a `R/6` statement.

  ## (P2) THE `MemInterchange` `∀ u`-TAIL (the J4-404 handoff, degenerate leg).

  `DaLimLUWallRecon.MemInterchange H F U pdpdH` quantifies `∀ (m i), ∀ u ∈ U`.  The `∀ u`-tail beyond
  `U` splits (as in `ESLegWidening` / `AllUSliceMeas`) on `rcases le_or_gt (u − epsSeq m) 0`.  In the
  DEGENERATE window `u − epsSeq m ≤ 0`, the oriented `s`-interval `0..(u−εₘ)` has unordered core
  `Ι 0 (u−εₘ) ⊆ {s ≤ 0}`, on which the Levi source `F s z 0` VANISHES (`hFzero`), so:
    •  the frozen convolution `heatConvFrozen H F u (u−εₘ) x 0 = 0` for EVERY `x` — hence its `pd∘pd`
       (LHS) is the double partial of the identically-zero function, `= 0`;
    •  the RHS strip integral `∫ s in 0..(u−εₘ), ∫ z, pdpdH i (u−s) z · F s z 0 = 0` likewise.
  Both sides collapse to `0`; the interchange holds UNCONDITIONALLY on the degenerate tail.  This is
  the exact measurability/integrability twin of `ESLegWidening.intervalIntegrable_of_deg` for the
  interchange EQUATION.  The `∀ u ∈ U` part stays the banked carry; `memInterchange_widened`
  assembles the two into the honest `(u ∈ U ∨ u − εₘ ≤ 0)`-reduction.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CConvV2DerivRep
import QIQTH.DaLimLUWallRecon

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.HeatDuhamel
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.DaLimLUWallRecon
open scoped Interval Topology BigOperators

namespace QIQTH.PerUProviders

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (P1) — the concrete census-shaped `hlin` field from the per-`(x,i)` provider.
    ############################################################################### -/

/-- **★★ (P1) `hlin_field_concrete` — THE CONCRETE CENSUS-SHAPED `hlin` FIELD.**  For the concrete
    van-Vleck gated witness `W := vanVleckGatedWitness g gi hC hK S a b` and Levi source
    `Fconv := leviSeries (heatOp g gi W)`, on a spatial neighbourhood `u` and fixed heat-time `t`,
    exports the FACADE `CConvDerivativeData.hlin` field
      `∀ x ∈ u, ∀ i, HasDerivAt (fun w => heatConv W Fconv t (update x i w) 0)
                       ((Dmap … Fconv t x)(Pi.single i 1)) (x i)`,
    by unpacking the per-`(x,i)` provider `hProv` (the SEVEN spatial-line differentiation-under-∫
    side conditions bundled into one existential — the `hFrozenData`-shape of the banked D feeder
    `W2Finish.w2_hQ1`, specialized to the diagonal `heatConv` window `uIoc 0 t`) and threading each
    member through `CConvV2DerivRep.hlin_as_D`.  Honest carry: `hProv` (each of its seven legs is a
    genuine, satisfiable diff-under-∫ side condition from the banked D feeders + C-pile
    continuity/majorants; NONE is the conclusion).  ⚠ NOT `a₁ = R/6`. -/
theorem hlin_field_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hProv : ∀ x ∈ u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 t ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t)) ∧
        IntervalIntegrable bound volume 0 t ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w)) :
    ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hC hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) t
          (Function.update x i w) 0)
        ((QIQTH.CConvV2DerivRep.Dmap g gi hC hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) t x)
          (Pi.single i (1 : ℝ))) (x i) := by
  intro x hx i
  obtain ⟨snb, bound, hsnb, hFmeas, hFint, hF'meas, hbdd, hbound, hdiff⟩ := hProv x hx i
  exact QIQTH.CConvV2DerivRep.hlin_as_D g gi hC hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) t i x
    snb hsnb hFmeas hFint hF'meas bound hbdd hbound hdiff

/-! ###############################################################################
    ### (P2) — the DEGENERATE-window leg of the `MemInterchange` `∀ u`-widening.
    ############################################################################### -/

/-- **★ (P2·helper) `frozenPairing_deg_zero`.**  On a degenerate/reversed interval (`β ≤ 0`), the
    space-time frozen pairing integral vanishes: `Ι 0 β = Ioc β 0 ⊆ {s ≤ 0}`, on which the Levi
    source `F s z 0 = 0` (`hFzero`), so the inner `z`-integral is `0` EVERYWHERE on the interval and
    the outer `intervalIntegral` is `0`.  Generic in the first factor `A`.  ⚠ NOT `a₁ = R/6`. -/
theorem frozenPairing_deg_zero (A F : ℝ → Point n → Point n → ℝ) (u β : ℝ) (x : Point n)
    (hβ : β ≤ 0) (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, F s z 0 = 0) :
    (∫ s in (0:ℝ)..β, ∫ z, A (u - s) x z * F s z 0) = 0 := by
  have hEq : Set.EqOn (fun s => ∫ z, A (u - s) x z * F s z 0) (fun _ => (0 : ℝ))
      (Set.uIcc 0 β) := by
    intro s hs
    have hub : s ∈ Set.Icc (min 0 β) (max 0 β) := hs
    have hs0 : s ≤ 0 := by
      have h2 : s ≤ max 0 β := hub.2
      rwa [max_eq_left hβ] at h2
    show (∫ z, A (u - s) x z * F s z 0) = (0 : ℝ)
    have hzf : (fun z => A (u - s) x z * F s z 0) = fun _ => (0 : ℝ) := by
      funext z; rw [hFzero s hs0 z, mul_zero]
    rw [hzf]; exact integral_zero (Point n) ℝ
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]

/-- **(P2·helper) `pd_zero`.**  The partial derivative of the identically-zero field is `0`. -/
theorem pd_zero (i : Fin n) (x : Point n) : pd (fun _ : Point n => (0 : ℝ)) i x = 0 := by
  unfold pd; simp

/-- **★★ (P2) `memInterchange_body_deg` — THE DEGENERATE-WINDOW LEG.**  For ANY `(m, i, u)` with the
    DEGENERATE window `u − epsSeq m ≤ 0`, the `MemInterchange` body holds UNCONDITIONALLY (BOTH sides
    collapse to `0` via the Levi vanishing `hFzero`):
      `pd (fun y => pd (fun x => heatConvFrozen H F u (u−εₘ) x 0) i y) i 0
         = ∫ s in 0..(u−εₘ), ∫ z, pdpdH i (u−s) z · F s z 0`.
    LHS: `heatConvFrozen H F u (u−εₘ) x 0 = 0` for every `x` (`frozenPairing_deg_zero`), so the
    `pd∘pd` of the identically-zero function is `0` (`pd_zero` twice).  RHS: the strip integral is
    `0` (`frozenPairing_deg_zero` at `A := fun τ _ z => pdpdH i τ z`).  The interchange EQUATION twin
    of `ESLegWidening.intervalIntegrable_of_deg`.  Honest carry: `hFzero` (banked Levi source
    vanishing).  ⚠ NOT `a₁ = R/6`. -/
theorem memInterchange_body_deg (H F : ℝ → Point n → Point n → ℝ)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, F s z 0 = 0)
    (m : ℕ) (i : Fin n) (u : ℝ) (hdeg : u - epsSeq m ≤ 0) :
    pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
      = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
  -- LHS: the frozen conv is identically 0, so its double partial is 0.
  have hInner : (fun x : Point n => heatConvFrozen H F u (u - epsSeq m) x 0) = fun _ => (0 : ℝ) := by
    funext x
    unfold heatConvFrozen
    exact frozenPairing_deg_zero H F u (u - epsSeq m) x hdeg hFzero
  have hLHS : pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0 = 0 := by
    rw [hInner]
    have hmid : (fun y : Point n => pd (fun _ : Point n => (0 : ℝ)) i y) = fun _ => (0 : ℝ) := by
      funext y; exact pd_zero i y
    rw [hmid]; exact pd_zero i 0
  rw [hLHS]; symm
  exact frozenPairing_deg_zero (fun τ _ z => pdpdH i τ z) F u (u - epsSeq m) 0 hdeg hFzero

/-- **★★★ (P2) `memInterchange_widened` — THE HONEST `∀ u`-REDUCTION.**  Assembles the banked
    `MemInterchange H F U pdpdH` carry (`∀ (m i), ∀ u ∈ U`) with the unconditional degenerate leg
    `memInterchange_body_deg` into the widened `(u ∈ U ∨ u − epsSeq m ≤ 0)` shape: the interchange
    EQUATION holds for every `(m, i, u)` that is EITHER in the census window `U` OR degenerate.  The
    `∀ u ∈ U` half is the banked carry `hU`; the degenerate half is closed by the Levi vanishing
    `hFzero`.  Honest carries: `hFzero`, `hU`.  ⚠ NOT `a₁ = R/6`. -/
theorem memInterchange_widened (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, F s z 0 = 0)
    (hU : MemInterchange H F U pdpdH) :
    ∀ (m : ℕ) (i : Fin n) (u : ℝ), (u ∈ U ∨ u - epsSeq m ≤ 0) →
      pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
        = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
  intro m i u hu
  rcases hu with hin | hdeg
  · exact hU m i u hin
  · exact memInterchange_body_deg H F pdpdH hFzero m i u hdeg

end QIQTH.PerUProviders

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.PerUProviders
#print axioms hlin_field_concrete
#print axioms frozenPairing_deg_zero
#print axioms pd_zero
#print axioms memInterchange_body_deg
#print axioms memInterchange_widened
end AxiomChecks
