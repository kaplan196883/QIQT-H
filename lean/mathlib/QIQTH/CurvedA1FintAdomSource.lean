/-
  CurvedA1FintAdomSource — J4-569.  SOURCE the last non-measurability carry of the `hFint` census
  member (`CurvedA1ClassBFint.curved_hFint_at_gate`) — its per-`m` CAPPED first-derivative Gaussian
  domination `hAdom` — from a NAMED banked-shape crude first-derivative envelope, via the ε-absorption
  arithmetic (the FIRST-derivative sibling of `EveryCeilingFamilies.gaussDdim_crude_to_capped`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This file turns the `hFint` carrier `hAdom` from a whole
  opaque carry into `{crude first-derivative envelope}  ⊕  {banked ε-absorption arithmetic}`, exactly
  mirroring how `CappedAdom2Audit.hAdom2_capped_family_of_crude` sources the SECOND-derivative capped
  family from the banked crude `τ⁻¹` envelope.  It does NOT make `a₁ = R/6` unconditional: the crude
  first-derivative geometric envelope `hcrude` (the honest carried residual, scoped precisely below),
  the `hFint_d` sibling's `hAdom`, `hsrc`, `hOffCollarTail`, the convergence trio, and `hInnerCont`
  all remain owed.

  ── THE SATISFIABILITY CORE (why capped-true / clean-false).  The census `hFint` binder demands a
  per-`m` CAPPED domination
      `∀ m i τ, epsSeq m ≤ τ → τ ≤ T → ∀ z, |witnessFieldDeriv g^K … i τ 0 z| ≤ CA m · gaussDdim (wA·τ) (0−z)`
  with `CA : ℕ → ℝ` (a constant chosen AFTER `m`).  The CLEAN whole-time analogue (a single `m`-free
  `CA`, `∀ τ > 0`) is **GENUINELY FALSE** at `g^K`: the first spatial derivative of the heat parametrix
  `∂_x G_τ` carries a `τ^(−1/2)` prefactor that blows up as `τ → 0` (the first-derivative sibling of the
  `τ⁻¹` second-derivative pathology documented in `CensusDominations` D3 / `CappedAdom2Audit`).  On the
  ε-floored range `epsSeq m ≤ τ`, however, `(Real.sqrt τ)⁻¹ ≤ (Real.sqrt (epsSeq m))⁻¹`, so the
  prefactor is absorbed into the per-`m` constant `CA m = Ccrude · (Real.sqrt (epsSeq m))⁻¹` — which
  MUST and DOES depend on `m` (`≈ (epsSeq m)^(−1/2)`).  A single `m`-independent `CA` = the FALSE clean
  bound = the vacuity trap the budget script does not catch.

  ── WHAT IS PROVED (axiom-free, no `sorry`).
    •  `sqrt_crude_to_capped` — the ε-absorption arithmetic for a `τ^(−1/2)` crude prefactor (the
       first-derivative sibling of the banked `gaussDdim_crude_to_capped`, which does the `τ⁻¹` case):
       a whole-time `Ccrude·(Real.sqrt τ)⁻¹·gaussDdim (wL·τ)(0−z)` bound on `(0,Tc]` restricted to
       `[εₘ,Tc]` becomes the genuine Gaussian bound `(Ccrude·(Real.sqrt εₘ)⁻¹)·gaussDdim (wL·τ)(0−z)`.
    •  `curved_hFint_hAdom_at_gate` — THE EXACT `hAdom` binder shape consumed by
       `CurvedA1ClassBFint.curved_hFint_at_gate`, produced from the crude first-derivative envelope
       `hcrude` for `g^K`, with `wA` passed through and `CA m := Ccrude·(Real.sqrt (epsSeq m))⁻¹`.
    •  `curved_hFint_at_gate_via_crude` — the demonstrator: `curved_hFint_at_gate` re-derived with its
       `hAdom` slot FILLED by `curved_hFint_hAdom_at_gate`, proving the binder plugs in verbatim.
    •  `curved_hFint_hAdom_at_gate_curved_satisfiable` — the CURVED (not-secretly-flat) gate.

  ── THE CARRIED RESIDUAL (scoped precisely; honest, non-vacuous, never the conclusion).
    •  `hcrude` — the crude first-derivative Gaussian envelope for `g^K` at the frozen field point 0:
       `∀ i τ, 0 < τ → τ ≤ T → ∀ z, |witnessFieldDeriv g^K … i τ 0 z| ≤ Ccrude·(Real.sqrt τ)⁻¹·gaussDdim (wA·τ)(0−z)`.
       This is TRUE for `g^K` (the genuine first-derivative envelope carries exactly a `τ^(−1/2)`
       prefactor; cf. the banked SECOND-derivative curved crude envelope
       `CurvedRNCHeatOpDom2.curvedRNC_witnessSecondXDeriv_dom_crude`, one power weaker for the first
       derivative) and is the honest banked-shape base-bound.  NO banked curved FIRST-derivative crude
       envelope exists yet (there is no `WideAmplitudeData.first_domination`, only `zeroth`/`second`), so
       it is carried; the value of this brick is that the ε-absorption arithmetic — previously bundled
       inside the opaque `hAdom` carry — is now BANKED, and the residual is reduced to precisely that
       crude geometric envelope.

  NO `sorry`.  NO new axioms.  NO `:= True`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CurvedA1ClassBFint
import QIQTH.EveryCeilingFamilies

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.LeviSeriesLocalData
open QIQTH.DaLimLUWallRecon QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness QIQTH.A1R6CoreAtGate
open QIQTH.CurvedA1ClassBFint QIQTH.EveryCeilingFamilies
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1FintAdomSource

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### THE `τ^(−1/2)` ε-ABSORPTION ARITHMETIC (the first-derivative sibling of `gaussDdim_crude_to_capped`).
    ############################################################################### -/

/-- **★ J4-569 (arithmetic) — `sqrt_crude_to_capped`.**  THE FIRST-DERIVATIVE UNLOCK ARITHMETIC.  A crude
    `Ccrude·(Real.sqrt τ)⁻¹·gaussDdim (wL·τ)(0−z)` bound valid on `(0, Tc]` — whose `τ^(−1/2)` prefactor
    blows up as `τ → 0` (the first-derivative pathology, one power weaker than the `τ⁻¹` second-derivative
    wall) — restricted to the lower-capped range `[εₘ, Tc]` becomes the GENUINE Gaussian bound
    `(Ccrude·(Real.sqrt εₘ)⁻¹)·gaussDdim (wL·τ)(0−z)`, via `(Real.sqrt τ)⁻¹ ≤ (Real.sqrt εₘ)⁻¹` for
    `τ ≥ εₘ > 0`.  Generic in `A`; the exact first-derivative analogue of the banked
    `EveryCeilingFamilies.gaussDdim_crude_to_capped` (which does the `τ⁻¹` second-derivative case).
    ⚠ NOT `a₁ = R/6`. -/
theorem sqrt_crude_to_capped (A : ℝ → Point n → Point n → ℝ)
    (Tc εₘ Ccrude wL : ℝ) (hεₘ : 0 < εₘ) (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ τ : ℝ, 0 < τ → τ ≤ Tc → ∀ z : Point n,
        |A τ 0 z| ≤ Ccrude * (Real.sqrt τ)⁻¹ * gaussDdim (wL * τ) (0 - z)) :
    ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
      |A τ 0 z| ≤ (Ccrude * (Real.sqrt εₘ)⁻¹) * gaussDdim (wL * τ) (0 - z) := by
  intro τ hτlo hτTc z
  have hτ0 : 0 < τ := lt_of_lt_of_le hεₘ hτlo
  refine le_trans (hcrude τ hτ0 hτTc z) ?_
  have hposε : (0 : ℝ) < Real.sqrt εₘ := Real.sqrt_pos.mpr hεₘ
  have hposτ : (0 : ℝ) < Real.sqrt τ := Real.sqrt_pos.mpr hτ0
  have hsqrtle : Real.sqrt εₘ ≤ Real.sqrt τ := Real.sqrt_le_sqrt hτlo
  have hinv : (Real.sqrt τ)⁻¹ ≤ (Real.sqrt εₘ)⁻¹ := by
    rw [inv_le_inv₀ hposτ hposε]; exact hsqrtle
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinv hCcrude) (gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### THE `hAdom` SOURCE for `curved_hFint_at_gate` at `g^K`.
    ############################################################################### -/

/-- **★★★ J4-569 — `curved_hFint_hAdom_at_gate`.**  THE EXACT per-`m` CAPPED first-derivative Gaussian
    domination `hAdom` consumed by `CurvedA1ClassBFint.curved_hFint_at_gate`, at the genuinely-curved
    witness `g^K = curvedRNCMetric κ`, SOURCED from the crude first-derivative envelope `hcrude` for
    `g^K` via the ε-absorption arithmetic `sqrt_crude_to_capped`.  The window width `wA` is passed
    through unchanged, and the per-`m` constant is `CA m := Ccrude·(Real.sqrt (epsSeq m))⁻¹` — which
    depends on `m` (`≈ (epsSeq m)^(−1/2)`), the ONLY honest choice: a single `m`-free constant would be
    the FALSE clean whole-time bound (the `τ^(−1/2)` blow-up at `τ → 0`).  This banks the ε-absorption
    step that was previously buried inside the opaque `hAdom` carry.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_hAdom_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T wA Ccrude : ℝ)
    (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Ccrude * (Real.sqrt τ)⁻¹ * gaussDdim (wA * τ) (0 - z)) :
    ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
      |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
        ≤ (Ccrude * (Real.sqrt (epsSeq m))⁻¹) * gaussDdim (wA * τ) (0 - z) := by
  intro m i
  exact sqrt_crude_to_capped
    (fun τ _p z => witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z)
    T (epsSeq m) Ccrude wA (epsSeq_pos m) hCcrude
    (fun τ hτ0 hτT z => hcrude i τ hτ0 hτT z)

/-- **★★ J4-569 (demonstrator) — `curved_hFint_at_gate_via_crude`.**  The `hFint` census member
    (`curved_hFint_at_gate`), re-derived with its `hAdom` slot FILLED by `curved_hFint_hAdom_at_gate`.
    This proves the sourced binder plugs into the capstone carrier VERBATIM: `wA := wA`,
    `CA := fun m => Ccrude·(Real.sqrt (epsSeq m))⁻¹`, with the remaining Levi/measurability carries
    (`hFdom`/`hFzero`/`hmeas`) forwarded unchanged.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_at_gate_via_crude (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (U : Set ℝ) (T : ℝ)
    (wA Ccrude wF CF : ℝ)
    (hwA : 0 < wA) (hCcrude : 0 ≤ Ccrude) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Ccrude * (Real.sqrt τ)⁻¹ * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0 = 0)
    (hmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m) :=
  curved_hFint_at_gate κ hChr hK a b c U T wA
    (fun m => Ccrude * (Real.sqrt (epsSeq m))⁻¹) wF CF hwA
    (fun m => mul_nonneg hCcrude (by positivity)) hwF hCF hUpos hUT
    (curved_hFint_hAdom_at_gate κ hChr hK a b c T wA Ccrude hCcrude hcrude)
    hFdom hFzero hmeas

/-- **★ J4-569 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the sourced `hAdom`
    binder is discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.  NOT
    `a₁ = R/6`. -/
theorem curved_hFint_hAdom_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintAdomSource

section AxiomChecks
open QIQTH.CurvedA1FintAdomSource
#print axioms sqrt_crude_to_capped
#print axioms curved_hFint_hAdom_at_gate
#print axioms curved_hFint_at_gate_via_crude
#print axioms curved_hFint_hAdom_at_gate_curved_satisfiable
end AxiomChecks
