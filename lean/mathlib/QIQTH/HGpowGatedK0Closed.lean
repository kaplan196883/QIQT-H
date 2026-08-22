/-
  HGpowGatedK0Closed — the `hGpow` moment-cancellation carry (of `MemAdjHiSliver.hII_hi_from_sliver` /
  `MemAdjHiMomentBound.hGpow_of_amplitudeData`) discharged UNCONDITIONALLY at the genuinely-curved
  `K = {0}` witness, by the SAME null-singleton base-gate mechanism that closed `hbint`/`hzmass`/the
  mixed field-Hessian envelope (J4-984/985/989) — WITHOUT the amplitude-data bundle, and WITHOUT the
  `RadialNormalCoordinateGauge`/`hjets`/opaque-chart route (`AmplitudeDerivativeDataOn`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MECHANISM (null-support of the SECOND `x`-derivative object).

  `witnessSecondXDeriv g gi hC hK S a b i τ z`
      `= pd (fun x => pd (fun x' => vanVleckGatedWitness … τ x' z) i x) i 0`
  is a NESTED field-slot partial of `x' ↦ vanVleckGatedWitness … τ x' z`.  The witness is a
  `gatedKernel K S H`, whose BASE-POINT slot is the THIRD argument `z` (= `q`), NOT the differentiation
  variable `x'`.  So for `z ∉ K` the base gate fires (`gatedKernel_apply_of_notMem … (Or.inl hz)`) and
  the WHOLE field function `x' ↦ vanVleckGatedWitness … τ x' z` is identically `0`, hence both nested
  `pd`'s vanish (`pd_const`) — EXACTLY the property already banked for the FIRST field-derivative
  `witnessFieldDeriv_eqZero_of_base_notMem_K` (J4-867), now transferred to the second-`x`-derivative
  object.  This is the object the `hGpow` z-integrand pairs with `leviSeries`.

  At the concrete curved witness `K = {0}` (`1 ≤ n ⟹ NoAtoms volume`): for EVERY time slot the z-integrand
  `witnessSecondXDeriv … i (u−s) z · leviSeries … s z 0` vanishes for `z ≠ 0`, so it is supported in the
  null singleton `{0}` and `∫ z = 0` for EVERY `s` (independent of `u−s`).  Hence `hGpow` holds with the
  constant `Cpair := 0`:  `|∫ z …| = 0 ≤ 0 · (u−s)^{-1/2}`.  No moment cancellation, no `hD2Hexpand`
  Leibniz-Gaussian decomposition, no chart Jacobian, no endpoint carry — the pairing is IDENTICALLY zero.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  ONLY the `hGpow` SUB-PIECE of the `hDuhamel` gate-chain, and ONLY at the degenerate `K = {0}` witness,
  where the whole pairing vanishes (null-singleton base gate; curved geometry does NO analytic work).  It
  does NOT close `hDuhamel` — which was proven NOT to hold at `K = {0}` (J4-989: the diagonal parametrix
  residual `E t 0 0 ≠ 0` for a nonflat witness; the same singleton-base collapse that trivialises `hGpow`
  cannot reproduce that nonzero value).  So `a₁ = R/6` remains STRICTLY CONDITIONAL on
  {hDuhamel, hDConv, hCConv}, UNCHANGED.  gpt-5.6-sol (high, 2026-08-22) GO-audited the transfer of the
  null-support mechanism to the nested-`pd` second-derivative object and the `Cpair := 0` discharge.  No
  `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, none equal to the conclusion,
  no existing file edited, nothing forced.

  ## WHAT LANDS (ns `QIQTH.HGpowGatedK0Closed`).
    • `witnessSecondXDeriv_eqZero_of_base_notMem_K` — ★ the second-`x`-derivative object vanishes for
      `z ∉ K` (unconditional, any `K`); nested-`pd` transfer of `witnessFieldDeriv_eqZero_of_base_notMem_K`.
    • `secondXDeriv_pairing_integral_gatedK0_eqZero` — the `z`-pairing integral is `0` at `K = {0}`
      (null-singleton base gate), for ANY right kernel, time `τ`, `s`, `y`.
    • `hGpow_gatedK0_closed` — ★★★ the EXACT `hGpow` type of `MemAdjHiMomentBound.hGpow_of_amplitudeData`
      (`hK := isCompact_singleton`, `1 ≤ n`), delivered with `Cpair = 0`.
-/
import Mathlib
import QIQTH.MemAdjHiMomentBound
import QIQTH.HZMassFullyClosedCurved

open MeasureTheory Set Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open scoped BigOperators Topology Interval

namespace QIQTH.HGpowGatedK0Closed

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — off-`K` vanishing of the SECOND `x`-derivative object (nested `pd`).
    ############################################################################### -/

/-- **★ OFF-`K` VANISHING of the second-`x`-derivative object (base slot).**  For a base point
    `z ∉ K`, the gated witness `x' ↦ vanVleckGatedWitness … τ x' z` is identically `0` (the base gate
    `gatedKernel … (Or.inl hz)` kills the whole kernel), so BOTH nested field-slot `pd`'s of
    `witnessSecondXDeriv` vanish (`pd_const`).  Nested-`pd` transfer of
    `HZMassIntegrabilityAttempt.witnessFieldDeriv_eqZero_of_base_notMem_K` (J4-867).  Unconditional. -/
theorem witnessSecondXDeriv_eqZero_of_base_notMem_K (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (hz : z ∉ K) :
    witnessSecondXDeriv g gi hC hK S a b i τ z = 0 := by
  have hfun : (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext x'
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  have hinner : (fun x : Point n =>
      pd (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext x
    rw [hfun]
    exact pd_const 0 i x
  unfold witnessSecondXDeriv
  rw [hinner]
  exact pd_const 0 i 0

/-! ###############################################################################
    ### §2 — the `z`-pairing integral vanishes at `K = {0}` (null-singleton base gate).
    ############################################################################### -/

/-- **★ `secondXDeriv_pairing_integral_gatedK0_eqZero`.**  At the `K = {0}` witness, the signed
    `z`-pairing of the second-`x`-derivative object with ANY right kernel `B` vanishes: for `z ≠ 0` the
    base gate kills `witnessSecondXDeriv … i τ z` (`witnessSecondXDeriv_eqZero_of_base_notMem_K`), so the
    integrand is supported in the null singleton `{0}` (`1 ≤ n ⟹ NoAtoms volume`), hence `∫ z = 0`.
    Holds for ANY `g gi S a b i`, times `τ s`, right kernel `B`, final point `y`. -/
theorem secondXDeriv_pairing_integral_gatedK0_eqZero (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ) (i : Fin n) (τ s : ℝ)
    (B : ℝ → Point n → Point n → ℝ) (y : Point n) :
    (∫ z, witnessSecondXDeriv g gi hC
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i τ z
      * B s z y) = 0 := by
  have hn0 : 0 < n := by omega
  haveI : Inhabited (Fin n) := ⟨⟨0, hn0⟩⟩
  haveI : Nontrivial (Point n) := Pi.nontrivial
  refine QIQTH.HZMassFullyClosedCurved.integral_eq_zero_of_support_subset_singleton
    (μ := (volume : Measure (Point n)))
    (fun z => witnessSecondXDeriv g gi hC
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i τ z * B s z y)
    (0 : Point n) ?_
  intro z hz
  rw [Set.mem_singleton_iff]
  by_contra hz0
  have hzK : z ∉ ({0} : Set (Point n)) := fun h => hz0 (Set.mem_singleton_iff.mp h)
  have hw : witnessSecondXDeriv g gi hC
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i τ z = 0 :=
    witnessSecondXDeriv_eqZero_of_base_notMem_K g gi hC _ S a b i τ z hzK
  exact (Function.mem_support.mp hz) (by rw [hw, zero_mul])

/-! ###############################################################################
    ### §3 — ★★★ the EXACT `hGpow` type, delivered with `Cpair = 0`.
    ############################################################################### -/

/-- **★★★ `hGpow_gatedK0_closed`.**  THE `hGpow` MOMENT-CANCELLATION CARRY, discharged UNCONDITIONALLY
    at the genuinely-curved `K = {0}` witness.  Exactly the conclusion type of
    `MemAdjHiMomentBound.hGpow_of_amplitudeData` (`hK := isCompact_singleton`), but obtained WITHOUT the
    `AmplitudeDerivativeData` bundle and WITHOUT the `RadialNormalCoordinateGauge`/`hjets`/opaque-chart
    route:
      `∃ Cpair ≥ 0, ∀ m i, ∀ u ∈ U, ∀ s ∈ uIoc (u − εₘ) u,
         |∫ z, witnessSecondXDeriv … i (u−s) z · leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0|
           ≤ Cpair · (u−s)^{-1/2}`.
    At `K = {0}` the `z`-pairing integral is IDENTICALLY `0` for every `s`
    (`secondXDeriv_pairing_integral_gatedK0_eqZero`), so the bound holds with `Cpair := 0`
    (`|0| = 0 ≤ 0 · (u−s)^{-1/2}`).

    ⚠ This closes ONLY the `hGpow` SUB-PIECE of `hDuhamel`, and ONLY at this degenerate witness where the
    pairing vanishes.  `hDuhamel` itself does NOT hold at `K = {0}` (J4-989: `E t 0 0 ≠ 0`).  NON-VACUOUS:
    a genuine integral-bound fact about a concrete function; `1 ≤ n` and the smooth-Christoffel carrier
    `hChr` are ordinary satisfiable data.  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}. -/
theorem hGpow_gatedK0_closed (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ) (U : Set ℝ) :
    ∃ Cpair : ℝ, 0 ≤ Cpair ∧
      ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) := by
  refine ⟨0, le_refl 0, ?_⟩
  intro m i u _hu s _hs
  rw [secondXDeriv_pairing_integral_gatedK0_eqZero hn g gi hChr S a b i (u - s) s
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b))) 0]
  rw [abs_zero, zero_mul]

end QIQTH.HGpowGatedK0Closed

/-! ## Axiom check — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HGpowGatedK0Closed
#print axioms witnessSecondXDeriv_eqZero_of_base_notMem_K
#print axioms secondXDeriv_pairing_integral_gatedK0_eqZero
#print axioms hGpow_gatedK0_closed
end AxiomChecks
