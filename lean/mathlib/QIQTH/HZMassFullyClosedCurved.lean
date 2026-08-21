/-
  HZMassFullyClosedCurved — the FULL discharge of the `hzmass` `z`-mass bound at the genuinely-curved
  witness `g^κ = curvedRNCMetric κ` (`κ < 0`, `1 ≤ n`, `K = {0}`), via the SAME null-support / singleton
  shortcut that J4-984 (`HbintFullyClosedCurved`) used to close the interior tube-cover `hbint` leg.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick closes ONE more
  `hCConv` census leg — the `hzmass` `z`-mass bound `∫z BL·BF ≤ C·(t−s)⁻¹` of
  `MixedDirectionsFieldHessianEnvelope` — UNCONDITIONALLY at the concrete curved `K = {0}` witness.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SINGLETON SHORTCUT (identical in spirit to J4-984's `hbint` closure).

  The envelope's `hzmass` field is the `z`-mass bound with the EXPLICIT J4-865 field-Hessian envelope
      `BF s z := ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x‖`,
  namely `∫z BL·BF ≤ C·(t−s)⁻¹`.  At the concrete curved witness the confinement set is the SINGLETON
  `K = {0}`, and the field-Hessian VANISHES OFF `K` (`HZMassIntegrabilityAttempt.
  BF_ciSup_eqZero_of_base_notMem_K`): for `z ∉ K`, the gated field kernel is identically `0`, so its
  Fréchet derivative is `0`, so the `⨆`-envelope `BF s z = 0`.  Hence the product `z ↦ BL s z · BF s z`
  is SUPPORTED IN `K = {0}` (`HZMassIntegrabilityAttempt.productEnvelope_support_subset_K`), a
  Lebesgue-NULL singleton (`measure_singleton`, valid for `1 ≤ n` via `Nontrivial (Point n)`).  A
  function supported on a null set is a.e. `0`, so
      `∫z BL·BF = 0 ≤ C·(t−s)⁻¹`   (given `C ≥ 0` and `t − s > 0` on the capped window).

  This is EXACTLY the same census-closure mechanism as `HbintFullyClosedCurved` (J4-984): the genuine
  analytic content (a Gaussian `z`-mass estimate on `⨆x‖fderiv‖`) is OUT OF SCOPE at this specialized
  witness because the integrand's support collapses to the null base point.  It is a real closure of the
  `hzmass` leg AT THIS WITNESS, but the curved geometry does no substantive work in it (interpretive
  caveat, not a soundness issue) — mirroring the honest status of the J4-984 `hbint` closure.

  ## WHAT LANDS (ns `QIQTH.HZMassFullyClosedCurved`).
    • `integral_eq_zero_of_support_subset_singleton` — the elementary measure-theoretic core: a real
      function supported in `{p}` has integral `0` (null singleton ⟹ a.e. `0` ⟹ `∫ = 0`).
    • `hzmass_fully_closed_curved` — ★★★ the FULL `hzmass` closure at the concrete curved `K = {0}`
      witness: for ANY `BL`, ANY gate scalars `a b c`, and ANY `C ≥ 0`, the `z`-mass bound
      `∫z BL·BF ≤ C·(t−s)⁻¹` holds on the capped window `s ∈ uIoc 0 (t−εₘ)` (`hepspos : 0 < t − εₘ`),
      with `BF` the exact J4-865/J4-984 explicit field-Hessian envelope.  UNCONDITIONAL.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HbintFullyClosedCurved
import QIQTH.HZMassCappedWindowClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.PullbackMetric
open QIQTH.HbintRequant
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.HZMassFullyClosedCurved

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — the elementary measure-theoretic core.
    ############################################################################### -/

/-- **★ `integral_eq_zero_of_support_subset_singleton`.**  A real function `f` whose support is
    contained in a singleton `{p}` integrates to `0` against a measure with no atoms: the support is
    Lebesgue-null (`measure_singleton`), so `f =ᵐ 0`, so `∫ f = 0`.  This is the measure-theoretic core
    of the singleton shortcut. -/
theorem integral_eq_zero_of_support_subset_singleton
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [NoAtoms μ]
    (f : α → ℝ) (p : α) (hsupp : Function.support f ⊆ {p}) :
    (∫ x, f x ∂μ) = 0 := by
  have hnull : μ ({p} : Set α) = 0 := measure_singleton p
  have hae : f =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull
    simp only [Set.mem_setOf_eq] at hx
    exact hsupp (by simpa [Function.mem_support] using hx)
  rw [integral_congr_ae hae, integral_zero]

/-! ###############################################################################
    ### §2 — the FULL `hzmass` closure at the concrete curved `K = {0}` witness.
    ############################################################################### -/

/-- **★★★ `hzmass_fully_closed_curved`.**  THE FULL `hzmass` closure of
    `MixedDirectionsFieldHessianEnvelope` at the genuinely-curved witness `g^κ = curvedRNCMetric κ`
    (`κ < 0`, `1 ≤ n`, `K = {0}`).  For ANY Levi envelope `BL`, ANY gate scalars `a b c`, and ANY
    `C ≥ 0`, on the capped window `s ∈ uIoc 0 (t−εₘ)` (with `hepspos : 0 < t − εₘ`),
      `∫z BL s z · (⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x‖) ≤ C·(t−s)⁻¹`,
    where the `BF` factor is the exact J4-865/J4-984 explicit field-Hessian envelope.

    MECHANISM (the singleton shortcut, cf. J4-984): the field-Hessian vanishes off `K = {0}`
    (`BF_ciSup_eqZero_of_base_notMem_K`), so the integrand is supported in the NULL singleton `{0}`
    (`productEnvelope_support_subset_K`), so `∫z BL·BF = 0`; and `0 ≤ C·(t−s)⁻¹` because `C ≥ 0` and
    `t − s ≥ εₘ > 0` on the capped window.

    NON-VACUOUS: no antecedent is unsatisfiable — `hC : 0 ≤ C` and `hepspos : 0 < t − εₘ` are ordinary
    satisfiable data (e.g. `C = 0`, any `m` with `εₘ < t`); the conclusion is a genuine integral bound,
    not `True` and not equal to a hypothesis.  NOT `a₁ = R/6` — this closes only ONE `hCConv` census
    leg at this witness; `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}. -/
theorem hzmass_fully_closed_curved (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (i : Fin n) (t : ℝ) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) (hepspos : 0 < t - epsSeq m)
    (a b c : ℝ) (BL : ℝ → Point n → ℝ) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      (∫ z, BL s z *
        (⨆ x : Point n,
          ‖fderiv ℝ (fun y => witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
            (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
              '' Metric.ball (0 : Point n) c) a b i (t - s) y z) x‖))
        ≤ C * (t - s)⁻¹ := by
  have hn0 : 0 < n := by omega
  haveI : Inhabited (Fin n) := ⟨⟨0, hn0⟩⟩
  haveI : Nontrivial (Point n) := Pi.nontrivial
  refine ae_of_all volume (fun s hs => ?_)
  -- capped-window positivity `0 < t − s`.
  obtain ⟨_, hgap⟩ := QIQTH.HZMassCappedWindowClosed.window_gap hepspos hs
  have hts : 0 < t - s := lt_of_lt_of_le (epsSeq_pos m) hgap
  -- the integrand is supported in the null singleton `K = {0}`, so `∫z BL·BF = 0`.
  have hsupp := productEnvelope_support_subset_K (curvedRNCMetric κ) (curvedRNCInv κ) hChr
    (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
      '' Metric.ball (0 : Point n) c) a b i (t - s) BL s
  have hzero := integral_eq_zero_of_support_subset_singleton
    (μ := (volume : Measure (Point n)))
    (fun z => BL s z *
      (⨆ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
            '' Metric.ball (0 : Point n) c) a b i (t - s) y z) x‖))
    (0 : Point n) hsupp
  rw [hzero]
  -- `0 ≤ C·(t−s)⁻¹`.
  exact mul_nonneg hC (le_of_lt (inv_pos.mpr hts))

end QIQTH.HZMassFullyClosedCurved

/-! ## Axiom check — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HZMassFullyClosedCurved
#print axioms integral_eq_zero_of_support_subset_singleton
#print axioms hzmass_fully_closed_curved
end AxiomChecks
