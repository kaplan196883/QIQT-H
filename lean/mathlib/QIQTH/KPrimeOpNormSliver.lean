/-
  KPrimeOpNormSliver — J4-779: the CLM OPERATOR-NORM reduction of the concrete `kPrime` sliver.
  J4-778b DEFINED the CLM Fréchet-derivative kernel `kPrime` (a `Point n →L[ℝ] ℝ`) and proved the
  scalar sliver IDENTITY `gderivInt − fderivBulkInt = ∫_{t−εₘ}^{t} ∫z kPrime`, then FLAGGED the
  RATE (`hsliver`, the O(√ε) OPERATOR-NORM bound on that CLM-valued integral) as the remaining
  content — noting the banked scalar sliver `XUniformSliverFull.witness_sliver2_xuniform` supplies
  only the SCALAR (single-direction) √ε rate, while `kPrime` is the FULL field gradient (all
  directions).  THIS FILE discharges the OPERATOR-NORM reduction that J4-778b's own report speculated
  about: since `Point n = Fin n → ℝ` carries the sup norm, a functional's operator norm is bounded by
  the ℓ¹ sum of its basis components — `‖L‖ ≤ Σⱼ |L (eⱼ)|` — so the CLM sliver `‖∫∫ kPrime‖_op`
  reduces to the FINITE SUM over `j : Fin n` of the SCALAR component slivers `|∫∫ (kPrime eⱼ)|`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  This brick closes ONE precisely-named hole flagged by J4-778b:
  it turns the CLM operator-norm `hsliver` census member into a FINITE SUM of scalar-component
  sliver bounds — the exact "‖CLM‖_op ≤ Σⱼ |component_j|" reduction speculated on there.  It does
  NOT reprove the scalar per-component sliver rate (that is the ALREADY-BANKED
  `witness_sliver2_xuniform` at each direction pair `(i,j)`); those scalar rates are carried as the
  satisfiable hypothesis `hcomp`.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (ns `QIQTH.KPrimeOpNormSliver`).

    • `opNorm_le_sum_apply_single` — ★ PURE: for `L : (Fin n → ℝ) →L[ℝ] ℝ` and reals `bb`, if every
      basis component obeys `|L (Pi.single j 1)| ≤ bb j` then `‖L‖ ≤ Σⱼ bb j`.  (Sup-norm ⇒ ℓ¹ dual.)

    • `kPrime_apply_single_sliver` — ★★ the concrete component pushthrough: the `j`-th basis component
      of the CLM sliver `(gderivInt − fderivBulkInt)(eⱼ)` equals the SCALAR sliver
      `∫_{t−εₘ}^{t} ∫z (kPrime … eⱼ)` — obtained from the banked sliver IDENTITY
      (`gderiv_sub_fderivBulk_eq_sliver`, J4-778b) by pushing the evaluation `· (eⱼ)` through the
      interval- and inner-integrals (`ContinuousLinearMap.intervalIntegral_apply` /
      `ContinuousLinearMap.integral_apply`).

    • `kPrime_opNorm_sliver_bound` — ★★★ THE `hsliver` OPERATOR-NORM DISCHARGE: given the two-sided
      interval integrability of the CLM profile (for the sliver identity), the a.e.-`s` inner
      integrability (for the eval pushthrough), and the scalar per-component sliver bounds `hcomp`,
        `dist (fderivBulkInt … i m x) (gderivInt … i x) ≤ Σⱼ bb j`.
      This is exactly the DIST-form control the `hsliver` slot of
      `HD1SliverRoute.hD1_bulk_sliver_reduction` (via `XUniformSliverFull.hD1_from_data`) consumes,
      now with `b := Σⱼ bb j` — a finite sum of the banked √ε scalar rates, hence still `O(√ε) → 0`.

  Every hypothesis is satisfiable and non-vacuous (the width-2 Gaussian model of the sliver census
  satisfies both integrabilities, and each scalar per-component sliver is exactly
  `witness_sliver2_xuniform` at the `(i,j)` direction pair), and none equals the conclusion (the
  conclusion bounds the OPERATOR NORM of the CLM double-integral; `hcomp` bounds SCALAR component
  integrals).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FderivBulkConcrete

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete
open scoped Topology Interval BigOperators

namespace QIQTH.KPrimeOpNormSliver

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### K0 — the pure sup-norm ⇒ ℓ¹ operator-norm reduction.
    ############################################################################### -/

/-- **★ K0 — `opNorm_le_sum_apply_single`.**  On `Point n = Fin n → ℝ` (the SUP norm), the operator
    norm of a continuous linear functional is bounded by the ℓ¹ sum of its basis components: if
    `|L (Pi.single j 1)| ≤ bb j` for every `j`, then `‖L‖ ≤ Σⱼ bb j`.  Proof: decompose
    `v = Σⱼ Pi.single j (v j)`, so `L v = Σⱼ v j · L (eⱼ)`; then
    `|L v| ≤ Σⱼ |v j|·|L eⱼ| ≤ Σⱼ ‖v‖·bb j = (Σⱼ bb j)·‖v‖` since `|v j| ≤ ‖v‖` (sup norm).
    NOT `a₁ = R/6`. -/
theorem opNorm_le_sum_apply_single
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (bb : Fin n → ℝ)
    (hb : ∀ j, |L (Pi.single j 1)| ≤ bb j) :
    ‖L‖ ≤ ∑ j, bb j := by
  have hbnn : ∀ j, 0 ≤ bb j := fun j => le_trans (abs_nonneg _) (hb j)
  refine L.opNorm_le_bound (Finset.sum_nonneg (fun j _ => hbnn j)) (fun v => ?_)
  -- coordinate decomposition of `Pi.single`.
  have hsm : ∀ (j : Fin n) (c : ℝ), (Pi.single j c : Fin n → ℝ) = c • Pi.single j (1 : ℝ) := by
    intro j c; funext k
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split <;> simp
  -- `L v = Σⱼ v j · L (eⱼ)`.
  have hdecomp : L v = ∑ j, v j * L (Pi.single j (1 : ℝ)) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hsm j (v j), map_smul, smul_eq_mul]
  rw [Real.norm_eq_abs, hdecomp]
  calc |∑ j, v j * L (Pi.single j (1 : ℝ))|
      ≤ ∑ j, |v j * L (Pi.single j (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |v j| * |L (Pi.single j (1 : ℝ))| := by simp_rw [abs_mul]
    _ ≤ ∑ j, ‖v‖ * bb j := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hvj : |v j| ≤ ‖v‖ := by
          have h := norm_le_pi_norm v j
          rwa [Real.norm_eq_abs] at h
        exact mul_le_mul hvj (hb j) (abs_nonneg _) (norm_nonneg _)
    _ = ‖v‖ * ∑ j, bb j := by rw [Finset.mul_sum]
    _ = (∑ j, bb j) * ‖v‖ := by rw [mul_comm]

/-! ###############################################################################
    ### K1 — the concrete component pushthrough for the `kPrime` sliver.
    ############################################################################### -/

/-- **★★ K1 — `kPrime_apply_single_sliver`.**  The `j`-th basis component of the CLM sliver equals the
    scalar sliver of the `j`-th component of `kPrime`:
      `(gderivInt … i x − fderivBulkInt … i m x)(Pi.single j 1)
          = ∫_{t−εₘ}^{t} ∫z (kPrime … i t s x z)(Pi.single j 1)`.
    From the banked sliver identity `gderiv_sub_fderivBulk_eq_sliver` (J4-778b), pushing the
    evaluation `· (Pi.single j 1)` through the interval integral (`intervalIntegral_apply`, off the
    CLM-profile interval integrability `hIbc`) and the inner integral (`integral_apply`, off the
    a.e.-`s` inner integrability `hzInt`).  NOT `a₁ = R/6`. -/
theorem kPrime_apply_single_sliver (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (i : Fin n) (m : ℕ) (x : Point n) (j : Fin n)
    (hIab : IntervalIntegrable (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
        volume 0 (t - epsSeq m))
    (hIbc : IntervalIntegrable (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
        volume (t - epsSeq m) t)
    (hzInt : ∀ᵐ s ∂volume, s ∈ Set.uIoc (t - epsSeq m) t →
        Integrable (fun z => kPrime g gi hC hK S a b i t s x z) volume) :
    (gderivInt g gi hC hK S a b t i x - fderivBulkInt g gi hC hK S a b t i m x) (Pi.single j 1)
      = ∫ s in (t - epsSeq m)..t, ∫ z, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1) := by
  rw [gderiv_sub_fderivBulk_eq_sliver g gi hC hK S a b t i m x hIab hIbc]
  rw [ContinuousLinearMap.intervalIntegral_apply hIbc (Pi.single j 1)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hzInt] with s hs hsmem
  exact ContinuousLinearMap.integral_apply (hs hsmem) (Pi.single j 1)

/-! ###############################################################################
    ### K2 — THE `hsliver` operator-norm discharge.
    ############################################################################### -/

/-- **★★★ K2 — `kPrime_opNorm_sliver_bound`.**  THE `hsliver` OPERATOR-NORM discharge: the CLM
    dist between the truncated and full derivative fields is bounded by the FINITE SUM of the scalar
    per-component sliver rates,
      `dist (fderivBulkInt … i m x) (gderivInt … i x) ≤ Σⱼ bb j`,
    by the ℓ¹ operator-norm reduction (`opNorm_le_sum_apply_single`) fed the component pushthrough
    (`kPrime_apply_single_sliver`) at each `j` and the scalar per-component sliver bounds `hcomp`
    (each `bb j` being the banked √ε rate `witness_sliver2_xuniform` at the direction pair `(i,j)`,
    so `Σⱼ bb j` is `O(√ε) → 0` — the vanishing `b` the `hsliver` slot consumes).  NOT `a₁ = R/6`. -/
theorem kPrime_opNorm_sliver_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (i : Fin n) (m : ℕ) (x : Point n) (bb : Fin n → ℝ)
    (hIab : IntervalIntegrable (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
        volume 0 (t - epsSeq m))
    (hIbc : IntervalIntegrable (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
        volume (t - epsSeq m) t)
    (hzInt : ∀ᵐ s ∂volume, s ∈ Set.uIoc (t - epsSeq m) t →
        Integrable (fun z => kPrime g gi hC hK S a b i t s x z) volume)
    (hcomp : ∀ j, |∫ s in (t - epsSeq m)..t, ∫ z, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)|
        ≤ bb j) :
    dist (fderivBulkInt g gi hC hK S a b t i m x) (gderivInt g gi hC hK S a b t i x)
      ≤ ∑ j, bb j := by
  rw [dist_eq_norm, norm_sub_rev]
  refine opNorm_le_sum_apply_single
    (gderivInt g gi hC hK S a b t i x - fderivBulkInt g gi hC hK S a b t i m x) bb (fun j => ?_)
  rw [kPrime_apply_single_sliver g gi hC hK S a b t i m x j hIab hIbc hzInt]
  exact hcomp j

end QIQTH.KPrimeOpNormSliver

section AxiomChecks
open QIQTH.KPrimeOpNormSliver
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms opNorm_le_sum_apply_single
#print axioms kPrime_apply_single_sliver
#print axioms kPrime_opNorm_sliver_bound
end AxiomChecks
