/-
  KPrimeMixedPdBridge — J4-788: the CONCRETE first link of the `kPrime`→normal-form bridge.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  algebraic identification of the abstract CLM-derivative kernel `kPrime`'s `j`-th basis component with
  the concrete MIXED second field partial `∂ⱼ∂ᵢ` of the van-Vleck witness, times the field-independent
  Levi factor.  This is the "connect abstract `kPrime … eⱼ` to the concrete `pd∘pd` normal form" step
  (J4-782 step 3, first link), the object `KPrimeOpNormSliver.kPrime_opNorm_sliver_bound`'s `hcomp`
  slot must be a sliver of.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE IDENTITY.

  `kPrime … i t s x z = (leviSeries … s z 0) • fderiv ℝ (y ↦ witnessFieldDeriv … i (t−s) y z) x`
  and `witnessFieldDeriv … i (t−s) y z = pd (x' ↦ H_G (t−s) x' z) i y` (definitionally).  Applying the
  CLM to the basis vector `eⱼ = Pi.single j 1` and using `Curvature.pd_eq_fderiv` (the partial derivative
  = `fderiv` on `eⱼ`, given field-differentiability of the first field-derivative kernel):

    `(kPrime … i t s x z)(eⱼ)
        = leviSeries … s z 0 · pd (y ↦ pd (x' ↦ H_G (t−s) x' z) i y) j x`,

  i.e. the `j`-th component of `kPrime` is the Levi factor times the MIXED second field partial
  `∂ⱼ∂ᵢ H_G` at the field point `x`.  On the gate this `∂ⱼ∂ᵢ` equals the mixed Leibniz–Gaussian normal
  form (`ChartJetHessianMixed.witnessMixed_gate_eq`, `i`/`j` swapped) that the closed mixed sliver rate
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed` (J4-787) estimates.

  Every hypothesis is satisfiable and non-vacuous (the field-differentiability carry `hd` holds on the
  gate where the witness is the smooth chart-Gaussian; the identity is an equality, never a bound), and
  is not the conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FderivBulkConcrete
import QIQTH.ChartJetHessianMixed

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete
open scoped Topology

namespace QIQTH.KPrimeMixedPdBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ J4-788 — `kPrime_apply_single_eq_mixedPd`.**  THE concrete first link of the bridge: the
    `j`-th basis component of the abstract CLM derivative kernel `kPrime` equals the field-independent
    Levi factor times the concrete MIXED second field partial `∂ⱼ∂ᵢ` of the gated van-Vleck witness at
    the field point `x`:
      `(kPrime … i t s x z)(Pi.single j 1)
          = leviSeries … s z 0 · pd (y ↦ pd (x' ↦ vanVleckGatedWitness … (t−s) x' z) i y) j x`.
    Route: unfold `kPrime`'s scalar-`smul`ed `fderiv`, apply `ContinuousLinearMap.smul_apply`, and
    rewrite `fderiv … (Pi.single j 1) = pd … j` via `Curvature.pd_eq_fderiv` (off the carried
    field-differentiability `hd` of the first field-derivative kernel `witnessFieldDeriv … i (t−s) · z`);
    the definitional identity `witnessFieldDeriv … i τ y z = pd (H_G τ · z) i y` closes the goal.
    NOT `a₁ = R/6`. -/
theorem kPrime_apply_single_eq_mixedPd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (t s : ℝ) (x z : Point n)
    (hd : DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x) :
    (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)
      = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
        * pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i y) j x := by
  simp only [kPrime, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← pd_eq_fderiv (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) j x hd]
  rfl

end QIQTH.KPrimeMixedPdBridge

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.KPrimeMixedPdBridge
#print axioms kPrime_apply_single_eq_mixedPd
end AxiomChecks
