/-
  KPrimeDiagPdBridge — the DIAGONAL (same-index `j = i`) analogue of J4-788's
  `KPrimeMixedPdBridge.kPrime_apply_single_eq_mixedPd`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  algebraic identification of the abstract CLM-derivative kernel `kPrime`'s **same-index** basis
  component `eᵢ = Pi.single i 1` with the concrete DIAGONAL second field partial `∂ᵢ∂ᵢ` of the gated
  van-Vleck witness, times the field-independent Levi factor.  It is the diagonal (`j = i`) twin of the
  MIXED (`i ≠ j`) first bridge link `KPrimeMixedPdBridge.kPrime_apply_single_eq_mixedPd` (J4-788), and
  is the concrete `kPrime`-level link the DIAGONAL leg of
  `KPrimeOpNormSliver.kPrime_opNorm_sliver_bound`'s `hcomp` slot (the `j = i` component) must be a
  sliver of — the counterpart to the mixed link for the off-diagonal `j ≠ i` components.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE IDENTITY.

  `kPrime … i t s x z = (leviSeries … s z 0) • fderiv ℝ (y ↦ witnessFieldDeriv … i (t−s) y z) x`
  and `witnessFieldDeriv … i τ y z = pd (x' ↦ H_G τ x' z) i y` (definitionally).  Applying the CLM to
  the SAME-index basis vector `eᵢ = Pi.single i 1` (the outer differentiation direction, NOT a distinct
  `j`) and using `Curvature.pd_eq_fderiv`:

    `(kPrime … i t s x z)(eᵢ)
        = leviSeries … s z 0 · pd (y ↦ pd (x' ↦ H_G (t−s) x' z) i y) i x`,

  i.e. the `i`-th (diagonal) component of `kPrime` is the Levi factor times the DIAGONAL second field
  partial `∂ᵢ∂ᵢ H_G` at the field point `x`.  On the gate this `∂ᵢ∂ᵢ` equals the DIAGONAL Leibniz–
  Gaussian three-term normal form (`sTerm0 + sTerm1 + sTerm2`) that the closed diagonal sliver rate
  `XUniformSliverFull.witness_sliver2_xuniform` estimates.

  ## RELATION TO J4-788.

  `KPrimeMixedPdBridge.kPrime_apply_single_eq_mixedPd` carries NO `i ≠ j` hypothesis — it is fully
  general in `(i, j)` — so the diagonal link below is, at the pure `kPrime`-CLM-link level, exactly its
  `j := i` instance.  This file states and proves it directly (via the same `Curvature.pd_eq_fderiv`
  route) as a self-contained, diagonally-labelled API object, making explicit that the diagonal leg of
  `kPrime_opNorm_sliver_bound`'s `hcomp` needs NO new `kPrime`-level link beyond the (index-agnostic)
  technique of J4-788: the "also-unbuilt diagonal kPrime link" flagged in the J4-787 report is the
  `j = i` restriction of the already-general mixed link.

  Every hypothesis is satisfiable and non-vacuous (the field-differentiability carry `hd` holds on the
  gate where the witness is the smooth chart-Gaussian; the identity is an equality, never a bound), and
  is not the conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FderivBulkConcrete

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete
open scoped Topology

namespace QIQTH.KPrimeDiagPdBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ `kPrime_apply_single_eq_diagPd`.**  THE diagonal (same-index) concrete `kPrime`→normal-form
    link: the `i`-th basis component of the abstract CLM derivative kernel `kPrime` equals the
    field-independent Levi factor times the concrete DIAGONAL second field partial `∂ᵢ∂ᵢ` of the gated
    van-Vleck witness at the field point `x`:
      `(kPrime … i t s x z)(Pi.single i 1)
          = leviSeries … s z 0 · pd (y ↦ pd (x' ↦ vanVleckGatedWitness … (t−s) x' z) i y) i x`.
    The `j := i` twin of `KPrimeMixedPdBridge.kPrime_apply_single_eq_mixedPd` (J4-788).  Route: unfold
    `kPrime`'s scalar-`smul`ed `fderiv`, apply `ContinuousLinearMap.smul_apply`, and rewrite
    `fderiv … (Pi.single i 1) = pd … i` via `Curvature.pd_eq_fderiv` (off the carried
    field-differentiability `hd` of the first field-derivative kernel `witnessFieldDeriv … i (t−s) · z`);
    the definitional identity `witnessFieldDeriv … i τ y z = pd (H_G τ · z) i y` closes the goal.
    NOT `a₁ = R/6`. -/
theorem kPrime_apply_single_eq_diagPd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t s : ℝ) (x z : Point n)
    (hd : DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x) :
    (kPrime g gi hC hK S a b i t s x z) (Pi.single i 1)
      = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
        * pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i y) i x := by
  simp only [kPrime, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← pd_eq_fderiv (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) i x hd]
  rfl

end QIQTH.KPrimeDiagPdBridge

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.KPrimeDiagPdBridge
#print axioms kPrime_apply_single_eq_diagPd
end AxiomChecks
