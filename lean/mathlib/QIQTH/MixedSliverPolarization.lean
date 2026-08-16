/-
  MixedSliverPolarization — the POLARIZATION of the mixed-index (`∂ᵢ∂ⱼ`, `i ≠ j`) Leibniz–Gaussian
  normal form into a finite linear combination of the DIAGONAL-SHAPE sliver terms `sTerm0`/`sTerm1`/
  `sTerm2` (`SliverAssembly`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT (why this exists).

  The concrete second-`x`-derivative sliver census that feeds `hCConv` (`ContDiffAt ℝ 2` of the
  diagonal Duhamel convolution) is, after the J4-779 CLM operator-norm reduction
  (`KPrimeOpNormSliver.kPrime_opNorm_sliver_bound`), a FINITE SUM over `j : Fin n` of scalar component
  slivers `|∫∫ (kPrime … i)(eⱼ)|`.  The `j = i` (DIAGONAL) component is exactly the banked scalar
  sliver `XUniformSliverFull.witness_sliver2_xuniform`, whose `hNormalForm` slot consumes the
  DIAGONAL-shape decomposition `D2H = sTerm0 Y P Q A0 + sTerm1 Y P A1 + sTerm2 Y A2` — a `(∑ Y·P)²`
  Hermite SQUARE plus a single doubled gradient term.

  For the OFF-DIAGONAL (`j ≠ i`) components the concrete kernel is the MIXED second field partial
  `∂ⱼ (witnessFieldDeriv … i)`, whose exact on-gate normal form is the ALREADY-BANKED (J4-218)
  `ChartJetHessianMixed.witnessMixed_gate_eq` / `gaussComp_amp_pd_pd_mixed`:
      `∂ᵢ∂ⱼ(G·A) = G·[⟨V,Pi⟩·⟨V,Pj⟩/(4τ²) − (⟨Pi,Pj⟩+⟨V,Q⟩)/(2τ)]·A
                   + G·(−⟨V,Pj⟩/(2τ))·∂ᵢA + G·(−⟨V,Pi⟩/(2τ))·∂ⱼA + G·∂ᵢ∂ⱼA`.
  Its Hessian coefficient is a PRODUCT `⟨V,Pi⟩·⟨V,Pj⟩` (NOT a square), and it has TWO distinct
  gradient terms — so it does NOT match the diagonal `sTerm0`/`sTerm1` shape verbatim.

  THIS FILE closes the algebraic half of that mismatch: by the classical POLARIZATION identity
  `a·b = ¼[(a+b)² − (a−b)²]`, the mixed Hessian PRODUCT is a difference of two Hermite SQUARES at the
  summed/differenced jet directions `Pi±Pj`, and the second-moment `⟨Pi,Pj⟩` and center-jet `⟨V,Q⟩`
  contributions polarize consistently (choose the second-jet data `±2·Q`).  Hence the mixed normal
  form equals EXACTLY
      `¼·sTerm0(V, Pi+Pj, 2Q, A) − ¼·sTerm0(V, Pi−Pj, −2Q, A)
        + ½·sTerm1(V, Pj, ∂ᵢA) + ½·sTerm1(V, Pi, ∂ⱼA) + sTerm2(V, ∂ᵢ∂ⱼA)`
  — a finite linear combination of the DIAGONAL sliver terms.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ALGEBRAIC identity (a polarization + `ring`) bridging the mixed-index normal form to the
  diagonal sliver terms.  It does NOT by itself supply the off-diagonal `hcomp` sliver BOUND: the
  polarized directions `Pi±Pj` are NOT coordinate-aligned (`‖(Pi±Pj) − eₖ‖ = O(1)`, not `O(‖z‖)`), so
  `witness_sliver2_xuniform`'s coordinate-tied `hJ3` / `(zᵢ)²`-Hermite estimates do NOT transfer
  verbatim to the polarized pieces — the mixed-direction √ε sliver estimate remains genuinely open
  analytic content (the off-diagonal `⟨V,Pi⟩⟨V,Pj⟩ ≈ zᵢzⱼ` leading term integrates to `0` by parity, a
  cleaner cancellation than the diagonal Hermite subtraction, but formalized nowhere yet).  This brick
  is the exact ALGEBRAIC reduction, precisely isolating that remaining estimate.  No `sorry`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited.  `a₁ = R/6` remains CONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (ns `QIQTH.MixedSliverPolarization`).

    • `gaussComp_amp_pd_pd_mixed_polarized` — ★★ the mixed second coordinate partial
      `∂ᵢ∂ⱼ(gaussDdim τ (V ·)·A)` at `x₀` equals the polarization combination of `sTerm0`/`sTerm1`/
      `sTerm2` displayed above.  Proved by rewriting through the banked
      `ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed` and a finite-sum polarization `ring`.
-/
import Mathlib
import QIQTH.ChartJetHessianMixed
import QIQTH.SliverAssembly

open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.ChartJetHessianMixed
open scoped BigOperators

namespace QIQTH.MixedSliverPolarization

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ `gaussComp_amp_pd_pd_mixed_polarized`.**  The mixed-index (`∂ᵢ∂ⱼ`) Leibniz–Gaussian normal
    form of `gaussDdim τ (V ·)·A` polarized into the DIAGONAL sliver terms:
      `∂ᵢ∂ⱼ(G·A) x₀
        = ¼·sTerm0(V, Pi+Pj, 2Q, A) − ¼·sTerm0(V, Pi−Pj, −2Q, A)
          + ½·sTerm1(V, Pj, ∂ᵢA) + ½·sTerm1(V, Pi, ∂ⱼA) + sTerm2(V, ∂ᵢ∂ⱼA)`,
    with `G := gaussDdim τ (V ·)`.  The Hessian PRODUCT `⟨V,Pi⟩·⟨V,Pj⟩` becomes a difference of Hermite
    SQUARES at the polarized jet directions `Pi±Pj`; the two distinct gradient terms become the two
    `sTerm1` pieces; the mass term is `sTerm2`.  Same hypotheses as the banked
    `ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed`.  Pure algebra (polarization + `ring`); NOT
    `a₁ = R/6`. -/
theorem gaussComp_amp_pd_pd_mixed_polarized (V : Point n → Point n) (A : Point n → ℝ)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) (x₀ : Point n)
    (hVi : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (Pi x k) (x i))
    (hVj : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x j s) k) (Pj x k) (x j))
    (hQ : ∀ k, HasDerivAt (fun s : ℝ => Pj (Function.update x₀ i s) k) (Q k) (x₀ i))
    (hAj1 : ∀ x, PdiffAt A j x)
    (hAi1 : PdiffAt A i x₀)
    (hA2 : PdiffAt (fun y => pd A j y) i x₀) :
    pd (fun y => pd (fun z => gaussDdim τ (V z) * A z) j y) i x₀
      = (1 / 4 : ℝ) * sTerm0 V (fun z => Pi z + Pj z) (fun _ => (2 : ℝ) • Q) (fun _ y => A y) τ x₀
        - (1 / 4 : ℝ) * sTerm0 V (fun z => Pi z - Pj z) (fun _ => (-2 : ℝ) • Q) (fun _ y => A y) τ x₀
        + (1 / 2 : ℝ) * sTerm1 V Pj (fun _ y => pd A i y) τ x₀
        + (1 / 2 : ℝ) * sTerm1 V Pi (fun _ y => pd A j y) τ x₀
        + sTerm2 V (fun _ y => pd (fun w => pd A j w) i y) τ x₀ := by
  rw [gaussComp_amp_pd_pd_mixed V A Pi Pj Q τ hτ i j x₀ hVi hVj hQ hAj1 hAi1 hA2]
  simp only [sTerm0, sTerm1, sTerm2]
  -- Finite-sum polarization of the four combined sums that appear on the RHS.
  have hVplus : (∑ k, V x₀ k * (Pi x₀ + Pj x₀) k)
      = (∑ k, V x₀ k * Pi x₀ k) + ∑ k, V x₀ k * Pj x₀ k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [_root_.Pi.add_apply]; ring)
  have hVminus : (∑ k, V x₀ k * (Pi x₀ - Pj x₀) k)
      = (∑ k, V x₀ k * Pi x₀ k) - ∑ k, V x₀ k * Pj x₀ k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [_root_.Pi.sub_apply]; ring)
  have hPPplus : (∑ k, (Pi x₀ + Pj x₀) k * (Pi x₀ + Pj x₀) k)
      = (∑ k, Pi x₀ k * Pi x₀ k) + 2 * (∑ k, Pi x₀ k * Pj x₀ k)
        + ∑ k, Pj x₀ k * Pj x₀ k := by
    have h1 : (∑ k, (Pi x₀ + Pj x₀) k * (Pi x₀ + Pj x₀) k)
        = ∑ k, (Pi x₀ k * Pi x₀ k + 2 * (Pi x₀ k * Pj x₀ k) + Pj x₀ k * Pj x₀ k) :=
      Finset.sum_congr rfl (fun k _ => by rw [_root_.Pi.add_apply]; ring)
    rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hPPminus : (∑ k, (Pi x₀ - Pj x₀) k * (Pi x₀ - Pj x₀) k)
      = (∑ k, Pi x₀ k * Pi x₀ k) - 2 * (∑ k, Pi x₀ k * Pj x₀ k)
        + ∑ k, Pj x₀ k * Pj x₀ k := by
    have h1 : (∑ k, (Pi x₀ - Pj x₀) k * (Pi x₀ - Pj x₀) k)
        = ∑ k, (Pi x₀ k * Pi x₀ k - 2 * (Pi x₀ k * Pj x₀ k) + Pj x₀ k * Pj x₀ k) :=
      Finset.sum_congr rfl (fun k _ => by rw [_root_.Pi.sub_apply]; ring)
    rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hVQplus : (∑ k, V x₀ k * ((2 : ℝ) • Q) k) = 2 * ∑ k, V x₀ k * Q k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [_root_.Pi.smul_apply, smul_eq_mul]; ring)
  have hVQminus : (∑ k, V x₀ k * ((-2 : ℝ) • Q) k) = -2 * ∑ k, V x₀ k * Q k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [_root_.Pi.smul_apply, smul_eq_mul]; ring)
  rw [hVplus, hVminus, hPPplus, hPPminus, hVQplus, hVQminus]
  ring

end QIQTH.MixedSliverPolarization

section AxiomChecks
open QIQTH.MixedSliverPolarization
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms gaussComp_amp_pd_pd_mixed_polarized
end AxiomChecks
