/-
  WideA1Assembly — J4-258 (wide-route brick 11): the RECON + the width-parametric capstone mirror
  that WIDTH-AGNOSTICIZES the `a₁ = R/6` residual capstone, so the parallel WIDE domination bank
  (`GaussianWidthTransfer` … `FixedGateSourceProviders`, bricks 1-10) threads through at its native
  width `lam·τ` instead of the hardcoded width-2 Gaussian.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the `a₁ = R/6` heat-kernel campaign: it relocates the width constant `κ` of the residual-Neumann
  domination from a hardcoded `2` to a FREE parameter, showing the leading-term / DeWitt-cancellation
  conclusion is width-agnostic.  The genuine analytic content (the Gaussian domination of the residual,
  the sliver `C²`, the off-diagonal Jacobi cancellation) is UNCHANGED and still carried honestly.

  ── THE RECON (answers to the mission's three questions, from the CODE, not the ledger):

  (1) WHERE the exact-width amplitude forms enter the conclusion chain.  Tracing
      `CConvConcreteThreading.a1_R6_of_residue_inf_v5`
        → `OmegaHsrcC4cAudit.a1_R6_of_residue_inf`
        → `OmegaHsrcC4cAudit.trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty`:
      the exact-width boundary parametrix forms (`hAnear`/`hu₀`/`hu₁`/`hAdom`/`hD2Hexpand`/
      `AmplitudeDerivativeData`) appear NOWHERE in these three theorems' binders or proofs (grep-verified:
      zero hits in `OmegaHsrcC4cAudit.lean`).  The capstone proof splits cleanly:
        • LEADING TERM `(heatKernel1D t 0)^n · (1 + Ric/6·t + …)` = the EXACT parametrix identity
          `heatParametrixFn_diagonal_a1_derived_infty` (`hParam`) ∘ the exact heat-equation
          `trueHeatKernel_heat_eqn_levi_C2` (`hHeat`).  Both are WIDTH-INDEPENDENT — they consume the
          transport ODE / DeWitt cancellation, never a Gaussian width.
        • ERROR / DOMINATION LAYER = the residual-Neumann summability `hIterSum`, produced by
          `neumann_summable_alpha0_width2_le` — the ONLY width-2-specific call in the whole proof — plus
          the `C²` sliver slot `hCConv`.  This is EXACTLY where the (exact- or wide-) amplitude bank
          lands: it feeds `hEboundW_le` / `hInt` / `hCConv`, never the leading term.
      ⟹ Sol #4 is CONFIRMED at the code level: swapping the exact-width error inputs for the wide
      analogues changes only the domination CONSTANT / WIDTH; the capstone conclusion is UNCHANGED.

  (2) The width-2 is HARDCODED in the top capstone (binder types `baseKernelW 2 0`,
      `IterConvIntegrableW E 2 0 C`; proof call `neumann_summable_alpha0_width2_le`), but the underlying
      summability ENGINE `HeatResidualBound.leviSeries_summableW_le (κ α C T)` is WIDTH-PARAMETRIC
      (`∀κ>0, ∀α≥0`).  So the width-2 wrapper is a convenience, not a load-bearing choice.

  (3) THE ASSEMBLY SHAPE = width-parametric engine under a width-hardcoded capstone.  The wide route is
      therefore the MECHANICAL swap `neumann_summable_alpha0_width2_le → leviSeries_summableW_le @ κ`,
      with the two width-typed binders retyped to `baseKernelW κ 0` / `IterConvIntegrableW E κ 0 C`.
      That is precisely what the three theorems below do.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; each std-3):
    • `wide_trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty` — the width-`κ` mirror of
      `OmegaHsrcC4cAudit.trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty`; identical proof,
      the single width-2 summability line swapped for the width-parametric engine at a FREE `κ > 0`.
    • `wide_a1_R6_of_residue_inf` — the width-`κ` mirror of `OmegaHsrcC4cAudit.a1_R6_of_residue_inf`.
    • `wide_a1_R6_of_residue_inf_v5` — the width-`κ` mirror of
      `CConvConcreteThreading.a1_R6_of_residue_inf_v5` (the `hCConv` `C²` slot still threaded from the
      facade bundles + carried `hD1`).  The wide bank's `gaussDdim (lam·τ)` dominations feed this at
      `κ := lam`.

  Every carried hypothesis is satisfiable, non-vacuous, never equal to the conclusion; the width `κ` is
  a genuine free parameter (`hκ : 0 < κ`, never instantiated to a false value).  NO conclusion-in-
  disguise.  NO vacuous / unsatisfiable hyps.  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OmegaHsrcC4cAudit
import QIQTH.CConvConcreteThreading

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.OmegaHsrcC4cAudit QIQTH.CConvFacade QIQTH.GateOpennessExport
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.WideA1Assembly

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ###############################################################################
    ### 1. THE WIDTH-`κ` RESIDUAL CAPSTONE — width-2 → free `κ`.
    ############################################################################### -/

/-- **★★★ `wide_trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty`.**  The width-`κ` mirror of
    `OmegaHsrcC4cAudit.trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty`.  The Gaussian
    domination and per-step integrability are stated at a FREE width `κ > 0` (`baseKernelW κ 0`,
    `IterConvIntegrableW E κ 0 C`) instead of the hardcoded `2`.  The proof is byte-for-byte the
    original EXCEPT the single width-2 summability call `neumann_summable_alpha0_width2_le` is swapped
    for the width-parametric engine `HeatResidualBound.leviSeries_summableW_le` at `κ` (whose `κ`/`α`
    are free with `0 < κ`, `0 ≤ α`).  Every other step (the parametrix leading term, the DeWitt
    cancellation, the heat equation) is width-independent, so the conclusion is IDENTICAL.  NOT `a₁ =
    R/6`. -/
theorem wide_trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    (H : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (κ : ℝ) (hκ : 0 < κ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hHdiag : H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi H τ p q| ≤ C * baseKernelW κ (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi H) κ 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
        = leviSeries (heatOp g gi H) t 0 0
          + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)
    (hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi H)
            (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0)
    (hDH : DifferentiableAt ℝ (fun u => H u 0 0) t)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t)
    (hCH : ContDiffAt ℝ 2 (fun p => H t p 0) (0 : Point n))
    (hCConv : ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (0 : Point n)) :
    heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  have hpref : (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n ≠ 0 :=
    pow_ne_zero n (ne_of_gt (QIQTH.GaussianConvolution.heatKernel1D_pos t 0 ht))
  have ht2 : (t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
  -- ★ THE ONLY WIDTH-SPECIFIC LINE: the width-parametric engine at free `κ`, replacing
  --   `neumann_summable_alpha0_width2_le`.
  have hIterSum := leviSeries_summableW_le (heatOp g gi H) κ (0 : ℝ) C t hκ le_rfl hC
    hEboundW_le hInt t ht le_rfl (0 : Point n) (0 : Point n)
  have hSum : Summable
      (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) t (0 : Point n) (0 : Point n)) := by
    have habs : Summable
        (fun k : ℕ => |iterE (heatOp g gi H) (k + 1) t (0 : Point n) (0 : Point n)|) :=
      summable_abs_iff.mpr hIterSum
    refine Summable.of_norm_bounded habs (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    simp
  have hHeat : heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0 :=
    trueHeatKernel_heat_eqn_levi_C2 g gi H (heatOp g gi H) t 0 0 rfl hDuhamel hSum hInter
      hDH hDConv hCH hCConv
  have hParam := heatParametrixFn_diagonal_a1_derived_infty N g gi Ric t hN hg hg0 hgi hΓ hdg0 htr hsrc
  have htail_eq : (∑ k ∈ Finset.Ico 2 (N + 1),
        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ k)
      = t ^ 2 * ∑ k ∈ Finset.Ico 2 (N + 1),
        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ (k - 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hpow : t ^ 2 * t ^ (k - 2) = t ^ k := by
      rw [← pow_add]; congr 1; omega
    rw [← hpow]; ring
  have hExp : trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
      = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
        * (1 + ((∑ i, Ric i i) / 6) * t
            + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                          * t ^ (k - 2))
                      + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                          / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
    rw [trueHeatKernel_apply, hHdiag, hParam, htail_eq]
    field_simp
    ring
  exact ⟨hHeat, hExp⟩

/-! ###############################################################################
    ### 2. THE WIDTH-`κ` `a1_R6_of_residue_inf` MIRROR.
    ############################################################################### -/

/-- **★★★ `wide_a1_R6_of_residue_inf`.**  The width-`κ` mirror of
    `OmegaHsrcC4cAudit.a1_R6_of_residue_inf`: the `∞`-capstone at the concrete gated van-Vleck witness
    with the residual Gaussian domination / integrability stated at a FREE width `κ > 0`.  Internally it
    threads through the width-`κ` capstone above; the `hHdiag`/`hDH` gate facts and the leading term are
    width-independent.  NOT `a₁ = R/6`. -/
theorem wide_a1_R6_of_residue_inf (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (κ : ℝ) (hκ : 0 < κ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (H : ℝ → Point n → Point n → ℝ)
    (hHeq : H = vanVleckGatedWitness g gi hChr hK S a b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi H τ p q| ≤ C * baseKernelW κ (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi H) κ 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
        = leviSeries (heatOp g gi H) t 0 0
          + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)
    (hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi H)
            (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t)
    (hCH : ContDiffAt ℝ 2 (fun p => H t p 0) (0 : Point n))
    (hCConv : ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (0 : Point n)) :
    heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  subst hHeq
  have hHdiag : vanVleckGatedWitness g gi hChr hK S a b t 0 0
      = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t (0 : Point n) :=
    capstone_hHdiag_supplied g gi hChr hK S a b ha hab t hK0 hS0
  have hDH : DifferentiableAt ℝ (fun u => vanVleckGatedWitness g gi hChr hK S a b u 0 0) t :=
    capstone_hDH_supplied g gi hChr hK S a b ha hab t ht hK0 hS0
  exact wide_trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty g gi Ric 1 le_rfl t ht
    (vanVleckGatedWitness g gi hChr hK S a b) C hCnn κ hκ hg hg0 hgi hΓ hdg0 htr hsrc
    hHdiag hEboundW_le hInt hDuhamel hInter hDH hDConv hCH hCConv

/-! ###############################################################################
    ### 3. THE WIDTH-`κ` v5 CAPSTONE — `hCConv` threaded, width free.
    ############################################################################### -/

/-- **★★★ `wide_a1_R6_of_residue_inf_v5`.**  The width-`κ` mirror of
    `CConvConcreteThreading.a1_R6_of_residue_inf_v5`: the `∞`-capstone with the spatial-`C²` `hCConv`
    slot DISCHARGED from the five facade `: Prop` bundles + explicit `D` + carried `hD1`
    (`CConvConcreteThreading.hCConv_concrete_from_data`), and the residual Gaussian domination /
    integrability stated at a FREE width `κ > 0`.  This is the top of the WIDE route: the wide-bank
    dominations `|heatOp g gi H τ p q| ≤ C·gaussDdim (lam·τ) …` feed `hEboundW_le` at `κ := lam`
    (`baseKernelW lam 0 τ p q = gaussDdim (lam·τ) (p−q)`).  NOT `a₁ = R/6`. -/
theorem wide_a1_R6_of_residue_inf_v5 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (κ : ℝ) (hκ : 0 < κ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW κ (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
        = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
          + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0)
    (hInter : heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
            (fun τ p q => (-1 : ℝ) ^ (k + 1)
              * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
            t 0 0)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t)
    (hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n))
    -- ★ the threading's ingredient set, REPLACING the single `hCConv` `C²` hypothesis.
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (Bs Ba Bd Cf : ℝ) (D : Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (chart : CConvChartGateData g gi hChr hK S a b t u)
    (source : CConvSourceData
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf)
    (deriv : CConvDerivativeData g gi hChr hK S a b t u
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      D)
    (env : CConvEnvelopeData g gi hChr hK S a b t u Bs Ba Bd)
    (hD1 : ContDiffAt ℝ 1 D (0 : Point n)) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- re-derive the `hCConv` `C²` slot from the threading ingredient set (width-agnostic).
  have hCConv : ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0) (0 : Point n) :=
    QIQTH.CConvConcreteThreading.hCConv_concrete_from_data g gi hChr hK S a b t ht u hu_open hu0
      Bs Ba Bd Cf D metric chart source deriv env hD1
  -- feed the width-`κ` `∞`-capstone with `hCConv` now discharged.
  exact wide_a1_R6_of_residue_inf g gi Ric t ht C hCnn κ hκ hChr hK S a b ha hab hK0 hS0
    (vanVleckGatedWitness g gi hChr hK S a b) rfl hg hg0 hgi hΓ hdg0 htr hsrc
    hEboundW_le hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.WideA1Assembly

section AxiomChecks
open QIQTH.WideA1Assembly
#print axioms wide_trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty
#print axioms wide_a1_R6_of_residue_inf
#print axioms wide_a1_R6_of_residue_inf_v5
end AxiomChecks
