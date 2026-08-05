/-
  WideA1AssemblyTrunc — J4-263: the TRUNCATED-`hInt` rethread of the wide `a₁` residual capstone,
  and the BOTH-SLOTS-INTERNAL composition.  ONE brick of the `a₁ = R/6` heat-kernel campaign.
  NOT `a₁ = R/6`; proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file rethreads the width-parametric `a₁` residual capstone of
  `WideA1Assembly` so its per-step integrability slot `hInt` consumes the SMALL-TIME truncated family
  `TruncatedHIntRethread.IterConvIntegrableWOn E κ 0 C t` (window `(0, t]`) instead of the all-τ
  `HeatResidualBound.IterConvIntegrableW E κ 0 C`, and then COMPOSES that with the geometry residual
  provider + the truncated producer to internalize BOTH residual slots.  It carries no
  coefficient/geometry content of its own; it is pure integrability plumbing on top of banked
  machinery.  It does NOT close `a₁ = R/6`.

  ── WHY THE RETHREAD IS A DROP-IN (the C-route verdict, recalled from `TruncatedHIntRethread`).
     The width-`κ` capstone `WideA1Assembly.wide_trueKernel_diagonal_a1_eq_R6_residual_restricted_
     C2_infty` consumes `hInt` at EXACTLY ONE call site — its single width-specific line
        `leviSeries_summableW_le (heatOp …) κ 0 C t hκ le_rfl hC hEboundW_le hInt t ht le_rfl 0 0`
     (`QIQTH.HeatResidualBound.leviSeries_summableW_le`, from `RestrictedEboundW`) — at the OUTER
     conclusion time `t`, never at any larger time.  `TruncatedHIntRethread.leviSeries_summableW_le_
     trunc` has a byte-identical signature EXCEPT `hInt : IterConvIntegrableWOn E κ α C T` in place of
     `IterConvIntegrableW E κ α C`.  Taking the truncation window `T := t` (the outer time itself),
     the call is argument-for-argument identical (`htT := le_rfl : t ≤ t`), the carried `hEboundW_le`
     (already stated on `0 < τ ≤ t`) is unchanged, and the CONCLUSION is UNCHANGED.  So the rethread
     is: retype the ONE `hInt` binder to `IterConvIntegrableWOn (heatOp …) κ 0 C t` and swap the ONE
     call `leviSeries_summableW_le → leviSeries_summableW_le_trunc`.  Nothing else moves.  (Compiled
     source is copied verbatim; the capstone statement is NOT reconstructed from scratch.)

  ── THE COMPOSITION — BOTH residual slots internal, NO constant mismatch (the real finding).
     `wide_a1_R6_both_slots_internal` mirrors `ResidualAssemblyRecon.wide_a1_R6_of_residue_inf_
     hEboundW_discharged` (which already internalized `hEboundW_le` from geometry at any `κ ≥ 2`) and
     ADDITIONALLY internalizes `hInt`.  The geometry residual provider
     `ResidualAssemblyRecon.hEboundW_wide_from_geometry` delivers, at a PROVIDER-CHOSEN gate `(a,b,S)`,
        `∀ τ p q, 0 < τ → τ ≤ t → |heatOp …| ≤ C'' · baseKernelW κ 0 τ p q`
     at a SINGLE FIXED nonnegative constant `C''`.  ⚠ CONSTANT-THREADING FINDING:  the capstone binds
     ONE constant `C'` for BOTH residual slots, and here `C' := C''` works for BOTH with NO `max` and
     NO monotonicity lift.  The reason the J4-261 affine obstruction does NOT bite:  the provider's
     bound is on the TRUNCATED range `τ ≤ t` at a FIXED `C''` (the affine `(1+t)` factor is a CONSTANT
     at fixed `t`); the truncated producer `TruncatedHIntRethread.iterConvIntegrableWOn_of_bound_
     baseMeas_trunc` at window `T₀ := t` consumes exactly that fixed-`C''` `τ ≤ t` bound and returns
     `IterConvIntegrableWOn (heatOp …) κ 0 C'' t` — the same `C''`.  The affine `_of_affine_trunc`
     route (with `C·(1+T₀)`) is therefore NOT even needed on this composition; the fixed-constant
     producer suffices, and both slots coincide at `C''`.

  ── HONEST REMAINING CARRIES of the best capstone `wide_a1_R6_both_slots_internal`
     (all genuine, satisfiable, non-vacuous, never the conclusion):
       • `1 ≤ n`                      — needed by `hEzeroE_concrete` (nonpositive-time vanishing).
       • S1 joint strong measurability `∀ S a b, tripleHEmeas g gi (vanVleckGatedWitness …)` — the
         Borel/measurability substrate of the heat operator, carried ∀-gate because the residual
         provider CHOOSES the gate existentially; discharged concretely elsewhere
         (`HEmeasBorelAudit.tripleHEmeas_of_surface` from the `BorelDischargeSurface` families).
       • base geometry hyps `hg/hg0/hgi/hΓ/hdg0/htr/hsrc/hgnd/hgsymm/hinvF/hframeK/hw/hChr/hK/hK0` —
         the frame/normal-coordinate + smoothness inputs the leading term and provider consume.
       • the Levi/Duhamel INTERFACE arrow hyps `hS0/hDuhamel/hInter/hDConv` and the two spatial-`C²`
         slots `hCH/hCConv` — inner interface-assembly hypotheses of the returned implication,
         satisfiable, never the conclusion.
     INTERNAL (no longer carried, vs `WideA1Assembly.wide_a1_R6_of_residue_inf`):  BOTH residual
     slots — `hEboundW_le` (from geometry via the provider) AND `hInt` (from the provider's fixed-`C''`
     bound through the truncated producer, `hEzero` discharged from geometry).

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses.  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OmegaHsrcC4cAudit
import QIQTH.CConvConcreteThreading
import QIQTH.TruncatedHIntRethread
import QIQTH.ResidualAssemblyRecon
import QIQTH.DataPileWitnessAudit
import QIQTH.HEmeasBorelAudit

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.OmegaHsrcC4cAudit QIQTH.CConvFacade QIQTH.GateOpennessExport
open QIQTH.TruncatedHIntRethread QIQTH.ResidualAssemblyRecon
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.WideA1AssemblyTrunc

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ###############################################################################
    ### 1. THE TRUNCATED-`hInt` BASE CAPSTONE — `IterConvIntegrableW → IterConvIntegrableWOn` at `T = t`.
    ############################################################################### -/

/-- **★★★ `wide_a1_R6_trunc` (THE MINIMUM BANKABLE — step 2).**  Byte-for-byte copy of
    `WideA1Assembly.wide_trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty` with the SINGLE
    change that the per-step integrability slot `hInt` is retyped from the all-τ
    `IterConvIntegrableW (heatOp g gi H) κ 0 C` to the SMALL-TIME truncated family
    `TruncatedHIntRethread.IterConvIntegrableWOn (heatOp g gi H) κ 0 C t` (window `(0, t]`), and the
    ONE consuming line `leviSeries_summableW_le` swapped for the truncated engine
    `leviSeries_summableW_le_trunc` at `T := t` (`htT := le_rfl`).  Sound because the entire capstone
    lineage consumes `hInt` only at the outer conclusion time `t` (the C-route verdict).  The
    CONCLUSION is IDENTICAL to the width-`κ` original.  NOT `a₁ = R/6`. -/
theorem wide_a1_R6_trunc
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
    (hInt : IterConvIntegrableWOn (heatOp g gi H) κ 0 C t)
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
  -- ★ THE ONE RETHREAD: the truncated summability engine at `T := t`, replacing
  --   `leviSeries_summableW_le` (all-τ `hInt`) with `leviSeries_summableW_le_trunc` (`IterConv-`
  --   `IntegrableWOn` at window `t`).  Argument-for-argument identical (`htT := le_rfl : t ≤ t`).
  have hIterSum := leviSeries_summableW_le_trunc (heatOp g gi H) κ (0 : ℝ) C t hκ le_rfl hC
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
    ### 2. THE TRUNCATED-`hInt` MIDDLE CAPSTONE — the `a1_R6_of_residue_inf` mirror.
    ############################################################################### -/

/-- **★★★ `wide_a1_R6_of_residue_inf_trunc`.**  Copy of `WideA1Assembly.wide_a1_R6_of_residue_inf`
    with the per-step integrability slot `hInt` retyped to the truncated family
    `IterConvIntegrableWOn (heatOp g gi H) κ 0 C t`, threading `wide_a1_R6_trunc` in place of the
    all-τ base capstone.  The gate/leading-term steps are width- and truncation-independent, so the
    CONCLUSION is IDENTICAL.  NOT `a₁ = R/6`. -/
theorem wide_a1_R6_of_residue_inf_trunc (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
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
    (hInt : IterConvIntegrableWOn (heatOp g gi H) κ 0 C t)
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
  exact wide_a1_R6_trunc g gi Ric 1 le_rfl t ht
    (vanVleckGatedWitness g gi hChr hK S a b) C hCnn κ hκ hg hg0 hgi hΓ hdg0 htr hsrc
    hHdiag hEboundW_le hInt hDuhamel hInter hDH hDConv hCH hCConv

/-! ###############################################################################
    ### 3. THE COMPOSITION — BOTH residual slots (`hEboundW_le` AND `hInt`) INTERNAL.
    ############################################################################### -/

/-- **★★★★ `wide_a1_R6_both_slots_internal` (THE PRIZE — step 3).**  The width-`κ` (`κ ≥ 2`)
    `∞`-capstone with BOTH residual Gaussian-domination slots discharged internally: `hEboundW_le`
    from geometry via `ResidualAssemblyRecon.hEboundW_wide_from_geometry` (the banked width-2 van-Vleck
    residual provider ∘ the width-up transfer), and `hInt` from that SAME fixed-`C''` `τ ≤ t` bound
    through the truncated producer `TruncatedHIntRethread.iterConvIntegrableWOn_of_bound_baseMeas_trunc`
    at window `T₀ := t`, with the nonpositive-time vanishing discharged from geometry
    (`DataPileWitnessAudit.hEzeroE_concrete`, needs `1 ≤ n`) and the S1 joint strong measurability
    carried ∀-gate.  The gate `(a,b,S)` is PROVIDER-CHOSEN (existential).
    ⚠ CONSTANT THREADING:  the capstone binds ONE `C'` for both slots; here `C' := C''` (the provider's
    fixed constant) fills BOTH with NO `max` and NO monotonicity — the truncation makes `hInt` land at
    the SAME constant as `hEboundW_le`.  Relative to `ResidualAssemblyRecon.wide_a1_R6_of_residue_inf_
    hEboundW_discharged` the returned implication is shorter by exactly the `IterConvIntegrableW …`
    (`hInt`) arrow.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem wide_a1_R6_both_slots_internal
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (κ : ℝ) (hκ : 2 ≤ κ) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hEmeas : ∀ (S : Point n → Set (Point n)) (a b : ℝ),
      tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b)) :
    ∃ a b C' : ℝ, ∃ S : Point n → Set (Point n),
      0 < a ∧ a < b ∧ 0 ≤ C' ∧
      ((0 : Point n) ∈ S 0 →
        (heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
            = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
              + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0) →
        (heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
            = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                (fun τ p q => (-1 : ℝ) ^ (k + 1)
                  * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
                t 0 0) →
        DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t →
        ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) →
        ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
            (0 : Point n) →
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
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  obtain ⟨a, b, C', ha, hab, hC0, S, hbound⟩ :=
    hEboundW_wide_from_geometry g gi hChr hK hg hgnd hgsymm hinvF hframeK hw hdg0 hg0 t ht.le κ hκ
  refine ⟨a, b, C', S, ha, hab, hC0, ?_⟩
  intro hS0 hDuhamel hInter hDConv hCH hCConv
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  -- ★ INTERNALIZE `hInt` from the SAME fixed-`C'` `τ ≤ t` residual bound via the truncated producer.
  have hInt : IterConvIntegrableWOn
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ 0 C' t :=
    iterConvIntegrableWOn_of_bound_baseMeas_trunc
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ C' t hκ0 hbound
      (hEzeroE_concrete g gi hChr hK S a b hn) (hEmeas S a b)
  exact wide_a1_R6_of_residue_inf_trunc g gi Ric t ht C' hC0 κ hκ0 hChr hK S a b ha hab hK0 hS0
    (vanVleckGatedWitness g gi hChr hK S a b) rfl hg hg0' hgi hΓ hdg0 htr hsrc
    hbound hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.WideA1AssemblyTrunc

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WideA1AssemblyTrunc
#print axioms wide_a1_R6_trunc
#print axioms wide_a1_R6_of_residue_inf_trunc
#print axioms wide_a1_R6_both_slots_internal
end AxiomChecks
