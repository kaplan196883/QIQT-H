/-
  GatedGlobalWitnessN1ThreeSlots — J4-773: the ORDER-1 gated van-Vleck capstone with THREE residual
  slots (`hEboundW`, `hInt`, `hInter`) all discharged INTERNALLY from geometry.  ONE brick of the
  `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about the `R/6` coefficient.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file is a WIRING ADAPTER, no coefficient/geometry content of its own.  It
  composes three ALREADY-BANKED pieces so that the residual `hEboundW`/`hInt`/`hInter` carries of the
  order-1 gated van-Vleck capstone are supplied internally, at the SAME live witness
      `H₁ := vanVleckGatedWitness g gi hChr hK S a b`
           = gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
               (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))
  used by `GatedGlobalWitnessN1Capstone.trueKernel_diagonal_a1_eq_R6_residual_N1_discharged` (J4-767).
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no hypothesis equal
  to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS CLOSES vs. THE J4-767 N1 CAPSTONE.

  The J4-767 capstone `trueKernel_diagonal_a1_eq_R6_residual_N1_discharged` CARRIES the width-2 residual
  bound `hEboundW` (PURE all-τ single-constant shape) as an open binder — and derives `hInt`/`hInter`
  from it via the ALL-τ producers `iterConvIntegrableW_of_bound_baseMeas` /
  `heatConv_leviSeries_interchange`.  J4-772 found that the exact-witness order-1 bound IS proven
  unconditionally from geometry — `CoeffU1Fix.gatedWitnessN1_hEboundW_le_vanVleck_final` — but only in
  a `(0,t]`-LOCAL, affine-in-τ form, which does NOT feed the pure all-τ binder.

  This file routes that geometry bound through the `(0,t]`-TRUNCATED consumer chain instead:
    • `EboundWiringHD1.hEboundW_from_geometry` repackages the van-Vleck provider into the FIXED-`C'`
      (`C' = C·(1+t)`), `τ ≤ t`, width-2 bound `hEboundW_le` (provider-chosen gate `(a,b,S)`);
    • `TruncatedHIntRethread.iterConvIntegrableWOn_of_bound_baseMeas_trunc` turns that SAME fixed-`C'`
      `τ ≤ t` bound into `hInt : IterConvIntegrableWOn (heatOp g gi H₁) 2 0 C' t` (window `(0,t]`),
      with nonpositive-time vanishing `hEzero` from `DataPileWitnessAudit.hEzeroE_concrete` (`1 ≤ n`)
      and base measurability from the carried ∀-gate `tripleHEmeas`;
    • `TruncatedHIntRethread.heatConv_leviSeries_interchange_trunc` turns the SAME data into
      `hInter` (the tsum/heatConv interchange) at `T₀ := t`, `htT := le_rfl` — the `_trunc` consumer
      the J4-772 note names;
    • `WideA1AssemblyTrunc.wide_a1_R6_of_residue_inf_trunc` (κ := 2) assembles the capstone from the
      truncated `hEboundW_le` + `hInt` (its Neumann convergence uses `leviSeries_summableW_le_trunc`).

  RESULT.  `n1_vanVleck_three_slots_internal` — the order-1 gated van-Vleck Seeley–DeWitt capstone with
  `hEboundW`, `hInt` AND `hInter` ALL supplied internally.  Relative to
  `WideA1AssemblyTrunc.wide_a1_R6_both_slots_internal` (J4-263, which already internalizes `hEboundW`
  and `hInt` at this witness) the returned implication is SHORTER by exactly the `hInter` antecedent.
  The surviving inner-implication antecedents are `hS0`, `hDuhamel`, `hDConv`, `hCH`, `hCConv`; the
  outer carries are the RNC/gauge geometry data + the ∀-gate joint strong measurability `hEmeas` +
  `1 ≤ n`.  Conclusion: the true-kernel diagonal Seeley–DeWitt expansion
      `K(t,0,0) = (4πt)^{−d/2} · (1 + (R/6)·t + t²·remainder)`,  `R = ∑ᵢ Ric_{ii}`,
  the `N = 1` remainder sum `∑_{k ∈ Ico 2 2}` EMPTY.

  ⚠ HONEST SCOPE (binding).  STILL CONDITIONAL; NOT `a₁ = R/6`.  What IS achieved: the `hInter` residual
  carry — the one interface arrow `wide_a1_R6_both_slots_internal` still left open at this witness — is
  now discharged internally from the SAME geometry data via the truncated interchange engine, leaving
  only the genuine Duhamel / spatial-continuity interface antecedents.  The remaining
  `hDuhamel`/`hDConv`/`hCH`/`hCConv` are the still-open analytic interface walls, order-independent.
-/
import Mathlib
import QIQTH.WideA1AssemblyTrunc
import QIQTH.EboundWiringHD1
import QIQTH.DataPileWitnessAudit
import QIQTH.HEmeasBorelAudit
import QIQTH.ConvApproximants
import QIQTH.LeviInterchangeTrunc

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound
open QIQTH.TruncatedHIntRethread QIQTH.LeviInterchangeTrunc QIQTH.ResidualAssemblyRecon QIQTH.EboundWiringHD1
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.WideA1AssemblyTrunc
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★★★★ J4-773 — the ORDER-1 gated van-Vleck capstone with `hEboundW`, `hInt`, `hInter` all
    INTERNAL.**  The order-1 gated van-Vleck Seeley–DeWitt capstone at the live witness
    `H₁ = vanVleckGatedWitness g gi hChr hK S a b` (defeq to the J4-767 witness), with the three
    residual carries supplied internally from geometry:

      • `hEboundW_le` — the FIXED-`C'` (`C' = C·(1+t)`), `τ ≤ t`, width-2 bound, delivered by
        `EboundWiringHD1.hEboundW_from_geometry` (= `CoeffU1Fix.gatedWitnessN1_hEboundW_le_vanVleck_final`
        repackaged; provider-chosen gate `(a,b,S)`);
      • `hInt : IterConvIntegrableWOn (heatOp g gi H₁) 2 0 C' t` — from that SAME bound via the
        truncated producer `iterConvIntegrableWOn_of_bound_baseMeas_trunc` (window `(0,t]`), `hEzero`
        from `hEzeroE_concrete` (`1 ≤ n`), base measurability from the ∀-gate `hEmeas`;
      • `hInter` — the tsum/heatConv interchange, from the SAME data via
        `heatConv_leviSeries_interchange_trunc` at `T₀ := t`.

    The capstone is assembled by `WideA1AssemblyTrunc.wide_a1_R6_of_residue_inf_trunc` (κ = 2).  The
    inner-implication antecedents are `hS0`, `hDuhamel`, `hDConv`, `hCH`, `hCConv` — one fewer (`hInter`)
    than `wide_a1_R6_both_slots_internal`.  STILL CONDITIONAL; NOT `a₁ = R/6`. -/
theorem n1_vanVleck_three_slots_internal
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
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
    ∃ a b : ℝ, ∃ S : Point n → Set (Point n),
      0 < a ∧ a < b ∧
      ((0 : Point n) ∈ S 0 →
        (heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
            = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
              + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0) →
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
  -- ── The van-Vleck residual bound, repackaged into the FIXED-`C'` `τ ≤ t` width-2 form. ──────────
  obtain ⟨a, b, C', ha, hab, hC0, S, hbound⟩ :=
    hEboundW_from_geometry g gi hChr hK hg hgnd hgsymm hinvF hframeK hw hdg0 hg0 t ht.le
  refine ⟨a, b, S, ha, hab, ?_⟩
  intro hS0 hDuhamel hDConv hCH hCConv
  -- Abbreviations for the concrete residual operator.
  set H := vanVleckGatedWitness g gi hChr hK S a b with hHdef
  -- Nonpositive-time vanishing (needs `1 ≤ n`).
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0 :=
    hEzeroE_concrete g gi hChr hK S a b hn
  -- Base joint strong measurability at the provider-chosen gate.
  have hEmeasG : StronglyMeasurable
      (fun w : ℝ × Point n × Point n => heatOp g gi H w.1 w.2.1 w.2.2) := hEmeas S a b
  -- ── `hInt` from the SAME fixed-`C'` `τ ≤ t` bound via the TRUNCATED producer. ────────────────────
  have hInt : IterConvIntegrableWOn (heatOp g gi H) (2 : ℝ) 0 C' t :=
    iterConvIntegrableWOn_of_bound_baseMeas_trunc (heatOp g gi H) (2 : ℝ) C' t (by norm_num)
      hbound hEzero hEmeasG
  -- ── `hInter` (tsum/heatConv interchange) from the SAME data via the TRUNCATED interchange. ────────
  have hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi H)
          (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 :=
    heatConv_leviSeries_interchange_trunc (heatOp g gi H) C' hC0 t hbound hEzero hEmeasG
      t ht le_rfl 0 0
  -- ── Assemble via the truncated wide capstone (κ = 2). ────────────────────────────────────────────
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  exact wide_a1_R6_of_residue_inf_trunc g gi Ric t ht C' hC0 (2 : ℝ) (by norm_num) hChr hK S a b
    ha hab hK0 hS0 H hHdef hg hg0' hgi hΓ hdg0 htr hsrc hbound hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.HeatResidualBound
