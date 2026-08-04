/-
  LeviSeriesLocalData — J4-205: the shared `(0,T]`-window local-data package for the SIGNED Levi
  series `F = leviSeries E`  (Sol final plan Phase 1, docs/qg_roadmap/JET4_TOWER_PLAN.md,
  "SOL CONSULT #3").

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a PACKAGING
  layer: it bundles, in ONE `: Prop` structure `LeviSeriesLocalData E C T`, the facts that the three
  downstream Levi consumers (`hInt` = `IterConvIntegrableW`; `hInter` = the tsum/heatConv
  interchange; the `hCConv` source-data facade) all need about `F := leviSeries E` on the `(0,T]`
  window, width-2, order-0:
      • the base joint strong measurability `hEmeas` of the residual (the HONEST carry — Sol);
      • the termwise joint strong measurability `htermMeas` of every `iterE E k`;
      • the termwise Volterra norm majorant `hmajor`  (`|iterE E (k+1)| ≤ C^(k+1)·iterKernelW 2 0`);
      • the scalar-majorant summability `hmajorSum`  (the `Γ`/factorial decay);
      • the sectionwise / spatial-L¹ integrability family `hInt` (`IterConvIntegrableW E 2 0 C`);
      • the strong measurability `hFmeas` of the ACTUAL pointwise `tsum` `leviSeries E`;
      • the local Gaussian envelope `hFenv` for `F` on `(0,T]`.

  Sol's point: `IterConvIntegrableW` alone does NOT hand you `hFmeas`/`hFenv` — the passage from the
  iterated-convolution domination to the actual `tsum` needs the SUMMABLE majorant; this file is the
  packaging that performs that passage ONCE, generically.

  TWO GENERIC LEMMAS carry the load (both pure Mathlib, geometry-free):
    • `leviSeries_stronglyMeasurable_of_termwise` — strongly-measurable partial sums + a.e. pointwise
      summability ⟹ the `tsum` is strongly measurable (`aestronglyMeasurable_of_tendsto_ae` on the
      finite partial sums, which converge to the `tsum` by `HasSum.tendsto_sum_nat`);
    • `leviSeries_bound_of_majorant` — `|aₖ| ≤ Mₖ` termwise + `Summable M` ⟹
      `|∑' k, (−1)^(k+1)·aₖ| ≤ ∑' k, Mₖ` (`norm_tsum_le_tsum_norm` + `tsum_le_tsum`).

  THE BUILDER `leviSeriesLocalData_of_windowBound` assembles the package from the actual residual's
  honest analytic inputs — the `(0,T]` one-step bound, the nonpositive-time vanishing `hEzero`, the
  base measurability `hEmeas` (carried), and the every-ceiling bound family `hglobal` that feeds
  `IterConvIntegrableW` — via the banked width-2 machinery
  (`iterConvIntegrableW_of_locally_bound_baseMeas`, `iterConvW_bound_le`, `scaledIterKernelW_summable`,
  `leviSeries_dominatedW_le`, `iterE_joint_stronglyMeasurable`/`iterE_zmeas`) plus the two generic
  lemmas above.  Every hypothesis is a genuine, non-vacuous fact of the actual residual — none is the
  conclusion.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GatedWitnessPackage
import QIQTH.GatedWitnessMeas
import QIQTH.RestrictedEboundW
import QIQTH.IterEMeasurable
import QIQTH.TrueHeatKernel

open MeasureTheory Filter Topology
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open scoped Interval

namespace QIQTH.LeviSeriesLocalData

set_option maxHeartbeats 3200000

variable {n : ℕ}

/-! ###############################################################################
    ### 1. THE TWO GENERIC LEMMAS (geometry-free, pure Mathlib).
    ############################################################################### -/

/-- **★ THE GENERIC `tsum` STRONG-MEASURABILITY LEMMA.**  On any measure space, if every term `f k`
    is `AEStronglyMeasurable` and the series `∑ₖ f k x` is a.e.-pointwise summable, then the actual
    `tsum` `x ↦ ∑' k, f k x` is `AEStronglyMeasurable`.  The finite partial sums
    `x ↦ ∑_{k<N} f k x` are `AEStronglyMeasurable` (`Finset.aestronglyMeasurable_sum`) and converge
    a.e. to the `tsum` (`HasSum.tendsto_sum_nat`), so `aestronglyMeasurable_of_tendsto_ae` closes.
    This is the passage from termwise data to the actual pointwise `tsum` Sol flags. -/
theorem leviSeries_stronglyMeasurable_of_termwise
    {X : Type*} [MeasurableSpace X] {μ : Measure X} (f : ℕ → X → ℝ)
    (hmeas : ∀ k, AEStronglyMeasurable (f k) μ)
    (hsum : ∀ᵐ x ∂μ, Summable (fun k => f k x)) :
    AEStronglyMeasurable (fun x => ∑' k : ℕ, f k x) μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (fun N => Finset.aestronglyMeasurable_sum (Finset.range N) (fun k _ => hmeas k)) ?_
  filter_upwards [hsum] with x hx
  simp only [Finset.sum_apply]
  exact hx.hasSum.tendsto_sum_nat

/-- **★ THE GENERIC ENVELOPE LEMMA.**  If `|a k| ≤ M k` for every `k` and `M` is summable, then the
    signed alternating series is dominated by the majorant series:
        `|∑' k, (−1)^(k+1)·a k| ≤ ∑' k, M k`.
    Route: `‖(−1)^(k+1)·a k‖ = |a k| ≤ M k`, so the norm series is summable
    (`Summable.of_nonneg_of_le`), and `norm_tsum_le_tsum_norm` then `tsum_le_tsum` conclude.  This is
    the generic form of the `leviSeries` envelope (the sign factor is unit-modulus). -/
theorem leviSeries_bound_of_majorant (a M : ℕ → ℝ)
    (hbd : ∀ k, |a k| ≤ M k) (hM : Summable M) :
    |∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * a k| ≤ ∑' k : ℕ, M k := by
  have habs : ∀ k, ‖(-1 : ℝ) ^ (k + 1) * a k‖ ≤ M k := by
    intro k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    exact hbd k
  have hnormSum : Summable (fun k : ℕ => ‖(-1 : ℝ) ^ (k + 1) * a k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) habs hM
  calc |∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * a k|
      = ‖∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * a k‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, ‖(-1 : ℝ) ^ (k + 1) * a k‖ := norm_tsum_le_tsum_norm hnormSum
    _ ≤ ∑' k : ℕ, M k := hnormSum.tsum_le_tsum habs hM

/-! ###############################################################################
    ### 2. THE `LeviSeriesLocalData` PACKAGE.
    ############################################################################### -/

/-- **`LeviSeriesLocalData E C T`.**  The shared `(0,T]`-window package for the signed Levi series
    `leviSeries E`, width-2, order-0, model-constant `C`.  Every field is a genuine derived fact
    (measurability / domination / summability), never the `a₁ = R/6` conclusion. -/
structure LeviSeriesLocalData (E : ℝ → Point n → Point n → ℝ) (C T : ℝ) : Prop where
  /-- `C ≥ 0` (the model-dominator constant). -/
  hC : 0 ≤ C
  /-- `T > 0` (the window ceiling). -/
  hT : 0 < T
  /-- The base joint strong measurability of the residual — the HONEST carry (Sol). -/
  hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)
  /-- Termwise joint strong measurability of every iterated convolution `iterE E k`. -/
  htermMeas : ∀ k, 1 ≤ k → ∀ y : Point n,
    StronglyMeasurable (fun p : ℝ × Point n => iterE E k p.1 p.2 y)
  /-- The termwise Volterra norm majorant on the window. -/
  hmajor : ∀ (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
    |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) τ p q
  /-- The scalar-majorant summability (the `Γ`/factorial decay). -/
  hmajorSum : ∀ (τ : ℝ) (p q : Point n), 0 < τ →
    Summable (fun k : ℕ => C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) τ p q)
  /-- The sectionwise / spatial-L¹ integrability family. -/
  hInt : IterConvIntegrableW E (2 : ℝ) (0 : ℝ) C
  /-- Strong measurability of the ACTUAL pointwise `tsum` `leviSeries E`, spatial slice. -/
  hFmeas : ∀ (s : ℝ), 0 < s → s ≤ T → ∀ y : Point n,
    AEStronglyMeasurable (fun z : Point n => leviSeries E s z y) (volume : Measure (Point n))
  /-- The local Gaussian envelope for `F = leviSeries E` on `(0,T]`. -/
  hFenv : ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
    |leviSeries E τ p q| ≤ C_L * baseKernelW (2 : ℝ) (0 : ℝ) τ p q

/-! ###############################################################################
    ### 3. THE BUILDER — assemble the package from the residual's honest inputs.
    ############################################################################### -/

/-- **★★ `leviSeriesLocalData_of_windowBound`.**  Assemble `LeviSeriesLocalData E C T` from the
    actual residual's honest analytic inputs:

    * `hEbnd`   — the width-2 one-step bound on the `(0,T]` window at constant `C`;
    * `hEzero`  — vanishing at nonpositive time;
    * `hEmeas`  — the base joint strong measurability (CARRIED — the honest M1 input);
    * `hglobal` — the every-ceiling bound family (an honest fact of the residual), which
                  `iterConvIntegrableW_of_locally_bound_baseMeas` needs to build the ALL-outer-time
                  `IterConvIntegrableW E 2 0 C`.

    Each output field is discharged by banked width-2 machinery + the two generic lemmas above:
    `hInt` = `iterConvIntegrableW_of_locally_bound_baseMeas`; `htermMeas` =
    `iterE_joint_stronglyMeasurable`; `hmajor` = `iterConvW_bound_le`; `hmajorSum` =
    `scaledIterKernelW_summable`; `hFmeas` = `leviSeries_stronglyMeasurable_of_termwise` fed the
    majorant summability; `hFenv` = `leviSeries_dominatedW_le`.  NOT `a₁ = R/6`. -/
theorem leviSeriesLocalData_of_windowBound
    (E : ℝ → Point n → Point n → ℝ) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 < T)
    (hEbnd : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (hglobal : ∀ T' : ℝ, 0 < T' → ∃ CT : ℝ, 0 ≤ CT ∧
        ∀ τ p q, 0 < τ → τ ≤ T' → |E τ p q| ≤ CT * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    LeviSeriesLocalData E C T := by
  have hInt : IterConvIntegrableW E (2 : ℝ) (0 : ℝ) C :=
    iterConvIntegrableW_of_locally_bound_baseMeas E C hEzero hEmeas hglobal
  refine
    { hC := hC
      hT := hT
      hEmeas := hEmeas
      htermMeas := iterE_joint_stronglyMeasurable E hEmeas
      hmajor := ?_
      hmajorSum := ?_
      hInt := hInt
      hFmeas := ?_
      hFenv := leviSeries_dominatedW_le E C T hC hT hEbnd hInt }
  · -- the termwise Volterra majorant
    intro k τ p q hτ hτT
    exact iterConvW_bound_le E (2 : ℝ) (0 : ℝ) C T hEbnd hInt (k + 1) (by omega) τ hτ hτT p q
  · -- the scalar-majorant summability
    intro τ p q hτ
    exact scaledIterKernelW_summable (2 : ℝ) (0 : ℝ) τ C (by norm_num) le_rfl hτ hC p q
  · -- the spatial `tsum` strong measurability
    intro s hs hsT y
    have hmeas : ∀ k : ℕ,
        AEStronglyMeasurable (fun z : Point n => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)
          (volume : Measure (Point n)) :=
      fun k => (iterE_zmeas E hEmeas (k + 1) (by omega) s y).const_mul _
    have hsum : ∀ᵐ z : Point n ∂(volume : Measure (Point n)),
        Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y) := by
      refine Filter.Eventually.of_forall (fun z => ?_)
      have hmodel : Summable (fun k : ℕ => C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y) :=
        scaledIterKernelW_summable (2 : ℝ) (0 : ℝ) s C (by norm_num) le_rfl hs hC z y
      refine Summable.of_norm_bounded hmodel (fun k => ?_)
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
      exact iterConvW_bound_le E (2 : ℝ) (0 : ℝ) C T hEbnd hInt (k + 1) (by omega) s hs hsT z y
    have key := leviSeries_stronglyMeasurable_of_termwise
      (fun k z => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y) hmeas hsum
    have hrw : (fun z : Point n => leviSeries E s z y)
        = fun z : Point n => ∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y := rfl
    rw [hrw]; exact key

/-! ###############################################################################
    ### 4. CONSUMER-FACING ACCESSORS (Phase-2 slots).
    ############################################################################### -/

/-- **`hInt_from_seriesData`.**  The `IterConvIntegrableW` slot pulled directly from the package —
    exactly the `hInt` demand of `trueKernel_diagonal_a1_eq_R6`/`leviSeries_volterra`. -/
theorem hInt_from_seriesData {E : ℝ → Point n → Point n → ℝ} {C T : ℝ}
    (data : LeviSeriesLocalData E C T) :
    IterConvIntegrableW E (2 : ℝ) (0 : ℝ) C :=
  data.hInt

end QIQTH.LeviSeriesLocalData

section AxiomChecks
open QIQTH.LeviSeriesLocalData
#print axioms leviSeries_stronglyMeasurable_of_termwise
#print axioms leviSeries_bound_of_majorant
#print axioms leviSeriesLocalData_of_windowBound
#print axioms hInt_from_seriesData
end AxiomChecks
