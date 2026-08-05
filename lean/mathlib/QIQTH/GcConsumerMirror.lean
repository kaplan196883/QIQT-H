/-
  GcConsumerMirror — J4-241: the Gc consumer MIRRORS (τ + field²) + the S1 SIDESTEP.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It completes
  the `Gc`-route (chart-wall-free) SUPPLIER story for the triple `hEmeas` (S1) of `HEmeasBorelAudit`:
  it banks the two remaining `Gc`-consumer mirrors (the `∂_τ` conjunct (1) and the mixed second
  field-`pd` conjunct (3)) — the analogues of `AmpPdComposition.firstFieldPd_prod_measurable_Gc`
  (conjunct (2), J4-240) — and then ASSEMBLES the full S1 triple DIRECTLY through
  `HEmeasBorelAudit.tripleHEmeas_of_surface`, WITHOUT the raw off-image joint chart measurability
  (`.choose` wall) and WITHOUT restating the forbidden ~130-binder capstone existentials.
  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses.
  No existing file is edited.

  ## THE GC ROUTE.  Each of the three BorelDischargeSurface conjuncts is the joint Borel measurability
  of a raw field-derivative kernel of the concrete gated van-Vleck witness.  The raw representative
  (`gatedTauRepProdS` / `gatedDerivRepProdS` / `gatedMixed2RepProdS`) carries the chart symbol
  `uniformInverseChart …` (a `Classical.choose` partial-homeomorph inverse), whose joint measurability
  is UNPROVABLE off the flow image.  The `Gc` route replaces it, on the gate, by a GLOBALLY MEASURABLE
  regional flow-inverse `Gc` (`ChartRepConstruction.flowInverse_jointMeasurable_regional`) plus the
  amplitude value / `pd` twins (`AmpGc` / `Afield…` / `Bfield`), glued by the on-gate value AGREEMENTS.
  Each mirror: (i) rewrite the raw kernel to its S-re-gated representative (the everywhere identity under
  the SATISFIABLE conditional `hgate`); (ii) on the gate the raw indicator body equals the `Gc`-swapped
  (globally measurable) body (the agreements); (iii) the `Gc` body is globally Borel (measurable algebra).

  ## WHAT LANDS.
    §A — `secondFieldPd_prod_measurable_Gc`  — ★ conjunct (3) mirror (mixed second field-`pd`).
    §B — `tauDeriv_prod_measurable_Gc`        — ★ conjunct (1) mirror (`∂_τ`; value swaps only).
    §C — `tripleHEmeas_Gc`                    — ★★ S1 for the concrete witness, DIRECT via the surface,
                                                 chart-wall-free, from SATISFIABLE `Gc`-carriers.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HEmeasBorelAudit
import QIQTH.HgateSatAudit
import QIQTH.GatedRepSFix
import QIQTH.Field2NbhdReshape
import QIQTH.AmpPdComposition

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open scoped Topology BigOperators ContDiff

namespace QIQTH.GcConsumerMirror

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — ★ the MIXED SECOND field-`pd` `Gc`-mirror (BorelDischargeSurface conjunct (3)).
    ############################################################################### -/

/-- **★★★ `secondFieldPd_prod_measurable_Gc` — the mixed second field-`pd` measurability WITHOUT the raw
    chart wall.**  Produces the joint Borel measurability of the raw off-diagonal second field-`pd`
    kernel `w ↦ pd (fun y => pd (fun x => vanVleckGatedWitness … w.1 x w.2.2) j y) i w.2.1` — the
    conjunct (3) shape — from the `Gc`-ROUTE inputs:
      • `Measurable Gc` (banked regional flow-inverse) instead of the UNPROVABLE raw chart measurability;
      • `AmpGc` / `AfieldI` / `AfieldJ` / `Bfield` measurable twins (the amplitude value and its `i`/`j`/
        mixed field-`pd`s) instead of the raw amplitude / amp-`pd` measurabilities;
      • the on-gate AGREEMENTS (`hChartAgree` / `hAmpAgree` / `hPdiAgree` / `hPdjAgree` / `hPd2Agree`)
        that make the raw re-gated representative EQUAL the `Gc`-substituted (globally measurable) one on
        the gate.
    Route: `witnessMixed2 = gatedMixed2RepProdS` (`Field2NbhdReshape.witnessMixed2_eq_gatedMixed2RepProdS_nbhd`,
    the WEAKENED-`hgate` v5 identity — satisfiable); on the gate the raw indicator body equals the
    `Gc`-substituted body (the five agreements); the `Gc` body is globally measurable.  The raw-chart
    measurability hypothesis is ELIMINATED.  NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_measurable_Gc (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (Gc : Point n × Point n → Point n) (AmpGc AfieldI AfieldJ Bfield : ℝ → Point n → Point n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hGcMeas : Measurable Gc)
    (hPimeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
    (hPjmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
    (hQmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
    (hAmpGcMeas : Measurable (fun w : ℝ × Point n × Point n => AmpGc w.1 w.2.2 w.2.1))
    (hAfieldIMeas : Measurable (fun w : ℝ × Point n × Point n => AfieldI w.1 w.2.2 w.2.1))
    (hAfieldJMeas : Measurable (fun w : ℝ × Point n × Point n => AfieldJ w.1 w.2.2 w.2.1))
    (hBfieldMeas : Measurable (fun w : ℝ × Point n × Point n => Bfield w.1 w.2.2 w.2.1))
    (hChartAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
    (hAmpAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 = AmpGc w.1 w.2.2 w.2.1)
    (hPdiAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 = AfieldI w.1 w.2.2 w.2.1)
    (hPdjAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1 = AfieldJ w.1 w.2.2 w.2.1)
    (hPd2Agree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1 = Bfield w.1 w.2.2 w.2.1)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k) (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1 = 0) :
    Measurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1) := by
  classical
  -- (i) the raw kernel equals the S-re-gated representative (SATISFIABLE conditional `hgate`).
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1)
      = QIQTH.GatedRepSFix.gatedMixed2RepProdS g gi hC hK S a b i j Pifield Pjfield Qfield := by
    funext w
    exact QIQTH.Field2NbhdReshape.witnessMixed2_eq_gatedMixed2RepProdS_nbhd hn g gi hC hK S a b i j
      Pifield Pjfield Qfield hgate hOffS2 w
  rw [hrw]
  -- (ii) on the gate the re-gated body equals the `Gc`-substituted (globally measurable) body.
  have hEq : QIQTH.GatedRepSFix.gatedMixed2RepProdS g gi hC hK S a b i j Pifield Pjfield Qfield
      = Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
          (fun w =>
            gaussDdim w.1 (Gc (w.2.2, w.2.1))
                * ((∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k)
                      * (∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k) / (4 * w.1 ^ 2)
                    - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                        + (∑ k, Gc (w.2.2, w.2.1) k * Qfield w.2.2 w.2.1 k)) / (2 * w.1))
                * AmpGc w.1 w.2.2 w.2.1
              + (gaussDdim w.1 (Gc (w.2.2, w.2.1))
                    * (-(∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k) / (2 * w.1)))
                  * AfieldI w.1 w.2.2 w.2.1
              + (gaussDdim w.1 (Gc (w.2.2, w.2.1))
                    * (-(∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k) / (2 * w.1)))
                  * AfieldJ w.1 w.2.2 w.2.1
              + gaussDdim w.1 (Gc (w.2.2, w.2.1)) * Bfield w.1 w.2.2 w.2.1) := by
    funext w
    unfold QIQTH.GatedRepSFix.gatedMixed2RepProdS
    by_cases hw : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
    · have hmem : w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} := hw
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
          hChartAgree w hw.1 hw.2, hAmpAgree w hw.1 hw.2,
          hPdiAgree w hw.1 hw.2, hPdjAgree w hw.1 hw.2, hPd2Agree w hw.1 hw.2]
    · have hnmem : w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} := hw
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmem]
  rw [hEq]
  -- (iii) the `Gc` body is globally Borel (measurable algebra, `Gc` in place of the chart).
  have hGcV : Measurable (fun w : ℝ × Point n × Point n => Gc (w.2.2, w.2.1)) :=
    hGcMeas.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  have hG : Measurable (fun w : ℝ × Point n × Point n => gaussDdim w.1 (Gc (w.2.2, w.2.1))) :=
    QIQTH.InnerKernelJointMeas.gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hGcV)
  have hVPi : Measurable (fun w : ℝ × Point n × Point n =>
      ∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k) :=
    Finset.measurable_sum Finset.univ (fun k _ => ((measurable_pi_apply k).comp hGcV).mul (hPimeas k))
  have hVPj : Measurable (fun w : ℝ × Point n × Point n =>
      ∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k) :=
    Finset.measurable_sum Finset.univ (fun k _ => ((measurable_pi_apply k).comp hGcV).mul (hPjmeas k))
  have hPiPj : Measurable (fun w : ℝ × Point n × Point n =>
      ∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) :=
    Finset.measurable_sum Finset.univ (fun k _ => (hPimeas k).mul (hPjmeas k))
  have hVQ : Measurable (fun w : ℝ × Point n × Point n =>
      ∑ k, Gc (w.2.2, w.2.1) k * Qfield w.2.2 w.2.1 k) :=
    Finset.measurable_sum Finset.univ (fun k _ => ((measurable_pi_apply k).comp hGcV).mul (hQmeas k))
  have hden2 : Measurable (fun w : ℝ × Point n × Point n => 4 * w.1 ^ 2) :=
    measurable_const.mul (measurable_fst.pow_const 2)
  have hden1 : Measurable (fun w : ℝ × Point n × Point n => 2 * w.1) :=
    measurable_const.mul measurable_fst
  have hHess : Measurable (fun w : ℝ × Point n × Point n =>
      (∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k)
          * (∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k) / (4 * w.1 ^ 2)
        - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
            + (∑ k, Gc (w.2.2, w.2.1) k * Qfield w.2.2 w.2.1 k)) / (2 * w.1)) :=
    ((hVPi.mul hVPj).div hden2).sub ((hPiPj.add hVQ).div hden1)
  have hGradj : Measurable (fun w : ℝ × Point n × Point n =>
      -(∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPj.neg.div hden1
  have hGradi : Measurable (fun w : ℝ × Point n × Point n =>
      -(∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPi.neg.div hden1
  exact (((((hG.mul hHess).mul hAmpGcMeas).add
      ((hG.mul hGradj).mul hAfieldIMeas)).add
      ((hG.mul hGradi).mul hAfieldJMeas)).add
      (hG.mul hBfieldMeas)).indicator hKSmeas

/-! ###############################################################################
    ### §B — ★ the `∂_τ` `Gc`-mirror (BorelDischargeSurface conjunct (1); value swaps only).
    ############################################################################### -/

/-- **★★★ `tauDeriv_prod_measurable_Gc` — the `∂_τ` measurability WITHOUT the raw chart wall.**  Produces
    the joint Borel measurability of the raw `∂_τ` kernel `w ↦ deriv (fun u => vanVleckGatedWitness …
    u w.2.1 w.2.2) w.1` — the conjunct (1) shape — from the `Gc`-ROUTE inputs.  The `∂_τ` representative
    (`HgateSatAudit.gatedTauRepProdS`) contains the chart only through its VALUE (the Gaussian
    `t`-derivative coefficient × amplitude, no field-`pd`s), so only the chart-value swap `Gc` and the
    amplitude-value swap `AmpGc` are needed — NO amp-`pd` twins.  Route: `witnessTauDeriv =
    gatedTauRepProdS` (`HgateSatAudit.witnessTauDeriv_eq_gatedTauRepProdS`, SATISFIABLE conditional
    `hgate`); on the gate the raw body equals the `Gc`/`AmpGc` body (`hChartAgree`/`hAmpAgree`); the
    `Gc` body is globally measurable.  NOT `a₁ = R/6`. -/
theorem tauDeriv_prod_measurable_Gc (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ)
    (Gc : Point n × Point n → Point n) (AmpGc : ℝ → Point n → Point n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hGcMeas : Measurable Gc)
    (hCmeas : Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1))
    (hAmpGcMeas : Measurable (fun w : ℝ × Point n × Point n => AmpGc w.1 w.2.2 w.2.1))
    (hChartAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
    (hAmpAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 = AmpGc w.1 w.2.2 w.2.1)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1) :
    Measurable (fun w : ℝ × Point n × Point n =>
      deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1) := by
  classical
  -- (i) the raw `∂_τ` kernel equals the S-re-gated τ representative.
  have hrw : (fun w : ℝ × Point n × Point n =>
        deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1)
      = QIQTH.HgateSatAudit.gatedTauRepProdS g gi hC hK S a b Cfield := by
    funext w
    exact QIQTH.HgateSatAudit.witnessTauDeriv_eq_gatedTauRepProdS hn g gi hC hK S a b Cfield hgate w
  rw [hrw]
  -- (ii) on the gate the re-gated τ body equals the `Gc`/`AmpGc` body.
  have hEq : QIQTH.HgateSatAudit.gatedTauRepProdS g gi hC hK S a b Cfield
      = Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
          (fun w =>
            ((∑ i, ((Gc (w.2.2, w.2.1) i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1)))
                  * gaussDdim w.1 (Gc (w.2.2, w.2.1)))
                * AmpGc w.1 w.2.2 w.2.1
              + gaussDdim w.1 (Gc (w.2.2, w.2.1)) * Cfield w.2.2 w.2.1) := by
    funext w
    unfold QIQTH.HgateSatAudit.gatedTauRepProdS
    by_cases hw : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
    · have hmem : w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} := hw
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
          hChartAgree w hw.1 hw.2, hAmpAgree w hw.1 hw.2]
    · have hnmem : w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} := hw
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmem]
  rw [hEq]
  -- (iii) the `Gc` τ body is globally Borel.
  have hGcV : Measurable (fun w : ℝ × Point n × Point n => Gc (w.2.2, w.2.1)) :=
    hGcMeas.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  have hG : Measurable (fun w : ℝ × Point n × Point n => gaussDdim w.1 (Gc (w.2.2, w.2.1))) :=
    QIQTH.InnerKernelJointMeas.gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hGcV)
  have hCoef : Measurable (fun w : ℝ × Point n × Point n =>
      ∑ i, ((Gc (w.2.2, w.2.1) i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) := by
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    have h1 : Measurable (fun w : ℝ × Point n × Point n =>
        (Gc (w.2.2, w.2.1) i) ^ 2 / (4 * w.1 ^ 2)) :=
      (((measurable_pi_apply i).comp hGcV).pow_const 2).div
        (measurable_const.mul (measurable_fst.pow_const 2))
    have h2 : Measurable (fun w : ℝ × Point n × Point n => (1 : ℝ) / (2 * w.1)) :=
      measurable_const.div (measurable_const.mul measurable_fst)
    exact h1.sub h2
  exact (((hCoef.mul hG).mul hAmpGcMeas).add (hG.mul hCmeas)).indicator hKSmeas

/-! ###############################################################################
    ### §C — ★★ THE SIDESTEP: S1 for the concrete witness, DIRECT via the surface (chart-wall-free).
    ############################################################################### -/

/-- **★★★ `tripleHEmeas_Gc` — S1 FOR THE CONCRETE WITNESS, `Gc`-ROUTE, CHART-WALL-FREE.**  The triple
    `hEmeas` (S1) `HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness …)` assembled DIRECTLY
    through `HEmeasBorelAudit.tripleHEmeas_of_surface` from the three `Gc`-route conjunct mirrors:
      • conjunct (1) `∂_τ`  — `tauDeriv_prod_measurable_Gc` (§B);
      • conjunct (2) first field-`pd` ∀ k — `AmpPdComposition.firstFieldPd_prod_measurable_Gc` (J4-240);
      • conjunct (3) mixed second field-`pd` ∀ i j — `secondFieldPd_prod_measurable_Gc` (§A);
      • conjuncts (4)/(5) `gi` / `christoffel` — `hgi` / `hchr`.
    The chart symbol is carried ONLY through the globally measurable regional flow-inverse `Gc` and the
    on-gate value AGREEMENTS (`hChartAgree`/`hAmpAgree`, shared; the amp-`pd` twin agreements per carrier)
    — the raw off-image joint chart measurability (`.choose` wall) NEVER appears.  Every carrier is
    SATISFIABLE at the concrete flow-ball gate: S-membership is a HYPOTHESIS (conditional `hgate`),
    `hKSmeas` is the (open flow-ball ∩ compact-`K`) product-preimage measurable set, `hOffS`/`hOffS2` are
    the radialCutoff-support vanishings, and `Gc`/`AmpGc`/`Afield…`/`Bfield` are the banked regional
    flow-inverse + amplitude value / `pd` twins.  NONE forces `K = ∅`.  Continuity-free.

    This is the S1 SIDESTEP: it discharges the exact slot `htriple` of `RightInverseGeneral.
    a1_R6_assembled_v2'` WITHOUT restating any ~130-binder capstone existential, and WITHOUT the raw
    chart wall of `ChartJetHessianMixed.tripleHEmeas_concrete` (J4-218, vacuous) or the RAW-chart
    `GatedRepSFix.tripleHEmeas_concrete_v4`.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_Gc (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Gc : Point n × Point n → Point n) (AmpGc : ℝ → Point n → Point n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hGcMeas : Measurable Gc)
    (hAmpGcMeas : Measurable (fun w : ℝ × Point n × Point n => AmpGc w.1 w.2.2 w.2.1))
    (hChartAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
    (hAmpAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 = AmpGc w.1 w.2.2 w.2.1)
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ (Pfield : Point n → Point n → Fin n → ℝ)
        (Afield : ℝ → Point n → Point n → ℝ),
        (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable (fun w : ℝ × Point n × Point n => Afield w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
            pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1 = Afield w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0))
    (hcarField2 : ∀ i j : Fin n, ∃ (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
        (AfieldI AfieldJ Bfield : ℝ → Point n → Point n → ℝ),
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable (fun w : ℝ × Point n × Point n => AfieldI w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => AfieldJ w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Bfield w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
            pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 = AfieldI w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
            pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1 = AfieldJ w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
            pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1
              = Bfield w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
              = 0))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hC hK S a b) := by
  refine QIQTH.HEmeasBorelAudit.tripleHEmeas_of_surface g gi
    (vanVleckGatedWitness g gi hC hK S a b) ⟨?_, ?_, ?_, hgi, hchr⟩
  · -- conjunct (1): `∂_τ` via §B.
    obtain ⟨Cfield, hCmeas, hgateTau⟩ := hcarTau
    exact (tauDeriv_prod_measurable_Gc hn g gi hC hK S a b Cfield Gc AmpGc hKSmeas hGcMeas hCmeas
      hAmpGcMeas hChartAgree hAmpAgree hgateTau).stronglyMeasurable
  · -- conjunct (2): first field-`pd` ∀ k via J4-240 §C.
    intro k
    obtain ⟨Pfield, Afield, hPmeas, hAfieldMeas, hPdAgree, hgate, hOffS⟩ := hcarField k
    exact (QIQTH.AmpPdComposition.firstFieldPd_prod_measurable_Gc hn g gi hC hK S a b k Pfield Gc
      AmpGc Afield hKSmeas hGcMeas hPmeas hAmpGcMeas hAfieldMeas hChartAgree hAmpAgree hPdAgree
      hgate hOffS).stronglyMeasurable
  · -- conjunct (3): mixed second field-`pd` ∀ i j via §A.
    intro i j
    obtain ⟨Pifield, Pjfield, Qfield, AfieldI, AfieldJ, Bfield, hPimeas, hPjmeas, hQmeas,
      hAfieldIMeas, hAfieldJMeas, hBfieldMeas, hPdiAgree, hPdjAgree, hPd2Agree, hgate, hOffS2⟩ :=
      hcarField2 i j
    exact (secondFieldPd_prod_measurable_Gc hn g gi hC hK S a b i j Pifield Pjfield Qfield Gc AmpGc
      AfieldI AfieldJ Bfield hKSmeas hGcMeas hPimeas hPjmeas hQmeas hAmpGcMeas hAfieldIMeas
      hAfieldJMeas hBfieldMeas hChartAgree hAmpAgree hPdiAgree hPdjAgree hPd2Agree
      hgate hOffS2).stronglyMeasurable

end QIQTH.GcConsumerMirror

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GcConsumerMirror
#print axioms secondFieldPd_prod_measurable_Gc
#print axioms tauDeriv_prod_measurable_Gc
#print axioms tripleHEmeas_Gc
end AxiomChecks
