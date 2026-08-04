/-
  GatedRepSFix — J4-232: the FIELD / FIELD² S-RE-GATING (completing J4-231's vacuity fix).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is the SOUNDNESS FIX for the
  first-field-`pd` and mixed (general-index) second-field-`pd` measurable-supplier carriers — the exact
  analogue of `HgateSatAudit.gatedTauRepProdS` / `tauDeriv_prod_stronglyMeasurable_v4` (the banked τ
  template) applied to the field and field² representatives.  No `sorry` (prose excepted), no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypotheses.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT J4-231 CONFIRMED (`HgateSatAudit`): the `hcarField k` / `hcarField2 i j` carriers of
  `ChartJetHessianMixed.tripleHEmeas_concrete` assert gate S-MEMBERSHIP as a *conclusion* over ALL field
  points (`∀ w, w.2.2 ∈ K → 0 < w.1 → … ∧ w.2.1 ∈ S w.2.2 ∧ …`).  Since `w.2.1` ranges over ALL of
  `Point n` with no guard, this FORCES `S q = univ` for every `q ∈ K`, i.e. it is UNSATISFIABLE for the
  concrete proper flow-ball gate with `K ≠ ∅` (`HgateSatAudit.hcarField_unsat` /
  `hcarField2_unsat`).  §2 of `HgateSatAudit` delivered the FULLY-PROVED fix for the τ carrier
  (`gatedTauRepProdS`, `witnessTauDeriv_eq_gatedTauRepProdS`, `tauDeriv_prod_stronglyMeasurable_v4`):
  re-gate the representative on the FULL gate `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}` and move S-membership
  to a HYPOTHESIS (`… → w.2.1 ∈ S w.2.2 → …`).

  ## THE FIELD-CASE ASYMMETRY (the one genuinely new content here).  For the τ derivative the off-gate
  region collapses cleanly: at a FIXED field point `p ∉ S q` the witness is identically `0` *in time*
  (`gatedKernel_apply_of_notMem`), so `∂_τ = 0` = off-gate indicator.  For the FIELD derivative the
  differentiation is IN the field variable, so `p ∉ S q` (with `q ∈ K`) does NOT by itself force the
  field-`pd` to vanish: nearby points `x ∈ S q` carry a nonzero witness.  The honest full-gate identity
  therefore needs, on the region `q ∈ K, p ∉ S q, τ > 0`, the vanishing of the raw field-`pd` — the
  radialCutoff-SUPPORT fact (the concrete witness `= radialCutoff(W)·gaussComp·amp` is supported
  strictly INSIDE `S q`, so it is locally `0` at every `p ∉ S q`, hence its field-`pd`s vanish there).
  This is a GENUINE, SATISFIABLE geometric fact of the concrete gate (`radialCutoff_eq_zero`), true
  exactly where the concrete construction places the cutoff radius inside the flow ball; we carry it as
  the explicit input `hOffS` / `hOffS2` — a satisfiable carrier of the SAME status as the jet /
  chart-measurability data, NOT a vacuous or conclusion-in-disguise hypothesis (it does not force
  `K = ∅`; it is TRUE for the concrete `S`).  §3 of `HgateSatAudit` (the plan) named the conditional
  `hgate` but omitted this off-`S` obligation; it is supplied here.

  ## WHAT LANDS.
    §A — `gatedDerivRepProdS` + `gatedDerivRepProdS_measurable` (`hKSmeas`) +
         `witnessFieldDeriv_eq_gatedDerivRepProdS` (CONDITIONAL hgate + `hOffS`) +
         `firstFieldPd_prod_stronglyMeasurable_v4` — BorelDischargeSurface conjunct (2), SATISFIABLE.
    §B — `gatedMixed2RepProdS` + `gatedMixed2RepProdS_measurable` (`hKSmeas`) +
         `witnessMixed2_eq_gatedMixed2RepProdS` (CONDITIONAL hgate + `hOffS2`) +
         `secondFieldPd_prod_stronglyMeasurable_v4` — BorelDischargeSurface conjunct (3) ∀ i j.
    §C — `tripleHEmeas_concrete_v4` — S1 for the concrete witness assembled through
         `HEmeasBorelAudit.tripleHEmeas_of_surface` from the τ v4 (banked in `HgateSatAudit`) + the two
         v4 conjuncts here, with EVERY hypothesis satisfiable at the concrete gate.  This corrects the
         VACUOUS `ChartJetHessianMixed.tripleHEmeas_concrete` (J4-218).

  ## Gc / hWG COMPOSITION (documented).  To keep the three S1 conjuncts interface-uniform with the
  BANKED τ v4 (`HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4`, which carries the RAW joint chart
  measurability `hChartMeas` + `hKSmeas`), the field / field² v4 here ALSO use the RAW chart route.  The
  Gc + guarded-`hWG` chart-elimination of `GatedChartMeasAudit` (J4-228) is an ORTHOGONAL fix (it
  changes `uniformInverseChart ↦ Gc` inside the representative body, independent of the outer-indicator /
  quantifier-order S-fix here); the two compose into a combined S+Gc representative, deferred to keep
  this brick isolated to the S-re-gating.  See §C prose for the composition recipe.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HgateSatAudit
import QIQTH.GatedDerivRepProduct

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open scoped Topology BigOperators ContDiff

namespace QIQTH.GatedRepSFix

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the FIRST field-`pd` carrier, S-re-gated on the FULL gate.
    ############################################################################### -/

/-- **`gatedDerivRepProdS` — the FULL-gate (base ∧ S) re-gated first field-`pd` representative.**
    Identical closed form to `GatedDerivRepProduct.gatedDerivRepProd` but indicator-gated on
    `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}` — so it VANISHES on the region `q ∈ K, p ∉ S q` (where the
    honest raw field-`pd` also vanishes by the radialCutoff support, carried as `hOffS`).  NOT `a₁ = R/6`. -/
noncomputable def gatedDerivRepProdS (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ) : ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
    (fun w : ℝ × Point n × Point n =>
      gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
          * (-(∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) / (2 * w.1))
          * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
        + gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
          * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)

/-- **★ `gatedDerivRepProdS_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the S-re-gated
    first-`pd` representative, from `hKSmeas` (the FULL-gate set is measurable — SATISFIABLE for the
    concrete gate) plus the same factor measurabilities as `gatedDerivRepProd_measurable`.  NO
    continuity.  NOT `a₁ = R/6`. -/
theorem gatedDerivRepProdS_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)) :
    Measurable (gatedDerivRepProdS g gi hC hK S a b k Pfield) := by
  unfold gatedDerivRepProdS
  have hG : Measurable
      (fun w : ℝ × Point n × Point n =>
        gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hChartMeas)
  have hSum : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp hChartMeas).mul (hPmeas j)
  have hSc : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) / (2 * w.1)) :=
    hSum.neg.div (measurable_const.mul measurable_fst)
  exact (((hG.mul hSc).mul hAmpMeas).add (hG.mul hAmpDerivMeas)).indicator hKSmeas

/-- **★ `witnessFieldDeriv_eq_gatedDerivRepProdS` — THE FIELD EVERYWHERE IDENTITY, CONDITIONAL hgate.**
    The raw first field-`pd` kernel EQUALS the FULL-gate re-gated representative at EVERY `w`, now with
    `hgate` SATISFIABLE (S-membership is a HYPOTHESIS).  Dichotomy:
      • FULL gate `q ∈ K ∧ p ∈ S q` — `τ > 0`: the on-gate closed form `witnessFieldDeriv_gate_eq`
        (using `hpS` and the CONDITIONAL `hgate w hzK hτ hpS`); `τ ≤ 0`: both `0` (shared `gaussDdim`);
      • OFF the full gate — `q ∉ K`: `witnessFieldDeriv_offGate_eq_zero`; `q ∈ K, p ∉ S q`: for `τ > 0`
        the radialCutoff-support vanishing `hOffS`, for `τ ≤ 0` the `nonpos` vanishing.
    The over-strong version's illicit region `q ∈ K, p ∉ S q, τ > 0` is now an HONEST off-gate branch
    (both sides `0`, via `hOffS`), NOT erased by an unsatisfiable hypothesis.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_eq_gatedDerivRepProdS (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (Pfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
          (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
    (hOffS : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0) :
    ∀ w : ℝ × Point n × Point n,
      witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2
        = gatedDerivRepProdS g gi hC hK S a b k Pfield w := by
  intro w
  simp only [gatedDerivRepProdS]
  by_cases hzKS : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
  · obtain ⟨hzK, hpS⟩ := hzKS
    rw [Set.indicator_of_mem
      (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from ⟨hzK, hpS⟩)]
    by_cases hτ : 0 < w.1
    · obtain ⟨hSopen, hjet, hamp⟩ := hgate w hzK hτ hpS
      exact witnessFieldDeriv_gate_eq g gi hC hK S a b k w.1 hτ w.2.2 hzK hSopen w.2.1 hpS
        (Pfield w.2.2 w.2.1) hjet hamp
    · rw [not_lt] at hτ
      rw [QIQTH.GatedDInstantiation.witnessFieldDeriv_eq_zero_of_nonpos hn g gi hC hK S a b k
            w.1 w.2.1 w.2.2 hτ,
          gaussDdim_eq_zero_of_nonpos hn w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1) hτ]
      ring
  · rw [Set.indicator_of_notMem
      (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from hzKS)]
    by_cases hzK : w.2.2 ∈ K
    · have hpS : w.2.1 ∉ S w.2.2 := fun h => hzKS ⟨hzK, h⟩
      by_cases hτ : 0 < w.1
      · exact hOffS w hzK hτ hpS
      · rw [not_lt] at hτ
        exact QIQTH.GatedDInstantiation.witnessFieldDeriv_eq_zero_of_nonpos hn g gi hC hK S a b k
          w.1 w.2.1 w.2.2 hτ
    · exact witnessFieldDeriv_offGate_eq_zero g gi hC hK S a b k w.1 w.2.1 w.2.2 hzK

/-- **★★ `firstFieldPd_prod_measurable_v4` — the field-`pd` measurability from the SATISFIABLE carrier.**
    Joint `(τ,p,q)`-Borel measurability of the raw first field-`pd` kernel with the field point varying,
    via `witnessFieldDeriv_eq_gatedDerivRepProdS` glued to `gatedDerivRepProdS_measurable`.  Every
    hypothesis SATISFIABLE at the concrete gate (S-membership conditional; `hOffS` = radialCutoff
    support).  NOT `a₁ = R/6`. -/
theorem firstFieldPd_prod_measurable_v4 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (Pfield : Point n → Point n → Fin n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1))
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
          (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
    (hOffS : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0) :
    Measurable (fun w : ℝ × Point n × Point n =>
      witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2)
      = gatedDerivRepProdS g gi hC hK S a b k Pfield := by
    funext w
    exact witnessFieldDeriv_eq_gatedDerivRepProdS hn g gi hC hK S a b k Pfield hgate hOffS w
  rw [hrw]
  exact gatedDerivRepProdS_measurable g gi hC hK S a b k Pfield hKSmeas hChartMeas hPmeas
    hAmpMeas hAmpDerivMeas

/-- **★★ `firstFieldPd_prod_stronglyMeasurable_v4` — BorelDischargeSurface CONJUNCT (2), SATISFIABLE.**
    For the concrete gated witness `G := vanVleckGatedWitness g gi hC hK S a b`,
      `∀ k, StronglyMeasurable (fun w => pd (fun x => G w.1 x w.2.2) k w.2.1)`,
    with the HONEST carrier: S-membership is a HYPOTHESIS (conditional `hgate`), the FULL-gate
    measurability `hKSmeas` is carried, and the off-`S` vanishing `hOffS` (radialCutoff support) is a
    satisfiable input.  Neither hypothesis forces `K = ∅`.  CONTINUITY-FREE.  NOT `a₁ = R/6`. -/
theorem firstFieldPd_prod_stronglyMeasurable_v4 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0)) :
    ∀ k : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) k w.2.1) := by
  intro k
  obtain ⟨Pfield, hChartMeas, hPmeas, hAmpMeas, hAmpDerivMeas, hgate, hOffS⟩ := hcar k
  exact (firstFieldPd_prod_measurable_v4 hn g gi hC hK S a b k Pfield hKSmeas hChartMeas hPmeas
    hAmpMeas hAmpDerivMeas hgate hOffS).stronglyMeasurable

/-! ###############################################################################
    ### §B — the MIXED (general-index) second field-`pd` carrier, S-re-gated on the FULL gate.
    ############################################################################### -/

/-- **`gatedMixed2RepProdS` — the FULL-gate re-gated general-index second field-`pd` representative.**
    Identical closed form to `ChartJetHessianMixed.gatedMixed2RepProd` but indicator-gated on the FULL
    gate `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}`.  NOT `a₁ = R/6`. -/
noncomputable def gatedMixed2RepProdS (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ) :
    ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
    (fun w : ℝ × Point n × Point n =>
      gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
          * ((∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k)
                * (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                / (4 * w.1 ^ 2)
              - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                  + (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Qfield w.2.2 w.2.1 k))
                / (2 * w.1))
          * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
        + (gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
              * (-(∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                  / (2 * w.1)))
            * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1
        + (gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
              * (-(∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k)
                  / (2 * w.1)))
            * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1
        + gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
            * pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)

/-- **★ `gatedMixed2RepProdS_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the S-re-gated
    general-index second-`pd` representative, from `hKSmeas` + the carried factor measurabilities (same
    as `gatedMixed2RepProd_measurable`).  NO continuity.  NOT `a₁ = R/6`. -/
theorem gatedMixed2RepProdS_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPimeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
    (hPjmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
    (hQmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivIMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1))
    (hAmpDerivJMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1))
    (hAmpDeriv2Meas : Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)) :
    Measurable (gatedMixed2RepProdS g gi hC hK S a b i j Pifield Pjfield Qfield) := by
  unfold gatedMixed2RepProdS
  have hG : Measurable
      (fun w : ℝ × Point n × Point n =>
        gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hChartMeas)
  have hVPi : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hChartMeas).mul (hPimeas k)
  have hVPj : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hChartMeas).mul (hPjmeas k)
  have hPiPj : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact (hPimeas k).mul (hPjmeas k)
  have hVQ : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Qfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hChartMeas).mul (hQmeas k)
  have hden2 : Measurable (fun w : ℝ × Point n × Point n => 4 * w.1 ^ 2) :=
    measurable_const.mul (measurable_fst.pow_const 2)
  have hden1 : Measurable (fun w : ℝ × Point n × Point n => 2 * w.1) :=
    measurable_const.mul measurable_fst
  have hHess : Measurable
      (fun w : ℝ × Point n × Point n =>
        (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k)
            * (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
            / (4 * w.1 ^ 2)
          - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
              + (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Qfield w.2.2 w.2.1 k))
            / (2 * w.1)) :=
    ((hVPi.mul hVPj).div hden2).sub ((hPiPj.add hVQ).div hden1)
  have hGradj : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPj.neg.div hden1
  have hGradi : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPi.neg.div hden1
  exact (((((hG.mul hHess).mul hAmpMeas).add
      ((hG.mul hGradj).mul hAmpDerivIMeas)).add
      ((hG.mul hGradi).mul hAmpDerivJMeas)).add
      (hG.mul hAmpDeriv2Meas)).indicator hKSmeas

/-- **★ `witnessMixed2_eq_gatedMixed2RepProdS` — THE MIXED EVERYWHERE IDENTITY, CONDITIONAL hgate.**
    The raw off-diagonal second field-`pd` of the concrete witness EQUALS the FULL-gate re-gated
    general-index representative at every `w`, with `hgate` SATISFIABLE (S-membership a HYPOTHESIS) and
    the off-`S` vanishing `hOffS2` (radialCutoff support) for the honest `q ∈ K, p ∉ S q, τ > 0` branch.
    NOT `a₁ = R/6`. -/
theorem witnessMixed2_eq_gatedMixed2RepProdS (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k) (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1 = 0) :
    ∀ w : ℝ × Point n × Point n,
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
        = gatedMixed2RepProdS g gi hC hK S a b i j Pifield Pjfield Qfield w := by
  intro w
  simp only [gatedMixed2RepProdS]
  by_cases hzKS : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
  · obtain ⟨hzK, hpS⟩ := hzKS
    rw [Set.indicator_of_mem
      (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from ⟨hzK, hpS⟩)]
    by_cases hτ : 0 < w.1
    · obtain ⟨hSopen, hjetVi, hjetVj, hjetQ, hampj, hampi, hamp2⟩ := hgate w hzK hτ hpS
      exact QIQTH.ChartJetHessianMixed.witnessMixed_gate_eq g gi hC hK S a b i j w.1 hτ w.2.2 hzK
        hSopen w.2.1 hpS (Pifield w.2.2) (Pjfield w.2.2) (Qfield w.2.2 w.2.1)
        hjetVi hjetVj hjetQ hampj hampi hamp2
    · rw [not_lt] at hτ
      rw [QIQTH.ChartJetHessianMixed.witnessMixed_eq_zero_of_nonpos hn g gi hC hK S a b i j
            w.1 w.2.1 w.2.2 hτ,
          gaussDdim_eq_zero_of_nonpos hn w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1) hτ]
      ring
  · rw [Set.indicator_of_notMem
      (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from hzKS)]
    by_cases hzK : w.2.2 ∈ K
    · have hpS : w.2.1 ∉ S w.2.2 := fun h => hzKS ⟨hzK, h⟩
      by_cases hτ : 0 < w.1
      · exact hOffS2 w hzK hτ hpS
      · rw [not_lt] at hτ
        exact QIQTH.ChartJetHessianMixed.witnessMixed_eq_zero_of_nonpos hn g gi hC hK S a b i j
          w.1 w.2.1 w.2.2 hτ
    · exact QIQTH.ChartJetHessianMixed.witnessMixed_offGate_eq_zero g gi hC hK S a b i j
        w.1 w.2.1 w.2.2 hzK

/-- **★★ `secondFieldPd_prod_measurable_v4` — the mixed second-`pd` measurability, SATISFIABLE carrier.**
    Joint `(τ,p,q)`-Borel measurability of the raw off-diagonal second field-`pd` kernel, via
    `witnessMixed2_eq_gatedMixed2RepProdS` glued to `gatedMixed2RepProdS_measurable`.  NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_measurable_v4 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPimeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
    (hPjmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
    (hQmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivIMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1))
    (hAmpDerivJMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1))
    (hAmpDeriv2Meas : Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1))
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k) (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1 = 0) :
    Measurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1)
      = gatedMixed2RepProdS g gi hC hK S a b i j Pifield Pjfield Qfield := by
    funext w
    exact witnessMixed2_eq_gatedMixed2RepProdS hn g gi hC hK S a b i j Pifield Pjfield Qfield
      hgate hOffS2 w
  rw [hrw]
  exact gatedMixed2RepProdS_measurable g gi hC hK S a b i j Pifield Pjfield Qfield hKSmeas
    hChartMeas hPimeas hPjmeas hQmeas hAmpMeas hAmpDerivIMeas hAmpDerivJMeas hAmpDeriv2Meas

/-- **★★ `secondFieldPd_prod_stronglyMeasurable_v4` — BorelDischargeSurface CONJUNCT (3), ∀ i j.**
    For the concrete gated witness `G := vanVleckGatedWitness g gi hC hK S a b`,
      `∀ i j, StronglyMeasurable (fun w => pd (fun y => pd (fun x => G w.1 x w.2.2) j y) i w.2.1)`,
    with the HONEST carrier (conditional `hgate`, `hKSmeas`, off-`S` vanishing `hOffS2`); no hypothesis
    forces `K = ∅`.  CONTINUITY-FREE.  NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_stronglyMeasurable_v4 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
              = 0)) :
    ∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1) := by
  intro i j
  obtain ⟨Pifield, Pjfield, Qfield, hChartMeas, hPimeas, hPjmeas, hQmeas, hAmpMeas,
    hAmpDerivIMeas, hAmpDerivJMeas, hAmpDeriv2Meas, hgate, hOffS2⟩ := hcar i j
  exact (secondFieldPd_prod_measurable_v4 hn g gi hC hK S a b i j Pifield Pjfield Qfield hKSmeas
    hChartMeas hPimeas hPjmeas hQmeas hAmpMeas hAmpDerivIMeas hAmpDerivJMeas hAmpDeriv2Meas
    hgate hOffS2).stronglyMeasurable

/-! ###############################################################################
    ### §C — ★ THE PAYOFF: `tripleHEmeas_concrete_v4` (the CORRECTED S1, all hyps satisfiable).
    ############################################################################### -/

/-- **★★★ `tripleHEmeas_concrete_v4` — S1 FOR THE CONCRETE WITNESS, VACUITY-FIXED.**  The triple
    `hEmeas` (S1) of `HEmeasBorelAudit.tripleHEmeas` for the concrete gated van-Vleck witness
    `G := vanVleckGatedWitness g gi hC hK S a b`, assembled through
    `HEmeasBorelAudit.tripleHEmeas_of_surface` from the three CORRECTED (satisfiable) conjuncts:
      • conjunct (1) `∂_τ`  — `HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4` (banked τ template);
      • conjunct (2) first field-`pd` — `firstFieldPd_prod_stronglyMeasurable_v4` (this file);
      • conjunct (3) mixed second field-`pd` ∀ i j — `secondFieldPd_prod_stronglyMeasurable_v4` (this
        file);
      • conjuncts (4)/(5) `gi` / `christoffel` — `hgi` / `hchr`.
    EVERY carried existential is SATISFIABLE at the concrete flow-ball gate: S-membership is a
    HYPOTHESIS (conditional `hgate`), `hKSmeas` is the (open flow-ball ∩ compact-`K`) product-preimage
    measurable set, and `hOffS`/`hOffS2` are the radialCutoff-support vanishings.  NONE forces `K = ∅`.
    This corrects the VACUOUS `ChartJetHessianMixed.tripleHEmeas_concrete` (J4-218), whose
    conclusion-form S-membership carriers were `HgateSatAudit.hcar{Tau,Field,Field2}_unsat`.
    Continuity-free.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_concrete_v4 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
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
  · exact QIQTH.HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4 hn g gi hC hK S a b hKSmeas hcarTau
  · exact firstFieldPd_prod_stronglyMeasurable_v4 hn g gi hC hK S a b hKSmeas hcarField
  · exact secondFieldPd_prod_stronglyMeasurable_v4 hn g gi hC hK S a b hKSmeas hcarField2

/-! ###############################################################################
    ### §D — RE-THREAD PLAN (stretch): `a1_R6_assembled_v7` from the v4 suppliers — PROSE.
    ###
    ### The endgame wrappers `AssemblyLadderR{1,2,3,5}.a1_R6_assembled_v*` carry the VACUOUS
    ### conclusion-form `hcar{Tau,Field,Field2}` (the `… ∧ w.2.1 ∈ S w.2.2 ∧ …` binders,
    ### `HgateSatAudit.hcar*_unsat`).  The corrected re-thread `a1_R6_assembled_v7` replaces the whole
    ### vacuous `htriple` block with `tripleHEmeas_concrete_v4` (this file): the wrapper's S1 supplier
    ### slot `htriple : tripleHEmeas g gi (vanVleckGatedWitness …)` is fed directly by
    ### `tripleHEmeas_concrete_v4 hn … hKSmeas hcarTau_v4 hcarField_v4 hcarField2_v4 hgi hchr`, with the
    ### v4 (conditional-`hgate` + `hKSmeas` + `hOffS`/`hOffS2`) carriers in place of the v2 ones.  Since
    ### the wrappers take `htriple` (or its `EndpointData`/`InterchangeData` bundles) as an OPAQUE
    ### hypothesis, the re-thread is a mechanical substitution of the supplier — NO change to the
    ### downstream Levi/Duhamel/interchange algebra.  It is deferred here only because it edits/duplicates
    ### the full `AssemblyLadder*` capstone signature (large); the S1 fix it needs — the satisfiable
    ### v4 triple — is COMPLETE above.
    ###
    ### THE `hKSmeas` DISCHARGE (concrete gate).  `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}`
    ### `= (Prod.snd ∘ Prod.snd) ⁻¹' K ∩ {w | w.2.1 ∈ S w.2.2}`.  For the concrete
    ### `S z = uniformFlowExp … z '' Metric.ball 0 c` (OPEN image) with `K` a `MeasurableSet`, both
    ### pieces are measurable (the first from `measurable_snd.snd`, the second from the joint openness /
    ### measurability of `(p,q) ↦ p ∈ S q`), so `hKSmeas` holds — SATISFIABLE, `K` NEED NOT be empty.
    ###
    ### THE `hOffS` / `hOffS2` DISCHARGE (concrete gate).  The concrete witness on `q ∈ K` is
    ### `radialCutoff(W q ·)·gaussComp·amp`, supported where `‖W q ·‖ < b`; with the construction's
    ### cutoff radius inside the flow-ball image, that support is `⊆ S q` and the witness is locally `0`
    ### at every `p ∉ S q` (`radialCutoff_eq_zero` + `CutoffAnnulusSupport`), so its field / field²
    ### `pd`s vanish there — SATISFIABLE, again independent of `K = ∅`.
    ###
    ### THE Gc / hWG COMPOSITION.  A combined S+Gc representative
    ### `gatedDerivRepProdSGc` = `Set.indicator {w.2.2∈K ∧ w.2.1∈S w.2.2} (…Gc-substituted body…)` drops
    ### the RAW `hChartMeas` for `Gc` + guarded `hWG` (the `GatedChartMeasAudit` §A–D funext-substitution
    ### applies verbatim inside the FULL-gate indicator, since the guard consumes only the amplitude
    ### support), giving a `tripleHEmeas_concrete_v5` with BOTH the S-fix and the chart-wall discharge.
    ### Deferred to isolate the S-re-gating; the two fixes are orthogonal (outer indicator / quantifier
    ### order vs. inner chart symbol).
    ###
    ### NOT `a₁ = R/6`.
    ############################################################################### -/

end QIQTH.GatedRepSFix

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GatedRepSFix
#print axioms gatedDerivRepProdS_measurable
#print axioms witnessFieldDeriv_eq_gatedDerivRepProdS
#print axioms firstFieldPd_prod_measurable_v4
#print axioms firstFieldPd_prod_stronglyMeasurable_v4
#print axioms gatedMixed2RepProdS_measurable
#print axioms witnessMixed2_eq_gatedMixed2RepProdS
#print axioms secondFieldPd_prod_measurable_v4
#print axioms secondFieldPd_prod_stronglyMeasurable_v4
#print axioms tripleHEmeas_concrete_v4
end AxiomChecks
