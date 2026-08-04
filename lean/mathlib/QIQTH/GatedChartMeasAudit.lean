/-
  GatedChartMeasAudit — J4-228: THE DECISIVE CONSUMER AUDIT of gated-vs-raw chart measurability.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  measurability plumbing audit.  No `sorry` (prose excepted), no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise.  Every carried hypothesis is a genuine MEASURABILITY, a genuine
  on-gate `HasDerivAt` fact, or the GUARDED pointwise chart-agreement `hWG` (a strictly WEAKER supplier
  than the unguarded `hChartRep` of `ChartJointBorel.a1_R6_assembled_v5`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE AUDIT VERDICT.  The four gate-equation representative-measurability consumers
  (`gatedTauRepProd_measurable`, `gatedDerivRepProd_measurable`, `gatedDeriv2RepProd_measurable`,
  `gatedMixed2RepProd_measurable`) all carry a RAW joint chart measurability
    `hChartMeas : Measurable (fun w => uniformInverseChart g gi hC hK w.2.2 w.2.1)`.
  That raw hypothesis is a DEFINITIONAL WALL (the `.choose`-built `uniformInverseChart` forgot the
  inverse off the flow image; `q ↦ Classical.choose (h q)` carries NO measurable-in-`q` structure there).

  AUDIT RESULT = **GATED-SUFFICIENT.**  In every representative body, `hChartMeas` is consumed ONLY for
    (a) the Gaussian envelope `gaussDdim w.1 (W q p)`, and
    (b) the polynomial-in-`W` moment coefficients `∑ (W·P)`, `∑ (W i)²`, `∑ (W·Q)`, …
  BOTH of which appear ONLY inside terms multiplied by an AMPLITUDE factor:
    • the order-`k` "moment" summand is multiplied by `chartFieldAmp` (`= radialCutoff(W)·amp`, which
      VANISHES for `‖W‖ ≥ b` — `radialCutoff_eq_zero`);
    • each "gradient / higher" summand is multiplied by an amplitude coordinate-`pd`
      (`pd chartFieldAmp`, `pd (pd chartFieldAmp)`) or by the carried `Cfield` (the amplitude
      `τ`-derivative) — every one of which likewise carries the `radialCutoff` support.
  `gaussDdim` itself never vanishes (positive Gaussian), but it NEVER stands alone: it is always paired
  with one of those amplitude factors.  Hence the ENTIRE representative equals its `Gc`-substituted twin
  (chart `W` replaced by any measurable joint `Gc` agreeing with `W` wherever the amplitude factor is
  nonzero) — POINTWISE — and the `Gc`-twin is measurable WITHOUT `hChartMeas`.

  ## THE RADII / RIGHT-INVERSE CHAIN (status).  The guard "amplitude factor ≠ 0 ⟹ `W q p = Gc(q,p)`"
  is DISCHARGEABLE from: (1) the BANKED regional flow-inverse `Gc`
  (`ChartRepConstruction.flowInverse_jointMeasurable_regional`, J4-227: `W q (φ_q v) = Gc(q, φ_q v)` for
  `q∈K`, `‖v‖ ≤ ρ`); (2) the support fact `radialCutoff(W q p) ≠ 0 ⟹ ‖W q p‖ < b`; and (3) the GENERAL
  right-inverse germ `‖W q p‖ < b ≤ ρ ⟹ p = φ_q (W q p)` (so `p` lies in the flow image, where `Gc`
  agrees).  Piece (1) is BANKED; piece (3) — the general-field-point right inverse (`chartW0_rightInverse`
  is banked only at the ORIGIN) — is the ONE genuinely-open geometric residue.  We therefore carry the
  combined guard as the explicit, satisfiable hypothesis `hWG`, and prove (`hWG_of_unguarded`) that any
  unguarded joint representative supplies it — certifying `hWG` is strictly WEAKER than
  `a1_R6_assembled_v5`'s `hChartRep`, hence non-vacuous.

  ## WHAT LANDS.  `…_measurable_v2` (all four reps, RAW chart DROPPED for `Gc`+`hWG`); the three
  strong-measurability capstones `…_prod_stronglyMeasurable_v2`; and `tripleHEmeas_concrete_v3` — the S1
  triple `hEmeas` for the concrete van-Vleck witness with the chart-measurability conjunct DISCHARGED
  (regional `Gc` + guarded `hWG`), not carried raw.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetHessianMixed
import QIQTH.ChartRepConstruction

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open scoped Topology BigOperators ContDiff

namespace QIQTH.GatedChartMeasAudit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §0 — non-vacuity bridge: the guarded `hWG` is WEAKER than the unguarded rep.
    ############################################################################### -/

/-- **`hWG_of_unguarded` — the guarded agreement is implied by the unguarded one.**  For ANY guard
    predicate `P`, an unguarded joint representative `Gc` agreeing with the chart on `{w.2.2 ∈ K}`
    supplies the guarded agreement.  This certifies that every `hWG`-style hypothesis below is
    SATISFIABLE (non-vacuous) — strictly WEAKER than `ChartJointBorel.a1_R6_assembled_v5`'s unguarded
    `hChartRep`.  NOT `a₁ = R/6`. -/
theorem hWG_of_unguarded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Gc : Point n × Point n → Point n) (P : ℝ × Point n × Point n → Prop)
    (hAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1)) :
    ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → P w →
      uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1) :=
  fun w hzK _ => hAgree w hzK

/-! ###############################################################################
    ### §A — the τ representative, RAW chart DROPPED (G-c v2).
    ############################################################################### -/

/-- **★★ `gatedTauRepProd_measurable_v2`.**  The τ representative is joint `(τ,p,q)`-Borel measurable
    from a measurable joint `Gc` agreeing with the chart wherever the amplitude/`Cfield` factor is
    nonzero (`hWG`) — the RAW `hChartMeas` is ELIMINATED.  Both terms carry an amplitude-support factor
    (`chartFieldAmp`, resp. the carried `Cfield`); off that support the term vanishes, so the whole
    representative equals its `Gc`-substituted twin pointwise.  NOT `a₁ = R/6`. -/
theorem gatedTauRepProd_measurable_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (Cfield : Point n → Point n → ℝ)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hKmeasSet : MeasurableSet K)
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hCmeas : Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1))
    (hWG : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0 ∨ Cfield w.2.2 w.2.1 ≠ 0) →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1)) :
    Measurable (QIQTH.GatedTauDerivRep.gatedTauRepProd g gi hC hK a b Cfield) := by
  have hGcomp : Measurable (fun w : ℝ × Point n × Point n => Gc (w.2.2, w.2.1)) :=
    hGmeas.comp (measurable_snd.snd.prodMk measurable_snd.fst)
  have hEq : QIQTH.GatedTauDerivRep.gatedTauRepProd g gi hC hK a b Cfield
      = Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K}
          (fun w : ℝ × Point n × Point n =>
            ((∑ i, ((Gc (w.2.2, w.2.1) i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1)))
                  * gaussDdim w.1 (Gc (w.2.2, w.2.1)))
                * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
              + gaussDdim w.1 (Gc (w.2.2, w.2.1)) * Cfield w.2.2 w.2.1) := by
    funext w
    simp only [QIQTH.GatedTauDerivRep.gatedTauRepProd]
    by_cases hzK : w.2.2 ∈ K
    · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK),
          Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
      by_cases hA : chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 = 0
      · by_cases hCf : Cfield w.2.2 w.2.1 = 0
        · rw [hA, hCf]; ring
        · rw [hA, hWG w hzK (Or.inr hCf)]
      · rw [hWG w hzK (Or.inl hA)]
    · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK),
          Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
  rw [hEq]
  have hgaussG : Measurable
      (fun w : ℝ × Point n × Point n => gaussDdim w.1 (Gc (w.2.2, w.2.1))) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hGcomp)
  have hCoef : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ i, ((Gc (w.2.2, w.2.1) i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) := by
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    have h1 : Measurable
        (fun w : ℝ × Point n × Point n => (Gc (w.2.2, w.2.1) i) ^ 2 / (4 * w.1 ^ 2)) :=
      (((measurable_pi_apply i).comp hGcomp).pow_const 2).div
        (measurable_const.mul (measurable_fst.pow_const 2))
    have h2 : Measurable (fun w : ℝ × Point n × Point n => (1 : ℝ) / (2 * w.1)) :=
      measurable_const.div (measurable_const.mul measurable_fst)
    exact h1.sub h2
  exact (((hCoef.mul hgaussG).mul hAmpMeas).add (hgaussG.mul hCmeas)).indicator
    (measurable_snd.snd hKmeasSet)

/-- **★★ `tauDeriv_prod_stronglyMeasurable_v2` — BorelDischargeSurface CONJUNCT (1), Gc-ROUTE.**  The
    `∂_τ` derivative field of the concrete gated van-Vleck witness is strongly measurable from the
    regional `Gc` + guarded `hWG` (RAW chart DROPPED).  The everywhere-identity
    `witnessTauDeriv_eq_gatedTauRepProd` (which uses only the on-gate `HasDerivAt` data, NOT chart
    measurability) glues the raw `∂_τ` kernel to the representative.  NOT `a₁ = R/6`. -/
theorem tauDeriv_prod_stronglyMeasurable_v2 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKmeasSet : MeasurableSet K)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0 ∨ Cfield w.2.2 w.2.1 ≠ 0) →
            uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1) := by
  obtain ⟨Cfield, hAmpMeas, hCmeas, hWG, hgate⟩ := hcar
  have hrw : (fun w : ℝ × Point n × Point n =>
        deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1)
      = QIQTH.GatedTauDerivRep.gatedTauRepProd g gi hC hK a b Cfield := by
    funext w
    exact QIQTH.GatedTauDerivRep.witnessTauDeriv_eq_gatedTauRepProd hn g gi hC hK S a b Cfield hgate w
  rw [hrw]
  exact (gatedTauRepProd_measurable_v2 g gi hC hK a b Cfield Gc hGmeas hKmeasSet hAmpMeas hCmeas
    hWG).stronglyMeasurable

/-! ###############################################################################
    ### §B — the first field-`pd` representative, RAW chart DROPPED (G-a v2).
    ############################################################################### -/

/-- **★★ `gatedDerivRepProd_measurable_v2`.**  The order-1 field representative is measurable from
    `Gc` + guarded `hWG` (RAW `hChartMeas` ELIMINATED).  Term-1 carries `chartFieldAmp`; term-2 carries
    the amplitude coordinate-`pd`; off their common support the representative equals its `Gc`-twin.
    NOT `a₁ = R/6`. -/
theorem gatedDerivRepProd_measurable_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hKmeasSet : MeasurableSet K)
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1))
    (hWG : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0
          ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1 ≠ 0) →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1)) :
    Measurable (QIQTH.GatedDerivRepProduct.gatedDerivRepProd g gi hC hK a b k Pfield) := by
  have hGcomp : Measurable (fun w : ℝ × Point n × Point n => Gc (w.2.2, w.2.1)) :=
    hGmeas.comp (measurable_snd.snd.prodMk measurable_snd.fst)
  have hEq : QIQTH.GatedDerivRepProduct.gatedDerivRepProd g gi hC hK a b k Pfield
      = Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K}
          (fun w : ℝ × Point n × Point n =>
            gaussDdim w.1 (Gc (w.2.2, w.2.1))
                * (-(∑ j, Gc (w.2.2, w.2.1) j * Pfield w.2.2 w.2.1 j) / (2 * w.1))
                * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
              + gaussDdim w.1 (Gc (w.2.2, w.2.1))
                * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1) := by
    funext w
    simp only [QIQTH.GatedDerivRepProduct.gatedDerivRepProd]
    by_cases hzK : w.2.2 ∈ K
    · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK),
          Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
      by_cases hA : chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 = 0
      · by_cases hPd : pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1 = 0
        · rw [hA, hPd]; ring
        · rw [hA, hWG w hzK (Or.inr hPd)]
      · rw [hWG w hzK (Or.inl hA)]
    · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK),
          Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
  rw [hEq]
  have hgaussG : Measurable
      (fun w : ℝ × Point n × Point n => gaussDdim w.1 (Gc (w.2.2, w.2.1))) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hGcomp)
  have hSum : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ j, Gc (w.2.2, w.2.1) j * Pfield w.2.2 w.2.1 j) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp hGcomp).mul (hPmeas j)
  have hSc : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ j, Gc (w.2.2, w.2.1) j * Pfield w.2.2 w.2.1 j) / (2 * w.1)) :=
    hSum.neg.div (measurable_const.mul measurable_fst)
  exact (((hgaussG.mul hSc).mul hAmpMeas).add (hgaussG.mul hAmpDerivMeas)).indicator
    (measurable_snd.snd hKmeasSet)

/-- **★★ `firstFieldPd_prod_measurable_v2`.**  The raw first field-`pd` kernel of the concrete witness
    is measurable from `Gc` + guarded `hWG`, via the product everywhere identity
    `witnessFieldDeriv_eq_gatedDerivRepProd` glued to `gatedDerivRepProd_measurable_v2`.  NOT `a₁ = R/6`. -/
theorem firstFieldPd_prod_measurable_v2 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (Pfield : Point n → Point n → Fin n → ℝ)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hKmeasSet : MeasurableSet K)
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1))
    (hWG : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0
          ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1 ≠ 0) →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
          (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1) :
    Measurable (fun w : ℝ × Point n × Point n =>
      witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2)
      = QIQTH.GatedDerivRepProduct.gatedDerivRepProd g gi hC hK a b k Pfield := by
    funext w
    exact QIQTH.GatedDerivRepProduct.witnessFieldDeriv_eq_gatedDerivRepProd hn g gi hC hK S a b k
      Pfield hgate w
  rw [hrw]
  exact gatedDerivRepProd_measurable_v2 g gi hC hK a b k Pfield Gc hGmeas hKmeasSet hPmeas
    hAmpMeas hAmpDerivMeas hWG

/-- **★★ `firstFieldPd_prod_stronglyMeasurable_v2` — BorelDischargeSurface CONJUNCT (2), Gc-ROUTE.**
    `∀ k`, the first field-`pd` of the concrete witness is strongly measurable from `Gc` + guarded
    `hWG`.  NOT `a₁ = R/6`. -/
theorem firstFieldPd_prod_stronglyMeasurable_v2 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKmeasSet : MeasurableSet K)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hcar : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1 ≠ 0) →
            uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)) :
    ∀ k : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) k w.2.1) := by
  intro k
  obtain ⟨Pfield, hPmeas, hAmpMeas, hAmpDerivMeas, hWG, hgate⟩ := hcar k
  exact (firstFieldPd_prod_measurable_v2 hn g gi hC hK S a b k Pfield Gc hGmeas hKmeasSet hPmeas
    hAmpMeas hAmpDerivMeas hWG hgate).stronglyMeasurable

/-! ###############################################################################
    ### §C — the DIAGONAL order-2 representative, RAW chart DROPPED (G-b diagonal v2).
    ############################################################################### -/

/-- **★★ `gatedDeriv2RepProd_measurable_v2`.**  The diagonal order-2 field representative is measurable
    from `Gc` + guarded `hWG` (RAW `hChartMeas` ELIMINATED); the three summands carry `chartFieldAmp`,
    `pd chartFieldAmp`, and `pd (pd chartFieldAmp)` respectively.  NOT `a₁ = R/6`. -/
theorem gatedDeriv2RepProd_measurable_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Point n → Fin n → ℝ)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hKmeasSet : MeasurableSet K)
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hQmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1))
    (hAmpDeriv2Meas : Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) i w.2.1))
    (hWG : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0
          ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ≠ 0
          ∨ pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) i w.2.1 ≠ 0) →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1)) :
    Measurable (QIQTH.GatedDerivRepProduct.gatedDeriv2RepProd g gi hC hK a b i Pfield Qfield) := by
  have hGcomp : Measurable (fun w : ℝ × Point n × Point n => Gc (w.2.2, w.2.1)) :=
    hGmeas.comp (measurable_snd.snd.prodMk measurable_snd.fst)
  have hEq : QIQTH.GatedDerivRepProduct.gatedDeriv2RepProd g gi hC hK a b i Pfield Qfield
      = Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K}
          (fun w : ℝ × Point n × Point n =>
            gaussDdim w.1 (Gc (w.2.2, w.2.1))
                * ((∑ j, Gc (w.2.2, w.2.1) j * Pfield w.2.2 w.2.1 j) ^ 2
                      / (4 * w.1 ^ 2)
                    - ((∑ j, Pfield w.2.2 w.2.1 j ^ 2)
                        + (∑ j, Gc (w.2.2, w.2.1) j * Qfield w.2.2 w.2.1 j))
                      / (2 * w.1))
                * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
              + 2 * (gaussDdim w.1 (Gc (w.2.2, w.2.1))
                    * (-(∑ j, Gc (w.2.2, w.2.1) j * Pfield w.2.2 w.2.1 j)
                        / (2 * w.1)))
                  * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1
              + gaussDdim w.1 (Gc (w.2.2, w.2.1))
                  * pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) i w.2.1) := by
    funext w
    simp only [QIQTH.GatedDerivRepProduct.gatedDeriv2RepProd]
    by_cases hzK : w.2.2 ∈ K
    · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK),
          Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
      by_cases hA : chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 = 0
      · by_cases hD1 : pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 = 0
        · by_cases hD2 : pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) i w.2.1 = 0
          · rw [hA, hD1, hD2]; ring
          · rw [hA, hD1, hWG w hzK (Or.inr (Or.inr hD2))]
        · rw [hA, hWG w hzK (Or.inr (Or.inl hD1))]
      · rw [hWG w hzK (Or.inl hA)]
    · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK),
          Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
  rw [hEq]
  have hgaussG : Measurable
      (fun w : ℝ × Point n × Point n => gaussDdim w.1 (Gc (w.2.2, w.2.1))) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hGcomp)
  have hVP : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ j, Gc (w.2.2, w.2.1) j * Pfield w.2.2 w.2.1 j) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp hGcomp).mul (hPmeas j)
  have hPP : Measurable
      (fun w : ℝ × Point n × Point n => ∑ j, Pfield w.2.2 w.2.1 j ^ 2) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact (hPmeas j).pow_const 2
  have hVQ : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ j, Gc (w.2.2, w.2.1) j * Qfield w.2.2 w.2.1 j) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp hGcomp).mul (hQmeas j)
  have hden2 : Measurable (fun w : ℝ × Point n × Point n => 4 * w.1 ^ 2) :=
    measurable_const.mul (measurable_fst.pow_const 2)
  have hden1 : Measurable (fun w : ℝ × Point n × Point n => 2 * w.1) :=
    measurable_const.mul measurable_fst
  have hHess : Measurable
      (fun w : ℝ × Point n × Point n =>
        (∑ j, Gc (w.2.2, w.2.1) j * Pfield w.2.2 w.2.1 j) ^ 2
            / (4 * w.1 ^ 2)
          - ((∑ j, Pfield w.2.2 w.2.1 j ^ 2)
              + (∑ j, Gc (w.2.2, w.2.1) j * Qfield w.2.2 w.2.1 j))
            / (2 * w.1)) :=
    ((hVP.pow_const 2).div hden2).sub ((hPP.add hVQ).div hden1)
  have hGrad : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ j, Gc (w.2.2, w.2.1) j * Pfield w.2.2 w.2.1 j) / (2 * w.1)) :=
    hVP.neg.div hden1
  exact ((((hgaussG.mul hHess).mul hAmpMeas).add
      ((measurable_const.mul (hgaussG.mul hGrad)).mul hAmpDerivMeas)).add
      (hgaussG.mul hAmpDeriv2Meas)).indicator (measurable_snd.snd hKmeasSet)

/-! ###############################################################################
    ### §D — the MIXED (general-index) order-2 representative, RAW chart DROPPED (G-b mixed v2).
    ############################################################################### -/

/-- **★★ `gatedMixed2RepProd_measurable_v2`.**  The general-index order-2 field representative is
    measurable from `Gc` + guarded `hWG` (RAW `hChartMeas` ELIMINATED); the four summands carry
    `chartFieldAmp`, `pd_i chartFieldAmp`, `pd_j chartFieldAmp`, and `pd_i (pd_j chartFieldAmp)`.
    NOT `a₁ = R/6`. -/
theorem gatedMixed2RepProd_measurable_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hKmeasSet : MeasurableSet K)
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
    (hWG : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0
          ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ≠ 0
          ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1 ≠ 0
          ∨ pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1 ≠ 0) →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1)) :
    Measurable (QIQTH.ChartJetHessianMixed.gatedMixed2RepProd g gi hC hK a b i j
      Pifield Pjfield Qfield) := by
  have hGcomp : Measurable (fun w : ℝ × Point n × Point n => Gc (w.2.2, w.2.1)) :=
    hGmeas.comp (measurable_snd.snd.prodMk measurable_snd.fst)
  have hEq : QIQTH.ChartJetHessianMixed.gatedMixed2RepProd g gi hC hK a b i j Pifield Pjfield Qfield
      = Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K}
          (fun w : ℝ × Point n × Point n =>
            gaussDdim w.1 (Gc (w.2.2, w.2.1))
                * ((∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k)
                      * (∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k)
                      / (4 * w.1 ^ 2)
                    - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                        + (∑ k, Gc (w.2.2, w.2.1) k * Qfield w.2.2 w.2.1 k))
                      / (2 * w.1))
                * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
              + (gaussDdim w.1 (Gc (w.2.2, w.2.1))
                    * (-(∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k)
                        / (2 * w.1)))
                  * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1
              + (gaussDdim w.1 (Gc (w.2.2, w.2.1))
                    * (-(∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k)
                        / (2 * w.1)))
                  * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1
              + gaussDdim w.1 (Gc (w.2.2, w.2.1))
                  * pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1) := by
    funext w
    simp only [QIQTH.ChartJetHessianMixed.gatedMixed2RepProd]
    by_cases hzK : w.2.2 ∈ K
    · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK),
          Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
      by_cases hA : chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 = 0
      · by_cases hDi : pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 = 0
        · by_cases hDj : pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1 = 0
          · by_cases hD2 :
                pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1 = 0
            · rw [hA, hDi, hDj, hD2]; ring
            · rw [hA, hDi, hDj, hWG w hzK (Or.inr (Or.inr (Or.inr hD2)))]
          · rw [hA, hDi, hWG w hzK (Or.inr (Or.inr (Or.inl hDj)))]
        · rw [hA, hWG w hzK (Or.inr (Or.inl hDi))]
      · rw [hWG w hzK (Or.inl hA)]
    · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK),
          Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
  rw [hEq]
  have hgaussG : Measurable
      (fun w : ℝ × Point n × Point n => gaussDdim w.1 (Gc (w.2.2, w.2.1))) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hGcomp)
  have hVPi : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hGcomp).mul (hPimeas k)
  have hVPj : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hGcomp).mul (hPjmeas k)
  have hPiPj : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact (hPimeas k).mul (hPjmeas k)
  have hVQ : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, Gc (w.2.2, w.2.1) k * Qfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hGcomp).mul (hQmeas k)
  have hden2 : Measurable (fun w : ℝ × Point n × Point n => 4 * w.1 ^ 2) :=
    measurable_const.mul (measurable_fst.pow_const 2)
  have hden1 : Measurable (fun w : ℝ × Point n × Point n => 2 * w.1) :=
    measurable_const.mul measurable_fst
  have hHess : Measurable
      (fun w : ℝ × Point n × Point n =>
        (∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k)
            * (∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k)
            / (4 * w.1 ^ 2)
          - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
              + (∑ k, Gc (w.2.2, w.2.1) k * Qfield w.2.2 w.2.1 k))
            / (2 * w.1)) :=
    ((hVPi.mul hVPj).div hden2).sub ((hPiPj.add hVQ).div hden1)
  have hGradj : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ k, Gc (w.2.2, w.2.1) k * Pjfield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPj.neg.div hden1
  have hGradi : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ k, Gc (w.2.2, w.2.1) k * Pifield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPi.neg.div hden1
  exact (((((hgaussG.mul hHess).mul hAmpMeas).add
      ((hgaussG.mul hGradj).mul hAmpDerivIMeas)).add
      ((hgaussG.mul hGradi).mul hAmpDerivJMeas)).add
      (hgaussG.mul hAmpDeriv2Meas)).indicator (measurable_snd.snd hKmeasSet)

/-- **★★ `secondFieldPd_prod_measurable_v2`.**  The raw off-diagonal second field-`pd` kernel of the
    concrete witness is measurable from `Gc` + guarded `hWG`, via the mixed everywhere identity
    `witnessMixed2_eq_gatedMixed2RepProd` glued to `gatedMixed2RepProd_measurable_v2`.  NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_measurable_v2 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hKmeasSet : MeasurableSet K)
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
    (hWG : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0
          ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ≠ 0
          ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1 ≠ 0
          ∨ pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1 ≠ 0) →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
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
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1) :
    Measurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1)
      = QIQTH.ChartJetHessianMixed.gatedMixed2RepProd g gi hC hK a b i j Pifield Pjfield Qfield := by
    funext w
    exact QIQTH.ChartJetHessianMixed.witnessMixed2_eq_gatedMixed2RepProd hn g gi hC hK S a b i j
      Pifield Pjfield Qfield hgate w
  rw [hrw]
  exact gatedMixed2RepProd_measurable_v2 g gi hC hK a b i j Pifield Pjfield Qfield Gc hGmeas
    hKmeasSet hPimeas hPjmeas hQmeas hAmpMeas hAmpDerivIMeas hAmpDerivJMeas hAmpDeriv2Meas hWG

/-- **★★ `secondFieldPd_prod_stronglyMeasurable_v2` — BorelDischargeSurface CONJUNCT (3), Gc-ROUTE.**
    `∀ i j`, the mixed second field-`pd` of the concrete witness is strongly measurable from `Gc` +
    guarded `hWG`.  NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_stronglyMeasurable_v2 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKmeasSet : MeasurableSet K)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hcar : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
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
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1 ≠ 0
              ∨ pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1 ≠ 0) →
            uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
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
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)) :
    ∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1) := by
  intro i j
  obtain ⟨Pifield, Pjfield, Qfield, hPimeas, hPjmeas, hQmeas, hAmpMeas,
    hAmpDerivIMeas, hAmpDerivJMeas, hAmpDeriv2Meas, hWG, hgate⟩ := hcar i j
  exact (secondFieldPd_prod_measurable_v2 hn g gi hC hK S a b i j Pifield Pjfield Qfield Gc hGmeas
    hKmeasSet hPimeas hPjmeas hQmeas hAmpMeas hAmpDerivIMeas hAmpDerivJMeas hAmpDeriv2Meas hWG
    hgate).stronglyMeasurable

/-! ###############################################################################
    ### §E — ★ THE PAYOFF: the concrete triple `hEmeas` (S1) with the chart wall DISCHARGED.
    ############################################################################### -/

/-- **★★★ `tripleHEmeas_concrete_v3` — S1 FOR THE CONCRETE WITNESS, CHART-MEASURABILITY DISCHARGED.**
    The triple `hEmeas` (S1) of `HEmeasBorelAudit.tripleHEmeas` for the concrete gated van-Vleck witness
    `G := vanVleckGatedWitness g gi hC hK S a b`, with EVERY derivative-field conjunct discharged
    continuity-free AND the raw joint chart measurability ELIMINATED: each supplier existential now
    carries the regional `Gc` + the GUARDED agreement `hWG` (weaker than the unguarded `hChartRep` of
    `a1_R6_assembled_v5`; see `hWG_of_unguarded`) in place of
    `Measurable (fun w => uniformInverseChart …)`.  Assembled through
    `HEmeasBorelAudit.tripleHEmeas_of_surface`.  This certifies the AUDIT VERDICT: the gate-equation
    representative-measurability tower needs the chart only on the AMPLITUDE SUPPORT (where `W = Gc`),
    never the raw off-image joint chart.  Continuity-free.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_concrete_v3 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKmeasSet : MeasurableSet K)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0 ∨ Cfield w.2.2 w.2.1 ≠ 0) →
            uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1 ≠ 0) →
            uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
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
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1 ≠ 0
              ∨ pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1 ≠ 0) →
            uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
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
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hC hK S a b) := by
  refine QIQTH.HEmeasBorelAudit.tripleHEmeas_of_surface g gi
    (vanVleckGatedWitness g gi hC hK S a b) ⟨?_, ?_, ?_, hgi, hchr⟩
  · exact tauDeriv_prod_stronglyMeasurable_v2 hn g gi hC hK S a b hKmeasSet Gc hGmeas hcarTau
  · exact firstFieldPd_prod_stronglyMeasurable_v2 hn g gi hC hK S a b hKmeasSet Gc hGmeas hcarField
  · exact secondFieldPd_prod_stronglyMeasurable_v2 hn g gi hC hK S a b hKmeasSet Gc hGmeas hcarField2

end QIQTH.GatedChartMeasAudit

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GatedChartMeasAudit
#print axioms hWG_of_unguarded
#print axioms gatedTauRepProd_measurable_v2
#print axioms tauDeriv_prod_stronglyMeasurable_v2
#print axioms gatedDerivRepProd_measurable_v2
#print axioms firstFieldPd_prod_measurable_v2
#print axioms firstFieldPd_prod_stronglyMeasurable_v2
#print axioms gatedDeriv2RepProd_measurable_v2
#print axioms gatedMixed2RepProd_measurable_v2
#print axioms secondFieldPd_prod_measurable_v2
#print axioms secondFieldPd_prod_stronglyMeasurable_v2
#print axioms tripleHEmeas_concrete_v3
end AxiomChecks
