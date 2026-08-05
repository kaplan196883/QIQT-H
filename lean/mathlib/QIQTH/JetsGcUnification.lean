/-
  JetsGcUnification — J4-248: the jets + `Gc` unification (map item [8]).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It ASSEMBLES the
  three `Gc`-flavored existential CARRIERS of `QIQTH.GcConsumerMirror.tripleHEmeas_Gc` — `hcarTau`,
  `hcarField`, `hcarField2` — CONCRETELY at the concrete flow-ball gate from already-banked pieces, and
  then internalizes them into the S1 triple `HEmeasBorelAudit.tripleHEmeas` for the concrete gated
  van-Vleck witness.  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypotheses.  No existing file is edited.

  ## WHAT FEEDS EACH CARRIER (all banked, all `std-3`).
    • `hcarTau_Gc_concrete`  — Cfield := `ChartRepFinal.chartTauAmpGc … Gc` (measurable via
        `chartTauAmpGc_prod_measurable`); the on-gate HasDerivAt from `OnGateJets.hcarTau_hasDeriv_concrete`
        with the `Cfield`-value swap `ChartRepFinal.chartFieldTauAmp_eq_chartTauAmpGc_of_agree`.
    • `hcarField_Gc_concrete` — jet twin `Pfield` (measurable + on-gate `HasDerivAt`) from
        `FlowDerivMeasurable.flowInverseJet_measurable_component`; amp-`pd` twin `Afield` from
        `AmpPdComposition.ampFieldPd_measurable`; `IsOpen`/`PdiffAt` from `OnGateJets.hcarField_hgate_concrete`;
        off-`S` from `OffSVanishing.hOffS_concrete`.
    • `hcarField2_Gc_concrete` — the mixed second-jet twins `Pjfield`/`Qfield` and the `i`-direction first-jet
        `Pifield` from `FlowDerivMeasurable.flowInverseSecondJet_measurable_component`; amp-`pd`/`pd²` twins from
        `AmpPdComposition.ampFieldPd_measurable`/`ampFieldSecondPd_measurable`; the amplitude `PdiffAt`
        conjuncts from `Field2NbhdReshape.hcarField2_hgate_concrete`; off-`S` from `OffSVanishing.hOffS2_concrete`.
    • `tripleHEmeas_Gc_concrete` — the shared `Gc`/`AmpGc` + agreements + `hKSmeas` from
        `AmpPdComposition.concreteGate_ampPd_Gc_supplier_FINAL`; the three carriers as above; measurable `gi`
        / `christoffel` as hypotheses; assembled through `GcConsumerMirror.tripleHEmeas_Gc`.

  ## RADII RECONCILIATION.  The banked pieces are returned parametrically as `∃ δ₀ > 0, ∀ c, … c < δ₀ → …`.
  The per-direction (`Fin n`) and per-pair (`Fin n × Fin n`) pieces are turned into a SINGLE uniform radius by
  `exists_forall_radius` (finite `min` over the index type, `Nonempty` from `0 < n`); the file-level radius is
  the `min` of all the pieces' radii.  Requiring `b < c` (with `0 < a < b`) satisfies both the `0 < c` and
  `b < c` gates of the various pieces simultaneously.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GcConsumerMirror
import QIQTH.OnGateJets
import QIQTH.Field2NbhdReshape
import QIQTH.ChartRepFinal
import QIQTH.FlowDerivMeasurable
import QIQTH.AmpPdComposition
import QIQTH.OffSVanishing
import QIQTH.ConcreteGateInstantiation

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open scoped Topology BigOperators ContDiff

namespace QIQTH.JetsGcUnification

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §0 — the finite-`min` radius reconciler.
    ############################################################################### -/

/-- **`exists_forall_radius` — turn a per-index family of radii into a single uniform radius.**  From
    `∀ k, ∃ δ_k > 0, ∀ c, 0 < c → c < δ_k → Q k c` produce `∃ δ > 0, ∀ c, 0 < c → c < δ → ∀ k, Q k c`
    by taking the finite `min` over the (nonempty, finite) index type.  Monotonicity of `Q k ·` in the
    radius is automatic (`c < δ_min ≤ δ_k`).  NOT `a₁ = R/6`. -/
theorem exists_forall_radius {ι : Type*} [Fintype ι] [Nonempty ι] (Q : ι → ℝ → Prop)
    (h : ∀ k : ι, ∃ δ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ → Q k c) :
    ∃ δ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ → ∀ k, Q k c := by
  classical
  choose δ hδ0 hδspec using h
  obtain ⟨kmin, -, hkmin⟩ := Finset.exists_min_image Finset.univ δ Finset.univ_nonempty
  refine ⟨δ kmin, hδ0 kmin, ?_⟩
  intro c hc0 hclt k
  exact hδspec k c hc0 (lt_of_lt_of_le hclt (hkmin k (Finset.mem_univ k)))

/-! ###############################################################################
    ### §1 — `hcarTau_Gc_concrete`  (the `∂_τ` carrier; value swaps + `Cfield` only).
    ############################################################################### -/

/-- **★★ `hcarTau_Gc_concrete` — the `hcarTau` existential of `tripleHEmeas_Gc`, witnessed at the gate.**
    Cfield := the `Gc`-composed `∂_τ` amplitude `ChartRepFinal.chartTauAmpGc … Gc` (globally measurable);
    on the gate its value equals the raw chart `∂_τ` slope (`chartFieldTauAmp_eq_chartTauAmpGc_of_agree`,
    under the on-gate chart agreement `hChartAgree`), so the HasDerivAt block of
    `OnGateJets.hcarTau_hasDeriv_concrete` transfers verbatim.  Works for ANY `S` (no radius).  NOT `a₁ = R/6`. -/
theorem hcarTau_Gc_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (Gc : Point n × Point n → Point n) (hGcMeas : Measurable Gc)
    (hChartAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1)) :
    ∃ Cfield : Point n → Point n → ℝ,
      Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
      ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
          HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
            (Cfield w.2.2 w.2.1) w.1) := by
  refine ⟨QIQTH.ChartRepFinal.chartTauAmpGc g gi a b Gc,
    QIQTH.ChartRepFinal.chartTauAmpGc_prod_measurable g gi hg hgi hgpos a b Gc hGcMeas, ?_⟩
  intro w hqK hτ hpS
  have hHD := QIQTH.OnGateJets.chartFieldAmp_hasDerivAt_tau g gi hC hK a b w.2.2 w.2.1 w.1
  have hEq := QIQTH.ChartRepFinal.chartFieldTauAmp_eq_chartTauAmpGc_of_agree g gi hC hK a b
    w.2.2 w.2.1 Gc (hChartAgree w hqK hpS)
  rwa [hEq] at hHD

/-! ###############################################################################
    ### §2 — `hcarField_Gc_concrete`  (the FIRST-jet carrier).
    ############################################################################### -/

/-- **★★ `hcarField_Gc_concrete` — the `hcarField` existential of `tripleHEmeas_Gc`, at the gate.**
    Per direction `k`: the measurable jet twin `Pfield` (measurability + on-gate `HasDerivAt`) from
    `FlowDerivMeasurable.flowInverseJet_measurable_component`, the amp-`pd` twin `Afield` from
    `AmpPdComposition.ampFieldPd_measurable`, the `IsOpen`/`PdiffAt` on-gate block from
    `OnGateJets.hcarField_hgate_concrete`, and the off-`S` vanishing from `OffSVanishing.hOffS_concrete`.
    Radii reconciled to a single `δ₀` (per-`k` pieces via `exists_forall_radius`).  NOT `a₁ = R/6`. -/
theorem hcarField_Gc_concrete (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ k : Fin n, ∃ (Pfield : Point n → Point n → Fin n → ℝ)
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
              witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- (a) the per-`k` measurable jet twin + on-gate `HasDerivAt`, uniform radius.
  obtain ⟨δP, hδP0, hδPspec⟩ := exists_forall_radius
    (fun k c => ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
          (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              ∀ j, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
                (Pfield w.2.2 w.2.1 j) (w.2.1 k)))
    (fun k => QIQTH.FlowDerivMeasurable.flowInverseJet_measurable_component g gi hC hK k)
  -- (b) the per-`k` measurable amp-`pd` twin + on-gate value, uniform radius.
  obtain ⟨δA, hδA0, hδAspec⟩ := exists_forall_radius
    (fun k c => ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Afield : ℝ → Point n → Point n → ℝ,
          Measurable (fun w : ℝ × Point n × Point n => Afield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              Afield w.1 w.2.2 w.2.1 = pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1))
    (fun k => QIQTH.AmpPdComposition.ampFieldPd_measurable g gi hC hK a b k hg hgi hgpos hu)
  -- (c) the `k`-uniform on-gate `IsOpen`/`PdiffAt` block.
  obtain ⟨δH, hδH0, hδHspec⟩ :=
    QIQTH.OnGateJets.hcarField_hgate_concrete g gi hC hK a b ha hab hg hgpos hu
  -- (d) the `k`-uniform off-`S` vanishing.
  obtain ⟨δO, hδO0, hδOspec⟩ := QIQTH.OffSVanishing.hOffS_concrete g gi hC hK a b ha hab
  refine ⟨min (min δP δA) (min δH δO), lt_min (lt_min hδP0 hδA0) (lt_min hδH0 hδO0), ?_⟩
  intro c hbc hcδ S hSeq k
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcP : c < δP := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcA : c < δA := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcH : c < δH := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcO : c < δO := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Pfield, hPmeas, hPgate⟩ := hδPspec c hc0 hcP k S hSeq
  obtain ⟨Afield, hAmeas, hAval⟩ := hδAspec c hc0 hcA k S hSeq
  have hH := hδHspec c hbc hcH S hSeq k
  have hO := hδOspec c hbc hcO S hSeq k
  obtain ⟨PfieldH, hHgate⟩ := hH
  refine ⟨Pfield, Afield, hPmeas, hAmeas, ?_, ?_, ?_⟩
  · intro w hqK hpS
    exact (hAval w hqK hpS).symm
  · intro w hqK hτ hpS
    exact ⟨(hHgate w hqK hτ hpS).1, hPgate w hqK hτ hpS, (hHgate w hqK hτ hpS).2.2⟩
  · intro w hqK hτ hpS
    exact hO w hqK hτ hpS

/-! ###############################################################################
    ### §3 — `hcarField2_Gc_concrete`  (the MIXED SECOND-jet carrier).
    ############################################################################### -/

/-- **★★ `hcarField2_Gc_concrete` — the `hcarField2` existential of `tripleHEmeas_Gc`, at the gate.**
    Per pair `(i, j)`: the mixed second-jet twins `Pjfield` (direction `j`, `∀ y ∈ S`) + `Qfield`
    (mixed `i`-on-`j`) from `FlowDerivMeasurable.flowInverseSecondJet_measurable_component i j`; the
    `i`-direction first-jet twin `Pifield` from `flowInverseSecondJet_measurable_component i i`; the amp-`pd`
    twins `AfieldI`/`AfieldJ` from `AmpPdComposition.ampFieldPd_measurable` and the mixed `pd²` twin
    `Bfield` from `ampFieldSecondPd_measurable`; the amplitude `PdiffAt` conjuncts from
    `Field2NbhdReshape.hcarField2_hgate_concrete`; the off-`S` vanishing from
    `OffSVanishing.hOffS2_concrete`.  Radii reconciled via `exists_forall_radius` (single directions over
    `Fin n`, pairs over `Fin n × Fin n`).  NOT `a₁ = R/6`. -/
theorem hcarField2_Gc_concrete (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ i j : Fin n, ∃ (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
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
                = 0) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  -- (a) per-pair mixed second-jet block (Pjfield dir j, ∀y; Qfield mixed i-on-j).
  obtain ⟨δM, hδM0, hδMspec⟩ := exists_forall_radius
    (fun p : Fin n × Fin n => fun c => ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Pjfield Qfield : Point n → Point n → Fin n → ℝ,
          (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
          ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              IsOpen (S w.2.2) ∧
              (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y p.2 s) k)
                (Pjfield w.2.2 y k) (y p.2)) ∧
              (∀ k, HasDerivAt
                (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 p.1 s) k)
                (Qfield w.2.2 w.2.1 k) (w.2.1 p.1))))
    (fun p => QIQTH.FlowDerivMeasurable.flowInverseSecondJet_measurable_component g gi hC hK p.1 p.2)
  -- (b) per-direction first-jet ∀y block (extracted from the `(d,d)` second-jet component).
  obtain ⟨δF, hδF0, hδFspec⟩ := exists_forall_radius
    (fun d : Fin n => fun c => ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
          (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 k))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y d s) k)
                (Pfield w.2.2 y k) (y d))))
    (fun d => by
      obtain ⟨δ, hδ, hspec⟩ :=
        QIQTH.FlowDerivMeasurable.flowInverseSecondJet_measurable_component g gi hC hK d d
      refine ⟨δ, hδ, fun c hc0 hcδ S hSeq => ?_⟩
      obtain ⟨Pj, Q', hPjm, _hQ'm, hb⟩ := hspec c hc0 hcδ S hSeq
      exact ⟨Pj, hPjm, fun w hqK hτ hpS => (hb w hqK hτ hpS).2.1⟩)
  -- (c) per-direction amp-`pd` twin.
  obtain ⟨δA, hδA0, hδAspec⟩ := exists_forall_radius
    (fun d : Fin n => fun c => ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Afield : ℝ → Point n → Point n → ℝ,
          Measurable (fun w : ℝ × Point n × Point n => Afield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              Afield w.1 w.2.2 w.2.1 = pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) d w.2.1))
    (fun d => QIQTH.AmpPdComposition.ampFieldPd_measurable g gi hC hK a b d hg hgi hgpos hu)
  -- (d) per-pair mixed `pd²` twin.
  obtain ⟨δB, hδB0, hδBspec⟩ := exists_forall_radius
    (fun p : Fin n × Fin n => fun c => ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Bfield : ℝ → Point n → Point n → ℝ,
          Measurable (fun w : ℝ × Point n × Point n => Bfield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              Bfield w.1 w.2.2 w.2.1
                = pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) p.2 y) p.1 w.2.1))
    (fun p => QIQTH.AmpPdComposition.ampFieldSecondPd_measurable g gi hC hK a b p.1 p.2 hg hgi hgpos hu)
  -- (e) the `(i,j)`-uniform amplitude `PdiffAt` block.
  obtain ⟨δH, hδH0, hδHspec⟩ :=
    QIQTH.Field2NbhdReshape.hcarField2_hgate_concrete g gi hC hK a b ha hab hg hgpos hu
  -- (f) the `(i,j)`-uniform off-`S` vanishing.
  obtain ⟨δO, hδO0, hδOspec⟩ := QIQTH.OffSVanishing.hOffS2_concrete g gi hC hK a b ha hab
  refine ⟨min (min (min δM δF) (min δA δB)) (min δH δO),
    lt_min (lt_min (lt_min hδM0 hδF0) (lt_min hδA0 hδB0)) (lt_min hδH0 hδO0), ?_⟩
  intro c hbc hcδ S hSeq i j
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcM : c < δM := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hcF : c < δF := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hcA : c < δA := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hcB : c < δB := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hcH : c < δH := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcO : c < δO := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Pjfield, Qfield, hPjmeas, hQmeas, hMblock⟩ := hδMspec c hc0 hcM (i, j) S hSeq
  obtain ⟨Pifield, hPimeas, hFblock⟩ := hδFspec c hc0 hcF i S hSeq
  obtain ⟨AfieldI, hAImeas, hAIval⟩ := hδAspec c hc0 hcA i S hSeq
  obtain ⟨AfieldJ, hAJmeas, hAJval⟩ := hδAspec c hc0 hcA j S hSeq
  obtain ⟨Bfield, hBmeas, hBval⟩ := hδBspec c hc0 hcB (i, j) S hSeq
  have hH := hδHspec c hbc hcH S hSeq i j
  have hO := hδOspec c hbc hcO S hSeq i j
  obtain ⟨PiH, PjH, QH, hHblock⟩ := hH
  refine ⟨Pifield, Pjfield, Qfield, AfieldI, AfieldJ, Bfield,
    hPimeas, hPjmeas, hQmeas, hAImeas, hAJmeas, hBmeas, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hqK hpS; exact (hAIval w hqK hpS).symm
  · intro w hqK hpS; exact (hAJval w hqK hpS).symm
  · intro w hqK hpS; exact (hBval w hqK hpS).symm
  · intro w hqK hτ hpS
    refine ⟨(hMblock w hqK hτ hpS).1, hFblock w hqK hτ hpS,
      (hMblock w hqK hτ hpS).2.1, (hMblock w hqK hτ hpS).2.2,
      (hHblock w hqK hτ hpS).2.2.2.2.1,
      (hHblock w hqK hτ hpS).2.2.2.2.2.1,
      (hHblock w hqK hτ hpS).2.2.2.2.2.2⟩
  · intro w hqK hτ hpS; exact hO w hqK hτ hpS

/-! ###############################################################################
    ### §4 — ★ `tripleHEmeas_Gc_concrete`  (the S1 triple with carriers INTERNAL).
    ############################################################################### -/

/-- **★★★ `tripleHEmeas_Gc_concrete` — the `Gc`-route S1 triple, carriers internalized.**  At the concrete
    flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c` (`0 < a < b < c < δ₀`), the S1
    triple `HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness …)` holds, assembled from ONLY:
      • geometry — `hC` (christoffel `C^∞`), `hg`/`hgi`/`hgpos`/`hu` (metric / inverse / positivity / transport);
      • radii — the single reconciled `δ₀` (`min` of the banked pieces' radii; `b < c` covers all gates);
      • measurable-set data — measurable `gi` (`hgiMeas`) and `christoffel` (`hchr`).
    The shared `Gc`/`AmpGc` + on-gate agreements + `hKSmeas` are `AmpPdComposition.concreteGate_ampPd_Gc_supplier_FINAL`;
    the three carriers are `hcarTau_Gc_concrete` / `hcarField_Gc_concrete` / `hcarField2_Gc_concrete`; the
    triple is closed through `GcConsumerMirror.tripleHEmeas_Gc`.  The `htriple` slot is now 100% concrete.
    NOT `a₁ = R/6`. -/
theorem tripleHEmeas_Gc_concrete (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hC hK S a b) := by
  obtain ⟨δF, hδF0, hδFspec⟩ :=
    QIQTH.AmpPdComposition.concreteGate_ampPd_Gc_supplier_FINAL g gi hC hK a b hg hgi hgpos
  obtain ⟨δcF, hδcF0, hδcFspec⟩ :=
    hcarField_Gc_concrete hn g gi hC hK a b ha hab hg hgi hgpos hu
  obtain ⟨δcF2, hδcF20, hδcF2spec⟩ :=
    hcarField2_Gc_concrete hn g gi hC hK a b ha hab hg hgi hgpos hu
  refine ⟨min δF (min δcF δcF2), lt_min hδF0 (lt_min hδcF0 hδcF20), ?_⟩
  intro c hbc hcδ S hSeq
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcF : c < δF := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hccF : c < δcF := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hccF2 : c < δcF2 := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Gc, AmpGc, hKSmeas, hGcMeas, hAmpGcMeas, hChartAgree, hAmpAgree⟩ :=
    hδFspec c hc0 hcF S hSeq
  have hcarTau := hcarTau_Gc_concrete g gi hC hK S a b hg hgi hgpos Gc hGcMeas hChartAgree
  have hcarField := hδcFspec c hbc hccF S hSeq
  have hcarField2 := hδcF2spec c hbc hccF2 S hSeq
  exact QIQTH.GcConsumerMirror.tripleHEmeas_Gc hn g gi hC hK S a b Gc AmpGc hKSmeas hGcMeas
    hAmpGcMeas hChartAgree hAmpAgree hcarTau hcarField hcarField2 hgiMeas hchr

end QIQTH.JetsGcUnification

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.JetsGcUnification
#print axioms exists_forall_radius
#print axioms hcarTau_Gc_concrete
#print axioms hcarField_Gc_concrete
#print axioms hcarField2_Gc_concrete
#print axioms tripleHEmeas_Gc_concrete
end AxiomChecks
