/-
  OnGateJets — J4-236: the ON-GATE C² JET data for the v7 `hcar…` supplier existentials.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick of
  the `a₁ = R/6` heat-kernel campaign: it discharges the ON-GATE C² jet CONJUNCTS carried inside the
  v7 supplier existentials `hcarTau` / `hcarField` (GatedRepSFix.tripleHEmeas_concrete_v4) at the
  CONCRETE flow-ball gate `S q = uniformFlowExp g gi hChr hK q '' Metric.ball 0 c`.

  Companion to `OffSVanishing.concreteGate_carriers_discharged_v2` (which discharged `hKSmeas`,
  `hS0`, `hchrMeas`, `hOffS`, `hOffS2`).  This file adds the on-gate `hgate` C² jet block of the
  FIRST field-`pd` existential (`hcarField`) and the `∂_τ` HasDerivAt of the amplitude existential
  (`hcarTau`).  NO `sorry`, NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypotheses.  No
  existing file is edited.

  ── WHAT LANDS.
    §A — `chartFieldFirstJet_hasDerivAt`  — ★ the general-field-point first FIELD jet HasDerivAt of
         the inverse chart, in the EXACT `hcarField` line shape
         `HasDerivAt (fun s => W z (update p k s) j) (fderiv (W z) p (eₖ) j) (p k)`, from
         `ContDiffAt ℝ 2 (W z) p` — the general-`p` port of `ChartJetBounds.chartField_firstJet_of_contDiffAt`
         (which was at the field centre `0` only).
    §B — `ampField_contDiffAt` / `ampField_pdiffAt` — the concrete on-gate amplitude `chartFieldAmp`
         is `C²`/`PdiffAt` at a GENERAL field point `p` (the field-slot regularity carried inside
         `hcarField`'s `hgate`), from chart-`C²`-at-`p` + Riemannian positivity `det g (W z p) > 0`.
         General-`p` port of `AmplitudeFamilyDischarge.amp_contDiffAt_general` (field centre `0`).
    §C — `chartFieldAmp_hasDerivAt_tau` — ★ the `∂_τ` HasDerivAt of `chartFieldAmp` (the `hcarTau`
         conjunct).  UNCONDITIONAL: the amplitude is AFFINE in `τ` (`= cutoff·Θ^{−1/2}·(u₀+u₁·τ)`),
         so `Cfield = cutoff·Θ^{−1/2}·u₁` and the derivative is elementary — no regularity needed.
    §D — `hcarField_hgate_concrete` / `hcarTau_hasDeriv_concrete` — the EXACT on-gate `hgate` /
         `∂_τ` conjuncts at the concrete gate, and `concreteGate_carriers_discharged_v3` — the v2
         bundle EXTENDED with these two on-gate jet blocks.

  ── WHAT REMAINS CARRIED / RESIDUE (named honestly; NOT discharged here).
    • The MEASURABILITY conjuncts of `hcarTau`/`hcarField` (`Measurable (chart)`, `Measurable (amp)`,
      `Measurable (Pfield)`, `Measurable (∂-amp)`) — the DEFINITIONAL `.choose` wall of
      `uniformInverseChart` (`ChartJointBorel`: `q ↦ Classical.choose (h q)` carries no measurable-
      in-`q` structure).  Isolated to the shared representative obligation `hChartRep`; NOT touched.
    • The FULL `hcarField2` second-field-`pd` `hgate` — its `∀ y k, HasDerivAt (fun s => W z (update y i s) k) …`
      conjunct is GLOBAL in the field point `y` (needed by `gaussComp_pd_pd`'s inner-`pd`-as-function
      step), but the chart `W z` is only `C²` NEAR image points; the global jet family is the honest
      wall (`ChartFieldC2General` header: off-image `E_z.symm` is junk).  NOT dischargeable at the
      concrete gate; left as residue.

  Radii carried HONESTLY: `0 < a < b < c < δ₀`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OffSVanishing
import QIQTH.ChartFieldC2General
import QIQTH.AmplitudeFamilyDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators ContDiff

namespace QIQTH.OnGateJets

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the general-field-point FIRST FIELD JET of the inverse chart.
    ############################################################################### -/

/-- **★ `chartFieldFirstJet_hasDerivAt` — the first FIELD jet at a GENERAL field point `p`.**
    For the inverse chart `W z := uniformInverseChart g gi hC hK z` that is `ContDiffAt ℝ 2` at a
    field point `p`, the coordinate-`k` line derivative of the `j`-th component exists in the EXACT
    `hcarField` `hgate` line shape:
        `HasDerivAt (fun s => W z (Function.update p k s) j) (fderiv (W z) p (eₖ) j) (p k)`.
    Route: `W z` differentiable at `p` (`C² ⟹ C¹`), chain the (rewritten-basepoint) `HasFDerivAt`
    with the coordinate line `hasDerivAt_update`, take component `j` (`hasDerivAt_pi`).  This is the
    general-`p` port of `ChartJetBounds.chartField_firstJet_of_contDiffAt` (field centre `0` only).
    NOT `a₁ = R/6`. -/
theorem chartFieldFirstJet_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z p : Point n) (k j : Fin n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) p) :
    HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update p k s) j)
      (fderiv ℝ (uniformInverseChart g gi hC hK z) p (Pi.single k (1 : ℝ)) j) (p k) := by
  set W := uniformInverseChart g gi hC hK z with hWdef
  have hWdiff : DifferentiableAt ℝ W p := hreg.differentiableAt (by norm_num)
  have hWfd' : HasFDerivAt W (fderiv ℝ W p) (Function.update p k (p k)) := by
    rw [Function.update_eq_self]; exact hWdiff.hasFDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => W (Function.update p k s))
      (fderiv ℝ W p (Pi.single k (1 : ℝ))) (p k) := by
    have h := hWfd'.comp_hasDerivAt (p k) (hasDerivAt_update p k (p k))
    simpa using h
  exact (hasDerivAt_pi.mp hcomp) j

/-! ###############################################################################
    ### §B — the general-field-point amplitude `C²` / `PdiffAt`.
    ############################################################################### -/

/-- **★ `ampField_contDiffAt` — the concrete amplitude `C²` at a GENERAL field point `p`.**
    General-`p` port of `AmplitudeFamilyDischarge.amp_contDiffAt_general` (field centre `0`).  Each
    factor of `chartFieldAmp = radialCutoff∘W · Θ(W)^{−1/2} · (u₀+u₁τ)∘W` is `ContDiffAt ℝ 2` at `p`
    via `ContDiffAt.comp` (using chart-`C²`-at-`p` `hWz` + Riemannian positivity `hdetz`); assembled
    by `ContDiffAt.mul`.  NOT `a₁ = R/6`. -/
theorem ampField_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) p)
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK z p))) :
    ContDiffAt ℝ 2 (chartFieldAmp g gi hChr hK a b τ z) p := by
  have hcut : ContDiffAt ℝ 2
      (fun p' => radialCutoff a b (uniformInverseChart g gi hChr hK z p')) p :=
    ((radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)).comp p hWz
  have hvv : ContDiffAt ℝ 2
      (fun p' => vanVleck g (uniformInverseChart g gi hChr hK z p')) p :=
    (vanVleck_contDiffAt g hg (uniformInverseChart g gi hChr hK z p) hdetz (k := 2)).comp p hWz
  have hne : (fun p' => vanVleck g (uniformInverseChart g gi hChr hK z p')) p ≠ 0 :=
    ne_of_gt (vanVleck_pos g (uniformInverseChart g gi hChr hK z p) hdetz)
  have hrpow : ContDiffAt ℝ 2
      (fun p' => vanVleck g (uniformInverseChart g gi hChr hK z p') ^ (-(1 : ℝ) / 2)) p :=
    hvv.rpow_const_of_ne hne
  have hu0 : ContDiffAt ℝ 2
      (fun p' => transportCoeff (transportOp (vanVleck g) g gi) 0
        (uniformInverseChart g gi hChr hK z p')) p :=
    (((hu 0).contDiffAt).of_le le_top).comp p hWz
  have hu1 : ContDiffAt ℝ 2
      (fun p' => transportCoeff (transportOp (vanVleck g) g gi) 1
        (uniformInverseChart g gi hChr hK z p')) p :=
    (((hu 1).contDiffAt).of_le le_top).comp p hWz
  have hsum : ContDiffAt ℝ 2
      (fun p' => transportCoeff (transportOp (vanVleck g) g gi) 0
          (uniformInverseChart g gi hChr hK z p')
        + transportCoeff (transportOp (vanVleck g) g gi) 1
            (uniformInverseChart g gi hChr hK z p') * τ) p :=
    hu0.add (hu1.mul contDiffAt_const)
  exact hcut.mul (hrpow.mul hsum)

/-- **`ampField_pdiffAt` — the amplitude `PdiffAt` at a GENERAL field point `p`.**
    The `hcarField` `hgate` amplitude conjunct (`C² ⟹ C¹ ⟹ PdiffAt`).  NOT `a₁ = R/6`. -/
theorem ampField_pdiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z p : Point n) (k : Fin n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) p)
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK z p))) :
    PdiffAt (chartFieldAmp g gi hChr hK a b τ z) k p :=
  QIQTH.LaplaceBeltrami.PdiffAt_of_contDiffAt _ k p
    ((ampField_contDiffAt g gi hChr hK a b τ z p hg hu hWz hdetz).of_le (by norm_num))

/-! ###############################################################################
    ### §C — the `∂_τ` HasDerivAt of the amplitude (the `hcarTau` conjunct).
    ############################################################################### -/

/-- **★ `chartFieldAmp_hasDerivAt_tau` — the `∂_τ` HasDerivAt of the concrete amplitude.**
    `chartFieldAmp g gi hChr hK a b τ z p` is AFFINE in `τ`
    (`= radialCutoff(W)·(Θ(W)^{−1/2}·(u₀(W) + u₁(W)·τ))`), so as a function of `τ` its derivative is
    `Cfield z p := radialCutoff(W)·(Θ(W)^{−1/2}·u₁(W))`.  UNCONDITIONAL — pure 1-D calculus, no
    regularity of `W` needed.  This is the exact `hcarTau` derivative conjunct.  NOT `a₁ = R/6`. -/
theorem chartFieldAmp_hasDerivAt_tau (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (z p : Point n) (τ : ℝ) :
    HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u z p)
      (radialCutoff a b (uniformInverseChart g gi hChr hK z p)
        * (vanVleck g (uniformInverseChart g gi hChr hK z p) ^ (-(1 : ℝ) / 2)
            * transportCoeff (transportOp (vanVleck g) g gi) 1
                (uniformInverseChart g gi hChr hK z p))) τ := by
  simp only [chartFieldAmp]
  have h0 : HasDerivAt
      (fun u : ℝ => transportCoeff (transportOp (vanVleck g) g gi) 0
            (uniformInverseChart g gi hChr hK z p)
          + transportCoeff (transportOp (vanVleck g) g gi) 1
            (uniformInverseChart g gi hChr hK z p) * u)
      (transportCoeff (transportOp (vanVleck g) g gi) 1
            (uniformInverseChart g gi hChr hK z p)) τ := by
    have h := (hasDerivAt_const τ (transportCoeff (transportOp (vanVleck g) g gi) 0
          (uniformInverseChart g gi hChr hK z p))).add
      ((hasDerivAt_id τ).const_mul (transportCoeff (transportOp (vanVleck g) g gi) 1
          (uniformInverseChart g gi hChr hK z p)))
    rw [zero_add, mul_one] at h
    exact h
  exact (h0.const_mul (vanVleck g (uniformInverseChart g gi hChr hK z p) ^ (-(1 : ℝ) / 2))).const_mul
    (radialCutoff a b (uniformInverseChart g gi hChr hK z p))

/-! ###############################################################################
    ### §D — the CONCRETE-gate on-gate jet conjuncts + the v3 bundle.
    ############################################################################### -/

/-- **★★ `hcarField_hgate_concrete` — the `hcarField` on-gate `hgate` block at the concrete gate.**
    At the concrete flow-ball gate `S q = uniformFlowExp g gi hChr hK q '' Metric.ball 0 c`
    (`0 < a < b < c < δ₀`), for every coordinate `k` there is a first-jet witness `Pfield` (the chart
    Fréchet-derivative columns) such that on the FULL gate (`q ∈ K`, `τ > 0`, `p ∈ S q`) the exact
    `hcarField` `hgate` triple holds:
      • `IsOpen (S q)` (the open flow-ball image, `uniformInverseChart_huniformChart`);
      • `∀ j, HasDerivAt (fun s => W q (update p k s) j) (Pfield q p j) (p k)` (§A, via chart-`C²`-at-`p`);
      • `PdiffAt (chartFieldAmp … τ q) k p` (§B, via chart-`C²`-at-`p` + `det g (W q p) > 0`).
    Riemannian positivity `hgpos` and the metric/transport smoothness `hg`/`hu` are carried (all
    satisfiable, never the conclusion).  NOT `a₁ = R/6`. -/
theorem hcarField_hgate_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) →
        ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
          ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1 := by
  obtain ⟨δr, hδr, hreach⟩ := QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hChr hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hChr hK
  refine ⟨min δr δo, lt_min hδr hδo, ?_⟩
  intro c hbc hcδ S hSeq k
  refine ⟨fun q p j =>
    fderiv ℝ (uniformInverseChart g gi hChr hK q) p (Pi.single k (1 : ℝ)) j, ?_⟩
  intro w hzK hτ hpS
  have hcδr : c < δr := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδo : c < δo := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hSq : S w.2.2 = uniformFlowExp g gi hChr hK w.2.2 '' Metric.ball (0 : Point n) c := by
    rw [hSeq]
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  -- reachable pre-image of `p`.
  have hpS' : w.2.1 ∈ uniformFlowExp g gi hChr hK w.2.2 '' Metric.ball (0 : Point n) c := by
    rwa [hSq] at hpS
  obtain ⟨v, hv, hvp⟩ := hpS'
  have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
  have hCp : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK w.2.2) w.2.1 := by
    rw [← hvp]; exact hreach w.2.2 hzK v (lt_trans hvc hcδr)
  have hdetp : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK w.2.2 w.2.1)) :=
    hgpos _
  refine ⟨?_, ?_, ?_⟩
  · rw [hSq]; exact (hopen w.2.2 hzK).2 c hc0 hcδo |>.1
  · intro j
    exact chartFieldFirstJet_hasDerivAt g gi hChr hK w.2.2 w.2.1 k j hCp
  · exact ampField_pdiffAt g gi hChr hK a b w.1 w.2.2 w.2.1 k hg hu hCp hdetp

/-- **★★ `hcarTau_hasDeriv_concrete` — the `hcarTau` `∂_τ` conjunct at the concrete gate.**
    At the concrete flow-ball gate there is an amplitude-time-derivative witness `Cfield` (the affine
    `τ`-slope of `chartFieldAmp`) such that on the FULL gate the exact `hcarTau` HasDerivAt holds:
      `HasDerivAt (fun u => chartFieldAmp … u q p) (Cfield q p) τ`.
    UNCONDITIONAL in `τ` (§C); the gate hypotheses are not needed for the elementary affine
    derivative and are simply not consumed (the fact is genuinely TRUE, not vacuous).  NOT `a₁ = R/6`. -/
theorem hcarTau_hasDeriv_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (S : Point n → Set (Point n)) :
    ∃ Cfield : Point n → Point n → ℝ,
      ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1 := by
  refine ⟨fun q p =>
    radialCutoff a b (uniformInverseChart g gi hChr hK q p)
      * (vanVleck g (uniformInverseChart g gi hChr hK q p) ^ (-(1 : ℝ) / 2)
          * transportCoeff (transportOp (vanVleck g) g gi) 1
              (uniformInverseChart g gi hChr hK q p)), ?_⟩
  intro w _ _ _
  exact chartFieldAmp_hasDerivAt_tau g gi hChr hK a b w.2.2 w.2.1 w.1

/-- **★★★ `concreteGate_carriers_discharged_v3` — the v2 bundle EXTENDED with the on-gate jet blocks.**
    At the concrete flow-ball gate `S z = uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`
    (`0 < a < b < c < δ₀`), UNDER a SINGLE radius `δ₀`, the `J4-235` bundle
    (`OffSVanishing.concreteGate_carriers_discharged_v2`: `hKSmeas`, `hS0`, `hchrMeas`, `hOffS`,
    `hOffS2`) holds SIMULTANEOUSLY with the ON-GATE C² jet blocks of the FIRST field-`pd` supplier
    (`hcarField`'s `hgate`, ∀ `k`, this file) AND the `∂_τ` amplitude supplier (`hcarTau`'s HasDerivAt,
    this file).

    What now REMAINS inside the v7 supplier existentials (`hcarTau`/`hcarField`) is exactly the
    MEASURABILITY block (the definitional `.choose` chart-measurability wall of `ChartJointBorel`,
    isolated to the shared `hChartRep` obligation), plus the SECOND field-`pd` supplier `hcarField2`
    (whose `hgate` carries a GLOBAL-in-`y` chart jet family — the off-image-junk wall).  NOT `a₁ = R/6`. -/
theorem concreteGate_carriers_discharged_v3 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) →
      -- J4-234/235: the five carriers of `concreteGate_carriers_discharged_v2`.
      ((MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
          ∧ (0 : Point n) ∈ S 0
          ∧ (∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)))
        ∧ (∀ (k : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDeriv g gi hChr hK S a b k w.1 w.2.1 w.2.2 = 0)
        ∧ (∀ (i j : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitness g gi hChr hK S a b w.1 x w.2.2) j y)
                i w.2.1 = 0))
      -- J4-236: the on-gate FIRST field-`pd` `hgate` block (∀ `k`).
      ∧ (∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
          ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
      -- J4-236: the on-gate `∂_τ` amplitude HasDerivAt (`hcarTau`).
      ∧ (∃ Cfield : Point n → Point n → ℝ,
          ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1) := by
  obtain ⟨δ₁, hδ₁, h2⟩ :=
    QIQTH.OffSVanishing.concreteGate_carriers_discharged_v2 g gi hChr hK hK0 a b ha hab
  obtain ⟨δ₂, hδ₂, hfield⟩ :=
    hcarField_hgate_concrete g gi hChr hK a b ha hab hg hgpos hu
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro c hbc hcδ S hSeq
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact ⟨h2 c hbc hcδ₁ S hSeq, hfield c hbc hcδ₂ S hSeq,
    hcarTau_hasDeriv_concrete g gi hChr hK a b S⟩

end QIQTH.OnGateJets

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.OnGateJets
#print axioms chartFieldFirstJet_hasDerivAt
#print axioms ampField_contDiffAt
#print axioms ampField_pdiffAt
#print axioms chartFieldAmp_hasDerivAt_tau
#print axioms hcarField_hgate_concrete
#print axioms hcarTau_hasDeriv_concrete
#print axioms concreteGate_carriers_discharged_v3
end AxiomChecks
