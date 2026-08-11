/-
  WhiteS1 — J4-628: S1 AT THE WHITENED WITNESS, FIRST SLICES — the Route-B (Gc-representative)
  joint-measurability mirror for `whiteCutKernel` / `whiteGatedWitness`, opening the discharge of
  the single labelled `hEmeas` residue of the J4-627 bridge feed
  (`WhiteBridge.white_tail_O_s_discharged`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: the REMAINDER of S1 at the whitened witness (see the residue map below) + `lam ≤ 8`
  (opaque `C₀`) + `K1TransportBudget` + the fat-`K` carrier piles + the capstone co-instantiation
  at the whitened witness + the prior analytic piles.

  ── THE DECOMPOSITION VERDICT (J4-628 STEP 1, verified in code below).  The whitened witness
     `whiteGatedWitness = gatedKernel K S (whiteCutKernel)` with
        `whiteCutKernel a b τ p q = χ_{a,b}(V^w_q p) · (√det g^κ(q) · G_τ(V^w_q p))`,
        `V^w_q = whiteUnvel_q ∘ uniformInverseChart_q`,
     is STRICTLY EASIER than the as-built van-Vleck witness on the S1 (measurability) axis:
       (i)   the ONLY `.choose`-based `q`-dependence is `uniformInverseChart` — SHARED with the
             as-built chain, so the banked measurable chart REPRESENTATIVE
             (`ImageSupportDischarge.hWG_gate_concrete`, the J4-598 Lusin–Souslin `Gc`) is
             consumed VERBATIM at the curved-RNC instantiation (`whiteChart_rep_concrete` below);
       (ii)  the whitening layer `whiteUnvel_q` on top is CLOSED FORM (entries of
             `g^κ(q)·E_q` are Borel in `q`: polynomial metric entries × the explicit
             `curvedWhitening` sqrt/rational entries) — a cheap composition
             (`whiteGcChart_measurable`);
       (iii) the AMPLITUDE `√det g^κ(q)` depends on `q` ONLY (no transport amplitude, no field
             point): the field-`pd` of the amplitude — the hard `AmpPdComposition` layer of the
             as-built campaign — is ABSENT here;
       (iv)  the τ-dependence sits ENTIRELY in the flat Gaussian `G_τ`, whose τ-derivative is a
             GLOBAL closed form — the ∂_τ E3d slot closes in THIS brick (`white_hDtau_concrete`).

  ── WHAT LANDS (all unconditional, std-3):
     ▸ SLICE 1 (chart): `curvedWhitening_entry_measurable` + `whiteGcChart` /
       `whiteGcChart_measurable` / `whiteInvChart_eq_whiteGcChart` — the whitened chart's
       measurable joint representative from ANY chart representative; and
       ★ `whiteChart_rep_concrete` — the CONCRETE banked supplier (`hWG_gate_concrete` at
       `g^κ/gi^κ`): a single `ρ > 0` and a globally measurable `Wg` agreeing with
       `whiteInvChart` on every flow-ball gate of radius `c ≤ ρ`.
     ▸ SLICE 2 (kernel + witness value): `whiteCutKernelGc` / `whiteCutKernelGc_measurable` /
       `whiteCutKernel_eq_whiteCutKernelGc_of_agree`; ★ `whiteGatedWitness_value_stronglyMeasurable`
       (the witness VALUE triple joint strong measurability at ANY measurable gate with a chart
       representative) and ★★ `white_witness_value_concrete` (unconditional at the concrete
       flow-ball gates).
     ▸ SLICE 3 (the ∂_τ E3d slot — slot 1 of the 3 derivative fields of
       `HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields`): `whiteTauDerivRep` /
       `whiteTauDerivRep_measurable` / `whiteWitness_tauDeriv_eq_rep` (the pointwise deriv-field
       identity: on-gate τ>0 product rule at the Gaussian's closed-form time derivative; on-gate
       τ≤0 zero via the `Iic` uniqueness trick; off-gate zero), ★ `white_hDtau_stronglyMeasurable`
       and ★★ `white_hDtau_concrete` — the EXACT `hDτ` slot shape, UNCONDITIONAL at the concrete
       flow-ball gates.
     ▸ coefficient measurabilities `curvedRNCInv_entry_measurable` /
       `curvedRNC_christoffel_measurable` — the E3d `hgi`/`hchr` slots at `g^κ`, unconditional.

  ── THE HONEST RESIDUE MAP (what `white_tripleHEmeas` still owes after this brick):
     (S1-a) the FIRST field-`pd` slot `hP1` — the whitened mirror of the gated first-derivative
            representative (`GatedRepSFix.gatedDerivRepProdS` pattern): chart field-jets
            `Pfield` (banked: `FlowDerivMeasurable.flowInverseJet_measurable_component` at
            `g^κ/gi^κ`, composed with the LINEAR `whiteUnvel_q`) + the closed-form
            `∂_k[χ·G_τ]` chain rule + off-`S` vanishing (`radialCutoff` support).  NO amplitude
            `pd` needed (verdict (iii)) — strictly smaller than the as-built §A.
     (S1-b) the SECOND field-`pd` slot `hP2` (general index `i,j`) — the order-2 mirror
            (`flowInverseSecondJet_measurable_component` + the Gaussian/cutoff Hessian closed
            form); again NO amplitude Hessian.  The largest remaining slice.
     (S1-c) the E3d assembly: `triple_hEmeas_of_borel_deriv_fields` at
            `G := whiteGatedWitness`, consuming {this brick's `hDτ`, (S1-a), (S1-b), this
            brick's `hgi`/`hchr`} — then the J4-627 feeder's `hEmeas` residue is DISCHARGED and
            `white_tail_O_s` becomes unconditional (modulo `hlam8` only).

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedents (non-vacuity gates
  §6); no existing file edited except the `QIQTH.lean` / `AxiomAudit.lean` wiring.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteGated
import QIQTH.HEmeasBorelAudit
import QIQTH.ImageSupportDischarge
import QIQTH.ConcreteGateInstantiation
import QIQTH.FrozenWire

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.EquivProbe
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace QIQTH.WhiteS1

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ###############################################################################
    ### §1 — SLICE 1(a): the closed-form whitening layer is Borel in the base point.
    ############################################################################### -/

/-- **`curvedWhitening_entry_measurable`** — each entry of the explicit whitening frame
    `E_q = a·δ + b·q qᵀ` (`a = (1−(κ/3)r²)^{-1/2}`, `b = (1−a)/r²`) is Borel-measurable in `q`:
    a composition of `rncRadialSq` (smooth), `Real.sqrt` (continuous), and field operations
    (division is Borel with NO nonvanishing hypothesis).  NOT `a₁ = R/6`. -/
theorem curvedWhitening_entry_measurable (κ : ℝ) (i j : Fin n) :
    Measurable (fun q : Point n => curvedWhitening κ q i j) := by
  have hr : Measurable (fun q : Point n => rncRadialSq q) :=
    rncRadialSq_contDiff.continuous.measurable
  have hs : Measurable (fun q : Point n =>
      1 / Real.sqrt (1 - κ / 3 * rncRadialSq q)) :=
    measurable_const.div
      (Real.continuous_sqrt.measurable.comp (measurable_const.sub (hr.const_mul (κ / 3))))
  have hqi : Measurable (fun q : Point n => q i) := measurable_pi_apply i
  have hqj : Measurable (fun q : Point n => q j) := measurable_pi_apply j
  simp only [curvedWhitening]
  exact (hs.mul measurable_const).add
    ((((measurable_const.sub hs).div hr).mul hqi).mul hqj)

/-- The metric entries `q ↦ g^κ(q)ᵢⱼ` are measurable (smooth, banked). -/
theorem curvedRNCMetric_entry_measurable (κ : ℝ) (i j : Fin n) :
    Measurable (fun q : Point n => curvedRNCMetric κ q i j) :=
  (curvedRNCMetric_contDiff κ i j).continuous.measurable

/-- The whitened amplitude `q ↦ √det g^κ(q)` is measurable (via the banked determinant
    continuity `FrozenWire.continuous_curvedRNCMetric_det`). -/
theorem sqrtDet_curvedRNCMetric_measurable (κ : ℝ) :
    Measurable (fun q : Point n => Real.sqrt (Matrix.det (curvedRNCMetric κ q))) :=
  (Real.continuous_sqrt.comp (QIQTH.FrozenWire.continuous_curvedRNCMetric_det κ)).measurable

/-! ###############################################################################
    ### §2 — SLICE 1(b): the whitened chart's measurable joint representative.
    ############################################################################### -/

/-- **`whiteGcChart` — the whitened chart representative**: any joint chart representative `Gc`
    (for `uniformInverseChart` at `g^κ/gi^κ`) pushed through the CLOSED-FORM whitening inverse
    `whiteUnvel_q = matToCLM (g^κ(q)·E_q)`.  Wherever `uniformInverseChart` agrees with `Gc`,
    `whiteInvChart` agrees with this (`whiteInvChart_eq_whiteGcChart`). -/
noncomputable def whiteGcChart (κ : ℝ) (Gc : Point n × Point n → Point n) :
    Point n × Point n → Point n :=
  fun zx => whiteUnvel κ zx.1 (Gc zx)

/-- **★ `whiteGcChart_measurable`** — the whitened chart representative is GLOBALLY measurable
    from `Measurable Gc` alone: componentwise it is the finite bilinear form
    `∑ⱼ (∑ₘ g^κ(z)ᵢₘ · E(z)ₘⱼ) · Gc(z,x)ⱼ` of Borel entry functions (§1).  This is the
    verdict-(ii) closed-form composition: the whitening layer adds NO new `.choose` wall.
    NOT `a₁ = R/6`. -/
theorem whiteGcChart_measurable (κ : ℝ) (Gc : Point n × Point n → Point n)
    (hGc : Measurable Gc) : Measurable (whiteGcChart κ Gc) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  have hrw : (fun zx : Point n × Point n => whiteGcChart κ Gc zx i)
      = fun zx : Point n × Point n =>
          ∑ j, (∑ m, curvedRNCMetric κ zx.1 i m * curvedWhitening κ zx.1 m j) * Gc zx j := by
    funext zx
    simp only [whiteGcChart, whiteUnvel, matToCLM_apply]
  rw [hrw]
  refine Finset.measurable_sum _ (fun j _ => Measurable.mul ?_ ?_)
  · refine Finset.measurable_sum _ (fun m _ => Measurable.mul ?_ ?_)
    · exact (curvedRNCMetric_entry_measurable κ i m).comp measurable_fst
    · exact (curvedWhitening_entry_measurable κ m j).comp measurable_fst
  · exact (measurable_pi_apply j).comp hGc

/-- Wherever the raw chart agrees with its representative, the WHITENED chart agrees with the
    whitened representative (pure substitution — the whitening is applied to both sides). -/
theorem whiteInvChart_eq_whiteGcChart (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (Gc : Point n × Point n → Point n) (q p : Point n)
    (hagree : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q p = Gc (q, p)) :
    whiteInvChart κ hκ hKc q p = whiteGcChart κ Gc (q, p) := by
  simp only [whiteInvChart, whiteGcChart, hagree]

/-- **★★ `whiteChart_rep_concrete` — the CONCRETE whitened chart representative** (the banked
    supplier consumed VERBATIM): from `ImageSupportDischarge.hWG_gate_concrete` at the curved-RNC
    data, a single `ρ > 0` and a GLOBALLY MEASURABLE `Wg` such that on every flow-ball gate of
    radius `c ≤ ρ`, `whiteInvChart` EQUALS `Wg`.  This is the S1(whitened) chart-measurability
    layer: the `.choose` wall is exactly the as-built one, already paid.  NOT `a₁ = R/6`. -/
theorem whiteChart_rep_concrete (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ ρ > (0 : ℝ), ∃ Wg : Point n × Point n → Point n, Measurable Wg ∧
      ∀ c : ℝ, c ≤ ρ → ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset →
        w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1) := by
  obtain ⟨ρ, hρ, Gc, hGcMeas, hagree⟩ :=
    QIQTH.ImageSupportDischarge.hWG_gate_concrete (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc
  refine ⟨ρ, hρ, whiteGcChart κ Gc, whiteGcChart_measurable κ Gc hGcMeas, ?_⟩
  intro c hc w hqK hp
  exact whiteInvChart_eq_whiteGcChart κ hκ hKc Gc w.2.2 w.2.1 (hagree c hc w hqK hp)

/-! ###############################################################################
    ### §3 — SLICE 2: the whitened cutoff kernel and the WITNESS VALUE triple.
    ############################################################################### -/

/-- **`whiteCutKernelGc` — the representative-substituted whitened cutoff kernel**:
    `χ_{a,b}(Wg(q,p)) · (√det g^κ(q) · G_τ(Wg(q,p)))` — verbatim `whiteCutKernel` with the
    whitened chart value replaced by the joint representative. -/
noncomputable def whiteCutKernelGc (κ a b : ℝ) (Wg : Point n × Point n → Point n) :
    ℝ × Point n × Point n → ℝ :=
  fun w => radialCutoff a b (Wg (w.2.2, w.2.1))
    * (Real.sqrt (Matrix.det (curvedRNCMetric κ w.2.2))
        * gaussDdim w.1 (Wg (w.2.2, w.2.1)))

/-- **★ `whiteCutKernelGc_measurable`** — globally jointly Borel from `Measurable Wg` alone:
    `radialCutoff` is smooth, `√det g^κ` is measurable (§1), `G` is jointly Borel
    (`gaussDdim_uncurry_measurable`).  Verdict (iii): NO amplitude field derivative anywhere.
    NOT `a₁ = R/6`. -/
theorem whiteCutKernelGc_measurable (κ a b : ℝ) (Wg : Point n × Point n → Point n)
    (hWg : Measurable Wg) : Measurable (whiteCutKernelGc κ a b Wg) := by
  have hWgw : Measurable (fun w : ℝ × Point n × Point n => Wg (w.2.2, w.2.1)) :=
    hWg.comp (measurable_snd.snd.prodMk measurable_snd.fst)
  refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
  · exact ((radialCutoff_contDiff a b).continuous.measurable).comp hWgw
  · exact (sqrtDet_curvedRNCMetric_measurable κ).comp measurable_snd.snd
  · exact QIQTH.InnerKernelJointMeas.gaussDdim_uncurry_measurable.comp
      (measurable_fst.prodMk hWgw)

/-- Wherever the whitened chart agrees with `Wg`, the whitened cutoff kernel equals its
    representative twin (pure substitution). -/
theorem whiteCutKernel_eq_whiteCutKernelGc_of_agree (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (a b : ℝ)
    (Wg : Point n × Point n → Point n) (τ : ℝ) (p q : Point n)
    (hagree : whiteInvChart κ hκ hKc q p = Wg (q, p)) :
    whiteCutKernel κ hκ hKc a b τ p q = whiteCutKernelGc κ a b Wg (τ, p, q) := by
  simp only [whiteCutKernel, whiteAmbientKernel, whiteCutKernelGc, hagree]

/-- **★ `whiteGatedWitness_value_stronglyMeasurable`** — the whitened gated witness VALUE is
    jointly `(τ,p,q)` strongly measurable at ANY measurable gate carrying a chart representative:
    the witness is EXACTLY the gate-indicator of the (globally measurable) representative kernel.
    NOT `a₁ = R/6`. -/
theorem whiteGatedWitness_value_stronglyMeasurable (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n) (hWg : Measurable Wg)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2})
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      whiteGatedWitness κ hκ hKc S a b w.1 w.2.1 w.2.2) := by
  classical
  have hrw : (fun w : ℝ × Point n × Point n =>
        whiteGatedWitness κ hκ hKc S a b w.1 w.2.1 w.2.2)
      = Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2}
          (whiteCutKernelGc κ a b Wg) := by
    funext w
    by_cases hg : w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2
    · rw [Set.indicator_of_mem
        (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2} from hg)]
      show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) w.1 w.2.1 w.2.2
          = whiteCutKernelGc κ a b Wg w
      rw [gatedKernel_apply_of_mem Kset S _ w.1 hg.1 hg.2]
      exact whiteCutKernel_eq_whiteCutKernelGc_of_agree κ hκ hKc a b Wg w.1 w.2.1 w.2.2
        (hagree w hg.1 hg.2)
    · rw [Set.indicator_of_notMem
        (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2} from hg)]
      exact gatedKernel_apply_of_notMem Kset S _ w.1 w.2.1 w.2.2 (not_and_or.mp hg)
  rw [hrw]
  exact ((whiteCutKernelGc_measurable κ a b Wg hWg).indicator hKSmeas).stronglyMeasurable

/-- **★★ `white_witness_value_concrete`** — UNCONDITIONAL at the concrete flow-ball gates: a
    single `δ₀ > 0` such that for every gate radius `0 < c < δ₀` the whitened gated witness
    VALUE triple is jointly strongly measurable (chart representative from
    `whiteChart_rep_concrete`; gate `MeasurableSet` from the banked Lusin–Souslin
    `hKSmeas_concrete`).  NOT `a₁ = R/6`. -/
theorem white_witness_value_concrete (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          w.1 w.2.1 w.2.2) := by
  obtain ⟨ρ, hρ, Wg, hWgMeas, hWagree⟩ := whiteChart_rep_concrete κ hκ hKc
  obtain ⟨δm, hδm, hδmspec⟩ :=
    QIQTH.ConcreteGateInstantiation.hKSmeas_concrete (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc
  refine ⟨min ρ δm, lt_min hρ hδm, ?_⟩
  intro c hc0 hcδ
  have hcρ : c ≤ ρ := le_of_lt (lt_of_lt_of_le hcδ (min_le_left _ _))
  have hcm : c < δm := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact whiteGatedWitness_value_stronglyMeasurable κ hκ hKc _ a b Wg hWgMeas
    (hδmspec c hc0 hcm) (fun w hqK hpS => hWagree c hcρ w hqK hpS)

/-! ###############################################################################
    ### §4 — SLICE 3: the ∂_τ derivative field (E3d slot 1 of 3) — closed in this brick.
    ############################################################################### -/

/-- **`whiteTauDerivRep` — the gated ∂_τ representative** of the whitened witness: on the
    time-positive full gate, the closed-form Gaussian time derivative
    `χ·(√det·((∑ᵢ (vᵢ²/(4τ²) − 1/(2τ)))·G_τ(v)))` at the representative chart value
    `v = Wg(q,p)`; `0` elsewhere. -/
noncomputable def whiteTauDerivRep (κ a b : ℝ) (Kset : Set (Point n))
    (S : Point n → Set (Point n)) (Wg : Point n × Point n → Point n) :
    ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n |
      (w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2) ∧ 0 < w.1}
    (fun w => radialCutoff a b (Wg (w.2.2, w.2.1))
      * (Real.sqrt (Matrix.det (curvedRNCMetric κ w.2.2))
          * ((∑ i, ((Wg (w.2.2, w.2.1)) i ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1)))
              * gaussDdim w.1 (Wg (w.2.2, w.2.1)))))

/-- **★ `whiteTauDerivRep_measurable`** — jointly Borel from `Measurable Wg` + the gate
    `MeasurableSet`; the `1/τ`, `1/τ²` factors are Borel with no nonvanishing hypothesis and are
    indicator-confined to `τ > 0`.  NOT `a₁ = R/6`. -/
theorem whiteTauDerivRep_measurable (κ a b : ℝ) (Kset : Set (Point n))
    (S : Point n → Set (Point n)) (Wg : Point n × Point n → Point n)
    (hWg : Measurable Wg)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2}) :
    Measurable (whiteTauDerivRep κ a b Kset S Wg) := by
  have hWgw : Measurable (fun w : ℝ × Point n × Point n => Wg (w.2.2, w.2.1)) :=
    hWg.comp (measurable_snd.snd.prodMk measurable_snd.fst)
  have hset : MeasurableSet {w : ℝ × Point n × Point n |
      (w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2) ∧ 0 < w.1} := by
    have hrw : {w : ℝ × Point n × Point n | (w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2) ∧ 0 < w.1}
        = {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2}
          ∩ {w : ℝ × Point n × Point n | 0 < w.1} := rfl
    rw [hrw]
    exact hKSmeas.inter (measurableSet_lt measurable_const measurable_fst)
  refine Measurable.indicator (Measurable.mul ?_ (Measurable.mul ?_ (Measurable.mul ?_ ?_))) hset
  · exact ((radialCutoff_contDiff a b).continuous.measurable).comp hWgw
  · exact (sqrtDet_curvedRNCMetric_measurable κ).comp measurable_snd.snd
  · refine Finset.measurable_sum _ (fun i _ => Measurable.sub ?_ ?_)
    · exact (((measurable_pi_apply i).comp hWgw).pow_const 2).div
        ((measurable_fst.pow_const 2).const_mul 4)
    · exact measurable_const.div (measurable_fst.const_mul 2)
  · exact QIQTH.InnerKernelJointMeas.gaussDdim_uncurry_measurable.comp
      (measurable_fst.prodMk hWgw)

/-- **★★ `whiteWitness_tauDeriv_eq_rep` — the pointwise ∂_τ-field identity.**  At EVERY
    `(τ,p,q)`, the time derivative of the whitened gated witness equals the gated representative:
      • on-gate, `τ > 0`: the hard gate is `τ`-independent, so the `u`-slice is
        `χ·(√det·G_u(v))` and the product rule at the Gaussian's closed-form time derivative
        applies (`heatKernel1D_hasDerivAt_t` / `gaussDdim_heat_eqn` / `gaussDdim_pd_pd_i`);
      • on-gate, `τ ≤ 0`: the `u`-slice vanishes on `Iic τ` (`G_u = 0` for `u ≤ 0`), so the
        `deriv` is `0` by the `Iic` unique-diff trick (junk-value coherence);
      • off-gate: the `u`-slice is identically `0`.
    NO continuity in the base point anywhere (Route B).  NOT `a₁ = R/6`. -/
theorem whiteWitness_tauDeriv_eq_rep (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n))
    (a b : ℝ) (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (w : ℝ × Point n × Point n) :
    deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u w.2.1 w.2.2) w.1
      = whiteTauDerivRep κ a b Kset S Wg w := by
  classical
  by_cases hg : w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2
  · have hvW := hagree w hg.1 hg.2
    have hfe : (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u w.2.1 w.2.2)
        = fun u : ℝ => radialCutoff a b (Wg (w.2.2, w.2.1))
            * (Real.sqrt (Matrix.det (curvedRNCMetric κ w.2.2))
                * gaussDdim u (Wg (w.2.2, w.2.1))) := by
      funext u
      show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) u w.2.1 w.2.2 = _
      rw [gatedKernel_apply_of_mem Kset S _ u hg.1 hg.2]
      simp only [whiteCutKernel, whiteAmbientKernel, hvW]
    by_cases hτ : 0 < w.1
    · -- ON GATE, τ > 0: product rule at the Gaussian closed-form time derivative.
      set v : Point n := Wg (w.2.2, w.2.1) with hvdef
      have hgd : DifferentiableAt ℝ (fun u : ℝ => gaussDdim u v) w.1 := by
        have h := HasDerivAt.fun_finsetProd
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
            heatKernel1D_hasDerivAt_t w.1 (v i) hτ)
        simpa only [gaussDdim] using h.differentiableAt
      have hde : deriv (fun u : ℝ => gaussDdim u v) w.1
          = (∑ i, ((v i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) * gaussDdim w.1 v := by
        rw [gaussDdim_heat_eqn w.1 hτ v, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => gaussDdim_pd_pd_i w.1 hτ v i)
      have hG : HasDerivAt (fun u : ℝ => gaussDdim u v)
          ((∑ i, ((v i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) * gaussDdim w.1 v) w.1 := by
        have h0 := hgd.hasDerivAt
        rwa [hde] at h0
      have hHD : HasDerivAt
          (fun u : ℝ => radialCutoff a b v
            * (Real.sqrt (Matrix.det (curvedRNCMetric κ w.2.2)) * gaussDdim u v))
          (radialCutoff a b v
            * (Real.sqrt (Matrix.det (curvedRNCMetric κ w.2.2))
                * ((∑ i, ((v i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1)))
                    * gaussDdim w.1 v))) w.1 :=
        (hG.const_mul (Real.sqrt (Matrix.det (curvedRNCMetric κ w.2.2)))).const_mul
          (radialCutoff a b v)
      rw [hfe, hHD.deriv]
      simp only [whiteTauDerivRep]
      rw [Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n |
          (w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2) ∧ 0 < w.1} from ⟨hg, hτ⟩)]
    · -- ON GATE, τ ≤ 0: the u-slice vanishes on `Iic τ`.
      rw [not_lt] at hτ
      have hzero_le : ∀ u : ℝ, u ≤ 0 →
          radialCutoff a b (Wg (w.2.2, w.2.1))
            * (Real.sqrt (Matrix.det (curvedRNCMetric κ w.2.2))
                * gaussDdim u (Wg (w.2.2, w.2.1))) = 0 := by
        intro u hu
        rw [QIQTH.InnerKernelJointMeas.gaussDdim_eq_zero_of_nonpos hn u _ hu,
          mul_zero, mul_zero]
      have hDW : HasDerivWithinAt
          (fun u : ℝ => radialCutoff a b (Wg (w.2.2, w.2.1))
            * (Real.sqrt (Matrix.det (curvedRNCMetric κ w.2.2))
                * gaussDdim u (Wg (w.2.2, w.2.1)))) 0 (Set.Iic w.1) w.1 := by
        refine (hasDerivAt_const w.1 (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
        · exact eventuallyEq_of_mem self_mem_nhdsWithin
            (fun u hu => hzero_le u (le_trans (Set.mem_Iic.mp hu) hτ))
        · exact hzero_le w.1 hτ
      rw [hfe, hDW.deriv_eq_zero (uniqueDiffWithinAt_Iic w.1)]
      simp only [whiteTauDerivRep]
      rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n |
        (w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2) ∧ 0 < w.1} from
        fun hmem => (not_lt.mpr hτ) hmem.2)]
  · -- OFF GATE: the u-slice is identically 0.
    have hfe : (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u w.2.1 w.2.2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext u
      exact gatedKernel_apply_of_notMem Kset S _ u w.2.1 w.2.2 (not_and_or.mp hg)
    rw [hfe, deriv_const w.1 (0 : ℝ)]
    simp only [whiteTauDerivRep]
    rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n |
      (w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2) ∧ 0 < w.1} from fun hmem => hg hmem.1)]

/-- **★ `white_hDtau_stronglyMeasurable` — the E3d `hDτ` slot at the whitened witness**, at ANY
    measurable gate with a chart representative: the ∂_τ derivative field is jointly strongly
    measurable — EXACTLY the `hDτ` antecedent shape of
    `HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields`.  NOT `a₁ = R/6`. -/
theorem white_hDtau_stronglyMeasurable (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n))
    (a b : ℝ) (Wg : Point n × Point n → Point n) (hWg : Measurable Wg)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2})
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u w.2.1 w.2.2) w.1) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc S a b u w.2.1 w.2.2) w.1)
      = whiteTauDerivRep κ a b Kset S Wg :=
    funext (whiteWitness_tauDeriv_eq_rep hn κ hκ hKc S a b Wg hagree)
  rw [hrw]
  exact (whiteTauDerivRep_measurable κ a b Kset S Wg hWg hKSmeas).stronglyMeasurable

/-- **★★ `white_hDtau_concrete` — the ∂_τ E3d slot, UNCONDITIONAL at the concrete flow-ball
    gates**: a single `δ₀ > 0` such that for every gate radius `0 < c < δ₀`, the whitened gated
    witness's ∂_τ derivative field is jointly strongly measurable — slot 1 of the 3 derivative
    fields of the whitened S1 (`triple_hEmeas_of_borel_deriv_fields`), fully discharged from
    geometry (no carried measurability input).  NOT `a₁ = R/6`. -/
theorem white_hDtau_concrete (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        deriv (fun u : ℝ => whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          u w.2.1 w.2.2) w.1) := by
  obtain ⟨ρ, hρ, Wg, hWgMeas, hWagree⟩ := whiteChart_rep_concrete κ hκ hKc
  obtain ⟨δm, hδm, hδmspec⟩ :=
    QIQTH.ConcreteGateInstantiation.hKSmeas_concrete (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc
  refine ⟨min ρ δm, lt_min hρ hδm, ?_⟩
  intro c hc0 hcδ
  have hcρ : c ≤ ρ := le_of_lt (lt_of_lt_of_le hcδ (min_le_left _ _))
  have hcm : c < δm := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact white_hDtau_stronglyMeasurable hn κ hκ hKc _ a b Wg hWgMeas
    (hδmspec c hc0 hcm) (fun w hqK hpS => hWagree c hcρ w hqK hpS)

/-! ###############################################################################
    ### §5 — the E3d coefficient slots at `g^κ` (`hgi` / `hchr`), unconditional.
    ############################################################################### -/

/-- The inverse-metric entries `p ↦ gi^κ(p)ᵢⱼ` are measurable — the E3d `hgi` slot at the
    curved-RNC data. -/
theorem curvedRNCInv_entry_measurable (κ : ℝ) (hκ : κ ≤ 0) (i j : Fin n) :
    Measurable (fun p : Point n => curvedRNCInv κ p i j) :=
  (curvedRNCInv_contDiff κ hκ i j).continuous.measurable

/-- The Christoffel fields of `g^κ` are measurable — the E3d `hchr` slot at the curved-RNC
    data (smooth via the banked `curvedRNC_hChr`). -/
theorem curvedRNC_christoffel_measurable (κ : ℝ) (hκ : κ ≤ 0) (k i j : Fin n) :
    Measurable (fun p : Point n =>
      christoffel (curvedRNCMetric κ) (curvedRNCInv κ) k i j p) :=
  (curvedRNC_hChr κ hκ k i j).continuous.measurable

/-! ###############################################################################
    ### §6 — Non-vacuity / adversarial gates (cp466 discipline).
    ############################################################################### -/

/-- **Gate 1 — the concrete flow-ball full gate is INHABITED** (the indicator representatives
    above are not indicators over `∅`): for every `q ∈ K` and every radius `c > 0`, the point
    `(τ, φ_q(0), q)` lies in the full gate set. -/
theorem white_flowball_gate_nonempty (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) {q : Point n} (hq : q ∈ Kset) (c : ℝ) (hc : 0 < c) (τ : ℝ) :
    (τ, uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q 0, q)
      ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧
          w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c} :=
  ⟨hq, ⟨0, Metric.mem_ball_self hc, rfl⟩⟩

/-- **Gate 2 — the measured object is genuinely NONZERO at the curved fat witness** (`n = 2`,
    `κ = −1`, `K = closedBall 0 2`, the concrete flow-ball gate, cutoff `a = 1 < b = 2`): the
    whitened gated witness at the flow-ball gate is STRICTLY POSITIVE on the origin diagonal for
    every `τ > 0` (the origin is a gate point since `φ_0(0) = 0`), so the strong-measurability
    theorems above concern a non-degenerate object — not the zero kernel.  NOT `a₁ = R/6`. -/
theorem white_S1_object_nonzero_gate :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ →
      0 < whiteGatedWitness (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2)
        (fun z => uniformFlowExp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
          (curvedRNC_hChr (-1 : ℝ) (by norm_num))
          (isCompact_closedBall (0 : Point 2) 2) z '' Metric.ball (0 : Point 2) c)
        1 2 τ 0 0 := by
  intro c hc τ hτ
  have h0K : (0 : Point 2) ∈ Metric.closedBall (0 : Point 2) 2 :=
    Metric.mem_closedBall_self (by norm_num)
  have hS0 : (0 : Point 2) ∈ uniformFlowExp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
      (curvedRNC_hChr (-1 : ℝ) (by norm_num))
      (isCompact_closedBall (0 : Point 2) 2) (0 : Point 2) '' Metric.ball (0 : Point 2) c :=
    ⟨0, Metric.mem_ball_self hc,
      uniformFlowExp_zero (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
        (curvedRNC_hChr (-1 : ℝ) (by norm_num))
        (isCompact_closedBall (0 : Point 2) 2) 0 h0K⟩
  rw [whiteGatedWitness_diag_eval (-1 : ℝ) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) _ one_pos (by norm_num) τ h0K hS0]
  exact QIQTH.LeviSeries.gaussDdim_pos τ hτ _

end QIQTH.WhiteS1

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteS1
#print axioms QIQTH.WhiteS1.curvedWhitening_entry_measurable
#print axioms QIQTH.WhiteS1.whiteGcChart_measurable
#print axioms QIQTH.WhiteS1.whiteChart_rep_concrete
#print axioms QIQTH.WhiteS1.whiteCutKernelGc_measurable
#print axioms QIQTH.WhiteS1.whiteGatedWitness_value_stronglyMeasurable
#print axioms QIQTH.WhiteS1.white_witness_value_concrete
#print axioms QIQTH.WhiteS1.whiteTauDerivRep_measurable
#print axioms QIQTH.WhiteS1.whiteWitness_tauDeriv_eq_rep
#print axioms QIQTH.WhiteS1.white_hDtau_stronglyMeasurable
#print axioms QIQTH.WhiteS1.white_hDtau_concrete
#print axioms QIQTH.WhiteS1.curvedRNCInv_entry_measurable
#print axioms QIQTH.WhiteS1.curvedRNC_christoffel_measurable
#print axioms QIQTH.WhiteS1.white_flowball_gate_nonempty
#print axioms QIQTH.WhiteS1.white_S1_object_nonzero_gate
end AxiomChecks
