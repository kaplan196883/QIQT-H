/-
  WhiteS1P2 — J4-631: S1-b AT THE WHITENED WITNESS — the hP2 SECOND field-`pd`
  measurable-representative slot (the largest remaining slice of the whitened S1 campaign;
  J4-629 = WhiteS1P1 landed hP1, J4-630 = WhiteCollar discharged hOffS AND pre-discharged the
  hOffS2 shape this file consumes).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: S1-c (the E3d assembly at the whitened witness, consuming this file's hP2 + the banked
  hDτ/hP1/hgi/hchr) + `hlam8` (`lam ≤ 8`, opaque `C₀`) + `K1TransportBudget` + the fat-`K` carrier
  piles + the capstone co-instantiation at the whitened witness + the prior analytic piles.
  This brick is the hP2 slice ONLY.

  ── THE TARGET (S1-b).  The `hP2` slot of `HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields`
     at `G := whiteGatedWitness`:
        `∀ i j, StronglyMeasurable (fun w => pd (fun y => pd (fun x => G w.1 x w.2.2) j y) i w.2.1)`
     (one fixed index pair here; the `∀ i j` closure happens at the S1-c instantiation).

  ── THE ROUTE (WhiteS1P1 mirrored ONE ORDER UP; the as-built precedent =
     `AmpPdComposition.ampFieldSecondPd_measurable`'s second difference-quotient):
       (1) the RAW second field-`pd` kernel `whiteFieldDeriv2 := pd_i (pd_j (G τ · q)) p` (§0);
       (2) the EVERYWHERE dichotomy (§1/§2): off-base and τ ≤ 0 it vanishes outright (the inner
           field slot is identically `0`); on the OPEN gate it equals the second field-`pd` of the
           UNGATED whitened cutoff kernel (germ congruence one level up — the inner `pd_j`s agree
           on the open gate by J4-629's `whiteFieldDeriv_gate_congr`); off the gate CLOSURE it
           vanishes (nested-germ trick); the gate-frontier leg `hOffS2` is SERVED by J4-630's
           `white_hOffS2_discharged`;
       (3) the on-gate measurable representative (§4) via a SECOND difference quotient: the banked
           abstract engine `measurable_dq_witness` in direction `i` applied to
           `fld τ q := pd_j (whiteCutKernel τ · q)` with `AG :=` the J4-629 FIRST-`pd` witness `Af`
           (`white_pdRep_concrete` at `j` — its global measurability is banked; the on-gate value
           swap is its on-gate value).  The order-2 bookkeeping: `PdiffAt (pd_j F) i p` from
           `ContDiffAt ℝ 2 F p` (`LaplaceBeltrami.PdiffAt_pd_of_contDiffAt`), with
           `F := whiteCutKernel(τ,·,q)` `C²` at chart-reachable points — cutoff `C^∞` ∘ (linear
           whitening ∘ chart-`C²`) × const × Gaussian `C^∞` ∘ (same) (`whiteCut_contDiffAt_of_chartC2`,
           §3; NO τ-case-split needed — `gaussDdim_contDiff` holds for every `τ`);
       (4) assembly: `whiteP2Rep` full-gate indicator + the everywhere identity ⟹
           ★ `white_hP2_stronglyMeasurable` (abstract), ★★ `white_hP2_concrete` (concrete gates,
           `hOffS2` carried), ★★ `white_hP2_unconditional` (`hOffS2` DISCHARGED by J4-630;
           radii `0 < a < b < c < δ₀`, the collar window).

  ── THE ORDER-2 JET LAYER (documentation of the on-gate structure, NOT needed by the measurable
     route — the same honest division as J4-629's `whiteFlowJet_concrete`/`whiteCut_pd_gate_eq`):
       ▸ `whiteFlowSecondJet_concrete` (§5) — the WHITENED second field-jet: the banked measurable
         chart second jet (`FlowDerivMeasurable.flowInverseSecondJet_measurable_component` at
         `g^κ/gi^κ`) pushed through the LINEAR whitening `whiteUnvel_q` (the same finite bilinear
         form of Borel entries as J4-629, applied to BOTH jet levels) — globally measurable
         `Pjw`/`Qw` + the on-gate first-jet FAMILY and mixed second jet;
       ▸ `whiteGauss_pd_pd_gate_eq` / ★ `whiteGauss_pd_pd_gate_concrete` (§6) — the on-gate MIXED
         second-`pd` normal form of the whitened Gaussian factor,
           `pd_i(pd_j(G_τ∘V̂)) = G_τ(V̂)·[⟨V̂,Pi⟩⟨V̂,Pj⟩/4τ² − (⟨Pi,Pj⟩+⟨V̂,Q⟩)/2τ]`,
         via the banked NEIGHBOURHOOD mixed Leibniz–Gaussian engine
         (`Field2NbhdReshape.gaussComp_pd_pd_mixed_nbhd`) at the whitened jets.  ⚠ HONEST: the
         FULL cutoff×amplitude×Gaussian second-Leibniz expansion is NOT claimed (the cutoff-`pd`
         factors have no banked closed form — same discipline as J4-629 at order 1); the
         measurable hP2 route (§4) does not need it.

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteCollar
import QIQTH.Field2NbhdReshape

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.EquivProbe
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteS1
open QIQTH.WhiteS1P1 QIQTH.WhiteCollar QIQTH.HeatParametrixOrder
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace QIQTH.WhiteS1P2

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ###############################################################################
    ### §0 — the raw SECOND field-`pd` kernel of the whitened gated witness.
    ############################################################################### -/

/-- **`whiteFieldDeriv2` — the raw MIXED SECOND field-`pd` kernel** of the whitened gated
    witness: `pd_i (pd_j (whiteGatedWitness τ · q)) p` — the exact integrand of the E3d `hP2`
    slot at `G := whiteGatedWitness` (one order up from `WhiteS1P1.whiteFieldDeriv`). -/
noncomputable def whiteFieldDeriv2 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (τ : ℝ) (p q : Point n) : ℝ :=
  pd (fun y : Point n =>
    pd (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q) j y) i p

/-! ###############################################################################
    ### §1 — outright vanishing legs + the on-gate germ congruence (one level up).
    ############################################################################### -/

/-- Off the BASE gate (`q ∉ K`) the witness is identically `0` in the field slot, so BOTH nested
    field-`pd`s vanish. -/
theorem whiteFieldDeriv2_offBase_eq_zero (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (τ : ℝ) (p q : Point n) (hq : q ∉ Kset) :
    whiteFieldDeriv2 κ hκ hKc S a b i j τ p q = 0 := by
  have hzero : (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q)
      = fun _ : Point n => (0 : ℝ) := by
    funext x
    show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ x q = 0
    exact gatedKernel_apply_of_notMem Kset S _ τ x q (Or.inl hq)
  unfold whiteFieldDeriv2
  rw [hzero]
  have hin : (fun y : Point n => pd (fun _ : Point n => (0 : ℝ)) j y)
      = fun _ : Point n => (0 : ℝ) := funext fun y => pd_const 0 j y
  rw [hin]
  exact pd_const 0 i p

/-- At `τ ≤ 0` the whitened witness is identically `0` in the field slot, so both nested
    field-`pd`s vanish — the junk-value coherence leg one order up. -/
theorem whiteFieldDeriv2_eq_zero_of_nonpos (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (p q : Point n) (hτ : τ ≤ 0) :
    whiteFieldDeriv2 κ hκ hKc S a b i j τ p q = 0 := by
  have hzero : (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q)
      = fun _ : Point n => (0 : ℝ) := by
    funext x
    show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ x q = 0
    by_cases hg : q ∈ Kset ∧ x ∈ S q
    · rw [gatedKernel_apply_of_mem Kset S _ τ hg.1 hg.2]
      simp only [whiteCutKernel, whiteAmbientKernel]
      rw [QIQTH.InnerKernelJointMeas.gaussDdim_eq_zero_of_nonpos hn τ _ hτ, mul_zero, mul_zero]
    · exact gatedKernel_apply_of_notMem Kset S _ τ x q (not_and_or.mp hg)
  unfold whiteFieldDeriv2
  rw [hzero]
  have hin : (fun y : Point n => pd (fun _ : Point n => (0 : ℝ)) j y)
      = fun _ : Point n => (0 : ℝ) := funext fun y => pd_const 0 j y
  rw [hin]
  exact pd_const 0 i p

/-- **On-gate germ congruence, order 2** — at an OPEN gate point the second field-`pd` of the
    GATED witness equals the second field-`pd` of the UNGATED whitened cutoff kernel: the inner
    `pd_j`s agree at every point OF the open gate (J4-629's `whiteFieldDeriv_gate_congr`), and
    the gate is a neighbourhood of `p`, so the outer `pd_i` transports. -/
theorem whiteFieldDeriv2_gate_congr (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (τ : ℝ) (q p : Point n) (hq : q ∈ Kset) (hSopen : IsOpen (S q)) (hp : p ∈ S q) :
    whiteFieldDeriv2 κ hκ hKc S a b i j τ p q
      = pd (fun y : Point n =>
          pd (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q) j y) i p := by
  have hev : (fun y : Point n =>
        pd (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q) j y)
      =ᶠ[𝓝 p] (fun y : Point n =>
        pd (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q) j y) := by
    refine eventually_nhds_iff.mpr ⟨S q, ?_, hSopen, hp⟩
    intro y hy
    exact whiteFieldDeriv_gate_congr κ hκ hKc S a b j τ q y hq hSopen hy
  unfold whiteFieldDeriv2
  exact pd_congr_of_eventuallyEq _ _ i p hev

/-- **★ Off-CLOSURE vanishing, order 2** — at every `p ∉ closure (S q)` the witness is
    identically `0` on a neighbourhood of `p`, so BOTH nested field-`pd`s vanish (the J4-630
    nested-germ trick).  Consequence: the `hOffS2` input's remaining content is EXACTLY the gate
    frontier `∂(S q)` — and at the concrete flow-ball gates it is FULLY discharged by J4-630's
    `white_hOffS2_discharged`.  NOT `a₁ = R/6`. -/
theorem whiteFieldDeriv2_eq_zero_off_closure (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    (τ : ℝ) (q p : Point n) (hp : p ∉ closure (S q)) :
    whiteFieldDeriv2 κ hκ hKc S a b i j τ p q = 0 := by
  have hU : IsOpen ((closure (S q))ᶜ) := isOpen_compl_iff.mpr isClosed_closure
  have hev : (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q)
      =ᶠ[𝓝 p] (fun _ : Point n => (0 : ℝ)) := by
    refine Filter.eventuallyEq_of_mem (hU.mem_nhds hp) ?_
    intro x hx
    show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ x q = 0
    exact gatedKernel_apply_of_notMem Kset S _ τ x q
      (Or.inr (fun hxS => hx (subset_closure hxS)))
  have hev2 : (fun y : Point n =>
      pd (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q) j y)
      =ᶠ[𝓝 p] (fun _ : Point n => (0 : ℝ)) := by
    have hnest := (eventually_eventually_nhds (p := fun x =>
      (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q) x
        = (fun _ : Point n => (0 : ℝ)) x)).mpr hev
    filter_upwards [hnest] with y hy
    rw [pd_congr_of_eventuallyEq _ _ j y hy]
    exact pd_const 0 j y
  unfold whiteFieldDeriv2
  rw [pd_congr_of_eventuallyEq _ _ i p hev2]
  exact pd_const 0 i p

/-! ###############################################################################
    ### §2 — the FULL-gate indicator representative and the EVERYWHERE identity.
    ############################################################################### -/

/-- **`whiteP2Rep` — the FULL-gate re-gated `hP2` representative**: the indicator of an on-gate
    representative `Af2` of the ungated SECOND field-`pd` on the full gate (the exact
    `whiteP1Rep` outer-indicator shape, one order up, with the on-gate body OPAQUE). -/
noncomputable def whiteP2Rep (Kset : Set (Point n)) (S : Point n → Set (Point n))
    (Af2 : ℝ → Point n → Point n → ℝ) : ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2}
    (fun w => Af2 w.1 w.2.2 w.2.1)

/-- **★ `whiteP2Rep_measurable`** — joint `(τ,p,q)`-Borel measurability from the measurability of
    `Af2` plus the full-gate `MeasurableSet` (no continuity anywhere).  NOT `a₁ = R/6`. -/
theorem whiteP2Rep_measurable (Kset : Set (Point n)) (S : Point n → Set (Point n))
    (Af2 : ℝ → Point n → Point n → ℝ)
    (hAf2Meas : Measurable (fun w : ℝ × Point n × Point n => Af2 w.1 w.2.2 w.2.1))
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2}) :
    Measurable (whiteP2Rep Kset S Af2) :=
  hAf2Meas.indicator hKSmeas

/-- **★ `whiteFieldDeriv2_eq_whiteP2Rep` — THE EVERYWHERE IDENTITY, order 2.**  At EVERY
    `(τ,p,q)` the raw second field-`pd` kernel equals the full-gate representative:
      • FULL gate — germ congruence (order 2) to the ungated kernel + the on-gate value of `Af2`;
      • `q ∈ K`, `p ∉ S q` — `τ > 0`: the `hOffS2` input (DISCHARGED at the concrete gates by
        J4-630's `white_hOffS2_discharged`); `τ ≤ 0`: the junk-value coherence leg;
      • `q ∉ K`: outright vanishing.
    NOT `a₁ = R/6`. -/
theorem whiteFieldDeriv2_eq_whiteP2Rep (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n))
    (a b : ℝ) (i j : Fin n) (Af2 : ℝ → Point n → Point n → ℝ)
    (hSopen : ∀ q ∈ Kset, IsOpen (S q))
    (hAf2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        Af2 w.1 w.2.2 w.2.1
          = pd (fun y : Point n =>
              pd (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        whiteFieldDeriv2 κ hκ hKc S a b i j w.1 w.2.1 w.2.2 = 0) :
    ∀ w : ℝ × Point n × Point n,
      whiteFieldDeriv2 κ hκ hKc S a b i j w.1 w.2.1 w.2.2 = whiteP2Rep Kset S Af2 w := by
  intro w
  simp only [whiteP2Rep]
  by_cases hg : w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2
  · rw [Set.indicator_of_mem
      (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2} from hg),
      hAf2 w hg.1 hg.2]
    exact whiteFieldDeriv2_gate_congr κ hκ hKc S a b i j w.1 w.2.2 w.2.1 hg.1
      (hSopen _ hg.1) hg.2
  · rw [Set.indicator_of_notMem
      (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2} from hg)]
    by_cases hqK : w.2.2 ∈ Kset
    · have hpS : w.2.1 ∉ S w.2.2 := fun h => hg ⟨hqK, h⟩
      by_cases hτ : 0 < w.1
      · exact hOffS2 w hqK hτ hpS
      · exact whiteFieldDeriv2_eq_zero_of_nonpos hn κ hκ hKc S a b i j w.1 w.2.1 w.2.2
          (not_lt.mp hτ)
    · exact whiteFieldDeriv2_offBase_eq_zero κ hκ hKc S a b i j w.1 w.2.1 w.2.2 hqK

/-- **★ `white_hP2_stronglyMeasurable` — the E3d `hP2` slot shape at ANY measurable open gate
    with an on-gate second-`pd` representative**: the second field-`pd` derivative field of the
    whitened gated witness is jointly strongly measurable — EXACTLY the `hP2` antecedent of
    `HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields` at `G := whiteGatedWitness` (one fixed
    index pair `(i,j)`; the `∀ i j` closure happens at the S1-c instantiation).
    NOT `a₁ = R/6`. -/
theorem white_hP2_stronglyMeasurable (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n))
    (a b : ℝ) (i j : Fin n) (Af2 : ℝ → Point n → Point n → ℝ)
    (hAf2Meas : Measurable (fun w : ℝ × Point n × Point n => Af2 w.1 w.2.2 w.2.1))
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2})
    (hSopen : ∀ q ∈ Kset, IsOpen (S q))
    (hAf2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        Af2 w.1 w.2.2 w.2.1
          = pd (fun y : Point n =>
              pd (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        whiteFieldDeriv2 κ hκ hKc S a b i j w.1 w.2.1 w.2.2 = 0) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y : Point n =>
        pd (fun x : Point n => whiteGatedWitness κ hκ hKc S a b w.1 x w.2.2) j y) i w.2.1) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun y : Point n =>
          pd (fun x : Point n => whiteGatedWitness κ hκ hKc S a b w.1 x w.2.2) j y) i w.2.1)
      = whiteP2Rep Kset S Af2 := by
    funext w
    show whiteFieldDeriv2 κ hκ hKc S a b i j w.1 w.2.1 w.2.2 = whiteP2Rep Kset S Af2 w
    exact whiteFieldDeriv2_eq_whiteP2Rep hn κ hκ hKc S a b i j Af2 hSopen hAf2 hOffS2 w
  rw [hrw]
  exact (whiteP2Rep_measurable Kset S Af2 hAf2Meas hKSmeas).stronglyMeasurable

/-! ###############################################################################
    ### §3 — the order-2 on-gate regularity: `whiteCutKernel` is `C²` at chart-`C²` points.
    ############################################################################### -/

/-- **On-gate `C²` of the ungated whitened cutoff kernel** from chart `C²`: the field slice
    `x ↦ χ_{a,b}(V̂_q x)·(√det g^κ(q)·G_τ(V̂_q x))` is `ContDiffAt ℝ 2` wherever the raw chart
    is `C²` — the cutoff and the Gaussian are `C^∞` (`radialCutoff_contDiff`,
    `gaussDdim_contDiff`, the latter for EVERY `τ`, so no τ-case-split), the whitening
    `whiteUnvel_q` is a continuous linear map, and the amplitude is field-constant.  This is the
    ONLY order-2 regularity input of the second difference quotient (§4).  NOT `a₁ = R/6`. -/
theorem whiteCut_contDiffAt_of_chartC2 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b τ : ℝ) (q p : Point n)
    (hC2 : ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) p) :
    ContDiffAt ℝ 2 (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q) p := by
  have hlin : ContDiffAt ℝ 2 (fun v : Point n => whiteUnvel κ q v)
      (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q p) :=
    ((whiteUnvel κ q).contDiff).contDiffAt
  have hV : ContDiffAt ℝ 2 (fun x : Point n => whiteInvChart κ hκ hKc q x) p := by
    have h := hlin.comp p hC2
    simpa [whiteInvChart, Function.comp] using h
  have hχ : ContDiffAt ℝ 2
      (fun x : Point n => radialCutoff a b (whiteInvChart κ hκ hKc q x)) p := by
    have hcut : ContDiffAt ℝ 2 (radialCutoff a b : Point n → ℝ)
        (whiteInvChart κ hκ hKc q p) :=
      (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have h := hcut.comp p hV
    simpa [Function.comp] using h
  have hG : ContDiffAt ℝ 2
      (fun x : Point n => gaussDdim τ (whiteInvChart κ hκ hKc q x)) p := by
    have hgauss : ContDiffAt ℝ 2 (fun v : Point n => gaussDdim τ v)
        (whiteInvChart κ hκ hKc q p) :=
      (gaussDdim_contDiff τ).contDiffAt.of_le le_top
    have h := hgauss.comp p hV
    simpa [Function.comp] using h
  have hrw : (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q)
      = fun x : Point n => radialCutoff a b (whiteInvChart κ hκ hKc q x)
          * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
              * gaussDdim τ (whiteInvChart κ hκ hKc q x)) := by
    funext x
    simp only [whiteCutKernel, whiteAmbientKernel]
  rw [hrw]
  exact hχ.mul (contDiffAt_const.mul hG)

/-! ###############################################################################
    ### §4 — the concrete flow-ball-gate instantiation: the SECOND difference quotient.
    ############################################################################### -/

/-- **★ `white_pd2Rep_concrete` — the measurable on-gate SECOND-`pd` representative at the
    concrete flow-ball gates**: a single `δ₀ > 0` such that for every gate radius `0 < c < δ₀`
    there is a GLOBALLY MEASURABLE `Af2` agreeing on the full gate with the mixed second
    field-`pd` of the ungated whitened cutoff kernel.  Route: the banked ABSTRACT
    difference-quotient engine (`AmpPdComposition.measurable_dq_witness`) in direction `i` at
    `fld τ q := pd_j (whiteCutKernel τ · q)` with `AG :=` the J4-629 FIRST-`pd` witness `Af`
    (`white_pdRep_concrete` at `j`); the on-gate `PdiffAt` of the first `pd` from
    `PdiffAt_pd_of_contDiffAt` at the §3 `C²` (chart-`C²` reachability).  The as-built precedent:
    `AmpPdComposition.ampFieldSecondPd_measurable`, verbatim one whitening over.
    NOT `a₁ = R/6`. -/
theorem white_pd2Rep_concrete (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (i j : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∃ Af2 : ℝ → Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => Af2 w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset →
            w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
            Af2 w.1 w.2.2 w.2.1
              = pd (fun y : Point n =>
                  pd (fun x : Point n =>
                    whiteCutKernel κ hκ hKc a b w.1 x w.2.2) j y) i w.2.1) := by
  obtain ⟨δ₁, hδ₁, hrep⟩ := white_pdRep_concrete hn κ hκ hKc a b j
  obtain ⟨δm, hδm, hδmspec⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δr, hδr, hreach⟩ := QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨min (min δ₁ δm) (min δr δo), lt_min (lt_min hδ₁ hδm) (lt_min hδr hδo), ?_⟩
  intro c hc0 hcδ
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδr : c < δr := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Af, hAfMeas, hAfval⟩ := hrep c hc0 hcδ₁
  obtain ⟨Af2, hAf2Meas, hAf2val⟩ := QIQTH.AmpPdComposition.measurable_dq_witness (K := Kset)
    (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc) c i
    (fun τ q => fun y : Point n =>
      pd (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q) j y)
    Af
    hAfMeas
    (hδmspec c hc0 hcδm)
    (fun q hq => ((hopen q hq).2 c hc0 hcδo).1)
    (by
      -- on-gate PdiffAt of the FIRST pd from the §3 C² (chart-C² reachability).
      intro w hqK hpImg
      obtain ⟨v, hv, hvp⟩ := hpImg
      have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
      have hC2 : ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w.2.2) w.2.1 := by
        rw [← hvp]
        exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
      have hK2 : ContDiffAt ℝ 2
          (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) w.2.1 :=
        whiteCut_contDiffAt_of_chartC2 κ hκ hKc a b w.1 w.2.2 w.2.1 hC2
      exact QIQTH.LaplaceBeltrami.PdiffAt_pd_of_contDiffAt
        (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) j i w.2.1 hK2)
    (by
      -- on-gate value swap: the first pd equals the J4-629 measurable first witness Af.
      intro w hqK p hp
      exact (hAfval (w.1, p, w.2.2) hqK hp).symm)
  exact ⟨Af2, hAf2Meas, fun w hqK hpS => hAf2val w hqK hpS⟩

/-- **★★ `white_hP2_concrete` — the `hP2` E3d slot at the concrete flow-ball gates** (mirroring
    `white_hP1_concrete`'s shape): a single `δ₀ > 0` such that for every gate radius
    `0 < c < δ₀`, GIVEN the off-`S` input `hOffS2` (DISCHARGED at radii `0 < a < b < c` by
    J4-630's `white_hOffS2_discharged` — consumed in ★★ `white_hP2_unconditional` below), the
    whitened gated witness's mixed second field-`pd` derivative field is jointly strongly
    measurable — slot 3 of the 3 derivative fields of the whitened S1
    (`triple_hEmeas_of_borel_deriv_fields`).  NOT `a₁ = R/6`. -/
theorem white_hP2_concrete (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (i j : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
          w.2.1 ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
          pd (fun y : Point n =>
            pd (fun x : Point n => whiteGatedWitness κ hκ hKc
              (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
              w.1 x w.2.2) j y) i w.2.1 = 0) →
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        pd (fun y : Point n =>
          pd (fun x : Point n => whiteGatedWitness κ hκ hKc
            (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
            w.1 x w.2.2) j y) i w.2.1) := by
  obtain ⟨δ₁, hδ₁, hrep⟩ := white_pd2Rep_concrete hn κ hκ hKc a b i j
  obtain ⟨δm, hδm, hδmspec⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨min δ₁ (min δm δo), lt_min hδ₁ (lt_min hδm hδo), ?_⟩
  intro c hc0 hcδ hOffS2
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Af2, hAf2Meas, hAf2val⟩ := hrep c hc0 hcδ₁
  exact white_hP2_stronglyMeasurable hn κ hκ hKc
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b i j Af2 hAf2Meas
    (hδmspec c hc0 hcδm)
    (fun q hq => ((hopen q hq).2 c hc0 hcδo).1)
    (fun w hq hp => hAf2val w hq hp)
    hOffS2

/-- **★★ `white_hP2_unconditional` — the `hP2` slot with `hOffS2` DISCHARGED.**  At the concrete
    flow-ball gates (radii `0 < a < b < c < δ₀`, the J4-630 collar window), the whitened gated
    witness's mixed second field-`pd` derivative field is jointly strongly measurable — the exact
    `hP2` antecedent of `HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields` at
    `G := whiteGatedWitness` (fixed `(i,j)`; `∀ i j` closes at S1-c), with NO carried
    measurability-side input: chart rep, gate measurability, gate openness, the on-gate
    second-`pd` representative (this file) AND the off-`S` collar (J4-630's
    `white_hOffS2_discharged`) are all discharged from geometry.  NOT `a₁ = R/6`. -/
theorem white_hP2_unconditional (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (ha : 0 < a) (hab : a < b) (i j : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        pd (fun y : Point n =>
          pd (fun x : Point n => whiteGatedWitness κ hκ hKc
            (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
            w.1 x w.2.2) j y) i w.2.1) := by
  obtain ⟨δ₁, hδ₁, hP2⟩ := white_hP2_concrete hn κ hκ hKc a b i j
  obtain ⟨δ₂, hδ₂, hOff2⟩ := white_hOffS2_discharged κ hκ hKc a b ha hab i j
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro c hbc hcδ
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  exact hP2 c hc0 (lt_of_lt_of_le hcδ (min_le_left _ _))
    (hOff2 c hbc (lt_of_lt_of_le hcδ (min_le_right _ _)))

/-! ###############################################################################
    ### §5 — the WHITENED second field-jet (the order-2 jet composition).
    ############################################################################### -/

/-- **★ `whiteFlowSecondJet_concrete` — the WHITENED second field-jet, measurable + on-gate
    values.**  The banked measurable chart SECOND jet
    (`FlowDerivMeasurable.flowInverseSecondJet_measurable_component` at `g^κ/gi^κ`) pushed
    through the LINEAR whitening — the SAME finite bilinear form of Borel entries as J4-629's
    `whiteFlowJet_concrete`, applied at BOTH jet levels (the whitening is field-constant, so the
    `i`-line derivative of the whitened first-jet family is the whitened mixed second jet):
      • `Pjw`/`Qw` globally measurable (∀ components);
      • on the full gate: the gate is OPEN, `Pjw` is the `j`-line first-jet FAMILY of the
        WHITENED chart on the whole gate, and `Qw` is its `i`-line derivative at the gate point.
    This is the order-2 analogue of the S1-a jet supplier; §6 consumes it.  NOT `a₁ = R/6`. -/
theorem whiteFlowSecondJet_concrete (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (i j : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∃ Pjw Qw : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjw w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qw w.2.2 w.2.1 k))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
            w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
            IsOpen (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c)
            ∧ (∀ y ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c, ∀ k,
                HasDerivAt
                  (fun s : ℝ => whiteInvChart κ hκ hKc w.2.2 (Function.update y j s) k)
                  (Pjw w.2.2 y k) (y j))
            ∧ (∀ k, HasDerivAt
                (fun s : ℝ => Pjw w.2.2 (Function.update w.2.1 i s) k)
                (Qw w.2.2 w.2.1 k) (w.2.1 i))) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := QIQTH.FlowDerivMeasurable.flowInverseSecondJet_measurable_component
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc i j
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  obtain ⟨Pjf, Qf, hPjmeas, hQmeas, hgate⟩ := hspec c hc0 hcδ
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) rfl
  refine ⟨fun q p k => ∑ m, (∑ l, curvedRNCMetric κ q k l * curvedWhitening κ q l m)
      * Pjf q p m,
    fun q p k => ∑ m, (∑ l, curvedRNCMetric κ q k l * curvedWhitening κ q l m)
      * Qf q p m, ?_, ?_, ?_⟩
  · -- measurability of `Pjw`: bilinear form of Borel entries × the banked measurable jet.
    intro k
    refine Finset.measurable_sum _ (fun m _ => Measurable.mul ?_ (hPjmeas m))
    refine Finset.measurable_sum _ (fun l _ => Measurable.mul ?_ ?_)
    · exact (curvedRNCMetric_entry_measurable κ k l).comp measurable_snd.snd
    · exact (curvedWhitening_entry_measurable κ l m).comp measurable_snd.snd
  · -- measurability of `Qw`: identical shape at the second jet.
    intro k
    refine Finset.measurable_sum _ (fun m _ => Measurable.mul ?_ (hQmeas m))
    refine Finset.measurable_sum _ (fun l _ => Measurable.mul ?_ ?_)
    · exact (curvedRNCMetric_entry_measurable κ k l).comp measurable_snd.snd
    · exact (curvedWhitening_entry_measurable κ l m).comp measurable_snd.snd
  · -- on-gate jets: linear combinations of the banked chart jets.
    intro w hqK hτ hpS
    obtain ⟨hSopen, hPj, hQ⟩ := hgate w hqK hτ hpS
    refine ⟨hSopen, ?_, ?_⟩
    · -- first-jet FAMILY of the whitened chart on the gate.
      intro y hy k
      have h1 : HasDerivAt
          (fun s : ℝ => ∑ m, (∑ l, curvedRNCMetric κ w.2.2 k l * curvedWhitening κ w.2.2 l m)
              * uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
                  (curvedRNC_hChr κ hκ) hKc w.2.2 (Function.update y j s) m)
          (∑ m, (∑ l, curvedRNCMetric κ w.2.2 k l * curvedWhitening κ w.2.2 l m)
              * Pjf w.2.2 y m) (y j) :=
        HasDerivAt.fun_sum (fun m _ => (hPj y hy m).const_mul _)
      have h2 : (fun s : ℝ => whiteInvChart κ hκ hKc w.2.2 (Function.update y j s) k)
          = (fun s : ℝ =>
              ∑ m, (∑ l, curvedRNCMetric κ w.2.2 k l * curvedWhitening κ w.2.2 l m)
                * uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
                    (curvedRNC_hChr κ hκ) hKc w.2.2 (Function.update y j s) m) := by
        funext s
        simp only [whiteInvChart, whiteUnvel, matToCLM_apply]
      rw [h2]
      exact h1
    · -- mixed second jet: the `i`-line derivative of the whitened first-jet family
      -- (the whitening coefficients are field-constant).
      intro k
      exact HasDerivAt.fun_sum (fun m _ => (hQ m).const_mul _)

/-! ###############################################################################
    ### §6 — the on-gate MIXED second-`pd` normal form of the whitened Gaussian.
    ############################################################################### -/

/-- **`whiteGauss_pd_pd_gate_eq` — the mixed second-`pd` Leibniz–Gaussian normal form at the
    whitened chart** (abstract jets): with `V̂ = whiteInvChart_q`, an `i`-line jet `Piw` at `x₀`,
    a `j`-line jet FAMILY `Pjw` on an open `U ∋ x₀`, and the mixed second jet `Q` at `x₀`,
      `pd_i(pd_j(G_τ∘V̂))(x₀) = G_τ(V̂ x₀)·[⟨V̂,Piw⟩⟨V̂,Pjw⟩/(4τ²) − (⟨Piw,Pjw⟩+⟨V̂,Q⟩)/(2τ)]`.
    Direct instantiation of the banked NEIGHBOURHOOD mixed engine
    (`Field2NbhdReshape.gaussComp_pd_pd_mixed_nbhd`).  ⚠ HONEST: this is the GAUSSIAN factor
    only; the full cutoff×amplitude second Leibniz is NOT claimed (J4-629 discipline), and the
    measurable route (§4) does not consume this identity.  NOT `a₁ = R/6`. -/
theorem whiteGauss_pd_pd_gate_eq (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (i j : Fin n) (τ : ℝ) (hτ : 0 < τ) (q x₀ : Point n)
    (U : Set (Point n)) (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (Piw : Fin n → ℝ) (Pjw : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hVi : ∀ k, HasDerivAt
      (fun s : ℝ => whiteInvChart κ hκ hKc q (Function.update x₀ i s) k) (Piw k) (x₀ i))
    (hVj : ∀ y ∈ U, ∀ k, HasDerivAt
      (fun s : ℝ => whiteInvChart κ hκ hKc q (Function.update y j s) k) (Pjw y k) (y j))
    (hQ : ∀ k, HasDerivAt
      (fun s : ℝ => Pjw (Function.update x₀ i s) k) (Q k) (x₀ i)) :
    pd (fun y : Point n =>
        pd (fun z : Point n => gaussDdim τ (whiteInvChart κ hκ hKc q z)) j y) i x₀
      = gaussDdim τ (whiteInvChart κ hκ hKc q x₀)
        * ((∑ k, whiteInvChart κ hκ hKc q x₀ k * Piw k)
              * (∑ k, whiteInvChart κ hκ hKc q x₀ k * Pjw x₀ k) / (4 * τ ^ 2)
            - ((∑ k, Piw k * Pjw x₀ k)
                + (∑ k, whiteInvChart κ hκ hKc q x₀ k * Q k)) / (2 * τ)) :=
  QIQTH.Field2NbhdReshape.gaussComp_pd_pd_mixed_nbhd (whiteInvChart κ hκ hKc q)
    (fun _ => Piw) Pjw Q τ hτ i j x₀ U hU hx₀ hVi hVj hQ

/-- **★ `whiteGauss_pd_pd_gate_concrete` — the on-gate mixed second-`pd` identity at the
    CONCRETE flow-ball gates**: for every gate radius `0 < c < δ₀` there are globally measurable
    whitened jets `Pjw`/`Qw` (§5) such that at every on-gate point, GIVEN any `i`-line jet `Piw`
    of the whitened chart there (satisfiable — §7 gate 4), the mixed second `pd` of the whitened
    Gaussian factor equals the §6 normal form at `(Piw, Pjw, Qw)`.  This documents the on-gate
    order-2 structure the S1-b DQ route rests on.  NOT `a₁ = R/6`. -/
theorem whiteGauss_pd_pd_gate_concrete (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (i j : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∃ Pjw Qw : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjw w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qw w.2.2 w.2.1 k))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
            w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
            ∀ Piw : Fin n → ℝ,
              (∀ k, HasDerivAt (fun s : ℝ =>
                  whiteInvChart κ hκ hKc w.2.2 (Function.update w.2.1 i s) k)
                (Piw k) (w.2.1 i)) →
              pd (fun y : Point n =>
                  pd (fun z : Point n =>
                    gaussDdim w.1 (whiteInvChart κ hκ hKc w.2.2 z)) j y) i w.2.1
                = gaussDdim w.1 (whiteInvChart κ hκ hKc w.2.2 w.2.1)
                  * ((∑ k, whiteInvChart κ hκ hKc w.2.2 w.2.1 k * Piw k)
                        * (∑ k, whiteInvChart κ hκ hKc w.2.2 w.2.1 k * Pjw w.2.2 w.2.1 k)
                        / (4 * w.1 ^ 2)
                      - ((∑ k, Piw k * Pjw w.2.2 w.2.1 k)
                          + (∑ k, whiteInvChart κ hκ hKc w.2.2 w.2.1 k * Qw w.2.2 w.2.1 k))
                        / (2 * w.1))) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := whiteFlowSecondJet_concrete κ hκ hKc i j
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  obtain ⟨Pjw, Qw, hPjmeas, hQmeas, hgate⟩ := hspec c hc0 hcδ
  refine ⟨Pjw, Qw, hPjmeas, hQmeas, ?_⟩
  intro w hqK hτ hpS Piw hPiw
  obtain ⟨hSopen, hPj, hQ⟩ := hgate w hqK hτ hpS
  exact whiteGauss_pd_pd_gate_eq κ hκ hKc i j w.1 hτ w.2.2 w.2.1
    (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c)
    hSopen hpS Piw (fun y => Pjw w.2.2 y) (fun k => Qw w.2.2 w.2.1 k)
    hPiw (fun y hy k => hPj y hy k) (fun k => hQ k)

/-! ###############################################################################
    ### §7 — Non-vacuity / adversarial gates (cp466 discipline).
    ############################################################################### -/

/-- **Gate 1 — the full-gate indicator set is INHABITED** at the concrete flow-ball gates (the
    `whiteP2Rep` indicator is not an indicator over `∅`): re-export of the J4-628 gate. -/
theorem white_hP2_gate_nonempty (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) {q : Point n} (hq : q ∈ Kset) (c : ℝ) (hc : 0 < c) (τ : ℝ) :
    (τ, uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q 0, q)
      ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧
          w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c} :=
  QIQTH.WhiteS1.white_flowball_gate_nonempty κ hκ hKc hq c hc τ

/-- **Gate 2 — the radius window of ★★ `white_hP2_unconditional` is SATISFIABLE at every chart
    radius**: re-export of the J4-630 constraint-system gate (`0 < a < b < c < δ₀` solvable for
    EVERY `δ₀ > 0`; the radii are free parameters chosen at assembly time).  ⚠ HONEST: for a
    FIXED `(a,b)` chosen before the chart radius, `b < δ₀` is not provable (`δ₀` opaque) — the
    same carried discipline as J4-630/J4-235. -/
theorem white_hP2_radii_satisfiable :
    ∀ δ₀ : ℝ, 0 < δ₀ → ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧ c < δ₀ :=
  QIQTH.WhiteCollar.white_collar_radii_satisfiable

/-- **Gate 3 — the measured object is genuinely NONZERO at the curved fat witness** (`n = 2`,
    `κ = −1`, `K = closedBall 0 2`, concrete flow-ball gate, cutoff `1 < 2`): the underlying
    whitened gated witness is strictly positive on the origin diagonal for every `τ > 0` — the
    `hP2` slot measures the second derivative field of a non-degenerate kernel, not of `0`.
    Re-export of the J4-628 object gate.  NOT `a₁ = R/6`. -/
theorem white_hP2_underlying_nonzero :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ →
      0 < whiteGatedWitness (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2)
        (fun z => uniformFlowExp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
          (curvedRNC_hChr (-1 : ℝ) (by norm_num))
          (isCompact_closedBall (0 : Point 2) 2) z '' Metric.ball (0 : Point 2) c)
        1 2 τ 0 0 :=
  QIQTH.WhiteS1P1.white_hP1_underlying_nonzero

/-- **Gate 4 — the `Piw` antecedent of ★ `whiteGauss_pd_pd_gate_concrete` is SATISFIABLE on the
    gate** (the concrete identity is not conditional on an empty jet supply): the J4-629 whitened
    first jet `whiteFlowJet_concrete` at direction `i` provides exactly such a `Piw` at every
    on-gate point.  NOT `a₁ = R/6`. -/
theorem white_secondJet_iLine_satisfiable (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (i : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
        w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
        ∃ Piw : Fin n → ℝ, ∀ k, HasDerivAt
          (fun s : ℝ => whiteInvChart κ hκ hKc w.2.2 (Function.update w.2.1 i s) k)
          (Piw k) (w.2.1 i) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := whiteFlowJet_concrete κ hκ hKc i
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  obtain ⟨Pw, _hmeas, hgate⟩ := hspec c hc0 hcδ
  intro w hqK hτ hpS
  exact ⟨fun k => Pw w.2.2 w.2.1 k, fun k => hgate w hqK hτ hpS k⟩

/-- **Gate 5 — the discharged-at-∅ coherence of the `hOffS2` binder** (the ★★ concrete theorem is
    not vacuously conditional): the `hOffS2` antecedent of ★★ `white_hP2_concrete` holds
    (vacuously) at `Kset = ∅`.  ⚠⚠ HONEST LIMIT (cp466): this certifies non-contradictoriness
    ONLY; the NON-degenerate discharge at fat `K` is J4-630's `white_hOffS2_discharged`,
    consumed by ★★ `white_hP2_unconditional`.  -/
theorem white_hP2_offS2_satisfiable_empty (κ : ℝ) (hκ : κ ≤ 0) (a b : ℝ) (i j : Fin n)
    (c : ℝ) :
    ∀ w : ℝ × Point n × Point n, w.2.2 ∈ (∅ : Set (Point n)) → 0 < w.1 →
      w.2.1 ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) (isCompact_empty (X := Point n)) w.2.2
          '' Metric.ball (0 : Point n) c →
      pd (fun y : Point n =>
        pd (fun x : Point n => whiteGatedWitness κ hκ (isCompact_empty (X := Point n))
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) (isCompact_empty (X := Point n)) z
              '' Metric.ball (0 : Point n) c) a b
          w.1 x w.2.2) j y) i w.2.1 = 0 :=
  fun _ hw _ _ => absurd hw (Set.notMem_empty _)

end QIQTH.WhiteS1P2

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteS1P2
#print axioms QIQTH.WhiteS1P2.whiteFieldDeriv2_offBase_eq_zero
#print axioms QIQTH.WhiteS1P2.whiteFieldDeriv2_eq_zero_of_nonpos
#print axioms QIQTH.WhiteS1P2.whiteFieldDeriv2_gate_congr
#print axioms QIQTH.WhiteS1P2.whiteFieldDeriv2_eq_zero_off_closure
#print axioms QIQTH.WhiteS1P2.whiteP2Rep_measurable
#print axioms QIQTH.WhiteS1P2.whiteFieldDeriv2_eq_whiteP2Rep
#print axioms QIQTH.WhiteS1P2.white_hP2_stronglyMeasurable
#print axioms QIQTH.WhiteS1P2.whiteCut_contDiffAt_of_chartC2
#print axioms QIQTH.WhiteS1P2.white_pd2Rep_concrete
#print axioms QIQTH.WhiteS1P2.white_hP2_concrete
#print axioms QIQTH.WhiteS1P2.white_hP2_unconditional
#print axioms QIQTH.WhiteS1P2.whiteFlowSecondJet_concrete
#print axioms QIQTH.WhiteS1P2.whiteGauss_pd_pd_gate_eq
#print axioms QIQTH.WhiteS1P2.whiteGauss_pd_pd_gate_concrete
#print axioms QIQTH.WhiteS1P2.white_hP2_gate_nonempty
#print axioms QIQTH.WhiteS1P2.white_hP2_radii_satisfiable
#print axioms QIQTH.WhiteS1P2.white_hP2_underlying_nonzero
#print axioms QIQTH.WhiteS1P2.white_secondJet_iLine_satisfiable
#print axioms QIQTH.WhiteS1P2.white_hP2_offS2_satisfiable_empty
end AxiomChecks
