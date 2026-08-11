/-
  WhiteS1P1 — J4-629: S1-a AT THE WHITENED WITNESS — the hP1 FIRST field-`pd`
  measurable-representative slot (the next slice of the whitened S1 campaign; J4-628 = WhiteS1
  landed slices 1–3: chart rep, kernel/value rep, ∂_τ slot, hgi/hchr).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: S1-b (the `hP2` second field-`pd` slot) + S1-c (the E3d assembly at the whitened witness)
  + `hlam8` (`lam ≤ 8`, opaque `C₀`) + `K1TransportBudget` + the fat-`K` carrier piles + the
  capstone co-instantiation at the whitened witness + the prior analytic piles.

  ── THE TARGET (S1-a).  The `hP1` slot of `HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields`
     at `G := whiteGatedWitness`:
        `∀ k, StronglyMeasurable (fun w => pd (fun x => G w.1 x w.2.2) k w.2.1)`.
     Route (the banked as-built pattern, `AmpPdComposition.measurable_dq_witness` + the
     `GatedRepSFix.gatedDerivRepProdS` full-gate re-gating shape):
       (1) the RAW first field-`pd` kernel `whiteFieldDeriv := pd (x ↦ G τ x q) k p`;
       (2) off the BASE gate (`q ∉ K`) and at `τ ≤ 0` it VANISHES outright (§1);
       (3) ON the open gate it equals the field-`pd` of the UNGATED whitened cutoff kernel
           (germ congruence, `whiteFieldDeriv_gate_congr`);
       (4) the ungated on-gate `pd` gets a GLOBALLY MEASURABLE representative `Af` by the
           banked ABSTRACT difference-quotient engine (`measurable_dq_witness`) applied to the
           J4-628 `Gc`-representative twin `whiteCutKernelGc` — the on-gate `PdiffAt` supplied
           by the chain-rule bookkeeping through the chart's `C²` (`whiteCut_pdiffAt_of_contDiffAt`);
       (5) the FULL-gate indicator `whiteP1Rep := 𝟙_{q∈K ∧ p∈S q}·Af` is then measurable and
           equals the raw kernel EVERYWHERE (`whiteFieldDeriv_eq_whiteP1Rep`), giving the exact
           `hP1` slot shape (`white_hP1_stronglyMeasurable`, ★★ `white_hP1_concrete`).
     Verdict (iii) of J4-628 holds: NO amplitude field-`pd` appears anywhere (the whitened
     amplitude `√det g^κ(q)` is field-constant) — strictly smaller than the as-built §A.

  ── THE CHAIN-RULE LAYER (the S1-a "one `matToCLM` application" content, consumed by S1-b too):
       ▸ `whiteFlowJet_concrete` — the WHITENED first field-jet: the banked measurable chart jet
         (`FlowDerivMeasurable.flowInverseJet_measurable_component` at `g^κ/gi^κ`) pushed through
         the closed-form linear whitening `whiteUnvel_q` (a finite bilinear form of Borel
         entries) — globally measurable + the on-gate `HasDerivAt`;
       ▸ `whiteCut_pd_gate_eq` — the on-gate POINTWISE chain-rule identity
         `pd_k[χ(V̂)·√det·G_τ(V̂)] = ∂_k(χ∘V̂)·(√det·G_τ(V̂)) + χ(V̂)·(√det·G_τ(V̂)·(−⟨V̂,∂_kV̂⟩/2τ))`
         (`pd_mul` + `gaussComp_pd` at the whitened jet; the cutoff-`pd` factor kept SYMBOLIC —
         honest: `radialCutoff`'s gradient has no banked closed form and none is claimed).

  ── ⚠ THE SINGLE CARRIED INPUT (honestly labelled, NOT discharged here): `hOffS` — the off-`S`
     vanishing of the raw field-`pd` at gate-frontier points (`q ∈ K`, `τ > 0`, `p ∉ S q`).  This
     is the WHITENED collar (the W2 support-containment layer already named as an R1 residue in
     `WhiteGated`): unlike the as-built collar (`OffSVanishing`, where the cutoff reads the RAW
     chart value `v` and `χ(v) ≠ 0 ⟹ ‖v‖ < b` bounds the support ball directly), the whitened
     cutoff reads `V̂ = E_q⁻¹ v`, so the support bound needs a uniform-on-`K` norm bound for the
     whitening frame `E_q` — a genuine geometric estimate deferred to its own brick.  PROVED
     here instead: the vanishing off the CLOSURE of the gate (`whiteFieldDeriv_eq_zero_off_closure`)
     — so `hOffS`'s remaining content is EXACTLY the gate frontier `∂(S q)`.  `hOffS` is carried
     as a hypothesis of ★★ `white_hP1_concrete` in the same status as `GatedRepSFix`'s `hOffS`
     was carried at the J4-232 stage (discharged later by J4-235); it does NOT force `K = ∅`
     (non-vacuity gates §5).

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteS1
import QIQTH.AmpPdComposition
import QIQTH.OffSVanishing

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.EquivProbe
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteS1
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace QIQTH.WhiteS1P1

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ###############################################################################
    ### §0 — the raw FIRST field-`pd` kernel of the whitened gated witness.
    ############################################################################### -/

/-- **`whiteFieldDeriv` — the raw first field-`pd` kernel** of the whitened gated witness:
    `pd (x ↦ whiteGatedWitness τ x q) k p` — the exact integrand of the E3d `hP1` slot at
    `G := whiteGatedWitness` (mirror of `EngineInstantiation.witnessFieldDeriv`). -/
noncomputable def whiteFieldDeriv (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (τ : ℝ) (p q : Point n) : ℝ :=
  pd (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q) k p

/-! ###############################################################################
    ### §1 — outright vanishing legs + the on-gate germ congruence.
    ############################################################################### -/

/-- Off the BASE gate (`q ∉ K`) the witness is identically `0` in the field slot, so the
    field-`pd` vanishes. -/
theorem whiteFieldDeriv_offBase_eq_zero (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (τ : ℝ) (p q : Point n) (hq : q ∉ Kset) :
    whiteFieldDeriv κ hκ hKc S a b k τ p q = 0 := by
  have hzero : (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q)
      = fun _ : Point n => (0 : ℝ) := by
    funext x
    show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ x q = 0
    exact gatedKernel_apply_of_notMem Kset S _ τ x q (Or.inl hq)
  unfold whiteFieldDeriv
  rw [hzero]
  exact pd_const 0 k p

/-- At `τ ≤ 0` the whitened witness is identically `0` in the field slot (the Gaussian factor
    vanishes on the gate, the gate kills the rest), so the field-`pd` vanishes — the junk-value
    coherence leg. -/
theorem whiteFieldDeriv_eq_zero_of_nonpos (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (τ : ℝ) (p q : Point n) (hτ : τ ≤ 0) :
    whiteFieldDeriv κ hκ hKc S a b k τ p q = 0 := by
  have hzero : (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q)
      = fun _ : Point n => (0 : ℝ) := by
    funext x
    show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ x q = 0
    by_cases hg : q ∈ Kset ∧ x ∈ S q
    · rw [gatedKernel_apply_of_mem Kset S _ τ hg.1 hg.2]
      simp only [whiteCutKernel, whiteAmbientKernel]
      rw [QIQTH.InnerKernelJointMeas.gaussDdim_eq_zero_of_nonpos hn τ _ hτ, mul_zero, mul_zero]
    · exact gatedKernel_apply_of_notMem Kset S _ τ x q (not_and_or.mp hg)
  unfold whiteFieldDeriv
  rw [hzero]
  exact pd_const 0 k p

/-- **On-gate germ congruence** — at an OPEN gate point the field-`pd` of the GATED witness
    equals the field-`pd` of the UNGATED whitened cutoff kernel (`pd` is local; the hard gate is
    a neighbourhood condition). -/
theorem whiteFieldDeriv_gate_congr (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (τ : ℝ) (q p : Point n) (hq : q ∈ Kset) (hSopen : IsOpen (S q)) (hp : p ∈ S q) :
    whiteFieldDeriv κ hκ hKc S a b k τ p q
      = pd (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q) k p := by
  have hev : (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q)
      =ᶠ[𝓝 p] (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q) := by
    refine eventually_nhds_iff.mpr ⟨S q, ?_, hSopen, hp⟩
    intro x hx
    show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ x q
        = whiteCutKernel κ hκ hKc a b τ x q
    exact gatedKernel_apply_of_mem Kset S _ τ hq hx
  unfold whiteFieldDeriv
  exact pd_congr_of_eventuallyEq _ _ k p hev

/-- **★ Off-CLOSURE vanishing** — the NON-degenerate partial discharge of the off-`S` leg: at
    every `p ∉ closure (S q)` the witness is identically `0` on a neighbourhood of `p` (the hard
    gate kills every nearby field point), so the field-`pd` vanishes.  Consequence: the carried
    `hOffS` input of ★★ `white_hP1_concrete` has remaining content EXACTLY on the gate frontier
    `∂(S q)` — the whitened-collar (W2) residue.  NOT `a₁ = R/6`. -/
theorem whiteFieldDeriv_eq_zero_off_closure (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (τ : ℝ) (q p : Point n) (hp : p ∉ closure (S q)) :
    whiteFieldDeriv κ hκ hKc S a b k τ p q = 0 := by
  have hU : IsOpen ((closure (S q))ᶜ) := isOpen_compl_iff.mpr isClosed_closure
  have hev : (fun x : Point n => whiteGatedWitness κ hκ hKc S a b τ x q)
      =ᶠ[𝓝 p] (fun _ : Point n => (0 : ℝ)) := by
    refine Filter.eventuallyEq_of_mem (hU.mem_nhds hp) ?_
    intro x hx
    show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ x q = 0
    exact gatedKernel_apply_of_notMem Kset S _ τ x q
      (Or.inr (fun hxS => hx (subset_closure hxS)))
  unfold whiteFieldDeriv
  rw [pd_congr_of_eventuallyEq _ _ k p hev]
  exact pd_const 0 k p

/-! ###############################################################################
    ### §2 — the FULL-gate indicator representative and the EVERYWHERE identity.
    ############################################################################### -/

/-- **`whiteP1Rep` — the FULL-gate re-gated `hP1` representative**: the indicator of an on-gate
    representative `Af` of the ungated field-`pd` on the full gate `{q ∈ K ∧ p ∈ S q}` (mirror of
    `GatedRepSFix.gatedDerivRepProdS`'s outer-indicator shape, with the on-gate body OPAQUE). -/
noncomputable def whiteP1Rep (Kset : Set (Point n)) (S : Point n → Set (Point n))
    (Af : ℝ → Point n → Point n → ℝ) : ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2}
    (fun w => Af w.1 w.2.2 w.2.1)

/-- **★ `whiteP1Rep_measurable`** — joint `(τ,p,q)`-Borel measurability from the measurability of
    `Af` plus the full-gate `MeasurableSet` (no continuity anywhere).  NOT `a₁ = R/6`. -/
theorem whiteP1Rep_measurable (Kset : Set (Point n)) (S : Point n → Set (Point n))
    (Af : ℝ → Point n → Point n → ℝ)
    (hAfMeas : Measurable (fun w : ℝ × Point n × Point n => Af w.1 w.2.2 w.2.1))
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2}) :
    Measurable (whiteP1Rep Kset S Af) :=
  hAfMeas.indicator hKSmeas

/-- **★ `whiteFieldDeriv_eq_whiteP1Rep` — THE EVERYWHERE IDENTITY.**  At EVERY `(τ,p,q)` the raw
    first field-`pd` kernel equals the full-gate representative:
      • FULL gate — germ congruence to the ungated kernel + the on-gate value of `Af` (`hAf`,
        proved for the concrete `Af` by the difference-quotient engine below);
      • `q ∈ K`, `p ∉ S q` — `τ > 0`: the carried off-`S` vanishing `hOffS` (the whitened-collar
        input); `τ ≤ 0`: the junk-value coherence leg;
      • `q ∉ K`: outright vanishing.
    NOT `a₁ = R/6`. -/
theorem whiteFieldDeriv_eq_whiteP1Rep (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n))
    (a b : ℝ) (k : Fin n) (Af : ℝ → Point n → Point n → ℝ)
    (hSopen : ∀ q ∈ Kset, IsOpen (S q))
    (hAf : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        Af w.1 w.2.2 w.2.1
          = pd (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) k w.2.1)
    (hOffS : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        whiteFieldDeriv κ hκ hKc S a b k w.1 w.2.1 w.2.2 = 0) :
    ∀ w : ℝ × Point n × Point n,
      whiteFieldDeriv κ hκ hKc S a b k w.1 w.2.1 w.2.2 = whiteP1Rep Kset S Af w := by
  intro w
  simp only [whiteP1Rep]
  by_cases hg : w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2
  · rw [Set.indicator_of_mem
      (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2} from hg),
      hAf w hg.1 hg.2]
    exact whiteFieldDeriv_gate_congr κ hκ hKc S a b k w.1 w.2.2 w.2.1 hg.1
      (hSopen _ hg.1) hg.2
  · rw [Set.indicator_of_notMem
      (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2} from hg)]
    by_cases hqK : w.2.2 ∈ Kset
    · have hpS : w.2.1 ∉ S w.2.2 := fun h => hg ⟨hqK, h⟩
      by_cases hτ : 0 < w.1
      · exact hOffS w hqK hτ hpS
      · exact whiteFieldDeriv_eq_zero_of_nonpos hn κ hκ hKc S a b k w.1 w.2.1 w.2.2
          (not_lt.mp hτ)
    · exact whiteFieldDeriv_offBase_eq_zero κ hκ hKc S a b k w.1 w.2.1 w.2.2 hqK

/-- **★ `white_hP1_stronglyMeasurable` — the E3d `hP1` slot shape at ANY measurable open gate
    with an on-gate `pd`-representative**: the first field-`pd` derivative field of the whitened
    gated witness is jointly strongly measurable — EXACTLY the `hP1` antecedent of
    `HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields` at `G := whiteGatedWitness` (one fixed
    direction `k`; the `∀ k` closure happens at the concrete instantiation).  NOT `a₁ = R/6`. -/
theorem white_hP1_stronglyMeasurable (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n))
    (a b : ℝ) (k : Fin n) (Af : ℝ → Point n → Point n → ℝ)
    (hAfMeas : Measurable (fun w : ℝ × Point n × Point n => Af w.1 w.2.2 w.2.1))
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧ w.2.1 ∈ S w.2.2})
    (hSopen : ∀ q ∈ Kset, IsOpen (S q))
    (hAf : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        Af w.1 w.2.2 w.2.1
          = pd (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) k w.2.1)
    (hOffS : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        whiteFieldDeriv κ hκ hKc S a b k w.1 w.2.1 w.2.2 = 0) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun x : Point n => whiteGatedWitness κ hκ hKc S a b w.1 x w.2.2) k w.2.1) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun x : Point n => whiteGatedWitness κ hκ hKc S a b w.1 x w.2.2) k w.2.1)
      = whiteP1Rep Kset S Af := by
    funext w
    show whiteFieldDeriv κ hκ hKc S a b k w.1 w.2.1 w.2.2 = whiteP1Rep Kset S Af w
    exact whiteFieldDeriv_eq_whiteP1Rep hn κ hκ hKc S a b k Af hSopen hAf hOffS w
  rw [hrw]
  exact (whiteP1Rep_measurable Kset S Af hAfMeas hKSmeas).stronglyMeasurable

/-! ###############################################################################
    ### §3 — the on-gate suppliers: `PdiffAt`, the whitened chart jet, the chain-rule identity.
    ############################################################################### -/

/-- **On-gate `PdiffAt` of the ungated whitened cutoff kernel** from chart `C²`: the field slice
    `x ↦ χ_{a,b}(V̂_q x)·(√det g^κ(q)·G_τ(V̂_q x))` is partially differentiable along coordinate
    `k` wherever the raw chart is `C²` — chain rule through the coordinate line, the LINEAR
    whitening `whiteUnvel_q`, the smooth `radialCutoff`, and the Gaussian line derivative
    (`gaussComp_hasDerivAt_line`); at `τ ≤ 0` the slice is identically `0`.  NOT `a₁ = R/6`. -/
theorem whiteCut_pdiffAt_of_contDiffAt (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (a b : ℝ) (k : Fin n) (τ : ℝ)
    (q p : Point n)
    (hC2 : ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) p) :
    PdiffAt (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q) k p := by
  by_cases hτ : 0 < τ
  · -- τ > 0: the chain rule through the chart line.
    have hWdiff : DifferentiableAt ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) p := hC2.differentiableAt (by norm_num)
    have hWfd : HasFDerivAt (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q)
        (fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) p) (Function.update p k (p k)) := by
      rw [Function.update_eq_self]
      exact hWdiff.hasFDerivAt
    have hlineW : HasDerivAt (fun s : ℝ => uniformInverseChart (curvedRNCMetric κ)
          (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q (Function.update p k s))
        (fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) p (Pi.single k (1 : ℝ))) (p k) := by
      simpa using hWfd.comp_hasDerivAt (p k) (hasDerivAt_update p k (p k))
    have hlineV : HasDerivAt
        (fun s : ℝ => whiteInvChart κ hκ hKc q (Function.update p k s))
        (whiteUnvel κ q (fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) p (Pi.single k (1 : ℝ)))) (p k) := by
      have h := ((whiteUnvel κ q).hasFDerivAt).comp_hasDerivAt (p k) hlineW
      simpa [whiteInvChart, Function.comp] using h
    have hcomp : ∀ j : Fin n, HasDerivAt
        (fun s : ℝ => whiteInvChart κ hκ hKc q (Function.update p k s) j)
        (whiteUnvel κ q (fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) p (Pi.single k (1 : ℝ))) j) (p k) :=
      fun j => hasDerivAt_pi.mp hlineV j
    have hG : HasDerivAt
        (fun s : ℝ => gaussDdim τ (whiteInvChart κ hκ hKc q (Function.update p k s)))
        (gaussDdim τ (whiteInvChart κ hκ hKc q p)
          * (-(∑ j, whiteInvChart κ hκ hKc q p j
              * whiteUnvel κ q (fderiv ℝ (uniformInverseChart (curvedRNCMetric κ)
                  (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q) p (Pi.single k (1 : ℝ))) j)
            / (2 * τ))) (p k) :=
      gaussComp_hasDerivAt_line (whiteInvChart κ hκ hKc q)
        (fun j => whiteUnvel κ q (fderiv ℝ (uniformInverseChart (curvedRNCMetric κ)
          (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q) p (Pi.single k (1 : ℝ))) j)
        τ hτ k p hcomp
    have hχ : DifferentiableAt ℝ
        (fun s : ℝ => radialCutoff a b (whiteInvChart κ hκ hKc q (Function.update p k s)))
        (p k) := by
      have hcut : Differentiable ℝ (radialCutoff a b : Point n → ℝ) :=
        (radialCutoff_contDiff a b).differentiable (by simp)
      have h := DifferentiableAt.comp (𝕜 := ℝ) (p k)
        (hcut.differentiableAt) hlineV.differentiableAt
      simpa [Function.comp] using h
    show DifferentiableAt ℝ
      (fun t : ℝ => whiteCutKernel κ hκ hKc a b τ (Function.update p k t) q) (p k)
    have hrw : (fun t : ℝ => whiteCutKernel κ hκ hKc a b τ (Function.update p k t) q)
        = fun t : ℝ =>
            radialCutoff a b (whiteInvChart κ hκ hKc q (Function.update p k t))
              * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
                  * gaussDdim τ (whiteInvChart κ hκ hKc q (Function.update p k t))) := by
      funext t
      simp only [whiteCutKernel, whiteAmbientKernel]
    rw [hrw]
    exact hχ.mul ((hG.differentiableAt).const_mul
      (Real.sqrt (Matrix.det (curvedRNCMetric κ q))))
  · -- τ ≤ 0: the field slice is identically 0.
    rw [not_lt] at hτ
    show DifferentiableAt ℝ
      (fun t : ℝ => whiteCutKernel κ hκ hKc a b τ (Function.update p k t) q) (p k)
    have hrw : (fun t : ℝ => whiteCutKernel κ hκ hKc a b τ (Function.update p k t) q)
        = fun _ : ℝ => (0 : ℝ) := by
      funext t
      simp only [whiteCutKernel, whiteAmbientKernel]
      rw [QIQTH.InnerKernelJointMeas.gaussDdim_eq_zero_of_nonpos hn τ _ hτ, mul_zero, mul_zero]
    rw [hrw]
    exact differentiableAt_const 0

/-- **★ `whiteFlowJet_concrete` — the WHITENED first field-jet, measurable + on-gate value.**
    The banked measurable chart jet (`FlowDerivMeasurable.flowInverseJet_measurable_component` at
    `g^κ/gi^κ`) pushed through the LINEAR whitening: one `matToCLM` application, componentwise the
    finite bilinear form `Pw q p j = ∑ᵢ (g^κ(q)·E_q)ⱼᵢ · Pfield q p i` of Borel entries (the
    J4-628 §1 entry measurabilities) — globally measurable, with the on-gate `HasDerivAt` of the
    WHITENED chart's coordinate line.  This is the S1-a jet supplier (S1-b consumes it again one
    order up).  NOT `a₁ = R/6`. -/
theorem whiteFlowJet_concrete (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (k : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∃ Pw : Point n → Point n → Fin n → ℝ,
        (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pw w.2.2 w.2.1 j))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
            w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
            ∀ j, HasDerivAt
              (fun s : ℝ => whiteInvChart κ hκ hKc w.2.2 (Function.update w.2.1 k s) j)
              (Pw w.2.2 w.2.1 j) (w.2.1 k)) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := QIQTH.FlowDerivMeasurable.flowInverseJet_measurable_component
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc k
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  obtain ⟨Pf, hPfmeas, hPfgate⟩ := hspec c hc0 hcδ
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) rfl
  refine ⟨fun q p j => ∑ i, (∑ m, curvedRNCMetric κ q j m * curvedWhitening κ q m i)
      * Pf q p i, ?_, ?_⟩
  · -- measurability: finite bilinear form of Borel entries × the banked measurable jet.
    intro j
    refine Finset.measurable_sum _ (fun i _ => Measurable.mul ?_ (hPfmeas i))
    refine Finset.measurable_sum _ (fun m _ => Measurable.mul ?_ ?_)
    · exact (curvedRNCMetric_entry_measurable κ j m).comp measurable_snd.snd
    · exact (curvedWhitening_entry_measurable κ m i).comp measurable_snd.snd
  · -- on-gate HasDerivAt: linear combination of the banked chart-line jets.
    intro w hqK hτ hpS j
    have hjets := hPfgate w hqK hτ hpS
    have h1 : HasDerivAt
        (fun s : ℝ => ∑ i, (∑ m, curvedRNCMetric κ w.2.2 j m * curvedWhitening κ w.2.2 m i)
            * uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc w.2.2 (Function.update w.2.1 k s) i)
        (∑ i, (∑ m, curvedRNCMetric κ w.2.2 j m * curvedWhitening κ w.2.2 m i)
            * Pf w.2.2 w.2.1 i) (w.2.1 k) :=
      HasDerivAt.fun_sum (fun i _ => (hjets i).const_mul _)
    have h2 : (fun s : ℝ => whiteInvChart κ hκ hKc w.2.2 (Function.update w.2.1 k s) j)
        = (fun s : ℝ => ∑ i, (∑ m, curvedRNCMetric κ w.2.2 j m * curvedWhitening κ w.2.2 m i)
            * uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc w.2.2 (Function.update w.2.1 k s) i) := by
      funext s
      simp only [whiteInvChart, whiteUnvel, matToCLM_apply]
    rw [h2]
    exact h1

/-- **★ `whiteCut_pd_gate_eq` — the on-gate POINTWISE chain-rule identity** through the whitened
    chart's first jet: with `V̂ = whiteInvChart_q`, the jet `Pw` of its coordinate-`k` line, and
    the cutoff-line partial differentiability `hχ`,
      `pd_k[χ(V̂)·(√det·G_τ(V̂))](p) = ∂_k(χ∘V̂)(p)·(√det·G_τ(V̂ p))
                                      + χ(V̂ p)·(√det·(G_τ(V̂ p)·(−⟨V̂ p, Pw⟩/(2τ))))`.
    Leibniz (`pd_mul`) + the Gaussian log-derivative normal form (`gaussComp_pd`).  ⚠ HONEST: the
    cutoff-`pd` factor is kept SYMBOLIC (no closed form for `∇radialCutoff` is banked or claimed);
    the measurable `hP1` route (§2/§4) does not need this identity — it documents the on-gate
    structure for S1-b.  NO amplitude `pd` (the whitened amplitude is field-constant).
    NOT `a₁ = R/6`. -/
theorem whiteCut_pd_gate_eq (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (k : Fin n) (τ : ℝ) (hτ : 0 < τ) (q p : Point n)
    (Pw : Fin n → ℝ)
    (hjet : ∀ j, HasDerivAt
      (fun s : ℝ => whiteInvChart κ hκ hKc q (Function.update p k s) j) (Pw j) (p k))
    (hχ : PdiffAt (fun x : Point n => radialCutoff a b (whiteInvChart κ hκ hKc q x)) k p) :
    pd (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q) k p
      = pd (fun x : Point n => radialCutoff a b (whiteInvChart κ hκ hKc q x)) k p
          * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
              * gaussDdim τ (whiteInvChart κ hκ hKc q p))
        + radialCutoff a b (whiteInvChart κ hκ hKc q p)
          * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
              * (gaussDdim τ (whiteInvChart κ hκ hKc q p)
                  * (-(∑ j, whiteInvChart κ hκ hKc q p j * Pw j) / (2 * τ)))) := by
  have hGdiff : PdiffAt (fun x : Point n => gaussDdim τ (whiteInvChart κ hκ hKc q x)) k p :=
    (gaussComp_hasDerivAt_line (whiteInvChart κ hκ hKc q) Pw τ hτ k p hjet).differentiableAt
  have hAmpdiff : PdiffAt (fun x : Point n =>
      Real.sqrt (Matrix.det (curvedRNCMetric κ q))
        * gaussDdim τ (whiteInvChart κ hκ hKc q x)) k p := by
    show DifferentiableAt ℝ
      (fun t : ℝ => Real.sqrt (Matrix.det (curvedRNCMetric κ q))
        * gaussDdim τ (whiteInvChart κ hκ hKc q (Function.update p k t))) (p k)
    exact DifferentiableAt.const_mul hGdiff _
  have hrw : (fun x : Point n => whiteCutKernel κ hκ hKc a b τ x q)
      = fun x : Point n => radialCutoff a b (whiteInvChart κ hκ hKc q x)
          * (Real.sqrt (Matrix.det (curvedRNCMetric κ q))
              * gaussDdim τ (whiteInvChart κ hκ hKc q x)) := by
    funext x
    simp only [whiteCutKernel, whiteAmbientKernel]
  rw [hrw, pd_mul _ _ k p hχ hAmpdiff,
    pd_const_mul _ _ k p hGdiff,
    gaussComp_pd (whiteInvChart κ hκ hKc q) Pw τ hτ k p hjet]

/-! ###############################################################################
    ### §4 — the concrete flow-ball-gate instantiation.
    ############################################################################### -/

/-- **★ `white_pdRep_concrete` — the measurable on-gate `pd` representative at the concrete
    flow-ball gates**: a single `δ₀ > 0` such that for every gate radius `0 < c < δ₀` there is a
    GLOBALLY MEASURABLE `Af` agreeing on the full gate with the field-`pd` of the ungated
    whitened cutoff kernel.  Route: the banked ABSTRACT difference-quotient engine
    (`AmpPdComposition.measurable_dq_witness`) at the J4-628 twin `whiteCutKernelGc` (globally
    measurable) with the on-gate `PdiffAt` from chart-`C²` reachability.  NOT `a₁ = R/6`. -/
theorem white_pdRep_concrete (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (k : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∃ Af : ℝ → Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => Af w.1 w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset →
            w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
            Af w.1 w.2.2 w.2.1
              = pd (fun x : Point n => whiteCutKernel κ hκ hKc a b w.1 x w.2.2) k w.2.1) := by
  obtain ⟨ρ, hρ, Wg, hWgMeas, hWagree⟩ := whiteChart_rep_concrete κ hκ hKc
  obtain ⟨δm, hδm, hδmspec⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δr, hδr, hreach⟩ := QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨min (min ρ δm) (min δr δo), lt_min (lt_min hρ hδm) (lt_min hδr hδo), ?_⟩
  intro c hc0 hcδ
  have hcρ : c ≤ ρ :=
    le_of_lt (lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδr : c < δr := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hAGmeas : Measurable (fun w : ℝ × Point n × Point n =>
      whiteCutKernelGc κ a b Wg (w.1, w.2.1, w.2.2)) := by
    simpa using whiteCutKernelGc_measurable κ a b Wg hWgMeas
  obtain ⟨Af, hAfMeas, hAfval⟩ := QIQTH.AmpPdComposition.measurable_dq_witness (K := Kset)
    (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc) c k
    (fun τ q p => whiteCutKernel κ hκ hKc a b τ p q)
    (fun τ q p => whiteCutKernelGc κ a b Wg (τ, p, q))
    hAGmeas
    (hδmspec c hc0 hcδm)
    (fun q hq => ((hopen q hq).2 c hc0 hcδo).1)
    (by
      -- on-gate PdiffAt from chart-C² reachability.
      intro w hqK hpImg
      obtain ⟨v, hv, hvp⟩ := hpImg
      have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
      have hC2 : ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w.2.2) w.2.1 := by
        rw [← hvp]
        exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
      exact whiteCut_pdiffAt_of_contDiffAt hn κ hκ hKc a b k w.1 w.2.2 w.2.1 hC2)
    (by
      -- on-gate value swap: whiteCutKernel = whiteCutKernelGc via the banked chart agreement.
      intro w hqK p hpImg
      exact whiteCutKernel_eq_whiteCutKernelGc_of_agree κ hκ hKc a b Wg w.1 p w.2.2
        (hWagree c hcρ (w.1, p, w.2.2) hqK hpImg))
  exact ⟨Af, hAfMeas, fun w hqK hpS => hAfval w hqK hpS⟩

/-- **★★ `white_hP1_concrete` — the `hP1` E3d slot at the concrete flow-ball gates** (mirroring
    `white_hDtau_concrete`'s shape): a single `δ₀ > 0` such that for every gate radius
    `0 < c < δ₀`, GIVEN the single carried off-`S` input `hOffS` (⚠ the whitened-collar / W2
    residue — needed ONLY on the gate frontier, by `whiteFieldDeriv_eq_zero_off_closure`), the
    whitened gated witness's first field-`pd` derivative field is jointly strongly measurable —
    slot 2 of the 3 derivative fields of the whitened S1
    (`triple_hEmeas_of_borel_deriv_fields`).  Chart rep, gate measurability, gate openness, and
    the on-gate `pd` representative are all DISCHARGED from geometry; `hOffS` is the ONLY carried
    measurability-side input (same status as `GatedRepSFix`'s `hOffS` at the J4-232 stage).
    NOT `a₁ = R/6`. -/
theorem white_hP1_concrete (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (k : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      (∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
          w.2.1 ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
          pd (fun x : Point n => whiteGatedWitness κ hκ hKc
            (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
            w.1 x w.2.2) k w.2.1 = 0) →
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        pd (fun x : Point n => whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          w.1 x w.2.2) k w.2.1) := by
  obtain ⟨δ₁, hδ₁, hrep⟩ := white_pdRep_concrete hn κ hκ hKc a b k
  obtain ⟨δm, hδm, hδmspec⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨min δ₁ (min δm δo), lt_min hδ₁ (lt_min hδm hδo), ?_⟩
  intro c hc0 hcδ hOffS
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Af, hAfMeas, hAfval⟩ := hrep c hc0 hcδ₁
  exact white_hP1_stronglyMeasurable hn κ hκ hKc
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b k Af hAfMeas
    (hδmspec c hc0 hcδm)
    (fun q hq => ((hopen q hq).2 c hc0 hcδo).1)
    (fun w hq hp => hAfval w hq hp)
    hOffS

/-! ###############################################################################
    ### §5 — Non-vacuity / adversarial gates (cp466 discipline).
    ############################################################################### -/

/-- **Gate 1 — the full-gate indicator set is INHABITED** at the concrete flow-ball gates (the
    `whiteP1Rep` indicator is not an indicator over `∅`): re-export of the J4-628 gate. -/
theorem white_hP1_gate_nonempty (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) {q : Point n} (hq : q ∈ Kset) (c : ℝ) (hc : 0 < c) (τ : ℝ) :
    (τ, uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q 0, q)
      ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧
          w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c} :=
  QIQTH.WhiteS1.white_flowball_gate_nonempty κ hκ hKc hq c hc τ

/-- **Gate 2 — the carried `hOffS` input is NOT contradictory**: it holds (vacuously) at
    `Kset = ∅`, so ★★ `white_hP1_concrete` is not vacuously conditional.  ⚠⚠ HONEST LIMIT
    (cp466): this certifies non-contradictoriness ONLY — at `Kset = ∅` the conclusion is
    degenerate.  The NON-degenerate content of `hOffS` is the gate-FRONTIER vanishing (the
    exterior is already a THEOREM, `whiteFieldDeriv_eq_zero_off_closure`); its fat-`K` discharge
    = the whitened-collar (W2) residue.  DO NOT read this as the collar being discharged. -/
theorem white_hP1_offS_satisfiable_empty (κ : ℝ) (hκ : κ ≤ 0) (a b : ℝ) (k : Fin n) (c : ℝ) :
    ∀ w : ℝ × Point n × Point n, w.2.2 ∈ (∅ : Set (Point n)) → 0 < w.1 →
      w.2.1 ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) (isCompact_empty (X := Point n)) w.2.2
          '' Metric.ball (0 : Point n) c →
      pd (fun x : Point n => whiteGatedWitness κ hκ (isCompact_empty (X := Point n))
        (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) (isCompact_empty (X := Point n)) z
            '' Metric.ball (0 : Point n) c) a b
        w.1 x w.2.2) k w.2.1 = 0 :=
  fun _ hw _ _ => absurd hw (Set.notMem_empty _)

/-- **Gate 3 — the measured object is genuinely NONZERO at the curved fat witness** (`n = 2`,
    `κ = −1`, `K = closedBall 0 2`, concrete flow-ball gate, cutoff `1 < 2`): the underlying
    whitened gated witness is strictly positive on the origin diagonal for every `τ > 0` — the
    `hP1` slot measures the derivative field of a non-degenerate kernel, not of `0`.  Re-export
    of the J4-628 object gate.  NOT `a₁ = R/6`. -/
theorem white_hP1_underlying_nonzero :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ →
      0 < whiteGatedWitness (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2)
        (fun z => uniformFlowExp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
          (curvedRNC_hChr (-1 : ℝ) (by norm_num))
          (isCompact_closedBall (0 : Point 2) 2) z '' Metric.ball (0 : Point 2) c)
        1 2 τ 0 0 :=
  QIQTH.WhiteS1.white_S1_object_nonzero_gate

end QIQTH.WhiteS1P1

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteS1P1
#print axioms QIQTH.WhiteS1P1.whiteFieldDeriv_offBase_eq_zero
#print axioms QIQTH.WhiteS1P1.whiteFieldDeriv_eq_zero_of_nonpos
#print axioms QIQTH.WhiteS1P1.whiteFieldDeriv_gate_congr
#print axioms QIQTH.WhiteS1P1.whiteFieldDeriv_eq_zero_off_closure
#print axioms QIQTH.WhiteS1P1.whiteP1Rep_measurable
#print axioms QIQTH.WhiteS1P1.whiteFieldDeriv_eq_whiteP1Rep
#print axioms QIQTH.WhiteS1P1.white_hP1_stronglyMeasurable
#print axioms QIQTH.WhiteS1P1.whiteCut_pdiffAt_of_contDiffAt
#print axioms QIQTH.WhiteS1P1.whiteFlowJet_concrete
#print axioms QIQTH.WhiteS1P1.whiteCut_pd_gate_eq
#print axioms QIQTH.WhiteS1P1.white_pdRep_concrete
#print axioms QIQTH.WhiteS1P1.white_hP1_concrete
#print axioms QIQTH.WhiteS1P1.white_hP1_gate_nonempty
#print axioms QIQTH.WhiteS1P1.white_hP1_offS_satisfiable_empty
#print axioms QIQTH.WhiteS1P1.white_hP1_underlying_nonzero
end AxiomChecks
