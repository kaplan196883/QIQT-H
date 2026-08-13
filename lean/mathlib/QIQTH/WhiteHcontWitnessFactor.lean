/-
  WhiteHcontWitnessFactor — J4-693: the WITNESS-factor TIME-continuity discharged, and the whitened
  Levi inner-pairing continuity's LAST carry (`hcont`) reduced to the BANKED Levi joint-continuity
  shape — the witness factor no longer carried.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── CONTEXT.  `WhiteLeviConvergenceTrio.white_hInnerCont_hmeas` (J4-692) discharged the interior
     slice measurability `hmeas`, dropping the composed whitened inner-pairing time-continuity carries
     to `{hcont}` ONLY:
         `∀ u ∈ U, ∀ s₀ ∈ Ioo 0 u, ∀ᵐ z, ContinuousAt
             (fun s => whiteGatedWitness κ … (u−s) 0 z · leviSeries (whiteDefectKernel κ …) s z 0) s₀`.
     The product `s ↦ W(u−s) · L(s)` factors into a WITNESS factor `s ↦ W(u−s) 0 z` and a LEVI factor
     `s ↦ L s z 0`.  This file DISCHARGES the witness factor's time-continuity completely (for EVERY
     `z`, not just a.e.), and reduces `hcont` to the single remaining honest input = the Levi factor's
     TIME-continuity, itself extracted from the banked JOINT `(s,z)`-continuity of the Levi slice
     (`LeviMTest.hBcontEvery_of_carries` shape).

  ── ★★ THE FINDING (the witness factor is `τ`-continuous by pure structure).  The whitened gated
     witness `whiteGatedWitness κ hκ hKc S a b = gatedKernel Kset S (whiteCutKernel κ …)` has, at a
     FIXED `z` (and left node `p = 0`), only THREE possibilities:  off the `q`-gate (`z ∉ Kset`) or off
     the spatial gate (`0 ∉ S z`) it is the constant `0`; ON the gate it equals
         `radialCutoff a b (whiteInvChart_z 0) · (√det g^κ(z) · gaussDdim τ (whiteInvChart_z 0))`,
     whose ONLY `τ`-dependence is the Gaussian factor `gaussDdim τ (·)` — the radial-cutoff, the
     √det and the inverse-chart image are ALL `τ`-independent.  The banked joint Gaussian continuity
     `InnerKernelJointMeas.gaussDdim_continuousOn_pos` (on `{0 < τ}`) then gives `ContinuousAt` of
     `s ↦ gaussDdim (u−s)(·)` at every `s₀` with `u − s₀ > 0` (i.e. `s₀ ∈ Ioo 0 u`), and multiplying by
     the two constants + composing with `s ↦ u − s` closes the witness factor — UNCONDITIONALLY, for
     every `z`.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `gaussDdim_time_continuousAt` — the scalar Gaussian is `ContinuousAt` in its width `τ` at any
      `τ₀ > 0`, extracted from the banked joint `(τ,x)`-continuity on `{0<τ}`.
    • `whiteWitness_time_continuousAt` — ★ THE WITNESS FACTOR, DISCHARGED.  For EVERY `z` and every
      `s₀ ∈ Ioo 0 u`, `s ↦ whiteGatedWitness κ hκ hKc S a b (u−s) 0 z` is `ContinuousAt s₀`.
    • `leviTimeCont_of_jointStrip` — the Levi factor's TIME-continuity `s ↦ leviSeries E s z 0`
      extracted from the banked JOINT strip continuity `ContinuousOn (leviSeries slice) (Ioc 0 T ×ˢ
      univ)` at any interior `(s₀,z)`, `0 < s₀ < T` (the `LeviMTest.hBcontEvery_of_carries` output).
    • `white_hInnerCont_leviJoint` — ★★★ the composed whitened inner-pairing continuity with the
      witness factor of `hcont` DISCHARGED: carries drop from `{hcont}` to the single BANKED-SHAPE
      Levi joint-continuity carry `∀ u ∈ U, ContinuousOn (leviSeries (whiteDefectKernel κ …) slice)
      (Ioc 0 u ×ˢ univ)`.  Same fat co-instantiated gate as `white_hInnerCont_hmeas`.
    • `white_hInnerCont_leviJoint_witness_gate` — the cp466 non-vacuity certificate.

  ── HONEST RESIDUAL.  The composed continuity now owes ONLY the Levi-slice JOINT continuity
     `hJoint` (the `LeviMTest.hBcontEvery_of_carries` shape, whose own residual is the whitened
     iterated-defect `iterE` TERMWISE joint continuity — the parametric-continuity-of-convolution
     wall / M-test residual, still open) plus the prior `K1TransportBudget` / capstone piles.  The
     witness factor of `hcont` is GONE.  `a₁ = R/6` established non-vacuously ONLY for the FLAT tower;
     `R/6` is a labelled carrier, untouched.

  ⚠ HONEST FIREWALL.  Witness-factor time-continuity + factor composition + joint→slice extraction
  ONLY — NOT `a₁ = R/6`.  DERIVED from the banked joint Gaussian continuity + the whitened-witness
  gate structure + the banked `white_hInnerCont_hmeas` reduction.  No `sorry`, no `admit`, no new
  axioms, no `:= True`, no vacuous hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.WhiteLeviConvergenceTrio
import QIQTH.InnerKernelJointMeas

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.WhiteGated QIQTH.WhiteAmbient QIQTH.WhiteBridge
open QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.InnerKernelJointMeas
open QIQTH.WhiteLeviConvergenceTrio
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteHcontWitnessFactor

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the scalar Gaussian is `ContinuousAt` in its width `τ > 0`.
    ############################################################################### -/

/-- **`gaussDdim_time_continuousAt`.**  The `d`-D heat Gaussian, at a FIXED spatial point `x`, is
    `ContinuousAt` in its width `τ` at any `τ₀ > 0`.  Extracted from the banked joint `(τ,x)`
    continuity `gaussDdim_continuousOn_pos` on the open set `{0 < τ}` (a neighbourhood of `(τ₀,x)`),
    composed with the continuous slice `τ ↦ (τ,x)`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_time_continuousAt (x : Point n) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    ContinuousAt (fun τ : ℝ => gaussDdim τ x) τ₀ := by
  have hopen : IsOpen {q : ℝ × Point n | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  have hmem : {q : ℝ × Point n | 0 < q.1} ∈ 𝓝 ((τ₀, x) : ℝ × Point n) :=
    hopen.mem_nhds hτ₀
  have hjoint : ContinuousAt (fun q : ℝ × Point n => gaussDdim q.1 q.2) (τ₀, x) :=
    gaussDdim_continuousOn_pos.continuousAt hmem
  have hmap : ContinuousAt (fun τ : ℝ => (τ, x)) τ₀ :=
    continuousAt_id.prodMk continuousAt_const
  exact hjoint.comp (f := fun τ : ℝ => (τ, x)) hmap

/-! ###############################################################################
    ### §2 — ★ the WITNESS FACTOR time-continuity, DISCHARGED (for every `z`).
    ############################################################################### -/

/-- **★ `whiteWitness_time_continuousAt` — THE WITNESS FACTOR, DISCHARGED.**  For EVERY `z : Point n`
    and every `s₀ ∈ Ioo 0 u`, the whitened witness factor
        `s ↦ whiteGatedWitness κ hκ hKc S a b (u − s) 0 z`
    is `ContinuousAt s₀`.  At a fixed `z` the gated witness is either the constant `0` (off either
    gate) or `χ · (√det · gaussDdim (u−s) (whiteInvChart_z 0))`, whose only `s`-dependence is the
    Gaussian width `u − s`.  Since `u − s₀ > 0`, `gaussDdim_time_continuousAt` + the constant factors
    + the continuous `s ↦ u − s` close it.  UNCONDITIONAL (all `z`).  NOT `a₁ = R/6`. -/
theorem whiteWitness_time_continuousAt (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (z : Point n) {s₀ : ℝ} (_hs₀ : 0 < s₀) (hs₀u : s₀ < u) :
    ContinuousAt (fun s => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z) s₀ := by
  have hτ₀ : (0 : ℝ) < u - s₀ := by linarith
  -- the continuous Gaussian slice `s ↦ gaussDdim (u − s) (whiteInvChart_z 0)`.
  have hg : ContinuousAt
      (fun s => gaussDdim (u - s) (whiteInvChart κ hκ hKc z 0)) s₀ :=
    (gaussDdim_time_continuousAt (whiteInvChart κ hκ hKc z 0) hτ₀).comp
      (continuousAt_const.sub continuousAt_id)
  by_cases hz : z ∈ Kset
  · by_cases h0 : (0 : Point n) ∈ S z
    · -- on the gate: the gated witness IS the whitened cutoff kernel.
      have hEq : (fun s => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z)
          = fun s => whiteCutKernel κ hκ hKc a b (u - s) 0 z := by
        funext s
        exact gatedKernel_apply_of_mem Kset S (whiteCutKernel κ hκ hKc a b) (u - s) hz h0
      rw [hEq]
      -- `whiteCutKernel (u−s) 0 z = χ · (√det · gaussDdim (u−s) (whiteInvChart_z 0))` (defeq).
      exact continuousAt_const.mul (continuousAt_const.mul hg)
    · -- off the spatial gate: constant `0`.
      have hEq : (fun s => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z)
          = fun _ => (0 : ℝ) := by
        funext s
        exact gatedKernel_apply_of_notMem Kset S (whiteCutKernel κ hκ hKc a b)
          (u - s) 0 z (Or.inr h0)
      rw [hEq]; exact continuousAt_const
  · -- off the `q`-gate: constant `0`.
    have hEq : (fun s => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z)
        = fun _ => (0 : ℝ) := by
      funext s
      exact gatedKernel_apply_of_notMem Kset S (whiteCutKernel κ hκ hKc a b)
        (u - s) 0 z (Or.inl hz)
    rw [hEq]; exact continuousAt_const

/-! ###############################################################################
    ### §3 — the LEVI factor time-continuity from the banked JOINT continuity.
    ############################################################################### -/

/-- **`leviTimeCont_of_jointStrip`.**  The Levi factor's TIME-continuity `s ↦ leviSeries E s z 0` at
    a fixed `z`, extracted from the banked JOINT strip continuity `ContinuousOn (leviSeries slice)
    (Ioc 0 T ×ˢ univ)` (the `LeviMTest.hBcontEvery_of_carries` output) at any interior time
    `0 < s₀ < T`.  Route: `(s₀,z)` is interior (`Ioo 0 T ×ˢ univ ⊆ Ioc 0 T ×ˢ univ` is a `𝓝 (s₀,z)`),
    so the joint `ContinuousOn` gives joint `ContinuousAt`, restricted to the `s`-slice.
    NOT `a₁ = R/6`. -/
theorem leviTimeCont_of_jointStrip
    (E : ℝ → Point n → Point n → ℝ) (T : ℝ)
    (hJoint : ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))))
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀T : s₀ < T) (z : Point n) :
    ContinuousAt (fun s => leviSeries E s z 0) s₀ := by
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) :=
    isOpen_Ioo.prod isOpen_univ
  have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (Point n)) ∈ 𝓝 ((s₀, z) : ℝ × Point n) :=
    hopen.mem_nhds ⟨⟨hs₀, hs₀T⟩, Set.mem_univ z⟩
  have hsub : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))
      ⊆ Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n)) :=
    Set.prod_mono Set.Ioo_subset_Ioc_self (subset_refl _)
  have hmemIoc : Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n)) ∈ 𝓝 ((s₀, z) : ℝ × Point n) :=
    Filter.mem_of_superset hmem hsub
  have hcontAt : ContinuousAt (fun p : ℝ × Point n => leviSeries E p.1 p.2 0) (s₀, z) :=
    hJoint.continuousAt hmemIoc
  exact hcontAt.comp (f := fun s : ℝ => (s, z)) (continuousAt_id.prodMk continuousAt_const)

/-! ###############################################################################
    ### §4 — ★★★ the composed continuity with the WITNESS factor of `hcont` discharged.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_leviJoint` — `hcont` REDUCED TO THE BANKED LEVI JOINT CONTINUITY.**  For
    EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)` (`n > 0`), and window `U ⊆ (·,1]`, there ARE a fat open gate
    `S`, radii `0 < a < b`, and a width `lam = whiteLam ≥ 2` such that — MODULO ONLY the BANKED-SHAPE
    Levi JOINT continuity carry
        `∀ u ∈ U, ContinuousOn (fun p => leviSeries (whiteDefectKernel κ hκ hKc S a b) p.1 p.2 0)
              (Ioc 0 u ×ˢ univ)`
    (the `LeviMTest.hBcontEvery_of_carries` output, per ceiling `u`) — the interior-time continuity of
    the whitened inner pairing holds on `Ioo 0 u`, ∀ `u ∈ U`.  Obtained by feeding
    `white_hInnerCont_hmeas` (which discharges S1 + value + Levi B-slot + interior `hmeas`) its last
    open carry `hcont`, produced HERE by multiplying the DISCHARGED witness factor
    (`whiteWitness_time_continuousAt`, ∀ `z`) against the Levi factor time-continuity extracted from
    `hJoint` (`leviTimeCont_of_jointStrip`, at ceiling `T = u`).  The witness factor of `hcont` is GONE.
    ⚠ HONEST width `lam = whiteLam`; the Levi joint-continuity carry's own residual = the whitened
    `iterE` termwise joint continuity (the M-test wall).  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_leviJoint (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R)
    (U : Set ℝ) (hU1 : ∀ u ∈ U, u ≤ 1) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        ((∀ u ∈ U, ContinuousOn
              (fun p : ℝ × Point n =>
                leviSeries (whiteDefectKernel κ hκ hKc S a b) p.1 p.2 0)
              (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (Point n)))) →
          ∀ u ∈ U, ContinuousOn
            (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
              * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
            (Set.Ioo 0 u)) := by
  obtain ⟨S, a, b, ha, hab, hfat, lam, hlam2, himpl⟩ :=
    white_hInnerCont_hmeas hn κ hκ hKc R hKb U hU1
  refine ⟨S, a, b, ha, hab, hfat, lam, hlam2, fun hJoint => ?_⟩
  refine himpl ?_
  -- produce the `hcont` carry from the discharged witness factor × the extracted Levi factor.
  intro u hu s₀ hs₀
  refine Filter.Eventually.of_forall (fun z => ?_)
  exact (whiteWitness_time_continuousAt κ hκ hKc S a b u z hs₀.1 hs₀.2).mul
    (leviTimeCont_of_jointStrip (whiteDefectKernel κ hκ hKc S a b) u (hJoint u hu) hs₀.1 hs₀.2 z)

/-- **cp466 non-vacuity gate** — at genuinely curved data (`n = 2`, `κ = −1`, `K = closedBall 0 2`):
    the ∃-package of `white_hInnerCont_leviJoint` produces ONE FAT gate (`0 ∈ S 0`, open) with
    `0 < a < b` and a width `lam ≥ 2`.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_leviJoint_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ ∃ lam : ℝ, 2 ≤ lam := by
  obtain ⟨S, a, b, ha, hab, hgate, lam, hlam2, -⟩ :=
    white_hInnerCont_leviJoint (n := 2) (by norm_num) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
      (U := (∅ : Set ℝ)) (by simp)
  exact ⟨S, a, b, ha, hab,
    hgate 0 (Metric.mem_closedBall_self (by norm_num)), lam, hlam2⟩

end QIQTH.WhiteHcontWitnessFactor

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.WhiteHcontWitnessFactor

#print axioms gaussDdim_time_continuousAt
#print axioms whiteWitness_time_continuousAt
#print axioms leviTimeCont_of_jointStrip
#print axioms white_hInnerCont_leviJoint
#print axioms white_hInnerCont_leviJoint_witness_gate

end AxiomChecks
