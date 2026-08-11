/-
  WhiteGated — J4-625: residues R1 + R2 of the whitened `hpkgBound` — the GATING LIFT
  (gate/cutoff the whitened ambient kernel through the banked `gatedKernel` constructor and lift
  the gate-shaped bound toward the unconstrained `∀ (p,q)` capstone slot) and the WIDTH ALIGNMENT
  (the ambient width `λ = 2(nC₀²+1)` against the BridgeWidth width-`w` consumers).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; nothing here touches the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: whatever remains of R1/R2 (see the residue ledger below) + `hEbound`/`hInt` at the
  whitened kernel + the `K1TransportBudget` + the fat-`K` carrier piles + the capstone
  co-instantiation at the whitened witness + the prior analytic piles.

  ── R1 (the gating lift), WHAT LANDS UNCONDITIONALLY:
    • `whiteCutKernel` — the whitened ambient kernel with the SAME radial-cutoff layer as the
      as-built constructor (`globalCutoffParametrixWitnessN`'s `χ_{a,b}(V_q p)·(profile)(V_q p)`
      shape, at the whitened inverse chart `whiteInvChart` and the amplitude-carrying whitened
      Gaussian `whiteAmbientKernel`).
    • `whiteGatedWitness` — the cutoff kernel pushed through the BANKED `gatedKernel` constructor
      (the J4-97 `q`-gate + spatial set-gate), mirroring `vanVleckGatedWitness`'s structure with
      the whitened chart + amplitude (the constructor is parametric in the inverse chart, per the
      J4-624 finding).
    • OFF-GATE VANISHING (`whiteGated_heatOp_zero_offGate`, `whiteGated_heatOp_zero_farCutoff`) —
      `q ∉ K`, gate locally off `p`, or the cutoff collar (`b² ≤ rncRadialSq(V_q ·)` near `p`)
      each force `heatOp = 0`, by the banked G2b / kernel-locally-zero engines (J4-94/J4-97/T2).
    • DEEP ON-GATE AGREEMENT (`whiteGated_heatOp_eq_deep`) — where the gate is a neighborhood of
      `p` AND the cutoff is locally ≡ 1 (`rncRadialSq(V_q ·) < a²` near `p`), the gated witness's
      `heatOp` EQUALS the ungated `whiteAmbientKernel`'s: the HARD set-gate + the deep-region
      cutoff plateau transfer both germs (`heatOp_congr_nhds`), so NO commutator terms arise
      there.  ⚠ HONEST COMMUTATOR SCOPE: derivative-hits-the-cutoff terms live EXACTLY on the
      transition annulus `a² ≤ rncRadialSq(V_q p)` — isolated below as the SINGLE labelled
      analytic input `hann` of the lift; NOT discharged here (the whitened analogue of the flat
      tower's `cutoffResidualN1_…` campaign is J4-626+ material).
    • THE WIDTH-PARAMETRIC COVER ENGINE (`gatedKernel_hpkg_of_cover_w`) — the 3-leg cover
      (in-gate bound / off-gate / kernel-locally-zero collar) delivers the capstone-`hpkgBound`
      SHAPE `∀ t' τ p q, 0 < τ → τ ≤ t' → |heatOp (gatedKernel …)| ≤ C(1+t')·baseKernelW lam 0`
      at ANY width `lam` — the width-generic replay of the banked width-2 T4 engine
      (`OrderOneTower.gatedKernel_hEboundW_le_of_mixedCover`), UNCONDITIONAL.
    • ★ `white_hpkgBound_of_gatePackage` + ★ `white_hpkgBound` — THE LIFT: the FULL unconstrained
      `∀ (p,q)` capstone-`hpkgBound` shape at the whitened gated witness, at the honest width
      `lam = 2(nC₀²+1)`, CONDITIONAL on a labelled gate-certificate + annulus package:
        (i)   `hSopen`    — gate openness (the W1 chart-image-openness layer);
        (ii)  `hSchart`   — every gate point is a chart point `p = whiteExp_q w`, `‖w‖ < r₀`,
                            with the inverse-chart value/continuity certificate (the banked
                            `whiteInvChart_pack` supplies these at germ points; matching the
                            gate radius to the germ radius is the gate-choice residue);
        (iii) `hfrontier` — off-gate points are either interior-off or in the cutoff zero collar
                            (the W2 support-containment layer);
        (iv)  `hann`      — ⚠ THE analytic residue: the annulus/commutator bound for the cutoff
                            kernel on `a² ≤ rncRadialSq(V_q p)` (the flat tower paid this via the
                            `cutoffResidualN1_…` machinery; the whitened replay is owed).
      Legs (i)–(iii) are GEOMETRIC certificates (satisfiable chart facts, not the conclusion);
      leg (iv) is the honest analytic core.  Everything else in the lift is DERIVED.
  ── R1 RESIDUE (honest): discharging (i)–(iii) for a concrete fat gate at the whitened chart
      (the whitened replay of the flat `hgood`/`hchartOC` certificate) + the annulus bound (iv).

  ── R2 (the width alignment), FINDINGS + WHAT LANDS:
    • `C₀ = uniformFlowConst …` is an OPAQUE compactness constant (a `.choose` from
      `geodesic_apriori_confinement_uniform`) — it has NO banked numeric value, only `0 ≤ C₀`.
      Route (i) (numeric instantiation `λ ≤ 8` from `C₀ ≤ √(3/2)` at `n = 2`) is therefore NOT
      currently derivable; `whiteLam_le_eight_iff` records the EXACT alignment condition
      `λ = 2(nC₀²+1) ≤ 8 ↔ n·C₀² ≤ 3` at the actual constant.
    • Route (ii)/(iii), PROVED: the consumers split honestly —
        ▸ the BRIDGE tail engine (`BridgeWidth.bridgeGeneric_tail_O_s_w`) consumes ANY width
          `w > 0`; its `G_{8s}` landing (`…_G8`) needs `w ∈ [2,8]`.  `hEuni_of_hpkgBound_w`
          (width-generic replay of the banked `hEuni_of_hpkgBound`) turns THIS file's width-`lam`
          `hpkgBound` shape into the engine's τ-capped width-`lam` `hEuni` — so the whitened
          producer CAN feed the bridge at `w := lam` (λ ≥ 2 always; the `G8` landing exactly iff
          `λ ≤ 8`, i.e. iff `n·C₀² ≤ 3`).
        ▸ `hpkgBound_widen8` — single-step chain-widening (`gaussDdim_widen_le`, `λτ ≤ 8τ ≤ 4λτ`
          iff `2 ≤ λ ≤ 8`): under the HONEST hypothesis `λ ≤ 8`, the width-`λ` `hpkgBound` shape
          becomes a literal width-8 `hpkgBound` shape (constant pays `2ⁿ`).  Widening can only
          INCREASE width: the capstone's LITERAL width-2 `baseKernelW 2 0` slot is NOT reachable
          from `λ > 2` by widening; serving it needs either a sharpened displacement constant or
          the width-parametric capstone re-thread.  The capstone's `hpkgBound` binder is a FREE
          hypothesis supplied by the capstone USER; the width-`w` BRIDGE (what actually consumes
          the domination downstream) is served at `w = λ` as above.
  ── R2 RESIDUE (honest): `λ ≤ 8` (⟺ `n·C₀² ≤ 3`) is NOT proved (C₀ opaque); the literal
      width-2 capstone slot is NOT served at `λ > 2`.

  ── NON-VACUITY (cp466 discipline):
    • `whiteGatedWitness_diag_eval` / `whiteGated_witness_gate` — at the genuinely curved fat
      witness (`n = 2`, `κ = −1`, `K = closedBall 0 2`, gate `ball 0 1 ∋ 0`, cutoff `a=1 < b=2`)
      the CONSTRUCTED gated witness is NONZERO on the diagonal (`= gaussDdim τ 0 > 0`) — the
      gate+cutoff layers do not zero the object; the ambient flat-phase pair at the same witness
      provably admits NO width-2 bound (the banked J4-621 pin, re-exported).
    • `white_gatePackage_satisfiable_empty` — the ★ lift's antecedent package is jointly
      SATISFIABLE (at `S = ∅`), so the conditional theorem is not vacuously conditional.
      ⚠ HONEST LIMIT (cp466): at `S = ∅` the conclusion is DEGENERATE (gated kernel ≡ 0); this
      gate certifies non-contradictoriness of the antecedents ONLY.  The NON-degenerate (fat-`S`)
      instantiation = discharging (i)–(iv) at the whitened chart = the R1 residue.  DO NOT read
      this as a curved-satisfiable capstone claim.

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.WhiteAmbient
import QIQTH.GlobalHunifAssembly
import QIQTH.HunifTrichotomy
import QIQTH.CapstoneWiring
import QIQTH.FrozenK2Sharp

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.GaussianWidthTransfer QIQTH.GaussianWidthTolerant
open QIQTH.FrozenGauss QIQTH.LeviSeries QIQTH.WhiteWitness
open QIQTH.WhiteAmbient QIQTH.FrozenK2Sharp QIQTH.CurvedA1CenterAmp
open Set Filter
open scoped Topology BigOperators

namespace QIQTH.WhiteGated

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ### 1. R1 — the whitened cutoff kernel and the gated witness (the banked constructor). -/

/-- **The whitened CUTOFF kernel** — the whitened ambient kernel with the as-built constructor's
    radial-cutoff layer through the (whitened) inverse chart:
        `whiteCutKernel a b τ p q := χ_{a,b}(whiteInvChart_q p) · whiteAmbientKernel τ p q`
    (`= χ_{a,b}(V_q p)·√det g^κ(q)·G_τ(V_q p)` — exactly the
    `globalCutoffParametrixWitnessN`-shape `χ_{a,b}(V_q p)·(profile)(τ, V_q p)` with the whitened
    chart and the amplitude-carrying whitened Gaussian profile). -/
noncomputable def whiteCutKernel (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) : ℝ → Point n → Point n → ℝ :=
  fun τ p q => radialCutoff a b (whiteInvChart κ hκ hKc q p)
    * whiteAmbientKernel κ hκ hKc τ p q

/-- **THE WHITENED GATED WITNESS** — the whitened cutoff kernel pushed through the BANKED
    `gatedKernel` constructor (J4-97: `q`-gate onto `K` + hard spatial set-gate `S q`), mirroring
    `vanVleckGatedWitness`'s structure (`gatedKernel K S (χ·profile∘chart)`) at the whitened
    inverse chart and whitened amplitude. -/
noncomputable def whiteGatedWitness (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) :
    ℝ → Point n → Point n → ℝ :=
  gatedKernel Kset S (whiteCutKernel κ hκ hKc a b)

/-! ### 2. R1(a) — off-gate vanishing. -/

/-- **Off-gate vanishing, gate legs** — `q ∉ K` or the spatial gate locally off `p` force
    `heatOp = 0` (the banked G2b engine, J4-97). -/
theorem whiteGated_heatOp_zero_offGate (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (p q : Point n)
    (h : q ∉ Kset ∨ {p' : Point n | p' ∉ S q} ∈ nhds p) :
    heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteGatedWitness κ hκ hKc S a b) τ p q = 0 :=
  gatedKernel_heatOp_eq_zero_of_notMem _ _ Kset S (whiteCutKernel κ hκ hKc a b) τ p q h

/-- **Off-gate vanishing, cutoff-collar leg** — where the whitened chart image lies in the cutoff
    zero zone (`b² ≤ rncRadialSq (whiteInvChart_q p')` on a neighborhood of `p`), the cutoff
    kernel is locally `0` in both slots, so `heatOp = 0` (the banked kernel-locally-zero engine,
    J4-94/T2).  This is the collar leg covering the gate frontier. -/
theorem whiteGated_heatOp_zero_farCutoff (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (τ : ℝ) (p q : Point n)
    (hfar : {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p')} ∈ nhds p) :
    heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteGatedWitness κ hκ hKc S a b) τ p q = 0 := by
  have hpmem : p ∈ {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p')} :=
    mem_of_mem_nhds hfar
  have hp : b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p) := hpmem
  refine gatedKernel_heatOp_eq_zero_of_kernel_locally_zero _ _ Kset S
    (whiteCutKernel κ hκ hKc a b) τ p q ?_ ?_
  · -- time germ: the cutoff factor at `p` is `0` for every time.
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [whiteCutKernel, radialCutoff_eq_zero ha hab hp, zero_mul]
  · -- space germ: the cutoff factor vanishes on the far neighborhood.
    filter_upwards [hfar] with p' hp'
    simp only [whiteCutKernel, radialCutoff_eq_zero ha hab hp', zero_mul]

/-! ### 3. R1(b) — the DEEP on-gate agreement (no commutator terms on the cutoff plateau). -/

/-- **★ Deep on-gate agreement** — where the gate is a NEIGHBORHOOD of `p` (`q ∈ K`) AND the
    cutoff is locally on its plateau (`rncRadialSq (whiteInvChart_q ·) < a²` near `p`), the gated
    witness's `heatOp` EQUALS the ungated `whiteAmbientKernel`'s: both the time germ (hard gate +
    plateau are `τ`-independent) and the space germ transfer via the banked `heatOp_congr_nhds`.
    ⚠ HONEST COMMUTATOR SCOPE: derivative-hits-the-cutoff terms are EXACTLY confined to the
    transition annulus `a² ≤ rncRadialSq (whiteInvChart_q p)` — the labelled `hann` input of the
    lift below; they do NOT arise on the plateau. -/
theorem whiteGated_heatOp_eq_deep (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (τ : ℝ) (p q : Point n) (hq : q ∈ Kset)
    (hS : S q ∈ nhds p)
    (hdeep : {p' : Point n | rncRadialSq (whiteInvChart κ hκ hKc q p') < a ^ 2} ∈ nhds p) :
    heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteGatedWitness κ hκ hKc S a b) τ p q
      = heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ p q := by
  have hpS : p ∈ S q := mem_of_mem_nhds hS
  have hpdmem : p ∈ {p' : Point n | rncRadialSq (whiteInvChart κ hκ hKc q p') < a ^ 2} :=
    mem_of_mem_nhds hdeep
  have hpdeep : rncRadialSq (whiteInvChart κ hκ hKc q p) < a ^ 2 := hpdmem
  refine heatOp_congr_nhds _ _ (whiteAmbientKernel κ hκ hKc)
    (whiteGatedWitness κ hκ hKc S a b) τ p q ?_ ?_
  · -- time germ: gate + plateau are `τ`-independent, equality for ALL `t`.
    refine Filter.Eventually.of_forall (fun t => ?_)
    show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) t p q
        = whiteAmbientKernel κ hκ hKc t p q
    rw [gatedKernel_apply_of_mem Kset S _ t hq hpS]
    simp only [whiteCutKernel, radialCutoff_eq_one ha hab hpdeep.le, one_mul]
  · -- space germ: on the gate-∩-plateau neighborhood the two kernels agree.
    filter_upwards [hS, hdeep] with p' hp'S hp'deep
    show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ p' q
        = whiteAmbientKernel κ hκ hKc τ p' q
    rw [gatedKernel_apply_of_mem Kset S _ τ hq hp'S]
    simp only [whiteCutKernel, radialCutoff_eq_one ha hab hp'deep.le, one_mul]

/-! ### 4. THE WIDTH-PARAMETRIC COVER ENGINE (unconditional; also serves R2 route (iii)). -/

/-- **★ The width-`lam` capstone-shape cover engine** — the width-GENERIC replay of the banked
    width-2 T4 engine (`OrderOneTower.gatedKernel_hEboundW_le_of_mixedCover`): GIVEN the 3-leg
    cover — for each `q ∈ K`, `τ > 0`, `p`: (1) the gate is a neighborhood of `p` AND the UNgated
    kernel obeys the width-`lam` Gaussian bound at `p`; or (2) the gate is locally off `p`; or
    (3) the kernel is locally `0` at `(τ,p)` in both slots — the GATED kernel obeys the EXACT
    capstone-`hpkgBound` SHAPE at width `lam`, for ALL `(p,q)` (including `q ∉ K`):
        `∀ t' τ p q, 0 < τ → τ ≤ t' → |heatOp (gatedKernel K S H) τ p q|
            ≤ (C·(1+t'))·baseKernelW lam 0 τ p q`.
    UNCONDITIONAL in the gating machinery; the cover is the sole input.  NOT `a₁ = R/6`. -/
theorem gatedKernel_hpkg_of_cover_w (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (C lam : ℝ) (hC : 0 ≤ C)
    (hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
        (S q ∈ nhds p ∧ |heatOp g gi H τ p q| ≤ C * gaussDdim (lam * τ) (p - q))
      ∨ ({p' : Point n | p' ∉ S q} ∈ nhds p)
      ∨ ((fun t => H t p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ)))) :
    ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp g gi (gatedKernel K S H) τ p q|
        ≤ (C * (1 + t')) * QIQTH.GaussianWidthTolerant.baseKernelW lam 0 τ p q := by
  intro t' τ p q hτ hτt
  have ht' : (0 : ℝ) < t' := lt_of_lt_of_le hτ hτt
  have hbase : QIQTH.GaussianWidthTolerant.baseKernelW lam (0 : ℝ) τ p q
      = gaussDdim (lam * τ) (p - q) := baseKernelW_zero_apply lam τ p q
  have hG0 : 0 ≤ gaussDdim (lam * τ) (p - q) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hrhs : 0 ≤ (C * (1 + t')) * QIQTH.GaussianWidthTolerant.baseKernelW lam 0 τ p q := by
    rw [hbase]; exact mul_nonneg (mul_nonneg hC (by linarith)) hG0
  by_cases hq : q ∈ K
  · rcases hcover q hq τ hτ p with ⟨hS, hbd⟩ | hoff | ⟨htz, hsz⟩
    · rw [gatedKernel_heatOp_eq_of_mem_nhds g gi K S H τ p q hq hS, hbase]
      calc |heatOp g gi H τ p q|
          ≤ C * gaussDdim (lam * τ) (p - q) := hbd
        _ ≤ (C * (1 + t')) * gaussDdim (lam * τ) (p - q) := by
            nlinarith [mul_nonneg (mul_nonneg hC ht'.le) hG0]
    · rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inr hoff), abs_zero]
      exact hrhs
    · rw [gatedKernel_heatOp_eq_zero_of_kernel_locally_zero g gi K S H τ p q htz hsz, abs_zero]
      exact hrhs
  · rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inl hq), abs_zero]
    exact hrhs

/-! ### 5. ★ R1(c) — THE LIFT: the `∀ (p,q)` capstone-`hpkgBound` shape at the whitened witness. -/

/-- **★★ THE GATING LIFT (parametric core)** — the FULL unconstrained `∀ (p,q)`
    capstone-`hpkgBound` SHAPE at the whitened gated witness, width `lam`, from:
      ▸ `hbd` — the banked on-gate ungated producer bound (supplied by
        `white_ambient_heatOp_bound_displacement` at `lam = 2(nC₀²+1)`);
      ▸ `hSopen`/`hSchart` — the gate-certificate package: `S q` open, every gate point a chart
        point `p = whiteExp_q w` (`‖w‖ < r₀`) with the inverse-chart value + continuity
        certificate (the banked `whiteInvChart_pack` supplies these at germ points — matching
        the gate radius to the germ radius is the labelled gate-choice residue);
      ▸ `hfrontier` — the frontier certificate: off-gate points are interior-off OR in the
        cutoff zero collar (the W2 support-containment layer);
      ▸ `hann` — ⚠ THE HONEST ANALYTIC RESIDUE: the annulus/commutator bound for the cutoff
        kernel where the cutoff derivative lives (`a² ≤ rncRadialSq (whiteInvChart_q p)`); the
        flat tower paid this via `cutoffResidualN1_…`; the whitened replay is owed (J4-626+).
    The cover is DERIVED: deep gate points transfer to the ungated bound with NO commutator
    (`whiteGated_heatOp_eq_deep` germ argument), annulus points use `hann`, the frontier uses the
    collar, and everything feeds the width-parametric engine.  NOT `a₁ = R/6`. -/
theorem white_hpkgBound_of_gatePackage (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n))
    {a b r₀ CB lam : ℝ} (ha : 0 < a) (hab : a < b) (hCB : 0 ≤ CB)
    (hbd : ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ w : Point n, ‖w‖ < r₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ
          (whiteExp κ hκ hKc q w) q|
        ≤ CB * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q))
    (hSopen : ∀ q ∈ Kset, IsOpen (S q))
    (hSchart : ∀ q ∈ Kset, ∀ p ∈ S q, ∃ w : Point n,
      p = whiteExp κ hκ hKc q w ∧ ‖w‖ < r₀ ∧ whiteInvChart κ hκ hKc q p = w
        ∧ ContinuousAt (fun p' => whiteInvChart κ hκ hKc q p') p)
    (hfrontier : ∀ q ∈ Kset, ∀ p : Point n, p ∉ S q →
      ({p' : Point n | p' ∉ S q} ∈ nhds p)
      ∨ ({p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p')} ∈ nhds p))
    (hann : ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ p ∈ S q,
      a ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p) →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteCutKernel κ hκ hKc a b) τ p q|
        ≤ CB * gaussDdim (lam * τ) (p - q)) :
    ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (CB * (1 + t')) * QIQTH.GaussianWidthTolerant.baseKernelW lam 0 τ p q := by
  refine gatedKernel_hpkg_of_cover_w (curvedRNCMetric κ) (curvedRNCInv κ) Kset S
    (whiteCutKernel κ hκ hKc a b) CB lam hCB ?_
  intro q hq τ hτ p
  by_cases hpS : p ∈ S q
  · -- in-gate: split plateau vs annulus.
    have hSnhds : S q ∈ nhds p := (hSopen q hq).mem_nhds hpS
    by_cases hdeep : rncRadialSq (whiteInvChart κ hκ hKc q p) < a ^ 2
    · -- DEEP: cutoff ≡ 1 locally; the ungated cutoff kernel's heatOp EQUALS the ambient one.
      left
      refine ⟨hSnhds, ?_⟩
      obtain ⟨w, hpw, hwr, hVw, hVcont⟩ := hSchart q hq p hpS
      -- the plateau neighborhood via chart continuity.
      have hrc : ContinuousAt
          (fun p' => rncRadialSq (whiteInvChart κ hκ hKc q p')) p :=
        (rncRadialSq_contDiff.continuous.continuousAt).comp hVcont
      have hdeepnhds : {p' : Point n |
          rncRadialSq (whiteInvChart κ hκ hKc q p') < a ^ 2} ∈ nhds p :=
        hrc.preimage_mem_nhds (Iio_mem_nhds hdeep)
      -- no commutator on the plateau: cutoff kernel ≡ ambient kernel as germs.
      have heq : heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteCutKernel κ hκ hKc a b) τ p q
          = heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (whiteAmbientKernel κ hκ hKc) τ p q := by
        refine heatOp_congr_nhds _ _ (whiteAmbientKernel κ hκ hKc)
          (whiteCutKernel κ hκ hKc a b) τ p q ?_ ?_
        · refine Filter.Eventually.of_forall (fun t => ?_)
          simp only [whiteCutKernel, radialCutoff_eq_one ha hab hdeep.le, one_mul]
        · filter_upwards [hdeepnhds] with p' hp'
          simp only [whiteCutKernel, radialCutoff_eq_one ha hab hp'.le, one_mul]
      rw [heq, hpw]
      exact hbd q hq τ hτ w hwr
    · -- ANNULUS: the labelled commutator input.
      left
      exact ⟨hSnhds, hann q hq τ hτ p hpS (not_lt.mp hdeep)⟩
  · -- off-gate: frontier certificate → interior-off or cutoff zero collar.
    rcases hfrontier q hq p hpS with hoff | hfar
    · right; left; exact hoff
    · right; right
      have hpmem : p ∈ {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p')} :=
        mem_of_mem_nhds hfar
      have hp : b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p) := hpmem
      constructor
      · refine Filter.Eventually.of_forall (fun t => ?_)
        simp only [whiteCutKernel, radialCutoff_eq_zero ha hab hp, zero_mul]
      · filter_upwards [hfar] with p' hp'
        simp only [whiteCutKernel, radialCutoff_eq_zero ha hab hp', zero_mul]

/-- **★★ J4-625 (R1) — `white_hpkgBound`: the capstone-slot-shaped lift at the banked width.**
    The existential packaging at the BANKED producer: ONE radius `r₀ > 0`, ONE constant `C ≥ 0`,
    ONE width `lam ≥ 2` (the J4-624 producer's `lam = 2(nC₀²+1)`), such that for EVERY gate `S`
    and cutoff radii `0 < a < b` whose gate-certificate + annulus package holds AT THOSE
    `(r₀, lam, C)`, the whitened gated witness obeys the FULL unconstrained `∀ (p,q)`
    capstone-`hpkgBound` shape at width `lam`:
        `∀ t' τ p q, 0 < τ → τ ≤ t' → |heatOp g^κ gi^κ (whiteGatedWitness S a b) τ p q|
            ≤ (C·(1+t'))·baseKernelW lam 0 τ p q`.
    ⚠ LABELLED RESIDUES: the gate-certificate legs (i)–(iii) (whitened chart-openness/collar
    certificates) + the annulus/commutator bound (iv) — see `white_hpkgBound_of_gatePackage`;
    and R2: the width is `lam`, NOT the capstone's literal `2` (see §6).  NOT `a₁ = R/6`. -/
theorem white_hpkgBound (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ lam : ℝ, 2 ≤ lam ∧
      ∀ S : Point n → Set (Point n), ∀ a b : ℝ, 0 < a → a < b →
      (∀ q ∈ Kset, IsOpen (S q)) →
      (∀ q ∈ Kset, ∀ p ∈ S q, ∃ w : Point n,
        p = whiteExp κ hκ hKc q w ∧ ‖w‖ < r₀ ∧ whiteInvChart κ hκ hKc q p = w
          ∧ ContinuousAt (fun p' => whiteInvChart κ hκ hKc q p') p) →
      (∀ q ∈ Kset, ∀ p : Point n, p ∉ S q →
        ({p' : Point n | p' ∉ S q} ∈ nhds p)
        ∨ ({p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p')} ∈ nhds p)) →
      (∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ p ∈ S q,
        a ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p) →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteCutKernel κ hκ hKc a b) τ p q|
          ≤ C * gaussDdim (lam * τ) (p - q)) →
      ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteGatedWitness κ hκ hKc S a b) τ p q|
          ≤ (C * (1 + t')) * QIQTH.GaussianWidthTolerant.baseKernelW lam 0 τ p q := by
  obtain ⟨r₀, hr₀0, C, hC0, lam, hlam2, hbd⟩ :=
    white_ambient_heatOp_bound_displacement κ hκ hKc R hKb
  refine ⟨r₀, hr₀0, C, hC0, lam, hlam2, ?_⟩
  intro S a b ha hab hSopen hSchart hfrontier hann
  exact white_hpkgBound_of_gatePackage κ hκ hKc S ha hab hC0 hbd hSopen hSchart hfrontier hann

/-! ### 6. R2 — the width alignment against the consumers. -/

/-- **R2 route (ii): single-step chain-widening of the `hpkgBound` shape to the literal width 8**
    (the TOP of the BridgeWidth `G8`-landing range `w ∈ [2,8]`), for `2 ≤ lam ≤ 8`, via the
    banked `gaussDdim_widen_le` (`lam·τ ≤ 8·τ ≤ 4·lam·τ`); the constant pays `2ⁿ`.  ⚠ HONEST:
    widening can only INCREASE width — the capstone's LITERAL width-2 slot is NOT reachable from
    `lam > 2` this way; and `lam = 2(nC₀²+1) ≤ 8` is a genuine unproved condition (see
    `whiteLam_le_eight_iff`).  NOT `a₁ = R/6`. -/
theorem hpkgBound_widen8 (E : ℝ → Point n → Point n → ℝ) (C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam) (hlam8 : lam ≤ 8)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |E τ p q| ≤ (C * (1 + t')) * QIQTH.GaussianWidthTolerant.baseKernelW lam 0 τ p q) :
    ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |E τ p q| ≤ ((2 ^ n * C) * (1 + t'))
        * QIQTH.GaussianWidthTolerant.baseKernelW (8 : ℝ) 0 τ p q := by
  intro t' τ p q hτ hτt
  have ht' : (0 : ℝ) < t' := lt_of_lt_of_le hτ hτt
  have hwide : gaussDdim (lam * τ) (p - q) ≤ 2 ^ n * gaussDdim (8 * τ) (p - q) :=
    gaussDdim_widen_le (lam * τ) (8 * τ) (by nlinarith) (by nlinarith) (by nlinarith) _
  have h := hpkg t' τ p q hτ hτt
  rw [baseKernelW_zero_apply] at h ⊢
  calc |E τ p q|
      ≤ (C * (1 + t')) * gaussDdim (lam * τ) (p - q) := h
    _ ≤ (C * (1 + t')) * (2 ^ n * gaussDdim (8 * τ) (p - q)) := by
        refine mul_le_mul_of_nonneg_left hwide ?_
        exact mul_nonneg hC (by linarith)
    _ = ((2 ^ n * C) * (1 + t')) * gaussDdim (8 * τ) (p - q) := by ring

/-- **R2 route (iii): the width-GENERIC `hEuni` slice** — the width-`lam` replay of the banked
    `BridgeWidth.hEuni_of_hpkgBound`: the width-`lam` `hpkgBound` shape, sliced at `t' = 1`,
    IS the bridge tail engine's τ-capped uniform width-`lam` domination `hEuni` with `C_U = 2C`.
    The BRIDGE engine `bridgeGeneric_tail_O_s_w` consumes ANY `w > 0` — so the whitened producer
    feeds it at `w := lam` (with the `G_{8s}` landing exactly when `lam ∈ [2,8]`); the capstone's
    literal width-2 binder is a SEPARATE slot, not served by this at `lam > 2`.  NOT `a₁ = R/6`. -/
theorem hEuni_of_hpkgBound_w (E : ℝ → Point n → Point n → ℝ) (C lam : ℝ)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |E τ p q| ≤ (C * (1 + t')) * QIQTH.GaussianWidthTolerant.baseKernelW lam 0 τ p q) :
    ∀ τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ (2 * C) * gaussDdim (lam * τ) (p - q) := by
  intro τ p q hτ hτ1
  have h := hpkg 1 τ p q hτ hτ1
  rw [baseKernelW_zero_apply] at h
  calc |E τ p q| ≤ (C * (1 + 1)) * gaussDdim (lam * τ) (p - q) := h
    _ = (2 * C) * gaussDdim (lam * τ) (p - q) := by ring

/-- **R2, the alignment condition at the ACTUAL constant** — the producer width
    `lam = 2(n·C₀² + 1)` (with `C₀` the banked uniform tube-confinement constant
    `uniformFlowConst`, an OPAQUE `.choose` compactness constant with no banked numeric value)
    lies in the BridgeWidth `G8`-landing range `[2, 8]` **iff** `n·C₀² ≤ 3`.  This records the
    exact unproved condition of R2 route (i); `lam ≥ 2` holds unconditionally.  NOT `a₁ = R/6`. -/
theorem whiteLam_le_eight_iff (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    (2 * ((n : ℝ) * (uniformFlowConst (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc) ^ 2 + 1) ≤ 8)
      ↔ ((n : ℝ) * (uniformFlowConst (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc) ^ 2 ≤ 3) := by
  constructor <;> intro h <;> nlinarith [h]

/-! ### 7. Non-vacuity / adversarial gates (cp466 discipline). -/

/-- **The gated witness is nonzero on the diagonal at the origin** — with `0 ∈ K`, `0 ∈ S 0`,
    `0 < a < b`, the whitened gated witness evaluates at the origin diagonal to the RAW Gaussian:
        `whiteGatedWitness S a b τ 0 0 = gaussDdim τ 0`
    (the chart fixes the origin, the whitening is linear, the cutoff is on its plateau, and the
    amplitude `√det g^κ(0) = 1` at the RNC center) — the gate + cutoff layers do NOT zero the
    constructed object.  NOT `a₁ = R/6`. -/
theorem whiteGatedWitness_diag_eval (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (τ : ℝ)
    (h0K : (0 : Point n) ∈ Kset) (hS0 : (0 : Point n) ∈ S 0) :
    whiteGatedWitness κ hκ hKc S a b τ 0 0 = gaussDdim τ (0 : Point n) := by
  show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ 0 0 = gaussDdim τ (0 : Point n)
  rw [gatedKernel_apply_of_mem Kset S _ τ h0K hS0]
  have hV0 : whiteInvChart κ hκ hKc (0 : Point n) (0 : Point n) = 0 := by
    show whiteUnvel κ 0 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc 0 0) = 0
    rw [uniformInverseChart_zero (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc h0K, map_zero]
  have hdet : Matrix.det (curvedRNCMetric κ (0 : Point n)) = 1 := by
    have h1 : curvedRNCMetric κ (0 : Point n) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      funext i j
      rw [curvedRNCMetric_zero κ i j, Matrix.one_apply]
    rw [h1, Matrix.det_one]
  simp only [whiteCutKernel, whiteAmbientKernel, hV0]
  rw [radialCutoff_eq_one ha hab (by rw [rncRadialSq_zero]; positivity),
    hdet, Real.sqrt_one, one_mul, one_mul]

/-- **★ The witness gate** — at the genuinely curved fat witness (`n = 2`, `κ = −1`,
    `K = closedBall 0 2`, gate `S ≡ ball 0 1 ∋ 0`, cutoff `a = 1 < b = 2`):
    (i) the constructed whitened gated witness is STRICTLY POSITIVE on the origin diagonal at
    every `τ > 0` — the gate/cutoff constructor layers are non-degenerate on the object;
    (ii) the AMBIENT flat-phase pair at the SAME witness provably admits NO width-2 uniform
    Gaussian bound (the banked J4-621 formal pin, re-exported) — the whitened gated route is not
    the flat tower in disguise.  NOT `a₁ = R/6`. -/
theorem whiteGated_witness_gate :
    (∀ τ : ℝ, 0 < τ →
      0 < whiteGatedWitness (-1 : ℝ) (by norm_num) (isCompact_closedBall (0 : Point 2) 2)
        (fun _ => Metric.ball (0 : Point 2) 1) 1 2 τ 0 0)
    ∧ (¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ p q : Point 2,
        |heatOp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
            (fun t x y => flatPhaseModel t x y) τ p q|
          ≤ C * gaussDdim (2 * τ) (fun i => p i - q i)) := by
  refine ⟨fun τ hτ => ?_, flatPhase_hpkgBound_fails_witness⟩
  rw [whiteGatedWitness_diag_eval (-1 : ℝ) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => Metric.ball (0 : Point 2) 1)
    one_pos (by norm_num) τ
    (Metric.mem_closedBall_self (by norm_num))
    (Metric.mem_ball_self one_pos)]
  exact gaussDdim_pos τ hτ _

/-- **Antecedent-inhabitance gate for the ★ lift** (cp466 discipline — the axiom-budget blind
    spot is UNSATISFIABLE antecedents): the gate-certificate + annulus package of
    `white_hpkgBound` is jointly SATISFIABLE — witnessed at `S = ∅` (all four certificate legs
    hold: openness trivially, chart/annulus legs vacuously over the empty gate, frontier by the
    interior-off leg `{p' | p' ∉ ∅} = univ ∈ 𝓝 p`).
    ⚠⚠ HONEST LIMIT: at `S = ∅` the CONCLUSION is DEGENERATE (the gated witness ≡ 0), so this
    gate certifies ONLY that the conditional theorem is not vacuously conditional (the
    antecedents are not contradictory).  It does NOT certify a non-degenerate curved
    instantiation: the FAT-gate discharge of legs (i)–(iv) at the whitened chart is the
    labelled R1 residue.  DO NOT read this as a curved-satisfiable capstone claim. -/
theorem white_gatePackage_satisfiable_empty (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (r₀ C lam : ℝ) (a b : ℝ) :
    (∀ q ∈ Kset, IsOpen ((fun _ : Point n => (∅ : Set (Point n))) q))
    ∧ (∀ q ∈ Kset, ∀ p ∈ (fun _ : Point n => (∅ : Set (Point n))) q, ∃ w : Point n,
        p = whiteExp κ hκ hKc q w ∧ ‖w‖ < r₀ ∧ whiteInvChart κ hκ hKc q p = w
          ∧ ContinuousAt (fun p' => whiteInvChart κ hκ hKc q p') p)
    ∧ (∀ q ∈ Kset, ∀ p : Point n, p ∉ (fun _ : Point n => (∅ : Set (Point n))) q →
        ({p' : Point n | p' ∉ (fun _ : Point n => (∅ : Set (Point n))) q} ∈ nhds p)
        ∨ ({p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p')} ∈ nhds p))
    ∧ (∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ p ∈ (fun _ : Point n => (∅ : Set (Point n))) q,
        a ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p) →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteCutKernel κ hκ hKc a b) τ p q|
          ≤ C * gaussDdim (lam * τ) (p - q)) := by
  refine ⟨fun q _ => isOpen_empty, fun q _ p hp => absurd hp (Set.notMem_empty p),
    fun q _ p _ => Or.inl ?_, fun q _ τ _ p hp => absurd hp (Set.notMem_empty p)⟩
  have : {p' : Point n | p' ∉ (∅ : Set (Point n))} = Set.univ := by
    ext p'; simp
  rw [this]
  exact Filter.univ_mem

end QIQTH.WhiteGated

section AxiomChecks
open QIQTH.WhiteGated
#print axioms QIQTH.WhiteGated.whiteGated_heatOp_zero_offGate
#print axioms QIQTH.WhiteGated.whiteGated_heatOp_zero_farCutoff
#print axioms QIQTH.WhiteGated.whiteGated_heatOp_eq_deep
#print axioms QIQTH.WhiteGated.gatedKernel_hpkg_of_cover_w
#print axioms QIQTH.WhiteGated.white_hpkgBound_of_gatePackage
#print axioms QIQTH.WhiteGated.white_hpkgBound
#print axioms QIQTH.WhiteGated.hpkgBound_widen8
#print axioms QIQTH.WhiteGated.hEuni_of_hpkgBound_w
#print axioms QIQTH.WhiteGated.whiteLam_le_eight_iff
#print axioms QIQTH.WhiteGated.whiteGatedWitness_diag_eval
#print axioms QIQTH.WhiteGated.whiteGated_witness_gate
#print axioms QIQTH.WhiteGated.white_gatePackage_satisfiable_empty
end AxiomChecks
