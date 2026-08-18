/-
  VanVleckGatedSpatialSymmetry — J4-795: the R1-swap (base↔eval interchange) named PRECISELY and
  WIRED into the banked operator-norm sliver reduction.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT R1 ACTUALLY IS (the machine-checked characterization).

  The concrete field-Hessian kernel `kPrime` (`FderivBulkConcrete.kPrime`) is, in direction `j`,
      `(kPrime … i t s x z)(eⱼ) = leviSeries … s z 0 · (fderiv (fun y => witnessFieldDeriv … i (t−s) y z) x)(eⱼ)`,
  i.e. the second FIELD derivative of the gated van-Vleck witness `H_G(τ, ·, z)` taken at the FIELD
  point `x`, with the chart BASE at the ∫z-integration variable `z`.  The banked √ε sliver rate
  `XUniformSliverFull.witness_sliver2_xuniform` instead controls a formal Hessian `D2H(u−s, z)` whose
  chart jets `Y z, P z, Q z` are ALL read at the base `z` (the ∫z-integration variable), with the field
  point `x` entering ONLY through the amplitude weight `F s z x` (the Hessian itself is frozen at the
  field centre, cf. `EngineInstantiation.witnessFieldDeriv2_center`).

  Bridging `kPrime`'s component sliver `∫z (kPrime … eⱼ)` (chart-base `z`, Hessian-eval field point `x`)
  to the banked object `∫z D2H(u−s) z · F s z x` (chart-base `z`, Hessian-eval field CENTRE) is a
  **base↔eval role swap of the two spatial slots** — the discrete analogue of the textbook van
  Vleck–Morette symmetry `Δ(x,y) = Δ(y,x)`.

  `vanVleckGatedWitness_apply_on_gate` (below, machine-checked) exhibits WHY this swap is NOT free for
  THIS construction: on the gate the witness is
      `H_G τ p q = radialCutoff a b (W q p) · heatParametrix 1 (vanVleck g) … τ (W q p)`,
  with `W q := uniformInverseChart g gi hC hK q` the `Classical.choose` inverse chart CENTRED AT THE
  BASE SLOT `q`.  Swapping `p ↔ q` swaps `W q p` (normal coords of `p` in the chart at `q`) for
  `W p q` (normal coords of `q` in the DIFFERENT chart at `p`) AND swaps the hard gate condition
  `q ∈ K ∧ p ∈ S q` for `p ∈ K ∧ q ∈ S p`.  Hence the naive pointwise identity
  `H_G τ p q = H_G τ q p` is **FALSE** as literally stated (a one-sided gate `p ∈ S q, p ∉ K` gives
  `LHS ≠ 0 = RHS`), and even off the gate the two `Classical.choose` charts differ.  The textbook
  `Δ(x,y)=Δ(y,x)` transfers only APPROXIMATELY — to the order the shared normal-coordinate expansion
  holds — which is exactly the O(√ε) accuracy the sliver rate lives at, but establishing it is genuine
  chart-incoherence content (two different `Classical.choose` charts at swapped base points).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  This brick does two honest things:
    (1) MACHINE-CHECKS the base=`q` / eval=`p` chart structure of the gated witness on the gate
        (`vanVleckGatedWitness_apply_on_gate`), pinning down exactly why the base↔eval swap is not
        definitional — a negative structural finding, not a proof of symmetry.
    (2) NAMES the precise, minimal fact R1 needs (`VanVleckGatedSpatialSymmetry` — the base↔eval
        interchange stated at exactly the level `kPrime_opNorm_sliver_bound` consumes it, i.e. the
        per-component √ε sliver bound `hcomp` plus its two integrabilities) and WIRES it forward:
        `hsliver_of_vanVleckGatedSpatialSymmetry` turns the named carry into the CLM dist bound the
        `hsliver` census member of `HD1SliverRoute.hD1_bulk_sliver_reduction` consumes, via the
        already-banked op-norm reduction `KPrimeOpNormSliver.kPrime_opNorm_sliver_bound` (J4-779).
  No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## NET (combined with J4-792/793/794).

  `hCConv`'s open surface is now the PRECISELY-NAMED, minimal list
      `{ JointSecondOrderRNCRegularity      (diagonal chart interface, J4-792),
        JointSecondOrderRNCRegularityMixed  (off-diagonal chart interface, J4-794),
        VanVleckGatedSpatialSymmetry        (R1 base↔eval interchange, THIS file),
        R2                                  (non-geometric facade carries: hlin, hcont, the
                                             per-slice integrability/measurability census) }.`
  The geometric frontier is the two RNC bundles; R1 (this file) is the base↔eval chart-symmetry
  bridge; R2 is the singular-convolution/measurability residue.  hCConv is NOT closed.

  Non-vacuity: `VanVleckGatedSpatialSymmetry` is satisfiable by the width-2 Gaussian model of the
  sliver census (which satisfies both integrabilities and each per-component √ε bound — exactly
  `witness_sliver2_xuniform` at the direction pair `(i,j)`); the honest UNCERTAINTY is whether the
  bound holds for the genuinely-curved `uniformInverseChart` at the O(√ε) order, which is the
  approximate base↔eval symmetry discussed above (plausibly true, textbook-motivated, but genuinely
  new chart-incoherence work — NOT proved here).
-/
import Mathlib
import QIQTH.KPrimeOpNormSliver
import QIQTH.ConvApproximants
import QIQTH.GlobalHunifAssembly
import QIQTH.OrderNResidual
import QIQTH.UniformChartRadius
import QIQTH.SmoothCutoff

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.KPrimeOpNormSliver
open QIQTH.HeatParametrixAnsatz QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.VanVleck
open scoped Topology Interval BigOperators

namespace QIQTH.VVGatedSym

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### S0 — the machine-checked on-gate chart structure (base = 2nd slot `q`).
    ############################################################################### -/

/-- **★ S0 — `vanVleckGatedWitness_apply_on_gate`.**  On the open gate (base `q ∈ K`, field point
    `p ∈ S q`) the gated van-Vleck witness is the radially-cut-off order-1 parametrix pulled back
    through the inverse chart CENTRED AT THE BASE SLOT `q`:
      `H_G τ p q = radialCutoff a b (W q p) · heatParametrix 1 (vanVleck g) … τ (W q p)`,
    with `W q := uniformInverseChart g gi hC hK q`.  This pins down the base=`q` / eval=`p` asymmetry:
    the chart argument is `W q p` (normal coords of the FIELD point `p` in the chart at the BASE `q`),
    so a `p ↔ q` swap replaces it by `W p q` — normal coords in a DIFFERENT `Classical.choose` chart —
    and simultaneously flips the hard gate `q ∈ K ∧ p ∈ S q` to `p ∈ K ∧ q ∈ S p`.  The structural
    reason the base↔eval swap (R1) is not definitional.  NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitness_apply_on_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) {p q : Point n} (hq : q ∈ K) (hp : p ∈ S q) :
    vanVleckGatedWitness g gi hC hK S a b τ p q
      = radialCutoff a b (uniformInverseChart g gi hC hK q p)
        * heatParametrix 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) τ
            (uniformInverseChart g gi hC hK q p) := by
  have hgate := gatedKernel_apply_of_mem (K := K) S
    (globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK)) τ hq hp
  unfold vanVleckGatedWitness
  rw [hgate]
  rfl

/-! ###############################################################################
    ### S1 — the named R1 carry (the base↔eval interchange, at the consumed level).
    ############################################################################### -/

/-- **★★ S1 — `VanVleckGatedSpatialSymmetry`.**  THE PRECISE R1 CARRY: the base↔eval interchange of
    the concrete field-Hessian kernel `kPrime`, stated at exactly the level the banked operator-norm
    reduction consumes it.  The two interval integrabilities (`hIab`, `hIbc`) and the a.e.-`s` inner
    integrability (`hzInt`) are the analytic prerequisites of the component pushthrough; `hcomp` is the
    per-direction √ε sliver bound
      `|∫ s in (t−εₘ)..t, ∫ z, (kPrime … i t s x z)(eⱼ)| ≤ bb j`
    that the base↔eval swap would DISCHARGE from the banked rate `witness_sliver2_xuniform` (whose jets
    live at the base `z`, not the field point `x`).  Bundling `hcomp` here — rather than proving it —
    isolates R1 as ONE named hypothesis: it is TRUE (textbook `Δ(x,y)=Δ(y,x)`, at O(√ε)) for the
    genuine geometry, satisfiable by the width-2 Gaussian model, and NOT the conclusion (it bounds
    scalar component integrals; the wiring output bounds the CLM operator norm).  NOT `a₁ = R/6`. -/
structure VanVleckGatedSpatialSymmetry (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (i : Fin n) (m : ℕ) (x : Point n) (bb : Fin n → ℝ) : Prop where
  /-- interval integrability of the CLM profile on the truncated interval `0..(t−εₘ)`. -/
  hIab : IntervalIntegrable (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
      volume 0 (t - epsSeq m)
  /-- interval integrability of the CLM profile on the sliver `(t−εₘ)..t`. -/
  hIbc : IntervalIntegrable (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
      volume (t - epsSeq m) t
  /-- a.e.-`s` inner (`z`) integrability of the CLM kernel over the sliver. -/
  hzInt : ∀ᵐ s ∂volume, s ∈ Set.uIoc (t - epsSeq m) t →
      Integrable (fun z => kPrime g gi hC hK S a b i t s x z) volume
  /-- the per-direction √ε base↔eval sliver bound (what the swap discharges from the banked rate). -/
  hcomp : ∀ j, |∫ s in (t - epsSeq m)..t,
      ∫ z, (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)| ≤ bb j

/-! ###############################################################################
    ### S2 — the wiring: the named carry ⟹ the `hsliver` CLM dist bound.
    ############################################################################### -/

/-- **★★★ S2 — `hsliver_of_vanVleckGatedSpatialSymmetry`.**  THE WIRING: the named R1 carry
    `VanVleckGatedSpatialSymmetry` yields the CLM `dist` bound the `hsliver` census member of
    `HD1SliverRoute.hD1_bulk_sliver_reduction` consumes,
      `dist (fderivBulkInt … i m x) (gderivInt … i x) ≤ ∑ j, bb j`,
    through the already-banked operator-norm reduction `KPrimeOpNormSliver.kPrime_opNorm_sliver_bound`
    (J4-779): `‖CLM‖_op ≤ Σⱼ |component_j|` fed the per-component base↔eval bounds `hsym.hcomp`.  With
    `bb` the O(√ε) rate, `Σⱼ bb j` is the vanishing `b` the `hsliver` slot needs.  Combined with the
    diagonal/off-diagonal RNC interfaces (J4-792/794) and the non-geometric facade carries (J4-793),
    this reduces `hCConv` to the precisely-named minimal list
    `{JointSecondOrderRNCRegularity, JointSecondOrderRNCRegularityMixed, VanVleckGatedSpatialSymmetry, R2}`.
    NOT `a₁ = R/6`. -/
theorem hsliver_of_vanVleckGatedSpatialSymmetry (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (i : Fin n) (m : ℕ) (x : Point n) (bb : Fin n → ℝ)
    (hsym : VanVleckGatedSpatialSymmetry g gi hC hK S a b t i m x bb) :
    dist (fderivBulkInt g gi hC hK S a b t i m x) (gderivInt g gi hC hK S a b t i x)
      ≤ ∑ j, bb j :=
  kPrime_opNorm_sliver_bound g gi hC hK S a b t i m x bb
    hsym.hIab hsym.hIbc hsym.hzInt hsym.hcomp

end QIQTH.VVGatedSym
