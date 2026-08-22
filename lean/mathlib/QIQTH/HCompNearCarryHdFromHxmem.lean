/-
  HCompNearCarryHdFromHxmem — J4-993: `hd` (differentiability of `witnessFieldDeriv`, `nb`'s remaining
  named-carry alongside `hxmem`) REDUCED to `hxmem` itself at the concrete flow-ball gate — a genuine,
  standalone composition, valuable independently of `hxmem`'s (currently blocked) status.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  `HCompNearCarryJetBundleConcreteGateDischarge.kPrime_baseField_CoV_of_jetBundle_gateRestricted_concreteGate`
  (J4-1032) leaves EXACTLY two residues beyond radius/metric bookkeeping: `hxmem` (`∀ z ∈ K, x ∈ S z`,
  DEFINITIVELY BLOCKED per cp988–cp991 — an architectural `uniformFlowExp` witness-sharing wall) and
  `hd` (`∀ z ∈ K, DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t − s) y z) x`,
  untouched until this dispatch).

  THIS FILE shows `hd` is NOT an independent obstruction: on the concrete gate, `hd` follows FROM
  `hxmem` alone (plus the standard metric data `hg`/`hgpos`/`hu`, already standing hypotheses of the
  live capstone) — no further chart-`C²` carry, no joint-regularity wall.  So the theorem's antecedent
  set effectively COLLAPSES from `{hxmem, hd}` to `{hxmem}`: once `hxmem` is discharged by a future
  architectural redesign of `uniformFlowExp` (out of scope here, per cp991), `hd` comes for free.

  ── THE MECHANISM (three already-banked bricks, single-variable — NOT the blocked joint-C² story).
    1. `ConcreteGateAssembly.reachableGate_concrete` — the concrete flow-ball gate `S z = φ_z '' ball 0 c`
       (`0 < c < δ₀`) is OPEN, and EVERY gate point `x ∈ S z` is reachable with the chart `W z :=
       uniformInverseChart … z` `ContDiffAt ℝ 2` AT `x` — for the FIXED `z`, no joint-in-`(z,x)`
       regularity needed (this is exactly the brick J4-1032 already used, index-swapped, for its own
       jet-bundle discharge).
    2. `OnGateFieldRegularity.gatedWitness_contDiffAt_field` — on the gate (`x ∈ S z` open, chart `C²`
       at `x`) the field-slot gated witness `x' ↦ vanVleckGatedWitness … x' z` is itself `ContDiffAt ℝ 2`
       at `x` (local coincidence with the smooth inner kernel + factor-wise `ContDiffAt.comp`).
    3. `HFdCoreContinuityClosed.pd_contDiffAt_one_of_two` — a `ContDiffAt ℝ 2` scalar field's coordinate
       partial `pd F i` is itself `ContDiffAt ℝ 1` (hence `DifferentiableAt`) — the SAME engine already
       banked for `hFd`'s core-continuity discharge (J4-874), applied here to `F := witness(·, z)`,
       giving DIRECTLY the FULL (all-direction) `DifferentiableAt` `hd` needs (`pd F i`'s target is
       `witnessFieldDeriv`'s OWN definition, `pd (fun x' => vanVleckGatedWitness … x' z) i`).

  Composing (1)+(2)+(3) at the SAME `x` for each `z ∈ K` supplied by `hxmem` yields `hd` outright — no
  new analytic content beyond the three banked bricks, no chart-`C²` carry left over.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `hxmem`
  itself is NOT discharged here (per cp988–cp991, it needs an architectural redesign of `uniformFlowExp`,
  explicitly out of scope for this dispatch) — this file only shows `hd` is REDUNDANT once `hxmem` is
  available, collapsing `nb`'s term1 residue set from `{hxmem, hd}` to `{hxmem}`.  `Bfac`'s other three
  summands (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`, `∂ⱼ∂ᵢA` diagonal legs beyond `hsMixed·A`) remain entirely untouched,
  and `fb` (the far carry) remains SEPARATELY open.  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.  `a₁ = R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ConcreteGateAssembly
import QIQTH.HFdCoreContinuityClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open QIQTH.ExpMap QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ConcreteGateAssembly QIQTH.OnGateFieldRegularity QIQTH.HFdCoreContinuityClosed
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryHdFromHxmem

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `hd_of_hxmem_concreteGate`.**  `hd` — the field-differentiability of `witnessFieldDeriv` at
    `x`, for every `z ∈ K` — REDUCED to `hxmem` alone at the concrete flow-ball gate `S z = φ_z '' ball
    0 c`, given the standard metric data `hg`/`hgpos`/`hu`.  No chart-`C²` carry survives: the concrete
    gate supplies it for free (`reachableGate_concrete`), the field-slot witness inherits `ContDiffAt ℝ
    2` on-gate (`gatedWitness_contDiffAt_field`), and its coordinate partial is `ContDiffAt ℝ 1`, hence
    `DifferentiableAt`, at `x` (`pd_contDiffAt_one_of_two`).  So `hd` is NOT an independent obstruction
    beyond `hxmem` on the concrete gate — `nb`'s term1 residue set collapses from `{hxmem, hd}` to
    `{hxmem}`.  NOT `a₁ = R/6`. -/
theorem hd_of_hxmem_concreteGate
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (a b : ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (i : Fin n) (τ : ℝ) (x : Point n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
    ∀ (hxmem : ∀ z ∈ K, x ∈ S z),
    ∀ z ∈ K, DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := reachableGate_concrete g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ S hSeq hxmem z hz
  subst hSeq
  obtain ⟨hSopen, _hLI, hReach⟩ := hspec c hc0 hcδ z hz
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  have hxSz : x ∈ S z := hxmem z hz
  have hxSz' : x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c := by
    rw [hSdef] at hxSz; exact hxSz
  obtain ⟨_hReachx, hWC2⟩ := hReach x hxSz'
  have hCD2 : ContDiffAt ℝ 2
      (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) x :=
    gatedWitness_contDiffAt_field g gi hC hK S a b τ z x hz hxSz hSopen hWC2 hg hgpos hu
  have hC1 : ContDiffAt ℝ 1
      (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y) x :=
    pd_contDiffAt_one_of_two (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x hCD2
  have hDiff : DifferentiableAt ℝ
      (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y) x :=
    hC1.differentiableAt (by norm_num)
  simpa [witnessFieldDeriv] using hDiff

end QIQTH.HCompNearCarryHdFromHxmem

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryHdFromHxmem
#print axioms hd_of_hxmem_concreteGate
end AxiomChecks
