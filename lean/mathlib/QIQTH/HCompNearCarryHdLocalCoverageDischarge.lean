/-
  HCompNearCarryHdLocalCoverageDischarge — J4-1045: composes `HCompNearCarryHdFromHxmem`'s
  `hd_of_hxmem_concreteGate` (J4-1034: `hd` REDUCED to `hxmem` alone, pointwise-in-`z`, at the concrete
  flow-ball gate) with `HxmemLocalSharpReachCoverage`'s `uniformFlowExp_local_coverage_ball` (J4-1042:
  `hxmem` DERIVED, not assumed, on `K ∩ Metric.ball x R`) to produce, for the FIRST time, `hd` itself
  GENUINELY DERIVED (not assumed) — on the SAME shrunk domain `K ∩ Metric.ball x R` that J4-1044 already
  delivered `hxmem` on.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`. No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited (NEW FILE).

  ── WHY THE COMPOSITION IS SOUND (checked pointwise, confirmed by gpt-5.6-sol high BEFORE writing this
  file).  J4-1034's proof of `hd_of_hxmem_concreteGate` only ever uses, for the SINGLE `z` at hand:
  (a) `z ∈ K` — fed to `reachableGate_concrete`'s `∀ z ∈ K` binder (this lemma is pointwise in `z`, no
      joint-in-`(x,z)` regularity, and does NOT depend on `x` when producing `δ₀`);
  (b) `x ∈ S z` — fed to `gatedWitness_contDiffAt_field` (also pointwise in `z`, given `x ∈ S z`).
  So restricting the quantifier domain from `z ∈ K` to `z ∈ K ∩ Metric.ball x R` is MECHANICAL: supply
  `hz.1 : z ∈ K` where `z ∈ K` was used, and supply the NEWLY-DERIVED (not assumed) membership fact
  `x ∈ S z` — sourced from `uniformFlowExp_local_coverage_ball` instead of an external `hxmem` hypothesis
  — everywhere the old external `hxmem z hz` appeared.  `K` itself, `hK`, and the gate formula `S z :=
  uniformFlowExp g gi hC hK z '' Metric.ball 0 c` are UNCHANGED (no re-derivation of `uniformFlowExp` on
  a shrunk `K`, no `K ↦ r(K) ↦ K` circularity — the SAME hazard that closed off `hxmem`'s general
  discharge, per cp988–cp991, is avoided exactly as it was in J4-1042/1044).

  The one genuine bookkeeping step (identified by Sol, exactly the shape J4-1044 already used): the two
  source lemmas constrain `c` differently — `reachableGate_concrete` needs `0 < c < δ₀`, while
  `uniformFlowExp_local_coverage_ball` needs `0 < c ≤ ρ₀ ∧ C_L * c < 1` — so the composed theorem below
  existentially quantifies `δ₀, ρ₀, C_L` jointly and asks the caller for a `c` satisfying BOTH constraint
  sets at once (pure side-condition conjunction, not conflicting analytic content — any sufficiently
  small `c > 0` satisfies all four inequalities simultaneously). `R` (the coverage radius) is obtained
  from `uniformFlowExp_local_coverage_ball` AFTER `c` is fixed, exactly as in J4-1042/1044 — no
  quantifier-order circularity, since `δ₀, ρ₀, C_L` never depend on `x` or `R`.

  ── WHAT THIS FILE DOES NOT DO.  It does NOT discharge `hxint`, `hτ`, or any of `Bfac`'s other three
  summands / `fb` (the far carry) — all remain exactly as open as before. It does NOT claim r6, `nb`, or
  `hcomp` is closed: the domain `K ∩ Metric.ball x R` on which `hd` is now genuinely derived is strictly
  SMALLER than all of `K` — points of `K` outside this ball still have no `hd` discharge (and, per
  cp988–991, `hxmem`'s general discharge on all of `K` remains definitively closed off). What this file
  DOES show: for the FIRST time in this chain, BOTH of J4-1032's two residues (`hxmem` and `hd`) are
  simultaneously genuinely derived (not merely assumed / reduced-to-each-other) on one common shrunk
  domain — a further consolidation, not a closure. `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryHdFromHxmem
import QIQTH.HxmemLocalSharpReachCoverage

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open QIQTH.ExpMap QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ConcreteGateAssembly QIQTH.OnGateFieldRegularity QIQTH.HFdCoreContinuityClosed
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryHdLocalCoverageDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★★ `hd_of_local_coverage`.**  `hd` — the field-differentiability of `witnessFieldDeriv` at
    `x`, for every `z ∈ K ∩ Metric.ball x R` — is GENUINELY DERIVED (not assumed): `hxmem` is sourced
    from `HxmemLocalSharpReachCoverage.uniformFlowExp_local_coverage_ball` (J4-1042) instead of taken as
    an external hypothesis, then fed pointwise-in-`z` through `HCompNearCarryHdFromHxmem`'s reduction
    (J4-1034). The ONLY hypotheses beyond radius/metric-regularity bookkeeping (`c` satisfying both
    source lemmas' side conditions) are the standing metric data `hg`/`hgpos`/`hu`. NOT `a₁ = R/6`. -/
theorem hd_of_local_coverage
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (a b : ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (i : Fin n) (τ : ℝ) (x : Point n) :
    ∃ δ₀ > (0 : ℝ), ∃ ρ₀ > (0 : ℝ), ∃ C_L : ℝ, 0 ≤ C_L ∧
    ∀ c : ℝ, 0 < c → c < δ₀ → c ≤ ρ₀ → C_L * c < 1 →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
    ∃ R > (0 : ℝ),
    ∀ z ∈ K ∩ Metric.ball x R, DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := reachableGate_concrete g gi hC hK
  obtain ⟨ρ₀, hρ₀, C_L, hCL0, hloccov⟩ :=
    QIQTH.HxmemLocalSharpReachCoverage.uniformFlowExp_local_coverage_ball g gi hC hK
  refine ⟨δ₀, hδ₀, ρ₀, hρ₀, C_L, hCL0, ?_⟩
  intro c hc0 hcδ hcρ hCLc S hSeq
  obtain ⟨R, hR, hcov⟩ := hloccov c hc0 hcρ hCLc x
  refine ⟨R, hR, ?_⟩
  intro z hz
  obtain ⟨hzK, hzball⟩ := hz
  subst hSeq
  obtain ⟨hSopen, _hLI, hReach⟩ := hspec c hc0 hcδ z hzK
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  -- `hxmem`, restricted to `K ∩ Metric.ball x R`, is DERIVED (not assumed) from J4-1042's local
  -- coverage fact — this is the ONLY change against `hd_of_hxmem_concreteGate`'s own proof body.
  have hxSz' : x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c :=
    hcov z hzK hzball
  have hxSz : x ∈ S z := by rw [hSdef]; exact hxSz'
  obtain ⟨_hReachx, hWC2⟩ := hReach x hxSz'
  have hCD2 : ContDiffAt ℝ 2
      (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) x :=
    gatedWitness_contDiffAt_field g gi hC hK S a b τ z x hzK hxSz hSopen hWC2 hg hgpos hu
  have hC1 : ContDiffAt ℝ 1
      (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y) x :=
    pd_contDiffAt_one_of_two (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x hCD2
  have hDiff : DifferentiableAt ℝ
      (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i y) x :=
    hC1.differentiableAt (by norm_num)
  simpa [witnessFieldDeriv] using hDiff

end QIQTH.HCompNearCarryHdLocalCoverageDischarge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryHdLocalCoverageDischarge
#print axioms hd_of_local_coverage
end AxiomChecks
