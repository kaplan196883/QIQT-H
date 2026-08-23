/-
  HFdomVanVleckHEmeasDischarged — `hFdom` for the concrete `N = 1` van-Vleck gated witness, with the M1
  measurability wall (`hEmeas`) GENUINELY DISCHARGED, at the CONSTANT-RADIUS flow-ball gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHY / CORRECTIVE.  `HFdomConcreteVanVleck.hFdom_concrete_vanVleck` (J4-1106) reduced `hDConv_AT_GATE`'s
  `hFdom` census member (for the concrete `N = 1` van-Vleck witness, at the ∃-selected `a, b, S` of
  `GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated`) to EXACTLY the M1 wall `hEmeas`: an
  IMPLICATION `StronglyMeasurable (...) → ∃ C_L, ...`.  That existential's gate `S` is built through the
  `_lin`/`_of_good` chain (`CoeffU1Fix.lean`), which names its per-point flow-ball radius via
  `Classical.choose` — OPAQUE even though (per `ConstRadiusGateExport.lean`'s header analysis) the chosen
  radius is secretly always the SAME constant `c = (b + ρc) / 2`.  No supplier for `hEmeas` at that
  opaque gate is known.

  `GatedGlobalWitnessN1CapstoneHEmeasDischarged.lean` (already banked, `a05b98ec`) already discharges
  `hEmeas`'s underlying content — `HEmeasBorelAudit.tripleHEmeas` — from GEOMETRY ALONE at the EXPOSED
  constant-radius gate `S z := uniformFlowExp g gi hC hK z '' Metric.ball 0 c`
  (`ConstRadiusGateExport.constRadius_package_and_S1`, J4-316), modulo a single honest real-number
  antecedent `c < δ₀` (two independently-constructed positive reals — not provably comparable in
  general, so carried, never assumed).  That file uses the discharged `hEmeas` INTERNALLY (assembling
  `hInt` via `iterConvIntegrableW_of_locally_bound_baseMeas`) but buries it inside a much larger
  multi-hundred-line capstone that also threads `hDuhamel`/`hDConv`/`hCConv`, and never exposes the
  resulting Levi-series domination in `hFdom`'s own literal binder shape.

  THIS FILE extracts EXACTLY that: replaying the SAME `constRadius_package_and_S1` → `hEzero` →
  `iterConvIntegrableW_of_locally_bound_baseMeas` → `leviSeries_dominatedW_le` chain, at the SAME
  constant-radius gate, but stopping at the `hFdom`-shaped conclusion (`gaussDdim`, not `baseKernelW`,
  via `baseKernelW_zero_apply`) — with `hEmeas` DiSCHARGED INTERNALLY, so the result is an UNCONDITIONAL
  existential (no `StronglyMeasurable (...) → ...` antecedent at all), modulo ONLY the same honest
  `c < δ₀` real-number carry and the standard geometric/gauge/measurability inputs
  `constRadius_package_and_S1` already needs (`hgiC, hgpos, hu, hgiMeas, hchr` beyond the landed
  capstone's base hypothesis list).

  No new rate/asymptotic/convergence claim is introduced (pure logical re-assembly of already-proven
  facts, replaying an already-banked route to a new literal target shape), so no fresh sympy check is
  needed per the standing rule's scope.

  ⚠ HONEST SCOPE.  This discharges `hFdom` (for the concrete `N = 1` van-Vleck witness, AT THE
  CONSTANT-RADIUS gate `S z := uniformFlowExp g gi hC hK z '' Metric.ball 0 c`, NOT the opaque `.choose`
  gate `HFdomConcreteVanVleck` targeted) modulo ONLY `{standard geometric/gauge hyps, c < δ₀}` — `hEmeas`
  is NO LONGER a separate open item for THIS gate.  It does NOT touch ANY of `hDConv_AT_GATE`'s other
  ~25 census hypotheses (`hEdom`, `hAdom`, `hLapFull`, `hII_lo/hi`, `hFII` family, `hQ1`, `hFmeas`,
  `hbound`/`hdiff` families, etc.) — those remain fully separately open, and NONE of them has yet been
  checked to also transfer cleanly to this constant-radius gate (the census's OTHER members were built
  against the opaque-gate `vanVleckGatedWitness g gi hC hK S a b` for an ARBITRARY `S`, so they are
  gate-agnostic in their STATEMENT, but whether they are actually PROVABLE at this specific constant `S`
  is a separate question, not addressed here).  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConstRadiusGateExport
import QIQTH.GatedGlobalWitnessN1Diag
import QIQTH.GatedWitnessPackage
import QIQTH.GatedWitnessMeas
import QIQTH.ConvApproximants
import QIQTH.ParametrixHEboundWiring

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatResidualBound QIQTH.ConstRadiusGateExport
open scoped BigOperators ContDiff Topology

namespace QIQTH.HFdomVanVleckHEmeasDischarged

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★★★ `hFdom` for the concrete `N = 1` van-Vleck witness at the constant-radius gate, WITH `hEmeas`
    DISCHARGED.**  From the SAME geometric/gauge/all-`k`-smoothness inputs as
    `ConstRadiusGateExport.constRadius_package_and_S1` (the base capstone hypotheses PLUS the four extra
    measurability/positivity inputs `hgiC, hgpos, hu, hgiMeas, hchr` that gate's `hEmeas` discharge
    needs) and a fixed ceiling `T > 0`, there are cutoff radii `a < b`, a constant `C ≥ 0`, a constant
    radius `c` with `b < c`, and a reach `δ₀ > 0`, such that — GIVEN ONLY the honest real-number
    smallness `c < δ₀` (NOT `hEmeas`, which is discharged internally) — the concrete gated van-Vleck
    witness `vanVleckGatedWitness g gi hC hK S a b` (`S z := uniformFlowExp g gi hC hK z '' ball 0 c`)
    has its Levi series Gaussian-dominated on `(0, T]`: `hDConv_AT_GATE`'s `hFdom` antecedent, literally,
    UNCONDITIONALLY on `hEmeas`. -/
theorem hFdom_vanVleck_hEmeas_discharged (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    (T : ℝ) (hT : 0 < T) :
    ∃ a b C c δ₀ : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧ 0 < δ₀ ∧
      (c < δ₀ → ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y)) := by
  obtain ⟨a, b, C, c, δ₀, ha, hab, hC0, hbc, hδ₀pos, hbound, hmemS0, hopenS0, hS1⟩ :=
    constRadius_package_and_S1 hn g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchr
  refine ⟨a, b, C, c, δ₀, ha, hab, hC0, hbc, hδ₀pos, ?_⟩
  intro hcδ
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  -- `hEmeas` — DISCHARGED from geometry alone at this concrete constant-radius gate.
  have hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) w.1 w.2.1 w.2.2) := hS1 hcδ
  have hn' : 1 ≤ n := hn
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q = 0 :=
    gatedGlobalWitnessN1_residual_hEzero g gi hn' K S (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK)
  have hlocal : ∀ T' : ℝ, 0 < T' → ∃ CT : ℝ, 0 ≤ CT ∧
      ∀ τ p q, 0 < τ → τ ≤ T' →
        |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q|
          ≤ CT * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
    fun T' hT' => ⟨C * (1 + T'), mul_nonneg hC0 (by linarith),
      fun τ p q hτ hτT' => hbound T' τ p q hτ hτT'⟩
  have hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))
      (2 : ℝ) (0 : ℝ) (C * (1 + T)) :=
    iterConvIntegrableW_of_locally_bound_baseMeas _ (C * (1 + T)) hEzero hEmeas hlocal
  obtain ⟨C_L, hC_L0, hCL⟩ :=
    leviSeries_dominatedW_le (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))
      (C * (1 + T)) T (mul_nonneg hC0 (by linarith)) hT
      (fun τ p q hτ hτT => hbound T τ p q hτ hτT) hInt
  refine ⟨C_L, hC_L0, fun s hs hsT z y => ?_⟩
  have h := hCL s z y hs hsT
  rwa [baseKernelW_zero_apply] at h

end QIQTH.HFdomVanVleckHEmeasDischarged

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HFdomVanVleckHEmeasDischarged
#print axioms hFdom_vanVleck_hEmeas_discharged
end AxiomChecks
