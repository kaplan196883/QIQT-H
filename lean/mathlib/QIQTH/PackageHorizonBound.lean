/-
QIQTH/PackageHorizonBound.lean

  Phase 1 of the capstone-signature redesign plan
  (`docs/qg_roadmap/CAPSTONE_SIGNATURE_REDESIGN_PLAN.md`, J4-1168, Sol's 38th consult), per the phase
  table's Phase 1 line: "`package_bound_on_horizon` + kernel-identity bridge + `hK0`/`hS0` discharge
  decision → D0/D1 green".

  Contents:
    • `package_bound_on_horizon` — the elementary bridging lemma flagged as item (1) of (a)(iii): given
      a `∀ t' τ p q, 0 < τ → τ ≤ t' → |heatOp g gi H τ p q| ≤ (C * (1 + t')) * baseKernelW …` bound
      (EXACTLY the shape `GateOpennessExport.gatedWitnessN1_package_open`'s `hbound` field has), specialize
      the outer `t'` to a caller-fixed horizon `t`.  Purely `hbound t`  —  Canary D1 (HorizonBound).
    • `vanVleckGatedWitness_eq_gatedKernel` — the kernel-identity bridge, item (4) of (a)(iii): a NAMED,
      reusable version of Canary D0 (SameKernel), which Phase 0 (J4-1169) verified only via a throwaway
      check file.  Still a literal `rfl` (`vanVleckGatedWitness`'s own `def` body,
      `ConvApproximants.lean:161-166`, unfolds to exactly the package's kernel,
      `GateOpennessExport.lean:387-393`) — reconfirms D0 here as banked content.
    • `gatedWitnessN1_horizon_bound` — a non-vacuous demonstration composing the two bridges directly on
      top of `GateOpennessExport.gatedWitnessN1_package_open`: opens the package's existential ONCE and
      re-exposes its `(0,t]`-local bound (at the CALLER's fixed horizon `t`) stated at
      `vanVleckGatedWitness` (not the raw `gatedKernel …` unfold), together with the unchanged
      `hmemS0`/`hopenS0` gate-membership/openness exports.  This is exactly the shape a future
      `a1_R6_assembled_v3` (Layer C, NOT built here — Phase 5) will need to derive its local `hEbound_t`
      slot; localizing the `_of_banked` consumers (Canaries D3/D4) remains Phase 2 and is NOT attempted
      in this file.

  The `hK0`/`hS0` discharge decision itself was already resolved in Phase 0 (J4-1169, bonus finding):
  `hS0` discharges via `hmemS0 hK0`; `K`/`hK`/`hK0` remain genuine external inputs (the package never
  produces `K`).  No new lemma is needed for that half of the Phase-1 line item — it is re-used verbatim
  by `gatedWitnessN1_horizon_bound`'s conclusion, which keeps `hmemS0`/`hopenS0` (NOT a discharged `hS0`)
  so callers retain the choice of applying `hK0` themselves, matching `a1_R6_assembled_v2'`'s own binder
  shape (`hS0` is a caller obligation there, discharged at the call site via `hmemS0 hK0`).

  `a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  This
  file is pure plumbing: it does not touch the Levi/Duhamel interface, the `_of_banked` consumers, or any
  of the ~50 independent hypotheses `a1_R6_assembled_v2'` demands.
-/
import Mathlib
import QIQTH.GateOpennessExport
import QIQTH.ConvApproximants

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound QIQTH.GateOpennessExport
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.PackageHorizonBound

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### D1 — `package_bound_on_horizon`: elementary horizon instantiation. -/

/-- **★ J4-1170 (Phase 1, D1) — `package_bound_on_horizon`.**  Given an affine-in-ceiling,
    `(0,t']`-local-for-every-`t'` bound (the exact shape of
    `GateOpennessExport.gatedWitnessN1_package_open`'s `hbound` field), specialize the outer horizon
    quantifier to a caller-fixed `t`.  Purely `hPkgBound t` — no analytic content, Canary D1
    (HorizonBound). -/
theorem package_bound_on_horizon (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (C t : ℝ)
    (hPkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
      |heatOp g gi H τ p q| ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi H τ p q| ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  fun τ p q hτ hτt => hPkgBound t τ p q hτ hτt

/-! ### D0 — `vanVleckGatedWitness_eq_gatedKernel`: named kernel-identity bridge (reconfirms Phase 0). -/

/-- **★ J4-1170 (Phase 1, D0 reconfirmed) — `vanVleckGatedWitness_eq_gatedKernel`.**  The kernel-identity
    bridge, item (4) of the plan's (a)(iii) list, as a NAMED reusable lemma (Phase 0 / J4-1169 verified
    this only inside a throwaway check file).  `vanVleckGatedWitness`'s own `def` body IS this expression
    (`ConvApproximants.lean:161-166`), and it is literally the kernel
    `GateOpennessExport.gatedWitnessN1_package_open` builds internally
    (`GateOpennessExport.lean:387-393`).  Literal `rfl`, no transport. -/
theorem vanVleckGatedWitness_eq_gatedKernel (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) :
    vanVleckGatedWitness g gi hChr hK S a b
      = gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hChr hK)) :=
  rfl

/-! ### Composition — a non-vacuous demonstration on top of `gatedWitnessN1_package_open`. -/

/-- **★★ J4-1170 (Phase 1 capstone of this dispatch) — `gatedWitnessN1_horizon_bound`.**  Opens
    `gatedWitnessN1_package_open`'s existential EXACTLY ONCE (Canary D6-style single-opening discipline,
    even though D6 itself is a later-phase canary) and re-exposes, at a CALLER-fixed horizon `t`, the
    `(0,t]`-local bound stated at `vanVleckGatedWitness` (via the D0 kernel-identity bridge, applied by
    defeq — no explicit `rw` needed) together with the unchanged gate-membership/openness exports.  This
    is the exact shape a future `a1_R6_assembled_v3` (Layer C, Phase 5, NOT built here) will consume to
    derive its local `hEbound_t` slot.  Localizing `endpointData_of_banked`/`interchangeData_of_banked`
    (Canaries D3/D4) is explicitly OUT OF SCOPE for this file — Phase 2. -/
theorem gatedWitnessN1_horizon_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (t : ℝ) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      (∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ ((0 : Point n) ∈ K → (0 : Point n) ∈ S 0)
      ∧ ((0 : Point n) ∈ K → IsOpen (S 0)) := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩ :=
    gatedWitnessN1_package_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  exact ⟨a, b, C, ha, hab, hC0, S,
    package_bound_on_horizon g gi (vanVleckGatedWitness g gi hChr hK S a b) C t hbound,
    hmemS0, hopenS0⟩

end QIQTH.PackageHorizonBound

section AxiomChecks
open QIQTH.PackageHorizonBound
#print axioms package_bound_on_horizon
#print axioms vanVleckGatedWitness_eq_gatedKernel
#print axioms gatedWitnessN1_horizon_bound
end AxiomChecks
