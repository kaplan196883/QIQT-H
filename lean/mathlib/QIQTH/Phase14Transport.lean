/-
  Phase14Transport — J4-472: THE LIGHTWEIGHT CENSUS-INTEGRATION TRANSPORT for the diagonal `hFint`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  lands the `v2Census_phase14` integration that J4-471 (`QIQTH.HFintDiagGrounding`) DEFERRED — but
  via a LIGHTWEIGHT TRANSPORT that stays under the <5 min per-lemma elaboration ceiling, instead of
  the monolithic ~330-hypothesis double re-application (which type-checked but elaborated in
  ~50–100 min, WS ~125 GB — a hard split-rule violation).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DESIGN — why the transport lives at the `hRemainderDiag` granularity, NOT the census-`Π`.

  `HProvGrounding.v2Census_phase13` has conclusion
      `∃ a b S, 0 < a ∧ a < b ∧ (Π ~85 dependent binders, TruncatedDuhamelCore)`.
  The DESIRED `phase14` differs from `phase13` in EXACTLY ONE binder: the honest-remainder carry
  `hRemainderDiag` has its second conjunct — the diagonal `hFint` interval-integrability — DROPPED
  (now discharged internally from `HFintDiagGrounding.hFint_diag_grounded`).  The other ~84 binders
  are carried through VERBATIM.

  ⟹ THE MONOLITH TRAP.  A standalone `phase14 : … → TruncatedDuhamelCore` MUST apply the phase13
      body to all ~85 giant-typed arguments (`vanVleckGatedWitness g gi …`, `leviSeries (heatOp …)`,
      `AmplitudeDerivativeDataOn …`, …).  The dependent-binder substitution forces recursive `defeq`
      unfolding of those huge terms — THAT is the ~50–100 min / ~125 GB blow-up, and it is INTRINSIC
      to threading 85 args through the phase13 body.  No `Structure`-pack or `Exists.imp` rephrasing
      removes it: the application is the cost.

  ⟹ THE LIGHTWEIGHT ROUTE (option (a), at the correct granularity).  The ENTIRE mathematical content
      of the phase14 integration is the transformation of the `hRemainderDiag` tuple itself: insert
      `hFint_diag_grounded` as the second conjunct.  That transport touches ONLY the `hRemainderDiag`-
      shaped `∃`/`∧` (a handful of conjuncts referencing `vanVleckGatedWitness`/`leviSeries`), NEVER
      the 85-binder census `Π`.  It elaborates in seconds.  This file LANDS it as
      `hRemainderDiag_reconstruct`.

  ⟹ WHY THE FULL `Core`-producing `phase14` IS NOT NEEDED AS A STANDALONE.  The reduction tower
      (phase1…phase13) is an AUDIT/census surface, NOT the critical path: the `a₁` capstone
      `A1R6FromData.a1_R6_from_data` consumes the bundled `A1R6GateSlots` package (the Duhamel /
      W1-free / L2 censuses), applying the census body EXACTLY ONCE at assembly.  The `hFint` supply
      is therefore best INLINED at that single point of use via `hRemainderDiag_reconstruct`, not
      pre-composed into a monolithic `phase14` that would pay the 85-arg blow-up for no downstream
      consumer.  See THE TRANSPORT LEDGER below.

  ── WHAT LANDS (ns `QIQTH.Phase14Transport`).
    • `hRemainderDiag_reconstruct` — ★★ THE lightweight transport: from the four diagonal `hFint`
        suppliers {`hFzero`, `hWitDomEvery`, `hFdomEvery`, `hFintMeas`} (+ `hUpos`) and a REDUCED
        remainder `hRemainderDiag'` (phase14-shape, `hFint` conjunct absent), rebuild the FULL
        phase13-shape `hRemainderDiag` by splicing in `hFint_diag_grounded`.  This is the exact
        census-integration content of `v2Census_phase14`, isolated from the monolithic `Π`.

  NO `sorry`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HFintDiagGrounding

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.LeviSeriesLocalData
open QIQTH.LaplaceBeltrami
open QIQTH.HProvGrounding QIQTH.HFintDiagGrounding
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.Phase14Transport

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★ `hRemainderDiag_reconstruct` — the lightweight `hFint` census-integration transport.
    ############################################################################### -/

/-- **★★ `hRemainderDiag_reconstruct` — THE LIGHTWEIGHT `hFint` CENSUS-INTEGRATION TRANSPORT.**
    The entire mathematical content of `v2Census_phase14`, isolated from the 85-binder census `Π`.
    Given:
      • `hUpos`, and the four diagonal `hFint` suppliers `hFzero` / `hWitDomEvery` / `hFdomEvery` /
        `hFintMeas` (exactly the inputs of `HFintDiagGrounding.hFint_diag_grounded`), and
      • the REDUCED remainder `hRemainderDiag'` — the phase13 `hRemainderDiag` with its SECOND
        conjunct (the diagonal `hFint` interval-integrability) ABSENT,
    reconstruct the FULL phase13-shape `hRemainderDiag` by splicing `hFint_diag_grounded` in as the
    second conjunct.  Every other conjunct (`snbx`, the dominator `bound`+`hbdd`+`hbound`, and the
    `z`-level reduced core) is carried through VERBATIM.  Because this touches ONLY the
    `hRemainderDiag`-shaped `∃`/`∧`, it elaborates in seconds — the split-rule-safe replacement for
    the monolithic phase14 double re-application.  ⚠ NOT `a₁ = R/6`. -/
theorem hRemainderDiag_reconstruct
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (nbP : ℝ → Set (Point n)) (hUpos : ∀ u ∈ U, 0 < u)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWitDomEvery : ∀ (x : Point n) (Tc : ℝ), ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ Tc → ∀ z : Point n,
          |vanVleckGatedWitness g gi hC hK S a b τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hFintMeas : ∀ u ∈ U, ∀ x ∈ nbP u, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 u)))
    (hRemainderDiag' : ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
        ∃ (snbx : Set ℝ) (bound : ℝ → ℝ),
          snbx ∈ 𝓝 (x i) ∧
          IntervalIntegrable bound volume 0 u ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
            ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
            ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
              znb ∈ 𝓝 w ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume) ∧
              Integrable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              Integrable bnd volume ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                ‖witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bnd z) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i (Function.update x i w')))) :
    ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
        ∃ (snbx : Set ℝ) (bound : ℝ → ℝ),
          snbx ∈ 𝓝 (x i) ∧
          IntervalIntegrable
            (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
          IntervalIntegrable bound volume 0 u ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
            ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
            ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
              znb ∈ 𝓝 w ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume) ∧
              Integrable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              Integrable bnd volume ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                ‖witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bnd z) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i (Function.update x i w'))) := by
  -- ★ the diagonal `hFint` leg, discharged once for all `(u, x)` via the zeroth-order route.
  have hFintLeg := hFint_diag_grounded g gi hC hK S a b U nbP hUpos
    hFzero hWitDomEvery hFdomEvery hFintMeas
  intro u hu x hx i
  obtain ⟨snbx, bound, hsnbx, hbdd, hbound, hRedCore⟩ := hRemainderDiag' u hu x hx i
  exact ⟨snbx, bound, hsnbx, hFintLeg u hu x hx, hbdd, hbound, hRedCore⟩

end QIQTH.Phase14Transport

/-! ## THE TRANSPORT LEDGER — `v2Census_phase14` landed as a lightweight `hRemainderDiag` transport.

  J4-471 (`HFintDiagGrounding`) discharged the diagonal `hFint` leg (`hFint_diag_grounded`) but had to
  REMOVE the census-integration `v2Census_phase14`: its monolithic proof re-applied `v2Census_phase13`'s
  ~85-binder body (`~330` explicit/implicit args across the double application), which type-checked but
  elaborated in ~50–100 min at ~125 GB WS — a hard <5 min split-rule violation.  This brick lands the
  SAME integration content under the ceiling by relocating the transport to the correct granularity.

  ── THE ANATOMY OF THE COST (why the monolith is intrinsic, not incidental).
    `phase14` ≟ `phase13`, differing in EXACTLY ONE of ~85 binders: `hRemainderDiag`'s second conjunct
    (the diagonal `hFint`) is dropped and supplied internally.  A standalone `phase14 : … → Core` must
    apply the phase13 body to all ~85 giant-typed args; the DEPENDENT-binder substitution recursively
    `defeq`-unfolds `vanVleckGatedWitness g gi …`, `leviSeries (heatOp …)`, `AmplitudeDerivativeDataOn …`,
    …  — the blow-up is the APPLICATION, not the statement.  No `Structure`-pack / `Exists.imp`
    rephrasing removes it: any route to the full `Core`-producing `phase14` pays it once.

  ── WHAT THIS BRICK LANDS (`hRemainderDiag_reconstruct`, ns `QIQTH.Phase14Transport`).
    The ENTIRE census-integration content of `v2Census_phase14` is the `hRemainderDiag` transport:
    splice `hFint_diag_grounded` into the tuple as the 2nd conjunct.  Isolated from the 85-binder `Π`,
    it touches only the `hRemainderDiag`-shaped `∃`/`∧` and elaborates in seconds.

      role                                                  status
      ───────────────────────────────────────────────────  ─────────────────────────────────────────
      the `hFint` census-integration (splice into tuple)    ★★ LANDED — `hRemainderDiag_reconstruct`
      the four `hFint` suppliers                            INPUT — {hFzero, hWitDomEvery, hFdomEvery,
                                                                     hFintMeas} (= `hFint_diag_grounded`)
      the ~84 verbatim census binders + the 85-arg body     DEFERRED (content-free) — see below

  ── THE DEFERRED PART IS CONTENT-FREE AND OFF THE CRITICAL PATH.
    What remains of a full `Core`-producing `phase14` — feeding the reconstructed `hRemainderDiag` (and
    the ~84 verbatim binders) through `v2Census_phase13`'s body — is a MECHANICAL, mathematically empty
    85-arg application (its correctness was already witnessed: the J4-471 monolith type-checked).  It is
    NOT needed as a standalone: the reduction tower phase1…phase13 is an AUDIT/census surface, while the
    `a₁` capstone `A1R6FromData.a1_R6_from_data` consumes the bundled `A1R6GateSlots` package and applies
    the census body EXACTLY ONCE at assembly.  The `hFint` supply is therefore best INLINED there via
    `hRemainderDiag_reconstruct`, paying the single application the capstone pays anyway — rather than
    pre-composing a monolithic `phase14` that costs ~50–100 min for zero downstream consumer.

  ── PHASE14 STATUS.  LANDED as `hRemainderDiag_reconstruct` (the lightweight transport = the census-
    integration content).  The monolithic `Core`-producing `v2Census_phase14` stays DEFERRED as a
    content-free, off-critical-path mechanical composition (splice-then-apply), to be inlined at the
    single `A1R6GateSlots` assembly if ever wired — NOT re-attempted as a standalone monolith.
  ⚠  NOT `a₁ = R/6`; CONDITIONAL on the full diagonal-remainder surface + the convergence trio +
     the geometric stack.
-/

section AxiomChecks
open QIQTH.Phase14Transport
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms hRemainderDiag_reconstruct
end AxiomChecks
