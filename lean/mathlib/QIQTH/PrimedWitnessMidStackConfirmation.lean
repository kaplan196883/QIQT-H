/-
  PrimedWitnessMidStackConfirmation — J4-1182 (Witness-unification Phase 2, D5/D6): CONFIRMATION
  ONLY, no new mathematical content.

  Direct-verification dispatch per `docs/qg_roadmap/WITNESS_UNIFICATION_PLAN.md` Phase 2 ("D5 — one
  real application of `TruncatedDuhamelCore`/`EndpointData`/`InterchangeData` at
  `Wit := vanVleckGatedWitness' ...`" / "D6 — `Mem*` reuse confirmation... `H := heatOp g gi
  (vanVleckGatedWitness' ...)`, `F := leviSeries (heatOp g gi (vanVleckGatedWitness' ...))`").

  The J4-1176 pre-check table already argued (by direct grep of the field lists) that
  `TruncatedDuhamelCore`/`EndpointData`/`InterchangeData` (`TruncatedDuhamelData.lean`) and the five
  `Mem*` abbrevs (`DaLimLUWallRecon.lean`) are fully generic over an ABSTRACT witness kernel `Wit`/
  `H F`, with zero chart/witness-specific tokens in their own field types. This dispatch does not just
  re-read that table — it produces an actual COMPILING instantiation of all eight symbols at the
  concrete primed witness `Wit := vanVleckGatedWitness' g gi hC hK S a b c` (J4-1156), confirming the
  pre-check's expectation with real elaboration rather than a second manual re-read.

  Method: `#check`-only skeleton (Phase-0/D1 style) — for each of the 8 symbols, an application whose
  every witness/kernel argument is literally `vanVleckGatedWitness' g gi hC hK S a b c` (or
  `heatOp g gi (vanVleckGatedWitness' ...)` / `leviSeries (heatOp g gi (vanVleckGatedWitness' ...))`
  for the `Mem*` family, per the plan's own D6 prescription), elaborated by Lean's kernel. Since all
  eight symbols are `Prop`-valued (structures/abbrevs) parameterized abstractly in `Wit`/`H F`, no
  proof obligation is discharged here — the point is PURELY that instantiation at the primed witness
  type-checks with no forking, no new field, no hidden non-generic dependency. This is the intended,
  literal reading of the plan's own Phase-0 D1 "signature skeleton" methodology, reused at Phase 2.

  RESULT: all 8 instantiations elaborate. **Canary C2 (Phase 2) CLOSED, zero new forks needed at this
  layer** — confirms the J4-1176 pre-check exactly. NOT `a₁ = R/6`. Not itself a proof of anything
  beyond "these types accept the primed witness with no changes."
-/
import QIQTH.TruncatedDuhamelData
import QIQTH.DaLimLUWallRecon
import QIQTH.VanVleckGatedWitnessWith

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound QIQTH.LaplaceBeltrami
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open scoped BigOperators Topology

namespace QIQTH.PrimedWitnessMidStackConfirmation

variable {n : ℕ}

/-! ###############################################################################
    ### D5 — `TruncatedDuhamelCore` / `EndpointData` / `InterchangeData` at the primed witness.
    ############################################################################### -/

--  **D5a.** `TruncatedDuhamelCore` instantiates cleanly at `Wit := vanVleckGatedWitness' ...`. 
#check fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => QIQTH.Curvature.christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c t : ℝ) =>
  (TruncatedDuhamelCore g gi (vanVleckGatedWitness' g gi hC hK S a b c) t : Prop)

--  **D5b.** `EndpointData` instantiates cleanly at `Wit := vanVleckGatedWitness' ...`. 
#check fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => QIQTH.Curvature.christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c t C : ℝ) =>
  (EndpointData g gi (vanVleckGatedWitness' g gi hC hK S a b c) t C : Prop)

--  **D5c.** `InterchangeData` instantiates cleanly at `Wit := vanVleckGatedWitness' ...`. 
#check fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => QIQTH.Curvature.christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c t : ℝ) =>
  (InterchangeData g gi (vanVleckGatedWitness' g gi hC hK S a b c) t : Prop)

--  **D5d (bonus).** `BulkLimitData` (the fourth Phase-2-adjacent bundle, also fully generic in `Wit`
--     per the same pre-check row) instantiates cleanly too. 
#check fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => QIQTH.Curvature.christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c t : ℝ) =>
  (BulkLimitData g gi (vanVleckGatedWitness' g gi hC hK S a b c) t : Prop)

/-! ###############################################################################
    ### D6 — the five `Mem*` abbrevs at `H := heatOp g gi (vanVleckGatedWitness' ...)`,
    ### `F := leviSeries (heatOp g gi (vanVleckGatedWitness' ...))`.
    ############################################################################### -/

--  **D6a.** `MemInterchange` instantiates cleanly at the primed `H`/`F`. 
#check fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => QIQTH.Curvature.christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c : ℝ)
    (U : Set ℝ) (pdpdH : Fin n → ℝ → Point n → ℝ) =>
  (MemInterchange
      (heatOp g gi (vanVleckGatedWitness' g gi hC hK S a b c))
      (leviSeries (heatOp g gi (vanVleckGatedWitness' g gi hC hK S a b c))) U pdpdH : Prop)

--  **D6b.** `MemLapFull` instantiates cleanly at the primed `H`/`F`. 
#check fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => QIQTH.Curvature.christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c : ℝ)
    (U : Set ℝ) (pdpdH : Fin n → ℝ → Point n → ℝ) =>
  (MemLapFull g gi
      (heatOp g gi (vanVleckGatedWitness' g gi hC hK S a b c))
      (leviSeries (heatOp g gi (vanVleckGatedWitness' g gi hC hK S a b c))) U pdpdH : Prop)

--  **D6c.** `MemAdjLo` instantiates cleanly at the primed `F`. 
#check fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => QIQTH.Curvature.christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c : ℝ)
    (U : Set ℝ) (pdpdH : Fin n → ℝ → Point n → ℝ) =>
  (MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness' g gi hC hK S a b c))) U pdpdH : Prop)

--  **D6d.** `MemAdjHi` instantiates cleanly at the primed `F`. 
#check fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => QIQTH.Curvature.christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c : ℝ)
    (U : Set ℝ) (pdpdH : Fin n → ℝ → Point n → ℝ) =>
  (MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness' g gi hC hK S a b c))) U pdpdH : Prop)

--  **D6e.** `MemECombine` instantiates cleanly at the primed `H`/`F`. 
#check fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => QIQTH.Curvature.christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b c : ℝ) =>
  (MemECombine g gi
      (heatOp g gi (vanVleckGatedWitness' g gi hC hK S a b c))
      (leviSeries (heatOp g gi (vanVleckGatedWitness' g gi hC hK S a b c))) : Prop)

end QIQTH.PrimedWitnessMidStackConfirmation
