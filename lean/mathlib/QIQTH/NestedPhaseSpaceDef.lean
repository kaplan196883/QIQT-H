/-
  NestedPhaseSpaceDef — Plan v7 Task L: a `def`-based (non-reducible) parallel type family for the
  nested phase spaces of the geodesic-flow variational tower, fixing the elaboration-performance wall
  that blocked the C⁴ (hexadecuple / 16-fold) climb.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  NOT `a₁ = R/6`.  Pure infrastructure: a type family + typeclass instances +
  a defeq/CLM bridge to the existing `abbrev`-based family.  NO new mathematics, NO `expRho`.

  ── THE WALL.  The banked nested phase spaces `St2/St4/St8` (`UniformFlowOctupleSupply.lean:62-64`)
  are declared as `abbrev` (`@[reducible] def`).  Reducible ⟹ typeclass instance search and `whnf`
  fully UNFOLD each one to its raw nested-`Prod` tree on every use (`St8` is secretly a 16-leaf,
  depth-4 binary product of `Point n`; the next level `St16` is a 32-leaf, depth-5 tree).  Instance
  synthesis (`NormedAddCommGroup`, `NormedSpace ℝ`, `ProperSpace`, …) re-derives across the FULL
  expanded tree every time, with cost blowing up per doubling level.

  ── EMPIRICAL EVIDENCE (measured this session, `#synth`, isolated files).
    • `NormedAddCommGroup (St16 n)` with the ABBREV scheme: FAILS TO SYNTHESIZE even at
      `synthInstance.maxHeartbeats 8000000` (8M — the search never terminates within budget).
    • `NormedAddCommGroup (St16' n)` with the DEF scheme below: SUCCEEDS at the DEFAULT
      `synthInstance.maxHeartbeats 20000` (20k).  Likewise `NormedSpace ℝ`, `ProperSpace` at St8'/St16'
      all succeed at 20k.  A ≥400× collapse — and, decisively, the def scheme SUCCEEDS where the abbrev
      scheme provably does not.

  ── THE FIX (verified sound by external Lean-expert consult; empirically confirmed here).  Declare the
  tower as `def` (NOT reducible) and register each level's instances via `inferInstanceAs`, STRICTLY
  BOTTOM-UP: `St2'` with its own registered instances first, THEN `St4'` referencing `St2'`'s registered
  instances, THEN `St8'`, THEN `St16'`.  Because `def` is opaque to instance search, each level's
  derivation touches exactly ONE `Prod` application (finding the already-registered child instance by
  its opaque head), never re-triggering the full unfold.

  ── WHAT LANDS.
    • `St2' / St4' / St8' / St16'` — the def-based phase-space tower, with `NormedAddCommGroup`,
      `NormedSpace ℝ`, `ProperSpace` registered bottom-up.
    • `St2'_eq_St2 / St4'_eq_St4 / St8'_eq_St8` — the def types are DEFINITIONALLY EQUAL (`rfl`) to the
      existing banked `abbrev` types `QIQTH.ExpMap.St2/St4/St8`, and their `NormedAddCommGroup` instances
      agree definitionally — so existing banked results transport with a thin cast, no re-proof.
    • `stEquiv8 : St8 n ≃L[ℝ] St8' n` (+ 2/4) — the identity linear isometry across the two
      representations (defeq), for ergonomic transport of `HasFDerivAt`/`fderiv`/`ContDiffOn` facts.
    • `st16'_isCompact_closedBall`, `st16'_convex_closedBall` — the exact `ProperSpace`/`NormedSpace`
      facts the Task-M 16-fold confinement construction consumes, proven non-vacuously over `St16'`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowOctupleSupply
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature
open scoped NNReal

variable {n : ℕ}

/-! ### The `def`-based phase-space tower with bottom-up registered instances.

Each level is a plain `def` (NOT `abbrev`), so it is OPAQUE to instance search: synthesizing an instance
for `St4' n × St4' n` finds `NormedAddCommGroup (St4' n)` by its opaque head (the already-registered
instance below) instead of unfolding `St4'` to its raw `Prod` tree.  This is the mechanism that
collapses the search from "32-leaf tree" to "one `Prod` level" at `St16'`. -/

/-- Level 2 (`= (Point n × Point n) × (Point n × Point n)`). -/
def St2' (n : ℕ) : Type := (Point n × Point n) × (Point n × Point n)

noncomputable instance instNACGSt2' : NormedAddCommGroup (St2' n) :=
  inferInstanceAs (NormedAddCommGroup ((Point n × Point n) × (Point n × Point n)))
noncomputable instance instNSSt2' : NormedSpace ℝ (St2' n) :=
  inferInstanceAs (NormedSpace ℝ ((Point n × Point n) × (Point n × Point n)))
instance instPSSt2' : ProperSpace (St2' n) :=
  inferInstanceAs (ProperSpace ((Point n × Point n) × (Point n × Point n)))

/-- Level 4 (`= St2' n × St2' n`).  Instances reference `St2'`'s REGISTERED instances (one `Prod` level). -/
def St4' (n : ℕ) : Type := St2' n × St2' n

noncomputable instance instNACGSt4' : NormedAddCommGroup (St4' n) :=
  inferInstanceAs (NormedAddCommGroup (St2' n × St2' n))
noncomputable instance instNSSt4' : NormedSpace ℝ (St4' n) :=
  inferInstanceAs (NormedSpace ℝ (St2' n × St2' n))
instance instPSSt4' : ProperSpace (St4' n) :=
  inferInstanceAs (ProperSpace (St2' n × St2' n))

/-- Level 8 (`= St4' n × St4' n`). -/
def St8' (n : ℕ) : Type := St4' n × St4' n

noncomputable instance instNACGSt8' : NormedAddCommGroup (St8' n) :=
  inferInstanceAs (NormedAddCommGroup (St4' n × St4' n))
noncomputable instance instNSSt8' : NormedSpace ℝ (St8' n) :=
  inferInstanceAs (NormedSpace ℝ (St4' n × St4' n))
instance instPSSt8' : ProperSpace (St8' n) :=
  inferInstanceAs (ProperSpace (St4' n × St4' n))

/-- Level 16 (`= St8' n × St8' n`) — the C⁴-climb phase space that blew the abbrev elaboration budget. -/
def St16' (n : ℕ) : Type := St8' n × St8' n

noncomputable instance instNACGSt16' : NormedAddCommGroup (St16' n) :=
  inferInstanceAs (NormedAddCommGroup (St8' n × St8' n))
noncomputable instance instNSSt16' : NormedSpace ℝ (St16' n) :=
  inferInstanceAs (NormedSpace ℝ (St8' n × St8' n))
instance instPSSt16' : ProperSpace (St16' n) :=
  inferInstanceAs (ProperSpace (St8' n × St8' n))

/-! ### Defeq bridge to the existing banked `abbrev` family.

The def and abbrev families bottom out at the same raw `Prod` tree of `Point n`, so they are
DEFINITIONALLY EQUAL and the equalities close by `rfl`.  This is what lets existing banked results
(stated over `St2/St4/St8`) be consumed where the def types are expected, and vice versa, via a thin
cast — no re-proof of the C²/C³ tower against the new representation. -/

theorem St2'_eq_St2 : St2' n = St2 n := rfl
theorem St4'_eq_St4 : St4' n = St4 n := rfl
theorem St8'_eq_St8 : St8' n = St8 n := rfl

/-- The registered `NormedAddCommGroup` instance on `St8'` agrees DEFINITIONALLY with the one the abbrev
    `St8` carries — so the two representations are not merely isomorphic but the SAME normed space, and
    `ContinuousLinearEquiv.refl` is a genuine linear ISOMETRY between them (below). -/
theorem instNACGSt8'_eq : (instNACGSt8' : NormedAddCommGroup (St8' n)) = inferInstanceAs (NormedAddCommGroup (St8 n)) := rfl

/-! ### CLM identity-equivalence bridges (for transporting derivative facts).

Since `St_k' n` and `St_k n` are defeq with defeq norm instances, `ContinuousLinearEquiv.refl` is a
linear isometry between the two representations.  Composing a banked `HasFDerivAt … (into St_k)` with the
appropriate `stEquiv` transports it to the def representation (and back), with the derivative CLM mapped
by the identity equiv — the ergonomic bridge Task M uses to feed abbrev-typed octuple-supply results
into def-typed hexadecuple constructions. -/

/-- Identity `≃L[ℝ]` from the abbrev `St2` to the def `St2'` (defeq). -/
noncomputable def stEquiv2 : St2 n ≃L[ℝ] St2' n := ContinuousLinearEquiv.refl ℝ (St2 n)
/-- Identity `≃L[ℝ]` from the abbrev `St4` to the def `St4'` (defeq). -/
noncomputable def stEquiv4 : St4 n ≃L[ℝ] St4' n := ContinuousLinearEquiv.refl ℝ (St4 n)
/-- Identity `≃L[ℝ]` from the abbrev `St8` to the def `St8'` (defeq). -/
noncomputable def stEquiv8 : St8 n ≃L[ℝ] St8' n := ContinuousLinearEquiv.refl ℝ (St8 n)

/-- Transport of a Fréchet derivative from the abbrev representation to the def representation.  For any
    map into `St8 n` that is Fréchet-differentiable at a point, the same map viewed into `St8' n` is
    Fréchet-differentiable with the identity-transported derivative.  (Since the representations are
    defeq this is definitionally trivial, but stated cleanly it is the bridge Task M invokes to reuse the
    banked octuple supply.) -/
theorem hasFDerivAt_stEquiv8 {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P → St8 n} {L : P →L[ℝ] St8 n} {x : P} (h : HasFDerivAt f L x) :
    HasFDerivAt (fun y => (stEquiv8 (f y) : St8' n))
      ((stEquiv8 : St8 n ≃L[ℝ] St8' n).toContinuousLinearMap.comp L) x :=
  (stEquiv8 : St8 n ≃L[ℝ] St8' n).toContinuousLinearMap.hasFDerivAt.comp x h

/-! ### Non-vacuous instance-usage lemmas over `St16'` (the exact facts Task M consumes).

These exercise `ProperSpace`/`NormedSpace`/`NormedAddCommGroup (St16' n)` in the concrete shapes the
16-fold confinement construction needs — `isCompact_closedBall` and `convex_closedBall` on the deepest
level — certifying the registered instances genuinely fire (not vacuous). -/

/-- The `ProperSpace (St16' n)` instance fires: every closed ball in the 16-fold phase space is compact —
    the exact `IsCompact` fact the Task-M hexadecuple confinement set is built from. -/
theorem st16'_isCompact_closedBall (c : St16' n) (r : ℝ) :
    IsCompact (Metric.closedBall c r) :=
  isCompact_closedBall c r

/-- Closed balls in `St16' n` are convex — the `Convex` half of the confinement datum. -/
theorem st16'_convex_closedBall (c : St16' n) (r : ℝ) :
    Convex ℝ (Metric.closedBall c r) :=
  convex_closedBall c r

/-- The product-confinement set of the Task-M shape (`St8'`-ball ×ˢ `St8'`-ball ⊆ `St16'`) is compact,
    built via `IsCompact.prod` on the def types — the precise compactness the 16-fold supply needs, now
    synthesizable at the default heartbeat budget. -/
theorem st16'_isCompact_prod_closedBall (c₁ c₂ : St8' n) (r₁ r₂ : ℝ) :
    IsCompact (Metric.closedBall c₁ r₁ ×ˢ Metric.closedBall c₂ r₂ : Set (St8' n × St8' n)) :=
  (isCompact_closedBall c₁ r₁).prod (isCompact_closedBall c₂ r₂)

end QIQTH.ExpMap
