/-
  UniformFlowHexadecupleField — Plan v7 Task M (C⁴ climb, brick 1): the HEXADECUPLED (16-fold) field
  regularity supply — one `genericDoubled` doubling up from `UniformFlowOctupleField`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  NOT `a₁ = R/6`.  One infrastructure brick of the Plan-v7 climb to the FIFTH
  velocity-jet of `uniformFlowExp` (⟹ `D⁴φ` continuity ⟹ `C⁴`), re-deriving regularity DIRECTLY on the
  uniform tube with NO `expRho`.

  The uniform-tube variational tower climbs one velocity-derivative order per `genericDoubled` doubling:
      `geodesicField` → D¹,  `doubledField` → D²,  `quadrupledField` → D³,  `octupledField` → D⁴ (banked).
  The FIFTH jet (⟹ C⁴) needs the HEXADECUPLED field on the 16-fold phase space, with its `C^∞` +
  `‖DΦ‖`/`‖D²Φ‖`-bounded-on-compact regularity supply.

  ── THE `def`-TYPING FIX (Task L applied at the field level).  `genericDoubled Φ` for `Φ : E → E` bakes
  the space `E` in from `Φ`'s type: with the banked octupled field `genericDoubled (genericDoubled
  (doubledField g gi))` (raw `St8 → St8`, `St8` a REDUCIBLE 16-leaf tree), the outer doubling lands on the
  raw `St8 × St8` = 32-leaf tree, and `‖fderiv ℝ (…)‖` re-triggers the elaboration wall (instance search
  on the fully-unfolded 32-leaf `NormedAddCommGroup`, provably infeasible even at 8M heartbeats).  Fix:
  re-type the octupled field as `octField8' : St8' n → St8' n` (`St8'` the OPAQUE `def` with registered
  instances, `NestedPhaseSpaceDef`), so `genericDoubled (octField8' g gi) : St8' × St8' → St8' × St8'`
  bottoms out at ONE `Prod` level over the registered `St8'` — `St8' × St8' = St16'` — and every
  `‖fderiv‖` synthesizes at the default budget.  `octField8'` is DEFINITIONALLY EQUAL to the banked raw
  octupled field, so `contDiff_octupledField` transports with `rfl`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms, NO `expRho`).
    • `octField8'` — the octupled field re-typed `St8' → St8'` (defeq to the banked raw field).
    • `contDiff_hexField'` / `hexField_fderiv_bddOn_compact` / `hexField_fderiv2_bddOn_compact` — the
        16-fold field `genericDoubled (octField8' g gi)`'s `C^∞` + compact operator bounds, stated over
        `St16'`, synthesizing cheaply (delegations to the field-agnostic `genericDoubled_*` engine).

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import QIQTH.NestedPhaseSpaceDef
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped Topology

set_option maxHeartbeats 1000000

section HexadecupleField

variable {n : ℕ}

/-- **The octupled field, re-typed `St8' → St8'`.**  Definitionally the banked raw octupled field
    `genericDoubled (genericDoubled (doubledField g gi))`; the `St8'` typing makes the OUTER doubling
    (below) land on the shallow registered `St8' × St8'` product. -/
noncomputable def octField8' (g gi : Point n → Fin n → Fin n → ℝ) : St8' n → St8' n :=
  genericDoubled (genericDoubled (doubledField g gi))

/-- `octField8'` is `C^∞` — defeq transport of `contDiff_octupledField`. -/
theorem contDiff_octField8' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (octField8' g gi) :=
  contDiff_octupledField g gi hC

/-- **The hexadecupled field is `C^∞`.**  `genericDoubled (octField8' g gi)` on the 16-fold phase space
    `St8' × St8' = St16'` is `C^∞`, since `octField8' g gi` is.  DERIVED. -/
theorem contDiff_hexField' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (genericDoubled (octField8' g gi)) :=
  contDiff_genericDoubled (contDiff_octField8' g gi hC)

/-- **Uniform bound on `DΦ` for the hexadecupled field over a compact set.**  Stated over the `def`-based
    16-fold phase space `St16' = St8' × St8'` — the exact `IsCompact`-argument shape the Task-M supply
    consumes; the registered instances make the (now shallow) search cheap.  DERIVED. -/
theorem hexField_fderiv_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (St16' n)} (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S,
      ‖fderiv ℝ (genericDoubled (octField8' g gi)) z‖ ≤ Kb :=
  genericDoubled_fderiv_bddOn_compact (contDiff_octField8' g gi hC) hS

/-- **Uniform bound on `D²Φ` for the hexadecupled field over a compact set.**  Stated over `St16'`.
    DERIVED. -/
theorem hexField_fderiv2_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (St16' n)} (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S,
      ‖fderiv ℝ (fderiv ℝ (genericDoubled (octField8' g gi))) z‖ ≤ Kb :=
  genericDoubled_fderiv2_bddOn_compact (contDiff_octField8' g gi hC) hS

end HexadecupleField

end QIQTH.ExpMap
