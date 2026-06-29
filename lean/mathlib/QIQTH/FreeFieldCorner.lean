/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# FREE-FIELD CORNER — unified corner transport for the free Standard-Model field content (Track A)

This module **unifies** the electron's CAR transport (D4, `encoded_anticomm`) and the photon's
truncated-CCR transport (D5, `encoded_truncated_ladder_commutator`) under one generic statement: any
**graded bracket** relation on the field code — `[x,y]_ε := x y + ε·(y x)` (ε = +1 the anticommutator /
CAR, ε = −1 the commutator / CCR) — is carried faithfully into the capacity-bounded **corner**
`P·End(𝓗_R)·P`, `P = VVᴴ`, by the encoding `ι_V`.  Every free SM field type (quark/lepton CAR,
W/Z/gluon and Higgs truncated-bosonic) is then an *instance* of this one transport.

**Honest scope (enforced).** FREE-FIELD content only: this *transports a supplied finite field algebra*
into the corner — it does NOT construct the field, and capacity is a CONSTRAINT, not a generator.
Interactions, non-abelian gauge dynamics, the Yang–Mills mass gap, confinement, chirality, and
spontaneous symmetry breaking are **cited frontiers** (open mathematics), out of scope.  The bosonic
fields are necessarily **truncated** in finite capacity (the defect is explicit, D5).  The corner unit is
`P`, never the ambient `1_𝓗`.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  See
`FIELDS_AND_SPACETIME_PLAN.md`.
-/
import QIQTH.CornerConstruction

namespace QIQTH.FreeFieldCorner

open Matrix QIQTH.CornerConstruction

section GradedBracket

variable {dC d𝓗 : Type*} [Fintype dC] [DecidableEq dC] [Fintype d𝓗] [DecidableEq d𝓗]

/-- The **graded bracket** `[x,y]_ε = x·y + ε·(y·x)` on the field code.  `ε = 1` is the **anticommutator**
`{x,y}` (CAR / fermions); `ε = -1` is the **commutator** `[x,y]` (CCR / bosons).  The single algebraic
object whose corner transport unifies the electron (D4) and the photon (D5). -/
noncomputable def gradedBracket (ε : ℂ) (x y : Matrix dC dC ℂ) : Matrix dC dC ℂ :=
  x * y + ε • (y * x)

/-- **★★ A1 — the graded bracket transports into the corner.**  The encoding `ι_V` carries the code
graded bracket to the corner graded bracket of the encoded operators:

  `[ι_V(x), ι_V(y)]_ε = ι_V([x,y]_ε)`.

This is the *single* unifying transport: with `ε = 1` it is the CAR/anticommutator transport (electron,
D4), with `ε = -1` the CCR/commutator transport (photon, D5).  Proof: the encoding is a `⋆`-homomorphism
that is also additive and scalar-linear (`encode_mul`, `encode_add`, `encode_smul`). -/
theorem encode_gradedBracket (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1) (ε : ℂ) (x y : Matrix dC dC ℂ) :
    gradedBracket ε (encode V x) (encode V y) = encode V (gradedBracket ε x y) := by
  unfold gradedBracket
  rw [encode_add, encode_mul V hV, encode_smul, encode_mul V hV]

/-- **★★ A1 — the master corner-transport of any field relation.**  If the code operators satisfy a graded
bracket relation `[x,y]_ε = M` on the code `C_R`, then their encodings satisfy `[ι_V(x), ι_V(y)]_ε =
ι_V(M)` in the corner.  Every free SM field's defining relation is an instance: the value `ι_V(M)` lives
in the corner (e.g. `M = c•1` gives `c•P`, `M` = a truncation defect gives the encoded defect) — never the
ambient `1_𝓗`. -/
theorem encoded_bracket_of_eq (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1) (ε : ℂ)
    (x y M : Matrix dC dC ℂ) (h : gradedBracket ε x y = M) :
    gradedBracket ε (encode V x) (encode V y) = encode V M := by
  rw [encode_gradedBracket V hV, h]

/-- **★ A1 — the fermionic (CAR) instance, re-derived generically.**  When the code anticommutator is a
scalar multiple of the identity, `{x,y} = [x,y]_{1} = c•1` (the CAR relation, `c = ⟪f,g⟫`), the corner
anticommutator is `c·P` — the corner unit, NOT the ambient `1_𝓗`.  This recovers D4's `encoded_anticomm`
as the `ε = 1` case of the unified transport. -/
theorem encoded_CAR_bracket (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1)
    (x y : Matrix dC dC ℂ) (c : ℂ) (h : gradedBracket 1 x y = c • (1 : Matrix dC dC ℂ)) :
    gradedBracket 1 (encode V x) (encode V y) = c • codeProjector V := by
  rw [encoded_bracket_of_eq V hV 1 x y _ h, encode_smul, encode_one]

end GradedBracket

end QIQTH.FreeFieldCorner
