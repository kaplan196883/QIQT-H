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

section Fermions

variable {dC d𝓗 : Type*} [Fintype dC] [DecidableEq dC] [Fintype d𝓗] [DecidableEq d𝓗]

/-- **★★ A2 — quark/lepton content: flavor-indexed CAR transports into the corner.**  The SM's fermion
content is a family of CAR modes indexed by a finite **flavor** type `Φ` (generations × colors × leptons),
with the flavor-resolved anticommutator `{a(α), a†(β)} = c(α,β)·1` on the code (`c(α,β) = ⟪f_α,g_β⟫`,
flavor-diagonal for orthogonal flavors).  Each transports to the corner with the corner unit `P`:

  `{ι_V(a(α)), ι_V(a†(β))} = c(α,β)·P`.

So the whole multi-flavor free-fermion algebra is an instance of the unified A1 transport — never the
ambient `1_𝓗`.  (Quarks and leptons together; transport of a supplied CAR family, not its construction.) -/
theorem encoded_flavor_CAR {Φ : Type*} (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1)
    (a adag : Φ → Matrix dC dC ℂ) (c : Φ → Φ → ℂ)
    (hCAR : ∀ α β, gradedBracket 1 (a α) (adag β) = c α β • (1 : Matrix dC dC ℂ)) (α β : Φ) :
    gradedBracket 1 (encode V (a α)) (encode V (adag β)) = c α β • codeProjector V :=
  encoded_CAR_bracket V hV (a α) (adag β) (c α β) (hCAR α β)

/-- **★ A2 — the multi-flavor fermion mode count is area-bounded.**  The CAR (exterior) Fock of `F`
flavors each with `m` one-particle modes has dimension `2^(F·m)`.  If it fits the microstate space
(`2^(F·m) ≤ |𝓗_R|`) under the holographic postulate, the total fermionic mode count obeys the area floor:

  `(F·m)·log 2 = log(2^(F·m)) ≤ log|𝓗_R| ≤ A/4ℓ_P²`.

So a region carries only `≲ A/(4ℓ_P² log 2)` quark+lepton modes — capacity bounds the *mode count* (it does
not generate the fermions).  Generalizes `CornerConstruction.fermion_modes_le_area` to multi-flavor. -/
theorem fermion_flavor_modes_le_area {F m : ℕ} {𝓗 : Type*} [Fintype 𝓗] {areaTerm : ℝ}
    [HolographicCapacityBound 𝓗 areaTerm] (hfit : 2 ^ (F * m) ≤ Fintype.card 𝓗) :
    ((F * m : ℕ) : ℝ) * Real.log 2 ≤ areaTerm :=
  fermion_modes_le_area hfit

end Fermions

section GaugeBosons

variable {dC d𝓗 : Type*} [Fintype dC] [DecidableEq dC] [Fintype d𝓗] [DecidableEq d𝓗]

/-- **★★ A3 — gauge-boson content (W/Z/gluon): the gauge-indexed commutator transports with its
truncation defect.**  The SM's massive vector bosons (W, Z) and gluons are *bosonic*, indexed by a finite
gauge/polarization type `G` (8 gluon colors, the 3 weak bosons, polarizations).  Each component's
commutator `[a(g), a†(g)] = M(g)` on the code transports into the corner as `ι_V(M(g))` — and because
the field is bosonic, `M(g)` is **not** a clean `c·1` but the **truncated-oscillator defect**
(`M(g) = 1 − N·|N-1⟩⟨N-1|`, D5), so the corner value is `P − N·ι_V(|top⟩⟨top|)`: the gauge boson on a
finite-capacity sector is necessarily **truncated**, the defect carried explicitly (contrast the clean
fermion `c·P` of A2).  This is the ε = −1 (commutator) instance of the unified A1 transport. -/
theorem encoded_gauge_boson_commutator {G : Type*} (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1)
    (a adag M : G → Matrix dC dC ℂ)
    (hCCR : ∀ g, gradedBracket (-1) (a g) (adag g) = M g) (g : G) :
    gradedBracket (-1) (encode V (a g)) (encode V (adag g)) = encode V (M g) :=
  encoded_bracket_of_eq V hV (-1) (a g) (adag g) (M g) (hCCR g)

/-- **★ A3 — the gauge-boson mode count is area-bounded.**  A `G`-component truncated bosonic sector (the
`G` gauge/polarization components, each a number-cutoff symmetric Fock `Γ_s^{≤N}(ℂ^d)` of dimension
`C(d+N,N)`) has total dimension `C(d+N,N)^G`.  If it fits the microstate space (`C(d+N,N)^G ≤ |𝓗_R|`)
under the holographic postulate, its log capacity obeys the area floor:

  `G·log C(d+N,N) = log(C(d+N,N)^G) ≤ log|𝓗_R| ≤ A/4ℓ_P²`.

The occupation cutoff `N` is explicit — without it the bosonic Fock is infinite-dimensional and fits no
finite sector (`no_finiteDim_CCR`).  Multi-component generalization of
`CornerConstruction.photon_modes_le_area`. -/
theorem gauge_boson_modes_le_area {d N G : ℕ} {𝓗 : Type*} [Fintype 𝓗] {areaTerm : ℝ}
    [hcap : HolographicCapacityBound 𝓗 areaTerm] (hfit : ((d + N).choose N) ^ G ≤ Fintype.card 𝓗) :
    (G : ℝ) * Real.log ((d + N).choose N) ≤ areaTerm := by
  have hpos : (0 : ℝ) < ((d + N).choose N : ℝ) ^ G :=
    pow_pos (by exact_mod_cast Nat.choose_pos (Nat.le_add_left N d)) G
  rw [← Real.log_pow]
  calc Real.log (((d + N).choose N : ℝ) ^ G)
      ≤ Real.log (Fintype.card 𝓗) := Real.log_le_log hpos (by exact_mod_cast hfit)
    _ ≤ areaTerm := hcap.bound

end GaugeBosons

end QIQTH.FreeFieldCorner
