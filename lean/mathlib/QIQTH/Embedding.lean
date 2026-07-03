/-
  THE EMBEDDING (THE_EMBEDDING_PLAN.md) — the matter-side dictionary: the N-mode truncated
  free-field diamond algebra IS a counted record corner.

  KEY OBSERVATION (binding): the keystone's microstate space `Micro L C = (e : C) → Fin (D e)` IS a
  multi-mode truncated Fock basis (joint occupation numbers `n_k < D_k`). No new Hilbert space is
  built — this file gives the already-counted `DiamondAlg` its FIELD structure and the mode↔link
  dictionary semantics. Transport, not construction; capacity is a constraint, NOT a generator;
  the cutoff→continuum limit is THE wall, never claimed.

  EM1 — the mode dictionary aliases:
  • `ModeAssignment` — mode labels with per-mode level cutoffs (the matter-side data);
  • `toLinkDims` — the dictionary map: A LINK IS A FIELD MODE, its dimension the mode's cutoff;
  • `FieldMicro`/`TruncatedFockBasis`/`FieldDiamondAlg` — the field-side readings of the keystone
    objects, with the rfl dictionary theorems (the identification is DEFINITIONAL);
  • CAPSTONE `truncated_field_diamond_entropy` — the keystone count READ as the truncated field
    diamond's entropy: `S(maxMixed) = Σ_k log D_k = A_τ(C)/4G`.
  Axiom-free, std-3.
-/
import Mathlib
import QIQTH.Keystone
import QIQTH.CornerConstruction

namespace QIQTH.Embedding

open QIQTH.Keystone

variable {M : Type*} [DecidableEq M]

/-- **The mode assignment of a truncated field diamond** — mode labels with per-mode truncation
    cutoffs (`n_k` levels for mode `k`). NAMED finite data per the binding verdict: which modes
    belong to the diamond and how deep they are cut off is carried, never constructed from the
    continuum (the localization map stays the wall). -/
structure ModeAssignment (M : Type*) where
  /-- the truncation cutoff (level count) of each mode -/
  cutoff : M → ℕ
  /-- every mode carries at least one level -/
  cutoff_pos : ∀ k, 0 < cutoff k

/-- **The dictionary map**: a LINK is a FIELD MODE; the link dimension is the mode's cutoff. -/
def ModeAssignment.toLinkDims (A : ModeAssignment M) : LinkDims M :=
  ⟨A.cutoff, A.cutoff_pos⟩

@[simp] theorem ModeAssignment.toLinkDims_D (A : ModeAssignment M) (k : M) :
    A.toLinkDims.D k = A.cutoff k := rfl

/-- **The truncated Fock basis** of the diamond's mode set `C`: joint occupation numbers
    `n_k < D_k` — DEFINITIONALLY the keystone's microstate space. -/
abbrev FieldMicro (A : ModeAssignment M) (C : Finset M) : Type _ :=
  Micro A.toLinkDims C

/-- Alias: the occupation basis. -/
abbrev TruncatedFockBasis (A : ModeAssignment M) (C : Finset M) : Type _ :=
  FieldMicro A C

/-- **The truncated field diamond algebra** — the full matrix algebra on the occupation basis;
    DEFINITIONALLY the keystone's counted `DiamondAlg`. -/
abbrev FieldDiamondAlg (A : ModeAssignment M) (C : Finset M) : Type _ :=
  DiamondAlg A.toLinkDims C

/-- The dictionary is definitional: the truncated Fock basis IS the keystone microstate space. -/
theorem fieldMicro_eq_micro (A : ModeAssignment M) (C : Finset M) :
    FieldMicro A C = Micro A.toLinkDims C := rfl

/-- The dictionary is definitional: the field diamond algebra IS the counted diamond algebra. -/
theorem fieldDiamondAlg_eq_diamondAlg (A : ModeAssignment M) (C : Finset M) :
    FieldDiamondAlg A C = DiamondAlg A.toLinkDims C := rfl

/-- An occupation state is literally a choice of level below each mode's cutoff. -/
theorem fieldMicro_occupation (A : ModeAssignment M) (C : Finset M) :
    FieldMicro A C = ((k : C) → Fin (A.cutoff k.val)) := rfl

/-- **The truncated field diamond's state count**: `#(occupation basis) = Π_k D_k` — the keystone
    count read on the field side. -/
theorem card_truncatedFockBasis (A : ModeAssignment M) (C : Finset M) :
    Fintype.card (TruncatedFockBasis A C) = ∏ k ∈ C, A.cutoff k :=
  card_micro A.toLinkDims C

/-- **EM1 CAPSTONE — the count READS as the truncated field diamond's entropy:** the maximal
    entropy of the N-mode truncated free-field diamond algebra equals the sum of the per-mode
    log-cutoffs equals the trace-induced area over `4G` — the keystone theorem with LINKS = MODES.
    (The keystone capstone applied verbatim through the dictionary; nothing new is proved — that
    definitional transparency IS the point.) -/
theorem truncated_field_diamond_entropy (A : ModeAssignment M) (C : Finset M)
    {G : ℝ} (hG : G ≠ 0) :
    QIQTH.QuantumEntropy.vonNeumannEntropy (maxMixed_isDensity (ι := FieldMicro A C))
      = inducedScreenAreaTau A.toLinkDims G C / (4 * G) :=
  K2a_count_capstone A.toLinkDims C hG

end QIQTH.Embedding
